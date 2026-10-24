(* ========================================================================= *)
(* 4CT/jordan.ml                                                             *)
(*                                                                           *)
(* jordan.v: the Jordan property of planar hypermaps.  A Moebius path        *)
(* (moebius_path) is a simple contour path whose two ends link back into it  *)
(* in crossing order; jordan H says there is none.  PLANAR_JORDAN (Coq       *)
(* planar_Jordan): a planar hypermap has the Jordan property, by induction   *)
(* on the number of darts, a Moebius path being transferred by a Walkup      *)
(* transform to a smaller planar hypermap (JORDAN_STEP) down to the          *)
(* three-dart map excluded by the Euler formula (THREE_DART_NOT_PLANAR).     *)
(* EVEN_GENUS (even_genusP) is the parity of the Euler defect, CUBIC_EULER   *)
(* (cubic_Euler) the Euler formula 6 F = D + 12 of planar plain cubic        *)
(* connected maps, and EULER_TREE (Euler_tree) says that under the Jordan    *)
(* property every edge cycle has a dart z with clink H z z or ~cross_edge H  *)
(* z, the Euler-tree leaf used by kempe.ml.                                  *)
(* ========================================================================= *)

needs "4CT/walkup.ml";;
needs "4CT/coloring.ml";;

let even_genus = new_definition
  `even_genus (H:(A)hypermap) <=>
    euler_lhs H = 2 * genus H + euler_rhs H`;;

let mem2 = new_definition
  `mem2 (p:(A)list) (x:A) (y:A) <=>
    ?p1 p2. p = APPEND p1 (CONS x p2) /\ MEM y (CONS x p2)`;;

let moebius_path = new_definition
  `moebius_path (H:(A)hypermap) (q:(A)list) <=>
    ~(q = []) /\
    PAIRWISE (\x:A y. ~(x = y)) q /\
    list_path (clink H) (HD q) (TL q) /\
    mem2 (TL q)
      (inverse (node_map H) (LAST q))
      (node_map H (HD q))`;;

let jordan = new_definition
  `jordan (H:(A)hypermap) <=> !q. ~(moebius_path H q)`;;

let clink1 = new_definition
  `clink1 (H:(A)hypermap) z x y <=>
     x = node_map H y \/ face_map (edge_walkup H z) x = y`;;

let iterlist = define
 `(iterlist 0 (f:A->A) x = []) /\
  (iterlist (SUC n) f x = CONS (f x) (iterlist n f (f x)))`;;
(* ------------------------------------------------------------------------- *)
(* Basic facts about the three maps of a hypermap.                           *)
(* ------------------------------------------------------------------------- *)

let INV_NODE_NODE = prove
 (`!(H:(A)hypermap) w. inverse(node_map H) (node_map H w) = w`,
  MESON_TAC[PERMUTES_INVERSES; NODE_MAP_PERMUTES]);;

let NODE_MAP_EQ = prove
 (`!(H:(A)hypermap) x v. node_map H x = v <=> face_map H (edge_map H v) = x`,
  MESON_TAC[nodeK; edgeK]);;

let FACE_MAP_EQ = prove
 (`!(H:(A)hypermap) x v. face_map H x = v <=> edge_map H (node_map H v) = x`,
  MESON_TAC[faceK; nodeK]);;

let CLINKF = prove
 (`!(H:(A)hypermap) x. clink H x (face_map H x)`,
  REWRITE_TAC[clink]);;

let CLINKN = prove
 (`!(H:(A)hypermap) x. clink H (node_map H x) x`,
  REWRITE_TAC[clink]);;

let CLINK_DART = prove
 (`!(H:(A)hypermap) x y. clink H x y /\ x IN dart H ==> y IN dart H`,
  REWRITE_TAC[clink] THEN
  MESON_TAC[PERMUTES_IN_IMAGE; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES]);;

let CLINK_OUTSIDE_DART = prove
 (`!(H:(A)hypermap) x y. clink H x y /\ ~(x IN dart H) ==> y = x`,
  REWRITE_TAC[clink] THEN
  MESON_TAC[PERMUTES_IN_IMAGE; NODE_MAP_PERMUTES; MAPS_OUTSIDE_DART]);;

(* ------------------------------------------------------------------------- *)
(* Paths along a relation (list_path, from geometry.ml).                     *)
(* ------------------------------------------------------------------------- *)

let LIST_PATH_APPEND = prove
 (`!(e:A->A->bool) p1 x p2.
     list_path e x (APPEND p1 p2) <=>
     list_path e x p1 /\ list_path e (LAST (CONS x p1)) p2`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[APPEND; list_path; LAST; NOT_CONS_NIL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[APPEND; list_path; LAST_CLAUSES] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let LIST_PATH_MONO = prove
 (`!(e:A->A->bool) e' x p.
     list_path e x p /\
     (!u v. MEM u (CONS x p) /\ MEM v p /\ e u v ==> e' u v)
     ==> list_path e' x p`,
  GEN_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_path; MEM] THEN
  REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let LIST_PATH_CLINK_DART = prove
 (`!(H:(A)hypermap) p x.
     list_path (clink H) x p /\ x IN dart H ==> !y. MEM y p ==> y IN dart H`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_path; MEM] THEN
  ASM_MESON_TAC[CLINK_DART]);;

let LIST_PATH_MEM_LAST = prove
 (`!(x:A) p. MEM (LAST (CONS x p)) (CONS x p)`,
  MESON_TAC[MEM_LAST; NOT_CONS_NIL]);;

let LIST_PATH_SPLIT_AT = prove
 (`!(e:A->A->bool) m x v. MEM v (x :: m) /\ list_path e x m
    ==> ?m1 m2. (x :: m):(A)list = APPEND (x :: m1) m2 /\
                list_path e x m1 /\ LAST(x :: m1) = v`,
  let ihtac =
    FIRST_X_ASSUM(MP_TAC o SPECL [`h:A`; `v:A`]) THEN ASM_REWRITE_TAC[MEM] THEN
    DISCH_THEN(X_CHOOSE_THEN `m1:(A)list` (X_CHOOSE_THEN `m2:(A)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(h:A) :: m1`; `m2:(A)list`] THEN
    ASM_REWRITE_TAC[APPEND; list_path; CONS_11; LAST_CLAUSES] in
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[list_path; MEM] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:(A)list`; `[]:(A)list`] THEN
    ASM_REWRITE_TAC[APPEND; list_path; LAST];
    MAP_EVERY EXISTS_TAC [`[]:(A)list`; `(h:A) :: t`] THEN
    ASM_REWRITE_TAC[APPEND; list_path; LAST];
    ihtac; ihtac]);;

let LIST_PATH_SPLIT_AT_TAIL = prove
 (`!(e:A->A->bool) m x v. MEM v (x :: m) /\ list_path e x m
    ==> ?m1 m2. (x :: m):(A)list = APPEND m1 (v :: m2) /\ list_path e v m2`,
  let ihtac =
    FIRST_X_ASSUM(MP_TAC o SPECL [`h:A`; `v:A`]) THEN ASM_REWRITE_TAC[MEM] THEN
    DISCH_THEN(X_CHOOSE_THEN `m1:(A)list` (X_CHOOSE_THEN `m2:(A)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`(x:A) :: m1`; `m2:(A)list`] THEN
    ASM_REWRITE_TAC[APPEND] in
  GEN_TAC THEN LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[list_path; MEM] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`[]:(A)list`; `[]:(A)list`] THEN
    ASM_REWRITE_TAC[APPEND; list_path];
    MAP_EVERY EXISTS_TAC [`[]:(A)list`; `(h:A) :: t`] THEN
    ASM_REWRITE_TAC[APPEND; list_path];
    ihtac; ihtac]);;

let LIST_PATH_DROP_LOOP = prove
 (`!(e:A->A->bool) a x b.
    list_path e x (APPEND a (CONS x b))
    ==> list_path e x b /\
        LAST(CONS x b) = LAST(CONS x (APPEND a (CONS x b)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIST_PATH_APPEND; list_path] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND; NOT_CONS_NIL] THEN
  SIMP_TAC[]);;

let LIST_PATH_SHORTEN = prove
 (`!(e:A->A->bool) x m.
    list_path e x m
    ==> ?m'. list_path e x m' /\ LAST(CONS x m') = LAST(CONS x m) /\
             PAIRWISE (\a b. ~(a = b)) (CONS x m') /\
             (!y. MEM y (CONS x m') ==> MEM y (CONS x m))`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!n x m. LENGTH m = n /\ list_path (e:A->A->bool) x m
            ==> ?m'. list_path e x m' /\ LAST(CONS x m') = LAST(CONS x m) /\
                     PAIRWISE (\a b. ~(a = b)) (CONS x m') /\
                     (!y. MEM y (CONS x m') ==> MEM y (CONS x m))`
   (fun th -> REPEAT STRIP_TAC THEN
              MP_TAC(SPECL [`LENGTH(m:(A)list)`; `x:A`; `m:(A)list`] th) THEN
              ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `m:(A)list` list_CASES) THEN STRIP_TAC THENL
   [EXISTS_TAC `[]:(A)list` THEN ASM_REWRITE_TAC[list_path; PAIRWISE; ALL];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `MEM (x:A) (CONS h t)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `a:(A)list` (X_CHOOSE_THEN `b:(A)list`
      SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
    MP_TAC(ISPECL [`e:A->A->bool`; `a:(A)list`; `x:A`; `b:(A)list`]
      LIST_PATH_DROP_LOOP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH(b:(A)list)`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `LENGTH (APPEND a (CONS (x:A) b)) = n` THEN
      REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `b:(A)list`]) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m':(A)list` THEN
    ASM_REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[];
    UNDISCH_TAC `list_path (e:A->A->bool) x (CONS h t)` THEN
    REWRITE_TAC[list_path] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `LENGTH(t:(A)list)`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `LENGTH (CONS (h:A) t) = n` THEN REWRITE_TAC[LENGTH] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`h:A`; `t:(A)list`]) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (h:A) t'` THEN
    ASM_REWRITE_TAC[list_path; LAST_CLAUSES; PAIRWISE; GSYM ALL_MEM] THEN
    ASM_MESON_TAC[MEM]]);;

(* ------------------------------------------------------------------------- *)
(* mem2 p x y: x occurs in p and y occurs at or after that occurrence.       *)
(* ------------------------------------------------------------------------- *)

let MEM2_NIL = prove
 (`!(x:A) b. ~(mem2 [] x b)`,
  REWRITE_TAC[mem2] THEN MESON_TAC[APPEND_EQ_NIL; NOT_CONS_NIL]);;

let MEM2_CONS = prove
 (`!(z:A) l x b.
     mem2 (CONS z l) x b <=> x = z /\ MEM b (CONS z l) \/ mem2 l x b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mem2] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p1:(A)list` MP_TAC) THEN
    MP_TAC(ISPEC `p1:(A)list` list_CASES) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[APPEND; CONS_11] THEN MESON_TAC[];
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`[]:(A)list`; `l:(A)list`] THEN
      ASM_REWRITE_TAC[APPEND];
      MAP_EVERY EXISTS_TAC [`CONS (z:A) p1`; `p2:(A)list`] THEN
      ASM_REWRITE_TAC[APPEND]]]);;

let MEM2_MEM = prove
 (`!(l:(A)list) x b. mem2 l x b ==> MEM x l /\ MEM b l`,
  REWRITE_TAC[mem2] THEN MESON_TAC[MEM_APPEND; MEM]);;

let MEM2_SPLICE_Z = prove
 (`!(p1:(A)list) z p2 b.
     MEM b (z :: p2) ==> mem2 (APPEND p1 (z :: p2)) z b`,
  REWRITE_TAC[mem2] THEN MESON_TAC[]);;

let MEM2_APPEND_R = prove
 (`!(l:(A)list) m x b. mem2 l x b ==> mem2 (APPEND l m) x b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mem2] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:(A)list` (X_CHOOSE_THEN `p2:(A)list`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`p1:(A)list`; `APPEND p2 (m:(A)list)`] THEN
  ASM_REWRITE_TAC[GSYM APPEND_ASSOC; APPEND] THEN
  UNDISCH_TAC `MEM (b:A) (CONS x p2)` THEN
  REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]);;

let MEM2_LAST = prove
 (`!(l:(A)list) x. MEM x l ==> mem2 l x (LAST l)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:(A)list` (X_CHOOSE_THEN `p2:(A)list`
    SUBST1_TAC) o MATCH_MP MEM_SPLIT) THEN
  REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL] THEN
  MATCH_MP_TAC MEM2_SPLICE_Z THEN REWRITE_TAC[LIST_PATH_MEM_LAST]);;

(* ------------------------------------------------------------------------- *)
(* Lists of pairwise distinct elements.                                      *)
(* ------------------------------------------------------------------------- *)

let PAIRWISE_DISTINCT_CONS = prove
 (`!(h:A) t. PAIRWISE (\a b. ~(a = b)) (CONS h t) <=>
             ~(MEM h t) /\ PAIRWISE (\a b. ~(a = b)) t`,
  REWRITE_TAC[PAIRWISE; GSYM ALL_MEM] THEN MESON_TAC[]);;

let PAIRWISE_DISTINCT_APPEND = prove
 (`!(l:(A)list) m. PAIRWISE (\a b. ~(a = b)) (APPEND l m) <=>
     PAIRWISE (\a b. ~(a = b)) l /\ PAIRWISE (\a b. ~(a = b)) m /\
     (!x. MEM x l ==> ~(MEM x m))`,
  REWRITE_TAC[PAIRWISE_APPEND] THEN MESON_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* The maps of the three Walkup transforms.  For edge_walkup H z the node    *)
(* and face maps are swap(z,n z) o n and swap(z,f z) o f; node_walkup and    *)
(* face_walkup (defined by triality) have the analogous explicit edge/face   *)
(* resp. edge/node maps, and the third map is determined by e o n o f = I.   *)
(* ------------------------------------------------------------------------- *)

let NODE_WALKUP_MAPS = prove
 (`!H (y:A). y IN dart H
   ==> face_map (node_walkup H y) = swap(y, face_map H y) o face_map H /\
       edge_map (node_walkup H y) = swap(y, edge_map H y) o edge_map H`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[node_walkup] THEN
  MP_TAC(ISPECL [`permN(H:(A)hypermap)`; `y:A`] EDGE_WALKUP_COMPONENTS) THEN
  ASM_REWRITE_TAC[PERMN_COMPONENTS] THEN
  SIMP_TAC[PERMF_COMPONENTS; PERMN_COMPONENTS]);;

let FACE_WALKUP_MAPS = prove
 (`!H (y:A). y IN dart H
   ==> edge_map (face_walkup H y) = swap(y, edge_map H y) o edge_map H /\
       node_map (face_walkup H y) = swap(y, node_map H y) o node_map H`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[face_walkup] THEN
  MP_TAC(ISPECL [`permF(H:(A)hypermap)`; `y:A`] EDGE_WALKUP_COMPONENTS) THEN
  ASM_REWRITE_TAC[PERMF_COMPONENTS] THEN
  SIMP_TAC[PERMN_COMPONENTS; PERMF_COMPONENTS]);;

let DART_NODE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> dart(node_walkup H z) = dart H DELETE z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[node_walkup; PERMF_COMPONENTS] THEN
  ASM_SIMP_TAC[DART_EDGE_WALKUP; PERMN_COMPONENTS]);;

let DART_FACE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> dart(face_walkup H z) = dart H DELETE z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[face_walkup; PERMN_COMPONENTS] THEN
  ASM_SIMP_TAC[DART_EDGE_WALKUP; PERMF_COMPONENTS]);;

let CARD_DART_NODE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> CARD(dart(node_walkup H z)) = CARD(dart H) - 1`,
  SIMP_TAC[DART_NODE_WALKUP; CARD_DELETE; FINITE_DART]);;

let CARD_DART_FACE_WALKUP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> CARD(dart(face_walkup H z)) = CARD(dart H) - 1`,
  SIMP_TAC[DART_FACE_WALKUP; CARD_DELETE; FINITE_DART]);;

let NODE_MAP_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H
    ==> node_map (edge_walkup H z) x = swap(z,node_map H z) (node_map H x)`,
  SIMP_TAC[EDGE_WALKUP_COMPONENTS; o_THM]);;

let FACE_MAP_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H
    ==> face_map (edge_walkup H z) x = swap(z,face_map H z) (face_map H x)`,
  SIMP_TAC[EDGE_WALKUP_COMPONENTS; o_THM]);;

let NODE_MAP_FACE_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H
    ==> node_map (face_walkup H z) x = swap(z,node_map H z) (node_map H x)`,
  SIMP_TAC[FACE_WALKUP_MAPS; o_THM]);;

let EDGE_MAP_FACE_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H
    ==> edge_map (face_walkup H z) x = swap(z,edge_map H z) (edge_map H x)`,
  SIMP_TAC[FACE_WALKUP_MAPS; o_THM]);;

let FACE_MAP_NODE_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H
    ==> face_map (node_walkup H z) x = swap(z,face_map H z) (face_map H x)`,
  SIMP_TAC[NODE_WALKUP_MAPS; o_THM]);;

let EDGE_MAP_NODE_WALKUP = prove
 (`!(H:(A)hypermap) z x. z IN dart H
    ==> edge_map (node_walkup H z) x = swap(z,edge_map H z) (edge_map H x)`,
  SIMP_TAC[NODE_WALKUP_MAPS; o_THM]);;

let SWAP_ENDS = prove
 (`!(a:A) b. swap(a,b) a = b /\ swap(a,b) b = a`,
  REWRITE_TAC[SWAP_LEFT; SWAP_RIGHT]);;

(* ------------------------------------------------------------------------- *)
(* Lifting contour links and paths through the Walkup transforms.            *)
(* ------------------------------------------------------------------------- *)

let CLINK_EDGE_WALKUP = prove
 (`!(H:(A)hypermap) z x y.
     z IN dart H /\ ~(x = z) /\ ~(y = z) /\ clink H x y
     ==> clink (edge_walkup H z) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clink] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NODE_MAP_EDGE_WALKUP; FACE_MAP_EDGE_WALKUP] THENL
   [DISJ1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC SWAP_OTHER THEN
    ASM_MESON_TAC[NODEI];
    DISJ2_TAC THEN MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[FACEI]]);;

let CLINK_NODE_WALKUP = prove
 (`!(H:(A)hypermap) z x y.
     z IN dart H /\ ~(x = z) /\ ~(y = z) /\ ~(y = face_map H z) /\
     clink H x y
     ==> clink (node_walkup H z) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clink] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[NODE_MAP_EQ] THEN
    SIMP_TAC[FACE_MAP_NODE_WALKUP; EDGE_MAP_NODE_WALKUP;
             ASSUME `(z:A) IN dart H`] THEN
    SUBGOAL_THEN `swap(z,edge_map H z) (edge_map H x) = edge_map H (x:A)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[EDGEI; nodeK]; ALL_TAC] THEN
    SUBGOAL_THEN `face_map H (edge_map H x) = (y:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[nodeK]; ALL_TAC] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN
    SIMP_TAC[FACE_MAP_NODE_WALKUP; ASSUME `(z:A) IN dart H`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SWAP_OTHER THEN ASM_REWRITE_TAC[]]);;

let CLINK_FACE_WALKUP = prove
 (`!(H:(A)hypermap) z x y.
     z IN dart H /\ ~(x = z) /\ ~(y = z) /\
     ~(y = face_map H (edge_map H z)) /\ clink H x y
     ==> clink (face_walkup H z) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[clink] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN
    SIMP_TAC[NODE_MAP_FACE_WALKUP; ASSUME `(z:A) IN dart H`] THEN
    CONV_TAC SYM_CONV THEN
    SUBGOAL_THEN `node_map H y = (x:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[NODEI];
    DISJ2_TAC THEN REWRITE_TAC[FACE_MAP_EQ] THEN
    SIMP_TAC[NODE_MAP_FACE_WALKUP; EDGE_MAP_FACE_WALKUP;
             ASSUME `(z:A) IN dart H`] THEN
    SUBGOAL_THEN `swap(z,node_map H z) (node_map H y) = node_map H (y:A)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[NODEI; nodeK]; ALL_TAC] THEN
    SUBGOAL_THEN `edge_map H (node_map H y) = (x:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[faceK]; ALL_TAC] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[nodeK]]);;

let LIFT_PATH_E = prove
 (`!(H:(A)hypermap) z x p.
     z IN dart H /\ ~(MEM z (CONS x p)) /\ list_path (clink H) x p
     ==> list_path (clink (edge_walkup H z)) x p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `clink (H:(A)hypermap)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLINK_EDGE_WALKUP THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM]);;

let LIFT_PATH_N = prove
 (`!(H:(A)hypermap) z x p.
     z IN dart H /\ ~(MEM z (CONS x p)) /\ ~(MEM (face_map H z) p) /\
     list_path (clink H) x p
     ==> list_path (clink (node_walkup H z)) x p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `clink (H:(A)hypermap)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLINK_NODE_WALKUP THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM]);;

let LIFT_PATH_F = prove
 (`!(H:(A)hypermap) z x p.
     z IN dart H /\ ~(MEM z (CONS x p)) /\
     ~(MEM (face_map H (edge_map H z)) p) /\ list_path (clink H) x p
     ==> list_path (clink (face_walkup H z)) x p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `clink (H:(A)hypermap)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLINK_FACE_WALKUP THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM]);;

(* ------------------------------------------------------------------------- *)
(* Moebius paths: unfolding, introduction and dart membership.               *)
(* ------------------------------------------------------------------------- *)

let MOEBIUS_PATH_CONS = prove
 (`!(H:(A)hypermap) x p.
     moebius_path H (CONS x p) <=>
     PAIRWISE (\a b. ~(a = b)) (CONS x p) /\ list_path (clink H) x p /\
     mem2 p (inverse (node_map H) (LAST (CONS x p))) (node_map H x)`,
  REWRITE_TAC[moebius_path; NOT_CONS_NIL; HD; TL]);;

let MOEBIUS_PATH_INTRO = prove
 (`!(H:(A)hypermap) u q w.
     PAIRWISE (\a b. ~(a = b)) (CONS u q) /\ list_path (clink H) u q /\
     LAST (CONS u q) = node_map H w /\ mem2 q w (node_map H u)
     ==> moebius_path H (CONS u q)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[MOEBIUS_PATH_CONS; INV_NODE_NODE]);;

let MOEBIUS_PATH_DART = prove
 (`!(H:(A)hypermap) x p.
     moebius_path H (CONS x p)
     ==> x IN dart H /\ !y. MEM y p ==> y IN dart H`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOEBIUS_PATH_CONS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN dart H` ASSUME_TAC THENL
   [MP_TAC(ISPEC `p:(A)list` list_CASES) THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[MEM2_NIL];
      RULE_ASSUM_TAC(REWRITE_RULE[list_path; PAIRWISE_DISTINCT_CONS; MEM]) THEN
      ASM_MESON_TAC[CLINK_OUTSIDE_DART]];
    ASM_MESON_TAC[LIST_PATH_CLINK_DART]]);;
(* ------------------------------------------------------------------------- *)
(* The Walkup steps of the minimal-counterexample proof of PLANAR_JORDAN.    *)
(* A Moebius path x :: p of H, with "node t = LAST (x :: p)", is transferred *)
(* to a Walkup transform of H in each of the following situations:           *)
(*  E1  a dart z of H is not on x :: p             (edge_walkup H z)         *)
(*  E2  x = node y, p = y :: _                     (edge_walkup H x)         *)
(*  F3  face x = y, node z = y, p = y :: z :: _    (face_walkup H y)         *)
(*  E4  face x = y, face y = z, t <> y             (edge_walkup H y)         *)
(*  N5  face x = y, face y = z, t = y, node x <> y (node_walkup H y)         *)
(*  E6  all of the above fail, face z = t          (edge_walkup H z)         *)
(*  F7  all of the above fail, node t = z          (face_walkup H z)         *)
(* ------------------------------------------------------------------------- *)

let NODE_INV_NODE = prove
 (`!(H:(A)hypermap) w. node_map H (inverse(node_map H) w) = w`,
  MESON_TAC[PERMUTES_INVERSES; NODE_MAP_PERMUTES]);;

(* Decompose a Moebius path hypothesis into its components.                  *)
let MOEBIUS_HYP_TAC th =
  STRIP_ASSUME_TAC(MATCH_MP MOEBIUS_PATH_DART th) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[MOEBIUS_PATH_CONS; LAST_CLAUSES; list_path;
                                PAIRWISE_DISTINCT_CONS] th);;

let JORDAN_STEP_E1 = prove
 (`!(H:(A)hypermap) x p z.
     moebius_path H (CONS x p) /\ z IN dart H /\ ~(MEM z (CONS x p))
     ==> moebius_path (edge_walkup H z) (CONS x p)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = inverse (node_map H) (LAST (CONS (x:A) p))` THEN
  SUBGOAL_THEN `node_map H t = LAST (CONS (x:A) p)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[NODE_INV_NODE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (t:A) p /\ MEM (node_map H x) p /\ MEM (node_map H t) (CONS x p)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM2_MEM; LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map (edge_walkup H z) t = node_map H t /\
                node_map (edge_walkup H z) x = node_map H (x:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_EDGE_WALKUP] THEN CONJ_TAC THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[NODEI; MEM];
    ALL_TAC] THEN
  MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `t:A` THEN
  ASM_SIMP_TAC[LIFT_PATH_E; PAIRWISE_DISTINCT_CONS]);;

let JORDAN_STEP_E2 = prove
 (`!(H:(A)hypermap) x y p.
     moebius_path H (CONS x (CONS y p)) /\ x = node_map H y
     ==> moebius_path (edge_walkup H x) (CONS y p)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC (ASSUME_TAC o SYM)) THEN
  ABBREV_TAC `t = inverse (node_map H) (LAST (CONS (y:A) p))` THEN
  SUBGOAL_THEN `node_map H t = LAST (CONS (y:A) p)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[NODE_INV_NODE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (t:A) (CONS y p) /\ MEM (node_map H x) (CONS y p) /\
    MEM (node_map H t) (CONS y p)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM2_MEM; LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:A = y)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map (edge_walkup H x) t = node_map H t /\
                node_map (edge_walkup H x) y = node_map H (x:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_EDGE_WALKUP; SWAP_ENDS] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[NODEI];
    ALL_TAC] THEN
  MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `t:A` THEN
  ASM_SIMP_TAC[LIFT_PATH_E; PAIRWISE_DISTINCT_CONS] THEN
  UNDISCH_TAC `mem2 (CONS y p) (t:A) (node_map H x)` THEN
  ASM_SIMP_TAC[MEM2_CONS]);;

let JORDAN_STEP_F3 = prove
 (`!(H:(A)hypermap) x y z p.
     moebius_path H (CONS x (CONS y (CONS z p))) /\
     face_map H x = y /\ node_map H z = y
     ==> moebius_path (face_walkup H y) (CONS x (CONS z p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:A = y) /\ ~(x = z) /\ ~(y = z)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  ABBREV_TAC `t = inverse (node_map H) (LAST (CONS (z:A) p))` THEN
  SUBGOAL_THEN `node_map H t = LAST (CONS (z:A) p)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[NODE_INV_NODE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (t:A) (CONS y (CONS z p)) /\
    MEM (node_map H x) (CONS y (CONS z p)) /\
    MEM (node_map H t) (CONS z p)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM2_MEM; LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map H (edge_map H y) = (z:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[nodeK]; ALL_TAC] THEN
  SUBGOAL_THEN `~(node_map H x = y:A) /\ ~(x = edge_map H y)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NODEI]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map (face_walkup H y) x = (z:A)` ASSUME_TAC THENL
   [REWRITE_TAC[FACE_MAP_EQ] THEN
    SIMP_TAC[NODE_MAP_FACE_WALKUP; EDGE_MAP_FACE_WALKUP;
             ASSUME `(y:A) IN dart H`] THEN
    ASM_REWRITE_TAC[SWAP_ENDS] THEN
    SUBGOAL_THEN `edge_map H (node_map H y) = (x:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[faceK]; ALL_TAC] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map (face_walkup H y) x = node_map H (x:A)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_FACE_WALKUP] THEN MATCH_MP_TAC SWAP_OTHER THEN
    ASM_MESON_TAC[NODEI];
    ALL_TAC] THEN
  SUBGOAL_THEN `list_path (clink (face_walkup H y)) x (CONS (z:A) p)`
  ASSUME_TAC THENL
   [REWRITE_TAC[list_path] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[clink];
      MATCH_MP_TAC LIFT_PATH_F THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:A = y` THENL
   [SUBGOAL_THEN `node_map (face_walkup H y) z = LAST (CONS (z:A) p)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[NODE_MAP_FACE_WALKUP; SWAP_ENDS] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `z:A` THEN
    ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS; MEM2_CONS; LAST_CLAUSES] THEN
    UNDISCH_TAC `~MEM (x:A) (CONS y (CONS z p))` THEN
    UNDISCH_TAC `MEM (node_map H x) (CONS y (CONS (z:A) p))` THEN
    UNDISCH_TAC `~(node_map H x = y:A)` THEN REWRITE_TAC[MEM] THEN
    MESON_TAC[];
    SUBGOAL_THEN `node_map (face_walkup H y) t = LAST (CONS (z:A) p)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[NODE_MAP_FACE_WALKUP] THEN MATCH_MP_TAC SWAP_OTHER THEN
      ASM_MESON_TAC[NODEI];
      ALL_TAC] THEN
    MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `t:A` THEN
    ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS; LAST_CLAUSES] THEN
    UNDISCH_TAC `mem2 (CONS y (CONS z p)) (t:A) (node_map H x)` THEN
    ASM_REWRITE_TAC[MEM2_CONS] THEN
    UNDISCH_TAC `~MEM (x:A) (CONS y (CONS z p))` THEN REWRITE_TAC[MEM] THEN
    MESON_TAC[]]);;

let JORDAN_STEP_E4 = prove
 (`!(H:(A)hypermap) x y z p.
     moebius_path H (CONS x (CONS y (CONS z p))) /\
     face_map H x = y /\ face_map H y = z /\
     ~(LAST (CONS z p) = node_map H y)
     ==> moebius_path (edge_walkup H y) (CONS x (CONS z p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:A = y) /\ ~(x = z) /\ ~(y = z)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  ABBREV_TAC `t = inverse (node_map H) (LAST (CONS (z:A) p))` THEN
  SUBGOAL_THEN `node_map H t = LAST (CONS (z:A) p)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[NODE_INV_NODE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t:A = y)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `mem2 (CONS z p) (t:A) (node_map H x)` ASSUME_TAC THENL
   [UNDISCH_TAC `mem2 (CONS y (CONS z p)) (t:A) (node_map H x)` THEN
    ASM_REWRITE_TAC[MEM2_CONS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (t:A) (CONS z p) /\ MEM (node_map H x) (CONS z p) /\
    MEM (node_map H t) (CONS z p)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM2_MEM; LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `node_map (edge_walkup H y) x = node_map H (x:A) /\
    node_map (edge_walkup H y) t = node_map H t /\
    face_map (edge_walkup H y) x = (z:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_EDGE_WALKUP; FACE_MAP_EDGE_WALKUP; SWAP_ENDS] THEN
    CONJ_TAC THEN MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[NODEI; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (x:A) (CONS z p)` ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (x:A) (CONS y (CONS z p))` THEN REWRITE_TAC[MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `t:A` THEN
  ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS; list_path; clink; LAST_CLAUSES] THEN
  MATCH_MP_TAC LIFT_PATH_E THEN ASM_REWRITE_TAC[]);;

let JORDAN_STEP_N5 = prove
 (`!(H:(A)hypermap) x y z p.
     moebius_path H (CONS x (CONS y (CONS z p))) /\
     face_map H x = y /\ face_map H y = z /\
     LAST (CONS z p) = node_map H y /\ ~(node_map H x = y)
     ==> moebius_path (node_walkup H y) (CONS x (CONS z p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:A = y) /\ ~(x = z) /\ ~(y = z)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `inverse (node_map H) (LAST (CONS (z:A) p)) = y`
  SUBST_ALL_TAC THENL [ASM_REWRITE_TAC[INV_NODE_NODE]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (node_map H x) (CONS (z:A) p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM2_MEM; MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x = edge_map H (y:A))` ASSUME_TAC THENL
   [ASM_MESON_TAC[edgeK; LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map (node_walkup H y) x = (z:A)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_MAP_NODE_WALKUP; SWAP_ENDS]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map (node_walkup H y) z = LAST (CONS (z:A) p)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NODE_MAP_EQ] THEN
    SIMP_TAC[FACE_MAP_NODE_WALKUP; EDGE_MAP_NODE_WALKUP;
             ASSUME `(y:A) IN dart H`] THEN
    SUBGOAL_THEN `edge_map H (LAST (CONS (z:A) p)) = x` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[faceK]; ALL_TAC] THEN
    SUBGOAL_THEN `swap(y,edge_map H y) (x:A) = x` SUBST1_TAC THENL
     [MATCH_MP_TAC SWAP_OTHER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SWAP_ENDS];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map (node_walkup H y) x = node_map H (x:A)`
  ASSUME_TAC THENL
   [REWRITE_TAC[NODE_MAP_EQ] THEN
    SIMP_TAC[FACE_MAP_NODE_WALKUP; EDGE_MAP_NODE_WALKUP;
             ASSUME `(y:A) IN dart H`] THEN
    SUBGOAL_THEN
     `swap(y,edge_map H y) (edge_map H (node_map H x)) =
      edge_map H (node_map H (x:A))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[EDGEI; nodeK]; ALL_TAC] THEN
    REWRITE_TAC[nodeK] THEN MATCH_MP_TAC SWAP_OTHER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (x:A) (CONS z p)` ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (x:A) (CONS y (CONS z p))` THEN REWRITE_TAC[MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `z:A` THEN
  ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS; list_path; clink; MEM2_CONS;
                  LAST_CLAUSES] THEN
  MATCH_MP_TAC LIFT_PATH_N THEN ASM_REWRITE_TAC[]);;

let JORDAN_STEP_E6 = prove
 (`!(H:(A)hypermap) x y z t p.
     moebius_path H (CONS x (CONS y (CONS z (CONS t p)))) /\
     face_map H x = y /\ face_map H y = z /\ node_map H x = y /\
     LAST (CONS t p) = node_map H y /\ face_map H z = t
     ==> moebius_path (edge_walkup H z) (CONS x (CONS y (CONS t p)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(x:A = y) /\ ~(x = z) /\ ~(x = t) /\ ~(y = z) /\ ~(y = t) /\ ~(z = t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (node_map H y) (CONS (t:A) p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN
   `face_map (edge_walkup H z) x = (y:A) /\
    face_map (edge_walkup H z) y = (t:A) /\
    node_map (edge_walkup H z) y = LAST (CONS (t:A) p) /\
    node_map (edge_walkup H z) x = (y:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_EDGE_WALKUP; FACE_MAP_EDGE_WALKUP; SWAP_ENDS] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SWAP_OTHER THEN
    ASM_MESON_TAC[NODEI; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (x:A) (CONS y (CONS t p)) /\ ~MEM (y:A) (CONS t p)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (x:A) (CONS y (CONS z (CONS t p)))` THEN
    UNDISCH_TAC `~MEM (y:A) (CONS z (CONS t p))` THEN REWRITE_TAC[MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `y:A` THEN
  ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS; list_path; clink; MEM2_CONS;
                  LAST_CLAUSES] THEN
  REWRITE_TAC[MEM] THEN MATCH_MP_TAC LIFT_PATH_E THEN ASM_REWRITE_TAC[MEM]);;

let JORDAN_STEP_F7 = prove
 (`!(H:(A)hypermap) x y z t p.
     moebius_path H (CONS x (CONS y (CONS z (CONS t p)))) /\
     face_map H x = y /\ face_map H y = z /\ node_map H x = y /\
     LAST (CONS t p) = node_map H y /\ node_map H t = z
     ==> moebius_path (face_walkup H z) (CONS x (CONS y (CONS t p)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MOEBIUS_HYP_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(x:A = y) /\ ~(x = z) /\ ~(x = t) /\ ~(y = z) /\ ~(y = t) /\ ~(z = t)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (node_map H y) (CONS (t:A) p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map H (edge_map H z) = (t:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[nodeK]; ALL_TAC] THEN
  SUBGOAL_THEN `~(x = edge_map H (z:A)) /\ ~(y = edge_map H z)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `node_map (face_walkup H z) y = LAST (CONS (t:A) p) /\
    node_map (face_walkup H z) x = (y:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_FACE_WALKUP] THEN CONJ_TAC THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_MESON_TAC[NODEI; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map (face_walkup H z) x = (y:A)` ASSUME_TAC THENL
   [REWRITE_TAC[FACE_MAP_EQ] THEN
    SIMP_TAC[EDGE_MAP_FACE_WALKUP; ASSUME `(z:A) IN dart H`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `edge_map H (node_map H y) = (x:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[faceK]; ALL_TAC] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map (face_walkup H z) y = (t:A)` ASSUME_TAC THENL
   [REWRITE_TAC[FACE_MAP_EQ] THEN
    SIMP_TAC[EDGE_MAP_FACE_WALKUP; NODE_MAP_FACE_WALKUP;
             ASSUME `(z:A) IN dart H`] THEN
    ASM_REWRITE_TAC[SWAP_ENDS] THEN
    SUBGOAL_THEN `edge_map H (node_map H z) = (y:A)` SUBST1_TAC THENL
     [ASM_MESON_TAC[faceK]; ALL_TAC] THEN
    MATCH_MP_TAC SWAP_OTHER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (x:A) (CONS y (CONS t p)) /\ ~MEM (y:A) (CONS t p)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (x:A) (CONS y (CONS z (CONS t p)))` THEN
    UNDISCH_TAC `~MEM (y:A) (CONS z (CONS t p))` THEN REWRITE_TAC[MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN EXISTS_TAC `y:A` THEN
  ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS; list_path; clink; MEM2_CONS;
                  LAST_CLAUSES] THEN
  REWRITE_TAC[MEM] THEN MATCH_MP_TAC LIFT_PATH_F THEN ASM_REWRITE_TAC[MEM]);;
(* ------------------------------------------------------------------------- *)
(* The three-dart case: a map whose edge, node and face maps are all the     *)
(* same 3-cycle has genus 1.                                                 *)
(* ------------------------------------------------------------------------- *)

let NCOMP_POS = prove
 (`!(H:(A)hypermap). ~(dart H = {}) ==> 1 <= number_of_components H`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[NCOMP_IMAGE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0; FINITE_IMAGE; FINITE_DART; IMAGE_EQ_EMPTY]);;

let ORBIT_3CYCLE = prove
 (`!(g:A->A) s x y z.
     g permutes s /\ (!w. w IN s <=> w = x \/ w = y \/ w = z) /\
     g x = y /\ g y = z /\ g z = x
     ==> !w. w IN s ==> orbit_map g w = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `w:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ORBIT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:A) IN orbit_map g w /\ g w IN orbit_map g w /\
    g(g w) IN orbit_map g w`
  MP_TAC THENL [MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]; ALL_TAC] THEN
  UNDISCH_TAC `(w:A) IN s` THEN ASM_REWRITE_TAC[SUBSET] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CARD_SET_OF_ORBITS_1 = prove
 (`!(g:A->A) s.
     ~(s = {}) /\ (!w. w IN s ==> orbit_map g w = s)
     ==> CARD(set_of_orbits s g) = 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `set_of_orbits s (g:A->A) = {s}` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[set_of_orbits; IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `u:A->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_TAC `w:A` o
        REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
      EXISTS_TAC `w:A` THEN ASM_SIMP_TAC[]];
    REWRITE_TAC[CARD_SING]]);;

let CARD_3 = prove
 (`!x y z:A. ~(x = y) /\ ~(x = z) /\ ~(y = z) ==> CARD {x,y,z} = 3`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let THREE_DART_NOT_PLANAR = prove
 (`!(H:(A)hypermap) x y z.
     (!w. w IN dart H ==> w = x \/ w = y \/ w = z) /\ x IN dart H /\
     ~(x = y) /\ ~(x = z) /\ ~(y = z) /\
     face_map H x = y /\ face_map H y = z /\
     node_map H x = y /\ node_map H y = z
     ==> ~(planar_hypermap H)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ (z:A) IN dart H` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MAPS_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `face_map H z = (x:A) /\ node_map H z = x`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> MP_TAC(SPEC `face_map H (z:A)` th) THEN
                          MP_TAC(SPEC `node_map H (z:A)` th)) THEN
    SIMP_TAC[MAPS_IN_DART; ASSUME `(z:A) IN dart H`] THEN
    UNDISCH_TAC `face_map H x = (y:A)` THEN
    UNDISCH_TAC `face_map H y = (z:A)` THEN
    UNDISCH_TAC `node_map H x = (y:A)` THEN
    UNDISCH_TAC `node_map H y = (z:A)` THEN
    UNDISCH_TAC `~(x:A = z)` THEN UNDISCH_TAC `~(y:A = z)` THEN
    MESON_TAC[FACEI; NODEI];
    ALL_TAC] THEN
  SUBGOAL_THEN `edge_map H x = (y:A) /\ edge_map H y = z /\ edge_map H z = x`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(SPECL [`H:(A)hypermap`; t] faceK))
     [`x:A`; `y:A`; `z:A`] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:A. w IN dart H <=> w = x \/ w = y \/ w = z`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `number_of_edges (H:(A)hypermap) = 1 /\
                number_of_nodes H = 1 /\ number_of_faces H = 1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[number_of_edges; number_of_nodes; number_of_faces;
                edge_set; node_set; face_set] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC CARD_SET_OF_ORBITS_1 THEN
    (CONJ_TAC THENL
      [ASM_MESON_TAC[MEMBER_NOT_EMPTY];
       MATCH_MP_TAC ORBIT_3CYCLE THEN
       MAP_EVERY EXISTS_TAC [`x:A`; `y:A`; `z:A`] THEN
       REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
       REWRITE_TAC[HYPERMAP_LEMMA]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(dart(H:(A)hypermap)) = 3` ASSUME_TAC THENL
   [SUBGOAL_THEN `dart H = {x:A,y,z}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_3 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `H:(A)hypermap` NCOMP_POS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[planar_hypermap; genus; euler_lhs; euler_rhs] THEN
  UNDISCH_TAC `CARD(dart(H:(A)hypermap)) = 3` THEN
  UNDISCH_TAC `number_of_edges (H:(A)hypermap) = 1` THEN
  UNDISCH_TAC `number_of_nodes (H:(A)hypermap) = 1` THEN
  UNDISCH_TAC `number_of_faces (H:(A)hypermap) = 1` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The inductive step and the theorem.                                       *)
(* ------------------------------------------------------------------------- *)

let JORDAN_STEP = prove
 (`!H:(A)hypermap.
     planar_hypermap H /\
     (!z. z IN dart H ==> jordan (edge_walkup H z)) /\
     (!z. z IN dart H ==> jordan (node_walkup H z)) /\
     (!z. z IN dart H ==> jordan (face_walkup H z))
     ==> jordan H`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[jordan] THEN
  X_GEN_TAC `q:(A)list` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `q:(A)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `p:(A)list` SUBST_ALL_TAC))) THENL
   [ASM_MESON_TAC[moebius_path]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOEBIUS_PATH_DART) THEN
  SUBGOAL_THEN `!w:A. w IN dart H ==> MEM w (CONS x p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[JORDAN_STEP_E1; jordan]; ALL_TAC] THEN
  MP_TAC(ISPEC `p:(A)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `p1:(A)list` SUBST_ALL_TAC))) THENL
   [ASM_MESON_TAC[MOEBIUS_PATH_CONS; MEM2_NIL]; ALL_TAC] THEN
  MP_TAC(ISPEC `p1:(A)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `p2:(A)list` SUBST_ALL_TAC))) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOEBIUS_PATH_CONS]) THEN
    REWRITE_TAC[MEM2_CONS; MEM2_NIL; MEM; LAST_CLAUSES;
                PAIRWISE_DISTINCT_CONS] THEN
    MESON_TAC[NODE_INV_NODE; NODEI];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart H /\ (z:A) IN dart H` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `clink H x y /\ clink H y z /\ list_path (clink H) z p2 /\
    ~(x:A = y) /\ ~(x = z) /\ ~(y = z)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOEBIUS_PATH_CONS]) THEN
    REWRITE_TAC[list_path; PAIRWISE_DISTINCT_CONS; MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map H x = (y:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `clink H (x:A) y` THEN REWRITE_TAC[clink] THEN
    ASM_MESON_TAC[JORDAN_STEP_E2; jordan];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map H y = (z:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `clink H (y:A) z` THEN REWRITE_TAC[clink] THEN
    ASM_MESON_TAC[JORDAN_STEP_F3; jordan];
    ALL_TAC] THEN
  SUBGOAL_THEN `LAST (CONS z p2) = node_map H (y:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[JORDAN_STEP_E4; jordan]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map H x = (y:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[JORDAN_STEP_N5; jordan]; ALL_TAC] THEN
  MP_TAC(ISPEC `p2:(A)list` list_CASES) THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `t:A` (X_CHOOSE_THEN `p3:(A)list` SUBST_ALL_TAC))) THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`; `y:A`; `z:A`]
      THREE_DART_NOT_PLANAR) THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[LAST_CLAUSES]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST_CLAUSES]) THEN
  UNDISCH_TAC `list_path (clink H) (z:A) (CONS t p3)` THEN
  REWRITE_TAC[list_path; clink] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[JORDAN_STEP_F7; jordan];
    ASM_MESON_TAC[JORDAN_STEP_E6; jordan]]);;

let PLANAR_JORDAN = prove
 (`!H:(A)hypermap. planar_hypermap H ==> jordan H`,
  SUBGOAL_THEN
   `!n (H:(A)hypermap). CARD(dart H) = n /\ planar_hypermap H ==> jordan H`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `H:(A)hypermap` THEN STRIP_TAC THEN
  MATCH_MP_TAC JORDAN_STEP THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
    [ASM_MESON_TAC[CARD_EQ_0; FINITE_DART; MEMBER_NOT_EMPTY;
                   ARITH_RULE `~(n = 0) ==> n - 1 < n`];
     DISCH_THEN MATCH_MP_TAC]) THEN
  ASM_SIMP_TAC[CARD_DART_EDGE_WALKUP; CARD_DART_NODE_WALKUP;
               CARD_DART_FACE_WALKUP; PLANAR_EDGE_WALKUP;
               PLANAR_NODE_WALKUP; PLANAR_FACE_WALKUP]);;
(* ------------------------------------------------------------------------- *)
(* The Euler formula with an even defect (Gonthier's even_genusP): the       *)
(* edge Walkup transform changes euler_lhs - euler_rhs by an even amount.    *)
(* ------------------------------------------------------------------------- *)

let FCARD_SWAP_REVERSE = prove
 (`!(f:A->A) s a b.
    FINITE s /\ f permutes s /\ a IN s /\ b IN s
    ==> CARD(set_of_orbits s (swap(a,b) o f))
        <= CARD(set_of_orbits s f) + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`swap(a:A,b) o (f:A->A)`; `s:A->bool`; `a:A`; `b:A`]
    FCARD_SWAP_BOUND) THEN
  REWRITE_TAC[o_ASSOC; SWAP_IDEMPOTENT; I_O_ID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PERMUTES_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PERMUTES_SWAP THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE]);;

(* Upper bound: ne(edge_walkup) <= ne + 1 when ~glink                        *)
let FCARD_EDGE_WALKUP_UPPER = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ ~glink H z z
    ==> number_of_edges(edge_walkup H z) <= number_of_edges H + 1`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP EDGE_ORBITS_WALKUP) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FCARD_SWAP_REVERSE THEN
  ASM_REWRITE_TAC[FINITE_DELETE; FINITE_DART]);;

(* Exact edge counts in cross/non-cross cases                                *)
let FIXED_COUNT = prove
 (`!(H:(A)hypermap) z. z IN dart H /\ glink H z z /\ ~dart_degenerate H z
    ==> (if edge_map H z = z then 1 else 0) +
        (if node_map H z = z then 1 else 0) +
        (if face_map H z = z then 1 else 0) = 1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP DEGENERATE_FROM_TWO_FIXED
     (CONJUNCT1 th)) THEN MP_TAC th) THEN
  REWRITE_TAC[GLINK_SELF_EQ; dart_degenerate] THEN
  MAP_EVERY ASM_CASES_TAC
   [`edge_map H z = z:A`; `node_map H z = z:A`; `face_map H z = z:A`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let EULER_STEP = prove
 (`!(H:(A)hypermap) z. z IN dart H
    ==> ?k. euler_lhs H + euler_rhs(edge_walkup H z) =
            euler_lhs(edge_walkup H z) + euler_rhs H + 2 * k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= CARD(dart(H:(A)hypermap))` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD_EQ_0; FINITE_DART; MEMBER_NOT_EMPTY;
                  ARITH_RULE `~(n = 0) ==> 1 <= n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] CARD_DART_EDGE_WALKUP) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_NODE_EDGE_WALKUP) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_FACE_EDGE_WALKUP) THEN
  ASM_REWRITE_TAC[euler_lhs; euler_rhs] THEN
  ASM_CASES_TAC `glink H (z:A) z` THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_GLINK) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_WALKUP_LE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `dart_degenerate H (z:A)` THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_DEGENERATE) THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[dart_degenerate]) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      EXISTS_TAC `number_of_components H -
                  number_of_components(edge_walkup H (z:A)) - 1` THEN
      ASM_ARITH_TAC;
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_NON_DEGENERATE_GE) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FIXED_COUNT) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY ASM_CASES_TAC
       [`edge_map H z = z:A`; `node_map H z = z:A`; `face_map H z = z:A`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN EXISTS_TAC `0` THEN
      ASM_ARITH_TAC];
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NOT_GLINK_SELF) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~dart_degenerate H (z:A)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[dart_degenerate]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_NON_DEGENERATE_GE) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `cross_edge H (z:A)` THENL
     [MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_CROSS) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_WALKUP_UPPER) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_NON_GLINK_BOUND) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      EXISTS_TAC `(number_of_components H + 1) -
                  number_of_components(edge_walkup H (z:A))` THEN
      ASM_ARITH_TAC;
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_NON_CROSS) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] FCARD_EDGE_NON_GLINK_BOUND) THEN
      MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] NCOMP_NON_GLINK_NON_CROSS) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN EXISTS_TAC `0` THEN
      ASM_ARITH_TAC]]);;

let EVEN_GENUS = prove
 (`!H:(A)hypermap. even_genus H`,
  GEN_TAC THEN REWRITE_TAC[even_genus; genus] THEN
  MATCH_MP_TAC EVEN_GENUS_CONCLUDE THEN
  SPEC_TAC(`H:(A)hypermap`,`H:(A)hypermap`) THEN
  SUBGOAL_THEN
   `!n (H:(A)hypermap). CARD(dart H) = n
                        ==> ?g. euler_lhs H = 2 * g + euler_rhs H`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `H:(A)hypermap` THEN DISCH_TAC THEN
  ASM_CASES_TAC `dart(H:(A)hypermap) = {}` THENL
   [EXISTS_TAC `0` THEN UNDISCH_TAC `CARD(dart(H:(A)hypermap)) = n` THEN
    ASM_REWRITE_TAC[euler_lhs; euler_rhs; number_of_components;
                    set_of_components; number_of_edges; number_of_nodes;
                    number_of_faces; edge_set; node_set; face_set;
                    set_of_orbits] THEN
    SIMP_TAC[SET_RULE `{(f:A->B) x | x IN {}} = {}`; CARD_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `z:A` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[CARD_EQ_0; FINITE_DART; MEMBER_NOT_EMPTY;
                  ARITH_RULE `~(n = 0) ==> n - 1 < n`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `edge_walkup H (z:A)`) THEN
  ASM_SIMP_TAC[CARD_DART_EDGE_WALKUP] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:num`) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `z:A`] EULER_STEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  EXISTS_TAC `g + k:num` THEN ASM_ARITH_TAC);;

let CUBIC_EULER = prove
 (`!H:(A)hypermap. plain_cubic_connected H /\ ~(dart H = {})
    ==> (planar_hypermap H <=> 6 * number_of_faces H = CARD(dart H) + 12)`,
  GEN_TAC THEN REWRITE_TAC[plain_cubic_connected; plain_cubic] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `H:(A)hypermap` EVEN_GENUS) THEN
  REWRITE_TAC[even_genus; planar_hypermap] THEN
  MP_TAC(ISPEC `H:(A)hypermap` PLAIN_DART_CARD) THEN
  MP_TAC(ISPEC `H:(A)hypermap` CUBIC_DART_CARD) THEN
  MP_TAC(ISPEC `H:(A)hypermap` CONNECTED_NCOMP) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[euler_lhs; euler_rhs] THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY ABBREV_TAC
    [`nc = number_of_components (H:(A)hypermap)`;
     `ne = number_of_edges (H:(A)hypermap)`;
     `nn = number_of_nodes (H:(A)hypermap)`;
     `nf = number_of_faces (H:(A)hypermap)`;
     `d = CARD(dart (H:(A)hypermap))`;
     `g = genus (H:(A)hypermap)`] THEN
  SUBGOAL_THEN `d = 2 * ne:num` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `2 * nc + 2 * ne = 2 * g + ne + nn + nf:num` THEN
  UNDISCH_TAC `nc = 1:num` THEN
  UNDISCH_TAC `3 * nn = 2 * ne:num` THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Contour paths along faces and nodes; explicit orbit lists (iterlist).     *)
(* ------------------------------------------------------------------------- *)

let CNODE_REFL = prove
 (`!(H:(A)hypermap) a. cnode H a a`,
  REWRITE_TAC[cnode; node; IN_ORBIT_MAP_REFL]);;

let CNODE_ITER = prove
 (`!(H:(A)hypermap) n a. cnode H a (ITER n (node_map H) a)`,
  REWRITE_TAC[cnode; node; orbit_map; IN_ELIM_THM] THEN MESON_TAC[]);;

let CNODE_CLINK_PATH_ITER = prove
 (`!(H:(A)hypermap) n a.
    ?m. list_path (clink H) (ITER n (node_map H) a) m /\
        LAST(CONS (ITER n (node_map H) a) m) = a /\
        ALL (\y. cnode H a y) (CONS (ITER n (node_map H) a) m)`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [EXISTS_TAC `[]:(A)list` THEN
    REWRITE_TAC[ITER; list_path; LAST; ALL; CNODE_REFL]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:(A)list` STRIP_ASSUME_TAC o SPEC `a:A`) THEN
  EXISTS_TAC `CONS (ITER n (node_map H) a:A) m` THEN
  ASM_REWRITE_TAC[ITER; list_path; LAST_CLAUSES; CLINKN; ALL] THEN
  REWRITE_TAC[GSYM ITER; CNODE_ITER]);;

let CFACE_RIGHT_FACE = prove
 (`!(H:(A)hypermap) x t.
     x IN dart H ==> (cface H t (face_map H x) <=> cface H t x)`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

let CFACE_LEFT_FACE = prove
 (`!(H:(A)hypermap) x w.
     x IN dart H ==> (cface H (face_map H x) w <=> cface H x w)`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

let LIST_PATH_ITERLIST = prove
 (`!(R:A->A->bool) f.
     (!y. R y (f y)) ==> !n x. list_path R x (iterlist n f x)`,
  GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN GEN_TAC THEN
  REWRITE_TAC[iterlist; list_path] THEN ASM_REWRITE_TAC[]);;

let LAST_ITERLIST = prove
 (`!(f:A->A) n x. LAST(CONS x (iterlist n f x)) = ITER n f x`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[iterlist; LAST_CLAUSES; ITER_ALT]);;

let MEM_ITERLIST = prove
 (`!(f:A->A) n x y.
     MEM y (iterlist n f x) <=> ?k. 1 <= k /\ k <= n /\ y = ITER k f x`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  ASM_REWRITE_TAC[iterlist; MEM] THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN ARITH_TAC; ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THENL
     [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[ITER_1] THEN ARITH_TAC;
      EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[ITER_ALT] THEN ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `k = 1` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[ITER_1];
      DISJ2_TAC THEN EXISTS_TAC `k - 1` THEN
      ASM_SIMP_TAC[GSYM(CONJUNCT2 ITER_ALT);
                   ARITH_RULE `1 <= k ==> SUC(k - 1) = k`] THEN
      ASM_ARITH_TAC]]);;

let LENGTH_ITERLIST = prove
 (`!(f:A->A) n x. LENGTH(iterlist n f x) = n`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[iterlist; LENGTH]);;

let ORBIT_AS_ITERLIST = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> !t. t IN orbit_map f x <=>
            MEM t (CONS x (iterlist (orbit_size f x - 1) f x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MEM; MEM_ITERLIST; ORBIT_MAP_ITER] THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ITER_ORBIT_SIZE) THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[] THEN SPEC_TAC(`orbit_size (f:A->A) x`,`d:num`) THEN
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    MP_TAC(SPECL [`f:A->A`; `x:A`; `d:num`; `n:num`] ITER_MOD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `n MOD d = 0` THEN ASM_REWRITE_TAC[ITER] THEN
    DISJ2_TAC THEN EXISTS_TAC `n MOD d` THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `d:num`] MOD_LT_EQ) THEN ASM_ARITH_TAC;
    MESON_TAC[ITER]]);;

let FACE_CYCLE_MEM = prove
 (`!(H:(A)hypermap) x. x IN dart H
    ==> !t. cface H x t <=>
            MEM t (CONS x (iterlist (orbit_size (face_map H) x - 1)
                                    (face_map H) x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cface; face] THEN
  MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`; `x:A`]
    ORBIT_AS_ITERLIST) THEN
  ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let ORBIT_LIST_PAIRWISE = prove
 (`!(f:A->A) s x. FINITE s /\ f permutes s /\ x IN s
    ==> PAIRWISE (\a b. ~(a = b))
                 (CONS x (iterlist (orbit_size f x - 1) f x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM HAS_SIZE_SET_OF_LIST] THEN
  SUBGOAL_THEN
   `set_of_list (CONS x (iterlist (orbit_size f x - 1) f x)) =
    orbit_map (f:A->A) x`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SET_OF_LIST] THEN
    X_GEN_TAC `t:A` THEN
    MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_AS_ITERLIST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `t:A`) THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE; GSYM orbit_size] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_FINITE) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LENGTH; LENGTH_ITERLIST] THEN
    MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `x:A`] ORBIT_SIZE_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let ITERLIST_ADD = prove
 (`!(f:A->A) k1 k2 x.
     iterlist (k1 + k2) f x =
     APPEND (iterlist k1 f x) (iterlist k2 f (ITER k1 f x))`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; iterlist; APPEND; ITER_ALT]);;

let FBAND_SING = prove
 (`!(H:(A)hypermap) a x. fband H [a] x <=> cface H x a`,
  REWRITE_TAC[fband; EX] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Paths that follow a function (f a = b, or b = g a, at each step): orbits  *)
(* as lists.                                                                 *)
(* ------------------------------------------------------------------------- *)

let LIST_PATH_F_MEM = prove
 (`!f (a:A) r. list_path (\x y. f x = y) a r
     ==> !y. MEM y (CONS a r) ==> y = LAST (CONS a r) \/ MEM (f y) r`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[list_path; MEM; LAST];
    REWRITE_TAC[list_path; MEM] THEN SIMP_TAC[LAST_CONS_NE; NOT_CONS_NIL] THEN
    ASM_MESON_TAC[MEM]]);;

let LIST_PATH_MEM_ORBIT = prove
 (`!f (a:A) r. list_path (\x y. f x = y) a r
    ==> (!y. MEM y r ==> y IN orbit_map f a)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_path; MEM] THEN
  ASM_MESON_TAC[ORBIT_MAP_SUCC; IN_ORBIT_MAP_REFL]);;

(* The same paths written with the equation the other way round.            *)
let GPATH_EQ = prove
 (`!g:A->A. (\a b. b = g a) = (\a b. g a = b)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let GPATH_MEM_ORBIT = prove
 (`!(g:A->A) l x.
     list_path (\a b. b = g a) x l
     ==> !y. MEM y (CONS x l) ==> y IN orbit_map g x`,
  REWRITE_TAC[GPATH_EQ; MEM] THEN
  MESON_TAC[LIST_PATH_MEM_ORBIT; IN_ORBIT_MAP_REFL]);;

let GPATH_NEXT = prove
 (`!(g:A->A) l x w.
     list_path (\a b. b = g a) x l /\ MEM w (CONS x l)
     ==> w = LAST (CONS x l) \/ MEM (g w) l`,
  REWRITE_TAC[GPATH_EQ] THEN MESON_TAC[LIST_PATH_F_MEM]);;

let GPATH_CYCLE_MEM = prove
 (`!(g:A->A) l x.
     list_path (\a b. b = g a) x l /\ g (LAST (CONS x l)) = x
     ==> !y. y IN orbit_map g x ==> MEM y (CONS x l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[ORBIT_MAP_ITER] THEN
  SUBGOAL_THEN `!n. MEM (ITER n (g:A->A) x) (CONS x l)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER; MEM] THEN
  MP_TAC(ISPECL [`g:A->A`; `l:(A)list`; `x:A`; `ITER n (g:A->A) x`]
    GPATH_NEXT) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(g:A->A) (LAST (CONS x l)) = x` THEN
  MESON_TAC[]);;

let GPATH_PRED = prove
 (`!(g:A->A) l x w.
     list_path (\a b. b = g a) x l /\ MEM w l
     ==> ?v. MEM v (BUTLAST (CONS x l)) /\ w = g v`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_path; MEM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[BUTLAST_CLAUSES; NOT_CONS_NIL; MEM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  DISCH_THEN SUBST_ALL_TAC THENL
   [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`(g:A->A) x`; `w:A`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]);;

let GPATH_ITERLIST = prove
 (`!(g:A->A) n x. list_path (\a b. b = g a) x (iterlist n g x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`\a b. b = (g:A->A) a`; `g:A->A`] LIST_PATH_ITERLIST) THEN
  REWRITE_TAC[]);;

let ORBIT_GPATH = prove
 (`!(g:A->A) x y.
     y IN orbit_map g x
     ==> ?l. list_path (\a b. b = g a) x l /\ LAST (CONS x l) = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ORBIT_MAP_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  EXISTS_TAC `iterlist n (g:A->A) x` THEN
  REWRITE_TAC[LAST_ITERLIST; GPATH_ITERLIST]);;

let FPATH_CLINK = prove
 (`!(H:(A)hypermap) x l.
     list_path (\a b. b = face_map H a) x l ==> list_path (clink H) x l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `\a b. b = face_map (H:(A)hypermap) a` THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[CLINKF]);;

let CFACE_CLINK_PATH = prove
 (`!(H:(A)hypermap) a b.
    cface H a b
    ==> ?m. list_path (clink H) a m /\ LAST(CONS a m) = b /\
            ALL (\y. cface H a y) (CONS a m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  EXISTS_TAC `iterlist n (face_map H) (a:A)` THEN
  REWRITE_TAC[LAST_ITERLIST; GSYM ALL_MEM; MEM; MEM_ITERLIST] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FPATH_CLINK THEN REWRITE_TAC[GPATH_ITERLIST];
    MESON_TAC[ITER]]);;

let NOT_MEM_LAST_BUTLAST = prove
 (`!l:(A)list. PAIRWISE (\a b. ~(a = b)) l /\ ~(l = [])
               ==> ~(MEM (LAST l) (BUTLAST l))`,
  MESON_TAC[MEM_BUTLAST_NEQ_LAST]);;

let LAST_CONS_APPEND_GEN = prove
 (`!(a:A) l m. LAST (CONS a (APPEND l m)) = LAST (CONS (LAST (CONS a l)) m)`,
  REPEAT GEN_TAC THEN MP_TAC(ISPEC `m:(A)list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND_NIL; LAST_CLAUSES] THEN
  ASM_SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL]);;

let BUTLAST_APPEND_CONS = prove
 (`!(l:(A)list) h m.
     BUTLAST (APPEND l (CONS h m)) = APPEND l (BUTLAST (CONS h m))`,
  REWRITE_TAC[BUTLAST_APPEND; NOT_CONS_NIL]);;

let FACE_SIMPLE_APPEND = prove
 (`!(H:(A)hypermap) l m. face_simple H (APPEND l m) ==> face_simple H l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; face_simple; FBAND_APPEND] THEN ASM_MESON_TAC[]);;

(* The face cycle of a dart x, listed from face x round to x.                *)
let FACE_CYCLE_LIST = prove
 (`!(H:(A)hypermap) x. x IN dart H
    ==> ?l. list_path (\a b. b = face_map H a) (face_map H x) l /\
            LAST (CONS (face_map H x) l) = x /\
            PAIRWISE (\a b. ~(a = b)) (CONS (face_map H x) l) /\
            (!t. MEM t (CONS (face_map H x) l) ==> cface H x t) /\
            (!t. cface H x t ==> MEM t (CONS (face_map H x) l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `face_map H (x:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[MAPS_IN_DART]; ALL_TAC] THEN
  EXISTS_TAC `iterlist (orbit_size (face_map H) (face_map H x) - 1)
                       (face_map H) (face_map H (x:A))` THEN
  let memtac =
    SUBGOAL_THEN
     `!t. MEM t (CONS (face_map H x)
           (iterlist (orbit_size (face_map H) (face_map H x) - 1)
                     (face_map H) (face_map H (x:A)))) <=> cface H x t`
     (fun th -> MESON_TAC[th]) THEN
    GEN_TAC THEN MP_TAC(ISPECL [`H:(A)hypermap`; `face_map H (x:A)`]
      FACE_CYCLE_MEM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_SIMP_TAC[CFACE_LEFT_FACE] in
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GPATH_ITERLIST];
    REWRITE_TAC[LAST_ITERLIST] THEN
    MATCH_MP_TAC(SPEC `H:(A)hypermap` FACEI) THEN
    MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`;
                   `face_map H (x:A)`] ITER_ORBIT_SIZE) THEN
    MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`;
                   `face_map H (x:A)`] ORBIT_SIZE_POS) THEN
    ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
    ABBREV_TAC `m = orbit_size (face_map H) (face_map H (x:A))` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `m = SUC(m - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ITER; SUC_SUB1]];
    MATCH_MP_TAC ORBIT_LIST_PAIRWISE THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES];
    memtac; memtac]);;

(* The node cycle of y, from y round to face (edge y) = node^-1 y.           *)
let NODE_CYCLE_PATH = prove
 (`!(H:(A)hypermap) y. y IN dart H
    ==> ?q. list_path (\a b. b = node_map H a) y q /\
            LAST (CONS y q) = face_map H (edge_map H y)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `iterlist (orbit_size (node_map H) y - 1) (node_map H) (y:A)` THEN
  REWRITE_TAC[GPATH_ITERLIST; LAST_ITERLIST] THEN
  MATCH_MP_TAC(SPEC `H:(A)hypermap` NODEI) THEN REWRITE_TAC[edgeK] THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `y:A`]
    ITER_ORBIT_SIZE) THEN
  MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `y:A`]
    ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
  SPEC_TAC(`orbit_size (node_map H) (y:A)`,`m:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_REFL; ITER; SUC_SUB1]);;
(* ------------------------------------------------------------------------- *)
(* Euler_tree.  If no dart of the edge cycle of x is degenerate or links to  *)
(* another edge cycle, a Moebius path is built from                          *)
(*  1. a maximal face-simple edge arc x' :: p1 whose last dart lies on the   *)
(*     face of node (face x');                                               *)
(*  2. a contour face x' :: q1 along the arc ending at node (face x'), which *)
(*     F-links enter only from the last dart of the arc or from inside;      *)
(*  3. an edge arc from face x' to node (face x') avoiding that last dart;   *)
(*  4. walking back along this arc, the contour is extended until it closes  *)
(*     up with a reverse N-link.                                             *)
(* ------------------------------------------------------------------------- *)

let EULER_TREE_ARC = prove
 (`!(H:(A)hypermap) p x.
     list_path (\a b. b = edge_map H a) x p /\ ~(face_simple H (CONS x p))
     ==> ?x' p1. x' IN orbit_map (edge_map H) x /\
                 list_path (\a b. b = edge_map H a) x' p1 /\
                 face_simple H (CONS x' p1) /\
                 cface H (LAST (CONS x' p1)) (node_map H (face_map H x'))`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_path] THENL
   [REWRITE_TAC[face_simple; FBAND_NIL]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
    ASSUME_TAC) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  ASM_CASES_TAC `face_simple H (CONS (edge_map H x) (t:(A)list))` THENL
   [SUBGOAL_THEN `fband H (CONS (edge_map H x) t) (x:A)` MP_TAC THENL
     [UNDISCH_TAC
       `~face_simple (H:(A)hypermap) (CONS x (CONS (edge_map H x) t))` THEN
      ASM_REWRITE_TAC[face_simple];
      ALL_TAC] THEN
    REWRITE_TAC[FBAND_MEM_IFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\a b. b = edge_map (H:(A)hypermap) a`; `t:(A)list`;
                   `edge_map H (x:A)`; `b:A`] LIST_PATH_SPLIT_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m1:(A)list` (X_CHOOSE_THEN `m2:(A)list`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`edge_map H (x:A)`; `m1:(A)list`] THEN
    ASM_REWRITE_TAC[edgeK] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL];
      MATCH_MP_TAC FACE_SIMPLE_APPEND THEN EXISTS_TAC `m2:(A)list` THEN
      UNDISCH_TAC `face_simple H (CONS (edge_map H x) (t:(A)list))` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `edge_map H (x:A)`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ORBIT_MAP_TRANS_GEN THEN EXISTS_TAC `edge_map H (x:A)` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[ORBIT_MAP_STEP; IN_ORBIT_MAP_REFL]]);;

let EULER_TREE_CONTOUR = prove
 (`!(H:(A)hypermap) z p1 x.
     x IN dart H /\ list_path (\a b. b = edge_map H a) x p1 /\
     face_simple H (CONS x p1) /\ cface H (LAST (CONS x p1)) z
     ==> ?q1. list_path (clink H) (face_map H x) q1 /\
              LAST (CONS (face_map H x) q1) = z /\
              PAIRWISE (\a b. ~(a = b)) (CONS (face_map H x) q1) /\
              (!t. MEM t (CONS (face_map H x) q1)
                   ==> ?b. MEM b (CONS x p1) /\ cface H t b) /\
              (!y. MEM (face_map H y) (CONS (face_map H x) q1)
                   ==> y = LAST (CONS x p1) \/
                       MEM y (BUTLAST (CONS (face_map H x) q1)))`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_path] THENL
   [X_GEN_TAC `x:A` THEN REWRITE_TAC[LAST_CLAUSES] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] FACE_CYCLE_LIST) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:(A)list` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `MEM (z:A) (CONS (face_map H x) l)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\a b. b = face_map (H:(A)hypermap) a`; `l:(A)list`;
                   `face_map H (x:A)`; `z:A`] LIST_PATH_SPLIT_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m1:(A)list` (X_CHOOSE_THEN `m2:(A)list`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `m1:(A)list` THEN
    SUBGOAL_THEN `!t:A. MEM t (CONS (face_map H x) m1) ==> cface H x t`
    ASSUME_TAC THENL [ASM_SIMP_TAC[MEM_APPEND]; ALL_TAC] THEN
    ASM_SIMP_TAC[FPATH_CLINK] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `PAIRWISE (\a b. ~(a = b))
                     (APPEND (CONS (face_map H x) m1) (m2:(A)list))` THEN
      REWRITE_TAC[PAIRWISE_DISTINCT_APPEND] THEN SIMP_TAC[];
      X_GEN_TAC `u:A` THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN CFACE_TAC[];
      X_GEN_TAC `y:A` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THENL
       [DISJ1_TAC THEN UNDISCH_TAC `face_map H y = face_map H (x:A)` THEN
        MESON_TAC[FACEI];
        DISJ2_TAC THEN
        MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `m1:(A)list`;
                       `face_map H (x:A)`; `face_map H (y:A)`] GPATH_PRED) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `y:A = v` SUBST1_TAC THENL
         [MATCH_MP_TAC(SPEC `H:(A)hypermap` FACEI) THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[LAST_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [face_simple]) THEN
  SUBGOAL_THEN `edge_map H (x:A) IN dart H` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] MAPS_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_map H (x:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x:A`] FACE_CYCLE_LIST) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!a:A. MEM a (CONS (face_map H x) l)
          ==> ~(MEM a (CONS (face_map H (edge_map H x)) q2))`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:A` THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `?b:A. MEM b (CONS (edge_map H x) t) /\ cface H a b`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC) THEN CFACE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND l (CONS (face_map H (edge_map H x)) (q2:(A)list))` THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); MEM_APPEND; BUTLAST_APPEND_CONS] THEN
  REWRITE_TAC[CONJUNCT2 APPEND] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LIST_PATH_APPEND; FPATH_CLINK; list_path; clink; edgeK];
    ASM_SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL];
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND); PAIRWISE_DISTINCT_APPEND] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `u:A` THEN REWRITE_TAC[GSYM(CONJUNCT2 APPEND); MEM_APPEND] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `x:A` THEN CFACE_TAC[];
      SUBGOAL_THEN `?b:A. MEM b (CONS (edge_map H x) t) /\ cface H u b`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[MEM] THEN MESON_TAC[]];
    X_GEN_TAC `y:A` THEN REWRITE_TAC[GSYM(CONJUNCT2 APPEND); MEM_APPEND] THEN
    STRIP_TAC THENL
     [DISJ2_TAC THEN DISJ1_TAC THEN
      UNDISCH_TAC `MEM (face_map H y) (CONS (face_map H x) (l:(A)list))` THEN
      GEN_REWRITE_TAC LAND_CONV [MEM] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `y:A = x` SUBST1_TAC THENL
         [UNDISCH_TAC `face_map H y = face_map H (x:A)` THEN
          MESON_TAC[FACEI];
          MP_TAC(ISPECL [`face_map H (x:A)`; `l:(A)list`]
            LIST_PATH_MEM_LAST) THEN
          ASM_REWRITE_TAC[]];
        MP_TAC(ISPECL [`face_map (H:(A)hypermap)`; `l:(A)list`;
                       `face_map H (x:A)`; `face_map H (y:A)`] GPATH_PRED) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `y:A = v` SUBST1_TAC THENL
         [MATCH_MP_TAC(SPEC `H:(A)hypermap` FACEI) THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC MEM_BUTLAST THEN ASM_REWRITE_TAC[]]];
      SUBGOAL_THEN
       `y = LAST (CONS (edge_map H x) t) \/
        MEM y (BUTLAST (CONS (face_map H (edge_map H x)) (q2:(A)list)))`
      MP_TAC THENL [ASM_SIMP_TAC[]; MESON_TAC[]]]]);;
let LIST_PATH_SUFFIX = prove
 (`!(e:A->A->bool) m x v.
     PAIRWISE (\a b. ~(a = b)) (CONS x m) /\ MEM v m /\ list_path e x m
     ==> ?m2. list_path e v m2 /\ LAST (CONS v m2) = LAST (CONS x m) /\
              ~(MEM x m2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIRWISE_DISTINCT_CONS] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e:A->A->bool`; `m:(A)list`; `x:A`; `v:A`]
    LIST_PATH_SPLIT_AT_TAIL) THEN
  ASM_REWRITE_TAC[MEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:(A)list` (X_CHOOSE_THEN `m2:(A)list`
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  MP_TAC(ISPEC `m1:(A)list` list_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[APPEND; CONS_11] THEN STRIP_TAC THEN
  EXISTS_TAC `m2:(A)list` THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[];
    UNDISCH_TAC `~MEM (x:A) m` THEN ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN
    ASM_SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL] THEN MESON_TAC[]]);;

(* Extending the contour a0 :: q1 (ending at node a0) backwards along a node *)
(* cycle: from a path q2 from node a0 to b avoiding the contour, with face b *)
(* off the contour, we reach every dart v of the node cycle of face b from   *)
(* node a0 avoiding the contour (otherwise a Moebius path would exist).      *)
let EULER_TREE_INNER = prove
 (`!(H:(A)hypermap) a0 q1 b q2.
     jordan H /\
     list_path (clink H) a0 q1 /\ LAST (CONS a0 q1) = node_map H a0 /\
     PAIRWISE (\a b. ~(a = b)) (CONS a0 q1) /\
     list_path (clink H) (node_map H a0) q2 /\
     LAST (CONS (node_map H a0) q2) = b /\
     (!t. MEM t q2 ==> ~(MEM t (CONS a0 q1))) /\
     ~(MEM (face_map H b) (CONS a0 q1))
     ==> !q v. list_path (\a c. c = node_map H a) v q /\
               LAST (CONS v q) = face_map H b
               ==> ~(v = node_map H a0) /\
                   ?q3. list_path (clink H) (node_map H a0) q3 /\
                        LAST (CONS (node_map H a0) q3) = v /\
                        (!t. MEM t q3 ==> ~(MEM t (CONS a0 q1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (node_map H a0) (CONS (a0:A) q1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIST_PATH_MEM_LAST]; ALL_TAC] THEN
  LIST_INDUCT_TAC THEN X_GEN_TAC `v:A` THEN
  REWRITE_TAC[list_path; LAST_CLAUSES] THENL
   [REWRITE_TAC[LAST_CLAUSES] THEN DISCH_THEN SUBST_ALL_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~(MEM (face_map H b) (CONS (a0:A) q1))` THEN
      UNDISCH_TAC `MEM (node_map H a0) (CONS (a0:A) q1)` THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `APPEND q2 [face_map H (b:A)]` THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path; CLINKF; LAST_CONS_SNOC;
                    MEM_APPEND; MEM] THEN
    UNDISCH_TAC `!t:A. MEM t q2 ==> ~(MEM t (CONS a0 q1))` THEN
    UNDISCH_TAC `~(MEM (face_map H b) (CONS (a0:A) q1))` THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
    ASSUME_TAC) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `node_map H (v:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q3:(A)list` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`clink (H:(A)hypermap)`; `node_map H (a0:A)`; `q3:(A)list`]
    LIST_PATH_SHORTEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q4:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t:A. MEM t q4 ==> ~(MEM t (CONS a0 q1))` ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `MEM (u:A) (CONS (node_map H a0) q3)` MP_TAC THENL
     [ASM_SIMP_TAC[MEM]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [MEM] THEN STRIP_TAC THENL
     [UNDISCH_TAC `MEM (u:A) q4` THEN
      UNDISCH_TAC
       `PAIRWISE (\a b. ~(a = b)) (CONS (node_map H a0) (q4:(A)list))` THEN
      ASM_REWRITE_TAC[PAIRWISE_DISTINCT_CONS] THEN MESON_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(MEM (v:A) (CONS a0 q1))` ASSUME_TAC THENL
   [REWRITE_TAC[MEM; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(node_map H v = node_map H (a0:A))` THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `jordan (H:(A)hypermap)` THEN
    REWRITE_TAC[jordan] THEN
    DISCH_THEN(MP_TAC o SPEC `CONS (a0:A) (APPEND q1 q4)`) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOEBIUS_PATH_INTRO THEN
    EXISTS_TAC `v:A` THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 APPEND); PAIRWISE_DISTINCT_APPEND] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC
         `PAIRWISE (\a b. ~(a = b)) (CONS (node_map H a0) (q4:(A)list))` THEN
        REWRITE_TAC[PAIRWISE_DISTINCT_CONS] THEN SIMP_TAC[];
        UNDISCH_TAC `!t:A. MEM t q4 ==> ~(MEM t (CONS a0 q1))` THEN
        MESON_TAC[]];
      ASM_REWRITE_TAC[LIST_PATH_APPEND];
      REWRITE_TAC[LAST_CONS_APPEND_GEN] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEM2_APPEND_R THEN
      SUBGOAL_THEN `node_map H a0 = LAST (q1:(A)list)` SUBST1_TAC THENL
       [UNDISCH_TAC `MEM (v:A) q1` THEN
        UNDISCH_TAC `LAST (CONS (a0:A) q1) = node_map H a0` THEN
        MESON_TAC[LAST_CONS_NE; MEM];
        MATCH_MP_TAC MEM2_LAST THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `~(MEM (v:A) (CONS a0 q1))` THEN
    UNDISCH_TAC `MEM (node_map H a0) (CONS (a0:A) q1)` THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `APPEND q4 [v:A]` THEN
  ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path; CLINKN; LAST_CONS_SNOC;
                  MEM_APPEND; MEM] THEN
  UNDISCH_TAC `!t:A. MEM t q4 ==> ~(MEM t (CONS a0 q1))` THEN
  UNDISCH_TAC `~(MEM (v:A) (CONS a0 q1))` THEN REWRITE_TAC[MEM] THEN
  MESON_TAC[]);;

(* Walking back along an edge arc ending at node a0 and avoiding z1, the     *)
(* contour is extended to a path from node a0 to the start of the arc.       *)
let EULER_TREE_KEY = prove
 (`!(H:(A)hypermap) a0 q1 z1.
     jordan H /\
     list_path (clink H) a0 q1 /\ LAST (CONS a0 q1) = node_map H a0 /\
     PAIRWISE (\a b. ~(a = b)) (CONS a0 q1) /\
     (!y. MEM (face_map H y) (CONS a0 q1)
          ==> y = z1 \/ MEM y (BUTLAST (CONS a0 q1)))
     ==> !r y. y IN dart H /\ list_path (\a b. b = edge_map H a) y r /\
               LAST (CONS y r) = node_map H a0 /\ ~(MEM z1 r)
               ==> ?q2. list_path (clink H) (node_map H a0) q2 /\
                        LAST (CONS (node_map H a0) q2) = y /\
                        (!t. MEM t q2 ==> ~(MEM t (CONS a0 q1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `y:A` THEN
  REWRITE_TAC[list_path; LAST_CLAUSES] THENL
   [REWRITE_TAC[MEM] THEN STRIP_TAC THEN EXISTS_TAC `[]:(A)list` THEN
    ASM_REWRITE_TAC[list_path; LAST_CLAUSES; MEM];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)
    (CONJUNCTS_THEN2 ASSUME_TAC
      (STRIP_ASSUME_TAC o REWRITE_RULE[MEM; DE_MORGAN_THM])))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `edge_map H (y:A) IN dart H` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`] MAPS_IN_DART) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_map H (y:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(MEM (face_map H (edge_map H y)) (CONS (a0:A) q1))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `edge_map H y = (z1:A) \/
      MEM (edge_map H y) (BUTLAST (CONS (a0:A) q1))`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~(z1:A = edge_map H y)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `CONS (node_map H a0) (q2:(A)list)` MEM_LAST) THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL; MEM] THEN STRIP_TAC THENL
     [UNDISCH_TAC `MEM (edge_map H y) (BUTLAST (CONS (a0:A) q1))` THEN
      MP_TAC(ISPEC `CONS (a0:A) q1` NOT_MEM_LAST_BUTLAST) THEN
      ASM_REWRITE_TAC[NOT_CONS_NIL] THEN MESON_TAC[];
      SUBGOAL_THEN `~(MEM (edge_map H y) (CONS (a0:A) q1))` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `MEM (edge_map H y) (BUTLAST (CONS (a0:A) q1))` THEN
      MESON_TAC[MEM_BUTLAST]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `y:A`] NODE_CYCLE_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `a0:A`; `q1:(A)list`; `edge_map H (y:A)`;
                 `q2:(A)list`] EULER_TREE_INNER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`q:(A)list`; `y:A`]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let EULER_TREE_CONTRA = prove
 (`!(H:(A)hypermap) x p1.
     jordan H /\ x IN dart H /\
     (!y. y IN orbit_map (edge_map H) x
          ==> ~(clink H y y) /\ cross_edge H y) /\
     list_path (\a b. b = edge_map H a) x p1 /\ face_simple H (CONS x p1) /\
     cface H (LAST (CONS x p1)) (node_map H (face_map H x))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `fx = face_map H (x:A)` THEN
  ABBREV_TAC `nfx = node_map H (fx:A)` THEN
  ABBREV_TAC `z1 = LAST (CONS (x:A) p1)` THEN
  SUBGOAL_THEN `(fx:A) IN dart H /\ (nfx:A) IN dart H` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MAPS_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map H (nfx:A) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[faceK]; ALL_TAC] THEN
  SUBGOAL_THEN `(nfx:A) IN orbit_map (edge_map H) x` ASSUME_TAC THENL
   [SUBGOAL_THEN `nfx = inverse (edge_map H) (x:A)` SUBST1_TAC THENL
     [REWRITE_TAC[EDGE_MAP_INVERSE; o_THM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INVERSE_IN_ORBIT THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
      ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. y IN orbit_map (edge_map H) x
          ==> node_map H y IN orbit_map (edge_map H) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `cross_edge H (y:A)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cross_edge] THEN
    SUBGOAL_THEN `orbit_map (edge_map H) (y:A) = orbit_map (edge_map H) x`
     (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES];
    ALL_TAC] THEN
  SUBGOAL_THEN `(fx:A) IN orbit_map (edge_map H) x` ASSUME_TAC THENL
   [SUBGOAL_THEN `!k. ITER k (node_map H) (nfx:A) IN orbit_map (edge_map H) x`
    ASSUME_TAC THENL [INDUCT_TAC THEN ASM_SIMP_TAC[ITER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`;
                   `fx:A`] ITER_ORBIT_SIZE) THEN
    MP_TAC(ISPECL [`node_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`;
                   `fx:A`] ORBIT_SIZE_POS) THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN
    ABBREV_TAC `m = orbit_size (node_map H) (fx:A)` THEN DISCH_TAC THEN
    SUBGOAL_THEN `m = SUC(m - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ITER_ALT; SUC_SUB1] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(MEM (fx:A) (CONS x p1))` ASSUME_TAC THENL
   [REWRITE_TAC[MEM; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `clink H (x:A) x` MP_TAC THENL
       [REWRITE_TAC[clink] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[IN_ORBIT_MAP_REFL]];
      DISCH_TAC THEN UNDISCH_TAC `face_simple H (CONS (x:A) p1)` THEN
      REWRITE_TAC[face_simple] THEN CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(fx:A = nfx)` ASSUME_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `clink H (nfx:A) nfx` MP_TAC THENL
     [REWRITE_TAC[clink] THEN DISJ1_TAC THEN
      UNDISCH_TAC `node_map H fx = (nfx:A)` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(fx:A = z1)` ASSUME_TAC THENL
   [EXPAND_TAC "z1" THEN DISCH_TAC THEN
    UNDISCH_TAC `~(MEM (fx:A) (CONS x p1))` THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th; LIST_PATH_MEM_LAST]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `nfx:A`; `p1:(A)list`; `x:A`]
    EULER_TREE_CONTOUR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z1:A) IN orbit_map (edge_map H) x` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `p1:(A)list`; `x:A`]
      GPATH_MEM_ORBIT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "z1" THEN
    REWRITE_TAC[LIST_PATH_MEM_LAST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p2. list_path (\a b. b = edge_map H a) (fx:A) p2 /\
         LAST (CONS fx p2) = nfx /\ ~(MEM z1 p2)`
  MP_TAC THENL
   [SUBGOAL_THEN `(nfx:A) IN orbit_map (edge_map H) z1` MP_TAC THENL
     [SUBGOAL_THEN `orbit_map (edge_map H) (z1:A) = orbit_map (edge_map H) x`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
      ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ORBIT_GPATH) THEN
    DISCH_THEN(X_CHOOSE_THEN `p0:(A)list` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`\a b. b = edge_map (H:(A)hypermap) a`; `z1:A`;
                   `p0:(A)list`] LIST_PATH_SHORTEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `MEM (fx:A) p` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `APPEND p1 (p:(A)list)`;
                     `x:A`] GPATH_CYCLE_MEM) THEN
      ASM_REWRITE_TAC[LIST_PATH_APPEND; LAST_CONS_APPEND_GEN] THEN
      DISCH_THEN(MP_TAC o SPEC `fx:A`) THEN
      ASM_REWRITE_TAC[GSYM(CONJUNCT2 APPEND); MEM_APPEND];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\a b. b = edge_map (H:(A)hypermap) a`; `p:(A)list`;
                   `z1:A`; `fx:A`] LIST_PATH_SUFFIX) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:(A)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `fx:A`; `q1:(A)list`; `z1:A`]
    EULER_TREE_KEY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`p2:(A)list`; `fx:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `CONS (nfx:A) q2` MEM_LAST) THEN
  ASM_REWRITE_TAC[NOT_CONS_NIL; MEM] THEN
  UNDISCH_TAC `!t:A. MEM t q2 ==> ~(MEM t (CONS fx q1))` THEN
  REWRITE_TAC[MEM] THEN MESON_TAC[]);;

let EULER_TREE = prove
 (`!(H:(A)hypermap) x. jordan H /\ x IN dart H
    ==> ?z. z IN orbit_map (edge_map H) x /\
            (clink H z z \/ ~cross_edge H z)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `!y:A. y IN orbit_map (edge_map H) x ==> ~(clink H y y) /\ cross_edge H y`
  THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;
                 `iterlist (orbit_size (edge_map H) x) (edge_map H) (x:A)`;
                 `x:A`] EULER_TREE_ARC) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GPATH_ITERLIST; face_simple] THEN
    MATCH_MP_TAC(TAUT `p ==> ~(~p /\ q)`) THEN
    REWRITE_TAC[FBAND_MEM_IFF] THEN EXISTS_TAC `x:A` THEN
    REWRITE_TAC[CFACE_REFL; MEM_ITERLIST] THEN
    EXISTS_TAC `orbit_size (edge_map H) (x:A)` THEN
    MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
      ITER_ORBIT_SIZE) THEN
    MP_TAC(ISPECL [`edge_map (H:(A)hypermap)`; `dart(H:(A)hypermap)`; `x:A`]
      ORBIT_SIZE_POS) THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':A` (X_CHOOSE_THEN `p1:(A)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `x':A`; `p1:(A)list`] EULER_TREE_CONTRA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `orbit_map (edge_map H) (x':A) = orbit_map (edge_map H) x`
  SUBST1_TAC THENL
   [MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; EDGE_MAP_PERMUTES];
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[ORBIT_MAP_IN; FINITE_DART; EDGE_MAP_PERMUTES]]);;
