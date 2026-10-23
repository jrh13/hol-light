(* ========================================================================= *)
(* 4CT/embed_prelim.ml                                                       *)
(*                                                                           *)
(* Preliminaries for embed.ml: the part of Gonthier's embed.v up to          *)
(* adj_kernel_max, with what it needs from mathcomp path.v (take, drop,      *)
(* rot, arc, rot_to_arc), from revsnip.v (chord_ring and its scycle,         *)
(* proper, diskN, fband and diskF lemmas) and from patch.v (the remainder    *)
(* halves of plain_patch and cubic_patch).  Main results: EMBED_FUNCTOR      *)
(* (h commutes with edge on the kernel), CFACE_AC_H and CFACE_INJ_EMBED      *)
(* (face transport), INTRO_PRE_HOM_RING and TRIVIAL_HOM_RING                 *)
(* (pre-homomorphic rings), CHORDLESS_PERIMETER, FCARD_ADJ_PERIMETER and     *)
(* ADJ_KERNEL_MAX.                                                           *)
(* ========================================================================= *)

needs "4CT/revsnip.ml";;

(* ------------------------------------------------------------------------- *)
(* Dart propagation, kernel and cface facts (the Coq section preliminaries). *)
(* ------------------------------------------------------------------------- *)

let KERNEL_FCLOSED = prove
 (`!(H:(A)hypermap) rc w.
     w IN kernel H rc ==> face_map H w IN kernel H rc`,
  REWRITE_TAC[IN; KERNEL_FACE]);;

let RLINK_DART = prove
 (`!(H:(A)hypermap) u v. u IN dart H /\ rlink H u v ==> v IN dart H`,
  REPEAT STRIP_TAC THEN CFACE_TAC[]);;

let RLINK_PATH_DART = prove
 (`!(H:(A)hypermap) p u.
     u IN dart H /\ list_path (rlink H) u p ==> ALL (\z. z IN dart H) p`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[list_path; ALL] THEN
  ASM_MESON_TAC[RLINK_DART]);;

let EDGE_CENTRAL_EDGE = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) h x.
     plain_hypermap Gc /\ plain_hypermap Gm
     ==> (edge_central Gc Gm h (edge_map Gc x) <=> edge_central Gc Gm h x)`,
  REWRITE_TAC[edge_central] THEN MESON_TAC[CFT_PLAIN_EE]);;

let DISKF_CFACE = prove
 (`!(H:(A)hypermap) r a b.
     a IN dart H /\ cface H a b /\ diskF H r a ==> diskF H r b`,
  REWRITE_TAC[cface; face] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`face_map(H:(A)hypermap)`; `dart(H:(A)hypermap)`;
                 `diskF (H:(A)hypermap) r`; `a:A`; `b:A`] ORBIT_INVARIANT) THEN
  ASM_SIMP_TAC[FINITE_DART; FACE_MAP_PERMUTES; DISKF_FACE]);;

let CUBIC_EQ_U = prove
 (`!(H:(A)hypermap) z.
     cubic_hypermap H ==> node_map H (node_map H (node_map H z)) = z`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(z:A) IN dart H` THEN
  ASM_SIMP_TAC[CUBIC_EQ] THEN
  ASM_MESON_TAC[PERMUTES_FIX_OUTSIDE; NODE_MAP_PERMUTES]);;

let CFACE_FACE_L = prove
 (`!(H:(A)hypermap) a b. cface H (face_map H a) b <=> cface H a b`,
  REPEAT GEN_TAC THEN CFACE_TAC[]);;

let KERNEL_NOT_MEM = prove
 (`!(H:(A)hypermap) rc z. z IN kernel H rc ==> ~MEM z rc`,
  REPEAT GEN_TAC THEN CFACE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Orbit sizes: small orbits, no early return, and invariance of the orbit   *)
(* size under an injective map intertwining two permutations.                *)
(* ------------------------------------------------------------------------- *)

let ORBIT_SIZE_EQ_2 = prove
 (`!(f:A->A) s z.
     FINITE s /\ f permutes s /\ z IN s /\ f(f z) = z /\ ~(f z = z)
     ==> orbit_size f z = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `orbit_size (f:A->A) z divides 2` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_DIVIDES; ITER2]; ALL_TAC] THEN
  SUBGOAL_THEN `~(orbit_size (f:A->A) z = 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_DIVIDES; ITER_1; DIVIDES_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `0 < orbit_size (f:A->A) z` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_POS]; ALL_TAC] THEN
  MP_TAC(SPECL [`orbit_size (f:A->A) z`; `2`] DIVIDES_LE) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC);;

let ORBIT_SIZE_EQ_3 = prove
 (`!(f:A->A) s z. FINITE s /\ f permutes s /\ z IN s /\
     f(f(f z)) = z /\ ~(f z = z) /\ ~(f(f z) = z) ==> orbit_size f z = 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(orbit_size (f:A->A) z = 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_DIVIDES; ITER_1; DIVIDES_ONE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(orbit_size (f:A->A) z = 2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(SPECL[`f:A->A`; `s:A->bool`; `z:A`; `2`] ORBIT_SIZE_DIVIDES) THEN
    ASM_REWRITE_TAC[ITER2; TWO_DIV_TWO];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < orbit_size (f:A->A) z` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `orbit_size (f:A->A) z divides 3` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_DIVIDES; ITER3]; ALL_TAC] THEN
  MP_TAC(SPECL [`orbit_size (f:A->A) z`; `3`] DIVIDES_LE) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_ARITH_TAC);;

let ORBIT_ITER_NEQ = prove
 (`!(f:A->A) s z k.
     FINITE s /\ f permutes s /\ z IN s /\ 0 < k /\ k < orbit_size f z
     ==> ~(ITER k f z = z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `z:A`; `k:num`]
           ORBIT_SIZE_DIVIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`orbit_size (f:A->A) z`; `k:num`] DIVIDES_LE) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ORBIT_NONFIX = prove
 (`!(f:A->A) s z.
     FINITE s /\ f permutes s /\ z IN s /\ 2 <= orbit_size f z ==> ~(f z = z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->A`; `s:A->bool`; `z:A`; `1`] ORBIT_ITER_NEQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ITER_1] THEN ASM_MESON_TAC[]);;

let ORBIT_SIZE_INTERTWINE = prove
 (`!f g s s' t (h:A->B) x.
     FINITE s /\ f permutes s /\ FINITE s' /\ g permutes s' /\ INJ h s s' /\
     t SUBSET s /\ (!y. y IN t ==> f y IN t /\ h (f y) = g (h y)) /\ x IN t
     ==> orbit_size f x = orbit_size g (h x)`,
  REWRITE_TAC[INJ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ORBIT_SIZE_PERIOD THEN
  EXISTS_TAC `s:A->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[ORBIT_SIZE_POS; SUBSET];
    X_GEN_TAC `n:num`] THEN
  MP_TAC(ISPECL [`g:B->B`; `s':B->bool`; `(h:A->B) x`; `n:num`]
    ORBIT_SIZE_DIVIDES) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`f:A->A`; `g:B->B`; `t:A->bool`; `h:A->B`]
    ITER_INTERTWINE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`n:num`; `x:A`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_MESON_TAC[ITER_PERMUTES_IN; SUBSET]);;

let QUASICUBIC_NEQ = prove
 (`!(H:(A)hypermap) r x.
     quasicubic H r /\ x IN dart H /\ ~(x IN r) ==> ~(node_map H x = x)`,
  REWRITE_TAC[quasicubic] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC ORBIT_NONFIX THEN EXISTS_TAC `dart(H:(A)hypermap)` THEN
  ASM_SIMP_TAC[ETA_AX; FINITE_DART; NODE_MAP_PERMUTES; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* List utilities: take/drop/rot/rotr, index, arcs (mathcomp path.v arc),    *)
(* uniq lists and the arc decomposition of a uniq list (rot_to_arc).         *)
(* ------------------------------------------------------------------------- *)

let take_list = define
 `(take_list 0 (l:A list) = []) /\
  (take_list (SUC n) l = if l = [] then [] else CONS (HD l) (take_list n (TL
    l)))`;;

let drop_list = define
 `(drop_list 0 (l:A list) = l) /\
  (drop_list (SUC n) l = if l = [] then [] else drop_list n (TL l))`;;

let rot_list = new_definition
 `rot_list n (l:A list) = APPEND (drop_list n l) (take_list n l)`;;

let rotr_list = new_definition
 `rotr_list n (l:A list) = rot_list (LENGTH l - n) l`;;

let index_list = define
 `(index_list (x:A) [] = 0) /\
  (index_list x (CONS h t) = if h = x then 0 else SUC (index_list x t))`;;

let arc_list = new_definition
 `arc_list (p:(A)list) x y =
    take_list (index_list y (rot_list (index_list x p) p)) (rot_list
      (index_list x p) p)`;;

let TAKE_DROP_LIST = prove
 (`!n (l:A list). APPEND (take_list n l) (drop_list n l) = l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[take_list; drop_list; APPEND; HD; TL; NOT_CONS_NIL]);;

let MEM_ROT_LIST = prove
 (`!n (l:A list) x. MEM x (rot_list n l) <=> MEM x l`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL[`n:num`; `l:(A)list`] TAKE_DROP_LIST) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[rot_list; MEM_APPEND] THEN MESON_TAC[]);;

let LENGTH_TAKE_LIST_COND = prove
 (`!n (l:A list).
     LENGTH (take_list n l) = if n <= LENGTH l then n else LENGTH l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[take_list; LENGTH; HD; TL; NOT_CONS_NIL; LE; LE_0;
                  ARITH] THEN
  ASM_REWRITE_TAC[LE_SUC] THEN ARITH_TAC);;

let LENGTH_DROP_LIST = prove
 (`!n (l:A list). LENGTH (drop_list n l) = LENGTH l - n`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[drop_list; LENGTH; HD; TL; NOT_CONS_NIL; SUB_0] THEN
  ARITH_TAC);;

let ROT_LIST_0 = prove
 (`!l:A list. rot_list 0 l = l`,
  REWRITE_TAC[rot_list; drop_list; take_list; APPEND_NIL]);;

let TAKE_APPEND_LENGTH = prove
 (`!(a:A list) b. take_list (LENGTH a) (APPEND a b) = a`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; take_list; APPEND; HD; TL; NOT_CONS_NIL]);;

let DROP_APPEND_LENGTH = prove
 (`!(a:A list) b. drop_list (LENGTH a) (APPEND a b) = b`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[LENGTH; drop_list; APPEND; HD; TL; NOT_CONS_NIL]);;

let INDEX_LIST_HEAD = prove
 (`!(x:A) t. index_list x (CONS x t) = 0`,
  REWRITE_TAC[index_list]);;

let INDEX_LIST_APPEND_NOTMEM = prove
 (`!(a:A list) x b. ~MEM x a
   ==> index_list x (APPEND a (CONS x b)) = LENGTH a`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; LENGTH; MEM; DE_MORGAN_THM] THENL
   [REWRITE_TAC[INDEX_LIST_HEAD];
    REPEAT STRIP_TAC THEN REWRITE_TAC[index_list] THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[]]]);;

let ROT_TO_FRONT = prove
 (`!(a:A list) x b. ~MEM x a
      ==> rot_list (index_list x (APPEND a (CONS x b))) (APPEND a (CONS x b))
          = CONS x (APPEND b a)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[INDEX_LIST_APPEND_NOTMEM; rot_list; DROP_APPEND_LENGTH;
               TAKE_APPEND_LENGTH] THEN
  REWRITE_TAC[APPEND]);;

let LEFT_ARC = prove
 (`!(x1:A) p1 x2 p2. ~MEM x2 (CONS x1 p1)
      ==> arc_list (APPEND (CONS x1 p1) (CONS x2 p2)) x1 x2 = CONS x1 p1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arc_list] THEN
  SUBGOAL_THEN `index_list (x1:A) (APPEND (CONS x1 p1) (CONS x2 p2)) = 0`
    SUBST1_TAC THENL [REWRITE_TAC[APPEND; INDEX_LIST_HEAD]; ALL_TAC] THEN
  REWRITE_TAC[ROT_LIST_0] THEN ASM_SIMP_TAC[INDEX_LIST_APPEND_NOTMEM] THEN
  REWRITE_TAC[TAKE_APPEND_LENGTH]);;

let RIGHT_ARC = prove
 (`!(x1:A) p1 x2 p2. ~MEM x2 (CONS x1 p1) /\ ~MEM x1 (CONS x2 p2)
      ==> arc_list (APPEND (CONS x1 p1) (CONS x2 p2)) x2 x1 = CONS x2 p2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arc_list] THEN
  ASM_SIMP_TAC[ROT_TO_FRONT] THEN
  SUBGOAL_THEN
    `(CONS (x2:A) (APPEND p2 (CONS x1 p1))) = APPEND (CONS x2 p2) (CONS x1 p1)`
    SUBST1_TAC THENL [REWRITE_TAC[APPEND]; ALL_TAC] THEN
  ASM_SIMP_TAC[INDEX_LIST_APPEND_NOTMEM] THEN
  REWRITE_TAC[TAKE_APPEND_LENGTH]);;

let rotate_to = new_definition
 `rotate_to (x:A) l = rot_list (index_list x l) l`;;

let uniq_list = new_definition
 `uniq_list (l:A list) <=> PAIRWISE (\x y. ~(x = y)) l`;;

let UNIQ_LIST_APPEND_DISJOINT = prove
 (`!(c:A list) d. uniq_list (APPEND c d) ==> !x. MEM x c ==> ~MEM x d`,
  REWRITE_TAC[uniq_list] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[APPEND; PAIRWISE; MEM; ALL_APPEND] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[ALL_MEM]);;

let UNIQ_APPEND_SYM = prove
 (`!(c:A list) d. uniq_list (APPEND c d) <=> uniq_list (APPEND d c)`,
  REWRITE_TAC[uniq_list; PAIRWISE_APPEND] THEN MESON_TAC[]);;

let UNIQ_ROT = prove
 (`!i (p:A list). uniq_list p ==> uniq_list (rot_list i p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`i:num`; `p:(A)list`] TAKE_DROP_LIST) THEN
  ABBREV_TAC `c = take_list i (p:A list)` THEN
  ABBREV_TAC `d = drop_list i (p:A list)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `rot_list i (p:A list) = APPEND d c` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "d"] THEN REWRITE_TAC[rot_list]; ALL_TAC] THEN
  ASM_MESON_TAC[UNIQ_APPEND_SYM]);;

let ROTATE_TO_FRONT = prove
 (`!(a:A list) x b. ~MEM x a
      ==> rotate_to x (APPEND a (CONS x b)) = CONS x (APPEND b a)`,
  REWRITE_TAC[rotate_to] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ROT_TO_FRONT]);;

let ROTATE_TO_SWAP = prove
 (`!(x:A) c d. uniq_list (APPEND c d) /\ MEM x (APPEND c d)
      ==> rotate_to x (APPEND d c) = rotate_to x (APPEND c d)`,
  REWRITE_TAC[MEM_APPEND] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `?c1 c2. c = APPEND c1 (CONS (x:A) c2) /\ ~MEM x c1`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FIRST_OCC_SPLIT]; ALL_TAC] THEN
    SUBGOAL_THEN `~MEM (x:A) d` ASSUME_TAC THENL
     [ASM_MESON_TAC[UNIQ_LIST_APPEND_DISJOINT]; ALL_TAC];
    SUBGOAL_THEN `?d1 d2. d = APPEND d1 (CONS (x:A) d2) /\ ~MEM x d1`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FIRST_OCC_SPLIT]; ALL_TAC] THEN
    SUBGOAL_THEN `~MEM (x:A) c` ASSUME_TAC THENL
     [ASM_MESON_TAC[UNIQ_LIST_APPEND_DISJOINT]; ALL_TAC]] THEN
  ASM_REWRITE_TAC[NF1; NF2] THEN
  ASM_SIMP_TAC[ROTATE_TO_FRONT; MEM_APPEND; DE_MORGAN_THM] THEN
  REWRITE_TAC[APPEND_ASSOC]);;

let ROTATE_TO_ROT = prove
 (`!(p:A list) i x. uniq_list p /\ MEM x p
      ==> rotate_to x (rot_list i p) = rotate_to x p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`i:num`; `p:(A)list`] TAKE_DROP_LIST) THEN
  ABBREV_TAC `c = take_list i (p:A list)` THEN
  ABBREV_TAC `d = drop_list i (p:A list)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `rot_list i (p:A list) = APPEND d c` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["c"; "d"] THEN REWRITE_TAC[rot_list]; ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
    [SYM(ASSUME `APPEND (c:A list) d = p`)] THEN
  MATCH_MP_TAC ROTATE_TO_SWAP THEN ASM_REWRITE_TAC[]);;

let ARC_ROT = prove
 (`!(p:A list) i x y. uniq_list p /\ MEM x p
      ==> arc_list (rot_list i p) x y = arc_list p x y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[arc_list; GSYM rotate_to] THEN
  ASM_SIMP_TAC[ROTATE_TO_ROT]);;

let ROTATE_TO_SHAPE = prove
 (`!(p:A list) x y. uniq_list p /\ MEM x p /\ MEM y p /\ ~(x = y)
      ==> ?p1 p2. rotate_to x p = APPEND (CONS x p1) (CONS y p2) /\
                  ~MEM y (CONS x p1) /\ ~MEM x (CONS y p2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP FIRST_OCC_SPLIT (ASSUME `MEM (x:A) p`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A list`
               (X_CHOOSE_THEN `b:A list` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `MEM (y:A) (APPEND b a)` MP_TAC THENL
   [UNDISCH_TAC `MEM (y:A) p` THEN ASM_REWRITE_TAC[MEM_APPEND; MEM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:A list`
               (X_CHOOSE_THEN `p2:A list` STRIP_ASSUME_TAC) o
             MATCH_MP FIRST_OCC_SPLIT) THEN
  MAP_EVERY EXISTS_TAC [`p1:A list`; `p2:A list`] THEN
  SUBGOAL_THEN `rotate_to (x:A) p = APPEND (CONS x p1) (CONS y p2)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[ROTATE_TO_FRONT; APPEND]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CONS (x:A) p1`; `CONS (y:A) p2`]
    UNIQ_LIST_APPEND_DISJOINT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[rotate_to; UNIQ_ROT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MEM] THEN ASM_MESON_TAC[]);;

let ROT_TO_ARC = prove
 (`!(p:A list) x y. uniq_list p /\ MEM x p /\ MEM y p /\ ~(x = y)
      ==> ?i p1 p2. arc_list p x y = CONS x p1 /\
                    arc_list p y x = CONS y p2 /\
                    rot_list i p = APPEND (CONS x p1) (CONS y p2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:A list`; `x:A`; `y:A`] ROTATE_TO_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:A list`
               (X_CHOOSE_THEN `p2:A list` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`index_list (x:A) p`; `p1:A list`; `p2:A list`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `arc_list (rotate_to (x:A) p) x y = arc_list p x y`
      (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[rotate_to] THEN MATCH_MP_TAC ARC_ROT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LEFT_ARC THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `arc_list (rotate_to (x:A) p) y x = arc_list p y x`
      (SUBST1_TAC o SYM) THENL
     [REWRITE_TAC[rotate_to] THEN MATCH_MP_TAC ARC_ROT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RIGHT_ARC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM rotate_to] THEN ASM_REWRITE_TAC[]]);;

let MEM_TAKE_LIST = prove
 (`!n (l:A list) z. MEM z (take_list n l) ==> MEM z l`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL[`n:num`; `l:(A)list`] TAKE_DROP_LIST) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[]);;

let MEM_ARC_LIST = prove
 (`!(r:A list) a b z. MEM z (arc_list r a b) ==> MEM z r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arc_list] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEM_TAKE_LIST) THEN REWRITE_TAC[MEM_ROT_LIST]);;

let ROT_LIST_APPEND = prove
 (`!(a:A list) b. rot_list (LENGTH a) (APPEND a b) = APPEND b a`,
  REWRITE_TAC[rot_list; DROP_APPEND_LENGTH; TAKE_APPEND_LENGTH]);;

let ROT_LIST_ONE = prove
 (`!(x:A) l. rot_list 1 (CONS x l) = APPEND l [x]`,
  REWRITE_TAC[ONE; rot_list; take_list; drop_list; NOT_CONS_NIL; HD; TL]);;

let MAP_INJ_MEM = prove
 (`!(f:A->B) l a b.
     PAIRWISE (\u v. ~(u = v)) (MAP f l) /\ MEM a l /\ MEM b l /\ f a = f b
     ==> a = b`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; PAIRWISE; MEM; GSYM ALL_MEM; MEM_MAP] THEN
  ASM_MESON_TAC[]);;

let LIST_PATH_CONS_SPLIT = prove
 (`!(e:A->A->bool) x p a u l.
     list_path e x p /\ CONS x p = APPEND a (CONS u l) ==> list_path e u l`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `a:(A)list` list_CASES) THEN
  REWRITE_TAC[APPEND; CONS_11] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIST_PATH_APPEND]) THEN
  REWRITE_TAC[list_path] THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Chord rings (revsnip.v chord_ring): scycle, proper, diskN partition and   *)
(* diskF of the two chord rings of a chord; rotation invariance.             *)
(* ------------------------------------------------------------------------- *)

let chord_ring = new_definition
 `chord_ring (H:(A)hypermap) r x =
    CONS x (arc_list r (fproj H r (edge_map H x)) (fproj H r x))`;;

let FACE_SIMPLE_UNIQ = prove
 (`!(H:(A)hypermap) p. face_simple H p ==> uniq_list p`,
  REWRITE_TAC[uniq_list; FACE_SIMPLE_PAIRWISE_GEN]);;

let FBAND_CROSS_SYM = prove
 (`!(H:(A)hypermap) a b.
     (!x. MEM x a ==> ~fband H b x) <=> (!x. MEM x b ==> ~fband H a x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[fband; NOT_EX; GSYM ALL_MEM] THEN
  MESON_TAC[CFACE_SYM_GEN]);;

let FBAND_OFF_SYM = prove
 (`!(H:(A)hypermap) a b.
     (!x. MEM x a ==> ~fband H b x) ==> (!x. MEM x b ==> ~fband H a x)`,
  MESON_TAC[FBAND_CROSS_SYM]);;

let FACE_SIMPLE_APPEND_SYM = prove
 (`!(H:(A)hypermap) a b.
     face_simple H (APPEND a b) <=> face_simple H (APPEND b a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FBAND_CROSS_SYM]);;

let FACE_SIMPLE_ROT = prove
 (`!(H:(A)hypermap) i r. face_simple H (rot_list i r) <=> face_simple H r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rot_list] THEN
  GEN_REWRITE_TAC LAND_CONV [FACE_SIMPLE_APPEND_SYM] THEN
  REWRITE_TAC[TAKE_DROP_LIST]);;

let LIST_CYCLE_APPEND_SYM = prove
 (`!e (a:A list) b. list_cycle e (APPEND a b) <=> list_cycle e (APPEND b a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:A list = []` THEN
  ASM_REWRITE_TAC[APPEND; APPEND_NIL] THEN ASM_CASES_TAC `b:A list = []` THEN
  ASM_REWRITE_TAC[APPEND; APPEND_NIL] THEN
  REWRITE_TAC[list_cycle; APPEND_EQ_NIL; LAST_APPEND; LIST_PATH_APPEND;
              LAST] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

let LIST_CYCLE_ROT = prove
 (`!e i (r:A list). list_cycle e (rot_list i r) <=> list_cycle e r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rot_list] THEN
  GEN_REWRITE_TAC LAND_CONV [LIST_CYCLE_APPEND_SYM] THEN
  REWRITE_TAC[TAKE_DROP_LIST]);;

let SCYCLE_ROT = prove
 (`!(H:(A)hypermap) e i r. scycle H e (rot_list i r) <=> scycle H e r`,
  REWRITE_TAC[scycle; LIST_CYCLE_ROT; FACE_SIMPLE_ROT]);;

let SCYCLE_CONS = prove
 (`!(H:(A)hypermap) c q.
     scycle H (rlink H) (CONS c q) <=>
     list_path (rlink H) c q /\ rlink H (LAST (CONS c q)) c /\
     ~fband H q c /\ face_simple H q`,
  REWRITE_TAC[scycle; LIST_CYCLE_CONS_PATH; LIST_PATH_APPEND; list_path;
              face_simple] THEN
  CONV_TAC TAUT);;

let CHORD_DECOMP = prove
 (`!(H:(A)hypermap) r x.
     plain_hypermap H /\ bridgeless H /\ scycle H (rlink H) r /\
     ALL (\z. z IN dart H) r /\ x IN dart H /\
     fband H r x /\ fband H r (edge_map H x)
     ==> ?y1 y2 i p1 p2.
           fproj H r x = y1 /\ fproj H r (edge_map H x) = y2 /\
           MEM y1 r /\ MEM y2 r /\ cface H x y1 /\ cface H (edge_map H x) y2 /\
           ~(y2 = y1) /\ uniq_list r /\
           arc_list r y1 y2 = CONS y1 p1 /\ arc_list r y2 y1 = CONS y2 p2 /\
           rot_list i r = APPEND (CONS y1 p1) (CONS y2 p2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:A list`; `x:A`] FPROJ_IN_FBAND) THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:A list`; `edge_map H (x:A)`]
    FPROJ_IN_FBAND) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `uniq_list (r:A list)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_SIMPLE_UNIQ; scycle]; ALL_TAC] THEN
  SUBGOAL_THEN `~(fproj H r (edge_map H x) = fproj H r (x:A))` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A list`; `fproj H r (x:A)`;
                 `fproj H r (edge_map H (x:A))`] ROT_TO_ARC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`fproj H r (x:A)`; `fproj H r (edge_map H (x:A))`;
                        `i:num`; `p1:A list`; `p2:A list`] THEN
  ASM_REWRITE_TAC[]);;

let SCYCLE_CHORD_RING = prove
 (`!(H:(A)hypermap) r x.
     plain_hypermap H /\ bridgeless H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ x IN dart H /\
     fband H r x /\ fband H r (edge_map H x)
     ==> scycle H (rlink H) (chord_ring H r x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:A list`; `x:A`] CHORD_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[chord_ring] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `rlink(H:(A)hypermap)`; `i:num`;
                 `r:A list`] SCYCLE_ROT) THEN
  ASM_REWRITE_TAC[APPEND; SCYCLE_CONS; LIST_PATH_APPEND; FBAND_APPEND;
                  FACE_SIMPLE_APPEND'; list_path] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 APPEND); LAST_APPEND; NOT_CONS_NIL] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[rlink] THEN
  ONCE_REWRITE_TAC[LAST] THEN ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
  CFACE_TAC[]);;

let PROPER_CHORD_RING = prove
 (`!(H:(A)hypermap) r x.
     plain_hypermap H /\ bridgeless H /\ scycle H (rlink H) r /\
     ALL (\z. z IN dart H) r /\ x IN dart H /\ ~MEM (edge_map H x) r /\
     fband H r x /\ fband H r (edge_map H x)
     ==> proper_ring H (chord_ring H r x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:A list`; `x:A`] CHORD_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[chord_ring] THEN
  STRUCT_CASES_TAC(ISPEC `p2:A list` list_CASES) THEN
  REWRITE_TAC[PROPER_TWO; proper_ring; CONS_11] THENL
   [ASM_MESON_TAC[]; MESON_TAC[]]);;

let ALL_DART_CHORD_RING = prove
 (`!(H:(A)hypermap) r x. x IN dart H /\ ALL (\z. z IN dart H) r
      ==> ALL (\z. z IN dart H) (chord_ring H r x)`,
  REWRITE_TAC[chord_ring; GSYM ALL_MEM; MEM] THEN MESON_TAC[MEM_ARC_LIST]);;

let CHORD_BASIC = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ scycle H (rlink H) r /\
     ALL (\z. z IN dart H) r /\ x IN diskE H r
     ==> x IN dart H /\ edge_map H x IN dart H /\
         edge_map H (edge_map H x) = x /\ ~(x = edge_map H x) /\
         ~(edge_map H x = x) /\ diskN H r x /\ ~MEM x r /\
         ~MEM (edge_map H x) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `diskN H r (x:A) /\ ~MEM x r` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN diskE H r` THEN SIMP_TAC[IN; diskE]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] DISKE_EDGE) THEN
  ASM_SIMP_TAC[diskE; EDGE_MAP_IN_DART; CFT_PLAIN_EE; PLAIN_NEQ]);;

let DISKN_CHORD_BASE = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x)
     ==> diskN H (chord_ring H r x) x /\
         ~diskN H (chord_ring H r (edge_map H x)) x /\
         diskN H r x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `x:A`] CHORD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_IN_DISKN THEN ASM_REWRITE_TAC[chord_ring; MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`H:(A)hypermap`;
                 `chord_ring (H:(A)hypermap) r (edge_map H x)`; `x:A`]
    DISKE_EDGE) THEN
  ASM_SIMP_TAC[SCYCLE_CHORD_RING; ALL_DART_CHORD_RING; DISKN_E] THEN
  REWRITE_TAC[diskE; chord_ring; MEM] THEN ASM_MESON_TAC[MEM_ARC_LIST]);;

let CHORD_RINGS_OK = prove
 (`!(H:(A)hypermap) r x.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x)
     ==> scycle H (rlink H) (chord_ring H r x) /\
         proper_ring H (chord_ring H r x) /\
         ALL (\z. z IN dart H) (chord_ring H r x) /\
         scycle H (rlink H) (chord_ring H r (edge_map H x)) /\
         proper_ring H (chord_ring H r (edge_map H x)) /\
         ALL (\z. z IN dart H) (chord_ring H r (edge_map H x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `x:A`] CHORD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SCYCLE_CHORD_RING; PROPER_CHORD_RING; ALL_DART_CHORD_RING]);;

let DISKN_FACE_EDGE = prove
 (`!(H:(A)hypermap) R x.
     plain_hypermap H /\ x IN dart H
     ==> (diskN H R (face_map H x) <=> diskN H R (edge_map H x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `R:A list`; `face_map H (x:A)`]
    DISKN_NODE_EQ) THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART; CFT_PLAIN_NF]);;

let DISKN_REDUCE = prove
 (`!(H:(A)hypermap) R w.
     planar_hypermap H /\ scycle H (rlink H) R /\ ALL (\y. y IN dart H) R /\
     w IN dart H
     ==> (diskN H R w <=> MEM w R \/ diskE H R w) /\
         (diskN H R (edge_map H w) <=> MEM (edge_map H w) R \/ diskE H R w)`,
  SIMP_TAC[DISKN_E; EDGE_MAP_IN_DART; DISKE_EDGE]);;

let DISKN_EDGE_EXCL = prove
 (`!(H:(A)hypermap) R z.
     planar_hypermap H /\ plain_hypermap H /\ scycle H (rlink H) R /\
     ALL (\y. y IN dart H) R /\ proper_ring H R /\ z IN dart H
     ==> ~(MEM z R /\ MEM (edge_map H z) R) /\
         ~(MEM z R /\ diskE H R z) /\
         ~(MEM (edge_map H z) R /\ diskE H R z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `R:A list`; `z:A`] DISKE_EDGE) THEN
  ASM_REWRITE_TAC[diskE] THEN
  ASM_MESON_TAC[DISKN_EDGE_RING; RING_IN_DISKN; EDGE_MAP_IN_DART]);;

let MEM_CHORD_PART = prove
 (`!(H:(A)hypermap) r x w.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x)
     ==> (MEM w (chord_ring H r x) \/ MEM w (chord_ring H r (edge_map H x)) <=>
          (w = x) \/ (w = edge_map H x) \/ MEM w r) /\
         ~(MEM w (chord_ring H r x) /\ MEM w (chord_ring H r (edge_map H x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `x:A`] CHORD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`] CHORD_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`i:num`; `r:A list`] UNIQ_ROT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP UNIQ_LIST_APPEND_DISJOINT) THEN
  SUBGOAL_THEN `!w:A. MEM w r <=> MEM w (CONS y1 p1) \/ MEM w (CONS y2 p2)`
  MP_TAC THENL
   [ASM_MESON_TAC[MEM_ROT_LIST; MEM_APPEND]; ALL_TAC] THEN
  ASM_REWRITE_TAC[chord_ring; MEM] THEN ASM_MESON_TAC[]);;

let Q_INV_EDGE = prove
 (`!(H:(A)hypermap) r x z.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x) /\
     z IN dart H /\
     (diskN H (chord_ring H r x) z \/ diskN H (chord_ring H r (edge_map H x)) z
      <=> diskN H r z) /\
     ~(diskN H (chord_ring H r x) z /\
       diskN H (chord_ring H r (edge_map H x)) z)
     ==> (diskN H (chord_ring H r x) (edge_map H z) \/
          diskN H (chord_ring H r (edge_map H x)) (edge_map H z) <=>
          diskN H r (edge_map H z)) /\
         ~(diskN H (chord_ring H r x) (edge_map H z) /\
           diskN H (chord_ring H r (edge_map H x)) (edge_map H z))`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 10 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `x:A`] CHORD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`] CHORD_RINGS_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY (fun q -> MP_TAC(ISPECL [`H:(A)hypermap`; q; `z:A`]
                               DISKN_REDUCE) THEN
                      MP_TAC(ISPECL [`H:(A)hypermap`; q; `z:A`]
                               DISKN_EDGE_EXCL))
   [`chord_ring (H:(A)hypermap) r x`;
    `chord_ring (H:(A)hypermap) r (edge_map H x)`; `r:A list`] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `z:A`] MEM_CHORD_PART) THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `edge_map H z:A`]
    MEM_CHORD_PART) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(edge_map H z = x <=> z = edge_map H (x:A)) /\
                (edge_map H z = edge_map H x <=> z = x)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[CFT_PLAIN_EE]; ALL_TAC] THEN
  ASM_CASES_TAC `z:A = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `z:A = edge_map H x` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC TAUT);;

let DISKN_CHORD_RING_WALK = prove
 (`!(H:(A)hypermap) r x q w.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x)
     ==> w IN dart H /\ list_path (clink H) w q /\ LAST (CONS w q) = x
         ==> (diskN H (chord_ring H r x) w \/
              diskN H (chord_ring H r (edge_map H x)) w <=>
              diskN H r w) /\
             ~(diskN H (chord_ring H r x) w /\
               diskN H (chord_ring H r (edge_map H x)) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`w:A`; `q:A list`] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[list_path; LAST_CLAUSES] THENL
   [GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`] DISKN_CHORD_BASE) THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `w:A` THEN STRIP_TAC] THEN
  SUBGOAL_THEN `(h:A) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLINK_DART]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o GEN_REWRITE_RULE I [clink]) THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[DISKN_NODE_EQ];
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[DISKN_FACE_EDGE] THEN
    MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `edge_map H (w:A)`]
      Q_INV_EDGE) THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; CFT_PLAIN_EE]]);;

let DISKN_CHORD_RING = prove
 (`!(H:(A)hypermap) r x w.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x) /\ w IN dart H
     ==> (diskN H (chord_ring H r x) w \/
          diskN H (chord_ring H r (edge_map H x)) w <=>
          diskN H r w) /\
         ~(diskN H (chord_ring H r x) w /\
           diskN H (chord_ring H r (edge_map H x)) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `x:A`] CHORD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `w:A`; `x:A`] CLINK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `p:A list`; `w:A`]
    DISKN_CHORD_RING_WALK) THEN
  ASM_REWRITE_TAC[]);;

let FBAND_ROT = prove
 (`!(H:(A)hypermap) n r y. fband H (rot_list n r) y <=> fband H r y`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[MEM_ROT_LIST]);;

let FBAND_CHORD_RING = prove
 (`!(H:(A)hypermap) r x y.
     plain_hypermap H /\ bridgeless H /\ scycle H (rlink H) r /\
     ALL (\z. z IN dart H) r /\ x IN dart H /\
     fband H r x /\ fband H r (edge_map H x)
     ==> (fband H (chord_ring H r x) y \/
          fband H (chord_ring H r (edge_map H x)) y <=>
          fband H r y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`] CHORD_DECOMP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `i:num`; `r:A list`; `y:A`] FBAND_ROT) THEN
  ASM_SIMP_TAC[chord_ring; CFT_PLAIN_EE; FBAND_APPEND; FBAND_CONS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EQ_TAC THEN STRIP_TAC THEN CFACE_TAC[]);;

let DISKF_CHORD_RING = prove
 (`!(H:(A)hypermap) r x y.
     planar_hypermap H /\ plain_hypermap H /\ bridgeless H /\
     connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r /\
     x IN diskE H r /\ fband H r x /\ fband H r (edge_map H x) /\ y IN dart H
     ==> (diskF H (chord_ring H r x) y <=>
          diskF H r y /\ ~diskF H (chord_ring H r (edge_map H x)) y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `x:A`] CHORD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`] CHORD_RINGS_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `fband H (chord_ring H r (edge_map H x)) y
    ==> ~diskF H (chord_ring H r x) (y:A)`
  MP_TAC THENL
   [REWRITE_TAC[FBAND_MEM_IFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:A) IN dart H` ASSUME_TAC THENL
     [UNDISCH_TAC
       `ALL (\z:A. z IN dart H) (chord_ring H r (edge_map H x))` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `z:A`]
      DISKN_CHORD_RING) THEN
    ASM_SIMP_TAC[RING_IN_DISKN] THEN ASM_MESON_TAC[DISKF_CFACE; diskF];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `y:A`]
    DISKN_CHORD_RING) THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:A list`; `x:A`; `y:A`]
    FBAND_CHORD_RING) THEN
  ASM_REWRITE_TAC[diskF] THEN CONV_TAC TAUT);;

let FBAND_ROT1 = prove
 (`!(H:(A)hypermap) l z. fband H (rot1 l) z <=> fband H l z`,
  REWRITE_TAC[FBAND_MEM_IFF] THEN MESON_TAC[MEM_ROT1]);;

let DISKN_ROT1 = prove
 (`!(H:(A)hypermap) l z. ~(l = []) ==> (diskN H (rot1 l) z <=> diskN H l z)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rot1] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `TL(l:A list)`; `HD(l:A list)`; `z:A`]
           DISKN_ROT1_CONS) THEN
  DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CONS_HD_TL THEN ASM_REWRITE_TAC[]);;

let DISKF_ROT1 = prove
 (`!(H:(A)hypermap) l z. ~(l = []) ==> (diskF H (rot1 l) z <=> diskF H l z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[diskF; FBAND_ROT1] THEN
  ASM_SIMP_TAC[DISKN_ROT1]);;

let CHORD_RING_ROT = prove
 (`!(H:(A)hypermap) R c u q d B i.
     scycle H (rlink H) R /\ c IN dart H /\
     rot_list i R = APPEND (CONS u q) (CONS d B) /\
     cface H c d /\ cface H (edge_map H c) u
     ==> chord_ring H R c = CONS c (CONS u q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `face_simple (H:(A)hypermap) R /\ uniq_list R`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SCYCLE_SIMPLE; FACE_SIMPLE_UNIQ]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (u:A) R /\ MEM (d:A) R` STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(ISPECL[`i:num`; `R:A list`] MEM_ROT_LIST)] THEN
    ASM_REWRITE_TAC[MEM_APPEND; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `fproj H R c = (d:A) /\ fproj H R (edge_map H c) = u`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL[`H:(A)hypermap`; `R:(A)list`; `c:A`; `d:A`] FPROJ_CFACE);
      MP_TAC(ISPECL[`H:(A)hypermap`; `R:(A)list`; `edge_map (H:(A)hypermap) c`;
                    `u:A`] FPROJ_CFACE)] THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[FBAND_MEM_IFF]; DISCH_THEN SUBST1_TAC]) THEN
    MATCH_MP_TAC SIMPLE_FPROJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[chord_ring] THEN
  MP_TAC(ISPECL[`R:(A)list`; `i:num`; `u:A`; `d:A`] ARC_ROT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC LEFT_ARC THEN MP_TAC(ISPECL[`i:num`; `R:(A)list`] UNIQ_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `d:A` o MATCH_MP UNIQ_LIST_APPEND_DISJOINT) THEN
  REWRITE_TAC[MEM] THEN CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* The node-cycle perimeter rc and its rlink rings REVERSE rc, MAP edge rc   *)
(* (embed.v rcN, edge_perimeter, URrrc, URerc, EercF), quasicubic facts and  *)
(* the face-orbit counting infrastructure.                                   *)
(* ------------------------------------------------------------------------- *)

let RCN = prove
 (`!(Gc:(A)hypermap) rc y.
     list_cycle (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc
     ==> (MEM (node_map Gc y) rc <=> MEM y rc)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `prevc rc (node_map Gc y) = (y:A)`
      (fun th -> ASM_MESON_TAC[th; PREVC_MEM]) THEN
    MATCH_MP_TAC NODEI THEN EXISTS_TAC `Gc:(A)hypermap` THEN
    MP_TAC(ISPECL [`node_map(Gc:(A)hypermap)`; `rc:(A)list`;
                   `prevc rc (node_map Gc (y:A))`] NEXTC_CYCLE) THEN
    ASM_SIMP_TAC[PREVC_MEM; NEXTC_PREVC] THEN MESON_TAC[];
    MP_TAC(ISPECL [`node_map(Gc:(A)hypermap)`; `rc:(A)list`]
      LIST_CYCLE_F_CLOSED) THEN
    ASM_SIMP_TAC[]]);;

let ARITY_FIX = prove
 (`!(Gc:(A)hypermap) x. x IN dart Gc /\ face_map Gc x = x ==> arity Gc x = 1`,
  SIMP_TAC[arity; orbit_size; ORBIT_FIXED; CARD_SING]);;

let EDGE_PERIMETER = prove
 (`!(Gc:(A)hypermap) rc x.
     plain_hypermap Gc /\
     scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\
     ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> ~MEM x rc \/ ~MEM (edge_map Gc x) rc`,
  REPEAT GEN_TAC THEN REWRITE_TAC[scycle] THEN STRIP_TAC THEN
  REWRITE_TAC[TAUT `(~a \/ ~b) <=> (a /\ b ==> F)`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map (Gc:(A)hypermap) (face_map Gc x) = edge_map Gc x`
    ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (face_map (Gc:(A)hypermap) x) rc` ASSUME_TAC THENL
   [SUBGOAL_THEN `MEM (node_map (Gc:(A)hypermap) (face_map Gc x)) rc`
      MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[RCN];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map (Gc:(A)hypermap) x = x` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `arity (Gc:(A)hypermap) x = 1` ASSUME_TAC THENL
   [MATCH_MP_TAC ARITY_FIX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[good_ring_arity] THEN
  ARITH_TAC);;

let RLINK_NODE = prove
 (`!(Gc:(A)hypermap) b. rlink Gc (node_map Gc b) b`,
  REPEAT GEN_TAC THEN CFACE_TAC[]);;

let LIST_CYCLE_MONO_MEM = prove
 (`!(R:A->A->bool) (R':A->A->bool) p.
       (!a b. MEM a p /\ R a b ==> R' a b) /\ list_cycle R p
         ==> list_cycle R' p`,
  REWRITE_TAC[list_cycle] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIST_PATH_MONO THEN
  EXISTS_TAC `R:A->A->bool` THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[MEM_LAST]);;

let RRC_SCYCLE = prove
 (`!(Gc:(A)hypermap) rc.
     scycle Gc (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc
     ==> scycle Gc (rlink Gc) (REVERSE rc)`,
  REWRITE_TAC[scycle; FACE_SIMPLE_REVERSE] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIST_CYCLE_MONO_MEM THEN
  EXISTS_TAC `\x y:A. prevc rc x = y` THEN
  SUBGOAL_THEN `~(rc:(A)list = [])` ASSUME_TAC THENL
   [ASM_MESON_TAC[list_cycle]; ALL_TAC] THEN
  ASM_SIMP_TAC[LIST_CYCLE_PREVC_REVERSE; MEM_REVERSE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`node_map(Gc:(A)hypermap)`; `rc:(A)list`;
                 `prevc rc (a:A)`] NEXTC_CYCLE) THEN
  ASM_SIMP_TAC[PREVC_MEM; NEXTC_PREVC] THEN CFACE_TAC[]);;

let ERC_IS_REVRING = prove
 (`!(Gc:(A)hypermap) rc. MAP (edge_map Gc) rc = rev_ring Gc (REVERSE rc)`,
  REWRITE_TAC[rev_ring; GSYM MAP_REVERSE; REVERSE_REVERSE]);;

let ERC_SCYCLE = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc
     ==> scycle Gc (rlink Gc) (MAP (edge_map Gc) rc)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ERC_IS_REVRING] THEN
  MATCH_MP_TAC SCYCLE_REV_RING THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RRC_SCYCLE THEN ASM_REWRITE_TAC[]);;

let EERCF = prove
 (`!(Gc:(A)hypermap) rc y.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc
     ==> (fband Gc (MAP (edge_map Gc) rc) y <=> fband Gc rc y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ERC_IS_REVRING] THEN
  SUBGOAL_THEN
    `fband (Gc:(A)hypermap) (rev_ring Gc (REVERSE rc)) y
     <=> fband Gc (REVERSE rc) y` SUBST1_TAC THENL
   [MATCH_MP_TAC FBAND_REV_RING THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`] RRC_SCYCLE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o MATCH_MP SCYCLE_CYCLE);
    REWRITE_TAC[FBAND_MEM_IFF; MEM_REVERSE]]);;

let ERC_ALL_DART = prove
 (`!(Gc:(A)hypermap) rc.
     ALL (\w. w IN dart Gc) rc
     ==> ALL (\z. z IN dart Gc) (MAP (edge_map Gc) rc)`,
  REWRITE_TAC[ALL_MAP; o_DEF; GSYM ALL_MEM] THEN
  MESON_TAC[EDGE_MAP_IN_DART]);;

let N3C = prove
 (`!(Gc:(A)hypermap) rc x.
     quasicubic Gc (\z. MEM z rc) /\ x IN dart Gc /\ ~MEM x rc
     ==> node_map Gc (node_map Gc (node_map Gc x)) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `\z:A. MEM z rc`; `x:A`] QUASICUBIC_EQ) THEN
  ASM_REWRITE_TAC[IN]);;

let QC_NEQ = prove
 (`!(Gc:(A)hypermap) rc x.
     quasicubic Gc (\z. MEM z rc) /\ x IN dart Gc /\ ~MEM x rc
     ==> ~(node_map Gc x = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `\z:A. MEM z rc`; `x:A`] QUASICUBIC_NEQ) THEN
  ASM_REWRITE_TAC[IN]);;

let ERC_BUNDLE = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc
     ==> scycle Gc (rlink Gc) (MAP (edge_map Gc) rc) /\
         ALL (\z. z IN dart Gc) (MAP (edge_map Gc) rc) /\
         (!y. fband Gc (MAP (edge_map Gc) rc) y <=> fband Gc rc y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ERC_SCYCLE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ERC_ALL_DART THEN ASM_REWRITE_TAC[];
    GEN_TAC THEN MATCH_MP_TAC EERCF THEN ASM_REWRITE_TAC[]]);;

let ARITY_CARD_CFACE = prove
 (`!(H:(A)hypermap) x. arity H x = CARD {z | cface H x z}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arity; orbit_size] THEN AP_TERM_TAC THEN
  REWRITE_TAC[cface; face; EXTENSION; IN_ELIM_THM]);;

let FINITE_CFACE_SET = prove
 (`!(H:(A)hypermap) x. FINITE {z:A | cface H x z}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{z:A | cface H x z} = orbit_map (face_map H) x`
    SUBST1_TAC THENL
   [REWRITE_TAC[cface; face; EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN dart H` THENL
   [ASM_MESON_TAC[ORBIT_FINITE; FINITE_DART; FACE_MAP_PERMUTES];
    ASM_MESON_TAC[ORBIT_FIXED; PERMUTES_FIX_OUTSIDE; FACE_MAP_PERMUTES;
                  FINITE_SING]]);;

let CFACE_SET_EQ = prove
 (`!(H:(A)hypermap) x y. x IN dart H /\ cface H x y
     ==> {z:A | cface H x z} = {z | cface H y z}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CFACE_TAC[]);;

let CARD_CFACE_SPLIT = prove
 (`!(H:(A)hypermap) x P.
     CARD {z:A | cface H x z /\ P z} + CARD {z | cface H x z /\ ~P z} =
     CARD {z | cface H x z}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  REWRITE_TAC[FINITE_CFACE_SET] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[]]);;

let ADJ_ARITY = prove
 (`!(Gc:(A)hypermap) rc x.
     ALL (\w. w IN dart Gc) rc /\ x IN dart Gc /\ ~(x IN kernel Gc rc)
     ==> ?w. MEM w rc /\ CARD {z:A | cface Gc x z} = arity Gc w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?w:A. MEM w rc /\ cface Gc x w` MP_TAC THENL
   [UNDISCH_TAC `~((x:A) IN kernel Gc rc)` THEN
    ASM_REWRITE_TAC[IN_KERNEL; fband; GSYM EX_MEM] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN EXISTS_TAC `w:A` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC (RAND_CONV) [ARITY_CARD_CFACE] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CFACE_SET_EQ THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[GSYM ALL_MEM]) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[]]);;

let FBAND_EDGE_RING = prove
 (`!(Gc:(A)hypermap) rc y.
      list_cycle (\a b. node_map Gc a = b) rc /\
      PAIRWISE (\a b. ~(a = b)) rc /\ MEM y rc
      ==> fband Gc rc (edge_map Gc y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MEM (face_map Gc (edge_map Gc (y:A))) rc` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`;
                  `face_map Gc (edge_map Gc (y:A))`] RCN) THEN
    ASM_REWRITE_TAC[edgeK];
    CFACE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The embedding functor (embed.v embed_functor): h commutes with edge on    *)
(* the kernel.  Core = induction on the size of diskN of a simple rlink      *)
(* cycle x :: p with x non-central and p central (EF_CORE); the two chord    *)
(* cases (EF_CASE_B: node x central, EF_CASE_C: node x not central) cut a    *)
(* smaller ring out of the ring p ++ [edge (node x)] (EF_P1_FACTS) and       *)
(* finish with CHORD_DESCENT; the darts of p left outside the new ring are   *)
(* excluded from its disk by the segment lemma SEG_OFF_DISKN.                *)
(* ------------------------------------------------------------------------- *)

let RLINK_DISKN_IFF = prove
 (`!(H:(A)hypermap) r w t.
     w IN dart H /\ rlink H w t /\ ~fband H r t
     ==> (diskN H r w <=> diskN H r t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rlink] THEN STRIP_TAC THEN
  ABBREV_TAC `v = face_map H (edge_map (H:(A)hypermap) w)` THEN
  SUBGOAL_THEN
    `v IN dart (H:(A)hypermap) /\ cface H v t /\ cface H t v /\ ~fband H r v /\
     t IN dart H /\ node_map H v = w` STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[DISKN_NODE_EQ] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `v:A`; `t:A`] DISKF_CFACE) THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `t:A`; `v:A`] DISKF_CFACE) THEN
  ASM_REWRITE_TAC[diskF] THEN CONV_TAC TAUT);;

let RLINK_PATH_DISKN_MEM = prove
 (`!(H:(A)hypermap) r l w.
     w IN dart H /\ list_path (rlink H) w l /\ ALL (\t. ~fband H r t) l
     ==> !y. MEM y (CONS w l) ==> (diskN H r y <=> diskN H r w)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `w:A` THEN
  REWRITE_TAC[list_path; ALL; MEM] THEN STRIP_TAC THENL
   [SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `h IN dart (H:(A)hypermap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RLINK_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `w:A`; `h:A`]
           RLINK_DISKN_IFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `h:A`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `y:A` THEN REWRITE_TAC[MEM] THEN
             STRIP_TAC THEN MP_TAC(SPEC `y:A` th)) THEN
  ASM_REWRITE_TAC[MEM]);;

let SEG_OFF_DISKN = prove
 (`!(H:(A)hypermap) q w l x.
     w IN dart H /\ list_path (rlink H) w l /\ ALL (\t. ~fband H q t) l /\
     MEM x (CONS w l) /\ ~diskN H q x
     ==> !y. MEM y (CONS w l) ==> ~diskN H q y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `q:(A)list`; `l:(A)list`; `w:A`]
           RLINK_PATH_DISKN_MEM) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~diskN (H:(A)hypermap) q x` THEN
  UNDISCH_TAC `MEM (x:A) (CONS w l)` THEN MESON_TAC[]);;

let RLINK_PATH_DISKN = prove
 (`!(H:(A)hypermap) r l w.
     w IN dart H /\ list_path (rlink H) w l /\ ALL (\t. ~fband H r t) l
     ==> (diskN H r w <=> diskN H r (LAST (CONS w l))) /\
         (diskN H r w ==> ALL (\t. diskN H r t) l)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP RLINK_PATH_DISKN_MEM) THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[LIST_PATH_MEM_LAST; MEM]);;

let DISKN_SUBSET_RING = prove
 (`!(H:(A)hypermap) q r.
     planar_hypermap H /\ plain_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\
     ALL (\z. z IN dart H) q /\ (!z. MEM z q ==> diskN H r z) /\
     (!y. diskN H q y /\ diskN H r y /\ ~MEM y q ==> ~MEM y r)
     ==> !z. diskN H q z ==> diskN H r z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!p w. w IN dart H /\ diskN (H:(A)hypermap) q w /\ diskN H r w /\
     list_path (dlink H q) w p ==> diskN H r (LAST (CONS w p))`
    ASSUME_TAC THENL
   [LIST_INDUCT_TAC THEN X_GEN_TAC `w:A` THEN
    REWRITE_TAC[list_path; LAST_CLAUSES; dlink; clink] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL[`node_map (H:(A)hypermap)`; `dart (H:(A)hypermap)`;
                      `h:A`] PERMUTES_IN_IMAGE) THEN
        ASM_REWRITE_TAC[NODE_MAP_PERMUTES];
        MATCH_MP_TAC DISKN_NODE_BWD THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC DISKN_NODE_BWD THEN ASM_REWRITE_TAC[]];
      FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
      ASM_SIMP_TAC[FACE_MAP_IN_DART; DISKN_FACE_OFFRING] THEN
      SUBGOAL_THEN `~MEM (w:A) r` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `w:A`] DISKN_REDUCE) THEN
      ASM_REWRITE_TAC[diskE] THEN STRIP_TAC THEN
      MP_TAC(ISPECL[`H:(A)hypermap`; `r:(A)list`; `face_map (H:(A)hypermap) w`]
               DISKN_NODE_EQ) THEN
      ASM_SIMP_TAC[FACE_MAP_IN_DART; PLAIN_EQ']];
    ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN DISCH_THEN(MP_TAC o MATCH_MP DISKN_DLINK_WITNESS) THEN
  DISCH_THEN(X_CHOOSE_THEN `y0:A`
               (X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `diskN H q (inverse (node_map H) y0) /\
     diskN (H:(A)hypermap) r (inverse (node_map H) y0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC DISKN_INVNODE THEN
    ASM_SIMP_TAC[RING_SUBSET_DISKN];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DISKN_SUBSET_DART THEN
  EXISTS_TAC `q:(A)list` THEN ASM_REWRITE_TAC[]);;

let CHORD_DESCENT = prove
 (`!(H:(A)hypermap) x p w t.
     planar_hypermap H /\ plain_hypermap H /\
     scycle H (rlink H) (CONS x p) /\ ALL (\z. z IN dart H) (CONS x p) /\
     ALL (\z. z IN dart H) (CONS w t) /\ ~diskN H (CONS w t) x /\
     (!z. MEM z (CONS w t) ==> diskN H (CONS x p) z) /\
     (!y. MEM y (CONS x p) /\ ~MEM y (CONS w t) ==> ~diskN H (CONS w t) y)
     ==> (!z. diskN H (CONS w t) z ==> diskN H (CONS x p) z) /\
         CARD (diskN H (CONS w t)) < CARD (diskN H (CONS x p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `!z. diskN H (CONS w t) z ==> diskN (H:(A)hypermap) (CONS x p) z`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DISKN_SUBSET_RING THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `diskN (H:(A)hypermap) (CONS x p) x` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_SIMP_TAC[FINITE_DISKN] THEN
  REWRITE_TAC[PSUBSET; SUBSET; EXTENSION; IN] THEN ASM_MESON_TAC[]);;

let H_EDGE_NODE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h y.
     preembedding Gc Gm h (kernel Gc rc) /\ y IN kernel Gc rc
     ==> edge_map Gc (node_map Gc y) IN kernel Gc rc /\
         h (edge_map Gc (node_map Gc y)) = edge_map Gm (node_map Gm (h y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `edge_map Gc (node_map Gc y) IN kernel (Gc:(A)hypermap) rc`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `y IN dart (Gc:(A)hypermap) /\ ~fband Gc rc y`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_KERNEL]; ALL_TAC] THEN
    REWRITE_TAC[IN_KERNEL] THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART] THEN
    ONCE_REWRITE_TAC[GSYM FBAND_FACE_MAP_EQ] THEN ASM_REWRITE_TAC[nodeK];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_map Gc (node_map Gc (y:A))` o CONJUNCT1 o
                  REWRITE_RULE[preembedding]) THEN
  ASM_REWRITE_TAC[nodeK] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[faceK]);;

let H_NODE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h y.
     preembedding Gc Gm h (kernel Gc rc) /\ y IN kernel Gc rc /\
     edge_central Gc Gm h (node_map Gc y)
     ==> h (node_map Gc y) = node_map Gm (h y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[edge_central] THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `y:A`] H_EDGE_NODE) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[EDGEI]);;

let HC_TRIPLE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     cubic_hypermap Gm /\ preembedding Gc Gm h (kernel Gc rc) /\
     x IN kernel Gc rc /\ node_map Gc x IN kernel Gc rc /\
     node_map Gc (node_map Gc x) IN kernel Gc rc /\
     node_map Gc (node_map Gc (node_map Gc x)) = x /\
     edge_central Gc Gm h (node_map Gc x) /\
     edge_central Gc Gm h (node_map Gc (node_map Gc x))
     ==> edge_central Gc Gm h x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`] H_NODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `node_map Gc (x:A)`] H_NODE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `node_map Gc (node_map Gc (x:A))`] H_EDGE_NODE) THEN
  ASM_REWRITE_TAC[edge_central] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[CUBIC_EQ_U]);;

let PROPER_RING_PRED = prove
 (`!(H:(A)hypermap) P c a.
     bridgeless H /\ c IN dart H /\ scycle H (rlink H) (CONS c a) /\
     (!t. MEM t a ==> P t) /\ ~P (edge_map H c)
     ==> proper_ring H (CONS c a)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[scycle; list_cycle; LAST_CLAUSES; list_path; rlink;
                PROPER_ONE] THEN
    MESON_TAC[BRIDGELESS_CFACE; CFACE_SYM_GEN];
    POP_ASSUM(K ALL_TAC) THEN
    STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THENL
     [REWRITE_TAC[PROPER_TWO; MEM] THEN MESON_TAC[];
      REWRITE_TAC[proper_ring] THEN MESON_TAC[]]]);;

let DISKN_NODE_CHORD = prove
 (`!(H:(A)hypermap) q c x.
     planar_hypermap H /\ plain_hypermap H /\ scycle H (rlink H) q /\
     ALL (\z. z IN dart H) q /\ proper_ring H q /\ MEM c q /\ x IN dart H /\
     (edge_map H c = node_map H x \/
      edge_map H c = node_map H (node_map H x))
     ==> ~diskN H q x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `q:(A)list`; `c:A`] DISKN_EDGE_RING) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DISKN_NODE_EQ; NODE_MAP_IN_DART]);;

let H_SPOKE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x y.
     preembedding Gc Gm h (kernel Gc rc) /\
     edge_map Gc x IN kernel Gc rc /\ y IN kernel Gc rc
     ==> ?p. list_path (rlink Gc) x p /\ cface Gc (LAST (CONS x p)) y /\
             ~(p = []) /\ face_simple Gc p /\
             ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm h z) p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `Gm:(B)hypermap`; `h:A->B`;
                `kernel (Gc:(A)hypermap) rc`] PREEMBEDDING_SIMPLE_PATH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC KERNEL_FCLOSED;
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let RLINK_PATH_START_SWAP = prove
 (`!(H:(A)hypermap) x y l.
     (!w. rlink H x w <=> rlink H y w) /\ list_path (rlink H) x l
     ==> list_path (rlink H) y l`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `l:(A)list` list_CASES) THEN
  REWRITE_TAC[list_path] THEN MESON_TAC[]);;

let CHORD_RING_EXCL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) h x w t.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     x IN dart Gc /\ w IN dart Gc /\ scycle Gc (rlink Gc) (CONS w t) /\
     ALL (\z. z IN dart Gc) t /\ (!y. MEM y t ==> edge_central Gc Gm h y) /\
     ~edge_central Gc Gm h (edge_map Gc w) /\
     (edge_map Gc w = node_map Gc x \/
      edge_map Gc w = node_map Gc (node_map Gc x))
     ==> ~diskN Gc (CONS w t) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `proper_ring (Gc:(A)hypermap) (CONS w t)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL[`Gc:(A)hypermap`;
                        `edge_central (Gc:(A)hypermap) (Gm:(B)hypermap)
                         (h:A->B)`] PROPER_RING_PRED) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC DISKN_NODE_CHORD THEN EXISTS_TAC `w:A` THEN
    ASM_REWRITE_TAC[ALL; MEM]]);;

let EF_FINISH = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) h x p w t.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     x IN dart Gc /\ scycle Gc (rlink Gc) (CONS x p) /\
     ALL (\z. z IN dart Gc) p /\
     w IN dart Gc /\ ~edge_central Gc Gm h w /\
     scycle Gc (rlink Gc) (CONS w t) /\ ALL (\z. z IN dart Gc) t /\
     (!y. MEM y t ==> edge_central Gc Gm h y) /\
     ~edge_central Gc Gm h (edge_map Gc w) /\
     (edge_map Gc w = node_map Gc x \/
      edge_map Gc w = node_map Gc (node_map Gc x)) /\
     (!z. MEM z (CONS w t) ==> diskN Gc (CONS x p) z) /\
     (!y. MEM y p /\ ~MEM y (CONS w t) ==> ~diskN Gc (CONS w t) y)
     ==> w IN dart Gc /\ ~edge_central Gc Gm h w /\
         scycle Gc (rlink Gc) (CONS w t) /\ ALL (\z. z IN dart Gc) t /\
         (!y. MEM y t ==> edge_central Gc Gm h y) /\
         (!z. diskN Gc (CONS w t) z ==> diskN Gc (CONS x p) z) /\
         CARD (diskN Gc (CONS w t)) < CARD (diskN Gc (CONS x p))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~diskN (Gc:(A)hypermap) (CONS w t) x` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`]
                   CHORD_RING_EXCL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CHORD_DESCENT THEN ASM_REWRITE_TAC[ALL] THEN
  X_GEN_TAC `y:A` THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MEM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let EF_P1_FACTS = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) h x p.
     planar_hypermap Gc /\ plain_hypermap Gc /\ plain_hypermap Gm /\
     x IN dart Gc /\ scycle Gc (rlink Gc) (CONS x p) /\
     ALL (\z. z IN dart Gc) p /\ (!y. MEM y p ==> edge_central Gc Gm h y)
     ==> node_map Gc x IN dart Gc /\ edge_map Gc (node_map Gc x) IN dart Gc /\
         edge_map Gc (edge_map Gc (node_map Gc x)) = node_map Gc x /\
         face_map Gc (edge_map Gc (node_map Gc x)) = x /\
         cface Gc (edge_map Gc (node_map Gc x)) x /\
         cface Gc x (edge_map Gc (node_map Gc x)) /\
         (edge_central Gc Gm h (edge_map Gc (node_map Gc x)) <=>
          edge_central Gc Gm h (node_map Gc x)) /\
         face_simple Gc (CONS x p) /\ PAIRWISE (\a b. ~(a = b)) (CONS x p) /\
         ~MEM x p /\ list_path (rlink Gc) x p /\
         rlink Gc (LAST (CONS x p)) x /\ diskN Gc (CONS x p) x /\
         diskN Gc (CONS x p) (node_map Gc x) /\
         list_path (rlink Gc) x (APPEND p [edge_map Gc (node_map Gc x)]) /\
         face_simple Gc (APPEND p [edge_map Gc (node_map Gc x)]) /\
         ALL (\z. z IN dart Gc) (APPEND p [edge_map Gc (node_map Gc x)]) /\
         (~MEM (node_map Gc x) (CONS x p)
          ==> diskN Gc (CONS x p) (edge_map Gc (node_map Gc x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `face_simple Gc (CONS x p) /\ PAIRWISE (\a b:A. ~(a = b)) (CONS x p) /\
     ~MEM (x:A) p /\ list_path (rlink Gc) x p /\ rlink Gc (LAST (CONS x p)) x`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `rlink (Gc:(A)hypermap)`; `CONS (x:A) p`]
             SCYCLE_PAIRWISE) THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `rlink (Gc:(A)hypermap)`; `CONS (x:A) p`]
             SCYCLE_SIMPLE) THEN
    UNDISCH_TAC `scycle Gc (rlink Gc) (CONS (x:A) p)` THEN
    REWRITE_TAC[SCYCLE_CONS; PAIRWISE_DISTINCT_CONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map Gc x IN dart Gc /\ edge_map Gc (node_map Gc x) IN dart Gc /\
     edge_map Gc (edge_map Gc (node_map Gc x)) = node_map Gc x /\
     face_map Gc (edge_map Gc (node_map Gc x)) = (x:A) /\
     cface Gc (edge_map Gc (node_map Gc x)) x /\
     cface Gc x (edge_map Gc (node_map Gc x))` STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `diskN Gc (CONS x p) x /\
     diskN (Gc:(A)hypermap) (CONS x p) (node_map Gc x)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DISKN_NODE_EQ] THEN MATCH_MP_TAC RING_SUBSET_DISKN THEN
    ASM_REWRITE_TAC[ALL; MEM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EDGE_CENTRAL_EDGE; ALL_APPEND; ALL] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path] THEN CFACE_TAC[];
    REWRITE_TAC[FACE_SIMPLE_ROT1] THEN
    UNDISCH_TAC `face_simple Gc (CONS (x:A) p)` THEN
    REWRITE_TAC[face_simple] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CFACE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `node_map Gc (x:A)`]
             DISKE_EDGE) THEN
    ASM_REWRITE_TAC[diskE; ALL] THEN SIMP_TAC[]]);;

let EF_CASE_B = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) h x p.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     plain_hypermap Gm /\ x IN dart Gc /\ scycle Gc (rlink Gc) (CONS x p) /\
     ALL (\z. z IN dart Gc) p /\ (!y. MEM y p ==> edge_central Gc Gm h y) /\
     node_map Gc (node_map Gc (node_map Gc x)) = x /\ ~(node_map Gc x = x) /\
     edge_central Gc Gm h (node_map Gc x) /\
     ~edge_central Gc Gm h (node_map Gc (node_map Gc x))
     ==> ?w t. w IN dart Gc /\ ~edge_central Gc Gm h w /\
               scycle Gc (rlink Gc) (CONS w t) /\ ALL (\z. z IN dart Gc) t /\
               (!y. MEM y t ==> edge_central Gc Gm h y) /\
               (!z. diskN Gc (CONS w t) z ==> diskN Gc (CONS x p) z) /\
               CARD (diskN Gc (CONS w t)) < CARD (diskN Gc (CONS x p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`; `x:A`;
                `p:(A)list`] EF_P1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
    [`nx = node_map (Gc:(A)hypermap) x`; `nnx = node_map (Gc:(A)hypermap) nx`;
     `enx = edge_map (Gc:(A)hypermap) nx`;
     `ennx = edge_map (Gc:(A)hypermap) nnx`] THEN
  SUBGOAL_THEN
    `~edge_central Gc Gm (h:A->B) ennx /\ nnx IN dart (Gc:(A)hypermap) /\
     ennx IN dart Gc /\ edge_map Gc ennx = nnx /\ face_map Gc ennx = nx /\
     face_map Gc (edge_map Gc x) = nnx` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "ennx" THEN ASM_SIMP_TAC[EDGE_CENTRAL_EDGE]; CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:A. rlink Gc ennx w <=> rlink Gc x w` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (nnx:A) (CONS x p)` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `diskN (Gc:(A)hypermap) (CONS x p) nnx` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `nx:A`] DISKN_NODE_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `diskN (Gc:(A)hypermap) (CONS x p) ennx` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `nnx:A`] DISKE_EDGE) THEN
    ASM_REWRITE_TAC[diskE; ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p1 = APPEND p [enx:A]` THEN
  SUBGOAL_THEN
    `list_path (rlink Gc) ennx p1 /\
     (!y. MEM y p1 ==> edge_central Gc Gm (h:A->B) y) /\
     LAST (CONS (ennx:A) p1) = enx /\ (!t. MEM t p1 ==> MEM t p \/ t = enx)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC RLINK_PATH_START_SWAP THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "p1" THEN REWRITE_TAC[MEM_APPEND; MEM; LAST_CONS_SNOC] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`cface Gc (ennx:A)`; `p1:(A)list`] FIRST_HIT_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:(A)list`
               (X_CHOOSE_THEN `l2:(A)list`
                  (CONJUNCTS_THEN2 ASSUME_TAC
                     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN
    `list_path (rlink Gc) ennx l1 /\ face_simple Gc l1 /\
     ~fband Gc l1 (ennx:A) /\ ALL (\z. z IN dart Gc) l1 /\
     (!y. MEM y l1 ==> edge_central Gc Gm (h:A->B) y) /\
     (!t. MEM t l1 ==> MEM t p1)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `list_path (rlink Gc) ennx (p1:(A)list)` THEN
    UNDISCH_TAC `face_simple (Gc:(A)hypermap) p1` THEN
    UNDISCH_TAC `ALL (\z. z IN dart (Gc:(A)hypermap)) p1` THEN
    UNDISCH_TAC `!y. MEM y p1 ==> edge_central Gc Gm (h:A->B) y` THEN
    UNDISCH_TAC `ALL (\z. ~cface Gc ennx z) (l1:(A)list)` THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; FACE_SIMPLE_APPEND'; ALL_APPEND;
                    MEM_APPEND; GSYM ALL_MEM; FBAND_MEM_IFF] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC
               (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[APPEND_NIL]) THEN
    UNDISCH_THEN `p1:(A)list = l1` SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~MEM (nx:A) (CONS x p)` ASSUME_TAC THENL
     [REWRITE_TAC[MEM; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      SUBGOAL_THEN `MEM (nx:A) l1` ASSUME_TAC THENL
       [UNDISCH_THEN `APPEND p [enx:A] = l1` (SUBST1_TAC o SYM) THEN
        ASM_REWRITE_TAC[MEM_APPEND];
        CFACE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `diskN (Gc:(A)hypermap) (CONS x p) enx` ASSUME_TAC THENL
     [MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `nx:A`] DISKE_EDGE) THEN
      ASM_REWRITE_TAC[diskE; ALL] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `scycle Gc (rlink Gc) (CONS ennx (l1:(A)list))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SCYCLE_CONS; rlink] THEN CFACE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~diskN (Gc:(A)hypermap) (CONS ennx l1) x` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`]
                     CHORD_RING_EXCL) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ennx:A`; `l1:(A)list`] THEN
    MATCH_MP_TAC EF_FINISH THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:A` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o C MATCH_MP (ASSUME `MEM (z:A) l1`)) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_SUBSET_DISKN THEN
      ASM_REWRITE_TAC[ALL; MEM];
      X_GEN_TAC `y:A` THEN REWRITE_TAC[MEM; DE_MORGAN_THM] THEN STRIP_TAC THEN
      UNDISCH_TAC `~MEM (y:A) l1` THEN REWRITE_TAC[] THEN
      UNDISCH_THEN `APPEND p [enx:A] = l1` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[MEM_APPEND]];
    FIRST_X_ASSUM(X_CHOOSE_THEN `b:A` (X_CHOOSE_THEN `c:(A)list` SUBST_ALL_TAC)
                    o MATCH_MP
                    (MESON[list_CASES]
                       `!l:(A)list. ~(l = []) ==> ?b c. l = CONS b c`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN
    SUBGOAL_THEN `?c'. p = APPEND l1 (CONS (b:A) c') /\ c = APPEND c' [enx]`
      (X_CHOOSE_THEN `c':(A)list`
         (CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)) THENL
     [MP_TAC(ISPECL[`p:(A)list`; `[enx:A]`; `l1:(A)list`; `c:(A)list`; `b:A`]
               APPEND_EQ_DECOMPOSE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(DISJ_CASES_THEN
                   (X_CHOOSE_THEN `r:(A)list` STRIP_ASSUME_TAC)) THENL
       [EXISTS_TAC `r:(A)list` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `[enx:A] = APPEND r (CONS b c)` THEN
      DISCH_THEN(MP_TAC o SYM) THEN
      STRUCT_CASES_TAC(ISPEC `r:(A)list` list_CASES) THEN
      REWRITE_TAC[APPEND; CONS_11; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (K ALL_TAC)) THEN CFACE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `rlink Gc (LAST (CONS ennx l1)) (b:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `list_path (rlink Gc) ennx (p1:(A)list)` THEN
      ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `scycle Gc (rlink Gc) (CONS ennx (l1:(A)list))`
      ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SCYCLE_CONS] THEN CFACE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~diskN (Gc:(A)hypermap) (CONS ennx l1) x` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`]
                     CHORD_RING_EXCL) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!t. MEM t (APPEND c' [x]) ==> ~fband Gc (CONS ennx l1) (t:A)`
      ASSUME_TAC THENL
     [SUBGOAL_THEN `face_simple Gc (APPEND (APPEND l1 [b]) (APPEND c' [x:A]))`
        MP_TAC THENL
       [UNDISCH_TAC `face_simple Gc (CONS x (APPEND l1 (CONS (b:A) c')))` THEN
        REWRITE_TAC[GSYM FACE_SIMPLE_ROT1; GSYM APPEND_ASSOC; APPEND];
        ALL_TAC] THEN
      REWRITE_TAC[FACE_SIMPLE_APPEND'] THEN
      DISCH_THEN(MP_TAC o MATCH_MP FBAND_OFF_SYM o CONJUNCT2 o CONJUNCT2) THEN
      DISCH_TAC THEN CFACE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `!y. MEM y (CONS b (APPEND c' [x])) ==> ~diskN Gc (CONS ennx l1) (y:A)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC SEG_OFF_DISKN THEN EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC[GSYM ALL_MEM] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `ALL (\z. z IN dart Gc) (APPEND l1 (CONS (b:A) c'))` THEN
        REWRITE_TAC[ALL_APPEND; ALL] THEN SIMP_TAC[];
        MATCH_MP_TAC LIST_PATH_CONS_SPLIT THEN
        MAP_EVERY EXISTS_TAC
          [`x:A`; `APPEND (APPEND l1 (CONS b c')) [x:A]`; `CONS (x:A) l1`] THEN
        REWRITE_TAC[APPEND; GSYM APPEND_ASSOC] THEN
        UNDISCH_TAC
          `scycle Gc (rlink Gc) (CONS x (APPEND l1 (CONS (b:A) c')))` THEN
        SIMP_TAC[scycle; LIST_CYCLE_CONS_PATH; GSYM APPEND_ASSOC; APPEND];
        REWRITE_TAC[MEM; MEM_APPEND]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`ennx:A`; `l1:(A)list`] THEN
    MATCH_MP_TAC EF_FINISH THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:A` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_SUBSET_DISKN THEN
      ASM_REWRITE_TAC[ALL; MEM; MEM_APPEND];
      X_GEN_TAC `y:A` THEN REWRITE_TAC[MEM; MEM_APPEND; DE_MORGAN_THM] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `~MEM (y:A) l1` THEN ASM_REWRITE_TAC[];
        ALL_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM; MEM_APPEND]]]);;

let EF_CASE_C = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     plain_hypermap Gm /\ preembedding Gc Gm h (kernel Gc rc) /\
     x IN dart Gc /\ scycle Gc (rlink Gc) (CONS x p) /\
     ALL (\z. z IN dart Gc) p /\ (!y. MEM y p ==> edge_central Gc Gm h y) /\
     (!y. diskN Gc (CONS x p) y ==> y IN kernel Gc rc) /\
     ~(node_map Gc x = x) /\ ~edge_central Gc Gm h (node_map Gc x)
     ==> ?w t. w IN dart Gc /\ ~edge_central Gc Gm h w /\
               scycle Gc (rlink Gc) (CONS w t) /\ ALL (\z. z IN dart Gc) t /\
               (!y. MEM y t ==> edge_central Gc Gm h y) /\
               (!z. diskN Gc (CONS w t) z ==> diskN Gc (CONS x p) z) /\
               CARD (diskN Gc (CONS w t)) < CARD (diskN Gc (CONS x p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`; `x:A`;
                `p:(A)list`] EF_P1_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
    [`nx = node_map (Gc:(A)hypermap) x`;
     `enx = edge_map (Gc:(A)hypermap) nx`] THEN
  SUBGOAL_THEN `~MEM (nx:A) (CONS x p) /\ ~edge_central Gc Gm (h:A->B) enx`
    STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MEM] THEN DISCH_TAC THEN
    UNDISCH_TAC `~edge_central Gc Gm (h:A->B) nx` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `diskN (Gc:(A)hypermap) (CONS x p) enx` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nx IN kernel Gc rc /\ (enx:A) IN kernel (Gc:(A)hypermap) rc`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `p1 = APPEND p [enx:A]` THEN
  SUBGOAL_THEN
    `LAST (CONS (x:A) p1) = enx /\ MEM (enx:A) p1 /\
     (!t. MEM t p1 ==> MEM t p \/ t = enx) /\ (!t. MEM t p ==> MEM t p1)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p1" THEN REWRITE_TAC[LAST_CONS_SNOC; MEM_APPEND; MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. fband Gc (CONS x p) t ==> fband (Gc:(A)hypermap) p1 t`
    ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "p1" THEN CFACE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `enx:A`; `enx:A`] H_SPOKE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `!z. MEM z q1 ==> z IN dart Gc /\ edge_central Gc Gm (h:A->B) (z:A)`
    ASSUME_TAC THENL
   [UNDISCH_TAC
      `ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm (h:A->B) z) q1` THEN
    REWRITE_TAC[GSYM ALL_MEM; IN_KERNEL] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`fband (Gc:(A)hypermap) p1`; `q1:(A)list`]
           FIRST_HIT_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:(A)list`
               (X_CHOOSE_THEN `l2:(A)list`
                  (CONJUNCTS_THEN2 ASSUME_TAC
                     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  SUBGOAL_THEN `~(l2:(A)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `q1:(A)list = APPEND q2 []` THEN
    REWRITE_TAC[APPEND_NIL] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `ALL (\z. ~fband Gc p1 z) (q1:(A)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN
    DISCH_THEN(MP_TAC o SPEC `LAST (q1:(A)list)`) THEN
    ASM_SIMP_TAC[MEM_LAST] THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
    EXISTS_TAC `enx:A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `cface Gc (LAST (CONS enx q1)) (enx:A)` THEN
    ASM_SIMP_TAC[LAST_CONS_NE];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2
               (fun th -> UNDISCH_TAC `~(l2:(A)list = [])` THEN
                REWRITE_TAC[th]) (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y1:A`
                  (X_CHOOSE_THEN `l2':(A)list` SUBST_ALL_TAC) o MATCH_MP
                  (MESON[list_CASES]
                     `!l:(A)list. ~(l = []) ==> ?b c. l = CONS b c`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD]) THEN UNDISCH_TAC `fband Gc p1 (y1:A)` THEN
  REWRITE_TAC[FBAND_MEM_IFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t. MEM t p1 ==> ~fband (Gc:(A)hypermap) q2 t` ASSUME_TAC THENL
   [MATCH_MP_TAC FBAND_OFF_SYM THEN
    UNDISCH_TAC `ALL (\z. ~fband Gc p1 z) (q2:(A)list)` THEN
    REWRITE_TAC[GSYM ALL_MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`y:A`; `p1:(A)list`] MEM_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:(A)list`
               (X_CHOOSE_THEN `p3:(A)list` (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `?m. APPEND m [enx:A] = CONS y p3 /\ APPEND p2 m = p`
    (X_CHOOSE_THEN `m:(A)list` STRIP_ASSUME_TAC) THENL
   [SUBGOAL_THEN `LAST (CONS y p3) = (enx:A)` ASSUME_TAC THENL
     [UNDISCH_TAC `LAST (CONS (x:A) p1) = enx` THEN
      SUBST1_TAC(SYM(ASSUME `APPEND p2 (CONS y p3) = (p1:(A)list)`)) THEN
      SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL];
      ALL_TAC] THEN
    EXISTS_TAC `BUTLAST (CONS (y:A) p3)` THEN
    SUBGOAL_THEN `APPEND (BUTLAST (CONS y p3)) [enx:A] = CONS y p3`
      ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `LAST (CONS y p3) = (enx:A)`)) THEN
      MATCH_MP_TAC APPEND_BUTLAST_LAST THEN REWRITE_TAC[NOT_CONS_NIL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[APPEND_RCANCEL]
                   `!l l1 l2:(A)list. APPEND l1 l = APPEND l2 l
                    ==> l1 = l2`) THEN
    EXISTS_TAC `[enx:A]` THEN ASM_REWRITE_TAC[GSYM APPEND_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:A. MEM t m ==> MEM t p` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `APPEND p2 m = (p:(A)list)`)) THEN
    REWRITE_TAC[MEM_APPEND] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `list_path (rlink Gc) enx q2 /\ rlink Gc (LAST (CONS enx q2)) (y1:A) /\
     face_simple (Gc:(A)hypermap) q2 /\
     (!z. MEM z q2 ==> z IN dart Gc /\ edge_central Gc Gm (h:A->B) z)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
      `!z. MEM z q1 ==> z IN dart Gc /\ edge_central Gc Gm (h:A->B) (z:A)` THEN
    UNDISCH_TAC `face_simple (Gc:(A)hypermap) q1` THEN
    UNDISCH_TAC `list_path (rlink Gc) enx (q1:(A)list)` THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path; FACE_SIMPLE_APPEND';
                    MEM_APPEND] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `list_path (rlink Gc) x p2 /\ list_path (rlink Gc) y p3 /\
     face_simple (Gc:(A)hypermap) (CONS y p3) /\ face_simple Gc p2 /\
     (!t. MEM t p2 ==> ~fband Gc (CONS y p3) t)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `face_simple (Gc:(A)hypermap) p1` THEN
    UNDISCH_TAC `list_path (rlink Gc) x (p1:(A)list)` THEN
    SUBST1_TAC(SYM(ASSUME `APPEND p2 (CONS y p3) = (p1:(A)list)`)) THEN
    REWRITE_TAC[LIST_PATH_APPEND; list_path; FACE_SIMPLE_APPEND'] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc (LAST (CONS enx q2)) (y:A)` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `scycle (Gc:(A)hypermap) (rlink Gc) (CONS enx (APPEND q2 m))`
    ASSUME_TAC THENL
   [REWRITE_TAC[scycle; LIST_CYCLE_CONS_PATH; GSYM FACE_SIMPLE_ROT1;
                GSYM APPEND_ASSOC] THEN
    SUBST1_TAC(ASSUME `APPEND m [enx:A] = CONS y p3`) THEN
    ASM_REWRITE_TAC[LIST_PATH_APPEND; list_path; FACE_SIMPLE_APPEND'] THEN
    CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `ALL (\z. z IN dart Gc) (APPEND q2 m) /\
     (!z. MEM z (APPEND q2 m) ==> edge_central Gc Gm (h:A->B) (z:A))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_APPEND] THEN
    UNDISCH_TAC
      `!z. MEM z q2 ==> z IN dart Gc /\ edge_central Gc Gm (h:A->B) (z:A)` THEN
    UNDISCH_TAC `!t:A. MEM t m ==> MEM t p` THEN
    UNDISCH_TAC `!y. MEM y p ==> edge_central Gc Gm (h:A->B) (y:A)` THEN
    UNDISCH_TAC `ALL (\z. z IN dart (Gc:(A)hypermap)) p` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~diskN (Gc:(A)hypermap) (CONS enx (APPEND q2 m)) x`
    ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`]
                   CHORD_RING_EXCL) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!t. MEM t p2 ==> ~fband (Gc:(A)hypermap) (CONS enx (APPEND q2 m)) t`
    ASSUME_TAC THENL
   [X_GEN_TAC `t:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (enx:A) (APPEND q2 m)`; `t:A`]
             FBAND_ROT1) THEN
    REWRITE_TAC[ROT1_CONS; GSYM APPEND_ASSOC] THEN
    SUBST1_TAC(ASSUME `APPEND m [enx:A] = CONS y p3`) THEN
    REWRITE_TAC[FBAND_APPEND] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBST1_TAC(SYM(ASSUME `APPEND p2 (CONS y p3) = (p1:(A)list)`)) THEN
      ASM_REWRITE_TAC[MEM_APPEND];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `!y'. MEM y' (CONS x p2) ==> ~diskN Gc (CONS enx (APPEND q2 m)) (y':A)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC SEG_OFF_DISKN THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM; MEM];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`enx:A`; `APPEND (q2:(A)list) m`] THEN
  MATCH_MP_TAC EF_FINISH THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:A` THEN REWRITE_TAC[MEM; MEM_APPEND] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `q2:(A)list`; `enx:A`]
               RLINK_PATH_DISKN) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [UNDISCH_TAC `ALL (\z. ~fband Gc p1 z) (q2:(A)list)` THEN
        UNDISCH_TAC
          `!t. fband Gc (CONS x p) t ==> fband (Gc:(A)hypermap) p1 t` THEN
        REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[ALL; MEM] THEN
      DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `y':A` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[MEM] THEN DISJ2_TAC THEN
    UNDISCH_TAC `~MEM (y':A) (CONS enx (APPEND q2 m))` THEN
    UNDISCH_TAC `MEM (y':A) p` THEN
    SUBST1_TAC(SYM(ASSUME `APPEND p2 m = (p:(A)list)`)) THEN
    REWRITE_TAC[MEM_APPEND; MEM; DE_MORGAN_THM] THEN MESON_TAC[]]);;

let EF_IH_TAC =
  DISCH_THEN(X_CHOOSE_THEN `w:A` (X_CHOOSE_THEN `t:(A)list` STRIP_ASSUME_TAC))
    THEN
  USE_THEN "ih" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`w:A`; `t:(A)list`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];;

let EF_CORE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\ cubic_hypermap Gm /\
     preembedding Gc Gm h (kernel Gc rc)
     ==> !n x p. CARD (diskN Gc (CONS x p)) < n /\ x IN dart Gc /\
                 ~edge_central Gc Gm h x /\ scycle Gc (rlink Gc) (CONS x p) /\
                 ALL (\z. z IN dart Gc) p /\
                 (!y. MEM y p ==> edge_central Gc Gm h y) /\
                 (!y. diskN Gc (CONS x p) y ==> y IN kernel Gc rc) ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT]; POP_ASSUM(LABEL_TAC "ih")] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `p:(A)list`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `diskN Gc (CONS x p) x /\ diskN Gc (CONS x p) (node_map Gc x) /\
     diskN (Gc:(A)hypermap) (CONS x p) (node_map Gc (node_map Gc x))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DISKN_NODE_EQ; NODE_MAP_IN_DART] THEN
    MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[ALL; MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `x IN kernel Gc rc /\ node_map Gc x IN kernel Gc rc /\
     node_map Gc (node_map Gc x) IN kernel (Gc:(A)hypermap) rc`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~fband Gc rc (x:A)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_KERNEL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map Gc (node_map Gc (node_map Gc x)) = x /\ ~(node_map Gc x = (x:A))`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `fband (Gc:(A)hypermap) rc`; `x:A`]
             QUASICUBIC_EQ) THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `fband (Gc:(A)hypermap) rc`; `x:A`]
             QUASICUBIC_NEQ) THEN
    ASM_REWRITE_TAC[IN] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `edge_central Gc Gm (h:A->B) (node_map Gc (x:A))` THENL
   [ASM_CASES_TAC
      `edge_central Gc Gm (h:A->B) (node_map Gc (node_map Gc (x:A)))` THENL
     [UNDISCH_TAC `~edge_central Gc Gm (h:A->B) (x:A)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HC_TRIPLE THEN EXISTS_TAC `rc:(A)list` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `h:A->B`; `x:A`;
                    `p:(A)list`] EF_CASE_B) THEN
      ASM_REWRITE_TAC[] THEN EF_IH_TAC];
    MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                  `x:A`; `p:(A)list`] EF_CASE_C) THEN
    ASM_REWRITE_TAC[] THEN EF_IH_TAC]);;

let NO_STRONG_CYCLE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\ cubic_hypermap Gm /\
     preembedding Gc Gm h (kernel Gc rc)
     ==> ~(?x p. x IN dart Gc /\ ~edge_central Gc Gm h x /\
                 scycle Gc (rlink Gc) (CONS x p) /\ ALL (\w. w IN dart Gc) p /\
                 ALL (edge_central Gc Gm h) p /\
                 (!z. diskN Gc (CONS x p) z ==> z IN kernel Gc rc))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP EF_CORE) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
                  SPECL[`SUC(CARD(diskN Gc (CONS (x:A) p)))`; `x:A`;
                        `p:(A)list`]) THEN
  ASM_REWRITE_TAC[LT] THEN
  UNDISCH_TAC `ALL (edge_central Gc Gm (h:A->B)) (p:(A)list)` THEN
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

let RLINK_CYCLE_DISKF_ABSORB = prove
 (`!(H:(A)hypermap) xp rc t z.
     planar_hypermap H /\ scycle H (rlink H) xp /\ ALL (\w. w IN dart H) xp /\
     scycle H (rlink H) rc /\ ALL (\w. w IN dart H) rc /\
     ALL (\w. ~fband H xp w) rc /\
     MEM t rc /\ diskF H xp t /\ MEM z rc
     ==> diskF H xp z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?a b. rc = APPEND a (CONS (t:A) b) /\ ~MEM t a`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FIRST_OCC_SPLIT]; ALL_TAC] THEN
  SUBGOAL_THEN `list_path (rlink H) t (APPEND b (a:(A)list))` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`H:(A)hypermap`; `rlink (H:(A)hypermap)`;
                  `LENGTH (a:(A)list)`; `rc:(A)list`] SCYCLE_ROT) THEN
    ASM_REWRITE_TAC[rot_list; DROP_APPEND_LENGTH; TAKE_APPEND_LENGTH;
                    APPEND] THEN
    REWRITE_TAC[scycle; LIST_CYCLE_CONS_PATH; LIST_PATH_APPEND] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `(t:A) IN dart H /\ ALL (\w. ~fband H xp w) (APPEND b a) /\
     ~fband H xp z /\ (z = t \/ MEM z (APPEND b a))`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `ALL (\w. ~fband H xp w) (rc:(A)list)` THEN
    UNDISCH_TAC `MEM (z:A) rc` THEN
    UNDISCH_TAC `ALL (\w. w IN dart (H:(A)hypermap)) rc` THEN
    ASM_REWRITE_TAC[ALL_APPEND; ALL; MEM_APPEND; MEM; GSYM ALL_MEM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`H:(A)hypermap`; `xp:(A)list`; `APPEND b (a:(A)list)`; `t:A`]
           RLINK_PATH_DISKN) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `diskF H xp (t:A)` THEN
  REWRITE_TAC[diskF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[]);;

let EMBED_FUNCTOR_FROM_NO_CYCLE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     plain_hypermap Gc /\ plain_hypermap Gm /\
     preembedding Gc Gm h (kernel Gc rc) /\
     ~(?x' p. x' IN dart Gc /\ x' IN kernel Gc rc /\
              ~edge_central Gc Gm h x' /\
              scycle Gc (rlink Gc) (CONS x' p) /\ ALL (\w. w IN dart Gc) p /\
              ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm h z) p) /\
     x IN kernel Gc rc /\ edge_map Gc x IN kernel Gc rc
     ==> h (edge_map Gc x) = edge_map Gm (h x)`,
  REPEAT GEN_TAC THEN INTRO_TAC "plainc plainm pre nocyc kx kex" THEN
  SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_KERNEL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM edge_central] THEN
  ASM_CASES_TAC `edge_central Gc Gm (h:A->B) x` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `Gm:(B)hypermap`; `h:A->B`;
                 `kernel (Gc:(A)hypermap) rc`] PREEMBEDDING_SIMPLE_PATH) THEN
  ASM_REWRITE_TAC[KERNEL_FCLOSED] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:A`; `x:A`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ALL (\w. w IN dart (Gc:(A)hypermap)) q` MP_TAC THENL
   [ASM_MESON_TAC[RLINK_PATH_DART]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:(A)list` (X_CHOOSE_THEN `y:A` SUBST_ALL_TAC) o
              MATCH_MP SNOC_DECOMP) THEN
  REMOVE_THEN "nocyc"
    (MP_TAC o SPECL [`x:A`; `p:(A)list`] o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST_CONS_SNOC; ALL_APPEND; ALL;
                              FACE_SIMPLE_ROT1; LIST_PATH_APPEND; list_path;
                              face_simple]) THEN
  ASM_REWRITE_TAC[SCYCLE_CONS; ALL_APPEND; ALL] THEN
  SUBGOAL_THEN `rlink Gc (LAST (CONS x p)) (x:A) /\ ~fband Gc p x`
    (fun th -> REWRITE_TAC[th]) THENL [CFACE_TAC[]; MESON_TAC[]]);;

let STRONG_CYCLE_FROM_ACHC_CYCLE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ plain_hypermap Gm /\
     scycle Gc (rlink Gc) rc /\ ALL (\w. w IN dart Gc) rc /\
     x IN kernel Gc rc /\ ~edge_central Gc Gm h x /\
     scycle Gc (rlink Gc) (CONS x p) /\ ALL (\w. w IN dart Gc) p /\
     ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm h z) p
     ==> ?x' p'. x' IN dart Gc /\ ~edge_central Gc Gm h x' /\
                 scycle Gc (rlink Gc) (CONS x' p') /\
                 ALL (\w. w IN dart Gc) p' /\
                 ALL (edge_central Gc Gm h) p' /\
                 (!z. diskN Gc (CONS x' p') z ==> z IN kernel Gc rc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_KERNEL]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!w. MEM w (CONS x p) ==> w IN kernel Gc rc /\ w IN dart (Gc:(A)hypermap)`
    ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
      `ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm (h:A->B) z) p` THEN
    UNDISCH_TAC `ALL (\z. z IN dart (Gc:(A)hypermap)) p` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. MEM w rc ==> ~fband (Gc:(A)hypermap) (CONS x p) w`
    ASSUME_TAC THENL
   [X_GEN_TAC `w:A` THEN DISCH_TAC THEN REWRITE_TAC[FBAND_MEM_IFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:A) IN kernel Gc rc` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; CFACE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?t. MEM t rc /\ diskF (Gc:(A)hypermap) (CONS x p) t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `proper_ring (Gc:(A)hypermap) (CONS x p)` ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL[`Gc:(A)hypermap`;
                          `\z. z IN kernel Gc rc /\
                           edge_central Gc (Gm:(B)hypermap) (h:A->B) z`]
                     PROPER_RING_PRED) THEN
      ASM_REWRITE_TAC[ALL_MEM] THEN ASM_SIMP_TAC[EDGE_CENTRAL_EDGE];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `scycle Gc (rlink Gc) (APPEND p [x]) /\ proper_ring Gc (APPEND p [x]) /\
       ALL (\w. w IN dart Gc) (APPEND p [x:A])` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[SCYCLE_ROT1_CONS; PROPER_RING_ROT1_CONS; ALL_APPEND; ALL];
      ALL_TAC] THEN
    SUBGOAL_THEN
      `edge_map Gc x IN dart Gc /\
       ~edge_central Gc Gm (h:A->B) (edge_map Gc (x:A))` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[EDGE_MAP_IN_DART; EDGE_CENTRAL_EDGE]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC
      [`edge_map Gc (x:A)`; `rev_ring (Gc:(A)hypermap) p`] THEN
    ASM_REWRITE_TAC[GSYM REV_RING_ROT1_CONS] THEN
    ASM_SIMP_TAC[SCYCLE_REV_RING; REV_RING_DART] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM ALL_MEM] THEN X_GEN_TAC `w:A` THEN
      ASM_SIMP_TAC[MEM_REV_RING] THEN DISCH_TAC THEN
      UNDISCH_TAC
        `ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm (h:A->B) z) p` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN
      DISCH_THEN(MP_TAC o SPEC `edge_map Gc (w:A)`) THEN
      ASM_SIMP_TAC[EDGE_CENTRAL_EDGE];
      X_GEN_TAC `z:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:A) IN dart Gc` ASSUME_TAC THENL
       [MATCH_MP_TAC DISKN_SUBSET_DART THEN
        EXISTS_TAC `rev_ring Gc (APPEND p [x:A])` THEN
        ASM_SIMP_TAC[REV_RING_DART];
        ALL_TAC] THEN
      SUBGOAL_THEN `~diskN (Gc:(A)hypermap) (CONS x p) z` ASSUME_TAC THENL
       [MP_TAC(ISPECL[`Gc:(A)hypermap`; `APPEND p [x:A]`; `z:A`]
                 DISKN_REV_RING) THEN
        ASM_REWRITE_TAC[DISKN_ROT1_CONS] THEN SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_KERNEL] THEN ASM_REWRITE_TAC[FBAND_MEM_IFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `diskF (Gc:(A)hypermap) (CONS x p) w` MP_TAC THENL
       [MATCH_MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `rc:(A)list`]
                       RLINK_CYCLE_DISKF_ABSORB) THEN
        EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[ALL; GSYM ALL_MEM];
        ALL_TAC] THEN
      MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (x:A) p`; `w:A`; `z:A`]
               DISKF_CFACE) THEN
      ASM_REWRITE_TAC[diskF] THEN
      SUBGOAL_THEN `(w:A) IN dart Gc /\ cface Gc w z`
        (fun th -> REWRITE_TAC[th]) THEN
      CFACE_TAC[]];
    MAP_EVERY EXISTS_TAC [`x:A`; `p:(A)list`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC
        `ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm (h:A->B) z) p` THEN
      REWRITE_TAC[GSYM ALL_MEM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN dart Gc` ASSUME_TAC THENL
     [MATCH_MP_TAC DISKN_SUBSET_DART THEN EXISTS_TAC `CONS (x:A) p` THEN
      ASM_REWRITE_TAC[ALL];
      ALL_TAC] THEN
    ASM_CASES_TAC `fband (Gc:(A)hypermap) (CONS x p) z` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
                      [FBAND_MEM_IFF]) THEN
      CFACE_TAC[];
      REWRITE_TAC[IN_KERNEL] THEN ASM_REWRITE_TAC[FBAND_MEM_IFF] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(?t:A. MEM t rc /\ diskF Gc (CONS x p) t)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `t:A` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DISKF_CFACE THEN EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC[diskF]]]);;

let EMBED_FUNCTOR_FROM_CORE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ plain_hypermap Gm /\
     scycle Gc (rlink Gc) rc /\ ALL (\w. w IN dart Gc) rc /\
     preembedding Gc Gm h (kernel Gc rc) /\
     ~(?x' p. x' IN dart Gc /\ ~edge_central Gc Gm h x' /\
              scycle Gc (rlink Gc) (CONS x' p) /\
              ALL (\w. w IN dart Gc) p /\
              ALL (edge_central Gc Gm h) p /\
              (!z. diskN Gc (CONS x' p) z ==> z IN kernel Gc rc)) /\
     x IN kernel Gc rc /\ edge_map Gc x IN kernel Gc rc
     ==> h (edge_map Gc x) = edge_map Gm (h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC EMBED_FUNCTOR_FROM_NO_CYCLE THEN EXISTS_TAC `rc:(A)list` THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x':A`; `p:(A)list`] STRONG_CYCLE_FROM_ACHC_CYCLE) THEN
  ASM_REWRITE_TAC[]);;

let EMBED_FUNCTOR = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\
     cubic_hypermap Gm /\ scycle Gc (rlink Gc) rc /\
     ALL (\w. w IN dart Gc) rc /\ preembedding Gc Gm h (kernel Gc rc) /\
     x IN kernel Gc rc /\ edge_map Gc x IN kernel Gc rc
     ==> h (edge_map Gc x) = edge_map Gm (h x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC EMBED_FUNCTOR_FROM_CORE THEN
  EXISTS_TAC `rc:(A)list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NO_STRONG_CYCLE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* h respects faces on the kernel (embed.v cface_ac_h, cface_h_ac,           *)
(* cface_inj_embed) and pre_hom_ring with its introduction rule.             *)
(* ------------------------------------------------------------------------- *)

let KERNEL_ITER_FACE = prove
 (`!n (Gc:(A)hypermap) rc x. kernel Gc rc x
   ==> kernel Gc rc (ITER n (face_map Gc) x)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  MATCH_MP_TAC KERNEL_FACE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let H_ITER_FACE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     preembedding Gc Gm h (kernel Gc rc) /\ kernel Gc rc x
     ==> !n. (h:A->B) (ITER n (face_map Gc) x) = ITER n (face_map Gm) (h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[preembedding] THEN STRIP_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ITER; IN; KERNEL_ITER_FACE]);;

let CFACE_AC_H = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x y.
     preembedding Gc Gm h (kernel Gc rc) /\ kernel Gc rc x /\ cface Gc x y
     ==> cface Gm (h x) (h y)`,
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[H_ITER_FACE]);;

let CFACE_H_AC = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x u.
     preembedding Gc Gm h (kernel Gc rc) /\ kernel Gc rc x /\ cface Gm (h x) u
     ==> ?y. cface Gc x y /\ (h:A->B) y = u`,
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[H_ITER_FACE]);;

let CFACE_INJ_EMBED = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x y.
     preembedding Gc Gm h (kernel Gc rc) /\ x IN dart Gc /\ kernel Gc rc x /\
     (h:A->B) x IN dart Gm /\ cface Gc x y /\ h x = h y ==> x = y`,
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER] THEN REPEAT STRIP_TAC THEN
  UNDISCH_THEN `y = ITER n (face_map Gc) (x:A)` SUBST_ALL_TAC THEN
  SUBGOAL_THEN `arity Gm ((h:A->B) x) = arity (Gc:(A)hypermap) x` MP_TAC THENL
   [ASM_MESON_TAC[preembedding; IN]; REWRITE_TAC[arity]] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:A`] H_ITER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  MP_TAC(ISPECL [`face_map (Gm:(B)hypermap)`; `dart(Gm:(B)hypermap)`;
                 `(h:A->B) x`; `n:num`] ORBIT_SIZE_DIVIDES) THEN
  MP_TAC(ISPECL [`face_map (Gc:(A)hypermap)`; `dart(Gc:(A)hypermap)`;
                 `x:A`; `n:num`] ORBIT_SIZE_DIVIDES) THEN
  ASM_SIMP_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN MESON_TAC[]);;

let RLINK_H = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h a b.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\
     cubic_hypermap Gm /\ scycle Gc (rlink Gc) rc /\
     ALL (\w. w IN dart Gc) rc /\ preembedding Gc Gm h (kernel Gc rc) /\
     a IN kernel Gc rc /\ edge_map Gc a IN kernel Gc rc /\ rlink Gc a b
     ==> rlink Gm (h a) (h b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[rlink] THEN
  SUBGOAL_THEN `edge_map Gm ((h:A->B) a) = h (edge_map Gc a)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC EMBED_FUNCTOR THEN
    EXISTS_TAC `rc:(A)list` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CFACE_AC_H THEN
  MAP_EVERY EXISTS_TAC [`Gc:(A)hypermap`; `rc:(A)list`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `edge_map (Gc:(A)hypermap) a IN kernel Gc rc` THEN
    REWRITE_TAC[IN];
    UNDISCH_TAC `rlink (Gc:(A)hypermap) a b` THEN REWRITE_TAC[rlink]]);;

let pre_hom_ring = new_definition
 `pre_hom_ring (Gc:(A)hypermap) (Gm:(B)hypermap) rc h x p <=>
    list_path (rlink Gc) x p /\
    (!z. MEM z (CONS x p) ==> z IN kernel Gc rc) /\
    scycle Gm (rlink Gm) (MAP h (CONS x p))`;;

let LIST_PATH_MAP_H = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\
     cubic_hypermap Gm /\ scycle Gc (rlink Gc) rc /\
     ALL (\w. w IN dart Gc) rc /\ preembedding Gc Gm h (kernel Gc rc)
     ==> !p x. list_path (rlink Gc) x p /\ x IN kernel Gc rc /\
               (!z. MEM z p ==> z IN kernel Gc rc)
               ==> list_path (rlink Gm) (h x) (MAP h p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; list_path] THEN X_GEN_TAC `x:A` THEN REWRITE_TAC[MEM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h':A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc (x:A) IN kernel Gc rc` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RLINK_H THEN
    MAP_EVERY EXISTS_TAC [`Gc:(A)hypermap`; `rc:(A)list`] THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let INTRO_PRE_HOM_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\
     cubic_hypermap Gm /\ scycle Gc (rlink Gc) rc /\
     ALL (\w. w IN dart Gc) rc /\ preembedding Gc Gm h (kernel Gc rc) /\
     x IN dart Gc /\ list_path (rlink Gc) x p /\
     rlink Gm (h (LAST (CONS x p))) (h x) /\
     (!z. MEM z (CONS x p) ==> z IN kernel Gc rc) /\
     face_simple Gm (MAP h (CONS x p))
     ==> pre_hom_ring Gc Gm rc h x p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[pre_hom_ring] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[scycle] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; list_cycle; NOT_CONS_NIL] THEN
  SUBGOAL_THEN `LAST (CONS ((h:A->B) x) (MAP h p)) = h (LAST (CONS x p))`
    SUBST1_TAC THENL
   [REWRITE_TAC[GSYM MAP] THEN MATCH_MP_TAC LAST_MAP THEN
    REWRITE_TAC[NOT_CONS_NIL];
    ALL_TAC] THEN
  REWRITE_TAC[list_path] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`]
           LIST_PATH_MAP_H) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEM];
    GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[MEM]]);;

(* ------------------------------------------------------------------------- *)
(* trivial_hom_ring (embed.v): a pre-homomorphic ring whose image has an     *)
(* empty inner face disk is itself an rlink cycle.  Induction on the length  *)
(* of the ring (THR_STEP); the chords of node (h y) and node (node (h y))    *)
(* either lie on the image ring (THR_ENY_MEM, THR_ENNY_MEM: an rlink         *)
(* predecessor in the image ring is unique, PHR_RLINK_PRED_EQ, and edge is   *)
(* then recovered from the face, PHR_EDGE_EQ) or cut off a shorter           *)
(* pre-homomorphic ring with empty inner disk (THR_CHORD: one descent lemma  *)
(* for both chords, via CHORD_RING_ROT and DISKF_CHORD_RING).                *)
(* ------------------------------------------------------------------------- *)

let embed_hyps = new_definition
 `embed_hyps (Gm:(B)hypermap) (Gc:(A)hypermap) rc h <=>
    planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
    bridgeless Gc /\ quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\
    cubic_hypermap Gm /\ bridgeless Gm /\ planar_hypermap Gm /\
    connected_hypermap Gm /\ scycle Gc (rlink Gc) rc /\
    ALL (\w. w IN dart Gc) rc /\ preembedding Gc Gm h (kernel Gc rc) /\
    (!z. z IN kernel Gc rc ==> h z IN dart Gm)`;;

let CFACE_EDGE_NODE = prove
 (`!(H:(A)hypermap) w. cface H (edge_map H (node_map H w)) w /\
                       cface H w (edge_map H (node_map H w))`,
  REPEAT GEN_TAC THEN CFACE_TAC[]);;

let DISKF_SNOC_CONS = prove
 (`!(H:(A)hypermap) l a z. diskF H (APPEND l [a]) z <=> diskF H (CONS a l) z`,
  REWRITE_TAC[diskF; DISKN_ROT1_CONS; FBAND_APPEND; FBAND_CONS;
              FBAND_SING] THEN
  CONV_TAC TAUT);;

let PRE_HOM_RING_FACTS = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p.
     embed_hyps Gm Gc rc h /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p
     ==> list_path (rlink Gc) x p /\
         (!z. MEM z (CONS x p)
              ==> z IN kernel Gc rc /\ z IN dart Gc /\ h z IN dart Gm) /\
         scycle Gm (rlink Gm) (MAP h (CONS x p)) /\
         ALL (\w. w IN dart Gm) (MAP h (CONS x p)) /\
         face_simple Gm (MAP h (CONS x p)) /\
         rlink Gm (h (LAST (CONS x p))) (h x) /\
         (!w. MEM w (MAP h (CONS x p)) ==> diskN Gm (MAP h (CONS x p)) w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[embed_hyps; pre_hom_ring] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `!z. MEM z (CONS x p) ==> z IN kernel Gc rc /\ z IN dart Gc /\
     (h:A->B) z IN dart (Gm:(B)hypermap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_KERNEL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ALL (\w. w IN dart Gm) (MAP (h:A->B) (CONS x p))`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ALL_MEM; MEM_MAP] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SUBSET_DISKN] THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `rlink (Gm:(B)hypermap)`;
                `MAP (h:A->B) (CONS x p)`] SCYCLE_SIMPLE) THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `rlink (Gm:(B)hypermap)`;
                `MAP (h:A->B) (CONS x p)`] SCYCLE_CYCLE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MAP; LIST_CYCLE_CONS_PATH; LIST_PATH_APPEND; list_path] THEN
  REWRITE_TAC[GSYM MAP] THEN SIMP_TAC[LAST_MAP; NOT_CONS_NIL]);;

let PHR_CFACE_EQ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p a b.
     embed_hyps Gm Gc rc h /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p /\
     MEM a (CONS x p) /\ MEM b (CONS x p) /\ cface Gm (h a) (h b) ==> a = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`; `p:(A)list`] PRE_HOM_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL[`h:A->B`; `CONS (x:A) p`] MAP_INJ_MEM) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SCYCLE_PAIRWISE THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `rlink (Gm:(B)hypermap)`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC SCYCLE_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `MAP (h:A->B) (CONS x p)`] THEN
    ASM_REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[]]);;

let PHR_RLINK_PRED_EQ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p a a' b.
     embed_hyps Gm Gc rc h /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p /\
     MEM a (CONS x p) /\ MEM a' (CONS x p) /\ MEM b (CONS x p) /\
     rlink Gm (h a) (h b) /\ rlink Gm (h a') (h b)
     ==> a = a'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`; `p:(A)list`] PRE_HOM_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC PHR_CFACE_EQ THEN
  MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                        `h:A->B`; `x:A`; `p:(A)list`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(h:A->B) a = h a'` (fun th -> REWRITE_TAC[th; CFACE_REFL]) THEN
  MATCH_MP_TAC NEXTC_INJ THEN EXISTS_TAC `MAP (h:A->B) (CONS x p)` THEN
  SUBGOAL_THEN `!w:A. MEM w (CONS x p) ==> MEM (h w) (MAP (h:A->B) (CONS x p))`
  ASSUME_TAC THENL [REWRITE_TAC[MEM_MAP] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SCYCLE_PAIRWISE]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `(h:A->B) b` THEN CONJ_TAC THENL
   [ALL_TAC; CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC RLINK_NEXTC_EQ THEN EXISTS_TAC `Gm:(B)hypermap` THEN
  ASM_SIMP_TAC[]);;

let PHR_EDGE_EQ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h t e.
     embed_hyps Gm Gc rc h /\ t IN kernel Gc rc /\
     edge_map Gc t IN kernel Gc rc /\ cface Gc (edge_map Gc t) e /\
     h e = edge_map Gm (h t)
     ==> edge_map Gc t = e`,
  REWRITE_TAC[embed_hyps] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CFACE_INJ_EMBED THEN
  MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                        `h:A->B`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[IN_KERNEL];
    ASM_MESON_TAC[IN];
    ASM_MESON_TAC[];
    MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                  `h:A->B`; `t:A`] EMBED_FUNCTOR) THEN
    ASM_REWRITE_TAC[]]);;

let DECOMP_TAC =
  SUBST1_TAC(SYM(ASSUME
    `APPEND a (APPEND (CONS u q) (CONS d b)) = CONS (x:A) p`));;

let THR_CHORD = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h n x p a u q d b c.
     embed_hyps Gm Gc rc h /\
     (!x p. LENGTH p < n /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p /\
            (!w. ~diskF Gm (MAP h (CONS x p)) w)
            ==> rlink Gc (LAST (CONS x p)) x) /\
     LENGTH p < SUC n /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p /\
     (!w. ~diskF Gm (MAP h (CONS x p)) w) /\
     APPEND a (APPEND (CONS u q) (CONS d b)) = CONS x p /\
     ~(APPEND a b = []) /\ c IN kernel Gc rc /\ cface Gc c d /\
     cface Gm (edge_map Gm (h c)) (h u) /\
     diskN Gm (MAP h (CONS x p)) (edge_map Gm (h c)) /\
     ~MEM (edge_map Gm (h c)) (MAP h (CONS x p))
     ==> rlink Gc c u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`; `p:(A)list`] PRE_HOM_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [embed_hyps]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pre_hom_ring]) THEN
  ABBREV_TAC `R = MAP (h:A->B) (CONS x p)` THEN
  SUBGOAL_THEN `MEM (u:A) (CONS x p) /\ MEM (d:A) (CONS x p)`
    STRIP_ASSUME_TAC THENL
   [DECOMP_TAC THEN REWRITE_TAC[MEM_APPEND; MEM]; ALL_TAC] THEN
  SUBGOAL_THEN
    `u IN kernel Gc rc /\ u IN dart Gc /\ (h:A->B) u IN dart Gm /\
     d IN kernel Gc rc /\ d IN dart Gc /\ h d IN dart Gm /\ (c:A) IN dart Gc /\
     h c IN dart Gm /\ MEM (h u) R /\ MEM (h d) R` STRIP_ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[IN_KERNEL] (ASSUME `(c:A) IN kernel Gc rc`)) THEN
    ASM_SIMP_TAC[] THEN EXPAND_TAC "R" THEN REWRITE_TAC[MEM_MAP] THEN
    DISCH_TAC THEN CONJ_TAC THENL [EXISTS_TAC `u:A`; EXISTS_TAC `d:A`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cface Gm ((h:A->B) c) (h d)` ASSUME_TAC THENL
   [MATCH_MP_TAC CFACE_AC_H THEN
    MAP_EVERY EXISTS_TAC [`Gc:(A)hypermap`; `rc:(A)list`] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:A) IN kernel Gc rc` THEN
    REWRITE_TAC[IN];
    ALL_TAC] THEN
  SUBGOAL_THEN `list_path (rlink Gc) u (APPEND q [c:A])` ASSUME_TAC THENL
   [SUBGOAL_THEN `list_path (rlink Gc) u (APPEND q (CONS (d:A) b))`
      MP_TAC THENL
     [MATCH_MP_TAC LIST_PATH_CONS_SPLIT THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `p:(A)list`; `a:(A)list`] THEN
      ASM_REWRITE_TAC[] THEN DECOMP_TAC THEN REWRITE_TAC[APPEND];
      REWRITE_TAC[LIST_PATH_APPEND; list_path] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `face_simple Gm (CONS ((h:A->B) u) (MAP h q)) /\
     ~fband Gm (CONS (h u) (MAP h q)) (h d)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `face_simple (Gm:(B)hypermap) R` THEN EXPAND_TAC "R" THEN
    DECOMP_TAC THEN REWRITE_TAC[MAP_APPEND; MAP; FACE_SIMPLE_APPEND'] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
      `!x. MEM x (CONS ((h:A->B) u) (MAP h q))
       ==> ~fband Gm (CONS (h d) (MAP h b)) x` THEN
    DISCH_THEN(MP_TAC o SPEC `(h:A->B) d` o MATCH_MP FBAND_OFF_SYM) THEN
    REWRITE_TAC[MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN `pre_hom_ring Gc Gm rc (h:A->B) u (APPEND q [c:A])`
    ASSUME_TAC THENL
   [MATCH_MP_TAC INTRO_PRE_HOM_RING THEN ASM_REWRITE_TAC[LAST_CONS_SNOC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[rlink];
      X_GEN_TAC `t:A` THEN REWRITE_TAC[MEM; MEM_APPEND] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN DECOMP_TAC THEN
      REWRITE_TAC[MEM_APPEND; MEM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MAP; MAP_APPEND; GSYM(CONJUNCT2 APPEND);
                  FACE_SIMPLE_ROT1] THEN
      ONCE_REWRITE_TAC[face_simple] THEN ASM_REWRITE_TAC[] THEN CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `proper_ring Gm R /\ (h:A->B) c IN diskE Gm R /\ fband Gm R (h c) /\
     fband Gm R (edge_map Gm (h c))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIZE_PROPER_RING THEN EXPAND_TAC "R" THEN
      REWRITE_TAC[LENGTH_MAP] THEN DECOMP_TAC THEN
      UNDISCH_TAC `~(APPEND (a:(A)list) b = [])` THEN
      REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[IN] THEN
      MP_TAC(ISPECL[`Gm:(B)hypermap`; `R:(B)list`; `(h:A->B) c`]
               DISKE_EDGE) THEN
      ASM_REWRITE_TAC[diskE];
      CFACE_TAC[];
      CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `chord_ring Gm R ((h:A->B) c) = CONS (h c) (CONS (h u) (MAP h q))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC CHORD_RING_ROT THEN
    MAP_EVERY EXISTS_TAC
      [`(h:A->B) d`; `APPEND (MAP (h:A->B) b) (MAP h a)`;
       `LENGTH (MAP (h:A->B) a)`] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN DECOMP_TAC THEN
    REWRITE_TAC[MAP_APPEND; MAP; ROT_LIST_APPEND; GSYM APPEND_ASSOC; APPEND];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL[`u:A`; `APPEND q [c:A]`]) THEN
  ASM_REWRITE_TAC[LAST_CONS_SNOC] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MP_TAC(AP_TERM `LENGTH:(A)list->num`
             (ASSUME
                `APPEND a (APPEND (CONS u q) (CONS d b)) = CONS (x:A) p`)) THEN
    UNDISCH_TAC `~(APPEND (a:(A)list) b = [])` THEN
    UNDISCH_TAC `LENGTH (p:(A)list) < SUC n` THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_APPEND; LENGTH] THEN ARITH_TAC;
    X_GEN_TAC `w:B` THEN
    REWRITE_TAC[MAP; MAP_APPEND; GSYM(CONJUNCT2 APPEND); DISKF_SNOC_CONS] THEN
    UNDISCH_THEN
      `chord_ring Gm R ((h:A->B) c) = CONS (h c) (CONS (h u) (MAP h q))`
      (SUBST1_TAC o SYM) THEN
    DISCH_TAC THEN SUBGOAL_THEN `(w:B) IN dart Gm` ASSUME_TAC THENL
     [MATCH_MP_TAC DISKN_SUBSET_DART THEN
      EXISTS_TAC `chord_ring Gm R ((h:A->B) c)` THEN
      ASM_SIMP_TAC[ALL_DART_CHORD_RING] THEN
      UNDISCH_TAC `diskF Gm (chord_ring Gm R ((h:A->B) c)) w` THEN
      SIMP_TAC[diskF];
      ALL_TAC] THEN
    MP_TAC(ISPECL[`Gm:(B)hypermap`; `R:(B)list`; `(h:A->B) c`; `w:B`]
             DISKF_CHORD_RING) THEN
    ASM_REWRITE_TAC[]]);;

let THR_ENY_MEM = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p1 z p2 y.
     embed_hyps Gm Gc rc h /\ x IN dart Gc /\
     pre_hom_ring Gc Gm rc h x (APPEND p1 (CONS z (APPEND p2 [y]))) /\
     cface Gm (h z) (node_map Gm (h y)) /\
     MEM (node_map Gm (h y))
         (MAP h (CONS x (APPEND p1 (CONS z (APPEND p2 [y])))))
     ==> rlink Gc (edge_map Gc (node_map Gc y)) z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = APPEND p1 (CONS (z:A) (APPEND p2 [y]))` THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`; `p:(A)list`] PRE_HOM_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [embed_hyps]) THEN
  ABBREV_TAC `t = LAST (CONS x (APPEND p1 (CONS (z:A) p2)))` THEN
  SUBGOAL_THEN
   `MEM (y:A) (CONS x p) /\ MEM (z:A) (CONS x p) /\ MEM (t:A) (CONS x p) /\
    rlink Gc t (y:A)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "t"] THEN
    UNDISCH_TAC `list_path (rlink Gc) x (p:(A)list)` THEN EXPAND_TAC "p" THEN
    REWRITE_TAC[MEM; MEM_APPEND] THEN
    MP_TAC(ISPECL[`x:A`; `APPEND p1 (CONS (z:A) p2)`] LIST_PATH_MEM_LAST) THEN
    REWRITE_TAC[MEM; MEM_APPEND; LIST_PATH_APPEND; list_path] THEN
    SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:A) IN kernel Gc rc /\ edge_map Gc t IN kernel Gc rc`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN CFACE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `MEM (node_map Gm ((h:A->B) y)) (MAP h (CONS x p))` THEN
  REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `u:A = t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC PHR_RLINK_PRED_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                          `h:A->B`; `x:A`; `p:(A)list`; `y:A`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[RLINK_NODE];
      MATCH_MP_TAC RLINK_H THEN
      MAP_EVERY EXISTS_TAC [`Gc:(A)hypermap`; `rc:(A)list`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `y:A`] H_EDGE_NODE) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `edge_map Gc (t:A) = edge_map Gc (node_map Gc y)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PHR_EDGE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`] THEN
    ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z:A = t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC PHR_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                          `h:A->B`; `x:A`; `p:(A)list`] THEN
    ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    CFACE_TAC[]]);;

let THR_ENNY_MEM = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p1 z p2 y.
     embed_hyps Gm Gc rc h /\ x IN dart Gc /\
     pre_hom_ring Gc Gm rc h x (APPEND p1 (CONS z (APPEND p2 [y]))) /\
     cface Gm (h z) (node_map Gm (h y)) /\
     node_map Gc y IN kernel Gc rc /\ h (node_map Gc y) = node_map Gm (h y) /\
     cface Gc (node_map Gc y) z /\
     MEM (node_map Gm (node_map Gm (h y)))
         (MAP h (CONS x (APPEND p1 (CONS z (APPEND p2 [y])))))
     ==> rlink Gc (edge_map Gc (node_map Gc (node_map Gc y))) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `p = APPEND p1 (CONS (z:A) (APPEND p2 [y]))` THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`; `p:(A)list`] PRE_HOM_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [embed_hyps]) THEN
  SUBGOAL_THEN
   `LAST (CONS (x:A) p) = y /\ MEM (y:A) (CONS x p) /\ MEM (z:A) (CONS x p) /\
    MEM (x:A) (CONS x p) /\ ~(p:(A)list = [])`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL; LAST_CONS_SNOC; MEM; MEM_APPEND;
             APPEND_EQ_NIL];
    ALL_TAC] THEN
  UNDISCH_TAC
   `MEM (node_map Gm (node_map Gm ((h:A->B) y))) (MAP h (CONS x p))` THEN
  REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t:A = x` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC PHR_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                          `h:A->B`; `x:A`; `p:(A)list`] THEN
    ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `MEM (HD p:A) (CONS x p) /\ rlink Gc x (HD p:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEM; HD_MEM] THEN
    UNDISCH_TAC `list_path (rlink Gc) x (p:(A)list)` THEN
    UNDISCH_TAC `~(p:(A)list = [])` THEN
    SPEC_TAC(`p:(A)list`, `p:(A)list`) THEN LIST_INDUCT_TAC THEN
    SIMP_TAC[list_path; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN kernel Gc rc /\ edge_map Gc x IN kernel Gc rc`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN CFACE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `node_map Gc (y:A)`] H_EDGE_NODE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `HD p:A = z` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC PHR_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                          `h:A->B`; `x:A`; `p:(A)list`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `rlink Gm ((h:A->B) x) (h (HD p))` MP_TAC THENL
     [MATCH_MP_TAC RLINK_H THEN
      MAP_EVERY EXISTS_TAC [`Gc:(A)hypermap`; `rc:(A)list`] THEN
      ASM_SIMP_TAC[];
      CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `edge_map Gc (x:A) = edge_map Gc (node_map Gc (node_map Gc y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PHR_EDGE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`] THEN
    ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    CFACE_TAC[]]);;

let THR_STEP = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h n.
     embed_hyps Gm Gc rc h /\
     (!x p. LENGTH p < n /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p /\
            (!u. ~diskF Gm (MAP h (CONS x p)) u)
            ==> rlink Gc (LAST (CONS x p)) x)
     ==> !x p. LENGTH p < SUC n /\ x IN dart Gc /\
               pre_hom_ring Gc Gm rc h x p /\
               (!u. ~diskF Gm (MAP h (CONS x p)) u)
               ==> rlink Gc (LAST (CONS x p)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`; `p:(A)list`] PRE_HOM_RING_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [embed_hyps]) THEN
  ABBREV_TAC `y = LAST (CONS (x:A) p)` THEN
  SUBGOAL_THEN `MEM (y:A) (CONS x p)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN MATCH_MP_TAC MEM_LAST THEN REWRITE_TAC[NOT_CONS_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `y IN kernel Gc rc /\ (y:A) IN dart Gc /\ (h:A->B) y IN dart Gm /\
     MEM (h y) (MAP h (CONS x p))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEM_MAP] THEN EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `diskN Gm (MAP h (CONS x p)) (node_map Gm ((h:A->B) y))`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gm:(B)hypermap`; `MAP (h:A->B) (CONS x p)`; `(h:A->B) y`]
             DISKN_NODE_EQ) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?z. MEM (z:A) (CONS x p) /\ cface Gm ((h:A->B) z) (node_map Gm (h y))`
    (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPEC `node_map Gm ((h:A->B) y)`
     (ASSUME `!u. ~diskF Gm (MAP (h:A->B) (CONS x p)) u`)) THEN
    REWRITE_TAC[diskF] THEN ASM_REWRITE_TAC[FBAND_MEM_IFF; MEM_MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A`
                 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `z IN kernel Gc rc /\ (z:A) IN dart Gc /\ (h:A->B) z IN dart Gm`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(z:A = x) /\ ~(z:A = y)` STRIP_ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?p1 p2. p = APPEND p1 (CONS (z:A) (APPEND p2 [y]))`
    (X_CHOOSE_THEN `p1:(A)list`
       (X_CHOOSE_THEN `p2:(A)list` SUBST_ALL_TAC)) THENL
   [MP_TAC(ISPECL[`z:A`; `p:(A)list`] MEM_SPLIT) THEN ANTS_TAC THENL
     [UNDISCH_TAC `MEM (z:A) (CONS x p)` THEN ASM_REWRITE_TAC[MEM];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:(A)list`
                 (X_CHOOSE_THEN `b:(A)list` SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `~(b:(A)list = [])` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(z:A = y)` THEN
      EXPAND_TAC "y" THEN REWRITE_TAC[LAST_CONS_SNOC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `b1:(A)list`
                    (X_CHOOSE_THEN `y1:A` SUBST_ALL_TAC) o MATCH_MP
                    SNOC_DECOMP) THEN
    SUBGOAL_THEN `y1:A = y` SUBST_ALL_TAC THENL
     [EXPAND_TAC "y" THEN
      SIMP_TAC[LAST_CONS_APPEND; NOT_CONS_NIL; LAST_CONS_SNOC];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`a:(A)list`; `b1:(A)list`] THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
    `edge_map Gc (node_map Gc y) IN kernel Gc rc /\
     (h:A->B) (edge_map Gc (node_map Gc y)) = edge_map Gm (node_map Gm (h y))`
    STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC H_EDGE_NODE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc (edge_map Gc (node_map Gc y)) (z:A)` ASSUME_TAC THENL
   [ASM_CASES_TAC
      `MEM (node_map Gm ((h:A->B) y))
       (MAP h (CONS x (APPEND p1 (CONS z (APPEND p2 [y])))))` THENL
     [MATCH_MP_TAC THR_ENY_MEM THEN
      MAP_EVERY EXISTS_TAC
        [`Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`; `x:A`; `p1:(A)list`;
         `p2:(A)list`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC THR_CHORD THEN
      MAP_EVERY EXISTS_TAC
        [`Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`; `n:num`; `x:A`;
         `APPEND p1 (CONS (z:A) (APPEND p2 [y]))`; `CONS (x:A) p1`;
         `p2:(A)list`; `y:A`; `[]:(A)list`] THEN
      ASM_SIMP_TAC[APPEND; APPEND_NIL; NOT_CONS_NIL; CFT_PLAIN_EE] THEN
      CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `cface Gc (node_map Gc y) (z:A) /\ node_map Gc y IN kernel Gc rc`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) (node_map Gc y) = node_map Gm (h y)` ASSUME_TAC THENL
   [MATCH_MP_TAC H_NODE THEN EXISTS_TAC `rc:(A)list` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[edge_central] THEN
    MATCH_MP_TAC EMBED_FUNCTOR THEN EXISTS_TAC `rc:(A)list` THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `edge_map Gc (node_map Gc (node_map Gc y)) IN kernel Gc rc /\
     (h:A->B) (edge_map Gc (node_map Gc (node_map Gc y)))
     = edge_map Gm (node_map Gm (node_map Gm (h y))) /\
     diskN Gm (MAP h (CONS x (APPEND p1 (CONS z (APPEND p2 [y])))))
     (node_map Gm (node_map Gm (h y)))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                  `node_map Gc (y:A)`] H_EDGE_NODE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`Gm:(B)hypermap`;
                  `MAP (h:A->B) (CONS x (APPEND p1 (CONS z (APPEND p2 [y]))))`;
                  `node_map Gm ((h:A->B) y)`] DISKN_NODE_EQ) THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc (edge_map Gc (node_map Gc (node_map Gc y))) (x:A)`
    MP_TAC THENL
   [ASM_CASES_TAC
      `MEM (node_map Gm (node_map Gm ((h:A->B) y)))
       (MAP h (CONS x (APPEND p1 (CONS z (APPEND p2 [y])))))` THENL
     [MATCH_MP_TAC THR_ENNY_MEM THEN
      MAP_EVERY EXISTS_TAC
        [`Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`; `p1:(A)list`; `z:A`;
         `p2:(A)list`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC THR_CHORD THEN
      MAP_EVERY EXISTS_TAC
        [`Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`; `n:num`; `x:A`;
         `APPEND p1 (CONS (z:A) (APPEND p2 [y]))`; `[]:(A)list`; `p1:(A)list`;
         `z:A`; `APPEND p2 [y:A]`] THEN
      ASM_SIMP_TAC[APPEND; APPEND_EQ_NIL; NOT_CONS_NIL; CFT_PLAIN_EE] THEN
      CFACE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `fband (Gc:(A)hypermap) rc`; `y:A`]
           QUASICUBIC_EQ) THEN
  ASM_REWRITE_TAC[IN] THEN ANTS_TAC THEN CFACE_TAC[]);;

let TRIVIAL_HOM_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x p.
     planar_hypermap Gc /\ plain_hypermap Gc /\ connected_hypermap Gc /\
     bridgeless Gc /\ quasicubic Gc (fband Gc rc) /\ plain_hypermap Gm /\
     cubic_hypermap Gm /\ bridgeless Gm /\ planar_hypermap Gm /\
     connected_hypermap Gm /\ scycle Gc (rlink Gc) rc /\
     ALL (\w. w IN dart Gc) rc /\ preembedding Gc Gm h (kernel Gc rc) /\
     (!z. z IN kernel Gc rc ==> (h:A->B) z IN dart Gm) /\ x IN dart Gc /\
     pre_hom_ring Gc Gm rc h x p /\ (!u. ~diskF Gm (MAP h (CONS x p)) u)
     ==> rlink Gc (LAST (CONS x p)) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `embed_hyps (Gm:(B)hypermap) (Gc:(A)hypermap) rc h`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[embed_hyps]; ALL_TAC] THEN
  SUBGOAL_THEN
    `!n x p. LENGTH p < n /\ x IN dart Gc /\ pre_hom_ring Gc Gm rc h x p /\
     (!u. ~diskF Gm (MAP (h:A->B) (CONS x p)) u)
     ==> rlink (Gc:(A)hypermap) (LAST (CONS x p)) x`
    (fun th ->
       MP_TAC(SPECL[`SUC(LENGTH(p:(A)list))`; `x:A`; `p:(A)list`] th) THEN
     ASM_REWRITE_TAC[LT]) THEN
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN MATCH_MP_TAC THR_STEP THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The perimeter lemmas (embed.v chordless_perimeter, fcard_adj_perimeter,   *)
(* adj_kernel_max).  nt_dFerc: a proper rlink ring whose tail lies on erc =  *)
(* MAP edge rc and whose disk misses rc has a dart strictly inside its face  *)
(* disk (induction on the ring length, NT_DF_AUX, with the two chord cases   *)
(* NT_DF_CASE_A / NT_DF_CASE_B, both computed by CHORD_RING_ROT and closed   *)
(* by NT_DF_CHORD); dFerc_ac: that face disk is exactly the kernel           *)
(* (DFERC_AC, via the spoke path).                                           *)
(* ------------------------------------------------------------------------- *)

let NT_DF_W_FACTS = prove
 (`!(Gc:(A)hypermap) rc w q1.
     plain_hypermap Gc /\ quasicubic Gc (\z. MEM z rc) /\
     scycle Gc (rlink Gc) (CONS w q1) /\ ALL (\z. z IN dart Gc) (CONS w q1) /\
     (!t. diskN Gc (CONS w q1) t ==> ~MEM t rc)
     ==> w IN dart Gc /\ ~MEM w rc /\ ~(node_map Gc w = w) /\
         node_map Gc (node_map Gc (node_map Gc w)) = w /\
         node_map Gc (node_map Gc w) = face_map Gc (edge_map Gc w) /\
         face_map Gc (edge_map Gc (face_map Gc (edge_map Gc w))) =
         node_map Gc w /\
         cface Gc (edge_map Gc (face_map Gc (edge_map Gc w)))
               (node_map Gc w) /\
         diskN Gc (CONS w q1) w /\
         diskN Gc (CONS w q1) (face_map Gc (edge_map Gc w)) /\
         diskN Gc (CONS w q1) (node_map Gc w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(w:A) IN dart Gc` ASSUME_TAC THENL
   [UNDISCH_TAC `ALL (\z. z IN dart (Gc:(A)hypermap)) (CONS w q1)` THEN
    REWRITE_TAC[ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `diskN Gc (CONS w q1) (w:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_SUBSET_DISKN THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (w:A) rc` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map Gc (node_map Gc (node_map Gc w)) = w /\ ~(node_map Gc w = (w:A))`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[N3C; QC_NEQ]; ALL_TAC] THEN
  SUBGOAL_THEN
    `node_map Gc (node_map Gc (w:A)) = face_map Gc (edge_map Gc w) /\
     face_map Gc (edge_map Gc (face_map Gc (edge_map Gc w))) = node_map Gc w /\
     cface Gc (edge_map Gc (face_map Gc (edge_map Gc w))) (node_map Gc w)`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[edgeK] THEN ASM_SIMP_TAC[DISKN_NODE_EQ] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (w:A) q1`;
                `face_map Gc (edge_map Gc (w:A))`] DISKN_NODE_EQ) THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK]);;

let NT_DF_CHORD = prove
 (`!(Gc:(A)hypermap) rc n q c l.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\
     (!q. LENGTH q < n /\ scycle Gc (rlink Gc) q /\ proper_ring Gc q /\
          ALL (\z. z IN dart Gc) q /\
          (!t. MEM t (TL q) ==> MEM t (MAP (edge_map Gc) rc)) /\
          (!t. diskN Gc q t ==> ~MEM t rc)
          ==> ?z. diskF Gc q z) /\
     LENGTH (CONS c l) < n /\ scycle Gc (rlink Gc) q /\ proper_ring Gc q /\
     ALL (\z. z IN dart Gc) q /\
     (!t. MEM t (TL q) ==> MEM t (MAP (edge_map Gc) rc)) /\
     (!t. diskN Gc q t ==> ~MEM t rc) /\
     c IN diskE Gc q /\ fband Gc q c /\ fband Gc q (edge_map Gc c) /\
     chord_ring Gc q c = CONS c l /\ (!t. MEM t l ==> MEM t (TL q))
     ==> ?z. diskF Gc q z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `diskN Gc q c /\ ~MEM (c:A) q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c:A) IN diskE Gc q` THEN SIMP_TAC[IN; diskE]; ALL_TAC] THEN
  SUBGOAL_THEN `(c:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (edge_map Gc c) (q:(A)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `q:(A)list`; `c:A`] DISKE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(c:A) IN diskE Gc q` THEN
    SIMP_TAC[IN; diskE];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `scycle Gc (rlink Gc) (CONS c l) /\ proper_ring Gc (CONS c l) /\
     ALL (\z. z IN dart Gc) (CONS (c:A) l)` STRIP_ASSUME_TAC THENL
   [UNDISCH_THEN `chord_ring Gc q c = CONS (c:A) l` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SCYCLE_CHORD_RING; PROPER_CHORD_RING; ALL_DART_CHORD_RING];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CONS (c:A) l`) THEN
  ASM_REWRITE_TAC[TL] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `t:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t:A) IN dart Gc` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `q:(A)list`; `c:A`; `t:A`]
             DISKN_CHORD_RING) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:A` ASSUME_TAC) THEN EXISTS_TAC `z:A` THEN
    SUBGOAL_THEN `(z:A) IN dart Gc` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_SUBSET_DART; diskF]; ALL_TAC] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `q:(A)list`; `c:A`; `z:A`]
             DISKF_CHORD_RING) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let ERC_PROPER = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ bridgeless Gc /\
     scycle Gc (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc /\
     ALL (\w. w IN dart Gc) rc /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     ~(rc = [])
     ==> proper_ring Gc (MAP (edge_map Gc) rc)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  POP_ASSUM(K ALL_TAC) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `CONS h t:(A)list`; `h:A`]
    EDGE_PERIMETER) THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `CONS h t:(A)list`] ERC_SCYCLE) THEN
  ASM_REWRITE_TAC[MEM] THEN
  STRUCT_CASES_TAC(ISPEC `t:(A)list` list_CASES) THENL
   [REWRITE_TAC[MAP; scycle; list_cycle; list_path; LAST; NOT_CONS_NIL;
                rlink] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ALL]) THEN
    ASM_MESON_TAC[CFT_PLAIN_EE; BRIDGELESS_CFACE];
    STRUCT_CASES_TAC(ISPEC `t':(A)list` list_CASES) THEN
    REWRITE_TAC[MAP; PROPER_TWO; proper_ring; CONS_11] THENL
     [ASM_MESON_TAC[CFT_PLAIN_EE; MEM]; MESON_TAC[]]]);;

let RRC_FACTS = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ bridgeless Gc /\
     scycle Gc (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc /\
     ALL (\w. w IN dart Gc) rc /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     ~(rc = [])
     ==> scycle Gc (rlink Gc) (REVERSE rc) /\
         ALL (\w. w IN dart Gc) (REVERSE rc) /\
         proper_ring Gc (REVERSE rc)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC RRC_SCYCLE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM ALL_MEM; MEM_REVERSE] THEN ASM_REWRITE_TAC[ALL_MEM];
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `REVERSE rc:(A)list`]
      PROPER_REV_RING) THEN
    ASM_REWRITE_TAC[GSYM ERC_IS_REVRING] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC ERC_PROPER THEN ASM_REWRITE_TAC[]]);;

let DISKN_REVERSE_MEM = prove
 (`!(Gc:(A)hypermap) rc w.
     list_cycle (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc /\
     diskN Gc (REVERSE rc) w
     ==> MEM w rc`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[diskN; GSYM EX_MEM; MEM_REVERSE; dconnect; dreach] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `y:A` (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `p:(A)list` MP_TAC) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `MEM (inverse (node_map Gc) y:A) rc` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`;
                   `inverse (node_map Gc) (y:A)`] RCN) THEN
    ASM_REWRITE_TAC[NODE_MAP_INVERSE; o_THM; edgeK];
    ALL_TAC] THEN
  STRUCT_CASES_TAC(ISPEC `p:(A)list` list_CASES) THEN
  ASM_REWRITE_TAC[list_path; dlink; LAST; MEM_REVERSE] THEN ASM_MESON_TAC[]);;

let DEEX = prove
 (`!(Gc:(A)hypermap) rc x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\
     scycle Gc (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc /\
     ALL (\w. w IN dart Gc) rc /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     ~(rc = []) /\ ~MEM x rc /\ ~MEM (edge_map Gc x) rc /\ x IN dart Gc
     ==> edge_map Gc x IN diskE Gc (MAP (edge_map Gc) rc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN; diskE] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] RRC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `REVERSE rc:(A)list`; `edge_map Gc (x:A)`]
    DISKN_REV_RING) THEN
  ASM_SIMP_TAC[GSYM ERC_IS_REVRING; EDGE_MAP_IN_DART] THEN
  DISCH_THEN(K ALL_TAC) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DISKN_REVERSE_MEM; SCYCLE_CYCLE];
    REWRITE_TAC[MEM_MAP] THEN ASM_MESON_TAC[CFT_PLAIN_EE]]);;

let NT_DF_CASE_A = prove
 (`!(Gc:(A)hypermap) rc n w q1.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     (!q. LENGTH q < n /\ scycle Gc (rlink Gc) q /\ proper_ring Gc q /\
          ALL (\z. z IN dart Gc) q /\
          (!t. MEM t (TL q) ==> MEM t (MAP (edge_map Gc) rc)) /\
          (!t. diskN Gc q t ==> ~MEM t rc)
          ==> ?z. diskF Gc q z) /\
     LENGTH (CONS w q1) < SUC n /\ scycle Gc (rlink Gc) (CONS w q1) /\
     proper_ring Gc (CONS w q1) /\ ALL (\z. z IN dart Gc) (CONS w q1) /\
     (!t. MEM t q1 ==> MEM t (MAP (edge_map Gc) rc)) /\
     (!t. diskN Gc (CONS w q1) t ==> ~MEM t rc) /\
     (!z. ~diskF Gc (CONS w q1) z) /\
     edge_map Gc (face_map Gc (edge_map Gc w)) IN diskE Gc (CONS w q1)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `w:A`; `q1:(A)list`]
           NT_DF_W_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
    `efex = edge_map Gc (face_map Gc (edge_map (Gc:(A)hypermap) w))` THEN
  SUBGOAL_THEN
    `efex IN dart Gc /\ edge_map Gc efex = face_map Gc (edge_map Gc (w:A))`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `diskN Gc (CONS w q1) efex /\ ~MEM (efex:A) (CONS w q1)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `efex IN diskE Gc (CONS (w:A) q1)` THEN SIMP_TAC[IN; diskE];
    ALL_TAC] THEN
  SUBGOAL_THEN `fband Gc (CONS w q1) (efex:A)` ASSUME_TAC THENL
   [MP_TAC(SPEC `efex:A` (ASSUME `!z:A. ~diskF Gc (CONS w q1) z`)) THEN
    REWRITE_TAC[diskF] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `z1:A` (X_CHOOSE_THEN `q1':(A)list` SUBST_ALL_TAC))
    (ISPEC `q1:(A)list` list_CASES) THENL
   [UNDISCH_TAC `proper_ring Gc [w:A]` THEN REWRITE_TAC[PROPER_ONE];
    ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc w (z1:A) /\ cface Gc (face_map Gc (edge_map Gc w)) z1`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `scycle Gc (rlink Gc) (CONS w (CONS (z1:A) q1'))` THEN
    REWRITE_TAC[scycle; LIST_CYCLE_CONS_PATH; APPEND; list_path] THEN
    STRIP_TAC THEN CFACE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y' = fproj Gc (CONS w (CONS (z1:A) q1')) efex` THEN
  SUBGOAL_THEN `MEM (y':A) (CONS w (CONS z1 q1')) /\ cface Gc efex y'`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y'" THEN MATCH_MP_TAC FPROJ_IN_FBAND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y':A = w)` ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (y':A) (CONS z1 q1')` ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (y':A) (CONS w (CONS z1 q1'))` THEN ASM_REWRITE_TAC[MEM];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`y':A`; `CONS (z1:A) q1'`] MEM_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:(A)list`
               (X_CHOOSE_THEN `p3:(A)list` MP_TAC)) THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z1':A` (X_CHOOSE_THEN `p2':(A)list` SUBST1_TAC))
    (ISPEC `p2:(A)list` list_CASES) THEN
  REWRITE_TAC[APPEND; CONS_11] THENL
   [DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC (K ALL_TAC)) THEN CFACE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC)] THEN
  SUBGOAL_THEN
    `chord_ring Gc (CONS w (CONS z1 (APPEND p2' (CONS y' p3)))) efex
     = CONS efex (CONS (z1:A) p2')` ASSUME_TAC THENL
   [MATCH_MP_TAC CHORD_RING_ROT THEN
    MAP_EVERY EXISTS_TAC [`y':A`; `APPEND p3 [w:A]`; `1`] THEN
    ASM_REWRITE_TAC[ROT_LIST_ONE; GSYM APPEND_ASSOC; APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `?z. diskF Gc (CONS w (CONS z1 (APPEND p2' (CONS (y':A) p3)))) z`
    MP_TAC THENL
   [MATCH_MP_TAC NT_DF_CHORD THEN
    MAP_EVERY EXISTS_TAC
      [`rc:(A)list`; `n:num`; `efex:A`; `CONS (z1:A) p2'`] THEN
    ASM_REWRITE_TAC[TL] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC
        `LENGTH (CONS w (CONS z1 (APPEND p2' (CONS (y':A) p3)))) < SUC n` THEN
      REWRITE_TAC[LENGTH; LENGTH_APPEND] THEN ARITH_TAC;
      CFACE_TAC[];
      REWRITE_TAC[MEM; MEM_APPEND] THEN MESON_TAC[]];
    ASM_REWRITE_TAC[]]);;

let NT_DF_NODE_OFF = prove
 (`!(Gc:(A)hypermap) rc w fex.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w) /\ w IN dart Gc /\ ~MEM w rc /\
     ~(node_map Gc w = w) /\ fex IN dart Gc /\
     face_map Gc (edge_map Gc fex) = node_map Gc w /\
     face_map Gc (edge_map Gc w) = fex /\ MEM fex (MAP (edge_map Gc) rc) /\
     MEM (node_map Gc w) (MAP (edge_map Gc) rc)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `list_cycle (\a b. node_map Gc a = b) rc /\
     face_simple (Gc:(A)hypermap) rc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `scycle Gc (\a b. node_map Gc a = b) (rc:(A)list)` THEN
    SIMP_TAC[scycle];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `MEM (edge_map Gc fex) rc /\
     MEM (face_map Gc (node_map Gc w)) (rc:(A)list)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `MEM (node_map Gc w) (MAP (edge_map Gc) (rc:(A)list))` THEN
    UNDISCH_TAC `MEM (fex:A) (MAP (edge_map Gc) rc)` THEN
    REWRITE_TAC[MEM_MAP] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:A`
                 (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r':A` STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[CFT_PLAIN_EE] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`;
                  `face_map Gc (edge_map Gc (r':A))`] RCN) THEN
    ASM_REWRITE_TAC[edgeK];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map Gc (node_map Gc w) = edge_map Gc (fex:A)`
    ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(node_map Gc w = edge_map Gc (fex:A))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~MEM (w:A) rc` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `w:A`] RCN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `!w. MEM w rc ==> good_ring_arity (Gc:(A)hypermap) w` THEN
  DISCH_THEN(MP_TAC o SPEC `edge_map Gc (fex:A)`) THEN
  ASM_REWRITE_TAC[good_ring_arity; arity] THEN
  SUBGOAL_THEN `orbit_size (face_map Gc) (edge_map Gc (fex:A)) = 2`
    (fun th -> REWRITE_TAC[th] THEN ARITH_TAC) THEN
  MATCH_MP_TAC ORBIT_SIZE_EQ_2 THEN EXISTS_TAC `dart (Gc:(A)hypermap)` THEN
  ASM_SIMP_TAC[FINITE_DART; FACE_MAP_PERMUTES; EDGE_MAP_IN_DART]);;

let NT_DF_CASE_B = prove
 (`!(Gc:(A)hypermap) rc n w q1.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     (!q. LENGTH q < n /\ scycle Gc (rlink Gc) q /\ proper_ring Gc q /\
          ALL (\z. z IN dart Gc) q /\
          (!t. MEM t (TL q) ==> MEM t (MAP (edge_map Gc) rc)) /\
          (!t. diskN Gc q t ==> ~MEM t rc)
          ==> ?z. diskF Gc q z) /\
     LENGTH (CONS w q1) < SUC n /\ scycle Gc (rlink Gc) (CONS w q1) /\
     proper_ring Gc (CONS w q1) /\ ALL (\z. z IN dart Gc) (CONS w q1) /\
     (!t. MEM t q1 ==> MEM t (MAP (edge_map Gc) rc)) /\
     (!t. diskN Gc (CONS w q1) t ==> ~MEM t rc) /\
     (!z. ~diskF Gc (CONS w q1) z) /\
     ~(edge_map Gc (face_map Gc (edge_map Gc w)) IN diskE Gc (CONS w q1))
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `w:A`; `q1:(A)list`]
           NT_DF_W_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
    `efex = edge_map Gc (face_map Gc (edge_map (Gc:(A)hypermap) w))` THEN
  SUBGOAL_THEN
    `efex IN dart Gc /\ edge_map Gc efex = face_map Gc (edge_map Gc (w:A))`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `MEM (face_map Gc (edge_map Gc w)) (CONS (w:A) q1)`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS (w:A) q1`;
                  `face_map Gc (edge_map Gc (w:A))`] DISKE_EDGE) THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART] THEN
    UNDISCH_TAC `~(efex IN diskE Gc (CONS (w:A) q1))` THEN
    REWRITE_TAC[IN; diskE] THEN ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `fex:A` (X_CHOOSE_THEN `p2:(A)list` SUBST_ALL_TAC))
    (ISPEC `q1:(A)list` list_CASES) THENL
   [UNDISCH_TAC `proper_ring Gc [w:A]` THEN REWRITE_TAC[PROPER_ONE];
    ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc w (fex:A) /\ list_path (rlink Gc) fex (APPEND p2 [w])`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `scycle Gc (rlink Gc) (CONS w (CONS (fex:A) p2))` THEN
    REWRITE_TAC[scycle; LIST_CYCLE_CONS_PATH; APPEND; list_path] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map Gc (edge_map Gc w) = (fex:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCYCLE_CFACE_EQ THEN
    MAP_EVERY EXISTS_TAC [`Gc:(A)hypermap`; `CONS w (CONS (fex:A) p2)`] THEN
    ASM_REWRITE_TAC[MEM] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc fex = (efex:A) /\ fex IN dart Gc`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `efex:A`] CFT_PLAIN_EE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ALL (\z. z IN dart Gc) (CONS w (CONS (fex:A) p2))` THEN
    REWRITE_TAC[ALL] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (node_map Gc w) (CONS w (CONS (fex:A) p2))`
    ASSUME_TAC THENL
   [REWRITE_TAC[MEM; DE_MORGAN_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [CFACE_TAC[];
      DISCH_TAC THEN
      MATCH_MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `w:A`; `fex:A`]
                     NT_DF_NODE_OFF) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `edge_map Gc (node_map Gc w) IN dart Gc /\
     edge_map Gc (edge_map Gc (node_map Gc w)) = node_map Gc w /\
     edge_map Gc (node_map Gc w) IN diskE Gc (CONS w (CONS fex p2)) /\
     fband Gc (CONS w (CONS fex p2)) (edge_map Gc (node_map Gc (w:A)))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; CFT_PLAIN_EE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN] THEN
      MP_TAC(ISPECL[`Gc:(A)hypermap`; `CONS w (CONS (fex:A) p2)`;
                    `node_map Gc (w:A)`] DISKE_EDGE) THEN
      ASM_SIMP_TAC[NODE_MAP_IN_DART; diskE];
      CFACE_TAC[]];
    ALL_TAC] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `p3:(A)list` SUBST_ALL_TAC))
    (ISPEC `p2:(A)list` list_CASES) THENL
   [UNDISCH_TAC `list_path (rlink Gc) fex (APPEND [] [w:A])` THEN
    REWRITE_TAC[APPEND; list_path] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `cface Gc (node_map Gc w) (z:A)` ASSUME_TAC THENL
   [UNDISCH_TAC `list_path (rlink Gc) fex (APPEND (CONS z p3) [w:A])` THEN
    REWRITE_TAC[APPEND; list_path] THEN CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `chord_ring Gc (CONS w (CONS fex (CONS z p3)))
     (edge_map Gc (node_map Gc w))
     = CONS (edge_map Gc (node_map Gc w)) (CONS (z:A) p3)` ASSUME_TAC THENL
   [MATCH_MP_TAC CHORD_RING_ROT THEN
    MAP_EVERY EXISTS_TAC [`w:A`; `[fex:A]`; `2`] THEN
    ASM_REWRITE_TAC[CFACE_EDGE_NODE] THEN
    REWRITE_TAC[TWO; ONE; rot_list; take_list; drop_list; NOT_CONS_NIL; HD; TL;
                APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z'. diskF Gc (CONS w (CONS fex (CONS (z:A) p3))) z'`
    MP_TAC THENL
   [MATCH_MP_TAC NT_DF_CHORD THEN
    MAP_EVERY EXISTS_TAC
      [`rc:(A)list`; `n:num`; `edge_map Gc (node_map Gc (w:A))`;
       `CONS (z:A) p3`] THEN
    ASM_REWRITE_TAC[TL] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `LENGTH (CONS w (CONS fex (CONS (z:A) p3))) < SUC n` THEN
      REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      CFACE_TAC[];
      REWRITE_TAC[MEM] THEN MESON_TAC[]];
    ASM_REWRITE_TAC[]]);;

let NT_DF_AUX = prove
 (`!(Gc:(A)hypermap) rc.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\ (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> !n q. LENGTH q < n /\ scycle Gc (rlink Gc) q /\ proper_ring Gc q /\
               ALL (\z. z IN dart Gc) q /\
               (!t. MEM t (TL q) ==> MEM t (MAP (edge_map Gc) rc)) /\
               (!t. diskN Gc q t ==> ~MEM t rc)
               ==> ?z. diskF Gc q z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT]; ALL_TAC] THEN
  X_GEN_TAC `q:(A)list` THEN STRIP_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `w:A` (X_CHOOSE_THEN `q1:(A)list` SUBST_ALL_TAC))
    (ISPEC `q:(A)list` list_CASES) THENL
   [UNDISCH_TAC `proper_ring Gc ([]:(A)list)` THEN REWRITE_TAC[PROPER_NIL];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
                 `((!z:A. ~diskF (Gc:(A)hypermap) (CONS w q1) z) ==> F)
                  ==> ?z. diskF Gc (CONS w q1) z`) THEN
  DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[TL]) THEN
  ASM_CASES_TAC
    `edge_map Gc (face_map Gc (edge_map Gc w)) IN diskE Gc
     (CONS (w:A) q1)` THENL
   [MATCH_MP_TAC NT_DF_CASE_A; MATCH_MP_TAC NT_DF_CASE_B] THEN
  MAP_EVERY EXISTS_TAC
    [`Gc:(A)hypermap`; `rc:(A)list`; `n:num`; `w:A`; `q1:(A)list`] THEN
  ASM_REWRITE_TAC[]);;

let DISKN_ERC_MEM = prove
 (`!(Gc:(A)hypermap) rc w.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\
     scycle Gc (\a b. node_map Gc a = b) rc /\ PAIRWISE (\a b. ~(a = b)) rc /\
     ALL (\w. w IN dart Gc) rc /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     ~(rc = []) /\ w IN dart Gc /\ diskN Gc (MAP (edge_map Gc) rc) w
     ==> ~MEM w rc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] RRC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `REVERSE rc:(A)list`; `w:A`]
    DISKN_REV_RING) THEN
  ASM_REWRITE_TAC[GSYM ERC_IS_REVRING] THEN
  ASM_MESON_TAC[RING_IN_DISKN; MEM_REVERSE]);;

let NT_DFERC = prove
 (`!(Gc:(A)hypermap) rc x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     ~(rc = []) /\ x IN diskE Gc (MAP (edge_map Gc) rc) /\
     fband Gc (MAP (edge_map Gc) rc) x /\
     fband Gc (MAP (edge_map Gc) rc) (edge_map Gc x)
     ==> ?y. diskF Gc (chord_ring Gc (MAP (edge_map Gc) rc) x) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`] ERC_BUNDLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `erc = MAP (edge_map Gc) (rc:(A)list)` THEN
  SUBGOAL_THEN `diskN Gc erc x /\ ~MEM (x:A) erc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN diskE Gc erc` THEN SIMP_TAC[IN; diskE]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (edge_map Gc x) (erc:(A)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `x:A`] DISKE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN diskE Gc erc` THEN
    SIMP_TAC[IN; diskE];
    ALL_TAC] THEN
  SUBGOAL_THEN `proper_ring (Gc:(A)hypermap) erc` ASSUME_TAC THENL
   [EXPAND_TAC "erc" THEN MATCH_MP_TAC ERC_PROPER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`] NT_DF_AUX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o
               SPECL[`SUC(LENGTH(chord_ring Gc (erc:(A)list) x))`;
                     `chord_ring Gc (erc:(A)list) x`]) THEN
  ASM_SIMP_TAC[LT; SCYCLE_CHORD_RING; PROPER_CHORD_RING;
               ALL_DART_CHORD_RING] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[chord_ring; TL] THEN EXPAND_TAC "erc" THEN
    MESON_TAC[MEM_ARC_LIST];
    X_GEN_TAC `t:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:A) IN dart Gc` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_SUBSET_DART; ALL_DART_CHORD_RING]; ALL_TAC] THEN
    SUBGOAL_THEN `diskN Gc (erc:(A)list) t` MP_TAC THENL
     [MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `x:A`; `t:A`]
               DISKN_CHORD_RING) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `t:A`] DISKN_ERC_MEM) THEN
    ASM_REWRITE_TAC[]]);;

let DFERC_WALK = prove
 (`!(Gc:(A)hypermap) rc R.
     plain_hypermap Gc /\ ALL (\z. z IN dart Gc) R /\
     (!y. y IN kernel Gc rc /\ diskN Gc R y ==> diskF Gc R y)
     ==> !p w. diskF Gc R w /\ list_path (rlink Gc) w p /\
               (!t. MEM t p ==> t IN kernel Gc rc)
               ==> diskF Gc R (LAST (CONS w p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN LIST_INDUCT_TAC THEN X_GEN_TAC `w:A` THEN
  REWRITE_TAC[list_path; LAST_CLAUSES; MEM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `(w:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART; diskF]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `diskF Gc R (face_map Gc (edge_map Gc (w:A)))` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [CFACE_TAC[];
      MP_TAC(ISPECL[`Gc:(A)hypermap`; `R:(A)list`;
                    `face_map Gc (edge_map Gc (w:A))`] DISKN_NODE_EQ) THEN
      ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; edgeK] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN UNDISCH_TAC `diskF Gc R (w:A)` THEN
      SIMP_TAC[diskF]];
    DISCH_TAC THEN MATCH_MP_TAC DISKF_CFACE THEN
    EXISTS_TAC `face_map Gc (edge_map Gc (w:A))` THEN ASM_REWRITE_TAC[] THEN
    CFACE_TAC[]]);;

let DFERC_AC = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\ (!w. MEM w rc ==> good_ring_arity Gc w) /\
     preembedding Gc Gm h (kernel Gc rc) /\ ~(rc = []) /\
     x IN diskE Gc (MAP (edge_map Gc) rc) /\
     fband Gc (MAP (edge_map Gc) rc) x /\
     fband Gc (MAP (edge_map Gc) rc) (edge_map Gc x)
     ==> !z. z IN dart Gc
             ==> (diskF Gc (chord_ring Gc (MAP (edge_map Gc) rc) x) z <=>
                  z IN kernel Gc rc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`] ERC_BUNDLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `erc = MAP (edge_map Gc) (rc:(A)list)` THEN
  SUBGOAL_THEN `diskN Gc erc x /\ ~MEM (x:A) erc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:A) IN diskE Gc erc` THEN SIMP_TAC[IN; diskE]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `~MEM (edge_map Gc x) (erc:(A)list)` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `x:A`] DISKE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:A) IN diskE Gc erc` THEN
    SIMP_TAC[IN; diskE];
    ALL_TAC] THEN
  SUBGOAL_THEN `proper_ring (Gc:(A)hypermap) erc` ASSUME_TAC THENL
   [EXPAND_TAC "erc" THEN MATCH_MP_TAC ERC_PROPER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cr = chord_ring Gc (erc:(A)list) x` THEN
  SUBGOAL_THEN `ALL (\z. z IN dart (Gc:(A)hypermap)) cr` ASSUME_TAC THENL
   [EXPAND_TAC "cr" THEN ASM_SIMP_TAC[ALL_DART_CHORD_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `!z. diskF Gc cr z ==> (z:A) IN kernel Gc rc` ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN dart Gc` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_SUBSET_DART; diskF]; ALL_TAC] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `x:A`; `z:A`]
             DISKF_CHORD_RING) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_KERNEL; diskF] THEN
    MP_TAC(SPEC `z:A` (ASSUME `!y:A. fband Gc erc y <=> fband Gc rc y`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN kernel Gc rc /\ diskN Gc cr y ==> diskF Gc cr (y:A)`
    ASSUME_TAC THENL
   [X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_KERNEL; diskF] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `x:A`; `y:A`]
             FBAND_CHORD_RING) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `y:A` (ASSUME `!y:A. fband Gc erc y <=> fband Gc rc y`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN EQ_TAC THENL
   [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] NT_DFERC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y0:A` ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:A) IN kernel Gc rc /\ y0 IN dart Gc` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[IN_KERNEL]; ALL_TAC] THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `edge_map Gc (y0:A)`; `z:A`] H_SPOKE) THEN
  ASM_SIMP_TAC[CFT_PLAIN_EE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `y1:A` (X_CHOOSE_THEN `p':(A)list` SUBST_ALL_TAC))
    (ISPEC `p:(A)list` list_CASES) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[list_path; ALL]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check
                         (is_conj o concl))) THEN
  SUBGOAL_THEN `diskF Gc cr (y1:A)` ASSUME_TAC THENL
   [MATCH_MP_TAC DISKF_CFACE THEN EXISTS_TAC `y0:A` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rlink Gc (edge_map Gc y0) (y1:A)` THEN
    ASM_SIMP_TAC[rlink; CFT_PLAIN_EE];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `cr:(A)list`] DFERC_WALK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL[`p':(A)list`; `y1:A`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC
      `ALL (\z. z IN kernel Gc rc /\ edge_central Gc Gm (h:A->B) z) p'` THEN
    REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC DISKF_CFACE THEN EXISTS_TAC `LAST (CONS (y1:A) p')` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `cface Gc (LAST (CONS (edge_map Gc y0) (CONS (y1:A) p'))) z` THEN
  REWRITE_TAC[LAST_CLAUSES] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DISKN_SUBSET_DART THEN EXISTS_TAC `cr:(A)list` THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `diskF Gc cr (LAST (CONS (y1:A) p'))` THEN
  SIMP_TAC[diskF]);;

let CHORDLESS_PERIMETER = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\
     (!w. MEM w rc ==> good_ring_arity Gc w) /\
     preembedding Gc Gm h (kernel Gc rc) /\
     x IN dart Gc /\ ~MEM x rc /\ ~MEM (edge_map Gc x) rc
     ==> x IN kernel Gc rc \/ edge_map Gc x IN kernel Gc rc`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN
  REWRITE_TAC[IN_KERNEL] THEN ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
  STRIP_TAC THEN MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`] ERC_BUNDLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(rc:(A)list = [])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `fband Gc [] (x:A)` THEN
    REWRITE_TAC[FBAND_NIL];
    ALL_TAC] THEN
  ABBREV_TAC `erc = MAP (edge_map Gc) (rc:(A)list)` THEN
  SUBGOAL_THEN `proper_ring (Gc:(A)hypermap) erc` ASSUME_TAC THENL
   [EXPAND_TAC "erc" THEN MATCH_MP_TAC ERC_PROPER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc x IN diskE Gc (erc:(A)list)` ASSUME_TAC THENL
   [EXPAND_TAC "erc" THEN MATCH_MP_TAC DEEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `fband Gc erc x /\ fband Gc erc (edge_map Gc x) /\
     fband Gc erc (edge_map Gc (edge_map Gc (x:A)))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CFT_PLAIN_EE]; ALL_TAC] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `edge_map Gc (x:A)`]
           NT_DFERC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:A` ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:A) IN dart Gc` ASSUME_TAC THENL
   [MATCH_MP_TAC DISKN_SUBSET_DART THEN
    EXISTS_TAC `chord_ring Gc erc (edge_map Gc (x:A))` THEN
    ASM_SIMP_TAC[ALL_DART_CHORD_RING; EDGE_MAP_IN_DART] THEN
    UNDISCH_TAC `diskF Gc (chord_ring Gc erc (edge_map Gc x)) (y:A)` THEN
    SIMP_TAC[diskF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN kernel Gc rc` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                  `edge_map Gc (x:A)`] DFERC_AC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN diskE Gc erc` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `x:A`] DISKE_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `edge_map Gc x IN diskE Gc (erc:(A)list)` THEN
    REWRITE_TAC[IN] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `diskF Gc (chord_ring Gc erc x) (y:A)` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                  `x:A`] DFERC_AC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `erc:(A)list`; `edge_map Gc (x:A)`; `y:A`]
           DISKF_CHORD_RING) THEN
  ASM_SIMP_TAC[CFT_PLAIN_EE]);;

let FCARD_ADJ_PERIMETER = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\
     (!w. MEM w rc ==> good_ring_arity Gc w) /\
     preembedding Gc Gm h (kernel Gc rc) /\
     x IN dart Gc /\ ~(x IN kernel Gc rc)
     ==> CARD {z | cface Gc x z /\ fband Gc rc (edge_map Gc z)} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?y. MEM y rc /\ cface Gc x (y:A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((x:A) IN kernel Gc rc)` THEN
    ASM_REWRITE_TAC[IN_KERNEL; FBAND_MEM_IFF];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `list_cycle (\a b. node_map Gc a = b) rc /\
     face_simple (Gc:(A)hypermap) rc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `scycle Gc (\a b. node_map Gc a = b) (rc:(A)list)` THEN
    SIMP_TAC[scycle];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart Gc /\ MEM (node_map Gc y) rc /\ cface Gc y x`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RCN] THEN CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y = edge_map Gc (node_map Gc (y:A)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `node_map Gc (y:A)`]
             EDGE_PERIMETER) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
    `{z | cface Gc x z /\ fband Gc rc (edge_map Gc z)}
     = {y, edge_map Gc (node_map Gc (y:A))}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:A` THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~a /\ ~b ==> F) ==> a \/ b`) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `cface Gc y (z:A) /\ z IN dart Gc /\ ~MEM z rc`
        STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~MEM (edge_map Gc z) (rc:(A)list)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN
          `MEM (z:A) (MAP (edge_map Gc) rc) /\
           MEM (edge_map Gc (node_map Gc y)) (MAP (edge_map Gc) rc)`
          STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[MEM_MAP] THEN CONJ_TAC THENL
           [EXISTS_TAC `edge_map Gc (z:A)`;
            EXISTS_TAC `node_map Gc (y:A)`] THEN
          ASM_SIMP_TAC[CFT_PLAIN_EE];
          CFACE_TAC[ERC_SCYCLE]];
        ALL_TAC] THEN
      MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                    `z:A`] CHORDLESS_PERIMETER) THEN
      ASM_REWRITE_TAC[IN_KERNEL] THEN
      SUBGOAL_THEN `fband Gc rc (z:A)` (fun th -> REWRITE_TAC[th]) THEN
      CFACE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC FBAND_EDGE_RING THEN ASM_REWRITE_TAC[]; CFACE_TAC[]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY] THEN
  ARITH_TAC);;

let ADJ_KERNEL_MAX = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc h x.
     planar_hypermap Gc /\ plain_hypermap Gc /\ bridgeless Gc /\
     connected_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     quasicubic Gc (\z. MEM z rc) /\
     (!w. MEM w rc ==> good_ring_arity Gc w) /\
     preembedding Gc Gm h (kernel Gc rc) /\
     x IN dart Gc /\ ~(x IN kernel Gc rc)
     ==> CARD {z | cface Gc x z /\ (edge_map Gc z) IN kernel Gc rc} <= 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                `x:A`] FCARD_ADJ_PERIMETER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] ADJ_ARITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL[`Gc:(A)hypermap`; `x:A`; `\z. fband Gc rc (edge_map Gc (z:A))`]
           CARD_CFACE_SPLIT) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `{z | cface Gc x z /\ ~fband Gc rc (edge_map Gc z)}
     = {z | cface Gc x z /\ edge_map Gc z IN kernel (Gc:(A)hypermap) rc}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_KERNEL] THEN
    ASM_MESON_TAC[CFT_DART; EDGE_MAP_IN_DART];
    ALL_TAC] THEN
  UNDISCH_TAC `!w. MEM w rc ==> good_ring_arity (Gc:(A)hypermap) w` THEN
  DISCH_THEN(MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[good_ring_arity] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cyclic successor under an injective map (NEXTC_MAP), and the remainder    *)
(* halves of patch.v's plain_patch and cubic_patch: PLAIN_PATCH and          *)
(* CUBIC_PATCH, instances of ORBIT_SIZE_INTERTWINE.                          *)
(* ------------------------------------------------------------------------- *)

let NEXTC_MAP = prove
 (`!(f:A->B) l x.
     PAIRWISE (\x y. ~(x = y)) l /\
     (!a b. MEM a l /\ MEM b l /\ f a = f b ==> a = b) /\ MEM x l
     ==> nextc (MAP f l) (f x) = f (nextc l x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
                REWRITE_RULE[MEM_EXISTS_EL]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `PAIRWISE (\x y. ~(x = y)) (MAP (f:A->B) l)` ASSUME_TAC THENL
   [MATCH_MP_TAC PAIRWISE_INJ_MAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(LENGTH(l:A list) = 0)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`MAP (f:A->B) l`; `i:num`] NEXTC_EL) THEN
  MP_TAC(ISPECL [`l:A list`; `i:num`] NEXTC_EL) THEN
  ASM_SIMP_TAC[LENGTH_MAP; EL_MAP; MOD_LT_EQ]);;

let PLAIN_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:B->B) bGd bGr /\ plain_hypermap G
     ==> plain_hypermap Gr`,
  REWRITE_TAC[plain_hypermap] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_INJ_HR) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_EDGE_R) THEN
  MP_TAC(ISPECL [`edge_map(Gr:(B)hypermap)`; `edge_map(G:(B)hypermap)`;
                 `dart(Gr:(B)hypermap)`; `dart(G:(B)hypermap)`;
                 `dart(Gr:(B)hypermap)`; `hr:B->B`; `x:B`]
    ORBIT_SIZE_INTERTWINE) THEN
  ASM_SIMP_TAC[FINITE_DART; EDGE_MAP_PERMUTES; EDGE_MAP_IN_DART;
               SUBSET_REFL] THEN
  DISCH_THEN(K ALL_TAC) THEN ASM_MESON_TAC[INJ]);;

let NODE_OFF_BORDER = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:B->B) bGd bGr /\ 2 <= LENGTH bGr
     ==> !x. x IN dart Gr /\ ~MEM x bGr ==> ~MEM (node_map Gr x) bGr`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN
  MATCH_MP_TAC PERM_COMPL_CLOSED THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_DART];
    REWRITE_TAC[SUBSET; IN_SET_OF_LIST] THEN
    MP_TAC(ISPECL
             [`G:(B)hypermap`; `Gd:(A)hypermap`; `Gr:(B)hypermap`; `hd:A->B`;
              `hr:B->B`; `bGd:(A)list`; `bGr:(B)list`] PATCH_BGR_IN_DART) THEN
    ASM_REWRITE_TAC[GSYM ALL_MEM];
    MP_TAC(ISPEC `Gr:(B)hypermap` NODE_MAP_PERMUTES) THEN
    DISCH_THEN(MP_TAC o MATCH_MP PERMUTES_INJECTIVE) THEN MESON_TAC[];
    X_GEN_TAC `w:B` THEN REWRITE_TAC[IN_SET_OF_LIST] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PATCH_CYCLE_R) THEN
    SUBGOAL_THEN `node_map (Gr:(B)hypermap) w = nextc bGr w` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NEXTC_CYCLE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC NEXTC_MEM THEN ASM_REWRITE_TAC[]]);;

let CUBIC_PATCH = prove
 (`!G Gd Gr hd hr bGd bGr.
     patch G Gd Gr (hd:A->B) (hr:B->B) bGd bGr /\ 2 <= LENGTH bGr /\
     cubic_hypermap G
     ==> quasicubic Gr (\z. MEM z bGr)`,
  REWRITE_TAC[quasicubic; cubic_hypermap; IN_MEM_LAM] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_INJ_HR) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PATCH_NODE_R) THEN
  MP_TAC(ISPECL [`node_map(Gr:(B)hypermap)`; `node_map(G:(B)hypermap)`;
                 `dart(Gr:(B)hypermap)`; `dart(G:(B)hypermap)`;
                 `{y | y IN dart Gr /\ ~MEM y (bGr:(B)list)}`; `hr:B->B`;
                 `x:B`] ORBIT_SIZE_INTERTWINE) THEN
  ASM_SIMP_TAC[FINITE_DART; NODE_MAP_PERMUTES; NODE_MAP_IN_DART;
               IN_ELIM_THM; SUBSET] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[NODE_OFF_BORDER]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[INJ]);;
