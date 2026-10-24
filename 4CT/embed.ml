(* ========================================================================= *)
(* 4CT/embed.ml                                                              *)
(*                                                                           *)
(* embed.v, second part (the first is embed_prelim.ml, the last              *)
(* embed_contract.ml): the embedding of a configuration map into a minimal   *)
(* counter-example.  embed_context bundles Coq's section hypotheses.  The    *)
(* preembedding h of the kernel is full (EMBED_FULL; Coq's three nested      *)
(* `suffices` statements are NO_BAD_RLINK_PATH_5, NO_PRE_HOM_RING_LE4 and    *)
(* NO_PRE_HOM_RING_SIDE, proved innermost first, with the path shortening    *)
(* SIMPLIFY_HOM_PATH and the ring reversal REVERSE_PRE_HOM_RING) and         *)
(* injective (PRE_EMBED_INJ), extends to the embedding embed of all darts    *)
(* off the ring (EMBEDE, EMBEDN, EMBED_INJ), and splits the counter-example  *)
(* into the disk map embed_disk and the remainder map embed_rem, patched     *)
(* along the ring (EMBED_PATCH), so that the remainder is planar, plain and  *)
(* quasicubic; embed preserves faces (CFACE_H1).                             *)
(* ========================================================================= *)

needs "4CT/birkhoff.ml";;

(* ------------------------------------------------------------------------- *)
(* The ambient hypotheses: Gc = configuration map with node-cycle ring rc,   *)
(* Gm = minimal counter-example, h = preembedding of the kernel, with the    *)
(* kernel of radius 2 around x0 (Coq embeddable + preembedding).             *)
(* ------------------------------------------------------------------------- *)

let embed_context = new_definition
 `embed_context (Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) <=>
    planar_hypermap Gc /\ plain_hypermap Gc /\
    bridgeless Gc /\ connected_hypermap Gc /\
    minimal_counter_example Gm /\
    planar_hypermap Gm /\ plain_hypermap Gm /\ cubic_hypermap Gm /\
    bridgeless Gm /\ connected_hypermap Gm /\ pentagonal Gm /\
    scycle Gc (\a b. node_map Gc a = b) rc /\
    PAIRWISE (\a b. ~(a = b)) rc /\
    ALL (\w. w IN dart Gc) rc /\
    quasicubic Gc (\z. MEM z rc) /\
    (!w. MEM w rc ==> good_ring_arity Gc w) /\
    preembedding Gc Gm h (kernel Gc rc) /\
    (!z. z IN kernel Gc rc ==> h z IN dart Gm) /\
    (?x0. x0 IN kernel Gc rc /\
          (!w. w IN kernel Gc rc
               ==> ?w1 w2. cface Gc x0 w1 /\ cface Gc w w2 /\
                           edge_map Gc w1 IN kernel Gc rc /\
                           cface Gc (edge_map Gc w1) (edge_map Gc w2)))`;;

(* ------------------------------------------------------------------------- *)
(* The embedding h1 = embed: h on the kernel, extended by one edge or node   *)
(* step (Coq embed).                                                         *)
(* ------------------------------------------------------------------------- *)

let embed = new_definition
 `embed (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) (x:A) =
    if x IN kernel Gc rc then h x
    else if edge_map Gc x IN kernel Gc rc then edge_map Gm (h (edge_map Gc x))
    else if node_map Gc x IN kernel Gc rc
         then face_map Gm (edge_map Gm (h (node_map Gc x)))
    else edge_map Gm
           (node_map Gm (node_map Gm (h (node_map Gc (edge_map Gc x)))))`;;

(* ------------------------------------------------------------------------- *)
(* The disk map: the darts of Gc off the ring rc, with edge and face maps    *)
(* skipping the ring (Coq embed_disk); the maps fix the darts outside.       *)
(* ------------------------------------------------------------------------- *)

let embd_D = new_definition
 `embd_D (Gc:(A)hypermap) (rc:(A)list) = {x | x IN dart Gc /\ ~MEM x rc}`;;

let embd_nmap = new_definition
 `embd_nmap (Gc:(A)hypermap) (rc:(A)list) x =
    if x IN embd_D Gc rc then node_map Gc x else x`;;

let embd_emap = new_definition
 `embd_emap (Gc:(A)hypermap) (rc:(A)list) x =
    if x IN embd_D Gc rc
    then (if ~MEM (edge_map Gc x) rc then edge_map Gc x
          else edge_map Gc (node_map Gc (edge_map Gc x)))
    else x`;;

let embd_fmap = new_definition
 `embd_fmap (Gc:(A)hypermap) (rc:(A)list) x =
    if x IN embd_D Gc rc
    then (if ~MEM (face_map Gc x) rc then face_map Gc x
          else face_map Gc (face_map Gc x))
    else x`;;

let embed_disk = new_definition
 `embed_disk (Gc:(A)hypermap) (rc:(A)list) =
    mk_hypermap (embd_D Gc rc, embd_emap Gc rc, embd_nmap Gc rc,
                 embd_fmap Gc rc)`;;

(* ------------------------------------------------------------------------- *)
(* The remainder map: the darts of Gm outside the image of the disk          *)
(* interior, with node and face maps rerouted along the ring (Coq            *)
(* embed_rem).                                                               *)
(* ------------------------------------------------------------------------- *)

let rdom' = new_definition
 `rdom' (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) =
    {x | ?u. u IN embd_D Gc rc /\ ~MEM u (MAP (edge_map Gc) rc) /\
             x = embed Gc Gm rc h u}`;;

let embr_D = new_definition
 `embr_D (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) =
    {x | x IN dart Gm /\ ~(x IN rdom' Gc Gm rc h)}`;;

let embr_emap = new_definition
 `embr_emap (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) x =
    if x IN embr_D Gc Gm rc h then edge_map Gm x else x`;;

let embr_nmap = new_definition
 `embr_nmap (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) x =
    if x IN embr_D Gc Gm rc h
    then (if (?u. MEM u (MAP (edge_map Gc) rc) /\ x = embed Gc Gm rc h u)
          then embed Gc Gm rc h
                 (node_map (embed_disk Gc rc) (face_map (embed_disk Gc rc)
                    (@u. MEM u (MAP (edge_map Gc) rc) /\
                         x = embed Gc Gm rc h u)))
          else node_map Gm x)
    else x`;;

let embr_fmap = new_definition
 `embr_fmap (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) x =
    if x IN embr_D Gc Gm rc h
    then (if (?u. MEM u (MAP (edge_map Gc) rc) /\
                  edge_map Gm x = embed Gc Gm rc h u)
          then embed Gc Gm rc h
                 (edge_map (embed_disk Gc rc)
                    (@u. MEM u (MAP (edge_map Gc) rc) /\
                         edge_map Gm x = embed Gc Gm rc h u))
          else face_map Gm x)
    else x`;;

let embed_rem = new_definition
 `embed_rem (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) =
    mk_hypermap (embr_D Gc Gm rc h, embr_emap Gc Gm rc h,
                 embr_nmap Gc Gm rc h, embr_fmap Gc Gm rc h)`;;

let embr_ring = new_definition
 `embr_ring (Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) =
    REVERSE (MAP (embed Gc Gm rc h) (MAP (edge_map Gc) rc))`;;

(* ------------------------------------------------------------------------- *)
(* Small general facts.                                                      *)
(* ------------------------------------------------------------------------- *)

let AC_BC = prove
 (`!(Gc:(A)hypermap) (rc:(A)list) x. kernel Gc rc x ==> ~MEM x rc`,
  MESON_TAC[KERNEL_NOT_MEM; IN]);;

let EMBED_ON_KERNEL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x.
     x IN kernel Gc rc ==> embed Gc Gm rc h x = h x`,
  SIMP_TAC[embed]);;

let KERNEL_FACE_EQ = prove
 (`!(H:(A)hypermap) p x. face_map H x IN kernel H p <=> x IN kernel H p`,
  REWRITE_TAC[IN_KERNEL; FBAND_FACE_MAP_EQ] THEN
  MESON_TAC[FACE_MAP_PERMUTES; PERMUTES_IN_IMAGE]);;

let FCARD_FACE_PSUBSET = prove
 (`!(H:(A)hypermap) s t.
     s SUBSET t /\ FINITE t /\ (!a b. a IN s /\ cface H a b ==> b IN s) /\
     (?v. v IN t /\ ~(v IN s))
     ==> fcard_face H s < fcard_face H t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[fcard_face; SET_OF_ORBITS_IMAGE] THEN
  MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_SIMP_TAC[FINITE_IMAGE; PSUBSET; IMAGE_SUBSET] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `orbit_map (face_map H) (v:A)`) THEN
  MATCH_MP_TAC(TAUT `q /\ ~p ==> (p <=> q) ==> F`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[NOT_EXISTS_THM]] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `cface H (a:A) v` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[cface; face] THEN ASM_MESON_TAC[IN_ORBIT_MAP_REFL]);;

let QUASICUBIC_MONO = prove
 (`!(H:(A)hypermap) P Q.
     quasicubic H P /\ (!x. x IN P ==> x IN Q) ==> quasicubic H Q`,
  REWRITE_TAC[quasicubic] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Paths and cycles under maps and reversal.                                 *)
(* ------------------------------------------------------------------------- *)

let LIST_PATH_MAP_REL = prove
 (`!R S (f:A->B) l x.
     list_path R x l /\
     (!u v. MEM u (CONS x l) /\ MEM v (CONS x l) /\ R u v ==> S (f u) (f v))
     ==> list_path S (f x) (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[list_path; MAP] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM]);;

let LAST_REV_BUTLAST = prove
 (`!(h:A) t. LAST (CONS (LAST (CONS h t)) (REVERSE (BUTLAST (CONS h t)))) = h`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[BUTLAST; REVERSE; LAST]; ALL_TAC] THEN
  REWRITE_TAC[BUTLAST; NOT_CONS_NIL; REVERSE; GSYM(CONJUNCT2 APPEND)] THEN
  REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST]);;

let LIST_PATH_REVERSE_REL = prove
 (`!R (l:(A)list) x.
     list_path R x l
     ==> list_path (\a b. R b a) (LAST (CONS x l))
                   (REVERSE (BUTLAST (CONS x l)))`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[list_path; BUTLAST; REVERSE; LAST]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN REWRITE_TAC[list_path] THEN STRIP_TAC THEN
  REWRITE_TAC[LAST_CLAUSES] THEN ONCE_REWRITE_TAC[BUTLAST] THEN
  REWRITE_TAC[NOT_CONS_NIL; REVERSE; LIST_PATH_APPEND; list_path;
              LAST_REV_BUTLAST] THEN
  ASM_SIMP_TAC[]);;

let LIST_CYCLE_MAP_REL = prove
 (`!R S (f:A->B) l.
     list_cycle R l /\ (!u v. MEM u l /\ MEM v l /\ R u v ==> S (f u) (f v))
     ==> list_cycle S (MAP f l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[list_cycle; MAP_EQ_NIL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LAST_MAP] THEN
  MATCH_MP_TAC(ISPEC `R:A->A->bool` LIST_PATH_MAP_REL) THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u:A`; `v:A`] THEN
  REWRITE_TAC[MEM] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[MEM_LAST]);;

let LIST_PATH_MEM_SUCC = prove
 (`!R (p:(A)list) x y z.
     list_path R x (APPEND p [y]) /\ MEM z (CONS x p)
     ==> ?v. MEM v (APPEND p [y]) /\ R z v`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND; list_path; MEM] THENL
   [MESON_TAC[]; ASM_MESON_TAC[MEM]]);;

let PAIRWISE_DISTINCT_OF_MAP = prove
 (`!(f:A->B) l.
     PAIRWISE (\a b. ~(a = b)) (MAP f l) ==> PAIRWISE (\a b. ~(a = b)) l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PAIRWISE_MAP] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `\x y. ~((f:A->B) x = f y)` PAIRWISE_IMPLIES) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Unpacking the context: the node ring, the map identities, the kernel,     *)
(* the perimeter lemmas, the preembedding lemmas and the hom-ring lemmas of  *)
(* embed_prelim, all specialised to the context.                             *)
(* ------------------------------------------------------------------------- *)

let CTX_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
         PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
         (!w. MEM w rc ==> good_ring_arity Gc w)`,
  REWRITE_TAC[embed_context] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[]);;

let CTX_MAPS = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> (!z. edge_map Gc (edge_map Gc z) = z) /\
         (!z. edge_map Gm (edge_map Gm z) = z) /\
         (!z. node_map Gm (node_map Gm (node_map Gm z)) = z) /\
         (!z. face_map Gm (edge_map Gm z) = node_map Gm (node_map Gm z)) /\
         (!x. x IN dart Gc /\ ~MEM x rc
              ==> node_map Gc (node_map Gc (node_map Gc x)) = x /\
                  face_map Gc (edge_map Gc x) = node_map Gc (node_map Gc x)) /\
         (!y. MEM (node_map Gc y) rc <=> MEM y rc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[embed_context] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CFT_PLAIN_EE; CUBIC_EQ_U] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:B` THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `node_map Gm (node_map Gm (z:B))`]
                  nodeK) THEN
    ASM_SIMP_TAC[CUBIC_EQ_U];
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] N3C) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `node_map Gc (node_map Gc (x:A))`]
                  nodeK) THEN
    ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[scycle]) THEN ASM_SIMP_TAC[RCN]]);;

let CTX_KERNEL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> (!x. x IN kernel Gc rc
              ==> x IN dart Gc /\ ~MEM x rc /\ h x IN dart Gm /\
                  h (face_map Gc x) = face_map Gm (h x)) /\
         (!x. face_map Gc x IN kernel Gc rc <=> x IN kernel Gc rc) /\
         (!x. edge_map Gc (node_map Gc x) IN kernel Gc rc <=>
              x IN kernel Gc rc) /\
         (!x y. x IN kernel Gc rc /\ cface Gc x y ==> y IN kernel Gc rc)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[embed_context] THEN STRIP_TAC THEN
  REWRITE_TAC[KERNEL_FACE_EQ] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
                         ASSUME_TAC(REWRITE_RULE[IN_KERNEL] th)) THEN
    UNDISCH_TAC `preembedding Gc Gm (h:A->B) (kernel Gc rc)` THEN
    REWRITE_TAC[preembedding] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[KERNEL_NOT_MEM];
    CFACE_TAC[];
    CFACE_TAC[]]);;

(* CTX_TAC ths discharges an embed_context antecedent into the assumptions,  *)
(* together with its conjuncts and the conclusions of the context lemmas     *)
(* ths; USE_CTX lemma ttac applies ttac to the instance of lemma at the      *)
(* embed_context assumption; CTX_CONJS splits a context lemma into one       *)
(* theorem per conjunct of its conclusion.                                   *)

let CTX_TAC ths =
  DISCH_THEN(fun th ->
    ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[embed_context] th) THEN
    MAP_EVERY (fun l -> STRIP_ASSUME_TAC(MATCH_MP l th)) ths);;

let USE_CTX lemma ttac = FIRST_ASSUM(fun th -> ttac (MATCH_MP lemma th));;

let CTX_CONJS th =
  map (fun c -> GEN_ALL(DISCH_ALL c)) (CONJUNCTS(UNDISCH(SPEC_ALL th)));;

let CTX_ERC = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> scycle Gc (rlink Gc) (MAP (edge_map Gc) rc) /\
         ALL (\w. w IN dart Gc) (MAP (edge_map Gc) rc) /\
         quasicubic Gc (fband Gc (MAP (edge_map Gc) rc)) /\
         kernel Gc (MAP (edge_map Gc) rc) = kernel Gc rc /\
         embed_hyps Gm Gc (MAP (edge_map Gc) rc) h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[embed_context] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`] ERC_BUNDLE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `kernel Gc (MAP (edge_map Gc) (rc:(A)list)) = kernel Gc rc`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM; kernel]; ALL_TAC] THEN
  SUBGOAL_THEN `quasicubic Gc (fband Gc (MAP (edge_map Gc) (rc:(A)list)))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC QUASICUBIC_MONO THEN EXISTS_TAC `\z:A. MEM z rc` THEN
    ASM_REWRITE_TAC[IN] THEN ASM_MESON_TAC[FBAND_MEM_IFF; CFACE_REFL];
    ASM_REWRITE_TAC[embed_hyps]]);;

let CTX_PERIMETER = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> (!x. ~MEM x rc \/ ~MEM (edge_map Gc x) rc) /\
         (!x. x IN dart Gc /\ ~MEM x rc /\ ~MEM (edge_map Gc x) rc
              ==> x IN kernel Gc rc \/ edge_map Gc x IN kernel Gc rc) /\
         (!x. x IN dart Gc /\ ~(x IN kernel Gc rc)
              ==> CARD {z | cface Gc x z /\ edge_map Gc z IN kernel Gc rc}
                  <= 4)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[embed_context] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:A` THENL
   [MP_TAC(ISPECL [`Gc:(A)hypermap`; `rc:(A)list`; `x:A`] EDGE_PERIMETER);
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                   `x:A`] CHORDLESS_PERIMETER);
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                   `x:A`] ADJ_KERNEL_MAX)] THEN
  ASM_REWRITE_TAC[]);;

let CTX_H = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> (!x y. x IN kernel Gc rc /\ cface Gc x y ==> cface Gm (h x) (h y)) /\
         (!x u. x IN kernel Gc rc /\ cface Gm (h x) u
                ==> ?y. cface Gc x y /\ h y = u) /\
         (!x y. x IN kernel Gc rc /\ cface Gc x y /\ h x = h y ==> x = y) /\
         (!x. x IN kernel Gc rc /\ edge_map Gc x IN kernel Gc rc
              ==> h (edge_map Gc x) = edge_map Gm (h x))`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_ERC; CTX_KERNEL] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                   `x:A`; `y:A`] CFACE_AC_H) THEN
    ASM_REWRITE_TAC[IN];
    MAP_EVERY X_GEN_TAC [`x:A`; `u:B`] THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                   `x:A`; `u:B`] CFACE_H_AC) THEN
    ASM_REWRITE_TAC[IN];
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                         `h:A->B`] CFACE_INJ_EMBED) THEN
    REWRITE_TAC[GSYM(ISPECL [`kernel (Gc:(A)hypermap) rc`; `x:A`] IN)] THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                   `MAP (edge_map Gc) (rc:(A)list)`; `h:A->B`; `x:A`]
                  EMBED_FUNCTOR) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

let CTX_HOM_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> (!x p. list_path (rlink Gc) x p /\
                rlink Gm (h (LAST (CONS x p))) (h x) /\
                (!z. MEM z (CONS x p) ==> z IN kernel Gc rc) /\
                face_simple Gm (MAP h (CONS x p))
                ==> pre_hom_ring Gc Gm rc h x p) /\
         (!x p. pre_hom_ring Gc Gm rc h x p /\
                (!u. ~diskF Gm (MAP h (CONS x p)) u)
                ==> rlink Gc (LAST (CONS x p)) x) /\
         (!x p. pre_hom_ring Gc Gm rc h x p
                ==> list_path (rlink Gc) x p /\
                    (!z. MEM z (CONS x p)
                         ==> z IN kernel Gc rc /\ z IN dart Gc /\
                             h z IN dart Gm) /\
                    scycle Gm (rlink Gm) (MAP h (CONS x p)) /\
                    ALL (\w. w IN dart Gm) (MAP h (CONS x p)) /\
                    face_simple Gm (MAP h (CONS x p)) /\
                    rlink Gm (h (LAST (CONS x p))) (h x) /\
                    (!w. MEM w (MAP h (CONS x p))
                         ==> diskN Gm (MAP h (CONS x p)) w)) /\
         (!a b. a IN kernel Gc rc /\ edge_map Gc a IN kernel Gc rc /\
                rlink Gc a b
                ==> rlink Gm (h a) (h b))`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_ERC; CTX_KERNEL] THEN
  SUBGOAL_THEN
   `!x p. pre_hom_ring Gc Gm rc (h:A->B) x p <=>
          pre_hom_ring Gc Gm (MAP (edge_map Gc) rc) h x p /\ x IN dart Gc`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[pre_hom_ring] THEN ASM_MESON_TAC[MEM]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL
     [ASM_MESON_TAC[MEM]; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                         `MAP (edge_map Gc) (rc:(A)list)`; `h:A->B`]
                        INTRO_PRE_HOM_RING);
    MATCH_MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                         `MAP (edge_map Gc) (rc:(A)list)`; `h:A->B`]
                        TRIVIAL_HOM_RING);
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                   `MAP (edge_map Gc) (rc:(A)list)`; `h:A->B`; `x:A`;
                   `p:(A)list`] PRE_HOM_RING_FACTS);
    MATCH_MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`;
                         `MAP (edge_map Gc) (rc:(A)list)`; `h:A->B`]
                        RLINK_H)] THEN
  ASM_SIMP_TAC[]);;

let CTX_INTRO,CTX_TRIVIAL,CTX_PHR_FACTS,CTX_RLINK_H =
  match CTX_CONJS CTX_HOM_RING with
    [a;b;c;d] -> a,b,c,d | _ -> failwith "CTX_HOM_RING";;

let CTX_CFACE_AC_H,CTX_CFACE_H_AC,CTX_CFACE_INJ =
  match CTX_CONJS CTX_H with
    [a;b;c;_] -> a,b,c | _ -> failwith "CTX_H";;

let CTX_E2C,CTX_E2M,CTX_N3M,CTX_FE_M,CTX_N3C =
  match CTX_CONJS CTX_MAPS with
    [a;b;c;d;e;_] -> a,b,c,d,e | _ -> failwith "CTX_MAPS";;

(* ------------------------------------------------------------------------- *)
(* Face counts: an empty or single-face disk.                                *)
(* ------------------------------------------------------------------------- *)

let DISKF_EMPTY_OF_FCARD = prove
 (`!(H:(A)hypermap) r.
     ALL (\y. y IN dart H) r /\ fcard_face H (diskF H r) = 0
     ==> !u. ~diskF H r u`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(A)hypermap`; `diskF (H:(A)hypermap) r`] FCARD0P) THEN
  ASM_SIMP_TAC[FINITE_DISKF; LT_REFL; IN] THEN ASM_MESON_TAC[]);;

let DISKF_SINGLE_FACE = prove
 (`!(H:(A)hypermap) r u.
     ALL (\y. y IN dart H) r /\ fcard_face H (diskF H r) <= 1 /\ diskF H r u
     ==> !v. diskF H r v <=> cface H u v`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `diskF (H:(A)hypermap) r`] FCARD1P) THEN
    ASM_SIMP_TAC[FINITE_DISKF; DISKF_SUBSET_DART; GSYM NOT_LE; IN] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[DISKF_CFACE; DISKF_SUBSET_DART; SUBSET; IN]]);;

(* ------------------------------------------------------------------------- *)
(* A 5-ring of a minimal counter-example whose disk is a single face is the  *)
(* spoke ring of that face: its successor map is face o face o edge.         *)
(* ------------------------------------------------------------------------- *)

let SPOKE_RING_5 = prove
 (`!(H:(A)hypermap) r u.
     minimal_counter_example H /\ scycle H (rlink H) r /\
     ALL (\y. y IN dart H) r /\ LENGTH r = 5 /\ u IN dart H /\
     (!v. diskF H r v <=> cface H u v)
     ==> !v. MEM v r ==> nextc r v = face_map H (face_map H (edge_map H v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    STRIP_ASSUME_TAC(REWRITE_RULE[minimal_counter_example] th) THEN
    ASSUME_TAC(MATCH_MP MCE_CUBIC th)) THEN
  ABBREV_TAC `ru = spoke_ring (H:(A)hypermap) u` THEN
  SUBGOAL_THEN `scycle H (rlink H) (ru:(A)list) /\ LENGTH ru = arity H u /\
                face_simple H ru /\ 4 < arity H u`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ru" THEN
    ASM_SIMP_TAC[SCYCLE_SPOKE_RING; SIZE_SPOKE_RING; MIN_ARITY;
                 FACE_SIMPLE_SPOKE_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:A. MEM v ru ==> cface H u (node_map H v) /\ v IN dart H`
    ASSUME_TAC THENL
   [X_GEN_TAC `v:A` THEN EXPAND_TAC "ru" THEN ASM_SIMP_TAC[MEM_SPOKE_RING] THEN
    ASM_MESON_TAC[CFT_DART; NODE_MAP_PERMUTES; PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `ALL (\y:A. y IN dart H) ru` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM ALL_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:A. MEM v ru ==> fband H r v` ASSUME_TAC THENL
   [X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `MEM (v:A) ru`))) THEN
    SUBGOAL_THEN `diskN H r (v:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_NODE_EQ; diskF]; ALL_TAC] THEN
    ASM_CASES_TAC `fband H r (v:A)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `cface H u (v:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[diskF]; CFACE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `fcard_face H (fband H (r:(A)list)) = 5 /\
                fcard_face H (fband H ru) = arity H u`
    STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`; `r:(A)list`]
                  SCYCLE_FCARD_FBAND) THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `rlink (H:(A)hypermap)`; `ru:(A)list`]
                  SCYCLE_FCARD_FBAND) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:A. fband H r v ==> fband H ru v` ASSUME_TAC THENL
   [X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `fband H (ru:(A)list) v` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `fband H (ru:(A)list)`;
                   `fband H (r:(A)list)`] FCARD_FACE_PSUBSET) THEN
    ASM_REWRITE_TAC[SUBSET; IN] THEN
    REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FBAND_MEM_IFF; CFT_TRANS];
      ASM_MESON_TAC[FINITE_SUBSET; FINITE_DART; FBAND_IN_DART; SUBSET; IN];
      CFACE_TAC[];
      ASM_MESON_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:A. MEM v r ==> MEM v ru` ASSUME_TAC THENL
   [X_GEN_TAC `v:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:A) IN dart H /\ edge_map H v IN dart H`
      STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ALL_MEM; EDGE_MAP_IN_DART]; ALL_TAC] THEN
    SUBGOAL_THEN `adj H u (v:A) /\ adj H u (edge_map H v)`
      STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "ru" THEN ASM_SIMP_TAC[GSYM FBAND_SPOKE_RING] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FBAND_MEM]; ALL_TAC] THEN
      SUBGOAL_THEN `rlink H v (nextc r (v:A)) /\ MEM (nextc r v) r`
        STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[CYCLE_NEXTC_STEP; NEXTC_MEM; scycle; SCYCLE_PAIRWISE];
        ALL_TAC] THEN
      EXPAND_TAC "ru" THEN
      SUBGOAL_THEN `fband H (spoke_ring H u) (nextc r (v:A))` MP_TAC THENL
       [ASM_MESON_TAC[FBAND_MEM]; ALL_TAC] THEN
      SUBGOAL_THEN `nextc r (v:A) IN dart H` ASSUME_TAC THENL
       [ASM_MESON_TAC[ALL_MEM]; ALL_TAC] THEN
      ASM_SIMP_TAC[FBAND_SPOKE_RING] THEN
      ASM_MESON_TAC[ADJ_CFACE; rlink];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `u:A`; `v:A`] ADJ11_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `diskN H r (edge_map H (v:A))` ASSUME_TAC THENL
     [ASM_MESON_TAC[DISKN_NODE_EQ; diskF]; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:(A)hypermap`; `r:(A)list`; `v:A`] DISKN_EDGE_RING) THEN
    ASM_SIMP_TAC[SIZE_PROPER_RING; ARITH];
    ALL_TAC] THEN
  X_GEN_TAC `v:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `nextc ru (v:A) = face_map H (face_map H (edge_map H v))`
    (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "ru" THEN ASM_SIMP_TAC[NEXT_SPOKE_RING; spoke]; ALL_TAC] THEN
  MATCH_MP_TAC CFT_FACE_SIMPLE THEN EXISTS_TAC `H:(A)hypermap` THEN
  EXISTS_TAC `ru:(A)list` THEN ASM_SIMP_TAC[NEXTC_MEM] THEN
  SUBGOAL_THEN `rlink H v (nextc r (v:A)) /\ rlink H v (nextc ru v)`
    MP_TAC THENL
   [ASM_MESON_TAC[CYCLE_NEXTC_STEP; scycle; SCYCLE_PAIRWISE];
    CFACE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Pulling the face o face o edge cycle back to Gc: consecutive darts of the *)
(* pre-hom ring have cofacial nodes, and node x must leave the kernel.       *)
(* ------------------------------------------------------------------------- *)

let CTX_H_NODE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN kernel Gc rc /\ node_map Gc x IN kernel Gc rc
             ==> h (node_map Gc x) = node_map Gm (h x)`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_H] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `edge_map Gc (node_map Gc (x:A)) IN kernel Gc rc`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) x = face_map Gm (edge_map Gm (h (node_map Gc x)))`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [SUBST1_TAC(AP_TERM `h:A->B`
                 (GSYM(ISPECL [`Gc:(A)hypermap`; `x:A`] nodeK))) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[edgeK]]);;

let CTX_FFE_STEP = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !a b. a IN kernel Gc rc /\ b IN kernel Gc rc /\ rlink Gc a b /\
               h b = face_map Gm (face_map Gm (edge_map Gm (h a)))
               ==> b = face_map Gc (face_map Gc (edge_map Gc a)) /\
                   cface Gc (node_map Gc a) (node_map Gc b)`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_H] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN REWRITE_TAC[rlink] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `edge_map Gc (a:A) IN kernel Gc rc /\
                cface Gc b (face_map Gc (face_map Gc (edge_map Gc (a:A))))`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:A) = face_map Gc (face_map Gc (edge_map Gc a))`
    ASSUME_TAC THENL
   [USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:A) IN dart Gc /\ ~MEM a rc` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_CTX CTX_N3C (MP_TAC o SPEC `a:A`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN USE_CTX CTX_E2C ASSUME_TAC THEN
  SUBGOAL_THEN
   `node_map Gc (face_map Gc (face_map Gc (edge_map Gc (a:A)))) =
    edge_map Gc (face_map Gc (edge_map Gc a))` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`Gc:(A)hypermap`;
                   `edge_map Gc (face_map Gc (edge_map Gc (a:A)))`] edgeK) THEN
    ASM_REWRITE_TAC[];
    CFACE_TAC[]]);;

let CTX_NODES_COFACIAL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !p x. list_path (rlink Gc) x p /\
               (!z. MEM z (CONS x p) ==> z IN kernel Gc rc) /\
               list_path (\a b. face_map Gm (face_map Gm (edge_map Gm a)) = b)
                         (h x) (MAP h p)
               ==> !z. MEM z (CONS x p)
                       ==> cface Gc (node_map Gc x) (node_map Gc z)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC(MATCH_MP CTX_FFE_STEP th)) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; list_path; MAP] THENL
   [MESON_TAC[CFACE_REFL]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `cface Gc (node_map Gc x) (node_map Gc (h':A))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `h':A`]) THEN ASM_SIMP_TAC[MEM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. MEM z (CONS (h':A) t) ==> cface Gc (node_map Gc h') (node_map Gc z)`
   ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM];
    ALL_TAC] THEN
  X_GEN_TAC `z:A` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[CFACE_REFL]; ALL_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CFT_TRANS THEN EXISTS_TAC `node_map Gc (h':A)` THEN
  ASM_SIMP_TAC[MEM]);;

let CTX_NODE_X_KERNEL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x y. x IN kernel Gc rc /\ y IN kernel Gc rc /\
               cface Gc (node_map Gc x) (node_map Gc y) /\
               face_map Gm (face_map Gm (edge_map Gm (h y))) = h x /\
               node_map Gc x IN kernel Gc rc
               ==> rlink Gc y x`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_H; CTX_MAPS; CTX_H_NODE] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `node_map Gc (y:A) IN kernel Gc rc` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) (node_map Gc y) = h (face_map Gc (node_map Gc x))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
    SUBGOAL_THEN `!z:B. node_map Gm (face_map Gm z) = edge_map Gm z`
      (fun th -> REWRITE_TAC[th]) THENL
     [USE_CTX CTX_E2M (fun th -> MESON_TAC[th; edgeK]);
      ASM_REWRITE_TAC[nodeK]];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map Gc (y:A) = face_map Gc (node_map Gc x)`
    ASSUME_TAC THENL
   [USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN dart Gc /\ ~MEM y rc` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[rlink] THEN
  SUBGOAL_THEN `face_map Gc (edge_map Gc (y:A)) = edge_map Gc (node_map Gc x)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `edge_map Gc (node_map Gc (x:A))`]
                  edgeK) THEN
    ASM_REWRITE_TAC[];
    CFACE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The innermost step of embed_full (Coq's third `suffices`): the inner      *)
(* disk of a pre-hom ring that does not close up has a face (else            *)
(* TRIVIAL_HOM_RING closes it), and more than one for a 5-ring (a single     *)
(* face would make it the spoke ring of that face, and then the face of      *)
(* node x would have five darts with edges in the kernel, one more than      *)
(* ADJ_KERNEL_MAX allows).                                                   *)
(* ------------------------------------------------------------------------- *)

let NO_PRE_HOM_RING_SIDE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x p.
     embed_context Gm Gc rc h /\ pre_hom_ring Gc Gm rc h x p /\
     ~rlink Gc (LAST (CONS x p)) x /\
     fcard_face Gm (diskF Gm (MAP h (CONS x p))) <=
     (if LENGTH p = 4 then 1 else 0)
     ==> F`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  CTX_TAC [CTX_KERNEL; CTX_PERIMETER] THEN
  USE_CTX CTX_PHR_FACTS (fun th ->
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  SUBGOAL_THEN `?u:B. diskF Gm (MAP (h:A->B) (CONS x p)) u`
    STRIP_ASSUME_TAC THENL
   [USE_CTX CTX_TRIVIAL (MP_TAC o SPECL [`x:A`; `p:(A)list`]) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LENGTH (p:(A)list) = 4 /\
    fcard_face Gm (diskF Gm (MAP (h:A->B) (CONS x p))) <= 1`
   STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gm:(B)hypermap`; `MAP (h:A->B) (CONS x p)`]
                  DISKF_EMPTY_OF_FCARD) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `fcard_face Gm (diskF Gm (MAP (h:A->B) (CONS x p))) <=
                 (if LENGTH p = 4 then 1 else 0)` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:B) IN dart Gm` ASSUME_TAC THENL
   [ASM_MESON_TAC[DISKN_SUBSET_DART; diskF]; ALL_TAC] THEN
  SUBGOAL_THEN `!v. diskF Gm (MAP (h:A->B) (CONS x p)) v <=> cface Gm u v`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gm:(B)hypermap`; `MAP (h:A->B) (CONS x p)`; `u:B`]
                  DISKF_SINGLE_FACE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. MEM v (MAP (h:A->B) (CONS x p))
        ==> nextc (MAP h (CONS x p)) v =
            face_map Gm (face_map Gm (edge_map Gm v))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC SPOKE_RING_5 THEN EXISTS_TAC `u:B` THEN
    ASM_REWRITE_TAC[LENGTH_MAP; LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `PAIRWISE (\a b:B. ~(a = b)) (MAP (h:A->B) (CONS x p))`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_SIMPLE_UNIQ; uniq_list]; ALL_TAC] THEN
  SUBGOAL_THEN
   `list_cycle (\a b. face_map Gm (face_map Gm (edge_map Gm a)) = b)
               (MAP (h:A->B) (CONS x p))`
   MP_TAC THENL
   [MP_TAC(ISPEC `MAP (h:A->B) (CONS x p)` LIST_CYCLE_NEXTC) THEN
    ASM_REWRITE_TAC[MAP_EQ_NIL; NOT_CONS_NIL] THEN MATCH_MP_TAC EQ_IMP THEN
    MATCH_MP_TAC LIST_CYCLE_CONG_MEM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[list_cycle; MAP; NOT_CONS_NIL; list_path; LAST_MAP_CONS] THEN
  REWRITE_TAC[GSYM MAP] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z:A. MEM z (CONS x p) ==> cface Gc (node_map Gc x) (node_map Gc z)`
   ASSUME_TAC THENL
   [USE_CTX CTX_NODES_COFACIAL (MP_TAC o SPECL [`p:(A)list`; `x:A`]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(node_map Gc (x:A) IN kernel Gc rc)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~rlink Gc (LAST (CONS x p)) (x:A)` THEN
    REWRITE_TAC[] THEN USE_CTX CTX_NODE_X_KERNEL MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MEM; MEM_LAST; NOT_CONS_NIL];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map Gc (x:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_MAP_IN_DART; MEM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`set_of_list (MAP (node_map Gc) (CONS (x:A) p))`;
                 `{z:A | cface Gc (node_map Gc x) z /\
                         edge_map Gc z IN kernel Gc rc}`] CARD_SUBSET) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SET_OF_LIST; MEM_MAP; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{z:A | cface Gc (node_map Gc x) z}` THEN
      REWRITE_TAC[FINITE_CFACE_SET; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (set_of_list (MAP (node_map Gc) (CONS (x:A) p))) = 5`
    SUBST1_TAC THENL
   [SUBGOAL_THEN `PAIRWISE (\a b:A. ~(a = b)) (MAP (node_map Gc) (CONS x p))`
      MP_TAC THENL
     [MATCH_MP_TAC PAIRWISE_INJ_MAP THEN CONJ_TAC THENL
       [MESON_TAC[NODEI];
        MATCH_MP_TAC PAIRWISE_DISTINCT_OF_MAP THEN EXISTS_TAC `h:A->B` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM HAS_SIZE_SET_OF_LIST; HAS_SIZE; LENGTH_MAP; LENGTH] THEN
      ASM_SIMP_TAC[ARITH]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `node_map Gc (x:A)` o
    check (fun th -> is_imp(snd(strip_forall(concl th))) &&
                     free_in `CARD:(A->bool)->num` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The image of a pre-hom ring that does not close up is a proper ring, and  *)
(* the ring can be reversed (Coq's hp_ok and Ehrp, in embed_full).           *)
(* ------------------------------------------------------------------------- *)

let PHR_PROPER_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x p.
     embed_context Gm Gc rc h /\ pre_hom_ring Gc Gm rc h x p /\
     ~rlink Gc (LAST (CONS x p)) x
     ==> ~(p = []) /\ proper_ring Gm (MAP h (CONS x p))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  CTX_TAC [CTX_KERNEL; CTX_H; CTX_MAPS] THEN
  USE_CTX CTX_PHR_FACTS (fun th ->
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `t:(A)list` SUBST_ALL_TAC))
   (ISPEC `p:(A)list` list_CASES) THENL
   [UNDISCH_TAC `rlink Gm ((h:A->B) (LAST [x])) (h x)` THEN
    REWRITE_TAC[LAST] THEN CFACE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_CONS_NIL; proper_ring; MAP] THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
   (X_CHOOSE_THEN `z:A` (X_CHOOSE_THEN `s:(A)list` SUBST_ALL_TAC))
   (ISPEC `t:(A)list` list_CASES) THEN
  REWRITE_TAC[MAP; CONS_11; NOT_CONS_NIL] THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MAP_EVERY EXISTS_TAC [`(h:A->B) x`; `(h:A->B) y`] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~rlink Gc (LAST [x; y]) (x:A)` THEN
  REWRITE_TAC[LAST; NOT_CONS_NIL; rlink] THEN
  SUBGOAL_THEN `edge_map Gc (x:A) = y` (SUBST1_TAC o SYM) THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[list_path; rlink]) THEN
    SUBGOAL_THEN `edge_map Gc (x:A) IN kernel Gc rc` ASSUME_TAC THENL
     [CFACE_TAC[]; ALL_TAC] THEN
    USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_SIMP_TAC[MEM];
    ASM_REWRITE_TAC[CFACE_REFL]]);;

let REVERSE_PRE_HOM_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x p.
     embed_context Gm Gc rc h /\ pre_hom_ring Gc Gm rc h x p /\
     ~rlink Gc (LAST (CONS x p)) x
     ==> ?rx rp. pre_hom_ring Gc Gm rc h rx rp /\
                 ~rlink Gc (LAST (CONS rx rp)) rx /\
                 LENGTH rp = LENGTH p /\
                 MAP h (CONS rx rp) = rot1 (rev_ring Gm (MAP h (CONS x p)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  CTX_TAC [CTX_KERNEL; CTX_H] THEN
  USE_CTX CTX_E2C ASSUME_TAC THEN USE_CTX CTX_E2M ASSUME_TAC THEN
  USE_CTX CTX_PHR_FACTS (fun th ->
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  SUBGOAL_THEN `~(p:(A)list = [])` MP_TAC THENL
   [ASM_MESON_TAC[PHR_PROPER_RING]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:(A)list` (X_CHOOSE_THEN `y:A`
    SUBST_ALL_TAC) o MATCH_MP SNOC_DECOMP) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LAST_CONS_SNOC]) THEN
  SUBGOAL_THEN `(x:A) IN kernel Gc rc /\ y IN kernel Gc rc /\
                (!z. MEM z (CONS x p1) ==> z IN kernel Gc rc)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEM; MEM_APPEND]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:A. MEM z (CONS x p1)
          ==> edge_map Gc z IN kernel Gc rc /\
              (h:A->B) (edge_map Gc z) = edge_map Gm (h z)`
   ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`rlink (Gc:(A)hypermap)`; `p1:(A)list`; `x:A`; `y:A`;
                   `z:A`] LIST_PATH_MEM_SUCC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:A) IN kernel Gc rc /\ v IN kernel Gc rc`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEM; MEM_APPEND]; ALL_TAC] THEN
    SUBGOAL_THEN `edge_map Gc (z:A) IN kernel Gc rc` ASSUME_TAC THENL
     [CFACE_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `list_path (rlink Gc) x (p1:(A)list) /\
                rlink Gc (LAST (CONS x p1)) y` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `list_path (rlink Gc) x (APPEND p1 [y:A])` THEN
    REWRITE_TAC[LIST_PATH_APPEND; list_path];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ry:A. cface Gc x ry /\ (h:A->B) ry = edge_map Gm (h y)`
    STRIP_ASSUME_TAC THENL
   [USE_CTX CTX_CFACE_H_AC MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ry:A) IN kernel Gc rc` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `q = MAP (edge_map Gc) (CONS (x:A) p1)` THEN
  SUBGOAL_THEN `~(q:(A)list = [])` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[MAP; NOT_CONS_NIL]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`LAST (q:(A)list)`; `APPEND (REVERSE (BUTLAST (q:(A)list))) [ry:A]`] THEN
  SUBGOAL_THEN `CONS (LAST q) (APPEND (REVERSE (BUTLAST q)) [ry:A]) =
                APPEND (REVERSE q) [ry]`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
      [GSYM(MATCH_MP APPEND_BUTLAST_LAST th)]) THEN
    REWRITE_TAC[REVERSE_APPEND; REVERSE; APPEND];
    ALL_TAC] THEN
  SUBGOAL_THEN `MAP (h:A->B) (APPEND (REVERSE q) [ry]) =
                rot1 (rev_ring Gm (MAP h (CONS x (APPEND p1 [y]))))`
    ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[rev_ring; MAP_APPEND; MAP; REVERSE_APPEND; REVERSE; APPEND;
                rot1; NOT_CONS_NIL; HD; TL; MAP_REVERSE] THEN
    ASM_SIMP_TAC[MEM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM MAP_o] THEN MATCH_MP_TAC MAP_EQ THEN
    ASM_SIMP_TAC[GSYM ALL_MEM; o_THM; MEM; MEM_REVERSE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pre_hom_ring; LAST_CONS_SNOC; LAST_SNOC'] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIST_PATH_APPEND; list_path] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`rlink (Gc:(A)hypermap)`; `\a b:A. rlink Gc b a`;
                     `edge_map (Gc:(A)hypermap)`; `p1:(A)list`; `x:A`]
                    LIST_PATH_MAP_REL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REWRITE_TAC[rlink] THEN ASM_REWRITE_TAC[] THEN
        MESON_TAC[CFACE_SYM_GEN];
        DISCH_THEN(MP_TAC o MATCH_MP LIST_PATH_REVERSE_REL) THEN
        EXPAND_TAC "q" THEN REWRITE_TAC[MAP; ETA_AX; LAST_MAP_CONS]];
      EXPAND_TAC "q" THEN REWRITE_TAC[MAP; LAST_REV_BUTLAST; rlink] THEN
      ASM_REWRITE_TAC[]];
    X_GEN_TAC `z:A` THEN EXPAND_TAC "q" THEN
    REWRITE_TAC[MEM_APPEND; MEM_REVERSE; MEM_MAP; MEM] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MEM];
    REWRITE_TAC[GSYM ROT_LIST_1; SCYCLE_ROT] THEN
    MATCH_MP_TAC SCYCLE_REV_RING THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `LAST (q:(A)list) = edge_map Gc (LAST (CONS x p1))`
      SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN REWRITE_TAC[MAP; LAST_MAP_CONS]; ALL_TAC] THEN
    REWRITE_TAC[rlink] THEN DISCH_TAC THEN
    UNDISCH_TAC `~rlink Gc y (x:A)` THEN ASM_REWRITE_TAC[rlink] THEN
    SUBGOAL_THEN `cface Gc (edge_map Gc (ry:A)) y /\
                  edge_map Gc ry IN kernel Gc rc`
      STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `edge_map Gc (ry:A) = y` (SUBST1_TAC o SYM) THENL
     [USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      CFACE_TAC[]];
    ASM_SIMP_TAC[LENGTH_APPEND; LENGTH_REVERSE; LENGTH_BUTLAST_1] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[LENGTH_MAP; LENGTH] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* No pre-hom ring of length at most 5 fails to close up: Birkhoff's theorem *)
(* gives a side with few faces, reversed if necessary (Coq embed_full, the   *)
(* second `suffices`).                                                       *)
(* ------------------------------------------------------------------------- *)

(* The inner faces of the reversed ring are the outer faces of the ring      *)
(* (Coq's EhrpF and diskF_rev_ring).                                         *)
let DISKF_ROT1_REV_RING = prove
 (`!(H:(A)hypermap) r.
     planar_hypermap H /\ plain_hypermap H /\ connected_hypermap H /\
     scycle H (rlink H) r /\ ALL (\z. z IN dart H) r /\ proper_ring H r
     ==> diskF H (rot1 (rev_ring H r)) = {x | x IN dart H /\ diskFC H r x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN
  SUBGOAL_THEN `~(rev_ring H r = []:(A)list)` ASSUME_TAC THENL
   [REWRITE_TAC[rev_ring; REVERSE_EQ_EMPTY; MAP_EQ_NIL] THEN
    ASM_MESON_TAC[proper_ring; NOT_CONS_NIL];
    ALL_TAC] THEN
  REWRITE_TAC[IN] THEN ASM_SIMP_TAC[DISKF_ROT1] THEN
  ASM_CASES_TAC `(x:A) IN dart H` THEN
  ASM_SIMP_TAC[DISKF_REV_RING; diskFC] THEN
  ASM_MESON_TAC[DISKF_SUBSET_DART; REV_RING_DART; SUBSET; IN]);;

let NO_PRE_HOM_RING_LE4 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> ~(?x p. (pre_hom_ring Gc Gm rc h x p /\
                  ~rlink Gc (LAST (CONS x p)) x) /\
                 LENGTH p <= 4)`,
  REPEAT GEN_TAC THEN CTX_TAC [] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `p:(A)list`] THEN STRIP_TAC THEN
  USE_CTX CTX_PHR_FACTS (fun th ->
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP th)) THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:A`; `p:(A)list`] PHR_PROPER_RING) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `Gm:(B)hypermap` BIRKHOFF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o ISPEC `MAP (h:A->B) (CONS x p)`) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; LENGTH; ARITH_RULE `SUC n <= 5 <=> n <= 4`;
                  ARITH_RULE `SUC n = 5 <=> n = 4`] THEN
  REWRITE_TAC[nontrivial_ring; GSYM NOT_LE] THEN CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                   `h:A->B`; `x:A`; `p:(A)list`] NO_PRE_HOM_RING_SIDE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:A`; `p:(A)list`] REVERSE_PRE_HOM_RING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rx:A` (X_CHOOSE_THEN `rp:(A)list`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `rx:A`; `rp:(A)list`] NO_PRE_HOM_RING_SIDE) THEN
  ASM_SIMP_TAC[DISKF_ROT1_REV_RING]);;

let NO_PHR_LE4 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x p. pre_hom_ring Gc Gm rc h x p /\ LENGTH p <= 4
               ==> rlink Gc (LAST (CONS x p)) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP NO_PRE_HOM_RING_LE4) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Shortening an rlink path of the kernel to one with a face-simple image    *)
(* (the induction of Coq's embed_full, first `suffices`).                    *)
(* ------------------------------------------------------------------------- *)

let SIMPLIFY_HOM_PATH = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !p x0. list_path (rlink Gc) x0 p /\
                (!z. MEM z p ==> z IN kernel Gc rc) /\ LENGTH p <= 5
                ==> ?q. list_path (rlink Gc) x0 q /\
                        LAST (CONS x0 q) = LAST (CONS x0 p) /\
                        (!z. MEM z q ==> z IN kernel Gc rc) /\
                        face_simple Gm (MAP h q) /\ LENGTH q <= LENGTH p`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_H] THEN
  LIST_INDUCT_TAC THENL
   [X_GEN_TAC `a:A` THEN DISCH_TAC THEN EXISTS_TAC `[]:(A)list` THEN
    REWRITE_TAC[list_path; MEM; MAP; face_simple; LENGTH; LE_REFL];
    ALL_TAC] THEN
  X_GEN_TAC `a:A` THEN REWRITE_TAC[list_path; MEM; LENGTH] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?q. list_path (rlink Gc) h' q /\ LAST (CONS h' q) = LAST (CONS h' t) /\
        (!z. MEM z q ==> z IN kernel Gc rc) /\
        face_simple Gm (MAP (h:A->B) q) /\ LENGTH q <= LENGTH t`
   STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `fband Gm (MAP (h:A->B) q) (h h')` THENL
   [ALL_TAC;
    EXISTS_TAC `CONS (h':A) q` THEN
    ASM_REWRITE_TAC[list_path; LAST_CLAUSES; MEM; MAP; face_simple; LENGTH;
                    LE_SUC] THEN
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FBAND_MEM_IFF]) THEN
  REWRITE_TAC[MEM_MAP] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:A`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `(x2:A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?x3:A. cface Gc x2 x3 /\ (h:A->B) x3 = h h'`
    STRIP_ASSUME_TAC THENL
   [USE_CTX CTX_CFACE_H_AC MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CFACE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x3:A) IN kernel Gc rc` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q1:(A)list` (X_CHOOSE_THEN `q2:(A)list`
    SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LIST_PATH_APPEND; list_path; MAP_APPEND; MAP;
                              FACE_SIMPLE_APPEND'; GSYM(CONJUNCT2 APPEND);
                              LAST_APPEND; NOT_CONS_NIL; MEM_APPEND; MEM;
                              LENGTH_APPEND; LENGTH]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o
    check (is_conj o concl))) THEN
  ASM_CASES_TAC `h':A = x3` THENL
   [EXISTS_TAC `CONS (x2:A) q2` THEN
    ASM_REWRITE_TAC[list_path; LAST_CLAUSES; MEM; MAP; LENGTH] THEN
    REPEAT CONJ_TAC THENL
     [CFACE_TAC[];
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x q1'. q1 = CONS (x:A) q1'` STRIP_ASSUME_TAC THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC ACCEPT_TAC
      (ISPEC `q1:(A)list` list_CASES) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LAST; list_path]) THEN
    SUBGOAL_THEN `edge_map Gc (h':A) IN kernel Gc rc` ASSUME_TAC THENL
     [CFACE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `rlink Gm ((h:A->B) h') (h x2)` MP_TAC THENL
     [USE_CTX CTX_RLINK_H MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; CFACE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~(h':A = x3)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[list_path; MEM; LAST_CLAUSES; LENGTH]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o
    check (is_conj o concl))) THEN
  SUBGOAL_THEN `(x:A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc (h':A) IN kernel Gc rc` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pre_hom_ring Gc Gm rc (h:A->B) x (APPEND q1' [x3])`
    ASSUME_TAC THENL
   [USE_CTX CTX_INTRO MATCH_MP_TAC THEN
    REWRITE_TAC[LIST_PATH_APPEND; list_path; GSYM(CONJUNCT2 APPEND);
                LAST_APPEND; NOT_CONS_NIL; CONJUNCT1 LAST_CLAUSES; MEM_APPEND;
                MEM] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [CFACE_TAC[];
      USE_CTX CTX_RLINK_H MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `MAP (h:A->B) (APPEND (CONS x q1') [x3]) =
                    APPEND (MAP h (CONS x q1')) [h x3]`
        SUBST1_TAC THENL [REWRITE_TAC[MAP_APPEND; MAP]; ALL_TAC] THEN
      REWRITE_TAC[FACE_SIMPLE_APPEND'; face_simple; FBAND_NIL; FBAND_SING;
                  MEM_MAP] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:B` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(h:A->B) w` o
        check (fun th -> is_forall(concl th) &&
                         free_in `fband (Gm:(B)hypermap)` (concl th))) THEN
      ASM_REWRITE_TAC[FBAND_CONS; MEM_MAP; DE_MORGAN_THM] THEN
      ANTS_TAC THENL [EXISTS_TAC `w:A` THEN ASM_REWRITE_TAC[]; CFACE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc (x3:A) x` MP_TAC THENL
   [USE_CTX NO_PHR_LE4 (MP_TAC o SPECL [`x:A`; `APPEND q1' [x3:A]`]) THEN
    ASM_REWRITE_TAC[LAST_APPEND; APPEND_EQ_NIL; NOT_CONS_NIL; LAST;
                    LENGTH_APPEND; LENGTH] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[rlink] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cface Gc (edge_map Gc (h':A)) (edge_map Gc x3) /\
                edge_map Gc x3 IN kernel Gc rc`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc (h':A) = edge_map Gc x3` MP_TAC THENL
   [USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP EDGEI) THEN SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* No short rlink path of the kernel joins x0 to a dart whose image is the   *)
(* edge of h (edge x0) (Coq embed_full, first `suffices`), hence EMBED_FULL. *)
(* ------------------------------------------------------------------------- *)

let NO_BAD_RLINK_PATH_5 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> ~(?x0 p. list_path (rlink Gc) x0 p /\ ~(LAST (CONS x0 p) = x0) /\
                  (!z. MEM z p ==> z IN kernel Gc rc) /\
                  edge_map Gm (h (LAST (CONS x0 p))) = h (edge_map Gc x0) /\
                  LENGTH p <= 5)`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_H] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `p:(A)list`] THEN
  STRIP_TAC THEN
  USE_CTX SIMPLIFY_HOM_PATH (MP_TAC o SPECL [`p:(A)list`; `a:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(LAST (CONS a p) = (a:A))` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> is_eq(concl th) &&
                     free_in `LAST:(A)list->A` (concl th))) THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC
    (X_CHOOSE_THEN `x:A` (X_CHOOSE_THEN `t:(A)list` SUBST_ALL_TAC))
    (ISPEC `q:(A)list` list_CASES) THENL
   [REWRITE_TAC[LAST]; ALL_TAC] THEN
  REWRITE_TAC[LAST_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[list_path; LAST_CLAUSES; MEM; LENGTH]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o
    check (is_conj o concl))) THEN
  SUBGOAL_THEN `(x:A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc (a:A) IN kernel Gc rc` ASSUME_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LAST (CONS (x:A) t) IN kernel Gc rc` ASSUME_TAC THENL
   [MP_TAC(ISPEC `CONS (x:A) t` MEM_LAST) THEN
    REWRITE_TAC[NOT_CONS_NIL; MEM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `rlink Gc (LAST (CONS x t)) (x:A)` MP_TAC THENL
   [USE_CTX NO_PHR_LE4 MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    USE_CTX CTX_INTRO MATCH_MP_TAC THEN ASM_REWRITE_TAC[rlink] THEN
    CONJ_TAC THENL
     [ALL_TAC; X_GEN_TAC `z:A` THEN REWRITE_TAC[MEM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[]] THEN
    USE_CTX CTX_CFACE_AC_H MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `rlink Gc (a:A) x` THEN REWRITE_TAC[rlink];
    ALL_TAC] THEN
  REWRITE_TAC[rlink] THEN DISCH_TAC THEN
  SUBGOAL_THEN `edge_map Gc (LAST (CONS (x:A) t)) IN kernel Gc rc`
    ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC EDGEI THEN EXISTS_TAC `Gc:(A)hypermap` THEN
  USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN CFACE_TAC[]);;

let EMBED_FULL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x1 x2. x1 IN kernel Gc rc /\ x2 IN kernel Gc rc /\
                 edge_map Gm (h x1) = h x2
                 ==> edge_map Gc x1 = x2`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_MAPS; NO_BAD_RLINK_PATH_5] THEN
  MAP_EVERY X_GEN_TAC [`x1:A`; `x2:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x1:A) IN dart Gc /\ (x2:A) IN dart Gc` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x1:A) IN kernel Gc rc` THEN
    UNDISCH_TAC `(x2:A) IN kernel Gc rc` THEN
    REWRITE_TAC[IN_KERNEL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(x1:A) IN kernel Gc rc`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `(x2:A) IN kernel Gc rc`)) THEN
    MP_TAC(check (is_exists o snd o dest_imp o snd o dest_forall o concl)
                 th) THEN DISCH_THEN(K ALL_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x02:A`
    (X_CHOOSE_THEN `x20:A` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x01:A`
    (X_CHOOSE_THEN `x10:A` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `edge_map Gc (x1:A) = x2` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl) o
    check (fun th -> is_exists(dest_neg(concl th)))) THEN
  REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC
   [`edge_map Gc (x1:A)`;
    `[x10; edge_map Gc (x01:A); x02; edge_map Gc (x20:A); x2]`] THEN
  REWRITE_TAC[list_path; rlink; LAST; NOT_CONS_NIL; MEM; LENGTH; ARITH] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CFACE_TAC[]; CFACE_TAC[]; CFACE_TAC[];
    X_GEN_TAC `z:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> free_in `(h:A->B) x2` (concl th))) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The preembedding is injective on the kernel (Coq pre_embed_inj).          *)
(* ------------------------------------------------------------------------- *)

let PRE_EMBED_INJ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x y. x IN kernel Gc rc /\ y IN kernel Gc rc /\ h x = h y ==> x = y`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL; CTX_H] THEN
  USE_CTX CTX_E2C ASSUME_TAC THEN USE_CTX EMBED_FULL ASSUME_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cface Gc (x:A) y` ASSUME_TAC THENL
   [ALL_TAC; USE_CTX CTX_CFACE_INJ MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `edge_map Gc (x:A)`; `y:A`] H_SPOKE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p:(A)list` MP_TAC) THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z1:A` (X_CHOOSE_THEN `p1:(A)list` SUBST1_TAC))
    (ISPEC `p:(A)list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; list_path; rlink; ALL; LAST_CLAUSES] THEN
  USE_CTX CTX_E2C (fun th -> REWRITE_TAC[th]) THEN
  DISJ_CASES_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `z2:A` (X_CHOOSE_THEN `p2:(A)list` SUBST1_TAC))
    (ISPEC `p1:(A)list` list_CASES) THEN
  REWRITE_TAC[list_path; LAST_CLAUSES; ALL; rlink; edge_central] THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `cface Gm ((h:A->B) y) (h z1)` MP_TAC THENL
   [SUBGOAL_THEN `cface Gm ((h:A->B) x) (h z1)` MP_TAC THENL
     [USE_CTX CTX_CFACE_AC_H MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    USE_CTX CTX_CFACE_H_AC
      (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:A) IN kernel Gc rc`) th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:A) IN kernel Gc rc /\ edge_map Gc z1 IN kernel Gc rc`
    STRIP_ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:A) = z1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC EDGEI THEN EXISTS_TAC `Gc:(A)hypermap` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o
      check (fun th -> is_forall(concl th) &&
                       free_in `edge_map (Gm:(B)hypermap)` (concl th))) THEN
    ASM_SIMP_TAC[];
    CFACE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The embedding h1 = embed: its four defining cases, every dart is within   *)
(* one edge or node step of the kernel (Coq embed_cases), and the darts with *)
(* both x and edge x off the kernel have node x in the kernel.               *)
(* ------------------------------------------------------------------------- *)

let EMBED_EDGE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B) x.
     ~(x IN kernel Gc rc) /\ edge_map Gc x IN kernel Gc rc
     ==> embed Gc Gm rc h x = edge_map Gm (h (edge_map Gc x))`,
  SIMP_TAC[embed]);;

let EMBED_NODE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B) x.
     ~(x IN kernel Gc rc) /\ ~(edge_map Gc x IN kernel Gc rc) /\
     node_map Gc x IN kernel Gc rc
     ==> embed Gc Gm rc h x = face_map Gm (edge_map Gm (h (node_map Gc x)))`,
  SIMP_TAC[embed]);;

let EMBED_ELSE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) rc (h:A->B) x.
     ~(x IN kernel Gc rc) /\ ~(edge_map Gc x IN kernel Gc rc) /\
     ~(node_map Gc x IN kernel Gc rc)
     ==> embed Gc Gm rc h x =
         edge_map Gm
           (node_map Gm (node_map Gm (h (node_map Gc (edge_map Gc x)))))`,
  SIMP_TAC[embed]);;

let RC_ENX_CONTRA = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN dart Gc /\ MEM (edge_map Gc x) rc /\
             MEM (edge_map Gc (node_map Gc x)) rc
             ==> F`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_RING; CTX_MAPS] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `MEM (face_map Gc (x:A)) rc` ASSUME_TAC THENL
   [SUBGOAL_THEN `node_map Gc (face_map Gc (x:A)) = edge_map Gc x`
      (fun th -> ASM_MESON_TAC[th]) THEN
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `x:A`] faceK) THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `face_map Gc (x:A) = edge_map Gc (node_map Gc x)`
    ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `arity Gc (face_map Gc (x:A)) <= 2` MP_TAC THENL
   [SUBGOAL_THEN `arity Gc (face_map Gc (x:A)) = arity Gc x` SUBST1_TAC THENL
     [MATCH_MP_TAC ARITY_CFACE THEN ASM_REWRITE_TAC[CFT_FACE]; ALL_TAC] THEN
    SUBGOAL_THEN `arity Gc (x:A) divides 2` MP_TAC THENL
     [REWRITE_TAC[arity] THEN
      MP_TAC(ISPECL [`face_map (Gc:(A)hypermap)`; `dart (Gc:(A)hypermap)`;
                     `x:A`; `2`] ORBIT_SIZE_DIVIDES) THEN
      ASM_REWRITE_TAC[FINITE_DART; FACE_MAP_PERMUTES] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ARITH_RULE `2 = SUC(SUC 0)`; ITER] THEN
      ASM_REWRITE_TAC[nodeK];
      MESON_TAC[DIVIDES_LE; ARITH_RULE `~(2 = 0)`]];
    FIRST_X_ASSUM(MP_TAC o SPEC `face_map Gc (x:A)` o
      check (fun th -> free_in `good_ring_arity:(A)hypermap->A->bool`
                               (concl th))) THEN
    ASM_REWRITE_TAC[good_ring_arity] THEN ARITH_TAC]);;

let EMBED_CASES = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN dart Gc
             ==> (x IN kernel Gc rc \/ edge_map Gc x IN kernel Gc rc) \/
                 node_map Gc x IN kernel Gc rc \/
                 node_map Gc (edge_map Gc x) IN kernel Gc rc`,
  REPEAT GEN_TAC THEN
  CTX_TAC [CTX_MAPS; CTX_KERNEL; CTX_PERIMETER; RC_ENX_CONTRA] THEN
  SUBGOAL_THEN
   `!z:A. z IN dart Gc /\ ~MEM z rc
          ==> (z IN kernel Gc rc \/ edge_map Gc z IN kernel Gc rc) \/
              node_map Gc z IN kernel Gc rc`
   ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    ASM_CASES_TAC `MEM (edge_map Gc (z:A)) rc` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_CASES_TAC `MEM (edge_map Gc (node_map Gc (z:A))) rc` THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `node_map Gc (z:A) IN dart Gc /\ ~MEM (node_map Gc z) rc`
      STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `edge_map Gc (x:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EDGE_MAP_IN_DART]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:A` th) THEN
                          MP_TAC(SPEC `edge_map Gc (x:A)` th)) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `x:A` o
    check (fun th -> is_disj(snd(dest_forall(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let BC_ACN = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !z. z IN dart Gc /\ ~MEM z rc /\ ~(z IN kernel Gc rc) /\
             ~(edge_map Gc z IN kernel Gc rc)
             ==> node_map Gc z IN kernel Gc rc`,
  REPEAT GEN_TAC THEN
  CTX_TAC [CTX_MAPS; CTX_KERNEL; CTX_PERIMETER; EMBED_CASES] THEN
  X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:A` o
    check (fun th -> is_disj(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~MEM (edge_map Gc (z:A)) rc` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* embed commutes with edge everywhere, with node off the ring, and is       *)
(* injective off the ring (Coq embedE, embedN, embed_inj).                   *)
(* ------------------------------------------------------------------------- *)

let EMBEDE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN dart Gc
             ==> embed Gc Gm rc (h:A->B) (edge_map Gc x) =
                 edge_map Gm (embed Gc Gm rc (h:A->B) x)`,
  REPEAT GEN_TAC THEN
  CTX_TAC [CTX_MAPS; CTX_KERNEL; CTX_H; CTX_PERIMETER; BC_ACN] THEN
  SUBGOAL_THEN
   `!x:A. x IN dart Gc /\ ~MEM x rc
          ==> embed Gc Gm rc (h:A->B) (edge_map Gc x) =
              edge_map Gm (embed Gc Gm rc h x)`
   ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_CASES_TAC `edge_map Gc (x:A) IN kernel Gc rc` THEN
    ASM_CASES_TAC `(x:A) IN kernel Gc rc` THEN
    ASM_SIMP_TAC[EMBED_ON_KERNEL; EMBED_EDGE] THEN
    ASM_CASES_TAC `node_map Gc (edge_map Gc (x:A)) IN kernel Gc rc` THENL
     [SUBGOAL_THEN `~MEM (edge_map Gc (x:A)) rc` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `node_map Gc (x:A) IN kernel Gc rc` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EMBED_NODE; EMBED_ELSE];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `MEM (x:A) rc` THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `edge_map Gc (x:A)`) THEN
  ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
  SUBGOAL_THEN `~MEM (edge_map Gc (x:A)) rc` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let EMBEDN = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN dart Gc /\ ~MEM x rc
             ==> embed Gc Gm rc (h:A->B) (node_map Gc x) =
                 node_map Gm (embed Gc Gm rc (h:A->B) x)`,
  REPEAT GEN_TAC THEN
  CTX_TAC [CTX_MAPS; CTX_KERNEL; CTX_H; CTX_PERIMETER; BC_ACN; CTX_H_NODE] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `node_map Gc (node_map Gc (node_map Gc (x:A))) = x /\
                face_map Gc (edge_map Gc x) = node_map Gc (node_map Gc x)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `node_map Gc (node_map Gc (x:A)) IN kernel Gc rc <=>
                edge_map Gc x IN kernel Gc rc`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN kernel Gc rc` THENL
   [SUBGOAL_THEN `edge_map Gc (node_map Gc (x:A)) IN kernel Gc rc`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[EMBED_ON_KERNEL] THEN MATCH_MP_TAC EDGEI THEN
    EXISTS_TAC `Gm:(B)hypermap` THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                   `x:A`] H_EDGE_NODE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2)] THEN
    ASM_CASES_TAC `node_map Gc (x:A) IN kernel Gc rc` THEN
    ASM_SIMP_TAC[EMBED_ON_KERNEL; EMBED_EDGE];
    ALL_TAC] THEN
  ASM_CASES_TAC `edge_map Gc (x:A) IN kernel Gc rc` THENL
   [ASM_SIMP_TAC[EMBED_EDGE] THEN
    SUBGOAL_THEN `edge_map Gm ((h:A->B) (edge_map Gc x)) =
                  node_map Gm (h (node_map Gc (node_map Gc x)))`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [SYM th]) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC EDGEI THEN
      EXISTS_TAC `Gm:(B)hypermap` THEN ASM_REWRITE_TAC[faceK];
      ALL_TAC] THEN
    ASM_CASES_TAC `node_map Gc (x:A) IN kernel Gc rc` THENL
     [ASM_SIMP_TAC[EMBED_ON_KERNEL] THEN
      SUBGOAL_THEN `(h:A->B) (node_map Gc (node_map Gc x)) =
                    node_map Gm (h (node_map Gc x))`
        SUBST1_TAC THENL [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `~(edge_map Gc (node_map Gc (x:A)) IN kernel Gc rc)`
        ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[EMBED_NODE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map Gc (x:A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EMBED_ON_KERNEL; EMBED_NODE; edgeK]);;

let EMBED_INJ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x y. x IN dart Gc /\ ~MEM x rc /\ y IN dart Gc /\ ~MEM y rc /\
               embed Gc Gm rc (h:A->B) x = embed Gc Gm rc h y
               ==> x = y`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_MAPS; CTX_KERNEL; CTX_H; BC_ACN] THEN
  SUBGOAL_THEN
   `!x y:A. x IN kernel Gc rc /\ y IN dart Gc /\ ~MEM y rc /\
            embed Gc Gm rc (h:A->B) x = embed Gc Gm rc h y
            ==> x = y`
   (LABEL_TAC "main") THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:A) IN dart Gc` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(y:A) IN kernel Gc rc` THENL
     [UNDISCH_TAC `embed Gc Gm rc (h:A->B) x = embed Gc Gm rc h y` THEN
      ASM_SIMP_TAC[EMBED_ON_KERNEL] THEN DISCH_TAC THEN
      USE_CTX PRE_EMBED_INJ MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `edge_map Gc (y:A) IN kernel Gc rc` THENL
     [UNDISCH_TAC `embed Gc Gm rc (h:A->B) x = embed Gc Gm rc h y` THEN
      ASM_SIMP_TAC[EMBED_ON_KERNEL; EMBED_EDGE] THEN DISCH_TAC THEN
      USE_CTX EMBED_FULL (MP_TAC o SPECL [`edge_map Gc (y:A)`; `x:A`]) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[EDGE_MAP_IN_DART];
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `node_map Gc (y:A) IN kernel Gc rc` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `embed Gc Gm rc (h:A->B) x = embed Gc Gm rc h y` THEN
    ASM_SIMP_TAC[EMBED_ON_KERNEL; EMBED_NODE] THEN
    USE_CTX CTX_FE_M
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM th]) THEN
    SUBGOAL_THEN `(h:A->B) x = face_map Gm (h (edge_map Gc (node_map Gc x)))`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
     [SUBST1_TAC(AP_TERM `h:A->B`
                   (GSYM(ISPECL [`Gc:(A)hypermap`; `x:A`] nodeK))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FACEI) THEN DISCH_TAC THEN
    USE_CTX EMBED_FULL
      (MP_TAC o SPECL [`node_map Gc (y:A)`;
                       `edge_map Gc (node_map Gc (x:A))`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART];
      DISCH_THEN(MP_TAC o MATCH_MP EDGEI) THEN
      DISCH_THEN(MP_TAC o MATCH_MP NODEI) THEN
      DISCH_THEN(ACCEPT_TAC o SYM)];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:A) IN kernel Gc rc` THENL
   [USE_THEN "main" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(y:A) IN kernel Gc rc` THENL
   [CONV_TAC SYM_CONV THEN USE_THEN "main" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `embed Gc Gm rc (h:A->B) (node_map Gc x) =
                embed Gc Gm rc h (node_map Gc y)`
    ASSUME_TAC THENL
   [USE_CTX EMBEDN (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
  ASM_CASES_TAC `node_map Gc (x:A) IN kernel Gc rc` THENL
   [MATCH_MP_TAC NODEI THEN EXISTS_TAC `Gc:(A)hypermap` THEN
    USE_THEN "main" MATCH_MP_TAC THEN ASM_SIMP_TAC[NODE_MAP_IN_DART];
    ALL_TAC] THEN
  ASM_CASES_TAC `node_map Gc (y:A) IN kernel Gc rc` THENL
   [MATCH_MP_TAC NODEI THEN EXISTS_TAC `Gc:(A)hypermap` THEN
    CONV_TAC SYM_CONV THEN USE_THEN "main" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `edge_map Gc (x:A) IN kernel Gc rc /\
                edge_map Gc (y:A) IN kernel Gc rc`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `~(node_map Gc (x:A) IN kernel Gc rc)`;
      UNDISCH_TAC `~(node_map Gc (y:A) IN kernel Gc rc)`] THEN
    MATCH_MP_TAC(TAUT `(~b ==> a) ==> (~a ==> b)`) THEN DISCH_TAC THEN
    USE_CTX BC_ACN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EDGEI THEN EXISTS_TAC `Gc:(A)hypermap` THEN
  USE_THEN "main" MATCH_MP_TAC THEN
  USE_CTX EMBEDE (fun th -> ASM_SIMP_TAC[EDGE_MAP_IN_DART; th]));;

(* ------------------------------------------------------------------------- *)
(* The disk map (Coq embed_disk): its maps fix the darts outside embd_D,     *)
(* keep embd_D and compose to the identity, so it is a hypermap on embd_D    *)
(* (HYPERMAP_PRED_CANCEL).                                                   *)
(* ------------------------------------------------------------------------- *)

let IN_EMBD_D = prove
 (`!(Gc:(A)hypermap) rc x. x IN embd_D Gc rc <=> x IN dart Gc /\ ~MEM x rc`,
  REWRITE_TAC[embd_D; IN_ELIM_THM]);;

let EMBED_RING_FACTS = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> (!z. edge_map Gc (edge_map Gc z) = z) /\
         (!y. MEM (node_map Gc y) rc <=> MEM y rc) /\
         (!x. ~MEM x rc \/ ~MEM (edge_map Gc x) rc) /\
         list_cycle (\a b. node_map Gc a = b) rc /\
         scycle Gc (rlink Gc) (MAP (edge_map Gc) rc)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CFT_PLAIN_EE; EDGE_PERIMETER; ERC_SCYCLE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[scycle]) THEN ASM_SIMP_TAC[RCN]);;

let EMBD_MAPS = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> (!x. ~(x IN embd_D Gc rc)
              ==> embd_emap Gc rc x = x /\ embd_nmap Gc rc x = x /\
                  embd_fmap Gc rc x = x) /\
         (!x. x IN embd_D Gc rc
              ==> embd_emap Gc rc x IN embd_D Gc rc /\
                  embd_nmap Gc rc x IN embd_D Gc rc /\
                  embd_fmap Gc rc x IN embd_D Gc rc) /\
         (!x. embd_emap Gc rc (embd_nmap Gc rc (embd_fmap Gc rc x)) = x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP EMBED_RING_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CFT_PLAIN_NF o CONJUNCT1) THEN
  SIMP_TAC[embd_emap; embd_nmap; embd_fmap] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_EMBD_D] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART] THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN embd_D Gc rc` THEN
    ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_EMBD_D]) THEN
    REWRITE_TAC[IN_EMBD_D] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[faceK] THEN
    ASM_MESON_TAC[faceK; FACE_MAP_IN_DART; NODE_MAP_IN_DART]]);;

let EMBD_DISK_COMPONENTS = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> dart (embed_disk Gc rc) = embd_D Gc rc /\
         edge_map (embed_disk Gc rc) = embd_emap Gc rc /\
         node_map (embed_disk Gc rc) = embd_nmap Gc rc /\
         face_map (embed_disk Gc rc) = embd_fmap Gc rc`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP EMBD_MAPS) THEN
  REWRITE_TAC[embed_disk] THEN MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  MATCH_MP_TAC HYPERMAP_PRED_CANCEL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `dart (Gc:(A)hypermap)` THEN
  REWRITE_TAC[FINITE_DART; SUBSET; IN_EMBD_D] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Faces of the disk map are the faces of Gc restricted to embd_D (Coq       *)
(* cface_embd), the ring erc = MAP edge rc lies in embd_D and is a simple    *)
(* edge cycle of the disk map (Coq scycle_embd_ring).                        *)
(* ------------------------------------------------------------------------- *)

let CFACE_EMBD = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> !u v. u IN embd_D Gc rc /\ v IN embd_D Gc rc
               ==> (cface (embed_disk Gc rc) u v <=> cface Gc u v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP EMBD_MAPS th) THEN
                       STRIP_ASSUME_TAC(MATCH_MP EMBD_DISK_COMPONENTS th)) THEN
  ASM_REWRITE_TAC[CFACE_AS_ITER] THEN
  SUBGOAL_THEN `!x:A. ?k. embd_fmap Gc rc x = ITER k (face_map Gc) x`
    ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[embd_fmap] THEN REPEAT COND_CASES_TAC THENL
     [EXISTS_TAC `SUC 0`; EXISTS_TAC `SUC(SUC 0)`; EXISTS_TAC `0`] THEN
    REWRITE_TAC[ITER];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [SPEC_TAC(`u:A`,`u:A`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[ITER_ALT] THENL
     [MESON_TAC[ITER]; ASM_MESON_TAC[ITER_ADD]];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  SPEC_TAC(`u:A`,`u:A`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `u:A` THEN REPEAT DISCH_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `p:num` SUBST_ALL_TAC)
    (SPEC `n:num` num_CASES) THENL [MESON_TAC[ITER]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ITER_ALT]) THEN REWRITE_TAC[ITER_ALT] THEN
  SUBGOAL_THEN `face_map Gc (u:A) IN dart Gc` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_EMBD_D; FACE_MAP_IN_DART]; ALL_TAC] THEN
  ASM_CASES_TAC `MEM (face_map Gc (u:A)) rc` THENL
   [DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `q:num` SUBST_ALL_TAC)
      (SPEC `p:num` num_CASES) THENL
     [ASM_MESON_TAC[ITER; IN_EMBD_D]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ITER_ALT]) THEN REWRITE_TAC[ITER_ALT] THEN
    SUBGOAL_THEN `embd_fmap Gc rc (u:A) = face_map Gc (face_map Gc u)`
      ASSUME_TAC THENL [ASM_REWRITE_TAC[embd_fmap]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `embd_fmap Gc rc (u:A)` o
      C MP (ARITH_RULE `q < SUC(SUC q)`) o SPEC `q:num`) THEN
    ASM_SIMP_TAC[];
    SUBGOAL_THEN `embd_fmap Gc rc (u:A) = face_map Gc u` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[embd_fmap]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `face_map Gc (u:A)` o
      C MP (ARITH_RULE `p < SUC p`) o SPEC `p:num`) THEN
    ASM_REWRITE_TAC[IN_EMBD_D]] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `SUC m` THEN
  ASM_REWRITE_TAC[ITER_ALT]);;

let ERC_IN_EMBD_D = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> ALL (\z. z IN embd_D Gc rc) (MAP (edge_map Gc) rc)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
                       STRIP_ASSUME_TAC(MATCH_MP EMBED_RING_FACTS th)) THEN
  REWRITE_TAC[GSYM ALL_MEM; MEM_MAP; IN_EMBD_D] THEN X_GEN_TAC `z:A` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[ALL_MEM; EDGE_MAP_IN_DART]; ASM_MESON_TAC[]]);;

let FACE_SIMPLE_CONG = prove
 (`!(G:(A)hypermap) (G':(A)hypermap) l.
     (!a b. MEM a l /\ MEM b l ==> (cface G a b <=> cface G' a b))
     ==> (face_simple G l <=> face_simple G' l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACE_SIMPLE_EQ_PAIRWISE] THEN
  EQ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PAIRWISE_IMP_MEM THENL
   [EXISTS_TAC `\x y:A. ~cface G x y`; EXISTS_TAC `\x y:A. ~cface G' x y`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let SCYCLE_EMBD_RING = prove
 (`!(Gc:(A)hypermap) rc.
     plain_hypermap Gc /\ scycle Gc (\a b. node_map Gc a = b) rc /\
     PAIRWISE (\a b. ~(a = b)) rc /\ ALL (\w. w IN dart Gc) rc /\
     (!w. MEM w rc ==> good_ring_arity Gc w)
     ==> scycle (embed_disk Gc rc) (\a b. edge_map (embed_disk Gc rc) a = b)
                (MAP (edge_map Gc) rc)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
                       STRIP_ASSUME_TAC(MATCH_MP EMBED_RING_FACTS th) THEN
                       STRIP_ASSUME_TAC(MATCH_MP EMBD_DISK_COMPONENTS th) THEN
                       ASSUME_TAC(MATCH_MP CFACE_EMBD th) THEN
                       ASSUME_TAC(MATCH_MP ERC_IN_EMBD_D th)) THEN
  REWRITE_TAC[scycle] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `\a b:A. node_map Gc a = b` LIST_CYCLE_MAP_REL) THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `edge_map Gc (a:A) IN embd_D Gc rc` ASSUME_TAC THENL
     [ASM_MESON_TAC[ALL_MEM; MEM_MAP]; ALL_TAC] THEN
    ASM_REWRITE_TAC[embd_emap];
    SUBGOAL_THEN `face_simple Gc (MAP (edge_map Gc) (rc:(A)list))` MP_TAC THENL
     [ASM_MESON_TAC[scycle]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FACE_SIMPLE_CONG THEN ASM_MESON_TAC[ALL_MEM]]);;

(* ------------------------------------------------------------------------- *)
(* The embedding on the disk darts: into dart Gm, injective, commutes with   *)
(* node and (off the ring) with edge (Coq embdd, embddN, embddE).            *)
(* ------------------------------------------------------------------------- *)

let EMBED_IN_DART = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN dart Gc ==> embed Gc Gm rc h x IN dart Gm`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL] THEN
  SUBGOAL_THEN `!y:A. y IN kernel Gc rc ==> (h:A->B) y IN dart Gm`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  USE_CTX EMBED_CASES (MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[embed] THEN
  REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY DISCH_TAC THEN
  REPEAT(FIRST(map MATCH_MP_TAC
    [EDGE_MAP_IN_DART; NODE_MAP_IN_DART; FACE_MAP_IN_DART])) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let EMBDD_INJ = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> INJ (embed Gc Gm rc h) (embd_D Gc rc) (dart Gm)`,
  REPEAT GEN_TAC THEN CTX_TAC [EMBED_IN_DART] THEN
  REWRITE_TAC[INJ; IN_EMBD_D] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN USE_CTX EMBED_INJ MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let EMBDDN = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !u. u IN embd_D Gc rc
             ==> embed Gc Gm rc h (node_map (embed_disk Gc rc) u) =
                 node_map Gm (embed Gc Gm rc h u)`,
  REPEAT GEN_TAC THEN CTX_TAC [] THEN
  USE_CTX CTX_RING
    (fun th -> STRIP_ASSUME_TAC(MATCH_MP EMBD_DISK_COMPONENTS th)) THEN
  X_GEN_TAC `u:A` THEN DISCH_TAC THEN ASM_SIMP_TAC[embd_nmap] THEN
  USE_CTX EMBEDN MATCH_MP_TAC THEN
  UNDISCH_TAC `(u:A) IN embd_D Gc rc` THEN REWRITE_TAC[IN_EMBD_D]);;

let EMBDDE = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !u. u IN embd_D Gc rc /\ ~MEM u (MAP (edge_map Gc) rc)
             ==> embed Gc Gm rc h (edge_map (embed_disk Gc rc) u) =
                 edge_map Gm (embed Gc Gm rc h u)`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_E2C] THEN
  USE_CTX CTX_RING
    (fun th -> STRIP_ASSUME_TAC(MATCH_MP EMBD_DISK_COMPONENTS th)) THEN
  X_GEN_TAC `u:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~MEM (edge_map Gc (u:A)) rc` ASSUME_TAC THENL
   [UNDISCH_TAC `~MEM (u:A) (MAP (edge_map Gc) rc)` THEN
    REWRITE_TAC[CONTRAPOS_THM; MEM_MAP] THEN DISCH_TAC THEN
    EXISTS_TAC `edge_map Gc (u:A)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[embd_emap] THEN USE_CTX EMBEDE MATCH_MP_TAC THEN
  UNDISCH_TAC `(u:A) IN embd_D Gc rc` THEN SIMP_TAC[IN_EMBD_D]);;

(* ------------------------------------------------------------------------- *)
(* The remainder map (Coq embed_rem): rdom' is the image under embed of the  *)
(* disk darts off the ring erc = MAP (edge_map Gc) rc, and embr_D is dart Gm *)
(* minus rdom'.                                                              *)
(* ------------------------------------------------------------------------- *)

let IN_RDOM = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) rc h x.
     x IN rdom' Gc Gm rc h <=>
     ?u. u IN embd_D Gc rc /\ ~MEM u (MAP (edge_map Gc) rc) /\
         x = embed Gc Gm rc h u`,
  REWRITE_TAC[rdom'; IN_ELIM_THM]);;

let IN_EMBR_D = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) rc h x.
     x IN embr_D Gc Gm rc h <=> x IN dart Gm /\ ~(x IN rdom' Gc Gm rc h)`,
  REWRITE_TAC[embr_D; IN_ELIM_THM]);;

let ERC_DISTINCT = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> PAIRWISE (\a b. ~(a = b)) (MAP (edge_map Gc) rc)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CTX_RING) THEN
  STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_INJ_MAP THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[EDGEI]);;

let REM_FACTS = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> (!u. u IN embd_D Gc rc ==> embed Gc Gm rc h u IN dart Gm) /\
         (!u v. u IN embd_D Gc rc /\ v IN embd_D Gc rc /\
                embed Gc Gm rc h u = embed Gc Gm rc h v
                ==> u = v) /\
         (!u. MEM u (MAP (edge_map Gc) rc) ==> u IN embd_D Gc rc) /\
         (!u. u IN embd_D Gc rc
              ==> edge_map (embed_disk Gc rc) u IN embd_D Gc rc /\
                  node_map (embed_disk Gc rc) u IN embd_D Gc rc /\
                  face_map (embed_disk Gc rc) u IN embd_D Gc rc) /\
         (!u. MEM (edge_map (embed_disk Gc rc) u) (MAP (edge_map Gc) rc) <=>
              MEM u (MAP (edge_map Gc) rc))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    let rg = MATCH_MP CTX_RING th in
    STRIP_ASSUME_TAC(REWRITE_RULE[scycle] (MATCH_MP SCYCLE_EMBD_RING rg)) THEN
    MP_TAC(REWRITE_RULE[GSYM ALL_MEM] (MATCH_MP ERC_IN_EMBD_D rg)) THEN
    MP_TAC(CONJUNCT1(CONJUNCT2(MATCH_MP EMBD_MAPS rg))) THEN
    REWRITE_TAC[GSYM(CONJUNCT2(MATCH_MP EMBD_DISK_COMPONENTS rg))]) THEN
  DISCH_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_EMBD_D] THEN REPEAT STRIP_TAC THEN
    USE_CTX EMBED_IN_DART MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_EMBD_D] THEN REPEAT STRIP_TAC THEN
    USE_CTX EMBED_INJ MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    GEN_TAC THEN MATCH_MP_TAC LIST_CYCLE_MEM_IMAGE THEN
    EXISTS_TAC `dart (embed_disk (Gc:(A)hypermap) rc)` THEN
    ASM_REWRITE_TAC[ETA_AX; EDGE_MAP_PERMUTES]]);;

let REM_IN_DART,REM_INJ,REM_ERC_D,REM_MAPS_D,REM_ERC_EDGE =
  match CTX_CONJS REM_FACTS with
    [a;b;c;d;e] -> a,b,c,d,e
  | _ -> failwith "REM_FACTS";;

let EMBED_IN_RDOM = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !u. u IN embd_D Gc rc
             ==> (embed Gc Gm rc h u IN rdom' Gc Gm rc h <=>
                  ~MEM u (MAP (edge_map Gc) rc))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_RDOM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `u:A = v` SUBST1_TAC THENL
     [USE_CTX REM_INJ MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_TAC THEN EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[]]);;

let EMBED_ERC_IN_EMBR_D = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !u. MEM u (MAP (edge_map Gc) rc)
             ==> embed Gc Gm rc h u IN embr_D Gc Gm rc h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:A) IN embd_D Gc rc` ASSUME_TAC THENL
   [USE_CTX REM_ERC_D MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_EMBR_D] THEN CONJ_TAC THENL
   [USE_CTX REM_IN_DART MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    USE_CTX EMBED_IN_RDOM (fun th -> ASM_SIMP_TAC[th])]);;

(* A disk image that is a remainder dart comes from the ring erc.            *)

let EMBD_IMAGE_CASES = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x w. x IN embr_D Gc Gm rc h /\ w IN embd_D Gc rc /\
               embed Gc Gm rc h w = x
               ==> MEM w (MAP (edge_map Gc) rc)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_EMBR_D] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  USE_CTX EMBED_IN_RDOM (MP_TAC o SPEC `w:A`) THEN ASM_REWRITE_TAC[]);;

(* The clauses of the remainder maps.                                        *)

let EMBR_SELECT = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) u0.
     embed_context Gm Gc rc h /\ MEM u0 (MAP (edge_map Gc) rc)
     ==> (@u. MEM u (MAP (edge_map Gc) rc) /\
              embed Gc Gm rc h u0 = embed Gc Gm rc h u) = u0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `u:A` THEN
  REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN CONV_TAC SYM_CONV THEN USE_CTX REM_INJ MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_CTX REM_ERC_D MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let EMBR_NMAP_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) u.
     embed_context Gm Gc rc h /\ MEM u (MAP (edge_map Gc) rc)
     ==> embr_nmap Gc Gm rc h (embed Gc Gm rc h u) =
         embed Gc Gm rc h
           (node_map (embed_disk Gc rc) (face_map (embed_disk Gc rc) u))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `u:A`] EMBR_SELECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `embed Gc Gm rc (h:A->B) u IN embr_D Gc Gm rc h`
    ASSUME_TAC THENL
   [USE_CTX EMBED_ERC_IN_EMBR_D MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v. MEM v (MAP (edge_map Gc) rc) /\
                    embed Gc Gm rc (h:A->B) u = embed Gc Gm rc h v`
    ASSUME_TAC THENL [EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[embr_nmap]);;

let EMBR_NMAP_OFF = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) rc (h:A->B) x.
     x IN embr_D Gc Gm rc h /\
     ~(?u. MEM u (MAP (edge_map Gc) rc) /\ x = embed Gc Gm rc h u)
     ==> embr_nmap Gc Gm rc h x = node_map Gm x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[embr_nmap]);;

let EMBR_FMAP_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B) x u.
     embed_context Gm Gc rc h /\ MEM u (MAP (edge_map Gc) rc) /\
     x IN embr_D Gc Gm rc h /\ edge_map Gm x = embed Gc Gm rc h u
     ==> embr_fmap Gc Gm rc h x =
         embed Gc Gm rc h (edge_map (embed_disk Gc rc) u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                 `u:A`] EMBR_SELECT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?v. MEM v (MAP (edge_map Gc) rc) /\
                    embed Gc Gm rc (h:A->B) u = embed Gc Gm rc h v`
    ASSUME_TAC THENL [EXISTS_TAC `u:A` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[embr_fmap]);;

let EMBR_FMAP_OFF = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) rc (h:A->B) x.
     x IN embr_D Gc Gm rc h /\
     ~(?u. MEM u (MAP (edge_map Gc) rc) /\ edge_map Gm x = embed Gc Gm rc h u)
     ==> embr_fmap Gc Gm rc h x = face_map Gm x`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[embr_fmap]);;

(* ------------------------------------------------------------------------- *)
(* The remainder maps keep embr_D and compose to the identity (Coq           *)
(* embr_edge/node/face_subproof and embed_rem_subproof).                     *)
(* ------------------------------------------------------------------------- *)

let REM_EDGE_INTO = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN embr_D Gc Gm rc h ==> edge_map Gm x IN embr_D Gc Gm rc h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN dart Gm` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN embr_D Gc Gm rc (h:A->B)` THEN SIMP_TAC[IN_EMBR_D];
    ALL_TAC] THEN
  REWRITE_TAC[IN_EMBR_D; IN_RDOM] THEN ASM_SIMP_TAC[EDGE_MAP_IN_DART] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `embed Gc Gm rc (h:A->B) (edge_map (embed_disk Gc rc) v) = x`
    ASSUME_TAC THENL
   [USE_CTX EMBDDE (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    USE_CTX CTX_E2M (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `MEM (edge_map (embed_disk Gc rc) (v:A)) (MAP (edge_map Gc) rc)`
   MP_TAC THENL
   [USE_CTX EMBD_IMAGE_CASES MATCH_MP_TAC THEN EXISTS_TAC `x:B` THEN
    ASM_REWRITE_TAC[] THEN USE_CTX REM_MAPS_D (fun th -> ASM_SIMP_TAC[th]);
    USE_CTX REM_ERC_EDGE (fun th -> ASM_REWRITE_TAC[th])]);;

let REM_NODE_INTO = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN embr_D Gc Gm rc h
             ==> embr_nmap Gc Gm rc h x IN embr_D Gc Gm rc h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN dart Gm` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:B) IN embr_D Gc Gm rc (h:A->B)` THEN SIMP_TAC[IN_EMBR_D];
    ALL_TAC] THEN
  ASM_CASES_TAC `?u. MEM u (MAP (edge_map Gc) rc) /\
                     (x:B) = embed Gc Gm rc (h:A->B) u`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                   `h:A->B`; `u:A`] EMBR_NMAP_RING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_CTX EMBED_ERC_IN_EMBR_D MATCH_MP_TAC THEN
    USE_CTX REM_ERC_EDGE (fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN
    ASM_REWRITE_TAC[faceK];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:B`] EMBR_NMAP_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_EMBR_D; IN_RDOM] THEN ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `node_map (embed_disk Gc rc) (v:A) IN embd_D Gc rc`
    ASSUME_TAC THENL
   [USE_CTX REM_MAPS_D (fun th -> ASM_SIMP_TAC[th]); ALL_TAC] THEN
  SUBGOAL_THEN
   `embed Gc Gm rc (h:A->B)
      (node_map (embed_disk Gc rc) (node_map (embed_disk Gc rc) v)) = x`
   ASSUME_TAC THENL
   [USE_CTX EMBDDN (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    USE_CTX CTX_N3M (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  UNDISCH_TAC `~(?u. MEM u (MAP (edge_map Gc) rc) /\
                     (x:B) = embed Gc Gm rc (h:A->B) u)` THEN
  REWRITE_TAC[] THEN
  EXISTS_TAC
   `node_map (embed_disk Gc rc) (node_map (embed_disk Gc rc) (v:A))` THEN
  ASM_REWRITE_TAC[] THEN USE_CTX EMBD_IMAGE_CASES MATCH_MP_TAC THEN
  EXISTS_TAC `x:B` THEN ASM_REWRITE_TAC[] THEN
  USE_CTX REM_MAPS_D (fun th -> ASM_SIMP_TAC[th]));;

let REM_FACE_INTO = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN embr_D Gc Gm rc h
             ==> embr_fmap Gc Gm rc h x IN embr_D Gc Gm rc h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN dart Gm /\ edge_map Gm x IN embr_D Gc Gm rc (h:A->B)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(x:B) IN embr_D Gc Gm rc (h:A->B)` THEN SIMP_TAC[IN_EMBR_D];
      USE_CTX REM_EDGE_INTO MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `?u. MEM u (MAP (edge_map Gc) rc) /\
                     edge_map Gm (x:B) = embed Gc Gm rc (h:A->B) u`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                   `h:A->B`; `x:B`; `u:A`] EMBR_FMAP_RING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    USE_CTX EMBED_ERC_IN_EMBR_D MATCH_MP_TAC THEN
    USE_CTX REM_ERC_EDGE (fun th -> ASM_REWRITE_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:B`] EMBR_FMAP_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_EMBR_D; IN_RDOM] THEN ASM_SIMP_TAC[FACE_MAP_IN_DART] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `embed Gc Gm rc (h:A->B) (node_map (embed_disk Gc rc) v) = edge_map Gm x`
   ASSUME_TAC THENL
   [USE_CTX EMBDDN (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `edge_map Gm (x:B)`] edgeK) THEN
    USE_CTX CTX_E2M (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  UNDISCH_TAC `~(?u. MEM u (MAP (edge_map Gc) rc) /\
                     edge_map Gm (x:B) = embed Gc Gm rc (h:A->B) u)` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `node_map (embed_disk Gc rc) (v:A)` THEN
  ASM_REWRITE_TAC[] THEN USE_CTX EMBD_IMAGE_CASES MATCH_MP_TAC THEN
  EXISTS_TAC `edge_map Gm (x:B)` THEN ASM_REWRITE_TAC[] THEN
  USE_CTX REM_MAPS_D (fun th -> ASM_SIMP_TAC[th]));;

let REM_ENF = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN embr_D Gc Gm rc h
             ==> embr_nmap Gc Gm rc h (embr_fmap Gc Gm rc h x) =
                 edge_map Gm x`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `edge_map Gm (x:B) IN embr_D Gc Gm rc (h:A->B) /\
                embr_fmap Gc Gm rc h x IN embr_D Gc Gm rc h`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_CTX REM_EDGE_INTO MATCH_MP_TAC;
      USE_CTX REM_FACE_INTO MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `node_map Gm (face_map Gm (x:B)) = edge_map Gm x`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Gm:(B)hypermap`; `edge_map Gm (x:B)`] edgeK) THEN
    USE_CTX CTX_E2M (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  ASM_CASES_TAC `?u. MEM u (MAP (edge_map Gc) rc) /\
                     edge_map Gm (x:B) = embed Gc Gm rc (h:A->B) u`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                   `h:A->B`; `x:B`; `u:A`] EMBR_FMAP_RING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`;
                   `h:A->B`; `edge_map (embed_disk Gc rc) (u:A)`]
                  EMBR_NMAP_RING) THEN
    USE_CTX REM_ERC_EDGE (fun th -> ASM_REWRITE_TAC[th; edgeK]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`;
                 `x:B`] EMBR_FMAP_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`Gc:(A)hypermap`; `Gm:(B)hypermap`; `rc:(A)list`; `h:A->B`;
                 `face_map Gm (x:B)`] EMBR_NMAP_OFF) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> (~p ==> q) ==> q`) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:A) IN embd_D Gc rc` ASSUME_TAC THENL
   [USE_CTX REM_ERC_D MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `embed Gc Gm rc (h:A->B) (node_map (embed_disk Gc rc) u) = edge_map Gm x`
   ASSUME_TAC THENL
   [USE_CTX EMBDDN (fun th -> ASM_SIMP_TAC[th]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(?u. MEM u (MAP (edge_map Gc) rc) /\
                     edge_map Gm (x:B) = embed Gc Gm rc (h:A->B) u)` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `node_map (embed_disk Gc rc) (u:A)` THEN
  ASM_REWRITE_TAC[] THEN USE_CTX EMBD_IMAGE_CASES MATCH_MP_TAC THEN
  EXISTS_TAC `edge_map Gm (x:B)` THEN ASM_REWRITE_TAC[] THEN
  USE_CTX REM_MAPS_D (fun th -> ASM_SIMP_TAC[th]));;

let EMBED_REM_COMPONENTS = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> dart (embed_rem Gc Gm rc h) = embr_D Gc Gm rc h /\
         edge_map (embed_rem Gc Gm rc h) = embr_emap Gc Gm rc h /\
         node_map (embed_rem Gc Gm rc h) = embr_nmap Gc Gm rc h /\
         face_map (embed_rem Gc Gm rc h) = embr_fmap Gc Gm rc h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[embed_rem] THEN
  MATCH_MP_TAC MK_HYPERMAP_COMPONENTS THEN
  MATCH_MP_TAC HYPERMAP_PRED_CANCEL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `dart (Gm:(B)hypermap)` THEN
    REWRITE_TAC[FINITE_DART; SUBSET; IN_EMBR_D] THEN MESON_TAC[];
    SIMP_TAC[embr_emap; embr_nmap; embr_fmap];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN ASM_SIMP_TAC[embr_emap] THEN
    REPEAT CONJ_TAC THENL
     [USE_CTX REM_EDGE_INTO MATCH_MP_TAC;
      USE_CTX REM_NODE_INTO MATCH_MP_TAC;
      USE_CTX REM_FACE_INTO MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:B` THEN
    ASM_CASES_TAC `(x:B) IN embr_D Gc Gm rc (h:A->B)` THENL
     [SUBGOAL_THEN `embr_fmap Gc Gm rc (h:A->B) x IN embr_D Gc Gm rc h`
        ASSUME_TAC THENL
       [USE_CTX REM_FACE_INTO MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `embr_nmap Gc Gm rc (h:A->B) (embr_fmap Gc Gm rc h x) IN
        embr_D Gc Gm rc h`
        ASSUME_TAC THENL
       [USE_CTX REM_NODE_INTO MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[embr_emap] THEN
      USE_CTX REM_ENF (fun th -> ASM_SIMP_TAC[th]) THEN
      USE_CTX CTX_E2M (fun th -> REWRITE_TAC[th]);
      ASM_SIMP_TAC[embr_emap; embr_nmap; embr_fmap]]]);;

(* ------------------------------------------------------------------------- *)
(* The patch: Gm is the disk map and the remainder map glued along the ring  *)
(* erc / embr_ring (Coq embed_patch), hence the remainder map is planar,     *)
(* plain and quasicubic.                                                     *)
(* ------------------------------------------------------------------------- *)

let EMBR_RING_MEM = prove
 (`!(Gc:(A)hypermap) (Gm:(B)hypermap) (rc:(A)list) (h:A->B) y.
     MEM y (embr_ring Gc Gm rc h) <=>
     ?u. MEM u (MAP (edge_map Gc) rc) /\ y = embed Gc Gm rc h u`,
  REWRITE_TAC[embr_ring; MEM_REVERSE; MEM_MAP]);;

let CODOM_EMBR = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN dart Gm
             ==> (x IN embr_D Gc Gm rc h <=>
                  ~(?u. x = embed Gc Gm rc h u /\ u IN embd_D Gc rc) \/
                  (?u. MEM u (MAP (edge_map Gc) rc) /\
                       x = embed Gc Gm rc h u))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[IN_EMBR_D; IN_RDOM] THEN
  USE_CTX REM_INJ (fun th1 ->
    USE_CTX REM_ERC_D (fun th2 -> MESON_TAC[th1; th2])));;

let UCYCLE_EMBR_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> list_cycle (\x y. node_map (embed_rem Gc Gm rc h) x = y)
                    (embr_ring Gc Gm rc h) /\
         PAIRWISE (\x y. ~(x = y)) (embr_ring Gc Gm rc h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_CTX EMBED_REM_COMPONENTS (fun th -> REWRITE_TAC[th]) THEN
  USE_CTX ERC_DISTINCT ASSUME_TAC THEN
  USE_CTX CTX_RING (fun th ->
    STRIP_ASSUME_TAC(REWRITE_RULE[scycle] (MATCH_MP SCYCLE_EMBD_RING th))) THEN
  REWRITE_TAC[embr_ring] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [MAP_REVERSE] THEN
    MATCH_MP_TAC(ISPEC `\a b:A. edge_map (embed_disk Gc rc) b = a`
                       LIST_CYCLE_MAP_REL) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\a b:A. edge_map (embed_disk Gc rc) a = b`;
                     `MAP (edge_map Gc) (rc:(A)list)`]
                    LIST_CYCLE_REVERSE) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN REWRITE_TAC[MEM_REVERSE] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`Gm:(B)hypermap`; `Gc:(A)hypermap`; `rc:(A)list`; `h:A->B`;
                   `edge_map (embed_disk Gc rc) (b:A)`] EMBR_NMAP_RING) THEN
    USE_CTX REM_ERC_EDGE (fun th -> ASM_REWRITE_TAC[th; edgeK]);
    REWRITE_TAC[PAIRWISE_REVERSE] THEN
    SUBGOAL_THEN `(\x y:B. ~(y = x)) = (\x y. ~(x = y))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PAIRWISE_INJ_MAP THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_CTX REM_INJ MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_CTX REM_ERC_D MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let EMBED_PATCH = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> patch Gm (embed_disk Gc rc) (embed_rem Gc Gm rc h)
                (embed Gc Gm rc h) (I:B->B) (MAP (edge_map Gc) rc)
                (embr_ring Gc Gm rc h)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_CTX EMBED_REM_COMPONENTS (fun th ->
    STRIP_ASSUME_TAC th THEN REWRITE_TAC[patch; CONJUNCT1 th]) THEN
  USE_CTX CTX_RING (fun th ->
    REWRITE_TAC[CONJUNCT1(MATCH_MP EMBD_DISK_COMPONENTS th)] THEN
    ASSUME_TAC(MATCH_MP SCYCLE_EMBD_RING th)) THEN
  REPEAT CONJ_TAC THENL
   [USE_CTX EMBDD_INJ ACCEPT_TAC;
    REWRITE_TAC[INJ; I_THM; IN_EMBR_D] THEN MESON_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    USE_CTX UCYCLE_EMBR_RING (ACCEPT_TAC o CONJUNCT1);
    USE_CTX UCYCLE_EMBR_RING (ACCEPT_TAC o CONJUNCT2);
    REWRITE_TAC[MAP_I; I_THM; embr_ring];
    X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    USE_CTX CODOM_EMBR (MP_TAC o SPEC `x:B`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; MEM_MAP; IMAGE_I; I_THM] THEN MESON_TAC[];
    USE_CTX EMBDDE ACCEPT_TAC;
    USE_CTX EMBDDN ACCEPT_TAC;
    ASM_REWRITE_TAC[I_THM] THEN SIMP_TAC[embr_emap];
    ASM_REWRITE_TAC[I_THM; EMBR_RING_MEM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EMBR_NMAP_OFF THEN ASM_REWRITE_TAC[]]);;

let PLAIN_EMBR = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h ==> plain_hypermap (embed_rem Gc Gm rc h)`,
  MESON_TAC[EMBED_PATCH; PLAIN_PATCH; embed_context]);;

let CUBIC_EMBR = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h /\ 2 <= LENGTH rc
     ==> quasicubic (embed_rem Gc Gm rc h) (\z. MEM z (embr_ring Gc Gm rc h))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CUBIC_PATCH THEN
  MAP_EVERY EXISTS_TAC [`Gm:(B)hypermap`; `embed_disk (Gc:(A)hypermap) rc`;
    `embed (Gc:(A)hypermap) (Gm:(B)hypermap) rc (h:A->B)`; `I:B->B`;
    `MAP (edge_map Gc) (rc:(A)list)`] THEN
  ASM_SIMP_TAC[EMBED_PATCH; embr_ring; LENGTH_REVERSE; LENGTH_MAP] THEN
  ASM_MESON_TAC[embed_context]);;

let PLANAR_EMBR = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h /\ 2 <= LENGTH rc
     ==> planar_hypermap (embed_rem Gc Gm rc h)`,
  MESON_TAC[EMBED_PATCH; PLANAR_PATCH; embed_context; LENGTH_MAP]);;

(* ------------------------------------------------------------------------- *)
(* Faces are preserved by the embedding (Coq cface_h1), and the face map     *)
(* commutes with it on the kernel.                                           *)
(* ------------------------------------------------------------------------- *)

let RING_FACE_OFF = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h ==> !y. MEM y rc ==> ~MEM (face_map Gc y) rc`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CTX_RING) THEN
  REWRITE_TAC[scycle] THEN STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN dart Gc` ASSUME_TAC THENL [CFACE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `(y:A) = face_map Gc y` MP_TAC THENL
   [CFACE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> (p ==> F)`) THEN CONV_TAC(RAND_CONV SYM_CONV) THEN
  MATCH_MP_TAC ORBIT_NONFIX THEN EXISTS_TAC `dart (Gc:(A)hypermap)` THEN
  ASM_REWRITE_TAC[ETA_AX; FINITE_DART; FACE_MAP_PERMUTES] THEN
  SUBGOAL_THEN `good_ring_arity Gc (y:A)` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[good_ring_arity; arity] THEN ARITH_TAC);;

let EMBED_FACE_RING = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !y. MEM y rc
             ==> embed Gc Gm rc h (face_map Gc y) =
                 face_map Gm (embed Gc Gm rc h y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN dart Gc /\ ~MEM (face_map Gc y) rc`
    STRIP_ASSUME_TAC THENL
   [USE_CTX CTX_RING STRIP_ASSUME_TAC THEN
    ASM_MESON_TAC[ALL_MEM; RING_FACE_OFF];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
    [GSYM(ISPECL [`Gc:(A)hypermap`; `y:A`] faceK)] THEN
  USE_CTX EMBEDE (fun th ->
    ASM_SIMP_TAC[th; FACE_MAP_IN_DART; NODE_MAP_IN_DART]) THEN
  USE_CTX EMBEDN (fun th -> ASM_SIMP_TAC[th; FACE_MAP_IN_DART; nodeK]));;

let EMBED_CFACE_REP = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !z. z IN dart Gc
             ==> ?z'. z' IN embd_D Gc rc /\ cface Gc z z' /\
                      cface Gm (embed Gc Gm rc h z) (embed Gc Gm rc h z')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `MEM (z:A) rc` THENL
   [EXISTS_TAC `face_map Gc (z:A)` THEN
    USE_CTX EMBED_FACE_RING (fun th -> ASM_SIMP_TAC[th; CFT_FACE]) THEN
    REWRITE_TAC[IN_EMBD_D] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FACE_MAP_IN_DART THEN ASM_REWRITE_TAC[];
      USE_CTX RING_FACE_OFF MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[IN_EMBD_D; CFACE_REFL]]);;

let CFACE_H1_BC = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x y. x IN embd_D Gc rc /\ y IN embd_D Gc rc /\ cface Gc x y
               ==> cface Gm (embed Gc Gm rc h x) (embed Gc Gm rc h y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  USE_CTX EMBED_PATCH (MP_TAC o MATCH_MP PATCH_CFACE_HD) THEN
  USE_CTX CTX_RING (fun th ->
    REWRITE_TAC[CONJUNCT1(MATCH_MP EMBD_DISK_COMPONENTS th)] THEN
    MP_TAC(MATCH_MP CFACE_EMBD th)) THEN
  MESON_TAC[]);;

let CFACE_H1 = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x y. cface Gc x y
               ==> cface Gm (embed Gc Gm rc h x) (embed Gc Gm rc h y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
  DISCH_TAC THEN ASM_CASES_TAC `(x:A) IN dart Gc` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`Gc:(A)hypermap`; `x:A`; `y:A`] CFACE_OUT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CFACE_REFL]] THEN
  SUBGOAL_THEN `(y:A) IN dart Gc` ASSUME_TAC THENL
   [MATCH_MP_TAC CFT_DART THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_CTX EMBED_CFACE_REP
    (fun th -> MP_TAC(SPEC `y:A` th) THEN MP_TAC(SPEC `x:A` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y':A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cface Gm (embed Gc Gm rc (h:A->B) x') (embed Gc Gm rc h y')`
    MP_TAC THENL
   [USE_CTX CFACE_H1_BC MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CFACE_TAC[];
    CFACE_TAC[]]);;

let EMBED_FACE_KERNEL = prove
 (`!(Gm:(B)hypermap) (Gc:(A)hypermap) (rc:(A)list) (h:A->B).
     embed_context Gm Gc rc h
     ==> !x. x IN kernel Gc rc
             ==> embed Gc Gm rc h (face_map Gc x) =
                 face_map Gm (embed Gc Gm rc h x)`,
  REPEAT GEN_TAC THEN CTX_TAC [CTX_KERNEL] THEN X_GEN_TAC `x:A` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `face_map Gc (x:A) IN kernel Gc rc` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[EMBED_ON_KERNEL]);;
