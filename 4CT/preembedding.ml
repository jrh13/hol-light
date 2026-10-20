(* ========================================================================= *)
(* 4CT/preembedding.ml                                                       *)
(*                                                                           *)
(* coloring.v, the Preembedding section (coloring.v:483-511), with its       *)
(* prerequisite simplify_rlink (geometry.v:692).  A preembedding is a        *)
(* partial hypermap morphism h : H -> H' on a set a of darts: a morphism for *)
(* face_map and arity on a, whose edge-commuting darts (edge_central) cover  *)
(* a up to cface and are rlink-connected; the predicate is used by quiz.ml   *)
(* and embed.ml.  SIMPLIFY_RLINK shortens an rlink path to a face-simple     *)
(* one, and PREEMBEDDING_SIMPLE_PATH (Coq preembedding_simple_path, used in  *)
(* embed_prelim.ml) gives, for darts x and y with edge x and y in a          *)
(* face-closed a, a nonempty face-simple rlink path from x ending in the     *)
(* face of y through edge-central darts of a.  Gonthier's fclosure and       *)
(* fclosed are written out (?y. edge_central H H' h y /\ cface H x y, and    *)
(* !w. w IN a ==> face_map H w IN a).                                        *)
(* ========================================================================= *)

needs "4CT/geometry.ml";;
needs "4CT/jordan.ml";;

(* Off the dart set the face orbit is a singleton, so cface a b <=> b = a.   *)
let CFACE_OUT = prove
 (`!(H:(A)hypermap) a b. ~(a IN dart H) ==> (cface H a b <=> b = a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cface; face; orbit_map; IN_ELIM_THM] THEN
  SUBGOAL_THEN `face_map H (a:A) = a` ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_FIX_OUTSIDE; FACE_MAP_PERMUTES]; ALL_TAC] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER];
    DISCH_TAC THEN EXISTS_TAC `0` THEN ASM_REWRITE_TAC[ITER]]);;

(* ------------------------------------------------------------------------- *)
(* SIMPLIFY_RLINK (Gonthier simplify_rlink, geometry.v:692): an rlink path   *)
(* from x can be shortened to a face-simple rlink path with the same last    *)
(* dart, empty iff the original is, whose members are members of the         *)
(* original.  Strong induction on the length (WF_INDUCT_TAC): if the head h  *)
(* lies in the face band of the tail t, project it to the first cofacial     *)
(* member z = fproj H t h, split t at z (MEM_SPLIT, LIST_PATH_APPEND)        *)
(* and recurse on the shorter path z :: t2 (rlink x z by CFACE_TAC);         *)
(* otherwise keep the head and recurse on the tail.                          *)
(* ------------------------------------------------------------------------- *)
let SIMPLIFY_RLINK = prove
 (`!(H:(A)hypermap) x p.
     list_path (rlink H) x p
     ==> ?q. list_path (rlink H) x q /\ face_simple H q /\
             LAST (CONS x p) = LAST (CONS x q) /\
             (p = [] <=> q = []) /\ ALL (\z. MEM z p) q`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  WF_INDUCT_TAC `LENGTH(p:A list)` THEN X_GEN_TAC `x:A` THEN
  POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC(ISPEC `p:(A)list` list_CASES) THENL
   [DISCH_TAC THEN DISCH_TAC THEN EXISTS_TAC `[]:(A)list` THEN
    REWRITE_TAC[list_path; face_simple; ALL];
    ALL_TAC] THEN
  REWRITE_TAC[LENGTH; LT_SUC_LE; list_path] THEN DISCH_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `fband H t (h:A)` THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FPROJ_IN_FBAND) THEN
    ABBREV_TAC `z = fproj H t (h:A)` THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `t1:(A)list` (X_CHOOSE_THEN `t2:(A)list`
      SUBST_ALL_TAC) o MATCH_MP MEM_SPLIT) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (z:A) t2`) THEN
    REWRITE_TAC[LENGTH_APPEND; LENGTH; ARITH_RULE `SUC n <= m + SUC n`] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LIST_PATH_APPEND; list_path]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[list_path] THEN CFACE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:(A)list` THEN
    ASM_REWRITE_TAC[NOT_CONS_NIL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_CONS_NIL]) THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      REWRITE_TAC[LAST_CLAUSES; LAST_CONS_APPEND_GEN];
      FIRST_X_ASSUM(MATCH_MP_TAC o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] ALL_MEM_TRANS)) THEN
      REWRITE_TAC[GSYM ALL_MEM; MEM; MEM_APPEND] THEN MESON_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `t:(A)list`) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `h:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `CONS (h:A) q` THEN
    ASM_REWRITE_TAC[list_path; face_simple; LAST; NOT_CONS_NIL; ALL; MEM] THEN
    UNDISCH_TAC `~fband H t (h:A)` THEN
    UNDISCH_TAC `ALL (\z:A. MEM z t) q` THEN
    REWRITE_TAC[FBAND_MEM_IFF; GSYM ALL_MEM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The Preembedding section (coloring.v:483): two hypermaps H (:A) and H'    *)
(* (:B) and a map h : A -> B.  edge_central H H' h x says that h commutes    *)
(* with edge_map at x; preembedding H H' h a is Gonthier's record, with      *)
(* fclosure written out in the cover clause (?y. edge_central H H' h y /\    *)
(* cface H x y) and fclosed face a written out as !w. w IN a ==> face_map H  *)
(* w IN a in the lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)
let edge_central = new_definition
  `edge_central (H:(A)hypermap) (H':(B)hypermap) (h:A->B) (x:A) <=>
     h (edge_map H x) = edge_map H' (h x)`;;

let preembedding = new_definition
  `preembedding (H:(A)hypermap) (H':(B)hypermap) (h:A->B) (a:A->bool) <=>
     (!x. x IN a ==> h (face_map H x) = face_map H' (h x)) /\
     (!x. x IN a ==> arity H' (h x) = arity H x) /\
     (!x. x IN a ==> ?y. edge_central H H' h y /\ cface H x y) /\
     rlink_connected H (\z. z IN a /\ edge_central H H' h z)`;;

(* A face-closed set is closed under cface.                                  *)
let FCLOSED_CFACE = prove
 (`!(H:(A)hypermap) a x y.
     (!w. w IN a ==> face_map H w IN a) /\ cface H x y /\ x IN a ==> y IN a`,
  REWRITE_TAC[cface; face; ORBIT_MAP_ITER; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ITER];
    ASM_REWRITE_TAC[ITER] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* PREEMBEDDING_SIMPLE_PATH (Coq preembedding_simple_path, coloring.v:511).  *)
(* The cover clause gives edge-central darts z and wt cofacial with edge x   *)
(* and with y, both in a by FCLOSED_CFACE; rlink_connected gives an rlink    *)
(* path p from node (face z) to wt through the edge-central darts of a.      *)
(* Since edge (node (face z)) = z (faceK) is cofacial with edge x, p is also *)
(* an rlink path from x; SIMPLIFY_RLINK makes it face-simple, keeping its    *)
(* last dart (so cface (LAST (CONS x q)) y by CFACE_SYM_GEN) and, by         *)
(* ALL_MEM_TRANS, the membership of its darts in a and edge_central.         *)
(* ------------------------------------------------------------------------- *)
let PREEMBEDDING_SIMPLE_PATH = prove
 (`!(H:(A)hypermap) (H':(B)hypermap) h a.
     preembedding H H' h a /\ (!w. w IN a ==> face_map H w IN a)
     ==> !x y. edge_map H x IN a /\ y IN a
         ==> ?p. list_path (rlink H) x p /\ cface H (LAST (CONS x p)) y /\
                 ~(p = []) /\ face_simple H p /\
                 ALL (\z. z IN a /\ edge_central H H' h z) p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[preembedding; rlink_connected] THEN
  INTRO_TAC "(hf ha cover conn) closed; !x y; ex ya" THEN
  REMOVE_THEN "cover" (fun th ->
    MP_TAC(SPEC `y:A` th) THEN MP_TAC(SPEC `edge_map H x:A` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `wt:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:A) IN a /\ (wt:A) IN a` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FCLOSED_CFACE]; ALL_TAC] THEN
  REMOVE_THEN "conn" (MP_TAC o SPECL [`z:A`; `wt:A`]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(A)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `list_path (rlink H) (x:A) p` MP_TAC THENL
   [UNDISCH_TAC
     `list_path (rlink H) (node_map H (face_map H z)) (p:A list)` THEN
    UNDISCH_TAC `~(p:(A)list = [])` THEN
    STRUCT_CASES_TAC(ISPEC `p:(A)list` list_CASES) THEN
    REWRITE_TAC[list_path; NOT_CONS_NIL; rlink; faceK] THEN
    ASM_MESON_TAC[CFT_TRANS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(A)list` STRIP_ASSUME_TAC o
    MATCH_MP SIMPLIFY_RLINK) THEN
  EXISTS_TAC `q:(A)list` THEN
  ASM_MESON_TAC[LAST_CONS_NE; CFACE_SYM_GEN; ALL_MEM_TRANS]);;
