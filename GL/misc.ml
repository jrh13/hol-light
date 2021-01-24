(* ========================================================================= *)
(* Miscellanea                                                               *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2021.              *)
(* ========================================================================= *)

let LABEL_ASM_CASES_TAC s tm =
  ASM_CASES_TAC tm THEN POP_ASSUM (LABEL_TAC s);;

(* ------------------------------------------------------------------------- *)
(* Monadic bind for lists.                                                   *)
(* ------------------------------------------------------------------------- *)

let FLATMAP = new_recursive_definition list_RECURSION
  `(!f:A->B list. FLATMAP f [] = []) /\
   (!f:A->B list h t. FLATMAP f (CONS h t) = APPEND (f h) (FLATMAP f t))`;;

let MEM_FLATMAP = prove
 (`!x f:A->B list l. MEM x (FLATMAP f l) <=> ?y. MEM y l /\ MEM x (f y)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[FLATMAP; MEM; MEM_APPEND] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Subtraction of lists: returns the first list without the elements         *)
(* occurring in the second list.                                             *)
(* ------------------------------------------------------------------------- *)

let LISTDIFF = new_definition
  `LISTDIFF l m = FILTER (\x:A. ~MEM x m) l`;;

let MEM_LISTDIFF = prove
 (`!x:A l m. MEM x (LISTDIFF l m) <=> MEM x l /\ ~MEM x m`,
  REWRITE_TAC[LISTDIFF; MEM_FILTER] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sublist relation.                                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("SUBLIST",get_infix_status "SUBSET");;

let SUBLIST = new_definition
  `l SUBLIST m <=> (!x:A. MEM x l ==> MEM x m)`;;

let NIL_NOT_MEM = prove
 (`!l:A list. l = [] <=> !x. ~(MEM x l)`,
  GEN_TAC THEN STRUCT_CASES_TAC (SPEC `l:A list` list_CASES) THEN
  REWRITE_TAC[MEM; NOT_CONS_NIL] THEN MESON_TAC[]);;

let SUBLIST_NIL = prove
 (`!l:A list. l SUBLIST [] <=> l = []`,
  REWRITE_TAC[SUBLIST; MEM; NIL_NOT_MEM]);;

let NIL_SUBLIST = prove
 (`!l:A list. [] SUBLIST l`,
  REWRITE_TAC[SUBLIST; MEM]);;

let SUBLIST_REFL = prove
 (`!l:A list. l SUBLIST l`,
  REWRITE_TAC[SUBLIST]);;

let CONS_SUBLIST = prove
 (`!h:A t l. CONS h t SUBLIST l <=> MEM h l /\ t SUBLIST l`,
  REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[]);;

let SUBLIST_TRANS = prove
 (`!l m n. l SUBLIST m /\ m SUBLIST n ==> l SUBLIST n`,
  REWRITE_TAC[SUBLIST] THEN MESON_TAC[]);;

let LISTDIFF_SUBLIST = prove
 (`!l m:A list.  LISTDIFF m l SUBLIST m`,
  REWRITE_TAC[SUBLIST; MEM_LISTDIFF] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lists without duplicates.                                                 *)
(* ------------------------------------------------------------------------- *)

let NOREPETITION = new_definition
  `NOREPETITION l <=> PAIRWISE (\x y:A. ~(x = y)) l`;;

let NOREPETITION_CLAUSES = prove
 (`NOREPETITION [] /\
   (!h:A t. NOREPETITION (CONS h t) <=> ~MEM h t /\ NOREPETITION t)`,
  REWRITE_TAC[NOREPETITION; PAIRWISE; GSYM ALL_MEM] THEN MESON_TAC[]);;

let NOREPETITION_LIST_OF_SET = prove
 (`!s:A->bool. FINITE s ==> NOREPETITION (list_of_set s)`,
  INTRO_TAC "!s; s" THEN
  REWRITE_TAC[NOREPETITION; GSYM HAS_SIZE_SET_OF_LIST] THEN
  ASM_SIMP_TAC[SET_OF_LIST_OF_SET; LENGTH_LIST_OF_SET] THEN
  ASM_REWRITE_TAC[GSYM FINITE_HAS_SIZE]);;

let EXISTS_NOREPETITION = prove
 (`!l:A list. ?m. NOREPETITION m /\ l SUBLIST m /\ m SUBLIST l`,
  GEN_TAC THEN EXISTS_TAC `list_of_set (set_of_list l):A list` THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  REWRITE_TAC[SUBLIST] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST]);;

let NOREPETION_FILTER = prove
 (`!P l:A list. NOREPETITION l ==> NOREPETITION (FILTER P l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[NOREPETITION_CLAUSES; FILTER; COND_ELIM_THM; MEM_FILTER]);;

(* ------------------------------------------------------------------------- *)
(* Further general results about lists:                                      *)
(* size of the set of lists with bounded length.                             *)
(* ------------------------------------------------------------------------- *)

let DELETE_HAS_SIZE = prove
 (`!s a:A n. s DELETE a HAS_SIZE n <=>
             a IN s /\ s HAS_SIZE SUC n \/
             ~(a IN s) /\ s HAS_SIZE n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE; FINITE_DELETE] THEN
  ASM_CASES_TAC `FINITE (s:A->bool)` THEN ASM_SIMP_TAC[CARD_DELETE] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(CARD (s:A->bool) = 0)`
    (fun th -> MP_TAC th THEN ARITH_TAC) THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

let HAS_SIZE_LENGTH_EQ = prove
 (`!s m n.
     s HAS_SIZE m
     ==> {l | LENGTH l = n /\ !x:A. MEM x l ==> x IN s} HAS_SIZE m EXP n`,
  FIX_TAC "s m" THEN INDUCT_TAC THEN INTRO_TAC "s" THENL
  [SUBGOAL_THEN `m EXP 0 = SUC 0` (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXP; ONE]; ALL_TAC] THEN
   REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
   MAP_EVERY EXISTS_TAC [`[]:A list`; `{}:A list->bool`] THEN
   REWRITE_TAC[NOT_IN_EMPTY; LENGTH_EQ_NIL] THEN
   REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM] THEN MESON_TAC[MEM];
   ALL_TAC] THEN
  SUBGOAL_THEN `m EXP SUC n = m * m EXP n` SUBST1_TAC THENL
  [REWRITE_TAC[EXP]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{l | LENGTH l = SUC n /\ (!x:A. MEM x l ==> x IN s)} =
     IMAGE (UNCURRY CONS)
           (s CROSS {l | LENGTH l = n /\ (!x. MEM x l ==> x IN s)})`
    SUBST1_TAC THENL
  [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET;
               FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
   CONJ_TAC THENL
   [GEN_TAC THEN STRUCT_CASES_TAC (ISPEC `l:A list` (cases "list")) THEN
    REWRITE_TAC[LENGTH; NOT_SUC; SUC_INJ; MEM] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; UNCURRY_DEF; injectivity "list";
                IN_CROSS; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
   REWRITE_TAC[FORALL_IN_CROSS; IMP_CONJ; RIGHT_FORALL_IMP_THM;
               FORALL_IN_GSPEC] THEN
   REWRITE_TAC[IN_ELIM_THM; UNCURRY_DEF; LENGTH; SUC_INJ; MEM] THEN
   MESON_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
  [SIMP_TAC[FORALL_PAIR_THM; UNCURRY_DEF; CONS_11; PAIR_EQ];
  ASM_SIMP_TAC[HAS_SIZE_CROSS]]);;

let FINITE_LENGTH_EQ = prove
 (`!s n. FINITE s ==> FINITE {l | LENGTH l = n /\ !x:A. MEM x l ==> x IN s}`,
  MESON_TAC[HAS_SIZE; HAS_SIZE_LENGTH_EQ]);;

let FINITE_LENGTH_LE = prove
 (`!s n. FINITE s ==> FINITE {l | LENGTH l <= n /\ !x:A. MEM x l ==> x IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
    `UNIONS (IMAGE (\k. {l | LENGTH l = k /\ !x:A. MEM x l ==> x IN s})
                   (0..n))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
   ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FINITE_LENGTH_EQ];
   REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIONS; EXISTS_IN_IMAGE] THEN
   REPEAT STRIP_TAC THEN REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM; LE_0] THEN
   ASM_MESON_TAC[]]);;

let LENGTH_NOREPETITION = prove
 (`!n l s. s HAS_SIZE n /\ (!x:A. MEM x l ==> x IN s) /\ NOREPETITION l
           ==> LENGTH l <= n`,
  INDUCT_TAC THENL
  [REWRITE_TAC[HAS_SIZE_CLAUSES; LE; LENGTH_EQ_NIL] THEN
   MESON_TAC[NIL_NOT_MEM; NOT_IN_EMPTY];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; LE_0] THEN
  POP_ASSUM (K ALL_TAC) THEN GEN_TAC THEN
  REWRITE_TAC[MEM; NOREPETITION_CLAUSES; LE_SUC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s DELETE h:A` THEN
  ASM_SIMP_TAC[DELETE_HAS_SIZE; IN_DELETE] THEN ASM_MESON_TAC[]);;

let FINITE_NOREPETITION = prove
 (`!s n. FINITE s ==> FINITE {l | NOREPETITION l /\ !x:A. MEM x l ==> x IN s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{l | LENGTH l <= CARD s /\ !x:A. MEM x l ==> x IN s}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_LENGTH_LE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[LENGTH_NOREPETITION; FINITE_HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of the types of characters and lists.                         *)
(* ------------------------------------------------------------------------- *)

let FINITE_CHAR = prove
 (`FINITE (:char)`,
  C SUBGOAL_THEN SUBST1_TAC
    `(:char) =
     IMAGE (\(b0,b1,b2,b3,b4,b5,b6,b7). ASCII b0 b1 b2 b3 b4 b5 b6 b7)
           UNIV` THENL
  [REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN X_GEN_TAC `c:char` THEN
   DESTRUCT_TAC "@b0 b1 b2 b3 b4 b5 b6 b7. c"
     (SPEC `c:char` (cases "char")) THEN
   EXISTS_TAC
     `b0:bool,b1:bool,b2:bool,b3:bool,b4:bool,b5:bool,b6:bool,b7:bool` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[GSYM CROSS_UNIV; FINITE_CROSS_EQ; FINITE_BOOL]);;

let HAS_SIZE_CHAR = prove
 (`(:char) HAS_SIZE 256`,
  C SUBGOAL_THEN SUBST1_TAC
    `(:char) =
     IMAGE (\(b0,b1,b2,b3,b4,b5,b6,b7). ASCII b0 b1 b2 b3 b4 b5 b6 b7)
           UNIV` THENL
  [REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN X_GEN_TAC `c:char` THEN
   DESTRUCT_TAC "@b0 b1 b2 b3 b4 b5 b6 b7. c"
     (SPEC `c:char` (cases "char")) THEN
   EXISTS_TAC
     `b0:bool,b1:bool,b2:bool,b3:bool,b4:bool,b5:bool,b6:bool,b7:bool` THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_UNIV; FORALL_PAIR_THM; injectivity "char"; PAIR_EQ];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM (NUM_REDUCE_CONV `2*2*2*2*2*2*2*2`); GSYM CROSS_UNIV] THEN
  MESON_TAC[HAS_SIZE_CROSS; HAS_SIZE_BOOL]);;

let FINITE_CHAR = prove
 (`FINITE (:char)`,
  MESON_TAC[HAS_SIZE_CHAR; HAS_SIZE]);;

let COUNTABLE_CHAR = prove
 (`COUNTABLE (:char)`,
  SIMP_TAC[FINITE_CHAR; FINITE_IMP_COUNTABLE]);;

let COUNTABLE_STRING = prove
 (`COUNTABLE (:string)`,
  SIMP_TAC[COUNTABLE_CHAR; COUNTABLE_LIST]);;
