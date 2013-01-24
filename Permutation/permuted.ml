(* ========================================================================= *)
(*  Permuted lists.                                                          *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi, 2005-2007                          *)
(* ========================================================================= *)

needs "Permutation/morelist.ml";;

parse_as_infix("PERMUTED",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(*  Permuted lists.                                                          *)
(* ------------------------------------------------------------------------- *)

let PERMUTED_RULES, PERMUTED_INDUCT, PERMUTED_CASES =
  new_inductive_definition
  `[] PERMUTED [] /\
   (!h t1 t2. t1 PERMUTED t2 ==> h :: t1 PERMUTED h :: t2) /\
   (!l1 l2 l3. l1 PERMUTED l2 /\ l2 PERMUTED l3 ==> l1 PERMUTED l3) /\
   (!x y t. x :: y :: t PERMUTED y :: x :: t)`;;

let PERMUTED_INDUCT_STRONG =
  derive_strong_induction(PERMUTED_RULES,PERMUTED_INDUCT);;

let PERMUTED_RFL = prove
  (`!l. l PERMUTED l`,
   LIST_INDUCT_TAC THEN ASM_SIMP_TAC [PERMUTED_RULES]);;

let PERMUTED_SYM = prove
  (`!(xs:A list) l2. xs PERMUTED l2 <=> l2 PERMUTED xs`,
   SUFFICE_TAC []
     `!(xs:A list) l2. xs PERMUTED l2 ==> l2 PERMUTED xs` THEN
   MATCH_MP_TAC PERMUTED_INDUCT THEN ASM_MESON_TAC [PERMUTED_RULES]);;

let PERMUTED_TRS = prove
  (`!xs l2 l3. xs PERMUTED l2 /\ l2 PERMUTED l3 ==> xs PERMUTED l3`,
   MESON_TAC [PERMUTED_RULES]);;

let PERMUTED_TRS_TAC tm : tactic =
  MATCH_MP_TAC PERMUTED_TRS THEN EXISTS_TAC tm THEN CONJ_TAC ;;

let PERMUTED_TAIL_IMP = prove
  (`!h t1 t2. t1 PERMUTED t2 ==> h :: t1 PERMUTED h :: t2`,
   SIMP_TAC [PERMUTED_RULES]);;

let PERMUTED_MAP = prove
  (`!f l1 l2. l1 PERMUTED l2 ==>  MAP f l1 PERMUTED MAP f l2`,
   GEN_TAC THEN MATCH_MP_TAC PERMUTED_INDUCT THEN
   REWRITE_TAC [MAP; PERMUTED_RULES]);;

let PERMUTED_LENGTH = prove
  (`!l1 l2. l1 PERMUTED l2 ==> LENGTH l1 = LENGTH l2`,
   MATCH_MP_TAC PERMUTED_INDUCT THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [LENGTH]);;

let PERMUTED_SWAP_HEAD = prove
  (`!a b l. a :: b :: l PERMUTED b :: a :: l`,
   REWRITE_TAC [PERMUTED_RULES]);;

let PERMUTED_MEM = prove
  (`!(a:A) l1 l2. l1 PERMUTED l2 ==> (MEM a l1 <=> MEM a l2)`,
   GEN_TAC THEN MATCH_MP_TAC PERMUTED_INDUCT THEN
   REWRITE_TAC [MEM] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let PERMUTED_ALL = prove
  (`!P xs ys. xs PERMUTED ys ==> (ALL P xs <=> ALL P ys)`,
   GEN_TAC THEN MATCH_MP_TAC PERMUTED_INDUCT THEN
   REWRITE_TAC [ALL] THEN REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC[] THEN MESON_TAC[]);;

let PERMUTED_NIL_EQ_NIL = prove
  (`(!l:A list. [] PERMUTED l <=> l = []) /\
    (!l:A list. l PERMUTED [] <=> l = [])`,
   SUFFICE_TAC [PERMUTED_SYM] `!l:A list. [] PERMUTED l <=> l = []` THEN
   LIST_CASES_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL; PERMUTED_RFL] THEN
   MESON_TAC [PERMUTED_LENGTH; LENGTH; NOT_SUC]);;

let PERMUTED_SINGLETON = prove
  (`(!(x:A) l. [x] PERMUTED l <=> l = [x]) /\
    (!(x:A) l. l PERMUTED [x] <=> l = [x])`,
   SUFFICE_TAC [PERMUTED_LENGTH; PERMUTED_RFL]
     `!l1 l2. l1 PERMUTED l2 ==> LENGTH l1 = LENGTH l2 /\
                                 (!x. l1 = [x:A] <=> l2 = [x])` THEN
   MATCH_MP_TAC PERMUTED_INDUCT THEN
   SIMP_TAC [PERMUTED_NIL_EQ_NIL; LENGTH; NOT_CONS_NIL; CONS_11;
             SUC_INJ; GSYM LENGTH_EQ_NIL]);;

let PERMUTED_CONS_DELETE1 = prove
  (`!(a:A) l. MEM a l ==> l PERMUTED a :: DELETE1 a l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [MEM; DELETE1] THEN
   COND_CASES_TAC THEN
   ASM_MESON_TAC [PERMUTED_RFL; PERMUTED_TAIL_IMP; PERMUTED_SWAP_HEAD;
                  PERMUTED_TRS]);;

let PERMUTED_COUNT = prove
  (`!l1 l2. l1 PERMUTED l2 <=> (!x:A. COUNT x l1 = COUNT x l2)`,
   let IFF_EXPAND = MESON [] `(p <=> q) <=> (p ==> q) /\ (q ==> p)` in
   REWRITE_TAC [IFF_EXPAND; FORALL_AND_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PERMUTED_INDUCT THEN REWRITE_TAC [COUNT] THEN
    ASM_MESON_TAC []; ALL_TAC] THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC [COUNT; PERMUTED_NIL_EQ_NIL] THENL
   [LIST_CASES_TAC THEN REWRITE_TAC [COUNT; NOT_CONS_NIL] THEN
    MESON_TAC [NOT_SUC]; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN ASSERT_TAC `MEM (h:A) l2` THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `h:A`) THEN REWRITE_TAC[MEM_COUNT]
    THEN ARITH_TAC; ALL_TAC] THEN
   ASSERT_TAC `(h:A) :: t PERMUTED h :: DELETE1 h l2` THENL
   [MATCH_MP_TAC PERMUTED_TAIL_IMP THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [COUNT_DELETE1] THEN GEN_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN ARITH_TAC;
    ASM_MESON_TAC [PERMUTED_CONS_DELETE1; PERMUTED_SYM; PERMUTED_TRS]]);;

let PERMUTED_TAIL = prove
  (`!x t1 t2. x :: t1 PERMUTED x :: t2 <=> t1 PERMUTED t2`,
   REPEAT GEN_TAC THEN REWRITE_TAC [PERMUTED_COUNT; COUNT] THEN
   MESON_TAC [SUC_INJ]);;

let PERMUTED_DELETE1_L = prove
  (`!(h:A) t l. h :: t PERMUTED l <=> MEM h l /\ t PERMUTED DELETE1 h l`,
   MESON_TAC [PERMUTED_MEM; MEM; PERMUTED_TAIL; PERMUTED_CONS_DELETE1;
              PERMUTED_SYM; PERMUTED_TRS]);;

let PERMUTED_DELETE1_R = prove
  (`!(h:A) t l. l PERMUTED h :: t <=> MEM h l /\ DELETE1 h l PERMUTED t`,
   MESON_TAC [PERMUTED_SYM; PERMUTED_DELETE1_L]);;

let PERMUTED_LIST_UNIQ = prove
  (`!xs ys. xs PERMUTED ys ==> (LIST_UNIQ xs <=> LIST_UNIQ ys)`,
   SIMP_TAC [PERMUTED_COUNT; LIST_UNIQ_COUNT; MEM_COUNT]);;

let PERMUTED_IMP_PAIRWISE = prove
 (`!(P:A->A->bool) l l'.
        (!x y. P x y ==> P y x) /\ l PERMUTED l' /\ PAIRWISE P l
        ==> PAIRWISE P l'`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PERMUTED_INDUCT_STRONG THEN
  ASM_SIMP_TAC[PAIRWISE; ALL] THEN MESON_TAC[PERMUTED_ALL]);;

let PERMUTED_PAIRWISE = prove
 (`!(P:A->A->bool) l l.
        (!x y. P x y ==> P y x) /\ l PERMUTED l'
        ==> (PAIRWISE P l <=> PAIRWISE P l')`,
  MESON_TAC[PERMUTED_IMP_PAIRWISE; PERMUTED_SYM]);;

let PERMUTED_APPEND_SWAP = prove
 (`!l1 l2. (APPEND l1 l2) PERMUTED (APPEND l2 l1)`,
  REWRITE_TAC[PERMUTED_COUNT; COUNT_APPEND] THEN ARITH_TAC);;
