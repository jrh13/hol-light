(* ========================================================================= *)
(*  More definitions and theorems and tactics about lists.                   *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi, 2005-2007                          *)
(* ========================================================================= *)

parse_as_infix ("::",(23,"right"));;
override_interface("::",`CONS`);;

(* ------------------------------------------------------------------------- *)
(*  Some handy tactics.                                                      *)
(* ------------------------------------------------------------------------- *)

let ASSERT_TAC tm = SUBGOAL_THEN tm ASSUME_TAC;;

let SUFFICE_TAC thl tm =
  SUBGOAL_THEN tm (fun th -> MESON_TAC (th :: thl));;

let LIST_CASES_TAC =
  let th = prove (`!P. P [] /\ (!h t. P (h :: t)) ==> !l. P l`,
                  GEN_TAC THEN STRIP_TAC THEN
                  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC [])
  in
  MATCH_MP_TAC th THEN CONJ_TAC THENL
  [ALL_TAC; GEN_TAC THEN GEN_TAC];;

(* ------------------------------------------------------------------------- *)
(*  Occasionally useful stuff.                                               *)
(* ------------------------------------------------------------------------- *)

let NULL_EQ_NIL = prove
  (`!l. NULL l <=> l = []`,
   LIST_CASES_TAC THEN REWRITE_TAC [NULL; NOT_CONS_NIL]);;

let NULL_LENGTH = prove
  (`!l. NULL l <=> LENGTH l = 0`,
   LIST_CASES_TAC THEN REWRITE_TAC [NULL; LENGTH; NOT_SUC]);;

let LENGTH_FILTER_LE = prove
  (`!f l:A list. LENGTH (FILTER f l) <= LENGTH l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [FILTER; LENGTH; LE_0] THEN
   COND_CASES_TAC THEN
   ASM_SIMP_TAC [LENGTH; LE_SUC; ARITH_RULE `n<=m ==> n<= SUC m`]);;

(* ------------------------------------------------------------------------- *)
(*  Well-founded induction on lists.                                         *)
(* ------------------------------------------------------------------------- *)

let list_WF = prove
  (`!P. (!l. (!l'. LENGTH l' < LENGTH l ==> P l') ==> P l)
        ==> (!l:A list. P l)`,
   MP_TAC (ISPEC `LENGTH:A list->num` WF_MEASURE) THEN
   REWRITE_TAC [WF_IND; MEASURE]);;

(* ------------------------------------------------------------------------- *)
(*  Delete one element from a list.                                          *)
(* ------------------------------------------------------------------------- *)

let DELETE1 = define
  `(!x. DELETE1 x [] = []) /\
   (!x h t. DELETE1 x (h :: t) = if x = h then t
                                          else h :: DELETE1 x t)`;;

let DELETE1_ID = prove
  (`!x l. ~MEM x l ==> DELETE1 x l = l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [MEM; DELETE1] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC [NOT_CONS_NIL; CONS_11]);;

let DELETE1_APPEND = prove
  (`!x l1 l2. DELETE1 x (APPEND l1 l2) =
              if MEM x l1 then APPEND (DELETE1 x l1) l2
                          else APPEND l1 (DELETE1 x l2)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [APPEND; DELETE1; MEM] THEN
   GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM; APPEND] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let FILTER_DELETE1 = prove
  (`!P x l. FILTER P (DELETE1 x l) =
            if P x then DELETE1 x (FILTER P l) else FILTER P l`,
   GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
   REPEAT (REWRITE_TAC [DELETE1; FILTER] THEN COND_CASES_TAC) THEN
   ASM_MESON_TAC []);;

let LENGTH_DELETE1 = prove
  (`!l x:A. LENGTH (DELETE1 x l) =
            if MEM x l then PRE (LENGTH l) else LENGTH l`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [MEM; LENGTH; DELETE1] THEN GEN_TAC THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[PRE; LENGTH] THEN COND_CASES_TAC THEN
   REWRITE_TAC [ARITH_RULE `SUC (PRE n)=n <=> ~(n=0)`; LENGTH_EQ_NIL] THEN
   ASM_MESON_TAC [MEM]);;

let MEM_DELETE1_MEM_IMP = prove
  (`!h t x. MEM x (DELETE1 h t) ==> MEM x t`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN GEN_TAC THEN
   REWRITE_TAC [MEM; DELETE1] THEN COND_CASES_TAC THEN
   REWRITE_TAC [MEM] THEN STRIP_TAC THEN ASM_SIMP_TAC []);;

let NOT_MEM_DELETE1 = prove
  (`!t h x. ~MEM x t ==> ~MEM x (DELETE1 h t)`,
   LIST_INDUCT_TAC THEN GEN_TAC THEN GEN_TAC THEN
   REWRITE_TAC [MEM; DELETE1] THEN
   COND_CASES_TAC THEN REWRITE_TAC [MEM; DE_MORGAN_THM] THEN
   STRIP_TAC THEN ASM_SIMP_TAC []);;

let MEM_DELETE1 = prove
  (`!l x y:A. MEM x l /\ ~(x = y) ==> MEM x (DELETE1 y l)`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [MEM; DELETE1] THEN
   GEN_TAC THEN GEN_TAC THEN COND_CASES_TAC THENL
   [EXPAND_TAC "h" THEN MESON_TAC [];
    REWRITE_TAC [MEM] THEN ASM_MESON_TAC []]);;

let ALL_DELETE1_ALL_IMP = prove
  (`!P x l. P x /\ ALL P (DELETE1 x l) ==> ALL P l`,
   GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC [ALL; DELETE1] THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC [ALL]);;

(* ------------------------------------------------------------------------- *)
(*  Counting occurrences of a given element in a list.                       *)
(* ------------------------------------------------------------------------- *)

let COUNT = define
  `(!x. COUNT x [] = 0) /\
   (!x h t. COUNT x (CONS h t) = if x=h then SUC (COUNT x t) else COUNT x t)`;;

let COUNT_LENGTH_FILTER = prove
  (`!x l. COUNT x l = LENGTH (FILTER ((=) x) l)`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [COUNT; FILTER; LENGTH] THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC [LENGTH]);;

let COUNT_FILTER = prove
  (`!P x l. COUNT x (FILTER P l) =
            if P x then COUNT x l else 0`,
   GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
   REPEAT (ASM_REWRITE_TAC [COUNT; FILTER] THEN COND_CASES_TAC) THEN
   ASM_MESON_TAC []);;

let COUNT_APPEND = prove
  (`!x l1 l2. COUNT x (APPEND l1 l2) = COUNT x l1 + COUNT x l2`,
    REWRITE_TAC [COUNT_LENGTH_FILTER; LENGTH_APPEND; FILTER_APPEND]);;

let COUNT_LE_LENGTH = prove
  (`!x l. COUNT x l <= LENGTH l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [COUNT; LENGTH; LE_REFL] THEN COND_CASES_TAC THEN
   ASM_SIMP_TAC [LE_SUC; ARITH_RULE `n<=m ==> n <= SUC m`]);;

let COUNT_ZERO = prove
  (`!x l. COUNT x l = 0 <=> ~MEM x l`,
   GEN_TAC THEN REWRITE_TAC [COUNT_LENGTH_FILTER; LENGTH_EQ_NIL] THEN
   LIST_INDUCT_TAC THEN REWRITE_TAC [FILTER; MEM] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC [NOT_CONS_NIL]);;

let MEM_COUNT = prove
  (`!x l. MEM x l <=> ~(COUNT x l = 0)`,
   MESON_TAC [COUNT_ZERO]);;

let COUNT_DELETE1 = prove
  (`!y x l. COUNT y (DELETE1 (x:A) l) =
            if y=x /\ MEM x l then PRE (COUNT y l) else COUNT y l`,
   REWRITE_TAC [COUNT_LENGTH_FILTER; FILTER_DELETE1] THEN REPEAT GEN_TAC THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM_FILTER; LENGTH_DELETE1]);;

(* ------------------------------------------------------------------------- *)
(*  Duplicates in a list.                                                    *)
(* ------------------------------------------------------------------------- *)

let LIST_UNIQ_RULES, LIST_UNIQ_INDUCT, LIST_UNIQ_CASES =
  new_inductive_definition
  `LIST_UNIQ [] /\
   (!x xs. LIST_UNIQ xs /\ ~MEM x xs ==> LIST_UNIQ (x :: xs))`;;

let LIST_UNIQ = prove
  (`LIST_UNIQ [] /\
   (!x. LIST_UNIQ [x]) /\
   (!x xs. LIST_UNIQ (x :: xs) <=> ~MEM x xs /\ LIST_UNIQ xs)`,
   SIMP_TAC [LIST_UNIQ_RULES; MEM] THEN
   REPEAT GEN_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC [ISPEC `h :: t` LIST_UNIQ_CASES] THEN
    REWRITE_TAC [CONS_11; NOT_CONS_NIL] THEN
    DISCH_THEN (CHOOSE_THEN CHOOSE_TAC) THEN ASM_REWRITE_TAC [];
    SIMP_TAC [LIST_UNIQ_RULES]]);;

let LIST_UNIQ_EQ_PAIRWISE_DISTINCT = prove
 (`LIST_UNIQ = PAIRWISE (\x y. ~(x = y))`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MATCH_MP_TAC list_INDUCT THEN ASM_REWRITE_TAC[LIST_UNIQ; PAIRWISE] THEN
  SIMP_TAC[GSYM ALL_MEM] THEN MESON_TAC[]);;

(* !!! forse e' meglio con IMP? *)
(* Magari LIST_UNIQ_COUNT + COUNT_LIST_UNIQ *)
let LIST_UNIQ_COUNT = prove
  (`!l. LIST_UNIQ l <=> (!x:A. COUNT x l = if MEM x l then 1 else 0)`,
   let IFF_EXPAND = MESON [] `(p <=> q) <=> (p ==> q) /\ (q ==> p)` in
   REWRITE_TAC [IFF_EXPAND; FORALL_AND_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIST_UNIQ_INDUCT THEN REWRITE_TAC [COUNT; MEM] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ONE];
    LIST_INDUCT_TAC THEN REWRITE_TAC [LIST_UNIQ; COUNT; MEM] THEN
    DISCH_TAC THEN FIRST_ASSUM (MP_TAC o SPEC `h:A`) THEN
    SIMP_TAC [MEM_COUNT; ONE; SUC_INJ] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
    FIRST_ASSUM (MP_TAC o SPEC `x:A`) THEN
    REWRITE_TAC [MEM_COUNT] THEN ARITH_TAC]);;

let LIST_UNIQ_DELETE1 = prove
  (`!l x. LIST_UNIQ l ==> LIST_UNIQ (DELETE1 x l)`,
   LIST_INDUCT_TAC THEN GEN_TAC THEN
   REWRITE_TAC [LIST_UNIQ; DELETE1] THEN STRIP_TAC THEN
   COND_CASES_TAC THEN ASM_SIMP_TAC [LIST_UNIQ; NOT_MEM_DELETE1]);;

let DELETE1_LIST_UNIQ = prove
  (`!l x:A. ~MEM x (DELETE1 x l) /\ LIST_UNIQ (DELETE1 x l)
            ==> LIST_UNIQ l`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [LIST_UNIQ; DELETE1; MEM] THEN
   GEN_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC [MEM; LIST_UNIQ] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC [MEM_DELETE1];
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC []]);;

let LIST_UNIQ_APPEND = prove
 (`!l m. LIST_UNIQ (APPEND l m) <=>
         LIST_UNIQ l /\ LIST_UNIQ m /\
         !x. ~(MEM x l /\ MEM x m)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LIST_UNIQ; MEM; MEM_APPEND] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(*  Lists and finite sets.                                                   *)
(* ------------------------------------------------------------------------- *)

let CARD_LENGTH = prove
  (`!l:A list. CARD (set_of_list l) <= LENGTH l`,
   LIST_INDUCT_TAC THEN
   SIMP_TAC [set_of_list; CARD_CLAUSES; LENGTH;
             FINITE_SET_OF_LIST; ARITH] THEN
   COND_CASES_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `LENGTH (t:A list)`
    THEN ASM_REWRITE_TAC [] THEN ARITH_TAC;
    ASM_REWRITE_TAC [LE_SUC]]);;

let LIST_UNIQ_CARD_LENGTH = prove
  (`!l:A list. LIST_UNIQ l <=> CARD (set_of_list l) = LENGTH l`,
   LIST_INDUCT_TAC THEN SIMP_TAC [LIST_UNIQ; set_of_list; FINITE_SET_OF_LIST;
                                  LENGTH; CARD_CLAUSES; IN_SET_OF_LIST] THEN
   FIRST_X_ASSUM SUBST1_TAC THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[SUC_INJ] THEN MP_TAC (SPEC `t:A list` CARD_LENGTH) THEN
   ARITH_TAC);;

let LIST_UNIQ_LIST_OF_SET = prove
 (`!s. FINITE s ==> LIST_UNIQ(list_of_set s)`,
  SIMP_TAC[LIST_UNIQ_CARD_LENGTH; SET_OF_LIST_OF_SET; LENGTH_LIST_OF_SET]);;
