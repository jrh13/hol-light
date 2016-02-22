(* ========================================================================= *)
(*  Permuted lists and finite permutations.                                  *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi, 2005-2007                          *)
(* ========================================================================= *)

needs "Permutation/permuted.ml";;

(* ------------------------------------------------------------------------- *)
(*  Permutation that reverse a list.                                         *)
(* ------------------------------------------------------------------------- *)

let REVPERM = define
  `REVPERM 0 = [] /\
   REVPERM (SUC n) = n :: REVPERM n`;;

let MEM_REVPERM = prove
  (`!n m. MEM m (REVPERM n) <=> m < n`,
   INDUCT_TAC THEN ASM_REWRITE_TAC [REVPERM; MEM; LT]);;

let LIST_UNIQ_REVPERM = prove
  (`!n. LIST_UNIQ (REVPERM n)`,
   INDUCT_TAC THEN ASM_REWRITE_TAC [REVPERM; LIST_UNIQ; MEM_REVPERM]
   THEN ARITH_TAC);;

let DELETE1_REVPERM = prove
  (`!n. DELETE1 n (REVPERM (SUC n)) = REVPERM n`,
   INDUCT_TAC THEN ASM_REWRITE_TAC [REVPERM; DELETE1; MEM]);;

let COUNT_REVPERM = prove
  (`!n i. COUNT i (REVPERM n) = if i < n then 1 else 0`,
   INDUCT_TAC THEN ASM_REWRITE_TAC [REVPERM; COUNT] THEN ARITH_TAC);;

let SET_OF_LIST_REVPERM = prove
  (`!n. set_of_list (REVPERM n) = {m | m < n}`,
   INDUCT_TAC THEN
   ASM_REWRITE_TAC [REVPERM; set_of_list; LT; EMPTY_GSPEC; EXTENSION;
                    IN_INSERT; IN_ELIM_THM; NOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(*  Permutations.                                                            *)
(* ------------------------------------------------------------------------- *)

let PERMUTATION = new_definition
  `!l. PERMUTATION l <=> REVPERM (LENGTH l) PERMUTED l`;;

let PERMUTATION_NIL = prove
  (`PERMUTATION []`,
   REWRITE_TAC [PERMUTATION; LENGTH; REVPERM; PERMUTED_RULES]);;

let PERMUTATION_LIST_UNIQ = prove
  (`!l. PERMUTATION l ==> LIST_UNIQ l`,
   MESON_TAC [PERMUTATION; PERMUTED_LIST_UNIQ; LIST_UNIQ_REVPERM]);;

let PERMUTATION_MEM = prove
  (`!l. PERMUTATION l ==> (!i. MEM i l <=> i < LENGTH l)`,
   REWRITE_TAC [PERMUTATION] THEN
   MESON_TAC [MEM_REVPERM; PERMUTED_MEM]);;

let PERMUTATION_COUNT = prove
  (`!l. PERMUTATION l <=> (!x. COUNT x l = if x < LENGTH l then 1 else 0)`,
   REWRITE_TAC [PERMUTATION; PERMUTED_COUNT; COUNT_REVPERM] THEN
   MESON_TAC[]);;

let LIST_UNIQ_PERMUTED_SET_OF_LIST = prove
  (`!l1 l2. LIST_UNIQ l1 /\ LIST_UNIQ l2
           ==> (l1 PERMUTED l2 <=> set_of_list l1 = set_of_list l2)`,
   REWRITE_TAC [LIST_UNIQ_COUNT] THEN REPEAT STRIP_TAC THEN
   REWRITE_TAC [EXTENSION; IN_SET_OF_LIST; PERMUTED_COUNT; MEM_COUNT] THEN
   ASM_REWRITE_TAC [] THEN MESON_TAC []);;

let PERMUTED_LENGTH_MEM = prove
 (`!l l':A list.
        LIST_UNIQ l /\ LENGTH l = LENGTH l' /\ (!x. MEM x l <=> MEM x l')
        ==> l PERMUTED l'`,
  REWRITE_TAC[GSYM IN_SET_OF_LIST; GSYM EXTENSION] THEN
  ASM_MESON_TAC[LIST_UNIQ_CARD_LENGTH; LIST_UNIQ_PERMUTED_SET_OF_LIST]);;

let PERMUTATION_SET_OF_LIST = prove
  (`!l. PERMUTATION l <=> set_of_list l = {n | n < LENGTH l}`,
   GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC [GSYM SET_OF_LIST_REVPERM] THEN
    ASM_MESON_TAC [LIST_UNIQ_PERMUTED_SET_OF_LIST; PERMUTATION;
                   PERMUTED_LIST_UNIQ; LIST_UNIQ_REVPERM];
    REWRITE_TAC [PERMUTATION] THEN ASSERT_TAC `LIST_UNIQ (l:num list)` THENL
    [REWRITE_TAC [LIST_UNIQ_CARD_LENGTH] THEN FIRST_X_ASSUM SUBST1_TAC THEN
     REWRITE_TAC [CARD_NUMSEG_LT];
     ASM_SIMP_TAC [SET_OF_LIST_REVPERM; LIST_UNIQ_REVPERM;
                   LIST_UNIQ_PERMUTED_SET_OF_LIST]]]);;

let MEM_PERMUTATION = prove
  (`!l. (!n. n < LENGTH l ==> MEM n l) ==> PERMUTATION l`,
   REPEAT STRIP_TAC THEN REWRITE_TAC [PERMUTATION_SET_OF_LIST] THEN
   MATCH_MP_TAC (GSYM CARD_SUBSET_LE) THEN
   REWRITE_TAC [FINITE_SET_OF_LIST; CARD_NUMSEG_LT; CARD_LENGTH] THEN
   ASM_SIMP_TAC [SUBSET; IN_ELIM_THM; IN_SET_OF_LIST]);;

let LIST_UNIQ_MEM_PERMUTATION = prove
  (`!l. LIST_UNIQ l /\ (!n. MEM n l ==> n < LENGTH l) ==> PERMUTATION l`,
   REWRITE_TAC [LIST_UNIQ_CARD_LENGTH; PERMUTATION_SET_OF_LIST] THEN
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_SUBSET_LE THEN
   ASM_REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM; IN_SET_OF_LIST;
                    CARD_NUMSEG_LT; LE_REFL]);;

let PERMUTATION_UNIQ_LT = prove
  (`!l. PERMUTATION l <=> LIST_UNIQ l /\ (!n. MEM n l ==> n < LENGTH l)`,
   MESON_TAC [PERMUTATION_LIST_UNIQ; PERMUTATION_MEM;
              LIST_UNIQ_MEM_PERMUTATION]);;
