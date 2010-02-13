(* ========================================================================= *)
(*  Quick sort algorithm.                                                    *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi, 2005-2007                          *)
(* ========================================================================= *)

needs "Permutation/permuted.ml";;

(* ------------------------------------------------------------------------- *)
(* Ordered lists.                                                            *)
(* ------------------------------------------------------------------------- *)

let ORDERED_RULES, ORDERED_INDUCT, ORDERED_CASES = new_inductive_definition
  `(!le. ORDERED le []) /\
   (!le h t. ORDERED le t /\ ALL (le h) t ==> ORDERED le (CONS h t))`;;

let ORDERED_CONS = prove
  (`!le (h:A) t. ORDERED le (h :: t) <=> (ORDERED le t /\ ALL (le h) t)`,
   SUBGOAL_THEN
    `!le (h:A) t. ORDERED le (h :: t) ==> (ORDERED le t /\ ALL (le h) t)`
   (fun th -> MESON_TAC [th; ORDERED_RULES]) THEN
   REPEAT GEN_TAC THEN
   DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [ORDERED_CASES]) THEN
   REWRITE_TAC [NOT_CONS_NIL; CONS_11] THEN MESON_TAC []);;

let ORDERED_APPEND = prove
 (`!l1 l2:A list.
      ORDERED le (APPEND l1 l2) <=>
      ORDERED le l1 /\ ORDERED le l2 /\ ALL (\x. ALL (le x) l2) l1`,
  SUBGOAL_THEN
    `(!l1 l2:A list.
        ORDERED le (APPEND l1 l2)
        ==> ORDERED le l1 /\ ORDERED le l2 /\ ALL (\x. ALL (le x) l2) l1) /\
     (!l1 l2. ORDERED le l1 /\ ORDERED le l2 /\ ALL (\x. ALL (le x) l2) l1
              ==> ORDERED le (APPEND l1 l2))`
   (fun th -> MESON_TAC [th]) THEN
   CONJ_TAC THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND; ALL; ORDERED_RULES; ORDERED_CONS] THEN
   ASM_SIMP_TAC [ORDERED_CONS; ALL_APPEND] THEN ASM_MESON_TAC [ALL_APPEND]);;

(* ------------------------------------------------------------------------- *)
(*  Quick Sort.                                                              *)
(* ------------------------------------------------------------------------- *)

let QSORT =
  let PROVE_RECURSIVE_FUNCTION_EXISTS_TAC : tactic = fun g ->
    let th = pure_prove_recursive_function_exists (snd g) in
    MATCH_MP_TAC (DISCH_ALL th) g in
  new_specification ["QSORT"] (prove
  (`?f. (!le. f le [] = [] : A list) /\
        (!le h t. f le (CONS h t) =
                  APPEND (f le (FILTER (\x. ~le h x) t))
                  (CONS h (f le (FILTER (\x. le h x) t))))`,
   REWRITE_TAC [GSYM SKOLEM_THM; AND_FORALL_THM] THEN GEN_TAC THEN
   PROVE_RECURSIVE_FUNCTION_EXISTS_TAC THEN
   EXISTS_TAC `MEASURE (LENGTH:A list -> num)` THEN
   REWRITE_TAC [WF_MEASURE; MEASURE; LENGTH; FILTER] THEN
   REWRITE_TAC [LT_SUC_LE; LENGTH_FILTER_LE]));;

let COUNT_QSORT = prove
  (`!le x l. COUNT x (QSORT le l) = COUNT x l`,
   GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC list_WF THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC [QSORT; COUNT; LENGTH; LT_SUC_LE; COUNT_APPEND] THEN
   DISCH_TAC THEN ASM_SIMP_TAC [COUNT; LENGTH_FILTER_LE] THEN
   REWRITE_TAC [COUNT_FILTER] THEN
   REPEAT (ASM_REWRITE_TAC [ADD; ADD_SUC; ADD_0] THEN COND_CASES_TAC) THEN
   ASM_MESON_TAC[ADD_SUC]);;

let QSORT_PERMUTED = prove
  (`!le (l:A list). QSORT le l PERMUTED l`,
   REWRITE_TAC [PERMUTED_COUNT; COUNT_QSORT]);;

let ALL_QSORT = prove
  (`!P le l. ALL P (QSORT le l) <=> ALL P l`,
   MESON_TAC [QSORT_PERMUTED; PERMUTED_ALL]);;

let LENGTH_QSORT = prove
  (`!le l. LENGTH (QSORT le l) =  LENGTH l`,
   MESON_TAC [QSORT_PERMUTED; PERMUTED_LENGTH]);;

let MEM_QSORT = prove
  (`!le l x. MEM x (QSORT le l) <=> MEM x l`,
   MESON_TAC [QSORT_PERMUTED; PERMUTED_MEM]);;

let ORDERED_QSORT = prove
 (`!le (l:A list).
     (!x y. le x y \/ le y x) /\ (!x y z. le x y \/ le y z ==> le x z)
     ==> ORDERED le (QSORT le l)`,
   REWRITE_TAC [GSYM RIGHT_IMP_FORALL_THM] THEN GEN_TAC THEN STRIP_TAC THEN
   MATCH_MP_TAC list_WF THEN LIST_CASES_TAC THEN
   REWRITE_TAC [QSORT; LENGTH; ORDERED_RULES; LT_SUC_LE] THEN DISCH_TAC THEN
   REWRITE_TAC [ORDERED_APPEND; ORDERED_CONS; ALL; ALL_QSORT; ALL_T] THEN
   ASM_SIMP_TAC [LENGTH_FILTER_LE] THEN REWRITE_TAC [GSYM ALL_MEM] THEN
   ASM_MESON_TAC[]);;

(* Example:
REWRITE_CONV [QSORT; ARITH_LE; ARITH_LT; FILTER; APPEND]
  `QSORT (<=) [12;3;5;1;23;2;1]`;;
*)
