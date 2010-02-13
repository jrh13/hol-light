(*---------------------------------------------------------------------------*)
(*
   File:         mk_ensures.sml

   Description:  This file defines ENSURES and the theorems and corrollaries
                 described in [CM88].

   Author:       (c) Copyright 1989-2008 by Flemming Andersen
   Date:         June 29, 1989
   Last Update:  December 30, 2007
*)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(* The definition of ENSURES is based on the definition:

      p ensures q in Pr = <p unless q in Pr /\ (?s in Pr: {p /\ ~q} s {q})>

  where p and q are state dependent first order logic predicates and s
  in the program Pr are conditionally enabled statements transforming
  a state into a new state. ENSURES then requires safety and the
  existance of at least one state transition statement s which makes q
  valid.
*)

let EXIST_TRANSITION_term =
   `(!p q. EXIST_TRANSITION (p:'a->bool) q []         <=> F) /\
    (!p q. EXIST_TRANSITION p q (CONS (st:'a->'a) Pr) <=>
	  ((!s. (p s /\ ~q s) ==> q (st s)) \/ (EXIST_TRANSITION p q Pr)))`;;
let EXIST_TRANSITION = new_recursive_definition
    list_RECURSION EXIST_TRANSITION_term;;
parse_as_infix ( "EXIST_TRANSITION", (TL_FIX, "right") );;

let ENSURES = new_infix_definition
  ("ENSURES", "<=>",
   `!(p:'a->bool) q (Pr:('a->'a)list).
       ENSURES p q Pr = (((p UNLESS q) Pr) /\ ((p EXIST_TRANSITION q) Pr))`,
   TL_FIX);;

let ENSURES_STMT = new_infix_definition
  ("ENSURES_STMT", "<=>",
   `!(p:'a->bool) q (st:'a->'a).
        ENSURES_STMT p q st = (\s. p s /\ ~(q s) ==> q (st s))`,
   TL_FIX);;


(*-------------------------------------------------------------------------*)
(*
  Lemmas
*)
(*-------------------------------------------------------------------------*)

let ENSURES_lemma0 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q r st.
          ((!s. p s /\ ~q s ==> q (st s)) /\ (!s. q s ==> r s)) ==>
           (!s. p s /\ ~r s ==> r (st s))`)),
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (CONTRAPOS (SPEC_ALL (ASSUME (`!s:'a. q s ==> r s`)))) THEN
    ASSUME_TAC (SPEC (`(st:'a->'a) s`) (ASSUME (`!s:'a. q s ==> r s`))) THEN
    RES_TAC THEN
    RES_TAC);;

set_goal([],
   (`!(p:'a->bool) p' q q' h.
     (!s. (p  UNLESS_STMT q)  h s)     ==>
     (!s. (p' UNLESS_STMT q') h s)     ==>
     (!s. p' s /\ ~q' s ==> q' (h s))  ==>
     (!s. (p /\* p') s /\ ~((p /\* q' \/* p' /\* q) \/* q /\* q') s) ==>
     (((p /\* q' \/* p' /\* q) \/* q /\* q') (h s))`)
);;
 
let ENSURES_lemma1 = TAC_PROOF
  (([],
    `!(p:'a->bool) p' q q' h.
      (!s. (p  UNLESS_STMT q)  h s)     ==>
      (!s. (p' UNLESS_STMT q') h s)     ==>
      (!s. p' s /\ ~q' s ==> q' (h s))  ==>
      (!s. (p /\* p') s /\ ~((p /\* q' \/* p' /\* q) \/* q /\* q') s
               ==> ((p /\* q' \/* p' /\* q) \/* q /\* q') (h s))`),
    REWRITE_TAC [UNLESS_STMT; AND_def; OR_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    MESON_TAC []);;

let ENSURES_lemma2 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q r st.
       (!s. p s /\ ~q s ==> q (st s)) ==>
         (!s. (p s \/ r s) /\ ~(q s \/ r s) ==> q (st s) \/ r (st s))`)),
     REWRITE_TAC [(GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC)));
                  (SYM (SPEC_ALL DISJ_ASSOC));NOT_CLAUSES;DE_MORGAN_THM] THEN
     REPEAT STRIP_TAC THEN RES_TAC THEN
     ASM_REWRITE_TAC []);;

let ENSURES_lemma3 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q r Pr. (p ENSURES (q \/* r)) Pr ==>
              (((p /\* (Not q)) \/* (p /\* q)) ENSURES (q \/* r)) Pr`)),
   REWRITE_TAC [AND_COMPL_OR_lemma]);;

let ENSURES_lemma4 = TAC_PROOF
  (([],
    `!(p:'a->bool) q r (st:'a->'a).
         (!s. p s /\ ~q s ==> q (st s)) ==>
            (!s. (p \/* r) s /\ ~(q \/* r) s ==> (q \/* r) (st s))`),
    REPEAT GEN_TAC THEN
    REWRITE_TAC [OR_def] THEN
    MESON_TAC []);;

(*---------------------------------------------------------------------------*)
(*
  Theorems about EXIST_TRANSITION
*)
(*---------------------------------------------------------------------------*)

(*
  EXIST_TRANSITION Consequence Weakening Theorem:

               p EXIST_TRANSITION q in Pr; q ==> r
              -------------------------------------
                   p EXIST_TRANSITION r in Pr
*)

let EXIST_TRANSITION_thm1 = prove_thm
 ("EXIST_TRANSITION_thm1",
  (`!(p:'a->bool) q r Pr.
     ((p EXIST_TRANSITION q) Pr /\ (!s. (q s) ==> (r s))) ==>
       ((p EXIST_TRANSITION r) Pr)`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [REWRITE_RULE
    [ASSUME `!s:'a. p s /\ ~q s ==> q (h s)`; ASSUME `!s:'a. q s ==> r s`]
     (SPECL [`p:'a->bool`;`q:'a->bool`;`r:'a->bool`;`h:'a->'a`] ENSURES_lemma0)]);;

(*
  Impossibility EXIST_TRANSITION Theorem:

               p EXIST_TRANSITION false in Pr
              --------------------------------
                          ~p 
*)
let EXIST_TRANSITION_thm2 = prove_thm
  ("EXIST_TRANSITION_thm2",
   (`!(p:'a->bool) Pr.
     ((p EXIST_TRANSITION False) Pr) ==> !s. (Not p) s`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION; NOT_def1] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THENL
   [
     UNDISCH_TAC (`!s:'a. ((p:'a->bool) s) /\ ~(False s)
                          ==> (False ((h:'a->'a) s))`) THEN
     REWRITE_TAC [FALSE_def] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV)
    ;
     UNDISCH_TAC (`!s:'a. (Not (p:'a->bool)) s`) THEN
     REWRITE_TAC [NOT_def1] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV)
   ]);;

(*
  Always EXIST_TRANSITION Theorem:

               false EXIST_TRANSITION p in Pr
*)
let EXIST_TRANSITION_thm3 = prove_thm
  ("EXIST_TRANSITION_thm3",
   (`!(p:'a->bool) st Pr. (False EXIST_TRANSITION p) (CONS st Pr)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION; FALSE_def]);;

let EXIST_TRANSITION_thm4 = prove_thm
  ("EXIST_TRANSITION_thm4",
   (`!(p:'a->bool) q r Pr.
         (p EXIST_TRANSITION q) Pr ==>
            ((p \/* r) EXIST_TRANSITION (q \/* r)) Pr`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [REWRITE_RULE 
      [ASSUME `!s:'a. (p:'a->bool) s /\ ~q s ==> q (h s)`] 
        (SPECL [`p:'a->bool`;`q:'a->bool`;`r:'a->bool`;`h:'a->'a`]
            ENSURES_lemma4)]);;

let APPEND_lemma01 = TAC_PROOF
  (([],
   `!(l:('a)list). (APPEND l []) = l`),
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND]);;

let EXIST_TRANSITION_thm5 = prove_thm
  ("EXIST_TRANSITION_thm5",
   (`!(p:'a->bool) q st Pr.
       (!s. p s /\ ~q s ==> q (st s))
            ==> (p EXIST_TRANSITION q) (CONS st Pr)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let APPEND_lemma02 = TAC_PROOF
  (([],
   `!st (l:('a)list).  (APPEND [st] l) = (CONS st l)`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND]);;   

let APPEND_lemma03 = TAC_PROOF
  (([],
   `!st (l1:('a)list) l2. 
       (APPEND (APPEND l1 [st]) l2) = (APPEND l1 (CONS st l2))`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND]);;

let APPEND_lemma04 = TAC_PROOF
  (([],
   `!st (l1:('a)list) l2. 
       (APPEND (CONS st l1) l2) = (CONS st (APPEND l1 l2))`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND]);;

let EXIST_TRANSITION_thm6 = prove_thm
  ("EXIST_TRANSITION_thm6",
   (`!(p:'a->bool) q st Pr1 Pr2.
       (!s. p s /\ ~q s ==> q (st s))
            ==> (p EXIST_TRANSITION q) (APPEND Pr1 (CONS st Pr2))`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION;APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []);;

let EXIST_TRANSITION_thm7 = prove_thm
  ("EXIST_TRANSITION_thm7",
   (`!(p:'a->bool) q FPr GPr.
     (p EXIST_TRANSITION q) FPr
              ==> (p EXIST_TRANSITION q) (APPEND FPr GPr)`),
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [EXIST_TRANSITION;APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND]);;

let EXIST_TRANSITION_thm8 = prove_thm
  ("EXIST_TRANSITION_thm8",
   (`!(p:'a->bool) q FPr GPr.
     (p EXIST_TRANSITION q) FPr
              ==> (p EXIST_TRANSITION q) (APPEND GPr FPr)`),
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND] THENL
   [
     REWRITE_TAC [UNDISCH_ALL (SPECL
      [`p:'a->bool`;`q:'a->bool`;`h:'a->'a`;`t':('a->'a)list`;`t:('a->'a)list`]
        EXIST_TRANSITION_thm6)]
    ;
     REWRITE_TAC [REWRITE_RULE [APPEND_lemma03] (SPECL
       [`(APPEND (t':('a->'a)list) [h])`]
        (ASSUME `!GPr:('a->'a)list. (p EXIST_TRANSITION q) (APPEND GPr t)`))]
   ]);;

let EXIST_TRANSITION_thm9 = prove_thm
  ("EXIST_TRANSITION_thm9",
   (`!(p:'a->bool) q st FPr GPr.
     (p EXIST_TRANSITION q) (APPEND FPr GPr)
              ==> (p EXIST_TRANSITION q) (APPEND FPr (CONS st GPr))`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND]);;

let EXIST_TRANSITION_thm10 = prove_thm
  ("EXIST_TRANSITION_thm10",
   (`!(p:'a->bool) q st Pr.
       (p EXIST_TRANSITION q) Pr ==> (p EXIST_TRANSITION q) (CONS st Pr)`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;APPEND;EXIST_TRANSITION] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let EXIST_TRANSITION_thm11 = prove_thm
  ("EXIST_TRANSITION_thm11",
   (`!(p:'a->bool) q st Pr.
      (p EXIST_TRANSITION q) (APPEND [st] Pr) =
      (p EXIST_TRANSITION q) (APPEND  Pr [st])`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;APPEND;EXIST_TRANSITION] THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;APPEND;EXIST_TRANSITION] THENL
   [
     REWRITE_TAC [REWRITE_RULE [APPEND_lemma02] (SYM (ASSUME
          `(((p:'a->bool) EXIST_TRANSITION q) (APPEND [st] t)) <=>
           ((p EXIST_TRANSITION q) (APPEND t [st]))`))] THEN
     ASM_REWRITE_TAC [EXIST_TRANSITION]
    ;
     REWRITE_TAC [REWRITE_RULE [APPEND_lemma02] (SYM (ASSUME
          `(((p:'a->bool) EXIST_TRANSITION q) (APPEND [st] t)) <=>
           ((p EXIST_TRANSITION q) (APPEND t [st]))`))] THEN
     ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
       [`p:'a->bool`;`q:'a->bool`;`st:'a->'a`;`t:('a->'a)list`]
        EXIST_TRANSITION_thm10)]
    ;
     STRIP_ASSUME_TAC (REWRITE_RULE [APPEND_lemma02;EXIST_TRANSITION]
       (ASSUME `((p:'a->bool) EXIST_TRANSITION q) (APPEND [st] t)`)) THEN
     ASM_REWRITE_TAC []
   ]);;

let EXIST_TRANSITION_thm12a = prove_thm
  ("EXIST_TRANSITION_thm12a",
   (`!(p:'a->bool) q FPr GPr.
      (p EXIST_TRANSITION q) (APPEND FPr GPr) ==>
      (p EXIST_TRANSITION q) (APPEND GPr FPr)`),
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;APPEND;EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND] THENL
    [
      REWRITE_TAC [UNDISCH_ALL (SPECL [`p:'a->bool`;`q:'a->bool`;`h:'a->'a`;
              `GPr:('a->'a)list`;`t:('a->'a)list`] EXIST_TRANSITION_thm6)]
     ;
      REWRITE_TAC [UNDISCH_ALL (SPECL [`p:'a->bool`;`q:'a->bool`;`h:'a->'a`;
              `GPr:('a->'a)list`;`t:('a->'a)list`] EXIST_TRANSITION_thm9)]
    ]);;

let EXIST_TRANSITION_thm12b = prove_thm
  ("EXIST_TRANSITION_thm12b",
   (`!(p:'a->bool) q FPr GPr.
      (p EXIST_TRANSITION q) (APPEND GPr FPr) ==>
      (p EXIST_TRANSITION q) (APPEND FPr GPr)`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;APPEND;EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [APPEND_lemma01;EXIST_TRANSITION;APPEND] THENL
    [
      REWRITE_TAC [UNDISCH_ALL (SPECL [`p:'a->bool`;`q:'a->bool`;`h:'a->'a`;
              `FPr:('a->'a)list`;`t:('a->'a)list`] EXIST_TRANSITION_thm6)]
     ;
      REWRITE_TAC [UNDISCH_ALL (SPECL [`p:'a->bool`;`q:'a->bool`;`h:'a->'a`;
              `FPr:('a->'a)list`;`t:('a->'a)list`] EXIST_TRANSITION_thm9)]
    ]);;

let EXIST_TRANSITION_thm12 = prove_thm
  ("EXIST_TRANSITION_thm12",
   (`!(p:'a->bool) q FPr GPr.
      (p EXIST_TRANSITION q) (APPEND GPr FPr) =
      (p EXIST_TRANSITION q) (APPEND FPr GPr)`),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   REWRITE_TAC [UNDISCH_ALL (SPEC_ALL EXIST_TRANSITION_thm12a);
                UNDISCH_ALL (SPEC_ALL EXIST_TRANSITION_thm12b)]);;

(*---------------------------------------------------------------------------*)
(*
  Theorems about ENSURES
*)
(*---------------------------------------------------------------------------*)

(*
  Reflexivity Theorem:

               p ensures p in Pr

  The theorem is only valid for non-empty programs
*)
let ENSURES_thm0 = prove_thm
  ("ENSURES_thm0",
   (`!(p:'a->bool) q. (p ENSURES q) [] = F`),
     REWRITE_TAC [ENSURES] THEN
     STRIP_TAC THEN
     REWRITE_TAC [UNLESS;EXIST_TRANSITION]);;

let ENSURES_thm1 = prove_thm
  ("ENSURES_thm1",
   (`!(p:'a->bool) st Pr. (p ENSURES p) (CONS st Pr)`),
     REWRITE_TAC [ENSURES] THEN
     STRIP_TAC THEN
     REWRITE_TAC [UNLESS;EXIST_TRANSITION] THEN
     REWRITE_TAC [UNLESS_thm1;UNLESS_STMT] THEN
     REWRITE_TAC [BETA_CONV (`(\s:'a. (p s /\ ~p s) ==> p (st s))s`)] THEN
     REWRITE_TAC[NOT_AND;IMP_CLAUSES]);;

(*
  Consequence Weakening Theorem:

               p ensures q in Pr; q ==> r
              ----------------------------
                   p ensures r in Pr
*)

let ENSURES_thm2 = prove_thm
  ("ENSURES_thm2",
   (`!(p:'a->bool) q r Pr.
         ((p ENSURES q) Pr /\ (!s:'a. (q s) ==> (r s)))
        ==>
	 ((p ENSURES r) Pr)`),
   REWRITE_TAC [ENSURES] THEN
   REPEAT STRIP_TAC THENL
     [
      ASSUME_TAC (UNDISCH_ALL (SPEC (`!s:'a. q s ==> r s`)
        (SPEC (`((p:'a->bool) UNLESS q) Pr`) AND_INTRO_THM))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm3))
     ;
      ASSUME_TAC (UNDISCH_ALL (SPEC (`!s:'a. q s ==> r s`)
        (SPEC (`((p:'a->bool) EXIST_TRANSITION q) Pr`) AND_INTRO_THM))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL EXIST_TRANSITION_thm1))
     ]);;

(*
  Impossibility Theorem:

               p ensures false in Pr
              ----------------------
                       ~p 
*)

let ENSURES_thm3 = prove_thm
  ("ENSURES_thm3",
   (`!(p:'a->bool) Pr. ((p ENSURES False) Pr) ==> !s. (Not p)s`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [ENSURES; UNLESS; EXIST_TRANSITION] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THENL
   [
     UNDISCH_TAC `!s:'a. (p:'a->bool) s /\ ~(False s) ==> False ((h:'a->'a) s)` THEN
     REWRITE_TAC [FALSE_def; NOT_def1] THEN
     CONV_TAC (DEPTH_CONV BETA_CONV)
    ;
     IMP_RES_TAC EXIST_TRANSITION_thm2
   ]);;

(*
  Conjunction Theorem:

                   p unless q in Pr; p' ensures q' in Pr
              -----------------------------------------------
               p/\p' ensures (p/\q')\/(p'/\q)\/(q/\q') in Pr
*)
let ENSURES_thm4 = prove_thm
  ("ENSURES_thm4",
   (`!(p:'a->bool) q p' q' Pr.
    (p UNLESS q) Pr /\ (p' ENSURES q') Pr ==>
      ((p /\* p') ENSURES (((p /\* q') \/*  (p' /\* q)) \/*  (q /\* q')))
        Pr`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THENL
   [
    REWRITE_TAC
      [REWRITE_RULE [ASSUME `!s:'a. ((p:'a->bool) UNLESS_STMT q)   (h:'a->'a) s`;
                     ASSUME `!s:'a. ((p':'a->bool) UNLESS_STMT q') (h:'a->'a) s`]
        (SPECL [`p:'a->bool`;`q:'a->bool`;`p':'a->bool`;`q':'a->bool`;`h:'a->'a`]
                UNLESS_STMT_thm3)]
   ;
    REWRITE_TAC
      [REWRITE_RULE [ASSUME `((p:'a->bool)  UNLESS q)  (t:('a->'a)list)`;
                     ASSUME `((p':'a->bool) UNLESS q') (t:('a->'a)list)`]
      (SPECL [`p:'a->bool`;`q:'a->bool`;`p':'a->bool`;`q':'a->bool`;`t:('a->'a)list`]
                UNLESS_thm4)]
   ;
    REWRITE_TAC [REWRITE_RULE
         [ASSUME `!s:'a. ((p:'a->bool) UNLESS_STMT q) (h:'a->'a) s`;
          ASSUME `!s:'a. ((p':'a->bool) UNLESS_STMT q') (h:'a->'a) s`;
          ASSUME `!s:'a. (p':'a->bool) s /\ ~(q' s) ==> q' ((h:'a->'a) s)`]
       (SPEC_ALL ENSURES_lemma1)]
   ;
    REWRITE_TAC
      [REWRITE_RULE [ASSUME `!s:'a. ((p:'a->bool) UNLESS_STMT q)   (h:'a->'a) s`;
                     ASSUME `!s:'a. ((p':'a->bool) UNLESS_STMT q') (h:'a->'a) s`]
        (SPECL [`p:'a->bool`;`q:'a->bool`;`p':'a->bool`;`q':'a->bool`;`h:'a->'a`]
                UNLESS_STMT_thm3)]
   ;
    UNDISCH_TAC `((p:'a->bool) UNLESS q) t /\ (p' ENSURES q') (t:('a->'a)list)
       ==> (p /\* p' ENSURES (p /\* q' \/* p' /\* q) \/* q /\* q') t` THEN
    ASM_REWRITE_TAC [ENSURES] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC []
   ;
    UNDISCH_TAC `((p:'a->bool) UNLESS q) t /\ (p' ENSURES q') (t:('a->'a)list)
       ==> (p /\* p' ENSURES (p /\* q' \/* p' /\* q) \/* q /\* q') t` THEN
    ASM_REWRITE_TAC [ENSURES] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC []
  ]);;

(*
  Conjunction Theorem:

                   p ensures q in Pr
              -------------------------
               p\/r ensures q\/r in Pr
*)

let ENSURES_thm5 = prove_thm
  ("ENSURES_thm5",
   (`!(p:'a->bool) q r Pr.
      ((p ENSURES q) Pr) ==> (((p \/* r) ENSURES (q \/* r)) Pr)`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [ENSURES;UNLESS;EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THENL
   [
     IMP_RES_TAC UNLESS_STMT_thm6 THEN
     ASM_REWRITE_TAC []
    ;
     IMP_RES_TAC UNLESS_cor23 THEN
     ASM_REWRITE_TAC []
    ;
     REWRITE_TAC [REWRITE_RULE 
      [ASSUME `!s:'a. (p:'a->bool) s /\ ~q s ==> q (h s)`] 
        (SPECL [`p:'a->bool`;`q:'a->bool`;`r:'a->bool`;`h:'a->'a`]
            ENSURES_lemma4)]
    ;
     IMP_RES_TAC UNLESS_STMT_thm6 THEN
     ASM_REWRITE_TAC []
    ;
     IMP_RES_TAC UNLESS_cor23 THEN
     ASM_REWRITE_TAC []
    ;
     IMP_RES_TAC EXIST_TRANSITION_thm4 THEN
     ASM_REWRITE_TAC []
   ]);;

(*
 -----------------------------------------------------------------------------
  Corollaries about ENSURES
 -----------------------------------------------------------------------------
*)

(*
  Implies Corollary:

                   p => q
              -------------------
               p ensures q in Pr

  This corollary is only valid for non-empty programs.
*)

let ENSURES_cor1 = prove_thm
  ("ENSURES_cor1",
   (`!(p:'a->bool) q st Pr.
    (!s. p s ==> q s) ==> (p ENSURES q) (CONS st Pr)`),
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPEC_ALL ENSURES_thm1) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((p:'a->bool) ENSURES p)(CONS st Pr)`);(`!s:'a. p s ==> q s`)]
      AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`p:'a->bool`);(`p:'a->bool`);(`q:'a->bool`);
      (`CONS (st:'a->'a) Pr`)]
      ENSURES_thm2)));;

let ENSURES_cor2 = prove_thm
  ("ENSURES_cor2",
   (`!(p:'a->bool) q Pr. (p ENSURES q) Pr ==> (p UNLESS q) Pr`),
   REWRITE_TAC [ENSURES] THEN
   REPEAT STRIP_TAC);;

let ENSURES_cor3 = prove_thm
  ("ENSURES_cor3",
   (`!(p:'a->bool) q r Pr.
        ((p \/*  q) ENSURES r)Pr ==> (p ENSURES (q \/*  r))Pr`),
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((p:'a->bool) \/*  q)`);(`r:'a->bool`);
      (`Pr:('a->'a)list`)] ENSURES_cor2)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`p:'a->bool`);(`q:'a->bool`);(`r:'a->bool`);
      (`Pr:('a->'a)list`)] UNLESS_cor4)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((p:'a->bool) UNLESS (q \/*  r))Pr`);
      (`(((p:'a->bool) \/*  q) ENSURES r)Pr`)]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`p:'a->bool`);(`((q:'a->bool) \/*  r)`);
      (`((p:'a->bool) \/*  q)`);(`r:'a->bool`);
      (`Pr:('a->'a)list`)] ENSURES_thm4)) THEN
   UNDISCH_TAC (`(((p:'a->bool) /\* (p \/*  q)) ENSURES
                (((p /\* r) \/*  ((p \/*  q) /\* (q \/*  r))) \/* 
                 ((q \/*  r) /\* r))) Pr`) THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;AND_ASSOC_lemma] THEN
   PURE_ONCE_REWRITE_TAC [SPECL
         [(`((q:'a->bool) \/*  r)`);
	  (`r:'a->bool`)] AND_COMM_lemma] THEN
   ONCE_REWRITE_TAC [AND_OR_EQ_AND_COMM_OR_lemma] THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL [(`p:'a->bool`);(`q:'a->bool`);(`r:'a->bool`)]
                           IMPLY_WEAK_lemma5) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    [(`((p:'a->bool) ENSURES
      ((p /\* r) \/*  (((p \/*  q) /\* (q \/*  r)) \/*  r)))Pr`);
     (`!s:'a. ((p /\* r) \/*  (((p \/*  q) /\* (q \/*  r)) \/* r))s ==>
	 (q \/*  r)s`)]
     AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
    [(`p:'a->bool`);
     (`(((p:'a->bool) /\* r) \/* (((p \/*  q) /\* (q \/*  r)) \/* r))`);
     (`((q:'a->bool) \/*  r)`);(`Pr:('a->'a)list`)]
     ENSURES_thm2)));;

let ENSURES_cor4 = prove_thm
  ("ENSURES_cor4",
   (`!(p:'a->bool) q r Pr. (p ENSURES (q \/*  r)) Pr ==>
              ((p /\* (Not  q)) ENSURES (q \/*  r)) Pr`),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL ENSURES_lemma3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((p:'a->bool) /\* (Not  q))`);(`((p:'a->bool) /\* q)`);
      (`((q:'a->bool) \/* r)`);(`Pr:('a->'a)list`)] ENSURES_cor3)) THEN
   UNDISCH_TAC
     (`(((p:'a->bool) /\* (Not  q)) ENSURES
	  ((p /\* q) \/* (q \/* r)))Pr`) THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL OR_ASSOC_lemma))] THEN
   REWRITE_TAC [P_AND_Q_OR_Q_lemma]);;

(*
  Consequence Weakening Corollary:

                  p ensures q in Pr
              -------------------------
               p ensures (q \/ r) in Pr
*)

let ENSURES_cor5 = prove_thm
 ("ENSURES_cor5",
   (`!(p:'a->bool) q r Pr.
         (p ENSURES q) Pr ==> (p ENSURES (q \/*  r)) Pr`),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL [(`q:'a->bool`);(`r:'a->bool`)]
	       IMPLY_WEAK_lemma_b) THEN
   ASSUME_TAC (SPECL
     [(`p:'a->bool`);(`q:'a->bool`);(`(q:'a->bool) \/* r`)]
	       ENSURES_thm2) THEN
   RES_TAC);;

(*
  Always Corollary:

                  false ensures p in Pr
*)

let ENSURES_cor6 = prove_thm
  ("ENSURES_cor6",
   (`!(p:'a->bool) st Pr. (False ENSURES p) (CONS st Pr)`),
   REWRITE_TAC [ENSURES;UNLESS_cor7;EXIST_TRANSITION_thm3]);;

let ENSURES_cor7 = prove_thm
  ("ENSURES_cor7",
   (`!(p:'a->bool) q r Pr.
        (p ENSURES q) Pr /\ (r STABLE Pr)
       ==>
	((p /\* r) ENSURES (q /\*
 r))Pr`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC (ONCE_REWRITE_RULE [AND_COMM_lemma]
      (REWRITE_RULE [AND_False_lemma;OR_False_lemma] 
        (ONCE_REWRITE_RULE [OR_AND_COMM_lemma] 
          (REWRITE_RULE [AND_False_lemma;OR_False_lemma] (SPECL
            [(`r:'a->bool`);(`False:'a->bool`);
	     (`p:'a->bool`);(`q:'a->bool`);
             (`Pr:('a->'a)list`)] ENSURES_thm4))))));;
