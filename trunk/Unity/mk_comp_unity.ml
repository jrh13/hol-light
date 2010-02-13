(*---------------------------------------------------------------------------*)
(*
   File:         mk_comp_unity.ml

   Description:  This file proves the unity compositionality theorems and
                 corrollaries valid.

   Author:       (c) Copyright 1989-2008 by Flemming Andersen
   Date:         December 1, 1989
   Last Update:  December 30, 2007
*)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*
  Theorems
*)
(*---------------------------------------------------------------------------*)

(*
   Prove:
   !p q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) ==> (p UNLESS q) FPr /\ (p UNLESS q) GPr
*)
let COMP_UNLESS_thm1_lemma_1 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) ==> (p UNLESS q) FPr /\ (p UNLESS q) GPr`)),
   REPEAT GEN_TAC THEN
   SPEC_TAC ((`GPr:('a->'a)list`),(`GPr:('a->'a)list`)) THEN
   SPEC_TAC ((`FPr:('a->'a)list`),(`FPr:('a->'a)list`)) THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS;APPEND]
     ;
      REWRITE_TAC [APPEND] THEN
      REWRITE_TAC [UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         RES_TAC
        ;
         RES_TAC]]);;

(*
   Prove:
     !p q FPr GPr.
     (p UNLESS q) FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)
*)
let COMP_UNLESS_thm1_lemma_2 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q FPr GPr.
     (p UNLESS q) FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)`)),
   REPEAT GEN_TAC THEN
   SPEC_TAC ((`GPr:('a->'a)list`),(`GPr:('a->'a)list`)) THEN
   SPEC_TAC ((`FPr:('a->'a)list`),(`FPr:('a->'a)list`)) THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [UNLESS;APPEND]
     ;
      REWRITE_TAC [APPEND] THEN
      REWRITE_TAC [UNLESS] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         RES_TAC
        ]]);;


(*
   Prove:
     !p q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) FPr /\ (p UNLESS q) GPr
*)
let COMP_UNLESS_thm1 = prove_thm
  ("COMP_UNLESS_thm1",
   (`!(p:'a->bool) q FPr GPr.
      (p UNLESS q) (APPEND FPr GPr) <=> (p UNLESS q) FPr /\ (p UNLESS q) GPr`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                       (SPEC_ALL COMP_UNLESS_thm1_lemma_1)
                       (SPEC_ALL COMP_UNLESS_thm1_lemma_2)));;


(*
   Prove:
   !p q FPr GPr.
    (p ENSURES q) (APPEND FPr GPr) ==> (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr
*)
let COMP_ENSURES_thm1_lemma_1 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q FPr GPr.
    (p ENSURES q) (APPEND FPr GPr) ==> (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr`)),
   REPEAT GEN_TAC THEN
   SPEC_TAC ((`GPr:('a->'a)list`),(`GPr:('a->'a)list`)) THEN
   SPEC_TAC ((`FPr:('a->'a)list`),(`FPr:('a->'a)list`)) THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND]
     ;
      GEN_TAC THEN
      REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND] THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THENL
        [
         DISJ1_TAC THEN
         ASM_REWRITE_TAC [] THEN
         ASM_REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL COMP_UNLESS_thm1))]
        ;
         ASSUME_TAC (UNDISCH_ALL (SPECL
           [(`((p:'a->bool) UNLESS q)(APPEND t GPr)`);
            (`((p:'a->bool) EXIST_TRANSITION q)(APPEND t GPr)`)]
            AND_INTRO_THM)) THEN
         UNDISCH_TAC (`((p:'a->bool) UNLESS  q)(APPEND t GPr) /\
                       (p EXIST_TRANSITION q)(APPEND t GPr)`) THEN
         REWRITE_TAC [SPECL [(`q:'a->bool`); (`p:'a->bool`); 
			     (`APPEND (t:('a->'a)list) GPr`)]
                             (GEN_ALL (SYM (SPEC_ALL ENSURES)))] THEN
         DISCH_TAC THEN
         RES_TAC THENL
           [
            UNDISCH_TAC (`((p:'a->bool) ENSURES q) t`) THEN
            REWRITE_TAC [ENSURES] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ;
            UNDISCH_TAC (`((p:'a->bool) ENSURES q) GPr`) THEN
            REWRITE_TAC [ENSURES] THEN
            STRIP_TAC THEN
            ASM_REWRITE_TAC []
           ]]]);;

(*
   Prove:
    !p q FPr GPr.
    (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
    (p ENSURES q) GPr /\ (p UNLESS q) FPr ==> (p ENSURES q) (APPEND FPr GPr)
*)
let COMP_ENSURES_thm1_lemma_2 = TAC_PROOF
  (([],
    `!(p:'a->bool) q FPr GPr.
    ((p ENSURES q) FPr /\ (p UNLESS q) GPr \/
     (p ENSURES q) GPr /\ (p UNLESS q) FPr)
           ==> (p ENSURES q) (APPEND FPr GPr)`),
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [ENSURES;EXIST_TRANSITION;UNLESS;APPEND] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [COMP_UNLESS_thm1;ENSURES;EXIST_TRANSITION;
                    UNLESS;APPEND] THEN
   REWRITE_TAC [UNDISCH_ALL (ONCE_REWRITE_RULE [EXIST_TRANSITION_thm12]
        (SPEC_ALL EXIST_TRANSITION_thm8))] THENL
   [
     REWRITE_TAC
       [ONCE_REWRITE_RULE [EXIST_TRANSITION_thm12] (UNDISCH_ALL (SPECL
          [`p:'a->bool`;`q:'a->bool`;`t:('a->'a)list`;`GPr:('a->'a)list`]
             EXIST_TRANSITION_thm8))]
   ;
     REWRITE_TAC
       [UNDISCH_ALL
          (SPECL [`p:'a->bool`;`q:'a->bool`;`GPr:('a->'a)list`;`t:('a->'a)list`]
             EXIST_TRANSITION_thm8)]
   ]);;

(*
   Prove:
    !p q FPr GPr.
      (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) FPr /\ (p UNLESS q) GPr \/
                                       (p ENSURES q) GPr /\ (p UNLESS q) FPr
*)
let COMP_ENSURES_thm1 = prove_thm
  ("COMP_ENSURES_thm1",
   (`!(p:'a->bool) q FPr GPr.
      (p ENSURES q) (APPEND FPr GPr) <=>
         ((p ENSURES q) FPr /\ (p UNLESS q) GPr \/
          (p ENSURES q) GPr /\ (p UNLESS q) FPr)`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                       (SPEC_ALL COMP_ENSURES_thm1_lemma_1)
                       (SPEC_ALL COMP_ENSURES_thm1_lemma_2)));;

(*
   Prove:
    |- !p q FPr GPr.
         (p ENSURES q)FPr /\ (p UNLESS q)GPr ==> (p ENSURES q)(APPEND FPr GPr)
*)
let COMP_ENSURES_cor0 = prove_thm
  ("COMP_ENSURES_cor0",
   (`!(p:'a->bool) q FPr GPr.
      (p ENSURES q) FPr /\ (p UNLESS q) GPr
         ==> (p ENSURES q) (APPEND FPr GPr)`),
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME (`((p:'a->bool) ENSURES q)FPr`);ASSUME (`((p:'a->bool) UNLESS q)GPr`)]
    (SPEC_ALL COMP_ENSURES_thm1)));;


(*
   Prove:
    |- !p q FPr GPr.
         (p ENSURES q)GPr /\ (p UNLESS q)FPr ==> (p ENSURES q)(APPEND FPr GPr)
*)
let COMP_ENSURES_cor1 = prove_thm
  ("COMP_ENSURES_cor1",
   (`!(p:'a->bool) q FPr GPr.
      (p ENSURES q) GPr /\ (p UNLESS q) FPr
         ==> (p ENSURES q) (APPEND FPr GPr)`),
   REPEAT STRIP_TAC THEN
   ACCEPT_TAC (REWRITE_RULE
    [ASSUME (`((p:'a->bool) ENSURES q)GPr`);ASSUME (`((p:'a->bool) UNLESS q)FPr`)]
    (SPEC_ALL COMP_ENSURES_thm1)));;


(*
   Prove:
     !p q FPr GPr.
      (p INVARIANT q) (APPEND FPr GPr) =
          (p INVARIANT q) FPr /\ (p INVARIANT q) GPr
*)
let COMP_UNITY_cor0 = prove_thm
  ("COMP_UNITY_cor0",
   (`!(p0:'a->bool) p FPr GPr.
       (p INVARIANT (p0, APPEND FPr GPr)) =
          (p INVARIANT (p0,FPr) /\ p INVARIANT (p0,GPr))`),
   REWRITE_TAC [INVARIANT;STABLE;COMP_UNLESS_thm1] THEN
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THEN
   RES_TAC THEN ASM_REWRITE_TAC []);;


(*
   Prove:
        !p FPr GPr.
           p STABLE (APPEND FPr GPr) = p STABLE FPr /\ p STABLE GPr
*)
let COMP_UNITY_cor1 = prove_thm
  ("COMP_UNITY_cor1",
   (`!(p:'a->bool) FPr GPr.
           (p STABLE (APPEND FPr GPr)) = (p STABLE FPr /\ p STABLE GPr)`),
   REWRITE_TAC [STABLE;COMP_UNLESS_thm1]);;


(*
   Prove:
        !p q FPr GPr.
         (p UNLESS q) FPr /\ p STABLE GPr ==>(p UNLESS q) (APPEND FPr GPr)
*)
let COMP_UNITY_cor2 = prove_thm
  ("COMP_UNITY_cor2",
   (`!(p:'a->bool) q FPr GPr.
         (p UNLESS q) FPr /\ p STABLE GPr ==>(p UNLESS q) (APPEND FPr GPr)`),
   REWRITE_TAC [STABLE;COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC THENL
     [
      ASM_REWRITE_TAC []
     ;
      UNDISCH_TAC (`((p:'a->bool) UNLESS False)GPr`) THEN
      SPEC_TAC ((`GPr:('a->'a)list`),(`GPr:('a->'a)list`)) THEN
      LIST_INDUCT_TAC THENL
        [
         REWRITE_TAC [UNLESS]
        ;
         REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
         CONV_TAC (DEPTH_CONV BETA_CONV) THEN
         REPEAT STRIP_TAC THENL
           [
            RES_TAC THEN
            UNDISCH_TAC
               (`~(False:'a->bool) s ==> (p:'a->bool)(h s) \/ False(h s)`) THEN
            REWRITE_TAC [FALSE_def;NOT_CLAUSES;OR_INTRO_THM1]
           ;
            RES_TAC]]]);;


(*
   Prove:
     !p0 p FPr GPr.
       p INVARIANT (p0; FPr) /\ p STABLE GPr
            ==> p INVARIANT (p0; (APPEND FPr GPr))
*)
let COMP_UNITY_cor3 = prove_thm
  ("COMP_UNITY_cor3",
   (`!(p0:'a->bool) p FPr GPr.
       p INVARIANT (p0, FPr) /\ p STABLE GPr ==>
                    p INVARIANT (p0, (APPEND FPr GPr))`),
   REWRITE_TAC [INVARIANT;STABLE;COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC THENL
     [
      RES_TAC
     ;
      ASM_REWRITE_TAC []
     ;
      ASM_REWRITE_TAC []]);;


(*
   Prove:
       !p q FPr GPr.
        (p ENSURES q) FPr /\ p STABLE GPr ==> (p ENSURES q) (APPEND FPr GPr)
*)
let COMP_UNITY_cor4 = prove_thm
  ("COMP_UNITY_cor4",
   (`!(p:'a->bool) q FPr GPr.
        (p ENSURES q) FPr /\ p STABLE GPr ==> (p ENSURES q) (APPEND FPr GPr)`),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(`p:'a->bool`);(`q:'a->bool`);(`FPr:('a->'a)list`)] ENSURES_cor2)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(`((p:'a->bool) UNLESS q)FPr`);(`(p:'a->bool) STABLE GPr`)]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(`p:'a->bool`);(`q:'a->bool`);(`FPr:('a->'a)list`);(`GPr:('a->'a)list`)]
         COMP_UNITY_cor2)) THEN
   REWRITE_TAC [ENSURES] THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC (`((p:'a->bool) ENSURES q)FPr`) THEN
   REWRITE_TAC [ENSURES] THEN
   STRIP_TAC THEN
   UNDISCH_TAC (`((p:'a->bool) EXIST_TRANSITION q)FPr`) THEN
   SPEC_TAC ((`FPr:('a->'a)list`),(`FPr:('a->'a)list`)) THEN
   LIST_INDUCT_TAC THENL
     [
      REWRITE_TAC [EXIST_TRANSITION]
     ;
      REWRITE_TAC [APPEND;EXIST_TRANSITION] THEN
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         RES_TAC THEN
         ASM_REWRITE_TAC []]]);;

(*
   Prove:
   !p q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) GPr
*)
let COMP_UNITY_cor5 = prove_thm
  ("COMP_UNITY_cor5",
   (`!(p:'a->bool) q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) GPr`),
   REWRITE_TAC [COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC);;

(*
   Prove:
    !p q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) FPr
*)
let COMP_UNITY_cor6 = prove_thm
  ("COMP_UNITY_cor6",
   (`!(p:'a->bool) q FPr GPr. (p UNLESS q)(APPEND FPr GPr) ==> (p UNLESS q) FPr`),
   REWRITE_TAC [COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC);;

(*
   Prove:
    !p q st FPr. (p UNLESS q)(CONS st FPr) ==> (p UNLESS q) FPr
*)
let COMP_UNITY_cor7 = prove_thm
  ("COMP_UNITY_cor7",
   (`!(p:'a->bool) q st FPr. (p UNLESS q)(CONS st FPr) ==> (p UNLESS q) FPr`),
   REWRITE_TAC [UNLESS] THEN
   REPEAT STRIP_TAC);;

(*
   Prove:
        !p FPr GPr.
           (p ENSURES (NotX  p)) FPr ==> (p ENSURES (NotX  p)) (APPEND FPr GPr)
*)
let COMP_UNITY_cor8 = prove_thm
  ("COMP_UNITY_cor8",
   (`!(p:'a->bool) FPr GPr.
        (p ENSURES (Not p)) FPr ==> (p ENSURES (Not p)) (APPEND FPr GPr)`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [APPEND;ENSURES;UNLESS;EXIST_TRANSITION] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [UNLESS_thm2] THEN
   REWRITE_TAC [UNDISCH_ALL (ONCE_REWRITE_RULE [EXIST_TRANSITION_thm12] (SPECL
     [`p:'a->bool`;`Not (p:'a->bool)`;`t:('a->'a)list`;`GPr:('a->'a)list`]
       EXIST_TRANSITION_thm8))]);;

(*
   Prove:
        !p q FPr GPr.
           p STABLE FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)
*)
let COMP_UNITY_cor9 = prove_thm
  ("COMP_UNITY_cor9",
   (`!(p:'a->bool) q FPr GPr.
         p STABLE FPr /\ (p UNLESS q) GPr ==> (p UNLESS q) (APPEND FPr GPr)`),
   REWRITE_TAC [STABLE;COMP_UNLESS_thm1] THEN
   REPEAT STRIP_TAC THENL
     [
      UNDISCH_TAC (`((p:'a->bool) UNLESS False)FPr`) THEN
      SPEC_TAC ((`FPr:('a->'a)list`),(`FPr:('a->'a)list`)) THEN
      LIST_INDUCT_TAC THENL
        [
         REWRITE_TAC [UNLESS]
        ;
         REWRITE_TAC [UNLESS;UNLESS_STMT] THEN
         BETA_TAC THEN
         REPEAT STRIP_TAC THENL
           [
            RES_TAC THEN
            UNDISCH_TAC
               (`~(False:'a->bool) s ==> (p:'a->bool)(h s) \/ False(h s)`) THEN
            REWRITE_TAC [FALSE_def;NOT_CLAUSES;OR_INTRO_THM1]
           ;
            RES_TAC
           ]
        ]
     ;
      ASM_REWRITE_TAC []
     ]);;


(*
   Prove:
    !p q FPr GPr.
         (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) (APPEND GPr FPr)
*)
let COMP_UNITY_cor10 = prove_thm
  ("COMP_UNITY_cor10",
   (`!(p:'a->bool) q FPr GPr.
         (p UNLESS q) (APPEND FPr GPr) = (p UNLESS q) (APPEND GPr FPr)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [COMP_UNLESS_thm1] THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

(*
   Prove:
    !p q FPr GPr.
         (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) (APPEND GPr FPr)
*)
let COMP_UNITY_cor11 = prove_thm
  ("COMP_UNITY_cor11",
   (`!(p:'a->bool) q FPr GPr.
         (p ENSURES q) (APPEND FPr GPr) = (p ENSURES q) (APPEND GPr FPr)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [COMP_ENSURES_thm1] THEN
   EQ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

(*
   Prove:
    !p q FPr GPr.
      (p LEADSTO q) (APPEND FPr GPr) = (p LEADSTO q) (APPEND GPr FPr)
*)

(*
  |- (!p' q'.
     ((p' ENSURES q')(APPEND Pr1 Pr2) ==> (p' LEADSTO q')(APPEND Pr2 Pr1)) /\
     (!r.
       (p' LEADSTO r)(APPEND Pr1 Pr2) /\ (p' LEADSTO r)(APPEND Pr2 Pr1) /\
       (r LEADSTO q')(APPEND Pr1 Pr2) /\ (r LEADSTO q')(APPEND Pr2 Pr1) ==>
       (p' LEADSTO q')(APPEND Pr1 Pr2) ==> (p' LEADSTO q')(APPEND Pr2 Pr1)) /\
     (!P.
       (!i. ((P i) LEADSTO q')(APPEND Pr1 Pr2)) /\
       (!i. ((P i) LEADSTO q')(APPEND Pr2 Pr1)) ==>
          (($ExistsX  P) LEADSTO q')(APPEND Pr1 Pr2) ==>
          (($ExistsX  P) LEADSTO q')(APPEND Pr2 Pr1)))
     ==>
       (p LEADSTO q)(APPEND Pr1 Pr2) ==> (p LEADSTO q)(APPEND Pr2 Pr1)
*)
let COMP_UNITY_cor12_lemma00 = (BETA_RULE (SPECL
  [(`\(p:'a->bool) q. (p LEADSTO q)(APPEND Pr2 Pr1)`);
   (`p:'a->bool`);(`q:'a->bool`);(`APPEND (Pr1:('a->'a)list) Pr2`)] LEADSTO_thm37));;

let COMP_UNITY_cor12_lemma01 = TAC_PROOF
  (([],
   (`!(p':'a->bool) q' Pr1 Pr2.
      (p' ENSURES q')(APPEND Pr1 Pr2) ==> (p' LEADSTO q')(APPEND Pr2 Pr1)`)),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (ONCE_REWRITE_RULE [COMP_UNITY_cor11] (ASSUME
    (`((p':'a->bool) ENSURES q')(APPEND Pr1 Pr2)`))) THEN
   IMP_RES_TAC LEADSTO_thm0);;

let COMP_UNITY_cor12_lemma02 = TAC_PROOF
  (([],
   (`!(p':'a->bool) q' Pr1 Pr2.
     (!r.
       (p' LEADSTO r)(APPEND Pr1 Pr2) /\ (p' LEADSTO r)(APPEND Pr2 Pr1) /\
       (r LEADSTO q')(APPEND Pr1 Pr2) /\ (r LEADSTO q')(APPEND Pr2 Pr1)
          ==> (p' LEADSTO q')(APPEND Pr2 Pr1))`)),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm1);;

let COMP_UNITY_cor12_lemma03 = TAC_PROOF
  (([],
   (`!(p':'a->bool) q' Pr1 Pr2.
     (!P:('a->bool)->bool.
       (!p''. p'' In P ==> (p'' LEADSTO q')(APPEND Pr1 Pr2)) /\
       (!p''. p'' In P ==> (p'' LEADSTO q')(APPEND Pr2 Pr1))
            ==> ((LUB P) LEADSTO q')(APPEND Pr2 Pr1))`)),
   REPEAT STRIP_TAC THEN
   IMP_RES_TAC LEADSTO_thm3a);;

(*
  |- !p q Pr1 Pr2.
       (p LEADSTO q)(APPEND Pr1 Pr2) ==> (p LEADSTO q)(APPEND Pr2 Pr1)
*)
let COMP_UNITY_cor12_lemma04 = (GEN_ALL (REWRITE_RULE
   [COMP_UNITY_cor12_lemma01;COMP_UNITY_cor12_lemma02;COMP_UNITY_cor12_lemma03]
    (SPEC_ALL COMP_UNITY_cor12_lemma00)));;

(*
 |- !p q Pr1 Pr2. (p LEADSTO q)(APPEND Pr1 Pr2) = (p LEADSTO q)(APPEND Pr2 Pr1)
*)
let COMP_UNITY_cor12 = prove_thm
  ("COMP_UNITY_cor12",
   (`!(p:'a->bool) q Pr1 Pr2.
       (p LEADSTO q)(APPEND Pr1 Pr2) = (p LEADSTO q)(APPEND Pr2 Pr1)`),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN REWRITE_TAC [COMP_UNITY_cor12_lemma04]);;

(*
  |- !p FPr GPr. p STABLE (APPEND FPr GPr) = p STABLE (APPEND GPr FPr)
*)
let COMP_UNITY_cor13 = prove_thm
  ("COMP_UNITY_cor13",
   (`!(p:'a->bool) FPr GPr.
      (p STABLE (APPEND FPr GPr)) = (p STABLE (APPEND GPr FPr))`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [COMP_UNITY_cor10] THEN
   ASM_REWRITE_TAC []);;


(*
  |- !p0 p FPr GPr.
      p INVARIANT (p0, APPEND FPr GPr) = p INVARIANT (p0, APPEND GPr FPr)
*)
let COMP_UNITY_cor14 = prove_thm
  ("COMP_UNITY_cor14",
   (`!(p0:'a->bool) p FPr GPr.
      (p INVARIANT (p0, (APPEND FPr GPr)))
    =
      (p INVARIANT (p0, (APPEND GPr FPr)))`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [INVARIANT] THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [COMP_UNITY_cor13] THEN
   ASM_REWRITE_TAC []);;
