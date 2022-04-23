(* ========================================================================= *)
(* Proof of the modal completeness of the provability logic GL.              *)
(*                                                                           *)
(* (c) Copyright, Marco Maggesi, Cosimo Perini Brogi 2020-2022.              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Iterated conjunction of formulae.                                         *)
(* ------------------------------------------------------------------------- *)

let CONJLIST = new_recursive_definition list_RECURSION
  `CONJLIST [] = True /\
   (!p X. CONJLIST (CONS p X) = if X = [] then p else p && CONJLIST X)`;;

let CONJLIST_IMP_MEM = prove
 (`!p X. MEM p X ==> |-- (CONJLIST X --> p)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJLIST] THEN
  STRIP_TAC THENL
  [POP_ASSUM (SUBST_ALL_TAC o GSYM) THEN
   COND_CASES_TAC THEN REWRITE_TAC[GL_imp_refl_th; GL_and_left_th];
   COND_CASES_TAC THENL [ASM_MESON_TAC[MEM]; ALL_TAC] THEN
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `CONJLIST t` THEN CONJ_TAC THENL
   [MATCH_ACCEPT_TAC GL_and_right_th; ASM_SIMP_TAC[]]]);;

let CONJLIST_MONO = prove
 (`!X Y. (!p. MEM p Y ==> MEM p X) ==> |-- (CONJLIST X --> CONJLIST Y)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJLIST] THENL
  [MESON_TAC[GL_add_assum; GL_truth_th]; ALL_TAC] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[CONJLIST_IMP_MEM];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC GL_and_intro THEN CONJ_TAC THENL
  [ASM_MESON_TAC[CONJLIST_IMP_MEM];
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let CONJLIST_CONS = prove
 (`!p X. |-- (CONJLIST (CONS p X) <-> p && CONJLIST X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THEN
  REWRITE_TAC[GL_iff_refl_th] THEN POP_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[CONJLIST] THEN ONCE_REWRITE_TAC[GL_iff_sym] THEN
  MATCH_ACCEPT_TAC GL_and_rigth_true_th);;

let CONJLIST_IMP_HEAD = prove
 (`!p X. |-- (CONJLIST (CONS p X) --> p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC[GL_imp_refl_th];
   REWRITE_TAC[GL_and_left_th]]);;

let CONJLIST_IMP_TAIL = prove
 (`!p X. |-- (CONJLIST (CONS p X) --> CONJLIST X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJLIST] THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC[CONJLIST; GL_imp_clauses];
   REWRITE_TAC[GL_and_right_th]]);;

let HEAD_TAIL_IMP_CONJLIST = prove
 (`!p h t. |-- (p --> h) /\ |-- (p --> CONJLIST t)
           ==> |-- (p --> CONJLIST (CONS h t))`,
  INTRO_TAC "!p h t; ph pt" THEN REWRITE_TAC[CONJLIST] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[GL_and_intro]]);;

let IMP_CONJLIST = prove
 (`!p X. |-- (p --> CONJLIST X) <=> (!q. MEM q X ==> |-- (p --> q))`,
  GEN_TAC THEN SUBGOAL_THEN
    `(!X q. |-- (p --> CONJLIST X) /\ MEM q X ==> |-- (p --> q)) /\
     (!X. (!q. MEM q X ==> |-- (p --> q)) ==> |-- (p --> CONJLIST X))`
    (fun th -> MESON_TAC[th]) THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `CONJLIST X` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM] THENL
  [REWRITE_TAC[CONJLIST; GL_imp_clauses]; ALL_TAC] THEN
  DISCH_TAC THEN  MATCH_MP_TAC HEAD_TAIL_IMP_CONJLIST THEN
  ASM_SIMP_TAC[]);;

let CONJLIST_IMP_SUBLIST = prove
 (`!X Y. Y SUBLIST X ==> |-- (CONJLIST X --> CONJLIST Y)`,
  REWRITE_TAC[SUBLIST; IMP_CONJLIST] THEN MESON_TAC[CONJLIST_IMP_MEM]);;

let CONJLIST_IMP = prove
 (`!l m.
     (!p. MEM p m ==> ?q. MEM q l /\ |-- (q --> p))
     ==> |-- (CONJLIST l --> CONJLIST m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; GL_imp_clauses]; ALL_TAC] THEN
  INTRO_TAC "hp" THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `h && CONJLIST t` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC GL_and_intro THEN
   CONJ_TAC THENL
   [HYP_TAC "hp: +" (SPEC `h:form`) THEN
    REWRITE_TAC[MEM] THEN MESON_TAC[CONJLIST_IMP_MEM; GL_imp_trans];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    INTRO_TAC "!p; p" THEN FIRST_X_ASSUM (MP_TAC o SPEC `p:form`) THEN
    ASM_REWRITE_TAC[MEM]];
   ALL_TAC] THEN
  MESON_TAC[CONJLIST_CONS; GL_iff_imp2]);;

let CONJLIST_APPEND = prove
 (`!l m. |-- (CONJLIST (APPEND l m) <-> CONJLIST l && CONJLIST m)`,
  FIX_TAC "m" THEN LIST_INDUCT_TAC THEN REWRITE_TAC[APPEND] THENL
  [REWRITE_TAC[CONJLIST] THEN ONCE_REWRITE_TAC[GL_iff_sym] THEN
   MATCH_ACCEPT_TAC GL_and_left_true_th;
   ALL_TAC] THEN
  MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `h && CONJLIST (APPEND t m)` THEN REWRITE_TAC[CONJLIST_CONS] THEN
  MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `h && (CONJLIST t && CONJLIST m)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_and_subst_th THEN ASM_REWRITE_TAC[GL_iff_refl_th];
   ALL_TAC] THEN
  MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `(h && CONJLIST t) && CONJLIST m` THEN CONJ_TAC THENL
  [MESON_TAC[GL_and_assoc_th; GL_iff_sym]; ALL_TAC] THEN
  MATCH_MP_TAC GL_and_subst_th THEN REWRITE_TAC[GL_iff_refl_th] THEN
  ONCE_REWRITE_TAC[GL_iff_sym] THEN MATCH_ACCEPT_TAC CONJLIST_CONS);;

let FALSE_NOT_CONJLIST = prove
 (`!X. MEM False X ==> |-- (Not (CONJLIST X))`,
  INTRO_TAC "!X; X" THEN REWRITE_TAC[GL_not_def] THEN
  MATCH_MP_TAC CONJLIST_IMP_MEM THEN POP_ASSUM MATCH_ACCEPT_TAC);;

let CONJLIST_MAP_BOX = prove
 (`!l. |-- (CONJLIST (MAP (Box) l) <-> Box (CONJLIST l))`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[CONJLIST; MAP; GL_iff_refl_th] THEN
   MATCH_MP_TAC GL_imp_antisym THEN
   SIMP_TAC[GL_add_assum; GL_truth_th; GL_necessitation];
   ALL_TAC] THEN
  REWRITE_TAC[MAP] THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `Box h && CONJLIST (MAP (Box) t)` THEN CONJ_TAC THENL
  [MATCH_ACCEPT_TAC CONJLIST_CONS; ALL_TAC] THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `Box h && Box (CONJLIST t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_imp_antisym THEN CONJ_TAC THEN
   MATCH_MP_TAC GL_and_intro THEN
   ASM_MESON_TAC[GL_and_left_th; GL_and_right_th; GL_iff_imp1;
                 GL_iff_imp2; GL_imp_trans];
   ALL_TAC] THEN
  MATCH_MP_TAC GL_iff_trans THEN EXISTS_TAC `Box (h && CONJLIST t)` THEN
  CONJ_TAC THENL
  [MESON_TAC[GL_box_and_th; GL_box_and_inv_th; GL_imp_antisym]; ALL_TAC] THEN
  MATCH_MP_TAC GL_box_iff THEN MATCH_MP_TAC GL_necessitation THEN
  ONCE_REWRITE_TAC[GL_iff_sym] THEN MATCH_ACCEPT_TAC CONJLIST_CONS);;

(* ------------------------------------------------------------------------- *)
(* Consistent list of formulas.                                              *)
(* ------------------------------------------------------------------------- *)

let CONSISTENT = new_definition
  `CONSISTENT (l:form list) <=> ~ (|-- (Not (CONJLIST l)))`;;

let CONSISTENT_SING = prove
 (`!p. CONSISTENT [p] <=> ~ |-- (Not p)`,
  REWRITE_TAC[CONSISTENT; CONJLIST]);;

let CONSISTENT_LEMMA = prove
 (`!X p. MEM p X /\ MEM (Not p) X ==> |-- (Not (CONJLIST X))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GL_not_def] THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `p && Not p` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_and_intro THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; GL_imp_trans; GL_and_pair_th];
   MESON_TAC[GL_nc_th]]);;

let CONSISTENT_SUBLIST = prove
 (`!X Y. CONSISTENT X /\ Y SUBLIST X ==> CONSISTENT Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT] THEN
  SUBGOAL_THEN `|-- (CONJLIST Y --> False) /\ Y SUBLIST X
                ==> |-- (CONJLIST X --> False)`
    (fun th -> ASM_MESON_TAC[th; GL_not_def]) THEN
  INTRO_TAC "inc sub" THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `CONJLIST Y` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CONJLIST_IMP_SUBLIST]);;

let CONSISTENT_CONS = prove
 (`!h t. CONSISTENT (CONS h t) <=> ~ |-- (Not h || Not (CONJLIST t))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[CONSISTENT] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC GL_iff THEN MATCH_MP_TAC GL_iff_trans THEN
  EXISTS_TAC `Not (h && CONJLIST t)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_not_subst THEN MATCH_ACCEPT_TAC CONJLIST_CONS;
   MATCH_ACCEPT_TAC GL_de_morgan_and_th]);;

let CONSISTENT_NC = prove
 (`!X p. MEM p X /\ MEM (Not p) X ==> ~CONSISTENT X`,
  INTRO_TAC "!X p; p np" THEN REWRITE_TAC[CONSISTENT; GL_not_def] THEN
  MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `p && Not p` THEN
  REWRITE_TAC[GL_nc_th] THEN MATCH_MP_TAC GL_and_intro THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM]);;

let CONSISTENT_EM = prove
 (`!h t. CONSISTENT t
         ==> CONSISTENT (CONS h t) \/ CONSISTENT (CONS (Not h) t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONSISTENT_CONS] THEN
  REWRITE_TAC[CONSISTENT] THEN
  SUBGOAL_THEN
    `|-- ((Not h || Not CONJLIST t) --> (Not Not h || Not CONJLIST t)
         --> (Not CONJLIST t))`
    (fun th -> MESON_TAC[th; GL_modusponens]) THEN
  REWRITE_TAC[GL_disj_imp] THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_imp_swap THEN REWRITE_TAC[GL_disj_imp] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GL_imp_swap THEN MATCH_MP_TAC GL_shunt THEN
    MATCH_MP_TAC GL_frege THEN EXISTS_TAC `False` THEN
    REWRITE_TAC[GL_nc_th] THEN
    MATCH_MP_TAC GL_add_assum THEN MATCH_ACCEPT_TAC GL_ex_falso_th;
    MATCH_ACCEPT_TAC GL_axiom_addimp];
   MATCH_MP_TAC GL_imp_swap THEN REWRITE_TAC[GL_disj_imp] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GL_add_assum THEN MATCH_ACCEPT_TAC GL_imp_refl_th;
    MATCH_ACCEPT_TAC GL_axiom_addimp]]);;

let FALSE_IMP_NOT_CONSISTENT = prove
 (`!X. MEM False X ==> ~ CONSISTENT X`,
  SIMP_TAC[CONSISTENT; FALSE_NOT_CONJLIST]);;

(* ------------------------------------------------------------------------- *)
(* Maximal Consistent Sets.                                                  *)
(* See Boolos p.79 (pdf p.118).  D in the text is p here.                    *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_CONSISTENT = new_definition
  `MAXIMAL_CONSISTENT p X <=>
   CONSISTENT X /\ NOREPETITION X /\
   (!q. q SUBFORMULA p ==> MEM q X \/ MEM (Not q) X)`;;

let MAXIMAL_CONSISTENT_LEMMA = prove
 (`!p X A b. MAXIMAL_CONSISTENT p X /\
             (!q. MEM q A ==> MEM q X) /\
             b SUBFORMULA p /\
             |-- (CONJLIST A --> b)
             ==> MEM b X`,
  INTRO_TAC "!p X A b; mconst subl b Ab" THEN REFUTE_THEN ASSUME_TAC THEN
  CLAIM_TAC "rmk" `MEM (Not b) X` THENL
  [ASM_MESON_TAC[MAXIMAL_CONSISTENT]; ALL_TAC] THEN
  CLAIM_TAC "rmk2" `|-- (CONJLIST X --> b && Not b)` THENL
  [MATCH_MP_TAC GL_and_intro THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONJLIST_MONO; GL_imp_trans];
    ASM_MESON_TAC[CONJLIST_IMP_MEM]];
   ALL_TAC] THEN
  CLAIM_TAC "rmk3" `|-- (CONJLIST X --> False)` THENL
  [ASM_MESON_TAC[GL_imp_trans; GL_nc_th]; ALL_TAC] THEN
  SUBGOAL_THEN `~ CONSISTENT X`
    (fun th -> ASM_MESON_TAC[th; MAXIMAL_CONSISTENT]) THEN
  ASM_REWRITE_TAC[CONSISTENT; GL_not_def]);;

let MAXIMAL_CONSISTENT_MEM_NOT = prove
 (`!X p q. MAXIMAL_CONSISTENT p X /\ q SUBFORMULA p
           ==> (MEM (Not q) X <=> ~ MEM q X)`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN MESON_TAC[CONSISTENT_NC]);;

let MAXIMAL_CONSISTENT_MEM_CASES = prove
 (`!X p q. MAXIMAL_CONSISTENT p X /\ q SUBFORMULA p
           ==> (MEM q X \/ MEM (Not q) X)`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN MESON_TAC[CONSISTENT_NC]);;

let MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE = prove
 (`!p w q. MAXIMAL_CONSISTENT p w /\ q SUBFORMULA p
           ==> (MEM q w <=> |-- (CONJLIST w --> q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_CONSISTENT; CONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN LABEL_ASM_CASES_TAC "q" `MEM (q:form) w` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN CLAIM_TAC "nq" `MEM (Not q) w` THENL
  [ASM_MESON_TAC[]; INTRO_TAC "deriv"] THEN
  SUBGOAL_THEN `|-- (Not (CONJLIST w))` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GL_not_def] THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `q && Not q` THEN REWRITE_TAC[GL_nc_th] THEN
  ASM_SIMP_TAC[GL_and_intro; CONJLIST_IMP_MEM]);;

let MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE = prove
 (`!p w q. MAXIMAL_CONSISTENT p w /\ q SUBFORMULA p
           ==> (MEM (Not q) w <=> |-- (CONJLIST w --> Not q))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MAXIMAL_CONSISTENT; CONSISTENT] THEN
  INTRO_TAC "(w em) sub" THEN LABEL_ASM_CASES_TAC "q" `MEM (Not q) w` THEN
  ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN CLAIM_TAC "nq" `MEM (q:form) w` THENL
  [ASM_MESON_TAC[]; INTRO_TAC "deriv"] THEN
  SUBGOAL_THEN `|-- (Not (CONJLIST w))` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GL_not_def] THEN MATCH_MP_TAC GL_imp_trans THEN
  EXISTS_TAC `q && Not q` THEN REWRITE_TAC[GL_nc_th] THEN
  ASM_SIMP_TAC[GL_and_intro; CONJLIST_IMP_MEM]);;

(* ------------------------------------------------------------------------- *)
(* Subsentences.                                                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("SUBSENTENCE",get_infix_status "SUBFORMULA");;

let SUBSENTENCE_RULES,SUBSENTENCE_INDUCT,SUBSENTENCE_CASES =
  new_inductive_definition
  `(!p q. p SUBFORMULA q ==> p SUBSENTENCE q) /\
   (!p q. p SUBFORMULA q ==> Not p SUBSENTENCE q)`;;

let GL_STANDARD_FRAME = new_definition
  `GL_STANDARD_FRAME p (W,R) <=>
   W = {w | MAXIMAL_CONSISTENT p w /\
            (!q. MEM q w ==> q SUBSENTENCE p)} /\
   ITF (W,R) /\
   (!q w. Box q SUBFORMULA p /\ w IN W
          ==> (MEM (Box q) w <=> !x. R w x ==> MEM q x))`;;

let SUBFORMULA_IMP_SUBSENTENCE = prove
 (`!p q. p SUBFORMULA q ==> p SUBSENTENCE q`,
  REWRITE_TAC[SUBSENTENCE_RULES]);;

let SUBFORMULA_IMP_NEG_SUBSENTENCE = prove
 (`!p q. p SUBFORMULA q ==> Not p SUBSENTENCE q`,
  REWRITE_TAC[SUBSENTENCE_RULES]);;

(* ------------------------------------------------------------------------- *)
(* Standard model.                                                           *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_MODEL = new_definition
  `GL_STANDARD_MODEL p (W,R) V <=>
   GL_STANDARD_FRAME p (W,R) /\
   (!a w. w IN W ==> (V a w <=> MEM (Atom a) w /\ Atom a SUBFORMULA p))`;;

(* ------------------------------------------------------------------------- *)
(* Truth Lemma.                                                              *)
(* ------------------------------------------------------------------------- *)

let GL_truth_lemma = prove
 (`!W R p V q.
     ~ |-- p /\
     GL_STANDARD_MODEL p (W,R) V /\
     q SUBFORMULA p
     ==> !w. w IN W ==> (MEM q w <=> holds (W,R) V q w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GL_STANDARD_MODEL; GL_STANDARD_FRAME; SUBSENTENCE_CASES] THEN
  INTRO_TAC "np ((W itf 1) val) q" THEN REMOVE_THEN "W" SUBST_VAR_TAC THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REMOVE_THEN "q" MP_TAC THEN
  HYP_TAC "1" (REWRITE_RULE[IN_ELIM_THM]) THEN
  HYP_TAC "val" (REWRITE_RULE[FORALL_IN_GSPEC]) THEN
  SPEC_TAC (`q:form`,`q:form`) THEN MATCH_MP_TAC form_INDUCT THEN
  REWRITE_TAC[holds] THEN
  CONJ_TAC THENL
  [INTRO_TAC "sub; !w; w" THEN
   HYP_TAC "w -> cons memq" (REWRITE_RULE[MAXIMAL_CONSISTENT]) THEN
   ASM_MESON_TAC[FALSE_IMP_NOT_CONSISTENT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[MAXIMAL_CONSISTENT] THEN
   INTRO_TAC "p; !w; (cons (norep mem)) subf" THEN
   HYP_TAC "mem: t | nt" (C MATCH_MP (ASSUME `True SUBFORMULA p`)) THEN
   ASM_REWRITE_TAC[] THEN
   REFUTE_THEN (K ALL_TAC) THEN
   REMOVE_THEN "cons" MP_TAC THEN REWRITE_TAC[CONSISTENT] THEN
   REWRITE_TAC[GL_not_def] THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `Not True` THEN ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN
   MATCH_MP_TAC GL_iff_imp1 THEN MATCH_ACCEPT_TAC GL_not_true_th;
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![q/a]; q; sub; !w; w" THEN REMOVE_THEN "q" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub1 q"] THEN EQ_TAC THENL
    [HYP MESON_TAC "w sub1 q" [MAXIMAL_CONSISTENT_MEM_NOT];
     REMOVE_THEN "q" (MP_TAC o SPEC `w: form list`) THEN
     ANTS_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT]];
     ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY
  (INTRO_TAC "![q1] [q2]; q1 q2; sub; !w; w" THEN
   REMOVE_THEN "q1" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub1 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
   REMOVE_THEN "q2" MP_TAC THEN
   MATCH_MP_TAC (MESON[] `P /\ (P /\ Q ==> R) ==> ((P ==> Q) ==> R)`) THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    INTRO_TAC "sub2 +" THEN DISCH_THEN (MP_TAC o SPEC `w:form list`)] THEN
   HYP REWRITE_TAC "w" [] THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN
   CLAIM_TAC "rmk"
     `!q. q SUBFORMULA p ==> (MEM q w <=> |-- (CONJLIST w --> q))` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE];
    ALL_TAC]) THENL
  [
   (* Case && *)
   ASM_SIMP_TAC[] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_EQ_DERIVABLE;
     GL_and_intro; GL_and_left_th; GL_and_right_th; GL_imp_trans]
  ;
   (* Case || *)
   EQ_TAC THENL
   [INTRO_TAC "q1q2";
    ASM_MESON_TAC[GL_or_left_th; GL_or_right_th; GL_imp_trans]] THEN
   CLAIM_TAC "wq1q2" `|-- (CONJLIST w --> q1 || q2)` THENL
   [ASM_SIMP_TAC[CONJLIST_IMP_MEM]; ALL_TAC] THEN
   CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CLAIM_TAC "hq2 | hq2" `MEM q2 w \/ MEM (Not q2) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_REWRITE_TAC[];
    REFUTE_THEN (K ALL_TAC)] THEN
   SUBGOAL_THEN `~ (|-- (CONJLIST w --> False))` MP_TAC THENL
   [REWRITE_TAC[GSYM GL_not_def] THEN
    ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT];
    REWRITE_TAC[]] THEN
   MATCH_MP_TAC GL_frege THEN EXISTS_TAC `q1 || q2` THEN
   ASM_SIMP_TAC[CONJLIST_IMP_MEM] THEN MATCH_MP_TAC GL_imp_swap THEN
   REWRITE_TAC[GL_disj_imp] THEN CONJ_TAC THEN MATCH_MP_TAC GL_imp_swap THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; GL_axiom_not; GL_iff_imp1; GL_imp_trans]
  ;
   (* Case --> *)
   ASM_SIMP_TAC[] THEN EQ_TAC THENL
   [ASM_MESON_TAC[GL_frege; CONJLIST_IMP_MEM]; INTRO_TAC "imp"] THEN
   CLAIM_TAC "hq1 | hq1" `MEM q1 w \/ MEM (Not q1) w` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_MESON_TAC[CONJLIST_IMP_MEM; GL_imp_swap; GL_add_assum];
    ALL_TAC] THEN
   MATCH_MP_TAC GL_shunt THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `q1 && Not q1` THEN CONJ_TAC THENL
   [ALL_TAC; MESON_TAC[GL_nc_th; GL_imp_trans; GL_ex_falso_th]] THEN
   MATCH_MP_TAC GL_and_intro THEN REWRITE_TAC[GL_and_right_th] THEN
   ASM_MESON_TAC[CONJLIST_IMP_MEM; GL_imp_trans; GL_and_left_th]
  ;
   (* Case <-> *)
   ASM_SIMP_TAC[] THEN REMOVE_THEN "sub" (K ALL_TAC) THEN EQ_TAC THENL
   [MESON_TAC[GL_frege; GL_add_assum; GL_modusponens_th;
              GL_axiom_iffimp1; GL_axiom_iffimp2];
    ALL_TAC] THEN
   INTRO_TAC "iff" THEN MATCH_MP_TAC GL_imp_trans THEN
   EXISTS_TAC `(q1 --> q2) && (q2 --> q1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GL_and_intro; MESON_TAC[GL_iff_def_th; GL_iff_imp2]] THEN
   CLAIM_TAC "rmk'"
     `!q. q SUBFORMULA p
          ==> (MEM (Not q) w <=> |-- (CONJLIST w --> Not q))` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_SUBFORMULA_MEM_NEG_EQ_DERIVABLE];
    ALL_TAC] THEN
   CLAIM_TAC "hq1 | hq1"
     `|-- (CONJLIST w --> q1) \/ |-- (CONJLIST w --> Not q1)` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_MESON_TAC[GL_imp_swap; GL_add_assum];
    ALL_TAC] THEN
   CLAIM_TAC "hq2 | hq2"
     `|-- (CONJLIST w --> q2) \/ |-- (CONJLIST w --> Not q2)` THENL
   [ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_CASES];
    ASM_MESON_TAC[GL_imp_swap; GL_add_assum];
    ALL_TAC] THEN
   ASM_MESON_TAC[GL_nc_th; GL_imp_trans; GL_and_intro;
                 GL_ex_falso_th; GL_imp_swap; GL_shunt]
  ;
   (* Case Box *)
   INTRO_TAC "!a; a; sub; !w; w" THEN REWRITE_TAC[holds; IN_ELIM_THM] THEN
   CLAIM_TAC "suba" `a SUBFORMULA p` THENL
   [MATCH_MP_TAC SUBFORMULA_TRANS THEN
     EXISTS_TAC `Box a` THEN
     ASM_REWRITE_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
     ALL_TAC] THEN
   HYP_TAC "itf" (REWRITE_RULE[ITF; IN_ELIM_THM]) THEN
   EQ_TAC THENL
   [INTRO_TAC "boxa; !w'; (maxw' subw') r" THEN
    HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
    HYP_TAC "a: +" (SPEC `w':form list`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o GSYM) THEN
    REMOVE_THEN "1" (MP_TAC o SPECL [`a: form`;`w: form list`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   INTRO_TAC "3" THEN
   REMOVE_THEN  "1" (MP_TAC o SPECL [`a:form`; `w:form list`]) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN INTRO_TAC "![w']; w'" THEN
   REMOVE_THEN "3" (MP_TAC o SPEC `w':form list`) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   HYP_TAC "a" (C MATCH_MP (ASSUME `a SUBFORMULA p`)) THEN
   HYP_TAC "a: +" (SPEC `w':form list`) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o GSYM) THEN REWRITE_TAC[]
  ]);;

(* ------------------------------------------------------------------------- *)
(* Extension Lemma.                                                          *)
(* Every consistent list of formulae can be extended to a maximal consistent *)
(* list by a construction similar to Lindenbaum's extension.                 *)
(* ------------------------------------------------------------------------- *)

let EXTEND_MAXIMAL_CONSISTENT = prove
 (`!p X. CONSISTENT X /\
         (!q. MEM q X ==> q SUBSENTENCE p)
         ==> ?M. MAXIMAL_CONSISTENT p M /\
                 (!q. MEM q M ==> q SUBSENTENCE p) /\
                 X SUBLIST M`,
  GEN_TAC THEN SUBGOAL_THEN
    `!L X. CONSISTENT X /\ NOREPETITION X /\
           (!q. MEM q X ==> q SUBSENTENCE p) /\
           (!q. MEM q L ==> q SUBFORMULA p) /\
           (!q. q SUBFORMULA p ==> MEM q L \/ MEM q X \/ MEM (Not q) X)
           ==> ?M. MAXIMAL_CONSISTENT p M /\
                   (!q. MEM q M ==> q SUBSENTENCE p) /\
                   X SUBLIST M`
    (LABEL_TAC "P") THENL
  [ALL_TAC;
   INTRO_TAC "![X']; cons' subf'" THEN
   DESTRUCT_TAC "@X. uniq sub1 sub2"
     (ISPEC `X':form list` EXISTS_NOREPETITION) THEN
   DESTRUCT_TAC "@L'. uniq L'" (SPEC `p:form` SUBFORMULA_LIST) THEN
   HYP_TAC "P: +" (SPECL[`L':form list`; `X:form list`]) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[CONSISTENT_SUBLIST]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBLIST];
    ALL_TAC] THEN
   INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBLIST_TRANS]] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC[MEM] THEN INTRO_TAC "!X; X uniq max subf" THEN
   EXISTS_TAC `X:form list` THEN
   ASM_REWRITE_TAC[SUBLIST_REFL; MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  POP_ASSUM (LABEL_TAC "hpind") THEN REWRITE_TAC[MEM] THEN
  INTRO_TAC "!X; cons uniq qmem qmem' subf" THEN
  LABEL_ASM_CASES_TAC "hmemX" `MEM (h:form) X` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form list`) THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  LABEL_ASM_CASES_TAC "nhmemX" `MEM (Not h) X` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `X:form list`) THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  LABEL_ASM_CASES_TAC "consh" `CONSISTENT (CONS (h:form) X)` THENL
  [REMOVE_THEN "hpind" (MP_TAC o SPEC `CONS (h:form) X`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOREPETITION_CLAUSES; MEM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_MESON_TAC[SUBLIST; SUBFORMULA_IMP_SUBSENTENCE];
    ALL_TAC] THEN
   INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
   ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MP_TAC THEN
   REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[];
   ALL_TAC] THEN
  REMOVE_THEN "hpind" (MP_TAC o SPEC `CONS (Not h) X`) THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[NOREPETITION_CLAUSES] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[CONSISTENT_EM]; ALL_TAC] THEN
   REWRITE_TAC[MEM] THEN ASM_MESON_TAC[SUBLIST; SUBSENTENCE_RULES];
   ALL_TAC] THEN
  INTRO_TAC "@M. max sub" THEN EXISTS_TAC `M:form list` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "sub" MP_TAC THEN
  REWRITE_TAC[SUBLIST; MEM] THEN MESON_TAC[]);;

let NONEMPTY_MAXIMAL_CONSISTENT = prove
 (`!p. ~ |-- p
       ==> ?M. MAXIMAL_CONSISTENT p M /\
               MEM (Not p) M /\
               (!q. MEM q M ==> q SUBSENTENCE p)`,
  INTRO_TAC "!p; p" THEN
  MP_TAC (SPECL [`p:form`; `[Not p]`] EXTEND_MAXIMAL_CONSISTENT) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[CONSISTENT_SING] THEN ASM_MESON_TAC[GL_DOUBLENEG_CL];
    ALL_TAC] THEN
   GEN_TAC THEN REWRITE_TAC[MEM] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MESON_TAC[SUBFORMULA_IMP_NEG_SUBSENTENCE; SUBFORMULA_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN EXISTS_TAC `M:form list` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBLIST; MEM]);;

(* ------------------------------------------------------------------------- *)
(* Accessibility lemma.                                                      *)
(* ------------------------------------------------------------------------- *)

let GL_STANDARD_REL = new_definition
  `GL_STANDARD_REL p w x <=>
   MAXIMAL_CONSISTENT p w /\ (!q. MEM q w ==> q SUBSENTENCE p) /\
   MAXIMAL_CONSISTENT p x /\ (!q. MEM q x ==> q SUBSENTENCE p) /\
   (!B. MEM (Box B) w ==> MEM (Box B) x /\ MEM B x) /\
   (?E. MEM (Box E) x /\ MEM (Not (Box E)) w)`;;

let ITF_MAXIMAL_CONSISTENT = prove
 (`!p. ~ |-- p
       ==> ITF ({M | MAXIMAL_CONSISTENT p M /\
                     (!q. MEM q M ==> q SUBSENTENCE p)},
                GL_STANDARD_REL p)`,
  INTRO_TAC "!p; p" THEN REWRITE_TAC[ITF] THEN
  (* Nonempty *)
  CONJ_TAC THENL
  [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
   ASM_MESON_TAC[NONEMPTY_MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  (* Well-defined *)
  CONJ_TAC THENL
  [REWRITE_TAC[GL_STANDARD_REL; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  (* Finite *)
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC
     `{l | NOREPETITION l /\
           !q. MEM q l ==> q IN {q | q SUBSENTENCE p}}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_NOREPETITION THEN POP_ASSUM_LIST (K ALL_TAC) THEN
    SUBGOAL_THEN
      `{q | q SUBSENTENCE p} =
       {q | q SUBFORMULA p} UNION IMAGE (Not) {q | q SUBFORMULA p}`
      SUBST1_TAC THENL
    [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_UNION;
                 FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
     REWRITE_TAC[IN_UNION; IN_ELIM_THM; SUBSENTENCE_RULES] THEN
     GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [SUBSENTENCE_CASES] THEN
     DISCH_THEN STRUCT_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
     ASM SET_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNION; FINITE_SUBFORMULA] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_SUBFORMULA];
    ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM; MAXIMAL_CONSISTENT] THEN
   GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Irreflexive *)
  CONJ_TAC THENL
  [REWRITE_TAC[FORALL_IN_GSPEC; GL_STANDARD_REL] THEN
   INTRO_TAC "!M; M sub" THEN ASM_REWRITE_TAC[] THEN
   INTRO_TAC "_ (@E. E1 E2)" THEN
   SUBGOAL_THEN `~ CONSISTENT M`
     (fun th -> ASM_MESON_TAC[th; MAXIMAL_CONSISTENT]) THEN
   MATCH_MP_TAC CONSISTENT_NC THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Transitive *)
  REWRITE_TAC[IN_ELIM_THM; GL_STANDARD_REL] THEN
  INTRO_TAC "!x y z; (x1 x2) (y1 y2) (z1 z2) +" THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let ACCESSIBILITY_LEMMA =
  let MEM_FLATMAP_LEMMA = prove
   (`!p l. MEM p (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) l) <=>
           (?q. p = Box q /\ MEM p l)`,
    GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; FLATMAP] THEN
    REWRITE_TAC[MEM_APPEND] THEN ASM_CASES_TAC `?c. h = Box c` THENL
    [POP_ASSUM (CHOOSE_THEN SUBST_VAR_TAC) THEN ASM_REWRITE_TAC[MEM] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    SUBGOAL_THEN `~ MEM p (match h with Box c -> [Box c] | _ -> [])`
      (fun th -> ASM_REWRITE_TAC[th]) THENL
    [POP_ASSUM MP_TAC THEN STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
     REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THEN
     MESON_TAC[];
     ALL_TAC] THEN
    POP_ASSUM (fun th -> MESON_TAC[th]))
  and CONJLIST_FLATMAP_DOT_BOX_LEMMA = prove
   (`!w. |-- (CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w)
              -->
              CONJLIST (MAP (Box)
                (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)))`,
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC[FLATMAP; MAP; GL_imp_refl_th]; ALL_TAC] THEN
    REWRITE_TAC[FLATMAP; MAP_APPEND] THEN MATCH_MP_TAC GL_imp_trans THEN
    EXISTS_TAC
      `CONJLIST (match h with Box c -> [Box c] | _ -> []) &&
       CONJLIST (FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) t)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC GL_iff_imp1 THEN MATCH_ACCEPT_TAC CONJLIST_APPEND;
     ALL_TAC] THEN
    MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC
      `CONJLIST (MAP (Box) (match h with Box c -> [c; Box c] | _ -> [])) &&
       CONJLIST (MAP (Box)
         (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) t))` THEN
    CONJ_TAC THENL
    [ALL_TAC;
     MATCH_MP_TAC GL_iff_imp2 THEN MATCH_ACCEPT_TAC CONJLIST_APPEND] THEN
    MATCH_MP_TAC GL_and_intro THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[GL_imp_trans; GL_and_right_th]] THEN
    MATCH_MP_TAC GL_imp_trans THEN
    EXISTS_TAC `CONJLIST (match h with Box c -> [Box c] | _ -> [])` THEN
    CONJ_TAC THENL [MATCH_ACCEPT_TAC GL_and_left_th; ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    STRUCT_CASES_TAC (SPEC `h:form` (cases "form")) THEN
    REWRITE_TAC[distinctness "form"; MAP; GL_imp_refl_th] THEN
    REWRITE_TAC[CONJLIST; NOT_CONS_NIL] THEN MATCH_ACCEPT_TAC GL_dot_box) in
 prove
 (`!p M w q.
     ~ |-- p /\
     MAXIMAL_CONSISTENT p M /\
     (!q. MEM q M ==> q SUBSENTENCE p) /\
     MAXIMAL_CONSISTENT p w /\
     (!q. MEM q w ==> q SUBSENTENCE p) /\
     MEM (Not p) M /\
     Box q SUBFORMULA p /\
     (!x. GL_STANDARD_REL p w x ==> MEM q x)
     ==> MEM (Box q) w`,
  REPEAT GEN_TAC THEN INTRO_TAC "p maxM subM maxw subw notp boxq rrr" THEN
  REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "rrr" MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THEN
  CLAIM_TAC "consistent_X"
    `CONSISTENT (CONS (Not q) (CONS (Box q)
       (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w)))` THENL
  [REMOVE_THEN "contra" MP_TAC THEN REWRITE_TAC[CONSISTENT; CONTRAPOS_THM] THEN
   INTRO_TAC "incons" THEN MATCH_MP_TAC MAXIMAL_CONSISTENT_LEMMA THEN
   MAP_EVERY EXISTS_TAC [`p:form`;
     `FLATMAP (\x. match x with Box c -> [Box c] | _ -> []) w`] THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[MEM_FLATMAP_LEMMA] THEN MESON_TAC[];
    ALL_TAC] THEN
   MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `Box(Box q --> q)` THEN
   REWRITE_TAC[GL_axiom_lob] THEN MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC
     `CONJLIST (MAP (Box)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[CONJLIST_FLATMAP_DOT_BOX_LEMMA]; ALL_TAC] THEN
   CLAIM_TAC "XIMP"
     `!x y l.
        |-- (Not (Not y && CONJLIST (CONS x l)))
        ==> |-- ((CONJLIST (MAP (Box) l)) --> Box(x --> y))` THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC GL_imp_trans THEN
    EXISTS_TAC `Box (CONJLIST l)` THEN CONJ_TAC THENL
    [MESON_TAC[CONJLIST_MAP_BOX;GL_iff_imp1]; ALL_TAC] THEN
    MATCH_MP_TAC GL_imp_box THEN MATCH_MP_TAC GL_shunt THEN
    ONCE_REWRITE_TAC[GSYM GL_contrapos_eq] THEN MATCH_MP_TAC GL_imp_trans THEN
    EXISTS_TAC `CONJLIST (CONS x l) --> False` THEN CONJ_TAC THENL
    [ASM_MESON_TAC[GL_shunt; GL_not_def];
     MATCH_MP_TAC GL_imp_trans THEN EXISTS_TAC `Not (CONJLIST(CONS x l))` THEN
     CONJ_TAC THENL
     [MESON_TAC[GL_axiom_not;GL_iff_imp2];
      MESON_TAC[GL_contrapos_eq;CONJLIST_CONS; GL_and_comm_th;
                GL_iff_imp2; GL_iff_imp1; GL_imp_trans]]];
    ALL_TAC] THEN
   POP_ASSUM MATCH_MP_TAC THEN
   HYP_TAC "incons" (REWRITE_RULE[CONSISTENT]) THEN
   HYP_TAC "incons" (ONCE_REWRITE_RULE[CONJLIST]) THEN
   HYP_TAC "incons" (REWRITE_RULE[NOT_CONS_NIL]) THEN
   POP_ASSUM MATCH_ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC (SPECL
    [`p:form`;
     `CONS (Not q) (CONS (Box q)
        (FLATMAP (\x. match x with Box c -> [c; Box c] | _ -> []) w))`]
    EXTEND_MAXIMAL_CONSISTENT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[MEM] THEN GEN_TAC THEN STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THENL
   [MATCH_MP_TAC SUBFORMULA_IMP_NEG_SUBSENTENCE THEN
    REWRITE_TAC[UNWIND_THM1] THEN HYP MESON_TAC "boxq"
      [SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   POP_ASSUM (DESTRUCT_TAC "@y. +" o REWRITE_RULE[MEM_FLATMAP]) THEN
   STRUCT_CASES_TAC (SPEC `y:form` (cases "form")) THEN REWRITE_TAC[MEM] THEN
   STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THENL
   [MATCH_MP_TAC SUBFORMULA_IMP_SUBSENTENCE THEN
    CLAIM_TAC "rmk" `Box a SUBSENTENCE p` THENL
    [POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []; ALL_TAC] THEN
    HYP_TAC "rmk" (REWRITE_RULE[SUBSENTENCE_CASES; distinctness "form"]) THEN
    TRANS_TAC SUBFORMULA_TRANS `Box a` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[SUBFORMULA_INVERSION; SUBFORMULA_REFL];
    POP_ASSUM MP_TAC THEN HYP MESON_TAC "subw" []];
   ALL_TAC] THEN
  INTRO_TAC "@X. maxX subX subl" THEN EXISTS_TAC `X:form list` THEN
  ASM_REWRITE_TAC[GL_STANDARD_REL; NOT_IMP] THEN CONJ_TAC THENL
  [CONJ_TAC THENL
   [INTRO_TAC "!B; B" THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
    CONJ_TAC THEN REMOVE_THEN "subl" MATCH_MP_TAC THEN
    REWRITE_TAC[MEM; distinctness "form"; injectivity "form"] THENL
    [DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN EXISTS_TAC `Box B` THEN
     ASM_REWRITE_TAC[MEM];
     DISJ2_TAC THEN DISJ2_TAC THEN REWRITE_TAC[MEM_FLATMAP] THEN
     EXISTS_TAC `Box B` THEN ASM_REWRITE_TAC[MEM]];
    ALL_TAC] THEN
   EXISTS_TAC `q:form` THEN HYP_TAC "subl" (REWRITE_RULE[SUBLIST]) THEN
   CONJ_TAC THENL
   [REMOVE_THEN "subl" MATCH_MP_TAC THEN REWRITE_TAC[MEM]; ALL_TAC] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT_MEM_NOT];
   ALL_TAC] THEN
  HYP_TAC "subl: +" (SPEC `Not q` o REWRITE_RULE[SUBLIST]) THEN
  REWRITE_TAC[MEM] THEN
  IMP_REWRITE_TAC[GSYM MAXIMAL_CONSISTENT_MEM_NOT] THEN
  SIMP_TAC[] THEN INTRO_TAC "_" THEN MATCH_MP_TAC SUBFORMULA_TRANS THEN
  EXISTS_TAC `Box q` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBFORMULA_TRANS; SUBFORMULA_INVERSION; SUBFORMULA_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness theorem for GL.                                        *)
(* ------------------------------------------------------------------------- *)

let GL_COUNTERMODEL = prove
 (`!M p.
     ~(|-- p) /\
     MAXIMAL_CONSISTENT p M /\
     MEM (Not p) M /\
     (!q. MEM q M ==> q SUBSENTENCE p)
     ==>
     ~holds
        ({M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
         GL_STANDARD_REL p)
        (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
        p M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL
    [`{M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)}`;
     `GL_STANDARD_REL p`;
     `p:form`;
     `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w`;
     `p:form`] GL_truth_lemma) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[SUBFORMULA_REFL; GL_STANDARD_MODEL;
                   GL_STANDARD_FRAME] THEN
   ASM_SIMP_TAC[ITF_MAXIMAL_CONSISTENT] THEN REWRITE_TAC[IN_ELIM_THM] THEN
   CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
   INTRO_TAC "!q w; boxq w subf" THEN EQ_TAC THENL
   [ASM_REWRITE_TAC[GL_STANDARD_REL] THEN SIMP_TAC[]; ALL_TAC] THEN
    INTRO_TAC "hp" THEN MATCH_MP_TAC ACCESSIBILITY_LEMMA THEN
    MAP_EVERY EXISTS_TAC [`p:form`; `M:form list`] THEN
    ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPEC `M:form list`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  DISCH_THEN (SUBST1_TAC o GSYM) THEN
  ASM_MESON_TAC[MAXIMAL_CONSISTENT; CONSISTENT_NC]);;

let GL_COUNTERMODEL_ALT = prove
 (`!p. ~(|-- p)
       ==>
       ~holds_in
          ({M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
           GL_STANDARD_REL p)
          p`,
  INTRO_TAC "!p; p" THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM] THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w` THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ |-- p`)) THEN
  EXISTS_TAC `M:form list` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GL_COUNTERMODEL THEN ASM_REWRITE_TAC[]);;

let COMPLETENESS_THEOREM = prove
 (`!p. ITF:(form list->bool)#(form list->form list->bool)->bool |= p
       ==> |-- p`,
  GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  INTRO_TAC "p" THEN REWRITE_TAC[valid; NOT_FORALL_THM] THEN
  EXISTS_TAC `({M | MAXIMAL_CONSISTENT p M /\
                    (!q. MEM q M ==> q SUBSENTENCE p)},
               GL_STANDARD_REL p)` THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
  [MATCH_MP_TAC ITF_MAXIMAL_CONSISTENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC GL_COUNTERMODEL_ALT THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Modal completeness for GL for models on a generic (infinite) domain.      *)
(* ------------------------------------------------------------------------- *)

let COMPLETENESS_THEOREM_GEN = prove
 (`!p. INFINITE (:A) /\ ITF:(A->bool)#(A->A->bool)->bool |= p ==> |-- p`,
  SUBGOAL_THEN
    `INFINITE (:A)
     ==> !p. ITF:(A->bool)#(A->A->bool)->bool |= p
             ==> ITF:(form list->bool)#(form list->form list->bool)->bool |= p`
    (fun th -> MESON_TAC[th; COMPLETENESS_THEOREM]) THEN
  INTRO_TAC "A" THEN MATCH_MP_TAC BISIMILAR_VALID THEN
  REPEAT GEN_TAC THEN INTRO_TAC "itf1 w1" THEN
  CLAIM_TAC "@f. inj" `?f:form list->A. (!x y. f x = f y ==> x = y)` THENL
  [SUBGOAL_THEN `(:form list) <=_c (:A)` MP_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:num)` THEN
    ASM_REWRITE_TAC[GSYM INFINITE_CARD_LE; GSYM COUNTABLE_ALT] THEN
    ASM_SIMP_TAC[COUNTABLE_LIST; COUNTABLE_FORM];
    REWRITE_TAC[le_c; IN_UNIV]];
   ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
    [`IMAGE (f:form list->A) W1`;
     `\x y:A. ?a b:form list.
        a IN W1 /\ b IN W1 /\ x = f a /\ y = f b /\ R1 a b`;
     `\a:string w:A. ?x:form list. w = f x /\ V1 a x`;
     `f (w1:form list):A`] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[ITF] THEN
   CONJ_TAC THENL [HYP SET_TAC "w1" []; ALL_TAC] THEN
   CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[ITF; FINITE_IMAGE]; ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN
    HYP_TAC "itf1: _ _ _ irrefl _" (REWRITE_RULE[ITF]) THEN
    HYP MESON_TAC " irrefl inj" [];
    ALL_TAC] THEN
   REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
   HYP_TAC "itf1: _ _ _ _ trans" (REWRITE_RULE[ITF]) THEN
   HYP MESON_TAC " trans inj" [];
   ALL_TAC] THEN
  REWRITE_TAC[BISIMILAR] THEN
  EXISTS_TAC `\w1:form list w2:A. w1 IN W1 /\ w2 = f w1` THEN
  ASM_REWRITE_TAC[BISIMIMULATION] THEN REMOVE_THEN "w1" (K ALL_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  CONJ_TAC THENL [HYP MESON_TAC "inj" []; ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
   ASM_MESON_TAC[ITF];
   ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Simple decision procedure for GL.                                         *)
(* ------------------------------------------------------------------------- *)

let GL_TAC : tactic =
  MATCH_MP_TAC COMPLETENESS_THEOREM THEN
  REWRITE_TAC[valid; FORALL_PAIR_THM; holds_in; holds;
              ITF; GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[];;

let GL_RULE tm =
  prove(tm, REPEAT GEN_TAC THEN GL_TAC);;

GL_RULE `!p q r. |-- (p && q && r --> p && r)`;;
GL_RULE `!p. |-- (Box p --> Box (Box p))`;;
GL_RULE `!p q. |-- (Box (p --> q) && Box p --> Box q)`;;
(* GL_RULE `!p. |-- (Box (Box p --> p) --> Box p)`;; *)
(* GL_RULE `|-- (Box (Box False --> False) --> Box False)`;; *)

(* GL_box_iff_th *)
GL_RULE `!p q. |-- (Box (p <-> q) --> (Box p <-> Box q))`;;

(* ------------------------------------------------------------------------- *)
(* Invariance by permutation.                                                *)
(* ------------------------------------------------------------------------- *)

let SET_OF_LIST_EQ_IMP_MEM = prove
 (`!l m x:A. set_of_list l = set_of_list m /\ MEM x l
             ==> MEM x m`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IN_SET_OF_LIST] THEN MESON_TAC[]);;

let SET_OF_LIST_EQ_CONJLIST = prove
 (`!X Y. set_of_list X = set_of_list Y
         ==> |-- (CONJLIST X --> CONJLIST Y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONJLIST_IMP THEN
  INTRO_TAC "!p; p" THEN EXISTS_TAC `p:form` THEN
  REWRITE_TAC[GL_imp_refl_th] THEN ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

let SET_OF_LIST_EQ_CONJLIST_EQ = prove
 (`!X Y. set_of_list X = set_of_list Y
         ==> |-- (CONJLIST X <-> CONJLIST Y)`,
  REWRITE_TAC[GL_iff_def] THEN MESON_TAC[SET_OF_LIST_EQ_CONJLIST]);;

let SET_OF_LIST_EQ_CONSISTENT = prove
 (`!X Y. set_of_list X = set_of_list Y /\ CONSISTENT X
         ==> CONSISTENT Y`,
  REWRITE_TAC[CONSISTENT] THEN INTRO_TAC "!X Y; eq hp; p" THEN
  REMOVE_THEN "hp" MP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC GL_modusponens THEN EXISTS_TAC `Not (CONJLIST Y)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC GL_contrapos THEN
  MATCH_MP_TAC SET_OF_LIST_EQ_CONJLIST THEN ASM_REWRITE_TAC[]);;

let SET_OF_LIST_EQ_MAXIMAL_CONSISTENT = prove
 (`!p X Y. set_of_list X = set_of_list Y /\ NOREPETITION Y /\
           MAXIMAL_CONSISTENT p X
           ==> MAXIMAL_CONSISTENT p Y`,
  REWRITE_TAC[MAXIMAL_CONSISTENT] THEN REPEAT STRIP_TAC THENL
  [ASM_MESON_TAC[SET_OF_LIST_EQ_CONSISTENT];
   ASM_REWRITE_TAC[];
   ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]]);;

let SET_OF_LIST_EQ_GL_STANDARD_REL = prove
 (`!p u1 u2 w1 w2.
     set_of_list u1 = set_of_list w1 /\ NOREPETITION w1 /\
     set_of_list u2 = set_of_list w2 /\ NOREPETITION w2 /\
     GL_STANDARD_REL p u1 u2
     ==> GL_STANDARD_REL p w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GL_STANDARD_REL] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  ASM_MESON_TAC[SET_OF_LIST_EQ_IMP_MEM]);;

(* ------------------------------------------------------------------------- *)
(* Countermodel using set of formulae (instead of lists of formulae).        *)
(* ------------------------------------------------------------------------- *)

let GL_STDWORLDS_RULES,GL_STDWORLDS_INDUCT,GL_STDWORLDS_CASES =
  new_inductive_set
  `!M. MAXIMAL_CONSISTENT p M /\
       (!q. MEM q M ==> q SUBSENTENCE p)
       ==> set_of_list M IN GL_STDWORLDS p`;;

let GL_STDREL_RULES,GL_STDREL_INDUCT,GL_STDREL_CASES = new_inductive_definition
  `!w1 w2. GL_STANDARD_REL p w1 w2
           ==> GL_STDREL p (set_of_list w1) (set_of_list w2)`;;

let GL_STDREL_IMP_GL_STDWORLDS = prove
 (`!p w1 w2. GL_STDREL p w1 w2 ==>
             w1 IN GL_STDWORLDS p /\
             w2 IN GL_STDWORLDS p`,
  GEN_TAC THEN MATCH_MP_TAC GL_STDREL_INDUCT THEN
  REWRITE_TAC[GL_STANDARD_REL] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;

let BISIMIMULATION_SET_OF_LIST = prove
 (`!p. BISIMIMULATION
       (
         {M | MAXIMAL_CONSISTENT p M /\ (!q. MEM q M ==> q SUBSENTENCE p)},
         GL_STANDARD_REL p,
         (\a w. Atom a SUBFORMULA p /\ MEM (Atom a) w)
       )
       (GL_STDWORLDS p,
        GL_STDREL p,
        (\a w. Atom a SUBFORMULA p /\ Atom a IN w))
       (\w1 w2.
          MAXIMAL_CONSISTENT p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN GL_STDWORLDS p /\
          set_of_list w1 = w2)`,
  GEN_TAC THEN REWRITE_TAC[BISIMIMULATION] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [GEN_TAC THEN FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC[IN_SET_OF_LIST];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![u1]; w1u1" THEN EXISTS_TAC `set_of_list u1:form->bool` THEN
   HYP_TAC "w1u1 -> hp" (REWRITE_RULE[GL_STANDARD_REL]) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN MATCH_MP_TAC GL_STDREL_RULES THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "![u2]; w2u2" THEN EXISTS_TAC `list_of_set u2:form list` THEN
  REWRITE_TAC[CONJ_ACI] THEN
  HYP_TAC "w2u2 -> @x2 y2. x2 y2 x2y2" (REWRITE_RULE[GL_STDREL_CASES]) THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  SIMP_TAC[SET_OF_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[MEM_LIST_OF_SET; FINITE_SET_OF_LIST; IN_SET_OF_LIST] THEN
  CONJ_TAC THENL
  [HYP_TAC "x2y2 -> hp" (REWRITE_RULE[GL_STANDARD_REL]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC SET_OF_LIST_EQ_GL_STANDARD_REL THEN
   EXISTS_TAC `x2:form list` THEN EXISTS_TAC `y2:form list` THEN
   ASM_REWRITE_TAC[] THEN
   SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
   ASM_MESON_TAC[MAXIMAL_CONSISTENT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[GL_STDREL_IMP_GL_STDWORLDS]; ALL_TAC] THEN
  MATCH_MP_TAC SET_OF_LIST_EQ_MAXIMAL_CONSISTENT THEN
  EXISTS_TAC `y2:form list` THEN
  SIMP_TAC[NOREPETITION_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  SIMP_TAC[EXTENSION; IN_SET_OF_LIST; MEM_LIST_OF_SET; FINITE_SET_OF_LIST] THEN
  ASM_MESON_TAC[GL_STANDARD_REL]);;

let GL_COUNTERMODEL_FINITE_SETS = prove
 (`!p. ~(|-- p) ==> ~holds_in (GL_STDWORLDS p, GL_STDREL p) p`,
  INTRO_TAC "!p; p" THEN
  DESTRUCT_TAC "@M. max mem subf"
    (MATCH_MP NONEMPTY_MAXIMAL_CONSISTENT (ASSUME `~ |-- p`)) THEN
  REWRITE_TAC[holds_in; NOT_FORALL_THM; NOT_IMP] THEN
  ASSUM_LIST (LABEL_TAC "hp" o MATCH_MP GL_COUNTERMODEL o
                end_itlist CONJ o rev) THEN
  EXISTS_TAC `\a w. Atom a SUBFORMULA p /\ Atom a IN w` THEN
  EXISTS_TAC `set_of_list M:form->bool` THEN CONJ_TAC THENL
  [MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "hp" MP_TAC THEN
  MATCH_MP_TAC (MESON[] `(p <=> q) ==> (~p ==> ~q)`) THEN
  MATCH_MP_TAC BISIMIMULATION_HOLDS THEN
  EXISTS_TAC
      `(\w1 w2.
          MAXIMAL_CONSISTENT p w1 /\
          (!q. MEM q w1 ==> q SUBSENTENCE p) /\
          w2 IN GL_STDWORLDS p /\
          set_of_list w1 = w2)` THEN
  ASM_REWRITE_TAC[BISIMIMULATION_SET_OF_LIST] THEN
  MATCH_MP_TAC GL_STDWORLDS_RULES THEN ASM_REWRITE_TAC[]);;
