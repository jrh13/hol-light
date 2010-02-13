(*-------------------------------------------------------------------------*)
(*
   File:         mk_unless.ml
   Description: 

   This file defines the theorems for the UNLESS definition.

   Author:       (c) Copyright 1989-2008 by Flemming Andersen
   Date:         June 29, 1989
   Last Update:  December 30, 2007
*)
(*-------------------------------------------------------------------------*)


(*-------------------------------------------------------------------------*)
(* The definition of UNLESS is based on the definition:

      p UNLESS q in Pr = <!s in Pr: {p /\ ~q} s {p \/ q}>

  where p and q are state dependent first order logic predicates or all
  s in the program Pr are conditionally enabled statements transforming
  a state into a new state.

  To define UNLESS as a relation UNLESS_STMT to be satisfied for a finite
  number of program statements, we define the UNLESS_STMT to be fulfilled as
  a separate HOARE tripple relation between pre- or post predicates to be
  satisfied for state transitions. The pre- or post predicates of the
  UNLESS_STMT relation must be satisfiable for all states possible in the
  finite state space of the program.
*)

let TL_FIX = 100;;

let UNLESS_STMT = new_infix_definition
  ("UNLESS_STMT", "<=>",
   `UNLESS_STMT (p:'a->bool) q st =
      \s:'a. (p s /\ ~q s) ==> (p (st s) \/ q (st s))`, TL_FIX);;

(*
  Since a program is defined as a set (list) of statements, we
  recursively define the UNLESS relation itself using the UNLESS_STMT
  relation to be satisfied for every statement in the program.

  As the bottom of the recursion we choose the empty program always to be
  satisfied. For every statement in the program the UNLESS_STMT relation
  must be satisfied in all possible states.
*)

let UNLESS_term =
  (`(!p q. UNLESS p q  []                   <=> T) /\
    (!p q. UNLESS p q (CONS (st:'a->'a) Pr) <=>
     ((!s:'a. (p UNLESS_STMT q) st s) /\ (UNLESS p q Pr)))`);;
let UNLESS = new_recursive_definition list_RECURSION UNLESS_term;;
parse_as_infix ( "UNLESS", (TL_FIX, "right") );;

let STABLE_STMT = new_infix_definition
  ("STABLE_STMT", "<=>",
   `STABLE_STMT (p:'a->bool) st = \s:'a. p s ==> p (st s)`, TL_FIX);;

(*
* The state predicate STABLE is a special case of UNLESS.
*
*       stable p in Pr = p unless false in Pr
*)
let STABLE = new_infix_definition
  ("STABLE", "<=>", `STABLE (p:'a->bool) Pr = (p UNLESS False) Pr`, TL_FIX);;

(*
*  The state predicate INVARIANT is a special case of UNLESS too.
*  However invariant is dependent of a program /\* its initial state.
*
*       invariant P in (initial condition, Pr) =
*           (initial condition ==> p) /\ (p stable in Pr)
*)
let INVARIANT = new_infix_definition
  ("INVARIANT", "<=>",
   `INVARIANT p (p0, Pr) = ((!s:'a. p0 s ==> p s) /\ (p STABLE Pr))`, TL_FIX);;

(************************************************************************
*									*
* Lemmas used in the UNLESS Theory					*
*									*
************************************************************************)

let s = `s:'a`;;
let p = `p:'a->bool`;;
let q = `q:'a->bool`;;
let r = `r:'a->bool`;;
let P = `P:num->'a->bool`;;

let IMP_IMP_CONJIMP_lemma = TAC_PROOF
  (([],
   (`!p q ps qs p' q' p's q's.
        (p /\ ~q ==> ps \/ qs) ==> (p' /\ ~q' ==> p's \/ q's) ==>
          (p /\ p' /\ (~p \/ ~q') /\ (~p' \/ ~q) /\ (~q \/ ~q') ==>
                ps /\ p's \/ ps /\ q's \/ p's /\ qs \/ qs /\ q's)`)),
   REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);;

let NOT_NOT_OR_lemma = TAC_PROOF
  (([],
   (`!t1 t2 t3. t1 \/ t2 \/ t3 <=> ~(~t1 /\ ~t2) \/ t3`)),
   REWRITE_TAC [NOT_CLAUSES; DE_MORGAN_THM; (SYM (SPEC_ALL DISJ_ASSOC))]);;

let CONJ_IMPLY_THM = TAC_PROOF
  (([],
   (`!p p' q q'.
     ((p \/ p') /\ (p \/ ~q') /\ (p' \/ ~q) /\ (~q \/ ~q')) =
     ((p /\ ~q) \/ (p' /\ ~q'))`)),
    REPEAT GEN_TAC THEN
    EQ_TAC THEN
    REPEAT STRIP_TAC THEN REPEAT (ASM_REWRITE_TAC []));;

(************************************************************************
*									*
* Theorems about UNLESS_STMT						*
*									*
************************************************************************)

(*
 *  The reflexivity theorem:
 *
 *               p unless_stmt P in Prog
 *)
let UNLESS_STMT_thm0 = prove_thm
  ("UNLESS_STMT_thm0",
    `!p st (s:'a). (p UNLESS_STMT p)st s`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [UNLESS_STMT] THEN
    REWRITE_TAC [BETA_CONV (`(\s:'a. p s /\ ~(p s) ==> p (st s))s`)] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC);;

(*
 *  Theorem:
 *               p unless_stmt Q in stmt, q ==> r
 *              ------------------------------
 *                   p unless_stmt r in stmt
 *)

let UNLESS_STMT_thm1 = prove_thm
  ("UNLESS_STMT_thm1",
   `!(p:'a->bool) q r st.
      ((!s. (p UNLESS_STMT q) st s) /\ (!s. (q s) ==> (r s))) ==>
       (!s. (p UNLESS_STMT r) st s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS_STMT] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (REWRITE_RULE [ASSUME `~r (s:'a)`]
     ( CONTRAPOS (SPEC `s:'a` (ASSUME `!s:'a. q s ==> r s`)))) THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [ASSUME `(p:'a->bool) s`; ASSUME `~q (s:'a)`]
     (SPEC `s:'a` (ASSUME `!s:'a. p s /\ ~q s ==> p (st s) \/ q (st s)`))) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [ASSUME `(q:'a->bool) ((st:'a->'a) s)`]
     (SPEC `(st:'a->'a) s` (ASSUME `!s:'a. q s ==> r s`))) THEN
   ASM_REWRITE_TAC []);;

(*
   Theorem:
                p unless_stmt Q in st, p' unless_stmt q' in st
               ------------------------------------------------
                        p\/p' unless_stmt q\/q' in st
*)
let UNLESS_STMT_thm2 = prove_thm
  ("UNLESS_STMT_thm2",
   `!p q p' q' (st:'a->'a).
    ((!s. (p UNLESS_STMT q) st s) /\ (!s. (p' UNLESS_STMT q') st s)) ==>
     (!s. ((p \/* p') UNLESS_STMT (q \/* q')) st s)`,
    REWRITE_TAC [UNLESS_STMT;OR_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC));
                 (SYM (SPEC_ALL DISJ_ASSOC)); NOT_CLAUSES; DE_MORGAN_THM] THEN
    (REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []));;

(*
  Conjunction Theorem:
               p unless_stmt Q in stmt, p' unless_stmt q' in stmt
     ------------------------------------------------------------------
     (p /\ p') unless_stmt (p /\ q') \/ (p' /\ q) \/ (q /\ q') in stmt
*)
let UNLESS_STMT_thm3 = prove_thm
  ("UNLESS_STMT_thm3",
   `!p q p' q' (st:'a->'a).
     ((!s. (p UNLESS_STMT q) st s) /\ (!s. (p' UNLESS_STMT q') st s)) ==>
      (!s. ((p /\* p') UNLESS_STMT
           (((p /\* q') \/* (p' /\* q)) \/* (q /\* q'))) st s)`,
    PURE_REWRITE_TAC [UNLESS_STMT;AND_def;OR_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC));
                 (SYM (SPEC_ALL DISJ_ASSOC)); NOT_CLAUSES; DE_MORGAN_THM] THEN
    STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    DISCH_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    ASSUME_TAC (CONJUNCT1 (ASSUME
       (`(!s. p s /\ ~q s ==> p ((st:'a->'a) s) \/ q (st s)) /\
           (!s. p' s /\ ~q' s ==> p'((st:'a->'a) s) \/ q'(st s))`))) THEN
    ASSUME_TAC (CONJUNCT2 (ASSUME
       (`(!s. p s /\ ~q s ==> p ((st:'a->'a) s) \/ q (st s)) /\
           (!s. p' s /\ ~q' s ==> p'((st:'a->'a) s) \/ q'(st s))`))) THEN
    STRIP_ASSUME_TAC (SPEC_ALL (ASSUME
       (`(!s. p s /\ ~q s ==> p ((st:'a->'a) s) \/ q (st s))`))) THEN
    STRIP_ASSUME_TAC (SPEC_ALL (ASSUME
       (`(!s. p' s /\ ~q' s ==> p'((st:'a->'a) s) \/ q'(st s))`))) THEN
    ASSUME_TAC (UNDISCH_ALL
     (SPEC (`(q':'a->bool) ((st:'a->'a) s)`)
      (SPEC (`(p':'a->bool) ((st:'a->'a) s)`)
       (SPEC (`(q':'a->bool) s`)
        (SPEC (`(p':'a->bool) s`)
         (SPEC (`(q:'a->bool) ((st:'a->'a) s)`)
          (SPEC (`(p:'a->bool) ((st:'a->'a) s)`)
           (SPEC (`(q:'a->bool) s`)
            (SPEC (`(p:'a->bool) s`)
             IMP_IMP_CONJIMP_lemma))))))))) THEN
    ASM_REWRITE_TAC []);;

(*
  Disjunction Theorem:
               p unless_stmt Q in stmt, p' unless_stmt q' in stmt
     ------------------------------------------------------------------
     (p \/ p') unless_stmt (~p /\ q') \/ (~p' /\ q) \/ (q /\ q') in stmt
*)
let UNLESS_STMT_thm4 = prove_thm
  ("UNLESS_STMT_thm4",
   `!p q p' q' (st:'a->'a).
     ((!s. (p UNLESS_STMT q) st s) /\ (!s. (p' UNLESS_STMT q') st s)) ==>
      (!s. ((p \/* p') UNLESS_STMT
            ((((Not p) /\* q') \/* ((Not p') /\* q)) \/* (q /\* q')))
           st s)`,
    REPEAT GEN_TAC THEN
    PURE_REWRITE_TAC [UNLESS_STMT;AND_def;OR_def;NOT_def1] THEN
    MESON_TAC []);;

let UNLESS_STMT_thm5_lemma1 = TAC_PROOF
  (([],
   `!p q r. (p ==> q) ==> (p \/ r ==> q \/ r)`),
   REPEAT STRIP_TAC THENL
     [RES_TAC THEN ASM_REWRITE_TAC []
     ;ASM_REWRITE_TAC []]);;

let UNLESS_STMT_thm5_lemma2 = TAC_PROOF
  (([],
   `!(P:num->('a->bool)) q s. ((?n. P n s) \/ q s) = (?n. P n s \/ q s)`),
   REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
    [ EXISTS_TAC (`n:num`) THEN
      ASM_REWRITE_TAC []
    ; EXISTS_TAC (`n:num`) THEN
      ASM_REWRITE_TAC []
    ; DISJ1_TAC THEN
      EXISTS_TAC (`n:num`) THEN
      ASM_REWRITE_TAC []
    ; DISJ2_TAC THEN
      ASM_REWRITE_TAC []
    ]);;

let UNLESS_STMT_thm5 = prove_thm
  ("UNLESS_STMT_thm5",
   `!(P:num->('a->bool)) q st.
          (!m. (!s. ((P m) UNLESS_STMT q)st s)) ==>
               (!s. ((\s. ?n. P n s) UNLESS_STMT q)st s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS_STMT] THEN
   BETA_TAC THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [UNLESS_STMT_thm5_lemma2] THEN
   EXISTS_TAC (`n:num`) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC []);;

let UNLESS_STMT_thm6 = prove_thm
  ("UNLESS_STMT_thm6",
   `!(p:'a->bool) q r (st:'a->'a).
      (!s. (p UNLESS_STMT q) st s) ==>
         (!s. ((p \/* r) UNLESS_STMT (q \/* r)) st s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [UNLESS_STMT; OR_def] THEN
   MESON_TAC []);;

(*
 Theorems about UNLESS
*)

(*
  The reflexivity theorem:
               p unless p in Prog
*)

let UNLESS_thm1 = prove_thm
  ("UNLESS_thm1",
   `!(p:'a->bool) Pr. (p UNLESS p) Pr`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   PURE_REWRITE_TAC [UNLESS] THEN
   ASM_REWRITE_TAC [] THEN
   PURE_REWRITE_TAC [UNLESS_STMT] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

(*
*  The anti reflexivity theorem:
*
*               p unless ~p in Prog
*)
let UNLESS_thm2 = prove_thm
  ("UNLESS_thm2",
   (`!(p:'a->bool) Pr. (p UNLESS (Not p)) Pr`),
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   PURE_REWRITE_TAC [UNLESS] THEN
   ASM_REWRITE_TAC [] THEN
   PURE_REWRITE_TAC [UNLESS_STMT;NOT_def1] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [EXCLUDED_MIDDLE]);;

(*
  The unless implies theorem:
               p unless q in Pr, q ==> r
              ---------------------------
                   p unless r in Pr
*)
let UNLESS_thm3 = prove_thm
  ("UNLESS_thm3",
   `!(p:'a->bool) q r Pr.
      (((p UNLESS q) Pr) /\ (!s. (q s) ==> (r s))) ==> ((p UNLESS r) Pr)`,
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [UNLESS] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    RES_TAC THEN
    ASM_REWRITE_TAC [] THEN
    IMP_RES_TAC UNLESS_STMT_thm1);;

(*
  Conjunction Theorem:
               p unless q in Pr, p' unless q' in Pr
     -----------------------------------------------------------
     (p /\ p') unless (p /\ q') \/ (p' /\ q) \/ (q /\ q') in Pr
*)
let UNLESS_thm4 = prove_thm
  ("UNLESS_thm4",
   `!(p:'a->bool) q p' q' Pr.
      (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
        (((p /\* p') UNLESS
         (((p /\* q') \/* (p' /\* q)) \/* (q /\* q'))) Pr)`,
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [UNLESS] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    RES_TAC THEN
    ASM_REWRITE_TAC [] THEN
    IMP_RES_TAC UNLESS_STMT_thm3);;

(*
  Disjunction Theorem:
               p unless q in Pr, p' unless q' in Pr
     -------------------------------------------------------------
     (p \/ p') unless (~p /\ q') \/ (~p' /\ q) \/ (q /\ q') in Pr
*)
let UNLESS_thm5 = prove_thm
  ("UNLESS_thm5",
   `!(p:'a->bool) q p' q' Pr.
        (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr))
      ==>
        (((p \/* p') UNLESS
	  ((((Not p) /\* q') \/* ((Not p') /\* q)) \/* (q /\* q'))) Pr)`,
    GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
    LIST_INDUCT_TAC THEN
    REWRITE_TAC [UNLESS] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    RES_TAC THEN
    ASM_REWRITE_TAC [] THEN
    IMP_RES_TAC UNLESS_STMT_thm4);;

(*
  Simple Conjunction Theorem:
               p unless q in Pr, p' unless q' in Pr
              -------------------------------------------
                    (p /\ p') unless (q \/ q') in Pr
*)
let UNLESS_thm6 = prove_thm
  ("UNLESS_thm6",
   `!(p:'a->bool) q p' q' Pr.
      (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
         (((p /\* p') UNLESS (q \/* q')) Pr)`,
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`((p:'a->bool) UNLESS q)Pr`);
          (`((p':'a->bool) UNLESS q')Pr`)]
           AND_INTRO_THM)) THEN
    ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm4)) THEN
    ASSUME_TAC (SPECL [(`p:'a->bool`); (`q:'a->bool`);
                       (`p':'a->bool`); (`q':'a->bool`)]
                       IMPLY_WEAK_lemma1) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
       [(`(((p:'a->bool) /\* p') UNLESS
	     (((p /\* q') \/* (p' /\* q)) \/* (q /\* q')))Pr`);
        (`!s. ((((p:'a->bool) /\* q') \/* (p' /\* q)) \/* (q /\* q'))s ==>
                (q \/* q')s`)]
        AND_INTRO_THM)) THEN
    ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
         [(`(p:'a->bool) /\* p'`);
          (`((((p:'a->bool) /\* q') \/* (p' /\* q)) \/* (q /\* q'))`);
          (`(q:'a->bool) \/* q'`); (`Pr:('a->'a)list`)]
          UNLESS_thm3)]);;

(*
  Simple Disjunction Theorem:
               p unless Q in Pr, p' unless q' in Pr
             ---------------------------------------
                 (p \/ p') unless (q \/ q') in Pr
*)
let UNLESS_thm7 = prove_thm
  ("UNLESS_thm7",
   `!(p:'a->bool) q p' q' Pr.
         (((p UNLESS q) Pr) /\ ((p' UNLESS q') Pr)) ==>
             (((p \/* p') UNLESS (q \/* q')) Pr)`,
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
        [(`((p:'a->bool) UNLESS q)Pr`); (`((p':'a->bool) UNLESS q')Pr`)]
         AND_INTRO_THM)) THEN
    ASSUME_TAC (UNDISCH_ALL (SPEC_ALL UNLESS_thm5)) THEN
    ASSUME_TAC (SPECL [(`p:'a->bool`);  (`q:'a->bool`);
                       (`p':'a->bool`); (`q':'a->bool`)]
                       IMPLY_WEAK_lemma2) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`(((p:'a->bool) \/* p') UNLESS
               ((((Not p) /\* q') \/* ((Not p') /\* q)) \/* (q /\* q')))
               Pr`);
          (`!s. ((((Not (p:'a->bool)) /\* q') \/* ((Not p') /\* q)) \/*
                    (q /\* q'))s ==> (q \/* q')s`)]
          AND_INTRO_THM)) THEN
    STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
         [`(p:'a->bool) \/* p'`;
          `(((Not (p:'a->bool)) /\* q') \/* ((Not p') /\* q)) \/* (q /\* q')`;
          `(q:'a->bool) \/* q'`;
          `Pr:('a->'a)list`]
           UNLESS_thm3)));;

(*
  Cancellation Theorem:
               p unless Q in Pr, q unless r in Pr
              ------------------------------------
                    (p \/ q) unless r in Pr
*)
let UNLESS_thm8 = prove_thm
  ("UNLESS_thm8",
   `!(p:'a->bool) q r Pr.
     (((p UNLESS q) Pr) /\ ((q UNLESS r) Pr)) ==>
     (((p \/* q) UNLESS r) Pr)`,
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         [`((p:'a->bool) UNLESS q)Pr`; `((q:'a->bool) UNLESS r)Pr`]
          AND_INTRO_THM)) THEN
    ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`p:'a->bool`); (`q:'a->bool`);
          (`q:'a->bool`); (`r:'a->bool`)]
          UNLESS_thm5))) THEN
    ASSUME_TAC (SPECL
         [(`p:'a->bool`); (`q:'a->bool`); (`r:'a->bool`)]
          IMPLY_WEAK_lemma3) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`(((p:'a->bool) \/* q) UNLESS
           ((((Not p) /\* r) \/* ((Not q) /\* q)) \/* (q /\* r))) Pr`);
          (`!s:'a. ((((Not p) /\* r) \/* ((Not q) /\* q)) \/*
                      (q /\* r))s ==> r s`)]
          AND_INTRO_THM)) THEN
    STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`((p:'a->bool) \/* q)`);
          (`((((Not (p:'a->bool)) /\* r) \/* ((Not q) /\* q)) \/*
               (q /\* r))`);
          (`r:'a->bool`)]
          UNLESS_thm3))));;

(*
  Corollaries
*)
let UNLESS_cor1 = prove_thm
  ("UNLESS_cor1",
   `!(p:'a->bool) q Pr. (!s. p s ==> q s) ==> ((p UNLESS q) Pr)`,
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
      [`((p:'a->bool) UNLESS p)Pr`; `!s:'a. p s ==> q s`]
       AND_INTRO_THM)) THEN
    ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
      [(`p:'a->bool`); (`p:'a->bool`); (`q:'a->bool`);
       (`Pr:('a->'a)list`)] UNLESS_thm3)]);;

let UNLESS_cor2 = prove_thm
  ("UNLESS_cor2",
   (`!(p:'a->bool) q Pr. (!s. (Not p)s ==> q s) ==> ((p UNLESS q) Pr)`),
    REPEAT STRIP_TAC THEN
    ASSUME_TAC (SPEC_ALL UNLESS_thm2) THEN
    ASSUME_TAC (UNDISCH_ALL (SPECL
      [(`((p:'a->bool) UNLESS (Not p))Pr`);
       (`!s:'a. (Not p) s ==> q s`)]
       AND_INTRO_THM)) THEN
    ASM_REWRITE_TAC [UNDISCH_ALL (SPECL
       [(`p:'a->bool`); (`Not (p:'a->bool)`);
        (`q:'a->bool`); (`Pr:('a->'a)list`)]
        UNLESS_thm3)]);;

let UNLESS_cor3a = TAC_PROOF
  (([],
   (`!(p:'a->bool) q r Pr.
          (p UNLESS (q \/* r)) Pr ==>
          ((p /\* (Not q)) UNLESS (q \/* r)) Pr`)),
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPECL [(`Not (q:'a->bool)`);
                      (`Pr:('a->'a)list`)] UNLESS_thm2) THEN
   UNDISCH_TAC (`((Not (q:'a->bool)) UNLESS (Not(Not q)))Pr`) THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((p:'a->bool) UNLESS (q \/* r))Pr`);
      (`((Not (q:'a->bool)) UNLESS q)Pr`)]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`p:'a->bool`); (`((q:'a->bool) \/* r)`);
      (`(Not (q:'a->bool))`); (`q:'a->bool`); (`Pr:('a->'a)list`)]
      UNLESS_thm6)) THEN
   UNDISCH_TAC (`(((p:'a->bool) /\* (Not q)) UNLESS
                    ((q \/* r) \/* q))Pr`) THEN
   PURE_ONCE_REWRITE_TAC
      [SPECL [(`(q:'a->bool) \/* r`);
              (`q:'a->bool`)] OR_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL OR_ASSOC_lemma))] THEN
   REWRITE_TAC [OR_OR_lemma]);;

let UNLESS_cor3b = TAC_PROOF
  (([],
   (`!(p:'a->bool) q r Pr.
      ((p /\* (Not q)) UNLESS (q \/* r)) Pr ==> (p UNLESS (q \/* r)) Pr`)),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPECL [(`(p:'a->bool) /\* q`);
                      (`Pr:('a->'a)list`)] UNLESS_thm1) THEN
   ASSUME_TAC (SPECL [(`p:'a->bool`); (`q:'a->bool`)]
                 AND_IMPLY_WEAK_lemma) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`(((p:'a->bool) /\* q) UNLESS (p /\* q))Pr`);
      (`!s:'a. (p /\* q)s ==> q s`)]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`(p:'a->bool) /\* q`); (`(p:'a->bool) /\* q`);
      (`q:'a->bool`); (`Pr:('a->'a)list`)]
      UNLESS_thm3)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`(((p:'a->bool) /\* (Not q)) UNLESS (q \/* r))Pr`);
      (`(((p:'a->bool) /\* q) UNLESS q)Pr`)]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((p:'a->bool) /\* (Not q))`); (`((q:'a->bool) \/* r)`);
      (`((p:'a->bool) /\* q)`); (`q:'a->bool`); (`Pr:('a->'a)list`)]
      UNLESS_thm7)) THEN
   UNDISCH_TAC
   (`((((p:'a->bool) /\* (Not q)) \/* (p /\* q)) UNLESS
        ((q \/* r) \/* q))Pr`) THEN
   REWRITE_TAC [AND_COMPL_OR_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL (OR_ASSOC_lemma)))] THEN
   REWRITE_TAC [OR_OR_lemma] THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor3 = prove_thm
  ("UNLESS_cor3",
   (`!(p:'a->bool) q r Pr.
         ((p /\* (Not q)) UNLESS (q \/* r)) Pr = (p UNLESS (q \/* r)) Pr`),
   REWRITE_TAC [IMP_ANTISYM_RULE
                 (SPEC_ALL UNLESS_cor3b) (SPEC_ALL UNLESS_cor3a)]);;

let UNLESS_cor4 = prove_thm
  ("UNLESS_cor4",
   (`!(p:'a->bool) q r Pr.
               ((p \/* q) UNLESS r) Pr ==> (p UNLESS (q \/* r)) Pr`),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (SPEC_ALL ((SPEC (`Not (q:'a->bool)`) UNLESS_thm2))) THEN
   UNDISCH_TAC (`((Not (q:'a->bool)) UNLESS (Not(Not q)))Pr`) THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`(((p:'a->bool) \/* q) UNLESS r)Pr`);
          (`((Not (q:'a->bool)) UNLESS q)Pr`)]
          AND_INTRO_THM))) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`((p:'a->bool) \/* q)`); (`r:'a->bool`);
          (`(Not (q:'a->bool))`); (`q:'a->bool`)]
          UNLESS_thm6))) THEN
   UNDISCH_TAC (`((((p:'a->bool) \/* q) /\* (Not q)) UNLESS
                    (r \/* q))Pr`) THEN
   REWRITE_TAC [OR_NOT_AND_lemma] THEN
   PURE_ONCE_REWRITE_TAC [SPECL [(`r:'a->bool`); (`q:'a->bool`)]
       OR_COMM_lemma] THEN
   REWRITE_TAC [UNLESS_cor3] THEN
   STRIP_TAC THEN
   PURE_ONCE_REWRITE_TAC [SPECL [(`r:'a->bool`); (`q:'a->bool`)]
       OR_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor5 = prove_thm
  ("UNLESS_cor5",
   (`!(p:'a->bool) Pr. (p UNLESS True) Pr`),
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm2) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`((p:'a->bool) UNLESS p)Pr`);
          (`((p:'a->bool) UNLESS (Not p))Pr`)]
          AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`p:'a->bool`); (`p:'a->bool`);
          (`p:'a->bool`); (`(Not (p:'a->bool))`)]
          UNLESS_thm6))) THEN
   UNDISCH_TAC (`(((p:'a->bool) /\* p) UNLESS (p \/* (Not p)))Pr`) THEN
   REWRITE_TAC [AND_AND_lemma;P_OR_NOT_P_lemma]);;

let UNLESS_cor6 = prove_thm
  ("UNLESS_cor6",
   (`!(p:'a->bool) Pr. (True UNLESS p) Pr`),
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
   ASSUME_TAC (SPEC_ALL (SPEC (`(Not (p:'a->bool))`) UNLESS_thm2)) THEN
   UNDISCH_TAC (`((Not (p:'a->bool)) UNLESS (Not(Not p)))Pr`) THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`((Not (p:'a->bool)) UNLESS p)Pr`);
	  (`((p:'a->bool) UNLESS p)Pr`)]
          AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`(Not (p:'a->bool))`); (`p:'a->bool`);
	  (`p:'a->bool`); (`p:'a->bool`)]
          UNLESS_thm7))) THEN
   UNDISCH_TAC (`(((Not (p:'a->bool)) \/* p) UNLESS (p \/* p))Pr`) THEN
   PURE_ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_OR_lemma;P_OR_NOT_P_lemma]);;

let UNLESS_cor7 = prove_thm
  ("UNLESS_cor7",
   (`!(p:'a->bool) Pr. (False UNLESS p) Pr`),
   REPEAT GEN_TAC THEN
   ASSUME_TAC (SPEC_ALL UNLESS_thm1) THEN
   ASSUME_TAC (SPEC_ALL (SPEC (`(Not (p:'a->bool))`) UNLESS_thm2)) THEN
   UNDISCH_TAC (`((Not (p:'a->bool)) UNLESS (Not(Not p)))Pr`) THEN
   REWRITE_TAC [NOT_NOT_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`((Not (p:'a->bool)) UNLESS p)Pr`);
	  (`((p:'a->bool) UNLESS p)Pr`)]
          AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
         [(`(Not (p:'a->bool))`); (`p:'a->bool`);
	  (`p:'a->bool`); (`p:'a->bool`)]
          UNLESS_thm6))) THEN
   UNDISCH_TAC (`(((Not (p:'a->bool)) /\* p) UNLESS (p \/* p))Pr`) THEN
   PURE_ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [OR_OR_lemma;P_AND_NOT_P_lemma]);;

let HeJiFeng_lemma1 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q p'.
     (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s) ==>
         (!s. p s /\ ~q s ==> p' s /\ ~q s)`)),
   REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);;

let HeJiFeng_lemma2 = TAC_PROOF
  (([],
   (`!(p:'a->bool) q p'.
     (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s) ==>
         (!s. p' s /\ ~q s ==> p s /\ ~q s)`)),
   REPEAT STRIP_TAC THEN RES_TAC THEN ASM_REWRITE_TAC []);;

let HeJiFeng_lemma = TAC_PROOF
  (([],
   (`!(p:'a->bool) q p'.
     (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s) ==>
         (!s. p s /\ ~q s <=> p' s /\ ~q s)`)),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [IMP_ANTISYM_RULE
     (SPEC_ALL (UNDISCH (UNDISCH (UNDISCH (SPEC_ALL HeJiFeng_lemma1)))))
     (SPEC_ALL (UNDISCH (UNDISCH (UNDISCH (SPEC_ALL HeJiFeng_lemma2)))))]);;

let HeJiFeng_lemma_f = MK_ABS (UNDISCH_ALL (SPEC_ALL HeJiFeng_lemma));;

let UNLESS_cor8 = prove_thm
  ("UNLESS_cor8",
   (`!(p:'a->bool) q p' Pr.
       (!s. p s /\ ~q s) ==> (!s. p' s) ==> (!s. p s \/ q s)
            ==> (((p  /\* (Not q)) UNLESS q) Pr =
                 ((p' /\* (Not q)) UNLESS q) Pr)`),
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [AND_def;OR_def;NOT_def1] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [HeJiFeng_lemma_f]);;

(*
  Corollary of generalized cancellation
*)
let UNLESS_cor9 = prove_thm
  ("UNLESS_cor9",
   (`!(p:'a->bool) q p' q' r r' Pr.
     ((p \/* p') UNLESS (q \/* r)) Pr /\ ((q \/* q') UNLESS (p \/* r')) Pr ==>
            ((p \/* p' \/* q \/* q') UNLESS ((p /\* q) \/* r \/* r')) Pr`),
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`((p:'a->bool) \/* p')`); (`((q:'a->bool) \/* r)`);
          (`((q:'a->bool) \/* q')`); (`((p:'a->bool) \/* r')`);
	  (`Pr:('a->'a)list`)]
          UNLESS_thm5)) THEN
   ASSUME_TAC (SPECL
        [(`p:'a->bool`); (`q:'a->bool`);
	 (`p':'a->bool`); (`q':'a->bool`);
         (`r:'a->bool`); (`r':'a->bool`)] IMPLY_WEAK_lemma4) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
      [(`((((p:'a->bool) \/* p') \/* (q \/* q')) UNLESS
        ((((Not(p \/* p')) /\* (p \/* r')) \/*
          ((Not(q \/* q')) /\* (q \/* r))) \/*
         ((q \/* r) /\* (p \/* r')))) Pr`);
       (`!s:'a. ((((Not(p \/* p')) /\* (p \/* r')) \/*
              ((Not(q \/* q')) /\* (q \/* r))) \/*
              ((q \/* r) /\* (p \/* r'))) s ==>
                  ((p /\* q) \/* (r \/* r'))s`)]
       AND_INTRO_THM)) THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPEC_ALL (SPECL
        [(`(((p:'a->bool) \/* p') \/* (q \/* q'))`);
         (`((((Not((p:'a->bool) \/* p')) /\* (p \/* r')) \/*
          ((Not(q \/* q')) /\* (q \/* r))) \/*
          ((q \/* r) /\* (p \/* r')))`);
         (`(((p:'a->bool) /\* q) \/* (r \/* r'))`)]
         UNLESS_thm3))) THEN
   UNDISCH_TAC (`((((p:'a->bool) \/* p') \/* (q \/* q')) UNLESS
                ((p /\* q) \/* (r \/* r')))Pr`) THEN
   REWRITE_TAC [OR_ASSOC_lemma]);;

let UNLESS_cor10 = prove_thm
  ("UNLESS_cor10",
   (`!(p:'a->bool) q Pr. (p \/* q) STABLE Pr ==> (p UNLESS q) Pr`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   STRIP_ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`p:'a->bool`); (`q:'a->bool`);
      (`False:'a->bool`); (`Pr:('a->'a)list`)]
      UNLESS_cor4)) THEN
   UNDISCH_TAC (`((p:'a->bool) UNLESS (q \/* False))Pr`) THEN
   REWRITE_TAC [OR_False_lemma]);;


let UNLESS_cor11 = prove_thm
  ("UNLESS_cor11",
   (`!(p:'a->bool) Pr. (!s. (Not p)s) ==> p STABLE Pr`),
   GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [UNLESS] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   GEN_TAC THEN
   REWRITE_TAC [UNLESS_STMT; FALSE_def] THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [NOT_def1]
       (SPEC `s:'a` (ASSUME `!s:'a. Not (p:'a->bool) s`))) THEN
   STRIP_TAC THEN
   RES_TAC);;

let UNLESS_cor12 = prove_thm
  ("UNLESS_cor12",
   (`!(p:'a->bool) Pr. (!s. (Not p)s) ==> (Not p) STABLE Pr`),
   GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [UNLESS] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [UNLESS_STMT]);;

let UNLESS_cor13 = prove_thm
  ("UNLESS_cor13",
   (`!(p:'a->bool) q Pr.
        (p UNLESS q) Pr /\ (q UNLESS p) Pr /\ (!s. Not (p /\* q) s) ==>
                (p \/* q) STABLE Pr`),
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
         [(`((p:'a->bool) /\* q)`);
	  (`Pr:('a->'a)list`)] UNLESS_cor11)) THEN
   UNDISCH_TAC (`((p:'a->bool) /\* q) STABLE Pr`) THEN
   REWRITE_TAC [STABLE] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
      [(`((p:'a->bool) UNLESS q)Pr`); (`((q:'a->bool) UNLESS p)Pr`)]
       AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
      [(`(p:'a->bool)`); (`(q:'a->bool)`);
       (`(q:'a->bool)`); (`(p:'a->bool)`); (`Pr:('a->'a)list`)]
       UNLESS_thm5)) THEN
   UNDISCH_TAC (`(((p:'a->bool) \/* q) UNLESS
                    ((((Not p) /\* p) \/* ((Not q) /\* q)) \/* (q /\* p))
                   ) Pr`) THEN
   PURE_ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma;OR_False_lemma] THEN
   PURE_ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_False_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
        [(`(((q:'a->bool) \/* p) UNLESS (p /\* q))Pr`);
         (`(((p:'a->bool) /\* q) UNLESS False)Pr`)]
         AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`((q:'a->bool) \/* p)`); (`((p:'a->bool) /\* q)`);
      (`False:'a->bool`); (`Pr:('a->'a)list`)]
       UNLESS_thm8)) THEN
   UNDISCH_TAC
     (`((((q:'a->bool) \/* p) \/* (p /\* q)) UNLESS False)Pr`) THEN
   REWRITE_TAC [OR_AND_DISTR_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;OR_OR_lemma] THEN
   PURE_ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_ASSOC_lemma;OR_OR_lemma;AND_AND_lemma]);;

let UNLESS_cor14 = prove_thm
  ("UNLESS_cor14",
   (`!(p:'a->bool) q Pr. (p UNLESS (Not q)) Pr /\ q STABLE Pr ==>
                               (p UNLESS (p /\* (Not q))) Pr`),
   REWRITE_TAC [STABLE] THEN
   REPEAT GEN_TAC THEN DISCH_TAC THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
    [(`p:'a->bool`); (`Not (q:'a->bool)`);
     (`q:'a->bool`); (`False:'a->bool`); (`Pr:('a->'a)list`)]
      UNLESS_thm4)) THEN
   UNDISCH_TAC (`(((p:'a->bool) /\* q) UNLESS
                     (((p /\* False) \/* (q /\* (Not q))) \/*
                      ((Not q) /\* False)))Pr`) THEN
   REWRITE_TAC [AND_False_lemma;P_AND_NOT_P_lemma;OR_False_lemma] THEN
   DISCH_TAC THEN
   ASSUME_TAC (SPECL
     [(`(p:'a->bool) /\* (Not q)`);
      (`Pr:('a->'a)list`)] UNLESS_thm1) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`(((p:'a->bool) /\* q) UNLESS False)Pr`);
      (`(((p:'a->bool) /\* (Not q)) UNLESS (p /\* (Not q)))Pr`)]
      AND_INTRO_THM)) THEN
   ASSUME_TAC (UNDISCH_ALL (SPECL
     [(`(p:'a->bool) /\* q`); (`False:'a->bool`);
      (`(p:'a->bool) /\* (Not q)`); (`(p:'a->bool) /\* (Not q)`);
      (`Pr:('a->'a)list`)]
      UNLESS_thm5)) THEN
   UNDISCH_TAC (`((((p:'a->bool) /\* q) \/* (p /\* (Not q))) UNLESS
                 ((((Not(p /\* q)) /\* (p /\* (Not q))) \/*
                   ((Not(p /\* (Not q))) /\* False)) \/*
                    (False /\* (p /\* (Not q)))))Pr`) THEN
   REWRITE_TAC [AND_False_lemma;OR_False_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [AND_COMPL_OR_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   REWRITE_TAC [AND_False_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_False_lemma] THEN
   REWRITE_TAC [NOT_AND_OR_NOT_lemma] THEN
   REWRITE_TAC [AND_OR_DISTR_lemma] THEN
   REWRITE_TAC [AND_ASSOC_lemma] THEN
   REWRITE_TAC [AND_AND_lemma] THEN
   ONCE_REWRITE_TAC [AND_AND_COMM_lemma] THEN
   REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL AND_ASSOC_lemma))] THEN
   REWRITE_TAC [P_AND_NOT_P_lemma] THEN
   ONCE_REWRITE_TAC [AND_COMM_OR_lemma] THEN
   REWRITE_TAC [AND_False_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [OR_False_lemma] THEN
   DISCH_TAC THEN
   ONCE_REWRITE_TAC [AND_COMM_lemma] THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor15_lem1 = TAC_PROOF
  (([],
   (`!p q. p /\ (~p \/ ~q) <=> p /\ ~q`)),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
     (RES_TAC THEN ASM_REWRITE_TAC []));;

let UNLESS_cor15_lem2 = TAC_PROOF
  (([],
   (`!p q. p \/ (p /\ q) <=> p`)),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let UNLESS_cor15_lem3 = TAC_PROOF
  (([],
   (`!P Q. (!(i:num). (P i) /\ (Q i)) <=> ((!i. P i) /\ (!i. Q i))`)),
   REPEAT GEN_TAC THEN
   EQ_TAC THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

(*
   MESON_TAC is powerful, but I should change this proof to not use
   MESON_TAC as a detailed proof will better show why the UNLESS_STMT
   property holds
*)
let UNLESS_STMT_cor15 = prove_thm
  ("UNLESS_STMT_cor15",
   `!(P:num->('a->bool)) Q st.
            (!i s. (P i UNLESS_STMT P i /\* Q i) st s) ==>
               (!s. ((!*) P UNLESS_STMT (!*) P /\* (?*) Q) st s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FORALL_def; EXISTS_def; UNLESS_STMT; AND_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   MESON_TAC []);;

let UNLESS_cor15 = prove_thm
  ("UNLESS_cor15",
   `!(P:num->('a->bool)) Q Pr.
       (!i. ((P i) UNLESS ((P i) /\* (Q i))) Pr) ==>
           (((!*) P) UNLESS (((!*) P) /\* ((?*) Q))) Pr`,
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [UNLESS] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [UNLESS_cor15_lem3] (ASSUME
    `!i:num. (!s:'a. (P i UNLESS_STMT P i /\* Q i) h s) /\
                  (P i UNLESS P i /\* Q i) t`)) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   IMP_RES_TAC UNLESS_STMT_cor15);;

let UNLESS_cor16 = prove_thm
  ("UNLESS_cor16",
   `!(P:num->('a->bool)) Q Pr.
    (!i. ((P i) UNLESS (Q i))Pr) ==>
      (!i. ((/<=\* P i) UNLESS (\<=/* Q i))Pr)`,
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   INDUCT_TAC THENL
     [
      ASM_REWRITE_TAC [AND_LE_N_def;OR_LE_N_def]
     ;
      REWRITE_TAC [AND_LE_N_def;OR_LE_N_def] THEN
      ASSUME_TAC (SPEC (`SUC i`) (ASSUME
        (`!i. (((P:num->('a->bool)) i) UNLESS (Q i))Pr`))) THEN
      STRIP_ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL
        [(`/<=\* (P:num->('a->bool)) i`);
	 (`\<=/* (Q:num->('a->bool)) i`);
         (`(P:num->('a->bool))(SUC i)`); (`(Q:num->('a->bool))(SUC i)`);
         (`Pr:('a->'a)list`)]
         UNLESS_thm6))))
     ]);;

let UNLESS_cor17 = prove_thm
  ("UNLESS_cor17",
   (`!(P:num->('a->bool)) q Pr.
       (!i. ((P i) UNLESS q)Pr) ==> (!i. ((/<=\* P i) UNLESS q)Pr)`),
   REPEAT GEN_TAC THEN
   DISCH_TAC THEN
   INDUCT_TAC THENL
     [
      ASM_REWRITE_TAC [AND_LE_N_def;OR_LE_N_def]
     ;
      REWRITE_TAC [AND_LE_N_def;OR_LE_N_def] THEN
      ASSUME_TAC (SPEC (`SUC i`) (ASSUME
        (`!i. (((P:num->('a->bool)) i) UNLESS q)Pr`))) THEN
      ASSUME_TAC (UNDISCH_ALL (hd (IMP_CANON (SPECL
        [(`/<=\* (P:num->('a->bool)) i`); (`q:'a->bool`);
         (`(P:num->('a->bool))(SUC i)`);
	 (`q:'a->bool`); (`Pr:('a->'a)list`)]
         UNLESS_thm6)))) THEN
      UNDISCH_ONE_TAC THEN
      REWRITE_TAC [OR_OR_lemma]
     ]);;

(*
   MESON_TAC is powerful, but I should change this proof to not use
   MESON_TAC as a detailed proof will better show why the UNLESS_STMT
   property holds
*)
let UNLESS_STMT_cor18 = prove_thm
  ("UNLESS_STMT_cor18",
   `!(P:num->('a->bool)) Q st.
         (!i s. ((P i) UNLESS_STMT q) st s) ==>
            (!s. (((?*) P) UNLESS_STMT q) st s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FORALL_def; EXISTS_def; UNLESS_STMT; AND_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   MESON_TAC []);;

let UNLESS_cor18 = prove_thm
  ("UNLESS_cor18",
   (`!(P:num->('a->bool)) q Pr.
        (!m. ((P m) UNLESS q) Pr) ==> (((?*) P) UNLESS q) Pr`),
   GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [UNLESS] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_ASSUME_TAC (REWRITE_RULE [UNLESS_cor15_lem3] (ASSUME
    `!m:num. (!s:'a. (P m UNLESS_STMT q) h s) /\ (P m UNLESS q) t`)) THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   IMP_RES_TAC UNLESS_STMT_cor18);;

let UNLESS_cor19 = prove_thm
  ("UNLESS_cor19",
   (`!Pr. (False:'a->bool) STABLE Pr`),
   GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   REWRITE_TAC [UNLESS_thm1]);;

let UNLESS_cor20 = prove_thm
  ("UNLESS_cor20",
   (`!(p:'a->bool) q Pr.
        (p STABLE Pr) /\ (q STABLE Pr) ==> ((p /\* q) STABLE Pr)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   ACCEPT_TAC (REWRITE_RULE [AND_False_lemma;OR_False_lemma] (SPECL
     [(`p:'a->bool`); (`False:'a->bool`);
      (`q:'a->bool`); (`False:'a->bool`);
      (`Pr:('a->'a)list`)] UNLESS_thm4)));;

let UNLESS_cor21 = prove_thm
  ("UNLESS_cor21",
   (`!(p:'a->bool) q Pr.
        (p STABLE Pr) /\ (q STABLE Pr) ==> ((p \/* q) STABLE Pr)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   ACCEPT_TAC (REWRITE_RULE [AND_False_lemma;OR_False_lemma] (SPECL
     [(`p:'a->bool`); (`False:'a->bool`);
      (`q:'a->bool`); (`False:'a->bool`);
      (`Pr:('a->'a)list`)] UNLESS_thm7)));;

let UNLESS_cor22 = prove_thm
  ("UNLESS_cor22",
   (`!(p:'a->bool) q r Pr.
          (p UNLESS q) Pr /\ (r STABLE Pr) ==>
          ((p /\* r) UNLESS (q /\* r))Pr`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [STABLE] THEN
   ACCEPT_TAC (REWRITE_RULE [OR_False_lemma] (ONCE_REWRITE_RULE [OR_COMM_lemma]
    (ONCE_REWRITE_RULE [OR_AND_COMM_lemma]
      (REWRITE_RULE [AND_False_lemma;OR_False_lemma] (SPECL
        [(`p:'a->bool`); (`q:'a->bool`);
	 (`r:'a->bool`); (`False:'a->bool`);
         (`Pr:('a->'a)list`)] UNLESS_thm4))))));;

let UNLESS_cor23 = prove_thm
  ("UNLESS_cor23",
   (`!(p:'a->bool) q r Pr.
         ((p UNLESS q) Pr) ==> ((p \/* r) UNLESS (q \/* r)) Pr`),
   GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   REWRITE_TAC [UNLESS] THEN
   STRIP_TAC THEN
   RES_TAC THEN
   ASM_REWRITE_TAC [] THEN
   IMP_RES_TAC UNLESS_STMT_thm6 THEN
   ASM_REWRITE_TAC []);;
