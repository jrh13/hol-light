(*
  File:        mk_state_logic.ml

  Description: This file defines the state abstracted logical
	       operators used in unity and some theorems valid for
	       the combination of these operators.

  Author:       (c) Copyright 1989-2008 by Flemming Andersen
  Date:         October 23, 1989
  Last Update:  December 30, 2007

*)

(* loadt"aux_definitions.ml";; *)

let FALSE_def   = new_definition (`(False:'a->bool)  = \s:'a. F`);;
let TRUE_def    = new_definition (`(True:'a->bool)   = \s:'a. T`);;
let NOT_def1    = new_definition (`Not (p:'a->bool) = \s. ~p s`);;
let NOT_def2    = new_definition (`~* (p:'a->bool)  = \s. ~p s`);;

let AND_def     = new_infix_definition
("/\*", "/\\", `/\* (p:'a->bool) (q:'a->bool) = \s. (p s) /\ (q s)`, OP_FIX);;
let OR_def      = new_infix_definition
("\/*", "\/", `\/* (p:'a->bool) (q:'a->bool) = \s. (p s) \/ (q s)`, OP_FIX);;

let FORALL_def  = new_binder_definition
   (`!* (P:'b->('a->bool)) = (\s. (!x. ((P x)s)))`) "!*";;
let EXISTS_def  = new_binder_definition
   (`?* (P:'b->('a->bool)) = (\s. (?x. ((P x)s)))`) "?*";;
let CHOICE_def  = new_binder_definition
   (`@* P = (\s:'a. (@x:'b. ((P x)s)))`) "@*";;

let IMPLIES_def = new_infix_definition
("==>*", "==>", `==>* (p:'a->bool) (q:'a->bool) = \s. (p s) ==> (q s)`, OP_FIX);;

let LESS_def = new_infix_definition
  ("<*", "<", `<* (p:'a->num) (q:'a->num) = \s. (p s) < (q s)`, OP_FIX);;
let GREATER_def = new_infix_definition
  (">*", ">", `>* (p:'a->num) (q:'a->num) = \s. (p s) > (q s)`, OP_FIX);;
let LESS_EQ_def = new_infix_definition
  ("<=*", "<=", `<=* (p:'a->num) (q:'a->num) = \s. (p s) <= (q s)`, OP_FIX);;
let GREATER_EQ_def = new_infix_definition
  (">=*", ">=", `>=* (p:'a->num) (q:'a->num) = \s. (p s) >= (q s)`, OP_FIX);;
let EQ_def = new_infix_definition
  ("=*", "=", `=* (p:'a->'b) (q:'a->'b) = \s. (p s) = (q s)`, OP_FIX);;
let NEQ_def = new_infix_definition
  ("<>*", "=", `<>* (p:'a->'b) (q:'a->'b) = \s. ~((p s) = (q s))`, OP_FIX);;
let GE_def = new_infix_definition
  ("=>*", "<=>", `=>* (p:'a->bool) (r1:'a->'b) (r2:'a->'b) =
                        \s. if (p s) then r1 s else r2 s`, OP_FIX);;
let PLUS_def = new_infix_definition
  ("+*", "+", `+* (p:'a->num) (q:'a->num) = \s. (p s) + (q s)`, OP_FIX);;
let SUB_def = new_infix_definition
  ("-*", "-", `-* (p:'a->num) (q:'a->num) = \s. (p s) - (q s)`, OP_FIX);;
let MUL_def = new_infix_definition
  ("**", "*", `(**) (p:'a->num) (q:'a->num) = \s. ((p s) * (q s))`, OP_FIX);;
let SUC_def = new_definition
  (`Suc (p:'a->num) = \s. SUC (p s)`);;
let PRE_def = new_definition
  (`Pre (p:'a->num) = \s. PRE (p s)`);;
let MOD_def = new_infix_definition
  ("%*", "MOD", `%* (p:'a->num) (q:'a->num) = \s. (p s) MOD (q s)`, OP_FIX);;
let DIV_def = new_infix_definition
  ("/*", "/", `/* (p:'a->num) (q:'a->num) = \s. (p s) DIV (q s)`, OP_FIX);;
let EXP_def = new_infix_definition
  ("***", "EXP", `*** (p:'a->num) (q:'a->num) = \s. (p s) EXP (q s)`, OP_FIX);;

(* State dependent index *)
(* Weakness in defining priority: does o have same prio as Ind? *)
let IND_def = new_infix_definition
  ("Ind", "o", `Ind (a:'a->('b->'c)) (i:'a->'b) = \s. (a s) (i s)`, OP_FIX);;

(* More State dependent operators to be defined ??? *)

(*  Be aware that (!i :: i <= m. P i) = (!i. i <= m ==> P i) *)
let FORALL_LE_def = new_definition
   (`!<=* (P:num->('a->bool)) m = (\s:'a. (!i. i <= m ==> ((P i)s)))`);;

(*  Be aware that ?i :: i <= m. P i == ?i. i <= m /\ P i *)
let EXISTS_LE_def = new_definition
   (`?<=* (P:num->('a->bool)) m = (\s:'a. (?i. i <= m /\ ((P i)s)))`);;

let EXISTS_LT_def = new_definition
   (`?<* (P:num->('a->bool)) m = (\s:'a. (?i. i < m /\ ((P i)s)))`);;

let AND_LE_N_def = new_recursive_definition
   num_RECURSION
   (`(!P. /<=\* P 0       = (P:num->('a->bool)) 0) /\
     (!P. /<=\* P (SUC i) = ((/<=\* P i) /\* (P (SUC i))))`);;

let OR_LE_N_def = new_recursive_definition
   num_RECURSION
   (`(!P. \<=/* P 0       = (P:num->('a->bool)) 0) /\
     (!P. (\<=/* P (SUC i)) = ((\<=/* P i) \/* (P (SUC i))))`);;

let AND_LT_N_def = new_recursive_definition
   num_RECURSION
   (`(!P. /<\* P 0       = (False:'a->bool)) /\
     (!P. /<\* P (SUC i) = ((/<\* P i) /\* (P i)))`);;

let OR_LT_N_def = new_recursive_definition
   num_RECURSION
   (`(!P. \</* P 0       = (False:'a->bool)) /\
     (!P. \</* P (SUC i) = ((\</* P i) \/* (P i)))`);;

(*-------------------------------------------------------------------------*)
(* Theorems valid in this theory                                           *)
(*-------------------------------------------------------------------------*)

let s  = `s:'a`;;
let p  = `p:'a->bool`;;
let q  = `q:'a->bool`;;
let r  = `r:'a->bool`;;
let i  = `i:num`;;
let P  = `P:num->('a->bool)`;;

let IMPLY_WEAK_lemma1 = prove_thm
   ("IMPLY_WEAK_lemma1",
    (`!p q p' q' (s:'a).
         ( (((p /\* q') \/* (p' /\* q)) \/* (q /\* q')) s ) ==> ((q \/* q') s)`),
    REPEAT(GEN_TAC) THEN
    REWRITE_TAC [AND_def; OR_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC))] THEN
    REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma2 = prove_thm
   ("IMPLY_WEAK_lemma2",
    `!p q p' q' (s:'a).
         ((((Not p) /\* q') \/* ((Not p') /\* q)) \/* (q /\* q'))s
       ==>
         (q \/* q')s`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
    BETA_TAC THEN
    REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC));
                 SYM (SPEC_ALL DISJ_ASSOC);
		 NOT_CLAUSES;
                 DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THENL
      [ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC [];
       ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_lemma3 = prove_thm
   ("IMPLY_WEAK_lemma3",
    `!p q r (s:'a).
         ((((Not p) /\* r) \/* ((Not q) /\* q)) \/* (q /\* r))s
       ==>
         r s`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC))] THEN
    REPEAT STRIP_TAC THEN
    RES_TAC);;

let IMPLY_WEAK_lemma4 = prove_thm
  ("IMPLY_WEAK_lemma4",
   `!p q p' q' r r' (s:'a).
        ((((Not(p \/* p')) /\* (p \/* r')) \/*
          ((Not(q \/* q')) /\* (q \/* r))) \/*
         ((q \/* r) /\* (p \/* r')))s
      ==>
        ((p /\* q) \/* r \/* r')s`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [SYM (SPEC_ALL DISJ_ASSOC);
                GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC));
                NOT_CLAUSES;
                DE_MORGAN_THM] THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN ASM_REWRITE_TAC []);;

let IMPLY_WEAK_lemma5 = prove_thm
  ("IMPLY_WEAK_lemma5",
   `!p q r (s:'a).
        ((p /\* r) \/* (((p \/* q) /\* (q \/* r)) \/* r)) s
      ==>
        (q \/* r) s`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   RES_TAC THEN ASM_REWRITE_TAC []);;

let IMPLY_WEAK_lemma6 = prove_thm
  ("IMPLY_WEAK_lemma6",
   `!p q b r (s:'a).
        ((r /\* q) \/* (p /\* b) \/* (b /\* q)) s
      ==>
        ((q /\* r) \/* b) s`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let IMPLY_WEAK_lemma7 = prove_thm
  ("IMPLY_WEAK_lemma7",
   `!p q b r (s:'a).
        (((r /\* q) \/* ((r /\* p) /\* b)) \/* (b /\* q)) s
      ==>
        ((q /\* r) \/* b) s`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_COMM_DISJ_lemma_a = TAC_PROOF
    (([],
      `!p q r (s:'a).
           (r s /\ q s) \/ p s
         ==>
	   (q s /\ r s) \/ p s`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_COMM_DISJ_lemma_b = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (q s /\ r s) \/ p s
       ==>
         (r s /\ q s) \/ p s`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_COMM_DISJ_lemma = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (r s /\ q s) \/ p s
       <=> (q s /\ r s) \/ p s`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_COMM_DISJ_lemma_a)
                    (SPEC_ALL CONJ_COMM_DISJ_lemma_b)));;

let AND_COMM_OR_lemma = prove_thm
  ("AND_COMM_OR_lemma",
   `!(p:'a->bool) q r. ((r /\* q) \/* p) = ((q /\* r) \/* p)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] CONJ_COMM_DISJ_lemma)));;

let CONJ_DISJ_COMM_lemma_a = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (p s /\ (r s \/ q s))
       ==>
         (p s /\ (q s \/ r s))`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_DISJ_COMM_lemma_b = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (p s /\ (q s \/ r s))
        ==>
         (p s /\ (r s \/ q s))`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_DISJ_COMM_lemma = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (p s /\ (r s \/ q s))
       = (p s /\ (q s \/ r s))`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_DISJ_COMM_lemma_a)
                    (SPEC_ALL CONJ_DISJ_COMM_lemma_b)));;

let AND_OR_COMM_lemma = prove_thm
  ("AND_OR_COMM_lemma",
   `!(p:'a->bool) q r.
        p /\* (r \/* q)
      = p /\* (q \/* r)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] CONJ_DISJ_COMM_lemma)));;

let DISJ_COMM_CONJ_lemma_a = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (r s \/ q s) /\ p s
       ==>
         (q s \/ r s) /\ p s`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_COMM_CONJ_lemma_b = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (q s \/ r s) /\ p s
       ==>
         (r s \/ q s) /\ p s`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_COMM_CONJ_lemma = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (r s \/ q s) /\ p s
       <=> (q s \/ r s) /\ p s`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_COMM_CONJ_lemma_a)
                    (SPEC_ALL DISJ_COMM_CONJ_lemma_b)));;

let OR_COMM_AND_lemma = prove_thm
  ("OR_COMM_AND_lemma",
   `!(p:'a->bool) q r.
        (r \/* q) /\* p
      = (q \/* r) /\* p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] DISJ_COMM_CONJ_lemma)));;

let DISJ_COMM_DISJ_lemma_a = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (r s \/ q s) \/ p s
       ==>
         (q s \/ r s) \/ p s`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_COMM_DISJ_lemma_b = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (q s \/ r s) \/ p s
       ==>
         (r s \/ q s) \/ p s`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_COMM_DISJ_lemma = TAC_PROOF
  (([],
    `!(p:'a->bool) q r s. (r s \/ q s) \/ p s <=> (q s \/ r s) \/ p s`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_COMM_DISJ_lemma_a)
                    (SPEC_ALL DISJ_COMM_DISJ_lemma_b)));;

let OR_COMM_OR_lemma = prove_thm
  ("OR_COMM_OR_lemma",
   `!(p:'a->bool) q r. (r \/* q) \/* p = (q \/* r) \/* p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] DISJ_COMM_DISJ_lemma)));;

let DISJ_DISJ_COMM_lemma_a = TAC_PROOF
  (([], `!p q r (s:'a). p s \/ (r s \/ q s) ==> p s \/ (q s \/ r s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_DISJ_COMM_lemma_b = TAC_PROOF
  (([], `!p q r (s:'a). p s \/ (q s \/ r s) ==> p s \/ (r s \/ q s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_DISJ_COMM_lemma = TAC_PROOF
  (([], `!p q r (s:'a). p s \/ (r s \/ q s) <=> p s \/ (q s \/ r s) `),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_DISJ_COMM_lemma_a)
                    (SPEC_ALL DISJ_DISJ_COMM_lemma_b)));;

let OR_OR_COMM_lemma = prove_thm
  ("OR_OR_COMM_lemma",
   (`!(p:'a->bool) q r. p \/* (r \/* q) = p \/* (q \/* r)`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] DISJ_DISJ_COMM_lemma)));;

let CONJ_COMM_CONJ_lemma_a = TAC_PROOF
  (([], `!p q r (s:'a). (r s /\ q s) /\ p s ==> (q s /\ r s) /\ p s`),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_COMM_CONJ_lemma_b = TAC_PROOF
  (([], `!p q r (s:'a). (q s /\ r s) /\ p s ==> (r s /\ q s) /\ p s`),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_COMM_CONJ_lemma = TAC_PROOF
  (([], `!p q r (s:'a). (r s /\ q s) /\ p s <=> (q s /\ r s) /\ p s`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_COMM_CONJ_lemma_a)
                    (SPEC_ALL CONJ_COMM_CONJ_lemma_b)));;

let AND_COMM_AND_lemma = prove_thm
  ("AND_COMM_AND_lemma",
   `!(p:'a->bool) q r. (r /\* q) /\* p = (q /\* r) /\* p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] CONJ_COMM_CONJ_lemma)));;

let CONJ_CONJ_COMM_lemma_a = TAC_PROOF
  (([], `!p q r (s:'a). p s /\ (r s /\ q s) ==> p s /\ (q s /\ r s)`),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_CONJ_COMM_lemma_b = TAC_PROOF
  (([], `!p q r (s:'a). p s /\ (q s /\ r s) ==> p s /\ (r s /\ q s)`),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let CONJ_CONJ_COMM_lemma = TAC_PROOF
  (([], `!p q r (s:'a). p s /\ (r s /\ q s) <=> p s /\ (q s /\ r s) `),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL CONJ_CONJ_COMM_lemma_a)
                    (SPEC_ALL CONJ_CONJ_COMM_lemma_b)));;

let AND_AND_COMM_lemma = prove_thm
  ("AND_AND_COMM_lemma",
   `!(p:'a->bool) q r. p /\* (r /\* q) = p /\* (q /\* r)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] CONJ_CONJ_COMM_lemma)));;

let DISJ_CONJ_COMM_lemma_a = TAC_PROOF
  (([], `!p q r (s:'a). p s \/ (r s /\ q s) ==> p s \/ (q s /\ r s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_CONJ_COMM_lemma_b = TAC_PROOF
  (([], `!p q r (s:'a). p s \/ (q s /\ r s) ==> p s \/ (r s /\ q s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_CONJ_COMM_lemma = TAC_PROOF
  (([], `!p q r (s:'a). p s \/ (r s /\ q s) <=> p s \/ (q s /\ r s)`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (IMP_ANTISYM_RULE
                    (SPEC_ALL DISJ_CONJ_COMM_lemma_a)
                    (SPEC_ALL DISJ_CONJ_COMM_lemma_b)));;

let OR_AND_COMM_lemma = prove_thm
  ("OR_AND_COMM_lemma",
   `!(p:'a->bool) q r. p \/* (r /\* q) = p \/* (q /\* r)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] DISJ_CONJ_COMM_lemma)));;

let NOT_NOT_lemma = prove_thm
   ("NOT_NOT_lemma",
    `!(p:'a->bool). (Not (Not p)) = p`,
    REWRITE_TAC [NOT_def1] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [NOT_CLAUSES; ETA_AX]);;

let DISJ_COMM_lemma = TAC_PROOF
   (([], `!p q (s:'a). p s \/ q s <=> q s \/ p s`),
    REPEAT STRIP_TAC THEN
    STRIP_ASSUME_TAC
      (SPECL [`(p (s:'a)):bool`; `(q (s:'a)):bool`] DISJ_SYM));;

let OR_COMM_lemma = prove_thm
   ("OR_COMM_lemma",
    `!(p:'a->bool) q. (p \/* q) = (q \/* p)`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC [OR_def] THEN
    ASSUME_TAC DISJ_COMM_lemma THEN
    STRIP_ASSUME_TAC
        (MK_ABS (SPECL [p;q] 
                (ASSUME (`!(p:'a->bool) q s. p s \/ q s <=> q s \/ p s`)))));;

let OR_OR_lemma = prove_thm
   ("OR_OR_lemma",
    `!p:'a->bool. p \/* p = p`,
    GEN_TAC THEN REWRITE_TAC [OR_def; ETA_AX]);;

let DISJ_ASSOC_lemma = TAC_PROOF
   (([], `!p q  r (s:'a). ((p s \/ q s) \/ r s) <=> (p s \/ (q s \/ r s))`),
    REWRITE_TAC [(SYM (SPEC_ALL DISJ_ASSOC))]);;

let OR_ASSOC_lemma = prove_thm
   ("OR_ASSOC_lemma",
    (`!(p:'a->bool) q r. (p \/* q) \/* r = p \/* (q \/* r)`),
    REPEAT STRIP_TAC THEN REWRITE_TAC [OR_def]  THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    ASSUME_TAC DISJ_ASSOC_lemma THEN
    STRIP_ASSUME_TAC
   (MK_ABS (SPECL [p;q;r]
      (ASSUME (`!p q r (s:'a).
                    ((p s \/ q s) \/ r s) <=> (p s \/ (q s \/ r s))`)))));;

let CONJ_WEAK_lemma = TAC_PROOF
  (([], `!p q (s:'a). p s /\ q s ==> q s`),
    REPEAT STRIP_TAC THEN RES_TAC);;

let AND_IMPLY_WEAK_lemma = prove_thm
  ("AND_IMPLY_WEAK_lemma",
    `!p q (s:'a). (p /\* q) s ==> q s`,
    REWRITE_TAC [AND_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [CONJ_WEAK_lemma]);;

let SYM_CONJ_WEAK_lemma = TAC_PROOF
  (([], `!p q (s:'a). p s /\ q s ==> p s`),
    REPEAT STRIP_TAC THEN RES_TAC);;

let SYM_AND_IMPLY_WEAK_lemma = prove_thm
  ("SYM_AND_IMPLY_WEAK_lemma",
    `!p q (s:'a). (p /\* q) s ==> p s`,
    REWRITE_TAC [AND_def] THEN
    CONV_TAC (DEPTH_CONV BETA_CONV) THEN
    REWRITE_TAC [SYM_CONJ_WEAK_lemma]);;

let OR_IMPLY_WEAK_lemma = prove_thm
  ("OR_IMPLY_WEAK_lemma",
   `!p q (s:'a). p s ==> (p \/* q) s`,
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let SYM_OR_IMPLY_WEAK_lemma = prove_thm
  ("SYM_OR_IMPLY_WEAK_lemma",
   `!p q (s:'a). p s ==> (q \/* p) s`,
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let IMPLY_WEAK_AND_lemma = prove_thm
  ("IMPLY_WEAK_AND_lemma",
   `!(p:'a->bool) q r.
        (!s. p s ==> q s)
      ==>
        (!s. (p /\* r) s ==> (q /\* r) s)`,
   REWRITE_TAC [AND_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [RES_TAC;
      RES_TAC THEN
      ASM_REWRITE_TAC []]);;

let IMPLY_WEAK_OR_lemma = prove_thm
  ("IMPLY_WEAK_OR_lemma",
   `!(p:'a->bool) q r.
        (!s. p s ==> q s)
      ==>
        (!s. (p \/* r) s ==> (q \/* r) s)`,
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THENL
     [RES_TAC THEN
      ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []]);;

let AND_AND_lemma = prove_thm
  ("AND_AND_lemma",
   `!p:'a->bool. p /\* p = p`,
   REWRITE_TAC [AND_def; ETA_AX]);;

let CONJ_COMM_lemma = TAC_PROOF
  (([],
    `!p q (s:'a). (p s /\ q s) <=> (q s /\ p s)`),
   REPEAT GEN_TAC THEN
   STRIP_ASSUME_TAC (SPECL [`(p:'a->bool) s`; `(q:'a->bool) s`] CONJ_SYM));;

let AND_COMM_lemma = prove_thm
   ("AND_COMM_lemma",
   (`!(p:'a->bool) q. (p /\* q) = (q /\* p)`),
   REWRITE_TAC [AND_def] THEN
   REPEAT GEN_TAC THEN
   ASSUME_TAC CONJ_COMM_lemma THEN
   STRIP_ASSUME_TAC
        (MK_ABS (SPECL [p;q] 
                (ASSUME (`!p q (s:'a). p s /\ q s <=> q s /\ p s`)))));;

let CONJ_ASSOC_lemma = TAC_PROOF
  (([],
    `!p q r (s:'a). ((p s /\ q s) /\ r s) <=> (p s /\ (q s /\ r s))`),
    REWRITE_TAC [GEN_ALL (SYM (SPEC_ALL CONJ_ASSOC))]);;

let AND_ASSOC_lemma = prove_thm
   ("AND_ASSOC_lemma",
    `!(p:'a->bool) q r. (p /\* q) /\* r = p /\* (q /\* r)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [AND_def]  THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   ASSUME_TAC CONJ_ASSOC_lemma THEN
   STRIP_ASSUME_TAC
   (MK_ABS (SPECL [p;q;r]
      (ASSUME (`!p q  r (s:'a).
                 ((p s /\ q s) /\ r s) <=> (p s /\ (q s /\ r s))`)))));;

let NOT_True_lemma = prove_thm
   ("NOT_True_lemma",
    `Not (True:'a->bool) = False`,
   REWRITE_TAC [NOT_def1; TRUE_def; FALSE_def; ETA_AX]);;

let NOT_False_lemma = prove_thm
   ("NOT_False_lemma",
    `Not (False:'a->bool) = True`,
   REWRITE_TAC [NOT_def1; TRUE_def; FALSE_def; ETA_AX]);;

let AND_True_lemma = prove_thm
   ("AND_True_lemma",
    `!p:'a->bool. p /\* True = p`,
   REWRITE_TAC [AND_def; TRUE_def; ETA_AX]);;

let OR_True_lemma = prove_thm
   ("OR_True_lemma",
    `!p:'a->bool. p \/* True = True`,
   REWRITE_TAC [OR_def; TRUE_def; ETA_AX]);;

let AND_False_lemma = prove_thm
   ("AND_False_lemma",
    `!p:'a->bool. p /\* False = False`,
   REWRITE_TAC [AND_def; FALSE_def; ETA_AX]);;

let OR_False_lemma = prove_thm
   ("OR_False_lemma",
    `!p:'a->bool. p \/* False = p`,
   REWRITE_TAC [OR_def; FALSE_def; ETA_AX]);;

let P_OR_NOT_P_lemma = prove_thm
   ("P_OR_NOT_P_lemma",
    `!p:'a->bool. p \/* (Not p) = True`,
   REWRITE_TAC [OR_def; NOT_def1; TRUE_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [EXCLUDED_MIDDLE; OR_CLAUSES; NOT_CLAUSES; ETA_AX]);;

let P_AND_NOT_P_lemma = prove_thm
   ("P_AND_NOT_P_lemma",
    `!p:'a->bool. p /\* (Not p) = False`,
   REWRITE_TAC [AND_def; NOT_def1; FALSE_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [NOT_AND; AND_CLAUSES; NOT_CLAUSES; ETA_AX]);;

let CONJ_COMPL_DISJ_lemma1 = TAC_PROOF
  (([],
    `!p q. p /\ ~q \/ p /\ q ==> p`),
   REPEAT STRIP_TAC);;

let CONJ_COMPL_DISJ_lemma2 = TAC_PROOF
  (([],
    `!p q. p ==> p /\ ~q \/ p /\ q`),
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   PURE_ONCE_REWRITE_TAC [DISJ_SYM] THEN
   REWRITE_TAC [EXCLUDED_MIDDLE]);;

let CONJ_COMPL_DISJ_lemma = TAC_PROOF
  (([],
    `!p q. p /\ ~q \/ p /\ q <=> p`),
   REWRITE_TAC [IMP_ANTISYM_RULE
                  (SPEC_ALL CONJ_COMPL_DISJ_lemma1)
                  (SPEC_ALL CONJ_COMPL_DISJ_lemma2)]);;

let AND_COMPL_OR_lemma = prove_thm
   ("AND_COMPL_OR_lemma",
    `!(p:'a->bool) q. ((p /\* (Not q)) \/* (p /\* q)) = p`,
   REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [CONJ_COMPL_DISJ_lemma; ETA_AX]);;

let DISJ_NOT_CONJ_lemma1 = TAC_PROOF
  (([],
    `!p q. (p \/ q) /\ ~q ==> p /\ ~q`),
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN RES_TAC);;

let DISJ_NOT_CONJ_lemma2 = TAC_PROOF
  (([],
    `!p q. p /\ ~q ==> (p \/ q) /\ ~q`),
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC [] THEN RES_TAC);;

let DISJ_NOT_CONJ_lemma = TAC_PROOF
  (([], `!p q. (p \/ q) /\ ~q <=> p /\ ~q`),
   REWRITE_TAC [IMP_ANTISYM_RULE
                  (SPEC_ALL DISJ_NOT_CONJ_lemma1)
                  (SPEC_ALL DISJ_NOT_CONJ_lemma2)]);;

let OR_NOT_AND_lemma = prove_thm
  ("OR_NOT_AND_lemma",
   `!(p:'a->bool) q. ((p \/* q) /\* (Not q)) = p /\* (Not q)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [DISJ_NOT_CONJ_lemma]);;

let P_CONJ_Q_DISJ_Q_lemma1 = TAC_PROOF
  (([], `!(p:'a->bool) q s. (p s /\ q s) \/ q s ==> q s`),
   REPEAT STRIP_TAC);;

let P_CONJ_Q_DISJ_Q_lemma2 = TAC_PROOF
  (([], `!(p:'a->bool) q s. q s ==> (p s /\ q s) \/ q s`),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let P_CONJ_Q_DISJ_Q_lemma = TAC_PROOF
  (([], `!(p:'a->bool) q s. (p s /\ q s) \/ q s <=> q s`),
   ASM_REWRITE_TAC [IMP_ANTISYM_RULE
                         (SPEC_ALL P_CONJ_Q_DISJ_Q_lemma1)
                         (SPEC_ALL P_CONJ_Q_DISJ_Q_lemma2)]);;

let P_AND_Q_OR_Q_lemma = prove_thm
  ("P_AND_Q_OR_Q_lemma",
   `!(p:'a->bool) q. (p /\* q) \/* q = q`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [GEN_ALL (MK_ABS (SPECL [p;q] P_CONJ_Q_DISJ_Q_lemma)); ETA_AX]);;

let P_DISJ_Q_CONJ_Q_lemma1 = TAC_PROOF
  (([], `!(p:'a->bool) q s. (p s \/ q s) /\ q s ==> q s`),
   REPEAT STRIP_TAC);;

let P_DISJ_Q_CONJ_Q_lemma2 = TAC_PROOF
  (([], `!(p:'a->bool) q s. q s ==> (p s \/ q s) /\ q s`),
   REPEAT STRIP_TAC THEN ASM_REWRITE_TAC []);;

let P_DISJ_Q_CONJ_Q_lemma = TAC_PROOF
  (([], `!(p:'a->bool) q s. (p s \/ q s) /\ q s <=> q s`),
   ASM_REWRITE_TAC [IMP_ANTISYM_RULE
                         (SPEC_ALL P_DISJ_Q_CONJ_Q_lemma1)
                         (SPEC_ALL P_DISJ_Q_CONJ_Q_lemma2)]);;

let P_OR_Q_AND_Q_lemma = prove_thm
  ("P_OR_Q_AND_Q_lemma",
   `!(p:'a->bool) q. (p \/* q) /\* q = q`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [GEN_ALL (MK_ABS (SPECL [p;q] P_DISJ_Q_CONJ_Q_lemma)); ETA_AX]);;

let NOT_OR_AND_NOT_lemma = prove_thm
  ("NOT_OR_AND_NOT_lemma",
   `!(p:'a->bool) q. Not (p \/* q) = (Not p) /\* (Not q)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [NOT_CLAUSES;
                DE_MORGAN_THM]);;

let NOT_AND_OR_NOT_lemma = prove_thm
  ("NOT_AND_OR_NOT_lemma",
   `!(p:'a->bool) q. Not (p /\* q) = (Not p) \/* (Not q)`,
      REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [NOT_CLAUSES;
                DE_MORGAN_THM]);;

let NOT_IMPLY_OR_lemma = prove_thm
  ("NOT_IMPLY_OR_lemma",
   `!(p:'a->bool) q.
        (!s. (Not p)s ==> q s)
      = (!s. (p \/* q)s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM]);;

let IMPLY_OR_lemma = prove_thm
  ("IMPLY_OR_lemma",
   `!(p:'a->bool) q. (!s. p s ==> q s) = (!s. ((Not p) \/* q)s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM]);;

let OR_IMPLY_lemma = prove_thm
  ("OR_IMPLY_lemma",
   `!(p:'a->bool) q. (!s. (p \/* q)s) = (!s. (Not p)s ==> q s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM; NOT_CLAUSES]);;

let NOT_OR_IMPLY_lemma = prove_thm
  ("NOT_OR_IMPLY_lemma",
   `!(p:'a->bool) q. (!s. ((Not p) \/* q)s) = (!s. p s ==> q s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [NOT_def1; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM; NOT_CLAUSES]);;

let DISJ_CONJ_lemma1 = TAC_PROOF
  (([],
    `!p q r (s:'a).
         (p s \/ q s /\ r s)
       ==>
         ((p s \/ q s) /\ (p s \/ r s))`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_CONJ_lemma2 = TAC_PROOF
  (([], `!(p:'a->bool) q r s. 
             ((p s \/ q s) /\ (p s \/ r s)) ==> (p s \/ q s /\ r s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let DISJ_CONJ_lemma = TAC_PROOF
  (([], `!(p:'a->bool) q r s. 
            (p s \/ q s /\ r s) <=> ((p s \/ q s) /\ (p s \/ r s))`),
   REWRITE_TAC [IMP_ANTISYM_RULE
                      (SPEC_ALL DISJ_CONJ_lemma1)
                      (SPEC_ALL DISJ_CONJ_lemma2)]);;

let OR_AND_DISTR_lemma = prove_thm
  ("OR_AND_DISTR_lemma",
   `!(p:'a->bool) q r. p \/* (q /\* r) = (p \/* q) /\* (p \/* r)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] DISJ_CONJ_lemma)));;

let CONJ_DISJ_lemma1 = TAC_PROOF
  (([], `!(p:'a->bool) q r s.
            (p s /\ (q s \/ r s)) ==> (p s /\ q s \/ p s /\ r s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_DISJ_lemma2 = TAC_PROOF
  (([], `!(p:'a->bool) q r s.
            (p s /\ q s \/ p s /\ r s) ==> (p s /\ (q s \/ r s))`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC [];
      ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_DISJ_lemma = TAC_PROOF
  (([], `!(p:'a->bool) q r s.
            (p s /\ (q s \/ r s)) <=> (p s /\ q s \/ p s /\ r s)`),
   REWRITE_TAC [IMP_ANTISYM_RULE
                      (SPEC_ALL CONJ_DISJ_lemma1)
                      (SPEC_ALL CONJ_DISJ_lemma2)]);;

let AND_OR_DISTR_lemma = prove_thm
  ("AND_OR_DISTR_lemma",
   `!(p:'a->bool) q r. p /\* (q \/* r) = (p /\* q) \/* (p /\* r)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [p;q;r] CONJ_DISJ_lemma)));;

let NOT_IMPLIES_False_lemma = prove_thm
  ("NOT_IMPLIES_False_lemma",
   `!(p:'a->bool). (!s. (Not p)s) ==> (!s. p s = False s)`,
   REWRITE_TAC [FALSE_def; NOT_def1] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC []);;

let NOT_P_IMPLIES_P_EQ_False_lemma = prove_thm
  ("NOT_P_IMPLIES_P_EQ_False_lemma",
   `!(p:'a->bool). (!s. (Not p)s) ==> (p = False)`,
   REPEAT STRIP_TAC THEN
   ASSUME_TAC (MK_ABS (UNDISCH_ALL (SPEC_ALL NOT_IMPLIES_False_lemma))) THEN
   UNDISCH_TAC (`(\s:'a. p s) = (\s. False s)`) THEN
   REWRITE_TAC [ETA_AX]);;

let NOT_AND_IMPLIES_lemma = prove_thm
  ("NOT_AND_IMPLIES_lemma",
   `!(p:'a->bool) q. (!s. (Not (p /\* q))s) <=> (!s. p s ==> Not q s)`,
   REWRITE_TAC [NOT_def1; AND_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [DE_MORGAN_THM; NOT_CLAUSES; IMP_DISJ_THM]);;

let NOT_AND_IMPLIES_lemma1 = prove_thm
  ("NOT_AND_IMPLIES_lemma1",
   `!(p:'a->bool) q. (!s. (Not (p /\* q))s) ==> (!s. p s ==> Not q s)`,
   REWRITE_TAC [NOT_AND_IMPLIES_lemma]);;

let NOT_AND_IMPLIES_lemma2 = prove_thm
  ("NOT_AND_IMPLIES_lemma2",
   `!(p:'a->bool) q. (!s. (Not (p /\* q))s) ==> (!s. q s ==> Not p s)`,
   REWRITE_TAC [NOT_AND_IMPLIES_lemma; NOT_def1] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REPEAT STRIP_TAC THEN
   RES_TAC);;

let CONJ_DISJ_IMPLY_lemma1 = TAC_PROOF
   (([], `!(p:'a->bool) q s. p s /\ (p s \/ q s) ==> p s`),
   REPEAT STRIP_TAC);;

let CONJ_DISJ_IMPLY_lemma2 = TAC_PROOF
   (([], `!(p:'a->bool) q s. p s ==> p s /\ (p s \/ q s)`),
   REPEAT STRIP_TAC THENL
     [ASM_REWRITE_TAC []; ASM_REWRITE_TAC []]);;

let CONJ_DISJ_IMPLY_lemma = TAC_PROOF
  (([], `!(p:'a->bool) q s. p s /\ (p s \/ q s) <=> p s`),
   REWRITE_TAC [IMP_ANTISYM_RULE
                  (SPEC_ALL CONJ_DISJ_IMPLY_lemma1)
                  (SPEC_ALL CONJ_DISJ_IMPLY_lemma2)]);;

let CONJ_DISJ_ABS_IMPLY_lemma = TAC_PROOF
  (([], `!(p:'a->bool) q.  (\s. p s /\ (p s \/ q s)) = p`),
   REPEAT GEN_TAC THEN
   REWRITE_TAC [CONJ_DISJ_IMPLY_lemma; ETA_AX]);;

let AND_OR_EQ_lemma = prove_thm
  ("AND_OR_EQ_lemma",
   `!(p:'a->bool) q. p /\* (p \/* q) = p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_def; OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC [CONJ_DISJ_ABS_IMPLY_lemma]);;

let AND_OR_EQ_AND_COMM_OR_lemma = prove_thm
  ("AND_OR_EQ_AND_COMM_OR_lemma",
   `!(p:'a->bool) q. p /\* (q \/* p) = p /\* (p \/* q)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [AND_OR_EQ_lemma] THEN
   ONCE_REWRITE_TAC [OR_COMM_lemma] THEN
   REWRITE_TAC [AND_OR_EQ_lemma]);;

let IMPLY_WEAK_lemma = prove_thm
  ("IMPLY_WEAK_lemma",
   `!(p:'a->bool) q. (!s. p s) ==> (!s. (p \/* q) s)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   ASM_REWRITE_TAC []);;

let IMPLY_WEAK_lemma_b = prove_thm
  ("IMPLY_WEAK_lemma_b",
   `!(p:'a->bool) q s. p s ==> (p \/* q) s`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [OR_def] THEN
   CONV_TAC (DEPTH_CONV BETA_CONV) THEN
   ASM_REWRITE_TAC []);;

let ALL_AND_lemma1 = TAC_PROOF
  (([],
   `!(P:num->('a->bool)) i s. (!i. P i s) <=> (P i s /\ (!i. P i s))`),
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      REPEAT STRIP_TAC THENL
        [
         ASM_REWRITE_TAC []
        ;
         ASM_REWRITE_TAC []
        ];
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC []]);;

let ALL_OR_lemma1 = TAC_PROOF
  (([],
   `!(P:num->('a->bool)) i s. (?i. P i s) <=> (P i s \/ (?i. P i s))`),
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [
     REPEAT STRIP_TAC THEN
     DISJ2_TAC THEN
     EXISTS_TAC (`i':num`) THEN
     ASM_REWRITE_TAC []
    ;
     REPEAT STRIP_TAC THENL
     [
       EXISTS_TAC (`i:num`) THEN
       ASM_REWRITE_TAC []
      ;
       EXISTS_TAC (`i:num`) THEN
       ASM_REWRITE_TAC []
     ]
   ]);;

let ALL_OR_lemma = prove_thm
  ("ALL_OR_lemma",
   `!(P:num->('a->bool)) i. (((?*) P) = ((P i) \/* ((?*) P)))`,
   GEN_TAC THEN GEN_TAC THEN
   REWRITE_TAC [EXISTS_def; OR_def] THEN
   BETA_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPECL [P;i] ALL_OR_lemma1)));;

let ALL_i_OR_lemma1 = TAC_PROOF
  (([],
    `!P (s:'a). (?i. \<=/* P i s) = (?i. P i s)`),
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
     [
      STRIP_TAC THEN
      UNDISCH_TAC (`\<=/* (P:num->('a->bool)) i s`) THEN
      SPEC_TAC (i,i) THEN
      INDUCT_TAC THENL
        [
         REWRITE_TAC [OR_LE_N_def] THEN
         DISCH_TAC THEN
         EXISTS_TAC (`0`) THEN
         ASM_REWRITE_TAC []
        ;
         REWRITE_TAC [OR_LE_N_def; OR_def] THEN
         BETA_TAC THEN
         REPEAT STRIP_TAC THENL
           [
            RES_TAC THEN
            EXISTS_TAC (`i':num`) THEN
            ASM_REWRITE_TAC []
           ;
            EXISTS_TAC (`SUC i`) THEN
            ASM_REWRITE_TAC []
           ]
        ]
     ;
      STRIP_TAC THEN
      UNDISCH_TAC (`(P (i:num) (s:'a)):bool`) THEN
      SPEC_TAC (i,i) THEN
      INDUCT_TAC THENL
        [
         DISCH_TAC THEN
         EXISTS_TAC (`0`) THEN
         ASM_REWRITE_TAC [OR_LE_N_def]
        ;
         DISCH_TAC THEN
         EXISTS_TAC (`SUC i`) THEN
         REWRITE_TAC [OR_LE_N_def; OR_def] THEN
         BETA_TAC THEN
         ASM_REWRITE_TAC []
        ]
     ]);;

let ALL_i_OR_lemma = prove_thm
  ("ALL_i_OR_lemma",
   (`!P. ((\s:'a. ?i. \<=/* P i s) = ((?*) P))`),
   REWRITE_TAC [EXISTS_def] THEN
   GEN_TAC THEN
   STRIP_ASSUME_TAC (MK_ABS (SPEC P ALL_i_OR_lemma1)));;
