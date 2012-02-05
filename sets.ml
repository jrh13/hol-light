(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "int.ml";;

(* ------------------------------------------------------------------------- *)
(* Infix symbols for set operations.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("IN",(11,"right"));;
parse_as_infix("SUBSET",(12,"right"));;
parse_as_infix("PSUBSET",(12,"right"));;
parse_as_infix("INTER",(20,"right"));;
parse_as_infix("UNION",(16,"right"));;
parse_as_infix("DIFF",(18,"left"));;
parse_as_infix("INSERT",(21,"right"));;
parse_as_infix("DELETE",(21,"left"));;

parse_as_infix("HAS_SIZE",(12,"right"));;
parse_as_infix("<=_c",(12,"right"));;
parse_as_infix("<_c",(12,"right"));;
parse_as_infix(">=_c",(12,"right"));;
parse_as_infix(">_c",(12,"right"));;
parse_as_infix("=_c",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set membership.                                                           *)
(* ------------------------------------------------------------------------- *)

let IN = new_definition
  `!P:A->bool. !x. x IN P <=> P x`;;

(* ------------------------------------------------------------------------- *)
(* Axiom of extensionality in this framework.                                *)
(* ------------------------------------------------------------------------- *)

let EXTENSION = prove
 (`!s t. (s = t) <=> !x:A. x IN s <=> x IN t`,
  REWRITE_TAC[IN; FUN_EQ_THM]);;

(* ------------------------------------------------------------------------- *)
(* General specification.                                                    *)
(* ------------------------------------------------------------------------- *)

let GSPEC = new_definition
  `GSPEC (p:A->bool) = p`;;

let SETSPEC = new_definition
  `SETSPEC v P t <=> P /\ (v = t)`;;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

let IN_ELIM_THM = prove
 (`(!P x. x IN GSPEC (\v. P (SETSPEC v)) <=> P (\p t. p /\ (x = t))) /\
   (!p x. x IN GSPEC (\v. ?y. SETSPEC v (p y) y) <=> p x) /\
   (!P x. GSPEC (\v. P (SETSPEC v)) x <=> P (\p t. p /\ (x = t))) /\
   (!p x. GSPEC (\v. ?y. SETSPEC v (p y) y) x <=> p x) /\
   (!p x. x IN (\y. p y) <=> p x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN; GSPEC] THEN
  TRY(AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]) THEN
  REWRITE_TAC[SETSPEC] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* These two definitions are needed first, for the parsing of enumerations.  *)
(* ------------------------------------------------------------------------- *)

let EMPTY = new_definition
  `EMPTY = (\x:A. F)`;;

let INSERT_DEF = new_definition
  `x INSERT s = \y:A. y IN s \/ (y = x)`;;

(* ------------------------------------------------------------------------- *)
(* The other basic operations.                                               *)
(* ------------------------------------------------------------------------- *)

let UNIV = new_definition
  `UNIV = (\x:A. T)`;;

let UNION = new_definition
  `s UNION t = {x:A | x IN s \/ x IN t}`;;

let UNIONS = new_definition
  `UNIONS s = {x:A | ?u. u IN s /\ x IN u}`;;

let INTER = new_definition
  `s INTER t = {x:A | x IN s /\ x IN t}`;;

let INTERS = new_definition
  `INTERS s = {x:A | !u. u IN s ==> x IN u}`;;

let DIFF = new_definition
  `s DIFF t =  {x:A | x IN s /\ ~(x IN t)}`;;

let INSERT = prove
 (`x INSERT s = {y:A | y IN s \/ (y = x)}`,
  REWRITE_TAC[EXTENSION; INSERT_DEF; IN_ELIM_THM]);;

let DELETE = new_definition
  `s DELETE x = {y:A | y IN s /\ ~(y = x)}`;;

(* ------------------------------------------------------------------------- *)
(* Other basic predicates.                                                   *)
(* ------------------------------------------------------------------------- *)

let SUBSET = new_definition
  `s SUBSET t <=> !x:A. x IN s ==> x IN t`;;

let PSUBSET = new_definition
  `(s:A->bool) PSUBSET t <=> s SUBSET t /\ ~(s = t)`;;

let DISJOINT = new_definition
  `DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)`;;

let SING = new_definition
  `SING s = ?x:A. s = {x}`;;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

let FINITE_RULES,FINITE_INDUCT,FINITE_CASES =
  new_inductive_definition
    `FINITE (EMPTY:A->bool) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)`;;

let INFINITE = new_definition
  `INFINITE (s:A->bool) <=> ~(FINITE s)`;;

(* ------------------------------------------------------------------------- *)
(* Stuff concerned with functions.                                           *)
(* ------------------------------------------------------------------------- *)

let IMAGE = new_definition
  `IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}`;;

let INJ = new_definition
  `INJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))`;;

let SURJ = new_definition
  `SURJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))`;;

let BIJ = new_definition
  `BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t`;;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

let CHOICE = new_definition
  `CHOICE s = @x:A. x IN s`;;

let REST = new_definition
  `REST (s:A->bool) = s DELETE (CHOICE s)`;;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

let NOT_IN_EMPTY = prove
 (`!x:A. ~(x IN EMPTY)`,
  REWRITE_TAC[IN; EMPTY]);;

let IN_UNIV = prove
 (`!x:A. x IN UNIV`,
  REWRITE_TAC[UNIV; IN]);;

let IN_UNION = prove
 (`!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; UNION]);;

let IN_UNIONS = prove
 (`!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; UNIONS]);;

let IN_INTER = prove
 (`!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM_THM; INTER]);;

let IN_INTERS = prove
 (`!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t`,
  REWRITE_TAC[IN_ELIM_THM; INTERS]);;

let IN_DIFF = prove
 (`!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\ ~(x IN t)`,
  REWRITE_TAC[IN_ELIM_THM; DIFF]);;

let IN_INSERT = prove
 (`!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s`,
  ONCE_REWRITE_TAC[DISJ_SYM] THEN REWRITE_TAC[IN_ELIM_THM; INSERT]);;

let IN_DELETE = prove
 (`!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)`,
  REWRITE_TAC[IN_ELIM_THM; DELETE]);;

let IN_SING = prove
 (`!x y. x IN {y:A} <=> (x = y)`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

let IN_IMAGE = prove
 (`!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s`,
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[IN_ELIM_THM; IMAGE]);;

let IN_REST = prove
 (`!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)`,
  REWRITE_TAC[REST; IN_DELETE]);;

let FORALL_IN_INSERT = prove
 (`!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x)`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

let EXISTS_IN_INSERT = prove
 (`!P a s. (?x. x IN (a INSERT s) /\ P x) <=> P a \/ ?x. x IN s /\ P x`,
  REWRITE_TAC[IN_INSERT] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic property of the choice function.                                    *)
(* ------------------------------------------------------------------------- *)

let CHOICE_DEF = prove
 (`!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s`,
  REWRITE_TAC[CHOICE; EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM; EXISTS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to automate some routine set theory by reduction to FOL.           *)
(* ------------------------------------------------------------------------- *)

let SET_TAC =
  let PRESET_TAC =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                IN_ELIM_THM; IN] in
  fun ths ->
    (if ths = [] then ALL_TAC else MP_TAC(end_itlist CONJ ths)) THEN
    PRESET_TAC THEN
    MESON_TAC[];;

let SET_RULE tm = prove(tm,SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc. theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

let NOT_EQUAL_SETS = prove
 (`!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The empty set.                                                            *)
(* ------------------------------------------------------------------------- *)

let MEMBER_NOT_EMPTY = prove
 (`!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The universal set.                                                        *)
(* ------------------------------------------------------------------------- *)

let UNIV_NOT_EMPTY = prove
 (`~(UNIV:A->bool = EMPTY)`,
  SET_TAC[]);;

let EMPTY_NOT_UNIV = prove
 (`~(EMPTY:A->bool = UNIV)`,
  SET_TAC[]);;

let EQ_UNIV = prove
 (`(!x:A. x IN s) <=> (s = UNIV)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set inclusion.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBSET_TRANS = prove
 (`!(s:A->bool) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`,
  SET_TAC[]);;

let SUBSET_REFL = prove
 (`!s:A->bool. s SUBSET s`,
  SET_TAC[]);;

let SUBSET_ANTISYM = prove
 (`!(s:A->bool) t. s SUBSET t /\ t SUBSET s ==> s = t`,
  SET_TAC[]);;

let SUBSET_ANTISYM_EQ = prove
 (`!(s:A->bool) t. s SUBSET t /\ t SUBSET s <=> s = t`,
  SET_TAC[]);;

let EMPTY_SUBSET = prove
 (`!s:A->bool. EMPTY SUBSET s`,
  SET_TAC[]);;

let SUBSET_EMPTY = prove
 (`!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)`,
  SET_TAC[]);;

let SUBSET_UNIV = prove
 (`!s:A->bool. s SUBSET UNIV`,
  SET_TAC[]);;

let UNIV_SUBSET = prove
 (`!s:A->bool. UNIV SUBSET s <=> (s = UNIV)`,
  SET_TAC[]);;

let SING_SUBSET = prove
 (`!s x. {x} SUBSET s <=> x IN s`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Proper subset.                                                            *)
(* ------------------------------------------------------------------------- *)

let PSUBSET_TRANS = prove
 (`!(s:A->bool) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

let PSUBSET_SUBSET_TRANS = prove
 (`!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

let SUBSET_PSUBSET_TRANS = prove
 (`!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

let PSUBSET_IRREFL = prove
 (`!s:A->bool. ~(s PSUBSET s)`,
  SET_TAC[]);;

let NOT_PSUBSET_EMPTY = prove
 (`!s:A->bool. ~(s PSUBSET EMPTY)`,
  SET_TAC[]);;

let NOT_UNIV_PSUBSET = prove
 (`!s:A->bool. ~(UNIV PSUBSET s)`,
  SET_TAC[]);;

let PSUBSET_UNIV = prove
 (`!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)`,
  SET_TAC[]);;

let PSUBSET_ALT = prove
 (`!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`,
  REWRITE_TAC[PSUBSET] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let UNION_ASSOC = prove
 (`!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)`,
  SET_TAC[]);;

let UNION_IDEMPOT = prove
 (`!s:A->bool. s UNION s = s`,
  SET_TAC[]);;

let UNION_COMM = prove
 (`!(s:A->bool) t. s UNION t = t UNION s`,
  SET_TAC[]);;

let SUBSET_UNION = prove
 (`(!s:A->bool. !t. s SUBSET (s UNION t)) /\
   (!s:A->bool. !t. s SUBSET (t UNION s))`,
  SET_TAC[]);;

let SUBSET_UNION_ABSORPTION = prove
 (`!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)`,
  SET_TAC[]);;

let UNION_EMPTY = prove
 (`(!s:A->bool. EMPTY UNION s = s) /\
   (!s:A->bool. s UNION EMPTY = s)`,
  SET_TAC[]);;

let UNION_UNIV = prove
 (`(!s:A->bool. UNIV UNION s = UNIV) /\
   (!s:A->bool. s UNION UNIV = UNIV)`,
  SET_TAC[]);;

let EMPTY_UNION = prove
 (`!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`,
  SET_TAC[]);;

let UNION_SUBSET = prove
 (`!s t u. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let INTER_ASSOC = prove
 (`!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)`,
  SET_TAC[]);;

let INTER_IDEMPOT = prove
 (`!s:A->bool. s INTER s = s`,
  SET_TAC[]);;

let INTER_COMM = prove
 (`!(s:A->bool) t. s INTER t = t INTER s`,
  SET_TAC[]);;

let INTER_SUBSET = prove
 (`(!s:A->bool. !t. (s INTER t) SUBSET s) /\
   (!s:A->bool. !t. (t INTER s) SUBSET s)`,
  SET_TAC[]);;

let SUBSET_INTER_ABSORPTION = prove
 (`!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)`,
  SET_TAC[]);;

let INTER_EMPTY = prove
 (`(!s:A->bool. EMPTY INTER s = EMPTY) /\
   (!s:A->bool. s INTER EMPTY = EMPTY)`,
  SET_TAC[]);;

let INTER_UNIV = prove
 (`(!s:A->bool. UNIV INTER s = s) /\
   (!s:A->bool. s INTER UNIV = s)`,
  SET_TAC[]);;

let SUBSET_INTER = prove
 (`!s t u. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNION_OVER_INTER = prove
 (`!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`,
  SET_TAC[]);;

let INTER_OVER_UNION = prove
 (`!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let IN_DISJOINT = prove
 (`!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`,
  SET_TAC[]);;

let DISJOINT_SYM = prove
 (`!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s`,
  SET_TAC[]);;

let DISJOINT_EMPTY = prove
 (`!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY`,
  SET_TAC[]);;

let DISJOINT_EMPTY_REFL = prove
 (`!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)`,
  SET_TAC[]);;

let DISJOINT_UNION = prove
 (`!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_EMPTY = prove
 (`!s:A->bool. s DIFF EMPTY = s`,
  SET_TAC[]);;

let EMPTY_DIFF = prove
 (`!s:A->bool. EMPTY DIFF s = EMPTY`,
  SET_TAC[]);;

let DIFF_UNIV = prove
 (`!s:A->bool. s DIFF UNIV = EMPTY`,
  SET_TAC[]);;

let DIFF_DIFF = prove
 (`!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t`,
  SET_TAC[]);;

let DIFF_EQ_EMPTY = prove
 (`!s:A->bool. s DIFF s = EMPTY`,
  SET_TAC[]);;

let SUBSET_DIFF = prove
 (`!s t. (s DIFF t) SUBSET s`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Insertion and deletion.                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPONENT = prove
 (`!x:A. !s. x IN (x INSERT s)`,
  SET_TAC[]);;

let DECOMPOSITION = prove
 (`!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN EXISTS_TAC `s DELETE x:A` THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let SET_CASES = prove
 (`!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`,
  MESON_TAC[MEMBER_NOT_EMPTY; DECOMPOSITION]);;

let ABSORPTION = prove
 (`!x:A. !s. x IN s <=> (x INSERT s = s)`,
  SET_TAC[]);;

let INSERT_INSERT = prove
 (`!x:A. !s. x INSERT (x INSERT s) = x INSERT s`,
  SET_TAC[]);;

let INSERT_COMM = prove
 (`!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`,
  SET_TAC[]);;

let INSERT_UNIV = prove
 (`!x:A. x INSERT UNIV = UNIV`,
  SET_TAC[]);;

let NOT_INSERT_EMPTY = prove
 (`!x:A. !s. ~(x INSERT s = EMPTY)`,
  SET_TAC[]);;

let NOT_EMPTY_INSERT = prove
 (`!x:A. !s. ~(EMPTY = x INSERT s)`,
  SET_TAC[]);;

let INSERT_UNION = prove
 (`!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let INSERT_UNION_EQ = prove
 (`!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`,
  SET_TAC[]);;

let INSERT_INTER = prove
 (`!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let DISJOINT_INSERT = prove
 (`!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)`,
  SET_TAC[]);;

let INSERT_SUBSET = prove
 (`!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`,
  SET_TAC[]);;

let SUBSET_INSERT = prove
 (`!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`,
  SET_TAC[]);;

let INSERT_DIFF = prove
 (`!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let INSERT_AC = prove
 (`(x INSERT (y INSERT s) = y INSERT (x INSERT s)) /\
   (x INSERT (x INSERT s) = x INSERT s)`,
  REWRITE_TAC[INSERT_COMM; INSERT_INSERT]);;

let INTER_ACI = prove
 (`(p INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)`,
  SET_TAC[]);;

let UNION_ACI = prove
 (`(p UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)`,
  SET_TAC[]);;

let DELETE_NON_ELEMENT = prove
 (`!x:A. !s. ~(x IN s) <=> (s DELETE x = s)`,
  SET_TAC[]);;

let IN_DELETE_EQ = prove
 (`!s x. !x':A.
     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))`,
  SET_TAC[]);;

let EMPTY_DELETE = prove
 (`!x:A. EMPTY DELETE x = EMPTY`,
  SET_TAC[]);;

let DELETE_DELETE = prove
 (`!x:A. !s. (s DELETE x) DELETE x = s DELETE x`,
  SET_TAC[]);;

let DELETE_COMM = prove
 (`!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`,
  SET_TAC[]);;

let DELETE_SUBSET = prove
 (`!x:A. !s. (s DELETE x) SUBSET s`,
  SET_TAC[]);;

let SUBSET_DELETE = prove
 (`!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)`,
  SET_TAC[]);;

let SUBSET_INSERT_DELETE = prove
 (`!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`,
  SET_TAC[]);;

let DIFF_INSERT = prove
 (`!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`,
  SET_TAC[]);;

let PSUBSET_INSERT_SUBSET = prove
 (`!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`,
  SET_TAC[]);;

let PSUBSET_MEMBER = prove
 (`!s:A->bool. !t. s PSUBSET t <=> (s SUBSET t /\ ?y. y IN t /\ ~(y IN s))`,
  SET_TAC[]);;

let DELETE_INSERT = prove
 (`!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

let INSERT_DELETE = prove
 (`!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`,
  SET_TAC[]);;

let DELETE_INTER = prove
 (`!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`,
  SET_TAC[]);;

let DISJOINT_DELETE_SYM = prove
 (`!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNIONS_0 = prove
 (`UNIONS {} = {}`,
  SET_TAC[]);;

let UNIONS_1 = prove
 (`UNIONS {s} = s`,
  SET_TAC[]);;

let UNIONS_2 = prove
 (`UNIONS {s,t} = s UNION t`,
  SET_TAC[]);;

let UNIONS_INSERT = prove
 (`UNIONS (s INSERT u) = s UNION (UNIONS u)`,
  SET_TAC[]);;

let FORALL_IN_UNIONS = prove
 (`!P s. (!x. x IN UNIONS s ==> P x) <=> !t x. t IN s /\ x IN t ==> P x`,
  SET_TAC[]);;

let EXISTS_IN_UNIONS = prove
 (`!P s. (?x. x IN UNIONS s /\ P x) <=> (?t x. t IN s /\ x IN t /\ P x)`,
  SET_TAC[]);;

let EMPTY_UNIONS = prove
 (`!s. (UNIONS s = {}) <=> !t. t IN s ==> t = {}`,
  SET_TAC[]);;

let INTER_UNIONS = prove
 (`(!s t. UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\
   (!s t. t INTER UNIONS s = UNIONS {t INTER x | x IN s})`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  MESON_TAC[IN_INTER]);;

let UNIONS_SUBSET = prove
 (`!f t. UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`,
  SET_TAC[]);;

let SUBSET_UNIONS = prove
 (`!f g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`,
  SET_TAC[]);;

let UNIONS_UNION = prove
 (`!s t. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)`,
  SET_TAC[]);;

let INTERS_UNION = prove
 (`!s t. INTERS (s UNION t) = INTERS s INTER INTERS t`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

let INTERS_0 = prove
 (`INTERS {} = (:A)`,
  SET_TAC[]);;

let INTERS_1 = prove
 (`INTERS {s} = s`,
  SET_TAC[]);;

let INTERS_2 = prove
 (`INTERS {s,t} = s INTER t`,
  SET_TAC[]);;

let INTERS_INSERT = prove
 (`INTERS (s INSERT u) = s INTER (INTERS u)`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLAUSES = prove
 (`(IMAGE f {} = {}) /\
   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))`,
  REWRITE_TAC[IMAGE; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT; EXTENSION] THEN
  MESON_TAC[]);;

let IMAGE_UNION = prove
 (`!f s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION] THEN MESON_TAC[]);;

let IMAGE_ID = prove
 (`!s. IMAGE (\x. x) s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNWIND_THM1]);;

let IMAGE_I = prove
 (`!s. IMAGE I s = s`,
  REWRITE_TAC[I_DEF; IMAGE_ID]);;

let IMAGE_o = prove
 (`!f g s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN MESON_TAC[]);;

let IMAGE_SUBSET = prove
 (`!f s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

let IMAGE_INTER_INJ = prove
 (`!f s t. (!x y. (f(x) = f(y)) ==> (x = y))
           ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN MESON_TAC[]);;

let IMAGE_DIFF_INJ = prove
 (`!f s t. (!x y. (f(x) = f(y)) ==> (x = y))
           ==> (IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN MESON_TAC[]);;

let IMAGE_DELETE_INJ = prove
 (`!f s a. (!x. (f(x) = f(a)) ==> (x = a))
           ==> (IMAGE f (s DELETE a) = (IMAGE f s) DELETE (f a))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN MESON_TAC[]);;

let IMAGE_EQ_EMPTY = prove
 (`!f s. (IMAGE f s = {}) <=> (s = {})`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[]);;

let FORALL_IN_IMAGE = prove
 (`!f s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let EXISTS_IN_IMAGE = prove
 (`!f s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let SUBSET_IMAGE = prove
 (`!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[IMAGE_SUBSET]] THEN
  DISCH_TAC THEN EXISTS_TAC `{x | x IN t /\ (f:A->B) x IN s}` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let FORALL_SUBSET_IMAGE = prove
 (`!P f s. (!t. t SUBSET IMAGE f s ==> P t) <=>
           (!t. t SUBSET s ==> P(IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

let EXISTS_SUBSET_IMAGE = prove
 (`!P f s.
    (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

let IMAGE_CONST = prove
 (`!s c. IMAGE (\x. c) s = if s = {} then {} else {c}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

let SIMPLE_IMAGE = prove
 (`!f s. {f x | x IN s} = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

let SIMPLE_IMAGE_GEN = prove
 (`!f P. {f x | P x} = IMAGE f {x | P x}`,
  SET_TAC[]);;

let IMAGE_UNIONS = prove
 (`!f s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`,
  ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_IMAGE] THEN
  MESON_TAC[]);;

let FUN_IN_IMAGE = prove
 (`!f s x. x IN s ==> f(x) IN IMAGE f s`,
  SET_TAC[]);;

let SURJECTIVE_IMAGE_EQ = prove
 (`!s t. (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
         ==> IMAGE f s = t`,
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let EMPTY_GSPEC = prove
 (`{x | F} = {}`,
  SET_TAC[]);;

let SING_GSPEC = prove
 (`(!a. {x | x = a} = {a}) /\
   (!a. {x | a = x} = {a})`,
  SET_TAC[]);;

let IN_ELIM_PAIR_THM = prove
 (`!P a b. (a,b) IN {(x,y) | P x y} <=> P a b`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PAIR_EQ]);;

let SET_PAIR_THM = prove
 (`!P. {p | P p} = {(a,b) | P(a,b)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM]);;

let FORALL_IN_GSPEC = prove
 (`(!P f. (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P f. (!z. z IN {f x y | P x y} ==> Q z) <=>
          (!x y. P x y ==> Q(f x y))) /\
   (!P f. (!z. z IN {f w x y | P w x y} ==> Q z) <=>
          (!w x y. P w x y ==> Q(f w x y)))`,
  SET_TAC[]);;

let EXISTS_IN_GSPEC = prove
 (`(!P f. (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P f. (?z. z IN {f x y | P x y} /\ Q z) <=>
          (?x y. P x y /\ Q(f x y))) /\
   (!P f. (?z. z IN {f w x y | P w x y} /\ Q z) <=>
          (?w x y. P w x y /\ Q(f w x y)))`,
  SET_TAC[]);;

let SET_PROVE_CASES = prove
 (`!P:(A->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s`,
  MESON_TAC[SET_CASES]);;

let UNIONS_IMAGE = prove
 (`!f s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERS_IMAGE = prove
 (`!f s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let UNIONS_GSPEC = prove
 (`(!P f. UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P f. UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P f. UNIONS {f x y z | P x y z} =
            {a | ?x y z. P x y z /\ a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERS_GSPEC = prove
 (`(!P f. INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P f. INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P f. INTERS {f x y z | P x y z} =
                {a | !x y z. P x y z ==> a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

let DIFF_INTERS = prove
 (`!u s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let INTERS_UNIONS = prove
 (`!s. INTERS s = UNIV DIFF (UNIONS {UNIV DIFF t | t IN s})`,
  REWRITE_TAC[GSYM DIFF_INTERS] THEN SET_TAC[]);;

let UNIONS_INTERS = prove
 (`!s. UNIONS s = UNIV DIFF (INTERS {UNIV DIFF t | t IN s})`,
  GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_UNIV; IN_DIFF; INTERS_GSPEC; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let DIFF_UNIONS = prove
 (`!s t. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}`,
  REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]);;

let INTERS_OVER_UNIONS = prove
 (`!f:A->(B->bool)->bool s.
        INTERS { UNIONS(f x) | x IN s} =
        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; INTERS_IMAGE; UNIONS_IMAGE; UNIONS_GSPEC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `b:B` THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_STRONG = prove
 (`!P:(A->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:A->bool. FINITE s ==> FINITE s /\ P s` MP_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN ASM_SIMP_TAC[FINITE_RULES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `x:A INSERT s = s` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_EMPTY = prove
 (`FINITE {}`,
  REWRITE_TAC[FINITE_RULES]);;

let FINITE_SUBSET = prove
 (`!(s:A->bool) t. FINITE t /\ s SUBSET t ==> FINITE s`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [MESON_TAC[SUBSET_EMPTY; FINITE_RULES]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE((x:A) INSERT (t DELETE x))` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t SUBSET (x:A INSERT u)` THEN SET_TAC[];
    ASM_CASES_TAC `x:A IN t` THENL
     [SUBGOAL_THEN `x:A INSERT (t DELETE x) = t` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `x:A IN t` THEN SET_TAC[]; ASM_REWRITE_TAC[]];
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `t SUBSET x:A INSERT u` THEN
      UNDISCH_TAC `~(x:A IN t)` THEN SET_TAC[]]]);;

let FINITE_UNION_IMP = prove
 (`!(s:A->bool) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[UNION_EMPTY] THEN
  SUBGOAL_THEN `!x s t. (x:A INSERT s) UNION t = x INSERT (s UNION t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [SET_TAC[];
    MESON_TAC[FINITE_RULES]]);;

let FINITE_UNION = prove
 (`!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(s:A->bool) UNION t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_ACCEPT_TAC FINITE_UNION_IMP]);;

let FINITE_INTER = prove
 (`!(s:A->bool) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)`,
  MESON_TAC[INTER_SUBSET; FINITE_SUBSET]);;

let FINITE_INSERT = prove
 (`!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `x:A INSERT s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    ASM_REWRITE_TAC[]]);;

let FINITE_SING = prove
 (`!a. FINITE {a}`,
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let FINITE_DELETE_IMP = prove
 (`!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let FINITE_DELETE = prove
 (`!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_DELETE_IMP] THEN
  ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `s = x INSERT (s DELETE x:A)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[FINITE_INSERT] THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    SUBGOAL_THEN `s DELETE x:A = s` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN SET_TAC[]]);;

let FINITE_FINITE_UNIONS = prove
 (`!s. FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; UNIONS_0; UNIONS_INSERT] THEN
  REWRITE_TAC[FINITE_UNION; FINITE_RULES] THEN MESON_TAC[]);;

let FINITE_IMAGE_EXPAND = prove
 (`!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY; REWRITE_RULE[] EMPTY_GSPEC; FINITE_RULES] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y | ?z. z IN (x INSERT s) /\ (y = (f:A->B) z)} =
                {y | ?z. z IN s /\ (y = f z)} UNION {(f x)}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_RULES]]);;

let FINITE_IMAGE = prove
 (`!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)`,
  REWRITE_TAC[IMAGE; FINITE_IMAGE_EXPAND]);;

let FINITE_IMAGE_INJ_GENERAL = prove
 (`!(f:A->B) A s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                  FINITE A ==> FINITE {x | x IN s /\ f(x) IN A}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{x | x IN s /\ (f:A->B) x IN EMPTY} = EMPTY`
    SUBST1_TAC THEN REWRITE_TAC[FINITE_RULES] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN X_GEN_TAC `t:B->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:A->B) x IN (y INSERT t)} =
                if (?x. x IN s /\ (f x = y))
                then (@x. x IN s /\ (f x = y)) INSERT {x | x IN s /\ f x IN t}
                else {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `z = @x. x IN s /\ ((f:A->B) x = y)` THEN
  ASM_MESON_TAC[]);;

let FINITE_FINITE_PREIMAGE_GENERAL = prove
 (`!f:A->B s t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | x IN s /\ f(x) = y})
        ==> FINITE {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:A->B)(x) IN t} =
    UNIONS (IMAGE (\a. {x | x IN s /\ f x = a}) t)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN SET_TAC[];
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE]]);;

let FINITE_FINITE_PREIMAGE = prove
 (`!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}`,
  REPEAT GEN_TAC THEN MP_TAC
   (ISPECL [`f:A->B`; `(:A)`; `t:B->bool`] FINITE_FINITE_PREIMAGE_GENERAL) THEN
  REWRITE_TAC[IN_UNIV]);;

let FINITE_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
                ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let FINITE_IMAGE_INJ = prove
 (`!(f:A->B) A. (!x y. (f(x) = f(y)) ==> (x = y)) /\
                FINITE A ==> FINITE {x | f(x) IN A}`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`f:A->B`; `A:B->bool`; `UNIV:A->bool`]
    FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]);;

let INFINITE_IMAGE_INJ = prove
 (`!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x | f(x) IN IMAGE (f:A->B) s}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IMAGE] THEN MESON_TAC[]]);;

let INFINITE_NONEMPTY = prove
 (`!s. INFINITE(s) ==> ~(s = EMPTY)`,
  MESON_TAC[INFINITE; FINITE_RULES]);;

let INFINITE_DIFF_FINITE = prove
 (`!s:A->bool t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(b /\ ~c ==> ~a) ==> a /\ b ==> c`) THEN
  REWRITE_TAC[INFINITE] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(t:A->bool) UNION (s DIFF t)` THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN SET_TAC[]);;

let FINITE_SUBSET_IMAGE = prove
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FINITE_IMAGE; IMAGE_SUBSET]] THEN
  STRIP_TAC THEN
  EXISTS_TAC `IMAGE (\y. @x. x IN s /\ ((f:A->B)(x) = y)) t` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[EXTENSION; SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `y:B` THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  ASM_MESON_TAC[SUBSET; IN_IMAGE]);;

let EXISTS_FINITE_SUBSET_IMAGE = prove
 (`!P f s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))`,
  REWRITE_TAC[FINITE_SUBSET_IMAGE; CONJ_ASSOC] THEN MESON_TAC[]);;

let FINITE_SUBSET_IMAGE_IMP = prove
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')`,
  MESON_TAC[SUBSET_REFL; FINITE_SUBSET_IMAGE]);;

let FINITE_DIFF = prove
 (`!s t. FINITE s ==> FINITE(s DIFF t)`,
  MESON_TAC[FINITE_SUBSET; SUBSET_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

let FINREC = new_recursive_definition num_RECURSION
  `(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))`;;

let FINREC_1_LEMMA = prove
 (`!f b s a. FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\ (a = f x b)`,
  REWRITE_TAC[FINREC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

let FINREC_SUC_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)`,
  let lem = prove(`s DELETE (x:A) DELETE y = s DELETE y DELETE x`,SET_TAC[]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC_1_LEMMA] THEN REWRITE_TAC[FINREC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `b:B` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [FINREC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `c:B` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `FINREC (f:A->B->B) b (s DELETE y) c (SUC n)` THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:A->B->B) y v` THEN ASM_REWRITE_TAC[FINREC] THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`y:A`; `v:B`] THEN
        ONCE_REWRITE_TAC[lem] THEN ASM_REWRITE_TAC[IN_DELETE];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let FINREC_UNIQUE_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
    REWRITE_TAC[FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

let FINREC_EXISTS_LEMMA = prove
 (`!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n`,
  let lem = prove(`~(x IN s ) ==> ((x:A INSERT s) DELETE x = s)`,SET_TAC[]) in
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:B`; `0`] THEN REWRITE_TAC[FINREC];
    MAP_EVERY EXISTS_TAC [`(f:A->B->B) x a`; `SUC n`] THEN
    REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [`x:A`; `a:B`] THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP lem th; IN_INSERT])]);;

let FINREC_FUN_LEMMA = prove
 (`!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\s:A. @a:B. ?n:C. R s a n` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC[]]);;

let FINREC_FUN = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))`,
  REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
  DISCH_THEN(MP_TAC o SPEC `b:B`) THEN DISCH_THEN
   (MP_TAC o CONJ (SPECL [`f:A->B->B`; `b:B`] FINREC_EXISTS_LEMMA)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:(A->bool)->B`) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `FINITE(EMPTY:A->bool)`
    (ANTE_RES_THEN (fun th -> GEN_REWRITE_TAC I [GSYM th])) THENL
     [REWRITE_TAC[FINITE_RULES];
      EXISTS_TAC `0` THEN REWRITE_TAC[FINREC]];
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME `FINITE(s:A->bool)`) THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g:(A->bool)->B) s`) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THENL
     [ASM_REWRITE_TAC[FINREC] THEN DISCH_TAC THEN UNDISCH_TAC `x:A IN s` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY];
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN `(g (s DELETE x:A) = w:B)` SUBST1_TAC THENL
       [SUBGOAL_THEN `FINITE(s DELETE x:A)` MP_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          DISCH_THEN(ANTE_RES_THEN (MP_TAC o GSYM)) THEN
          DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
          EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]]]);;

let SET_RECURSION_LEMMA = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `b:B` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ABSORPTION] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `FINITE(x:A INSERT s) /\ x IN (x INSERT s)` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[FINITE_RULES];
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]]);;

let ITSET = new_definition
  `ITSET f s b =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s`;;

let FINITE_RECURSION = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ITSET] THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC SET_RECURSION_LEMMA THEN
  ASM_REWRITE_TAC[]);;

let FINITE_RECURSION_DELETE = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f s b =
                       if x IN s then f x (ITSET f (s DELETE x) b)
                                 else ITSET f (s DELETE x) b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FINITE_RECURSION) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o SPEC `b:B`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN s` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o MATCH_MP FINITE_DELETE_IMP) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC o SPEC `x:A`) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    REWRITE_TAC[IN_DELETE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

let ITSET_EQ = prove
 (`!s f g b. FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
             (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
             (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
             ==> (ITSET f s b = ITSET g s b)`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FINITE_RECURSION; NOT_IN_EMPTY; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
  ASM_MESON_TAC[]);;

let SUBSET_RESTRICT = prove
 (`!s P. {x | x IN s /\ P x} SUBSET s`,
  SIMP_TAC[SUBSET; IN_ELIM_THM]);;

let FINITE_RESTRICT = prove
 (`!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}`,
  MESON_TAC[SUBSET_RESTRICT; FINITE_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

let CARD = new_definition
 `CARD s = ITSET (\x n. SUC n) s 0`;;

let CARD_CLAUSES = prove
 (`(CARD ({}:A->bool) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))`,
  MP_TAC(ISPECL [`\(x:A) n. SUC n`; `0`] FINITE_RECURSION) THEN
  REWRITE_TAC[CARD]);;

let CARD_UNION = prove
 (`!(s:A->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; CARD_CLAUSES; INTER_EMPTY; ADD_CLAUSES] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `s:A->bool` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A INSERT s) UNION t = x INSERT (s UNION t)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((s:A->bool) UNION t) /\ FINITE s`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_UNION_IMP THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool`] (CONJUNCT2 CARD_CLAUSES)) THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool UNION t`] (CONJUNCT2 CARD_CLAUSES)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:A IN (s UNION t))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `(x:A INSERT s) INTER t = EMPTY` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[SUC_INJ; ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x:A INSERT s INTER t = EMPTY` THEN SET_TAC[]]);;

let CARD_DELETE = prove
 (`!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `s = x:A INSERT (s DELETE x)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [UNDISCH_TAC `x:A IN s` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; IN_DELETE; SUC_SUB1];
    AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

let CARD_UNION_EQ = prove
 (`!s t u. FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
           ==> (CARD s + CARD t = CARD u)`,
  MESON_TAC[CARD_UNION; FINITE_SUBSET; SUBSET_UNION]);;

let CARD_DIFF = prove
 (`!s t. FINITE s /\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a + b:num = c ==> a = c - b`) THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

let CARD_EQ_0 = prove
 (`!s. FINITE s ==> ((CARD s = 0) <=> (s = {}))`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_INSERT_EMPTY; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_DELETE = prove
 (`!P. P {} /\
       (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (P(s DELETE x) ==> P s))
       ==> !s:A->bool. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(s:A->bool)` THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!s. FINITE s /\ ~(s = {}) ==> ?x:A. x IN s /\ (P(s DELETE x) ==> P s)` THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (x:A)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; CARD_EQ_0;
               ARITH_RULE `n - 1 < n <=> ~(n = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE = new_definition
  `s HAS_SIZE n <=> FINITE s /\ (CARD s = n)`;;

let HAS_SIZE_CARD = prove
 (`!s n. s HAS_SIZE n ==> (CARD s = n)`,
  SIMP_TAC[HAS_SIZE]);;

let HAS_SIZE_0 = prove
 (`!(s:A->bool). s HAS_SIZE 0 <=> (s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[FINITE_RULES; CARD_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
  ASM_REWRITE_TAC[NOT_SUC]);;

let HAS_SIZE_SUC = prove
 (`!(s:A->bool) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; NOT_SUC] THEN
  REWRITE_TAC[FINITE_DELETE] THEN
  ASM_CASES_TAC `FINITE(s:A->bool)` THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; MEMBER_NOT_EMPTY] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_REWRITE_TAC[SUC_INJ] THEN MESON_TAC[]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

let HAS_SIZE_UNION = prove
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
             ==> (s UNION t) HAS_SIZE (m + n)`,
  SIMP_TAC[HAS_SIZE; FINITE_UNION; DISJOINT; CARD_UNION]);;

let HAS_SIZE_DIFF = prove
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
             ==> (s DIFF t) HAS_SIZE (m - n)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF]);;

let HAS_SIZE_UNIONS = prove
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CARD_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0; EMPTY_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `m:num`; `n:num`] THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}`] THEN
  REWRITE_TAC[ARITH_RULE `SUC a * b = b + a * b`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN ASM_SIMP_TAC[IN_INSERT] THEN
  REWRITE_TAC[SET_RULE
   `DISJOINT a (UNIONS s) <=> !x. x IN s ==> DISJOINT a x`] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_INSERT]);;

let FINITE_HAS_SIZE = prove
 (`!s. FINITE s <=> s HAS_SIZE CARD s`,
  REWRITE_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CLAUSES = prove
 (`(s HAS_SIZE 0 <=> (s = {})) /\
   (s HAS_SIZE (SUC n) <=>
        ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,
  let lemma = SET_RULE `a IN s ==> (s = a INSERT (s DELETE a))` in
  REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[lemma; IN_DELETE];
    SIMP_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONV =
  let pth = prove
   (`(~(a IN {}) /\ P <=> P) /\
     (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
     (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)`,
    SET_TAC[])
  and qth = prove
   (`((?s. s HAS_SIZE 0 /\ P s) <=> P {}) /\
     ((?s. s HAS_SIZE (SUC n) /\ P s) <=>
      (?a s. s HAS_SIZE n /\ ~(a IN s) /\ P(a INSERT s)))`,
    REWRITE_TAC[HAS_SIZE_CLAUSES] THEN MESON_TAC[]) in
  let qconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 qth]
  and qconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 qth]
  and rconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and rconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec EXISTS_HAS_SIZE_AND_CONV tm =
   (qconv_0 ORELSEC
    (BINDER_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
     qconv_1 THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV)) tm in
  let rec NOT_IN_INSERT_CONV tm =
   ((rconv_0 THENC NOT_IN_INSERT_CONV) ORELSEC
    (rconv_1 THENC RAND_CONV NOT_IN_INSERT_CONV) ORELSEC
    ALL_CONV) tm in
  let HAS_SIZE_CONV =
    GEN_REWRITE_CONV I [CONJUNCT1 HAS_SIZE_CLAUSES] ORELSEC
    (RAND_CONV num_CONV THENC
     GEN_REWRITE_CONV I [CONJUNCT2 HAS_SIZE_CLAUSES] THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV) in
  fun tm ->
    let th = HAS_SIZE_CONV tm in
    let tm' = rand(concl th) in
    let evs,bod = strip_exists tm' in
    if evs = [] then th else
    let th' = funpow (length evs) BINDER_CONV NOT_IN_INSERT_CONV tm' in
    TRANS th th';;

(* ------------------------------------------------------------------------- *)
(* Various useful lemmas about cardinalities of unions etc.                  *)
(* ------------------------------------------------------------------------- *)

let CARD_SUBSET_EQ = prove
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:A->bool`; `b DIFF (a:A->bool)`] CARD_UNION) THEN
  SUBGOAL_THEN `FINITE(a:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(b:A->bool DIFF a)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a:A->bool INTER (b DIFF a) = EMPTY` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a UNION (b:A->bool DIFF a) = b` ASSUME_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(a = a + b) <=> (b = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `b:A->bool DIFF a = EMPTY` MP_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE_0] THEN
    ASM_REWRITE_TAC[HAS_SIZE];
    UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]]);;

let CARD_SUBSET = prove
 (`!(a:A->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b:A->bool = a UNION (b DIFF a)` SUBST1_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (a UNION b DIFF a) = CARD(a:A->bool) + CARD(b DIFF a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    ARITH_TAC]);;

let CARD_SUBSET_LE = prove
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD b <= CARD a) ==> (a = b)`,
  MESON_TAC[CARD_SUBSET; CARD_SUBSET_EQ; LE_ANTISYM]);;

let SUBSET_CARD_EQ = prove
 (`!s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)`,
  MESON_TAC[CARD_SUBSET_EQ; LE_ANTISYM; CARD_SUBSET]);;

let CARD_PSUBSET = prove
 (`!(a:A->bool) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
   `a PSUBSET b <=> ?x. x IN b /\ ~(x IN a) /\ a SUBSET (b DELETE x)` ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(b DELETE (x:A))` THEN
  ASM_SIMP_TAC[CARD_SUBSET; FINITE_DELETE] THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]);;

let CARD_UNION_LE = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(s:A->bool) + CARD(t DIFF s)` THEN
  ASM_SIMP_TAC[LE_ADD_LCANCEL; CARD_SUBSET; SUBSET_DIFF; FINITE_DIFF] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

let CARD_UNIONS_LE = prove
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n)
        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THEN
  REWRITE_TAC[SET_RULE `UNIONS {t x | x IN {}} = {}`; CARD_CLAUSES; LE_0] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t x | x IN a INSERT s} = t(a) UNION UNIONS {t x | x IN s}`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC
   `CARD((t:A->B->bool) x) + CARD(UNIONS {(t:A->B->bool) y | y IN s})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC[IN_INSERT] THEN
    REWRITE_TAC[SET_RULE `{t x | x IN s} = IMAGE t s`] THEN
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 IN_INSERT];
    MATCH_MP_TAC(ARITH_RULE `a <= n /\ b <= x * n ==> a + b <= SUC x * n`) THEN
    ASM_SIMP_TAC[IN_INSERT]]);;

let CARD_UNION_GEN = prove
 (`!s t. FINITE s /\ FINITE t
         ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `x:num <= y ==> (a + y) - x = a + (y - x)`;
               CARD_SUBSET; INTER_SUBSET; GSYM CARD_DIFF] THEN
  REWRITE_TAC[SET_RULE `t DIFF (s INTER t) = t DIFF s`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

let CARD_UNION_OVERLAP_EQ = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  REWRITE_TAC[ARITH_RULE `a - b = a <=> b = 0 \/ a = 0`] THEN
  ASM_SIMP_TAC[ADD_EQ_0; CARD_EQ_0; FINITE_INTER] THEN SET_TAC[]);;

let CARD_UNION_OVERLAP = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD(s UNION t) < CARD(s) + CARD(t)
         ==> ~(s INTER t = {})`,
  SIMP_TAC[GSYM CARD_UNION_OVERLAP_EQ] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

let CARD_IMAGE_INJ = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> b ==> a ==> c`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; IN_IMAGE] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[IN_INSERT]);;

let HAS_SIZE_IMAGE_INJ = prove
 (`!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n
        ==> (IMAGE f s) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE; FINITE_IMAGE] THEN MESON_TAC[CARD_IMAGE_INJ]);;

let CARD_IMAGE_LE = prove
 (`!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE; LE_REFL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ARITH_TAC);;

let CARD_IMAGE_INJ_EQ = prove
 (`!f:A->B s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

let CARD_SUBSET_IMAGE = prove
 (`!f s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t`,
  MESON_TAC[LE_TRANS; FINITE_IMAGE; CARD_IMAGE_LE; CARD_SUBSET]);;

let HAS_SIZE_IMAGE_INJ_EQ = prove
 (`!f s n.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(TAUT
   `(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ;
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_IMAGE_INJ] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSET_STRONG = prove
 (`!n s:A->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_SUC] THENL
   [MESON_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN
  REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; ARITH_RULE `~(SUC n <= 0)`] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; LE_SUC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:A) INSERT t` THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_INSERT; FINITE_DELETE;
               CARD_CLAUSES] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  ASM SET_TAC[]);;

let CHOOSE_SUBSET = prove
 (`!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  MESON_TAC[CHOOSE_SUBSET_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_PRODUCT_DEPENDENT = prove
 (`!s m t n.
         s HAS_SIZE m /\ (!x. x IN s ==> t(x) HAS_SIZE n)
         ==> {(x:A,y:B) | x IN s /\ y IN t(x)} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY; IN_INSERT] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `n:num`] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `CARD(s:A->bool)`) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[SET_RULE
    `{(x,y) | (x = a \/ x IN s) /\ y IN t(x)} =
     {(x,y) | x IN s /\ y IN t(x)} UNION
     IMAGE (\y. (a,y)) (t a)`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN
  ASM_SIMP_TAC[HAS_SIZE_IMAGE_INJ; PAIR_EQ] THEN
  REWRITE_TAC[DISJOINT; IN_IMAGE; IN_ELIM_THM; IN_INTER; EXTENSION;
              NOT_IN_EMPTY; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[PAIR_EQ]);;

let FINITE_PRODUCT_DEPENDENT = prove
 (`!f:A->B->C s t.
        FINITE s /\ (!x. x IN s ==> FINITE(t x))
        ==> FINITE {f x y | x IN s /\ y IN (t x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). (f:A->B->C) x y) {x,y | x IN s /\ y IN t x}` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE; MESON_TAC[]] THEN
  MAP_EVERY UNDISCH_TAC
   [`!x:A. x IN s ==> FINITE(t x :B->bool)`; `FINITE(s:A->bool)`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`t:A->B->bool`; `s:A->bool`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `{(x:A,y:B) | x IN {} /\ y IN (t x)} = {}`
     (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `t:A->B->bool` THEN
  SUBGOAL_THEN
   `{(x:A,y:B) | x IN (a INSERT s) /\ y IN (t x)} =
    IMAGE (\y. a,y) (t a) UNION {(x,y) | x IN s /\ y IN (t x)}`
   (fun th -> ASM_SIMP_TAC[IN_INSERT; FINITE_IMAGE; FINITE_UNION; th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INSERT; IN_UNION] THEN
  MESON_TAC[]);;

let FINITE_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}`,
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT]);;

let CARD_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:A->bool`; `CARD(s:A->bool)`; `\x:A. t:B->bool`;
                  `CARD(t:B->bool)`] HAS_SIZE_PRODUCT_DEPENDENT) THEN
  ASM_SIMP_TAC[HAS_SIZE]);;

let HAS_SIZE_PRODUCT = prove
 (`!s m t n. s HAS_SIZE m /\ t HAS_SIZE n
             ==> {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)`,
  SIMP_TAC[HAS_SIZE; CARD_PRODUCT; FINITE_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

let CROSS = new_definition
 `s CROSS t = {x,y | x IN s /\ y IN t}`;;

let IN_CROSS = prove
 (`!x y s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[CROSS; IN_ELIM_PAIR_THM]);;

let HAS_SIZE_CROSS = prove
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)`,
  REWRITE_TAC[CROSS; HAS_SIZE_PRODUCT]);;

let FINITE_CROSS = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE(s CROSS t)`,
  SIMP_TAC[CROSS; FINITE_PRODUCT]);;

let CARD_CROSS = prove
 (`!s t. FINITE s /\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t`,
  SIMP_TAC[CROSS; CARD_PRODUCT]);;

let CROSS_EQ_EMPTY = prove
 (`!s t. s CROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_FUNSPACE = prove
 (`!d n t:B->bool m s:A->bool.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; EXP] THEN
    CONV_TAC HAS_SIZE_CONV THEN EXISTS_TAC `(\x. d):A->B` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN REWRITE_TAC[FUN_EQ_THM];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`s0:A->bool`; `a:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{f:A->B | (!x. x IN a INSERT s ==> f x IN t) /\
              (!x. ~(x IN a INSERT s) ==> (f x = d))} =
    IMAGE (\(b,g) x. if x = a then b else g(x))
          {b,g | b IN t /\
                 g IN {f | (!x. x IN s ==> f x IN t) /\
                           (!x. ~(x IN s) ==> (f x = d))}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM;
                EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ; CONJ_ASSOC; ONCE_REWRITE_RULE[CONJ_SYM]
     UNWIND_THM1] THEN
    X_GEN_TAC `f:A->B` THEN REWRITE_TAC[IN_INSERT] THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) a`; `\x. if x IN s then (f:A->B) x else d`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `g:A->B`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[EXP; HAS_SIZE_PRODUCT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ; CONJ_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_MESON_TAC[]]);;

let CARD_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {f | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> (f x = d))} =
              (CARD t) EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

let FINITE_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t
         ==> FINITE {f | (!x. x IN s ==> f(x) IN t) /\
                         (!x. ~(x IN s) ==> (f x = d))}`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_POWERSET = prove
 (`!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{t | t SUBSET s} =
    {f | (!x:A. x IN s ==> f(x) IN UNIV) /\ (!x. ~(x IN s) ==> (f x = F))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV; SUBSET; IN; CONTRAPOS_THM];
    MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`T`; `F`] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC TAUT]);;

let CARD_POWERSET = prove
 (`!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

let FINITE_POWERSET = prove
 (`!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

let FINITE_UNIONS = prove
 (`!s:(A->bool)->bool.
        FINITE(UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)`,
  GEN_TAC THEN ASM_CASES_TAC `FINITE(s:(A->bool)->bool)` THEN
  ASM_SIMP_TAC[FINITE_FINITE_UNIONS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_POWERSET) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC[]);;

let POWERSET_CLAUSES = prove
 (`{s | s SUBSET {}} = {{}} /\
   (!a:A t. {s | s SUBSET (a INSERT t)} =
            {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t})`,
  REWRITE_TAC[SUBSET_INSERT_DELETE; SUBSET_EMPTY; SING_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[UNION_SUBSET] THEN
  ONCE_REWRITE_TAC[SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  X_GEN_TAC `s:A->bool` THEN
  ASM_CASES_TAC `(a:A) IN s` THENL [ALL_TAC; ASM SET_TAC[]] THEN
  STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `s DELETE (a:A)` THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_NUMSEG_LT = prove
 (`!n. {m | m < n} HAS_SIZE n`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{m | m < 0} = {}`
       (fun th -> REWRITE_TAC[HAS_SIZE_0; th]) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; LT];
    SUBGOAL_THEN `{m | m < SUC n} = n INSERT {m | m < n}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT] THEN
    REWRITE_TAC[IN_ELIM_THM; LT_REFL]]);;

let CARD_NUMSEG_LT = prove
 (`!n. CARD {m | m < n} = n`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

let FINITE_NUMSEG_LT = prove
 (`!n:num. FINITE {m | m < n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

let HAS_SIZE_NUMSEG_LE = prove
 (`!n. {m | m <= n} HAS_SIZE (n + 1)`,
  REWRITE_TAC[GSYM LT_SUC_LE; HAS_SIZE_NUMSEG_LT; ADD1]);;

let FINITE_NUMSEG_LE = prove
 (`!n. FINITE {m | m <= n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

let CARD_NUMSEG_LE = prove
 (`!n. CARD {m | m <= n} = n + 1`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

let num_FINITE = prove
 (`!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`s:num->bool`,`s:num->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[LE_CASES; LE_TRANS];
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:num | m <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]]);;

let num_FINITE_AVOID = prove
 (`!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)`,
  MESON_TAC[num_FINITE; LT; NOT_LT]);;

let num_INFINITE = prove
 (`INFINITE(:num)`,
  REWRITE_TAC[INFINITE] THEN MESON_TAC[num_FINITE_AVOID; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = prove
 (`INFINITE(:string)`,
  MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o ISPEC `LENGTH:string->num` o MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[LENGTH_REPLICATE]);;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

let FINITE_REAL_INTERVAL = prove
 (`(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)`,
  SUBGOAL_THEN `!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ASM_CASES_TAC `a:real < b` THEN
    ASM_SIMP_TAC[REAL_ARITH `~(a:real < b) ==> ~(a < x /\ x < b)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (\n. a + (b - a) / (&n + &2)) (:num)`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_ADDR; REAL_ARITH `a + x / y < b <=> x / y < b - a`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ; NOT_IMP;
                 REAL_ARITH `&0:real < &n + &2`] THEN
    REWRITE_TAC[REAL_ARITH `x:real < x * (n + &2) <=> &0 < x * (n + &1)`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_MUL; REAL_ARITH `&0:real < &n + &1`] THEN
    MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>
                 &n:real = &m)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH
     `a:real <= x /\ x < b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a`];
    REWRITE_TAC[REAL_ARITH
     `a:real < x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = b`];
    ASM_CASES_TAC `b:real = a` THEN
    ASM_SIMP_TAC[REAL_LE_ANTISYM; REAL_LE_REFL; SING_GSPEC; FINITE_SING] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `~(b:real = a) ==>
        (a <= x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a \/
        ~(b <= a) /\ x = b)`]] THEN
  ASM_REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x \/ q x} = {x | p x} UNION {x | q x}`] THEN
  ASM_CASES_TAC `b:real <= a` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]);;

let real_INFINITE = prove
 (`INFINITE(:real)`,
  REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `{x:real | &0 <= x}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[FINITE_REAL_INTERVAL; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_INDEX = prove
 (`!s n. s HAS_SIZE n
         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\
                        (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  SIMP_TAC[HAS_SIZE_0; HAS_SIZE_SUC; LT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (MP_TAC o SPEC `a:A`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m:num. if m < n then f(m) else a:A` THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  ASM_CASES_TAC `a:A = x` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let set_of_list = new_recursive_definition list_RECURSION
  `(set_of_list ([]:A list) = {}) /\
   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))`;;

let list_of_set = new_definition
  `list_of_set s = @l. (set_of_list l = s) /\ (LENGTH l = CARD s)`;;

let LIST_OF_SET_PROPERTIES = prove
 (`!s:A->bool. FINITE(s)
               ==> (set_of_list(list_of_set s) = s) /\
                   (LENGTH(list_of_set s) = CARD s)`,
  REWRITE_TAC[list_of_set] THEN
  CONV_TAC(BINDER_CONV(RAND_CONV SELECT_CONV)) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `[]:A list` THEN REWRITE_TAC[CARD_CLAUSES; LENGTH; set_of_list];
    EXISTS_TAC `CONS (x:A) l` THEN ASM_REWRITE_TAC[LENGTH] THEN
    ASM_REWRITE_TAC[set_of_list] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
    ASM_REWRITE_TAC[]]);;

let SET_OF_LIST_OF_SET = prove
 (`!s. FINITE(s) ==> (set_of_list(list_of_set s) = s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

let LENGTH_LIST_OF_SET = prove
 (`!s. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

let MEM_LIST_OF_SET = prove
 (`!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV)
    [GSYM th]) THEN
  SPEC_TAC(`list_of_set(s:A->bool)`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; set_of_list; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let FINITE_SET_OF_LIST = prove
 (`!l. FINITE(set_of_list l)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[set_of_list; FINITE_RULES]);;

let IN_SET_OF_LIST = prove
 (`!x l. x IN (set_of_list l) <=> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MEM; set_of_list] THEN
  ASM_MESON_TAC[]);;

let SET_OF_LIST_APPEND = prove
 (`!l1 l2. set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_UNION; MEM_APPEND]);;

let SET_OF_LIST_MAP = prove
 (`!f l. set_of_list(MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[set_of_list; MAP; IMAGE_CLAUSES]);;

let SET_OF_LIST_EQ_EMPTY = prove
 (`!l. set_of_list l = {} <=> l = []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[set_of_list; NOT_CONS_NIL; NOT_INSERT_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Mappings from finite set enumerations to lists (no "setification").       *)
(* ------------------------------------------------------------------------- *)

let dest_setenum =
  let fn = splitlist (dest_binary "INSERT") in
  fun tm -> let l,n = fn tm in
            if is_const n & fst(dest_const n) = "EMPTY" then l
            else failwith "dest_setenum: not a finite set enumeration";;

let is_setenum = can dest_setenum;;

let mk_setenum =
  let insert_atm = `(INSERT):A->(A->bool)->(A->bool)`
  and nil_atm = `(EMPTY):A->bool` in
  fun (l,ty) ->
    let insert_tm = inst [ty,aty] insert_atm
    and nil_tm = inst [ty,aty] nil_atm in
    itlist (mk_binop insert_tm) l nil_tm;;

let mk_fset l = mk_setenum(l,type_of(hd l));;

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let pairwise = new_definition
  `pairwise r s <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y`;;

let PAIRWISE = new_recursive_definition list_RECURSION
  `(PAIRWISE (r:A->A->bool) [] <=> T) /\
   (PAIRWISE (r:A->A->bool) (CONS h t) <=> ALL (r h) t /\ PAIRWISE r t)`;;

let PAIRWISE_EMPTY = prove
 (`!r. pairwise r {} <=> T`,
  REWRITE_TAC[pairwise; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let PAIRWISE_SING = prove
 (`!r x. pairwise r {x} <=> T`,
  REWRITE_TAC[pairwise; IN_SING] THEN MESON_TAC[]);;

let PAIRWISE_MONO = prove
 (`!r s t. pairwise r s /\ t SUBSET s ==> pairwise r t`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let CARD_SET_OF_LIST_LE = prove
 (`!l. CARD(set_of_list l) <= LENGTH l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; set_of_list; CARD_CLAUSES; FINITE_SET_OF_LIST] THEN
  ASM_ARITH_TAC);;

let HAS_SIZE_SET_OF_LIST = prove
 (`!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y. ~(x = y)) l`,
  REWRITE_TAC[HAS_SIZE; FINITE_SET_OF_LIST] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LENGTH; set_of_list; PAIRWISE; ALL;
               FINITE_SET_OF_LIST; GSYM ALL_MEM; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  ASM_MESON_TAC[CARD_SET_OF_LIST_LE; ARITH_RULE `~(SUC n <= n)`]);;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

let SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!s t f:A->B.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `CARD(s DELETE (y:A))` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
      ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `x - 1 < x <=> ~(x = 0)`] THEN
      ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `IMAGE (f:A->B) s = t` MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[EXTENSION; IN_IMAGE]] THEN
    ASM_MESON_TAC[CARD_SUBSET_EQ; CARD_IMAGE_INJ]]);;

let SURJECTIVE_IFF_INJECTIVE = prove
 (`!s f:A->A.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN]);;

let IMAGE_IMP_INJECTIVE_GEN = prove
 (`!s t f:A->B.
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`s:A->bool`; `t:B->bool`; `f:A->B`]
                SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[SUBSET_REFL; FINITE_IMAGE] THEN
  ASM_MESON_TAC[EXTENSION; IN_IMAGE]);;

let IMAGE_IMP_INJECTIVE = prove
 (`!s f. FINITE s /\ (IMAGE f s = s)
       ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MESON_TAC[IMAGE_IMP_INJECTIVE_GEN]);;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_INJ = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:A->B. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CARD_CLAUSES; LE; NOT_SUC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `t:B->bool`] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LE_SUC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:A. if z = x then (y:B) else f(z)` THEN
  REWRITE_TAC[IN_INSERT; SUBSET; IN_IMAGE] THEN
  ASM_MESON_TAC[SUBSET; IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

let FORALL_IN_CLAUSES = prove
 (`(!P. (!x. x IN {} ==> P x) <=> T) /\
   (!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let EXISTS_IN_CLAUSES = prove
 (`(!P. (?x. x IN {} /\ P x) <=> F) /\
   (!P a s. (?x. x IN (a INSERT s) /\ P x) <=> P a \/ (?x. x IN s /\ P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

let SURJECTIVE_ON_RIGHT_INVERSE = prove
 (`!f t. (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
         (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))`,
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

let INJECTIVE_ON_LEFT_INVERSE = prove
 (`!f s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))`,
  let lemma = MESON[]
   `(!x. x IN s ==> (g(f(x)) = x)) <=>
    (!y x. x IN s /\ (y = f x) ==> (g y = x))` in
  REWRITE_TAC[lemma; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let BIJECTIVE_ON_LEFT_RIGHT_INVERSE = prove
 (`!f s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN ASM_MESON_TAC[]);;

let SURJECTIVE_RIGHT_INVERSE = prove
 (`(!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)`,
  MESON_TAC[SURJECTIVE_ON_RIGHT_INVERSE; IN_UNIV]);;

let INJECTIVE_LEFT_INVERSE = prove
 (`(!x y. (f x = f y) ==> (x = y)) <=> (?g. !x. g(f(x)) = x)`,
  let th = REWRITE_RULE[IN_UNIV]
   (ISPECL [`f:A->B`; `UNIV:A->bool`] INJECTIVE_ON_LEFT_INVERSE) in
  REWRITE_TAC[th]);;

let BIJECTIVE_LEFT_RIGHT_INVERSE = prove
 (`!f:A->B.
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC[IN_UNIV]);;

let FUNCTION_FACTORS_LEFT_GEN = prove
 (`!P f g. (!x y. P x /\ P y /\ g x = g y ==> f x = f y) <=>
           (?h. !x. P x ==> f(x) = h(g x))`,
  ONCE_REWRITE_TAC[MESON[]
   `(!x. P x ==> f(x) = g(k x)) <=> (!y x. P x /\ y = k x ==> f x = g y)`] THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let FUNCTION_FACTORS_LEFT = prove
 (`!f g. (!x y. (g x = g y) ==> (f x = f y)) <=> ?h. f = h o g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM;
   GSYM(REWRITE_RULE[] (ISPEC `\x. T` FUNCTION_FACTORS_LEFT_GEN))]);;

let FUNCTION_FACTORS_RIGHT_GEN = prove
 (`!P f g. (!x. P x ==> ?y. g(y) = f(x)) <=>
           (?h. !x. P x ==> f(x) = g(h x))`,
  REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let FUNCTION_FACTORS_RIGHT = prove
 (`!f g. (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

let SURJECTIVE_FORALL_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN MESON_TAC[]);;

let SURJECTIVE_EXISTS_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:B. !x:A. ~(f x = y)`) THEN MESON_TAC[]);;

let SURJECTIVE_IMAGE_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `\y:B. T`)] THEN
  MESON_TAC[]);;

let IMAGE_INJECTIVE_IMAGE_OF_SUBSET = prove
 (`!f:A->B s.
     ?t. t SUBSET s /\
         IMAGE f s = IMAGE f t /\
         (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `?g. !y. y IN IMAGE (f:A->B) s ==> g(y) IN s /\ f(g(y)) = y`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SURJECTIVE_ON_RIGHT_INVERSE] THEN SET_TAC[];
    EXISTS_TAC `IMAGE (g:B->A) (IMAGE (f:A->B) s)` THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image under a function.                   *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_IMAGE = prove
 (`!f:A->B u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC; SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{x:A}`; `{y:A}`]) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES] THEN SET_TAC[]);;

let INJECTIVE_IMAGE = prove
 (`!f:A->B.
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN MP_TAC(ISPECL [`f:A->B`; `(:A)`] INJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

let SURJECTIVE_ON_IMAGE = prove
 (`!f:A->B u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{y:B}`) THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `t:B->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{x | x IN u /\ (f:A->B) x IN t}` THEN ASM SET_TAC[]]);;

let SURJECTIVE_IMAGE = prove
 (`!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] SURJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

let CARD_EQ_BIJECTION = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MP_TAC CARD_LE_INJ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN] THEN
  MESON_TAC[SUBSET; IN_IMAGE]);;

let CARD_EQ_BIJECTIONS = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f(g y) = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

let BIJECTIONS_HAS_SIZE = prove
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST_ALL_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

let BIJECTIONS_HAS_SIZE_EQ = prove
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
  [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] BIJECTIONS_HAS_SIZE) THENL
   [MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->A`];
    MAP_EVERY EXISTS_TAC [`g:B->A`; `f:A->B`]] THEN
  ASM_MESON_TAC[]);;

let BIJECTIONS_CARD_EQ = prove
 (`!s t f:A->B g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP BIJECTIONS_HAS_SIZE_EQ)) THEN
  MESON_TAC[HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

let WF_FINITE = prove
 (`!(<<). (!x. ~(x << x)) /\ (!x y z. x << y /\ y << z ==> x << z) /\
          (!x:A. FINITE {y | y << x})
          ==> WF(<<)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m < n ==> (s:num->A) n << s m` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:num->A` INFINITE_IMAGE_INJ) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[LT_CASES]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(:num)`) THEN
  REWRITE_TAC[num_INFINITE] THEN REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s(0) INSERT {y:A | y << s(0)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_INSERT] THEN
  INDUCT_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LT_0]);;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Examples/card.ml)                    *)
(* ------------------------------------------------------------------------- *)

let le_c = new_definition
  `s <=_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                    (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))`;;

let lt_c = new_definition
  `s <_c t <=> s <=_c t /\ ~(t <=_c s)`;;

let eq_c = new_definition
  `s =_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                   !y. y IN t ==> ?!x. x IN s /\ (f x = y)`;;

let ge_c = new_definition
 `s >=_c t <=> t <=_c s`;;

let gt_c = new_definition
 `s >_c t <=> t <_c s`;;

let LE_C = prove
 (`!s t. s <=_c t <=> ?g. !x. x IN s ==> ?y. y IN t /\ (g y = x)`,
  REWRITE_TAC[le_c; INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE;
              RIGHT_IMP_EXISTS_THM; SKOLEM_THM; RIGHT_AND_EXISTS_THM] THEN
  MESON_TAC[]);;

let GE_C = prove
 (`!s t. s >=_c t <=> ?f. !y. y IN t ==> ?x. x IN s /\ (y = f x)`,
  REWRITE_TAC[ge_c; LE_C] THEN MESON_TAC[]);;

let COUNTABLE = new_definition
  `COUNTABLE t <=> (:num) >=_c t`;;

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

let sup = new_definition
  `sup s = @a:real. (!x. x IN s ==> x <= a) /\
                    !b. (!x. x IN s ==> x <= b) ==> a <= b`;;

let SUP = prove
 (`!s. ~(s = {}) /\ (?b. !x. x IN s ==> x <= b)
       ==> (!x. x IN s ==> x <= sup s) /\
           !b. (!x. x IN s ==> x <= b) ==> sup s <= b`,
  REWRITE_TAC[sup] THEN CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_COMPLETE THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

let SUP_FINITE_LEMMA = prove
 (`!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> x <= b`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

let SUP_FINITE = prove
 (`!s. FINITE s /\ ~(s = {}) ==> (sup s) IN s /\ !x. x IN s ==> x <= sup s`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUP_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL; SUP]);;

let REAL_LE_SUP_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\ a <= x)`,
  MESON_TAC[SUP_FINITE; REAL_LE_TRANS]);;

let REAL_SUP_LE_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)`,
  MESON_TAC[SUP_FINITE; REAL_LE_TRANS]);;

let REAL_LT_SUP_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\ a < x)`,
  MESON_TAC[SUP_FINITE; REAL_LTE_TRANS]);;

let REAL_SUP_LT_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)`,
  MESON_TAC[SUP_FINITE; REAL_LET_TRANS]);;

let REAL_SUP_UNIQUE = prove
 (`!s b. (!x. x IN s ==> x <= b) /\
         (!b'. b' < b ==> ?x. x IN s /\ b' < x)
         ==> sup s = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sup] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE; REAL_LE_ANTISYM]);;

let REAL_SUP_LE = prove
 (`!b. ~(s = {}) /\ (!x. x IN s ==> x <= b) ==> sup s <= b`,
  MESON_TAC[SUP]);;

let REAL_SUP_LE_SUBSET = prove
 (`!s t. ~(s = {}) /\ s SUBSET t /\ (?b. !x. x IN t ==> x <= b)
         ==> sup s <= sup t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE THEN
  MP_TAC(SPEC `t:real->bool` SUP) THEN ASM SET_TAC[]);;

let REAL_SUP_BOUNDS = prove
 (`!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= sup s /\ sup s <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` SUP) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let REAL_ABS_SUP_LE = prove
 (`!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_SUP_BOUNDS]);;

let REAL_SUP_ASCLOSE = prove
 (`!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(sup s - l) <= e`,
  SIMP_TAC[REAL_ARITH `abs(x - l):real <= e <=> l - e <= x /\ x <= l + e`] THEN
  REWRITE_TAC[REAL_SUP_BOUNDS]);;

let inf = new_definition
  `inf s = @a:real. (!x. x IN s ==> a <= x) /\
                    !b. (!x. x IN s ==> b <= x) ==> b <= a`;;

let INF = prove
 (`!s. ~(s = {}) /\ (?b. !x. x IN s ==> b <= x)
       ==> (!x. x IN s ==> inf s <= x) /\
           !b. (!x. x IN s ==> b <= x) ==> b <= inf s`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[inf] THEN
  CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_NEG2] THEN
  EXISTS_TAC `--(sup (IMAGE (--) s))` THEN
  MP_TAC(SPEC `IMAGE (--) (s:real->bool)` SUP) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  ABBREV_TAC `a = sup (IMAGE (--) s)` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE] THEN
  ASM_MESON_TAC[REAL_NEG_NEG; MEMBER_NOT_EMPTY; REAL_LE_NEG2]);;

let INF_FINITE_LEMMA = prove
 (`!s. FINITE s /\ ~(s = {}) ==> ?b:real. b IN s /\ !x. x IN s ==> b <= x`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

let INF_FINITE = prove
 (`!s. FINITE s /\ ~(s = {}) ==> (inf s) IN s /\ !x. x IN s ==> inf s <= x`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INF_FINITE_LEMMA) THEN
  ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TOTAL; INF]);;

let REAL_LE_INF_FINITE = prove
(`!s a. FINITE s /\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)`,
  MESON_TAC[INF_FINITE; REAL_LE_TRANS]);;

let REAL_INF_LE_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\ x <= a)`,
  MESON_TAC[INF_FINITE; REAL_LE_TRANS]);;

let REAL_LT_INF_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)`,
  MESON_TAC[INF_FINITE; REAL_LTE_TRANS]);;

let REAL_INF_LT_FINITE = prove
 (`!s a. FINITE s /\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\ x < a)`,
  MESON_TAC[INF_FINITE; REAL_LET_TRANS]);;

let REAL_INF_UNIQUE = prove
 (`!s b. (!x. x IN s ==> b <= x) /\
         (!b'. b < b' ==> ?x. x IN s /\ x < b')
         ==> inf s = b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inf] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  ASM_MESON_TAC[REAL_NOT_LE; REAL_LE_ANTISYM]);;

let REAL_LE_INF = prove
 (`!b. ~(s = {}) /\ (!x. x IN s ==> b <= x) ==> b <= inf s`,
  MESON_TAC[INF]);;

let REAL_LE_INF_SUBSET = prove
 (`!s t. ~(t = {}) /\ t SUBSET s /\ (?b. !x. x IN s ==> b <= x)
         ==> inf s <= inf t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF THEN
  MP_TAC(SPEC `s:real->bool` INF) THEN ASM SET_TAC[]);;

let REAL_INF_BOUNDS = prove
 (`!s a b. ~(s = {}) /\ (!x. x IN s ==> a <= x /\ x <= b)
           ==> a <= inf s /\ inf s <= b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:real->bool` INF) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let REAL_ABS_INF_LE = prove
 (`!s a. ~(s = {}) /\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a`,
  REWRITE_TAC[GSYM REAL_BOUNDS_LE; REAL_INF_BOUNDS]);;

let REAL_INF_ASCLOSE = prove
 (`!s l e. ~(s = {}) /\ (!x. x IN s ==> abs(x - l) <= e)
           ==> abs(inf s - l) <= e`,
  SIMP_TAC[REAL_ARITH `abs(x - l):real <= e <=> l - e <= x /\ x <= l + e`] THEN
  REWRITE_TAC[REAL_INF_BOUNDS]);;

let SUP_UNIQUE_FINITE = prove
 (`!s. FINITE s /\ ~(s = {})
       ==> (sup s = a <=> a IN s /\ !y. y IN s ==> y <= a)`,
   ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_SUP_FINITE; REAL_SUP_LE_FINITE;
               NOT_INSERT_EMPTY; FINITE_INSERT; FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LE_ANTISYM]);;

let INF_UNIQUE_FINITE = prove
 (`!s. FINITE s /\ ~(s = {})
       ==> (inf s = a <=> a IN s /\ !y. y IN s ==> a <= y)`,
   ASM_SIMP_TAC[GSYM REAL_LE_ANTISYM; REAL_LE_INF_FINITE; REAL_INF_LE_FINITE;
               NOT_INSERT_EMPTY; FINITE_INSERT; FINITE_EMPTY] THEN
   MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS; REAL_LE_ANTISYM]);;

let SUP_INSERT_FINITE = prove
 (`!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SUP_UNIQUE_FINITE;  FINITE_INSERT; FINITE_EMPTY;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN
  REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[SUP_FINITE; IN_INSERT; REAL_LE_REFL] THEN
  ASM_MESON_TAC[SUP_FINITE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

let INF_INSERT_FINITE = prove
 (`!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INF_UNIQUE_FINITE;  FINITE_INSERT; FINITE_EMPTY;
               NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_SING; REAL_LE_REFL] THEN
  REWRITE_TAC[real_min] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[INF_FINITE; IN_INSERT; REAL_LE_REFL] THEN
  ASM_MESON_TAC[INF_FINITE; REAL_LE_TOTAL; REAL_LE_TRANS]);;

let REAL_SUP_EQ_INF = prove
 (`!s. ~(s = {}) /\ (?B. !x. x IN s ==> abs(x) <= B)
       ==> (sup s = inf s <=> ?a. s = {a})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `sup s` THEN MATCH_MP_TAC
     (SET_RULE `~(s = {}) /\ (!x. x IN s ==> x = a) ==> s = {a}`) THEN
    ASM_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN
    ASM_MESON_TAC[SUP; REAL_ABS_BOUNDS; INF];
    STRIP_TAC THEN
    ASM_SIMP_TAC[SUP_INSERT_FINITE; INF_INSERT_FINITE; FINITE_EMPTY]]);;
