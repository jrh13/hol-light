(* ========================================================================= *)
(* Additional theorems, mainly about quantifiers.                            *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "simp.ml";;

(* ------------------------------------------------------------------------- *)
(* More stuff about equality.                                                *)
(* ------------------------------------------------------------------------- *)

let EQ_REFL = prove
 (`!x:A. x = x`,
  GEN_TAC THEN REFL_TAC);;

let REFL_CLAUSE = prove
 (`!x:A. (x = x) <=> T`,
  GEN_TAC THEN MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL EQ_REFL)));;

let EQ_SYM = prove
 (`!(x:A) y. (x = y) ==> (y = x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM));;

let EQ_SYM_EQ = prove
 (`!(x:A) y. (x = y) <=> (y = x)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN MATCH_ACCEPT_TAC EQ_SYM);;

let EQ_TRANS = prove
 (`!(x:A) y z. (x = y) /\ (y = z) ==> (x = z)`,
  REPEAT STRIP_TAC THEN PURE_ASM_REWRITE_TAC[] THEN REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The following is a common special case of ordered rewriting.              *)
(* ------------------------------------------------------------------------- *)

let AC acsuite = EQT_ELIM o PURE_REWRITE_CONV[acsuite; REFL_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* A couple of theorems about beta reduction.                                *)
(* ------------------------------------------------------------------------- *)

let BETA_THM = prove
 (`!(f:A->B) y. (\x. (f:A->B) x) y = f y`,
  REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);;

let ABS_SIMP = prove
 (`!(t1:A) (t2:B). (\x. t1) t2 = t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETA_THM; REFL_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* A few "big name" intuitionistic tautologies.                              *)
(* ------------------------------------------------------------------------- *)

let CONJ_ASSOC = prove
 (`!t1 t2 t3. t1 /\ t2 /\ t3 <=> (t1 /\ t2) /\ t3`,
  ITAUT_TAC);;

let CONJ_SYM = prove
 (`!t1 t2. t1 /\ t2 <=> t2 /\ t1`,
  ITAUT_TAC);;

let CONJ_ACI = prove
 (`(p /\ q <=> q /\ p) /\
   ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
   (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
   (p /\ p <=> p) /\
   (p /\ (p /\ q) <=> p /\ q)`,
  ITAUT_TAC);;

let DISJ_ASSOC = prove
 (`!t1 t2 t3. t1 \/ t2 \/ t3 <=> (t1 \/ t2) \/ t3`,
  ITAUT_TAC);;

let DISJ_SYM = prove
 (`!t1 t2. t1 \/ t2 <=> t2 \/ t1`,
  ITAUT_TAC);;

let DISJ_ACI = prove
 (`(p \/ q <=> q \/ p) /\
   ((p \/ q) \/ r <=> p \/ (q \/ r)) /\
   (p \/ (q \/ r) <=> q \/ (p \/ r)) /\
   (p \/ p <=> p) /\
   (p \/ (p \/ q) <=> p \/ q)`,
  ITAUT_TAC);;

let IMP_CONJ = prove
 (`p /\ q ==> r <=> p ==> q ==> r`,
  ITAUT_TAC);;

let IMP_IMP = GSYM IMP_CONJ;;

let IMP_CONJ_ALT = prove
 (`p /\ q ==> r <=> q ==> p ==> r`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A couple of "distribution" tautologies are useful.                        *)
(* ------------------------------------------------------------------------- *)

let LEFT_OR_DISTRIB = prove
 (`!p q r. p /\ (q \/ r) <=> p /\ q \/ p /\ r`,
  ITAUT_TAC);;

let RIGHT_OR_DISTRIB = prove
 (`!p q r. (p \/ q) /\ r <=> p /\ r \/ q /\ r`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Degenerate cases of quantifiers.                                          *)
(* ------------------------------------------------------------------------- *)

let FORALL_SIMP = prove
 (`!t. (!x:A. t) = t`,
  ITAUT_TAC);;

let EXISTS_SIMP = prove
 (`!t. (?x:A. t) = t`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* I also use this a lot (as a prelude to congruence reasoning).             *)
(* ------------------------------------------------------------------------- *)

let EQ_IMP = ITAUT `(a <=> b) ==> a ==> b`;;

(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)

let EQ_CLAUSES = prove
 (`!t. ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\
       ((F <=> t) <=> ~t) /\ ((t <=> F) <=> ~t)`,
  ITAUT_TAC);;

let NOT_CLAUSES_WEAK = prove
 (`(~T <=> F) /\ (~F <=> T)`,
  ITAUT_TAC);;

let AND_CLAUSES = prove
 (`!t. (T /\ t <=> t) /\ (t /\ T <=> t) /\ (F /\ t <=> F) /\
       (t /\ F <=> F) /\ (t /\ t <=> t)`,
  ITAUT_TAC);;

let OR_CLAUSES = prove
 (`!t. (T \/ t <=> T) /\ (t \/ T <=> T) /\ (F \/ t <=> t) /\
       (t \/ F <=> t) /\ (t \/ t <=> t)`,
  ITAUT_TAC);;

let IMP_CLAUSES = prove
 (`!t. (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
       (t ==> t <=> T) /\ (t ==> F <=> ~t)`,
  ITAUT_TAC);;

extend_basic_rewrites
  [REFL_CLAUSE;
   EQ_CLAUSES;
   NOT_CLAUSES_WEAK;
   AND_CLAUSES;
   OR_CLAUSES;
   IMP_CLAUSES;
   FORALL_SIMP;
   EXISTS_SIMP;
   BETA_THM;
   let IMP_EQ_CLAUSE = prove
    (`((x = x) ==> p) <=> p`,
     REWRITE_TAC[EQT_INTRO(SPEC_ALL EQ_REFL); IMP_CLAUSES]) in
   IMP_EQ_CLAUSE];;

extend_basic_congs
  [ITAUT `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')`];;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for unique existence.                                        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_THM = prove
 (`!P. (?!x:A. P x) <=> (?x. P x) /\ (!x x'. P x /\ P x' ==> (x = x'))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_REFL = prove
 (`!a:A. ?x. x = a`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;

let EXISTS_UNIQUE_REFL = prove
 (`!a:A. ?!x. x = a`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THENL
   [EXISTS_TAC `a:A`; ASM_REWRITE_TAC[]] THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)

let UNWIND_THM1 = prove
 (`!P (a:A). (?x. a = x /\ P x) <=> P a`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC));
    DISCH_TAC THEN EXISTS_TAC `a:A` THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    REFL_TAC]);;

let UNWIND_THM2 = prove
 (`!P (a:A). (?x. x = a /\ P x) <=> P a`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC UNWIND_THM1);;

let FORALL_UNWIND_THM2 = prove
 (`!P (a:A). (!x. x = a ==> P x) <=> P a`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    DISCH_TAC THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]]);;

let FORALL_UNWIND_THM1 = prove
 (`!P a. (!x. a = x ==> P x) <=> P a`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC FORALL_UNWIND_THM2);;

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)

let SWAP_FORALL_THM = prove
 (`!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)`,
  ITAUT_TAC);;

let SWAP_EXISTS_THM = prove
 (`!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

let FORALL_AND_THM = prove
 (`!P Q. (!x:A. P x /\ Q x) <=> (!x. P x) /\ (!x. Q x)`,
  ITAUT_TAC);;

let AND_FORALL_THM = prove
 (`!P Q. (!x. P x) /\ (!x. Q x) <=> (!x:A. P x /\ Q x)`,
  ITAUT_TAC);;

let LEFT_AND_FORALL_THM = prove
 (`!P Q. (!x:A. P x) /\ Q <=> (!x:A. P x /\ Q)`,
  ITAUT_TAC);;

let RIGHT_AND_FORALL_THM = prove
 (`!P Q. P /\ (!x:A. Q x) <=> (!x. P /\ Q x)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let EXISTS_OR_THM = prove
 (`!P Q. (?x:A. P x \/ Q x) <=> (?x. P x) \/ (?x. Q x)`,
  ITAUT_TAC);;

let OR_EXISTS_THM = prove
 (`!P Q. (?x. P x) \/ (?x. Q x) <=> (?x:A. P x \/ Q x)`,
  ITAUT_TAC);;

let LEFT_OR_EXISTS_THM = prove
 (`!P Q. (?x. P x) \/ Q <=> (?x:A. P x \/ Q)`,
  ITAUT_TAC);;

let RIGHT_OR_EXISTS_THM = prove
 (`!P Q. P \/ (?x. Q x) <=> (?x:A. P \/ Q x)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let LEFT_EXISTS_AND_THM = prove
 (`!P Q. (?x:A. P x /\ Q) <=> (?x:A. P x) /\ Q`,
  ITAUT_TAC);;

let RIGHT_EXISTS_AND_THM = prove
 (`!P Q. (?x:A. P /\ Q x) <=> P /\ (?x:A. Q x)`,
  ITAUT_TAC);;

let TRIV_EXISTS_AND_THM = prove
 (`!P Q. (?x:A. P /\ Q) <=> (?x:A. P) /\ (?x:A. Q)`,
  ITAUT_TAC);;

let LEFT_AND_EXISTS_THM = prove
 (`!P Q. (?x:A. P x) /\ Q <=> (?x:A. P x /\ Q)`,
  ITAUT_TAC);;

let RIGHT_AND_EXISTS_THM = prove
 (`!P Q. P /\ (?x:A. Q x) <=> (?x:A. P /\ Q x)`,
  ITAUT_TAC);;

let TRIV_AND_EXISTS_THM = prove
 (`!P Q. (?x:A. P) /\ (?x:A. Q) <=> (?x:A. P /\ Q)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

let TRIV_FORALL_OR_THM = prove
 (`!P Q. (!x:A. P \/ Q) <=> (!x:A. P) \/ (!x:A. Q)`,
  ITAUT_TAC);;

let TRIV_OR_FORALL_THM = prove
 (`!P Q. (!x:A. P) \/ (!x:A. Q) <=> (!x:A. P \/ Q)`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let RIGHT_IMP_FORALL_THM = prove
 (`!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)`,
  ITAUT_TAC);;

let RIGHT_FORALL_IMP_THM = prove
 (`!P Q. (!x. P ==> Q x) <=> (P ==> !x:A. Q x)`,
  ITAUT_TAC);;

let LEFT_IMP_EXISTS_THM = prove
 (`!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)`,
  ITAUT_TAC);;

let LEFT_FORALL_IMP_THM = prove
 (`!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)`,
  ITAUT_TAC);;

let TRIV_FORALL_IMP_THM = prove
 (`!P Q. (!x:A. P ==> Q) <=> ((?x:A. P) ==> (!x:A. Q))`,
  ITAUT_TAC);;

let TRIV_EXISTS_IMP_THM = prove
 (`!P Q. (?x:A. P ==> Q) <=> ((!x:A. P) ==> (?x:A. Q))`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Alternative versions of unique existence.                                 *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_ALT = prove
 (`!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x:A`) ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN
    ASM_REWRITE_TAC[GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]);;

let EXISTS_UNIQUE = prove
 (`!P:A->bool. (?!x. P x) <=> (?x. P x /\ !y. P y ==> (y = x))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [ITAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN SIMP_TAC[] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[CONJ_ACI]);;
