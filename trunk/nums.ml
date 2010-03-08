(* ========================================================================= *)
(* The axiom of infinity; construction of the natural numbers.               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "pair.ml";;

(* ------------------------------------------------------------------------- *)
(* Declare a new type "ind" of individuals.                                  *)
(* ------------------------------------------------------------------------- *)

new_type ("ind",0);;

(* ------------------------------------------------------------------------- *)
(* We assert the axiom of infinity as in HOL88, but then we can forget it!   *)
(* ------------------------------------------------------------------------- *)

let ONE_ONE = new_definition
  `ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;

let ONTO = new_definition
  `ONTO(f:A->B) = !y. ?x. y = f x`;;

let INFINITY_AX = new_axiom
  `?f:ind->ind. ONE_ONE f /\ ~(ONTO f)`;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce constants.                                             *)
(* ------------------------------------------------------------------------- *)

let IND_SUC_0_EXISTS = prove
 (`?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))`,
  X_CHOOSE_TAC `f:ind->ind` INFINITY_AX THEN EXISTS_TAC `f:ind->ind` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ONE_ONE; ONTO] THEN MESON_TAC[]);;

let IND_SUC_INJ,IND_SUC_0 = CONJ_PAIR
  (new_specification ["IND_SUC"; "IND_0"] IND_SUC_0_EXISTS);;

(* ------------------------------------------------------------------------- *)
(* Carve out the natural numbers inductively.                                *)
(* ------------------------------------------------------------------------- *)

let NUM_REP_RULES,NUM_REP_INDUCT,NUM_REP_CASES =
  new_inductive_definition
   `NUM_REP IND_0 /\
    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))`;;

let num_tydef = new_basic_type_definition
  "num" ("mk_num","dest_num")
    (CONJUNCT1 NUM_REP_RULES);;

let ZERO_DEF = new_definition
 `_0 = mk_num IND_0`;;

let SUC_DEF = new_definition
 `SUC n = mk_num(IND_SUC(dest_num n))`;;

(* ------------------------------------------------------------------------- *)
(* Distinctness and injectivity of constructors.                             *)
(* ------------------------------------------------------------------------- *)

let NOT_SUC = prove
 (`!n. ~(SUC n = _0)`,
  REWRITE_TAC[SUC_DEF; ZERO_DEF] THEN
  MESON_TAC[NUM_REP_RULES; fst num_tydef; snd num_tydef; IND_SUC_0]);;

let SUC_INJ = prove
 (`!m n. SUC m = SUC n <=> m = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUC_DEF] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM `dest_num`) THEN
  SUBGOAL_THEN `!p. NUM_REP (IND_SUC (dest_num p))` MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC (CONJUNCT2 NUM_REP_RULES); ALL_TAC] THEN
  REWRITE_TAC[fst num_tydef; snd num_tydef] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[IND_SUC_INJ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `mk_num`) THEN
  REWRITE_TAC[fst num_tydef]);;

(* ------------------------------------------------------------------------- *)
(* Induction.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_INDUCTION = prove
 (`!P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\i. NUM_REP i /\ P(mk_num i):bool` NUM_REP_INDUCT) THEN
  ASM_REWRITE_TAC[GSYM ZERO_DEF; NUM_REP_RULES] THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 NUM_REP_RULES) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `mk_num(IND_SUC i) = SUC(mk_num i)` SUBST1_TAC THENL
       [REWRITE_TAC[SUC_DEF] THEN REPEAT AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM(snd num_tydef)] THEN
        FIRST_ASSUM MATCH_ACCEPT_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]];
    DISCH_THEN(MP_TAC o SPEC `dest_num n`) THEN
    REWRITE_TAC[fst num_tydef; snd num_tydef]]);;

(* ------------------------------------------------------------------------- *)
(* Recursion.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_Axiom = prove
 (`!(e:A) f. ?!fn. (fn _0 = e) /\
                   (!n. fn (SUC n) = f (fn n) n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [(MP_TAC o prove_inductive_relations_exist)
      `PRG _0 e /\ (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n))` THEN
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN `!n:num. ?!y:A. PRG n y` MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC BINDER_CONV [GSYM th]) THEN
      REWRITE_TAC[GSYM NOT_SUC; NOT_SUC; SUC_INJ; EXISTS_UNIQUE_REFL] THEN
      REWRITE_TAC[UNWIND_THM1] THEN
      UNDISCH_TAC `?!y. PRG (n:num) (y:A)` THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y:A`) ASSUME_TAC) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MAP_EVERY EXISTS_TAC [`(f:A->num->A) y n`; `y:A`];
        AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIQUE_SKOLEM_ALT] THEN
      DISCH_THEN(X_CHOOSE_THEN `fn:num->A` (ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC `fn:num->A` THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN REFL_TAC];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The basic numeral tag; rewrite existing instances of "_0".                *)
(* ------------------------------------------------------------------------- *)

let NUMERAL = new_definition
 `NUMERAL (n:num) = n`;;

let [NOT_SUC; num_INDUCTION; num_Axiom] =
  let th = prove(`_0 = 0`,REWRITE_TAC[NUMERAL]) in
  map (GEN_REWRITE_RULE DEPTH_CONV [th])
    [NOT_SUC; num_INDUCTION; num_Axiom];;

(* ------------------------------------------------------------------------- *)
(* Induction tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

let (INDUCT_TAC:tactic) =
  MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN DISCH_TAC];;

let num_RECURSION =
  let avs = fst(strip_forall(concl num_Axiom)) in
  GENL avs (EXISTENCE (SPECL avs num_Axiom));;

(* ------------------------------------------------------------------------- *)
(* Cases theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let num_CASES = prove
 (`!m. (m = 0) \/ (?n. m = SUC n)`,
  INDUCT_TAC THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Augmenting inductive type store.                                          *)
(* ------------------------------------------------------------------------- *)

let num_RECURSION_STD = prove
 (`!e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`e:Z`; `(\z n. (f:num->Z->Z) n z)`] num_RECURSION) THEN
  REWRITE_TAC[]);;

inductive_type_store :=
 ("num",(2,num_INDUCTION,num_RECURSION_STD))::(!inductive_type_store);;
