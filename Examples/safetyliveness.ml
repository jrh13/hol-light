(* ========================================================================= *)
(* Formal definition of "safety" and "liveness" for properties of traces.    *)
(* Proof that any property of traces can be decomposed into the conjunction  *)
(* of a safety and a liveness property, following Fred Schneider's paper     *)
(* "Decomposing Properties into Safety and Liveness using Predicate Logic".  *)
(*                                                                           *)
(*         https://apps.dtic.mil/dtic/tr/fulltext/u2/a187556.pdf             *)
(* ========================================================================= *)

let safety = new_definition
 `safety (p:(num->S)->bool) <=>
        !s. ~(p s) ==> ?n. !s'. (!m. m <= n ==> s(m) = s'(m)) ==> ~(p s')`;;

let liveness = new_definition
 `liveness (p:(num->S)->bool) <=>
        !s n. ?s'. (!m. m <= n ==> s(m) = s'(m)) /\ p s'`;;

(* ------------------------------------------------------------------------- *)
(* It doesn't matter whether we take strict or non-strict subsequences.      *)
(* ------------------------------------------------------------------------- *)

let SAFETY = prove
 (`!p:(num->S)->bool.
        safety p <=>
        !s. ~(p s) ==> ?n. !s'. (!m. m < n ==> s(m) = s'(m)) ==> ~(p s')`,
  GEN_TAC THEN REWRITE_TAC[safety; GSYM LT_SUC_LE] THEN
  MESON_TAC[ARITH_RULE `m < n ==> m < SUC n`]);;

let LIVENESS = prove
 (`!p:(num->S)->bool.
        liveness p <=>
        !s n. ?s'. (!m. m < n ==> s(m) = s'(m)) /\ p s'`,
  GEN_TAC THEN REWRITE_TAC[liveness; GSYM LT_SUC_LE] THEN
  MESON_TAC[ARITH_RULE `m < n ==> m < SUC n`]);;

(* ------------------------------------------------------------------------- *)
(* Decomposition theorem (following top level of Schneider's proof).         *)
(* ------------------------------------------------------------------------- *)

let SAFETY_LIVENESS_DECOMPOSITION = prove
 (`!P:(num->S)->bool.
      ?S L. safety S /\ liveness L /\ (!x. S x /\ L x <=> P x)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Q = \s:num->S. !i. ?b. (!j. j <= i ==> b j = s j) /\ P b` THEN
  MAP_EVERY EXISTS_TAC [`\s:num->S. P s \/ Q s`; `\s:num->S. P s \/ ~Q s`] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[safety; liveness]; MESON_TAC[]] THEN
  REWRITE_TAC[DE_MORGAN_THM; IMP_CONJ; NOT_FORALL_THM] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[];
    MESON_TAC[]]);;
