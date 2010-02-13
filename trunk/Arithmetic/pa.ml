(* ========================================================================= *)
(* Two interesting axiom systems: full Peano Arithmetic and Robinson's Q.    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* We define PA as an "inductive" predicate because the pattern-matching     *)
(* is a bit nicer, but of course we could just define the term explicitly.   *)
(* In effect, the returned PA_CASES would be our explicit definition.        *)
(*                                                                           *)
(* The induction axiom is done a little strangely in order to avoid using    *)
(* substitution as a primitive concept.                                      *)
(* ------------------------------------------------------------------------- *)

let PA_RULES,PA_INDUCT,PA_CASES = new_inductive_definition
 `(!s. PA(Not (Z === Suc(s)))) /\
  (!s t. PA(Suc(s) === Suc(t) --> s === t)) /\
  (!t. PA(t ++ Z === t)) /\
  (!s t. PA(s ++ Suc(t) === Suc(s ++ t))) /\
  (!t. PA(t ** Z === Z)) /\
  (!s t. PA(s ** Suc(t) === s ** t ++ s)) /\
  (!p i j. ~(j IN FV(p))
           ==> PA
                ((??i (V i === Z && p)) &&
                 (!!j (??i (V i === V j && p)
                           --> ??i (V i === Suc(V j) && p)))
                 --> !!i p))`;;

let PA_SOUND = prove
 (`!A p. (!a. a IN A ==> true a) /\ (PA UNION A) |-- p ==> true p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THEOREMS_TRUE THEN
  EXISTS_TAC `PA UNION A` THEN
  ASM_SIMP_TAC[IN_UNION; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[IN] THEN MATCH_MP_TAC PA_INDUCT THEN
  REWRITE_TAC[true_def; holds; termval] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [SIMP_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; SUC_INJ; NOT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:form`; `i:num`; `j:num`] THEN
  ASM_CASES_TAC `j:num = i` THEN
  ASM_REWRITE_TAC[VALMOD; VALMOD_VALMOD_BASIC] THEN
  SIMP_TAC[HOLDS_VALMOD_OTHER] THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNWIND_THM2] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!a b v. holds ((i |-> a) ((j |-> b) v)) q <=> holds ((i |-> a) v) q`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLDS_VALUATION THEN
    ASM_REWRITE_TAC[valmod] THEN ASM_MESON_TAC[];
    GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Robinson's axiom system Q.                                                *)
(*                                                                           *)
(*  <<(forall m n. S(m) = S(n) ==> m = n) /\                                 *)
(*    (forall n. ~(n = 0) <=> exists m. n = S(m)) /\                         *)
(*    (forall n. 0 + n = n) /\                                               *)
(*    (forall m n. S(m) + n = S(m + n)) /\                                   *)
(*    (forall n. 0 * n = 0) /\                                               *)
(*    (forall m n. S(m) * n = n + m * n) /\                                  *)
(*    (forall m n. m <= n <=> exists d. m + d = n) /\                        *)
(*    (forall m n. m < n <=> S(m) <= n)>>;;                                  *)
(* ------------------------------------------------------------------------- *)

let robinson = new_definition
 `robinson =
        (!!0 (!!1 (Suc(V 0) === Suc(V 1) --> V 0 === V 1))) &&
        (!!1 (Not(V 1 === Z) <-> ??0 (V 1 === Suc(V 0)))) &&
        (!!1 (Z ++ V 1 === V 1)) &&
        (!!0 (!!1 (Suc(V 0) ++ V 1 === Suc(V 0 ++ V 1)))) &&
        (!!1 (Z ** V 1 === Z)) &&
        (!!0 (!!1 (Suc(V 0) ** V 1 === V 1 ++ V 0 ** V 1))) &&
        (!!0 (!!1 (V 0 <<= V 1 <-> ??2 (V 0 ++ V 2 === V 1)))) &&
        (!!0 (!!1 (V 0 << V 1 <-> Suc(V 0) <<= V 1)))`;;
