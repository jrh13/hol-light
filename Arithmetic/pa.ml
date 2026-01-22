(* ========================================================================= *)
(* The full Peano arithmetic axiom system.                                   *)
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
 `PA(!!1 (Not (Z === Suc(V 1)))) /\
  PA(!!0 (!!1 (Suc(V 0) === Suc(V 1) --> V 0 === V 1))) /\
  PA(!!1 (V 1 ++ Z === V 1)) /\
  PA(!!0 (!!1 (V 0 ++ Suc(V 1) === Suc(V 0 ++ V 1)))) /\
  PA(!!1 (V 1 ** Z === Z)) /\
  PA(!!0 (!!1 (V 0 ** Suc(V 1) === V 0 ** V 1 ++ V 0))) /\
  PA(!!0 (!!1 (V 0 <<= V 1 <-> ??2 (V 0 ++ V 2 === V 1)))) /\
  PA(!!0 (!!1 (V 0 << V 1 <-> Suc(V 0) <<= V 1))) /\
  (!i j p. ~(j IN FV(p))
           ==> PA
                ((??i (V i === Z && p)) &&
                 (!!j (??i (V i === V j && p)
                           --> ??i (V i === Suc(V j) && p)))
                 --> !!i p))`;;

let PA_SOUND = prove
 (`!A p. (!a. a IN A ==> arithtrue a) /\ (PA UNION A) |-- p ==> arithtrue p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC THEOREMS_TRUE THEN
  EXISTS_TAC `PA UNION A` THEN
  ASM_SIMP_TAC[IN_UNION; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[IN] THEN MATCH_MP_TAC PA_INDUCT THEN
  REWRITE_TAC[arithtrue; holds; termval] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [SIMP_TAC[ADD_CLAUSES; MULT_CLAUSES; EXP; SUC_INJ; NOT_SUC; valmod;
             ARITH_EQ; MESON[LE_EXISTS] `(?d. m + d = n) <=> m <= n`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`; `q:form`] THEN
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
