(* ========================================================================= *)
(* 4CT/cfreducible.ml                                                        *)
(*                                                                           *)
(* cfreducible.v: the reducibility check implies cfreducible, and the        *)
(* embedding consequence NOT_EMBED_REDUCIBLE_CONFIG.                         *)
(*                                                                           *)
(*   check_reducible cf  <=> cf passes the C-reducibility check:             *)
(*                           contract_ctree cf returns a ctree disjoint from *)
(*                           the Kempe tree of cfprog cf.                    *)
(*   cfreducible cf      <=> c_reducible (FST(cfmap cf)) (cfring cf)         *)
(*                           (cfcontract cf)   (c_reducible: embed_contract) *)
(*                                                                           *)
(* CHECK_REDUCIBLE_VALID : check_reducible cf ==> cfreducible cf chains      *)
(* CONTRACT_CTREEP (cfcontract.ml, which proves the whole valid_contract     *)
(* record including its triad clause), CTREE_MEM_DISJOINT (ctree.ml) and     *)
(* KEMPE_TREEP (kempetree_wrap.ml), with a Kempe-coclosure rotation          *)
(* conjugation tail (KEMPE_COCLOSURE_ROTR1, Gonthier's closedP1).            *)
(* NOT_EMBED_REDUCIBLE_CONFIG is Gonthier's present.v:183 step: a            *)
(* configuration that passes the check does not embed in a minimal           *)
(* counter-example (NOT_EMBED_REDUCIBLE of embed_contract.ml).               *)
(* ========================================================================= *)

needs "4CT/cfcontract.ml";;
needs "4CT/kempetree_wrap.ml";;
needs "4CT/kempe.ml";;
needs "4CT/embed_contract.ml";;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

(* check_reducible (Gonthier cfreducible.v:39, oapp (ctree_disjoint          *)
(* (Kempe_tree (cfprog cf))) false (contract_ctree cf)): the contract ctree  *)
(* exists and is disjoint from the Kempe tree.                               *)
let check_reducible = new_definition
 `check_reducible (cf:(cpstep)list#(num)list) <=>
    ?cct. contract_ctree cf = SOME cct /\
          ctree_disjoint (kempe_tree (cfprog cf)) cct`;;

(* cfreducible (Gonthier cfreducible.v:42).                                  *)
let cfreducible = new_definition
 `cfreducible (cf:(cpstep)list#(num)list) <=>
    c_reducible (FST(cfmap cf)) (cfring cf) (cfcontract cf)`;;

(* ------------------------------------------------------------------------- *)
(* Un-rotating a Kempe coclosure: the closedP1 conjugation of Gonthier       *)
(* cfreducible.v:58-64 (ROT1_ROT_LIST1 is in kempetree_wrap.ml).             *)
(* ------------------------------------------------------------------------- *)

(* Un-rotate a Kempe coclosure (both the ring-trace predicate and the seed). *)
let KEMPE_COCLOSURE_ROTR1 = prove
 (`!(G:(A)hypermap) s x.
     ~(s = []) /\
     kempe_coclosure (ring_trace G (rot_list 1 s)) (rot_list 1 x)
     ==> kempe_coclosure (ring_trace G s) x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ROT1_ROT_LIST1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[kempe_coclosure] THEN DISCH_TAC THEN
  X_GEN_TAC `Q:(color)list->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o
    SPEC `\y:(color)list. (Q:(color)list->bool)(rotr1 y)`) THEN
  ASM_SIMP_TAC[KEMPE_CLOSED_ROTR1; ROTR1_ROT1] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:(color)list` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `rotr1 (y:(color)list)` THEN ASM_SIMP_TAC[RING_TRACE_ROTR1]);;

(* contract_ctree cf = SOME cct forces cfctr_ok, hence config_prog, hence    *)
(* cubic.                                                                    *)
let CONTRACT_CTREE_CUBIC = prove
 (`!cf:(cpstep)list#(num)list cct.
      contract_ctree cf = SOME cct ==> cubic_prog(cfprog cf)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[contract_ctree] THEN
  REPEAT LET_TAC THEN REWRITE_TAC[cfctr] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[option_DISTINCT] THEN
  STRIP_TAC THEN ASM_MESON_TAC[CFCTR_CONFIG_PROG; CONFIG_PROG_CUBIC]);;

(* ------------------------------------------------------------------------- *)
(* CHECK_REDUCIBLE_VALID (Gonthier cfreducible.v:44).                        *)
(* ------------------------------------------------------------------------- *)

let CHECK_REDUCIBLE_VALID = prove
 (`!cf:(cpstep)list#(num)list. check_reducible cf ==> cfreducible cf`,
  GEN_TAC THEN REWRITE_TAC[check_reducible] THEN
  DISCH_THEN(X_CHOOSE_THEN `cct:ctree` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CONTRACT_CTREEP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CONTRACT_CTREE_CUBIC) THEN
  ASM_REWRITE_TAC[cfreducible; c_reducible; cfring; REVERSE_REVERSE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[cfmap]) THEN REWRITE_TAC[cfmap] THEN
  ABBREV_TAC `cp = cfprog (cf:(cpstep)list#(num)list)` THEN
  ABBREV_TAC `r = cpring (FST(cpmap cp)) (SND(cpmap cp))` THEN
  X_GEN_TAC `et:(color)list` THEN REWRITE_TAC[cc_ring_trace] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num->color` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `~(r:num list = []) /\ ~(rot_list 1 (et:(color)list) = []) /\
    rot_list 1 et = trace_col (rot_list 1 (MAP (k:num->color) r)) /\
    LENGTH (rot_list 1 et) = cprsize cp`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `LENGTH (r:num list) = cprsize cp /\ 2 <= cprsize cp`
    MP_TAC THENL
     [EXPAND_TAC "r" THEN
      ASM_SIMP_TAC[CPRSIZE_GE_2; SIZE_CPRING; CPMAP_PT_IN_DART;
                   CPRSIZE_OSIZE];
      STRIP_TAC THEN
      ASM_SIMP_TAC[TRACE_COL_ROT; LENGTH_ROT_LIST; LENGTH_TRACE; LENGTH_MAP;
                   MAP_EQ_NIL; GSYM LENGTH_EQ_NIL;
                   ARITH_RULE `2 <= n ==> 1 <= n /\ ~(n = 0)`]];
    ALL_TAC] THEN
  MATCH_MP_TAC KEMPE_COCLOSURE_ROTR1 THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC KEMPE_COCLOSURE_ROTR1 THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[ROT_LIST_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `rot_list 1 (rot_list 1 et) = ctrace_a (TL (rot_list 1 et))`
  SUBST1_TAC THENL
   [REWRITE_TAC[CTRACE_A_ROT] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CTRACE_BEHEAD_ZEROSUM THEN ASM_REWRITE_TAC[SUMT_TRACE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`cp:(cpstep)list`; `TL (rot_list 1 (et:(color)list))`]
    KEMPE_TREEP) THEN
  ASM_SIMP_TAC[LENGTH_TL] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(TAUT `(p <=> F) ==> ~p`) THEN
  MATCH_MP_TAC CTREE_MEM_DISJOINT THEN EXISTS_TAC `cct:ctree` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[cc_ring_trace] THEN EXISTS_TAC `k:num->color` THEN
  ASM_REWRITE_TAC[MAP_ROT_LIST]);;

(* ------------------------------------------------------------------------- *)
(* Side condition derived from check_reducible.                              *)
(* ------------------------------------------------------------------------- *)

(* The configuration ring has at least two darts (cprsize >= 2 for cubic     *)
(* progs).                                                                   *)
let CHECK_REDUCIBLE_RING_SIZE = prove
 (`!cf:(cpstep)list#(num)list.
     check_reducible cf ==> 2 <= LENGTH (cfring cf)`,
  GEN_TAC THEN REWRITE_TAC[check_reducible] THEN
  DISCH_THEN(X_CHOOSE_THEN `cct:ctree` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cubic_prog (cfprog cf)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTRACT_CTREE_CUBIC]; ALL_TAC] THEN
  REWRITE_TAC[cfring; LENGTH_REVERSE; cfmap] THEN
  MP_TAC(ISPECL[`FST(cpmap (cfprog cf))`;
    `SND(cpmap (cfprog cf))`] SIZE_CPRING) THEN
  REWRITE_TAC[CPMAP_PT_IN_DART] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM CPRSIZE_OSIZE] THEN
  MATCH_MP_TAC CPRSIZE_GE_2 THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* NOT_EMBED_REDUCIBLE_CONFIG (Gonthier present.v:183, `not_embed_reducible  *)
(* cexG cf_ok embedG red_cf`): a configuration that passes the reducibility  *)
(* check does not embed in a minimal counter-example.  The triad clause of   *)
(* valid_contract is part of cfreducible (CONTRACT_CTREEP), so               *)
(* NOT_EMBED_REDUCIBLE needs nothing beyond c_reducible and the ring-size    *)
(* side condition above.                                                     *)
(* ------------------------------------------------------------------------- *)

let NOT_EMBED_REDUCIBLE_CONFIG = prove
 (`!(Gm:(B)hypermap) (cf:(cpstep)list#(num)list) (h:num->B).
     check_reducible cf /\
     embed_context Gm (FST(cfmap cf)) (cfring cf) h
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL[`Gm:(B)hypermap`; `FST(cfmap cf)`; `cfring cf`; `h:num->B`;
                `cfcontract cf`] NOT_EMBED_REDUCIBLE) THEN
  ASM_SIMP_TAC[CHECK_REDUCIBLE_RING_SIZE] THEN
  MP_TAC(SPEC `cf:(cpstep)list#(num)list` CHECK_REDUCIBLE_VALID) THEN
  ASM_REWRITE_TAC[cfreducible]);;
