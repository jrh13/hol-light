(* ========================================================================= *)
(* 4CT/kempetree_wrap.ml                                                     *)
(*                                                                           *)
(* kempetree.v, last part: the Kempe tree of a configuration program.        *)
(* kempe_tree cp runs the Kempe closure fixpoint of kempetree.ml from the    *)
(* initial full trees of initctree.ml and initgtree.ml with the colouring    *)
(* tree cpcolor cp; the bridge lemmas KEMPE_COMPLETE_INIT, KEMPE_VALID_INIT  *)
(* and KEMPE_COMPLETEP (Coq kempetree.v:345-388) and the main theorem        *)
(* KEMPE_TREEP (Coq Kempe_treeP): a trace is outside the Kempe tree iff the  *)
(* ring traces of the configuration map are Kempe-coclosed at it.            *)
(* ========================================================================= *)

needs "4CT/cpcolor_correct.ml";;
needs "4CT/kempetree.ml";;
needs "4CT/initgtree.ml";;
needs "4CT/initctree.ml";;
needs "4CT/birkhoff.ml";;

(* ------------------------------------------------------------------------- *)
(* Colour-algebra / trace plumbing used by the completeness bridge.          *)
(* ------------------------------------------------------------------------- *)

let CBIT1_VALS = prove
 (`cbit1 Color0 = F /\ cbit1 Color1 = F /\ cbit1 Color2 = T /\
 cbit1 Color3 = T`,
  REWRITE_TAC[cbit1; distinctness "color"]);;

(* edge_rot permutations are 3-cycles; their pairwise compositions.          *)
let PERMT_231_231 = prove
 (`!t. permt Eperm231 (permt Eperm231 t) = permt Eperm312 t`,
  GEN_TAC THEN REWRITE_TAC[PERMT_PERMT; PERMT_MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:color` (cases "color")) THEN
  REWRITE_TAC[permc_DEF]);;

let PERMT_312_312 = prove
 (`!t. permt Eperm312 (permt Eperm312 t) = permt Eperm231 t`,
  GEN_TAC THEN REWRITE_TAC[PERMT_PERMT; PERMT_MAP] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `x:color` (cases "color")) THEN
  REWRITE_TAC[permc_DEF]);;

let LAM_312_231 = prove
 (`(\c. permc Eperm312 (permc Eperm231 c)) = (\c:color. c)`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:color` (cases "color")) THEN
  REWRITE_TAC[permc_DEF]);;

let LAM_231_312 = prove
 (`(\c. permc Eperm231 (permc Eperm312 c)) = (\c:color. c)`,
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  STRUCT_CASES_TAC(ISPEC `x:color` (cases "color")) THEN
  REWRITE_TAC[permc_DEF]);;

let PERMT_312_231 = prove
 (`!t. permt Eperm312 (permt Eperm231 t) = t`,
  GEN_TAC THEN REWRITE_TAC[PERMT_PERMT; LAM_312_231; MAP_ID]);;

let PERMT_231_312 = prove
 (`!t. permt Eperm231 (permt Eperm312 t) = t`,
  GEN_TAC THEN REWRITE_TAC[PERMT_PERMT; LAM_231_312; MAP_ID]);;

(* odd count of cbit1 colours = parity of the trace sum.                     *)
let ODD_COUNT_CBIT1 = prove
 (`!et. ODD (count_cbit1 et) <=> cbit1 (sumt et)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[count_cbit1; sumt; ODD; CBIT1_VALS];
    REWRITE_TAC[count_cbit1; sumt; CBIT1_ADDC] THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    REWRITE_TAC[CBIT1_VALS; ADD_CLAUSES; ODD_ADD] THEN
    REWRITE_TAC[ARITH_RULE `ODD 1`; ARITH_RULE `~ODD 0`] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN CONV_TAC TAUT]);;

let SUMT_CTRACE_C0 = prove
 (`!et. sumt (ctrace et) = Color0`,
  GEN_TAC THEN REWRITE_TAC[ctrace; sumt; ADDCC]);;

(* The Dyck weight of a ctrace is always positive (count_cbit1 is even).     *)
let DYCK_CTRACE_POS = prove
 (`!et. 0 < dyck (count_cbit1 (ctrace et))`,
  GEN_TAC THEN
  SUBGOAL_THEN `EVEN (count_cbit1 (ctrace et))` MP_TAC THENL
   [REWRITE_TAC[GSYM NOT_ODD; ODD_COUNT_CBIT1; SUMT_CTRACE_C0; CBIT1_VALS];
    REWRITE_TAC[EVEN_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[EVEN_DYCK_POS]]);;

let MEM_C0_APPEND1 = prove
 (`!et x. MEM Color0 (APPEND et [x]) <=> MEM Color0 et \/ x = Color0`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; MEM] THEN MESON_TAC[]);;

let MATCH_COUNT_ZERO = prove
 (`!et st bs. ~(?w. st w /\ matchpg bs et w) ==> match_count st bs et = 0`,
  MESON_TAC[MATCH_COUNTP]);;

(* even_trace is invariant under the edge_rot permutations (all 3-cycles).   *)
let EVEN_TRACE_PERMT_ROT = prove
 (`!e X. even_trace (permt (edge_rot e) X) <=> even_trace X`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[permt];
    REWRITE_TAC[permt; even_trace; ttail; proper_trace; NOT_CONS_NIL;
                HD; TL] THEN
    STRUCT_CASES_TAC(ISPEC `e:color` (cases "color")) THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    REWRITE_TAC[edge_rot_DEF; permc_DEF; distinctness "color"; NOT_CONS_NIL;
                PERMT_ID] THEN
    REWRITE_TAC[even_trace; ttail; proper_trace; NOT_CONS_NIL; HD; TL;
                distinctness "color"; edge_rot_DEF] THEN
    REWRITE_TAC[PERMT_231_231; PERMT_312_312; PERMT_312_231; PERMT_231_312;
                PERMT_ID]]);;

(* ------------------------------------------------------------------------- *)
(* The three bridge lemmas (Gonthier kempetree.v:345-388).                   *)
(* ------------------------------------------------------------------------- *)

(* Kempe_complete_init: the initial state is complete up to 3^(h+2), for any *)
(* ctr recognising all P-closed etraces (and any gtr).                       *)
let KEMPE_COMPLETE_INIT = prove
 (`!h P ctr gtr.
     (!et. P (ctrace_a et) ==> ctree_mem ctr (etrace et))
     ==> kempe_complete P (3 EXP (SUC(SUC h)))
           (ctree_init_tree (SUC h)) ctr gtr (gtree_init_tree (SUC h))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[kempe_complete] THEN CONJ_TAC THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `ctree_size (ctree_init_tree (SUC h)) <= 3 EXP (SUC h)`
    MP_TAC THENL
     [MATCH_MP_TAC CTREE_MAX_SIZE_PROPER THEN
     REWRITE_TAC[CTREE_INIT_TREE_PROPER];
      MATCH_MP_TAC(ARITH_RULE
        `3 EXP (SUC h) < 3 EXP (SUC(SUC h))
         ==> x <= 3 EXP (SUC h) ==> x < 3 EXP (SUC(SUC h))`) THEN
      REWRITE_TAC[LT_EXP] THEN ARITH_TAC];
    GEN_TAC THEN STRIP_TAC THENL
     [DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN REWRITE_TAC[gtree_sub] THEN
      MATCH_MP_TAC MATCH_COUNT_ZERO THEN
      REWRITE_TAC[GTREE_MEM_INIT_TREE; init_gtree_spec; NOT_EXISTS_THM] THEN
      X_GEN_TAC `w:(gram_symbol)list` THEN
      REWRITE_TAC[TAUT `~((a /\ b) /\ c) <=> a /\ b ==> ~c`] THEN
      STRIP_TAC THEN
      DISCH_TAC THEN
      UNDISCH_TAC `~ctree_mem (ctree_init_tree (SUC h))
      (permt (edge_rot e) (etrace et))` THEN
      REWRITE_TAC[ctree_mem; CTREE_SUB_INIT_TREE] THEN
      SUBGOAL_THEN
       `LENGTH (permt (edge_rot e) (etrace et)) = SUC h /\
        ~MEM Color0 (ctrace (permt (edge_rot e) (etrace et))) /\
        even_trace (permt (edge_rot e) (etrace et))`
       (fun th -> REWRITE_TAC[th]) THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[LENGTH_PERMT; ETRACE_LENGTH] THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP MATCHPG_SIZE) THEN
          ASM_REWRITE_TAC[] THEN ARITH_TAC;
          SUBGOAL_THEN `~(MEM Color0 (APPEND et [sumt et]))` MP_TAC THENL
           [MATCH_MP_TAC MATCHG_MEMC0 THEN
            MAP_EVERY EXISTS_TAC [`cgram 0 F w`; `[]:(bool)list`] THEN
            ASM_MESON_TAC[MATCHG_PG];
            REWRITE_TAC[MEM_C0_APPEND1; DE_MORGAN_THM] THEN STRIP_TAC THEN
            REWRITE_TAC[ctrace; MEM; MEM_COLOR0_PERMT; etrace; SUMT_PERMT] THEN
            ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
            REWRITE_TAC[PERMC_EQ_0; SUMT_PERMT] THEN
            REWRITE_TAC[PERMC_EQ_0] THEN ASM_REWRITE_TAC[]];
          REWRITE_TAC[EVEN_TRACE_PERMT_ROT; EVEN_ETRACE]];
        ALL_TAC] THEN
      MP_TAC(SPEC `permt (edge_rot e) (etrace et)` DYCK_CTRACE_POS) THEN
      ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Kempe_tree cp and Kempe_treeP (Gonthier kempetree.v:390-422).             *)
(* ------------------------------------------------------------------------- *)

let kempe_tree = new_definition
 `kempe_tree (cp:(cpstep)list) =
    if 2 <= cprsize cp then
      let h = cprsize cp - 2 in
      FST (kempe_tree_closure h (SUC(SUC h))
             (ctree_init_tree (SUC h)) (cpcolor cp) (gtree_init_tree (SUC h)))
    else CtreeEmpty`;;

(* ------------------------------------------------------------------------- *)
(* Trace-rotation / kempe_coclosure helpers for KEMPE_TREEP.                 *)
(* ------------------------------------------------------------------------- *)

(* rot1 (kempe.ml) is rot_list 1 (embed_prelim.ml).                          *)
let ROT1_ROT_LIST1 = prove
 (`!(l:(A)list). rot1 l = rot_list 1 l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[rot1; NOT_CONS_NIL; HD; TL; rot_list; num_CONV `1`;
              take_list; drop_list; APPEND_NIL; APPEND]);;

(* ctrace_a (SNOC form) is rot 1 of ctrace (CONS form).                      *)
let CTRACE_A_ROT = prove
 (`!et. ctrace_a et = rot_list 1 (ctrace et)`,
  REWRITE_TAC[CTRACE_A_ROT1; ROT1_ROT_LIST1]);;

(* ring_trace is preserved when the ring and the trace are rotated together. *)
let RING_TRACE_ROT_BOTH = prove
 (`!(G:(num)hypermap) r et'. ring_trace G r et' /\ ~(r = [])
     ==> ring_trace G (rot_list 1 r) (rot_list 1 et')`,
  SIMP_TAC[GSYM ROT1_ROT_LIST1; RING_TRACE_ROT1]);;

(* The inverse: un-rotate the ring and the trace together.                   *)
let RING_TRACE_ROTR_BOTH = prove
 (`!(G:(num)hypermap) (r:(num)list) (x:(color)list).
     ring_trace G (rot_list 1 r) (rot_list 1 x) /\ ~(r = [])
     ==> ring_trace G r x`,
  REWRITE_TAC[GSYM ROT1_ROT_LIST1] THEN
  MESON_TAC[RING_TRACE_ROTR1; ROTR1_ROT1]);;

(* KEMPE_TREEP (Gonthier's Kempe_treeP), for cubic programs (the hypothesis  *)
(* of CTREE_MEM_CPCOLOR).  Rotation: our ring_trace uses trace_col           *)
(* (Gonthier's urtrace) while his uses trace = urtrace o rot 1, so his       *)
(* ring_trace r is our ring_trace (rot 1 r); his Kempe_treeP takes the ring  *)
(* rot 1 cpring with his ctrace (the snoc form, our ctrace_a), so the        *)
(* faithful HOL ring is rot_list 1 (rot_list 1 cpring).  Proof: unfold       *)
(* kempe_tree (2 <= cprsize by CPRSIZE_GE_2); build kempe_valid by           *)
(* KEMPE_VALID_RESTRICT from KEMPE_VALID_INIT (the members of cpcolor cp are *)
(* P-closed by KEMPE_COCLOSURE_SELF, CTREE_MEM_CPCOLOR, RING_TRACE_ROT_BOTH  *)
(* and CTRACE_A_ROT); run KEMPE_TREE_CLOSURE_CORRECT; feed                   *)
(* KEMPE_COMPLETE_INIT using RING_TRACE_ROTR_BOTH and RING_TRACE_PERMT for   *)
(* the etrace gauge; then KEMPE_COMPLETEP decides.                           *)
let KEMPE_TREEP = prove
 (`!cp et.
     cubic_prog cp /\ LENGTH et = cprsize cp - 1
     ==> (kempe_coclosure (ring_trace (FST(cpmap cp))
              (rot_list 1 (rot_list 1 (cpring (FST(cpmap cp))
                                       (SND(cpmap cp)))))) (ctrace_a et) <=>
          ~(ctree_mem (kempe_tree cp) (etrace et)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CPRSIZE_GE_2) THEN
  ASM_REWRITE_TAC[kempe_tree] THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  ABBREV_TAC `h = cprsize cp - 2` THEN
  SUBGOAL_THEN `LENGTH (et:(color)list) = SUC h` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp)))` THEN
  SUBGOAL_THEN `~(r:num list = [])` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC ROT_LIST_NONEMPTY THEN
    MATCH_MP_TAC CPRING_NONEMPTY THEN REWRITE_TAC[CPMAP_PT_IN_DART];
    ALL_TAC] THEN
  ABBREV_TAC `Pcol = ring_trace (FST(cpmap cp)) (rot_list 1 r)` THEN
  MP_TAC(ISPECL [`h:num`; `Pcol:(color)list->bool`; `SUC(SUC h)`;
                 `ctree_init_tree (SUC h)`; `cpcolor cp`;
                 `gtree_init_tree (SUC h)`] KEMPE_TREE_CLOSURE_CORRECT) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[KEMPE_VALID_INIT]
      (SPECL [`h:num`; `Pcol:(color)list->bool`; `ctree_init_tree (SUC h)`;
              `cpcolor cp`; `GtreeEmpty`; `gtree_init_tree (SUC h)`]
             KEMPE_VALID_RESTRICT)) THEN
    X_GEN_TAC `et1:(color)list` THEN ASM_SIMP_TAC[CTREE_MEM_CPCOLOR] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [EXPAND_TAC "Pcol" THEN MATCH_MP_TAC KEMPE_COCLOSURE_SELF THEN
      REWRITE_TAC[CTRACE_A_ROT; ctrace] THEN
      MATCH_MP_TAC RING_TRACE_ROT_BOTH THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP RING_TRACE_LENGTH) THEN
      EXPAND_TAC "r" THEN
      REWRITE_TAC[LENGTH; LENGTH_ROT_LIST; GSYM cprsize] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `res = kempe_tree_closure h (SUC (SUC h))
                      (ctree_init_tree (SUC h)) (cpcolor cp)
                      (gtree_init_tree (SUC h))` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `0`)) THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH_RULE `SUC 0 = 1`] THEN ANTS_TAC THENL
   [MATCH_MP_TAC KEMPE_COMPLETE_INIT THEN X_GEN_TAC `et1:(color)list` THEN
    ASM_SIMP_TAC[CTREE_MEM_CPCOLOR; EVEN_ETRACE; GSYM ctrace] THEN
    DISCH_TAC THEN
    REWRITE_TAC[etrace; CTRACE_PERMT] THEN MATCH_MP_TAC RING_TRACE_PERMT THEN
    MATCH_MP_TAC RING_TRACE_ROTR_BOTH THEN ASM_REWRITE_TAC[GSYM CTRACE_A_ROT];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `Pcol:(color)list->bool`;
                 `FST(res:ctree#gtree_pair)`; `CtreeEmpty`;
                 `gtree_pair_sub (SND(res:ctree#gtree_pair)) F`;
                 `gtree_pair_sub (SND(res:ctree#gtree_pair)) T`]
                KEMPE_COMPLETEP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC);;

