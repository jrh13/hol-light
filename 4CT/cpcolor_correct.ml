(* ========================================================================= *)
(* 4CT/cpcolor_correct.ml                                                    *)
(*                                                                           *)
(* cfcolor.v, second part: correctness of cpcolor for every construction     *)
(* program.  The colouring algorithm cpcolor (cfcolor.ml) enumerates exactly *)
(* the even partial ring traces of the colourings of cpmap cp, for every     *)
(* program (steps CpR n, CpRr, CpY, CpH, CpU, CpK, CpA), as in Gonthier's    *)
(* ctree_mem_cpcolor.  The argument is his per-step invariant cp_extcol: for *)
(* every step s the functional cpcolor1 s reflects colouring extension       *)
(* across the step (CPCOLOR1R_CORRECT, CPCOLOR1RR_CORRECT,                   *)
(* CPCOLOR1U_CORRECT, CPCOLOR1Y_CORRECT, CPCOLOR1H_CORRECT,                  *)
(* CPCOLOR1K_CORRECT and CPCOLOR1A_CORRECT), assembled by one induction with *)
(* a seven-way step dispatch (CPCOLOR1_CORRECT) into CTREE_MEM_CPCOLOR_ALL;  *)
(* CTREE_MEM_CPCOLOR_GEN (programs without CpRr, used by cfcontract.ml) and  *)
(* the cubic CTREE_MEM_CPCOLOR (used by kempetree_wrap.ml and birkhoff.ml)   *)
(* are corollaries.  Gonthier proves the Y and H steps through cpexpand,     *)
(* which rewrites them as sequences of U, K, R and R' steps; here they are   *)
(* proved directly, with their own extended colourings kuY and kuH.          *)
(*                                                                           *)
(* The carrier.  In the fixed num carrier the old-dart injection injcp is    *)
(* the identity: cpmap (catrev_cp cp1 cp2) is cpmap cp2 with the steps of    *)
(* cp1 applied on top, so Gonthier's injcp morphism facts become the         *)
(* per-step cface and edge preservation lemmas of cfmap.ml and of this file. *)
(* The only property of the later steps cp1 that a step lemma needs is that  *)
(* colourings of the final map restrict to colourings of the current map     *)
(* (cp_restrict, Gonthier's gcol_cface and gcol_adj); it holds for every     *)
(* program (CP_RESTRICT_ANY, proved before the step lemmas).                 *)
(*                                                                           *)
(* The trace convention.  trace_col L is Gonthier's urtrace (wrap sum        *)
(* first); his trace is urtrace o rot 1, realised here as ftrace L =         *)
(* trace_col (rot_list 1 L); CTREE_MEM_CPCOLOR uses rot_list 1 on the ring   *)
(* likewise.                                                                 *)
(* ========================================================================= *)

needs "4CT/cfcolor.ml";;
needs "4CT/kempetree.ml";;

(* ------------------------------------------------------------------------- *)
(* cpmap of concatenated / consed programs.                                  *)
(* ------------------------------------------------------------------------- *)

let CPMAP_CONS = prove
 (`!s t. cpmap (CONS s t) = cpstep_apply s (cpmap t)`,
  REWRITE_TAC[cpmap; ITLIST]);;

let CPMAP_CONS_U = prove
 (`!cp2. cpmap (CONS CpU cp2) =
         (ecpU (FST(cpmap cp2)) (SND(cpmap cp2)), ecpU_pt (FST(cpmap cp2)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

let CPMAP_NIL_FST = prove
  (`FST(cpmap []) = cpmap0`, REWRITE_TAC[cpmap; ITLIST]);;
let CPMAP_NIL_SND = prove (`SND(cpmap []) = 1`, REWRITE_TAC[cpmap; ITLIST]);;

(* ------------------------------------------------------------------------- *)
(* List rotation (mathcomp rot): length, map, indexing, composition.         *)
(* ------------------------------------------------------------------------- *)

let LENGTH_TAKE_LIST = prove
 (`!n l:A list. LENGTH(take_list n l) = MIN n (LENGTH l)`,
  INDUCT_TAC THEN REWRITE_TAC[take_list; LENGTH; ARITH_RULE `MIN 0 m = 0`] THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[take_list; LENGTH; NOT_CONS_NIL; HD; TL] THEN ARITH_TAC);;

let LENGTH_ROT_LIST = prove
 (`!n l:A list. LENGTH(rot_list n l) = LENGTH l`,
  REWRITE_TAC[rot_list; LENGTH_APPEND; LENGTH_TAKE_LIST; LENGTH_DROP_LIST] THEN
  ARITH_TAC);;

let ROT_LIST_NONEMPTY = prove
 (`!n (l:A list). ~(l = []) ==> ~(rot_list n l = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_ROT_LIST]);;

let MAP_TAKE_LIST = prove
 (`!f n l. MAP (f:A->B) (take_list n l) = take_list n (MAP f l)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[take_list; MAP] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[take_list; MAP; HD; TL; NOT_CONS_NIL]);;

let MAP_DROP_LIST = prove
 (`!f n l. MAP (f:A->B) (drop_list n l) = drop_list n (MAP f l)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[drop_list; MAP] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[drop_list; MAP; HD; TL; NOT_CONS_NIL]);;

let MAP_ROT_LIST = prove
 (`!f n l. MAP (f:A->B) (rot_list n l) = rot_list n (MAP f l)`,
  REWRITE_TAC[rot_list; MAP_APPEND; MAP_TAKE_LIST; MAP_DROP_LIST]);;

let TAKE_LIST_ALL = prove
 (`!n (l:A list). LENGTH l <= n ==> take_list n l = l`,
  INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[take_list; LENGTH; NOT_CONS_NIL; HD; TL; LE_SUC; LE_0;
               ARITH_RULE `~(SUC n <= 0)`]);;

let ROT_LIST_ALL = prove
 (`!n (l:A list). LENGTH l <= n ==> rot_list n l = l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rot_list] THEN
  SUBGOAL_THEN `drop_list n (l:A list) = []` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_DROP_LIST] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[TAKE_LIST_ALL; APPEND]]);;

let EL_DROP_LIST = prove
 (`!n l i. i + n < LENGTH l ==> EL i (drop_list n (l:A list)) = EL (i + n) l`,
  INDUCT_TAC THEN REWRITE_TAC[drop_list; ADD_CLAUSES] THEN
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; LT; NOT_CONS_NIL; TL; LT_SUC; ADD_CLAUSES; EL]);;

let EL_TAKE_LIST = prove
 (`!n l i. i < n /\ i < LENGTH l ==> EL i (take_list n (l:A list)) = EL i l`,
  INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; CONJUNCT1 LT; take_list; NOT_CONS_NIL; HD; TL] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; TL; LT_SUC]);;

let EL_ROT_LIST = prove
 (`!n l i. n <= LENGTH l /\ i < LENGTH l
           ==> EL i (rot_list n (l:A list)) =
               (if i < LENGTH l - n then EL (i + n) l
                else EL (i - (LENGTH l - n)) l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rot_list] THEN
  ASM_SIMP_TAC[EL_APPEND; LENGTH_DROP_LIST] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC EL_DROP_LIST THEN ASM_ARITH_TAC;
    MATCH_MP_TAC EL_TAKE_LIST THEN ASM_ARITH_TAC]);;

let ROT_LIST_ADD = prove
 (`!a b (L:A list). a + b <= LENGTH L
     ==> rot_list a (rot_list b L) = rot_list (a + b) L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ; LENGTH_ROT_LIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH(L:A list)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[LENGTH_ROT_LIST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:num`; `rot_list b (L:A list)`; `i:num`] EL_ROT_LIST) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[LENGTH_ROT_LIST] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_ROT_LIST] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`a + b:num`; `L:A list`; `i:num`] EL_ROT_LIST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `i < LENGTH(L:A list) - a` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`b:num`; `L:A list`; `i + a:num`] EL_ROT_LIST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `i < LENGTH(L:A list) - (a + b)`
     (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       ASM_ARITH_TAC;
      SUBGOAL_THEN `~(i < LENGTH(L:A list) - (a + b))`
      (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       ASM_ARITH_TAC];
    MP_TAC(ISPECL [`b:num`; `L:A list`; `i - (LENGTH(L:A list) - a):num`
    ] EL_ROT_LIST) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `~(i < LENGTH(L:A list) - (a + b))`
    (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rotation commutes with the cyclic trace (Gonthier trace_rot).  The        *)
(* one-step case is PTRACE_SNOC, the general case an induction on n.         *)
(* ------------------------------------------------------------------------- *)

let TRACE_ROT1 = prove
 (`!L:color list. trace_col (rot_list 1 L) = rot_list 1 (trace_col L)`,
  LIST_INDUCT_TAC THENL
   [REWRITE_TAC[rot_list; drop_list; take_list; ONE; APPEND; trace_DEF];
    REWRITE_TAC[ROT_LIST_ONE; trace_DEF; APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST; ptrace] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 APPEND)] THEN
    SIMP_TAC[PTRACE_SNOC; NOT_CONS_NIL; ROT_LIST_ONE; LAST]]);;

let TRACE_COL_ROT = prove
 (`!n (L:color list). n <= LENGTH L /\ ~(L = [])
     ==> trace_col (rot_list n L) = rot_list n (trace_col L)`,
  INDUCT_TAC THEN REWRITE_TAC[ROT_LIST_0] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1`; `n:num`; `trace_col (L:color list)`] ROT_LIST_ADD) THEN
  MP_TAC(ISPECL [`1`; `n:num`; `L:color list`] ROT_LIST_ADD) THEN
  REWRITE_TAC[LENGTH_TRACE] THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC n <= m ==> 1 + n <= m`] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[TRACE_ROT1] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `SUC n <= m ==> n <= m`]);;

let TRACE_COL_NONEMPTY = prove
 (`!L:(color)list. ~(L = []) ==> ~(trace_col L = [])`,
  REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_TRACE]);;

(* ------------------------------------------------------------------------- *)
(* ftrace = Gonthier's `trace`: the ring trace with the wrap sum last, so a  *)
(* step prepends its new colours at the front.  ftrace (a :: M) is the       *)
(* partial trace of a :: M ++ [a]; ftrace (a :: X :: M) exposes its head.    *)
(* ------------------------------------------------------------------------- *)

let ftrace = new_definition
 `ftrace (lc:color list) = trace_col (rot_list 1 lc)`;;

let LENGTH_FTRACE = prove
 (`!L:color list. LENGTH(ftrace L) = LENGTH L`,
  REWRITE_TAC[ftrace; LENGTH_TRACE; LENGTH_ROT_LIST]);;

let FTRACE_ROT = prove
 (`!n (L:color list). ftrace (rot_list n L) = rot_list n (ftrace L)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `LENGTH(L:color list) <= n` THENL
   [ASM_SIMP_TAC[ROT_LIST_ALL; LENGTH_FTRACE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(L:color list = []) /\ n <= LENGTH L` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; LE_0; NOT_LE; LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[ftrace] THEN
  SUBGOAL_THEN
    `rot_list 1 (rot_list n L) = rot_list n (rot_list 1 (L:color list))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[ROT_LIST_ADD;
                 ARITH_RULE `~(m <= n) ==> 1 + n <= m /\ n + 1 <= m`] THEN
    REWRITE_TAC[ADD_SYM];
    MATCH_MP_TAC TRACE_COL_ROT THEN
    ASM_SIMP_TAC[ROT_LIST_NONEMPTY; LENGTH_ROT_LIST]]);;

let FTRACE_CONS1 = prove
 (`!a (M:color list). ftrace (CONS a M) = ptrace (CONS a (APPEND M [a]))`,
  REWRITE_TAC[ftrace; ROT_LIST_ONE; trace_DEF; APPEND_EQ_NIL; NOT_CONS_NIL;
              LAST_APPEND; LAST]);;

let FTRACE_CONS2 = prove
 (`!a X (M:color list).
     ftrace (CONS a (CONS X M)) =
     CONS (addc a X) (ptrace (CONS X (APPEND M [a])))`,
  REWRITE_TAC[FTRACE_CONS1; APPEND; ptrace]);;

let FTRACE_CONS2_TL = prove
 (`!a X b (M:color list).
     ftrace (CONS a (CONS X M)) =
     CONS (addc a X) (CONS (addc X (HD(APPEND M [a])))
                           (TL(TL(ftrace (CONS a (CONS b M))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FTRACE_CONS2; TL] THEN
  SUBGOAL_THEN
    `APPEND (M:color list) [a] = CONS (HD(APPEND M [a])) (TL(APPEND M [a]))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CONS_HD_TL THEN REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL];
    REWRITE_TAC[ptrace; HD; TL]]);;

(* ------------------------------------------------------------------------- *)
(* Rotating the ring pointer rotates the ring list and its trace             *)
(* (Gonthier cpring_ecpR, trace_rot).                                        *)
(* ------------------------------------------------------------------------- *)

let ORBIT_SIZE_ITER_GEN = prove
 (`!(f:A->A) s x j. FINITE s /\ f permutes s /\ x IN s
     ==> orbit_size f (ITER j f x) = orbit_size f x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orbit_size] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC ORBIT_MAP_EQ THEN EXISTS_TAC `s:A->bool` THEN
  ASM_REWRITE_TAC[ORBIT_MAP_ITER] THEN MESON_TAC[]);;

let ORBIT_LIST_ROT = prove
 (`!(f:A->A) s x j. FINITE s /\ f permutes s /\ x IN s /\ j <= orbit_size f x
     ==> orbit_list f (ITER j f x) = rot_list j (orbit_list f x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < orbit_size (f:A->A) x /\ ITER j f x IN s /\
                orbit_size f (ITER j f x) = orbit_size f x`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ORBIT_SIZE_POS; ITER_PERMUTES_IN; ORBIT_SIZE_ITER_GEN];
    ALL_TAC] THEN
  REWRITE_TAC[LIST_EQ] THEN
  ASM_SIMP_TAC[LENGTH_ORBIT_LIST; LENGTH_ROT_LIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_ORBIT_LIST; EL_ROT_LIST; LENGTH_ORBIT_LIST; ITER_ADD] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[EL_ORBIT_LIST; ARITH_RULE `i < n - j ==> i + j < n`] THEN
  ASM_SIMP_TAC[EL_ORBIT_LIST;
               ARITH_RULE `i < n /\ ~(i < n - j) ==> i - (n - j) < n`] THEN
  SUBGOAL_THEN `i + j = (i - (orbit_size (f:A->A) x - j)) + orbit_size f x`
  SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[GSYM ITER_ADD]] THEN
  ASM_MESON_TAC[ITER_ORBIT_SIZE]);;

let REVERSE_ROT_LIST = prove
 (`!m (l:A list). m <= LENGTH l
     ==> REVERSE (rot_list m l) = rot_list (LENGTH l - m) (REVERSE l)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_EQ] THEN
  REWRITE_TAC[LENGTH_REVERSE; LENGTH_ROT_LIST] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i < LENGTH(l:A list)` ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN
   REWRITE_TAC[LENGTH_REVERSE; LENGTH_ROT_LIST]; ALL_TAC] THEN
  ASM_SIMP_TAC[EL_REVERSE; LENGTH_ROT_LIST] THEN
  MP_TAC(ISPECL [`m:num`; `l:A list`;
                 `LENGTH(l:A list) - 1 - i`] EL_ROT_LIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`LENGTH(l:A list) - m`; `REVERSE(l:A list)`; `i:num`
  ] EL_ROT_LIST) THEN
  ANTS_TAC THENL [REWRITE_TAC[LENGTH_REVERSE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LENGTH_REVERSE] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `i < LENGTH(l:A list) - (LENGTH l - m)` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `~(LENGTH(l:A list) - 1 - i < LENGTH l - m)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EL_REVERSE; ARITH_RULE
      `i < LENGTH(l:A list) - (LENGTH l - m) /\ m <= LENGTH l ==>
       i + LENGTH l - m < LENGTH l`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `LENGTH(l:A list) - 1 - i < LENGTH l - m` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EL_REVERSE;
 ARITH_RULE `i < LENGTH(l:A list) ==>
 i - (LENGTH l - (LENGTH l - m)) < LENGTH l`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let CPRING_ECPR_ROT = prove
 (`!(G2:(num)hypermap) x2 n. x2 IN dart G2 /\ n <= orbit_size (node_map G2) x2
     ==> cpring G2 (ecpR_pt G2 n x2) = rot_list n (cpring G2 x2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `G2:(num)hypermap` HYPERMAP_LEMMA) THEN STRIP_TAC THEN
  REWRITE_TAC[cpring; ecpR_pt; ITER_2_COMMUTE] THEN
  SUBGOAL_THEN `node_map G2 (node_map G2 (x2:num)) IN dart G2 /\
                orbit_size (node_map G2) (node_map G2 (node_map G2 x2)) =
                orbit_size (node_map G2) x2 /\ 0 < orbit_size (node_map G2) x2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; ITER_2; ORBIT_SIZE_ITER_GEN;
                  ORBIT_SIZE_POS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map(G2:(num)hypermap)`; `dart(G2:(num)hypermap)`;
                 `node_map G2 (node_map G2 (x2:num))`;
                 `orbit_size (node_map G2) (x2:num) - n`] ORBIT_LIST_ROT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `m - n <= m`] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REVERSE_ROT_LIST; LENGTH_ORBIT_LIST; ARITH_RULE `m - n <= m`
  ] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let FTRACE_CPRING_ECPR_ROT = prove
 (`!(G2:(num)hypermap) x2 n k.
     x2 IN dart G2
     ==> ftrace (MAP k (cpring G2 (ecpR_pt G2 n x2))) =
         rot_list n (ftrace (MAP k (cpring G2 x2)))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n <= orbit_size (node_map G2) (x2:num)` THENL
   [ASM_SIMP_TAC[CPRING_ECPR_ROT; MAP_ROT_LIST; FTRACE_ROT]; ALL_TAC] THEN
  SUBGOAL_THEN `ecpR_pt G2 n (x2:num) = x2` SUBST1_TAC THENL
   [REWRITE_TAC[ecpR_pt] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n <= m) ==> m - n = 0`; ITER];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC ROT_LIST_ALL THEN
    ASM_SIMP_TAC[LENGTH_FTRACE; LENGTH_MAP; SIZE_CPRING] THEN ASM_ARITH_TAC]);;

let ROT_LIST_C1C1 = prove
 (`!n. rot_list n [Color1; Color1] = [Color1; Color1]`,
  GEN_TAC THEN ASM_CASES_TAC `2 <= n` THENL
   [ASM_SIMP_TAC[ROT_LIST_ALL; LENGTH; ARITH_RULE `SUC(SUC 0) = 2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `n = 0 \/ n = 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ROT_LIST_0; ROT_LIST_ONE; APPEND]);;

(* ------------------------------------------------------------------------- *)
(* Trace normalisation (Gonthier color.v etail_perm, eptrace_inj): etail is  *)
(* invariant under colour permutations, eptrace under injective recolouring. *)
(* ------------------------------------------------------------------------- *)

let PERMT_INV_CANCEL = prove
 (`!p l. permt (inv_eperm p) (permt p l) = l`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`inv_eperm p`; `p:edge_perm`; `Eperm123`; `Eperm123`]
                PERMT_PERMT_CONG) THEN
  REWRITE_TAC[INV_PERMC; permc_DEF; PERMT_ID]);;

let ETAIL_PERM = prove
 (`!et. proper_trace et ==> ?g. permt g et = CONS Color1 (etail et)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[proper_trace; NOT_CONS_NIL; HD] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM TTAIL_ETRACE; etrace] THEN
  ABBREV_TAC `hh = etrace_perm (CONS (h:color) t)` THEN
  REWRITE_TAC[permt; ttail; proper_trace; NOT_CONS_NIL; HD; TL;
              PERMC_EQ_0] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`edge_rot (permc hh h)`; `hh:edge_perm`] COMPOSE_PERMT) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:edge_perm` (fun th ->
    EXISTS_TAC `g:edge_perm` THEN REWRITE_TAC[GSYM(CONJUNCT2 permt)] THEN
    REWRITE_TAC[GSYM th])) THEN
  REWRITE_TAC[permt; CONS_11] THEN
  SUBGOAL_THEN `~(permc hh h = Color0)` MP_TAC THENL
   [ASM_REWRITE_TAC[PERMC_EQ_0];
    SPEC_TAC(`permc hh h`,`d:color`) THEN MATCH_MP_TAC color_INDUCT THEN
    REWRITE_TAC[edge_rot_DEF; permc_DEF; distinctness "color"]]);;

let EVEN_TAIL_PERM_EQ = prove
 (`!r t1 t2. permt r (CONS Color1 t1) = CONS Color1 t2 /\
             even_tail t1 /\ even_tail t2
             ==> t1 = t2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[permt; CONS_11] THEN STRIP_TAC THEN
  SUBGOAL_THEN `r = Eperm123 \/ r = Eperm132` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `permc r Color1 = Color1` THEN
    SPEC_TAC(`r:edge_perm`,`r:edge_perm`) THEN
    MATCH_MP_TAC edge_perm_INDUCT THEN
    REWRITE_TAC[permc_DEF; distinctness "color"];
    ASM_MESON_TAC[PERMT_ID];
    UNDISCH_TAC `permt r t1 = t2` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `even_tail (permt Eperm132 t1)` THEN
    UNDISCH_TAC `even_tail t1` THEN
    SPEC_TAC(`t1:color list`,`t:color list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[permt] THEN
    STRUCT_CASES_TAC(ISPEC `h:color` (cases "color")) THEN
    ASM_REWRITE_TAC[permc_DEF; even_tail; distinctness "color"; CONS_11] THEN
    ASM_MESON_TAC[]]);;

let ETAIL_PERMT = prove
 (`!g et. etail (permt g et) = etail et`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `proper_trace et` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[etail; ttail; PROPER_PERMT; etrace_perm; even_trace] THEN
    COND_CASES_TAC THEN REWRITE_TAC[permt; PERMC_0]] THEN
  MP_TAC(ISPEC `permt g et` ETAIL_PERM) THEN
  MP_TAC(ISPEC `et:color list` ETAIL_PERM) THEN
  ASM_REWRITE_TAC[PROPER_PERMT] THEN
  DISCH_THEN(X_CHOOSE_TAC `p:edge_perm`) THEN
  DISCH_THEN(X_CHOOSE_TAC `h:edge_perm`) THEN
  MP_TAC(ISPECL [`h:edge_perm`; `g:edge_perm`] COMPOSE_PERMT) THEN
  DISCH_THEN(X_CHOOSE_TAC `hg:edge_perm`) THEN
  MP_TAC(ISPECL [`hg:edge_perm`; `inv_eperm p`] COMPOSE_PERMT) THEN
  DISCH_THEN(X_CHOOSE_TAC `q:edge_perm`) THEN
  MATCH_MP_TAC(GSYM EVEN_TAIL_PERM_EQ) THEN
  EXISTS_TAC `q:edge_perm` THEN REWRITE_TAC[EVEN_ETAIL] THEN
  ASM_MESON_TAC[PERMT_INV_CANCEL]);;

let EPTRACE_INJ = prove
 (`!f lc. (!x y:color. f x = f y ==> x = y) ==>
 eptrace (MAP f lc) = eptrace lc`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[eptrace] THEN
  ONCE_REWRITE_TAC[GSYM(ISPECL [`(f:color->color) Color0`;
                                `MAP (f:color->color) lc`] PTRACE_ADDC)] THEN
  REWRITE_TAC[GSYM MAP_o; o_DEF] THEN
  MP_TAC(ISPEC `\c. addc ((f:color->color) Color0) (f c)` COLOR_INJ_PERMC) THEN
  REWRITE_TAC[ADDCC; ADDC_CANCEL_L] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN(X_CHOOSE_TAC `q:edge_perm`)] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[ETA_AX; GSYM PERMT_MAP; PTRACE_PERMT; ETAIL_PERMT]);;

(* ------------------------------------------------------------------------- *)
(* Colouring facts: adjacent darts differ, injective recolouring, a dart and *)
(* its node image differ, so the ring of a coloured map is a proper cycle.   *)
(* ------------------------------------------------------------------------- *)

let ADJ_COLORING = prove
 (`!(H:(num)hypermap) (k:num->color) x y.
      coloring H k /\ edge_map H permutes dart H /\ x IN dart H /\ adj H x y
      ==> ~(k x = k y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[adj; rlink] THEN STRIP_TAC THEN
  SUBGOAL_THEN `z IN dart(H:(num)hypermap) /\ edge_map H z IN dart H`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_IN_DART; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:num->color) x = k z /\ k y = k (edge_map H z)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_MESON_TAC[CFACE_COLORING; CFACE_SYM; cface];
    ASM_MESON_TAC[coloring]]);;

let COLORING_INJ_GEN = prove
 (`!(H:(num)hypermap) k h.
     coloring H k /\ (!x y:color. h x = h y ==> x = y)
     ==> coloring H (h o k)`,
  REWRITE_TAC[coloring; o_THM] THEN MESON_TAC[]);;

let COLORING_NODE = prove
 (`!(H:(num)hypermap) k x.
     coloring H k /\ x IN dart H ==> ~(k(node_map H x) = k x)`,
  MESON_TAC[COLORING_NODE_NEQ]);;

let COLORING_PROPER_CPRING = prove
 (`!(H:(num)hypermap) k x0. coloring H k /\ x0 IN dart H
                            ==> 2 <= orbit_size (node_map H) x0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 < n`] THEN
  MATCH_MP_TAC ORBIT_SIZE_GT_1 THEN EXISTS_TAC `dart(H:(num)hypermap)` THEN
  ASM_MESON_TAC[HYPERMAP_LEMMA; COLORING_NODE]);;

(* ------------------------------------------------------------------------- *)
(* The ring is a node cycle: consecutive ring darts are node-linked.         *)
(* ------------------------------------------------------------------------- *)

let RING_CONSEC_NODE = prove
 (`!(H:(num)hypermap) x0 i.
     x0 IN dart H /\ SUC i < orbit_size (node_map H) x0
     ==> node_map H (EL (SUC i) (cpring H x0)) = EL i (cpring H x0)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EL_CPRING; ARITH_RULE `SUC i < s ==> i < s`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 ITER)] THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ASM_ARITH_TAC);;

let RING_WRAP_NODE = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ 2 <= orbit_size (node_map H) x0
     ==> node_map H (EL 0 (cpring H x0)) =
         EL (orbit_size (node_map H) x0 - 1) (cpring H x0)`,
  REPEAT STRIP_TAC THEN ABBREV_TAC `s = orbit_size (node_map H) (x0:num)` THEN
  ASM_SIMP_TAC[EL_CPRING; ARITH_RULE `2 <= s ==> 0 < s /\ s - 1 < s`] THEN
  SUBGOAL_THEN `(s + 1) - 0 = SUC s /\ (s + 1) - (s - 1) = 2`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ITER s (node_map H) (x0:num) = x0` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC ITER_ORBIT_SIZE THEN
    EXISTS_TAC `dart(H:(num)hypermap)` THEN
    ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES];
    ASM_REWRITE_TAC[TWO; ONE; ITER]]);;

let EL_CPRING_IN_DART = prove
 (`!(H:(num)hypermap) x0 i.
     x0 IN dart H /\ i < LENGTH(cpring H x0) ==> EL i (cpring H x0) IN dart H`,
  MESON_TAC[MEM_CPRING_IN_DART; MEM_EL]);;

(* ------------------------------------------------------------------------- *)
(* The ring trace of a colouring never contains Color0 (memc0_trace_cpring). *)
(* ------------------------------------------------------------------------- *)

let PTRACE_NO_COLOR0 = prove
 (`!lc. (!i. SUC i < LENGTH lc ==> ~(EL i lc = EL (SUC i) lc))
        ==> ~(MEM Color0 (ptrace lc))`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[ptrace; MEM] THEN
  X_GEN_TAC `c1:color` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[ptrace; MEM] THEN
  MAP_EVERY X_GEN_TAC [`c2:color`; `rest:color list`] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_TAC THEN
  REWRITE_TAC[ptrace; MEM; DE_MORGAN_THM] THEN DISCH_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[ADDC_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
    REWRITE_TAC[LENGTH; EL; HD; TL; LT_SUC; LT_0];
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[LENGTH; LT_SUC] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC i`) THEN
    ASM_REWRITE_TAC[LENGTH; EL; TL; LT_SUC]]);;

let PTRACE_MAP_NO_COLOR0 = prove
 (`!(k:num->color) l.
     (!i. SUC i < LENGTH l ==> ~(k (EL i l) = k (EL (SUC i) l)))
     ==> ~(MEM Color0 (ptrace (MAP k l)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC PTRACE_NO_COLOR0 THEN
  REWRITE_TAC[LENGTH_MAP] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[EL_MAP; ARITH_RULE `SUC i < n ==> i < n`]);;

let MEMC0_TRACE_CPRING = prove
 (`!(H:(num)hypermap) k x0.
     coloring H k /\ x0 IN dart H
     ==> ~(MEM Color0 (trace_col (MAP k (cpring H x0))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = orbit_size (node_map H) (x0:num)` THEN
  ABBREV_TAC `r = cpring H (x0:num)` THEN
  SUBGOAL_THEN `2 <= s /\ LENGTH(r:num list) = s /\ ~(r = []) /\
                (!i. i < s ==> EL i r IN dart H)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COLORING_PROPER_CPRING; SIZE_CPRING; LENGTH_EQ_NIL;
                  ARITH_RULE `2 <= s ==> ~(s = 0)`; EL_CPRING_IN_DART];
    ALL_TAC] THEN
  UNDISCH_TAC `MEM Color0 (trace_col (MAP (k:num->color) r))` THEN
  ASM_SIMP_TAC[trace_DEF; MAP_EQ_NIL; LAST_MAP; GSYM(CONJUNCT2 MAP)] THEN
  MATCH_MP_TAC PTRACE_MAP_NO_COLOR0 THEN ASM_REWRITE_TAC[LENGTH; LT_SUC] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  DISJ_CASES_THEN2 SUBST_ALL_TAC (X_CHOOSE_THEN `j:num` SUBST_ALL_TAC)
    (SPEC `i:num` num_CASES) THENL
   [REWRITE_TAC[EL; HD; TL] THEN ASM_SIMP_TAC[LAST_EL] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] RING_WRAP_NODE) THEN
    ASM_REWRITE_TAC[EL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COLORING_NODE THEN
    ASM_MESON_TAC[ARITH_RULE `2 <= s ==> 0 < s`; EL];
    REWRITE_TAC[EL; TL] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`; `j:num`] RING_CONSEC_NODE) THEN
    ASM_REWRITE_TAC[EL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COLORING_NODE THEN ASM_MESON_TAC[EL]]);;

(* ------------------------------------------------------------------------- *)
(* The ring trace et = ftrace (MAP k ring) of a colouring: length >= 2, no   *)
(* Color0, proper tail; its normalised tail is eptrace (rot_list 1 ring).    *)
(* ------------------------------------------------------------------------- *)

let MEMC0_FTRACE_CPRING = prove
 (`!(H:(num)hypermap) k x0.
     coloring H k /\ x0 IN dart H ==>
     ~(MEM Color0 (ftrace (MAP k (cpring H x0))))`,
  REWRITE_TAC[ftrace; TRACE_ROT1; MEM_ROT_LIST] THEN
  MESON_TAC[MEMC0_TRACE_CPRING]);;

let TL_TRACE_COL = prove
 (`!L:color list. ~(L = []) ==> TL(trace_col L) = ptrace L`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[trace_DEF; NOT_CONS_NIL; ptrace; TL]);;

let TL_FTRACE = prove
 (`!L:color list. ~(L = []) ==> TL(ftrace L) = ptrace (rot_list 1 L)`,
  SIMP_TAC[ftrace; TL_TRACE_COL; ROT_LIST_NONEMPTY]);;

let LENGTH_ETAIL = prove
 (`!et. proper_trace et ==> LENGTH(etail et) = LENGTH et - 1`,
  GEN_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[etail; ttail; LENGTH_PERMT] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[proper_trace] THEN
  STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[NOT_CONS_NIL; TL; LENGTH; LENGTH_PERMT; SUC_SUB1]);;

let MEMC0_ETAIL = prove
 (`!Y:color list. ~(Y = []) /\ ~(MEM Color0 Y) ==> ~(MEM Color0 (etail Y))`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[NOT_CONS_NIL; MEM; DE_MORGAN_THM; etail; ttail; proper_trace;
              HD; TL; MEM_COLOR0_PERMT] THEN
  STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MEM_COLOR0_PERMT; MEM] THEN
  ASM_MESON_TAC[]);;

let PROPER_TRACE_TL = prove
 (`!et:color list. 2 <= LENGTH et /\ ~(MEM Color0 et) ==>
 proper_trace (TL et)`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `et:color list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= 0)`] THEN
  STRUCT_CASES_TAC(ISPEC `t:color list` list_CASES) THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= SUC 0)`; MEM; TL; proper_trace;
              NOT_CONS_NIL; HD] THEN
  MESON_TAC[]);;

let FTRACE_TAIL_FACTS = prove
 (`!L:color list. 2 <= LENGTH L /\ ~(MEM Color0 (ftrace L))
     ==> proper_trace (TL(ftrace L)) /\
         etail (TL(ftrace L)) = eptrace (rot_list 1 L) /\
         LENGTH(eptrace (rot_list 1 L)) = LENGTH L - 2 /\
         ~(MEM Color0 (eptrace (rot_list 1 L)))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(L:color list = []) /\ ~(ftrace L = [])`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LENGTH_EQ_NIL; LENGTH_FTRACE;
                  ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `proper_trace (TL(ftrace L)) /\ ~(MEM Color0 (TL(ftrace L)))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PROPER_TRACE_TL; LENGTH_FTRACE; MEM_TL_IMP]; ALL_TAC] THEN
  SUBGOAL_THEN `TL(ftrace L) = ptrace (rot_list 1 L)` SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[TL_FTRACE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[eptrace] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LENGTH_ETAIL; LENGTH_PTRACE; LENGTH_ROT_LIST] THEN ARITH_TAC;
    MATCH_MP_TAC MEMC0_ETAIL THEN ASM_MESON_TAC[proper_trace]]);;

let RING_FTRACE_FACTS = prove
 (`!(H:(num)hypermap) k x0.
     coloring H k /\ x0 IN dart H
     ==> 2 <= LENGTH(ftrace (MAP k (cpring H x0))) /\
         proper_trace (TL(ftrace (MAP k (cpring H x0)))) /\
         etail (TL(ftrace (MAP k (cpring H x0)))) =
         eptrace (rot_list 1 (MAP k (cpring H x0))) /\
         LENGTH(eptrace (rot_list 1 (MAP k (cpring H x0)))) =
         LENGTH(cpring H x0) - 2 /\
         ~(MEM Color0 (eptrace (rot_list 1 (MAP k (cpring H x0)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 <= LENGTH(cpring H (x0:num))` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIZE_CPRING; COLORING_PROPER_CPRING]; ALL_TAC] THEN
  MP_TAC(ISPEC `MAP (k:num->color) (cpring H x0)` FTRACE_TAIL_FACTS) THEN
  ASM_SIMP_TAC[MEMC0_FTRACE_CPRING; LENGTH_FTRACE; LENGTH_MAP]);;

(* ------------------------------------------------------------------------- *)
(* The ring trace of k at a proper ring x2 starts with k(node x2) +c k x2    *)
(* and k x2 +c k(face(edge x2)) (Gonthier trace_cpring_eq): face(edge x2) is *)
(* the third ring dart, or node x2 again when the ring has only two darts    *)
(* (CPRING_THIRD_COLOR).                                                     *)
(* ------------------------------------------------------------------------- *)

let HEAD_FTRACE_MAP_CPRING = prove
 (`!(G2:(num)hypermap) x2 k.
     x2 IN dart G2 /\ proper_cpring G2 x2
     ==> HD (ftrace (MAP k (cpring G2 x2))) = addc (k(node_map G2 x2)) (k x2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[MAP; FTRACE_CONS2; HD]);;

let LONG_CPRING_TLTL = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> (long_cpring H x0 <=> ~(TL(TL(cpring H x0)) = []))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIZE_LONG_CPRING] THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = TL(TL(cpring (H:(num)hypermap) x0))` THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LENGTH; GSYM LENGTH_EQ_NIL] THEN ARITH_TAC);;

let CPRING_THIRD_COLOR = prove
 (`!(G2:(num)hypermap) x2 (k:num->color).
     x2 IN dart G2 /\ proper_cpring G2 x2
     ==> HD (APPEND (MAP k (TL(TL(cpring G2 x2)))) [k(node_map G2 x2)]) =
         k(face_map G2 (edge_map G2 x2))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `long_cpring G2 (x2:num)` THENL
   [MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_LONG_CPRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[TL; MAP; APPEND; HD];
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] LONG_CPRING_TLTL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[long_cpring]) THEN
    ASM_REWRITE_TAC[MAP; APPEND; HD]]);;

let RING_TRACE_SHAPE = prove
 (`!(G2:(num)hypermap) x2 k.
     x2 IN dart G2 /\ proper_cpring G2 x2
     ==> ftrace (MAP k (cpring G2 x2)) =
         CONS (addc (k(node_map G2 x2)) (k x2))
              (CONS (addc (k x2) (k(face_map G2 (edge_map G2 x2))))
                    (TL(TL(ftrace (MAP k (cpring G2 x2))))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    CPRING_THIRD_COLOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = TL(TL(cpring (G2:(num)hypermap) x2))` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MAP; TL] THEN
  MATCH_ACCEPT_TAC FTRACE_CONS2_TL);;

let SECOND_FTRACE_MAP_CPRING = prove
 (`!(G2:(num)hypermap) x2 k.
     x2 IN dart G2 /\ proper_cpring G2 x2
     ==> HD(TL (ftrace (MAP k (cpring G2 x2)))) =
         addc (k x2) (k(face_map G2 (edge_map G2 x2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    RING_TRACE_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[HD; TL]);;

let RING_TRACE_HEADS = prove
 (`!(G2:(num)hypermap) x2 k.
     coloring G2 k /\ x2 IN dart G2
     ==> 2 <= LENGTH (ftrace (MAP k (cpring G2 x2))) /\
         HD (ftrace (MAP k (cpring G2 x2))) =
         addc (k(node_map G2 x2)) (k x2) /\
         HD (TL (ftrace (MAP k (cpring G2 x2)))) =
         addc (k x2) (k (face_map G2 (edge_map G2 x2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `proper_cpring (G2:(num)hypermap) x2` ASSUME_TAC THENL
   [REWRITE_TAC[proper_cpring] THEN ASM_MESON_TAC[COLORING_NODE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    RING_TRACE_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[LENGTH; HD; TL; ARITH_RULE `2 <= SUC(SUC n)`]);;

(* ------------------------------------------------------------------------- *)
(* The invariant (Gonthier cp_extcol).  catrev_cp cp1 cp2 is the program of  *)
(* the extended map; cp_tr0 says k0's ring trace standardises to et0.        *)
(* ------------------------------------------------------------------------- *)

let catrev_cp = new_definition
 `catrev_cp cp1 cp2 = APPEND (REVERSE cp1) cp2`;;

let CATREV_CP_NIL = prove
 (`!cp2. catrev_cp [] cp2 = cp2`, REWRITE_TAC[catrev_cp; REVERSE; APPEND]);;

let CATREV_CP_CONS = prove
 (`!s cp1 cp2. catrev_cp (CONS s cp1) cp2 = catrev_cp cp1 (CONS s cp2)`,
  REWRITE_TAC[catrev_cp; REVERSE; GSYM APPEND_ASSOC; APPEND]);;

let cp_tr0 = new_definition
 `cp_tr0 et0 cp1 cp2 (k0:num->color) <=>
    ttail et0 = eptrace
    (rot_list 1 (MAP k0 (cpring (FST(cpmap(catrev_cp cp1 cp2)))
                                                    (SND(cpmap(catrev_cp cp1
                                                    cp2))))))`;;

let cp_extcol = new_definition
 `cp_extcol et0 cp1 cp2 (f:(color)list->ctree) (k:num->color) <=>
    ctree_proper (cprsize (catrev_cp cp1 cp2) - 2)
                 (f (ftrace (MAP k (cpring (FST(cpmap cp2))
                                    (SND(cpmap cp2)))))) /\
    (ctree_mem (f (ftrace (MAP k (cpring (FST(cpmap cp2)) (SND(cpmap cp2))))))
    (ttail et0) <=>
     (?k0. (coloring (FST(cpmap(catrev_cp cp1 cp2))) k0 /\ cp_tr0 et0
            cp1 cp2 k0) /\
           (!x. x IN dart(FST(cpmap cp2)) ==> k0 x = k x)))`;;

(* gcol_perm: an affine recolouring c +c h(k0 x) preserves both invariants.  *)

let GCOL_PERM = prove
 (`!et0 cp1 cp2 (k0:num->color) c h.
      coloring (FST(cpmap(catrev_cp cp1 cp2))) k0 /\ cp_tr0 et0 cp1 cp2 k0
      ==> coloring (FST(cpmap(catrev_cp cp1 cp2)))
      (\x. addc c (permc h (k0 x))) /\
          cp_tr0 et0 cp1 cp2 (\x. addc c (permc h (k0 x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. addc c (permc h (k0 x))) = (\y. addc c (permc h y)) o (k0:num->color)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y. addc c (permc h x) = addc c (permc h y) ==> x = y`
  ASSUME_TAC THENL
   [MESON_TAC[ADDC_CANCEL_L; PERMC_INJ]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COLORING_INJ_GEN THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `cp_tr0 et0 cp1 cp2 k0` THEN REWRITE_TAC[cp_tr0] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM MAP_ROT_LIST; MAP_o] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC EPTRACE_INJ THEN ASM_REWRITE_TAC[]]);;

(* cpbranch_correct: the base case cp1 = [] of the per-step induction.       *)

let CPBRANCH_CORRECT = prove
 (`!et0 cp2 k. coloring (FST(cpmap cp2)) k ==>
 cp_extcol et0 [] cp2 cpbranch k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cp_extcol; cp_tr0; CATREV_CP_NIL] THEN
  MP_TAC(ISPECL [`FST(cpmap cp2)`; `k:num->color`; `SND(cpmap cp2)`]
                RING_FTRACE_FACTS) THEN
  ASM_REWRITE_TAC[CPMAP_PT_IN_DART] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CPBRANCH_SPEC; cprsize; CTREE_OF_TTAIL_MEM] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[CTREE_OF_TTAIL_PROPER];
    EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `k:num->color` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
      ASM_MESON_TAC[MEM_CPRING_IN_DART; CPMAP_PT_IN_DART]]]);;

(* ------------------------------------------------------------------------- *)
(* Geometry of the U and N steps on the two fresh darts a = FST(new_dart2    *)
(* ..) and b = SND(new_dart2 ..) and on the old darts. ecpY = ecpN o ecpU    *)
(* and ecpH = ecpN o ecpY, so the Y/H facts are instances.                   *)
(* ------------------------------------------------------------------------- *)

let ECP_EDGE_FRESH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> edge_map (ecpU H x0) (FST(new_dart2(dart H))) =
     SND(new_dart2(dart H)) /\
         edge_map (ecpU H x0) (SND(new_dart2(dart H))) =
         FST(new_dart2(dart H)) /\
         (!z. z IN dart H ==> edge_map (ecpU H x0) z = edge_map H z) /\
         edge_map (ecpN H x0) (FST(new_dart2(dart H))) =
         SND(new_dart2(dart H)) /\
         edge_map (ecpN H x0) (SND(new_dart2(dart H))) =
         FST(new_dart2(dart H)) /\
         (!z. z IN dart H ==> edge_map (ecpN H x0) z = edge_map H z)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [CONJUNCT1(CONJUNCT2(MATCH_MP ECPU_COMPONENTS th));
    CONJUNCT1(CONJUNCT2(MATCH_MP ECPN_COMPONENTS th))]) THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ECPU_EDGE_CLAUSES) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

let ECP_NEW_IN_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> FST(new_dart2(dart H)) IN dart(ecpU H x0) /\
         SND(new_dart2(dart H)) IN dart(ecpU H x0) /\
         dart H SUBSET dart(ecpU H x0) /\
         FST(new_dart2(dart H)) IN dart(ecpN H x0) /\
         SND(new_dart2(dart H)) IN dart(ecpN H x0) /\
         dart H SUBSET dart(ecpN H x0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [CONJUNCT1(MATCH_MP ECPU_COMPONENTS th);
    CONJUNCT1(MATCH_MP ECPN_COMPONENTS th)]) THEN
  SET_TAC[]);;

let IN_DART_ECPU = prove
 (`!(H:(num)hypermap) x0 u. x0 IN dart H
     ==> (u IN dart(ecpU H x0) <=>
          u = FST(new_dart2(dart H)) \/ u = SND(new_dart2(dart H)) \/
          u IN dart H)`,
  MESON_TAC[ECPU_COMPONENTS; IN_INSERT]);;

let IN_DART_ECPN = prove
 (`!(H:(num)hypermap) x0 u. x0 IN dart H
     ==> (u IN dart(ecpN H x0) <=>
          u = FST(new_dart2(dart H)) \/ u = SND(new_dart2(dart H)) \/
          u IN dart H)`,
  MESON_TAC[ECPN_COMPONENTS; IN_INSERT]);;

let IN_DART_ECPY = prove
 (`!(H:(num)hypermap) x0 u. x0 IN dart H
     ==> (u IN dart(ecpY H x0) <=>
          u = FST(new_dart2(dart(ecpU H x0))) \/
          u = SND(new_dart2(dart(ecpU H x0))) \/
          u = FST(new_dart2(dart H)) \/ u = SND(new_dart2(dart H)) \/
          u IN dart H)`,
  SIMP_TAC[ecpY; IN_DART_ECPN; ECPU_PT_IN_DART; IN_DART_ECPU]);;

let ECPN_FACE_NEW = prove
 (`!(G:(num)hypermap) y. y IN dart G ==>
 face_map (ecpN G y) (FST(new_dart2(dart G))) = y`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [CONJUNCT2(CONJUNCT2(CONJUNCT2(MATCH_MP ECPN_COMPONENTS th)))]) THEN
  REWRITE_TAC[ecpN_face]);;

(* The U step (interface forms).                                             *)

let EDGE_ECPU_OLD = prove
 (`!H x0 x. x0 IN dart H /\ FINITE(dart H) /\ x IN dart H
            ==> edge_map (ecpU H x0) x = edge_map H x`,
  MESON_TAC[ECP_EDGE_FRESH]);;

let EDGE_ECPU_B_APEX = prove
 (`!H x0. x0 IN dart H /\ FINITE(dart H)
          ==> edge_map (ecpU H x0) (SND(new_dart2(dart H))) = ecpU_pt H`,
  REWRITE_TAC[ecpU_pt] THEN MESON_TAC[ECP_EDGE_FRESH]);;

let EDGE_ECPN_OLD_GEN = prove
 (`!(H:(num)hypermap) x0 z. x0 IN dart H /\ z IN dart H
            ==> edge_map (ecpN H x0) z = edge_map H z`,
  MESON_TAC[ECP_EDGE_FRESH; FINITE_DART]);;

let DART_H_SUBSET_ECPU = prove
 (`!H x0 z. x0 IN dart H /\ z IN dart H ==> z IN dart(ecpU H x0)`,
  MESON_TAC[ECP_NEW_IN_DART; SUBSET]);;

let CFACE_STEP = prove
 (`!(H:(num)hypermap) x. cface H x (face_map H x)`,
  REWRITE_TAC[CFACE_FACE_SUCC]);;

let CFACE_ECPU_B_NODE = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ FINITE(dart G2)
     ==> cface (ecpU G2 x2) (SND(new_dart2(dart G2))) (node_map G2 x2)`,
  MESON_TAC[ECPU_FACE_SND; CFACE_STEP]);;

let FACE_ECPU_APEX_SING = prove
 (`!H x0 u. x0 IN dart H ==>
 (u IN face (ecpU H x0) (ecpU_pt H) <=> u = ecpU_pt H)`,
  REWRITE_TAC[GSYM cface] THEN MESON_TAC[CFACE_ECPU_APEX; CFACE_REFL]);;

let ADJ_ECPU_APEX = prove
 (`!H x0 u. x0 IN dart H
            ==> (adj (ecpU H x0) (ecpU_pt H) u <=>
                 cface (ecpU H x0) (SND(new_dart2(dart H))) u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[adj; rlink] THEN
  ASM_SIMP_TAC[FACE_ECPU_APEX_SING] THEN REWRITE_TAC[UNWIND_THM2] THEN
  ASM_SIMP_TAC[ECPU_EDGE_PT]);;

(* --- Y step: ecpY G x = ecpN (ecpU G x) (ecpU_pt G), new darts             *)
(* ecpY_pt G x = FST(new_dart2(dart(ecpU G x))) and its partner              *)
(* b' = SND(new_dart2(dart(ecpU G x))).                                      *)

let DART_H_SUBSET_ECPY = prove
 (`!H x0 z. x0 IN dart H /\ z IN dart H ==> z IN dart(ecpY H x0)`,
  REWRITE_TAC[ecpY] THEN MESON_TAC[ECP_NEW_IN_DART; SUBSET; ECPU_PT_IN_DART]);;

let HEAD_IN_DART_ECPY = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 ==>
 SND(new_dart2(dart G2)) IN dart(ecpY G2 x2)`,
  REWRITE_TAC[ecpY] THEN MESON_TAC[ECP_NEW_IN_DART; SUBSET; ECPU_PT_IN_DART]);;

let ECPU_PT_IN_DART_ECPY = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 ==> ecpU_pt G2 IN dart(ecpY G2 x2)`,
  REWRITE_TAC[ecpY] THEN MESON_TAC[ECP_NEW_IN_DART; SUBSET; ECPU_PT_IN_DART]);;

let BPRIME_IN_DART_ECPY = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2
     ==> SND(new_dart2(dart(ecpU G2 x2))) IN dart(ecpY G2 x2)`,
  REWRITE_TAC[ecpY] THEN MESON_TAC[ECP_NEW_IN_DART; ECPU_PT_IN_DART]);;

let EDGE_ECPY_ECPU = prove
 (`!(G2:(num)hypermap) x2 z.
     x2 IN dart G2 /\ FINITE(dart G2) /\ z IN dart(ecpU G2 x2)
     ==> edge_map (ecpY G2 x2) z = edge_map (ecpU G2 x2) z`,
  REWRITE_TAC[ecpY] THEN MESON_TAC[ECP_EDGE_FRESH; ECPU_PT_IN_DART]);;

let EDGE_ECPY_APEX = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 /\ FINITE(dart G2)
     ==> edge_map (ecpY G2 x2) (ecpY_pt G2 x2) =
     SND(new_dart2(dart(ecpU G2 x2)))`,
  REWRITE_TAC[ecpY; ecpY_pt; ecpN_pt] THEN
  MESON_TAC[ECP_EDGE_FRESH; ECPU_PT_IN_DART]);;

let EDGE_ECPY_B = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 /\ FINITE(dart G2)
     ==> edge_map (ecpY G2 x2) (SND(new_dart2(dart(ecpU G2 x2)))) =
     ecpY_pt G2 x2`,
  REWRITE_TAC[ecpY; ecpY_pt; ecpN_pt] THEN
  MESON_TAC[ECP_EDGE_FRESH; ECPU_PT_IN_DART]);;

let ADJ_EDGE_PAIR = prove
 (`!(G:(num)hypermap) u v. u IN dart G /\ edge_map G u = v ==> adj G u v`,
  MESON_TAC[ADJ_EDGE]);;

let ADJ_ECPY_APEX_B = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2
     ==> adj (ecpY G2 x2) (ecpY_pt G2 x2) (SND(new_dart2(dart(ecpU G2 x2))))`,
  MESON_TAC[ADJ_EDGE_PAIR; EDGE_ECPY_APEX; ECPY_PT_IN_DART; FINITE_DART]);;

let ADJ_ECPY_ECPUPT_HEAD = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2
     ==> adj (ecpY G2 x2) (ecpU_pt G2) (SND(new_dart2(dart G2)))`,
  MESON_TAC[ADJ_EDGE_PAIR; EDGE_ECPY_ECPU; ECPU_EDGE_PT; ECPU_PT_IN_DART;
            ECPU_PT_IN_DART_ECPY; FINITE_DART]);;

(* The inner-U face chain at the N step: face_ecpU(edge(node x2)) = x2 and   *)
(* face_ecpY b' = x2, so b' is in the face of x2 (Gonthier cface_icpY).      *)

let FACE_ECPU_EDGE_NODE = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 /\ proper_cpring G2 x2
     ==> face_map (ecpU G2 x2) (edge_map G2 (node_map G2 x2)) = x2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `edge_map G2 (node_map G2 (x2:num)) IN dart G2` ASSUME_TAC THENL
   [ASM_MESON_TAC[NODE_FACE_IN_DART; EDGE_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] ECPU_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `dart(G2:(num)hypermap)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  REWRITE_TAC[ecpU_face; nodeK] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[proper_cpring]);;

let FACE_ECPY_B = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ FINITE(dart G2) /\
     edge_map G2 permutes dart G2 /\ node_map G2 permutes dart G2 /\
     face_map G2 permutes dart G2 /\ proper_cpring G2 x2
     ==> face_map (ecpY G2 x2) (SND(new_dart2(dart(ecpU G2 x2)))) = x2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpY] THEN
  SUBGOAL_THEN
    `ecpU_pt G2 IN dart(ecpU G2 x2) /\ long_cpring (ecpU G2 x2) (ecpU_pt G2) /\
                node_map G2 (x2:num) IN dart G2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ECPU_PT_IN_DART; LONG_ECPU; NODE_FACE_IN_DART]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ecpU (G2:(num)hypermap) x2`; `ecpU_pt (G2:(num)hypermap)`]
                ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `dart(ecpU (G2:(num)hypermap) x2)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[ecpN_face] THEN
  ASM_SIMP_TAC[ECPU_EDGE_PT; ECPU_FACE_SND; EDGE_ECPU_OLD;
               FACE_ECPU_EDGE_NODE]);;

let CFACE_ECPY_B_PT = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ FINITE(dart G2) /\
     edge_map G2 permutes dart G2 /\ node_map G2 permutes dart G2 /\
     face_map G2 permutes dart G2 /\ proper_cpring G2 x2
     ==> cface (ecpY G2 x2) (SND(new_dart2(dart(ecpU G2 x2)))) x2`,
  MESON_TAC[FACE_ECPY_B; CFACE_STEP]);;

(* --- H step: ecpH G x = ecpN (ecpY G x) (ecpY_pt G x), new darts           *)
(* ecpH_pt G x = FST(new_dart2(dart(ecpY G x))) and its partner              *)
(* b'' = SND(new_dart2(dart(ecpY G x))).                                     *)

let ECPH_DART = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> dart(ecpH H x0) =
         FST(new_dart2(dart(ecpY H x0))) INSERT
         SND(new_dart2(dart(ecpY H x0))) INSERT
         dart(ecpY H x0)`,
  REWRITE_TAC[ecpH] THEN MESON_TAC[ECPN_COMPONENTS; ECPY_PT_IN_DART]);;

let DART_ECPY_SUBSET_ECPH = prove
 (`!(H:(num)hypermap) x0 z. x0 IN dart H /\ z IN dart(ecpY H x0) ==>
 z IN dart(ecpH H x0)`,
  REWRITE_TAC[ecpH] THEN MESON_TAC[ECP_NEW_IN_DART; SUBSET; ECPY_PT_IN_DART]);;

let BPP_IN_DART_ECPH = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H
     ==> SND(new_dart2(dart(ecpY H x0))) IN dart(ecpH H x0)`,
  REWRITE_TAC[ecpH] THEN MESON_TAC[ECP_NEW_IN_DART; ECPY_PT_IN_DART]);;

let EDGE_ECPH_ECPY = prove
 (`!(G2:(num)hypermap) x2 z.
     x2 IN dart G2 /\ z IN dart(ecpY G2 x2)
     ==> edge_map (ecpH G2 x2) z = edge_map (ecpY G2 x2) z`,
  REWRITE_TAC[ecpH] THEN MESON_TAC[ECP_EDGE_FRESH; ECPY_PT_IN_DART]);;

let EDGE_ECPH_APEX = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 /\ proper_cpring G2 x2
     ==> edge_map (ecpH G2 x2) (ecpH_pt G2 x2) =
     SND(new_dart2(dart(ecpY G2 x2)))`,
  REWRITE_TAC[ecpH; ecpH_pt; ecpN_pt] THEN
  MESON_TAC[ECP_EDGE_FRESH; ECPY_PT_IN_DART]);;

let EDGE_ECPH_B = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2
     ==> edge_map (ecpH G2 x2) (SND(new_dart2(dart(ecpY G2 x2)))) =
     ecpH_pt G2 x2`,
  REWRITE_TAC[ecpH; ecpH_pt; ecpN_pt] THEN
  MESON_TAC[ECP_EDGE_FRESH; ECPY_PT_IN_DART]);;

let EDGE_ECPH_OLD = prove
 (`!(H:(num)hypermap) x0 z. x0 IN dart H /\ z IN dart H
            ==> edge_map (ecpH H x0) z = edge_map H z`,
  MESON_TAC[EDGE_ECPH_ECPY; DART_H_SUBSET_ECPY; EDGE_ECPY_OLD]);;

let FACE_ECPH_PT = prove
 (`!(H:(num)hypermap) x0. x0 IN dart H /\ proper_cpring H x0
     ==> face_map (ecpH H x0) (ecpH_pt H x0) = ecpY_pt H x0`,
  REWRITE_TAC[ecpH; ecpH_pt; ecpN_pt] THEN
  MESON_TAC[ECPN_FACE_NEW; ECPY_PT_IN_DART]);;

let EDGE_ECPY_NODE_ECPY_PT = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ FINITE(dart G2) /\
     edge_map G2 permutes dart G2 /\ node_map G2 permutes dart G2 /\
     face_map G2 permutes dart G2 /\
     proper_cpring G2 x2
     ==> edge_map (ecpY G2 x2) (node_map (ecpY G2 x2) (ecpY_pt G2 x2)) =
     ecpU_pt G2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NODE_ECPY_PT_VALUE] THEN
  ASM_MESON_TAC[EDGE_ECPY_ECPU; EDGE_ECPU_B_APEX; ECP_NEW_IN_DART]);;

let FACE_ECPH_ECPU_PT = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ FINITE(dart G2) /\
     edge_map G2 permutes dart G2 /\ node_map G2 permutes dart G2 /\
     face_map G2 permutes dart G2 /\
     proper_cpring G2 x2
     ==> face_map (ecpH G2 x2) (ecpU_pt G2) = ecpH_pt G2 x2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ecpU_pt G2 IN dart(ecpY (G2:(num)hypermap) x2) /\
                ecpY_pt G2 x2 IN dart(ecpY G2 x2) /\ edge_map G2 x2 IN dart G2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ECPU_PT_IN_DART_ECPY; ECPY_PT_IN_DART; EDGE_IN_DART];
    ALL_TAC] THEN
  REWRITE_TAC[ecpH; ecpH_pt] THEN
  MP_TAC(ISPECL [`ecpY (G2:(num)hypermap) x2`; `ecpY_pt (G2:(num)hypermap) x2`]
                ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `dart(ecpY (G2:(num)hypermap) x2)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  REWRITE_TAC[ecpN_face; ecpN_pt] THEN
  ASM_SIMP_TAC[ECPY_FACE_EDGE_PT; EDGE_ECPY_OLD; EDGE_ECPY_NODE_ECPY_PT] THEN
  SUBGOAL_THEN
    `~(ecpU_pt G2 = FST(new_dart2(dart(ecpY (G2:(num)hypermap) x2)))) /\
                ~(ecpU_pt G2 = SND(new_dart2(dart(ecpY G2 x2)))) /\
                ~(ecpU_pt G2 = edge_map G2 x2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ECPU_PT_NOT_IN_DART; FINITE_DART]; ASM_REWRITE_TAC[]]);;

(* b'' lies on the face of face(edge x2) in ecpH (Gonthier cface_icpH).      *)

let CFACE_ECPH_B_PT = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ FINITE(dart G2) /\
     edge_map G2 permutes dart G2 /\ node_map G2 permutes dart G2 /\
     face_map G2 permutes dart G2 /\ proper_cpring G2 x2
     ==> cface (ecpH G2 x2) (SND(new_dart2(dart(ecpY G2 x2))))
     (face_map G2 (edge_map G2 x2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `edge_map G2 (x2:num) IN dart G2 /\ edge_map G2 x2 IN dart(ecpY G2 x2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[EDGE_IN_DART; DART_H_SUBSET_ECPY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ecpY (G2:(num)hypermap) x2`; `ecpY_pt (G2:(num)hypermap) x2`]
                ECPN_B_IN_FACE_ORBIT) THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; HYPERMAP_LEMMA; EDGE_ECPY_APEX;
               FACE_ECPY_B; EDGE_ECPY_OLD; GSYM ecpH; GSYM face;
               GSYM cface] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
 `cface (ecpH G2 x2) (edge_map G2 (x2:num))
  (face_map (ecpY G2 x2) (edge_map G2 x2)) /\
                cface (ecpH G2 x2) (edge_map G2 x2)
                (face_map G2 (edge_map G2 x2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[ecpH] THEN MATCH_MP_TAC CFACE_ECPN_LIFT THEN
      ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; HYPERMAP_LEMMA; CFACE_STEP];
      MATCH_MP_TAC CFACE_ECPH_LIFT THEN ASM_REWRITE_TAC[CFACE_STEP]];
    ASM_MESON_TAC[CFACE_TRANS; CFACE_SYM; DART_ECPY_SUBSET_ECPH]]);;

let CFACE_LEFT_IN_DART = prove
 (`!(H:(A)hypermap) u z. cface H u z /\ z IN dart H ==> u IN dart H`,
  MESON_TAC[CFACE_SYM_GEN; FACE_IN_DART; cface]);;

let ADJ_ECPH_APEX_B = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2 /\ proper_cpring G2 x2
     ==> adj (ecpH G2 x2) (ecpH_pt G2 x2) (SND(new_dart2(dart(ecpY G2 x2))))`,
  MESON_TAC[ADJ_EDGE_PAIR; EDGE_ECPH_APEX; ECPH_PT_IN_DART]);;

let ADJ_ECPH_ECPYPT_BPRIME = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2
     ==> adj (ecpH G2 x2) (ecpY_pt G2 x2) (SND(new_dart2(dart(ecpU G2 x2))))`,
  MESON_TAC[ADJ_EDGE_PAIR; EDGE_ECPH_ECPY; EDGE_ECPY_APEX; ECPY_PT_IN_DART;
            DART_ECPY_SUBSET_ECPH; FINITE_DART]);;

let ADJ_ECPH_ECPUPT_HEAD = prove
 (`!(G2:(num)hypermap) x2. x2 IN dart G2
     ==> adj (ecpH G2 x2) (ecpU_pt G2) (SND(new_dart2(dart G2)))`,
  MESON_TAC[ADJ_EDGE_PAIR; EDGE_ECPH_ECPY; EDGE_ECPY_ECPU; ECPU_EDGE_PT;
            ECPU_PT_IN_DART; ECPU_PT_IN_DART_ECPY; DART_ECPY_SUBSET_ECPH;
            FINITE_DART]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of colourings (Gonthier's gcol_cface / gcol_adj through the   *)
(* injcp morphism).  cpstep_restrict s: a colouring of the map after step s  *)
(* is a colouring of the map before it; cp_restrict cp1 cp2: colourings of   *)
(* cpmap (catrev_cp cp1 cp2) restrict to cpmap cp2.                          *)
(* ------------------------------------------------------------------------- *)

let cpstep_restrict = new_definition
 `cpstep_restrict s <=>
    !(G:(num)hypermap) x (k0:num->color).
        x IN dart G /\ coloring (FST(cpstep_apply s (G,x))) k0 ==>
        coloring G k0`;;

let cp_restrict = new_definition
 `cp_restrict cp1 cp2 <=>
    !k0:num->color. coloring (FST(cpmap(catrev_cp cp1 cp2))) k0
                    ==> coloring (FST(cpmap cp2)) k0`;;

let CP_RESTRICT_ALL = prove
 (`!cp1 cp2. ALL cpstep_restrict cp1 ==> cp_restrict cp1 cp2`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; cp_restrict; CATREV_CP_NIL] THEN
  X_GEN_TAC `cp2:(cpstep)list` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CONS (h:cpstep) cp2`) THEN
  ASM_REWRITE_TAC[cp_restrict; CATREV_CP_CONS] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cpstep_restrict]) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`FST(cpmap cp2)`; `SND(cpmap cp2)`; `k0:num->color`]) THEN
  REWRITE_TAC[PAIR; CPMAP_PT_IN_DART; GSYM CPMAP_CONS] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* A colouring restricts along any step that keeps old darts, their edges    *)
(* and their cface relation.                                                 *)

let COLORING_RESTRICT_LIFT = prove
 (`!(H:(num)hypermap) H' k0.
     (!u v. u IN dart H /\ cface H u v ==> cface H' u v) /\
     (!u. u IN dart H ==> edge_map H' u = edge_map H u) /\
     dart H SUBSET dart H' /\ coloring H' k0
     ==> coloring H k0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [coloring]) THEN STRIP_TAC THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THEN X_GEN_TAC `u:num` THEN
  DISCH_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC CFACE_COLORING THEN EXISTS_TAC `H':(num)hypermap` THEN
    ASM_MESON_TAC[SUBSET; CFACE_STEP]]);;

let ECPU_RESTRICT = prove
 (`!(H:(num)hypermap) x0 k0. x0 IN dart H /\ coloring (ecpU H x0) k0 ==>
 coloring H k0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COLORING_RESTRICT_LIFT THEN
  EXISTS_TAC `ecpU (H:(num)hypermap) x0` THEN
  ASM_SIMP_TAC[CFACE_ECPU_LIFT; EDGE_ECPU_OLD; DART_SUBSET_ECPU;
               HYPERMAP_LEMMA]);;

let ECPN_RESTRICT = prove
 (`!(G:(num)hypermap) y k0.
     y IN dart G /\ long_cpring G y /\ coloring (ecpN G y) k0 ==>
     coloring G k0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COLORING_RESTRICT_LIFT THEN
  EXISTS_TAC `ecpN (G:(num)hypermap) y` THEN
  ASM_SIMP_TAC[CFACE_ECPN_LIFT; EDGE_ECPN_OLD_GEN; ECP_NEW_IN_DART;
               HYPERMAP_LEMMA]);;

(* An N step at a non-long ring has no colouring at all (its new face is a   *)
(* 2-cycle through an edge), so long_cpring is forced.                       *)

let ECPN_FACE_B_SHORT = prove
 (`!(G:(num)hypermap) y. y IN dart G /\ ~long_cpring G y
     ==> face_map (ecpN G y) (SND(new_dart2(dart G))) =
     FST(new_dart2(dart G))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `y:num`] ECPN_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPEC `dart(G:(num)hypermap)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[ecpN_face]);;

let ECPN_COLORING_LONG = prove
 (`!(G:(num)hypermap) y k0. y IN dart G /\ coloring (ecpN G y) k0 ==>
 long_cpring G y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `y:num`] ECP_NEW_IN_DART) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `y:num`] ECP_EDGE_FRESH) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `y:num`] ECPN_FACE_B_SHORT) THEN
  UNDISCH_TAC `coloring (ecpN G y) k0` THEN ASM_REWRITE_TAC[coloring] THEN
  MESON_TAC[]);;

(* The step predicate for R, R', U, Y, H and K.                              *)

let CPSTEP_APPLY_EXPAND = prove
 (`(!n (G:(num)hypermap) x. cpstep_apply (CpR n) (G,x) = (G, ecpR_pt G n x)) /\
   (!(G:(num)hypermap) x. cpstep_apply CpRr (G,x) = (G, ecpRr_pt G x)) /\
   (!(G:(num)hypermap) x. cpstep_apply CpY (G,x) = (ecpY G x, ecpY_pt G x)) /\
   (!(G:(num)hypermap) x. cpstep_apply CpH (G,x) = (ecpH G x, ecpH_pt G x)) /\
   (!(G:(num)hypermap) x. cpstep_apply CpU (G,x) = (ecpU G x, ecpU_pt G)) /\
   (!(G:(num)hypermap) x. cpstep_apply CpK (G,x) =
   (ecpN G (ecpRr_pt G x), ecpK_pt G x)) /\
   (!(G:(num)hypermap) x. cpstep_apply CpA (G,x) = (ecpA G x, ecpA_pt G x))`,
  REWRITE_TAC[cpstep_apply; ecpR; ECPRR_EQ; ecpK]);;

let CPSTEP_RESTRICT_CUBIC = prove
 (`(!n. cpstep_restrict (CpR n)) /\ cpstep_restrict CpRr /\
 cpstep_restrict CpU /\
   cpstep_restrict CpY /\ cpstep_restrict CpH /\ cpstep_restrict CpK`,
  REWRITE_TAC[cpstep_restrict; CPSTEP_APPLY_EXPAND; FST] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[ECPU_RESTRICT];
    ASM_MESON_TAC[ecpY; ECPU_RESTRICT; ECPN_RESTRICT;
                  ECPU_PT_IN_DART; LONG_ECPU];
    ASM_MESON_TAC[ecpH; ecpY; ECPU_RESTRICT; ECPN_RESTRICT; ECPN_COLORING_LONG;
                  ECPU_PT_IN_DART; ECPY_PT_IN_DART; LONG_ECPU];
    ASM_MESON_TAC[ECPN_RESTRICT; ECPN_COLORING_LONG; ECPRR_PT_IN_DART]]);;

(* ------------------------------------------------------------------------- *)
(* The A step merges the faces of face(edge x0) and node x0 (Gonthier        *)
(* ecpA_merge): when they are distinct faces, iterating ecpA_face from node  *)
(* x0 follows the old face of node x0 (ECPA_ITER_AGREE) and reaches          *)
(* face(edge x0) after one period (ECPA_ITER_REACH).  Hence every old face   *)
(* lies in a face of ecpA (CFACE_ECPA_STEP, SUB_CFACE_ICPA) and adjacency    *)
(* lifts to ecpA (ECPA_EDGE_CFACE, SUB_ADJ_ICPA).                            *)
(* ------------------------------------------------------------------------- *)

(* When edge x0 and node x0 lie on different faces, iterating ecpA_face      *)
(* from node x0 follows face_map H for less than a full loop.                *)

let ECPA_ITER_AGREE = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ ~cface H (edge_map H x0) (node_map H x0)
     ==> !k. k < orbit_size (face_map H) (node_map H x0)
             ==> ITER k (ecpA_face H x0) (node_map H x0) =
                 ITER k (face_map H) (node_map H x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`face_map (H:(num)hypermap)`; `dart(H:(num)hypermap)`;
                 `node_map H (x0:num)`; `0`; `SUC k`] ITER_INJ_PERIOD) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; LT_0; FINITE_DART; FACE_MAP_PERMUTES] THEN
  REWRITE_TAC[ITER] THEN
  SUBGOAL_THEN
   `ITER k (face_map H) (node_map H x0) IN dart H /\
    cface H (node_map H x0) (ITER k (face_map H) (node_map H (x0:num)))`
  MP_TAC THENL
   [ASM_SIMP_TAC[ITER_PERMUTES_IN; FACE_MAP_PERMUTES; NODE_MAP_IN_DART] THEN
    REWRITE_TAC[cface; face; ITER_IN_ORBIT];
    SPEC_TAC(`ITER k (face_map H) (node_map H (x0:num))`,`p:num`)] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ecpA_face] THEN
  ASM_MESON_TAC[CFACE_SYM_GEN]);;

(* Hence after a full node-face loop, ecpA_face reaches face(edge x0).       *)

let ECPA_ITER_REACH = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ ~cface H (edge_map H x0) (node_map H x0)
     ==> ITER (orbit_size (face_map H) (node_map H x0)) (ecpA_face H x0)
              (node_map H x0) =
         face_map H (edge_map H x0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_ITER_AGREE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `d = orbit_size (face_map H) (node_map H (x0:num))` THEN
  SUBGOAL_THEN `0 < d /\
                ITER d (face_map H) (node_map H (x0:num)) = node_map H x0`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC ORBIT_SIZE_POS; MATCH_MP_TAC ITER_ORBIT_SIZE] THEN
    EXISTS_TAC `dart(H:(num)hypermap)` THEN
    ASM_SIMP_TAC[NODE_MAP_IN_DART; FINITE_DART; FACE_MAP_PERMUTES];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `d - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `d = SUC(d - 1)` SUBST_ALL_TAC THENL
   [ASM_ARITH_TAC; RULE_ASSUM_TAC(REWRITE_RULE[ITER]) THEN
    REWRITE_TAC[ITER; SUC_SUB1] THEN DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `ITER (d - 1) (face_map H) (node_map H x0) IN dart (H:(num)hypermap)`
  MP_TAC THENL
   [ASM_SIMP_TAC[ITER_PERMUTES_IN; FACE_MAP_PERMUTES; NODE_MAP_IN_DART];
    UNDISCH_TAC
     `face_map H (ITER (d - 1) (face_map H) (node_map H x0)) =
      node_map H (x0:num)` THEN
    SPEC_TAC(`ITER (d - 1) (face_map H) (node_map H (x0:num))`,`w:num`)] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ecpA_face] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  UNDISCH_TAC `~cface H (edge_map H x0) (node_map H (x0:num))` THEN
  ASM_REWRITE_TAC[] THEN CFACE_TAC[]);;

(* Main theorem: Gonthier ecpA_merge.                                        *)

let ECPA_MERGE = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H
     ==> cface (ecpA H x0) (face_map H (edge_map H x0)) (node_map H x0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ECPA_COMPONENTS) THEN
  ASM_CASES_TAC `cface (H:(num)hypermap) (edge_map H x0) (node_map H x0)` THENL
   [SUBGOAL_THEN
     `face (ecpA H x0) (face_map H (edge_map H x0)) =
      face H (face_map H (edge_map H (x0:num)))`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[face] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC ORBIT_MAP_EQ_AGREE THEN
      EXISTS_TAC `dart(H:(num)hypermap)` THEN
      ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; FACE_MAP_PERMUTES;
                   ecpA_face];
      ASM_REWRITE_TAC[cface] THEN REWRITE_TAC[GSYM cface] THEN CFACE_TAC[]];
    MATCH_MP_TAC CFACE_SYM_GEN THEN ASM_REWRITE_TAC[cface; face] THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_ITER_REACH) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[ITER_IN_ORBIT]]);;

let CFACE_ECPA_STEP = prove
 (`!(H:(num)hypermap) x0 z.
     x0 IN dart H /\ z IN dart H ==> cface (ecpA H x0) z (face_map H z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] ECPA_MERGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `face_map (ecpA H x0) z = ecpA_face H x0 z` MP_TAC THENL
   [ASM_SIMP_TAC[ECPA_COMPONENTS]; ALL_TAC] THEN
  REWRITE_TAC[ecpA_face] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  DISCH_TAC THEN CFACE_TAC[]);;

let SUB_CFACE_ICPA = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ x IN dart H /\ cface H x y ==> cface (ecpA H x0) x y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cface]) THEN
  REWRITE_TAC[face; ORBIT_MAP_ITER] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[ITER; CFACE_REFL] THEN
  MATCH_MP_TAC CFT_TRANS THEN EXISTS_TAC `ITER n (face_map H) (x:num)` THEN
  ASM_SIMP_TAC[CFACE_ECPA_STEP; ITER_PERMUTES_IN; FACE_MAP_PERMUTES]);;

let ECPA_EDGE_CFACE = prove
 (`!(H:(num)hypermap) x0 z y.
     z IN dart H /\ cface H (edge_map H z) y ==> cface H (ecpA_edge H x0 z) y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpA_edge] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN CFACE_TAC[]);;

let SUB_ADJ_ICPA = prove
 (`!(H:(num)hypermap) x0 x y.
     x0 IN dart H /\ x IN dart H /\ adj H x y ==> adj (ecpA H x0) x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `z:num` THEN
  SUBGOAL_THEN `(z:num) IN dart H` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_IN_DART; cface]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_CFACE_ICPA; ECPA_COMPONENTS] THEN
  MATCH_MP_TAC SUB_CFACE_ICPA THEN ASM_SIMP_TAC[ECPA_EDGE_CFACE] THEN
  REWRITE_TAC[ecpA_edge] THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_SIMP_TAC[EDGE_MAP_IN_DART; NODE_MAP_IN_DART]));;

(* ------------------------------------------------------------------------- *)
(* Restriction along every step: CPSTEP_RESTRICT_CUBIC above covers R, Rr,   *)
(* U, Y, H, K; the A step keeps the dart set and lifts cface and adj         *)
(* (SUB_CFACE_ICPA, SUB_ADJ_ICPA).  Hence cp_restrict holds for all programs *)
(* and a colouring of cpmap (APPEND cp1 cp2) restricts to cpmap cp2          *)
(* (GCOL_RESTRICT_GEN), with its cface consequence GCOL_CFACE_GEN used by    *)
(* the K and A step lemmas.                                                  *)
(* ------------------------------------------------------------------------- *)

let CPSTEP_RESTRICT_A = prove
 (`cpstep_restrict CpA`,
  REWRITE_TAC[cpstep_restrict; CPSTEP_APPLY_EXPAND; FST] THEN
  MAP_EVERY X_GEN_TAC [`G:(num)hypermap`; `x:num`; `k0:num->color`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `dart(ecpA G x) = dart(G:(num)hypermap)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ECPA_DART]; ALL_TAC] THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THEN X_GEN_TAC `u:num` THEN
  DISCH_TAC THENL
   [MP_TAC(ISPECL [`ecpA (G:(num)hypermap) x`; `k0:num->color`; `u:num`;
      `edge_map (G:(num)hypermap) u`] ADJ_COLORING) THEN
    ASM_REWRITE_TAC[EDGE_MAP_PERMUTES] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    MATCH_MP_TAC SUB_ADJ_ICPA THEN ASM_SIMP_TAC[ADJ_EDGE];
    MATCH_MP_TAC CFACE_COLORING THEN EXISTS_TAC `ecpA (G:(num)hypermap) x` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUB_CFACE_ICPA THEN
    ASM_REWRITE_TAC[CFACE_FACE_SUCC]]);;

let CPSTEP_RESTRICT_ANY = prove
 (`!s. cpstep_restrict s`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `s:cpstep` (cases "cpstep")) THEN
  REWRITE_TAC[CPSTEP_RESTRICT_CUBIC; CPSTEP_RESTRICT_A]);;

let CP_RESTRICT_ANY = prove
 (`!cp1 cp2. cp_restrict cp1 cp2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CP_RESTRICT_ALL THEN
  REWRITE_TAC[GSYM ALL_MEM; CPSTEP_RESTRICT_ANY]);;

let GCOL_RESTRICT_GEN = prove
 (`!cp1 cp2 k0. coloring (FST(cpmap(APPEND cp1 cp2))) k0
                ==> coloring (FST(cpmap cp2)) k0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`REVERSE(cp1:(cpstep)list)`; `cp2:(cpstep)list`]
    CP_RESTRICT_ANY) THEN
  REWRITE_TAC[cp_restrict; catrev_cp; REVERSE_REVERSE] THEN MESON_TAC[]);;

let GCOL_CFACE_GEN = prove
 (`!cp1 cp2 k0 x y.
      coloring (FST(cpmap(APPEND cp1 cp2))) k0 /\
      x IN dart(FST(cpmap cp2)) /\ cface (FST(cpmap cp2)) x y
      ==> k0 y = k0 x`,
  MESON_TAC[GCOL_RESTRICT_GEN; CFACE_COLORING]);;

(* ------------------------------------------------------------------------- *)
(* The extended colourings k' of Gonthier's step proofs all have the shape   *)
(* kext G' G2 k c: the colour of the old dart on u's face in G', or c when   *)
(* the face of u contains no old dart.  Generic facts about this shape.      *)
(* ------------------------------------------------------------------------- *)

let kext = new_definition
 `kext (G':(num)hypermap) (G2:(num)hypermap) (k:num->color) (c:color) u =
    if (?x. x IN dart G2 /\ cface G' u x)
    then k (@x. x IN dart G2 /\ cface G' u x)
    else c`;;

let KEXT_CFACE = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k c u z.
     coloring G2 k /\ dart G2 SUBSET dart G' /\
     (!x y. x IN dart G2 /\ y IN dart G2 /\ cface G' x y ==> cface G2 x y) /\
     z IN dart G2 /\ cface G' u z
     ==> kext G' G2 k c u = k z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kext] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `w = @x. x IN dart G2 /\ cface (G':(num)hypermap) u x` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `u IN dart (G':(num)hypermap)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CFACE_LEFT_IN_DART; SUBSET]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CFACE_COLORING THEN
  EXISTS_TAC `G2:(num)hypermap` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[CFACE_TRANS]);;

let KEXT_OLD = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k c z.
     coloring G2 k /\ dart G2 SUBSET dart G' /\
     (!x y. x IN dart G2 /\ y IN dart G2 /\ cface G' x y ==> cface G2 x y) /\
     z IN dart G2
     ==> kext G' G2 k c z = k z`,
  MESON_TAC[KEXT_CFACE; CFACE_REFL]);;

let KEXT_APEX = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k c u.
     ~(?x. x IN dart G2 /\ cface G' u x) ==> kext G' G2 k c u = c`,
  SIMP_TAC[kext]);;

let KEXT_FACE = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k c u.
     u IN dart G' ==> kext G' G2 k c (face_map G' u) = kext G' G2 k c u`,
  SIMP_TAC[kext; CFACE_LEFT_FACE]);;

(* k0G: a colouring k0 of G' agreeing with k on G2 and taking the value c on *)
(* the darts whose face has no old dart is kext G' G2 k c.                   *)

let K0_KEXT = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k k0 c u.
     coloring G' k0 /\ (!x. x IN dart G2 ==> k0 x = k x) /\ u IN dart G' /\
     (~(?x. x IN dart G2 /\ cface G' u x) ==> k0 u = c)
     ==> k0 u = kext G' G2 k c u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kext] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `w = @x. x IN dart G2 /\ cface (G':(num)hypermap) u x` THEN
  STRIP_TAC THEN
  ASM_MESON_TAC[CFACE_COLORING]);;

(* ------------------------------------------------------------------------- *)
(* The U step (Gonthier cpcolor1U_correct).  kuU G2 x2 k e colours the two   *)
(* new darts e +c k(node x2) (apex) and k(node x2) (its partner).            *)
(* ------------------------------------------------------------------------- *)

let kuU = new_definition
 `kuU (G2:(num)hypermap) x2 (k:num->color) e u =
    if (?x. x IN dart G2 /\ cface (ecpU G2 x2) u x)
    then k (@x. x IN dart G2 /\ cface (ecpU G2 x2) u x)
    else addc e (k (node_map G2 x2))`;;

let KUU_KEXT = prove
 (`!(G2:(num)hypermap) x2 k e.
     kuU G2 x2 k e = kext (ecpU G2 x2) G2 k (addc e (k (node_map G2 x2)))`,
  REWRITE_TAC[FUN_EQ_THM; kuU; kext]);;

let KUU_OLD = prove
 (`!(G2:(num)hypermap) x2 k e z.
     coloring G2 k /\ x2 IN dart G2 /\ z IN dart G2 ==> kuU G2 x2 k e z = k z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUU_KEXT] THEN MATCH_MP_TAC KEXT_OLD THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPU] THEN ASM_MESON_TAC[CFACE_ECPU_PROJ]);;

let KUU_APEX = prove
 (`!(G2:(num)hypermap) x2 k e.
     x2 IN dart G2 ==>
     kuU G2 x2 k e (ecpU_pt G2) = addc e (k (node_map G2 x2))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUU_KEXT] THEN MATCH_MP_TAC KEXT_APEX THEN
  ASM_MESON_TAC[CFACE_ECPU_APEX; ECPU_PT_NOT_IN_DART; FINITE_DART]);;

let KUU_B = prove
 (`!(G2:(num)hypermap) x2 k e.
     coloring G2 k /\ x2 IN dart G2
     ==> kuU G2 x2 k e (SND(new_dart2(dart G2))) = k (node_map G2 x2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUU_KEXT] THEN MATCH_MP_TAC KEXT_CFACE THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPU; CFACE_ECPU_B_NODE; FINITE_DART;
               NODE_FACE_IN_DART] THEN
  ASM_MESON_TAC[CFACE_ECPU_PROJ]);;

let ADDC_ABSORB = prove
 (`!e c. addc e c = c <=> e = Color0`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF; distinctness "color"]);;

let ADDC_MID_CANCEL_EQ = prove
 (`!a b c. addc a b = addc b c <=> a = c`,
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF; distinctness "color"]);;

let KUU_COLORING = prove
 (`!(G2:(num)hypermap) x2 k e.
     coloring G2 k /\ x2 IN dart G2 /\ ~(e = Color0)
     ==> coloring (ecpU G2 x2) (kuU G2 x2 k e)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[coloring] THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[KUU_KEXT; KEXT_FACE]] THEN
  X_GEN_TAC `u:num` THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] ECPU_COMPONENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] ECP_EDGE_FRESH) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `e:color`]
    KUU_APEX) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `e:color`]
    KUU_B) THEN
  ASM_REWRITE_TAC[IN_INSERT; ecpU_pt] THEN
  DISCH_TAC THEN DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[KUU_OLD; EDGE_IN_DART] THEN
  ASM_MESON_TAC[ADDC_ABSORB; coloring]);;

let FTRACE_CONS_ABSORB = prove
 (`!a e (M:color list).
     ftrace (CONS a (CONS (addc e a) (CONS a M))) =
     CONS e (CONS e (ftrace (CONS a M)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FTRACE_CONS2] THEN
  REWRITE_TAC[FTRACE_CONS1; APPEND; ptrace; CONS_11] THEN
  SPEC_TAC(`a:color`,`a:color`) THEN SPEC_TAC(`e:color`,`e:color`) THEN
  COLOR_CASES_TAC THEN REWRITE_TAC[addc_DEF]);;

let KUU_MAP_CPRING_ECPU = prove
 (`!(G2:(num)hypermap) x2 k e.
     coloring G2 k /\ x2 IN dart G2
     ==> MAP (kuU G2 x2 k e) (cpring (ecpU G2 x2) (ecpU_pt G2)) =
         CONS (k (node_map G2 x2))
              (CONS (addc e (k(node_map G2 x2))) (MAP k (cpring G2 x2)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < orbit_size (node_map G2) (x2:num)` ASSUME_TAC THENL
   [ASM_MESON_TAC[COLORING_PROPER_CPRING; ARITH_RULE `2 <= n ==> 1 < n`];
    ASM_SIMP_TAC[CPRING_ECPU; MAP; KUU_B; KUU_APEX; CONS_11]] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[KUU_OLD; MEM_CPRING_IN_DART]);;

let DK_PRIME_U = prove
 (`!(G2:(num)hypermap) x2 k e.
     coloring G2 k /\ x2 IN dart G2
     ==> ftrace (MAP (kuU G2 x2 k e) (cpring (ecpU G2 x2) (ecpU_pt G2))) =
         CONS e (CONS e (ftrace (MAP k (cpring G2 x2))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[KUU_MAP_CPRING_ECPU] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] CPRING_CONS_HEAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[MAP; FTRACE_CONS_ABSORB]);;

let CPCOLOR1_U = prove
 (`!f et. cpcolor1 CpU f et =
          ctree_union (f (CONS Color1 (CONS Color1 et)))
            (ctree_union (f (CONS Color2 (CONS Color2 et)))
                         (f (CONS Color3 (CONS Color3 et))))`,
  REWRITE_TAC[cpcolor1]);;

let CP_TR0_CONS_U = prove
 (`!et0 cp1 cp2 k0. cp_tr0 et0 (CONS CpU cp1) cp2 k0 <=>
 cp_tr0 et0 cp1 (CONS CpU cp2) k0`,
  REWRITE_TAC[cp_tr0; CATREV_CP_CONS]);;

(* k0G and e0 <> 0 (Gonthier cfcolor.v:304-315), for any colouring k0 of the *)
(* U-stepped map.                                                            *)

let K0G_U_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0 u.
     coloring G2 k /\ x2 IN dart G2 /\ coloring (ecpU G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x) /\ u IN dart(ecpU G2 x2)
     ==> k0 u = kuU G2 x2 k (addc (k0 (ecpU_pt G2)) (k (node_map G2 x2))) u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUU_KEXT] THEN MATCH_MP_TAC K0_KEXT THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u = ecpU_pt (G2:(num)hypermap)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `u:num`] FBAND_ICPU) THEN
    ASM_REWRITE_TAC[HYPERMAP_LEMMA] THEN
    ASM_MESON_TAC[CFACE_ECPU_APEX; CFACE_SYM_GEN];
    REWRITE_TAC[GSYM ADDC_ASSOC; ADDCC; ADDC_0]]);;

let E0_NONZERO_U_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0.
     coloring G2 k /\ x2 IN dart G2 /\ coloring (ecpU G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x)
     ==> ~(addc (k0 (ecpU_pt G2)) (k (node_map G2 x2)) = Color0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `node_map G2 (x2:num) IN dart G2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[NODE_FACE_IN_DART]; ALL_TAC] THEN
  UNDISCH_TAC `addc (k0 (ecpU_pt G2)) (k (node_map G2 x2)) = Color0` THEN
  REWRITE_TAC[ADDC_EQ_0] THEN
  SUBGOAL_THEN `(k:num->color) (node_map G2 x2) = k0 (node_map G2 x2)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC ADJ_COLORING THEN EXISTS_TAC `ecpU (G2:(num)hypermap) x2` THEN
  ASM_SIMP_TAC[EDGE_MAP_PERMUTES; ECPU_PT_IN_DART; ADJ_ECPU_APEX;
               CFACE_ECPU_B_NODE;
               FINITE_DART]);;

let COLOR_NONZERO_CASES = prove
 (`!c. ~(c = Color0) ==> c = Color1 \/ c = Color2 \/ c = Color3`,
  COLOR_CASES_TAC THEN REWRITE_TAC[distinctness "color"]);;

(* The 3-way membership reflection of the U step, for any predicate Q on the *)
(* extended colourings that forces a colouring of the U-stepped map.         *)

let CPCOLOR1U_MEM_GEN = prove
 (`!(G2:(num)hypermap) x2 k (Q:(num->color)->bool).
     coloring G2 k /\ x2 IN dart G2 /\ (!k0. Q k0 ==> coloring (ecpU G2 x2) k0)
     ==>
 ((?k0. Q k0 /\ (!x. x IN dart(ecpU G2 x2) ==> k0 x = kuU G2 x2 k Color1 x)) \/
          (?k0. Q k0 /\
          (!x. x IN dart(ecpU G2 x2) ==> k0 x = kuU G2 x2 k Color2 x)) \/
          (?k0. Q k0 /\
          (!x. x IN dart(ecpU G2 x2) ==> k0 x = kuU G2 x2 k Color3 x)) <=>
          (?k0. Q k0 /\ (!x. x IN dart G2 ==> k0 x = k x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `k0:num->color` THEN
    ASM_MESON_TAC[DART_H_SUBSET_ECPU; KUU_OLD];
    DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `coloring (ecpU (G2:(num)hypermap) x2) k0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `e0 =
    addc (k0 (ecpU_pt G2)) (k (node_map (G2:(num)hypermap) x2))` THEN
    SUBGOAL_THEN `~(e0 = Color0) /\
                  !u. u IN dart(ecpU (G2:(num)hypermap) x2) ==>
                  k0 u = kuU G2 x2 k e0 u`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e0" THEN ASM_MESON_TAC[E0_NONZERO_U_GEN; K0G_U_GEN];
      ALL_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC
      (DISJ_CASES_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC) o MATCH_MP
        COLOR_NONZERO_CASES) THEN
    ASM_MESON_TAC[]]);;

let CPCOLOR1U_CORRECT = prove
 (`!et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS CpU cp2))) k'
           ==> cp_extcol et0 cp1 (CONS CpU cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS CpU cp1) cp2 (cpcolor1 CpU f) k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "ih" o REWRITE_RULE[CPMAP_CONS_U; FST]) ASSUME_TAC) THEN
  ABBREV_TAC `G2 = FST(cpmap cp2)` THEN ABBREV_TAC `x2 = SND(cpmap cp2)` THEN
  SUBGOAL_THEN
    `(x2:num) IN dart (G2:(num)hypermap) /\ 1 < orbit_size (node_map G2) x2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CPMAP_PT_IN_DART; COLORING_PROPER_CPRING;
                  ARITH_RULE `2 <= n <=> 1 < n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST(cpmap(CONS CpU cp2)) = ecpU (G2:(num)hypermap) x2 /\
                SND(cpmap(CONS CpU cp2)) = ecpU_pt G2`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[CPMAP_CONS_U; FST; SND]; ALL_TAC] THEN
  ABBREV_TAC `et =
  ftrace (MAP (k:num->color) (cpring (G2:(num)hypermap) x2))` THEN
  ABBREV_TAC `h = cprsize (catrev_cp cp1 (CONS CpU cp2)) - 2` THEN
  SUBGOAL_THEN
   `!e. ~(e = Color0)
        ==> ctree_proper h (f (CONS e (CONS e et))) /\
            (ctree_mem (f (CONS e (CONS e et))) (ttail et0) <=>
             ?k0. (coloring (FST(cpmap(catrev_cp cp1 (CONS CpU cp2)))) k0 /\
                   cp_tr0 et0 cp1 (CONS CpU cp2) k0) /\
                  (!x. x IN dart(ecpU (G2:(num)hypermap) x2) ==>
                  k0 x = kuU G2 x2 k e x))`
  (fun th -> MP_TAC(SPEC `Color1` th) THEN MP_TAC(SPEC `Color2` th) THEN
             MP_TAC(SPEC `Color3` th)) THENL
   [X_GEN_TAC `e:color` THEN DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPEC `kuU (G2:(num)hypermap) x2 k e`) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[KUU_COLORING];
      REWRITE_TAC[cp_extcol] THEN
      ASM_SIMP_TAC[DK_PRIME_U]];
    ALL_TAC] THEN
  REWRITE_TAC[distinctness "color"] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_CONS; CP_TR0_CONS_U] THEN
  ASM_REWRITE_TAC[CPCOLOR1_U] THEN
  SUBGOAL_THEN `ctree_proper h (ctree_union (f (CONS Color2 (CONS Color2 et)))
                                            (f (CONS Color3
                                                (CONS Color3 et))))`
  ASSUME_TAC THENL
  [MATCH_MP_TAC CTREE_UNION_PROPER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CTREE_UNION_PROPER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `f (CONS Color2 (CONS Color2 et)):ctree`;
                 `f (CONS Color3 (CONS Color3 et)):ctree`; `ttail et0`
                 ] CTREE_MEM_UNION) THEN
  MP_TAC(ISPECL [`h:num`; `f (CONS Color1 (CONS Color1 et)):ctree`;
                 `ctree_union (f (CONS Color2 (CONS Color2 et)))
                  (f (CONS Color3 (CONS Color3 et)))`;
                 `ttail et0`] CTREE_MEM_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`;
                 `\k0:num->color. coloring
                  (FST(cpmap(catrev_cp cp1 (CONS CpU cp2)))) k0 /\
                                  cp_tr0 et0 cp1 (CONS CpU cp2) k0`
                                  ] CPCOLOR1U_MEM_GEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[cp_restrict; CP_RESTRICT_ANY]);;

(* ------------------------------------------------------------------------- *)
(* The Y step (Gonthier handles it through cpexpand; here directly).  With   *)
(* a = k(node x2), b = k x2 and e1 = a +c b the junction colour is           *)
(* a +c p(e1) for p in {Eperm231, Eperm312}; kuY G2 x2 k p colours the two   *)
(* new apex darts with it.                                                   *)
(* ------------------------------------------------------------------------- *)

let kuY = new_definition
 `kuY (G2:(num)hypermap) x2 (k:num->color) (p:edge_perm) u =
    if (?x. x IN dart G2 /\ cface (ecpY G2 x2) u x)
    then k (@x. x IN dart G2 /\ cface (ecpY G2 x2) u x)
    else addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2)))`
    ;;

let KUY_KEXT = prove
 (`!(G2:(num)hypermap) x2 k p.
     kuY G2 x2 k p =
     kext (ecpY G2 x2) G2 k
     (addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2))))`,
  REWRITE_TAC[FUN_EQ_THM; kuY; kext]);;

let KUY_OLD = prove
 (`!(G2:(num)hypermap) x2 k p z.
     coloring G2 k /\ x2 IN dart G2 /\ z IN dart G2 ==> kuY G2 x2 k p z = k z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT] THEN MATCH_MP_TAC KEXT_OLD THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPY] THEN ASM_MESON_TAC[CFACE_ECPY_PROJ]);;

let KUY_APEX = prove
 (`!(G2:(num)hypermap) x2 k p.
     x2 IN dart G2
     ==> kuY G2 x2 k p (ecpY_pt G2 x2) =
         addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT] THEN MATCH_MP_TAC KEXT_APEX THEN
  ASM_MESON_TAC[CFACE_ECPY_APEX_OLD; HYPERMAP_LEMMA]);;

let KUY_HEAD = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2
     ==> kuY G2 x2 k p (SND(new_dart2(dart G2))) = k (node_map G2 x2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT] THEN MATCH_MP_TAC KEXT_CFACE THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPY; CFACE_NODE_ECPY; FINITE_DART;
               NODE_FACE_IN_DART;
               EDGE_MAP_PERMUTES; NODE_MAP_PERMUTES; FACE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[CFACE_ECPY_PROJ]);;

let KUY_B = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2
     ==> kuY G2 x2 k p (SND(new_dart2(dart(ecpU G2 x2)))) = k x2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT] THEN MATCH_MP_TAC KEXT_CFACE THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPY; CFACE_ECPY_B_PT; HYPERMAP_LEMMA] THEN
  ASM_MESON_TAC[CFACE_ECPY_PROJ]);;

let KUY_ECPU_PT = prove
 (`!(G2:(num)hypermap) x2 k p.
     x2 IN dart G2
     ==> kuY G2 x2 k p (ecpU_pt G2) =
         addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`ecpY (G2:(num)hypermap) x2`; `G2:(num)hypermap`; `k:num->color`;
                 `addc (k(node_map G2 x2))
                  (permc p (addc (k(node_map G2 x2)) (k (x2:num))))`;
                 `ecpU_pt (G2:(num)hypermap)`] KEXT_FACE) THEN
  ASM_SIMP_TAC[ECPU_PT_IN_DART_ECPY; ECPY_APEX_TWO_CYCLE; GSYM KUY_KEXT;
               KUY_APEX]);;

let KUY_MAP_CPRING_ECPY = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2
     ==> MAP (kuY G2 x2 k p) (cpring (ecpY G2 x2) (ecpY_pt G2 x2)) =
         CONS (k (node_map G2 x2))
              (CONS (addc (k(node_map G2 x2)) (permc p
                                            (addc (k(node_map G2 x2)) (k x2))))
                    (MAP k (TL(cpring G2 x2))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CPRING_ECPY; MAP; KUY_HEAD; KUY_APEX; CONS_11] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  ASM_MESON_TAC[KUY_OLD; MEM_CPRING_IN_DART; MEM_TL_IMP; CPRING_NONEMPTY]);;

(* Klein-four facts about the junction colour.                               *)

let JUNCTION_ALG = prove
 (`!p a b. p = Eperm231 \/ p = Eperm312
           ==> addc a (addc a (permc p (addc a b))) = permc p (addc a b) /\
               addc (addc a (permc p (addc a b))) b =
               permc (inv_eperm p) (addc a b) /\
               (~(a = b) ==> ~(addc a (permc p (addc a b)) = a) /\
                             ~(a = addc a (permc p (addc a b))) /\
                             ~(addc a (permc p (addc a b)) = b) /\
                             ~(b = addc a (permc p (addc a b))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[inv_eperm; distinctness "edge_perm"] THEN
  SPEC_TAC(`a:color`,`a:color`) THEN SPEC_TAC(`b:color`,`b:color`) THEN
  COLOR_CASES_TAC THEN
  REWRITE_TAC[addc_DEF; permc_DEF; distinctness "color"]);;

let DK_PRIME_Y = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     (p = Eperm231 \/ p = Eperm312)
     ==> ftrace (MAP (kuY G2 x2 k p) (cpring (ecpY G2 x2) (ecpY_pt G2 x2))) =
         CONS (permc p (addc (k(node_map G2 x2)) (k x2)))
              (CONS (permc (inv_eperm p) (addc (k(node_map G2 x2)) (k x2)))
                    (TL(ftrace (MAP k (cpring G2 x2)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[KUY_MAP_CPRING_ECPY] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[MAP; TL; FTRACE_CONS2; APPEND; ptrace; CONS_11] THEN
  ASM_SIMP_TAC[JUNCTION_ALG]);;

let KUY_COLORING = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     (p = Eperm231 \/ p = Eperm312)
     ==> coloring (ecpY G2 x2) (kuY G2 x2 k p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `~((k:num->color)(node_map G2 x2) = k x2) /\
                !u. u IN dart G2 ==> ~(k (edge_map G2 u) = k u)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[COLORING_NODE; coloring]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`p:edge_perm`; `(k:num->color)(node_map G2 x2)`; `(k:num->color) x2`]
                JUNCTION_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[KUY_KEXT; KEXT_FACE]] THEN
  X_GEN_TAC `u:num` THEN
  ASM_SIMP_TAC[IN_DART_ECPY] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `p:edge_perm`]
    KUY_APEX) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `p:edge_perm`]
    KUY_B) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `p:edge_perm`]
    KUY_HEAD) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `p:edge_perm`]
    KUY_ECPU_PT) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] EDGE_ECPY_APEX) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] EDGE_ECPY_B) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] ECP_EDGE_FRESH) THEN
  ASM_REWRITE_TAC[ecpY_pt; ecpN_pt; ecpU_pt; FINITE_DART] THEN
  REPLICATE_TAC 7 STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_ECPY_ECPU; ECP_NEW_IN_DART; EDGE_ECPY_OLD; KUY_OLD;
               EDGE_IN_DART; FINITE_DART]);;

(* k0G for Y: a colouring k0 of the Y-stepped map agreeing with k on G2 and  *)
(* taking the junction colour of p at the apex is kuY G2 x2 k p.             *)

let K0G_Y_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0 p u.
     coloring G2 k /\ x2 IN dart G2 /\ coloring (ecpY G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x) /\
     k0 (ecpY_pt G2 x2) =
     addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2))) /\
     u IN dart(ecpY G2 x2)
     ==> k0 u = kuY G2 x2 k p u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT] THEN MATCH_MP_TAC K0_KEXT THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `u:num`] FBAND_ICPY) THEN
  ASM_REWRITE_TAC[HYPERMAP_LEMMA] THEN
  ASM_MESON_TAC[CFACE_COLORING]);;

let EXISTS_JUNCTION_PERM = prove
 (`!a b c:color. ~(a = b) /\ ~(c = a) /\ ~(c = b)
           ==> ?p. (p = Eperm231 \/ p = Eperm312) /\
                   c = addc a (permc p (addc a b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `if addc a (permc Eperm231 (addc a b)) = c then Eperm231
  else Eperm312` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`~(a:color = b)`; `~(c:color = a)`; `~(c:color = b)`
  ] THEN
  SPEC_TAC(`a:color`,`a:color`) THEN SPEC_TAC(`b:color`,`b:color`) THEN
  SPEC_TAC(`c:color`,`c:color`) THEN
  COLOR_CASES_TAC THEN
  REWRITE_TAC[addc_DEF; permc_DEF; distinctness "color"]);;

let JUNCTION_P_EXISTS_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     coloring (ecpY G2 x2) k0 /\ (!x. x IN dart G2 ==> k0 x = k x)
     ==> ?p. (p = Eperm231 \/ p = Eperm312) /\
             k0 (ecpY_pt G2 x2) =
             addc (k(node_map G2 x2))
             (permc p (addc (k(node_map G2 x2)) (k x2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXISTS_JUNCTION_PERM THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] ECPY_APEX_TWO_CYCLE) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] CFACE_NODE_ECPY) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] CFACE_ECPY_B_PT) THEN
  ASM_REWRITE_TAC[HYPERMAP_LEMMA] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(k0:num->color) (ecpU_pt G2) = k0 (ecpY_pt G2 x2) /\
    k (node_map G2 x2) = k0 (SND(new_dart2(dart G2))) /\
    k x2 = k0 (SND(new_dart2(dart(ecpU G2 x2))))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CFACE_COLORING; CFACE_FACE_SUCC; ECPY_PT_IN_DART;
                  HEAD_IN_DART_ECPY; BPRIME_IN_DART_ECPY; NODE_MAP_IN_DART];
    ASM_REWRITE_TAC[]] THEN
  ASM_MESON_TAC[ADJ_COLORING; EDGE_MAP_PERMUTES; ECPU_PT_IN_DART_ECPY;
                ADJ_ECPY_ECPUPT_HEAD; ECPY_PT_IN_DART; ADJ_ECPY_APEX_B;
                COLORING_NODE]);;

let CP_TR0_CONS_Y = prove
 (`!et0 cp1 cp2 k0. cp_tr0 et0 (CONS CpY cp1) cp2 k0 <=>
 cp_tr0 et0 cp1 (CONS CpY cp2) k0`,
  REWRITE_TAC[cp_tr0; CATREV_CP_CONS]);;

let CPCOLOR1_Y = prove
 (`!f e1 et'. cpcolor1 CpY f (CONS e1 et') =
              ctree_union (f (CONS (permc Eperm231 e1)
                              (CONS (permc Eperm312 e1) et')))
                          (f (CONS (permc Eperm312 e1)
                              (CONS (permc Eperm231 e1) et')))`,
  REWRITE_TAC[cpcolor1; NOT_CONS_NIL; HD; TL]);;

let CPCOLOR1Y_MEM_GEN = prove
 (`!(G2:(num)hypermap) x2 k (Q:(num->color)->bool).
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     (!k0. Q k0 ==> coloring (ecpY G2 x2) k0)
     ==>
 ((?k0. Q k0 /\ (!x. x IN dart(ecpY G2 x2) ==> k0 x = kuY G2 x2 k Eperm231 x))
 \/
          (?k0. Q k0 /\
          (!x. x IN dart(ecpY G2 x2) ==> k0 x = kuY G2 x2 k Eperm312 x)) <=>
          (?k0. Q k0 /\ (!x. x IN dart G2 ==> k0 x = k x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `k0:num->color` THEN
    ASM_MESON_TAC[DART_H_SUBSET_ECPY; KUY_OLD];
    DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `coloring (ecpY (G2:(num)hypermap) x2) k0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
      [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `k0:num->color`]
                  JUNCTION_P_EXISTS_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:edge_perm` (fun th ->
      ASSUME_TAC(CONJUNCT2 th) THEN
      DISJ_CASES_THEN SUBST_ALL_TAC (CONJUNCT1 th))) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `k0:num->color` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC K0G_Y_GEN THEN ASM_REWRITE_TAC[]]);;

let CPCOLOR1Y_CORRECT = prove
 (`!et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS CpY cp2))) k'
           ==> cp_extcol et0 cp1 (CONS CpY cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS CpY cp1) cp2 (cpcolor1 CpY f) k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "ih" o REWRITE_RULE[CPMAP_CONS_Y; FST]) ASSUME_TAC) THEN
  ABBREV_TAC `G2 = FST(cpmap cp2)` THEN ABBREV_TAC `x2 = SND(cpmap cp2)` THEN
  SUBGOAL_THEN `(x2:num) IN dart (G2:(num)hypermap) /\ proper_cpring G2 x2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CPMAP_PT_IN_DART; COLORING_NODE; proper_cpring];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST(cpmap(CONS CpY cp2)) = ecpY (G2:(num)hypermap) x2 /\
                SND(cpmap(CONS CpY cp2)) = ecpY_pt G2 x2`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[CPMAP_CONS_Y; FST; SND]; ALL_TAC] THEN
  ABBREV_TAC `et =
  ftrace (MAP (k:num->color) (cpring (G2:(num)hypermap) x2))` THEN
  ABBREV_TAC `h = cprsize (catrev_cp cp1 (CONS CpY cp2)) - 2` THEN
  ABBREV_TAC `e1 = addc ((k:num->color)(node_map G2 x2)) (k x2)` THEN
  SUBGOAL_THEN `~(et:color list = []) /\ HD et = e1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["et"; "e1"] THEN
    ASM_SIMP_TAC[HEAD_FTRACE_MAP_CPRING; GSYM LENGTH_EQ_NIL; LENGTH_FTRACE;
                 LENGTH_MAP] THEN
    ASM_MESON_TAC[SIZE_CPRING; COLORING_PROPER_CPRING;
                  ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. (p = Eperm231 \/ p = Eperm312)
        ==> ctree_proper h
        (f (CONS (permc p e1) (CONS (permc (inv_eperm p) e1) (TL et)))) /\
            (ctree_mem (f (CONS (permc p e1) (CONS (permc (inv_eperm p)
                                                    e1) (TL et))))
                       (ttail et0) <=>
             ?k0. (coloring (FST(cpmap(catrev_cp cp1 (CONS CpY cp2)))) k0 /\
                   cp_tr0 et0 cp1 (CONS CpY cp2) k0) /\
                  (!x. x IN dart(ecpY (G2:(num)hypermap) x2) ==>
                  k0 x = kuY G2 x2 k p x))`
  (fun th -> MP_TAC(SPEC `Eperm231` th) THEN MP_TAC(SPEC `Eperm312` th)) THENL
   [X_GEN_TAC `p:edge_perm` THEN DISCH_TAC THEN
    USE_THEN "ih" (MP_TAC o SPEC `kuY (G2:(num)hypermap) x2 k p`) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[KUY_COLORING];
      REWRITE_TAC[cp_extcol] THEN ASM_SIMP_TAC[DK_PRIME_Y]];
    ALL_TAC] THEN
  REWRITE_TAC[inv_eperm; distinctness "edge_perm"] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_CONS; CP_TR0_CONS_Y] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `cpcolor1 CpY f et =
                ctree_union (f (CONS (permc Eperm231 e1)
                                (CONS (permc Eperm312 e1) (TL et))))
                            (f (CONS (permc Eperm312 e1)
                                (CONS (permc Eperm231 e1) (TL et))))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `et:color list = CONS (HD et) (TL et)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_MESON_TAC[CONS_HD_TL]; ASM_REWRITE_TAC[CPCOLOR1_Y]];
    ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CTREE_UNION_PROPER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
 [`h:num`;
  `f (CONS (permc Eperm231 e1) (CONS (permc Eperm312 e1) (TL et))):ctree`;
                 `f (CONS (permc Eperm312 e1) (CONS (permc Eperm231 e1)
                                               (TL et))):ctree`;
                 `ttail et0`] CTREE_MEM_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`;
                 `\k0:num->color. coloring
                  (FST(cpmap(catrev_cp cp1 (CONS CpY cp2)))) k0 /\
                                  cp_tr0 et0 cp1 (CONS CpY cp2) k0`
                                  ] CPCOLOR1Y_MEM_GEN) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[cp_restrict; CP_RESTRICT_ANY]);;

(* ------------------------------------------------------------------------- *)
(* The H step: ecpH G x = ecpN (ecpY G x) (ecpY_pt G x).  With a = k(node    *)
(* x2), b = k x2 and c = k(face(edge x2)) (the third ring colour) the ring   *)
(* trace starts a+b, b+c.  Doubled branch (a+b = b+c, i.e. a = c): kuH p     *)
(* with the junction colour a +c p(a+b), p in {231,312}.  Swap branch: the   *)
(* unique p with p(a+b) = b+c.                                               *)
(* ------------------------------------------------------------------------- *)

let kuH = new_definition
 `kuH (G2:(num)hypermap) x2 (k:num->color) (p:edge_perm) u =
    if (?x. x IN dart G2 /\ cface (ecpH G2 x2) u x)
    then k (@x. x IN dart G2 /\ cface (ecpH G2 x2) u x)
    else addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2)))`
    ;;

let KUH_KEXT = prove
 (`!(G2:(num)hypermap) x2 k p.
     kuH G2 x2 k p =
     kext (ecpH G2 x2) G2 k
     (addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2))))`,
  REWRITE_TAC[FUN_EQ_THM; kuH; kext]);;

let KUH_OLD = prove
 (`!(G2:(num)hypermap) x2 k p z.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\ z IN dart G2
     ==> kuH G2 x2 k p z = k z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUH_KEXT] THEN MATCH_MP_TAC KEXT_OLD THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPH] THEN ASM_MESON_TAC[CFACE_ECPH_PROJ]);;

let KUH_CFACE = prove
 (`!(G2:(num)hypermap) x2 k p u z.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     z IN dart G2 /\ cface (ecpH G2 x2) u z
     ==> kuH G2 x2 k p u = k z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUH_KEXT] THEN MATCH_MP_TAC KEXT_CFACE THEN
  ASM_SIMP_TAC[DART_SUBSET_ECPH] THEN ASM_MESON_TAC[CFACE_ECPH_PROJ]);;

let KUH_APEX = prove
 (`!(G2:(num)hypermap) x2 k p.
     x2 IN dart G2 /\ proper_cpring G2 x2
     ==> kuH G2 x2 k p (ecpH_pt G2 x2) =
         addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUH_KEXT] THEN MATCH_MP_TAC KEXT_APEX THEN
  ASM_MESON_TAC[CFACE_ECPH_APEX_OLD; HYPERMAP_LEMMA]);;

let KUH_VALUES = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2
     ==> kuH G2 x2 k p (node_map (ecpY G2 x2) (ecpY_pt G2 x2)) =
     k (node_map G2 x2) /\
         kuH G2 x2 k p (SND(new_dart2(dart G2))) = k (node_map G2 x2) /\
         kuH G2 x2 k p (SND(new_dart2(dart(ecpY G2 x2)))) =
         k (face_map G2 (edge_map G2 x2)) /\
         kuH G2 x2 k p (SND(new_dart2(dart(ecpU G2 x2)))) = k x2 /\
         kuH G2 x2 k p (ecpY_pt G2 x2) =
         addc (k(node_map G2 x2))
         (permc p (addc (k(node_map G2 x2)) (k x2))) /\
         kuH G2 x2 k p (ecpU_pt G2) =
         addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] NODE_ECPY_PT_VALUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `cface (ecpH G2 x2) (SND(new_dart2(dart(ecpU G2 x2)))) (x2:num)`
  ASSUME_TAC THENL
   [REWRITE_TAC[ecpH] THEN MATCH_MP_TAC CFACE_ECPN_LIFT THEN
    ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; HYPERMAP_LEMMA;
                 BPRIME_IN_DART_ECPY; CFACE_ECPY_B_PT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC KUH_CFACE THEN
      ASM_SIMP_TAC[NODE_FACE_IN_DART; EDGE_IN_DART] THEN
      ASM_MESON_TAC[CFACE_NODE_ECPH; CFACE_ECPH_B_PT;
                    HYPERMAP_LEMMA] THEN NO_TAC) THEN
  REWRITE_TAC[KUH_KEXT] THENL
   [MP_TAC(ISPECL
     [`ecpH (G2:(num)hypermap) x2`; `G2:(num)hypermap`; `k:num->color`;
       `addc (k(node_map G2 x2))
        (permc p (addc (k(node_map G2 x2)) (k (x2:num))))`;
       `ecpH_pt (G2:(num)hypermap) x2`] KEXT_FACE) THEN
    ASM_SIMP_TAC[ECPH_PT_IN_DART; FACE_ECPH_PT; GSYM KUH_KEXT; KUH_APEX];
    MP_TAC(ISPECL
      [`ecpH (G2:(num)hypermap) x2`; `G2:(num)hypermap`; `k:num->color`;
       `addc (k(node_map G2 x2))
        (permc p (addc (k(node_map G2 x2)) (k (x2:num))))`;
       `ecpU_pt (G2:(num)hypermap)`] KEXT_FACE) THEN
    ASM_SIMP_TAC[ECPU_PT_IN_DART_ECPY; DART_ECPY_SUBSET_ECPH;
                 FACE_ECPH_ECPU_PT; HYPERMAP_LEMMA; GSYM KUH_KEXT;
                 KUH_APEX]]);;

let KUH_MAP_CPRING_ECPH = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2
     ==> MAP (kuH G2 x2 k p) (cpring (ecpH G2 x2) (ecpH_pt G2 x2)) =
         CONS (k (node_map G2 x2))
              (CONS (addc (k(node_map G2 x2)) (permc p
                                            (addc (k(node_map G2 x2)) (k x2))))
                    (MAP k (TL(TL(cpring G2 x2)))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CPRING_ECPH; MAP; KUH_VALUES; KUH_APEX; CONS_11] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `z:num` THEN DISCH_TAC THEN MATCH_MP_TAC KUH_OLD THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x2:num` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[MEM]);;

let DK_PRIME_H = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2
     ==> ftrace (MAP (kuH G2 x2 k p) (cpring (ecpH G2 x2) (ecpH_pt G2 x2))) =
         CONS (permc p (addc (k(node_map G2 x2)) (k x2)))
              (CONS (addc (addc (k(node_map G2 x2))
                                (permc p (addc (k(node_map G2 x2)) (k x2))))
                          (k(face_map G2 (edge_map G2 x2))))
                    (TL(TL(ftrace (MAP k (cpring G2 x2))))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[KUH_MAP_CPRING_ECPH] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    CPRING_THIRD_COLOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `R = TL(TL(cpring (G2:(num)hypermap) x2))` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MAP; TL] THEN
  GEN_REWRITE_TAC LAND_CONV [ISPECL [`(k:num->color)(node_map G2 x2)`;
    `addc ((k:num->color)(node_map G2 x2))
     (permc p (addc (k(node_map G2 x2)) (k x2)))`;
    `(k:num->color) x2`; `MAP (k:num->color) R`] FTRACE_CONS2_TL] THEN
  REWRITE_TAC[CONS_11; ADDC_CANCEL]);;

(* Klein-four facts for the swap branch.                                     *)

let COLORING_X2_FACE_EDGE = prove
 (`!(G2:(num)hypermap) x2 (k:num->color).
     coloring G2 k /\ x2 IN dart G2
     ==> ~(k x2 = k (face_map G2 (edge_map G2 x2)))`,
  REWRITE_TAC[coloring] THEN MESON_TAC[EDGE_MAP_IN_DART]);;

let SWAP_PERM_EXISTS = prove
 (`!e1 e2:color. ~(e1 = Color0) /\ ~(e2 = Color0) /\ ~(e1 = e2)
    ==> (?p. (p = Eperm231 \/ p = Eperm312) /\ permc p e1 = e2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `if permc Eperm231 e1 = e2 then Eperm231 else Eperm312` THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  MAP_EVERY UNDISCH_TAC
    [`~(e1:color = Color0)`; `~(e2:color = Color0)`; `~(e1:color = e2)`] THEN
  SPEC_TAC(`e1:color`,`e1:color`) THEN SPEC_TAC(`e2:color`,`e2:color`) THEN
  COLOR_CASES_TAC THEN REWRITE_TAC[permc_DEF; distinctness "color"]);;

let SWAP_JUNCTION_VALID = prove
 (`!a b c. ~(a = b) /\ ~(a = c) /\ ~(b = c)
    ==> ~(addc a (addc b c) = c) /\
        (addc a (addc b c) = addc a (permc Eperm231 (addc a b)) \/
         addc a (addc b c) = addc a (permc Eperm312 (addc a b)))`,
  COLOR_CASES_TAC THEN
  REWRITE_TAC[addc_DEF; permc_DEF; distinctness "color"]);;

let SWAP_Q_FORCED = prove
 (`!a b c q. (q = Eperm231 \/ q = Eperm312) /\ ~(a = b) /\
 ~(a = c) /\ ~(b = c) /\
             ~(addc a (permc q (addc a b)) = c)
             ==> permc q (addc a b) = addc b c`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    DISJ_CASES_THEN
      (fun e -> SUBST1_TAC e THEN MP_TAC(SUBS [e] (CONJUNCT2 th)))
                    (CONJUNCT1 th)) THEN
  SPEC_TAC(`a:color`,`a:color`) THEN SPEC_TAC(`b:color`,`b:color`) THEN
  SPEC_TAC(`c:color`,`c:color`) THEN
  COLOR_CASES_TAC THEN
  REWRITE_TAC[addc_DEF; permc_DEF; distinctness "color"]);;

let IN_DART_ECPH = prove
 (`!(H:(num)hypermap) x0 u. x0 IN dart H
     ==> (u IN dart(ecpH H x0) <=>
          u = FST(new_dart2(dart(ecpY H x0))) \/
          u = SND(new_dart2(dart(ecpY H x0))) \/
          u = FST(new_dart2(dart(ecpU H x0))) \/
          u = SND(new_dart2(dart(ecpU H x0))) \/
          u = FST(new_dart2(dart H)) \/ u = SND(new_dart2(dart H)) \/
          u IN dart H)`,
  SIMP_TAC[ecpH; IN_DART_ECPN; ECPY_PT_IN_DART; IN_DART_ECPY]);;

(* kuH p colours ecpH whenever the junction colour differs from c.           *)

let KUH_COLORING_CORE = prove
 (`!(G2:(num)hypermap) x2 k p.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     (p = Eperm231 \/ p = Eperm312) /\
     ~(addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2))) =
       k (face_map G2 (edge_map G2 x2)))
     ==> coloring (ecpH G2 x2) (kuH G2 x2 k p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN `~((k:num->color)(node_map G2 x2) = k x2) /\
                !u. u IN dart G2 ==> ~(k (edge_map G2 u) = k u)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[COLORING_NODE; coloring]; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`p:edge_perm`; `(k:num->color)(node_map G2 x2)`; `(k:num->color) x2`]
                JUNCTION_ALG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[coloring] THEN CONJ_TAC THENL
   [ALL_TAC; SIMP_TAC[KUH_KEXT; KEXT_FACE]] THEN
  X_GEN_TAC `u:num` THEN ASM_SIMP_TAC[IN_DART_ECPH] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `p:edge_perm`
  ] KUH_APEX) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `p:edge_perm`
  ] KUH_VALUES) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] EDGE_ECPH_APEX) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] EDGE_ECPH_B) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] EDGE_ECPY_APEX) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] EDGE_ECPY_B) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] ECP_EDGE_FRESH) THEN
  ASM_REWRITE_TAC[ecpH_pt; ecpY_pt; ecpN_pt; ecpU_pt; FINITE_DART] THEN
  REPLICATE_TAC 7 STRIP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EDGE_ECPH_ECPY; EDGE_ECPY_ECPU; ECP_NEW_IN_DART;
               BPRIME_IN_DART_ECPY;
               REWRITE_RULE[ecpU_pt] ECPU_PT_IN_DART_ECPY; HEAD_IN_DART_ECPY;
               REWRITE_RULE[ecpY_pt; ecpN_pt] ECPY_PT_IN_DART; FINITE_DART;
               EDGE_ECPH_OLD; KUH_OLD; EDGE_IN_DART]);;

(* k0G for H, the junction perm and the apex inequality, for any colouring   *)
(* of the H-stepped map.                                                     *)

let K0G_H_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0 p u.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     coloring (ecpH G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x) /\
     k0 (ecpH_pt G2 x2) =
     addc (k(node_map G2 x2)) (permc p (addc (k(node_map G2 x2)) (k x2))) /\
     u IN dart(ecpH G2 x2)
     ==> k0 u = kuH G2 x2 k p u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUH_KEXT] THEN MATCH_MP_TAC K0_KEXT THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `u:num`] FBAND_ICPH) THEN
  ASM_REWRITE_TAC[HYPERMAP_LEMMA] THEN
  ASM_MESON_TAC[CFACE_COLORING]);;

let CFACE_ECPH_BPRIME = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ proper_cpring G2 x2
     ==> cface (ecpH G2 x2) (SND(new_dart2(dart(ecpU G2 x2)))) x2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpH] THEN
  MATCH_MP_TAC CFACE_ECPN_LIFT THEN
  ASM_SIMP_TAC[ECPY_PT_IN_DART; LONG_ECPY; HYPERMAP_LEMMA; BPRIME_IN_DART_ECPY;
               CFACE_ECPY_B_PT]);;

let K0_APEX_VALUES = prove
 (`!(G2:(num)hypermap) x2 k k0.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     coloring (ecpH G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x)
     ==> k0 (ecpH_pt G2 x2) = k0 (ecpU_pt G2) /\
         k0 (ecpY_pt G2 x2) = k0 (ecpH_pt G2 x2) /\
         k (node_map G2 x2) = k0 (SND(new_dart2(dart G2))) /\
         k x2 = k0 (SND(new_dart2(dart(ecpU G2 x2)))) /\
         k (face_map G2 (edge_map G2 x2)) =
         k0 (SND(new_dart2(dart(ecpY G2 x2))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] FACE_ECPH_ECPU_PT) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] FACE_ECPH_PT) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] CFACE_NODE_ECPH) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] CFACE_ECPH_BPRIME) THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] CFACE_ECPH_B_PT) THEN
  ASM_SIMP_TAC[HYPERMAP_LEMMA; NODE_ECPY_PT_VALUE] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN
  ASM_MESON_TAC[CFACE_COLORING; CFACE_FACE_SUCC; ECPH_PT_IN_DART;
                ECPU_PT_IN_DART_ECPY; DART_ECPY_SUBSET_ECPH;
                HEAD_IN_DART_ECPY; BPRIME_IN_DART_ECPY; BPP_IN_DART_ECPH;
                NODE_MAP_IN_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART]);;

let JUNCTION_P_EXISTS_H_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     coloring (ecpH G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x)
     ==> ?p. (p = Eperm231 \/ p = Eperm312) /\
             k0 (ecpH_pt G2 x2) =
             addc (k(node_map G2 x2))
             (permc p (addc (k(node_map G2 x2)) (k x2)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXISTS_JUNCTION_PERM THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `k0:num->color`]
                K0_APEX_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[COLORING_NODE];
    MP_TAC(ISPECL
  [`ecpH (G2:(num)hypermap) x2`; `k0:num->color`; `ecpU_pt (G2:(num)hypermap)`;
                   `SND(new_dart2(dart(G2:(num)hypermap)))`] ADJ_COLORING) THEN
    ASM_SIMP_TAC[EDGE_MAP_PERMUTES; ECPU_PT_IN_DART_ECPY;
                 DART_ECPY_SUBSET_ECPH;
                 ADJ_ECPH_ECPUPT_HEAD; FINITE_DART];
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th])
      THEN
    MP_TAC(ISPECL
 [`ecpH (G2:(num)hypermap) x2`; `k0:num->color`;
  `ecpY_pt (G2:(num)hypermap) x2`;
                   `SND(new_dart2(dart(ecpU (G2:(num)hypermap) x2)))`
                   ] ADJ_COLORING) THEN
    ASM_SIMP_TAC[EDGE_MAP_PERMUTES; ECPY_PT_IN_DART; DART_ECPY_SUBSET_ECPH;
                 ADJ_ECPH_ECPYPT_BPRIME; FINITE_DART]]);;

let K0_APEX_NE_C_GEN = prove
 (`!(G2:(num)hypermap) x2 k k0.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     coloring (ecpH G2 x2) k0 /\
     (!x. x IN dart G2 ==> k0 x = k x)
     ==> ~(k0 (ecpH_pt G2 x2) = k (face_map G2 (edge_map G2 x2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `k0:num->color`]
                K0_APEX_VALUES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
 [`ecpH (G2:(num)hypermap) x2`; `k0:num->color`;
  `ecpH_pt (G2:(num)hypermap) x2`;
                 `SND(new_dart2(dart(ecpY (G2:(num)hypermap) x2)))`
                 ] ADJ_COLORING) THEN
  ASM_SIMP_TAC[EDGE_MAP_PERMUTES; ECPH_PT_IN_DART; ADJ_ECPH_APEX_B]);;

let CP_TR0_CONS_H = prove
 (`!et0 cp1 cp2 k0. cp_tr0 et0 (CONS CpH cp1) cp2 k0 <=>
 cp_tr0 et0 cp1 (CONS CpH cp2) k0`,
  REWRITE_TAC[cp_tr0; CATREV_CP_CONS]);;

let CPCOLOR1_H = prove
 (`!f e1 e2 et'. cpcolor1 CpH f (CONS e1 (CONS e2 et')) =
     (if e1 = e2 then
        ctree_union (f (CONS (permc Eperm231 e1) (CONS
                                                  (permc Eperm231 e1) et')))
                    (f (CONS (permc Eperm312 e1) (CONS
                                                  (permc Eperm312 e1) et')))
      else f (CONS e2 (CONS e1 et')))`,
  REWRITE_TAC[cpcolor1; LENGTH; HD; TL; ARITH_RULE `~(SUC(SUC n) < 2)`]);;

(* The two membership reflections of the H step.                             *)

let CPCOLOR1H_MEM_GEN = prove
 (`!(G2:(num)hypermap) x2 k (Q:(num->color)->bool).
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     (!k0. Q k0 ==> coloring (ecpH G2 x2) k0)
     ==>
 ((?k0. Q k0 /\ (!x. x IN dart(ecpH G2 x2) ==> k0 x = kuH G2 x2 k Eperm231 x))
 \/
          (?k0. Q k0 /\
          (!x. x IN dart(ecpH G2 x2) ==> k0 x = kuH G2 x2 k Eperm312 x)) <=>
          (?k0. Q k0 /\ (!x. x IN dart G2 ==> k0 x = k x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `k0:num->color` THEN
    ASM_MESON_TAC[DART_SUBSET_ECPH; SUBSET; KUH_OLD];
    DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `coloring (ecpH (G2:(num)hypermap) x2) k0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
      [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `k0:num->color`]
                  JUNCTION_P_EXISTS_H_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:edge_perm` (fun th ->
      ASSUME_TAC(CONJUNCT2 th) THEN
      DISJ_CASES_THEN SUBST_ALL_TAC (CONJUNCT1 th))) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    EXISTS_TAC `k0:num->color` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC K0G_H_GEN THEN ASM_REWRITE_TAC[]]);;

let CPCOLOR1H_MEM_SWAP_GEN = prove
 (`!(G2:(num)hypermap) x2 k (Q:(num->color)->bool) pv.
     coloring G2 k /\ x2 IN dart G2 /\ proper_cpring G2 x2 /\
     (!k0. Q k0 ==> coloring (ecpH G2 x2) k0) /\
     (pv = Eperm231 \/ pv = Eperm312) /\
     ~(k (node_map G2 x2) = k (face_map G2 (edge_map G2 x2))) /\
     permc pv (addc (k(node_map G2 x2)) (k x2)) =
     addc (k x2) (k (face_map G2 (edge_map G2 x2)))
     ==>
    ((?k0. Q k0 /\ (!x. x IN dart(ecpH G2 x2) ==> k0 x = kuH G2 x2 k pv x)) <=>
          (?k0. Q k0 /\ (!x. x IN dart G2 ==> k0 x = k x)))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `k0:num->color` THEN
    ASM_MESON_TAC[DART_SUBSET_ECPH; SUBSET; KUH_OLD];
    DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `coloring (ecpH (G2:(num)hypermap) x2) k0` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
      [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `k0:num->color`]
                  JUNCTION_P_EXISTS_H_GEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:edge_perm`
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    SUBGOAL_THEN `permc q (addc ((k:num->color)(node_map G2 x2)) (k x2)) =
                  addc (k x2) (k (face_map G2 (edge_map G2 x2)))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `k0:num->color`]
                    K0_APEX_NE_C_GEN) THEN
      MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`
      ] COLORING_X2_FACE_EDGE) THEN
      MP_TAC(ISPECL [`G2:(num)hypermap`; `k:num->color`; `x2:num`
      ] COLORING_NODE) THEN
      ASM_REWRITE_TAC[HYPERMAP_LEMMA] THEN
      REPEAT DISCH_TAC THEN MATCH_MP_TAC SWAP_Q_FORCED THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `k0:num->color` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC K0G_H_GEN THEN ASM_REWRITE_TAC[]]);;

let CPCOLOR1H_CORRECT = prove
 (`!et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS CpH cp2))) k'
           ==> cp_extcol et0 cp1 (CONS CpH cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS CpH cp1) cp2 (cpcolor1 CpH f) k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (LABEL_TAC "ih" o REWRITE_RULE[CPMAP_CONS_H; FST]) ASSUME_TAC) THEN
  ABBREV_TAC `G2 = FST(cpmap cp2)` THEN ABBREV_TAC `x2 = SND(cpmap cp2)` THEN
  SUBGOAL_THEN `(x2:num) IN dart (G2:(num)hypermap) /\ proper_cpring G2 x2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CPMAP_PT_IN_DART; COLORING_NODE; proper_cpring];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST(cpmap(CONS CpH cp2)) = ecpH (G2:(num)hypermap) x2 /\
                SND(cpmap(CONS CpH cp2)) = ecpH_pt G2 x2`
  STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC[CPMAP_CONS_H; FST; SND]; ALL_TAC] THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_CONS; CP_TR0_CONS_H] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    RING_TRACE_SHAPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[CPCOLOR1_H; ADDC_MID_CANCEL_EQ] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    DK_PRIME_H) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((k:num->color) (node_map G2 x2) = k x2) /\
                ~(k x2 = k (face_map G2 (edge_map G2 x2)))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COLORING_NODE; COLORING_X2_FACE_EDGE];
    ALL_TAC] THEN
  ABBREV_TAC
   `et = ftrace (MAP (k:num->color) (cpring (G2:(num)hypermap) x2))` THEN
  ABBREV_TAC `a = (k:num->color) (node_map G2 x2)` THEN
  ABBREV_TAC `b = (k:num->color) x2` THEN
  ABBREV_TAC `c = (k:num->color) (face_map G2 (edge_map G2 x2))` THEN
  ABBREV_TAC `h = cprsize (catrev_cp cp1 (CONS CpH cp2)) - 2` THEN
  (* each kuH p whose junction colour differs from c gives one branch        *)
  SUBGOAL_THEN
   `!p. (p = Eperm231 \/ p = Eperm312) /\ ~(addc a (permc p (addc a b)) = c)
        ==> ctree_proper h
              (f (CONS (permc p (addc a b))
                   (CONS (addc (addc a (permc p (addc a b))) c)
                         (TL(TL et))))) /\
            (ctree_mem
              (f (CONS (permc p (addc a b))
                   (CONS (addc (addc a (permc p (addc a b))) c)
                         (TL(TL et)))))
              (ttail et0) <=>
             ?k0. (coloring (FST(cpmap(catrev_cp cp1 (CONS CpH cp2)))) k0 /\
                   cp_tr0 et0 cp1 (CONS CpH cp2) k0) /\
                  (!x. x IN dart(ecpH (G2:(num)hypermap) x2) ==>
                       k0 x = kuH G2 x2 k p x))`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:edge_perm` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    USE_THEN "ih" (MP_TAC o SPEC `kuH (G2:(num)hypermap) x2 k p`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC KUH_COLORING_CORE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[cp_extcol];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:color = c` THEN ASM_REWRITE_TAC[] THENL
   [(* doubled branch a = c: both junction colours, p = Eperm231, Eperm312 *)
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `Eperm312` th) THEN
                            MP_TAC(SPEC `Eperm231` th)) THEN
    ASM_SIMP_TAC[ADDC_CANCEL; JUNCTION_ALG] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CTREE_UNION_PROPER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:num`;
      `f (CONS (permc Eperm231 (addc a b))
              (CONS (permc Eperm231 (addc a b)) (TL(TL et)))):ctree`;
      `f (CONS (permc Eperm312 (addc a b))
              (CONS (permc Eperm312 (addc a b)) (TL(TL et)))):ctree`;
      `ttail et0`] CTREE_MEM_UNION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`;
                   `\k0:num->color.
                      coloring (FST(cpmap(catrev_cp cp1 (CONS CpH cp2)))) k0 /\
                      cp_tr0 et0 cp1 (CONS CpH cp2) k0`]
      CPCOLOR1H_MEM_GEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[cp_restrict; CP_RESTRICT_ANY];
    (* swap branch: the unique pv with pv(a +c b) = b +c c                   *)
    MP_TAC(ISPECL [`addc (a:color) b`; `addc (b:color) c`]
      SWAP_PERM_EXISTS) THEN
    ASM_REWRITE_TAC[ADDC_EQ_0; ADDC_MID_CANCEL_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `pv:edge_perm` (CONJUNCTS_THEN ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `pv:edge_perm`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `~(addc a (addc b c) = c) /\ addc (addc a (addc b c)) c = addc a b`
     (fun th -> REWRITE_TAC[th])
    THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[SWAP_JUNCTION_VALID];
        REWRITE_TAC[ADDC_ASSOC; ADDC_CANCEL]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`;
                   `\k0:num->color.
                      coloring (FST(cpmap(catrev_cp cp1 (CONS CpH cp2)))) k0 /\
                      cp_tr0 et0 cp1 (CONS CpH cp2) k0`;
                   `pv:edge_perm`] CPCOLOR1H_MEM_SWAP_GEN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[cp_restrict; CP_RESTRICT_ANY]]);;

(* ------------------------------------------------------------------------- *)
(* The R step (ecpR is the identity map, only the ring pointer rotates), and *)
(* the per-cpstep correctness induction over R/U/Y/H programs.               *)
(* ------------------------------------------------------------------------- *)

let CPCOLOR1R_CORRECT = prove
 (`!n et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS (CpR n) cp2))) k'
           ==> cp_extcol et0 cp1 (CONS (CpR n) cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS (CpR n) cp1) cp2 (cpcolor1 (CpR n) f) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FST(cpmap(CONS (CpR n) cp2)) = FST(cpmap cp2)` ASSUME_TAC THENL
   [REWRITE_TAC[CPMAP_CONS_R; FST; ecpR]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num->color` o check(is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_CONS] THEN
  REWRITE_TAC[cpcolor1] THEN
  REWRITE_TAC[cp_tr0; CATREV_CP_CONS] THEN
  SUBGOAL_THEN
   `ftrace (MAP k (cpring (FST(cpmap cp2)) (SND(cpmap(CONS (CpR n) cp2))))) =
    rot_list n (ftrace (MAP k (cpring (FST(cpmap cp2)) (SND(cpmap cp2)))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[CPMAP_CONS_R; SND] THEN
    MATCH_MP_TAC FTRACE_CPRING_ECPR_ROT THEN
    REWRITE_TAC[CPMAP_PT_IN_DART]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Base map cpmap0 facts.                                                    *)
(* ------------------------------------------------------------------------- *)

let KBASE_COLORING = prove
 (`coloring cpmap0 (\x:num. if x = 1 then Color1 else Color0)`,
  REWRITE_TAC[coloring; CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[swap; I_THM] THEN
  CONV_TAC(DEPTH_CONV NUM_REL_CONV) THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[distinctness "color"]);;

let KBASE_TRACE = prove
 (`ftrace (MAP (\x:num. if x = 1 then Color1 else Color0) (cpring cpmap0 1)) =
   [Color1; Color1]`,
  REWRITE_TAC[CPRING_CPMAP0; MAP] THEN
  CONV_TAC(DEPTH_CONV NUM_REL_CONV) THEN REWRITE_TAC[] THEN
  REWRITE_TAC[ftrace; ONE] THEN
  REWRITE_TAC[rot_list; drop_list; take_list; TL; HD; NOT_CONS_NIL;
              APPEND] THEN
  REWRITE_TAC[trace_DEF; LAST; NOT_CONS_NIL; ptrace] THEN
  REWRITE_TAC[ADDC_0] THEN ONCE_REWRITE_TAC[ADDC_COMM] THEN
  REWRITE_TAC[ADDC_0]);;

let CPMAP0_DART_CASES = prove
 (`!p x. p IN dart cpmap0 /\ x IN dart cpmap0 ==>
 x = p \/ x = node_map cpmap0 p`,
  REWRITE_TAC[CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[swap] THEN
  CONV_TAC(DEPTH_CONV NUM_REL_CONV) THEN REWRITE_TAC[]);;

let CPMAP0_HYP = prove
 (`FINITE(dart cpmap0) /\ edge_map cpmap0 permutes dart cpmap0 /\
   node_map cpmap0 permutes dart cpmap0 /\
   face_map cpmap0 permutes dart cpmap0`,
  MP_TAC(ISPEC `cpmap0` HYPERMAP_LEMMA) THEN SIMP_TAC[]);;

let PROPER_CPRING_CPMAP0 = prove
 (`!p. p IN dart cpmap0 ==> proper_cpring cpmap0 p`,
  REWRITE_TAC[proper_cpring; CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY] THEN
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[swap] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Colour-algebra identities for the CpY / CpU base-colouring bridges.       *)
(* ------------------------------------------------------------------------- *)

let PERMC_312_231_COMM = prove
 (`!c. permc Eperm312 (permc Eperm231 c) = permc Eperm231 (permc Eperm312 c)`,
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[permc_DEF]);;

let PERMC_213_INVOL = prove
 (`!c. permc Eperm213 (permc Eperm213 c) = c`,
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[permc_DEF]);;

let FTRACE_PERMC_COMPOSE = prove
 (`!g k L. ftrace (MAP (permc g o k) L) = permt g (ftrace (MAP k L))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ftrace; GSYM MAP_o] THEN
  ONCE_REWRITE_TAC[GSYM PERMT_MAP] THEN REWRITE_TAC[GSYM TRACE_PERMT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[PERMT_MAP; MAP_ROT_LIST; MAP_o]);;

(* ------------------------------------------------------------------------- *)
(* The ring-trace facts in the forms the cpmap0 bridges and the final        *)
(* correctness theorem consume (from RING_FTRACE_FACTS).                     *)
(* ------------------------------------------------------------------------- *)

let MEMC0_EPTRACE_ROT_CPRING = prove
 (`!(H:(num)hypermap) k x0.
     coloring H k /\ x0 IN dart H
     ==> ~(MEM Color0 (eptrace (rot_list 1 (MAP k (cpring H x0)))))`,
  MESON_TAC[RING_FTRACE_FACTS]);;

let PROPER_PTRACE_ROT_CPRING = prove
 (`!(H:(num)hypermap) k x0.
     coloring H k /\ x0 IN dart H
     ==> proper_trace (ptrace (rot_list 1 (MAP k (cpring H x0))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ptrace (rot_list 1 (MAP (k:num->color) (cpring H x0))) =
                TL(ftrace (MAP k (cpring H x0)))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC TL_FTRACE THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_MAP] THEN
    ASM_MESON_TAC[SIZE_CPRING; COLORING_PROPER_CPRING;
                  ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ASM_MESON_TAC[RING_FTRACE_FACTS]]);;

(* The base traces of the CpU and CpY branches of cpcolor0, from a base      *)
(* colouring kk of trace [Color1; Color1] (DK_PRIME_U gives e :: e :: the    *)
(* base trace): kuU of permc Eperm213 o kk (trace [Color2; Color2]) and of   *)
(* kk itself, with e = Color1, give [C1; C1; C2; C2] and [C1; C1; C1; C1];   *)
(* kuY of permc Eperm312 o kk (trace [Color3; Color3]) via Eperm231 gives    *)
(* [C1; C2; C3], as in cpcolor0's CpY clause.                                *)

let KPRIME_UA_TRACE = prove
 (`!kk p. coloring cpmap0 kk /\ p IN dart cpmap0 /\
          ftrace (MAP kk (cpring cpmap0 p)) = [Color1; Color1]
          ==> ftrace (MAP (kuU cpmap0 p (permc Eperm213 o kk) Color1)
                          (cpring (ecpU cpmap0 p) (ecpU_pt cpmap0))) =
              [Color1; Color1; Color2; Color2]`,
  SIMP_TAC[DK_PRIME_U; COLORING_PERMC; FTRACE_PERMC_COMPOSE; permt;
           permc_DEF]);;

let KPRIME_UB_TRACE = prove
 (`!kk p. coloring cpmap0 kk /\ p IN dart cpmap0 /\
          ftrace (MAP kk (cpring cpmap0 p)) = [Color1; Color1]
          ==> ftrace (MAP (kuU cpmap0 p kk Color1)
                          (cpring (ecpU cpmap0 p) (ecpU_pt cpmap0))) =
              [Color1; Color1; Color1; Color1]`,
  SIMP_TAC[DK_PRIME_U]);;

let KPRIME_Y_TRACE = prove
 (`!kk p. coloring cpmap0 kk /\ p IN dart cpmap0 /\
          ftrace (MAP kk (cpring cpmap0 p)) = [Color1; Color1]
          ==> ftrace (MAP (kuY cpmap0 p (permc Eperm312 o kk) Eperm231)
                          (cpring (ecpY cpmap0 p) (ecpY_pt cpmap0 p))) =
              [Color1; Color2; Color3]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ftrace (MAP (permc Eperm312 o kk) (cpring cpmap0 p)) = [Color3; Color3]`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FTRACE_PERMC_COMPOSE; permt; permc_DEF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cpmap0`; `p:num`; `permc Eperm312 o (kk:num->color)`]
    HEAD_FTRACE_MAP_CPRING) THEN
  MP_TAC(ISPECL [`cpmap0`; `p:num`; `permc Eperm312 o (kk:num->color)`;
                 `Eperm231`] DK_PRIME_Y) THEN
  ASM_SIMP_TAC[COLORING_PERMC; PROPER_CPRING_CPMAP0; inv_eperm] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[HD; TL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[permc_DEF]);;

(* ========================================================================= *)
(* The ring of a cubic program has length >= 2 (CPRSIZE_GE_2), and the trace *)
(* normalisation behind CTREE_MEM_CPCOLOR_ALL (Gonthier cfcolor.v:659): our  *)
(* ring_trace (coloring.ml) uses trace_col (=urtrace, wrap-first) whereas    *)
(* Gonthier's uses trace=urtrace o rot 1; hence the rot_list 1 (cpring ...)  *)
(* on the ring, matching kempetree_wrap KEMPE_TREEP.                         *)
(* ========================================================================= *)

let CPRSIZE_GE_2 = prove
 (`!cp. cubic_prog cp ==> 2 <= cprsize cp`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[cprsize] THEN
  MP_TAC(ISPEC `cp:(cpstep)list` CPMAP_PROPER) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`FST(cpmap cp)`; `SND(cpmap cp)`] SIZE_PROPER_CPRING) THEN
  REWRITE_TAC[CPMAP_PT_IN_DART] THEN DISCH_THEN SUBST1_TAC THEN ARITH_TAC);;

(* --- CTREE_MEM_CPCOLOR trace-normalisation support ---                     *)

let ZEROSUM_CONS_SUMT = prove
 (`!M. ~(M = []) /\ sumt M = Color0 ==> M = CONS (sumt (TL M)) (TL M)`,
  MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[NOT_CONS_NIL; HD; TL; sumt] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[CONS_11] THEN REWRITE_TAC[ADDC_EQ_0] THEN SIMP_TAC[]);;

let TRACE_COL_CTRACE_PTRACE = prove
 (`!L. ~(L = []) ==> trace_col L = ctrace (ptrace L)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TRACE_COL_NONEMPTY) THEN
  MP_TAC(ISPEC `trace_col L` ZEROSUM_CONS_SUMT) THEN
  ASM_REWRITE_TAC[SUMT_TRACE] THEN
  ASM_SIMP_TAC[TL_TRACE_COL] THEN
  REWRITE_TAC[ctrace]);;

let RING_TRACE_CTRACE_PTRACE = prove
 (`!(G:(num)hypermap) r et. ~(r = [])
            ==>
 (ring_trace G r (ctrace et) <=> (?k. coloring G k /\ et = ptrace (MAP k r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ring_trace] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:num->color` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num->color` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(MAP (k:num->color) r = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MAP_EQ_NIL];
    FIRST_X_ASSUM(fun th -> if can(find_term(fun t->t=`ctrace et`))(concl th)
    then MP_TAC th else NO_TAC) THEN
    ASM_SIMP_TAC[TRACE_COL_CTRACE_PTRACE] THEN
    REWRITE_TAC[ctrace; CONS_11] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[MAP_EQ_NIL];
    ASM_SIMP_TAC[TRACE_COL_CTRACE_PTRACE]]);;

let ETAIL_EQ_PERMT = prove
 (`!et1 et2. proper_trace et1 /\ proper_trace et2 /\ etail et1 = etail et2
             ==> ?g. et2 = permt g et1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `et1:(color)list` ETAIL_PERM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `g1:edge_perm`) THEN
  MP_TAC(ISPEC `et2:(color)list` ETAIL_PERM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `g2:edge_perm`) THEN
  MP_TAC(ISPECL [`inv_eperm g2`; `g1:edge_perm`] COMPOSE_PERMT) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:edge_perm`
 (fun th -> EXISTS_TAC `h:edge_perm` THEN MP_TAC(SPEC `et1:(color)list` th)))
   THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `permt g1 (et1:(color)list) = permt g2 et2` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[PERMT_INV_CANCEL]);;

let ETAIL_EQ_TTAIL_EVEN = prove
 (`!et. even_trace et ==> etail et = ttail et`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[etail; etrace_perm] THEN
  ASM_REWRITE_TAC[PERMT_ID]);;

let TTAIL_IMPROPER = prove
 (`!et. ~(proper_trace et) ==> ttail et = [Color0]`,
  GEN_TAC THEN REWRITE_TAC[ttail] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let PTRACE_ROT_MAP_PERMC = prove
 (`!(h:edge_perm) k0 (G:(num)hypermap) x0.
     ptrace (rot_list 1 (MAP ((permc h) o (k0:num->color)) (cpring G x0))) =
     permt h (ptrace (rot_list 1 (MAP k0 (cpring G x0))))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MAP_o; GSYM MAP_ROT_LIST; GSYM PERMT_MAP; GSYM PTRACE_PERMT] THEN
  REWRITE_TAC[PERMT_MAP; MAP_ROT_LIST]);;

(* The core of the trace-normalisation equivalence, without the agreement    *)
(* hypothesis (Gonthier's gauge argument, cfcolor.v:668-690).  Forward: et   *)
(* is proper (otherwise ttail et = [Color0], but eptrace contains no Color0) *)
(* and even, and k0 is gauged by ETAIL_EQ_PERMT to hit et exactly.           *)
(* Backward: with k0 = k, ttail et = etail et (even) = etail (ptrace ...) =  *)
(* eptrace (...).                                                            *)
let CTREE_MEM_CPCOLOR_CORE_AF = prove
 (`!(G:(num)hypermap) x0 et.
     x0 IN dart G
     ==> ((?k0. coloring G k0 /\
                ttail et = eptrace (rot_list 1 (MAP k0 (cpring G x0))))
          <=> even_trace et /\
              (?k. coloring G k /\
              et = ptrace (rot_list 1 (MAP k (cpring G x0)))))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `even_trace et` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[even_trace; eptrace; EVEN_ETAIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~MEM Color0 (ttail et)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEMC0_EPTRACE_ROT_CPRING THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `proper_trace et` ASSUME_TAC THENL
     [MP_TAC(ISPEC `et:(color)list` TTAIL_IMPROPER) THEN
      ASM_CASES_TAC `proper_trace et` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~MEM Color0 (ttail et)` THEN
      ASM_REWRITE_TAC[MEM]; ALL_TAC] THEN
    ABBREV_TAC `et0 =
    ptrace (rot_list 1 (MAP (k0:num->color) (cpring G x0)))` THEN
    SUBGOAL_THEN `proper_trace et0` ASSUME_TAC THENL
     [EXPAND_TAC "et0" THEN MATCH_MP_TAC PROPER_PTRACE_ROT_CPRING THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `etail et = etail et0` ASSUME_TAC THENL
     [MP_TAC(SPEC `et:(color)list` ETAIL_EQ_TTAIL_EVEN) THEN
     ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "et0" THEN
      REWRITE_TAC[eptrace]; ALL_TAC] THEN
    MP_TAC(ISPECL [`et0:(color)list`; `et:(color)list`] ETAIL_EQ_PERMT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `h:edge_perm`) THEN
    EXISTS_TAC `(permc h) o (k0:num->color)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC COLORING_INJ_GEN THEN ASM_REWRITE_TAC[] THEN
     MESON_TAC[PERMC_INJ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[PTRACE_ROT_MAP_PERMC];
    STRIP_TAC THEN EXISTS_TAC `k:num->color` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[eptrace] THEN
    MP_TAC(SPEC `et:(color)list` ETAIL_EQ_TTAIL_EVEN) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[]]);;

(* For distinct colours a,b, an injective colour-map sending a->C0, b->C1    *)
(* (affine c |-> addc (permc h a) (permc h c) with h picked so permc h (addc *)
(* a b) = C1).                                                               *)
let COLOR_GAUGE_EXISTS = prove
 (`!a b. ~(a = b) ==>
 ?F. (!x y:color. F x = F y ==> x = y) /\ F a = Color0 /\ F b = Color1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(addc a b = Color0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ADDC_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `?h. permc h (addc a b) = Color1`
  (X_CHOOSE_TAC `h:edge_perm`) THENL
   [UNDISCH_TAC `~(addc a b = Color0)` THEN SPEC_TAC(`addc a b`,`c:color`) THEN
    MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[distinctness "color"] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `Eperm123` THEN REWRITE_TAC[permc_DEF];
      EXISTS_TAC `Eperm213` THEN REWRITE_TAC[permc_DEF];
      EXISTS_TAC `Eperm231` THEN REWRITE_TAC[permc_DEF]]; ALL_TAC] THEN
  EXISTS_TAC `\c. addc (permc h a) (permc h c)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[ADDC_CANCEL_L] THEN
    DISCH_THEN(MP_TAC o MATCH_MP PERMC_INJ) THEN SIMP_TAC[];
    REWRITE_TAC[ADDCC];
    REWRITE_TAC[GSYM PERMC_ADDC] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Geometry of the K step ecpK G x0 = ecpN G (node x0) (Gonthier cfmap.v     *)
(* ecpK, icpK): the two fresh darts ecpN_pt G and SND(new_dart2(dart G)) are *)
(* cofacial with node x0 and face(edge x0) respectively, old faces project   *)
(* back to G (CFACE_ECPK_PROJ), every dart of ecpK is cofacial with an old   *)
(* dart (FBAND_ECPK), and the ring of ecpK is ecpN_pt G :: TL(TL(ring))      *)
(* (CPRING_ECPK).  Also cpmap of the K and A steps.                          *)
(* ------------------------------------------------------------------------- *)

let CPRING_ECPR_ROT_GEN = prove
 (`!H (x0:num) n. x0 IN dart H /\ node_map H permutes dart H /\ FINITE(dart H)
   ==> cpring (ecpR H n x0) (ecpR_pt H n x0) = rot_list n (cpring H x0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpR] THEN
  ASM_CASES_TAC `n <= orbit_size (node_map H) (x0:num)` THENL
   [ASM_SIMP_TAC[CPRING_ECPR_ROT]; ALL_TAC] THEN
  SUBGOAL_THEN `rot_list n (cpring H (x0:num)) = cpring H x0 /\ ecpR_pt H n x0
    = x0`
    (fun th -> REWRITE_TAC[th]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ROT_LIST_ALL THEN ASM_SIMP_TAC[SIZE_CPRING] THEN
     ASM_ARITH_TAC;
    REWRITE_TAC[ecpR_pt] THEN
    SUBGOAL_THEN `orbit_size (node_map H) (x0:num) - n = 0` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ITER]]]);;

let CFACE_REFL_ALL = prove
 (`!(H:(A)hypermap) x. cface H x x`,
  REWRITE_TAC[cface; face; IN_ORBIT_MAP_REFL]);;

let LONG_CPRING_NODE = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ long_cpring G x0 ==> long_cpring G (node_map G x0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `node_map G (x0:num)`]
    SIZE_LONG_CPRING) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] SIZE_LONG_CPRING) THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; SIZE_CPRING] THEN
  MP_TAC(ISPECL [`node_map (G:(num)hypermap)`; `dart (G:(num)hypermap)`;
                 `x0:num`; `1`] ORBIT_SIZE_ITER_GEN) THEN
  ASM_REWRITE_TAC[ONE; ITER; FINITE_DART; NODE_MAP_PERMUTES] THEN
  ASM_MESON_TAC[]);;

let ECPRR_PT_NODE = prove
 (`!(G:(num)hypermap) x0. x0 IN dart G ==> ecpRr_pt G x0 = node_map G x0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ecpRr_pt; ecpR_pt] THEN
  MP_TAC(ISPECL [`node_map (G:(num)hypermap)`; `dart (G:(num)hypermap)`;
                 `x0:num`] ORBIT_SIZE_POS) THEN
  ASM_REWRITE_TAC[FINITE_DART; NODE_MAP_PERMUTES] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `orbit_size (node_map G) (x0:num) - (orbit_size (node_map G) x0 - 1) = 1`
  SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ONE; ITER]]);;

let ECPK_ALT = prove
 (`!(G:(num)hypermap) x0. x0 IN dart G ==> ecpK G x0 = ecpN G (node_map G x0)`,
  SIMP_TAC[ecpK; ecpR; ECPRR_EQ; ECPRR_PT_NODE]);;

let ECPN_FRESH = prove
 (`!(H:(num)hypermap).
     ~(ecpN_pt H IN dart H) /\ ~(SND(new_dart2(dart H)) IN dart H) /\
     ~(ecpN_pt H = SND(new_dart2(dart H))) /\
     ~(SND(new_dart2(dart H)) = ecpN_pt H)`,
  GEN_TAC THEN REWRITE_TAC[ecpN_pt] THEN
  MP_TAC(ISPEC `dart(H:(num)hypermap)` NEW_DART2_FRESH) THEN
  REWRITE_TAC[FINITE_DART] THEN MESON_TAC[]);;

let DART_ECPN_CASES = prove
 (`!(H:(num)hypermap) y z.
     y IN dart H
     ==> (z IN dart(ecpN H y) <=>
          z = ecpN_pt H \/ z = SND(new_dart2(dart H)) \/ z IN dart H)`,
  SIMP_TAC[ECPN_COMPONENTS; IN_INSERT; ecpN_pt]);;

let EDGE_ECPN_AB = prove
 (`!(H:(num)hypermap) y.
     y IN dart H
     ==> edge_map (ecpN H y) (ecpN_pt H) = SND(new_dart2(dart H)) /\
         edge_map (ecpN H y) (SND(new_dart2(dart H))) = ecpN_pt H`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `H:(num)hypermap` ECPN_FRESH) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[ECPN_COMPONENTS; ecpU_edge; ecpN_pt] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ecpN_pt]) THEN ASM_REWRITE_TAC[]);;

let FACE_ECPN_A = prove
 (`!(H:(num)hypermap) y. y IN dart H ==> face_map (ecpN H y) (ecpN_pt H) = y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPN_COMPONENTS; ecpN_face; ecpN_pt]);;

let FACE_ECPN_B_LONG = prove
 (`!(H:(num)hypermap) y.
     y IN dart H /\ long_cpring H y
     ==> face_map (ecpN H y) (SND(new_dart2(dart H))) =
         face_map H (edge_map H (face_map H (edge_map H y)))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `H:(num)hypermap` ECPN_FRESH) THEN
  REWRITE_TAC[ecpN_pt] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ECPN_COMPONENTS; ecpN_face]);;

let EDGE_ECPK_OLD = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G /\
     z IN dart G
     ==> edge_map (ecpK G x0) z = edge_map G z`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPK_ALT] THEN
  MATCH_MP_TAC EDGE_ECPN_OLD_GEN THEN ASM_SIMP_TAC[NODE_MAP_IN_DART]);;

let CFACE_ECPK_A_NODE = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G
     ==> cface (ecpK G x0) (ecpN_pt G) (node_map G x0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPK_ALT] THEN
  MP_TAC(ISPECL [`ecpN G (node_map G (x0:num))`; `ecpN_pt (G:(num)hypermap)`]
    CFACE_STEP) THEN
  ASM_SIMP_TAC[FACE_ECPN_A; NODE_MAP_IN_DART]);;

let CFACE_ECPK_B_FE = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G /\
     long_cpring G x0
     ==> cface (ecpK G x0) (SND(new_dart2(dart G)))
               (face_map G (edge_map G x0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPK_ALT] THEN
  MP_TAC(ISPECL [`ecpN G (node_map G (x0:num))`;
                 `SND(new_dart2(dart (G:(num)hypermap)))`] CFACE_STEP) THEN
  ASM_SIMP_TAC[FACE_ECPN_B_LONG; NODE_MAP_IN_DART; LONG_CPRING_NODE; nodeK]);;

let CFACE_ECPK_PROJ = prove
 (`!(G:(num)hypermap) x0 x y.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G /\
     long_cpring G x0 /\ x IN dart G /\ y IN dart G /\ cface (ecpK G x0) x y
     ==> cface G x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CFACE_ECPN_PROJ THEN
  EXISTS_TAC `node_map G (x0:num)` THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; LONG_CPRING_NODE] THEN
  ASM_MESON_TAC[ECPK_ALT]);;

let DART_ECPK_CASES = prove
 (`!(G:(num)hypermap) x0 z.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G
     ==> (z IN dart(ecpK G x0) <=>
          z = ecpN_pt G \/ z = SND(new_dart2(dart G)) \/ z IN dart G)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPK_ALT; DART_ECPN_CASES;
    NODE_MAP_IN_DART]);;

let EDGE_ECPK_AB = prove
 (`!(G:(num)hypermap) x0.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G
     ==> edge_map (ecpK G x0) (ecpN_pt G) = SND(new_dart2(dart G)) /\
         edge_map (ecpK G x0) (SND(new_dart2(dart G))) = ecpN_pt G`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPK_ALT; EDGE_ECPN_AB;
    NODE_MAP_IN_DART]);;

let FBAND_ECPK = prove
 (`!(G:(num)hypermap) x0 u.
     x0 IN dart G /\ FINITE(dart G) /\ node_map G permutes dart G /\
     face_map G permutes dart G /\ edge_map G permutes dart G /\
     long_cpring G x0 /\ u IN dart(ecpK G x0)
     ==> ?x. x IN dart G /\ cface (ecpK G x0) u x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPK_A_NODE) THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] CFACE_ECPK_B_FE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `(u:num) IN dart (ecpK G x0)` THEN
  ASM_SIMP_TAC[DART_ECPK_CASES] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `node_map G (x0:num)` THEN ASM_SIMP_TAC[NODE_MAP_IN_DART];
    EXISTS_TAC `face_map G (edge_map G (x0:num))` THEN
    ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART];
    EXISTS_TAC `u:num` THEN ASM_REWRITE_TAC[CFACE_REFL_ALL]]);;

let TL_TL_APPEND_SING = prove
 (`!(l:A list) x.
     2 <= LENGTH l ==> APPEND (TL(TL l)) [x] = TL(TL(APPEND l [x]))`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= 0)`] THEN
  POP_ASSUM(K ALL_TAC) THEN SPEC_TAC(`t:A list`,`t:A list`) THEN
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `~(2 <= SUC 0)`; APPEND; TL;
              ARITH_RULE `2 <= SUC(SUC n)`]);;

let CPRING_ECPK = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H /\ long_cpring H x0 /\ FINITE(dart H) /\
     edge_map H permutes dart H /\ node_map H permutes dart H /\
     face_map H permutes dart H
     ==> cpring (ecpK H x0) (ecpK_pt H x0) =
         CONS (ecpN_pt H) (TL(TL(cpring H x0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(node_map H (x0:num)) IN dart H /\
                node_map H (node_map H x0) IN dart H`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[NODE_MAP_IN_DART]; ALL_TAC] THEN
  SUBGOAL_THEN `2 < orbit_size (node_map H) (node_map H (node_map H (x0:num)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`node_map (H:(num)hypermap)`; `dart (H:(num)hypermap)`;
                   `x0:num`; `SUC(SUC 0)`] ORBIT_SIZE_ITER_GEN) THEN
    ASM_REWRITE_TAC[ITER] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`H:(num)hypermap`; `x0:num`] SIZE_LONG_CPRING) THEN
    ASM_SIMP_TAC[SIZE_CPRING]; ALL_TAC] THEN
  REWRITE_TAC[ecpK; ecpK_pt; ECPRR_EQ] THEN ASM_SIMP_TAC[ECPRR_PT_NODE] THEN
  MP_TAC(ISPECL [`ecpN H (node_map H (x0:num))`; `ecpN_pt (H:(num)hypermap)`;
                 `1`] CPRING_ECPR_ROT_GEN) THEN
  ASM_SIMP_TAC[ECPN_PT_IN_DART; FINITE_DART; NODE_MAP_PERMUTES] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `node_map H (x0:num)`] CPRING_ECPN) THEN
  ASM_SIMP_TAC[LONG_CPRING_NODE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ROT_LIST_ONE; APPEND] THEN AP_TERM_TAC THEN
  REWRITE_TAC[cpring] THEN
  SUBGOAL_THEN
   `orbit_list (node_map H) (node_map H (node_map H (node_map H (x0:num)))) =
    rot_list 1 (orbit_list (node_map H) (node_map H (node_map H x0)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`node_map (H:(num)hypermap)`; `dart (H:(num)hypermap)`;
                   `node_map H (node_map H (x0:num))`; `1`] ORBIT_LIST_ROT)
                     THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[num_CONV `1`; ITER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`node_map (H:(num)hypermap)`;
                 `node_map H (node_map H (x0:num))`] LENGTH_ORBIT_LIST) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[orbit_list] THEN
  ABBREV_TAC `il = iterlist (orbit_size (node_map H)
                     (node_map H (node_map H x0)) - 1)
                   (node_map H) (node_map H (node_map H (x0:num)))` THEN
  REWRITE_TAC[LENGTH] THEN DISCH_TAC THEN
  REWRITE_TAC[ROT_LIST_ONE; REVERSE_APPEND; REVERSE; APPEND; TL] THEN
  MATCH_MP_TAC TL_TL_APPEND_SING THEN REWRITE_TAC[LENGTH_REVERSE] THEN
  ASM_ARITH_TAC);;

let CPMAP_CONS_K = prove
 (`!cp. cpmap (CONS CpK cp) =
        (ecpK (FST(cpmap cp)) (SND(cpmap cp)),
         ecpK_pt (FST(cpmap cp)) (SND(cpmap cp)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

let CPMAP_CONS_A = prove
 (`!cp. cpmap (CONS CpA cp) =
        (ecpA (FST(cpmap cp)) (SND(cpmap cp)),
         ecpA_pt (FST(cpmap cp)) (SND(cpmap cp)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply]);;

(* ------------------------------------------------------------------------- *)
(* The K step colouring kcfK G2 x2 h c0 = kext (ecpK G2 x2) G2 h c0 (the     *)
(* colour of the old dart on the face, c0 off the old faces): its values on  *)
(* old darts and on the two new darts ecpN_pt G2 / SND(new_dart2(dart G2))   *)
(* (KCFK_HEAD, KCFK_B), the ecpK ring colouring KCFK_MAP_CPRING_ECPK and     *)
(* KCFK_COLORING (needs only h(face(edge x2)) <> h(node x2)); the ecpK facts *)
(* CFACE_ECPK_A_NODE, CFACE_ECPK_B_FE, DART_ECPK_CASES, CFACE_ECPK_PROJ come *)
(* from the geometry section above.                                          *)
(* ------------------------------------------------------------------------- *)

let kcfK = new_definition
 `kcfK (G2:(num)hypermap) x2 (h:num->color) c0 u =
    if (?x. x IN dart G2 /\ cface (ecpK G2 x2) u x)
    then h (@x. x IN dart G2 /\ cface (ecpK G2 x2) u x)
    else c0`;;

(* ecpK face-projection onto G (ecpK = ecpN G pk, pk long).                  *)

let TL_CPRING_NONEMPTY = prove
 (`!(G:(num)hypermap) x0. x0 IN dart G /\ proper_cpring G x0
                           ==> ~(TL(cpring G x0) = [])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`G:(num)hypermap`; `x0:num`] HEAD_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[TL; NOT_CONS_NIL]);;

let DART_SUBSET_ECPK = prove
 (`!(G2:(num)hypermap) x2 z.
     x2 IN dart G2 /\ z IN dart G2 ==> z IN dart(ecpK G2 x2)`,
  SIMP_TAC[DART_ECPK_CASES; FINITE_DART; NODE_MAP_PERMUTES]);;

let KCFK_KEXT = prove
 (`!(G2:(num)hypermap) x2 h c0. kcfK G2 x2 h c0 = kext (ecpK G2 x2) G2 h c0`,
  REWRITE_TAC[FUN_EQ_THM; kcfK; kext]);;

let KCFK_PROJ = prove
 (`!(G2:(num)hypermap) x2.
     x2 IN dart G2 /\ long_cpring G2 x2
     ==> dart G2 SUBSET dart(ecpK G2 x2) /\
         (!x y. x IN dart G2 /\ y IN dart G2 /\ cface (ecpK G2 x2) x y
                ==> cface G2 x y)`,
  REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[SUBSET; DART_SUBSET_ECPK];
    ASM_MESON_TAC[CFACE_ECPK_PROJ; FINITE_DART; NODE_MAP_PERMUTES]]);;

let KCFK_OLD = prove
 (`!(G2:(num)hypermap) x2 h c0 z.
     coloring G2 h /\ x2 IN dart G2 /\ long_cpring G2 x2 /\ z IN dart G2
     ==> kcfK G2 x2 h c0 z = h z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KCFK_KEXT] THEN MATCH_MP_TAC KEXT_OLD THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC KCFK_PROJ THEN ASM_REWRITE_TAC[]);;

let KCFK_CFACE = prove
 (`!(G2:(num)hypermap) x2 h c0 u z.
     coloring G2 h /\ x2 IN dart G2 /\ long_cpring G2 x2 /\
     z IN dart G2 /\ cface (ecpK G2 x2) u z
     ==> kcfK G2 x2 h c0 u = h z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KCFK_KEXT] THEN
  MATCH_MP_TAC KEXT_CFACE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC KCFK_PROJ THEN ASM_REWRITE_TAC[]);;

let KCFK_FACE = prove
 (`!(G2:(num)hypermap) x2 h c0 u.
     u IN dart(ecpK G2 x2)
     ==> kcfK G2 x2 h c0 (face_map (ecpK G2 x2) u) = kcfK G2 x2 h c0 u`,
  SIMP_TAC[KCFK_KEXT; KEXT_FACE]);;

let KCFK_HEAD = prove
 (`!(G2:(num)hypermap) x2 h c0.
     coloring G2 h /\ x2 IN dart G2 /\ long_cpring G2 x2
     ==> kcfK G2 x2 h c0 (ecpN_pt G2) = h (node_map G2 x2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KCFK_CFACE THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; CFACE_ECPK_A_NODE; FINITE_DART;
               NODE_MAP_PERMUTES]);;

let KCFK_B = prove
 (`!(G2:(num)hypermap) x2 h c0.
     coloring G2 h /\ x2 IN dart G2 /\ long_cpring G2 x2
     ==> kcfK G2 x2 h c0 (SND(new_dart2(dart G2))) =
         h (face_map G2 (edge_map G2 x2))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC KCFK_CFACE THEN
  ASM_SIMP_TAC[FACE_MAP_IN_DART; EDGE_MAP_IN_DART; CFACE_ECPK_B_FE;
               FINITE_DART; NODE_MAP_PERMUTES]);;

let KCFK_MAP_CPRING_ECPK = prove
 (`!(G2:(num)hypermap) x2 h c0.
     coloring G2 h /\ x2 IN dart G2 /\ long_cpring G2 x2
     ==> MAP (kcfK G2 x2 h c0) (cpring (ecpK G2 x2) (ecpK_pt G2 x2)) =
         CONS (h (node_map G2 x2)) (MAP h (TL(TL(cpring G2 x2))))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CPRING_ECPK; MAP; KCFK_HEAD; CONS_11; HYPERMAP_LEMMA] THEN
  MATCH_MP_TAC MAP_EQ THEN REWRITE_TAC[GSYM ALL_MEM] THEN
  X_GEN_TAC `z:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC KCFK_OLD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEM_CPRING_IN_DART THEN EXISTS_TAC `x2:num` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEM_TL_TL_IMP THEN
  ASM_MESON_TAC[CPRING_NONEMPTY; TL_CPRING_NONEMPTY; LONG_IMP_PROPER]);;

let KCFK_COLORING = prove
 (`!(G2:(num)hypermap) x2 h c0.
     coloring G2 h /\ x2 IN dart G2 /\ long_cpring G2 x2 /\
     ~(h(face_map G2 (edge_map G2 x2)) = h(node_map G2 x2))
     ==> coloring (ecpK G2 x2) (kcfK G2 x2 h c0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[coloring] THEN CONJ_TAC THEN
  X_GEN_TAC `u:num` THENL
   [ASM_SIMP_TAC[DART_ECPK_CASES; FINITE_DART; NODE_MAP_PERMUTES] THEN
    STRIP_TAC THEN TRY(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_SIMP_TAC[EDGE_ECPK_AB; KCFK_HEAD; KCFK_B; KCFK_OLD; EDGE_ECPK_OLD;
                 EDGE_IN_DART; FINITE_DART; NODE_MAP_PERMUTES] THEN
    ASM_MESON_TAC[coloring];
    DISCH_TAC THEN MATCH_MP_TAC KCFK_FACE THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The A step (Gonthier cfcolor.v cpcolor1A_correct): KUA_COLORING (k itself *)
(* colours ecpA when k(node x2) = k(face(edge x2))), DK_PRIME_A (the merged  *)
(* ring trace) and CPCOLOR1A_CORRECT; then the K step: ADJ_NODE_FEDGE_ECPK   *)
(* (the K-created adjacency refutes e1 = e2), DK_PRIME_K, the membership     *)
(* bridge CPCOLOR1K_MEM_BRIDGE and CPCOLOR1K_CORRECT.                        *)
(* ------------------------------------------------------------------------- *)

let TLTL_FTRACE_3 = prove
 (`!a x b rest. TL(TL(ftrace (CONS a (CONS x (CONS b rest))))) = ptrace (CONS b
   (APPEND rest [a]))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ftrace; rot_list; num_CONV `1`; drop_list; take_list;
    NOT_CONS_NIL; TL; HD; APPEND] THEN
  REWRITE_TAC[trace_DEF; NOT_CONS_NIL; LAST_APPEND; LAST; APPEND_EQ_NIL] THEN
  REWRITE_TAC[ptrace; TL]);;

let FTRACE_CONS_NONNIL = prove
 (`!c t. ~(ftrace(CONS c t) = [])`,
  REPEAT GEN_TAC THEN
    REWRITE_TAC[GSYM LENGTH_EQ_NIL; LENGTH_FTRACE; LENGTH; NOT_SUC]);;

let LONG_TRACE_MERGE = prove
 (`!ka kx kb rest.
    ka = kb
    ==> ftrace (CONS kb rest) = TL(TL(ftrace (CONS ka (CONS kx (CONS kb
      rest)))))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FTRACE_CONS1; TLTL_FTRACE_3]);;

(* CpA branch of cpcolor1 (its clause in the definition).                    *)

let CPCOLOR1_A = prove
 (`!f et. cpcolor1 CpA f et =
    (if LENGTH et < 2 then CtreeEmpty
     else if HD et = HD(TL et) then f(if TL(TL et) = [] then et else TL(TL et))
       else CtreeEmpty)`,
  REWRITE_TAC[cpcolor1]);;

let CP_TR0_CONS_A = prove
 (`!et0 cp1 cp2 k0. cp_tr0 et0 (CONS CpA cp1) cp2 k0 <=> cp_tr0 et0 cp1 (CONS
   CpA cp2) k0`,
  REWRITE_TAC[cp_tr0; CATREV_CP_CONS]);;

(* long-case trace backbone (rest2 possibly [])                              *)

let DK_A_LONG_TEST = prove
 (`!(k:num->color) a x2nd b rest2.
     k a = k b
     ==> ftrace (MAP k (CONS b rest2)) =
         (if TL(TL(ftrace(MAP k (CONS a (CONS x2nd (CONS b rest2)))))) = []
          then ftrace(MAP k (CONS a (CONS x2nd (CONS b rest2))))
          else TL(TL(ftrace(MAP k (CONS a (CONS x2nd (CONS b rest2)))))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MAP] THEN
  MP_TAC(ISPECL [`(k:num->color) a`; `(k:num->color) x2nd`; `(k:num->color) b`;
                 `MAP (k:num->color) rest2`] LONG_TRACE_MERGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MAP] THEN DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN
    ASSUME_TAC th) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN ASM_REWRITE_TAC[FTRACE_CONS_NONNIL]);;

(* When k(node x2) = k(face(edge x2)), k itself colours ecpA G2 x2 (same     *)
(* dart set; Gonthier's k'col and k'F).                                      *)

let KUA_COLORING = prove
 (`!(G2:(num)hypermap) x2 k.
     coloring G2 k /\ x2 IN dart G2 /\
     k(node_map G2 x2) = k(face_map G2 (edge_map G2 x2))
     ==> coloring (ecpA G2 x2) k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP ECPA_COMPONENTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [coloring]) THEN
  ASM_REWRITE_TAC[coloring; ecpA_edge; ecpA_face] THEN
  CONJ_TAC THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
  ASM_MESON_TAC[CFACE_COLORING; COLORING_NODE; CFT_EDGE_NODE;
                EDGE_MAP_IN_DART; NODE_MAP_IN_DART]);;

(* Its ring trace on ecpA is TL(TL et), or et itself for a 2-ring.           *)

let DK_PRIME_A = prove
 (`!(G2:(num)hypermap) x2 k.
     x2 IN dart G2 /\ proper_cpring G2 x2 /\
     k(node_map G2 x2) = k(face_map G2 (edge_map G2 x2))
     ==> ftrace (MAP k (cpring (ecpA G2 x2) (ecpA_pt G2 x2))) =
         (if TL(TL(ftrace(MAP k (cpring G2 x2)))) = []
          then ftrace(MAP k (cpring G2 x2))
          else TL(TL(ftrace(MAP k (cpring G2 x2)))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CPRING_ECPA] THEN
  ASM_CASES_TAC `long_cpring G2 (x2:num)` THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_LONG_CPRING) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[TL] THEN MATCH_MP_TAC DK_A_LONG_TEST THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `TL(TL(ftrace(MAP (k:num->color) (cpring G2 x2)))) = []`
      (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_PROPER_CPRING) THEN
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] LONG_CPRING_TLTL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
    REWRITE_TAC[MAP; FTRACE_CONS2; APPEND; ptrace; TL]]);;

(* ------------------------------------------------------------------------- *)
(* CPCOLOR1A_CORRECT (Gonthier cfcolor.v cpcolor1A_correct).  The CpA test   *)
(* HD et = HD(TL et) is k(node x2) = k(face(edge x2)); if it holds, k itself *)
(* colours ecpA (KUA_COLORING) with ring trace DK_PRIME_A and the same dart  *)
(* set; otherwise no colouring of the final map agrees with k on G2, since   *)
(* the merged faces of ecpA (ECPA_MERGE) force k0(node x2) = k0(face(edge    *)
(* x2)).                                                                     *)
(* ------------------------------------------------------------------------- *)

let CPCOLOR1A_CORRECT = prove
 (`!et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS CpA cp2))) k'
           ==> cp_extcol et0 cp1 (CONS CpA cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS CpA cp1) cp2 (cpcolor1 CpA f) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G2 = FST(cpmap cp2)` THEN ABBREV_TAC `x2 = SND(cpmap cp2)` THEN
  SUBGOAL_THEN `(x2:num) IN dart(G2:(num)hypermap)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G2"; "x2"] THEN REWRITE_TAC[CPMAP_PT_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `proper_cpring (G2:(num)hypermap) x2` ASSUME_TAC THENL
   [REWRITE_TAC[proper_cpring] THEN ASM_MESON_TAC[COLORING_NODE]; ALL_TAC] THEN
  SUBGOAL_THEN `FST(cpmap(CONS CpA cp2)) = ecpA (G2:(num)hypermap) x2 /\
                SND(cpmap(CONS CpA cp2)) = ecpA_pt G2 x2`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[CPMAP_CONS_A]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    RING_TRACE_HEADS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `et = ftrace (MAP (k:num->color) (cpring (G2:(num)hypermap) x2))`
  THEN STRIP_TAC THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_CONS; CP_TR0_CONS_A] THEN
  ASM_REWRITE_TAC[CPCOLOR1_A; GSYM NOT_LE; ADDC_MID_CANCEL_EQ] THEN
  COND_CASES_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th)
                            then MP_TAC(SPEC `k:num->color` th) else NO_TAC)
    THEN ASM_SIMP_TAC[KUA_COLORING] THEN
    REWRITE_TAC[cp_extcol] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`] DK_PRIME_A)
    THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[ECPA_DART];
    REWRITE_TAC[ctree_proper; CTREE_MEM_EMPTY; NOT_EXISTS_THM] THEN
    X_GEN_TAC `k0:num->color` THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    MATCH_MP_TAC(TAUT `(a /\ c ==> F) ==> (~a \/ ~b) \/ ~c`) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(k0:num->color) (node_map G2 x2) =
                  k0 (face_map G2 (edge_map G2 x2))` MP_TAC THENL
     [MATCH_MP_TAC CFACE_COLORING THEN
      EXISTS_TAC `ecpA (G2:(num)hypermap) x2` THEN
      ASM_SIMP_TAC[ECPA_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART;
                   ECPA_MERGE] THEN
      MP_TAC(ISPECL [`cp1:(cpstep)list`; `CONS CpA cp2`; `k0:num->color`]
        (REWRITE_RULE[cp_restrict] CP_RESTRICT_ANY)) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[NODE_MAP_IN_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART]]]);;

let ADJ_ECPN_CENTER_W0 = prove
 (`!(H:(num)hypermap) y v.
     y IN dart H /\ face_map H (edge_map H (face_map H (edge_map H y))) = v
     ==> adj (ecpN H y) y v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[adj; rlink; GSYM cface] THEN
  EXISTS_TAC `ecpN_pt (H:(num)hypermap)` THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `y:num`] FACE_ECPN_A) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `y:num`] FACE_ECPN_B_LONG) THEN
  MP_TAC(ISPECL [`H:(num)hypermap`; `y:num`] ECPN_FACE_B_SHORT) THEN
  ASM_CASES_TAC `long_cpring H (y:num)` THEN
  ASM_SIMP_TAC[EDGE_ECPN_AB; GSYM ecpN_pt] THEN REPEAT DISCH_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `v:num = y` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[nodeK; long_cpring]; ALL_TAC]] THEN
  CFACE_TAC[]);;

(* The K-merge adjacency (Gonthier adj_icpK, third disjunct, cfmap.v:922),   *)
(* unconditional: node x0 is adjacent to face (edge x0) in ecpK.  adj (ecpK) *)
(* = adj (ecpN (node x0)), then ADJ_ECPN_CENTER_W0 with w0 = face (edge      *)
(* (face (edge (node x0)))) = face (edge x0) by nodeK.                       *)

let ADJ_NODE_FEDGE_ECPK = prove
 (`!(H:(num)hypermap) x0.
     x0 IN dart H
     ==> adj (ecpK H x0) (node_map H x0) (face_map H (edge_map H x0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ECPK_ALT] THEN
  MATCH_MP_TAC ADJ_ECPN_CENTER_W0 THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART; FACE_MAP_IN_DART; EDGE_MAP_IN_DART] THEN
  REWRITE_TAC[nodeK]);;

let LONG_TRACE_MERGE_K = prove
 (`!ka kx kb rest.
    ftrace (CONS ka (CONS kb rest)) =
    CONS (addc ka kb) (TL(TL(ftrace (CONS ka (CONS kx (CONS kb rest))))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TLTL_FTRACE_3] THEN
  GEN_REWRITE_TAC (LAND_CONV) [FTRACE_CONS1] THEN
  REWRITE_TAC[APPEND; ptrace]);;

(* Colour-merge: addc(addc a x)(addc x b) = addc a b (the CpK e1 +c e2 =     *)
(* k(node) +c k(face(edge)) identity).                                       *)

(* CpK branch of cpcolor1 (cfcolor.ml:89): Empty if e1=e2, else merge.       *)

let CPCOLOR1_K = prove
 (`!f et. cpcolor1 CpK f et =
    (if LENGTH et < 2 then CtreeEmpty
     else if HD et = HD(TL et) then CtreeEmpty
     else f (CONS (addc (HD et) (HD(TL et))) (TL(TL et))))`,
  REWRITE_TAC[cpcolor1]);;

let CP_TR0_CONS_K = prove
 (`!et0 cp1 cp2 k0. cp_tr0 et0 (CONS CpK cp1) cp2 k0 <=> cp_tr0 et0 cp1 (CONS
   CpK cp2) k0`,
  REWRITE_TAC[cp_tr0; CATREV_CP_CONS]);;

(* Merged ecpK ring trace of kcfK = CONS (addc(HD et)(HD(TL et))) (TL(TL     *)
(* et)).                                                                     *)

let DK_PRIME_K = prove
 (`!(G2:(num)hypermap) x2 k (c0:color).
     coloring G2 k /\ x2 IN dart G2 /\ long_cpring G2 x2
     ==> ftrace (MAP (kcfK G2 x2 k c0) (cpring (ecpK G2 x2) (ecpK_pt G2 x2))) =
         CONS (addc (HD (ftrace (MAP k (cpring G2 x2))))
                    (HD(TL (ftrace (MAP k (cpring G2 x2))))))
              (TL(TL (ftrace (MAP k (cpring G2 x2)))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `proper_cpring G2 (x2:num)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LONG_IMP_PROPER]; ALL_TAC] THEN
  ASM_SIMP_TAC[KCFK_MAP_CPRING_ECPK; HEAD_FTRACE_MAP_CPRING;
               SECOND_FTRACE_MAP_CPRING; ADDC_CANCEL] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`] HEAD_LONG_CPRING) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `RT3 = TL(TL(TL(cpring G2 (x2:num))))` THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[TL; MAP] THEN
  MATCH_ACCEPT_TAC LONG_TRACE_MERGE_K);;

(* Every dart of ecpK is cofacial with an old dart (the three dart classes:  *)
(* ecpN_pt -> node x2, SND nd2 -> face(edge x2), old -> itself).             *)

let CPCOLOR1K_MEM_BRIDGE = prove
 (`!cp1 cp2 (G2:(num)hypermap) x2 k (c0:color) et0.
     coloring G2 k /\ x2 IN dart G2 /\ long_cpring G2 x2 /\
     FST(cpmap(CONS CpK cp2)) = ecpK G2 x2
     ==> ((?k0. (coloring (FST(cpmap(catrev_cp cp1 (CONS CpK cp2)))) k0 /\
                 cp_tr0 et0 cp1 (CONS CpK cp2) k0) /\
                (!x. x IN dart(ecpK G2 x2) ==> k0 x = kcfK G2 x2 k c0 x)) <=>
          (?k0. (coloring (FST(cpmap(catrev_cp cp1 (CONS CpK cp2)))) k0 /\
                 cp_tr0 et0 cp1 (CONS CpK cp2) k0) /\
                (!x. x IN dart G2 ==> k0 x = k x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k0:num->color` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THENL
   [SUBGOAL_THEN `x IN dart(ecpK G2 x2)` ASSUME_TAC THENL
     [MATCH_MP_TAC DART_SUBSET_ECPK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC KCFK_OLD THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `x:num`] FBAND_ECPK) THEN
    ASM_REWRITE_TAC[HYPERMAP_LEMMA] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `kcfK G2 x2 k c0 x = k z` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `c0:color`;
       `x:num`; `z:num`] KCFK_CFACE) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(k:num->color) z = k0 z` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`REVERSE(cp1:(cpstep)list)`; `CONS CpK (cp2:(cpstep)list)`;
                   `k0:num->color`; `x:num`; `z:num`] GCOL_CFACE_GEN) THEN
    REWRITE_TAC[GSYM catrev_cp] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* CPCOLOR1K_CORRECT (Gonthier cfcolor.v cpcolor1K_correct).  The CpK test   *)
(* HD et = HD(TL et), i.e. k(node x2) = k(face(edge x2)), gives CtreeEmpty,  *)
(* refuted by the K-created adjacency (ADJ_NODE_FEDGE_ECPK); otherwise the   *)
(* ring is long and kcfK G2 x2 k Color0 colours ecpK (KCFK_COLORING) with    *)
(* the merged ring trace DK_PRIME_K; CPCOLOR1K_MEM_BRIDGE moves the          *)
(* agreement from dart(ecpK) to dart G2.                                     *)
(* ------------------------------------------------------------------------- *)

let CPCOLOR1K_CORRECT = prove
 (`!et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS CpK cp2))) k'
           ==> cp_extcol et0 cp1 (CONS CpK cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS CpK cp1) cp2 (cpcolor1 CpK f) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `G2 = FST(cpmap cp2)` THEN ABBREV_TAC `x2 = SND(cpmap cp2)` THEN
  SUBGOAL_THEN `(x2:num) IN dart(G2:(num)hypermap)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G2"; "x2"] THEN REWRITE_TAC[CPMAP_PT_IN_DART];
    ALL_TAC] THEN
  SUBGOAL_THEN `FST(cpmap(CONS CpK cp2)) = ecpK (G2:(num)hypermap) x2 /\
                SND(cpmap(CONS CpK cp2)) = ecpK_pt G2 x2`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[CPMAP_CONS_K]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`]
    RING_TRACE_HEADS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `et = ftrace (MAP (k:num->color) (cpring (G2:(num)hypermap) x2))`
  THEN STRIP_TAC THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_CONS; CP_TR0_CONS_K] THEN
  ASM_REWRITE_TAC[CPCOLOR1_K; GSYM NOT_LE; ADDC_MID_CANCEL_EQ] THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[ctree_proper; CTREE_MEM_EMPTY; NOT_EXISTS_THM] THEN
    X_GEN_TAC `k0:num->color` THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    MATCH_MP_TAC(TAUT `(a /\ c ==> F) ==> (~a \/ ~b) \/ ~c`) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `coloring (ecpK (G2:(num)hypermap) x2) k0` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`cp1:(cpstep)list`; `CONS CpK cp2`; `k0:num->color`]
        (REWRITE_RULE[cp_restrict] CP_RESTRICT_ANY)) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ecpK (G2:(num)hypermap) x2`; `k0:num->color`;
      `node_map G2 (x2:num)`; `face_map G2 (edge_map G2 (x2:num))`]
      ADJ_COLORING) THEN
    ASM_SIMP_TAC[EDGE_MAP_PERMUTES; NODE_MAP_IN_DART; FACE_MAP_IN_DART;
                 EDGE_MAP_IN_DART; DART_SUBSET_ECPK; ADJ_NODE_FEDGE_ECPK];
    SUBGOAL_THEN `long_cpring G2 (x2:num)` ASSUME_TAC THENL
     [REWRITE_TAC[long_cpring] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th)
       then MP_TAC(SPEC `kcfK (G2:(num)hypermap) x2 k Color0` th) else NO_TAC)
    THEN ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC KCFK_COLORING THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cp_extcol] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `Color0`]
      DK_PRIME_K) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`cp1:(cpstep)list`; `cp2:(cpstep)list`; `G2:(num)hypermap`;
      `x2:num`; `k:num->color`; `Color0`; `et0:(color)list`]
      CPCOLOR1K_MEM_BRIDGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The cpmap0 membership bridges for the CpU / CpY cases of cpcolor0.  Both  *)
(* follow from CPCOLOR1U_MEM_GEN / CPCOLOR1Y_MEM_GEN with Q k0 taken as k0   *)
(* is a colouring of the final map with the required ring trace: the branch  *)
(* colourings of cpcolor0 are affine recolourings (c +c permc h) of the      *)
(* kuU / kuY colourings of the _MEM_GEN disjunctions (KUU_AFFINE, KUY_AFFINE *)
(* and the congruences KUU_CONG / KUY_CONG), and Q is invariant under affine *)
(* recolouring (GCOL_PERM), so EXISTS_RECOLOUR identifies the disjuncts.     *)
(* The transposition fixing the two base colours a, a +c Color1 is           *)
(* y |-> (a +c permc Eperm132 a) +c permc Eperm132 y (TSW_FIX, TSW_INVOL).   *)
(* ------------------------------------------------------------------------- *)

let KEXT_AFFINE = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k c0 c h u.
     addc c (permc h (kext G' G2 k c0 u)) =
     kext G' G2 (\x. addc c (permc h (k x))) (addc c (permc h c0)) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kext] THEN COND_CASES_TAC THEN
  REWRITE_TAC[]);;

let KEXT_CONG = prove
 (`!(G':(num)hypermap) (G2:(num)hypermap) k k' c u.
     (!x. x IN dart G2 ==> k x = k' x)
     ==> kext G' G2 k c u = kext G' G2 k' c u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kext] THEN COND_CASES_TAC THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SELECT_RULE) THEN SIMP_TAC[]);;

let KUU_AFFINE = prove
 (`!(G2:(num)hypermap) x2 k c h e u.
     addc c (permc h (kuU G2 x2 k e u)) =
     kuU G2 x2 (\x. addc c (permc h (k x))) (permc h e) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[KUU_KEXT; KEXT_AFFINE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PERMC_ADDC] THEN
  MESON_TAC[ADDC_ASSOC; ADDC_COMM]);;

let KUU_PERMC = prove
 (`!(G2:(num)hypermap) x2 k h e u.
     permc h (kuU G2 x2 k e u) = kuU G2 x2 (permc h o k) (permc h e) u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `Color0`;
    `h:edge_perm`; `e:color`; `u:num`] KUU_AFFINE) THEN
  REWRITE_TAC[ADDC_0]);;

let KUU_CONG = prove
 (`!(G2:(num)hypermap) x2 k k' e u.
     x2 IN dart G2 /\ (!x. x IN dart G2 ==> k x = k' x)
     ==> kuU G2 x2 k e u = kuU G2 x2 k' e u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUU_KEXT] THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN MATCH_MP_TAC KEXT_CONG THEN
  ASM_REWRITE_TAC[]);;

let KUY_AFFINE = prove
 (`!(G2:(num)hypermap) x2 k c h p p' u.
     (!z. permc h (permc p z) = permc p' (permc h z))
     ==> addc c (permc h (kuY G2 x2 k p u)) =
         kuY G2 x2 (\x. addc c (permc h (k x))) p' u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT; KEXT_AFFINE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[ADDC_SYM_CANCEL] THEN
  REWRITE_TAC[GSYM PERMC_ADDC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
  REWRITE_TAC[PERMC_ADDC; ADDC_ASSOC]);;

let KUY_PERMC = prove
 (`!(G2:(num)hypermap) x2 k h p p' u.
     (!z. permc h (permc p z) = permc p' (permc h z))
     ==> permc h (kuY G2 x2 k p u) = kuY G2 x2 (permc h o k) p' u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `x2:num`; `k:num->color`; `Color0`;
    `h:edge_perm`; `p:edge_perm`; `p':edge_perm`; `u:num`] KUY_AFFINE) THEN
  ASM_REWRITE_TAC[ADDC_0]);;

let KUY_CONG = prove
 (`!(G2:(num)hypermap) x2 k k' p u.
     x2 IN dart G2 /\ (!x. x IN dart G2 ==> k x = k' x)
     ==> kuY G2 x2 k p u = kuY G2 x2 k' p u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[KUY_KEXT] THEN
  ASM_SIMP_TAC[NODE_MAP_IN_DART] THEN MATCH_MP_TAC KEXT_CONG THEN
  ASM_REWRITE_TAC[]);;

let EXISTS_RECOLOUR = prove
 (`!(Q:(num->color)->bool) (Fc:color->color) Fi (g:num->color) (D:num->bool).
     (!k0. Q k0 ==> Q (\x. Fc (k0 x))) /\ (!k0. Q k0 ==> Q (\x. Fi (k0 x))) /\
     (!c. Fi (Fc c) = c)
     ==> ((?k0. Q k0 /\ (!x. x IN D ==> k0 x = Fc (g x))) <=>
          (?k0. Q k0 /\ (!x. x IN D ==> k0 x = g x)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `\x:num. (Fi:color->color) (k0 x)`;
    EXISTS_TAC `\x:num. (Fc:color->color) (k0 x)`] THEN
  ASM_SIMP_TAC[]);;

let TSW_FIX = prove
 (`!a b cc. addc a b = Color1 /\ (cc = a \/ cc = b)
            ==> addc (addc a (permc Eperm132 a)) (permc Eperm132 cc) = cc`,
  MATCH_MP_TAC color_INDUCT THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC color_INDUCT THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC color_INDUCT THEN
  REWRITE_TAC[addc_DEF; permc_DEF; distinctness "color"]);;

let TSW_INVOL = prove
 (`!a y. addc (addc a (permc Eperm132 a))
              (permc Eperm132 (addc (addc a (permc Eperm132 a))
                                    (permc Eperm132 y))) = y`,
  MATCH_MP_TAC color_INDUCT THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[addc_DEF; permc_DEF]);;

let PERMC_132_231_312 = prove
 (`!z. permc Eperm132 (permc Eperm231 z) = permc Eperm312 (permc Eperm132 z)`,
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[permc_DEF]);;

let PERMC_231_312_INV = prove
 (`!z. permc Eperm231 (permc Eperm312 z) = z`,
  MATCH_MP_TAC color_INDUCT THEN REWRITE_TAC[permc_DEF]);;

let CPU_BRIDGE_Q = prove
 (`!(Q:(num->color)->bool) kk p.
     coloring cpmap0 kk /\ p IN dart cpmap0 /\
     addc (kk (node_map cpmap0 p)) (kk p) = Color1 /\
     (!k0. Q k0 ==> coloring (ecpU cpmap0 p) k0) /\
     (!k0 c h. Q k0 ==> Q (\x. addc c (permc h (k0 x))))
     ==> (((?k0. Q k0 /\
                (!x. x IN dart(ecpU cpmap0 p)
                     ==> k0 x = kuU cpmap0 p (permc Eperm213 o kk) Color1 x))
           \/
           (?k0. Q k0 /\
                (!x. x IN dart(ecpU cpmap0 p)
                     ==> k0 x = kuU cpmap0 p kk Color1 x))) <=>
          (?k0. Q k0 /\ (!x. x IN dart cpmap0 ==> k0 x = kk x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`cpmap0`; `p:num`; `kk:num->color`; `Q:(num->color)->bool`]
    CPCOLOR1U_MEM_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `!k0 h. Q k0 ==> Q (\x:num. permc h (k0 x))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k0:num->color`; `Color0`; `h:edge_perm`])
    THEN ASM_REWRITE_TAC[ADDC_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. kuU cpmap0 p (permc Eperm213 o kk) Color1 x =
                    permc Eperm213 (kuU cpmap0 p kk Color2 x)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[KUU_PERMC; permc_DEF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:(num->color)->bool`; `permc Eperm213`; `permc Eperm213`;
    `kuU cpmap0 p kk Color2`; `dart(ecpU cpmap0 p)`] EXISTS_RECOLOUR) THEN
  ASM_SIMP_TAC[PERMC_213_INVOL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!x. kuU cpmap0 p kk Color3 x =
        addc (addc (kk (node_map cpmap0 p))
                   (permc Eperm132 (kk (node_map cpmap0 p))))
             (permc Eperm132 (kuU cpmap0 p kk Color2 x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[KUU_AFFINE; permc_DEF] THEN
    MATCH_MP_TAC KUU_CONG THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TSW_FIX THEN EXISTS_TAC `(kk:num->color) p` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:num`; `x:num`] CPMAP0_DART_CASES) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:(num->color)->bool`;
    `\y. addc (addc (kk (node_map cpmap0 p))
                    (permc Eperm132 (kk (node_map cpmap0 p))))
              (permc Eperm132 y)`;
    `\y. addc (addc (kk (node_map cpmap0 p))
                    (permc Eperm132 (kk (node_map cpmap0 p))))
              (permc Eperm132 y)`;
    `kuU cpmap0 p kk Color2`; `dart(ecpU cpmap0 p)`] EXISTS_RECOLOUR) THEN
  ASM_SIMP_TAC[TSW_INVOL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DISJ_ACI]);;

let CPY_BRIDGE_Q = prove
 (`!(Q:(num->color)->bool) kk p.
     coloring cpmap0 kk /\ p IN dart cpmap0 /\
     addc (kk (node_map cpmap0 p)) (kk p) = Color1 /\
     (!k0. Q k0 ==> coloring (ecpY cpmap0 p) k0) /\
     (!k0 c h. Q k0 ==> Q (\x. addc c (permc h (k0 x))))
     ==> ((?k0. Q k0 /\
                (!x. x IN dart(ecpY cpmap0 p)
                     ==> k0 x = kuY cpmap0 p (permc Eperm312 o kk) Eperm231 x))
          <=> (?k0. Q k0 /\ (!x. x IN dart cpmap0 ==> k0 x = kk x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `proper_cpring cpmap0 p` ASSUME_TAC THENL
   [UNDISCH_TAC `p IN dart cpmap0` THEN
    REWRITE_TAC[proper_cpring; CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[swap] THEN
    CONV_TAC(DEPTH_CONV NUM_REL_CONV) THEN REWRITE_TAC[ARITH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cpmap0`; `p:num`; `kk:num->color`; `Q:(num->color)->bool`]
    CPCOLOR1Y_MEM_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `!k0 h. Q k0 ==> Q (\x:num. permc h (k0 x))` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k0:num->color`; `Color0`; `h:edge_perm`])
    THEN ASM_REWRITE_TAC[ADDC_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. kuY cpmap0 p (permc Eperm312 o kk) Eperm231 x =
                    permc Eperm312 (kuY cpmap0 p kk Eperm231 x)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC KUY_PERMC THEN
    REWRITE_TAC[PERMC_312_231_COMM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:(num->color)->bool`; `permc Eperm312`; `permc Eperm231`;
    `kuY cpmap0 p kk Eperm231`; `dart(ecpY cpmap0 p)`] EXISTS_RECOLOUR) THEN
  ASM_SIMP_TAC[PERMC_231_312_INV] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!x. kuY cpmap0 p kk Eperm312 x =
        addc (addc (kk (node_map cpmap0 p))
                   (permc Eperm132 (kk (node_map cpmap0 p))))
             (permc Eperm132 (kuY cpmap0 p kk Eperm231 x))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`cpmap0`; `p:num`; `kk:num->color`;
      `addc (kk (node_map cpmap0 p))
            (permc Eperm132 (kk (node_map cpmap0 p)))`;
      `Eperm132`; `Eperm231`; `Eperm312`; `x:num`] KUY_AFFINE) THEN
    REWRITE_TAC[PERMC_132_231_312] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC KUY_CONG THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC TSW_FIX THEN EXISTS_TAC `(kk:num->color) p` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:num`; `x:num`] CPMAP0_DART_CASES) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:(num->color)->bool`;
    `\y. addc (addc (kk (node_map cpmap0 p))
                    (permc Eperm132 (kk (node_map cpmap0 p))))
              (permc Eperm132 y)`;
    `\y. addc (addc (kk (node_map cpmap0 p))
                    (permc Eperm132 (kk (node_map cpmap0 p))))
              (permc Eperm132 y)`;
    `kuY cpmap0 p kk Eperm231`; `dart(ecpY cpmap0 p)`] EXISTS_RECOLOUR) THEN
  ASM_SIMP_TAC[TSW_INVOL] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let CPU_MEM_BRIDGE_CF = prove
 (`!cp' kk p cp2 et0.
   coloring cpmap0 kk /\ p IN dart cpmap0 /\
   FST(cpmap cp2) = cpmap0 /\ SND(cpmap cp2) = p /\
   addc (kk (node_map cpmap0 p)) (kk p) = Color1
   ==> (((?k0. (coloring (FST(cpmap(catrev_cp cp' (CONS CpU cp2)))) k0 /\
                cp_tr0 et0 cp' (CONS CpU cp2) k0) /\
               (!x. x IN dart(ecpU cpmap0 p)
                    ==> k0 x = kuU cpmap0 p (permc Eperm213 o kk) Color1 x)) \/
         (?k0. (coloring (FST(cpmap(catrev_cp cp' (CONS CpU cp2)))) k0 /\
                cp_tr0 et0 cp' (CONS CpU cp2) k0) /\
               (!x. x IN dart(ecpU cpmap0 p)
                    ==> k0 x = kuU cpmap0 p kk Color1 x))) <=>
        (?k0. (coloring (FST(cpmap(catrev_cp cp' (CONS CpU cp2)))) k0 /\
               cp_tr0 et0 cp' (CONS CpU cp2) k0) /\
              (!x. x IN dart cpmap0 ==> k0 x = kk x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k0:num->color.
      coloring (FST(cpmap(catrev_cp cp' (CONS CpU cp2)))) k0 /\
      cp_tr0 et0 cp' (CONS CpU cp2) k0`; `kk:num->color`; `p:num`]
    CPU_BRIDGE_Q) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `k0:num->color` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cp':(cpstep)list`; `CONS CpU cp2`; `k0:num->color`]
        (REWRITE_RULE[cp_restrict] CP_RESTRICT_ANY)) THEN
      ASM_REWRITE_TAC[CPMAP_CONS_U; FST];
      REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC GCOL_PERM];
    DISCH_THEN ACCEPT_TAC]);;

let CPY_MEM_BRIDGE_CF = prove
 (`!cp' kk p cp2 et0.
   coloring cpmap0 kk /\ p IN dart cpmap0 /\
   FST(cpmap cp2) = cpmap0 /\ SND(cpmap cp2) = p /\
   addc (kk (node_map cpmap0 p)) (kk p) = Color1
   ==> ((?k0. (coloring (FST(cpmap(catrev_cp cp' (CONS CpY cp2)))) k0 /\
               cp_tr0 et0 cp' (CONS CpY cp2) k0) /\
              (!x. x IN dart(ecpY cpmap0 p)
                   ==> k0 x = kuY cpmap0 p (permc Eperm312 o kk) Eperm231 x))
        <=> (?k0. (coloring (FST(cpmap(catrev_cp cp' (CONS CpY cp2)))) k0 /\
                   cp_tr0 et0 cp' (CONS CpY cp2) k0) /\
                  (!x. x IN dart cpmap0 ==> k0 x = kk x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k0:num->color.
      coloring (FST(cpmap(catrev_cp cp' (CONS CpY cp2)))) k0 /\
      cp_tr0 et0 cp' (CONS CpY cp2) k0`; `kk:num->color`; `p:num`]
    CPY_BRIDGE_Q) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `k0:num->color` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cp':(cpstep)list`; `CONS CpY cp2`; `k0:num->color`]
        (REWRITE_RULE[cp_restrict] CP_RESTRICT_ANY)) THEN
      ASM_REWRITE_TAC[CPMAP_CONS_Y; FST];
      REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC GCOL_PERM];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The R' step (Gonthier cpcolor1R'_correct): ecpRr is the identity map and  *)
(* the pointer moves back one node, so the ring trace rotates right by one;  *)
(* a colouring has a ring of length >= 2 (COLORING_PROPER_CPRING), which     *)
(* passes the length guard of cpcolor1 CpRr.                                 *)
(* ------------------------------------------------------------------------- *)

let CPMAP_CONS_RR = prove
 (`!cp2. cpmap (CONS CpRr cp2) =
         (FST(cpmap cp2), ecpRr_pt (FST(cpmap cp2)) (SND(cpmap cp2)))`,
  REWRITE_TAC[CPMAP_CONS_PAIR; cpstep_apply; ECPRR_EQ]);;

let FTRACE_CPRING_ECPRR = prove
 (`!(G2:(num)hypermap) x2 k.
     coloring G2 k /\ x2 IN dart G2
     ==> ~(LENGTH(ftrace (MAP k (cpring G2 x2))) <= 1) /\
         ftrace (MAP k (cpring G2 (ecpRr_pt G2 x2))) =
         rotr_list 1 (ftrace (MAP k (cpring G2 x2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`G2:(num)hypermap`; `k:num->color`; `x2:num`]
    COLORING_PROPER_CPRING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[LENGTH_FTRACE; LENGTH_MAP; SIZE_CPRING; rotr_list; ecpRr_pt;
               FTRACE_CPRING_ECPR_ROT] THEN
  ASM_ARITH_TAC);;

let CPCOLOR1RR_CORRECT = prove
 (`!et0 cp1 cp2 f k.
     (!k'. coloring (FST(cpmap(CONS CpRr cp2))) k'
           ==> cp_extcol et0 cp1 (CONS CpRr cp2) f k') /\
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 (CONS CpRr cp1) cp2 (cpcolor1 CpRr f) k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num->color` o check(is_forall o concl)) THEN
  REWRITE_TAC[cp_extcol; cp_tr0; CATREV_CP_CONS; cpcolor1; CPMAP_CONS_RR;
              FST; SND] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`FST(cpmap cp2)`; `SND(cpmap cp2)`; `k:num->color`]
    FTRACE_CPRING_ECPRR) THEN
  ASM_REWRITE_TAC[CPMAP_PT_IN_DART] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[th]) SUBST1_TAC) THEN
  DISCH_THEN ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The induction over an arbitrary program (Gonthier cpcolor1_correct):      *)
(* seven-way dispatch on the step; CP_RESTRICT_ANY supplies the restriction  *)
(* hypothesis of the U/Y/H step lemmas.                                      *)
(* ------------------------------------------------------------------------- *)

let CPCOLOR1_CORRECT = prove
 (`!cp1 cp2 (k:num->color) et0.
     coloring (FST(cpmap cp2)) k
     ==> cp_extcol et0 cp1 cp2 (ITLIST cpcolor1 cp1 cpbranch) k`,
  ONCE_REWRITE_TAC[MESON[]
   `(!cp1 cp2 k et0. (P:(cpstep)list->(cpstep)list->(num->color)->(color)list
                       ->bool) cp1 cp2 k et0) <=>
    (!cp1. (!cp2 k et0. P cp1 cp2 k et0))`] THEN
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ITLIST] THEN
    MATCH_MP_TAC CPBRANCH_CORRECT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:cpstep` THEN X_GEN_TAC `cp1:(cpstep)list` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ITLIST] THEN
  SUBGOAL_THEN `!k'. coloring (FST(cpmap(CONS s cp2))) k'
                     ==> cp_extcol et0 cp1 (CONS s cp2)
                                   (ITLIST cpcolor1 cp1 cpbranch) k'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:cpstep` (cases "cpstep")) THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [MATCH_MP_TAC CPCOLOR1R_CORRECT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CPCOLOR1RR_CORRECT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CPCOLOR1Y_CORRECT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CPCOLOR1H_CORRECT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CPCOLOR1U_CORRECT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CPCOLOR1K_CORRECT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CPCOLOR1A_CORRECT THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The base-colouring gauge: the agreement with kbase on dart cpmap0 = {0,1} *)
(* can be dropped from the invariant, because every colouring of cpmap cp    *)
(* restricts to cpmap0 (GCOL_RESTRICT_GEN), where 0 and 1 are edge-adjacent  *)
(* and so get distinct colours, and an injective recolouring moving them to  *)
(* Color0, Color1 (COLOR_GAUGE_EXISTS) preserves the ring trace.             *)
(* ------------------------------------------------------------------------- *)

let AGREE_BRIDGE = prove
 (`!cp et.
     (?k0. (coloring (FST(cpmap cp)) k0 /\
            ttail et = eptrace (MAP k0 (rot_list 1 (cpring (FST(cpmap cp))
              (SND(cpmap cp)))))) /\
           (!x. x IN dart cpmap0 ==> k0 x = (if x = 1 then Color1 else
             Color0)))
     <=> (?k0. coloring (FST(cpmap cp)) k0 /\
               ttail et = eptrace (MAP k0 (rot_list 1 (cpring (FST(cpmap cp))
                 (SND(cpmap cp))))))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k0:num->color` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num->color` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((k0:num->color) 1 = k0 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cp:(cpstep)list`; `[]:(cpstep)list`; `k0:num->color`]
      GCOL_RESTRICT_GEN) THEN
    ASM_REWRITE_TAC[APPEND_NIL; CPMAP_NIL_FST] THEN
    REWRITE_TAC[coloring; CPMAP0_COMPONENTS] THEN
    DISCH_THEN(MP_TAC o SPEC `0` o CONJUNCT1) THEN
    REWRITE_TAC[IN_INSERT; swap] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(k0:num->color) 0`; `(k0:num->color) 1`]
    COLOR_GAUGE_EXISTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fc:color->color` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(Fc:color->color) o (k0:num->color)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COLORING_INJ_GEN THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[GSYM MAP_o] THEN
    MP_TAC(ISPECL [`Fc:color->color`;
      `MAP (k0:num->color) (rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap
        cp))))`] EPTRACE_INJ) THEN
    ASM_REWRITE_TAC[MAP_o] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CPMAP0_COMPONENTS; IN_INSERT; NOT_IN_EMPTY] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
    CONV_TAC(DEPTH_CONV NUM_REL_CONV) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* cpcolor0 (Gonthier cpcolor0_correct): induction over the leading steps,   *)
(* generalised to any cp2 with FST(cpmap cp2) = cpmap0 and a colouring kk of *)
(* cpmap0 with ring trace [Color1; Color1] at cp2's pointer, so that the CpR *)
(* case can recurse into cp2 (the trace rotates by FTRACE_CPRING_ECPR_ROT to *)
(* itself, ROT_LIST_C1C1).  CpY and CpU examine the colourings kuY / kuU of  *)
(* the extended base map (traces KPRIME_Y_TRACE, KPRIME_UA_TRACE,            *)
(* KPRIME_UB_TRACE, membership bridges CPY_MEM_BRIDGE_CF and                 *)
(* CPU_MEM_BRIDGE_CF); every other leading step folds cpcolor1 over the      *)
(* whole program from the base trace (CPCOLOR1_CORRECT).                     *)
(* ------------------------------------------------------------------------- *)

let CPCOLOR0_GEN = prove
 (`!cp cp2. FST(cpmap cp2) = cpmap0 /\ coloring cpmap0 kk /\
            ftrace (MAP kk (cpring cpmap0 (SND(cpmap cp2)))) = [Color1; Color1]
            ==> cp_extcol et0 cp cp2 (\l. cpcolor0 cp) kk`,
  MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[cpcolor0; ITLIST] THEN
    MP_TAC(ISPECL [`et0:(color)list`; `cp2:(cpstep)list`;
      `kk:num->color`] CPBRANCH_CORRECT) THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[cp_extcol]; ALL_TAC] THEN
  X_GEN_TAC `s:cpstep` THEN X_GEN_TAC `cp':(cpstep)list` THEN DISCH_TAC THEN
  X_GEN_TAC `cp2:(cpstep)list` THEN STRIP_TAC THEN
  ABBREV_TAC `p = SND(cpmap cp2)` THEN
  SUBGOAL_THEN `p IN dart cpmap0` ASSUME_TAC THENL
   [SUBGOAL_THEN `SND(cpmap cp2) IN dart(FST(cpmap cp2))` MP_TAC THENL
     [REWRITE_TAC[CPMAP_PT_IN_DART]; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `addc (kk (node_map cpmap0 p)) (kk p) = Color1` ASSUME_TAC
  THENL
   [MP_TAC(ISPECL [`cpmap0`; `p:num`; `kk:num->color`]
      HEAD_FTRACE_MAP_CPRING) THEN
    ASM_SIMP_TAC[PROPER_CPRING_CPMAP0; HD]; ALL_TAC] THEN
  ASM_CASES_TAC `?n. s = CpR n` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `cpcolor0 (CONS (CpR a) cp') = cpcolor0 cp'`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[cpcolor0] THEN MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `FST(cpmap (CONS (CpR a) cp2)) = cpmap0` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CPMAP_CONS_R; FST; ecpR]; ALL_TAC] THEN
    SUBGOAL_THEN `ftrace (MAP kk (cpring cpmap0 (SND(cpmap (CONS (CpR a)
      cp2))))) = [Color1; Color1]` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[CPMAP_CONS_R; SND] THEN
      MP_TAC(ISPECL [`cpmap0`; `p:num`; `a:num`; `kk:num->color`]
        FTRACE_CPRING_ECPR_ROT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[ROT_LIST_C1C1]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th)
       then MP_TAC(SPEC `CONS (CpR a) cp2` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[cp_extcol; cp_tr0; CATREV_CP_CONS] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `s = CpY` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `FST(cpmap(CONS CpY cp2)) = ecpY cpmap0 p /\
                  SND(cpmap(CONS CpY cp2)) = ecpY_pt cpmap0 p`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[CPMAP_CONS_Y]; ALL_TAC] THEN
    SUBGOAL_THEN `coloring (ecpY cpmap0 p) (kuY cpmap0 p (permc Eperm312 o kk)
      Eperm231)` ASSUME_TAC THENL
     [MATCH_MP_TAC KUY_COLORING THEN
      ASM_SIMP_TAC[COLORING_PERMC; PROPER_CPRING_CPMAP0]; ALL_TAC] THEN
    SUBGOAL_THEN `cpcolor0 (CONS CpY cp') = ITLIST cpcolor1 cp' cpbranch
      [Color1; Color2; Color3]` SUBST1_TAC THENL
     [REWRITE_TAC[cpcolor0]; ALL_TAC] THEN
    MP_TAC(ISPECL [`cp':(cpstep)list`; `CONS CpY cp2`;
      `kuY cpmap0 p (permc Eperm312 o kk) Eperm231`; `et0:(color)list`]
      CPCOLOR1_CORRECT) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[cp_extcol] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ftrace (MAP (kuY cpmap0 p (permc Eperm312 o kk) Eperm231)
      (cpring (ecpY cpmap0 p) (ecpY_pt cpmap0 p))) = [Color1; Color2; Color3]`
      (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC KPRIME_Y_TRACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cp_tr0; CATREV_CP_CONS] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_iff(concl th) then MP_TAC th else NO_TAC)
    THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`cp':(cpstep)list`; `kk:num->color`; `p:num`;
      `cp2:(cpstep)list`; `et0:(color)list`] CPY_MEM_BRIDGE_CF) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[cp_tr0; CATREV_CP_CONS]; ALL_TAC] THEN
  ASM_CASES_TAC `s = CpU` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `FST(cpmap(CONS CpU cp2)) = ecpU cpmap0 p /\
                  SND(cpmap(CONS CpU cp2)) = ecpU_pt cpmap0`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[CPMAP_CONS_U]; ALL_TAC] THEN
    SUBGOAL_THEN `coloring (ecpU cpmap0 p) (kuU cpmap0 p (permc Eperm213 o kk)
      Color1) /\ coloring (ecpU cpmap0 p) (kuU cpmap0 p kk Color1)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC KUU_COLORING THEN
      ASM_SIMP_TAC[COLORING_PERMC] THEN
      REWRITE_TAC[distinctness "color"]; ALL_TAC] THEN
    SUBGOAL_THEN `cpcolor0 (CONS CpU cp') = ctree_union (ITLIST cpcolor1 cp'
      cpbranch [Color1; Color1; Color2; Color2]) (ITLIST cpcolor1 cp' cpbranch
      [Color1; Color1; Color1; Color1])` SUBST1_TAC THENL
     [REWRITE_TAC[cpcolor0]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!k' et. coloring (ecpU cpmap0 p) k' /\
              ftrace (MAP k' (cpring (ecpU cpmap0 p) (ecpU_pt cpmap0))) = et
              ==> ctree_proper (cprsize(catrev_cp cp' (CONS CpU cp2)) - 2)
                    (ITLIST cpcolor1 cp' cpbranch et) /\
                  (ctree_mem (ITLIST cpcolor1 cp' cpbranch et) (ttail et0) <=>
                   (?k0. (coloring (FST(cpmap(catrev_cp cp' (CONS CpU cp2))))
                            k0 /\ cp_tr0 et0 cp' (CONS CpU cp2) k0) /\
                         (!x. x IN dart(ecpU cpmap0 p) ==> k0 x = k' x)))`
    ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      MP_TAC(ISPECL [`cp':(cpstep)list`; `CONS CpU cp2`; `k':num->color`;
        `et0:(color)list`] CPCOLOR1_CORRECT) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[cp_extcol] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cp_extcol] THEN ASM_REWRITE_TAC[CATREV_CP_CONS] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`kuU cpmap0 p (permc Eperm213 o kk) Color1`;
      `[Color1; Color1; Color2; Color2]`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`kuU cpmap0 p kk Color1`;
      `[Color1; Color1; Color1; Color1]`]) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`kk:num->color`; `p:num`] KPRIME_UA_TRACE) THEN
    MP_TAC(ISPECL [`kk:num->color`; `p:num`] KPRIME_UB_TRACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC
    THEN REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
    CONJ_TAC THENL [MATCH_MP_TAC CTREE_UNION_PROPER THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`cprsize(catrev_cp cp' (CONS CpU cp2)) - 2`;
      `ITLIST cpcolor1 cp' cpbranch [Color1; Color1; Color2; Color2]`;
      `ITLIST cpcolor1 cp' cpbranch [Color1; Color1; Color1; Color1]`;
      `ttail et0`] CTREE_MEM_UNION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CP_TR0_CONS_U] THEN
    MP_TAC(ISPECL [`cp':(cpstep)list`; `kk:num->color`; `p:num`;
      `cp2:(cpstep)list`; `et0:(color)list`] CPU_MEM_BRIDGE_CF) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cpcolor0 (CONS s cp') =
                ITLIST cpcolor1 (CONS s cp') cpbranch [Color1; Color1]`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(s = CpU)`; `~(s = CpY)`; `~(?n. s = CpR n)`] THEN
    STRUCT_CASES_TAC(SPEC `s:cpstep` (cases "cpstep")) THEN
    REWRITE_TAC[cpcolor0; distinctness "cpstep"; injectivity "cpstep"] THEN
    MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`CONS (s:cpstep) cp'`; `cp2:(cpstep)list`; `kk:num->color`;
    `et0:(color)list`] CPCOLOR1_CORRECT) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[cp_extcol] THEN ASM_REWRITE_TAC[]);;

let CPCOLOR0_CORRECT = prove
 (`!et0 cp. cp_extcol et0 cp [] (\l. cpcolor0 cp)
                               (\x:num. if x = 1 then Color1 else Color0)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`cp:(cpstep)list`; `[]:(cpstep)list`]
    (INST [`(\x:num. if x = 1 then Color1 else Color0)`,`kk:num->color`]
      CPCOLOR0_GEN)) THEN
  REWRITE_TAC[CPMAP_NIL_FST; CPMAP_NIL_SND; KBASE_COLORING; KBASE_TRACE]);;

(* ------------------------------------------------------------------------- *)
(* The correctness theorem (Gonthier ctree_mem_cpcolor) for every program,   *)
(* and its two specialisations used downstream.                              *)
(* ------------------------------------------------------------------------- *)

let CTREE_MEM_CPCOLOR_ALL = prove
 (`!cp et.
      ctree_mem (cpcolor cp) et <=>
      even_trace et /\
      ring_trace (FST(cpmap cp))
                 (rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp))))
                 (CONS (sumt et) et)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cpcolor; CTREE_MEM_CONS_ROT] THEN
  REWRITE_TAC[GSYM ctrace] THEN
  MP_TAC(ISPECL [`et:(color)list`; `REVERSE (cp:(cpstep)list)`]
    CPCOLOR0_CORRECT) THEN
  REWRITE_TAC[cp_extcol; CATREV_CP_NIL] THEN
  REWRITE_TAC[catrev_cp; APPEND_NIL; REVERSE_REVERSE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp))) = [])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ROT_LIST_NONEMPTY THEN MATCH_MP_TAC CPRING_NONEMPTY THEN
    REWRITE_TAC[CPMAP_PT_IN_DART]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_TRACE_CTRACE_PTRACE] THEN
  REWRITE_TAC[cp_tr0; catrev_cp; APPEND_NIL; REVERSE_REVERSE] THEN
  REWRITE_TAC[CPMAP_NIL_FST] THEN REWRITE_TAC[GSYM MAP_ROT_LIST] THEN
  REWRITE_TAC[AGREE_BRIDGE] THEN
  MP_TAC(ISPECL [`FST(cpmap cp)`; `SND(cpmap cp)`; `et:(color)list`]
    CTREE_MEM_CPCOLOR_CORE_AF) THEN
  REWRITE_TAC[CPMAP_PT_IN_DART] THEN
  REWRITE_TAC[GSYM MAP_ROT_LIST] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;

let CTREE_MEM_CPCOLOR_GEN = prove
 (`!cp et.
      ALL (\s. ~(s = CpRr)) cp
      ==> (ctree_mem (cpcolor cp) et <=>
           even_trace et /\
           ring_trace (FST(cpmap cp))
                      (rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp))))
                      (CONS (sumt et) et))`,
  REWRITE_TAC[CTREE_MEM_CPCOLOR_ALL]);;

let CTREE_MEM_CPCOLOR = prove
 (`!cp et.
      cubic_prog cp
      ==> (ctree_mem (cpcolor cp) et <=>
           even_trace et /\
           ring_trace (FST(cpmap cp))
                      (rot_list 1 (cpring (FST(cpmap cp)) (SND(cpmap cp))))
                      (CONS (sumt et) et))`,
  REWRITE_TAC[CTREE_MEM_CPCOLOR_ALL]);;
