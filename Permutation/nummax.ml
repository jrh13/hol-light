(* ========================================================================= *)
(*  Maximum of two nums and of a list of nums.                               *)
(*                                                                           *)
(*  Author: Marco Maggesi                                                    *)
(*          University of Florence, Italy                                    *)
(*          http://www.math.unifi.it/~maggesi/                               *)
(*                                                                           *)
(*          (c) Copyright, Marco Maggesi, 2005-2007                          *)
(* ========================================================================= *)

needs "Permutation/morelist.ml";;

(* ------------------------------------------------------------------------- *)
(*  Maximum of two nums.                                                     *)
(* ------------------------------------------------------------------------- *)

let MAX_LT = prove
 (`!m n p. MAX m n < p <=> m < p /\ n < p`,
   REWRITE_TAC [MAX] THEN ARITH_TAC);;

let MAX_LE = prove
 (`!m n p. MAX m n <= p <=> m <= p /\ n <= p`,
   REWRITE_TAC [MAX] THEN ARITH_TAC);;

let LT_MAX = prove
 (`!m n p. p < MAX m n <=> p < m \/ p < n`,
   REWRITE_TAC [MAX] THEN ARITH_TAC);;

let LE_MAX = prove
 (`!m n p. p <= MAX m n <=> p <= m \/ p <= n`,
   REWRITE_TAC [MAX] THEN ARITH_TAC);;

let MAX_SYM = prove
  (`!m n. MAX n m = MAX m n`,
   MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THEN REPEAT GEN_TAC THENL
   [EQ_TAC THEN SIMP_TAC []; SIMP_TAC [MAX] THEN ARITH_TAC]);;

let MAX_ASSOC = prove
  (`!m n p. MAX (MAX m n) p = MAX m (MAX n p)`,
   REPEAT GEN_TAC THEN REWRITE_TAC [MAX] THEN
   ASM_CASES_TAC `m <= n` THEN ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `n <= p` THEN ASM_REWRITE_TAC [] THENL
   [SUBGOAL_THEN `m <= p` (fun th -> REWRITE_TAC [th]) THEN
    MATCH_MP_TAC LE_TRANS THEN ASM_MESON_TAC [];
    SUBGOAL_THEN `~(m <= p)` (fun th -> REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM MP_TAC THEN FIRST_X_ASSUM MP_TAC THEN ARITH_TAC]);;

let MAX_ACI = prove
  (`(!m n. MAX n m = MAX m n) /\
    (!m n p. MAX (MAX m n) p = MAX m (MAX n p)) /\
    (!m n p. MAX m (MAX n p) = MAX n (MAX m p)) /\
    (!m. MAX m m = m) /\
    (!m n. MAX m (MAX m n) = MAX m n)`,
   SUBGOAL_THEN `!n. MAX n n = n` ASSUME_TAC THENL
   [REWRITE_TAC [MAX] THEN ARITH_TAC;
    ASM_MESON_TAC [MAX_SYM; MAX_ASSOC]]);;

let MAX_0 = prove
  (`(!n. MAX n 0 = n) /\ (!n. MAX 0 n = n)`,
   REWRITE_TAC [MAX_SYM] THEN REWRITE_TAC [MAX] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(*  Maximum of a list of nums.                                               *)
(* ------------------------------------------------------------------------- *)

let MAXL = define
  `MAXL [] = 0 /\
   (!h t. MAXL (CONS h t) = MAX h (MAXL t))`;;

let MAXL_LE = prove
  (`!l n. MAXL l <= n <=> ALL (\m. m <= n) l`,
   LIST_INDUCT_TAC THEN REWRITE_TAC [ALL; MAXL; LE_0] THEN
   ASM_SIMP_TAC [MAX_LE]);;

let LT_MAXL = prove
  (`!l n. n < MAXL l <=> EX (\m. n < m) l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [EX; MAXL; NOT_LT; LE_0; LT_MAX]);;

let LE_MAXL = prove
  (`!n l. MEM n l ==> n <= MAXL l`,
   GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC [MEM; MAXL] THEN
   STRIP_TAC THEN ASM_SIMP_TAC [LE_REFL; LE_MAX]);;

let MEM_MAXL = prove
  (`!l. ~NULL l ==> MEM (MAXL l) l`,
   REWRITE_TAC [NULL_EQ_NIL] THEN LIST_INDUCT_TAC THEN
   REWRITE_TAC [MEM; MAXL; NOT_CONS_NIL] THEN
   ASM_CASES_TAC `t:num list=[]` THEN ASM_REWRITE_TAC[MAXL; MAX_0] THEN
   ASM_MESON_TAC [MAX]);;
