(* ========================================================================= *)
(* Termination bounds for the Bernstein-Yang "divstep" iteration.            *)
(*            https://gcd.cr.yp.to/safegcd-20190413.pdf                      *)
(* ========================================================================= *)

needs "Library/floor.ml";;
needs "Divstep/divstep.ml";;
needs "Divstep/idivstep.ml";;
needs "Divstep/hull_light.ml";;

(* ------------------------------------------------------------------------- *)
(* A couple of trivial lemmas about starting divstep with d = 1/2.           *)
(* ------------------------------------------------------------------------- *)

let INTEGER_DIVSTEP_DELTA = prove
 (`!f g n. integer(FST(ITER n divstep (&1 / &2,f,g)) - &1 / &2)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; REAL_SUB_REFL; INTEGER_CLOSED] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`ITER n divstep (&1 / &2,f,g)`,`t:real#int#int`) THEN
  REWRITE_TAC[divstep; FORALL_PAIR_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&1 - x - &1 / &2 = --(x - &1 / &2)`] THEN
  REWRITE_TAC[REAL_ARITH `(&1 + x) - &1 / &2 = &1 + (x - &1 / &2)`] THEN
  MESON_TAC[INTEGER_CLOSED]);;

let ITER_DIVSTEP_ODD_ALT = prove
 (`!f g n.
        f rem &2 = &1
        ==> FST(SND(ITER n divstep (&1 / &2,f,g))) rem &2 = &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ITER_DIVSTEP_ODD THEN
  ASM_MESON_TAC[PAIR]);;

(* ------------------------------------------------------------------------- *)
(* Instantiate and tweak the bounds theorem.                                 *)
(* ------------------------------------------------------------------------- *)

let DIVSTEP_ENDTOEND_BITS_SIMPLE = prove
 (`!f g b n.
        &0 <= g /\ g <= f /\ f <= &2 pow b /\ f rem &2 = &1 /\
        9437 * b + 1 <= 4096 * n
        ==> SND(SND(ITER n divstep (&1 / &2,f,g))) = &0`,
  REWRITE_TAC[GSYM divsteps_s] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [GSYM ITER_DIVSTEP_BOUND_ALT] THEN
  MP_TAC(ISPECL
   [`\n. int_of_real(FST (ITER n divstep (&1 / &2,f,g)) - &1 / &2)`;
    `\n. real_of_int(FST (SND(ITER n divstep (&1 / &2,f,g))))`;
    `\n. real_of_int(SND (SND(ITER n divstep (&1 / &2,f,g))))`;
    `b:num`; `n:num`]
   endtoend_bits_simple) THEN
  REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES; IMP_IMP; GSYM CONJ_ASSOC] THEN
  SIMP_TAC[REAL_OF_INT_OF_REAL; INTEGER_DIVSTEP_DELTA] THEN
  REWRITE_TAC[INTEGER_REAL_OF_INT] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ITER; REAL_SUB_0] THEN REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
  REWRITE_TAC[int_of_num_th; GSYM int_eq] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[INT_OF_NUM_LT] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[ITER; GSYM ADD1] THEN
  MP_TAC(SPECL [`f:int`; `g:int`; `m:num`] INTEGER_DIVSTEP_DELTA) THEN
  MP_TAC(SPECL [`f:int`; `g:int`; `m:num`] ITER_DIVSTEP_ODD_ALT) THEN
  SPEC_TAC(`ITER m divstep (&1 / &2,f,g)`,`t:real#int#int`) THEN
  ASM_REWRITE_TAC[divstep; FORALL_PAIR_THM] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`delta:real`; `f:int`; `g:int`] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `delta - &1 / &2 < &0 <=> ~(delta > &0)` SUBST1_TAC THENL
   [EQ_TAC THENL [ASM_SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(SPEC `g:int` INT_REM_2_CASES) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_MUL_LID; INT_MUL_LZERO; INT_ADD_RID] THENL
   [DISJ1_TAC; DISJ1_TAC; DISJ2_TAC; DISJ2_TAC] THEN
  (CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
  REWRITE_TAC[REAL_ARITH `x = y / &2 <=> &2 * x = y`] THEN
  REWRITE_TAC[REAL_OF_INT_CLAUSES] THEN
  REWRITE_TAC[INT_MUL_DIV_EQ; INT_2_DIVIDES_ADD; INT_2_DIVIDES_SUB] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_REM_2_DIVIDES]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Overall result for the integer-scaled version starting at 1.              *)
(* ------------------------------------------------------------------------- *)

let IDIVSTEP_ENDTOEND_BITS_SIMPLE = prove
 (`!f g b n.
        &0 <= g /\ g <= f /\ f <= &2 pow b /\ f rem &2 = &1 /\
        9437 * b + 1 <= 4096 * n
        ==> divstep_g n (&1,f,g) = &0 /\
            abs(divstep_f n (&1,f,g)) = gcd(f,g)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP DIVSTEP_ENDTOEND_BITS_SIMPLE) THEN
    REWRITE_TAC[ITER_DIVSTEP_INTEGER];
    ASM_MESON_TAC[DIVSTEP_FG_GCD; INT_GCD_0]]);;
