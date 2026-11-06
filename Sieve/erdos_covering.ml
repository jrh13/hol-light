(* ========================================================================= *)
(* Erdos (1950): an infinite arithmetic progression of odd numbers none of   *)
(* which is a prime plus a power of 2.  Every n == 7629217 (mod 11184810) is *)
(* not of the form p + 2^k (ERDOS_PRIME_PLUS_POW2); hence infinitely many    *)
(* odd numbers are not (ERDOS_ODD_NOT_PRIME_PLUS_POW2).  Contrast Romanov's  *)
(* theorem: a positive proportion of all numbers are p + 2^k.                *)
(*                                                                           *)
(* The covering system                                                       *)
(*   k == 0 (2), 0 (3), 1 (4), 3 (8), 7 (12), 23 (24)                        *)
(* uses the primes 3, 7, 5, 17, 13, 241, for which 2 has order 2, 3, 4, 8,   *)
(* 12, 24, and 11184810 = 2 * 3 * 5 * 7 * 13 * 17 * 241.  For each k the     *)
(* prime q of the class of k MOD 24 divides n - 2^k (ERDOS_COVERING_A,       *)
(* POW2_MOD_PERIOD), so p = q; and q + 2^k is never == 7629217 modulo all    *)
(* six primes (ERDOS_COVERING_B).  Both covering facts are finite checks.    *)
(* ========================================================================= *)

needs "Sieve/base.ml";;
needs "Library/pocklington.ml";;

prioritize_num(); prioritize_complex();;

let ERDOS_COVERING_A = prove
 (`!r. r < 24
       ==> ?q. q IN {3,5,7,13,17,241} /\ (2 EXP r == 7629217) (mod q)`,
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY;
              TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`; EXISTS_OR_THM;
              UNWIND_THM2] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let ERDOS_COVERING_B = prove
 (`!r. r < 24
       ==> !q. q IN {3,5,7,13,17,241} /\ (2 EXP r == 7629217) (mod q)
               ==> ?q'. q' IN {3,5,7,13,17,241} /\
                        ~((q + 2 EXP r == 7629217) (mod q'))`,
  CONV_TAC EXPAND_CASES_CONV THEN REPEAT CONJ_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY;
              TAUT `(a \/ b) /\ c <=> a /\ c \/ b /\ c`; EXISTS_OR_THM;
              UNWIND_THM2] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; IMP_CONJ; FORALL_UNWIND_THM2] THEN
  REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV);;

let POW2_MOD_PERIOD = prove
 (`!k q. q IN {3,5,7,13,17,241} ==> (2 EXP k == 2 EXP (k MOD 24)) (mod q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(2 EXP 24 == 1) (mod q)` ASSUME_TAC THENL
   [UNDISCH_TAC `q IN {3,5,7,13,17,241}` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[CONG] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `24`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
    (RATOR_CONV o RATOR_CONV o RAND_CONV o RAND_CONV) [CONJUNCT1 th]) THEN
  REWRITE_TAC[EXP_ADD; ONCE_REWRITE_RULE[MULT_SYM] (GSYM EXP_EXP)] THEN
  MATCH_MP_TAC(NUMBER_RULE `(a == 1) (mod q) ==> (a * b == b) (mod q)`) THEN
  ONCE_REWRITE_TAC[GSYM(SPEC `k DIV 24` EXP_ONE)] THEN
  MATCH_MP_TAC CONG_EXP THEN ASM_REWRITE_TAC[]);;

let ERDOS_PRIME_PLUS_POW2 = prove
 (`!n. (n == 7629217) (mod 11184810)
       ==> ~(?p k. prime p /\ n = p + 2 EXP k)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `r = k MOD 24` THEN
  SUBGOAL_THEN `r < 24` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN {3,5,7,13,17,241} ==> (p + 2 EXP r == 7629217) (mod q)`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `n:num` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[CONG_ADD_LCANCEL_EQ] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
      EXPAND_TAC "r" THEN MATCH_MP_TAC POW2_MOD_PERIOD THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONG_DIVIDES_MODULUS THEN EXISTS_TAC `11184810` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `q IN {3,5,7,13,17,241}` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[DIVIDES_MOD] THEN
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  MP_TAC(SPEC `r:num` ERDOS_COVERING_A) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `prime q` ASSUME_TAC THENL
   [UNDISCH_TAC `q IN {3,5,7,13,17,241}` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC PRIME_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `p:num = q` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(SPECL [`q:num`; `p:num`] DIVIDES_PRIME_PRIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(2 EXP r == 7629217) (mod q)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPEC `r:num` ERDOS_COVERING_B) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':num` STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[]);;

let ERDOS_ODD_NOT_PRIME_PLUS_POW2 = prove
 (`INFINITE {n | ODD n /\ ~(?p k. prime p /\ n = p + 2 EXP k)}`,
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `IMAGE (\m. 11184810 * m + 7629217) (:num)` THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `\m. 11184810 * m + 7629217` INFINITE_IMAGE_INJ) THEN
    ANTS_TAC THENL [REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[num_INFINITE];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `m:num` THEN CONJ_TAC THENL
     [REWRITE_TAC[ODD_ADD; ODD_MULT] THEN CONV_TAC NUM_REDUCE_CONV;
      MATCH_MP_TAC ERDOS_PRIME_PLUS_POW2 THEN CONV_TAC NUMBER_RULE]]);;
