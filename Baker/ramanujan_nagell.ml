(* ========================================================================= *)
(* The Ramanujan-Nagell theorem: x^2 + 7 = 2^n only for (x, n) = (1, 3), (3, *)
(* 4), (5, 5), (11, 7), (181, 15) (Ramanujan 1913, Nagell 1948).             *)
(*                                                                           *)
(* Purpose: RAMANUJAN_NAGELL, the equation in natural numbers.               *)
(*                                                                           *)
(* Method (Nagell). For n even, (2^(n/2) - x) (2^(n/2) + x) = 7 gives n = 4  *)
(* and x = 3. For n odd, n >= 3, x = 2k + 1 is odd and with m = n - 2 the    *)
(* element alpha = k + omega of the ring of integers of Q(sqrt(-7)), omega = *)
(* (1 + sqrt(-7))/2, has norm alpha cnj(alpha) = 2^m. The ring is a UFD      *)
(* (Euclidean: IMAG_QUADRATIC_INTEGERS_UFD), alpha and cnj(alpha) are        *)
(* coprime (a common divisor has norm dividing 7 = N(alpha - cnj alpha) and  *)
(* 2^m), so alpha is a unit times an m-th power (UFD_COPRIME_MUL_POW with c  *)
(* = 2), the units are +-1 (IMAG_QUADRATIC_INTEGERS_UNIT_GENERIC) and the    *)
(* elements of norm 2 are +-omega, +-cnj(omega). With omega^m = -2 b(m-1) +  *)
(* b(m) omega, comparing imaginary parts gives b(m) = +-1 for the integer    *)
(* sequence b(0) = 0, b(1) = 1, b(m+2) = b(m+1) - 2 b(m) (nagell_seq).       *)
(* Modulo 4, b(m) = -1 for odd m >= 3; and b(m) = -1 only for m = 3, 5, 13:  *)
(* b is 21-periodic modulo 7 (b(r) = -1 mod 7, r < 21, only for r = 3, 5,    *)
(* 13), and a 7-adic argument (Nagell) shows that two solutions m, m + N     *)
(* with 21 | N coincide: if 3 7^l | N, l >= 1, then b(N) = 2N and b(N + 1) = *)
(* N + 1 modulo 7^(l+1) (RAMANUJAN_NAGELL_SEQ_7ADIC, by the multiplication   *)
(* lemma RAMANUJAN_NAGELL_SEQ_MUL_CONG), so by the addition formula b(m + N) *)
(* = b(m) + N (2 b(m+1) - b(m)) modulo 7^(l+1), and 2 b(m+1) - b(m) is prime *)
(* to 7 for m = 3, 5, 13; hence 3 7^l | N for all l and N = 0.               *)
(*                                                                           *)
(* Main results: RAMANUJAN_NAGELL; the sequence: nagell_seq,                 *)
(* RAMANUJAN_NAGELL_SEQ_ADD (addition formula), RAMANUJAN_NAGELL_SEQ_NEG1    *)
(* (b(m) = -1 iff m = 3, 5, 13), RAMANUJAN_NAGELL_SEQ_PM1 (b(m) = +-1 for    *)
(* odd m iff m = 1, 3, 5, 13); helper names RAMANUJAN_NAGELL_*.              *)
(*                                                                           *)
(* Uses: Baker/quadint_ring.ml (QUAD_OMEGA_SQUARE, QUAD_OMEGA_CNJ,           *)
(* QUAD_OMEGA_NORM, IMAG_QUADRATIC_INTEGERS_IN, _UNIT, _UNIT_GENERIC, _UFD,  *)
(* _DIVIDES_NORM and related tools), Baker/quadint_ant.ml                    *)
(* (IMAG_QUADRATIC_INTEGERS_CLAUSES, _SUB_POW), ANT/ufd.ml                   *)
(* (UFD_COPRIME_MUL_POW), Library/ringtheory.ml (ring_coprime, ring_divides, *)
(* RING_DIVIDES_SUB).                                                        *)
(* ========================================================================= *)

needs "ANT/ufd.ml";;
needs "Baker/quadint_ring.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The sequence b(m): omega^(m+1) = -2 b(m) + b(m+1) omega for any root      *)
(* omega of z^2 - z + 2.                                                     *)
(* ------------------------------------------------------------------------- *)

let nagell_seq = define
 `nagell_seq 0 = &0:int /\ nagell_seq 1 = &1 /\
  !m. nagell_seq(m + 2) = nagell_seq(m + 1) - &2 * nagell_seq m`;;

let RAMANUJAN_NAGELL_SEQ_REC = prove
 (`!m. nagell_seq(m + 2) = nagell_seq(m + 1) - &2 * nagell_seq m`,
  REWRITE_TAC[nagell_seq]);;

(* The values b(0), ..., b(22), as a conjunction of equations.              *)

let RAMANUJAN_NAGELL_SEQ_VALUES =
  let rec build k acc =
    if k > 20 then rev acc else
    let th = CONV_RULE NUM_REDUCE_CONV
               (SPEC (mk_small_numeral k) RAMANUJAN_NAGELL_SEQ_REC) in
    let th' = CONV_RULE (RAND_CONV (REWRITE_CONV acc THENC INT_REDUCE_CONV))
                th in
    build (k + 1) (th' :: acc) in
  end_itlist CONJ
   (build 0 [CONJUNCT1(CONJUNCT2 nagell_seq); CONJUNCT1 nagell_seq]);;

let RAMANUJAN_NAGELL_SEQ_ADD = prove
 (`!m n. nagell_seq(m + n) =
         nagell_seq m * nagell_seq(n + 1) +
         (nagell_seq(m + 1) - nagell_seq m) * nagell_seq n`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!n. nagell_seq(m + n) =
        nagell_seq m * nagell_seq(n + 1) +
        (nagell_seq(m + 1) - nagell_seq m) * nagell_seq n /\
        nagell_seq(m + n + 1) =
        nagell_seq m * nagell_seq(n + 2) +
        (nagell_seq(m + 1) - nagell_seq m) * nagell_seq(n + 1)`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; RAMANUJAN_NAGELL_SEQ_VALUES] THEN INT_ARITH_TAC;
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC)] THEN
  REWRITE_TAC[ARITH_RULE `m + SUC n + 1 = (m + n) + 2`;
              ARITH_RULE `m + SUC n = m + n + 1`;
              ARITH_RULE `SUC n + 1 = n + 2`;
              ARITH_RULE `SUC n + 2 = (n + 1) + 2`; ADD1] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_REC] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_REC] THEN
  INT_ARITH_TAC);;

let RAMANUJAN_NAGELL_SEQ_ADD_1 = prove
 (`!m n. nagell_seq(m + n + 1) =
         nagell_seq(m + 1) * nagell_seq(n + 1) -
         &2 * nagell_seq m * nagell_seq n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SPECL [`m:num`; `n + 1`] RAMANUJAN_NAGELL_SEQ_ADD] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_REC] THEN INT_ARITH_TAC);;

let RAMANUJAN_NAGELL_POW = prove
 (`!z m. z pow 2 = z - Cx(&2)
         ==> z pow (m + 1) =
             Cx(-- &2 * real_of_int(nagell_seq m)) +
             Cx(real_of_int(nagell_seq(m + 1))) * z`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; COMPLEX_POW_1; RAMANUJAN_NAGELL_SEQ_VALUES] THEN
    REWRITE_TAC[int_of_num_th; CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC m + 1 = SUC(m + 1)`] THEN
  ASM_REWRITE_TAC[complex_pow] THEN
  REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_REC] THEN
  REWRITE_TAC[int_sub_th; int_mul_th; int_of_num_th; CX_SUB; CX_MUL;
              CX_NEG] THEN
  UNDISCH_TAC `z pow 2 = z - Cx(&2)` THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Modulo 4: b(m) = 1 for even m >= 2 and b(m) = -1 for odd m >= 3.          *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_SEQ_MOD4 = prove
 (`!k. (nagell_seq(2 * k + 2) == &1) (mod &4) /\
       (nagell_seq(2 * k + 3) == -- &1) (mod &4)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; RAMANUJAN_NAGELL_SEQ_VALUES] THEN
    REWRITE_TAC[INT_CONG_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC k + 2 = (2 * k + 2) + 2`;
              ARITH_RULE `2 * SUC k + 3 = (2 * k + 3) + 2`] THEN
  REWRITE_TAC[SPEC `2 * k + 3` RAMANUJAN_NAGELL_SEQ_REC] THEN
  REWRITE_TAC[ARITH_RULE `(2 * k + 3) + 1 = (2 * k + 2) + 2`] THEN
  REWRITE_TAC[SPEC `2 * k + 2` RAMANUJAN_NAGELL_SEQ_REC] THEN
  REWRITE_TAC[ARITH_RULE `(2 * k + 2) + 1 = 2 * k + 3`] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[int_congruent] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:int`)
   (X_CHOOSE_TAC `c:int`)) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `c - &2 * a - &1:int`; EXISTS_TAC `--c - &2 * a:int`] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The multiplication lemma: if q divides C (2 E - C - 2) and                *)
(* (E - 1)^2 - 2 C^2, where C = b(M) and E = b(M + 1), then b(t M) = t C and *)
(* b(t M + 1) = 1 + t (E - 1) modulo q (omega^M = 1 + w with w^2 = 0 mod q). *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_MUL_STEP = prove
 (`!q C E B0 B1 t:int.
     q divides C * (&2 * E - C - &2) /\
     q divides (E - &1) pow 2 - &2 * C pow 2 /\
     (B0 == t * C) (mod q) /\ (B1 == &1 + t * (E - &1)) (mod q)
     ==> (C * B1 + (E - C) * B0 == (t + &1) * C) (mod q) /\
         (E * B1 - &2 * C * B0 == &1 + (t + &1) * (E - &1)) (mod q)`,
  CONV_TAC INTEGER_RULE);;

let RAMANUJAN_NAGELL_SEQ_MUL_CONG = prove
 (`!M q. q divides nagell_seq M *
                   (&2 * nagell_seq(M + 1) - nagell_seq M - &2) /\
         q divides (nagell_seq(M + 1) - &1) pow 2 - &2 * nagell_seq M pow 2
         ==> !t. (nagell_seq(t * M) == &t * nagell_seq M) (mod q) /\
                 (nagell_seq(t * M + 1) ==
                  &1 + &t * (nagell_seq(M + 1) - &1)) (mod q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; RAMANUJAN_NAGELL_SEQ_VALUES] THEN
    REWRITE_TAC[INT_MUL_LZERO; INT_ADD_RID; INT_CONG_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[MULT_CLAUSES; GSYM INT_OF_NUM_SUC] THEN
  REWRITE_TAC[ARITH_RULE `t * M + M = M + t * M`;
              ARITH_RULE `(t * M + M) + 1 = M + t * M + 1`] THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_ADD_1] THEN
  REWRITE_TAC[SPECL [`M:num`; `t * M`] RAMANUJAN_NAGELL_SEQ_ADD] THEN
  MATCH_MP_TAC RAMANUJAN_NAGELL_MUL_STEP THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The 7-adic lemma: if 3 7^(l+1) divides N then b(N) = 2 N and              *)
(* b(N + 1) = N + 1 modulo 7^(l+2).                                          *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_POW7 = prove
 (`!l. (&7:int) pow (l + 1) = &7 * &7 pow l /\
       (&7:int) pow (l + 2) = &49 * &7 pow l /\
       (&7:int) pow (l + 3) = &343 * &7 pow l`,
  GEN_TAC THEN REWRITE_TAC[INT_POW_ADD] THEN CONV_TAC INT_REDUCE_CONV THEN
  INT_ARITH_TAC);;

let RAMANUJAN_NAGELL_7ADIC_BASE = prove
 (`!B0 B1 t:int.
     (B0 == t * &287) (mod &49) /\ (B1 == &1 + t * (&1541 - &1)) (mod &49)
     ==> (B0 == &2 * &21 * t) (mod &49) /\ (B1 == &21 * t + &1) (mod &49)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_congruent] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:int`)
   (X_CHOOSE_TAC `b:int`)) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `a + &5 * t:int`; EXISTS_TAC `b + &31 * t:int`] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN INT_ARITH_TAC);;

let RAMANUJAN_NAGELL_7ADIC_COND = prove
 (`!C E n p:int.
     (C == &2 * n) (mod (&49 * p)) /\ (E == n + &1) (mod (&49 * p)) /\
     n = &21 * p
     ==> (&343 * p) divides C * (&2 * E - C - &2) /\
         (&343 * p) divides (E - &1) pow 2 - &2 * C pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_congruent; int_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:int`)
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `b:int`) SUBST_ALL_TAC)) THEN
  CONJ_TAC THENL
   [EXISTS_TAC `p * (&6 + &7 * a) * (&2 * b - a):int`;
    EXISTS_TAC
     `p * (&7 * b pow 2 - &14 * a pow 2 + &6 * b - &24 * a - &9):int`]
  THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING);;

let RAMANUJAN_NAGELL_7ADIC_LIFT = prove
 (`!C E B0 B1 n p k:int.
     (C == &2 * n) (mod (&49 * p)) /\ (E == n + &1) (mod (&49 * p)) /\
     (B0 == (&7 * k) * C) (mod (&343 * p)) /\
     (B1 == &1 + (&7 * k) * (E - &1)) (mod (&343 * p)) /\
     n = &21 * p
     ==> (B0 == &2 * ((&7 * k) * n)) (mod (&343 * p)) /\
         (B1 == (&7 * k) * n + &1) (mod (&343 * p))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))
  THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INTEGER_RULE);;

let RAMANUJAN_NAGELL_SEQ_7ADIC = prove
 (`!l N. (3 * 7 EXP (l + 1)) divides N
         ==> (nagell_seq N == &2 * &N) (mod (&7 pow (l + 2))) /\
             (nagell_seq(N + 1) == &N + &1) (mod (&7 pow (l + 2)))`,
  INDUCT_TAC THENL
   [X_GEN_TAC `N:num` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST1_TAC) THEN
    MP_TAC(SPECL [`21`; `&49:int`] RAMANUJAN_NAGELL_SEQ_MUL_CONG) THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_VALUES] THEN
      REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `t:num`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_VALUES; ARITH_RULE `t * 21 = 21 * t`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; RAMANUJAN_NAGELL_7ADIC_BASE];
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN
  REWRITE_TAC[ARITH_RULE `SUC l + 1 = l + 2`;
              ARITH_RULE `SUC l + 2 = l + 3`] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `(3 * 7 EXP (l + 2)) * k = (7 * k) * (3 * 7 EXP (l + 1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `l + 2 = SUC(l + 1)`; EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `3 * 7 EXP (l + 1)`) THEN
  REWRITE_TAC[DIVIDES_REFL] THEN
  ABBREV_TAC `M = 3 * 7 EXP (l + 1)` THEN
  SUBGOAL_THEN `&M:int = &21 * &7 pow l` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW;
                RAMANUJAN_NAGELL_POW7] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_POW7] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `(&343 * &7 pow l):int`]
    RAMANUJAN_NAGELL_SEQ_MUL_CONG) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC RAMANUJAN_NAGELL_7ADIC_COND THEN
    EXISTS_TAC `&M:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `7 * k`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN STRIP_TAC THEN
  MATCH_MP_TAC RAMANUJAN_NAGELL_7ADIC_LIFT THEN
  MAP_EVERY EXISTS_TAC [`nagell_seq M`; `nagell_seq(M + 1)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Consequences: b is 21-periodic modulo 7, and two solutions of b(m) = -1   *)
(* that are congruent modulo 21 coincide; hence b(m) = -1 only for m = 3, 5  *)
(* and 13.                                                                   *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_MOD7_STEP = prove
 (`!B0 B1 X Y k:int.
     (B0 == &2 * &21 * k) (mod &49) /\ (B1 == &21 * k + &1) (mod &49)
     ==> (B0 * X + (B1 - B0) * Y == Y) (mod &7)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_congruent] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:int`)
   (X_CHOOSE_TAC `b:int`)) THEN
  EXISTS_TAC `(&6 * k + &7 * a) * X + (&7 * b - &3 * k - &7 * a) * Y:int` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC INT_RING);;

let RAMANUJAN_NAGELL_SEQ_MOD7 = prove
 (`!k r. (nagell_seq(21 * k + r) == nagell_seq r) (mod &7)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`0`; `21 * k`] RAMANUJAN_NAGELL_SEQ_7ADIC) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[NUMBER_RULE `(a:num) divides a * b`; GSYM INT_OF_NUM_MUL] THEN
  MP_TAC(SPECL [`21 * k`; `r:num`] RAMANUJAN_NAGELL_SEQ_ADD) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_MOD7_STEP]);;

let RAMANUJAN_NAGELL_SEQ_RESIDUES = prove
 (`!r. r < 21 /\ (nagell_seq r == -- &1) (mod &7)
       ==> r = 3 \/ r = 5 \/ r = 13`,
  REWRITE_TAC[GSYM IMP_IMP] THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_VALUES; GSYM INT_REM_EQ] THEN
  CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV);;

let RAMANUJAN_NAGELL_UNIQUE_STEP = prove
 (`!q B0 B1 E n:int.
     (B0 == &2 * n) (mod q) /\ (B1 == n + &1) (mod q) /\
     -- &1 = -- &1 * B1 + (E - -- &1) * B0
     ==> q divides n * (&2 * E + &1)`,
  CONV_TAC INTEGER_RULE);;

let RAMANUJAN_NAGELL_SEQ_UNIQUE = prove
 (`!r N. nagell_seq r = -- &1 /\ coprime(&7,&2 * nagell_seq(r + 1) + &1) /\
         21 divides N /\ nagell_seq(r + N) = -- &1
         ==> N = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!l. (3 * 7 EXP (l + 1)) divides N` MP_TAC THENL
   [INDUCT_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP RAMANUJAN_NAGELL_SEQ_7ADIC) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(&7 pow (l + 2)):int`; `nagell_seq N`; `nagell_seq(N + 1)`;
                   `nagell_seq(r + 1)`; `&N:int`]
      RAMANUJAN_NAGELL_UNIQUE_STEP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`r:num`; `N:num`] RAMANUJAN_NAGELL_SEQ_ADD) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&7 pow (l + 2)) divides (&N:int)` MP_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!a b n:int. coprime(a,b) /\ a divides n * b ==> a divides n`) THEN
      EXISTS_TAC `&2 * nagell_seq(r + 1) + &1` THEN
      ASM_REWRITE_TAC[INT_COPRIME_LPOW];
      ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_POW; GSYM num_divides] THEN DISCH_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC l + 1 = l + 2`] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!a b n:num. coprime(a,b) /\ a divides n /\ b divides n
                  ==> (a * b) divides n`) THEN
    ASM_REWRITE_TAC[COPRIME_REXP; COPRIME_CONV `coprime(3,7)`] THEN
    MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `21` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC DIVIDES_CONV;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  MP_TAC(SPEC `N:num` LT_POW2_REFL) THEN
  MP_TAC(SPECL [`2`; `7`; `N:num`] EXP_MONO_LE) THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC);;

let RAMANUJAN_NAGELL_K_COPRIME = prove
 (`coprime(&7:int,-- &5) /\ coprime(&7:int,&11) /\ coprime(&7:int,-- &181)`,
  REWRITE_TAC[int_coprime] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`-- &2:int`; `-- &3:int`];
    MAP_EVERY EXISTS_TAC [`-- &3:int`; `&2:int`];
    MAP_EVERY EXISTS_TAC [`&26:int`; `&1:int`]] THEN
  INT_ARITH_TAC);;

let RAMANUJAN_NAGELL_SEQ_NEG1 = prove
 (`!m. nagell_seq m = -- &1 <=> m = 3 \/ m = 5 \/ m = 13`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_VALUES]] THEN
  MP_TAC(SPECL [`m:num`; `21`] DIVISION) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `q = m DIV 21` THEN ABBREV_TAC `r = m MOD 21` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `nagell_seq(r + 21 * q) = -- &1` ASSUME_TAC THENL
   [UNDISCH_TAC `nagell_seq(q * 21 + r) = -- &1` THEN
    REWRITE_TAC[ARITH_RULE `q * 21 + r = r + 21 * q`];
    ALL_TAC] THEN
  SUBGOAL_THEN `r = 3 \/ r = 5 \/ r = 13` ASSUME_TAC THENL
   [MATCH_MP_TAC RAMANUJAN_NAGELL_SEQ_RESIDUES THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`q:num`; `r:num`] RAMANUJAN_NAGELL_SEQ_MOD7) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_CONG_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `21 * q = 0` MP_TAC THENL
   [MATCH_MP_TAC RAMANUJAN_NAGELL_SEQ_UNIQUE THEN EXISTS_TAC `r:num` THEN
    ASM_REWRITE_TAC[NUMBER_RULE `(a:num) divides a * b`] THEN
    FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_VALUES] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[RAMANUJAN_NAGELL_K_COPRIME];
    ASM_ARITH_TAC]);;

let RAMANUJAN_NAGELL_SEQ_PM1 = prove
 (`!m. ODD m /\ abs(nagell_seq m) = &1 <=> m = 1 \/ m = 3 \/ m = 5 \/ m = 13`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_VALUES] THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN CONV_TAC NUM_REDUCE_CONV]
  THEN
  REWRITE_TAC[INT_ARITH `abs(x:int) = &1 <=> x = &1 \/ x = -- &1`] THEN
  REWRITE_TAC[RAMANUJAN_NAGELL_SEQ_NEG1] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THENL
   [CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MP_TAC(CONJUNCT2(SPEC `k - 1` RAMANUJAN_NAGELL_SEQ_MOD4)) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> 2 * (k - 1) + 3 = SUC(2 * k)`] THEN
  REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* The ring of integers of Q(sqrt(-7)): a UFD, omega^2 = omega - 2, the norm *)
(* form x^2 + x y + 2 y^2, the units +-1 and the elements of norm 2.         *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_SQUAREFREE = prove
 (`squarefree 7`,
  MATCH_MP_TAC PRIME_IMP_SQUAREFREE THEN CONV_TAC PRIME_CONV);;

let RAMANUJAN_NAGELL_UFD = prove
 (`UFD(imag_quadratic_integers 7)`,
  MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_UFD THEN REWRITE_TAC[IN_INSERT]);;

let RAMANUJAN_NAGELL_OMEGA_SQUARE = prove
 (`quad_omega 7 pow 2 = quad_omega 7 - Cx(&2) /\
   cnj(quad_omega 7) pow 2 = cnj(quad_omega 7) - Cx(&2)`,
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[QUAD_OMEGA_SQUARE] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    DISCH_THEN(MP_TAC o AP_TERM `cnj`) THEN
    REWRITE_TAC[CNJ_POW; CNJ_SUB; CNJ_CX]]);;

let RAMANUJAN_NAGELL_OMEGA_CNJ = prove
 (`cnj(quad_omega 7) = Cx(&1) - quad_omega 7`,
  REWRITE_TAC[QUAD_OMEGA_CNJ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let RAMANUJAN_NAGELL_OMEGA_NORM = prove
 (`!x y. norm(Cx x + Cx y * quad_omega 7) pow 2 =
         x pow 2 + x * y + &2 * y pow 2`,
  REWRITE_TAC[QUAD_OMEGA_NORM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let RAMANUJAN_NAGELL_OMEGA_IM = prove
 (`&0 < Im(quad_omega 7)`,
  MATCH_MP_TAC QUAD_OMEGA_IM_POS THEN ARITH_TAC);;

let RAMANUJAN_NAGELL_COORDS = prove
 (`!z. z IN ring_carrier(imag_quadratic_integers 7)
       ==> ?x y:int.
             z = Cx(real_of_int x) + Cx(real_of_int y) * quad_omega 7 /\
             norm z pow 2 = real_of_int(x pow 2 + x * y + &2 * y pow 2)`,
  GEN_TAC THEN
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_IN; RAMANUJAN_NAGELL_SQUAREFREE] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`int_of_real p`; `int_of_real q`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[int_rep]) THEN
  ASM_REWRITE_TAC[int_add_th; int_mul_th; int_pow_th; int_of_num_th;
                  RAMANUJAN_NAGELL_OMEGA_NORM]);;

let RAMANUJAN_NAGELL_INT_SQUARE_LT_4 = prove
 (`!x:int. x pow 2 < &4 ==> x = -- &1 \/ x = &0 \/ x = &1`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(x:int) < &2` MP_TAC THENL
   [REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`2`; `&2:int`; `abs(x:int)`] INT_POW_LE2) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    INT_ARITH_TAC]);;

let RAMANUJAN_NAGELL_INT_BOUNDS = prove
 (`!x y:int. x pow 2 + x * y + &2 * y pow 2 <= &2
             ==> (x = -- &1 \/ x = &0 \/ x = &1) /\
                 (y = -- &1 \/ y = &0 \/ y = &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  MATCH_MP_TAC RAMANUJAN_NAGELL_INT_SQUARE_LT_4 THENL
   [MP_TAC(SPEC `x + &4 * y:int` INT_LE_POW_2);
    MP_TAC(SPEC `&2 * x + y:int` INT_LE_POW_2)] THEN
  POP_ASSUM MP_TAC THEN INT_ARITH_TAC);;

let RAMANUJAN_NAGELL_INT_NORM_2 = prove
 (`!x y:int. real_of_int(x pow 2 + x * y + &2 * y pow 2) = &2
             ==> x = &0 /\ y = &1 \/ x = -- &1 /\ y = &1 \/
                 x = &0 /\ y = -- &1 \/ x = &1 /\ y = -- &1`,
  REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int`; `y:int`] RAMANUJAN_NAGELL_INT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)
                             (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  POP_ASSUM MP_TAC THEN CONV_TAC INT_REDUCE_CONV);;

let RAMANUJAN_NAGELL_UNITS = prove
 (`!u. ring_unit (imag_quadratic_integers 7) u ==> u = Cx(&1) \/ u = --Cx(&1)`,
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_UNIT_GENERIC; RAMANUJAN_NAGELL_SQUAREFREE;
           ARITH_EQ]);;

let RAMANUJAN_NAGELL_NORM_2 = prove
 (`!e. e IN ring_carrier(imag_quadratic_integers 7) /\ norm e pow 2 = &2
       ==> e = quad_omega 7 \/ e = --quad_omega 7 \/
           e = cnj(quad_omega 7) \/ e = --cnj(quad_omega 7)`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP RAMANUJAN_NAGELL_COORDS)
    ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC
   (MP_TAC o MATCH_MP RAMANUJAN_NAGELL_INT_NORM_2 o SYM)) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN
   (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  REWRITE_TAC[int_of_num_th; int_neg_th; CX_NEG;
              RAMANUJAN_NAGELL_OMEGA_CNJ] THEN
  FIRST (map (fun t -> t THEN CONV_TAC COMPLEX_RING)
   [DISJ1_TAC; DISJ2_TAC THEN DISJ1_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC;
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ2_TAC]));;

(* ------------------------------------------------------------------------- *)
(* The two factors of (x^2 + 7)/4 = 2^m are coprime; Im(e^m) for the        *)
(* elements e of norm 2.                                                     *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_COPRIME = prove
 (`!a m. a IN ring_carrier(imag_quadratic_integers 7) /\
         norm a pow 2 = &2 pow m /\ norm(a - cnj a) pow 2 = &7
         ==> ring_coprime (imag_quadratic_integers 7) (a,cnj a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ring_coprime; IMAG_QUADRATIC_INTEGERS_CNJ] THEN
  X_GEN_TAC `d:complex` THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_divides (imag_quadratic_integers 7) d (a - cnj a)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`imag_quadratic_integers 7`; `a:complex`; `cnj a`;
                   `d:complex`] RING_DIVIDES_SUB) THEN
    ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_SUB_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `d IN ring_carrier(imag_quadratic_integers 7)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_divides]; ALL_TAC] THEN
  MP_TAC(SPECL [`7`; `d:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  MP_TAC(SPECL [`7`; `d:complex`; `a - cnj a`]
    IMAG_QUADRATIC_INTEGERS_DIVIDES_NORM) THEN
  MP_TAC(SPECL [`7`; `d:complex`; `a:complex`]
    IMAG_QUADRATIC_INTEGERS_DIVIDES_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN DISCH_THEN(X_CHOOSE_TAC `n2:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
  ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_UNIT] THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_POS; ARITH_EQ; REAL_POW_ONE;
                  REAL_OF_NUM_EQ] THEN
  SUBGOAL_THEN `(j:num) divides 7 /\ j divides 2 EXP m` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[divides] THEN CONJ_TAC THENL
     [EXISTS_TAC `n2:num` THEN UNDISCH_TAC `&7 = norm(d:complex) pow 2 * &n2`;
      EXISTS_TAC `n1:num` THEN
      UNDISCH_TAC `&2 pow m = norm(d:complex) pow 2 * &n1`] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL;
                    GSYM REAL_OF_NUM_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `j = 1 \/ j = 7` MP_TAC THENL
   [MP_TAC(EQT_ELIM(PRIME_CONV `prime 7`)) THEN REWRITE_TAC[prime] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `7`; `2`] PRIME_DIVEXP) THEN
  ASM_REWRITE_TAC[EQT_ELIM(PRIME_CONV `prime 7`)] THEN
  CONV_TAC(LAND_CONV DIVIDES_CONV) THEN REWRITE_TAC[]);;

let RAMANUJAN_NAGELL_ABS_IM_POW = prove
 (`!e m. (e = quad_omega 7 \/ e = --quad_omega 7 \/
          e = cnj(quad_omega 7) \/ e = --cnj(quad_omega 7))
         ==> abs(Im(e pow (m + 1))) =
             abs(real_of_int(nagell_seq(m + 1))) * abs(Im(quad_omega 7))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!z. z pow 2 = z - Cx(&2)
        ==> Im(z pow (m + 1)) = real_of_int(nagell_seq(m + 1)) * Im z`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `m:num` o MATCH_MP RAMANUJAN_NAGELL_POW) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_CX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[COMPLEX_POW_NEG] THEN TRY COND_CASES_TAC THEN
  ASM_SIMP_TAC[IM_NEG; REAL_ABS_NEG; RAMANUJAN_NAGELL_OMEGA_SQUARE; IM_CNJ;
               REAL_ABS_MUL]);;

let RAMANUJAN_NAGELL_ABS_CANCEL = prove
 (`!b w. &0 < w /\ abs w = abs b * abs w ==> abs b = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`abs b`; `&1`; `abs w`] REAL_EQ_MUL_RCANCEL) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The algebraic step: if x^2 + 7 = 2^(m+2) with m >= 1 then b(m) = +-1.     *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_ALGEBRA = prove
 (`!x m. ~(m = 0) /\ x EXP 2 + 7 = 2 EXP (m + 2) ==> abs(nagell_seq m) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ODD x` MP_TAC THENL
   [REWRITE_TAC[GSYM NOT_EVEN] THEN
    FIRST_ASSUM(MP_TAC o AP_TERM `EVEN`) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_EXP; ADD_EQ_0] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `&k pow 2 + &k * &1 + &2 * &1 pow 2 = (&2:real) pow m`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `real_of_num`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW;
                GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_MUL; REAL_POW_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `a = Cx(&k) + Cx(&1) * quad_omega 7` THEN
  SUBGOAL_THEN `a IN ring_carrier(imag_quadratic_integers 7)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_IN_COORDS THEN
    REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a:complex) pow 2 = &2 pow m` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN ASM_REWRITE_TAC[RAMANUJAN_NAGELL_OMEGA_NORM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`imag_quadratic_integers 7`; `a:complex`; `cnj a`;
                 `Cx(&2)`; `m:num`] UFD_COPRIME_MUL_POW) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES; IMAG_QUADRATIC_INTEGERS_SUB_POW;
              RAMANUJAN_NAGELL_UFD] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CNJ; IMAG_QUADRATIC_INTEGERS_CX;
                 INTEGER_CLOSED] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW] THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC RAMANUJAN_NAGELL_COPRIME THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
    REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_CX; RAMANUJAN_NAGELL_OMEGA_CNJ] THEN
    SUBGOAL_THEN
     `(Cx(&k) + Cx(&1) * quad_omega 7) -
      (Cx(&k) + Cx(&1) * (Cx(&1) - quad_omega 7)) =
      Cx(-- &1) + Cx(&2) * quad_omega 7`
    SUBST1_TAC THENL
     [REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING;
      REWRITE_TAC[RAMANUJAN_NAGELL_OMEGA_NORM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:complex`; `e:complex`] THEN STRIP_TAC THEN
  MP_TAC(ASSUME `ring_unit (imag_quadratic_integers 7) u`) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_UNIT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(e:complex) pow 2 = &2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`7`; `e:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    SUBGOAL_THEN `2 EXP m = j EXP m` MP_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_POW] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `norm(a:complex) pow 2 = &2 pow m` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_POW_POW; ARITH_RULE `m * 2 = 2 * m`] THEN
      MESON_TAC[];
      ASM_REWRITE_TAC[EXP_MONO_EQ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. m = n + 1` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `m - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`e:complex`; `n:num`] RAMANUJAN_NAGELL_ABS_IM_POW) THEN
  ANTS_TAC THENL [MATCH_MP_TAC RAMANUJAN_NAGELL_NORM_2 THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  SUBGOAL_THEN `abs(Im(e pow (n + 1))) = abs(Im(quad_omega 7))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `abs(Im(a:complex)) = abs(Im(quad_omega 7))`
     (SUBST1_TAC o SYM) THENL
     [EXPAND_TAC "a" THEN REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_CX] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o
      MATCH_MP RAMANUJAN_NAGELL_UNITS) THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_LID; IM_NEG; REAL_ABS_NEG];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJ RAMANUJAN_NAGELL_OMEGA_IM) THEN
  DISCH_THEN(MP_TAC o MATCH_MP RAMANUJAN_NAGELL_ABS_CANCEL) THEN
  REWRITE_TAC[GSYM int_abs_th; GSYM int_of_num_th; GSYM int_eq]);;

(* ------------------------------------------------------------------------- *)
(* The case of even n: (2^k - x) (2^k + x) = 7.                              *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL_EVEN = prove
 (`!x k. x EXP 2 + 7 = 2 EXP (2 * k) ==> x = 3 /\ k = 2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 * k = k * 2`] THEN REWRITE_TAC[GSYM EXP_EXP] THEN
  ABBREV_TAC `y = 2 EXP k` THEN DISCH_TAC THEN
  SUBGOAL_THEN `x < y` MP_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`y:num`; `x:num`; `2`] EXP_MONO_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[LT_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `2 * x * SUC d + SUC d * SUC d = 7` ASSUME_TAC THENL
   [UNDISCH_TAC `x EXP 2 + 7 = (x + SUC d) EXP 2` THEN
    REWRITE_TAC[EXP_2] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `d = 0` SUBST_ALL_TAC THENL
   [ASM_CASES_TAC `2 <= d` THENL
     [MP_TAC(SPECL [`3`; `SUC d`; `3`; `SUC d`] LE_MULT2) THEN ASM_ARITH_TAC;
      ASM_CASES_TAC `d = 1` THENL
       [UNDISCH_TAC `2 * x * SUC d + SUC d * SUC d = 7` THEN
        ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x = 0` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x = 3` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `2 * x * SUC 0 + SUC 0 * SUC 0 = 7` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP k = 2 EXP 2` MP_TAC THENL
   [UNDISCH_TAC `2 EXP k = 3 + SUC 0` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[];
    REWRITE_TAC[EQ_EXP] THEN CONV_TAC NUM_REDUCE_CONV]);;

let RAMANUJAN_NAGELL_ROOT = prove
 (`!x c. x EXP 2 + 7 = c EXP 2 + 7 ==> x = c`,
  REWRITE_TAC[EQ_ADD_RCANCEL; EXP_MONO_EQ] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Ramanujan-Nagell theorem.                                             *)
(* ------------------------------------------------------------------------- *)

let RAMANUJAN_NAGELL = prove
 (`!x n. x EXP 2 + 7 = 2 EXP n <=>
         x = 1 /\ n = 3 \/ x = 3 /\ n = 4 \/ x = 5 /\ n = 5 \/
         x = 11 /\ n = 7 \/ x = 181 /\ n = 15`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV] THEN
  DISCH_TAC THEN DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o
      REWRITE_RULE[EVEN_EXISTS]) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP RAMANUJAN_NAGELL_EVEN) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [UNDISCH_TAC `x EXP 2 + 7 = 2 EXP n` THEN ASM_REWRITE_TAC[EXP_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?m. n = m + 2` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `n - 2` THEN
    SUBGOAL_THEN `~(n = 0)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `ODD n` THEN ASM_REWRITE_TAC[ODD];
      UNDISCH_TAC `~(n = 1)` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `ODD m` ASSUME_TAC THENL
   [UNDISCH_TAC `ODD(m + 2)` THEN REWRITE_TAC[ODD_ADD; ARITH]; ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `m:num`] RAMANUJAN_NAGELL_ALGEBRA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN UNDISCH_TAC `ODD m` THEN
    ASM_REWRITE_TAC[ODD];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `m:num` RAMANUJAN_NAGELL_SEQ_PM1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THENL
   [MP_TAC(SPECL [`x:num`; `1`] RAMANUJAN_NAGELL_ROOT);
    MP_TAC(SPECL [`x:num`; `5`] RAMANUJAN_NAGELL_ROOT);
    MP_TAC(SPECL [`x:num`; `11`] RAMANUJAN_NAGELL_ROOT);
    MP_TAC(SPECL [`x:num`; `181`] RAMANUJAN_NAGELL_ROOT)] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV);;
