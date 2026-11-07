(* ========================================================================= *)
(* Fermat: the only integer solutions of x^2 + 2 = y^3 are x = +-5, y = 3;   *)
(* so 26 is the only natural number between a square and a cube.             *)
(*                                                                           *)
(* Purpose: the classical application of unique factorization in Z[sqrt(-2)] *)
(* (claimed by Fermat, proved by Euler with a gap filled by unique           *)
(* factorization): FERMAT_SQUARE_CUBE over the integers and FERMAT_26 over   *)
(* the natural numbers.                                                      *)
(*                                                                           *)
(* Method (Euler): x is odd (for x = 2k, y^3 = 4 k^2 + 2 is 2 mod 4, while a *)
(* cube is odd or divisible by 8). In the ring O = imag_quadratic_integers 2 *)
(* = Z[w], w = sqrt(-2), w^2 = -2, a UFD and a PID (Euclidean:               *)
(* IMAG_QUADRATIC_INTEGERS_UFD, _PID), we have (x + w) (x - w) = y^3, and    *)
(* the two factors are coprime: for x = 2k + 1 the explicit identity (x + w) *)
(* U + (x - w) V = 1 with U = 1 + (k + 1)^2 w and V = (2k + 2) - k (k + 2) w *)
(* (BEZOUT_RING_COPRIME). By UFD_COPRIME_MUL_POW (k = 3) x + w is a unit     *)
(* times a cube, and the units of O are +-1                                  *)
(* (IMAG_QUADRATIC_INTEGERS_UNIT_GENERIC), themselves cubes: x + w = (p + q  *)
(* w)^3, whose coordinates give x = p^3 - 6 p q^2 and 1 = q (3 p^2 - 2 q^2), *)
(* so q = 1, p = +-1, x = -+5 and y^3 = 27, y = 3.                           *)
(*                                                                           *)
(* Main results: FERMAT_SQUARE_CUBE, FERMAT_26; the real-integer form        *)
(* FERMAT_26_REAL; helper names FERMAT_26_*.                                 *)
(*                                                                           *)
(* Uses: Baker/quadint_ring.ml (IMAG_QUADRATIC_INTEGERS_IN, _UNIT_GENERIC,   *)
(* _PID, _UFD, _IN_COORDS, _CX, _CLOSED, QUAD_OMEGA_SQUARE,                  *)
(* QUAD_OMEGA_COORDS, QUAD_INTEGER_PARITY, QUAD_INTEGER_TAC),                *)
(* Baker/quadint_ant.ml (IMAG_QUADRATIC_INTEGERS_CLAUSES, _SUB_POW),         *)
(* ANT/ufd.ml (UFD_COPRIME_MUL_POW), Library/ringtheory.ml (ring_coprime,    *)
(* BEZOUT_RING_COPRIME, PID_IMP_BEZOUT_RING, RING_UNIT_IN_CARRIER),          *)
(* Library/floor.ml (INTEGER_ABS_MUL_EQ_1, REAL_ABS_INTEGER_LEMMA), int.ml   *)
(* (int_eq, int_add_th, int_pow_th: transfer to the reals).                  *)
(* ========================================================================= *)

needs "ANT/ufd.ml";;
needs "Baker/quadint_ring.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The ring Z[sqrt(-2)]: squarefree, a UFD, w^2 = -2, the carrier.           *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_SQUAREFREE = prove
 (`squarefree 2`,
  MATCH_MP_TAC PRIME_IMP_SQUAREFREE THEN REWRITE_TAC[PRIME_2]);;

let FERMAT_26_UFD = prove
 (`UFD(imag_quadratic_integers 2)`,
  MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_UFD THEN REWRITE_TAC[IN_INSERT]);;

let FERMAT_26_OMEGA = prove
 (`quad_omega 2 pow 2 = --Cx(&2)`,
  REWRITE_TAC[QUAD_OMEGA_SQUARE] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let FERMAT_26_IN = prove
 (`!z. z IN ring_carrier(imag_quadratic_integers 2) <=>
       ?x y. integer x /\ integer y /\ z = Cx x + Cx y * quad_omega 2`,
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_IN; FERMAT_26_SQUAREFREE]);;

(* ------------------------------------------------------------------------- *)
(* Small facts on integers.                                                  *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_INTEGER_SQUARE = prove
 (`!t. integer t ==> t pow 2 = &0 \/ &1 <= t pow 2`,
  GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `t = &0` THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISJ2_TAC] THEN
  MP_TAC(SPEC `t:real` REAL_ABS_INTEGER_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&1:real`; `t:real`] REAL_LE_SQUARE_ABS) THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE] THEN MESON_TAC[]);;

let FERMAT_26_INTEGER_HALF = prove
 (`!z. integer z ==> ~(&2 * z = &1)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `z:real` REAL_ABS_INTEGER_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The units of Z[sqrt(-2)] are +-1.                                         *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_UNIT = prove
 (`!u. ring_unit (imag_quadratic_integers 2) u
       ==> u = Cx(&1) \/ u = --Cx(&1)`,
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_UNIT_GENERIC; FERMAT_26_SQUAREFREE;
           ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* For odd x = 2k + 1, x + w and x - w are coprime: an explicit Bezout       *)
(* identity.                                                                 *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_COPRIME = prove
 (`!k. integer k
       ==> ring_coprime (imag_quadratic_integers 2)
            (Cx(&2 * k + &1) + Cx(&1) * quad_omega 2,
             Cx(&2 * k + &1) + Cx(-- &1) * quad_omega 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BEZOUT_RING_COPRIME; PID_IMP_BEZOUT_RING; IN_INSERT;
               IMAG_QUADRATIC_INTEGERS_PID; IMAG_QUADRATIC_INTEGERS_CLAUSES;
               IMAG_QUADRATIC_INTEGERS_IN_COORDS; INTEGER_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`Cx(&1) + Cx((k + &1) pow 2) * quad_omega 2`;
    `Cx(&2 * k + &2) + Cx(--k * (k + &2)) * quad_omega 2`] THEN
  ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_IN_COORDS; INTEGER_CLOSED] THEN
  MP_TAC FERMAT_26_OMEGA THEN
  REWRITE_TAC[CX_ADD; CX_MUL; CX_NEG; CX_POW] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Hence x + w is a cube in Z[sqrt(-2)].                                     *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_CUBE = prove
 (`!k y. integer k /\ integer y /\ (&2 * k + &1) pow 2 + &2 = y pow 3
         ==> ?p q. integer p /\ integer q /\
                   Cx(&2 * k + &1) + Cx(&1) * quad_omega 2 =
                   (Cx p + Cx q * quad_omega 2) pow 3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`imag_quadratic_integers 2`;
                 `Cx(&2 * k + &1) + Cx(&1) * quad_omega 2`;
                 `Cx(&2 * k + &1) + Cx(-- &1) * quad_omega 2`;
                 `Cx y`; `3`] UFD_COPRIME_MUL_POW) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES;
              IMAG_QUADRATIC_INTEGERS_SUB_POW] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FERMAT_26_UFD; FERMAT_26_COPRIME;
                 IMAG_QUADRATIC_INTEGERS_IN_COORDS;
                 IMAG_QUADRATIC_INTEGERS_CX; INTEGER_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `Cx`) THEN MP_TAC FERMAT_26_OMEGA THEN
    REWRITE_TAC[CX_ADD; CX_MUL; CX_NEG; CX_POW] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:complex`; `e:complex`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `u * e IN ring_carrier(imag_quadratic_integers 2)` MP_TAC THENL
   [ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CLOSED; RING_UNIT_IN_CARRIER];
    ALL_TAC] THEN
  REWRITE_TAC[FERMAT_26_IN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP FERMAT_26_UNIT) THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The coordinates of a cube, and the Diophantine consequence.               *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_CUBE_COORDS = prove
 (`!p q:real.
        (Cx p + Cx q * quad_omega 2) pow 3 =
        Cx(p pow 3 - &6 * p * q pow 2) +
        Cx(&3 * p pow 2 * q - &2 * q pow 3) * quad_omega 2`,
  REPEAT GEN_TAC THEN MP_TAC FERMAT_26_OMEGA THEN
  REWRITE_TAC[CX_SUB; CX_MUL; CX_POW] THEN CONV_TAC COMPLEX_RING);;

let FERMAT_26_DIOPH = prove
 (`!p q. integer p /\ integer q /\ &3 * p pow 2 * q - &2 * q pow 3 = &1
         ==> q = &1 /\ (p = &1 \/ p = -- &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs q = &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`q:real`; `&3 * p pow 2 - &2 * q pow 2`]
      INTEGER_ABS_MUL_EQ_1) THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    SUBGOAL_THEN `q * (&3 * p pow 2 - &2 * q pow 2) = &1` SUBST1_TAC THENL
     [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; SIMP_TAC[REAL_ABS_NUM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 * p pow 2 - &2 = q` ASSUME_TAC THENL
   [SUBGOAL_THEN `q pow 2 = &1` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      ASM_REWRITE_TAC[REAL_POW_ONE];
      UNDISCH_TAC `&3 * p pow 2 * q - &2 * q pow 3 = &1` THEN
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = &1 /\ p pow 2 = &1` MP_TAC THENL
   [MP_TAC(SPEC `p:real` FERMAT_26_INTEGER_SQUARE) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`abs q = &1`; `&3 * p pow 2 - &2 = q`] THEN
    REAL_ARITH_TAC;
    CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* x is odd.                                                                 *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_NOT_EVEN = prove
 (`!k y. integer k /\ integer y ==> ~((&2 * k) pow 2 + &2 = y pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `y:real` QUAD_INTEGER_PARITY) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:real`; `s:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 DISJ_CASES_TAC SUBST1_TAC)) THEN
  FIRST_X_ASSUM SUBST1_TAC THENL
   [MP_TAC(SPEC `&2 * j pow 3 - k pow 2` FERMAT_26_INTEGER_HALF);
    MP_TAC(SPEC `&4 * j pow 3 + &6 * j pow 2 + &3 * j - &2 * k pow 2`
      FERMAT_26_INTEGER_HALF)] THEN
  (ANTS_TAC THENL [QUAD_INTEGER_TAC; CONV_TAC REAL_RING]));;

let FERMAT_26_ODD = prove
 (`!x y. integer x /\ integer y /\ x pow 2 + &2 = y pow 3
         ==> ?k. integer k /\ x = &2 * k + &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `x:real` QUAD_INTEGER_PARITY) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real`; `r:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 DISJ_CASES_TAC SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THENL
   [UNDISCH_TAC `(&2 * k + &0) pow 2 + &2 = y pow 3` THEN
    REWRITE_TAC[REAL_ADD_RID] THEN ASM_SIMP_TAC[FERMAT_26_NOT_EVEN];
    EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The theorem for real integers, over the integers, over the naturals.      *)
(* ------------------------------------------------------------------------- *)

let FERMAT_26_REAL = prove
 (`!x y. integer x /\ integer y
         ==> (x pow 2 + &2 = y pow 3 <=> (x = &5 \/ x = -- &5) /\ y = &3)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  SUBGOAL_THEN `x = &5 \/ x = -- &5` ASSUME_TAC THENL
   [MP_TAC(SPECL [`x:real`; `y:real`] FERMAT_26_ODD) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    MP_TAC(SPECL [`k:real`; `y:real`] FERMAT_26_CUBE) THEN
    ASM_REWRITE_TAC[FERMAT_26_CUBE_COORDS; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`2`; `&2 * k + &1`; `&1`; `p pow 3 - &6 * p * q pow 2`;
                  `&3 * p pow 2 * q - &2 * q pow 3`] QUAD_OMEGA_COORDS) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (ASSUME_TAC o SYM)) THEN
    MP_TAC(SPECL [`p:real`; `q:real`] FERMAT_26_DIOPH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (DISJ_CASES_THEN SUBST1_TAC)) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_EQ_ODD THEN EXISTS_TAC `3` THEN
  REWRITE_TAC[ARITH] THEN
  UNDISCH_TAC `x pow 2 + &2 = y pow 3` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

let FERMAT_SQUARE_CUBE = prove
 (`!x y:int. x pow 2 + &2 = y pow 3 <=> (x = &5 \/ x = -- &5) /\ y = &3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[int_eq; int_add_th; int_pow_th; int_neg_th; int_of_num_th] THEN
  MATCH_MP_TAC FERMAT_26_REAL THEN REWRITE_TAC[INTEGER_REAL_OF_INT]);;

let FERMAT_26 = prove
 (`!n. (?x. n = x EXP 2 + 1) /\ (?y. n + 1 = y EXP 3) <=> n = 26`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(&x:real) pow 2 + &2 = &y pow 3` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
      ASM_ARITH_TAC;
      SIMP_TAC[FERMAT_26_REAL; INTEGER_CLOSED]] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; REAL_ARITH `~(&x:real = -- &5)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `5`; EXISTS_TAC `3`] THEN
    CONV_TAC NUM_REDUCE_CONV]);;
