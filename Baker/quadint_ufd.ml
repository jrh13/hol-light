(* ========================================================================= *)
(* Unique factorization in the ring of integers of Q(sqrt(-d)) forces class  *)
(* number one.                                                               *)
(*                                                                           *)
(* Purpose: for squarefree d, if the ring of integers O of Q(sqrt(-d))       *)
(* (imag_quadratic_integers d) is a UFD then form_classno (qdisc d) = 1.     *)
(* Contrapositive: if the class number is not 1 there is a reduced form (a,  *)
(* b, c) of discriminant D = qdisc d other than the principal form, so a >=  *)
(* 2 (a = 1 forces the principal form) and 3 a^2 <= |D|. For a prime p       *)
(* dividing a, gamma = (b + sqrt D)/2 = x + omega has norm a c, so p divides *)
(* gamma * cnj gamma in O but neither gamma nor cnj gamma (their omega       *)
(* coordinates are 1 and -1). And p is irreducible in O: a proper factor     *)
(* would have norm p, but x^2 = p is impossible and the elements x + y omega *)
(* with y <> 0 have norm >= |D|/4 > p. So p is irreducible but not prime,    *)
(* hence O is not a UFD (UFD_IRREDUCIBLE_EQ_PRIME). The primitivity of the   *)
(* second form is not needed.                                                *)
(*                                                                           *)
(* Main results: QUAD_UFD_IMP_CLASSNO_ONE; helper names QUAD_UFD_*.          *)
(*                                                                           *)
(* Uses: Baker/quadint_ring.ml (IMAG_QUADRATIC_INTEGERS_CARRIER,             *)
(* IMAG_QUADRATIC_INTEGERS_IN, _IN_COORDS, _CX, _CNJ, _NORM_POW_2, _UNIT,    *)
(* QUAD_OMEGA_CNJ, QUAD_OMEGA_NORM, QUAD_OMEGA_COORDS, QUAD_DMOD4_REAL),     *)
(* Baker/quadint_ant.ml (IMAG_QUADRATIC_INTEGERS_CLAUSES),                   *)
(* Baker/classno_forms.ml (CLASSNO_PRINCIPAL_REDUCED, QF_REDUCED_DISC,       *)
(* QF_FORMS_IN), Baker/classno_series.ml (CLASSNO_SERIES_C0),                *)
(* Library/ringtheory.ml (UFD_IRREDUCIBLE_EQ_PRIME), Library/pocklington.ml  *)
(* (SQUAREFREE_IMP_NZ).                                                      *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Baker/quadint_ring.ml";;
needs "Baker/classno_forms.ml";;
needs "Baker/classno_series.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* A rational prime p with 4 p < |qdisc d| is irreducible.                  *)
(* ------------------------------------------------------------------------- *)

let QUAD_UFD_NORM_NE_PRIME = prove
 (`!d x y p. integer x /\ integer y /\ prime p /\
             &4 * &p < (if d MOD 4 = 3 then &d else &4 * &d:real)
             ==> ~(norm(Cx x + Cx y * quad_omega d) pow 2 = &p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[QUAD_OMEGA_NORM] THEN
  ASM_CASES_TAC `y = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_POW_ZERO; ARITH_EQ;
                    COND_ID] THEN
    UNDISCH_TAC `integer x` THEN REWRITE_TAC[integer] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `prime(n EXP 2)` THEN REWRITE_TAC[PRIME_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= y pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&d * &1 <= &d * y pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  COND_CASES_TAC THEN
  UNDISCH_TAC `&4 * &p < (if d MOD 4 = 3 then &d else &4 * &d:real)` THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `(&4 * &((d + 1) DIV 4)) * y pow 2 = (&d + &1) * y pow 2`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[QUAD_DMOD4_REAL]; ALL_TAC] THEN
    MP_TAC(SPEC `&2 * x + y` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC]);;

let QUAD_UFD_PRIME_IRREDUCIBLE = prove
 (`!d p. squarefree d /\ prime p /\
         &4 * &p < (if d MOD 4 = 3 then &d else &4 * &d:real)
         ==> ring_irreducible (imag_quadratic_integers d) (Cx(&p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  REWRITE_TAC[ring_irreducible; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  SUBGOAL_THEN `Cx(&p) IN ring_carrier (imag_quadratic_integers d)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CX; INTEGER_CLOSED];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `2 <= p` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ring_unit; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:complex` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    MP_TAC(SPECL [`d:num`; `u:complex`]
      IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    UNDISCH_TAC `Cx(&p) * u = Cx(&1)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:complex. norm z pow 2`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL; COMPLEX_NORM_CX;
                    REAL_ABS_NUM; REAL_OF_NUM_POW; REAL_OF_NUM_MUL;
                    REAL_OF_NUM_EQ; EXP_ONE; MULT_EQ_1; EXP_EQ_1] THEN
    UNDISCH_TAC `2 <= p` THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `a:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  MP_TAC(SPECL [`d:num`; `b:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `m * n = p EXP 2` ASSUME_TAC THENL
   [UNDISCH_TAC `a * b = Cx(&p)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:complex. norm z pow 2`) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL; COMPLEX_NORM_CX;
                    REAL_ABS_NUM; REAL_OF_NUM_POW; REAL_OF_NUM_MUL;
                    REAL_OF_NUM_EQ];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [DISJ1_TAC THEN UNDISCH_TAC `norm(a:complex) pow 2 = &m` THEN
    ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_UNIT; REAL_POW_EQ_1;
                    REAL_ABS_NORM; ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 1` THENL
   [DISJ2_TAC THEN UNDISCH_TAC `norm(b:complex) pow 2 = &n` THEN
    ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_UNIT; REAL_POW_EQ_1;
                    REAL_ABS_NORM; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `m:num = p` ASSUME_TAC THENL
   [MP_TAC(SPEC `m:num` (MATCH_MP (INST [`2`,`k:num`] DIVIDES_PRIMEPOW)
                                  (ASSUME `prime p`))) THEN
    MATCH_MP_TAC(TAUT `s /\ (t ==> u) ==> (s <=> t) ==> u`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[divides] THEN EXISTS_TAC `n:num` THEN
      FIRST_ASSUM(ACCEPT_TAC o SYM);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2` MP_TAC THENL
     [UNDISCH_TAC `i <= 2` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [UNDISCH_TAC `~(m = 1)` THEN ASM_REWRITE_TAC[EXP];
      ASM_REWRITE_TAC[EXP_1];
      UNDISCH_TAC `~(n = 1)` THEN UNDISCH_TAC `m * n = p EXP 2` THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[ARITH_RULE `x * n = x <=> x * n = x * 1`] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL; EXP_EQ_0] THEN
      UNDISCH_TAC `2 <= p` THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `a:complex`] IMAG_QUADRATIC_INTEGERS_IN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` (X_CHOOSE_THEN `y:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `norm(Cx x + Cx y * quad_omega d) pow 2 = &p` MP_TAC THENL
   [UNDISCH_TAC `norm(a:complex) pow 2 = &m` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~s ==> s ==> t`) THEN
  MATCH_MP_TAC QUAD_UFD_NORM_NE_PRIME THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* p is not prime when it divides the norm of x + omega.                     *)
(* ------------------------------------------------------------------------- *)

let QUAD_UFD_NOT_DIVIDES = prove
 (`!d p x y. squarefree d /\ 2 <= p /\ integer y /\ abs y = &1
             ==> ~ring_divides (imag_quadratic_integers d) (Cx(&p))
                               (Cx x + Cx y * quad_omega d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ring_divides; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex` MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(SPECL [`d:num`; `z:complex`] IMAG_QUADRATIC_INTEGERS_IN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `Cx(&p) * (Cx u + Cx v * quad_omega d) =
                Cx(&p * u) + Cx(&p * v) * quad_omega d` SUBST1_TAC THENL
   [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP QUAD_OMEGA_COORDS o
    CONJ (MATCH_MP (ARITH_RULE `~(d = 0) ==> 1 <= d`)
      (MATCH_MP SQUAREFREE_IMP_NZ (ASSUME `squarefree d`)))) THEN
  DISCH_TAC THEN UNDISCH_TAC `abs y = &1` THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  UNDISCH_TAC `integer v` THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ; MULT_EQ_1] THEN
  UNDISCH_TAC `2 <= p` THEN ARITH_TAC);;

let QUAD_UFD_CNJ_OMEGA1 = prove
 (`!d x. integer x
         ==> ?x'. integer x' /\
                  cnj(Cx x + Cx(&1) * quad_omega d) =
                  Cx x' + Cx(-- &1) * quad_omega d`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_CX; QUAD_OMEGA_CNJ] THEN
  COND_CASES_TAC THENL
   [EXISTS_TAC `x + &1` THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[CX_ADD; CX_NEG] THEN CONV_TAC COMPLEX_RING;
    EXISTS_TAC `x:real` THEN ASM_REWRITE_TAC[CX_NEG] THEN
    CONV_TAC COMPLEX_RING]);;

let QUAD_UFD_NOT_PRIME = prove
 (`!d p x k. squarefree d /\ prime p /\ integer x /\ integer k /\
             norm(Cx x + Cx(&1) * quad_omega d) pow 2 = &p * k
             ==> ~ring_prime (imag_quadratic_integers d) (Cx(&p))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `Cx x + Cx(&1) * quad_omega d
                IN ring_carrier (imag_quadratic_integers d)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_IN_COORDS THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `cnj(Cx x + Cx(&1) * quad_omega d)
                IN ring_carrier (imag_quadratic_integers d)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_CNJ THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ring_prime; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  DISCH_THEN(MP_TAC o SPECL [`Cx x + Cx(&1) * quad_omega d`;
                             `cnj(Cx x + Cx(&1) * quad_omega d)`] o
             CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `s /\ ~t /\ ~u ==> ~(s ==> t \/ u)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[ring_divides; COMPLEX_MUL_CNJ; GSYM CX_POW;
                    IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
    ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_CX; INTEGER_CLOSED] THEN
    EXISTS_TAC `Cx k` THEN ASM_REWRITE_TAC[CX_MUL; IMAG_QUADRATIC_INTEGERS_CX];
    MATCH_MP_TAC QUAD_UFD_NOT_DIVIDES THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`d:num`; `x:real`] QUAD_UFD_CNJ_OMEGA1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':real` (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    MATCH_MP_TAC QUAD_UFD_NOT_DIVIDES THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC]);;

let QUAD_UFD_NOT_UFD = prove
 (`!d p x k. squarefree d /\ prime p /\
             &4 * &p < (if d MOD 4 = 3 then &d else &4 * &d:real) /\
             integer x /\ integer k /\
             norm(Cx x + Cx(&1) * quad_omega d) pow 2 = &p * k
             ==> ~UFD(imag_quadratic_integers d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_irreducible (imag_quadratic_integers d) (Cx(&p))`
  MP_TAC THENL
   [MATCH_MP_TAC QUAD_UFD_PRIME_IRREDUCIBLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[UFD_IRREDUCIBLE_EQ_PRIME] THEN
  MATCH_MP_TAC QUAD_UFD_NOT_PRIME THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `k:real`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The form side: a second reduced form gives a prime p and an integer x     *)
(* with p dividing x^2 + x + (d + 1)/4 resp. x^2 + d, and 4 p < |qdisc d|.   *)
(* ------------------------------------------------------------------------- *)

let QUAD_UFD_MOD4_INT = prove
 (`!d t:int. d MOD 4 = 3 ==> ~(&d = &4 * t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `4 divides d` MP_TAC THENL
   [REWRITE_TAC[num_divides; int_divides] THEN EXISTS_TAC `t:int` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[DIVIDES_MOD; ARITH_EQ]]);;

let QUAD_UFD_ONE_NE_4 = prove
 (`!t:int. ~(&1 = &4 * t)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `4 divides 1` MP_TAC THENL
   [REWRITE_TAC[num_divides; int_divides] THEN EXISTS_TAC `t:int` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[DIVIDES_ONE; ARITH_EQ]]);;

let QUAD_UFD_INT_PARITY = prove
 (`!b:int. ?q. b = &2 * q \/ b = &2 * q + &1`,
  GEN_TAC THEN EXISTS_TAC `b div &2` THEN
  MP_TAC(SPECL [`b:int`; `&2:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN INT_ARITH_TAC);;

let QUAD_UFD_PARITY = prove
 (`!d a b c:int.
        b pow 2 - &4 * a * c = qdisc d
        ==> ?x. b = &2 * x + (if d MOD 4 = 3 then &1 else &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qdisc] THEN
  X_CHOOSE_THEN `q:int` (DISJ_CASES_THEN SUBST1_TAC)
    (SPEC `b:int` QUAD_UFD_INT_PARITY) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN DISCH_TAC THENL
   [SUBGOAL_THEN `&d = &4 * (a * c - q pow 2):int` MP_TAC THENL
     [POP_ASSUM MP_TAC THEN INT_ARITH_TAC; ASM_SIMP_TAC[QUAD_UFD_MOD4_INT]];
    EXISTS_TAC `q:int` THEN INT_ARITH_TAC;
    EXISTS_TAC `q:int` THEN INT_ARITH_TAC;
    SUBGOAL_THEN `&1 = &4 * ((a * c - q pow 2 - q) - &d):int` MP_TAC THENL
     [POP_ASSUM MP_TAC THEN INT_ARITH_TAC; REWRITE_TAC[QUAD_UFD_ONE_NE_4]]]);;

let QUAD_UFD_REDUCED_ONE = prove
 (`!b c:int. qf_reduced (&1) b c ==> b = &0 \/ b = &1`,
  REWRITE_TAC[qf_reduced] THEN INT_ARITH_TAC);;

let QUAD_UFD_PRINCIPAL_FORM = prove
 (`!d. squarefree d
       ==> ?b0 c0. qf_reduced (&1) b0 c0 /\
                   b0 pow 2 - &4 * &1 * c0 = qdisc d /\
                   gcd(&1,gcd(b0,c0)) = &1 /\
                   !b c. qf_reduced (&1) b c /\
                         b pow 2 - &4 * &1 * c = qdisc d
                         ==> b = b0 /\ c = c0`,
  GEN_TAC THEN DISCH_THEN(ASSUME_TAC o MATCH_MP
   (ARITH_RULE `~(d = 0) ==> 1 <= d`) o MATCH_MP SQUAREFREE_IMP_NZ) THEN
  REWRITE_TAC[qdisc; INT_GCD_1] THEN COND_CASES_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&1:int`; `&((d + 1) DIV 4):int`] THEN
    ASM_SIMP_TAC[CLASSNO_PRINCIPAL_REDUCED] THEN
    MAP_EVERY X_GEN_TAC [`b:int`; `c:int`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`b:int`; `c:int`] QUAD_UFD_REDUCED_ONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [SUBGOAL_THEN `&d = &4 * c:int` MP_TAC THENL
       [UNDISCH_TAC `&0 pow 2 - &4 * &1 * c = --(&d:int)` THEN INT_ARITH_TAC;
        ASM_SIMP_TAC[QUAD_UFD_MOD4_INT]];
      REWRITE_TAC[] THEN
      MP_TAC(SPEC `d:num` CLASSNO_SERIES_C0) THEN
      ASM_REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL;
                      GSYM INT_OF_NUM_ADD] THEN
      UNDISCH_TAC `&1 pow 2 - &4 * &1 * c = --(&d:int)` THEN INT_ARITH_TAC];
    MAP_EVERY EXISTS_TAC [`&0:int`; `&d:int`] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[qf_reduced] THEN UNDISCH_TAC `1 <= d` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC;
      INT_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`b:int`; `c:int`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`b:int`; `c:int`] QUAD_UFD_REDUCED_ONE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [REWRITE_TAC[] THEN
        UNDISCH_TAC `&0 pow 2 - &4 * &1 * c = --(&4 * &d:int)` THEN
        INT_ARITH_TAC;
        SUBGOAL_THEN `&1 = &4 * (c - &d):int` MP_TAC THENL
         [UNDISCH_TAC `&1 pow 2 - &4 * &1 * c = --(&4 * &d:int)` THEN
          INT_ARITH_TAC;
          REWRITE_TAC[QUAD_UFD_ONE_NE_4]]]]]);;

let QUAD_UFD_CARD_NE_1 = prove
 (`!s:A->bool z. z IN s /\ ~(CARD s = 1) ==> ?q. q IN s /\ ~(q = z)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s = {z:A}` THENL
   [UNDISCH_TAC `~(CARD(s:A->bool) = 1)` THEN ASM_REWRITE_TAC[CARD_SING];
    ASM SET_TAC[]]);;

let QUAD_UFD_SECOND_FORM = prove
 (`!d. squarefree d /\ ~(form_classno (qdisc d) = 1)
       ==> ?a b c. qf_reduced a b c /\ b pow 2 - &4 * a * c = qdisc d /\
                   &2 <= a`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:num` QUAD_UFD_PRINCIPAL_FORM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:int` (X_CHOOSE_THEN `c0:int`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`{(a,b,c) | qf_reduced a b c /\
                             b pow 2 - &4 * a * c = qdisc d /\
                             gcd(a,gcd(b,c)) = &1}`;
                 `(&1:int,b0:int,c0:int)`] QUAD_UFD_CARD_NE_1) THEN
  REWRITE_TAC[GSYM form_classno; QF_FORMS_IN; EXISTS_PAIR_THM; PAIR_EQ] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:int`; `b:int`; `c:int`] THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:int = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`b:int`; `c:int`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `qf_reduced a b c` THEN REWRITE_TAC[qf_reduced] THEN
    UNDISCH_TAC `~(a:int = &1)` THEN INT_ARITH_TAC]);;

let QUAD_UFD_FORM_WITNESS = prove
 (`!d. squarefree d /\ ~(form_classno (qdisc d) = 1)
       ==> ?p x k. prime p /\
                   &4 * &p < (if d MOD 4 = 3 then &d else &4 * &d:int) /\
                   (if d MOD 4 = 3 then x pow 2 + x + &((d + 1) DIV 4)
                    else x pow 2 + &d) = &p * k:int`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP QUAD_UFD_SECOND_FORM) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP QF_REDUCED_DISC) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`d:num`; `a:int`; `b:int`; `c:int`] QUAD_UFD_PARITY) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:int`) THEN
  SUBGOAL_THEN `?n. (a:int) = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int a` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    UNDISCH_TAC `&2 <= a:int` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ANTS_TAC THENL
   [UNDISCH_TAC `&2 <= &n:int` THEN REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `p <= n` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `&2 <= &n:int` THEN REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num` o REWRITE_RULE[divides]) THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `x:int`; `&m * c:int`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&2 * &n <= (&n:int) pow 2` ASSUME_TAC THENL
     [REWRITE_TAC[INT_POW_2] THEN MATCH_MP_TAC INT_LE_RMUL THEN
      UNDISCH_TAC `&2 <= &n:int` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&p <= &n:int` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(if d MOD 4 = 3 then &d else &4 * &d:int) = --(qdisc d)`
    SUBST1_TAC THENL
     [REWRITE_TAC[qdisc] THEN COND_CASES_TAC THEN REWRITE_TAC[INT_NEG_NEG];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`&3 * (&n:int) pow 2 <= &4 * &n * c - b pow 2`;
      `b pow 2 - &4 * &n * c = qdisc d`; `&2 * &n <= (&n:int) pow 2`;
      `&p <= &n:int`; `&2 <= &n:int`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&n = &p * &m:int` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_MUL]; ALL_TAC] THEN
  UNDISCH_TAC `b pow 2 - &4 * &n * c = qdisc d` THEN
  UNDISCH_TAC `(b:int) = &2 * x + (if d MOD 4 = 3 then &1 else &0)` THEN
  DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `&n = &p * &m:int` THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[qdisc] THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MP_TAC(SPEC `d:num` CLASSNO_SERIES_C0) THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_MUL;
                    GSYM INT_OF_NUM_ADD] THEN
    INT_ARITH_TAC;
    INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let QUAD_UFD_IMP_CLASSNO_ONE = prove
 (`!d. squarefree d /\ UFD (imag_quadratic_integers d)
       ==> form_classno (qdisc d) = 1`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `s /\ t ==> u <=> s /\ ~u ==> ~t`] THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `d:num` QUAD_UFD_FORM_WITNESS) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `x:int`; `k:int`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC QUAD_UFD_NOT_UFD THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `real_of_int x`; `real_of_int k`] THEN
  ASM_REWRITE_TAC[INTEGER_REAL_OF_INT; QUAD_OMEGA_NORM; REAL_MUL_RID;
                  REAL_POW_ONE] THEN
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[int_lt; int_eq; int_add_th; int_mul_th; int_pow_th;
              int_of_num_th] THEN
  SIMP_TAC[]);;
