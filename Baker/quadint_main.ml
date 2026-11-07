(* ========================================================================= *)
(* The ring of integers of Q(sqrt(-d)) is a UFD, equivalently a PID,         *)
(* equivalently of class number one, iff d is m^2 k with k one of the nine   *)
(* values of Gauss.                                                          *)
(*                                                                           *)
(* Purpose: for squarefree d, imag_quadratic_integers d (the algebraic       *)
(* integers of Q(sqrt(-d)) as a subring of complex_ring) is a PID iff it is  *)
(* a UFD iff its ideal class number is 1 iff form_classno (qdisc d) = 1      *)
(* (QUAD_PID_EQ_CLASSNO_ONE, QUAD_UFD_EQ_CLASSNO_ONE,                        *)
(* IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS): a PID is a UFD (PID_IMP_UFD of   *)
(* Library/ringtheory.ml), a UFD has form class number one                   *)
(* (QUAD_UFD_IMP_CLASSNO_ONE) and form class number one gives a PID          *)
(* (QUAD_CLASSNO_ONE_IMP_PID); PID iff class number 1 holds in every         *)
(* Dedekind ring of integers                                                 *)
(* (IMAG_QUADRATIC_INTEGERS_PID_EQ_CLASS_NUMBER_1). With CLASS_NUMBER_ONE    *)
(* (Baker, Transcendental Number Theory, Theorem 5.1) these rings are those  *)
(* with d in {1, 2, 3, 7, 11, 19, 43, 67, 163}. For every d, writing d = m^2 *)
(* k with k squarefree (m <> 0 unless d = 0), the ring of d is that of k     *)
(* (IMAG_QUADRATIC_INTEGERS_SQUARE_MUL) and the ring of 0 is Z, a PID        *)
(* (PID_IMAG_QUADRATIC_INTEGERS_0); so for every d the ring is a PID, a UFD, *)
(* of class number one, iff d = m^2 k for some m and some k among the nine   *)
(* (CLASS_NUMBER_ONE_PID, CLASS_NUMBER_ONE_UFD,                              *)
(* CLASS_NUMBER_ONE_IDEAL_CLASSES; d = 0 with m = 0). With                   *)
(* UFD_EQ_UNIQUE_FACTORIZATION the same holds for the explicit statement:    *)
(* every nonzero element is associate to a product of irreducibles, unique   *)
(* up to order and associates (CLASS_NUMBER_ONE_UNIQUE_FACTORIZATION).       *)
(*                                                                           *)
(* Main results: QUAD_PID_EQ_CLASSNO_ONE, QUAD_UFD_EQ_CLASSNO_ONE,           *)
(* IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS, CLASS_NUMBER_ONE_PID,             *)
(* CLASS_NUMBER_ONE_UFD, CLASS_NUMBER_ONE_IDEAL_CLASSES,                     *)
(* CLASS_NUMBER_ONE_UNIQUE_FACTORIZATION; helpers                            *)
(* CLASS_NUMBER_ONE_NINE_SQUAREFREE (the nine are squarefree) and            *)
(* CLASS_NUMBER_ONE_REDUCTION (from squarefree d to all d, for any property  *)
(* of the rings that holds for d = 0).                                       *)
(*                                                                           *)
(* Uses: Baker/quadint_ant.ml (IMAG_QUADRATIC_INTEGERS_UFD_EQ_PID,           *)
(* IMAG_QUADRATIC_INTEGERS_PID_EQ_CLASS_NUMBER_1,                            *)
(* IMAG_QUADRATIC_INTEGERS_SQUARE_MUL, PID_IMAG_QUADRATIC_INTEGERS_0,        *)
(* IMAG_QUADRATIC_INTEGERS_INTEGRAL_DOMAIN,                                  *)
(* IMAG_QUADRATIC_INTEGERS_CLAUSES), Baker/quadint_ufd.ml                    *)
(* (QUAD_UFD_IMP_CLASSNO_ONE), Baker/quadint_pid.ml                          *)
(* (QUAD_CLASSNO_ONE_IMP_PID), Baker/classno_main.ml (CLASS_NUMBER_ONE),     *)
(* Library/pocklington.ml (SQUAREFREE_DECOMPOSITION, PRIME_IMP_SQUAREFREE),  *)
(* Library/ringtheory.ml (PID_IMP_UFD, UFD_EQ_UNIQUE_FACTORIZATION).         *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files, 100/dirichlet.ml before *)
(* Multivariate/gamma.ml), so that the file also loads alone.                *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Baker/classno_main.ml";;
needs "Baker/quadint_pid.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* PID, UFD and class number one (squarefree d).                             *)
(* ------------------------------------------------------------------------- *)

let QUAD_PID_EQ_CLASSNO_ONE = prove
 (`!d. squarefree d
       ==> (PID (imag_quadratic_integers d) <=> form_classno (qdisc d) = 1)`,
  MESON_TAC[PID_IMP_UFD; QUAD_UFD_IMP_CLASSNO_ONE; QUAD_CLASSNO_ONE_IMP_PID]);;

let QUAD_UFD_EQ_CLASSNO_ONE = prove
 (`!d. squarefree d
       ==> (UFD (imag_quadratic_integers d) <=> form_classno (qdisc d) = 1)`,
  MESON_TAC[PID_IMP_UFD; QUAD_UFD_IMP_CLASSNO_ONE; QUAD_CLASSNO_ONE_IMP_PID]);;

let IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS = prove
 (`!d. squarefree d
       ==> (class_number (imag_quadratic_integers d) = 1 <=>
            form_classno (qdisc d) = 1)`,
  SIMP_TAC[GSYM IMAG_QUADRATIC_INTEGERS_PID_EQ_CLASS_NUMBER_1;
           QUAD_PID_EQ_CLASSNO_ONE]);;

(* ------------------------------------------------------------------------- *)
(* The nine fields of Gauss, for every d: d = m^2 k with k among the nine.   *)
(* ------------------------------------------------------------------------- *)

let CLASS_NUMBER_ONE_NINE_SQUAREFREE = prove
 (`!k. k IN {1,2,3,7,11,19,43,67,163} ==> squarefree k`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SQUAREFREE_1] THEN MATCH_MP_TAC PRIME_IMP_SQUAREFREE THEN
  CONV_TAC PRIME_CONV);;

let CLASS_NUMBER_ONE_REDUCTION = prove
 (`!P. P(imag_quadratic_integers 0) /\
       (!d. squarefree d
            ==> (P(imag_quadratic_integers d) <=>
                 d IN {1,2,3,7,11,19,43,67,163}))
       ==> !d. P(imag_quadratic_integers d) <=>
               ?m k. d = m EXP 2 * k /\ k IN {1,2,3,7,11,19,43,67,163}`,
  GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `d:num` THEN EQ_TAC THENL
   [ASM_CASES_TAC `d = 0` THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`0`; `1`] THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPEC `d:num` SQUAREFREE_DECOMPOSITION) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(m = 0) /\ d = m EXP 2 * k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(d = 0)` THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_SQUARE_MUL] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`m:num`; `k:num`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `k:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_REWRITE_TAC[ARITH_RULE `0 EXP 2 * k = 0`];
      ASM_SIMP_TAC[IMAG_QUADRATIC_INTEGERS_SQUARE_MUL] THEN
      ASM_MESON_TAC[CLASS_NUMBER_ONE_NINE_SQUAREFREE]]]);;

let CLASS_NUMBER_ONE_PID = prove
 (`!d. PID (imag_quadratic_integers d) <=>
       ?m k. d = m EXP 2 * k /\ k IN {1,2,3,7,11,19,43,67,163}`,
  MATCH_MP_TAC CLASS_NUMBER_ONE_REDUCTION THEN
  REWRITE_TAC[PID_IMAG_QUADRATIC_INTEGERS_0] THEN
  SIMP_TAC[QUAD_PID_EQ_CLASSNO_ONE; CLASS_NUMBER_ONE]);;

let CLASS_NUMBER_ONE_UFD = prove
 (`!d. UFD (imag_quadratic_integers d) <=>
       ?m k. d = m EXP 2 * k /\ k IN {1,2,3,7,11,19,43,67,163}`,
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_UFD_EQ_PID; CLASS_NUMBER_ONE_PID]);;

let CLASS_NUMBER_ONE_IDEAL_CLASSES = prove
 (`!d. class_number (imag_quadratic_integers d) = 1 <=>
       ?m k. d = m EXP 2 * k /\ k IN {1,2,3,7,11,19,43,67,163}`,
  REWRITE_TAC[GSYM IMAG_QUADRATIC_INTEGERS_PID_EQ_CLASS_NUMBER_1;
              CLASS_NUMBER_ONE_PID]);;

(* ------------------------------------------------------------------------- *)
(* Unique factorization into irreducibles, explicitly.                       *)
(* ------------------------------------------------------------------------- *)

let CLASS_NUMBER_ONE_UNIQUE_FACTORIZATION = prove
 (`!d. (!x. x IN ring_carrier (imag_quadratic_integers d) /\
            ~(x = Cx(&0))
            ==> ?n p.
                  (!i. 1 <= i /\ i <= n
                       ==> ring_irreducible (imag_quadratic_integers d)
                                            (p i)) /\
                  ring_associates (imag_quadratic_integers d)
                    (ring_product (imag_quadratic_integers d) (1..n) p)
                    x /\
                  !m q. (!j. 1 <= j /\ j <= m
                             ==> ring_irreducible
                                   (imag_quadratic_integers d) (q j)) /\
                        ring_associates (imag_quadratic_integers d)
                          (ring_product (imag_quadratic_integers d)
                             (1..m) q)
                          x
                        ==> ?f. IMAGE f (1..n) = 1..m /\
                                (!i j. 1 <= i /\ i <= n /\
                                       1 <= j /\ j <= n
                                       ==> (f i = f j <=> i = j)) /\
                                (!i. 1 <= i /\ i <= n
                                     ==> ring_associates
                                           (imag_quadratic_integers d)
                                           (p i) (q(f i)))) <=>
       ?m k. d = m EXP 2 * k /\ k IN {1,2,3,7,11,19,43,67,163}`,
  REWRITE_TAC[GSYM CLASS_NUMBER_ONE_UFD] THEN
  REWRITE_TAC[UFD_EQ_UNIQUE_FACTORIZATION;
              IMAG_QUADRATIC_INTEGERS_INTEGRAL_DOMAIN;
              IMAG_QUADRATIC_INTEGERS_CLAUSES]);;
