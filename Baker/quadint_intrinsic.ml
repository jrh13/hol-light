(* ========================================================================= *)
(* The class number one theorem for an abstract imaginary quadratic field.   *)
(*                                                                           *)
(* Purpose: the Baker-Heegner-Stark theorem in the language of ANT/, for a   *)
(* number field k:A ring of any type, with no parameter: if [k:Q] = 2 and    *)
(* the discriminant d_k is negative, then O_k = ring_of_integers k has class *)
(* number 1 iff d_k is one of the nine discriminants -3, -4, -7, -8, -11,    *)
(* -19, -43, -67, -163 (IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE), and the same  *)
(* holds for unique factorization and for principal ideals                   *)
(* (IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_UFD, _PID).                         *)
(*                                                                           *)
(* Route: k contains a square root x of a squarefree integer e <> 1 and d_k  *)
(* is e or 4 e (QUADRATIC_FIELD_SQRT_EXISTS, QUADRATIC_FIELD_DISCRIMINANT),  *)
(* so e = -d with d a squarefree natural number and d_k = qdisc d            *)
(* (QDISC_ALT); the complex field Q(sqrt(-d)) also contains a square root of *)
(* -d, so it is isomorphic to k (QUADRATIC_FIELD_UNIQUE), and isomorphic     *)
(* number fields have equal class numbers                                    *)
(* (NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC). Then                              *)
(* IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS of Baker/quadint_main.ml (the      *)
(* ideal and form class number one are equivalent) and CLASS_NUMBER_ONE of   *)
(* Baker/classno_main.ml finish the proof; QDISC_IN_NINE translates the nine *)
(* values of d into the nine discriminants.                                  *)
(*                                                                           *)
(* Main results: IMAGINARY_QUADRATIC_FIELD_ISOMORPHIC,                       *)
(* IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE,                                     *)
(* IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_UFD,                                 *)
(* IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_PID; helper QDISC_IN_NINE.           *)
(*                                                                           *)
(* Uses: ANT/quadratic.ml (QUADRATIC_FIELD_SQRT_EXISTS,                      *)
(* QUADRATIC_FIELD_DISCRIMINANT, QUADRATIC_FIELD_UNIQUE), ANT/classgroup.ml  *)
(* (NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC,                                    *)
(* NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1), ANT/dedekind_struct.ml               *)
(* (DEDEKIND_UFD_IFF_PID), ANT/ring_of_integers.ml                           *)
(* (DEDEKIND_RING_OF_INTEGERS), Baker/classno_defs.ml (qdisc),               *)
(* Baker/quadint_defs.ml (imag_quadratic_field), Baker/quadint_ant.ml        *)
(* (IMAG_QUADRATIC_FIELD_NUMBER_FIELD, _PRIME_SUBFIELD, _DEGREE, _SQRT,      *)
(* RING_OF_INTEGERS_IMAG_QUADRATIC_FIELD, QDISC_ALT), Baker/quadint_main.ml  *)
(* (IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS), Baker/classno_main.ml           *)
(* (CLASS_NUMBER_ONE), Library/pocklington.ml (SQUAREFREE_IMP_NZ).           *)
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
needs "Baker/quadint_main.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The nine discriminants.                                                   *)
(* ------------------------------------------------------------------------- *)

let QDISC_IN_NINE = prove
 (`!d. qdisc d IN {-- &3, -- &4, -- &7, -- &8, -- &11, -- &19, -- &43, -- &67,
                  -- &163} <=>
       d IN {1,2,3,7,11,19,43,67,163}`,
  GEN_TAC THEN ASM_CASES_TAC `d IN {1,2,3,4,7,8,11,19,43,67,163}` THENL
   [POP_ASSUM(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC o
      REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
    REWRITE_TAC[qdisc; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV);
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[qdisc; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[INT_EQ_NEG2; INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    REWRITE_TAC[ARITH_RULE `4 * d = 4 <=> d = 1`;
                ARITH_RULE `4 * d = 8 <=> d = 2`] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (MP_TAC o AP_TERM `EVEN`)) THEN
    REWRITE_TAC[EVEN_MULT; ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Every imaginary quadratic field is a complex field Q(sqrt(-d)).           *)
(* ------------------------------------------------------------------------- *)

let IMAGINARY_QUADRATIC_FIELD_ISOMORPHIC = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field_discriminant k < &0
        ==> ?d. squarefree d /\ number_field_discriminant k = qdisc d /\
                k isomorphic_ring
                subring_generated complex_ring (imag_quadratic_field d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` QUADRATIC_FIELD_SQRT_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`e:int`; `x:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `e:int`] QUADRATIC_FIELD_DISCRIMINANT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:int` INT_IMAGE) THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `number_field_discriminant(k:A ring) < &0` THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `squarefree d /\ ~(d = 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `squarefree(num_of_int(abs(-- &d:int)))` THEN
    REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
    MESON_TAC[SQUAREFREE_IMP_NZ];
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[QDISC_ALT]] THEN
  MATCH_MP_TAC QUADRATIC_FIELD_UNIQUE THEN EXISTS_TAC `-- &d:int` THEN
  ASM_SIMP_TAC[IMAG_QUADRATIC_FIELD_NUMBER_FIELD;
               IMAG_QUADRATIC_FIELD_PRIME_SUBFIELD;
               IMAG_QUADRATIC_FIELD_DEGREE] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `ii * Cx(sqrt(&d))` THEN REWRITE_TAC[IMAG_QUADRATIC_FIELD_SQRT]);;

(* ------------------------------------------------------------------------- *)
(* Class number one, unique factorization and principal ideals.              *)
(* ------------------------------------------------------------------------- *)

let IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field_discriminant k < &0
        ==> (class_number(ring_of_integers k) = 1 <=>
             number_field_discriminant k IN
             {-- &3, -- &4, -- &7, -- &8, -- &11, -- &19, -- &43, -- &67,
              -- &163})`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP IMAGINARY_QUADRATIC_FIELD_ISOMORPHIC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `subring_generated complex_ring (imag_quadratic_field d)`]
    NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_IMAG_QUADRATIC_FIELD] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[IMAG_QUADRATIC_CLASS_NUMBER_1_EQ_FORMS; CLASS_NUMBER_ONE;
               QDISC_IN_NINE]);;

let IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_PID = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field_discriminant k < &0
        ==> (PID(ring_of_integers k) <=>
             number_field_discriminant k IN
             {-- &3, -- &4, -- &7, -- &8, -- &11, -- &19, -- &43, -- &67,
              -- &163})`,
  SIMP_TAC[NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1;
           IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE]);;

let IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_UFD = prove
 (`!k:A ring.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        number_field_discriminant k < &0
        ==> (UFD(ring_of_integers k) <=>
             number_field_discriminant k IN
             {-- &3, -- &4, -- &7, -- &8, -- &11, -- &19, -- &43, -- &67,
              -- &163})`,
  SIMP_TAC[DEDEKIND_UFD_IFF_PID; DEDEKIND_RING_OF_INTEGERS;
           IMAGINARY_QUADRATIC_CLASS_NUMBER_ONE_PID]);;
