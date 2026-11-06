(* ========================================================================= *)
(* Valuations of the elements of a number field k at the nonzero primes P of *)
(* O = ring_of_integers k; denominator ideals and the denominators of p-th   *)
(* roots.                                                                    *)
(*                                                                           *)
(*   dedekind_valuation (ring_of_integers k,k) I P x = v_P(x), an integer:   *)
(*      for x = a / b with a, b nonzero in O, v_P((a)) - v_P((b))            *)
(*                                                                           *)
(* (the valuations of ANT/dedekind_valuation.ml for r = O and h = I; v_P of  *)
(* an ideal is ideal_valuation of ANT/dedekind.ml, and the value at zero is  *)
(* unspecified). k is the fraction field of O along I, field_of_fractions    *)
(* (O,k) I (RING_OF_INTEGERS_FRACTION_FIELD, by RING_OF_INTEGERS_DENOMINATOR *)
(* of ANT/numfield.ml), so the general results apply, and the first theorems *)
(* below are their number field forms. Main results: the value on any        *)
(* representation (NUMBER_FIELD_VALUATION) and on O                          *)
(* (NUMBER_FIELD_VALUATION_RING_OF_INTEGERS); v_P is a homomorphism from the *)
(* nonzero elements to the integers (_1, _MUL, _INV, _DIV, _POW, _NEG),      *)
(* ultrametric (_ADD, _ADD_STRICT), with finite support (_FINITE); x is in O *)
(* iff all v_P(x) >= 0 (_INTEGRAL), a unit of O iff all v_P(x) = 0 (_UNIT),  *)
(* in P iff v_P(x) > 0 (_PRIME_IDEAL); x, y have the same valuations iff x = *)
(* u y with u a unit (_EQ); and there is a finite set t of primes outside of *)
(* which every divisor is principal                                          *)
(* (NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE). Denominators: a nonzero x has *)
(* a denominator ideal J of O with v_P(J) = max 0 (-v_P(x))                  *)
(* (NUMBER_FIELD_DENOMINATOR_IDEAL), c x is in O for every c in an ideal J   *)
(* with v_P(J) + v_P(x) >= 0 (NUMBER_FIELD_IDEAL_MUL_INTEGRAL), and if a x^p *)
(* is in O for a nonzero a in O, then so is b x for an integer b >= 1 with   *)
(* b^p <= N((a)) (NUMBER_FIELD_ROOT_DENOMINATOR; Baker and Stark 1971, Lemma *)
(* 4).                                                                       *)
(*                                                                           *)
(* Approximation in number fields: some nonzero x has prescribed valuations  *)
(* at finitely many nonzero primes and v_Q(x) >= 0 at all the others         *)
(* (NUMBER_FIELD_VALUATION_APPROXIMATION).                                   *)
(*                                                                           *)
(* Routes: the first results are instances of those of                       *)
(* ANT/dedekind_valuation.ml. For the last two: every ideal class contains   *)
(* one of the finitely many nonzero ideals of norm at most some c            *)
(* (NUMBER_FIELD_IDEAL_CLASS_BOUND, NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM) *)
(* and t is the set of primes containing one of them: a nonzero ideal j is   *)
(* equivalent to such a j0, (a) j = (b) j0, and b / a has the valuations of  *)
(* j outside t; a divisor is the difference of the valuations of two ideals  *)
(* (its positive and its negative part;                                      *)
(* DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS). Root denominators: b = N(J) lies   *)
(* in the denominator ideal J of x (IDEAL_NORM_IN_IDEAL), so b x is          *)
(* integral; v_P(a) + p v_P(x) >= 0 gives v_P(a) >= p v_P(J), so (a) SUBSET  *)
(* J^p (DEDEKIND_IDEAL_SUBSET_VALUATION) and b^p = N(J^p) divides N((a))     *)
(* (IDEAL_NORM_IDEAL_POW, IDEAL_NORM_SUBSET_DIVIDES).                        *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, ANT/ideal_arith.ml, ANT/dedekind.ml,         *)
(* ANT/dedekind_struct.ml (IN_IDEAL_CLASS), ANT/dedekind_valuation.ml        *)
(* (dedekind_valuation, DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS),               *)
(* ANT/ideal_norm.ml (ideal_norm, IDEAL_NORM_IN_IDEAL, IDEAL_NORM_IDEAL_POW, *)
(* IDEAL_NORM_SUBSET_DIVIDES), ANT/numfield.ml                               *)
(* (RING_OF_INTEGERS_DENOMINATOR), ANT/ring_of_integers.ml                   *)
(* (DEDEKIND_RING_OF_INTEGERS, RING_OF_INTEGERS_FINITE_QUOTIENT) and         *)
(* ANT/classgroup.ml (NUMBER_FIELD_IDEAL_CLASS_BOUND,                        *)
(* NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM).                                 *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/classgroup.ml";;

(* k is the fraction field of O along the inclusion I, so the general        *)
(* results of ANT/dedekind_valuation.ml apply with r = O and h = I.          *)

let RING_OF_INTEGERS_FRACTION_FIELD = prove
 (`!k:A ring.
        ring_monomorphism(ring_of_integers k,k) I /\
        (number_field k
         ==> dedekind_domain(ring_of_integers k) /\
             field_of_fractions(ring_of_integers k,k) I)`,
  GEN_TAC THEN
  SUBGOAL_THEN `ring_monomorphism(ring_of_integers k:A ring,k) I`
  ASSUME_TAC THENL
   [REWRITE_TAC[ring_of_integers; I_DEF; RING_MONOMORPHISM_INCLUSION];
    ASM_REWRITE_TAC[field_of_fractions; RING_OF_INTEGERS; I_THM] THEN
    DISCH_TAC] THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] RING_OF_INTEGERS_DENOMINATOR) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Values and the homomorphism property.                                     *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_VALUATION = prove
 (`!k:A ring P x a b.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\
        a IN ring_carrier(ring_of_integers k) /\
        b IN ring_carrier(ring_of_integers k) /\
        ~(a = ring_0 k) /\ ~(b = ring_0 k) /\ ring_mul k b x = a
        ==> dedekind_valuation (ring_of_integers k,k) I P x =
            &(ideal_valuation (ring_of_integers k) P
               (ideal_generated (ring_of_integers k) {a})) -
            &(ideal_valuation (ring_of_integers k) P
               (ideal_generated (ring_of_integers k) {b}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_RING_OF_INTEGERS = prove
 (`!k:A ring P x.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P x =
            &(ideal_valuation (ring_of_integers k) P
               (ideal_generated (ring_of_integers k) {x}))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_IMAGE)) THEN
  ASM_REWRITE_TAC[]);;

(* Only field k is needed: every representation of 1 is b * 1 = b.           *)

let NUMBER_FIELD_VALUATION_1 = prove
 (`!k:A ring P.
        field k
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_1 k) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION_1 THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_FRACTION_FIELD]);;

let NUMBER_FIELD_VALUATION_MUL = prove
 (`!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_mul k x y) =
            dedekind_valuation (ring_of_integers k,k) I P x +
            dedekind_valuation (ring_of_integers k,k) I P y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_MUL)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_INV = prove
 (`!k:A ring P x.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_inv k x) =
            --(dedekind_valuation (ring_of_integers k,k) I P x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_INV)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_DIV = prove
 (`!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_div k x y) =
            dedekind_valuation (ring_of_integers k,k) I P x -
            dedekind_valuation (ring_of_integers k,k) I P y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_DIV)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_POW = prove
 (`!k:A ring P x n.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_pow k x n) =
            &n * dedekind_valuation (ring_of_integers k,k) I P x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_POW)) THEN
  ASM_REWRITE_TAC[]);;

(* Only x IN ring_carrier k is needed (DEDEKIND_VALUATION_NEG).              *)

let NUMBER_FIELD_VALUATION_NEG = prove
 (`!k:A ring P x.
        x IN ring_carrier k
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_neg k x) =
            dedekind_valuation (ring_of_integers k,k) I P x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION_NEG THEN
  ASM_SIMP_TAC[RING_MONOMORPHISM_IMP_HOMOMORPHISM;
               RING_OF_INTEGERS_FRACTION_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* The ultrametric inequality and finite support.                            *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_VALUATION_ADD = prove
 (`!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ y IN ring_carrier k /\
        ~(ring_add k x y = ring_0 k)
        ==> min (dedekind_valuation (ring_of_integers k,k) I P x)
                (dedekind_valuation (ring_of_integers k,k) I P y)
            <= dedekind_valuation (ring_of_integers k,k) I P (ring_add k x y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_ADD)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_ADD_STRICT = prove
 (`!k:A ring P x y.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\ y IN ring_carrier k /\
        dedekind_valuation (ring_of_integers k,k) I P x <
        dedekind_valuation (ring_of_integers k,k) I P y
        ==> dedekind_valuation (ring_of_integers k,k) I P (ring_add k x y) =
            dedekind_valuation (ring_of_integers k,k) I P x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_ADD_STRICT)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_FINITE = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> FINITE
             {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                  ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_FINITE)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integers, units and prime ideals by valuations.                           *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_VALUATION_INTEGRAL = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> (x IN ring_carrier(ring_of_integers k) <=>
             !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                 ==> &0 <= dedekind_valuation (ring_of_integers k,k) I P x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM; IMAGE_I]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_INTEGRAL)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_UNIT = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier k
        ==> (ring_unit (ring_of_integers k) x <=>
             ~(x = ring_0 k) /\
             !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                 ==> dedekind_valuation (ring_of_integers k,k) I P x = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM; IMAGE_I; IN_ELIM_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_UNIT)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_PRIME_IDEAL = prove
 (`!k:A ring P x.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
        ==> (x IN P <=> &0 < dedekind_valuation (ring_of_integers k,k) I P x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_PRIME_IDEAL)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_EQ = prove
 (`!k:A ring x y.
        number_field k /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> ((!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                  ==> dedekind_valuation (ring_of_integers k,k) I P x =
                      dedekind_valuation (ring_of_integers k,k) I P y) <=>
             ?u. ring_unit (ring_of_integers k) u /\ x = ring_mul k u y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_VALUATION_EQ)) THEN
  ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_VALUATION_APPROXIMATION = prove
 (`!k s (e:(A->bool)->int).
        number_field k /\ FINITE s /\
        (!P. P IN s ==> prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}))
        ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                (!P. P IN s
                     ==> dedekind_valuation (ring_of_integers k,k) I P x =
                         e P) /\
                (!P. prime_ideal (ring_of_integers k) P /\
                     ~(P = {ring_0 k}) /\ ~(P IN s)
                     ==> &0 <= dedekind_valuation (ring_of_integers k,k) I
                                                  P x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`;
                 `s:(A->bool)->bool`; `e:(A->bool)->int`]
    DEDEKIND_VALUATION_APPROXIMATION) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
               RING_OF_INTEGERS_FRACTION_FIELD; RING_OF_INTEGERS]);;

(* ------------------------------------------------------------------------- *)
(* Divisors are principal outside a finite set of primes.                    *)
(* ------------------------------------------------------------------------- *)

(* The local lemma takes for t the primes containing one of the finitely     *)
(* many nonzero ideals of bounded norm that meet every class: if (a) j = (b) *)
(* j0 with j0 such an ideal, then b / a has the valuations of j outside t. A *)
(* divisor is the difference of its positive and its negative part, each the *)
(* divisor of a nonzero ideal (DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS).        *)

let NUMBER_FIELD_VALUATION_PRINCIPAL_OUTSIDE = prove
 (`!k:A ring.
        number_field k
        ==> ?t. FINITE t /\
                (!P. P IN t
                     ==> prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k})) /\
                !e. FINITE {P | prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\ ~(e P = &0)}
                    ==> ?y. y IN ring_carrier k /\ ~(y = ring_0 k) /\
                            !P. prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\ ~(P IN t)
                                ==> dedekind_valuation
                                      (ring_of_integers k,k) I P y = e P`,
  let class_lemma = prove
   (`!k:A ring.
        number_field k
        ==> ?t. FINITE t /\
                (!P. P IN t ==> prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k})) /\
                !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> ?y. y IN ring_carrier k /\ ~(y = ring_0 k) /\
                            !P. prime_ideal (ring_of_integers k) P /\
                                ~(P = {ring_0 k}) /\ ~(P IN t)
                                ==> dedekind_valuation
                                      (ring_of_integers k,k) I P y =
                                    &(ideal_valuation (ring_of_integers k)
                                        P j)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `c:num` o
      MATCH_MP NUMBER_FIELD_IDEAL_CLASS_BOUND) THEN
    EXISTS_TAC
     `UNIONS (IMAGE (\j. {P | prime_ideal (ring_of_integers k) P /\
                              ~(P = {ring_0 k}) /\ j SUBSET P})
                    {j | ring_ideal (ring_of_integers k) j /\
                         ~(j = {ring_0 k}) /\
                         ideal_norm (ring_of_integers k:A ring) j <= c})` THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                   NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
        DEDEKIND_IDEAL_FACTORIZATION) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS];
      MESON_TAC[];
      X_GEN_TAC `j:A->bool` THEN STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN
    ASM_REWRITE_TAC[IN_IDEAL_CLASS; RING_OF_INTEGERS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j0:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    EXISTS_TAC `ring_mul k (ring_inv k a) b:A` THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; INTEGRAL_DOMAIN_MUL_EQ_0;
                 FIELD_IMP_INTEGRAL_DOMAIN; FIELD_INV_EQ_0] THEN
    X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j0:A->bool` o
      REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `ring_mul k (ring_inv k a) b:A`;
                   `b:A`; `a:A`] NUMBER_FIELD_VALUATION) THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; RING_MUL_ASSOC; FIELD_MUL_RINV;
                 RING_MUL_LID] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM
     `ideal_valuation (ring_of_integers k) (P:A->bool)`) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `j0:A->bool`]
      IDEAL_VALUATION_EQ_0) THEN
    ASM_SIMP_TAC[IDEAL_VALUATION_IDEAL_PROD; RING_IDEAL_IDEAL_GENERATED;
                 IDEAL_GENERATED_EQ_0; RING_OF_INTEGERS] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
    INT_ARITH_TAC) in
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP class_lemma) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:(A->bool)->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "class"))) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:(A->bool)->int` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `\P:A->bool. num_of_int(max (--(e P)) (&0))`]
    DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `\P:A->bool. num_of_int(max (e P) (&0))`]
    DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
  MATCH_MP_TAC(TAUT
   `(p /\ q) /\ (r ==> s ==> t) ==> (p ==> r) ==> (q ==> s) ==> t`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      FINITE_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM INT_OF_NUM_EQ] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&0 <= max (x:int) (&0)`] THEN
    INT_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `j1:A->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j2:A->bool` STRIP_ASSUME_TAC)] THEN
  REMOVE_THEN "class" (fun th -> MP_TAC(SPEC `j2:A->bool` th) THEN
                                 MP_TAC(SPEC `j1:A->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ring_div k y1 y2:A` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  ASM_SIMP_TAC[RING_DIV; ring_div; INTEGRAL_DOMAIN_MUL_EQ_0; RING_INV;
               FIELD_IMP_INTEGRAL_DOMAIN; FIELD_INV_EQ_0] THEN
  ASM_SIMP_TAC[GSYM ring_div; NUMBER_FIELD_VALUATION_DIV] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&0 <= max (x:int) (&0)`] THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Denominator ideals and the denominators of p-th roots.                    *)
(* ------------------------------------------------------------------------- *)

(* The denominator ideal of x: the product of the P^(-v_P(x)) over the       *)
(* finitely many P with v_P(x) < 0.                                          *)

let NUMBER_FIELD_DENOMINATOR_IDEAL = prove
 (`!k:A ring x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> ?J. ring_ideal (ring_of_integers k) J /\ ~(J = {ring_0 k}) /\
                !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                    ==> &(ideal_valuation (ring_of_integers k) P J):int =
                        max (&0)
                         (--dedekind_valuation (ring_of_integers k,k) I P x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`]
     DEDEKIND_DENOMINATOR_IDEAL)) THEN
  ASM_REWRITE_TAC[]);;

(* An ideal J with v_P(J) + v_P(x) >= 0 at every nonzero prime P clears      *)
(* the denominator of x: c x is integral for every c in J.                   *)

let NUMBER_FIELD_IDEAL_MUL_INTEGRAL = prove
 (`!k:A ring J x c.
        number_field k /\ ring_ideal (ring_of_integers k) J /\
        x IN ring_carrier k /\
        (!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
             ==> &0 <= &(ideal_valuation (ring_of_integers k) P J) +
                       dedekind_valuation (ring_of_integers k,k) I P x) /\
        c IN J
        ==> ring_mul k c x IN ring_carrier(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS; I_THM; IMAGE_I]
   (ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`;
            `J:A->bool`] DEDEKIND_IDEAL_MUL_INTEGRAL)) THEN
  ASM_REWRITE_TAC[]);;

(* Denominators of p-th roots (Baker and Stark 1971, Lemma 4): for the       *)
(* denominator ideal J of x, b = N(J) lies in J, so b x is integral; and     *)
(* v_P(a) >= p v_P(J) at every P, so (a) SUBSET J^p and b^p = N(J^p)         *)
(* divides N((a)).                                                           *)

let NUMBER_FIELD_ROOT_DENOMINATOR = prove
 (`!k:A ring x a p.
        number_field k /\ x IN ring_carrier k /\
        a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
        ring_mul k a (ring_pow k x p) IN ring_carrier(ring_of_integers k)
        ==> ?b. 1 <= b /\
                b EXP p <= ideal_norm (ring_of_integers k)
                             (ideal_generated (ring_of_integers k) {a}) /\
                ring_mul k (ring_of_num k b) x
                IN ring_carrier(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  SUBGOAL_THEN
   `~(ideal_generated (ring_of_integers k) {a} = {ring_0 k:A}) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers k)
            (ideal_generated (ring_of_integers k) {a})))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `a:A`]
        IDEAL_GENERATED_EQ_0) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS];
      DISCH_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]];
    ALL_TAC] THEN
  ASM_CASES_TAC `x:A = ring_0 k` THENL
   [EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[EXP_ONE; IDEAL_NORM_POS; LE_REFL; RING_OF_NUM_1;
                 RING_MUL_RZERO; RING_1] THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_0) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_DENOMINATOR_IDEAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `J:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "val")))) THEN
  SUBGOAL_THEN
   `FINITE(ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `ideal_norm (ring_of_integers k) (J:A->bool)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_NORM_POS THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `a IN ring_carrier k /\ ~(ring_pow k x p = ring_0 k) /\
      ~(ring_mul k a (ring_pow k x p) = ring_0 k:A)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) ==> p /\ q /\ r`) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; DISCH_TAC] THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; INTEGRAL_DOMAIN_POW_EQ_0;
                   RING_POW; FIELD_IMP_INTEGRAL_DOMAIN];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(ideal_pow (ring_of_integers k) J p = {ring_0 k:A})`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `J:A->bool`; `p:num`]
        IDEAL_POW_EQ_ZERO) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS; INTEGRAL_DOMAIN_RING_OF_INTEGERS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `J:A->bool`; `p:num`]
      IDEAL_NORM_IDEAL_POW) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    MATCH_MP_TAC DIVIDES_LE_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_NORM_SUBSET_DIVIDES;
      MATCH_MP_TAC(ARITH_RULE `1 <= n ==> n = 0 ==> m = 0`) THEN
      MATCH_MP_TAC IDEAL_NORM_POS THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_IDEAL_GENERATED] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ideal_generated (ring_of_integers k) {a:A}`;
                   `ideal_pow (ring_of_integers k) J p:A->bool`]
      DEDEKIND_IDEAL_SUBSET_VALUATION) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW;
                    RING_IDEAL_IDEAL_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `J:A->bool`;
                   `p:num`] IDEAL_VALUATION_IDEAL_POW) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `a:A`]
      NUMBER_FIELD_VALUATION_RING_OF_INTEGERS) THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_mul k a (ring_pow k x p):A`]
      NUMBER_FIELD_VALUATION_INTEGRAL) THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `a:A`; `ring_pow k x p:A`]
      NUMBER_FIELD_VALUATION_MUL) THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `x:A`; `p:num`]
      NUMBER_FIELD_VALUATION_POW) THEN
    ASM_SIMP_TAC[RING_POW; RING_MUL] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(MP_TAC o SPEC `P:A->bool`) THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
    USE_THEN "val" (MP_TAC o SPEC `P:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[INT_MAX] THEN COND_CASES_TAC THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_MUL_RNEG; INT_POS] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC NUMBER_FIELD_IDEAL_MUL_INTEGRAL THEN
  EXISTS_TAC `J:A->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    USE_THEN "val" (MP_TAC o SPEC `P:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; INT_ARITH_TAC];
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `J:A->bool`]
      IDEAL_NORM_IN_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS]]);;
