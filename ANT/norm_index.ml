(* ========================================================================= *)
(* The index of a principal ideal in a ring free over Z is the absolute      *)
(* value of the norm (the determinant of the multiplication matrix); for     *)
(* number fields N((a)) = |N(a)|, and the ideal norm is multiplicative.      *)
(*                                                                           *)
(* Main results: FREE_BASIS_IDEAL_NORM_PRINCIPAL (for any ring r free of     *)
(* rank n over Z with basis w, and a in r of nonzero norm, r/(a) is finite   *)
(* with |det M_a| elements, M_a the multiplication matrix of a),             *)
(* NUMBER_FIELD_NORM_INTEGRAL_BASIS (the norm of an algebraic integer is the *)
(* image in k of its norm over Z in an integral basis; likewise the trace,   *)
(* NUMBER_FIELD_TRACE_INTEGRAL_BASIS), NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q   *)
(* (N((a)) = |N(a)| in O_K) and NUMBER_FIELD_IDEAL_NORM_MUL_Q (N(j k) = N(j) *)
(* N(k) for nonzero ideals). A nonzero ideal of O_K of prime norm is prime   *)
(* (NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME), and an element of O_K whose    *)
(* norm is p or -p for a prime p is a prime element                          *)
(* (NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME).                                 *)
(*                                                                           *)
(* Proof route: the cosets of an ideal j of r correspond to the cosets of    *)
(* the lattice of the coordinate vectors of the elements of j                *)
(* (FREE_BASIS_QUOTIENT_RING_HAS_SIZE of ring_of_integers.ml); for j = (a)   *)
(* this lattice is the image of the multiplication matrix of a under the     *)
(* coordinate map (FREE_BASIS_IDEAL_NORM_IMAGE,                              *)
(* FREE_BASIS_IDEAL_NORM_COORD_MUL), and INT_COSETS_MATRIX_IMAGE of          *)
(* zlattice.ml counts its cosets. The norm over Z is algebra_norm            *)
(* (integer_ring,r) (ring_of_int r) of Library/ring_det.ml, the determinant  *)
(* of the multiplication matrix in any free basis (ALGEBRA_NORM_FREE_BASIS). *)
(* For number fields an integral basis is a Q-basis whose multiplication     *)
(* matrices are the images of the integer ones                               *)
(* (MUL_MATRIX_RING_OF_INTEGERS), and ring_det commutes with                 *)
(* ring_of_int (RING_DET_HOMOMORPHISM).                                      *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml, Library/isum.ml,     *)
(* ANT/algmisc.ml, Library/ring_det.ml, ANT/ideal_arith.ml (ideal_prod),     *)
(* ANT/ideal_norm.ml (ideal_norm, IDEAL_NORM_MUL), ANT/zlattice.ml,          *)
(* ANT/numfield.ml and ANT/ring_of_integers.ml.                              *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/isum.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/zlattice.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;

(* ------------------------------------------------------------------------- *)
(* The index of a principal ideal in a ring free over Z.                     *)
(* ------------------------------------------------------------------------- *)

(* Multiplication by a acts on the coordinates (zero outside i < n) by the   *)
(* multiplication matrix of a.                                               *)
let FREE_BASIS_IDEAL_NORM_COORD_MUL = prove
 (`!r:A ring n w (f:A->num->int) a x.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!x i. f x i =
               if i < n
               then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i
               else &0) /\
        a IN ring_carrier r /\ x IN ring_carrier r
        ==> f(ring_mul r a x) =
            (\i. if i < n
                 then isum {i | i < n}
                        (\j. mul_matrix (integer_ring,r)
                               (ring_of_int r) n w a i j * f x j)
                 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`; `n:num`;
                 `w:num->A`; `a:A`; `x:A`; `i:num`] BASIS_COORDINATES_MUL) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING;
                  INTEGER_RING_SUM] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  SIMP_TAC[IN_ELIM_THM]);;

(* The coordinate image of the principal ideal (a).                          *)
let FREE_BASIS_IDEAL_NORM_IMAGE = prove
 (`!r:A ring n w (f:A->num->int) a.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!x i. f x i =
               if i < n
               then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i
               else &0) /\
        a IN ring_carrier r
        ==> IMAGE f (ideal_generated r {a}) =
            int_matrix_image {i | i < n}
              (mul_matrix (integer_ring,r) (ring_of_int r) n w a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT; int_matrix_image] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `y:num->int` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:A` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN
    EXISTS_TAC `(f:A->num->int) x` THEN
    MATCH_MP_TAC FREE_BASIS_IDEAL_NORM_COORD_MUL THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `z:num->int` SUBST1_TAC) THEN
    ABBREV_TAC
     `x = ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r ((z:num->int) i))
                            ((w:num->A) i))` THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
    EXISTS_TAC `ring_mul r a x:A` THEN
    CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `f:A->num->int`;
                   `a:A`; `x:A`] FREE_BASIS_IDEAL_NORM_COORD_MUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM INTEGER_RING_SUM] THEN MATCH_MP_TAC RING_SUM_EQ THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "x" THEN
    ASM_SIMP_TAC[BASIS_COORDINATES_LINCOMB; INTEGER_RING; IN_UNIV;
                 RING_HOMOMORPHISM_INTEGER_RING_OF_INT]]);;

(* The index of (a) in a ring free of rank n over Z is |N(a)|.               *)
let FREE_BASIS_IDEAL_NORM_PRINCIPAL = prove
 (`!r:A ring n w a.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        a IN ring_carrier r /\
        ~(algebra_norm (integer_ring,r) (ring_of_int r) a = &0)
        ==> FINITE(ring_carrier(quotient_ring r (ideal_generated r {a}))) /\
            &(ideal_norm r (ideal_generated r {a})) =
            abs(algebra_norm (integer_ring,r) (ring_of_int r) a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`; `n:num`;
                 `w:num->A`; `a:A`] ALGEBRA_NORM_FREE_BASIS) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `?f:A->num->int.
      !x i. f x i =
            if i < n
            then basis_coordinates (integer_ring,r) (ring_of_int r) n w x i
            else &0`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\x:A i. if i < n
                        then basis_coordinates (integer_ring,r) (ring_of_int r)
                               n w x i
                        else &0` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `f:A->num->int`;
                 `a:A`] FREE_BASIS_IDEAL_NORM_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "im")] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `ideal_generated r {a:A}`;
                 `num_of_int(abs(ring_det integer_ring {i | i < n}
                   (mul_matrix (integer_ring,r) (ring_of_int r) n w (a:A))))`]
    FREE_BASIS_QUOTIENT_RING_HAS_SIZE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{z | (!i. ~(i < n) ==> z i = &0) /\
         ring_sum r {i | i < n} (\i. ring_mul r (ring_of_int r (z i)) (w i))
         IN ideal_generated r {a:A}} =
    IMAGE (f:A->num->int) (ideal_generated r {a})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `z:num->int` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC `ring_sum r {i | i < n}
                    (\i. ring_mul r (ring_of_int r ((z:num->int) i))
                                    ((w:num->A) i))` THEN
      ASM_REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[BASIS_COORDINATES_LINCOMB; INTEGER_RING; IN_UNIV;
                   RING_HOMOMORPHISM_INTEGER_RING_OF_INT];
      DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 SUBST1_TAC
        ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:A) IN ring_carrier r` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`r:A ring`; `{a:A}`] IDEAL_GENERATED_SUBSET) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_sum r {i | i < n}
          (\i. ring_mul r (ring_of_int r ((f:A->num->int) x i))
                          ((w:num->A) i)) = x`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      TRANS_TAC EQ_TRANS
       `ring_sum r {i | i < n}
          (\i. ring_mul r
                 (ring_of_int r
                   (basis_coordinates (integer_ring,r) (ring_of_int r) n w x i))
                 ((w:num->A) i))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
        MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [REMOVE_THEN "im" SUBST1_TAC THEN
    MP_TAC(ISPECL
     [`{i:num | i < n}`;
      `mul_matrix (integer_ring,r) (ring_of_int r) n w (a:A)`]
     INT_COSETS_MATRIX_IMAGE) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[HAS_SIZE; ideal_norm] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    REWRITE_TAC[INT_ABS_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Number fields: norms and traces in an integral basis, N((a)) = |N(a)|.    *)
(* ------------------------------------------------------------------------- *)

let MUL_MATRIX_RING_OF_INTEGERS = prove
 (`!k:A ring n w a i j.
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        free_basis (subfield_generated k {ring_0 k},k) I n w /\
        a IN ring_carrier(ring_of_integers k) /\ i < n /\ j < n
        ==> mul_matrix (subfield_generated k {ring_0 k},k) I n w a i j =
            ring_of_int k
             (mul_matrix (integer_ring,ring_of_integers k)
                (ring_of_int k) n w a i j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[mul_matrix] THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `n:num`; `w:num->A`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_mul (ring_of_integers k) a ((w:num->A) j) IN
    ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `ring_mul (ring_of_integers k) a ((w:num->A) j)`]
    BASIS_COORDINATES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ABBREV_TAC
   `z = basis_coordinates (integer_ring,ring_of_integers k) (ring_of_int k)
          n w (ring_mul (ring_of_integers k) a ((w:num->A) j))` THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_RING_OF_INTEGERS o
    lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_MUL THEN
    ASM_SIMP_TAC[RING_OF_INT_IN_RING_OF_INTEGERS];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k}:A ring`;
                 `k:A ring`; `n:num`; `w:num->A`; `ring_mul k a ((w:num->A) j)`;
                 `\i. ring_of_int k ((z:num->int) i):A`]
    BASIS_COORDINATES_UNIQUE) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM;
                  RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* The norm of an algebraic integer, computed in an integral basis.          *)
let NUMBER_FIELD_NORM_INTEGRAL_BASIS = prove
 (`!k:A ring n w a.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        a IN ring_carrier(ring_of_integers k)
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I a =
            ring_of_int k
              (algebra_norm (integer_ring,ring_of_integers k)
                            (ring_of_int k) a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[SUBSET] (SPEC `k:A ring` RING_OF_INTEGERS_SUBSET))) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `n:num`; `w:num->A`; `a:A`] ALGEBRA_NORM_FREE_BASIS) THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `n:num`; `w:num->A`; `a:A`]
    ALGEBRA_NORM_FREE_BASIS) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    REPEAT(DISCH_THEN SUBST1_TAC)] THEN
  MP_TAC(ISPECL
   [`integer_ring`; `subfield_generated k {ring_0 k}:A ring`;
    `ring_of_int k:int->A`; `{i:num | i < n}`;
    `mul_matrix (integer_ring,ring_of_integers k) (ring_of_int k)
       n w (a:A)`]
   RING_DET_HOMOMORPHISM) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; INTEGER_RING; IN_UNIV] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC MUL_MATRIX_RING_OF_INTEGERS THEN
  ASM_REWRITE_TAC[]);;

(* The trace of an algebraic integer, computed in an integral basis.         *)
let NUMBER_FIELD_TRACE_INTEGRAL_BASIS = prove
 (`!k:A ring n w x.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        x IN ring_carrier(ring_of_integers k)
        ==> algebra_trace (subfield_generated k {ring_0 k},k) I x =
            ring_of_int k
              (algebra_trace (integer_ring,ring_of_integers k)
                             (ring_of_int k) x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[SUBSET] (SPEC `k:A ring` RING_OF_INTEGERS_SUBSET))) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `n:num`; `w:num->A`; `x:A`] ALGEBRA_TRACE_FREE_BASIS) THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `n:num`; `w:num->A`; `x:A`]
    ALGEBRA_TRACE_FREE_BASIS) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
  ANTS_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    REPEAT(DISCH_THEN SUBST1_TAC)] THEN
  MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
  REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED] THEN
  DISCH_THEN(fun th -> W(MP_TAC o PART_MATCH (lhand o rand)
    (MATCH_MP RING_HOMOMORPHISM_SUM th) o rand o snd)) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; INTEGER_RING; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; o_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MUL_MATRIX_RING_OF_INTEGERS THEN
  ASM_REWRITE_TAC[]);;

(* N((a)) = |N(a)|.                                                          *)
let NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q = prove
 (`!k:A ring a.
        number_field k /\ a IN ring_carrier(ring_of_integers k) /\
        ~(a = ring_0 k)
        ==> ?m. algebra_norm (subfield_generated k {ring_0 k},k) I a =
                ring_of_int k m /\
                &(ideal_norm (ring_of_integers k)
                    (ideal_generated (ring_of_integers k) {a})) = abs m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  EXISTS_TAC `algebra_norm (integer_ring,ring_of_integers k)
                (ring_of_int k) (a:A)` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_NORM_INTEGRAL_BASIS THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `w:num->A`] THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`; `a:A`]
    FREE_BASIS_IDEAL_NORM_PRINCIPAL) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(a:A = ring_0 k)` THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`] NUMBER_FIELD_NORM_EQ_0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP
     (REWRITE_RULE[SUBSET] (SPEC `k:A ring` RING_OF_INTEGERS_SUBSET)));
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[RING_OF_INT_0]]);;

(* The ideal norm is multiplicative on nonzero ideals of O_K.                *)
let NUMBER_FIELD_IDEAL_NORM_MUL_Q = prove
 (`!k:A ring j j'.
        number_field k /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
        ring_ideal (ring_of_integers k) j' /\ ~(j' = {ring_0 k})
        ==> ideal_norm (ring_of_integers k)
              (ideal_prod (ring_of_integers k) j j') =
            ideal_norm (ring_of_integers k) j *
            ideal_norm (ring_of_integers k) j'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_NORM_MUL THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS_FINITE_QUOTIENT;
               RING_OF_INTEGERS]);;

let NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME = prove
 (`!k j:A->bool.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k}) /\ prime(ideal_norm (ring_of_integers k) j)
        ==> prime_ideal (ring_of_integers k) j`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MAXIMAL_IMP_PRIME_IDEAL THEN
  MATCH_MP_TAC IDEAL_NORM_PRIME_IMP_MAXIMAL THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT]);;

let NUMBER_FIELD_NORM_PRIME_IMP_RING_PRIME = prove
 (`!k x:A p.
        number_field k /\ x IN ring_carrier(ring_of_integers k) /\ prime p /\
        (algebra_norm (subfield_generated k {ring_0 k},k) I x =
         ring_of_num k p \/
         algebra_norm (subfield_generated k {ring_0 k},k) I x =
         ring_neg k (ring_of_num k p))
        ==> ring_prime (ring_of_integers k) x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; GSYM RING_OF_INT_NEG] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(x:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_0 k:A`] NUMBER_FIELD_NORM_EQ_0) THEN
    ASM_REWRITE_TAC[RING_0] THEN DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0] THEN
    REWRITE_TAC[INT_NEG_EQ_0; INT_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `m:int` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    ASSUME_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP RING_OF_INT_EQ_CHAR_0
   (ASSUME `ring_char(k:A ring) = 0`)]) THEN
  SUBGOAL_THEN
   `ideal_norm (ring_of_integers k)
               (ideal_generated (ring_of_integers k) {x:A}) = p`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `prime_ideal (ring_of_integers k)
                (ideal_generated (ring_of_integers k) {x:A})`
  MP_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_IDEAL_NORM_PRIME_IMP_PRIME THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `x:A`]
      IDEAL_GENERATED_EQ_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ASM_REWRITE_TAC[PRIME_IDEAL_SING; RING_OF_INTEGERS]]);;
