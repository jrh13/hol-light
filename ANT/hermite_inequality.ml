(* ========================================================================= *)
(* Hermite inequality for positive definite real quadratic forms on integer  *)
(* vectors, type-free in the style of ANT/linear_forms.ml: the matrix A is   *)
(* indexed by a finite set s in any type K, the form is                      *)
(* Q(x) = sum_i sum_j A i j x_i x_j, positive definite means Q(x) > 0 for    *)
(* every real vector x that is nonzero on s, and the determinant is          *)
(* ring_det real_ring s A.                                                   *)
(*                                                                           *)
(* Main results: a positive definite symmetric matrix has a positive         *)
(* determinant (QUADRATIC_FORM_DET_POS); the integer vectors vanishing       *)
(* outside s with bounded value are finitely many                            *)
(* (QUADRATIC_FORM_FINITE_INTEGER_POINTS), so a nonzero integer vector of    *)
(* least value exists (QUADRATIC_FORM_MINIMAL_VECTOR); Hermite: if s is      *)
(* nonempty with n elements, some nonzero integer vector x has               *)
(* Q(x)^(2 n) <= (4/3)^(n (n - 1)) det(A)^2 (HERMITE_INEQUALITY), that is    *)
(* Q(x) <= (4/3)^((n - 1) / 2) det(A)^(1 / n), the classical bound for the   *)
(* Hermite constant.                                                         *)
(*                                                                           *)
(* Routes. Positivity and finiteness: induction on s with the Schur          *)
(* complement at an element a of s (QUADRATIC_FORM_COMPLETE_SQUARE,          *)
(* QUADRATIC_FORM_SCHUR_POSITIVE and REAL_DET_SCHUR_COMPLEMENT of            *)
(* ANT/linear_forms.ml); for the finiteness, completing the square bounds    *)
(* the a-coordinate of x in terms of the others. Hermite inequality, by      *)
(* induction on s: a minimal vector x, of value m, is primitive              *)
(* (QUADRATIC_FORM_MINIMAL_PRIMITIVE), so it is the column a of an integer   *)
(* matrix U with |det U| = 1 (INT_PRIMITIVE_UNIMODULAR_COLUMN of             *)
(* ANT/zlattice.ml). The congruent form B = U^T A U                          *)
(* (QUADRATIC_FORM_CHANGE_BASIS, QUADRATIC_FORM_CONGRUENT_POSITIVE) has      *)
(* B a a = m, det B = det A (REAL_DET_CONGRUENT_MATRIX) and the same nonzero *)
(* integer values. Completing the square at a leaves the Schur complement S  *)
(* on s DELETE a, positive definite with det B = m det S; the induction      *)
(* hypothesis gives a nonzero integer vector y with a small value for S, and *)
(* rounding the a-coordinate to a nearest integer (INTEGER_ROUND of          *)
(* Library/floor.ml) gives a nonzero integer vector of value at most         *)
(* m / 4 + Q_S(y). So (3/4) m <= Q_S(y) and                                  *)
(* ((3/4) m)^(2 (n - 1)) <= (4/3)^((n - 1) (n - 2)) (det A / m)^2.           *)
(*                                                                           *)
(* The lemmas on quadratic forms used here are those of ANT/linear_forms.ml. *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (real_ring, integer_ring), Library/isum.ml    *)
(* (int_isum), Library/floor.ml (INTEGER_ROUND), Library/ring_det.ml         *)
(* (ring_det, RING_DET_HOMOMORPHISM, RING_DET_DEPENDENT_COLUMNS),            *)
(* ANT/zlattice.ml (INT_PRIMITIVE_UNIMODULAR_COLUMN) and ANT/linear_forms.ml *)
(* (the quadratic form lemmas). No Multivariate files.                       *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/isum.ml";;
needs "Library/floor.ml";;
needs "Library/ring_det.ml";;
needs "ANT/zlattice.ml";;
needs "ANT/linear_forms.ml";;

(* ------------------------------------------------------------------------- *)
(* The determinant of a positive definite form.                              *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FORM_DET_POS = prove
 (`!s (A:K->K->real).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> &0 < ring_det real_ring s A`,
  SUBGOAL_THEN
   `!s. FINITE s
        ==> !A:K->K->real.
              (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> &0 < ring_det real_ring s A`
  (fun th -> REPEAT GEN_TAC THEN STRIP_TAC THEN
             MATCH_MP_TAC(MP (SPEC `s:K->bool` th)
                             (ASSUME `FINITE(s:K->bool)`)) THEN
             ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[RING_DET_EMPTY; REAL_RING_CLAUSES; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `A:K->K->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `A:K->K->real`]
    QUADRATIC_FORM_SCHUR_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `A:K->K->real`]
    REAL_DET_SCHUR_COMPLEMENT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "ih" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integer vectors of bounded value; a minimal nonzero vector.               *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FORM_FINITE_INTEGER_POINTS =
  let lemma = prove
   (`!b. FINITE {u:int | abs(real_of_int u) <= b}`,
    GEN_TAC THEN MP_TAC(SPEC `b:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{u:int | --(&N) <= u /\ u <= &N}` THEN
    REWRITE_TAC[FINITE_INT_SEG; SUBSET; IN_ELIM_THM; GSYM INT_ABS_BOUNDS] THEN
    REWRITE_TAC[int_le; int_abs_th; int_of_num_th] THEN
    ASM_MESON_TAC[REAL_LE_TRANS]) in
  prove
   (`!s (A:K->K->real) C.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> FINITE {x:K->int | (!i. ~(i IN s) ==> x i = &0) /\
                               sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                                    real_of_int(x j))) <= C}`,
  SUBGOAL_THEN
   `!s. FINITE s
        ==> !(A:K->K->real) C.
              (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> FINITE
                   {x:K->int | (!i. ~(i IN s) ==> x i = &0) /\
                               sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                                    real_of_int(x j))) <= C}`
  (fun th -> REPEAT GEN_TAC THEN STRIP_TAC THEN
             MATCH_MP_TAC(MP (SPEC `s:K->bool` th)
                             (ASSUME `FINITE(s:K->bool)`)) THEN
             ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(\i. &0):K->int}` THEN
    REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`A:K->K->real`; `C:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `A:K->K->real`]
    QUADRATIC_FORM_SCHUR_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o
    SPEC `\i j. (A:K->K->real) i j - A i a * A a j / A a a`) THEN
  DISCH_THEN(MP_TAC o SPEC `C:real`) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `Y = {y:K->int | (!i. ~(i IN t) ==> y i = &0) /\
                    sum t (\i. sum t (\j. ((A:K->K->real) i j -
                                            A i a * A a j / A a a) *
                                          real_of_int(y i) *
                                          real_of_int(y j))) <= C}` THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{(\y u i. if i = a then u else (y:K->int) i) y u | y,u |
     y IN Y /\
     u IN (\y. {u:int | abs(real_of_int u) <=
                        abs(sum t (\j. (A:K->K->real) a j * real_of_int(y j)) /
                            A a a) + max (&1) (C / A a a)}) y}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[lemma];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:K->int` THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\i. if i IN t then (x:K->int) i else &0`; `(x:K->int) a`] THEN
  REWRITE_TAC[] THEN
  MP_TAC(BETA_RULE(ISPECL [`a:K`; `t:K->bool`; `A:K->K->real`;
                 `\i. real_of_int((x:K->int) i)`]
    QUADRATIC_FORM_COMPLETE_SQUARE)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[IN_INSERT];
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  SUBGOAL_THEN
   `!j. j IN t
        ==> real_of_int((if j IN t then (x:K->int) j else &0)) =
            real_of_int(x j)`
  ASSUME_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\j. (A:K->K->real) a j *
               real_of_int(if j IN t then (x:K->int) j else &0)) =
    sum t (\j. A a j * real_of_int(x j)) /\
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                          real_of_int(if i IN t then (x:K->int) i else &0) *
                          real_of_int(if j IN t then x j else &0))) =
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                          real_of_int(x i) * real_of_int(x j)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:K->bool`;
                 `\i j. (A:K->K->real) i j - A i a * A a j / A a a`;
                 `\i. real_of_int((x:K->int) i)`] QUADRATIC_FORM_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = sum t
              (\j. (A:K->K->real) a j * real_of_int((x:K->int) j))` THEN
  ABBREV_TAC
   `q = sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
                              real_of_int((x:K->int) i) *
                              real_of_int(x j)))` THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `q:real` THEN CONJ_TAC THENL
     [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        free_in `C:real` (concl th) && free_in `q:real` (concl th))) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= u ==> u + q <= C ==> q <= C:real`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_LE_POW_2]];
    ABBREV_TAC `z = real_of_int((x:K->int) a) + c / A a a` THEN
    SUBGOAL_THEN `z pow 2 <= C / (A:K->K->real) a a` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        free_in `z:real` (concl th) && free_in `C:real` (concl th))) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(z:real) <= max (&1) (z pow 2)` MP_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      ASM_CASES_TAC `abs(z:real) <= &1` THEN ASM_REWRITE_TAC[REAL_LE_MAX] THEN
      REWRITE_TAC[REAL_POW_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `real_of_int((x:K->int) a) + c / A a a = z` THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
      free_in `z:real` (concl th) && not(free_in `x:K->int` (concl th)))) THEN
    REWRITE_TAC[REAL_LE_MAX] THEN REAL_ARITH_TAC;
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]]);;

let QUADRATIC_FORM_MINIMAL_VECTOR = prove
 (`!s (A:K->K->real).
        FINITE s /\ ~(s = {}) /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> ?x:K->int.
              (!i. ~(i IN s) ==> x i = &0) /\ (?i. i IN s /\ ~(x i = &0)) /\
              !y:K->int.
                (!i. ~(i IN s) ==> y i = &0) /\ (?i. i IN s /\ ~(y i = &0))
                ==> sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                         real_of_int(x j))) <=
                    sum s (\i. sum s (\j. A i j * real_of_int(y i) *
                                         real_of_int(y j)))`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:K` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL
   [`s:K->bool`; `A:K->K->real`;
    `sum s (\i. sum s (\j. (A:K->K->real) i j *
       real_of_int(if i = a then &1 else &0) *
       real_of_int(if j = a then &1 else &0)))`]
   QUADRATIC_FORM_FINITE_INTEGER_POINTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC
   `IMAGE (\x:K->int. sum s (\i. sum s (\j. (A:K->K->real) i j *
                       real_of_int(x i) * real_of_int(x j))))
          {x:K->int | ((!i. ~(i IN s) ==> x i = &0) /\
                       (?i. i IN s /\ ~(x i = &0))) /\
                      sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                            real_of_int(x j))) <=
                      sum s (\i. sum s (\j. A i j *
                         real_of_int(if i = a then &1 else &0) *
                         real_of_int(if j = a then &1 else &0)))}`
   INF_FINITE_LEMMA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
      SET_TAC[];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `\i:K. if i = a then &1:int else &0` THEN
      REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[]; EXISTS_TAC `a:K` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC INT_REDUCE_CONV]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:K->int` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `y:K->int` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:K->int`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Hermite inequality.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Local lemmas: the numerical induction step (step) and rounding to the     *)
(* nearest integer in the form used (round, from INTEGER_ROUND).             *)
let HERMITE_INEQUALITY =
  let step = prove
   (`!m q D S p.
          &0 < m /\ &3 / &4 * m <= q /\
          q pow (2 * p) <= (&4 / &3) pow (p * (p - 1)) * S pow 2 /\
          D = m * S /\ 1 <= p
          ==> m pow (2 * (p + 1)) <= (&4 / &3) pow ((p + 1) * p) * D pow 2`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `2 * (p + 1) = 2 * p + 2 /\ (p + 1) * p = 2 * p + p * (p - 1)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
        GEN_REWRITE_RULE I [LE_EXISTS]) THEN
      REWRITE_TAC[ARITH_RULE `(1 + d) - 1 = d:num`] THEN CONV_TAC NUM_RING;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_ADD; REAL_POW_MUL] THEN
    SUBGOAL_THEN `(&3 / &4 * m) pow (2 * p) <= q pow (2 * p)` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `(&4 / &3) pow (2 * p) * (&3 / &4) pow (2 * p) = &1`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_POW_ONE];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (m:real) pow 2 /\ &0 < (&4 / &3:real) pow (2 * p)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `S:real` (concl th))) THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`(&4 / &3) pow (2 * p)`,`a:real`) THEN
    SPEC_TAC(`(&3 / &4) pow (2 * p)`,`b:real`) THEN
    SPEC_TAC(`(&4 / &3) pow (p * (p - 1))`,`c:real`) THEN
    SPEC_TAC(`(m:real) pow (2 * p)`,`u:real`) THEN
    SPEC_TAC(`(q:real) pow (2 * p)`,`v:real`) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(u:real) <= a * c * S pow 2` ASSUME_TAC THENL
     [SUBGOAL_THEN `(u:real) = a * (b * u)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_LID]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `((a:real) * c * S pow 2) * m pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC])
  and round = prove
   (`!c. ?n:int. abs(real_of_int n + c) <= &1 / &2`,
    GEN_TAC THEN MP_TAC(SPEC `--c:real` INTEGER_ROUND) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `int_of_real m` THEN ASM_SIMP_TAC[REAL_OF_INT_OF_REAL] THEN
    ASM_REAL_ARITH_TAC) in
  prove
   (`!s (A:K->K->real).
        FINITE s /\ ~(s = {}) /\
        (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> ?x:K->int.
              (!i. ~(i IN s) ==> x i = &0) /\ (?i. i IN s /\ ~(x i = &0)) /\
              sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                   real_of_int(x j))) pow (2 * CARD s) <=
              (&4 / &3) pow (CARD s * (CARD s - 1)) *
              ring_det real_ring s A pow 2`,
  SUBGOAL_THEN
   `!s. FINITE s
        ==> !A:K->K->real.
              ~(s = {}) /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
              (!x. (?i. i IN s /\ ~(x i = &0))
                   ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
              ==> ?x:K->int.
                    (!i. ~(i IN s) ==> x i = &0) /\
                    (?i. i IN s /\ ~(x i = &0)) /\
                    sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                         real_of_int(x j))) pow (2 * CARD s) <=
                    (&4 / &3) pow (CARD s * (CARD s - 1)) *
                    ring_det real_ring s A pow 2`
  (fun th -> REPEAT GEN_TAC THEN STRIP_TAC THEN
             MATCH_MP_TAC(MP (SPEC `s:K->bool` th)
                             (ASSUME `FINITE(s:K->bool)`)) THEN
             ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `t:K->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `A:K->K->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(a:K) INSERT t`; `A:K->K->real`]
    QUADRATIC_FORM_MINIMAL_VECTOR) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:K->int` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "min")))) THEN
  EXISTS_TAC `x:K->int` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `m = sum (a INSERT t) (\i. sum (a INSERT t) (\j. (A:K->K->real) i j *
          real_of_int((x:K->int) i) * real_of_int(x j)))` THEN
  SUBGOAL_THEN `&0 < (m:real)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && free_in `A:K->K->real` (concl th) &&
      is_imp(snd(dest_forall(concl th))))) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:K` STRIP_ASSUME_TAC o check
      (is_exists o concl)) THEN
    EXISTS_TAC `i:K` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `m <= sum (a INSERT t) (\i. sum (a INSERT t) (\j. (A:K->K->real) i j *
          real_of_int(if i = a then &1 else &0) *
          real_of_int(if j = a then &1 else &0)))`
  MP_TAC THENL
   [USE_THEN "min" (MP_TAC o SPEC `\i:K. if i = a then &1:int else &0`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    EXISTS_TAC `a:K` THEN REWRITE_TAC[IN_INSERT] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MESON[int_of_num_th]
   `!p. real_of_int(if p then &1 else &0) = if p then &1 else &0`] THEN
  ASM_SIMP_TAC[QUADRATIC_FORM_BASIS_VECTOR; FINITE_INSERT; IN_INSERT] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[CARD_CLAUSES; SUC_SUB1] THEN
  ASM_CASES_TAC `t:K->bool = {}` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[CARD_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    SIMP_TAC[RING_DET_SING; REAL_RING_CLAUSES; IN_UNIV] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(a:K) INSERT t`; `A:K->K->real`; `x:K->int`]
    QUADRATIC_FORM_MINIMAL_PRIMITIVE) THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(a:K) INSERT t`; `x:K->int`; `a:K`]
    INT_PRIMITIVE_UNIMODULAR_COLUMN) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:K->K->int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `ring_det real_ring (a INSERT t) (\k i. real_of_int((U:K->K->int) k i))
    pow 2 = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`integer_ring`; `real_ring`; `ring_of_int real_ring`;
                   `(a:K) INSERT t`; `U:K->K->int`] RING_DET_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; FINITE_INSERT;
                    INTEGER_RING; IN_UNIV; REAL_RING_OF_INT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM int_pow_th; GSYM int_of_num_th; GSYM int_eq] THEN
    ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN ASM_REWRITE_TAC[INT_POW_ONE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(a:K) INSERT t`; `A:K->K->real`;
                 `\k i. real_of_int((U:K->K->int) k i)`]
    QUADRATIC_FORM_CONGRUENT_POSITIVE) THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN ANTS_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `ring_det real_ring (a INSERT t) (\k i. real_of_int((U:K->K->int) k i))
      pow 2 = &1` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`(a:K) INSERT t`; `A:K->K->real`;
                 `\k i. real_of_int((U:K->K->int) k i)`]
    REAL_DET_CONGRUENT_MATRIX) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; REAL_MUL_LID] THEN DISCH_TAC THEN
  ABBREV_TAC
   `B = \i j. sum (a INSERT t) (\k. sum (a INSERT t) (\l.
                real_of_int((U:K->K->int) k i) * (A:K->K->real) k l *
                real_of_int(U l j)))` THEN
  SUBGOAL_THEN `(B:K->K->real) a a = m` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN EXPAND_TAC "m" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:K` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(U:K->K->int) k a = x k /\ U l a = x l`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[IN_INSERT]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:K->int.
      (!i. ~(i IN a INSERT t) ==> y i = &0) /\
      (?i. i IN a INSERT t /\ ~(y i = &0))
      ==> m <= sum (a INSERT t) (\i. sum (a INSERT t) (\j.
                 (B:K->K->real) i j * real_of_int(y i) * real_of_int(y j)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:K->int` THEN STRIP_TAC THEN EXPAND_TAC "B" THEN
    MP_TAC(BETA_RULE(ISPECL
     [`(a:K) INSERT t`; `A:K->K->real`;
      `\k i. real_of_int((U:K->K->int) k i)`;
      `\i. real_of_int((y:K->int) i)`] QUADRATIC_FORM_CHANGE_BASIS)) THEN
    ASM_REWRITE_TAC[FINITE_INSERT] THEN DISCH_THEN SUBST1_TAC THEN
    REMOVE_THEN "min" (MP_TAC o SPEC
     `\k. if k IN a INSERT t
          then isum (a INSERT t) (\i. (U:K->K->int) k i * y i) else &0`) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE
       [NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
      MP_TAC(ISPECL [`integer_ring`; `(a:K) INSERT t`; `U:K->K->int`;
                     `y:K->int`] RING_DET_DEPENDENT_COLUMNS) THEN
      ASM_REWRITE_TAC[INTEGRAL_DOMAIN_INTEGER_RING; FINITE_INSERT;
                      INTEGER_RING; IN_UNIV; INTEGER_RING_SUM] THEN
      MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p ==> q)`) THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        X_GEN_TAC `k:K` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:K` o check (fun th ->
          is_forall(concl th) && free_in `U:K->K->int` (concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `abs(ring_det integer_ring (a INSERT t) (U:K->K->int)) =
                     &1` THEN INT_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> m <= x ==> m <= y`) THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `l:K` THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[int_isum; int_mul_th]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i j. i IN a INSERT t /\ j IN a INSERT t
           ==> (B:K->K->real) i j = B j i) /\
    (!y. (?i. i IN a INSERT t /\ ~(y i = &0))
         ==> &0 < sum (a INSERT t) (\i. sum (a INSERT t)
                    (\j. B i j * y i * y j)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `B:K->K->real`]
    QUADRATIC_FORM_SCHUR_POSITIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o
    SPEC `\i j. (B:K->K->real) i j - B i a * B a j / B a a`) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:K->int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:K`; `t:K->bool`; `B:K->K->real`]
    REAL_DET_SCHUR_COMPLEMENT) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
  MP_TAC(SPEC `sum t (\j. (B:K->K->real) a j * real_of_int((z:K->int) j)) / m`
    round) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. if i = a then n else (z:K->int) i` o
    check (fun th -> is_forall(concl th) &&
                     free_in `B:K->K->real` (concl th) &&
                     free_in `m:real` (concl th))) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    EXISTS_TAC `i:K` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`a:K`; `t:K->bool`; `B:K->K->real`;
    `\i. real_of_int(if i = a then n else (z:K->int) i)`]
   QUADRATIC_FORM_COMPLETE_SQUARE)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[IN_INSERT];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. j IN t ==> (if j = a then n else (z:K->int) j) = z j`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\j. (B:K->K->real) a j *
               real_of_int(if j = a then n else (z:K->int) j)) =
    sum t (\j. B a j * real_of_int(z j)) /\
    sum t (\i. sum t (\j. (B i j - B i a * B a j / m) *
                          real_of_int(if i = a then n else (z:K->int) i) *
                          real_of_int(if j = a then n else z j))) =
    sum t (\i. sum t (\j. (B i j - B i a * B a j / m) *
                          real_of_int(z i) * real_of_int(z j)))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `c = sum t (\j. (B:K->K->real) a j * real_of_int((z:K->int) j))
                  / m` THEN
  ABBREV_TAC
   `q = sum t (\i. sum t (\j. ((B:K->K->real) i j - B i a * B a j / m) *
                              real_of_int((z:K->int) i) *
                              real_of_int(z j)))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(real_of_int n + c) pow 2 <= &1 / &4` ASSUME_TAC THENL
   [MP_TAC(SPECL [`real_of_int n + c`; `&1 / &2`] REAL_LE_SQUARE_ABS) THEN
    ASM_REWRITE_TAC[REAL_ARITH `abs(&1 / &2) = &1 / &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `m * (real_of_int n + c) pow 2 <= m * &1 / &4` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[GSYM real_div] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN MATCH_MP_TAC step THEN
  MAP_EVERY EXISTS_TAC
   [`q:real`;
    `ring_det real_ring t (\i j. (B:K->K->real) i j - B i a * B a j / m)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; CARD_EQ_0]]);;
