(* ========================================================================= *)
(* The discriminant of a number field k with ring of integers                *)
(* O = ring_of_integers k:                                                   *)
(*                                                                           *)
(*   number_field_discriminant k = the discriminant over Z of any integral   *)
(*                                 basis of O (an integer d_K)               *)
(*                                                                           *)
(* Main results: d_K is the common discriminant of all integral bases (a     *)
(* change of integral basis has determinant +-1), its image in k is the      *)
(* discriminant over Q of any integral basis, and d_K is nonzero. Index      *)
(* formula: for a Q-basis g of algebraic integers with Z-span M, the cosets  *)
(* of M in O number N with disc(g) = N^2 d_K (NUMBER_FIELD_DISCRIMINANT_     *)
(* INDEX); g is an integral basis iff disc(g) = d_K; M + pO = O iff p does   *)
(* not divide N, in particular when p^2 does not divide disc(g). Along the   *)
(* way, for a ring r free over Z with basis w and g = C w: the cosets of the *)
(* Z-span of g number |det C| and span + pr = r iff p does not divide det C  *)
(* (FREE_BASIS_INTEGER_RING_SPAN_INDEX/_COPRIME), and a square integer       *)
(* matrix is onto modulo a prime p iff p does not divide its determinant     *)
(* (INT_MATRIX_SURJECTIVE_MOD_PRIME). Integral bases of ideals: every        *)
(* nonzero ideal j of O has a Q-basis of k with [k:Q] elements whose Z-span  *)
(* is j (NUMBER_FIELD_IDEAL_INTEGRAL_BASIS, with                             *)
(* RING_OF_INTEGERS_IDEAL_INT_LINCOMB), the discriminant of such a basis is  *)
(* N(j)^2 d_K (NUMBER_FIELD_IDEAL_DISCRIMINANT), and a Q-basis lying in j    *)
(* spans j over Z iff its discriminant is N(j)^2 d_K                         *)
(* (NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT).                         *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml, Library/isum.ml,     *)
(* Library/ring_det.ml (basis_discriminant), ANT/zlattice.ml,                *)
(* ANT/ideal_norm.ml, ANT/numfield.ml, ANT/ring_of_integers.ml,              *)
(* ANT/norm_index.ml (NUMBER_FIELD_TRACE_INTEGRAL_BASIS).                    *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/isum.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/zlattice.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;

(* ------------------------------------------------------------------------- *)
(* The discriminant of a number field.                                       *)
(* ------------------------------------------------------------------------- *)

let number_field_discriminant = new_definition
 `number_field_discriminant (k:A ring) =
  @d. !n w. free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
            ==> basis_discriminant (integer_ring,ring_of_integers k)
                                       (ring_of_int k) n w = d`;;

(* Two integral bases differ by a matrix of determinant +-1, so they have    *)
(* the same discriminant over Z.                                             *)

let NUMBER_FIELD_DISCRIMINANT_BASIS = prove
 (`!k:A ring n w.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> number_field_discriminant k =
            basis_discriminant (integer_ring,ring_of_integers k)
                                   (ring_of_int k) n w`,
  let lemma = prove
   (`!r:A ring n w w'.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        free_basis (integer_ring,r) (ring_of_int r) n w'
        ==> basis_discriminant (integer_ring,r) (ring_of_int r) n w' =
            basis_discriminant (integer_ring,r) (ring_of_int r) n w`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
                   `n:num`; `w:num->A`; `w':num->A`;
                   `\i j. basis_coordinates (integer_ring,r) (ring_of_int r) n w
                            ((w':num->A) i) j`]
      BASIS_DISCRIMINANT_CHANGE_OF_BASIS) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING;
                    IN_UNIV; INTEGER_RING_POW] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN
      ASM_MESON_TAC[FREE_BASIS_IN_CARRIER];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(INT_RING `(x:int) pow 2 = &1 ==> x pow 2 * d = d`) THEN
    MP_TAC(ISPECL [`integer_ring`; `{i:num | i < n}`;
      `\i m. basis_coordinates (integer_ring,r) (ring_of_int r) n w
               ((w':num->A) m) i`] RING_DET_TRANSP) THEN
    MP_TAC(ISPECL [`integer_ring`; `{i:num | i < n}`;
      `\i m. basis_coordinates (integer_ring,r) (ring_of_int r) n w
               ((w':num->A) m) i`;
      `\m j. basis_coordinates (integer_ring,r) (ring_of_int r) n w'
               ((w:num->A) j) m`] RING_DET_MUL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; INTEGER_RING; IN_UNIV] THEN
    SUBGOAL_THEN
     `ring_det integer_ring {i:num | i < n}
       (\i j. ring_sum integer_ring {m | m < n}
                (\m. basis_coordinates (integer_ring,r) (ring_of_int r) n w
                       ((w':num->A) m) i *
                     basis_coordinates (integer_ring,r) (ring_of_int r) n w'
                       ((w:num->A) j) m)) = &1`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
                     `n:num`; `n:num`; `w':num->A`; `w:num->A`]
        BASIS_COORDINATES_CHANGE_OF_BASIS_INVERSE) THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING] THEN
      DISCH_TAC THEN
      TRANS_TAC EQ_TRANS
       `ring_det integer_ring {i:num | i < n}
          (\i j. if i = j then ring_1 integer_ring
                 else ring_0 integer_ring)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; INTEGER_RING];
        SIMP_TAC[RING_DET_I; FINITE_NUMSEG_LT; INTEGER_RING]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[INT_MUL_EQ_1] THEN
    DISCH_THEN(fun th -> DISCH_THEN SUBST1_TAC THEN STRIP_ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[number_field_discriminant] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `d:int` THEN
  REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`n:num`; `w:num->A`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `v:num->A`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `m:num = n` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_FREE_BASIS_FIELD]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                   `v:num->A`] lemma) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS]]);;

let NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD = prove
 (`!k:A ring n w.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w
        ==> ring_of_int k (number_field_discriminant k) =
            basis_discriminant (subfield_generated k {ring_0 k},k) I n w`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_DISCRIMINANT_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring`
    RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
  REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `n:num`; `w:num->A`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[basis_discriminant] THEN
  MP_TAC(ISPECL
   [`integer_ring`; `subfield_generated k {ring_0 k}:A ring`;
    `ring_of_int k:int->A`; `{i:num | i < n}`;
    `\i j. algebra_trace (integer_ring,ring_of_integers k) (ring_of_int k)
             (ring_mul (ring_of_integers k) ((w:num->A) i) (w j))`]
   RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; INTEGER_RING; IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; RING_OF_INTEGERS] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL_BASIS THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `w:num->A`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `(w:num->A) i`; `(w:num->A) j`]
    RING_MUL) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS]);;

let NUMBER_FIELD_DISCRIMINANT_NONZERO = prove
 (`!k:A ring. number_field k ==> ~(number_field_discriminant k = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I` THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[RING_OF_INT_0] THEN STRIP_TAC THEN
  CONV_TAC(RAND_CONV SYM_CONV) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k}:A ring`;
                 `k:A ring`; `n:num`; `w:num->A`]
    BASIS_DISCRIMINANT_NONZERO) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_DEGREE_POS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[number_field]) THEN
  ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
               SUBFIELD_GENERATED; GSYM RING_OF_INT_OF_NUM;
               RING_OF_INT_SUBFIELD_GENERATED; RING_OF_INT_EQ_0_CHAR_0;
               INT_OF_NUM_EQ; LE_1]);;

(* ------------------------------------------------------------------------- *)
(* Rings free over Z: the index of the Z-span of g = C w.                    *)
(* ------------------------------------------------------------------------- *)

(* The coordinate isomorphism Z^n -> r of a free basis w over Z, and the     *)
(* coordinates of the Z-linear combinations of g = C w.                      *)

let FREE_BASIS_INTEGER_RING_LINCOMB = prove
 (`!r:A ring n w psi.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!z. psi z = ring_sum r {i | i < n}
                       (\i. ring_mul r (ring_of_int r (z i)) (w i)))
        ==> (!z. psi z IN ring_carrier r) /\
            (!x. x IN ring_carrier r
                 ==> ?z. (!i. ~(i < n) ==> z i = &0) /\ psi z = x) /\
            (!z z'. psi z = psi z' <=> !i. i < n ==> z i = z' i) /\
            (!z z'. psi(\i. z i + z' i) = ring_add r (psi z) (psi z')) /\
            (!m z. psi(\i. m * z i) = ring_mul r (ring_of_int r m) (psi z)) /\
            (!g C. (!i. i < n
                        ==> g i = ring_sum r {j | j < n}
                                    (\j. ring_mul r (ring_of_int r (C i j))
                                                    (w j)))
                   ==> !c. ring_sum r {i | i < n}
                             (\i. ring_mul r (ring_of_int r (c i)) (g i)) =
                           psi(\i. isum {j | j < n} (\j. C j i * c j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`]
    FREE_BASIS_INTEGER_RING_COORDINATES) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `r:A ring` RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
  DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
                     `n:num`; `w:num->A`] BASIS_COORDINATES_UNIQUE) THEN
      ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV] THEN
      DISCH_THEN(fun th ->
        MP_TAC(SPECL [`ring_sum r {i | i < n}
           (\i. ring_mul r (ring_of_int r ((z':num->int) i)) ((w:num->A) i))`;
                      `z:num->int`] th) THEN
        MP_TAC(SPECL [`ring_sum r {i | i < n}
           (\i. ring_mul r (ring_of_int r ((z':num->int) i)) ((w:num->A) i))`;
                      `z':num->int`] th)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
        MP_TAC(CONJ (SPEC `i:num` th1) (SPEC `i:num` th2)))) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
                   `{i:num | i < n}`] EXTENSION_LINCOMB_ADD) THEN
    ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; FINITE_NUMSEG_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_ELIM_THM];
    REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
                   `{i:num | i < n}`] EXTENSION_LINCOMB_LMUL) THEN
    ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; FINITE_NUMSEG_LT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_ELIM_THM];
    MAP_EVERY X_GEN_TAC [`g:num->A`; `C:num->num->int`] THEN
    DISCH_TAC THEN X_GEN_TAC `c:num->int` THEN
    TRANS_TAC EQ_TRANS
     `ring_sum r {m | m < n}
        (\m. ring_mul r (ring_of_int r ((c:num->int) m))
               (ring_sum r {i | i < n}
                 (\i. ring_mul r (ring_of_int r (C m i)) ((w:num->A) i))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`;
                   `{i:num | i < n}`; `{i:num | i < n}`; `c:num->int`;
                   `C:num->num->int`; `w:num->A`] EXTENSION_LINCOMB_SUM) THEN
    ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; FINITE_NUMSEG_LT; IN_ELIM_THM;
                    INTEGER_RING_SUM] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC RING_SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC ISUM_EQ THEN REWRITE_TAC[INT_MUL_SYM]]);;

(* A square integer matrix is onto modulo a prime p iff p does not divide   *)
(* its determinant (adjugate and Bezout; determinants of congruent matrices  *)
(* are congruent, via ring_of_int into integer_mod_ring p).                  *)

let INT_MATRIX_SURJECTIVE_MOD_PRIME = prove
 (`!s (A:K->K->int) p.
        FINITE s /\ prime p
        ==> ((!z. ?c y. !i. i IN s
                          ==> z i = isum s (\j. A i j * c j) + &p * y i) <=>
             ~(&p divides ring_det integer_ring s A))`,
  let lemma = prove
   (`!s (f:K->K->int) g p.
        FINITE s /\ (!i j. i IN s /\ j IN s ==> (f i j == g i j) (mod &p))
        ==> (ring_det integer_ring s f == ring_det integer_ring s g)
            (mod &p)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`integer_mod_ring p`;
                   `ring_det integer_ring s (f:K->K->int)`;
                   `ring_det integer_ring s (g:K->K->int)`] RING_OF_INT_EQ) THEN
    REWRITE_TAC[INTEGER_MOD_RING_CHAR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`integer_ring`; `integer_mod_ring p`;
                   `ring_of_int(integer_mod_ring p)`; `s:K->bool`]
      RING_DET_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING;
                    IN_UNIV] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN MATCH_MP_TAC RING_DET_EQ THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ; INTEGER_MOD_RING_CHAR]) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:(K->int)->K->int`; `y:(K->int)->K->int`] THEN
    DISCH_THEN(ASSUME_TAC o BETA_RULE o GEN `j:K` o
      SPEC `\i:K. if i = j then &1:int else &0`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`s:K->bool`; `\i j:K. if i = j then &1:int else &0`;
      `\i j:K. isum s (\m. (A:K->K->int) i m *
                            (c:(K->int)->K->int)
                              (\i:K. if i = j then &1:int else &0) m)`;
      `p:num`] lemma) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`j:K`; `i:K`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_ACCEPT_TAC(INTEGER_RULE
       `!x a b p:int. x = a + p * b ==> (x == a) (mod p)`);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`integer_ring`; `s:K->bool`] RING_DET_I) THEN
    ASM_SIMP_TAC[INTEGER_RING; INT_DET_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
    UNDISCH_TAC `&p divides ring_det integer_ring s (A:K->K->int)` THEN
    REWRITE_TAC[TAUT `p ==> ~q <=> ~(p /\ q)`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
     `!a b p:int. p divides a /\ (&1 == a * b) (mod p) ==> p divides &1`)) THEN
    REWRITE_TAC[GSYM num_divides; DIVIDES_ONE] THEN
    ASM_MESON_TAC[PRIME_1];
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?u v. &p * u + ring_det integer_ring s (A:K->K->int) * v = &1`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM int_coprime] THEN
      UNDISCH_TAC `~(&p divides ring_det integer_ring s (A:K->K->int))` THEN
      SPEC_TAC(`ring_det integer_ring s (A:K->K->int)`,`d:int`) THEN
      REWRITE_TAC[FORALL_INT_CASES; INTEGER_RULE
       `coprime(a:int,--b) <=> coprime(a,b)`; INTEGER_RULE
       `(a:int) divides --b <=> a divides b`] THEN
      ASM_SIMP_TAC[GSYM num_coprime; GSYM num_divides; PRIME_COPRIME_EQ];
      ALL_TAC] THEN
    X_GEN_TAC `z:K->int` THEN
    EXISTS_TAC `\j. isum s (\k. ring_cofactor integer_ring s A k j *
                                (v * (z:K->int) k))` THEN
    EXISTS_TAC `\i. u * (z:K->int) i` THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    MP_TAC(BETA_RULE(ISPECL
     [`s:K->bool`; `A:K->K->int`;
      `\j k. ring_cofactor integer_ring s (A:K->K->int) k j`;
      `\l j:K. v * (z:K->int) l`; `i:K`; `i:K`] INT_MATRIX_MUL_ASSOC)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `isum s (\l. isum s (\k. (A:K->K->int) i k *
                              ring_cofactor integer_ring s A l k) *
                  (v * (z:K->int) l)) =
      isum s (\l. if l = i then ring_det integer_ring s A * (v * z l)
                  else &0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `l:K` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`integer_ring`; `s:K->bool`; `A:K->K->int`; `i:K`;
                     `l:K`] RING_DET_ADJUGATE_ROWS) THEN
      ASM_REWRITE_TAC[INTEGER_RING; INTEGER_RING_SUM; IN_UNIV] THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_CASES_TAC `l:K = i` THEN ASM_REWRITE_TAC[INT_MUL_LZERO];
      ASM_REWRITE_TAC[ISUM_DELTA_GEN] THEN
      UNDISCH_TAC `&p * u + ring_det integer_ring s (A:K->K->int) * v = &1` THEN
      CONV_TAC INT_RING]]);;

(* The cosets of the span M = psi(C^T Z^n) are the images of the cosets of  *)
(* the lattice C^T Z^n, |det C| many (INT_COSETS_MATRIX_IMAGE).              *)

let FREE_BASIS_INTEGER_RING_SPAN_INDEX = prove
 (`!r:A ring n w g C.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!i. i < n
             ==> g i = ring_sum r {j | j < n}
                         (\j. ring_mul r (ring_of_int r (C i j)) (w j))) /\
        ~(ring_det integer_ring {i | i < n} C = &0)
        ==> {ring_coset r
              {ring_sum r {i | i < n}
                 (\i. ring_mul r (ring_of_int r (c i)) (g i)) |
               c IN (:num->int)} x |
             x | x IN ring_carrier r}
            HAS_SIZE num_of_int(abs(ring_det integer_ring {i | i < n} C))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `psi = \z:num->int. ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))` THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `psi:(num->int)->A`]
    FREE_BASIS_INTEGER_RING_LINCOMB) THEN
  ANTS_TAC THENL [EXPAND_TAC "psi" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "car") (CONJUNCTS_THEN2
   (LABEL_TAC "onto") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "add")
   (MP_TAC o SPECL [`g:num->A`; `C:num->num->int`] o CONJUNCT2))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC
   `M = {(psi:(num->int)->A) (\i. isum {j | j < n} (\j. C j i * c j)) |
         c IN (:num->int)}` THEN
  ABBREV_TAC
   `L = int_matrix_image {i:num | i < n} (\i j. (C:num->num->int) j i)` THEN
  SUBGOAL_THEN
   `!z:num->int. (!i. ~(i < n) ==> z i = &0)
         ==> ring_coset (r:A ring) M ((psi:(num->int)->A) z) =
             IMAGE psi {y | (!i. ~(i < n) ==> y i = &0) /\
                            (\i. y i - z i) IN L}`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:num->int` THEN DISCH_TAC THEN
    EXPAND_TAC "M" THEN EXPAND_TAC "L" THEN
    REWRITE_TAC[ring_coset; EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIV;
                INT_MATRIX_IMAGE_IN] THEN
    X_GEN_TAC `b:A` THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `c:num->int`] THEN
      DISCH_THEN(fun th ->
        SUBST1_TAC(CONJUNCT2 th) THEN SUBST1_TAC(CONJUNCT1 th)) THEN
      EXISTS_TAC `\i:num. if i < n then z i + isum {j | j < n} (\j. C j i * c j)
                      else &0` THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "add" (fun th -> REWRITE_TAC[GSYM th]) THEN
        USE_THEN "inj" (fun th -> SIMP_TAC[th]);
        SIMP_TAC[];
        EXISTS_TAC `c:num->int` THEN REWRITE_TAC[FUN_EQ_THM] THEN
        X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num < n` THEN
        ASM_SIMP_TAC[INT_ADD_SUB; INT_SUB_REFL]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `y:num->int` THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c:num->int`))) THEN
      EXISTS_TAC
       `(psi:(num->int)->A) (\i. isum {j | j < n} (\j:num. C j i * c j))` THEN
      CONJ_TAC THENL [EXISTS_TAC `c:num->int` THEN REFL_TAC; ALL_TAC] THEN
      USE_THEN "add" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C AP_THM `i:num`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_ACCEPT_TAC(INT_ARITH `!a b c:int. a - b = c ==> a = b + c`)];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{i:num | i < n}`; `\i j. (C:num->num->int) j i`]
    INT_COSETS_MATRIX_IMAGE) THEN
  MP_TAC(ISPECL [`integer_ring`; `{i:num | i < n}`; `C:num->num->int`]
    RING_DET_TRANSP) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{ring_coset r M x | x | x IN ring_carrier r} =
    IMAGE (IMAGE (psi:(num->int)->A)) (int_cosets {i:num | i < n} L)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; int_cosets] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 ASSUME_TAC
        SUBST1_TAC)) THEN
      USE_THEN "onto" (MP_TAC o SPEC `a:A`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num->int` (CONJUNCTS_THEN2 ASSUME_TAC
        (SUBST1_TAC o SYM))) THEN
      EXISTS_TAC `{y | (!i. ~(i < n) ==> y i = &0) /\
                       (\i. y i - (z:num->int) i) IN L}` THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `z:num->int` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `u:(num->int)->bool` (CONJUNCTS_THEN2
        SUBST1_TAC (X_CHOOSE_THEN `z:num->int` (CONJUNCTS_THEN2
        ASSUME_TAC SUBST1_TAC)))) THEN
      EXISTS_TAC `(psi:(num->int)->A) z` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`int_cosets {i:num | i < n} L`;
                 `{z:num->int | !i. ~(i < n) ==> z i = &0}`;
                 `psi:(num->int)->A`]
   (SET_RULE `!S V (f:B->C).
       (!s. s IN S ==> s SUBSET V) /\
       (!a b. a IN V /\ b IN V /\ f a = f b ==> a = b)
       ==> !x y. x IN S /\ y IN S /\ IMAGE f x = IMAGE f y ==> x = y`)) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[int_cosets; FORALL_IN_GSPEC; IN_ELIM_THM] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num->int`; `b:num->int`] THEN
    USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n` THEN ASM_SIMP_TAC[]]);;

(* In coordinates, M + pr = r says that C^T is onto modulo p.              *)

let FREE_BASIS_INTEGER_RING_SPAN_COPRIME = prove
 (`!r:A ring n w g C p.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!i. i < n
             ==> g i = ring_sum r {j | j < n}
                         (\j. ring_mul r (ring_of_int r (C i j)) (w j))) /\
        prime p
        ==> (ring_setadd r
               {ring_sum r {i | i < n}
                  (\i. ring_mul r (ring_of_int r (c i)) (g i)) |
                c IN (:num->int)}
               (ideal_generated r {ring_of_num r p}) =
             ring_carrier r <=>
             ~(&p divides ring_det integer_ring {i | i < n} C))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `psi = \z:num->int. ring_sum r {i | i < n}
            (\i. ring_mul r (ring_of_int r (z i)) ((w:num->A) i))` THEN
  MP_TAC(ISPECL [`r:A ring`; `n:num`; `w:num->A`; `psi:(num->int)->A`]
    FREE_BASIS_INTEGER_RING_LINCOMB) THEN
  ANTS_TAC THENL [EXPAND_TAC "psi" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "car") (CONJUNCTS_THEN2
   (LABEL_TAC "onto") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
   (CONJUNCTS_THEN2 (LABEL_TAC "add") (CONJUNCTS_THEN2 (LABEL_TAC "mul")
   (MP_TAC o SPECL [`g:num->A`; `C:num->num->int`])))))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`{i:num | i < n}`; `\i j. (C:num->num->int) j i`; `p:num`]
    INT_MATRIX_SURJECTIVE_MOD_PRIME) THEN
  MP_TAC(ISPECL [`integer_ring`; `{i:num | i < n}`; `C:num->num->int`]
    RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ABBREV_TAC
   `M = {(psi:(num->int)->A) (\i. isum {j | j < n} (\j. C j i * c j)) |
         c IN (:num->int)}` THEN
  SUBGOAL_THEN
   `ring_setadd r M (ideal_generated r {ring_of_num r p}) SUBSET
    ring_carrier (r:A ring)`
   (fun th -> REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; th]) THENL
   [MATCH_MP_TAC RING_SETADD THEN REWRITE_TAC[IDEAL_GENERATED_SUBSET] THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    USE_THEN "car" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SIMP_TAC[IDEAL_GENERATED_SING_ALT; RING_OF_NUM] THEN EXPAND_TAC "M" THEN
  REWRITE_TAC[SUBSET; ring_setadd; IN_ELIM_THM; IN_UNIV] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `z:num->int` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(psi:(num->int)->A) z`) THEN
    USE_THEN "car" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`; `c:num->int`; `u:A`] THEN
    STRIP_TAC THEN
    USE_THEN "onto" (MP_TAC o SPEC `u:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:num->int` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`c:num->int`; `v:num->int`] THEN
    USE_THEN "inj" (MP_TAC o SPECL
     [`z:num->int`;
      `\i. isum {j | j < n} (\j. (C:num->num->int) j i * c j) +
           &p * (v:num->int) i`]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "add" (fun th -> REWRITE_TAC[BETA_RULE(SPECL
     [`\i. isum {j | j < n} (\j. (C:num->num->int) j i * c j)`;
      `\i. &p * (v:num->int) i`] th)]) THEN
    USE_THEN "mul" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[RING_OF_INT_OF_NUM];
    DISCH_TAC THEN X_GEN_TAC `a:A` THEN DISCH_TAC THEN
    USE_THEN "onto" (MP_TAC o SPEC `a:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num->int` (CONJUNCTS_THEN2 ASSUME_TAC
      (SUBST1_TAC o SYM))) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `c:num->int` (X_CHOOSE_TAC `y:num->int`) o
      SPEC `z:num->int`) THEN
    MAP_EVERY EXISTS_TAC
     [`(psi:(num->int)->A) (\i. isum {j | j < n} (\j:num. C j i * c j))`;
      `ring_mul r (ring_of_num r p) ((psi:(num->int)->A) y)`] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `c:num->int` THEN REFL_TAC;
      EXISTS_TAC `(psi:(num->int)->A) y` THEN
      USE_THEN "car" (fun th -> REWRITE_TAC[th]);
      REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
      USE_THEN "mul" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "add" (fun th -> REWRITE_TAC[GSYM th]) THEN
      USE_THEN "inj" (fun th -> REWRITE_TAC[th]) THEN
      FIRST_ASSUM ACCEPT_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The index of the Z-span of a Q-basis of algebraic integers.               *)
(* ------------------------------------------------------------------------- *)

(* A Q-basis g of algebraic integers is g = C w for an integral basis w and  *)
(* an integer matrix C, with det C <> 0 and disc(g) = det(C)^2 d_K.          *)

let NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS = prove
 (`!k:A ring n g.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
        ==> ?w C. free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                    n w /\
                  (!i. i < n
                       ==> g i = ring_sum (ring_of_integers k) {j | j < n}
                                   (\j. ring_mul k (ring_of_int k (C i j))
                                                   (w j))) /\
                  ~(ring_det integer_ring {i | i < n} C = &0) /\
                  basis_discriminant (subfield_generated k {ring_0 k},k)
                                         I n g =
                  ring_of_int k (ring_det integer_ring {i | i < n} C pow 2 *
                                 number_field_discriminant k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
    NUMBER_FIELD_FREE_BASIS_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  MAP_EVERY EXISTS_TAC
   [`w:num->A`;
    `\i j. basis_coordinates (integer_ring,ring_of_integers k) (ring_of_int k)
             n w ((g:num->A) i) j`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                 `ring_of_integers k:A ring`; `n:num`; `w:num->A`]
    FREE_BASIS_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> (g:num->A) i =
            ring_sum (ring_of_integers k) {j | j < n}
              (\j. ring_mul k (ring_of_int k
                     (basis_coordinates (integer_ring,ring_of_integers k)
                        (ring_of_int k) n w (g i) j)) (w j))`
  (LABEL_TAC "gO") THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`;
                   `ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                   `(g:num->A) i`] BASIS_COORDINATES_EXPAND) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> (g:num->A) i =
            ring_sum k {j | j < n}
              (\j. ring_mul k (ring_of_int k
                     (basis_coordinates (integer_ring,ring_of_integers k)
                        (ring_of_int k) n w (g i) j)) (w j))`
  (LABEL_TAC "gk") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "gO" (fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP th
     (ASSUME `i:num < n`)]) THEN
    MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`] RING_MUL) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ r /\ (r ==> q) ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "gO" ACCEPT_TAC;
    MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k}:A ring`;
                   `k:A ring`; `n:num`; `w:num->A`; `g:num->A`;
                   `\i j. ring_of_int k
                          (basis_coordinates (integer_ring,ring_of_integers k)
                             (ring_of_int k) n w ((g:num->A) i) j):A`]
      BASIS_DISCRIMINANT_CHANGE_OF_BASIS) THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
      NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN
    MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
      RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM;
                      RING_OF_INT_IN_SUBFIELD_GENERATED];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`integer_ring`; `subfield_generated k {ring_0 k}:A ring`;
      `ring_of_int k:int->A`; `{i:num | i < n}`;
      `\i j. basis_coordinates (integer_ring,ring_of_integers k)
               (ring_of_int k) n w ((g:num->A) i) j`]
     RING_DET_HOMOMORPHISM) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; INTEGER_RING; IN_UNIV] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_POW; SUBFIELD_GENERATED;
                RING_POW_SUBFIELD_GENERATED];
    REMOVE_THEN "gO" (K ALL_TAC) THEN REMOVE_THEN "gk" (K ALL_TAC) THEN
    DISCH_THEN(fun th -> DISCH_THEN(fun th' ->
      MP_TAC(REWRITE_RULE[th'] th))) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_MUL_LZERO; RING_OF_INT_0] THEN
    SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
        NUMBER_FIELD_FREE_BASIS_DEGREE) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_DEGREE_POS) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k}:A ring`;
                   `k:A ring`; `n:num`; `g:num->A`]
      BASIS_DISCRIMINANT_NONZERO) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
                 CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED);
                 GSYM RING_OF_INT_OF_NUM; RING_OF_INT_SUBFIELD_GENERATED;
                 RING_OF_INT_EQ_0_CHAR_0; INT_OF_NUM_EQ]]);;

(* All that is used below, with d = det C.                                   *)

let NUMBER_FIELD_INDEX_DETERMINANT = prove
 (`!k:A ring n g.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
        ==> ?d. ~(d = &0) /\
                basis_discriminant (subfield_generated k {ring_0 k},k) I
                                       n g =
                ring_of_int k (d pow 2 * number_field_discriminant k) /\
                {ring_coset (ring_of_integers k)
                   {ring_sum k {i | i < n}
                      (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
                    c IN (:num->int)} x |
                 x | x IN ring_carrier(ring_of_integers k)}
                HAS_SIZE num_of_int(abs d) /\
                !p. prime p
                    ==> (ring_setadd (ring_of_integers k)
                           {ring_sum k {i | i < n}
                              (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
                            c IN (:num->int)}
                           (ideal_generated (ring_of_integers k)
                              {ring_of_num k p}) =
                         ring_carrier(ring_of_integers k) <=>
                         ~(&p divides d))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
    NUMBER_FIELD_DISCRIMINANT_CHANGE_OF_BASIS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:num->A`; `C:num->num->int`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_det integer_ring {i | i < n} (C:num->num->int)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) =
        ring_sum (ring_of_integers k) {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) (g i))`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `g:num->A`; `C:num->num->int`]
    FREE_BASIS_INTEGER_RING_SPAN_INDEX) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `g:num->A`; `C:num->num->int`]
    FREE_BASIS_INTEGER_RING_SPAN_COPRIME) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN SIMP_TAC[]);;

let NUMBER_FIELD_DISCRIMINANT_INDEX = prove
 (`!k:A ring n g M.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k)) /\
        M = {ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
             c IN (:num->int)}
        ==> ?N. {ring_coset (ring_of_integers k) M x |
                 x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N /\
                basis_discriminant (subfield_generated k {ring_0 k},k) I
                                       n g =
                ring_of_int k (&N pow 2 * number_field_discriminant k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
    NUMBER_FIELD_INDEX_DETERMINANT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:int` THEN
  STRIP_TAC THEN EXISTS_TAC `num_of_int(abs d)` THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_POW2_ABS]);;

let NUMBER_FIELD_INTEGRAL_BASIS_DISCRIMINANT = prove
 (`!k:A ring n g.
        number_field k /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k))
        ==> (free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
                        n g <=>
             basis_discriminant (subfield_generated k {ring_0 k},k) I n g =
             ring_of_int k (number_field_discriminant k))`,
  let lemma = prove
   (`!r M:A->bool.
        M SUBSET ring_carrier r /\ ring_0 r IN M /\
        {ring_coset r M x | x | x IN ring_carrier r} HAS_SIZE 1
        ==> ring_carrier r SUBSET M`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ONE; HAS_SIZE_CLAUSES; HAS_SIZE_0; UNWIND_THM2;
                NOT_IN_EMPTY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `a:A->bool`))) THEN
    SUBGOAL_THEN `!y:A. y IN ring_carrier r ==> ring_coset r M y = a`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `ring_coset r M (y:A)` o
        GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_coset r M (x:A) = M` MP_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `M:A->bool`] RING_COSET_0) THEN
      ASM_SIMP_TAC[RING_0];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[ring_coset; IN_ELIM_THM] THEN EXISTS_TAC `ring_0 r:A` THEN
      ASM_SIMP_TAC[RING_ADD_RZERO]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
    NUMBER_FIELD_INDEX_DETERMINANT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:int` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `num_of_int(abs(d:int)) = 1` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
    MATCH_MP_TAC INT_POW_EQ_1_IMP THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ] THEN
    MATCH_MP_TAC(INT_RING
     `!d e:int. e = d pow 2 * e /\ ~(e = &0) ==> d pow 2 = &1`) THEN
    EXISTS_TAC `number_field_discriminant (k:A ring)` THEN
    ASM_SIMP_TAC[NUMBER_FIELD_DISCRIMINANT_NONZERO; GSYM RING_OF_INT_EQ_CHAR_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) IN
        ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`;
      `\i. ring_mul k (ring_of_int k ((c:num->int) i)) ((g:num->A) i)`]
      RING_SUM_RING_OF_INTEGERS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
      REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[RING_OF_INT_IN_RING_OF_INTEGERS];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_SUM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `{ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) ((g:num->A) i)) |
                   c IN (:num->int)}`] lemma) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_UNIV; RING_OF_INTEGERS] THEN
    EXISTS_TAC `\i:num. &0:int` THEN
    BETA_TAC THEN REWRITE_TAC[RING_OF_INT_0] THEN CONV_TAC SYM_CONV THEN
    TRANS_TAC EQ_TRANS `ring_sum (k:A ring) {i:num | i < n} (\i. ring_0 k)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[RING_SUM_0]] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_LZERO THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN ASM SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_carrier(ring_of_integers k):A->bool`;
                 `n:num`; `g:num->A`]
    FREE_BASIS_INTEGER_RING_SUBRING_GENERATED) THEN
  REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV];
    X_GEN_TAC `c:num->int` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o BETA_RULE o
      SPEC `\i. ring_of_int k ((c:num->int) i):A` o
      CONJUNCT2 o CONJUNCT2 o GEN_REWRITE_RULE I [free_basis]) THEN
    ASM_SIMP_TAC[I_THM; RING_OF_INT_IN_SUBFIELD_GENERATED;
                 CONJUNCT1(CONJUNCT2 SUBFIELD_GENERATED);
                 RING_OF_INT_EQ_0_CHAR_0]]);;

let NUMBER_FIELD_INDEX_COPRIME = prove
 (`!k:A ring n g M p N.
        number_field k /\ prime p /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k)) /\
        M = {ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
             c IN (:num->int)} /\
        {ring_coset (ring_of_integers k) M x |
         x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N
        ==> (ring_setadd (ring_of_integers k) M
               (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
             ring_carrier(ring_of_integers k) <=>
             ~(p divides N))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
    NUMBER_FIELD_INDEX_DETERMINANT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:int` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `N = num_of_int(abs d)` SUBST1_TAC THENL
   [ASM_MESON_TAC[HAS_SIZE];
    SIMP_TAC[num_divides; INT_OF_NUM_OF_INT; INT_ABS_POS; INT_DIVIDES_RABS]]);;

let NUMBER_FIELD_INDEX_COPRIME_DISCRIMINANT = prove
 (`!k:A ring n g M p D.
        number_field k /\ prime p /\
        free_basis (subfield_generated k {ring_0 k},k) I n g /\
        (!i. i < n ==> g i IN ring_carrier(ring_of_integers k)) /\
        M = {ring_sum k {i | i < n}
                     (\i. ring_mul k (ring_of_int k (c i)) (g i)) |
             c IN (:num->int)} /\
        basis_discriminant (subfield_generated k {ring_0 k},k) I n g =
        ring_of_int k D /\
        ~(&p pow 2 divides D)
        ==> ring_setadd (ring_of_integers k) M
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `g:num->A`]
    NUMBER_FIELD_INDEX_DETERMINANT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:int` THEN
  STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `~(&p pow 2 divides D)` THEN
  SUBGOAL_THEN `D = d pow 2 * number_field_discriminant(k:A ring)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC[GSYM(MATCH_MP RING_OF_INT_EQ_CHAR_0 th)]) THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_ACCEPT_TAC(INTEGER_RULE
     `!p d e:int. p divides d ==> p pow 2 divides d pow 2 * e`)]);;

(* ------------------------------------------------------------------------- *)
(* Integral bases of nonzero ideals and their discriminants.                 *)
(* ------------------------------------------------------------------------- *)

let RING_OF_INTEGERS_IDEAL_INT_LINCOMB = prove
 (`!k:A ring j s (c:K->int) w.
        ring_ideal (ring_of_integers k) j /\ (!i. i IN s ==> w i IN j)
        ==> ring_sum k s (\i. ring_mul k (ring_of_int k (c i)) (w i)) IN j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  SUBGOAL_THEN
   `!i. i IN s
        ==> ring_mul k (ring_of_int k ((c:K->int) i)) ((w:K->A) i) IN j`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`;
                   `ring_of_int k ((c:K->int) i):A`; `(w:K->A) i`]
      IN_RING_IDEAL_LMUL) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
    lhand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_IDEAL_INTEGRAL_BASIS = prove
 (`!k j:A->bool.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k})
        ==> ?w. free_basis (subfield_generated k {ring_0 k},k) I
                  (extension_degree (subfield_generated k {ring_0 k},k) I) w /\
                {ring_sum k
                   {i | i < extension_degree
                              (subfield_generated k {ring_0 k},k) I}
                   (\i. ring_mul k (ring_of_int k (c i)) (w i)) |
                 c IN (:num->int)} = j`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `n = extension_degree (subfield_generated k {ring_0 k},k:A ring) I`
  THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  MP_TAC(ISPECL [`k:A ring`; `j:A->bool`] RING_OF_INTEGERS_IDEAL_INTEGER) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `m:int` THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FREE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:num->A`) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `v:num->A`]
    RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `v:num->A`]
    FREE_BASIS_INTEGER_RING_COORDINATES) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "coord") ASSUME_TAC))) THEN
  SUBGOAL_THEN `!i. i < n ==> (v:num->A) i IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[free_basis]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. ring_sum k {i | i < n} (\i. ring_mul k (ring_of_int k (z i)) (v i)) =
        ring_sum (ring_of_integers k) {i | i < n}
          (\i. ring_mul k (ring_of_int k (z i)) ((v:num->A) i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC RING_OF_INTEGERS_RING_OF_INT_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`;
                 `\i. ring_mul k (ring_of_int k m) ((v:num->A) i)`;
                 `j:A->bool`; `m:int`] NUMBER_FIELD_INT_LINCOMB_SANDWICH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`subfield_generated k {ring_0 k:A}`; `k:A ring`;
                     `I:A->A`; `n:num`; `v:num->A`;
                     `\i:num. ring_of_int k m:A`] FREE_BASIS_SCALE) THEN
      ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED;
                   RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_THM] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED; SUBFIELD_GENERATED] THEN
      FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
        GEN_REWRITE_RULE I [number_field]) THEN
      ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ring_carrier(ring_of_integers k:A ring)` THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBSET];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `x:A`; `y:A`]
        IN_RING_IDEAL_SUB) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS];
      X_GEN_TAC `c:num->int` THEN
      MP_TAC(ISPECL [`k:A ring`; `j:A->bool`; `{i:num | i < n}`;
                     `c:num->int`;
                     `\i. ring_mul k (ring_of_int k m) ((v:num->A) i)`]
        RING_OF_INTEGERS_IDEAL_INT_LINCOMB) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`;
                     `ring_of_int k m:A`; `(v:num->A) i`]
        IN_RING_IDEAL_RMUL) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS];
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      USE_THEN "coord" (MP_TAC o SPEC `x:A`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num->int` (SUBST1_TAC o SYM o CONJUNCT2)) THEN
      EXISTS_TAC `z:num->int` THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
        is_forall(concl th) && is_eq(snd(dest_forall(concl th))))) THEN
      SUBGOAL_THEN `!i. i < n ==> (v:num->A) i IN ring_carrier k`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM RING_SUM_LMUL; FINITE_NUMSEG_LT; IN_ELIM_THM;
                   RING_OF_INT; RING_MUL] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul (k:A ring) a (ring_mul k b c) =
        ring_mul k b (ring_mul k a c)`) THEN
      ASM_SIMP_TAC[RING_OF_INT]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w:num->A` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `x:A` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
    MATCH_MP_TAC RING_OF_INTEGERS_IDEAL_INT_LINCOMB THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ASM_MESON_TAC[]]);;

let NUMBER_FIELD_IDEAL_DISCRIMINANT = prove
 (`!k j:A->bool n w.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        free_basis (subfield_generated k {ring_0 k},k) I n w /\
        {ring_sum k {i | i < n} (\i. ring_mul k (ring_of_int k (c i)) (w i)) |
         c IN (:num->int)} = j
        ==> basis_discriminant (subfield_generated k {ring_0 k},k) I n w =
            ring_of_int k (&(ideal_norm (ring_of_integers k) j) pow 2 *
                           number_field_discriminant k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [free_basis]) THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->A) i IN j` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      rand(concl th) = `j:A->bool`)) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `\m:num. if m = i then &1 else &0:int` THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; RING_OF_INT_1; RING_OF_INT_0] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum k {m | m < n} (\m. if m = i then (w:num->A) i else ring_0 k)`
    THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_SUM_DELTA; IN_ELIM_THM];
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LZERO]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `j:A->bool`]
    NUMBER_FIELD_DISCRIMINANT_INDEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!x:A s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `j:A->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
  ASM_SIMP_TAC[ideal_norm; QUOTIENT_RING; HAS_SIZE]);;

let NUMBER_FIELD_IDEAL_INTEGRAL_BASIS_DISCRIMINANT = prove
 (`!k j:A->bool n w.
        number_field k /\ ring_ideal (ring_of_integers k) j /\
        ~(j = {ring_0 k}) /\
        free_basis (subfield_generated k {ring_0 k},k) I n w /\
        (!i. i < n ==> w i IN j)
        ==> ({ring_sum k {i | i < n}
                (\i. ring_mul k (ring_of_int k (c i)) (w i)) |
              c IN (:num->int)} = j <=>
             basis_discriminant (subfield_generated k {ring_0 k},k) I n w =
             ring_of_int k (&(ideal_norm (ring_of_integers k) j) pow 2 *
                            number_field_discriminant k))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC NUMBER_FIELD_IDEAL_DISCRIMINANT THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  ABBREV_TAC
   `M = {ring_sum k {i | i < n}
           (\i. ring_mul k (ring_of_int k (c i)) ((w:num->A) i)) |
         c IN (:num->int)}` THEN
  SUBGOAL_THEN `(M:A->bool) SUBSET j` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    X_GEN_TAC `c:num->int` THEN
    MATCH_MP_TAC RING_OF_INTEGERS_IDEAL_INT_LINCOMB THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(M:A->bool) SUBSET ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_0 k IN (M:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `\i:num. &0:int` THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[RING_OF_INT_0] THEN
    MATCH_MP_TAC RING_SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_LZERO THEN
    ASM_MESON_TAC[free_basis];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `M:A->bool`]
    NUMBER_FIELD_DISCRIMINANT_INDEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_CHAR_0; INT_EQ_MUL_RCANCEL;
               NUMBER_FIELD_DISCRIMINANT_NONZERO; INT_OF_NUM_POW;
               INT_OF_NUM_EQ; EXP_MONO_EQ; ARITH_EQ] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN
   `{ring_coset (ring_of_integers k) j x | x | x IN
     ring_carrier(ring_of_integers k)} HAS_SIZE
    ideal_norm (ring_of_integers k) (j:A->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
      (CONJUNCT1 QUOTIENT_RING)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[HAS_SIZE; ideal_norm] THEN
    MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN ring_carrier(ring_of_integers k)
        ==> ring_setadd (ring_of_integers k)
              (ring_coset (ring_of_integers k) M x) j =
            ring_coset (ring_of_integers k) j (x:A)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[RING_COSET_SETADD] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SETADD_ASSOC o lhand o snd) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC RING_SETADD_LSUBSET THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{ring_coset (ring_of_integers k) j x | x | x IN
     ring_carrier(ring_of_integers k)} =
    IMAGE (\s. ring_setadd (ring_of_integers k) s j)
          {ring_coset (ring_of_integers k) M (x:A) | x | x IN
           ring_carrier(ring_of_integers k)}`
  (LABEL_TAC "img") THENL
   [REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
    MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t. s IN {ring_coset (ring_of_integers k) M (x:A) | x | x IN
                ring_carrier(ring_of_integers k)} /\
          t IN {ring_coset (ring_of_integers k) M x | x | x IN
                ring_carrier(ring_of_integers k)} /\
          ring_setadd (ring_of_integers k) s j =
          ring_setadd (ring_of_integers k) t j
          ==> s = t`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\s. ring_setadd (ring_of_integers k) s (j:A->bool)`;
                   `{ring_coset (ring_of_integers k) M (x:A) | x | x IN
                     ring_carrier(ring_of_integers k)}`]
      CARD_IMAGE_EQ_INJ) THEN
    REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REMOVE_THEN "img" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_coset (ring_of_integers k) M (y:A) = M` MP_TAC THENL
   [TRANS_TAC EQ_TRANS
     `ring_coset (ring_of_integers k) M (ring_0 (ring_of_integers k):A)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[RING_COSET_0]] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `ring_0 (ring_of_integers k):A` THEN REWRITE_TAC[RING_0];
      ASM_SIMP_TAC[RING_0] THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `y:A`]
        RING_COSET_EQ_IDEAL) THEN
      ASM_SIMP_TAC[RING_COSET_0]];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[ring_coset; IN_ELIM_THM] THEN
  EXISTS_TAC `ring_0 k:A` THEN ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_RZERO THEN
  ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]);;
