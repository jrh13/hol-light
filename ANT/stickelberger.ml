(* ========================================================================= *)
(* The Stickelberger theorem: the discriminant of a number field is 0 or 1   *)
(* modulo 4.                                                                 *)
(*                                                                           *)
(* Main results: for an array f of algebraic integers in a field of          *)
(* characteristic 0 whose permanent a and squared determinant d are          *)
(* integers, d == a^2 (mod 4) (RING_DET_PERMANENT_MOD_4); for algebraic      *)
(* integers w_j of a number field and an enumeration e_i of its complex      *)
(* embeddings, the permanent of (e_i(w_j)) is an integer                     *)
(* (NUMBER_FIELD_PERMANENT_INTEGRAL); hence the Stickelberger theorem d_K == *)
(* 0 or 1 (mod 4) (NUMBER_FIELD_DISCRIMINANT_MOD_4; the sign of d_K is       *)
(* NUMBER_FIELD_DISCRIMINANT_SIGN of ANT/infinite_places.ml).                *)
(*                                                                           *)
(* Routes (no normal closure is needed). Determinant and permanent: with P   *)
(* and N the sums of prod_i f i (p i) over the even and the odd permutations *)
(* p, det f = P - N and the permanent is P + N; P and N are algebraic        *)
(* integers and 4 P N = a^2 - d, so P N is a rational algebraic integer,     *)
(* hence an integer (RING_OF_INTEGERS_PRIME_SUBFIELD). Permanent of          *)
(* (e_i(w_j)): by the Ryser formula (RING_SUM_PERMUTATIONS_RYSER of          *)
(* Library/ring_det.ml) a sum of terms +-prod_i e_i(w_t),                    *)
(* w_t = sum_(j IN t) w_j, which are the images of the norms N(w_t)          *)
(* (NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS), integers. Stickelberger: for an   *)
(* integral basis w, det(e_i(w_j))^2 = d_K                                   *)
(* (NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS), and squares are 0 or 1 mod 4.     *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml,                      *)
(* Library/permutations.ml (evenperm), Library/ringtheory.ml                 *)
(* (RING_OF_INT_EQ_CHAR_0), Library/ring_det.ml (ring_det,                   *)
(* RING_SUM_PERMUTATIONS_RYSER, free_basis), ANT/numfield.ml,                *)
(* ANT/ring_of_integers.ml (RING_OF_INTEGERS_FREE), ANT/discriminant.ml,     *)
(* ANT/complex_embeddings.ml (and with it Multivariate/cauchy.ml) and        *)
(* ANT/infinite_places.ml (NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS,             *)
(* NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS). Also Multivariate/complex_ring.ml  *)
(* (complex_ring).                                                           *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/permutations.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "Multivariate/complex_ring.ml";;

(* ------------------------------------------------------------------------- *)
(* Squared determinants of arrays of algebraic integers modulo 4, and the    *)
(* Stickelberger theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let RING_DET_PERMANENT_MOD_4 = prove
 (`!k s (f:K->K->A) a d.
        field k /\ ring_char k = 0 /\ FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> f i j IN ring_carrier(ring_of_integers k)) /\
        ring_sum k {p | p permutes s} (\p. ring_product k s (\i. f i (p i))) =
        ring_of_int k a /\
        ring_pow k (ring_det k s f) 2 = ring_of_int k d
        ==> (d == a pow 2) (mod &4)`,
  let lemma = prove
   (`!k x:A b c.
        field k /\ ring_char k = 0 /\
        x IN ring_carrier(ring_of_integers k) /\ ~(c = &0) /\
        ring_mul k (ring_of_int k c) x = ring_of_int k b
        ==> ?m. x = ring_of_int k m`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_PRIME_SUBFIELD) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `{ring_0 k:A}`] SUBFIELD_SUBFIELD_GENERATED) THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`ring_carrier(subfield_generated k {ring_0 k:A})`,
             `u:A->bool`) THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `u:A->bool`; `ring_of_int k c:A`]
      IN_SUBFIELD_LINV) THEN
    ASM_SIMP_TAC[IN_SUBRING_INT; SUBFIELD_IMP_SUBRING_OF; RING_OF_INT_EQ_0;
                 INTEGER_RULE `!x:int. &0 divides x <=> x = &0`] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_of_int k c:A`] RING_INV) THEN
    REWRITE_TAC[RING_OF_INT] THEN
    SPEC_TAC(`ring_inv k (ring_of_int k c):A`, `z:A`) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `x = ring_mul k z (ring_of_int k b):A` SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check ((=) `ring_of_int k b:A` o rand o
        concl)) THEN
      UNDISCH_TAC `ring_mul k (ring_of_int k c) z = ring_1 k:A` THEN
      W(MP_TAC o RING_RULE o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
                      REWRITE_TAC[]];
      MATCH_MP_TAC IN_SUBFIELD_MUL THEN
      ASM_SIMP_TAC[IN_SUBRING_INT; SUBFIELD_IMP_SUBRING_OF]]) in
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `x = ring_sum k {p | p permutes s}
          (\p. if evenperm p then ring_product k s (\i. (f:K->K->A) i (p i))
               else ring_0 k)` THEN
  ABBREV_TAC
   `y = ring_sum k {p | p permutes s}
          (\p. if evenperm p then ring_0 k
               else ring_product k s (\i. (f:K->K->A) i (p i)))` THEN
  SUBGOAL_THEN `ring_mul k (x:A) y IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_SUBRING_MUL THEN REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
    MAP_EVERY EXPAND_TAC ["x"; "y"] THEN CONJ_TAC THEN
    MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
    X_GEN_TAC `p:K->K` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN SIMP_TAC[RING_OF_INTEGERS_SUBRING; IN_SUBRING_0] THEN
    MATCH_MP_TAC IN_SUBRING_PRODUCT THEN
    REWRITE_TAC[RING_OF_INTEGERS_SUBRING] THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_add k (x:A) y = ring_of_int k a /\
    ring_sub k x y = ring_det k s (f:K->K->A)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `ring_sum k {p | p permutes s}
        (\p. ring_product k s (\i. (f:K->K->A) i (p i))) =
      ring_of_int k a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXPAND_TAC ["x"; "y"] THEN REWRITE_TAC[ring_det] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_ADD o lhand o snd);
      W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_SUB o lhand o snd)] THEN
    (ANTS_TAC THENL
      [ASM_SIMP_TAC[FINITE_PERMUTATIONS] THEN REPEAT STRIP_TAC THEN
       COND_CASES_TAC THEN REWRITE_TAC[RING_PRODUCT; RING_0];
       DISCH_THEN(SUBST1_TAC o SYM)]) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[ring_sign] THEN COND_CASES_TAC THEN
    SIMP_TAC[RING_ADD_LZERO; RING_ADD_RZERO; RING_SUB_RZERO; RING_SUB_LZERO;
             RING_MUL_LID; RING_MUL_LNEG; RING_PRODUCT; RING_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k /\ y IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul k (ring_of_int k (&4)) (ring_mul k x y) =
    ring_of_int k (a pow 2 - d):A`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RING_OF_INT_CLAUSES] THEN
    REWRITE_TAC[GSYM(ASSUME `ring_add k (x:A) y = ring_of_int k a`);
                GSYM(ASSUME `ring_pow k (ring_det k s (f:K->K->A)) 2 =
                             ring_of_int k d`)] THEN
    REWRITE_TAC[GSYM(ASSUME
     `ring_sub k (x:A) y = ring_det k s (f:K->K->A)`)] THEN
    W(MP_TAC o RING_RULE o snd) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_mul k x y:A`; `a pow 2 - d:int`; `&4:int`]
    lemma) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:int`) THEN
  UNDISCH_TAC
   `ring_mul k (ring_of_int k (&4)) (ring_mul k x y) =
    ring_of_int k (a pow 2 - d):A` THEN
  ASM_SIMP_TAC[RING_OF_INT_CLAUSES; RING_OF_INT_EQ_CHAR_0] THEN
  DISCH_TAC THEN REWRITE_TAC[int_congruent] THEN EXISTS_TAC `--c:int` THEN
  ASM_INT_ARITH_TAC);;

let NUMBER_FIELD_PERMANENT_INTEGRAL = prove
 (`!k s (e:K->A->complex) (w:K->A).
        number_field k /\
        (!j. j IN s ==> w j IN ring_carrier(ring_of_integers k)) /\
        (!i j. i IN s /\ j IN s /\ e i = e j ==> i = j) /\
        IMAGE e s = complex_embeddings k
        ==> ?a. ring_sum complex_ring {p | p permutes s}
                  (\p. ring_product complex_ring s (\i. e i (w (p i)))) =
                Cx(real_of_int a)`,
  let lemma = prove
   (`!k x:A.
        number_field k /\ x IN ring_carrier(ring_of_integers k)
        ==> cproduct (complex_embeddings k) (\g. g x) IN
            {ring_of_int complex_ring a | a IN (:int)}`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
    MP_TAC(ISPECL [`k:A ring`; `g:A->complex`; `x:A`]
      NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_NORM_INTEGRAL_Q) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:int` SUBST1_TAC) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `m:int` THEN
    UNDISCH_TAC `(g:A->complex) IN complex_embeddings k` THEN
    REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN
    DISCH_THEN(fun th ->
      REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (CONJUNCT1 th)])) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s:K->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:K->A->complex`; `s:K->bool`] FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_COMPLEX_EMBEDDINGS THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. ring_product complex_ring s (\i. (e:K->A->complex) i x) =
        cproduct (complex_embeddings k) (\g. g x)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    SIMP_TAC[GSYM COMPLEX_RING_PRODUCT; FINITE_IMAGE;
             ASSUME `FINITE(s:K->bool)`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_PRODUCT_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
    UNDISCH_THEN
     `!i j. i IN s /\ j IN s /\ (e:K->A->complex) i = e j ==> i = j`
     (K ALL_TAC)] THEN
  SUBGOAL_THEN
   `!i. i IN s ==> ring_homomorphism(k,complex_ring) ((e:K->A->complex) i)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (e:K->A->complex) s = complex_embeddings k` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; complex_embeddings; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`complex_ring`; `s:K->bool`; `\i:K j:K. (e:K->A->complex) i ((w:K->A) j)`]
   RING_SUM_PERMUTATIONS_RYSER)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[FUN_EQ_THM] COMPLEX_RING_OF_INT)] THEN
  MATCH_MP_TAC(SET_RULE
   `!x:complex. x IN {ring_of_int complex_ring a | a IN (:int)}
                ==> ?a. x = ring_of_int complex_ring a`) THEN
  MATCH_MP_TAC IN_SUBRING_MUL THEN
  SIMP_TAC[PRIME_SUBRING; IN_SUBRING_POW; IN_SUBRING_NEG; IN_SUBRING_1] THEN
  MATCH_MP_TAC IN_SUBRING_SUM THEN REWRITE_TAC[PRIME_SUBRING] THEN
  X_GEN_TAC `t:K->bool` THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
  MATCH_MP_TAC IN_SUBRING_MUL THEN
  SIMP_TAC[PRIME_SUBRING; IN_SUBRING_POW; IN_SUBRING_NEG; IN_SUBRING_1] THEN
  SUBGOAL_THEN
   `FINITE(t:K->bool) /\
    !j. j IN t ==> (w:K->A) j IN ring_carrier(ring_of_integers k) /\
                   w j IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN
    UNDISCH_TAC `(t:K->bool) SUBSET s` THEN
    UNDISCH_TAC
     `!j. j IN s ==> (w:K->A) j IN ring_carrier(ring_of_integers k)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_product complex_ring s
      (\i. ring_sum complex_ring t (\j. (e:K->A->complex) i (w j))) =
    ring_product complex_ring s (\i. e i (ring_sum k (t:K->bool) w))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(k,complex_ring) ((e:K->A->complex) i)`
    MP_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
                  ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPECL [`w:K->A`; `t:K->bool`] o
               MATCH_MP RING_HOMOMORPHISM_SUM) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; SIMP_TAC[o_DEF]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_SUBRING_SUM THEN ASM_SIMP_TAC[RING_OF_INTEGERS_SUBRING]]);;

let NUMBER_FIELD_DISCRIMINANT_MOD_4 = prove
 (`!k:A ring.
        number_field k
        ==> (number_field_discriminant k == &0) (mod &4) \/
            (number_field_discriminant k == &1) (mod &4)`,
  let lemma = prove
   (`!a d:int. (d == a pow 2) (mod &4)
               ==> (d == &0) (mod &4) \/ (d == &1) (mod &4)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`a:int`; `&2:int`] INT_DIVISION_SIMP) THEN
    SPEC_TAC(`a div &2`, `q:int`) THEN GEN_TAC THEN
    DISJ_CASES_THEN SUBST1_TAC (SPEC `a:int` INT_REM_2_CASES) THEN
    DISCH_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC(INTEGER_RULE
     `!x y z n:int. (x == y) (mod n) /\ (y == z) (mod n)
                    ==> (x == z) (mod n)`) THEN
    EXISTS_TAC `(a:int) pow 2` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN INTEGER_TAC) in
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `n = extension_degree (subfield_generated k {ring_0 k:A},k) I` THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->A->complex` STRIP_ASSUME_TAC o
    MATCH_MP HAS_SIZE_INDEX) THEN
  DISCH_THEN(X_CHOOSE_TAC `w:num->A`) THEN
  SUBGOAL_THEN
   `(!i j. i < n /\ j < n /\ (e:num->A->complex) i = e j ==> i = j) /\
    IMAGE e {i | i < n} = complex_embeddings k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[EXISTS_UNIQUE_THM];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [free_basis]) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `e:num->A->complex`]
    NUMBER_FIELD_DISCRIMINANT_EMBEDDINGS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{i:num | i < n}`; `e:num->A->complex`;
                 `w:num->A`] NUMBER_FIELD_PERMANENT_INTEGRAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(X_CHOOSE_TAC `a:int`)] THEN
  MATCH_MP_TAC lemma THEN EXISTS_TAC `a:int` THEN
  MATCH_MP_TAC(BETA_RULE(ISPECL
   [`complex_ring`; `{i:num | i < n}`;
    `\i:num j:num. (e:num->A->complex) i ((w:num->A) j)`]
   RING_DET_PERMANENT_MOD_4)) THEN
  ASM_REWRITE_TAC[FIELD_COMPLEX_RING; RING_CHAR_COMPLEX_RING; FINITE_NUMSEG_LT;
                  COMPLEX_RING_OF_INT; COMPLEX_RING_POW; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN
  EXISTS_TAC `ring_of_integers k:A ring` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_RING_OF_INTEGERS THEN
    UNDISCH_TAC
     `!m. m < n ==> (e:num->A->complex) m IN complex_embeddings k` THEN
    REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
