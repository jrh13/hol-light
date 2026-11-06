(* ========================================================================= *)
(* Ideal classes of a domain, their invariance under ring isomorphisms, and  *)
(* the finiteness of the class group of a number field by the box principle  *)
(* (no Minkowski theory, no embeddings).                                     *)
(*                                                                           *)
(*   ideal_classes r  = the set of the classes ideal_class r j of the        *)
(*                      nonzero ideals j (ideal_class of                     *)
(*                      ANT/dedekind_struct.ml: the nonzero ideals k with    *)
(*                      (a) j = (b) k for some a, b <> 0)                    *)
(*   class_number r   = CARD(ideal_classes r)                                *)
(*                                                                           *)
(* Abstract part: an ideal j has the class of a nonzero ideal k iff k is in  *)
(* the class of j (IDEAL_CLASS_EQ); a Dedekind domain is a PID iff it has    *)
(* exactly one class (DEDEKIND_PID_EQ_CLASS_NUMBER_1). A ring isomorphism    *)
(* maps the classes of one ring onto those of the other                      *)
(* (IDEAL_CLASS_ISOMORPHIC_IMAGE), so isomorphic rings have equinumerous     *)
(* sets of ideal classes (ISOMORPHIC_RING_IDEAL_CLASSES) and, if one of them *)
(* is finite, the same class number (ISOMORPHIC_RING_CLASS_NUMBER;           *)
(* class_number is a CARD, unspecified on infinite sets).                    *)
(*                                                                           *)
(* Number fields k, with O = ring_of_integers k: there are finitely many     *)
(* nonzero ideals of bounded norm (NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM:  *)
(* an ideal of norm m contains m, and the ideals containing m correspond to  *)
(* subsets of the finite ring O/(m); in particular finitely many nonzero     *)
(* primes, NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM, each of norm at    *)
(* least 2, NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2); every class contains an     *)
(* ideal of norm at most n! (n B)^n, where w is an integral basis of size n  *)
(* and B bounds the entries of the multiplication matrices of the w i        *)
(* (NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT); hence a bound independent of   *)
(* the class (NUMBER_FIELD_IDEAL_CLASS_BOUND), finitely many classes         *)
(* (NUMBER_FIELD_CLASS_GROUP_FINITE), a positive class number                *)
(* (NUMBER_FIELD_CLASS_NUMBER_POS), and O is a PID iff the class number is 1 *)
(* (NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1); isomorphic number fields have the   *)
(* same class number (NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC). Every ideal     *)
(* class contains an ideal prime to a given nonzero ideal                    *)
(* (NUMBER_FIELD_IDEAL_CLASS_COPRIME).                                       *)
(*                                                                           *)
(* Route of the bound (Hurwitz). For the class of j take a nonzero ideal i   *)
(* with i j principal (DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE), and t with    *)
(* t^n <= N(i) < (t+1)^n. Two of the (t+1)^n elements sum_k m_k w_k with 0   *)
(* <= m_k <= t are congruent modulo i (FREE_BASIS_IDEAL_BOX_PRINCIPLE), so i *)
(* contains a nonzero a with coordinates bounded by t, and N((a)) =          *)
(* |det(M_a)| <= n! (n t B)^n <= n! (n B)^n N(i)                             *)
(* (NUMBER_FIELD_IDEAL_SMALL_ELEMENT, with FREE_BASIS_NORM_BOUND:            *)
(* INT_DET_BOUND and the linearity of the multiplication matrix in its       *)
(* argument). Since (a) is contained in i, it is a product i j1 (a Dedekind  *)
(* domain), so N(j1) = N((a)) / N(i) <= n! (n B)^n, and j1 is equivalent to  *)
(* j.                                                                        *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (FINITE_IDEALS_SUPERSET),                     *)
(* Library/fieldtheory.ml, Library/isum.ml, ANT/algmisc.ml (NUM_ROOT_FLOOR,  *)
(* UPPER_BOUND_FINITE_SET_INT), ANT/ideal_arith.ml, ANT/dedekind.ml,         *)
(* ANT/dedekind_struct.ml (ideal_class, IN_IDEAL_CLASS,                      *)
(* IN_IDEAL_CLASS_ISOMORPHIC_IMAGE), ANT/ideal_norm.ml, Library/ring_det.ml, *)
(* ANT/zlattice.ml (INT_DET_BOUND), ANT/numfield.ml, ANT/ring_of_integers.ml *)
(* and ANT/norm_index.ml.                                                    *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/isum.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/ideal_norm.ml";;
needs "Library/ring_det.ml";;
needs "ANT/zlattice.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/norm_index.ml";;

let ideal_classes = new_definition
 `ideal_classes (r:A ring) =
  {ideal_class r j | j | ring_ideal r j /\ ~(j = {ring_0 r})}`;;

let class_number = new_definition
 `class_number (r:A ring) = CARD(ideal_classes r)`;;

(* ------------------------------------------------------------------------- *)
(* Abstract part: classes of nonzero ideals of a domain.                     *)
(* ------------------------------------------------------------------------- *)

let IDEAL_CLASS_EQ = prove
 (`!r j k:A->bool.
        integral_domain r /\ ring_ideal r k /\ ~(k = {ring_0 r})
        ==> (ideal_class r j = ideal_class r k <=> k IN ideal_class r j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `k:A->bool`) THEN
    ASM_SIMP_TAC[IDEAL_CLASS_REFL];
    ASM_MESON_TAC[IDEAL_CLASS_SYM; IDEAL_CLASS_TRANS]]);;

(* In a domain the unit ideal is a nonzero ideal.                            *)
let INTEGRAL_DOMAIN_UNIT_IDEAL = prove
 (`!r:A ring.
        integral_domain r
        ==> ring_ideal r (ring_carrier r) /\
            ~(ring_carrier r = {ring_0 r})`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
    INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING) THEN
  SIMP_TAC[trivial_ring; RING_IDEAL_CARRIER]);;

let DEDEKIND_PID_EQ_CLASS_NUMBER_1 = prove
 (`!r:A ring. dedekind_domain r ==> (PID r <=> ideal_classes r HAS_SIZE 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_UNIT_IDEAL) THEN
  CONV_TAC(RAND_CONV HAS_SIZE_CONV) THEN EQ_TAC THENL
   [DISCH_TAC THEN
    EXISTS_TAC `ideal_class r (ring_carrier r):(A->bool)->bool` THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[ideal_classes; IN_SING; IN_ELIM_THM] THEN
    X_GEN_TAC `c:(A->bool)->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `j:A->bool` STRIP_ASSUME_TAC) THEN
      ASM_SIMP_TAC[IDEAL_CLASS_EQ] THEN
      MATCH_MP_TAC PRINCIPAL_IDEAL_CLASS THEN ASM_MESON_TAC[PID];
      DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `c:(A->bool)->bool`) THEN
    ASM_REWRITE_TAC[PID] THEN X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j = {ring_0 r:A}` THEN
    ASM_REWRITE_TAC[PRINCIPAL_IDEAL_0] THEN
    MATCH_MP_TAC IDEAL_CLASS_PRINCIPAL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `ring_carrier r:A->bool`]
      IDEAL_CLASS_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `s = {c:B} ==> !x y. x IN s /\ y IN s ==> x = y`)) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ideal_classes; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The box principle.                                                        *)
(* ------------------------------------------------------------------------- *)

let FREE_BASIS_IDEAL_BOX_PRINCIPLE = prove
 (`!r:A ring n w i t.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        ring_ideal r i /\ FINITE(ring_carrier(quotient_ring r i)) /\
        ideal_norm r i < (t + 1) EXP n
        ==> ?c. (!m. m < n ==> abs(c m) <= &t) /\
                (?m. m < n /\ ~(c m = &0)) /\
                ring_sum r {m | m < n}
                  (\m. ring_mul r (ring_of_int r (c m)) (w m)) IN i`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [free_basis]) THEN
  ABBREV_TAC
   `x = \f:num->num. ring_sum r {m | m < n}
                       (\m. ring_mul r (ring_of_int r (&(f m))) (w m)):A` THEN
  SUBGOAL_THEN `!f:num->num. (x:(num->num)->A) f IN ring_carrier r`
  ASSUME_TAC THENL [EXPAND_TAC "x" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`0`; `t + 1`; `{j:num | j <= t}`; `n:num`;
                 `{m:num | m < n}`] HAS_SIZE_FUNSPACE) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_LT; HAS_SIZE_NUMSEG_LE] THEN
  ABBREV_TAC
   `S = {f:num->num | (!m. m IN {m | m < n} ==> f m IN {j | j <= t}) /\
                      (!m. ~(m IN {m | m < n}) ==> f m = 0)}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `~(!f g. f IN S /\ g IN S /\
            ring_coset r i ((x:(num->num)->A) f) = ring_coset r i (x g)
            ==> f = g)`
  MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`\f. ring_coset r i ((x:(num->num)->A) f)`;
                   `S:(num->num)->bool`; `(t + 1) EXP n`]
      HAS_SIZE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`IMAGE (\f. ring_coset r i ((x:(num->num)->A) f)) S`;
      `ring_carrier(quotient_ring r (i:A->bool))`] CARD_SUBSET) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN
    UNDISCH_TAC `ideal_norm r (i:A->bool) < (t + 1) EXP n` THEN
    ASM_SIMP_TAC[ideal_norm; QUOTIENT_RING_CARRIER] THEN
    REWRITE_TAC[NOT_IMP] THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `f:num->num` THEN DISCH_TAC THEN
      EXISTS_TAC `(x:(num->num)->A) f` THEN ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`f:num->num`; `g:num->num`] THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `\m. &((f:num->num) m) - &((g:num->num) m):int` THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x <= t /\ &0 <= y /\ y <= t ==> abs(x - y:int) <= t`) THEN
    ASM_SIMP_TAC[INT_POS; INT_OF_NUM_LE];
    UNDISCH_TAC `~(f:num->num = g)` THEN
    REWRITE_TAC[FUN_EQ_THM; NOT_FORALL_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[INT_SUB_0; INT_OF_NUM_EQ] THEN
    ASM_CASES_TAC `m:num < n` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((f:num->num) m = g m)` THEN ASM_SIMP_TAC[];
    UNDISCH_TAC
     `ring_coset r i ((x:(num->num)->A) f) = ring_coset r i (x g)` THEN
    ASM_SIMP_TAC[RING_COSET_EQ] THEN
    MATCH_MP_TAC(SET_RULE `(a:A) = b ==> b IN s ==> a IN s`) THEN
    EXPAND_TAC "x" THEN
    MP_TAC(ISPECL [`r:A ring`; `{m:num | m < n}`; `w:num->A`]
      RING_INT_LINCOMB) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)])]);;

(* ------------------------------------------------------------------------- *)
(* Number fields: ideals of bounded norm, the class bound, finiteness.       *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM = prove
 (`!k:A ring c.
        number_field k
        ==> FINITE {j | ring_ideal (ring_of_integers k) j /\
                        ~(j = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) j <= c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\m. {j | ring_ideal (ring_of_integers k) j /\
                            ideal_generated (ring_of_integers k)
                              {ring_of_num k m} SUBSET j})
                  (1..c)):(A->bool)->bool` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_IDEALS_SUPERSET THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC(SET_RULE
     `!x:A s a. x IN s /\ ~(x = a) ==> ~(s = {a})`) THEN
    EXISTS_TAC `ring_of_num k m:A` THEN
    REWRITE_TAC[IN_IDEAL_GENERATED_SELF] THEN
    REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    REWRITE_TAC[RING_OF_INT_OF_NUM] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    REWRITE_TAC[RING_CHAR_EQ_0] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `j:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN STRIP_TAC THEN
    EXISTS_TAC `ideal_norm (ring_of_integers k) (j:A->bool)` THEN
    MP_TAC(ISPECL [`k:A ring`; `j:A->bool`]
      RING_OF_INTEGERS_FINITE_QUOTIENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[IN_NUMSEG; IDEAL_NORM_POS; IN_ELIM_THM] THEN
    MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[SING_SUBSET] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
      IDEAL_NORM_IN_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS]]);;

let NUMBER_FIELD_FINITE_PRIME_IDEALS_BOUNDED_NORM = prove
 (`!k:A ring c.
        number_field k
        ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        ideal_norm (ring_of_integers k) P <= c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{j | ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k}) /\
         ideal_norm (ring_of_integers k) (j:A->bool) <= c}` THEN
  ASM_SIMP_TAC[NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_RING_IDEAL]);;

let NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2 = prove
 (`!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> FINITE(ring_carrier(quotient_ring (ring_of_integers k) P)) /\
            2 <= ideal_norm (ring_of_integers k) P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    DISCH_TAC THEN REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 < n`] THEN
    MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
    RULE_ASSUM_TAC(REWRITE_RULE[prime_ideal; proper_ideal; PSUBSET]) THEN
    ASM_REWRITE_TAC[]]);;

(* The norm of an integer combination with coefficients bounded by t of an  *)
(* integral basis whose multiplication matrices are bounded by B.           *)
let FREE_BASIS_NORM_BOUND = prove
 (`!r:A ring n w B c t.
        free_basis (integer_ring,r) (ring_of_int r) n w /\
        (!i l m. i < n /\ l < n /\ m < n
                 ==> abs(mul_matrix (integer_ring,r) (ring_of_int r)
                           n w (w i) m l) <= B) /\
        (!m. m < n ==> abs(c m) <= &t)
        ==> abs(algebra_norm (integer_ring,r) (ring_of_int r)
                 (ring_sum r {m | m < n}
                    (\m. ring_mul r (ring_of_int r (c m)) (w m)))) <=
            &(FACT n) * ((&n * B) * &t) pow n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`; `n:num`;
    `w:num->A`; `ring_sum r {m | m < n}
      (\m. ring_mul r (ring_of_int r ((c:num->int) m)) ((w:num->A) m))`]
    ALGEBRA_NORM_FREE_BASIS) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; RING_SUM] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`{i:num | i < n}`;
    `mul_matrix (integer_ring,r) (ring_of_int r) n w
       (ring_sum r {m | m < n}
          (\m. ring_mul r (ring_of_int r ((c:num->int) m)) ((w:num->A) m)))`;
    `(&n * (B:int)) * &t`] INT_DET_BOUND) THEN
  REWRITE_TAC[CARD_NUMSEG_LT; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  MP_TAC(ISPECL [`ring_of_int r:int->A`; `integer_ring`; `r:A ring`; `n:num`;
                 `w:num->A`; `{m:num | m < n}`; `c:num->int`; `w:num->A`;
                 `p:num`; `q:num`] MUL_MATRIX_RING_SUM) THEN
  ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; FINITE_NUMSEG_LT; IN_ELIM_THM;
                  RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `&(CARD {m:num | m < n}) * (&t * B):int` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[CARD_NUMSEG_LT] THEN INT_ARITH_TAC] THEN
  REWRITE_TAC[INTEGER_RING_SUM] THEN MATCH_MP_TAC ISUM_ABS_BOUND THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_MUL2 THEN
  ASM_SIMP_TAC[INT_ABS_POS]);;

(* Every nonzero ideal j of O_K contains a nonzero a with N((a)) <= n! (n    *)
(* B)^n N(j).                                                                *)
let NUMBER_FIELD_IDEAL_SMALL_ELEMENT = prove
 (`!k:A ring n w B j.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        (!i l m. i < n /\ l < n /\ m < n
                 ==> abs(mul_matrix (integer_ring,ring_of_integers k)
                           (ring_of_int k) n w (w i) m l)
                     <= B) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ?a. a IN j /\ ~(a = ring_0 k) /\
                &(ideal_norm (ring_of_integers k)
                    (ideal_generated (ring_of_integers k) {a})) <=
                (&(FACT n) * (&n * B) pow n) *
                &(ideal_norm (ring_of_integers k) j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_char(k:A ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(integer_ring,ring_of_integers k) (ring_of_int k:int->A)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring`
      RING_HOMOMORPHISM_INTEGER_RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`]
      RING_OF_INTEGERS_FREE_BASIS_FIELD) THEN
    MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_SIMP_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (B:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `abs(mul_matrix (integer_ring,ring_of_integers k)
                      (ring_of_int k) n w ((w:num->A) 0) 0 0)` THEN
    REWRITE_TAC[INT_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `ideal_norm (ring_of_integers k) (j:A->bool)`]
    NUM_ROOT_FLOOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                 `j:A->bool`; `t:num`] FREE_BASIS_IDEAL_BOX_PRINCIPLE) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->int` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `m0:num`) ASSUME_TAC))) THEN
  ABBREV_TAC `a = ring_sum (ring_of_integers k) {m | m < n}
      (\m. ring_mul k (ring_of_int k ((c:num->int) m)) ((w:num->A) m))` THEN
  EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->int` o last o CONJUNCTS o
      GEN_REWRITE_RULE I [free_basis]) THEN
    ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV;
                    RING_OF_INTEGERS] THEN
    ASM_MESON_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`] NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_Q) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `a:A`]
    NUMBER_FIELD_NORM_INTEGRAL_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[ring_monomorphism] o
    GEN_REWRITE_RULE I [GSYM RING_MONOMORPHISM_INTEGER_RING_OF_INT]) THEN
  REWRITE_TAC[INTEGER_RING; IN_UNIV] THEN
  DISCH_THEN(fun th -> DISCH_THEN(SUBST_ALL_TAC o MATCH_MP th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `&(FACT n) * ((&n * (B:int)) * &t) pow n` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `n:num`; `w:num->A`;
                   `B:int`; `c:num->int`; `t:num`] FREE_BASIS_NORM_BOUND) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [INT_POW_MUL] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN REWRITE_TAC[INT_POS] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN
    ASM_SIMP_TAC[INT_POW_LE; INT_LE_MUL; INT_POS] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE]]);;

let NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT = prove
 (`!k:A ring n w B.
        number_field k /\
        free_basis (integer_ring,ring_of_integers k) (ring_of_int k) n w /\
        (!i l m. i < n /\ l < n /\ m < n
                 ==> abs(mul_matrix (integer_ring,ring_of_integers k)
                           (ring_of_int k) n w (w i) m l)
                     <= B)
        ==> !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                ==> ?j'. j' IN ideal_class (ring_of_integers k) j /\
                         &(ideal_norm (ring_of_integers k) j') <=
                         &(FACT n) * (&n * B) pow n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `dedekind_domain(ring_of_integers k:A ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `?i b. ring_ideal (ring_of_integers k) i /\ ~(i = {ring_0 k}) /\
          b IN ring_carrier(ring_of_integers k) /\ ~(b = ring_0 k) /\
          ideal_prod (ring_of_integers k) j i =
          ideal_generated (ring_of_integers k) {b:A}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
      DEDEKIND_IDEAL_HAS_PRINCIPAL_MULTIPLE) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `B:int`; `i:A->bool`]
    NUMBER_FIELD_IDEAL_SMALL_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(a:A) IN ring_carrier(ring_of_integers k) /\
    ~(ideal_generated (ring_of_integers k) {a:A} = {ring_0 k})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; DISCH_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!x:A s z. x IN s /\ ~(x = z) ==> ~(s = {z})`) THEN
    EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[IN_IDEAL_GENERATED_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?j'. ring_ideal (ring_of_integers k) j' /\
         ideal_prod (ring_of_integers k) i j' =
         ideal_generated (ring_of_integers k) {a:A}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ideal_generated (ring_of_integers k) {a:A}`;
                   `i:A->bool`] DEDEKIND_IDEAL_SUBSET_IFF_DIVIDES) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(j' = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `i:A->bool`; `j':A->bool`]
      IDEAL_PROD_EQ_ZERO) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  EXISTS_TAC `j':A->bool` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IDEAL_CLASS; RING_OF_INTEGERS] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME
     `ideal_prod (ring_of_integers k) i j' =
      ideal_generated (ring_of_integers k) {a:A}`)) THEN
    SUBST1_TAC(SYM(ASSUME
     `ideal_prod (ring_of_integers k) j i =
      ideal_generated (ring_of_integers k) {b:A}`)) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `i:A->bool`;
                   `j':A->bool`] IDEAL_PROD_ASSOC) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET];
                    DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC IDEAL_PROD_COMM THEN CONJ_TAC THEN
    MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_PROD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&(ideal_norm (ring_of_integers k) (j':A->bool)):int`;
                 `&(FACT n) * (&n * (B:int)) pow n`;
                 `&(ideal_norm (ring_of_integers k) (i:A->bool)):int`]
    INT_LE_LMUL_EQ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LT; ARITH_RULE `0 < n <=> 1 <= n`] THEN
    MATCH_MP_TAC IDEAL_NORM_POS THEN
    MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`k:A ring`; `i:A->bool`; `j':A->bool`]
    NUMBER_FIELD_IDEAL_NORM_MUL_Q) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_IDEAL_CLASS_BOUND = prove
 (`!k:A ring.
        number_field k
        ==> ?c. !j. ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
                    ==> ?j'. j' IN ideal_class (ring_of_integers k) j /\
                             ideal_norm (ring_of_integers k) j' <= c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `w:num->A` o MATCH_MP RING_OF_INTEGERS_FREE) THEN
  ABBREV_TAC
   `n = extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)` THEN
  MP_TAC(ISPECL
   [`\p. abs(mul_matrix (integer_ring,ring_of_integers k)
               (ring_of_int k) n w ((w:num->A)(FST p)) (SND(SND p))
               (FST(SND p)))`;
    `{i:num | i < n} CROSS ({l:num | l < n} CROSS {m:num | m < n})`]
    UPPER_BOUND_FINITE_SET_INT) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:int`) THEN
  MP_TAC(ISPECL [`k:A ring`; `n:num`; `w:num->A`; `B:int`]
    NUMBER_FIELD_IDEAL_CLASS_BOUND_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  EXISTS_TAC `num_of_int(&(FACT n) * (&n * (B:int)) pow n)` THEN
  X_GEN_TAC `j:A->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j':A->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  MP_TAC(ISPEC `&(FACT n) * (&n * (B:int)) pow n` INT_OF_NUM_OF_INT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INT_POS; INT_LE_TRANS];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let NUMBER_FIELD_CLASS_GROUP_FINITE = prove
 (`!k:A ring. number_field k ==> FINITE(ideal_classes(ring_of_integers k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integral_domain(ring_of_integers k:A ring)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `c:num` o
    MATCH_MP NUMBER_FIELD_IDEAL_CLASS_BOUND) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (ideal_class (ring_of_integers k))
                {j:A->bool | ring_ideal (ring_of_integers k) j /\
                             ~(j = {ring_0 k}) /\
                             ideal_norm (ring_of_integers k) j <= c}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM] THEN
  REWRITE_TAC[ideal_classes; RING_OF_INTEGERS] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `x:(A->bool)->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `j:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `j':A->bool` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_IDEAL_CLASS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RING_OF_INTEGERS]) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`; `j':A->bool`]
    IDEAL_CLASS_EQ) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS]);;

let NUMBER_FIELD_CLASS_NUMBER_POS = prove
 (`!k:A ring. number_field k ==> 1 <= class_number(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[class_number; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0; NUMBER_FIELD_CLASS_GROUP_FINITE] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `ideal_class (ring_of_integers k)
                (ring_carrier(ring_of_integers k:A ring))` THEN
  REWRITE_TAC[ideal_classes; IN_ELIM_THM] THEN
  EXISTS_TAC `ring_carrier(ring_of_integers k:A ring)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGRAL_DOMAIN_UNIT_IDEAL THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD]);;

let NUMBER_FIELD_PID_EQ_CLASS_NUMBER_1 = prove
 (`!k:A ring.
        number_field k
        ==> (PID(ring_of_integers k) <=>
             class_number(ring_of_integers k) = 1)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DEDEKIND_PID_EQ_CLASS_NUMBER_1; DEDEKIND_RING_OF_INTEGERS] THEN
  ASM_SIMP_TAC[HAS_SIZE; class_number; NUMBER_FIELD_CLASS_GROUP_FINITE]);;

let NUMBER_FIELD_IDEAL_CLASS_COPRIME = prove
 (`!k i j:A->bool.
        number_field k /\
        ring_ideal (ring_of_integers k) i /\ ~(i = {ring_0 k}) /\
        ring_ideal (ring_of_integers k) j /\ ~(j = {ring_0 k})
        ==> ?l. l IN ideal_class (ring_of_integers k) i /\
                ring_setadd (ring_of_integers k) l j =
                ring_carrier(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_IDEAL_CLASS_COPRIME THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS]);;

(* ------------------------------------------------------------------------- *)
(* Ideal classes along ring isomorphisms.                                    *)
(* ------------------------------------------------------------------------- *)

let IDEAL_CLASS_ISOMORPHIC_IMAGE = prove
 (`!r s (h:A->B) j.
        ring_isomorphism(r,s) h /\ ring_ideal r j
        ==> ideal_class s (IMAGE h j) = IMAGE (IMAGE h) (ideal_class r j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_isomorphism]) THEN
  REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:B->A` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `k':B->bool` THEN
  REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `IMAGE (g:B->A) k'` THEN
    SUBGOAL_THEN
     `k' SUBSET ring_carrier(s:B ring) /\ j SUBSET ring_carrier(r:A ring)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_IDEAL_CLASS; RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:B ring`; `r:A ring`; `g:B->A`; `IMAGE (h:A->B) j`;
                   `k':B->bool`] IN_IDEAL_CLASS_ISOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:A->bool`
     (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    MATCH_MP_TAC IN_IDEAL_CLASS_ISOMORPHIC_IMAGE THEN
    EXISTS_TAC `r:A ring` THEN ASM_REWRITE_TAC[]]);;

let ISOMORPHIC_RING_IDEAL_CLASSES = prove
 (`!r:A ring s:B ring.
        r isomorphic_ring s ==> ideal_classes r =_c ideal_classes s`,
  let lemma = prove
   (`!r:A ring s:B ring f g.
        ring_isomorphisms(r,s) (f,g)
        ==> !c. c IN ideal_classes r
                ==> IMAGE (IMAGE f) c IN ideal_classes s /\
                    IMAGE (IMAGE g) (IMAGE (IMAGE f) c) = c`,
    REPEAT GEN_TAC THEN REWRITE_TAC[RING_ISOMORPHISMS_ISOMORPHISM] THEN
    STRIP_TAC THEN REWRITE_TAC[ideal_classes; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `ring_ideal s (IMAGE (f:A->B) j) /\ ~(IMAGE f j = {ring_0 s})`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `j:A->bool`;
                     `j:A->bool`] IN_IDEAL_CLASS_ISOMORPHIC_IMAGE) THEN
      ASM_SIMP_TAC[IDEAL_CLASS_REFL] THEN SIMP_TAC[IN_IDEAL_CLASS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:B ring`; `r:A ring`; `g:B->A`; `IMAGE (f:A->B) j`]
      IDEAL_CLASS_ISOMORPHIC_IMAGE) THEN
    MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `j:A->bool`]
      IDEAL_CLASS_ISOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; AP_TERM_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!s. (!x. x IN s ==> (g:B->A) ((f:A->B) x) = x) /\ t SUBSET s
          ==> IMAGE g (IMAGE f t) = t`) THEN
    EXISTS_TAC `ring_carrier r:A->bool` THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[isomorphic_ring; ring_isomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `g:B->A`] THEN DISCH_TAC THEN
  REWRITE_TAC[EQ_C_BIJECTIONS] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (IMAGE (f:A->B))`; `IMAGE (IMAGE (g:B->A))`] THEN
  CONJ_TAC THEN MATCH_MP_TAC lemma THEN ASM_MESON_TAC[RING_ISOMORPHISMS_SYM]);;

let ISOMORPHIC_RING_CLASS_NUMBER = prove
 (`!r:A ring s:B ring.
        r isomorphic_ring s /\
        (FINITE(ideal_classes r) \/ FINITE(ideal_classes s))
        ==> class_number r = class_number s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (ASSUME_TAC o MATCH_MP ISOMORPHIC_RING_IDEAL_CLASSES) MP_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CARD_FINITE_CONG) THEN
  REWRITE_TAC[class_number] THEN DISCH_TAC THEN
  MATCH_MP_TAC CARD_EQ_CARD_IMP THEN ASM_REWRITE_TAC[]);;

let NUMBER_FIELD_CLASS_NUMBER_ISOMORPHIC = prove
 (`!k:A ring l:B ring.
        number_field k /\ k isomorphic_ring l
        ==> class_number(ring_of_integers k) =
            class_number(ring_of_integers l)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISOMORPHIC_RING_CLASS_NUMBER THEN
  ASM_SIMP_TAC[ISOMORPHIC_RING_RING_OF_INTEGERS;
               NUMBER_FIELD_CLASS_GROUP_FINITE]);;
