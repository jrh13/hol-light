(* ========================================================================= *)
(* Infinitely many primes split completely in any finite extension of number *)
(* fields, in particular infinitely many primes of degree one, by the        *)
(* theorem of Schur on the prime divisors of the values of an integer        *)
(* polynomial (Narkiewicz Thm. 4.37; the qualitative form of the density     *)
(* statements of Neukirch VII.13 and Ribenboim 25.2).                        *)
(*                                                                           *)
(*   INTEGER_POLY_PRIME_DIVISORS_INFINITE: a nonconstant q in Z[X] has       *)
(*     infinitely many primes p dividing some value q(n), n in N (Schur)     *)
(*   NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q: infinitely many rational primes  *)
(*     split completely in a number field l                                  *)
(*   NUMBER_FIELD_TOTALLY_SPLIT_INFINITE: for number fields k, l             *)
(*     with h : k -> l infinitely many nonzero primes of O_k split           *)
(*     completely in O_l                                                     *)
(*   NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE: O_l has infinitely many        *)
(*     nonzero primes of absolute residue degree 1                           *)
(*                                                                           *)
(* On the way: every number field embeds into a number field that is Galois  *)
(* over its prime subfield (NUMBER_FIELD_GALOIS_CLOSURE_Q, from              *)
(* FINITE_EXTENSION_NORMAL_CLOSURE in an algebraic closure), hence an        *)
(* extension l of k into a number field Galois over k                        *)
(* (NUMBER_FIELD_GALOIS_CLOSURE), and total splitting of a rational prime    *)
(* descends to subfields (NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE,   *)
(* by the tower laws for e and f).                                           *)
(*                                                                           *)
(* Routes. Schur: if c = q(0) = 0 every prime divides q(p); else, with P the *)
(* product of the finitely many primes in question and m = |c| P, the value  *)
(* q(m t) = c (1 +- P t u) is not +-c for some t (a nonconstant polynomial   *)
(* takes each value finitely often, INTEGER_POLY_FIBRE_FINITE), so 1 +- P t  *)
(* u has a prime factor, which divides P and 1. Galois case                  *)
(* (NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE): l Galois over Q with group  *)
(* G and an integral primitive element a; the integer minimal polynomial of  *)
(* a is q(X) = prod_(g in G) (X - g(a))                                      *)
(* (NUMBER_FIELD_GALOIS_CONJUGATES_POLY). If p divides q(n) then n - g(a)    *)
(* lies in a prime above p for some g, so a - n lies in some prime P above   *)
(* p, and every s in the decomposition group D_P has s(a) - a in P. Outside  *)
(* the finitely many p below primes containing some g(a) - a with g <> I     *)
(* (NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE, from                     *)
(* DEDEKIND_IDEAL_FACTORIZATION) this forces D_P = {I}, that is p totally    *)
(* split (NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT, from                   *)
(* NUMBER_FIELD_GALOIS_SPLITTING_TYPES). The integral primitive element is   *)
(* NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT of ANT/integrality.ml.            *)
(* The relative version and the primes of degree one follow by choosing a    *)
(* prime above each split rational prime: distinct rational primes lie below *)
(* distinct primes.                                                          *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (polynomials, POLY_ROOT_BOUND,                *)
(* MONIC_POLY_EQ_ROOTS_PRODUCT), Library/fieldtheory.ml                      *)
(* (ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH, FINITE_EXTENSION_NORMAL_CLOSURE),    *)
(* Library/galois.ml, Library/primitive.ml (INT_PRIME), ANT/dedekind.ml,     *)
(* ANT/numfield.ml, ANT/prime_split.ml, ANT/dedekind_kummer.ml               *)
(* (RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL), ANT/relative_split.ml,     *)
(* ANT/integrality.ml (NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT),             *)
(* ANT/splitting_types.ml and ANT/decomposition_field.ml.                    *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/galois.ml";;
needs "Library/primitive.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/numfield.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/dedekind_kummer.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/integrality.ml";;
needs "ANT/splitting_types.ml";;
needs "ANT/decomposition_field.ml";;

(* ------------------------------------------------------------------------- *)
(* The theorem of Schur: prime divisors of the values of an integer          *)
(* polynomial.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Integer polynomials preserve congruences (POLY_EVALUATE_SUB_IN_IDEAL),    *)
(* and take each value only finitely often unless constant                   *)
(* (POLY_ROOT_BOUND).                                                        *)
let INTEGER_POLY_CONGRUENCE = prove
 (`!q m x y.
        q IN ring_carrier(poly_ring integer_ring (:1)) /\ m divides (x - y)
        ==> m divides (poly_eval integer_ring q x -
                       poly_eval integer_ring q y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. ring_sub integer_ring a b = a - b` ASSUME_TAC THENL
   [REWRITE_TAC[ring_sub; INTEGER_RING] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`integer_ring`; `ideal_generated integer_ring {m:int}`;
                 `q:(1->num)->int`; `y:int`; `x:int`]
    POLY_EVALUATE_SUB_IN_IDEAL) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; INTEGER_RING; IN_UNIV] THEN
  SIMP_TAC[IN_IDEAL_GENERATED_SING_EQ; INTEGER_RING; IN_UNIV;
           INTEGER_RING_DIVIDES; poly_eval] THEN
  ASM_REWRITE_TAC[]);;

let INTEGER_POLY_FIBRE_FINITE = prove
 (`!q v. q IN ring_carrier(poly_ring integer_ring (:1)) /\
         ~(poly_deg integer_ring q = 0)
         ==> FINITE {x | poly_eval integer_ring q x = v}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_ring`;
                 `poly_sub integer_ring (q:(1->num)->int)
                    (poly_const integer_ring v)`]
    POLY_ROOT_BOUND) THEN
  SUBGOAL_THEN
   `(poly_const integer_ring v:(1->num)->int) IN
    ring_carrier(poly_ring integer_ring (:1))`
  ASSUME_TAC THENL
   [REWRITE_TAC[POLY_CONST; INTEGER_RING; IN_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_sub integer_ring = ring_sub (poly_ring integer_ring (:1))`
  SUBST1_TAC THENL [REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INTEGRAL_DOMAIN_INTEGER_RING] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_SUB THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[RING_SUB_EQ_0] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `~(poly_deg integer_ring (poly_const integer_ring v:(1->num)->int) =
          0)` THEN
      REWRITE_TAC[POLY_DEG_CONST]];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; INTEGER_RING; IN_UNIV] THEN
  X_GEN_TAC `x:int` THEN
  REWRITE_TAC[POLY_RING_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_SUB o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RING_POLYNOMIAL] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[POLY_EVAL_CONST; INTEGER_RING; IN_UNIV] THEN
  REWRITE_TAC[ring_sub; INTEGER_RING] THEN INT_ARITH_TAC);;

let INTEGER_POLY_PRIME_DIVISORS_INFINITE = prove
 (`!q. q IN ring_carrier(poly_ring integer_ring (:1)) /\
       ~(poly_deg integer_ring q = 0)
       ==> INFINITE {p | prime p /\
                         ?n. &p divides poly_eval integer_ring q (&n)}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `c = poly_eval integer_ring (q:(1->num)->int) (&0)` THEN
  REWRITE_TAC[INFINITE] THEN
  ABBREV_TAC
   `S = {p | prime p /\ ?n. &p divides poly_eval integer_ring q (&n)}` THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `c:int = &0` THENL
   [UNDISCH_TAC `FINITE(S:num->bool)` THEN REWRITE_TAC[GSYM INFINITE] THEN
    MATCH_MP_TAC INFINITE_SUPERSET THEN EXISTS_TAC `{p | prime p}` THEN
    REWRITE_TAC[PRIMES_INFINITE] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:num` THEN
    MP_TAC(ISPECL [`q:(1->num)->int`; `&p:int`; `&p:int`; `&0:int`]
      INTEGER_POLY_CONGRUENCE) THEN
    ASM_REWRITE_TAC[INT_SUB_RZERO; INT_DIVIDES_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `P = nproduct S (\p:num. p)` THEN
  SUBGOAL_THEN `!p:num. p IN S ==> p divides P` ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    MP_TAC(ISPECL [`\p:num. p`; `S:num->bool`; `p:num`] NPRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[divides] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P:num = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[GSYM LT_NZ] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "S" THEN SIMP_TAC[IN_ELIM_THM; LT_NZ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `M = num_of_int(abs c) * P` THEN
  SUBGOAL_THEN `&M:int = abs c * &P` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    SIMP_TAC[GSYM INT_OF_NUM_MUL; INT_OF_NUM_OF_INT; INT_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(M:num = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[INT_ENTIRE] THEN
    ASM_REWRITE_TAC[INT_ABS_ZERO; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?t. ~(poly_eval integer_ring q (&(M * t)) = c) /\
        ~(poly_eval integer_ring q (&(M * t)) = --c)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\t. &(M * t):int`;
                   `{x | poly_eval integer_ring q x = c} UNION
                    {x | poly_eval integer_ring q x = --c}`]
      FINITE_IMAGE_INJ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_UNION; INTEGER_POLY_FIBRE_FINITE] THEN
      REWRITE_TAC[INT_OF_NUM_EQ; EQ_MULT_LCANCEL] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`(:num)`;
      `{t | poly_eval integer_ring q (&(M * t)) = c \/
            poly_eval integer_ring q (&(M * t)) = --c}`]
     INFINITE_DIFF_FINITE) THEN
    ASM_REWRITE_TAC[num_INFINITE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_UNIV; IN_ELIM_THM;
                DE_MORGAN_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:(1->num)->int`; `&(M * t):int`; `&(M * t):int`; `&0:int`]
    INTEGER_POLY_CONGRUENCE) THEN
  ASM_REWRITE_TAC[INT_SUB_RZERO; INT_DIVIDES_REFL] THEN
  REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `u:int`) THEN
  SUBGOAL_THEN
   `poly_eval integer_ring q (&(M * t)) =
    c * (&1 + (if &0 <= c then &1 else -- &1) * &P * &t * u)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `poly_eval integer_ring q (&(M * t)) - c = &(M * t) * u` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
    UNDISCH_TAC `&M:int = abs c * &P` THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_ABS] THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  ABBREV_TAC
   `z:int = &1 + (if &0 <= (c:int) then &1 else -- &1) * &P * &t * u` THEN
  MP_TAC(SPEC `z:int` INT_PRIME_FACTOR) THEN ANTS_TAC THENL
   [REWRITE_TAC[INT_ARITH `abs(z:int) = &1 <=> z = &1 \/ z = -- &1`] THEN
    STRIP_TAC THEN UNDISCH_TAC
     `poly_eval integer_ring q (&(M * t)) = c * z` THEN
    ASM_REWRITE_TAC[INT_MUL_RID; INT_MUL_RNEG];
    DISCH_THEN(X_CHOOSE_THEN `r:int` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `num_of_int(abs r) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM INT_PRIME] THEN
      SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_PRIME_ABS] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `M * t:num` THEN
      SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_DIVIDES_LABS] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_DIVIDES_LMUL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `num_of_int(abs r)`) THEN
  ASM_REWRITE_TAC[num_divides] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_DIVIDES_LABS] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(r:int) divides &1` MP_TAC THENL
   [SUBGOAL_THEN
     `&1:int = z - ((if &0 <= (c:int) then &1 else -- &1) * &t * u) * &P`
    SUBST1_TAC THENL
     [EXPAND_TAC "z" THEN CONV_TAC INT_RING; ALL_TAC] THEN
    MATCH_MP_TAC INT_DIVIDES_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_DIVIDES_LMUL THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INT_DIVIDES_ONE] THEN
    STRIP_TAC THEN UNDISCH_TAC `int_prime r` THEN
    ASM_REWRITE_TAC[INT_PRIME_NEG; INT_PRIME_1]]);;

(* ------------------------------------------------------------------------- *)
(* Galois extensions of Q: the polynomial of the conjugates of an integral   *)
(* primitive element, totally split primes through the decomposition group.  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_GALOIS_CONJUGATES_POLY = prove
 (`!l:B ring a.
        number_field l /\
        galois_extension(subfield_generated l {ring_0 l},l) I /\
        a IN ring_carrier(ring_of_integers l) /\
        subring_generated l
          (a INSERT ring_carrier(subfield_generated l {ring_0 l})) = l
        ==> ?q. q IN ring_carrier(poly_ring integer_ring (:1)) /\
                poly_deg integer_ring q =
                extension_degree(subfield_generated l {ring_0 l},l) I /\
                !n. ring_of_int l (poly_eval integer_ring q n) =
                    ring_product l
                      (group_carrier
                        (galois_group(subfield_generated l {ring_0 l},l) I))
                      (\f. ring_sub l (ring_of_int l n) (f a))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Q = subfield_generated l {ring_0(l:B ring)}` THEN
  ABBREV_TAC `G = group_carrier(galois_group(Q,l) (I:B->B))` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `finite_extension(Q,l) (I:B->B) /\ field Q /\
                ring_homomorphism(Q,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED;
      RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
    ASM_MESON_TAC[number_field];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `a:B`]
    RING_OF_INTEGERS_INTEGER_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:(1->num)->int` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_deg integer_ring (q:(1->num)->int) = extension_degree(Q,l) (I:B->B)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`I:B->B`; `Q:B ring`; `l:B ring`; `a:B`]
      EXTENSION_DEGREE_SIMPLE) THEN
    ASM_REWRITE_TAC[IMAGE_I] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[finite_extension; field_extension;
                      FINITE_IMP_FIELD_EXTENSION];
        MP_TAC(ISPECL [`I:B->B`; `Q:B ring`; `l:B ring`]
          FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
        ASM_SIMP_TAC[algebraic_extension]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(G:(B->B)->bool) /\ CARD G = extension_degree(Q,l) (I:B->B)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN ASM_SIMP_TAC[FINITE_GALOIS_GROUP] THEN
    ASM_MESON_TAC[GALOIS_EXTENSION_EQ_CARD];
    ALL_TAC] THEN
  ABBREV_TAC `qq = (ring_of_int l:int->B) o (q:(1->num)->int)` THEN
  SUBGOAL_THEN
   `qq IN ring_carrier(poly_ring (l:B ring) (:1)) /\ monic l qq /\
    poly_deg l qq = poly_deg integer_ring (q:(1->num)->int)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "qq" THEN
    MP_TAC(ISPECL [`integer_ring`; `l:B ring`; `ring_of_int l:int->B`;
                   `q:(1->num)->int`] MONIC_HOMOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
                   FIELD_IMP_NONTRIVIAL_RING];
      SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC)] THEN
    MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `integer_ring` THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. poly_eval (l:B ring) qq x =
        poly_extend (integer_ring,l) (ring_of_int l) (\v:1. x)
                    (q:(1->num)->int)`
  ASSUME_TAC THENL
   [EXPAND_TAC "qq" THEN
    SIMP_TAC[poly_eval; POLY_EXTEND_EVALUATE;
             RING_HOMOMORPHISM_INTEGER_RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `qq = ring_product (poly_ring (l:B ring) (:1)) G
          (\f. poly_sub l (poly_var l one) (poly_const l ((f:B->B) a)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MONIC_POLY_EQ_ROOTS_PRODUCT THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
      SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
       [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
      MP_TAC(ISPECL [`integer_ring`; `l:B ring`; `l:B ring`;
                     `ring_of_int l:int->B`; `(:1)`; `\v:1. (a:B)`;
                     `f:B->B`; `q:(1->num)->int`]
        POLY_EXTEND_HOMOMORPHIC_IMAGE) THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(f:B->B) o ring_of_int (l:B ring) = ring_of_int l /\
                    (f:B->B) o (\v:1. a) = (\v. f a)`
      (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
        ASM_MESON_TAC[RING_HOMOMORPHISM_RING_OF_INT];
        ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_0];
      MAP_EVERY X_GEN_TAC [`f:B->B`; `g:B->B`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`I:B->B`; `f:B->B`; `g:B->B`; `Q:B ring`; `l:B ring`;
                     `{a:B}`] GALOIS_GROUP_EQ_ON_GENERATORS) THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_SING] THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      REWRITE_TAC[SUBFIELD_GENERATED_EQ; IMAGE_I] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET]; ALL_TAC] THEN
      FIRST_ASSUM((fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o check (fun th ->
          is_eq(concl th) && rand(concl th) = `l:B ring`)) THEN
      SUBGOAL_THEN `ring_carrier Q UNION {a:B} = a INSERT ring_carrier Q`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED]];
    ALL_TAC] THEN
  X_GEN_TAC `n:int` THEN
  MP_TAC(ISPECL [`integer_ring`; `l:B ring`; `n:int`; `ring_of_int l:int->B`;
                 `q:(1->num)->int`] POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING;
                  IN_UNIV] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!f. f IN G ==> (f:B->B) a IN ring_carrier l`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_IN_CARRIER THEN EXISTS_TAC `l:B ring` THEN
    ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_RING_PRODUCT o lhand o snd)
    THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INT] THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    MATCH_MP_TAC POLY_X_MINUS_A_IN_CARRIER THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC RING_PRODUCT_EQ THEN X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_SUB o lhand o snd) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[POLY_EVAL_VAR; POLY_EVAL_CONST; RING_OF_INT]);;

let NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT = prove
 (`!l:B ring p P.
        number_field l /\
        galois_extension(subfield_generated l {ring_0 l},l) I /\
        prime p /\ prime_ideal (ring_of_integers l) P /\ ring_of_num l p IN P
        ==> (totally_split (integer_ring,ring_of_integers l) (ring_of_int l)
              (ideal_generated integer_ring {&p}) <=>
             group_carrier
              (decomposition_group(subfield_generated l {ring_0 l},l) I P) =
             {I})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`l:B ring`; `p:num`] SPLITTING_TYPES_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2) THEN
  MP_TAC(ISPECL [`l:B ring`; `p:num`]
    RING_OF_INTEGERS_PRIME_SUBFIELD_IDEAL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Q = subfield_generated l {ring_0(l:B ring)}` THEN
  ABBREV_TAC
   `p0 = ideal_generated (ring_of_integers Q) {ring_of_num (l:B ring) p}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `P:B->bool`))) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `Q:B ring`; `l:B ring`; `p0:B->bool`; `P:B->bool`]
    NUMBER_FIELD_GALOIS_SPLITTING_TYPES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; CONJUNCT2 SUBFIELD_GENERATED;
      RING_HOMOMORPHISM_SUBFIELD_INCLUSION];
    SIMP_TAC[]]);;

let NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE = prove
 (`!l:B ring Y.
        number_field l /\ FINITE Y /\
        Y SUBSET ring_carrier(ring_of_integers l) /\ ~(ring_0 l IN Y)
        ==> FINITE {p | prime p /\
                        ?P y. prime_ideal (ring_of_integers l) P /\
                              ring_of_num l p IN P /\ y IN Y /\ y IN P}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\P. ring_char(quotient_ring (ring_of_integers l) P))
          (UNIONS {{P | prime_ideal (ring_of_integers l) P /\
                        ~(P = {ring_0(ring_of_integers l)}) /\
                        ideal_generated (ring_of_integers l) {y} SUBSET P} |
                   (y:B) IN Y})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_UNIONS] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `ideal_generated (ring_of_integers l) {y:B}`]
      DEDEKIND_IDEAL_FACTORIZATION) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED] THEN
    DISCH_THEN(MP_TAC o AP_TERM `(IN) (y:B)`) THEN
    REWRITE_TAC[IN_SING; RING_OF_INTEGERS] THEN
    MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p <=> q)`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MATCH_MP_TAC IDEAL_GENERATED_INC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_UNIONS; EXISTS_IN_GSPEC] THEN
  X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `P:B->bool` (X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `P:B->bool` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P:B->bool`; `p:num`]
      RING_OF_NUM_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    EXISTS_TAC `y:B` THEN ASM_REWRITE_TAC[IN_ELIM_THM; RING_OF_INTEGERS] THEN
    CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[];
      MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; SING_SUBSET]]]);;

let NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE = prove
 (`!l:B ring.
        number_field l /\
        galois_extension(subfield_generated l {ring_0 l},l) I
        ==> INFINITE {p | prime p /\
                          totally_split (integer_ring,ring_of_integers l)
                            (ring_of_int l) (ideal_generated integer_ring
                              {&p})}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  ABBREV_TAC `Q = subfield_generated l {ring_0(l:B ring)}` THEN
  ABBREV_TAC `G = group_carrier(galois_group(Q,l) (I:B->B))` THEN
  SUBGOAL_THEN `field Q /\ ring_homomorphism(Q,l) (I:B->B) /\
                finite_extension(Q,l) (I:B->B) /\ FINITE(G:(B->B)->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED;
      RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[number_field];
      EXPAND_TAC "G" THEN EXPAND_TAC "Q" THEN SIMP_TAC[FINITE_GALOIS_GROUP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Q:B ring`; `l:B ring`; `I:B->B`]
    NUMBER_FIELD_INTEGRAL_PRIMITIVE_ELEMENT) THEN
  ASM_REWRITE_TAC[IMAGE_I] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `a:B`] NUMBER_FIELD_GALOIS_CONJUGATES_POLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `q:(1->num)->int` INTEGER_POLY_PRIME_DIVISORS_INFINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `l:B ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN G ==> ring_homomorphism(l,l) (f:B->B) /\
                   (f a) IN ring_carrier(ring_of_integers l) /\
                   (!n. f(ring_of_int l n) = ring_of_int l n)`
  (LABEL_TAC "Gprops") THENL
   [X_GEN_TAC `f:B->B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_homomorphism(l,l) (f:B->B)` ASSUME_TAC THENL
     [ASM_MESON_TAC[GALOIS_GROUP_RING_HOMOMORPHISM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `f:B->B`]
        RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
      ASM_REWRITE_TAC[ring_homomorphism] THEN ASM SET_TAC[];
      ASM_MESON_TAC[RING_HOMOMORPHISM_RING_OF_INT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. f IN G /\ (f:B->B) a = a ==> f = I`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`I:B->B`; `f:B->B`; `I:B->B`; `Q:B ring`; `l:B ring`;
                   `{a:B}`] GALOIS_GROUP_EQ_ON_GENERATORS) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_SING; I_THM; GALOIS_GROUP_I] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[SUBFIELD_GENERATED_EQ; IMAGE_I] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET] THEN
    FIRST_ASSUM((fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o check (fun th ->
        is_eq(concl th) && rand(concl th) = `l:B ring`)) THEN
    SUBGOAL_THEN `ring_carrier Q UNION {a:B} = a INSERT ring_carrier Q`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  ABBREV_TAC
   `E = {p | prime p /\
             ?P y. prime_ideal (ring_of_integers l) P /\
                   ring_of_num l p IN P /\
                   y IN {ring_sub l ((f:B->B) a) a | f | f IN G /\ ~(f = I)} /\
                   y IN P}` THEN
  SUBGOAL_THEN `FINITE(E:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN
    MATCH_MP_TAC NUMBER_FIELD_RATIONAL_PRIMES_CONTAINING_FINITE THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SET_RULE
       `{(g:(B->B)->B) x | x | x IN s /\ P x} = IMAGE g {x | x IN s /\ P x}`]
      THEN
      MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`ring_of_integers l:B ring`; `(f:B->B) a`; `a:B`]
        RING_SUB) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS];
      REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `f:B->B` THEN STRIP_TAC THEN
      UNDISCH_TAC `~(f:B->B = I)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`l:B ring`; `(f:B->B) a`; `a:B`] RING_SUB_EQ_0) THEN
      ASM_SIMP_TAC[RING_HOMOMORPHISM_IN_CARRIER] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC
   `{p | prime p /\ ?n. &p divides poly_eval integer_ring q (&n)} DIFF E` THEN
  ASM_SIMP_TAC[INFINITE_DIFF_FINITE] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `n:num`)) ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`l:B ring`; `p:num`] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P0:B->bool` STRIP_ASSUME_TAC o CONJUNCT1 o
    CONJUNCT2) THEN
  SUBGOAL_THEN
   `!g. g IN G
        ==> ring_sub l (ring_of_int l (&n)) ((g:B->B) a) IN
            ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `ring_of_int l (&n):B`;
                   `(g:B->B) a`] RING_SUB) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?f. f IN G /\ ring_sub l (ring_of_int l (&n)) ((f:B->B) a) IN P0`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P0:B->bool`;
                   `G:(B->B)->bool`;
                   `\f. ring_sub l (ring_of_int l (&n)) ((f:B->B) a)`]
      RING_PRODUCT_IN_PRIME_IDEAL) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `ring_product (ring_of_integers l) G
        (\f. ring_sub l (ring_of_int l (&n)) ((f:B->B) a)) =
      ring_product l G (\f. ring_sub l (ring_of_int l (&n)) (f a))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [GSYM(CONJUNCT2 RING_OF_INTEGERS_SUBRING)] THEN
      REWRITE_TAC[RING_PRODUCT_SUBRING_GENERATED_GEN;
                  CONJUNCT2 RING_OF_INTEGERS_SUBRING] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[GSYM th]) o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "poly_eval")) (concl th))) THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P0:B->bool`; `p:num`]
      RING_OF_INT_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES o check (fun th ->
    concl th = `(f:B->B) IN group_carrier(galois_group(Q,l) I)`) o
    REWRITE_RULE[SYM(ASSUME `group_carrier(galois_group(Q,l) (I:B->B)) = G`)]
    o check (fun th -> concl th = `(f:B->B) IN G`)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  SUBGOAL_THEN `inverse(f:B->B) IN G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC GALOIS_GROUP_INVERSE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `P = IMAGE (inverse(f:B->B)) P0` THEN
  SUBGOAL_THEN
   `prime_ideal (ring_of_integers l) P /\ ring_of_num l p IN P /\
    ring_sub l (ring_of_int l (&n)) (a:B) IN P`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`I:B->B`; `Q:B ring`; `l:B ring`;
                   `ring_of_integers l:B ring`; `inverse(f:B->B)`;
                   `P0:B->bool`] GALOIS_GROUP_PRIME_IDEAL_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[RING_OF_INTEGERS_SUBRING; GALOIS_GROUP_RING_OF_INTEGERS] THEN
      ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET] THEN
      UNDISCH_TAC `inverse(f:B->B) IN G` THEN EXPAND_TAC "G" THEN SIMP_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "P" THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "Gprops" (MP_TAC o SPEC `inverse(f:B->B)`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `ring_of_num l p:B` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN
      MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `inverse(f:B->B)`]
        RING_HOMOMORPHISM_RING_OF_NUM) THEN ASM_SIMP_TAC[];
      EXISTS_TAC `ring_sub l (ring_of_int l (&n)) ((f:B->B) a)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f:B->B) a IN ring_carrier l` ASSUME_TAC THENL
       [MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "Gprops" (MP_TAC o SPEC `f:B->B`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `inverse(f:B->B)`]
        RING_HOMOMORPHISM_SUB) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`ring_of_int l (&n):B`; `(f:B->B) a`]) THEN
      ASM_REWRITE_TAC[RING_OF_INT] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `p:num`; `P:B->bool`]
    NUMBER_FIELD_GALOIS_RATIONAL_TOTALLY_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(a:B->B) IN s /\ (!x. x IN s ==> x = a) ==> s = {a}`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `decomposition_group(Q,l) (I:B->B) P` GROUP_ID) THEN
    REWRITE_TAC[DECOMPOSITION_GROUP];
    ALL_TAC] THEN
  REWRITE_TAC[DECOMPOSITION_GROUP; IN_ELIM_THM] THEN
  X_GEN_TAC `g:B->B` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:B->B) IN G` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~((p:num) IN E)` THEN REWRITE_TAC[] THEN EXPAND_TAC "E" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`P:B->bool`; `ring_sub l ((g:B->B) a) a`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `g:B->B` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "Gprops" (MP_TAC o SPEC `g:B->B`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `(g:B->B) a IN ring_carrier l` ASSUME_TAC THENL
   [MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_sub l (ring_of_int l (&n)) ((g:B->B) a) IN P`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `ring_sub l (ring_of_int l (&n)) ((g:B->B) a) =
      g (ring_sub l (ring_of_int l (&n)) a)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`l:B ring`; `l:B ring`; `g:B->B`]
        RING_HOMOMORPHISM_SUB) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`ring_of_int l (&n):B`; `a:B`]) THEN
      ASM_REWRITE_TAC[RING_OF_INT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REFL_TAC;
      UNDISCH_TAC `IMAGE (g:B->B) P = P` THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P:B->bool`;
                 `ring_sub l (ring_of_int l (&n)) (a:B)`;
                 `ring_sub l (ring_of_int l (&n)) ((g:B->B) a)`]
    IN_RING_IDEAL_SUB) THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(RING_RULE
   `ring_sub r (ring_sub r n x) (ring_sub r n y) = ring_sub r y (x:B)`) THEN
  ASM_REWRITE_TAC[RING_OF_INT]);;

(* ------------------------------------------------------------------------- *)
(* Any number field: a Galois closure over Q, descent of total splitting,    *)
(* infinitely many totally split primes and primes of degree one.            *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_GALOIS_CLOSURE_Q = prove
 (`!l:B ring.
        number_field l
        ==> ?(m:(B#num)ring) j.
                number_field m /\ ring_homomorphism(l,m) j /\
                galois_extension(subfield_generated m {ring_0 m},m) I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_char(l:B ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  ABBREV_TAC `Q = subfield_generated l {ring_0(l:B ring)}` THEN
  SUBGOAL_THEN
   `field Q /\ ring_homomorphism(Q,l) (I:B->B) /\
    finite_extension(Q,l) (I:B->B) /\ number_field Q /\
    subfield_generated Q {ring_0 Q} = Q`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
                 NUMBER_FIELD_PRIME_SUBFIELD;
                   PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC[number_field];
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` ALGEBRAIC_CLOSURE_EXISTS_BIGENOUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(B#num)ring`
    (X_CHOOSE_THEN `f:B->B#num` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `field(c:(B#num)ring) /\ ring_monomorphism(l,c) (f:B->B#num) /\
    ring_homomorphism(l,c) f`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[algebraic_extension; field_extension;
                  RING_MONOMORPHISM_IMP_HOMOMORPHISM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:B->B`; `f:B->B#num`; `Q:B ring`; `l:B ring`;
                 `c:(B#num)ring`] FINITE_EXTENSION_NORMAL_CLOSURE) THEN
  ASM_REWRITE_TAC[I_O_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(B#num)->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `N = subfield_generated c (IMAGE (f:B->B#num) (ring_carrier Q) UNION s)` THEN
  EXISTS_TAC `N:(B#num)ring` THEN EXISTS_TAC `f:B->B#num` THEN
  SUBGOAL_THEN `IMAGE (f:B->B#num) (ring_carrier l) SUBSET ring_carrier N`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `f:B->B#num` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "SUBSET")) (concl th))) THEN
    ASM_REWRITE_TAC[I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(l,N) (f:B->B#num)` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_INTO_SUBRING THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "N" THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `field(N:(B#num)ring) /\ ring_char N = 0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_CHAR_SUBFIELD_GENERATED] THEN
    MP_TAC(ISPECL [`f:B->B#num`; `l:B ring`; `c:(B#num)ring`]
      PRIME_SUBFIELD_TOWER_LAW) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(Q,N) ((f:B->B#num) o I)` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `l:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `number_field(N:(B#num)ring)` ASSUME_TAC THENL
   [REWRITE_TAC[number_field] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(f:B->B#num) o I`; `Q:B ring`; `N:(B#num)ring`]
      PRIME_SUBFIELD_TOWER_LAW) THEN
    ASM_REWRITE_TAC[I_O_ID] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ASM_MESON_TAC[number_field];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ring_homomorphism(Q,N) (f:B->B#num)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      concl th = `ring_homomorphism(Q,N) ((f:B->B#num) o I)`)) THEN
    REWRITE_TAC[I_O_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_char(Q:B ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  SUBGOAL_THEN `galois_extension(Q,N) (f:B->B#num)` ASSUME_TAC THENL
   [REWRITE_TAC[galois_extension] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PERFECT_FIELD_IMP_SEPARABLE_EXTENSION THEN
    ASM_SIMP_TAC[PERFECT_FIELD_CHAR_0; FINITE_IMP_ALGEBRAIC_EXTENSION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:B->B#num) (ring_carrier Q) =
    IMAGE I (ring_carrier(subfield_generated N {ring_0 N}))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_I] THEN
    MP_TAC(ISPECL [`Q:B ring`; `N:(B#num)ring`; `f:B->B#num`]
      PRIME_SUBFIELD_MONOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FIELD_RING_HOMOMORPHISM_MONOMORPHISM THEN
    ASM_SIMP_TAC[FIELD_IMP_NONTRIVIAL_RING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`I:(B#num)->(B#num)`;
                 `subfield_generated N {ring_0(N:(B#num)ring)}`;
                 `N:(B#num)ring`] GALOIS_EXTENSION_EQ_CARD) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[number_field]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`f:B->B#num`; `Q:B ring`; `N:(B#num)ring`]
    GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:B->B#num`; `I:(B#num)->(B#num)`; `Q:B ring`;
                 `subfield_generated N {ring_0(N:(B#num)ring)}`;
                 `N:(B#num)ring`] GALOIS_GROUP_EQ_IMAGE) THEN
  MP_TAC(ISPECL [`f:B->B#num`; `I:(B#num)->(B#num)`; `Q:B ring`;
                 `subfield_generated N {ring_0(N:(B#num)ring)}`;
                 `N:(B#num)ring`] EXTENSION_DEGREE_EQ_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[]);;

(* An extension l of k embeds into a number field m Galois over k: a Galois  *)
(* closure of l over the rationals (NUMBER_FIELD_GALOIS_CLOSURE_Q) is Galois *)
(* over the image of the prime subfield of k, hence over k.                  *)
let NUMBER_FIELD_GALOIS_CLOSURE = prove
 (`!k:A ring l:B ring h.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> ?(m:(B#num)ring) j.
                number_field m /\ ring_homomorphism(l,m) j /\
                galois_extension(k,m) (j o h)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_GALOIS_CLOSURE_Q) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:(B#num)ring` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:B->B#num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = (j:B->B#num) o (h:A->B)` THEN
  SUBGOAL_THEN `ring_homomorphism(k:A ring,m:(B#num)ring) g` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `m:(B#num)ring`; `g:A->B#num`]
    NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  MP_TAC(ISPECL [`I:A->A`; `g:A->B#num`;
                 `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `m:(B#num)ring`] GALOIS_EXTENSION_INTERMEDIATE) THEN
  ASM_REWRITE_TAC[I_O_ID; FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (g:A->B#num) (ring_carrier(subfield_generated k {ring_0 k})) =
    IMAGE I (ring_carrier(subfield_generated m {ring_0 m}))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_I] THEN MATCH_MP_TAC PRIME_SUBFIELD_MONOMORPHIC_IMAGE THEN
    ASM_MESON_TAC[field_extension];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `field_extension(subfield_generated k {ring_0 k},m:(B#num)ring)
      (g:A->B#num) /\
    finite_extension(subfield_generated m {ring_0 m},m:(B#num)ring) I`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_EXTENSION_FROM_SUBFIELD_GENERATED] THEN
    ASM_MESON_TAC[number_field];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `finite_extension(subfield_generated k {ring_0 k},m:(B#num)ring)
      (g:A->B#num)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:A->B#num`; `I:B#num->B#num`;
                   `subfield_generated k {ring_0 k:A}`;
                   `subfield_generated m {ring_0 m:B#num}`; `m:(B#num)ring`]
      FINITE_EXTENSION_EQ_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[finite_extension];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:A->B#num`; `subfield_generated k {ring_0 k:A}`;
                 `m:(B#num)ring`] GALOIS_EXTENSION_EQ_CARD) THEN
  MP_TAC(ISPECL [`I:B#num->B#num`; `subfield_generated m {ring_0 m:B#num}`;
                 `m:(B#num)ring`] GALOIS_EXTENSION_EQ_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g:A->B#num`; `I:B#num->B#num`;
                 `subfield_generated k {ring_0 k:A}`;
                 `subfield_generated m {ring_0 m:B#num}`; `m:(B#num)ring`]
    GALOIS_GROUP_EQ_IMAGE) THEN
  MP_TAC(ISPECL [`g:A->B#num`; `I:B#num->B#num`;
                 `subfield_generated k {ring_0 k:A}`;
                 `subfield_generated m {ring_0 m:B#num}`; `m:(B#num)ring`]
    EXTENSION_DEGREE_EQ_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[]);;

let NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE = prove
 (`!(j:B->C) l m p.
        field l /\ number_field m /\ ring_homomorphism(l,m) j /\ prime p /\
        totally_split (integer_ring,ring_of_integers m) (ring_of_int m)
          (ideal_generated integer_ring {&p})
        ==> totally_split (integer_ring,ring_of_integers l) (ring_of_int l)
              (ideal_generated integer_ring {&p})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC
   `totally_split (integer_ring,ring_of_integers (m:C ring)) (ring_of_int m)
      (ideal_generated integer_ring {&p:int}) :bool` THEN
  ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
    (ISPEC `ring_of_integers m:C ring` SPLITTING_TYPES_INTEGER_RING);
               REWRITE_RULE[RING_OF_INTEGERS]
    (ISPEC `ring_of_integers l:B ring` SPLITTING_TYPES_INTEGER_RING)] THEN
  DISCH_TAC THEN X_GEN_TAC `P:B->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `number_field(l:B ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NUMBER_FIELD_HOMOMORPHIC_PREIMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(P = {ring_0(l:B ring)})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_of_num l p IN {ring_0(l:B ring)}` THEN
    REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field] o
      check (fun th -> concl th = `number_field(l:B ring)`)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIVIDES_ZERO] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`; `P:B->bool`]
    NUMBER_FIELD_PRIME_IDEALS_ABOVE) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P':C->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P':C->bool`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_of_num m p = (j:B->C)(ring_of_num l p)` SUBST1_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_RING_OF_NUM]; ASM SET_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`; `P:B->bool`; `P':C->bool`]
    NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `j:B->C`; `P:B->bool`; `P':C->bool`]
    NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 = n <=> n = 1`; MULT_EQ_1] THEN SIMP_TAC[]);;

let NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q = prove
 (`!l:B ring.
        number_field l
        ==> INFINITE {p | prime p /\
                          totally_split (integer_ring,ring_of_integers l)
                            (ring_of_int l) (ideal_generated integer_ring
                              {&p})}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `l:B ring` NUMBER_FIELD_GALOIS_CLOSURE_Q) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(B#num)ring`
    (X_CHOOSE_THEN `j:B->B#num` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `m:(B#num)ring` NUMBER_FIELD_GALOIS_TOTALLY_SPLIT_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INFINITE_SUPERSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`j:B->B#num`; `l:B ring`; `m:(B#num)ring`; `p:num`]
    NUMBER_FIELD_TOTALLY_SPLIT_HOMOMORPHIC_PREIMAGE) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD]);;

let NUMBER_FIELD_TOTALLY_SPLIT_INFINITE = prove
 (`!(h:A->B) k l.
        field k /\ number_field l /\ ring_homomorphism(k,l) h
        ==> INFINITE {p | prime_ideal (ring_of_integers k) p /\
                          ~(p = {ring_0 k}) /\
                          totally_split (ring_of_integers k,ring_of_integers l)
                            h p}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `number_field(k:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NUMBER_FIELD_HOMOMORPHIC_PREIMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_char(k:A ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `S = {q | prime q /\
             totally_split (integer_ring,ring_of_integers (l:B ring))
               (ring_of_int l) (ideal_generated integer_ring {&q})}` THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `pp = \q. @p. prime_ideal (ring_of_integers k) p /\
                 ring_of_num (k:A ring) q IN p` THEN
  SUBGOAL_THEN
   `!q. q IN S
        ==> prime q /\
            totally_split (integer_ring,ring_of_integers (l:B ring))
              (ring_of_int l) (ideal_generated integer_ring {&q}) /\
            prime_ideal (ring_of_integers k) (pp q) /\
            ring_of_num (k:A ring) q IN pp q`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "pp" THEN
    CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL [`k:A ring`; `q:num`] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `IMAGE (pp:num->A->bool) S` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFINITE_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`q1:num`; `q2:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `(pp:num->A->bool) q2`]
      RING_OF_NUM_IN_PRIME_IDEAL) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `q1:num` th) THEN
                         MP_TAC(SPEC `q2:num` th)) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(pp:num->A->bool) q1 = pp q2`)) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `p = (pp:num->A->bool) q` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t ->
    is_const t && fst(dest_const t) = "totally_split")) (concl th))) THEN
  ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
    (ISPEC `ring_of_integers l:B ring` SPLITTING_TYPES_INTEGER_RING)] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(p = {ring_0(k:A ring)})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `ring_of_num k q IN {ring_0(k:A ring)}` THEN
    ASM_REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN
    ASM_MESON_TAC[PRIME_0];
    ASM_REWRITE_TAC[totally_split]] THEN
  X_GEN_TAC `P:B->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:B->bool`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_of_num l q = (h:A->B)(ring_of_num k q)` SUBST1_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_RING_OF_NUM]; ASM SET_TAC[]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    NUMBER_FIELD_RAMIFICATION_INDEX_TOWER_Q) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    NUMBER_FIELD_RESIDUE_DEGREE_TOWER_Q) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 = n <=> n = 1`; MULT_EQ_1] THEN SIMP_TAC[]);;

let NUMBER_FIELD_DEGREE_ONE_PRIMES_INFINITE = prove
 (`!l:B ring.
        number_field l
        ==> INFINITE {P | prime_ideal (ring_of_integers l) P /\
                          ~(P = {ring_0 l}) /\
                          residue_degree (integer_ring,ring_of_integers l)
                            (ring_of_int l) P = 1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_char(l:B ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  MP_TAC(ISPEC `l:B ring` NUMBER_FIELD_TOTALLY_SPLIT_INFINITE_Q) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `S = {q | prime q /\
             totally_split (integer_ring,ring_of_integers (l:B ring))
               (ring_of_int l) (ideal_generated integer_ring {&q})}` THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `pp = \q. @P. prime_ideal (ring_of_integers l) P /\
                 ring_of_num (l:B ring) q IN P` THEN
  SUBGOAL_THEN
   `!q. q IN S
        ==> prime q /\
            (!P. prime_ideal (ring_of_integers l) P /\
                 ring_of_num l q IN P
                 ==> ramification_index (integer_ring,ring_of_integers l)
                       (ring_of_int l) P = 1 /\
                     residue_degree (integer_ring,ring_of_integers l)
                       (ring_of_int l) P = 1) /\
            prime_ideal (ring_of_integers l) (pp q) /\
            ring_of_num (l:B ring) q IN pp q`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `totally_split (integer_ring,ring_of_integers (l:B ring))
        (ring_of_int l) (ideal_generated integer_ring {&q})` THEN
    ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
      (ISPEC `ring_of_integers l:B ring` SPLITTING_TYPES_INTEGER_RING)] THEN
    DISCH_THEN(K ALL_TAC) THEN EXPAND_TAC "pp" THEN
    CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL [`l:B ring`; `q:num`] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `IMAGE (pp:num->B->bool) S` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFINITE_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`q1:num`; `q2:num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `(pp:num->B->bool) q2`]
      RING_OF_NUM_IN_PRIME_IDEAL) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `q1:num` th) THEN
                         MP_TAC(SPEC `q2:num` th)) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `(pp:num->B->bool) q1 = pp q2`)) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `q:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (pp:num->B->bool) q` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `ring_of_num l q IN {ring_0(l:B ring)}` THEN
  ASM_REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN
  ASM_MESON_TAC[PRIME_0]);;
