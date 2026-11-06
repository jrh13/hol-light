(* ========================================================================= *)
(* Ramification index and residue degree of a prime over its contraction,    *)
(* and the splitting of rational primes in a number field k with ring of     *)
(* integers O = ring_of_integers k. For a ring homomorphism h : r -> s and   *)
(* an ideal P of s, with p = {x | x IN r /\ h x IN P} the contraction of P:  *)
(*                                                                           *)
(*   ramification_index (r,s) h P = e(P|p), the exponent of P in the         *)
(*                                  extended ideal p s                       *)
(*   residue_degree (r,s) h P     = f(P|p), the degree of s/P over the image *)
(*                                  of r, that is [s/P : r/p]                *)
(*                                                                           *)
(* The absolute notions over Z are the case of the canonical map h =         *)
(* ring_of_int r from integer_ring: e(P) is the exponent of P in (p), p =    *)
(* char(r/P) (RAMIFICATION_INDEX_INTEGER_RING) and f(P) the degree of r/P    *)
(* over its prime field (RESIDUE_DEGREE_INTEGER_RING). For a ring of         *)
(* integers the map Z -> O is written ring_of_int k (the same function as    *)
(* ring_of_int O, RING_OF_INTEGERS), as for integral bases. The relative     *)
(* theory (number field extensions, towers) is in ANT/relative_split.ml.     *)
(*                                                                           *)
(* Main results: a prime P of any ring contains the prime number p iff r/P   *)
(* has characteristic p (RING_OF_NUM_IN_PRIME_IDEAL), and then P meets the   *)
(* integers in pZ; N(P) = char(r/P)^f for a prime ideal of finite index      *)
(* (IDEAL_NORM_RESIDUE_DEGREE_Q); a nonzero prime of O lies over exactly one *)
(* rational prime p, O/P is a finite field with p^f elements, so f = 1 iff   *)
(* N(P) is prime (NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE); pO is the product of *)
(* the powers P^e(P) of the primes above p (and conversely e is read off     *)
(* from any such factorization), sum e(P) f(P) = [k:Q] (the fundamental      *)
(* identity), hence finitely many (at least one, at most [k:Q]) primes lie   *)
(* over p. For an indexed family of distinct primes P_i above p with         *)
(* exponents e_i: a factorization pO = prod P_i^e_i consists of all the      *)
(* primes above p with e_i = e(P_i)                                          *)
(* (NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE), N(prod P_i^e_i) = p^(sum *)
(* f(P_i) e_i) (NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT), and a product prod   *)
(* P_i^e_i inside pO with sum e_i f(P_i) = [k:Q] is the factorization of pO  *)
(* (NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ); if pO is prime, pO = P Q    *)
(* for primes P, Q forces P = Q (NUMBER_FIELD_PRIME_IDEAL_PROD_EQ).          *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml (extension_degree,    *)
(* CARD_EXTENSION_DEGREE, PRIME_SUBFIELD_EQ_SUBRING), Library/products.ml    *)
(* (EXP_NSUM, NPRODUCT_EQ), ANT/ideal_arith.ml, ANT/dedekind.ml              *)
(* (ideal_valuation, factorization,                                          *)
(* DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE), ANT/ideal_norm.ml,              *)
(* ANT/numfield.ml, ANT/ring_of_integers.ml.                                 *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/products.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;

(* ------------------------------------------------------------------------- *)
(* Ramification index and residue degree of a prime ideal.                   *)
(* ------------------------------------------------------------------------- *)

let ramification_index = new_definition
 `ramification_index (r:A ring,s:B ring) (h:A->B) (P:B->bool) =
  ideal_valuation s P
   (ideal_generated s (IMAGE h {x | x IN ring_carrier r /\ h x IN P}))`;;

let residue_degree = new_definition
 `residue_degree (r:A ring,s:B ring) (h:A->B) (P:B->bool) =
  extension_degree
   (subring_generated (quotient_ring s P)
                      (IMAGE (ring_coset s P o h) (ring_carrier r)),
    quotient_ring s P) I`;;

(* The case of the map from the integers: the exponent of P in (p) with p =  *)
(* char(r/P), and the degree of r/P over its prime field.                    *)

let RAMIFICATION_INDEX_INTEGER_RING = prove
 (`!r:A ring P.
        ring_ideal r P
        ==> ramification_index (integer_ring,r) (ring_of_int r) P =
            ideal_valuation r P
             (ideal_generated r
                {ring_of_num r (ring_char(quotient_ring r P))})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ramification_index] THEN
  AP_TERM_TAC THEN
  ABBREV_TAC `c = ring_char(quotient_ring r (P:A->bool))` THEN
  SUBGOAL_THEN `!x. ring_of_int r x IN (P:A->bool) <=> &c divides x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:int` THEN
    MP_TAC(ISPECL [`r:A ring`; `quotient_ring r (P:A->bool)`;
                   `ring_coset r (P:A->bool)`]
      RING_HOMOMORPHISM_RING_OF_INT) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET] THEN
    DISCH_THEN(MP_TAC o SPEC `x:int`) THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `ring_of_int r x:A`]
      RING_COSET_EQ_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`] QUOTIENT_RING_0) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) THEN
    EXPAND_TAC "c" THEN REWRITE_TAC[RING_OF_INT_EQ_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
    REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; SUBSET; FORALL_IN_IMAGE;
                IN_ELIM_THM; int_divides] THEN
    X_GEN_TAC `x:int` THEN DISCH_THEN(X_CHOOSE_THEN `t:int` SUBST1_TAC) THEN
    REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN
    MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
    REWRITE_TAC[ring_divides] THEN
    SIMP_TAC[RING_MUL; RING_OF_NUM; RING_OF_INT] THEN
    MESON_TAC[RING_OF_INT];
    MATCH_MP_TAC IDEAL_GENERATED_MONO THEN
    REWRITE_TAC[SING_SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `&c:int` THEN REWRITE_TAC[RING_OF_INT_OF_NUM] THEN
    CONV_TAC INTEGER_RULE]);;

let RESIDUE_DEGREE_INTEGER_RING = prove
 (`!r:A ring P.
        prime_ideal r P /\ ~(ring_char(quotient_ring r P) = 0)
        ==> residue_degree (integer_ring,r) (ring_of_int r) P =
            extension_degree
             (subfield_generated (quotient_ring r P)
                {ring_0(quotient_ring r P)},
              quotient_ring r P) I`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[residue_degree] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUBRING_GENERATED_BY_SUBFIELD_GENERATED] THEN
  AP_TERM_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `prime(ring_char(quotient_ring r (P:A->bool)))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `quotient_ring r (P:A->bool)` INTEGRAL_DOMAIN_CHAR) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_QUOTIENT_RING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRIME_SUBFIELD_EQ_SUBRING] THEN
  MP_TAC(ISPECL [`r:A ring`; `quotient_ring r (P:A->bool)`;
                 `ring_coset r (P:A->bool)`]
    RING_HOMOMORPHISM_RING_OF_INT) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[INTEGER_RING; o_DEF; SIMPLE_IMAGE; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Prime ideals and prime numbers, in any ring.                              *)
(* ------------------------------------------------------------------------- *)

let RING_OF_NUM_IN_PRIME_IDEAL = prove
 (`!r:A ring P p.
        prime_ideal r P /\ prime p
        ==> (ring_of_num r p IN P <=> ring_char(quotient_ring r P) = p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`quotient_ring r (P:A->bool)`; `p:num`]
    RING_CHAR_DIVIDES_PRIME) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_QUOTIENT_RING] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM RING_OF_NUM_EQ_0] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `p:num` o
    MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM o
    MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_NUM]);;

let RING_OF_INT_IN_PRIME_IDEAL = prove
 (`!r:A ring P p.
        prime_ideal r P /\ prime p /\ ring_of_num r p IN P
        ==> !m. ring_of_int r m IN P <=> &p divides m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `ring_char(quotient_ring r (P:A->bool)) = p`
   (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[RING_OF_NUM_IN_PRIME_IDEAL]; ALL_TAC] THEN
  REWRITE_TAC[GSYM RING_OF_INT_EQ_0] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `m:int` o
    MATCH_MP RING_HOMOMORPHISM_RING_OF_INT o
    MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_INT]);;

let RAMIFICATION_INDEX_PRIME = prove
 (`!r:A ring P p.
        prime_ideal r P /\ prime p /\ ring_of_num r p IN P
        ==> ramification_index (integer_ring,r) (ring_of_int r) P =
            ideal_valuation r P (ideal_generated r {ring_of_num r p})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_char(quotient_ring r (P:A->bool)) = p` MP_TAC THENL
   [ASM_MESON_TAC[RING_OF_NUM_IN_PRIME_IDEAL];
    ASM_SIMP_TAC[RAMIFICATION_INDEX_INTEGER_RING; PRIME_IMP_RING_IDEAL]]);;

(* The residue field R = r/P is a finite field of prime characteristic, its  *)
(* prime field has char(R) elements, and |R| = char(R)^f                     *)
(* (CARD_EXTENSION_DEGREE).                                                  *)

let IDEAL_NORM_RESIDUE_DEGREE_Q = prove
 (`!r:A ring P.
        prime_ideal r P /\ FINITE(ring_carrier(quotient_ring r P))
        ==> ideal_norm r P =
            ring_char(quotient_ring r P) EXP
            residue_degree (integer_ring,r) (ring_of_int r) P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `integral_domain(quotient_ring r (P:A->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_DOMAIN_QUOTIENT_RING; PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_char(quotient_ring r (P:A->bool)) = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_INTEGRAL_DOMAIN_CHAR; PRIME_IMP_NZ]; ALL_TAC] THEN
  ASM_SIMP_TAC[RESIDUE_DEGREE_INTEGER_RING; ideal_norm] THEN
  ABBREV_TAC `R = quotient_ring r (P:A->bool)` THEN
  MP_TAC(ISPECL [`I:(A->bool)->(A->bool)`;
                 `subfield_generated R {ring_0 R:A->bool}`; `R:(A->bool)ring`]
    CARD_EXTENSION_DEGREE) THEN
  ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; PRIME_SUBFIELD_EQ_SUBRING;
               CARD_PRIME_SUBRING; PRIME_IMP_NZ; FINITE_INTEGRAL_DOMAIN_CHAR;
               FINITE_INTEGRAL_DOMAIN_IMP_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Prime ideals of a ring of integers: lying over, residue fields.           *)
(* ------------------------------------------------------------------------- *)

let RING_OF_INTEGERS_PRIME_IDEAL_ABOVE = prove
 (`!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> ?!p. prime p /\ ring_of_num k p IN P`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN
   `prime(ring_char(quotient_ring (ring_of_integers k) (P:A->bool)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_QUOTIENT_RING;
                 RING_OF_INTEGERS_FINITE_QUOTIENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
    RING_OF_NUM_IN_PRIME_IDEAL) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN ASM_MESON_TAC[]);;

let RING_OF_INTEGERS_RESIDUE_FIELD = prove
 (`!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> field(quotient_ring (ring_of_integers k) P) /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers k) P))`,
  MESON_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT; PRIME_IMP_RING_IDEAL;
            INTEGRAL_DOMAIN_QUOTIENT_RING; FINITE_INTEGRAL_DOMAIN_IMP_FIELD]);;

let RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q = prove
 (`!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\ prime p /\
        ring_of_num k p IN P
        ==> ideal_norm (ring_of_integers k) P =
            p EXP residue_degree (integer_ring,ring_of_integers k)
                    (ring_of_int k) P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
    RING_OF_NUM_IN_PRIME_IDEAL) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
    IDEAL_NORM_RESIDUE_DEGREE_Q) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
  ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN DISCH_TAC THEN
  UNDISCH_TAC `ring_of_num k p IN (P:A->bool)` THEN
  ASM_REWRITE_TAC[IN_SING; RING_OF_NUM_EQ_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[number_field]) THEN
  ASM_SIMP_TAC[DIVIDES_ZERO; PRIME_IMP_NZ]);;

let NUMBER_FIELD_PRIME_IDEAL_DEGREE_ONE = prove
 (`!k:A ring P.
        number_field k /\ prime_ideal (ring_of_integers k) P /\
        ~(P = {ring_0 k})
        ==> (residue_degree (integer_ring,ring_of_integers k)
               (ring_of_int k) P = 1 <=>
             prime(ideal_norm (ring_of_integers k) P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_ABOVE) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (STRIP_ASSUME_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
    RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[PRIME_EXP]);;

(* ------------------------------------------------------------------------- *)
(* The primes above p: factorization and the fundamental identity.           *)
(* ------------------------------------------------------------------------- *)

(* The ideal pO is nonzero, and its nonzero prime divisors are the primes    *)
(* above p, finitely many.                                                   *)

let RING_OF_INTEGERS_IDEAL_GENERATED_PRIME = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> ~(ideal_generated (ring_of_integers k) {ring_of_num k p} =
              {ring_0 k}) /\
            {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ideal_generated (ring_of_integers k) {ring_of_num k p}
                 SUBSET P} =
            {P | prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P} /\
            FINITE {P | prime_ideal (ring_of_integers k) P /\
                        ring_of_num k p IN P}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ring_of_num k p IN ring_carrier(ring_of_integers k) /\
                ~(ring_of_num k p = ring_0 k:A)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [number_field]) THEN
    ASM_SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO; PRIME_IMP_NZ] THEN
    MESON_TAC[RING_OF_NUM; RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(ideal_generated (ring_of_integers k) {ring_of_num k p} = {ring_0 k:A})`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_IDEAL_GENERATED_SELF; IN_SING]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ q /\ (q ==> r) ==> p /\ q /\ r`) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `P:A->bool` THEN
    ASM_CASES_TAC `prime_ideal (ring_of_integers k) (P:A->bool)` THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ; PRIME_IMP_RING_IDEAL] THEN
    ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`]
      DEDEKIND_IDEAL_FACTORIZATION) THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                 RING_OF_INTEGERS]]);;

let NUMBER_FIELD_PRIME_FACTORIZATION_Q = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k)
              {P | prime_ideal (ring_of_integers k) P /\
                   ring_of_num k p IN P}
              (\P. ideal_pow (ring_of_integers k) P
                     (ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`]
    DEDEKIND_IDEAL_FACTORIZATION) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
               RING_OF_INTEGERS] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
  MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
    RAMIFICATION_INDEX_PRIME) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS]);;

let NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q = prove
 (`!k:A ring p s e.
        number_field k /\ prime p /\ FINITE s /\
        (!P. P IN s ==> prime_ideal (ring_of_integers k) P /\ ~(e P = 0)) /\
        ideal_generated (ring_of_integers k) {ring_of_num k p} =
        ideal_product (ring_of_integers k) s
          (\P. ideal_pow (ring_of_integers k) P (e P))
        ==> s = {P | prime_ideal (ring_of_integers k) P /\
                     ring_of_num k p IN P} /\
            !P. P IN s ==> ramification_index (integer_ring,ring_of_integers k)
                             (ring_of_int k) P = e P`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `s:(A->bool)->bool`;
                 `e:(A->bool)->num`]
    DEDEKIND_IDEAL_PRODUCT_PRIME_POW_UNIQUE) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM o CONJUNCT1)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS];
    REWRITE_TAC[RING_OF_INTEGERS] THEN STRIP_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
    RAMIFICATION_INDEX_PRIME) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ideal_generated (ring_of_integers k) {ring_of_num k p}
               SUBSET (P:A->bool)` THEN
  MATCH_MP_TAC(SET_RULE `(x:A) IN j ==> j SUBSET P ==> x IN P`) THEN
  REWRITE_TAC[IN_IDEAL_GENERATED_SELF] THEN
  MESON_TAC[RING_OF_NUM; RING_OF_INTEGERS]);;

(* p^n = N(pO) = prod N(P)^e(P) = prod p^(e(P) f(P)) = p^(sum e(P) f(P)).   *)

let NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> nsum {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
                 (\P. ramification_index (integer_ring,ring_of_integers k)
                        (ring_of_int k) P *
                      residue_degree (integer_ring,ring_of_integers k)
                        (ring_of_int k) P) =
            extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`]
    IDEAL_NORM_FACTORIZATION) THEN
  MP_TAC(ISPECL [`k:A ring`; `&p:int`] RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
               RING_OF_INTEGERS; RING_OF_INTEGERS_FINITE_QUOTIENT;
               INT_OF_NUM_EQ; PRIME_IMP_NZ; RING_OF_INT_OF_NUM; INT_ABS_NUM;
               NUM_OF_INT_OF_NUM] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN
   `!P. P IN {P | prime_ideal (ring_of_integers k) P /\
                   ring_of_num (k:A ring) p IN P}
        ==> ideal_norm (ring_of_integers k) P EXP
            ideal_valuation (ring_of_integers k) P
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            p EXP (ramification_index (integer_ring,ring_of_integers k)
                     (ring_of_int k) P *
                   residue_degree (integer_ring,ring_of_integers k)
                     (ring_of_int k) P)`
  (MP_TAC o MATCH_MP NPRODUCT_EQ) THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RAMIFICATION_INDEX_PRIME) THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
      RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    REPEAT(DISCH_THEN SUBST1_TAC) THEN REWRITE_TAC[EXP_EXP; MULT_SYM];
    ASM_SIMP_TAC[GSYM EXP_NSUM] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[EQ_EXP; PRIME_IMP_NZ; PRIME_GE_2;
                 ARITH_RULE `2 <= p ==> ~(p = 1)`] THEN
    MESON_TAC[]]);;

let NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q = prove
 (`!k:A ring P p.
        number_field k /\ prime_ideal (ring_of_integers k) P /\ prime p /\
        ring_of_num k p IN P
        ==> 1 <= ramification_index (integer_ring,ring_of_integers k)
                   (ring_of_int k) P /\
            1 <= residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) P /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P *
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k) P
            <= extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(MP_TAC o SPEC `P:A->bool` o GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RAMIFICATION_INDEX_PRIME) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`]
      IDEAL_VALUATION_EQ_0) THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                 RING_OF_INTEGERS] THEN
    ARITH_TAC;
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
      IDEAL_NORM_GT_1) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q;
                 RING_OF_INTEGERS_FINITE_QUOTIENT; PRIME_IMP_RING_IDEAL] THEN
    ANTS_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IDEAL_IMP_PSUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= f) <=> f = 0`] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXP; LT_REFL];
    MP_TAC(ISPECL
     [`\P. ramification_index (integer_ring,ring_of_integers k)
             (ring_of_int k) P *
           residue_degree (integer_ring,ring_of_integers (k:A ring))
             (ring_of_int (k:A ring)) P`;
      `extension_degree (subfield_generated k {ring_0 k},k) (I:A->A)`;
      `{P | prime_ideal (ring_of_integers k) P /\
            ring_of_num k p IN (P:A->bool)}`] NSUM_POS_BOUND) THEN
    ASM_SIMP_TAC[NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q; LE_REFL] THEN
    DISCH_THEN(MP_TAC o SPEC `P:A->bool`) THEN ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q = prove
 (`!k:A ring p.
        number_field k /\ prime p
        ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                        ring_of_num k p IN P} /\
            ~({P | prime_ideal (ring_of_integers k) P /\
                   ring_of_num k p IN P} = {}) /\
            CARD {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P}
            <= extension_degree (subfield_generated k {ring_0 k},k) I`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    RING_OF_INTEGERS_IDEAL_GENERATED_PRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`] NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q) THEN
  MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[NSUM_CLAUSES]) THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[CARD_EQ_NSUM] THEN MATCH_MP_TAC NSUM_LE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `P:A->bool` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
      NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Indexed families of primes above p: the exponents of a factorization of   *)
(* pO are the ramification indices, the norm of a product of prime powers, a *)
(* product of prime powers inside pO with sum e f = [k:Q] is the             *)
(* factorization; a prime pO is not a product of two primes.                 *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE = prove
 (`!k:A ring p s (P:K->A->bool) e.
        number_field k /\ prime p /\ FINITE s /\
        (!i. i IN s ==> prime_ideal (ring_of_integers k) (P i) /\ ~(e i = 0)) /\
        (!i j. i IN s /\ j IN s /\ P i = P j ==> i = j) /\
        ideal_generated (ring_of_integers k) {ring_of_num k p} =
        ideal_product (ring_of_integers k) s
          (\i. ideal_pow (ring_of_integers k) (P i) (e i))
        ==> {q | prime_ideal (ring_of_integers k) q /\ ring_of_num k p IN q} =
            IMAGE P s /\
            !i. i IN s ==> ramification_index (integer_ring,ring_of_integers k)
                             (ring_of_int k) (P i) = e i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> (@j. j IN s /\ (P:K->A->bool) j = P i) = i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`; `IMAGE (P:K->A->bool) s`;
                 `\q. (e:K->num) (@i. i IN s /\ (P:K->A->bool) i = q)`]
    NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_Q) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP IDEAL_PRODUCT_IMAGE th]) THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE] THEN ANTS_TAC THENL
   [MATCH_MP_TAC IDEAL_PRODUCT_EQ THEN ASM_SIMP_TAC[o_THM];
    SIMP_TAC[]]);;

let NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT = prove
 (`!k:A ring p s (P:K->A->bool) e.
        number_field k /\ prime p /\ FINITE s /\
        (!i. i IN s
             ==> prime_ideal (ring_of_integers k) (P i) /\
                 ring_of_num k p IN P i)
        ==> FINITE(ring_carrier(quotient_ring (ring_of_integers k)
                    (ideal_product (ring_of_integers k) s
                      (\i. ideal_pow (ring_of_integers k) (P i) (e i))))) /\
            ideal_norm (ring_of_integers k)
              (ideal_product (ring_of_integers k) s
                (\i. ideal_pow (ring_of_integers k) (P i) (e i))) =
            p EXP nsum s (\i. residue_degree (integer_ring,ring_of_integers k)
                                (ring_of_int k) (P i) * e i)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ring_of_num k p = ring_0 (k:A ring))` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_NUM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
    SIMP_TAC[DIVIDES_ZERO] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN s
        ==> ring_ideal (ring_of_integers k) ((P:K->A->bool) i) /\
            ~(P i = {ring_0 k}) /\
            FINITE(ring_carrier(quotient_ring (ring_of_integers k) (P i))) /\
            ideal_norm (ring_of_integers k) (P i) =
            p EXP residue_degree (integer_ring,ring_of_integers k)
                    (ring_of_int k) (P i)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((P:K->A->bool) i = {ring_0 k})` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT;
                 RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `s:K->bool`;
                 `\i. ideal_pow (ring_of_integers k) ((P:K->A->bool) i)
                                ((e:K->num) i)`]
    IDEAL_NORM_IDEAL_PRODUCT) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW;
               INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
               IDEAL_NORM_IDEAL_POW; RING_OF_INTEGERS; REWRITE_RULE
                [RING_OF_INTEGERS] (ISPEC `ring_of_integers k:A ring`
                IDEAL_POW_EQ_ZERO)] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  TRANS_TAC EQ_TRANS
   `nproduct s (\i. p EXP (residue_degree (integer_ring,ring_of_integers k)
                             (ring_of_int k)
                             ((P:K->A->bool) i) * (e:K->num) i))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[nproduct] THEN
    MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_MUL) THEN
    ASM_SIMP_TAC[IDEAL_NORM_IDEAL_POW; DEDEKIND_RING_OF_INTEGERS;
                 RING_OF_INTEGERS; EXP_EXP];
    UNDISCH_TAC `FINITE(s:K->bool)` THEN SPEC_TAC(`s:K->bool`,`s:K->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    SIMP_TAC[NSUM_CLAUSES; NPRODUCT_CLAUSES; EXP; EXP_ADD]]);;

let NUMBER_FIELD_PRIME_FACTORIZATION_SUBSET_EQ = prove
 (`!k:A ring p s (P:K->A->bool) e.
        number_field k /\ prime p /\ FINITE s /\
        (!i. i IN s
             ==> prime_ideal (ring_of_integers k) (P i) /\
                 ring_of_num k p IN P i /\ ~(e i = 0)) /\
        (!i j. i IN s /\ j IN s /\ P i = P j ==> i = j) /\
        ideal_product (ring_of_integers k) s
          (\i. ideal_pow (ring_of_integers k) (P i) (e i)) SUBSET
        ideal_generated (ring_of_integers k) {ring_of_num k p} /\
        nsum s (\i. residue_degree (integer_ring,ring_of_integers k)
                      (ring_of_int k) (P i) * e i) =
        extension_degree (subfield_generated k {ring_0 k},k) I
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k) s
              (\i. ideal_pow (ring_of_integers k) (P i) (e i)) /\
            {q | prime_ideal (ring_of_integers k) q /\ ring_of_num k p IN q} =
            IMAGE P s /\
            !i. i IN s ==> ramification_index (integer_ring,ring_of_integers k)
                             (ring_of_int k) (P i) = e i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`; `s:K->bool`; `P:K->A->bool`; `e:K->num`]
    NUMBER_FIELD_IDEAL_NORM_PRIME_PRODUCT) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [W(fun (_,w) -> MP_TAC(ISPECL
     [`ring_of_integers k:A ring`; rand w; lhs w] IDEAL_NORM_SUBSET_EQ)) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; RING_IDEAL_IDEAL_PRODUCT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`k:A ring`; `&p:int`]
      RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN
    ASM_REWRITE_TAC[RING_OF_INT_OF_NUM; INT_ABS_NUM; NUM_OF_INT_OF_NUM;
                    INT_OF_NUM_EQ] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ];
    DISCH_TAC THEN
    MATCH_MP_TAC NUMBER_FIELD_PRIME_FACTORIZATION_UNIQUE_IMAGE THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

let NUMBER_FIELD_PRIME_IDEAL_PROD_EQ = prove
 (`!k:A ring p P Q.
        number_field k /\ prime p /\
        prime_ideal (ring_of_integers k)
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) /\
        prime_ideal (ring_of_integers k) P /\
        prime_ideal (ring_of_integers k) Q /\
        ideal_generated (ring_of_integers k) {ring_of_num k p} =
        ideal_prod (ring_of_integers k) P Q
        ==> P = Q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `j = ideal_generated (ring_of_integers k) {ring_of_num k p:A}` THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (j:A->bool)` MP_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ring_of_num k p IN (j:A->bool)` MP_TAC THENL
     [EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
      REWRITE_TAC[IN_SING; RING_OF_INTEGERS] THEN
      REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_RING_OF_INTEGERS];
      ASM_REWRITE_TAC[IN_SING] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[number_field]) THEN
      ASM_REWRITE_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN
      ASM_MESON_TAC[PRIME_IMP_NZ]];
    ALL_TAC] THEN
  REWRITE_TAC[maximal_ideal; NOT_EXISTS_THM] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `proper_ideal (ring_of_integers k) (P:A->bool) /\
    proper_ideal (ring_of_integers k) (Q:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[prime_ideal]; ALL_TAC] THEN
  SUBGOAL_THEN `(j:A->bool) SUBSET P /\ j SUBSET Q` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[proper_ideal]) THEN
    ASM_SIMP_TAC[IDEAL_PROD_SUBSET_LEFT; IDEAL_PROD_SUBSET_RIGHT;
                 RING_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `j:A->bool = P /\ j = Q` (fun th -> MESON_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
   `!j k:A->bool. j SUBSET k /\ ~(j PSUBSET k) ==> j = k`) THEN
  ASM_MESON_TAC[]);;
