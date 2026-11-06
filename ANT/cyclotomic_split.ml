(* ========================================================================= *)
(* The decomposition of primes in a cyclotomic field k = Q(z), z of order n  *)
(* (Neukirch I.10.1, I.10.3, I.10.4). For a prime p with n = p^a m, p not    *)
(* dividing m, every prime P of O above p has ramification index phi(p^a)    *)
(* and residue degree order m p (the least f with p^f == 1 mod m), and there *)
(* are phi(m) / order m p of them (CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION).    *)
(* Hence p ramifies iff p divides n, except for p = 2 when 4 does not divide *)
(* n (CYCLOTOMIC_FIELD_RAMIFIED, stated with the discriminant), a prime p    *)
(* not dividing n splits completely iff p == 1 (mod n)                       *)
(* (CYCLOTOMIC_FIELD_TOTALLY_SPLIT), and for n = p^(v+1) the prime p is      *)
(* totally ramified, pO = (1 - z)^phi(n) with (1 - z) prime of residue       *)
(* degree 1 (CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED). On the way: the         *)
(* Dedekind-Kummer theorem for z with the primes (p, g(z)) for the           *)
(* irreducible factors g of Phi_m mod p (CYCLOTOMIC_FIELD_DEDEKIND_KUMMER).  *)
(* For p not dividing n the decomposition law extends to the subfields of k  *)
(* (CYCLOTOMIC_SUBFIELD_PRIME_DECOMPOSITION of                               *)
(* ANT/cyclotomic_subfield_split.ml; its case K = k is the unramified case   *)
(* here).                                                                    *)
(*                                                                           *)
(* Routes. O = Z[z] (CYCLOTOMIC_FIELD_RING_OF_INTEGERS), so the              *)
(* Dedekind-Kummer theorem (DEDEKIND_KUMMER_Q) applies to every p, with the  *)
(* integer polynomial cyclotomic_poly integer_ring n of degree [k:Q] =       *)
(* phi(n); mod p it is Phi_m^phi(p^a) (CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE,    *)
(* CYCLOTOMIC_POLY_RING_CHAR). Over F_p, Phi_m is the product of             *)
(* phi(m) / order m p distinct monic irreducible polynomials of degree       *)
(* order m p (CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION of                   *)
(* ANT/cyclotomic_poly.ml). Ramification:                                    *)
(* NUMBER_FIELD_RAMIFIED_DISCRIMINANT; splitting:                            *)
(* NUMBER_FIELD_TOTALLY_SPLIT_CARD and ORDER_EQ_1. Prime powers: m = 1 and   *)
(* the single factor X - 1 of Phi_1 mod p; the prime (p, g(z)) is (1 - z),   *)
(* since g(z) == z - 1 modulo p (DEDEKIND_KUMMER_EPIMORPHISM_Q) and p is a   *)
(* multiple of 1 - z (RING_ASSOCIATES_PRIME_POWER_ORDER of                   *)
(* ANT/cyclotomic_integers.ml).                                              *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (RING_PRODUCT_POW), Library/fieldtheory.ml    *)
(* (subfield_generated), ANT/ideal_arith.ml (ideal_pow, ideal_product),      *)
(* ANT/numfield.ml, ANT/prime_split.ml, ANT/discriminant.ml,                 *)
(* ANT/ramification.ml (NUMBER_FIELD_RAMIFIED_DISCRIMINANT),                 *)
(* ANT/dedekind_kummer.ml (DEDEKIND_KUMMER_Q), ANT/splitting_types.ml        *)
(* (NUMBER_FIELD_PRIME_DECOMPOSITION_Q, NUMBER_FIELD_TOTALLY_SPLIT_CARD),    *)
(* ANT/cyclotomic_poly.ml, ANT/cyclotomic_field.ml and                       *)
(* ANT/cyclotomic_integers.ml (CYCLOTOMIC_FIELD_RING_OF_INTEGERS,            *)
(* RING_ASSOCIATES_PRIME_POWER_ORDER).                                       *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/numfield.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/ramification.ml";;
needs "ANT/dedekind_kummer.ml";;
needs "ANT/splitting_types.ml";;
needs "ANT/cyclotomic_poly.ml";;
needs "ANT/cyclotomic_field.ml";;
needs "ANT/cyclotomic_integers.ml";;

(* ------------------------------------------------------------------------- *)
(* The Dedekind-Kummer theorem for cyclotomic fields: z and the integer      *)
(* polynomial Phi_n satisfy the hypotheses of DEDEKIND_KUMMER_Q (O = Z[z]),  *)
(* and Phi_n mod p = prod_(g in s) g^phi(p^a) when Phi_m mod p is the        *)
(* product of the distinct monic irreducibles g in s.                        *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_FIELD_DEDEKIND_KUMMER = prove
 (`!(k:A ring) z p a m s P.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = p EXP a * m /\ subfield_generated k {z} = k /\
        prime p /\ ~(p divides m) /\ FINITE s /\
        (!g. g IN s
             ==> g IN ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
                 monic (integer_mod_ring p) g /\
                 ring_irreducible (poly_ring (integer_mod_ring p) (:1)) g) /\
        cyclotomic_poly (integer_mod_ring p) m =
        ring_product (poly_ring (integer_mod_ring p) (:1)) s (\g. g) /\
        (!g. P g =
             ideal_generated (ring_of_integers k)
               {ring_of_num k p,
                poly_extend (integer_ring,k) (ring_of_int k) (\v. z) g})
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_product (ring_of_integers k) s
              (\g. ideal_pow (ring_of_integers k) (P g) (phi(p EXP a))) /\
            {Q | prime_ideal (ring_of_integers k) Q /\ ring_of_num k p IN Q} =
            IMAGE P s /\
            (!g h. g IN s /\ h IN s /\ P g = P h ==> g = h) /\
            (!g. g IN s
                 ==> prime_ideal (ring_of_integers k) (P g) /\
                     residue_degree (integer_ring,ring_of_integers k)
                       (ring_of_int k) (P g) =
                     poly_deg (integer_mod_ring p) g /\
                     ramification_index (integer_ring,ring_of_integers k)
                       (ring_of_int k) (P g) =
                     phi(p EXP a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = p EXP a * m` THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; DIVIDES_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `p:num`; `cyclotomic_poly integer_ring n`;
                 `s:((1->num)->int)->bool`; `\g:(1->num)->int. g`;
                 `\g:(1->num)->int. phi(p EXP a)`;
                 `P:((1->num)->int)->A->bool`] DEDEKIND_KUMMER_Q) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_MONIC] THEN
  ASM_SIMP_TAC[PHI_EQ_0; EXP_EQ_0; PRIME_IMP_NZ] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CYCLOTOMIC_POLY_DEG; INTEGER_RING; INT_OF_NUM_EQ; ARITH_EQ] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CYCLOTOMIC_FIELD_DEGREE THEN
    EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[];
    SIMP_TAC[POLY_EXTEND_EVALUATE; RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    REWRITE_TAC[GSYM poly_eval; MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
      (ISPEC `k:A ring` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)] THEN
    MATCH_MP_TAC CYCLOTOMIC_POLY_ROOT THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD; FIELD_IMP_INTEGRAL_DOMAIN];
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`]
      CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SETADD_RSUBSET THEN
    REWRITE_TAC[CARRIER_SUBRING_OF; IDEAL_GENERATED_SUBSET;
                IDEAL_GENERATED_NONEMPTY];
    REWRITE_TAC[MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
      (ISPEC `integer_mod_ring p` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)] THEN
    EXPAND_TAC "n" THEN
    ASM_SIMP_TAC[CYCLOTOMIC_POLY_RING_CHAR; INTEGER_MOD_RING_CHAR] THEN
    REWRITE_TAC[GSYM(ISPECL [`integer_mod_ring p`; `(:1)`]
                     (el 7 (CONJUNCTS POLY_RING_CLAUSES)))] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_PRODUCT_POW THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The decomposition law.                                                    *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION = prove
 (`!(k:A ring) z n p a m.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        subfield_generated k {z} = k /\
        prime p /\ n = p EXP a * m /\ ~(p divides m)
        ==> (!P. prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
                 ==> ramification_index (integer_ring,ring_of_integers k)
                       (ring_of_int k) P = phi(p EXP a) /\
                     residue_degree (integer_ring,ring_of_integers k)
                       (ring_of_int k) P = order m p) /\
            CARD {P | prime_ideal (ring_of_integers k) P /\
                      ring_of_num k p IN P} * order m p = phi m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  MP_TAC(ISPECL [`integer_mod_ring p`; `m:num`]
    CYCLOTOMIC_POLY_IRREDUCIBLE_FACTORIZATION) THEN
  ASM_SIMP_TAC[FIELD_INTEGER_MOD_RING; FINITE_INTEGER_MOD_RING;
               CARD_INTEGER_MOD_RING; PRIME_IMP_NZ;
               ONCE_REWRITE_RULE[COPRIME_SYM] PRIME_COPRIME_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:((1->num)->int)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `p:num`; `a:num`; `m:num`;
                 `s:((1->num)->int)->bool`;
                 `\g. ideal_generated (ring_of_integers k)
                        {ring_of_num (k:A ring) p,
                         poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                           (g:(1->num)->int)}`]
    CYCLOTOMIC_FIELD_DEDEKIND_KUMMER) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(Q:A->bool) IN
      {Q | prime_ideal (ring_of_integers k) Q /\ ring_of_num (k:A ring) p IN Q}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[IN_IMAGE]] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(1->num)->int`
     (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
    ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o
      lhand o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let CYCLOTOMIC_FIELD_RAMIFIED =
  let lemma = prove
   (`!p a m.
        prime p /\ ~(p divides m)
        ==> (1 < phi(p EXP a) <=>
             p divides p EXP a * m /\ ~(p = 2 /\ ~(4 divides p EXP a * m)))`,
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PHI_PRIMEPOW_ALT] THEN
    ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES; LT_REFL] THEN
    ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_REXP; DIVIDES_REFL] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    ASM_CASES_TAC `p = 2` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_CASES_TAC `a = 1` THEN ASM_REWRITE_TAC[] THENL
       [CONV_TAC NUM_REDUCE_CONV THEN UNDISCH_TAC `~(2 divides m)` THEN
        REWRITE_TAC[CONTRAPOS_THM; divides] THEN STRIP_TAC THEN
        EXISTS_TAC `x:num` THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `?b. a = b + 2` (CHOOSE_THEN SUBST1_TAC) THENL
         [EXISTS_TAC `a - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `(b + 2) - 1 = b + 1`; EXP_ADD] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        REWRITE_TAC[ARITH_RULE `1 < (x * 2) * 1 <=> ~(x = 0)`; EXP_EQ_0] THEN
        CONV_TAC NUMBER_RULE];
      MATCH_MP_TAC(ARITH_RULE `1 * 2 <= x * y ==> 1 < x * y`) THEN
      MATCH_MP_TAC LE_MULT2 THEN
      ASM_SIMP_TAC[LE_1; EXP_EQ_0; PRIME_IMP_NZ] THEN ASM_ARITH_TAC]) in
  prove
   (`!(k:A ring) z n p.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        prime p
        ==> (&p divides number_field_discriminant k <=>
             p divides n /\ ~(p = 2 /\ ~(4 divides n)))`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= p ==> ~(p = 1)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`p:num`; `index p n`; `m:num`] lemma) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM NUMBER_FIELD_RAMIFIED_DISCRIMINANT] THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`; `p:num`; `index p n`; `m:num`]
      CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    MP_TAC(ISPECL [`k:A ring`; `p:num`] NUMBER_FIELD_PRIME_DECOMPOSITION_Q) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `P:A->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_MESON_TAC[]);;

let CYCLOTOMIC_FIELD_TOTALLY_SPLIT = prove
 (`!(k:A ring) z n p.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        prime p /\ ~(p divides n)
        ==> (totally_split (integer_ring,ring_of_integers k)
               (ring_of_int k) (ideal_generated integer_ring {&p}) <=>
             (p == 1) (mod n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_TOTALLY_SPLIT_CARD; GSYM ORDER_EQ_1] THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`] CYCLOTOMIC_FIELD_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`; `p:num`; `0`; `n:num`]
    CYCLOTOMIC_FIELD_PRIME_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MP_TAC(SPEC `n:num` PHI_EQ_0) THEN ASM_REWRITE_TAC[] THEN
  MATCH_ACCEPT_TAC(MESON[MULT_CLAUSES; EQ_MULT_LCANCEL]
   `!c t f:num. ~(f = 0) ==> c * t = f ==> (c = f <=> t = 1)`));;

(* ------------------------------------------------------------------------- *)
(* Prime powers: (1 - z) is totally ramified. Local lemmas: 1 - z divides p  *)
(* in an integral domain when z has order p^(b+1) ((1 - z)^phi(p^(b+1)) and  *)
(* p are associates, RING_ASSOCIATES_PRIME_POWER_ORDER); for a in O with O = *)
(* Z[a] + pO and an ideal j containing p, g(a) is in j iff 1 - a is, where g *)
(* = X - 1 over F_p (DEDEKIND_KUMMER_EPIMORPHISM_Q); hence the prime         *)
(* (p, g(z)) of Dedekind-Kummer is (1 - z).                                  *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_FIELD_PRIME_POWER_RAMIFIED =
  let lemma1 = prove
   (`!(r:A ring) z p b.
        integral_domain r /\ z IN ring_carrier r /\ prime p /\
        ring_order r z = p EXP (b + 1)
        ==> ring_divides r (ring_sub r (ring_1 r) z) (ring_of_num r p)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `z:A`; `p:num`; `b + 1`]
      RING_ASSOCIATES_PRIME_POWER_ORDER) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ring_associates] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] RING_DIVIDES_TRANS) THEN
    MP_TAC(SPEC `p EXP (b + 1)` PHI_LOWERBOUND_1_STRONG) THEN
    ASM_SIMP_TAC[LE_1; EXP_EQ_0; PRIME_IMP_NZ] THEN
    SPEC_TAC(`phi(p EXP (b + 1))`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ARITH; ring_pow] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC RING_DIVIDES_RMUL THEN
    ASM_SIMP_TAC[RING_DIVIDES_REFL; RING_SUB; RING_1; RING_POW]) in
  let lemma2 = prove
   (`!(k:A ring) a p.
        number_field k /\ prime p /\ a IN ring_carrier(ring_of_integers k) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k)
        ==> poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
              (cyclotomic_poly (integer_mod_ring p) 1) IN
            ring_carrier(ring_of_integers k) /\
            !j. ring_ideal (ring_of_integers k) j /\ ring_of_num k p IN j
                ==> (poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                       (cyclotomic_poly (integer_mod_ring p) 1) IN j <=>
                     ring_sub k (ring_1 k) a IN j)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `\v:1. (a:A)`;
                   `cyclotomic_poly (integer_mod_ring p) 1`]
      POLY_EXTEND_RING_OF_INTEGERS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[POLY_RING_INTEGER_MOD_RING_SUBSET; SUBSET;
                    CYCLOTOMIC_POLY_IN_CARRIER];
      DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]] THEN
    ABBREV_TAC `x = poly_extend (integer_ring,k:A ring) (ring_of_int k)
                      (\v. a) (cyclotomic_poly (integer_mod_ring p) 1)` THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_SUB) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_1) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN
    X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `a:A`; `p:num`; `j:A->bool`]
      DEDEKIND_KUMMER_EPIMORPHISM_Q) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `cyclotomic_poly integer_ring 1` o CONJUNCT2) THEN
    REWRITE_TAC[CYCLOTOMIC_POLY_IN_CARRIER; MATCH_MP
      CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
      (ISPEC `integer_mod_ring p` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)] THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[POLY_EXTEND_EVALUATE; RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    REWRITE_TAC[GSYM poly_eval; MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
      (ISPEC `k:A ring` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)] THEN
    ASM_SIMP_TAC[CYCLOTOMIC_POLY_1; POLY_EVAL_SUB; POLY_EVAL_VAR; POLY_EVAL_1;
                 RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_1; RING_COSET_EQ] THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_TAC THEN
    MP_TAC(REWRITE_RULE[RING_OF_INTEGERS] (ISPECL
     [`ring_of_integers k:A ring`; `j:A->bool`] IN_RING_IDEAL_SUB)) THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:A`] (RING_RULE
     `!r x a:A. ring_sub r (ring_sub r x (ring_sub r a (ring_1 r))) x =
                ring_sub r (ring_1 r) a /\
                ring_sub r (ring_sub r x (ring_sub r a (ring_1 r)))
                  (ring_sub r (ring_1 r) a) = x`)) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ASM_MESON_TAC[]]) in
  let lemma3 = prove
   (`!(k:A ring) z p b.
        number_field k /\ z IN ring_carrier k /\ prime p /\
        ring_order k z = p EXP (b + 1) /\ subfield_generated k {z} = k
        ==> ideal_generated (ring_of_integers k)
              {ring_of_num k p,
               poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                 (cyclotomic_poly (integer_mod_ring p) 1)} =
            ideal_generated (ring_of_integers k) {ring_sub k (ring_1 k) z}`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(z:A) IN ring_carrier(ring_of_integers k) /\
      ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {z}))
        (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
      ring_carrier(ring_of_integers k)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP (b + 1)`]
        CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN
      ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[SUBRING_GENERATED_INC_GEN; IN_SING] THEN
      MATCH_MP_TAC RING_SETADD_RSUBSET THEN
      REWRITE_TAC[CARRIER_SUBRING_OF; IDEAL_GENERATED_SUBSET;
                  IDEAL_GENERATED_NONEMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_of_num k p IN
      ideal_generated (ring_of_integers k) {ring_sub k (ring_1 k) (z:A)}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `z:A`; `p:num`; `b:num`]
        lemma1) THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
                   RING_OF_INTEGERS] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[RING_ORDER_UNIQUE; RING_OF_INTEGERS] THEN
      X_GEN_TAC `d:num` THEN
      MP_TAC(ISPECL [`k:A ring`; `z:A`; `d:num`] RING_ORDER_DIVIDES) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_SUB) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_1) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`k:A ring`; `z:A`; `p:num`] lemma2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; IDEALS_GENERATED_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    CONJ_TAC THEN X_GEN_TAC `w:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IN_IDEAL_GENERATED_SELF] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `ideal_generated (ring_of_integers k)
        {ring_of_num k p,
         poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
           (cyclotomic_poly (integer_mod_ring p) 1):A}`) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_INC_GEN;
                 IN_INSERT]) in
  prove
   (`!(k:A ring) z p v.
        number_field k /\ z IN ring_carrier k /\ prime p /\
        ring_order k z = p EXP (v + 1) /\ subfield_generated k {z} = k
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_sub k (ring_1 k) z}) /\
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)
              (ideal_generated (ring_of_integers k)
                 {ring_sub k (ring_1 k) z}) = 1 /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_sub k (ring_1 k) z})
              (phi(p EXP (v + 1)))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:A ring`; `z:A`; `p:num`; `v:num`] lemma3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `p:num`; `v + 1`; `1`;
                   `{cyclotomic_poly (integer_mod_ring p) 1}`;
                   `\g. ideal_generated (ring_of_integers k)
                          {ring_of_num (k:A ring) p,
                           poly_extend (integer_ring,k) (ring_of_int k) (\v. z)
                             (g:(1->num)->int)}`]
      CYCLOTOMIC_FIELD_DEDEKIND_KUMMER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MULT_CLAUSES; DIVIDES_ONE; FINITE_SING; IN_SING;
                   FORALL_UNWIND_THM2; CYCLOTOMIC_POLY_IN_CARRIER;
                   CYCLOTOMIC_POLY_MONIC; RING_PRODUCT_SING;
                   ARITH_RULE `2 <= p ==> ~(p = 1)`] THEN
      MATCH_MP_TAC POLY_DEG_1_IMP_IRREDUCIBLE;
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_SING; FORALL_UNWIND_THM2; IDEAL_PRODUCT_SING;
                 RING_IDEAL_IDEAL_POW; CYCLOTOMIC_POLY_DEG;
                 CYCLOTOMIC_POLY_IN_CARRIER; FIELD_INTEGER_MOD_RING;
                 GSYM TRIVIAL_RING_10; TRIVIAL_INTEGER_MOD_RING; PHI_1;
                 ARITH_RULE `2 <= p ==> ~(p = 1)`]);;
