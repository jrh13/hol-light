(* ========================================================================= *)
(* The ring of integers of a cyclotomic field. For a number field k with an  *)
(* element z of exact order n generating k (k = Q(z), the setting of         *)
(* ANT/cyclotomic_field.ml), the ring of integers is Z[z] =                  *)
(* subring_generated k {z} (CYCLOTOMIC_FIELD_RING_OF_INTEGERS), with the     *)
(* integral basis 1, z, ..., z^(phi(n)-1) (CYCLOTOMIC_FIELD_INTEGRAL_BASIS). *)
(* The discriminant: for n = p^(v+1), d_k = (-1)^(phi(n)/2)                  *)
(* p^(p^v (p (v+1) - v - 2)) (CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER),    *)
(* and for every n, d_k prod_(p | n) p^(phi(n)/(p-1)) = (-1)^(phi(n)/2)      *)
(* n^phi(n) (CYCLOTOMIC_FIELD_DISCRIMINANT).                                 *)
(*                                                                           *)
(* Route (no discriminants, no composita). Z[z] is p-maximal in O_k for      *)
(* every prime p, in any number field containing an element z of finite      *)
(* order: x in O_k and p x in Z[z] imply x in Z[z]                           *)
(* (SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL). With a Q-basis of powers of z, *)
(* every x in O_k has a nonzero integer multiple in Z[z], hence lies in Z[z] *)
(* by induction on the multiple.                                             *)
(*                                                                           *)
(* For w of order m, the integer polynomials vanishing at w are the          *)
(* multiples of Phi_m (CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY, by the minimal  *)
(* polynomial over Q), and divisibility of reductions modulo n lifts to Z[X] *)
(* (POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT). For p not dividing m,          *)
(* Z[w]/pZ[w] is reduced (SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED): if       *)
(* h(w)^j is in pZ[w], then Phi_m divides h^j modulo p, so it divides h      *)
(* modulo p, Phi_m being squarefree over F_p (CYCLOTOMIC_POLY_SQUAREFREE,    *)
(* RING_SQUAREFREE_DIVPOW). A nonzero integer D with D O_K in Z[w] for K =   *)
(* Q(w) (SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR, from                   *)
(* RING_OF_INTEGERS_DISCRIMINANT and the power basis of K) gives             *)
(* p-maximality: for D = p^s t with p not dividing t, (t p x)^(s+1) is in    *)
(* pZ[w], so t x is in Z[w], and x is in Z[w] by Bezout                      *)
(* (SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME). So an element of Z[w]  *)
(* some power of which is in pO_k is in pZ[w]                                *)
(* (SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL).                                *)
(*                                                                           *)
(* For p dividing n, n = p^a m with p not dividing m: with eta = z^m, w =    *)
(* z^(p^a), pi = 1 - eta and e = phi(p^a), pi^e and p are associates in Z[z] *)
(* (RING_ASSOCIATES_PRIME_POWER_ORDER, from CYCLOTOMIC_POLY_SPLITS at 1) and *)
(* Z[z] = Z[w] + pi Z[z] (SUBRING_GENERATED_POW_DECOMPOSE). If p x = p r +   *)
(* pi^i s with r, s in Z[z] and i < e, write s = c + pi t with c in Z[w]:    *)
(* then c is in pi O_k, hence c^e in pO_k, so c is in pZ[w] and p x = p r1 + *)
(* pi^(i+1) t; at i = e, pi^e is in pZ[z] and x is in Z[z]                   *)
(* (SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES).                        *)
(*                                                                           *)
(* Discriminant, prime powers. d_k is the discriminant of the power basis,   *)
(* so ring_of_int d_k = (-1)^(m(m-1)/2) N(D(z)) with D the derivative of     *)
(* Phi_n and m = phi(n) (CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV, by             *)
(* NUMBER_FIELD_DISCRIMINANT_POWER_BASIS of ANT/power_basis.ml). From X^n -  *)
(* 1 = Phi_n (X^(p^v) - 1) follows n = (-z) D(z) (1 - z^(p^v)); the norm of  *)
(* c - a for rational c is f(c), f the minimal polynomial of a generator a   *)
(* (NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL of ANT/numfield.ml), so N(-z) = *)
(* Phi_n(0) = 1, and N(1 - z^(p^v)) = Phi_p(1)^(p^v) = p^(p^v) by the norm   *)
(* tower for Q(z^(p^v)) (CYCLOTOMIC_FIELD_NORM_SUB_POW).                     *)
(*                                                                           *)
(* Discriminant, general n, by induction. For n = r s with r, s coprime, eta *)
(* = z^s and w = z^r, the products eta^i w^j (i < phi(r), j < phi(s)) form   *)
(* an integral basis of k (CYCLOTOMIC_FIELD_PRODUCT_BASIS: they span Z[z] =  *)
(* O since z = eta^u w^v, and there are [k:Q] of them), the trace of k on    *)
(* products x y with x in K = Q(eta) and y in L = Q(w) is Tr_K(x) Tr_L(y)    *)
(* (ALGEBRA_TRACE_PRODUCT_BASIS of ANT/power_basis.ml), so the trace matrix  *)
(* is a Kronecker product and d_k = d_K^phi(s) d_L^phi(r)                    *)
(* (RING_DET_KRONECKER_MOD_DIV of Library/ring_det.ml,                       *)
(* CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM); the case n = 1 is the instance *)
(* r = s = 1 (d_k = d_k^2 and d_k is nonzero).                               *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (polynomial division, squarefree elements of  *)
(* a UFD, RING_SUM_MUL_MOD_DIV), Library/fieldtheory.ml (minimal             *)
(* polynomials, PRIME_SUBFIELD_SUBFIELD_GENERATED,                           *)
(* RING_ORDER_SUBFIELD_GENERATED, FREE_BASIS_SPANNING_DEGREE),               *)
(* Library/products.ml (nproduct), Library/multiplicative.ml (PHI_EXPAND,    *)
(* loaded by Library/primitive.ml), Library/ring_det.ml                      *)
(* (RING_DET_KRONECKER_MOD_DIV, free_basis,                                  *)
(* algebra_trace, algebra_norm), ANT/integral.ml, ANT/numfield.ml            *)
(* (NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL),                               *)
(* ANT/ring_of_integers.ml (RING_OF_INTEGERS_DISCRIMINANT),                  *)
(* ANT/discriminant.ml, ANT/dedekind_kummer.ml                               *)
(* (SUBRING_GENERATED_INT_LINCOMB, IMAGE_POLY_EXTEND_INTEGER_RING),          *)
(* ANT/relative_split.ml (RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE,             *)
(* NUMBER_FIELD_TOWER_LAW), ANT/cyclotomic_poly.ml, ANT/power_basis.ml       *)
(* (NUMBER_FIELD_DISCRIMINANT_POWER_BASIS, NUMBER_FIELD_NORM_TOWER) and      *)
(* ANT/cyclotomic_field.ml.                                                  *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/products.ml";;
needs "Library/primitive.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/integral.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/dedekind_kummer.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/cyclotomic_poly.ml";;
needs "ANT/power_basis.ml";;
needs "ANT/cyclotomic_field.ml";;

(* ------------------------------------------------------------------------- *)
(* Integer polynomials at roots of unity, and reduction modulo n.            *)
(* ------------------------------------------------------------------------- *)

(* The integer polynomial Phi_n vanishes at an element of order n.           *)
let CYCLOTOMIC_POLY_INTEGER_ROOT = prove
 (`!k:A ring w n.
        integral_domain k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0)
        ==> poly_extend (integer_ring,k) (ring_of_int k) (\v. w)
              (cyclotomic_poly integer_ring n) = ring_0 k`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[POLY_EXTEND_EVALUATE; RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
  REWRITE_TAC[GSYM poly_eval] THEN
  REWRITE_TAC[MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
    (ISPEC `k:A ring` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)] THEN
  MATCH_MP_TAC CYCLOTOMIC_POLY_ROOT THEN ASM_REWRITE_TAC[]);;

(* Z[w] is the integer span of 1, w, ..., w^(phi(n)-1) for w of order n.     *)
let SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB = prove
 (`!k:A ring w n.
        integral_domain k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0)
        ==> ring_carrier(subring_generated k {w}) =
            {ring_sum k {i | i < phi n}
               (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k w i)) |
             c IN (:num->int)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `cyclotomic_poly integer_ring n`]
    SUBRING_GENERATED_INT_LINCOMB) THEN
  ASM_SIMP_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_MONIC;
               CYCLOTOMIC_POLY_DEG; CYCLOTOMIC_POLY_INTEGER_ROOT] THEN
  REWRITE_TAC[INTEGER_RING; INT_OF_NUM_EQ; ARITH_EQ]);;

(* The integer polynomials vanishing at w of order n are the multiples of    *)
(* Phi_n: Phi_n is the integer model of the minimal polynomial of w          *)
(* (CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL), so                                  *)
(* NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES applies.                  *)
let CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY = prove
 (`!k:A ring w n q.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\
        q IN ring_carrier(poly_ring integer_ring (:1))
        ==> (ring_divides (poly_ring integer_ring (:1))
               (cyclotomic_poly integer_ring n) q <=>
             poly_extend (integer_ring,k) (ring_of_int k) (\v. w) q =
             ring_0 k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `n:num`] CYCLOTOMIC_POLY_INTEGER_ROOT) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[ring_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(1->num)->int` STRIP_ASSUME_TAC o
      last o CONJUNCTS) THEN
    MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `(:1)`; `ring_of_int k:int->A`;
                   `\v:1. (w:A)`] RING_HOMOMORPHISM_POLY_EXTEND) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                                      CYCLOTOMIC_POLY_IN_CARRIER]) THEN
    MATCH_MP_TAC RING_MUL_LZERO THEN REWRITE_TAC[POLY_EXTEND];
    DISCH_TAC THEN
    MATCH_MP_TAC NUMBER_FIELD_INTEGER_MINIMAL_POLYNOMIAL_DIVIDES THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `w:A`] THEN
    ASM_SIMP_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_MONIC;
                 CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL; CYCLOTOMIC_POLY_DEG;
                 SUBFIELD_GENERATED; FIELD_NONTRIVIAL] THEN
    REWRITE_TAC[INTEGER_RING; INT_OF_NUM_EQ; ARITH_EQ]]);;

(* If f divides h modulo n, then h = f u + n d in Z[X]: the cofactor modulo  *)
(* n has its coefficients in 0..n-1 and is an integer polynomial.            *)
let POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT = prove
 (`!n f h.
        f IN ring_carrier(poly_ring integer_ring (:1)) /\
        h IN ring_carrier(poly_ring integer_ring (:1)) /\
        ring_divides (poly_ring (integer_mod_ring n) (:1))
          (ring_of_int (integer_mod_ring n) o f)
          (ring_of_int (integer_mod_ring n) o h)
        ==> ?u d. u IN ring_carrier(poly_ring integer_ring (:1)) /\
                  d IN ring_carrier(poly_ring integer_ring (:1)) /\
                  h = ring_add (poly_ring integer_ring (:1))
                        (ring_mul (poly_ring integer_ring (:1)) f u)
                        (ring_mul (poly_ring integer_ring (:1))
                           (ring_of_num (poly_ring integer_ring (:1)) n) d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:(1->num)->int` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`integer_ring`; `integer_mod_ring n`;
                 `ring_of_int(integer_mod_ring n)`; `(:1)`]
    RING_HOMOMORPHISM_POLY_RINGS) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(u:(1->num)->int) IN ring_carrier(poly_ring integer_ring (:1)) /\
    ring_of_int (integer_mod_ring n) o u = u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[POLY_RING_INTEGER_MOD_RING_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; INTEGER_MOD_RING_OF_INT; INT_REM_EQ_SELF;
                INT_ABS_NUM] THEN
    X_GEN_TAC `m:1->num` THEN
    UNDISCH_TAC
     `(u:(1->num)->int) IN
      ring_carrier(poly_ring (integer_mod_ring n) (:1))` THEN
    REWRITE_TAC[IN_POLY_RING_CARRIER; ring_polynomial; ring_powerseries] THEN
    DISCH_THEN(MP_TAC o SPEC `m:1->num` o hd o CONJUNCTS) THEN
    REWRITE_TAC[IN_INTEGER_MOD_RING_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`integer_ring`; `(:1)`; `&n:int`;
    `ring_sub (poly_ring integer_ring (:1)) h
       (ring_mul (poly_ring integer_ring (:1)) f u)`]
    POLY_CONST_DIVIDES_COEFFS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_SUB; RING_MUL; INTEGER_RING_DIVIDES] THEN
    SUBGOAL_THEN
     `ring_of_int (integer_mod_ring n) o
      ring_sub (poly_ring integer_ring (:1)) h
        (ring_mul (poly_ring integer_ring (:1)) f u) =
      ring_0(poly_ring (integer_mod_ring n) (:1))`
    MP_TAC THENL
     [FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[BETA_RULE(MATCH_MP RING_HOMOMORPHISM_SUB th);
                     BETA_RULE(MATCH_MP RING_HOMOMORPHISM_MUL th); RING_MUL;
                     RING_SUB_REFL]);
      REWRITE_TAC[FUN_EQ_THM; o_THM; INTEGER_MOD_RING_OF_INT; INT_REM_EQ_0;
                  POLY_RING_CLAUSES; POLY_0; INTEGER_MOD_RING_CLAUSES]];
    ALL_TAC] THEN
  REWRITE_TAC[ring_divides; GSYM INTEGER_RING_OF_NUM; GSYM(ISPECL
   [`integer_ring`; `(:1)`] RING_OF_NUM_POLY_RING)] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(1->num)->int` STRIP_ASSUME_TAC o
    last o CONJUNCTS) THEN
  MAP_EVERY EXISTS_TAC [`u:(1->num)->int`; `d:(1->num)->int`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  MATCH_MP_TAC(GEN_ALL(RING_RULE
   `ring_sub r h a = b ==> (h:A) = ring_add r a b`)) THEN
  ASM_SIMP_TAC[RING_MUL; RING_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Primes not dividing the order.                                            *)
(* ------------------------------------------------------------------------- *)

(* Z[w]/pZ[w] is reduced for p not dividing the order n of w, as Phi_n is    *)
(* squarefree modulo p.                                                      *)
let SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED = prove
 (`!k:A ring w n p c j.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\ prime p /\ ~(p divides n) /\
        c IN ring_carrier(subring_generated k {w}) /\
        (?y. y IN ring_carrier(subring_generated k {w}) /\
             ring_pow k c j = ring_mul k (ring_of_num k p) y)
        ==> ?y. y IN ring_carrier(subring_generated k {w}) /\
                c = ring_mul k (ring_of_num k p) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`] IMAGE_POLY_EXTEND_INTEGER_RING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `n:num`] CYCLOTOMIC_POLY_INTEGER_ROOT) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `(:1)`; `ring_of_int k:int->A`;
                 `\v:1. w:A`] RING_HOMOMORPHISM_POLY_EXTEND) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN DISCH_TAC THEN
  ABBREV_TAC `E = poly_extend (integer_ring,k) (ring_of_int k) (\v:1. w:A)` THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    CONJUNCT1 o GEN_REWRITE_RULE I [RING_HOMOMORPHISM]) THEN
  UNDISCH_TAC `(y:A) IN ring_carrier(subring_generated k {w})` THEN
  UNDISCH_TAC `(c:A) IN ring_carrier(subring_generated k {w})` THEN
  ASM_REWRITE_TAC[IN_IMAGE; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(1->num)->int`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(1->num)->int`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `n:num`;
    `ring_sub (poly_ring integer_ring (:1))
       (ring_pow (poly_ring integer_ring (:1)) h j)
       (ring_mul (poly_ring integer_ring (:1))
          (ring_of_num (poly_ring integer_ring (:1)) p) g)`]
    CYCLOTOMIC_POLY_DIVIDES_INTEGER_POLY) THEN
  ASM_SIMP_TAC[RING_SUB; RING_POW; RING_MUL; RING_OF_NUM] THEN
  MP_TAC(ASSUME
   `ring_homomorphism(poly_ring integer_ring (:1),k)
                     (E:((1->num)->int)->A)`) THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th;
    MATCH_MP RING_HOMOMORPHISM_MUL th; MATCH_MP RING_HOMOMORPHISM_POW th;
    MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th; RING_POW; RING_OF_NUM;
    RING_MUL; RING_SUB_REFL]) THEN
  MP_TAC(ISPECL [`integer_ring`; `integer_mod_ring p`;
                 `ring_of_int(integer_mod_ring p)`; `(:1)`]
    RING_HOMOMORPHISM_POLY_RINGS) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
  DISCH_THEN(fun th ->
    DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP (REWRITE_RULE[IMP_CONJ]
      RING_DIVIDES_HOMOMORPHIC_IMAGE) th)) THEN
    ASSUME_TAC th) THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[BETA_RULE(MATCH_MP RING_HOMOMORPHISM_SUB th);
                 BETA_RULE(MATCH_MP RING_HOMOMORPHISM_MUL th);
                 BETA_RULE(MATCH_MP RING_HOMOMORPHISM_POW th);
                 BETA_RULE(MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th);
                 RING_POW; RING_MUL; RING_OF_NUM]) THEN
  SUBGOAL_THEN
   `ring_of_int (integer_mod_ring p) o (g:(1->num)->int) IN
    ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
    ring_of_int (integer_mod_ring p) o (h:(1->num)->int) IN
    ring_carrier(poly_ring (integer_mod_ring p) (:1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_RING_POLYNOMIAL_CARRIER_COMPOSE THEN
    EXISTS_TAC `integer_ring` THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_num (poly_ring (integer_mod_ring p) (:1)) p =
    ring_0 (poly_ring (integer_mod_ring p) (:1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RING_OF_NUM_EQ_0; RING_CHAR_POLY_RING; INTEGER_MOD_RING_CHAR;
                DIVIDES_REFL];
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_SUB_RZERO; RING_POW]] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num`; `cyclotomic_poly integer_ring n`; `h:(1->num)->int`]
    POLY_RING_INTEGER_MOD_RING_DIVIDES_LIFT) THEN
  ASM_REWRITE_TAC[CYCLOTOMIC_POLY_IN_CARRIER] THEN ANTS_TAC THENL
   [MATCH_MP_TAC RING_SQUAREFREE_DIVPOW THEN EXISTS_TAC `j:num` THEN
    ASM_REWRITE_TAC[MATCH_MP CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE
     (ISPEC `integer_mod_ring p` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)] THEN
    ASM_SIMP_TAC[PID_IMP_UFD; PID_POLY_RING; FIELD_INTEGER_MOD_RING;
                 FIELD_IMP_INTEGRAL_DOMAIN; CYCLOTOMIC_POLY_SQUAREFREE;
                 RING_OF_NUM_EQ_0; INTEGER_MOD_RING_CHAR];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(1->num)->int` (X_CHOOSE_THEN `d:(1->num)->int`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN
  EXISTS_TAC `d:(1->num)->int` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME
   `ring_homomorphism(poly_ring integer_ring (:1),k)
                     (E:((1->num)->int)->A)`) THEN
  DISCH_THEN(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD th;
    MATCH_MP RING_HOMOMORPHISM_MUL th;
    MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th; RING_OF_NUM;
    RING_MUL; CYCLOTOMIC_POLY_IN_CARRIER]) THEN
  ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_LZERO; RING_MUL; RING_OF_NUM]);;

(* A nonzero integer d with d y in Z[w] for every algebraic integer y of     *)
(* Q(w), from the power basis of the number field Q(w) (algebraic integers)  *)
(* and RING_OF_INTEGERS_DISCRIMINANT.                                        *)
let SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR = prove
 (`!k:A ring w n.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0)
        ==> ?d. ~(d = 0) /\
                !y. y IN ring_carrier(ring_of_integers k) /\
                    y IN ring_carrier(subfield_generated k {w})
                    ==> ring_mul k (ring_of_num k d) y IN
                        ring_carrier(subring_generated k {w})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `(w:A) IN ring_carrier(subfield_generated k {w})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBFIELD_GENERATED_INC THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subfield_generated k {w:A}`; `phi n`;
                 `\i. ring_pow (subfield_generated k {w:A}) w i`]
    RING_OF_INTEGERS_DISCRIMINANT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_SUBFIELD_GENERATED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CYCLOTOMIC_FIELD_FREE_BASIS THEN
      ASM_SIMP_TAC[NUMBER_FIELD_SUBFIELD_GENERATED;
                   RING_ORDER_SUBFIELD_GENERATED; SUBFIELD_GENERATED_IDEMPOT];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `ring_of_integers(subfield_generated k {w:A})` RING_POW) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM;
                integral_element] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `cyclotomic_poly integer_ring n` THEN
    REWRITE_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_MONIC] THEN
    MATCH_MP_TAC CYCLOTOMIC_POLY_INTEGER_ROOT THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FIELD_SUBFIELD_GENERATED;
                 RING_ORDER_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED; CONJUNCT2 SUBFIELD_GENERATED] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:int` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "D"))) THEN
  SUBGOAL_THEN `&0 <= D * D /\ ~(D * D = &0:int)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_LE_SQUARE; INT_ENTIRE] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[RING_OF_INT_0];
    ALL_TAC] THEN
  EXISTS_TAC `num_of_int(D * D)` THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT;
               GSYM RING_OF_INT_OF_NUM] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  REMOVE_THEN "D" (MP_TAC o SPEC `y:A`) THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`subfield_generated k {w:A}`; `k:A ring`; `I:A->A`;
                   `y:A`] RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN
    ASM_SIMP_TAC[I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED;
                  field_extension];
    DISCH_THEN(X_CHOOSE_TAC `c:num->int`)] THEN
  SUBGOAL_THEN
   `ring_mul k (ring_of_int k D) y IN ring_carrier(subring_generated k {w:A})`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_SUBFIELD_GENERATED] THEN
    MP_TAC(ISPECL [`subfield_generated k {w:A}`; `w:A`; `n:num`]
      SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FIELD_SUBFIELD_GENERATED;
                 RING_ORDER_SUBFIELD_GENERATED] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `c:num->int` THEN
    REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED; CONJUNCT2 SUBFIELD_GENERATED];
    DISCH_TAC] THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul k (ring_of_int k (D * D)) y =
    ring_mul k (ring_of_int k D) (ring_mul k (ring_of_int k D) y:A)`
  SUBST1_TAC THENL
   [SIMP_TAC[RING_OF_INT_MUL; RING_MUL_ASSOC; RING_OF_INT;
             ASSUME `(y:A) IN ring_carrier k`];
    MATCH_MP_TAC IN_SUBRING_MUL THEN
    SIMP_TAC[SUBRING_SUBRING_GENERATED; IN_SUBRING_INT] THEN
    FIRST_ASSUM ACCEPT_TAC]);;

(* p-maximality for p not dividing the order: with d as in the previous      *)
(* lemma, d = p^s t and p not dividing t, (t p x)^(s+1) is in pZ[w], so t x  *)
(* is in Z[w] by reducedness, and x is in Z[w] by Bezout.                    *)
let SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME = prove
 (`!k:A ring w n p x.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\ prime p /\ ~(p divides n) /\
        x IN ring_carrier(ring_of_integers k) /\
        ring_mul k (ring_of_num k p) x IN ring_carrier(subring_generated k {w})
        ==> x IN ring_carrier(subring_generated k {w})`,
  let lemma = prove
   (`!k:A ring s a b x.
        s subring_of k /\ x IN ring_carrier k /\ coprime(a,b) /\
        ring_mul k (ring_of_num k a) x IN s /\
        ring_mul k (ring_of_num k b) x IN s
        ==> x IN s`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (INTEGER_RULE
     `!a b:int. coprime(a,b) ==> ?u v. u * a + v * b = &1`) o
     GEN_REWRITE_RULE I [num_coprime]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:int`; `v:int`] THEN
    DISCH_THEN(MP_TAC o AP_TERM `ring_of_int (k:A ring)`) THEN
    REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL; RING_OF_INT_OF_NUM;
                RING_OF_INT_1] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `x = ring_add k
            (ring_mul k (ring_of_int k u) (ring_mul k (ring_of_num k a) x))
            (ring_mul k (ring_of_int k v) (ring_mul k (ring_of_num k b) x)):A`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_add r (ring_mul r u a) (ring_mul r v b) = ring_1 r
        ==> (x:A) = ring_add r (ring_mul r u (ring_mul r a x))
                               (ring_mul r v (ring_mul r b x))`))) THEN
      ASM_REWRITE_TAC[RING_OF_INT; RING_OF_NUM];
      ASM_SIMP_TAC[IN_SUBRING_ADD; IN_SUBRING_MUL; IN_SUBRING_INT]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  SUBGOAL_THEN
   `(x:A) IN ring_carrier k /\ ~(ring_of_num k p = ring_0 k) /\
    ring_carrier(subring_generated k {w}) SUBSET
    ring_carrier(subfield_generated k {w:A})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN
    ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET;
                  SUBRING_GENERATED_SUBFIELD_GENERATED;
                  RING_CARRIER_SUBRING_GENERATED_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier(subfield_generated k {w})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `x = ring_mul k (ring_inv k (ring_of_num k p))
                     (ring_mul k (ring_of_num k p) x):A`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; RING_OF_NUM; FIELD_MUL_LINV;
                   RING_MUL_LID];
      MATCH_MP_TAC RING_MUL_IN_SUBFIELD_GENERATED THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
      MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN
      ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED] THEN
      MP_TAC(ISPECL [`subfield_generated k {w:A}`; `p:num`] RING_OF_NUM) THEN
      REWRITE_TAC[RING_OF_NUM_SUBFIELD_GENERATED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `n:num`]
    SUBRING_GENERATED_ROOT_OF_UNITY_DENOMINATOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "d"))) THEN
  MP_TAC(SPECL [`d:num`; `p:num`] INDEX_DECOMPOSITION) THEN
  ASM_SIMP_TAC[MESON[PRIME_1] `prime p ==> ~(p = 1)`] THEN
  ABBREV_TAC `s = index p d` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `R = ring_carrier(subring_generated k {w:A})` THEN
  SUBGOAL_THEN `(R:A->bool) subring_of k` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED]; ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC [`k:A ring`; `t:num`; `p:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`k:A ring`; `w:A`; `n:num`; `p:num`;
    `ring_mul k (ring_of_num k t) (ring_mul k (ring_of_num k p) x:A)`;
    `s + 1`] SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED) THEN
  ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_NUM] THEN
  ANTS_TAC THENL
   [EXISTS_TAC
     `ring_mul k (ring_of_num k (t EXP s))
        (ring_mul k (ring_of_num k d) (ring_pow k x (s + 1))):A` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_SIMP_TAC[IN_SUBRING_NUM] THEN
      REMOVE_THEN "d" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[RING_POW_IN_SUBFIELD_GENERATED] THEN
      MP_TAC(ISPEC `ring_of_integers k:A ring` RING_POW) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_of_num k t) (ring_mul k (ring_of_num k p) x) =
      ring_mul k (ring_of_num k (t * p)) (x:A)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_OF_NUM_MUL; RING_MUL_ASSOC; RING_OF_NUM]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_MUL_POW; RING_OF_NUM; GSYM RING_OF_NUM_EXP;
                 RING_MUL_ASSOC; GSYM RING_OF_NUM_MUL; RING_POW] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
      check (fun th -> rand(concl th) = `d:num`)) THEN
    REWRITE_TAC[EXP_ADD; EXP_1; MULT_EXP; MULT_AC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ring_mul k (ring_of_num k t) x = v:A`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k p:A`] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_NUM; RING_MUL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[subring_of; SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[RING_MUL_ASSOC; RING_OF_NUM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC RING_MUL_SYM THEN
  REWRITE_TAC[RING_OF_NUM]);;

(* An element of Z[w] with a power in pO_k is in pZ[w].                      *)
let SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL = prove
 (`!k:A ring w n p c y j.
        number_field k /\ w IN ring_carrier k /\
        ring_order k w = n /\ ~(n = 0) /\ prime p /\ ~(p divides n) /\
        c IN ring_carrier(subring_generated k {w}) /\
        y IN ring_carrier(ring_of_integers k) /\
        ring_pow k c j = ring_mul k (ring_of_num k p) y
        ==> ?b. b IN ring_carrier(subring_generated k {w}) /\
                c = ring_mul k (ring_of_num k p) b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_REDUCED THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `p:num`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[IN_SUBRING_POW; SUBRING_SUBRING_GENERATED]);;

(* ------------------------------------------------------------------------- *)
(* Primes dividing the order.                                                *)
(* ------------------------------------------------------------------------- *)

(* For x of order p^a, a >= 1, in an integral domain, (1 - x)^phi(p^a) and p *)
(* are associates: p is the product of the 1 - x^j with j coprime to p, and  *)
(* 1 - x and 1 - x^j divide each other.                                      *)
let RING_ASSOCIATES_PRIME_POWER_ORDER = prove
 (`!r:A ring x p a.
        integral_domain r /\ x IN ring_carrier r /\ prime p /\ ~(a = 0) /\
        ring_order r x = p EXP a
        ==> ring_associates r
              (ring_pow r (ring_sub r (ring_1 r) x) (phi(p EXP a)))
              (ring_of_num r p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ABBREV_TAC `U = {j | j < p EXP a /\ coprime(j,p EXP a)}` THEN
  SUBGOAL_THEN `FINITE(U:num->bool) /\ CARD U = phi(p EXP a)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[PHI_ALT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j:num | j < p EXP a}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      AP_TERM_TAC THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= p EXP a` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 <= p /\ p <= q ==> 2 <= q`) THEN
    ASM_SIMP_TAC[PRIME_GE_2] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    ASM_SIMP_TAC[LE_EXP; LE_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_num r p =
    ring_product r U (\j. ring_sub r (ring_1 r) (ring_pow r (x:A) j))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `p:num`; `a:num`]
      CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`r:A ring`; `x:A`; `p EXP a`] CYCLOTOMIC_POLY_SPLITS) THEN
    ASM_REWRITE_TAC[EXP_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) POLY_EVAL_RING_PRODUCT o
      lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_SUB;
                   RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST; RING_POW;
                   RING_1];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_PRODUCT_EQ THEN
    ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST;
                 RING_POW; POLY_EVAL_VAR; POLY_EVAL_CONST; RING_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow r (ring_sub r (ring_1 r) x) (phi(p EXP a)) =
    ring_product r (U:num->bool) (\j. ring_sub r (ring_1 r) (x:A))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_PRODUCT_CONST; RING_SUB; RING_1]; ALL_TAC] THEN
  SUBGOAL_THEN `!j. j IN U ==> ~(j = 0) /\ coprime(j,p EXP a)`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[COPRIME_0] THENL
     [ASM_ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[ring_associates] THEN CONJ_TAC THEN
  MATCH_MP_TAC RING_DIVIDES_PRODUCTS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP th)) THENL
   [MP_TAC(ISPECL [`r:A ring`; `ring_1 r:A`; `x:A`; `j:num`]
      RING_DIVIDES_SUB_POW) THEN
    ASM_REWRITE_TAC[RING_1; RING_POW_ONE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`j:num`; `1`; `p EXP a`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
  SUBGOAL_THEN `~(i = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES;
      NUMBER_RULE `(0 == 1) (mod n) <=> n = 1`]) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_1 r:A`; `ring_pow r x j:A`; `i:num`]
    RING_DIVIDES_SUB_POW) THEN
  ASM_SIMP_TAC[RING_1; RING_POW_ONE; RING_POW; RING_POW_POW] THEN
  SUBGOAL_THEN `ring_pow r x (j * i) = ring_pow r (x:A) 1` MP_TAC THENL
   [ASM_SIMP_TAC[RING_POW_EQ_GEN; EXP_EQ_0]; ASM_SIMP_TAC[RING_POW_1]]);;

(* Z[z] = Z[z^q] + (1 - z^m) Z[z] if z^(q m) = 1 and q, m are coprime: the   *)
(* right side is a subring containing z^m and z^q, hence z.                  *)
let SUBRING_GENERATED_POW_DECOMPOSE = prove
 (`!k:A ring z q m s.
        z IN ring_carrier k /\ ring_pow k z (q * m) = ring_1 k /\
        coprime(q,m) /\ s IN ring_carrier(subring_generated k {z})
        ==> ?c t. c IN ring_carrier(subring_generated k {ring_pow k z q}) /\
                  t IN ring_carrier(subring_generated k {z}) /\
                  s = ring_add k c (ring_mul k
                        (ring_sub k (ring_1 k) (ring_pow k z m)) t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `R = ring_carrier(subring_generated k {z:A})` THEN
  ABBREV_TAC `W = ring_carrier(subring_generated k {ring_pow k z q:A})` THEN
  ABBREV_TAC `l = ring_sub k (ring_1 k) (ring_pow k z m:A)` THEN
  SUBGOAL_THEN
   `(R:A->bool) subring_of k /\ (W:A->bool) subring_of k /\ z IN R /\
    W SUBSET R /\ (l:A) IN R`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "W"; "l"] THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
      REWRITE_TAC[SING_SUBSET; SUBRING_SUBRING_GENERATED];
      MATCH_MP_TAC IN_SUBRING_SUB] THEN
    ASM_SIMP_TAC[SUBRING_SUBRING_GENERATED; IN_SUBRING_1; IN_SUBRING_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:A. x IN W ==> x IN R) /\ (!x:A. x IN R ==> x IN ring_carrier k) /\
    (!x:A. x IN W ==> x IN ring_carrier k) /\ (l:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[subring_of; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{y:A | ?c t. c IN W /\ t IN R /\ y = ring_add k c (ring_mul k l t)}
    subring_of k`
  ASSUME_TAC THENL
   [REWRITE_TAC[subring_of; SUBSET; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhand o concl) o
           check (is_eq o concl))) THENL
     [ASM_SIMP_TAC[RING_ADD; RING_MUL];
      MAP_EVERY EXISTS_TAC [`ring_0 k:A`; `ring_0 k:A`] THEN
      ASM_SIMP_TAC[IN_SUBRING_0; RING_MUL_RZERO; RING_ADD_LZERO; RING_0];
      MAP_EVERY EXISTS_TAC [`ring_1 k:A`; `ring_0 k:A`] THEN
      ASM_SIMP_TAC[IN_SUBRING_0; IN_SUBRING_1; RING_MUL_RZERO; RING_ADD_RZERO;
                   RING_1];
      MAP_EVERY EXISTS_TAC [`ring_neg k c:A`; `ring_neg k t:A`];
      MAP_EVERY EXISTS_TAC [`ring_add k c c':A`; `ring_add k t t':A`];
      MAP_EVERY EXISTS_TAC
       [`ring_mul k c c':A`;
        `ring_add k (ring_mul k c t')
           (ring_add k (ring_mul k t c') (ring_mul k l (ring_mul k t t'))):A`]
      THEN CONJ_TAC THENL [ASM_SIMP_TAC[IN_SUBRING_MUL]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IN_SUBRING_ADD THEN
        ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_ADD];
        ALL_TAC]]
    THEN ASM_SIMP_TAC[IN_SUBRING_NEG; IN_SUBRING_ADD; IN_SUBRING_MUL] THEN
    W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `U = {y:A | ?c t. c IN W /\ t IN R /\
                     y = ring_add k c (ring_mul k l t)}` THEN
  SUBGOAL_THEN `ring_pow k z m IN U /\ ring_pow k (z:A) q IN U`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`ring_1 k:A`; `ring_neg k (ring_1 k):A`] THEN
      ASM_SIMP_TAC[IN_SUBRING_1; IN_SUBRING_NEG] THEN EXPAND_TAC "l" THEN
      W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[RING_POW];
      MAP_EVERY EXISTS_TAC [`ring_pow k z q:A`; `ring_0 k:A`] THEN
      ASM_SIMP_TAC[IN_SUBRING_0; RING_MUL_RZERO; RING_ADD_RZERO; RING_POW] THEN
      EXPAND_TAC "W" THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_SIMP_TAC[SING_SUBSET; RING_POW; IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN U` ASSUME_TAC THENL
   [ASM_CASES_TAC `q = 1` THENL
     [UNDISCH_TAC `ring_pow k (z:A) q IN U` THEN ASM_SIMP_TAC[RING_POW_1];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `coprime(q,0)` THEN
      ASM_REWRITE_TAC[COPRIME_0];
      ALL_TAC] THEN
    MP_TAC(SPECL [`m:num`; `q:num`] COPRIME_BEZOUT_STRONG) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` (X_CHOOSE_TAC `b:num`)) THEN
    SUBGOAL_THEN
     `z = ring_mul k (ring_pow k (ring_pow k z m) a)
                     (ring_pow k (ring_pow k z q) (b * (m - 1))):A`
    SUBST1_TAC THENL
     [SIMP_TAC[RING_POW_POW; GSYM RING_POW_ADD;
               ASSUME `(z:A) IN ring_carrier k`] THEN
      SUBGOAL_THEN `m * a + q * b * (m - 1) = 1 + (q * m) * b`
      SUBST1_TAC THENL
       [UNDISCH_TAC `m * a = q * b + 1` THEN
        MP_TAC(SPEC `m:num` num_CASES) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
        REWRITE_TAC[SUC_SUB1] THEN CONV_TAC NUM_RING;
        ASM_SIMP_TAC[RING_POW_ADD; RING_POW_MUL; RING_POW_1; RING_POW_ONE;
                     RING_MUL_RID]];
      ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->bool) SUBSET U` MP_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `s:A`) THEN
    EXPAND_TAC "U" THEN ASM_REWRITE_TAC[IN_ELIM_THM]]);;

(* p-maximality for p dividing the order n = p^a m: the descent of the file  *)
(* header.                                                                   *)
let SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES = prove
 (`!k:A ring z p a m x.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = p EXP a * m /\ prime p /\ ~(a = 0) /\
        ~(p divides m) /\
        x IN ring_carrier(ring_of_integers k) /\
        ring_mul k (ring_of_num k p) x IN ring_carrier(subring_generated k {z})
        ==> x IN ring_carrier(subring_generated k {z})`,
  let lemma = prove
   (`!k:A ring R S W l q u v e x.
        (!s. s IN R
             ==> ?c t. c IN W /\ t IN R /\
                       s = ring_add k c (ring_mul k l t)) /\
        (!c y. c IN W /\ y IN S /\ c = ring_mul k l y
               ==> ?b. b IN W /\ c = ring_mul k q b) /\
        integral_domain k /\ R subring_of k /\ S subring_of k /\
        W SUBSET R /\ R SUBSET S /\ l IN R /\ ~(l = ring_0 k) /\
        q IN ring_carrier k /\ ~(q = ring_0 k) /\ u IN R /\ v IN R /\
        ring_mul k (ring_pow k l e) v = q /\ ring_pow k l e = ring_mul k q u /\
        x IN S /\ ring_mul k q x IN R
        ==> x IN R`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "dec")
     (CONJUNCTS_THEN2 (LABEL_TAC "key") STRIP_ASSUME_TAC)) THEN
    MP_TAC(ASSUME `(S:A->bool) subring_of k`) THEN
    REWRITE_TAC[subring_of; SUBSET] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    SUBGOAL_THEN
     `(!y:A. y IN R ==> y IN ring_carrier k) /\
      (!y:A. y IN W ==> y IN ring_carrier k)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(l:A) IN ring_carrier k /\ (u:A) IN ring_carrier k /\
      (v:A) IN ring_carrier k /\ (x:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. i <= e
          ==> ?r s. r IN R /\ s IN R /\
                    ring_mul k q (x:A) =
                    ring_add k (ring_mul k q r) (ring_mul k (ring_pow k l i) s)`
    (MP_TAC o SPEC `e:num`) THENL
     [INDUCT_TAC THENL
       [DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`ring_0 k:A`; `ring_mul k q x:A`] THEN
        ASM_SIMP_TAC[IN_SUBRING_0; ring_pow; RING_MUL_RZERO; RING_ADD_LZERO;
                     RING_MUL_LID; RING_MUL];
        ALL_TAC] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:A`
        (X_CHOOSE_THEN `s:A` STRIP_ASSUME_TAC)) THEN
      USE_THEN "dec" (MP_TAC o C MP (ASSUME `(s:A) IN R`) o SPEC `s:A`) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:A` (X_CHOOSE_THEN `t:A`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          SUBST_ALL_TAC)))) THEN
      USE_THEN "key" (MP_TAC o SPECL
       [`c:A`; `ring_sub k (ring_mul k (ring_pow k l (e - SUC i))
                  (ring_mul k v (ring_sub k x r))) t:A`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REPEAT(FIRST [MATCH_MP_TAC IN_SUBRING_SUB;
                        MATCH_MP_TAC IN_SUBRING_MUL;
                        MATCH_MP_TAC IN_SUBRING_POW; CONJ_TAC]) THEN
          ASM_SIMP_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
        MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_pow k l i:A`] THEN
        ASM_SIMP_TAC[RING_POW; INTEGRAL_DOMAIN_POW_EQ_0; RING_MUL;
                     RING_SUB] THEN
        CONJ_TAC THENL
         [REPEAT(FIRST [MATCH_MP_TAC RING_SUB; MATCH_MP_TAC RING_MUL;
                        MATCH_MP_TAC RING_POW; CONJ_TAC]) THEN ASM_SIMP_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `ring_pow k l e = ring_mul k (ring_pow k l i)
                             (ring_mul k l (ring_pow k l (e - SUC i))):A`
        ASSUME_TAC THENL
         [FIRST_ASSUM(MP_TAC o MATCH_MP
           (ARITH_RULE `SUC i <= e ==> e = i + 1 + (e - SUC i)`)) THEN
          DISCH_THEN(fun th ->
            GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
          ASM_SIMP_TAC[RING_POW_ADD; RING_POW_1];
          ALL_TAC] THEN
        MP_TAC(RING_RULE
         `ring_mul k q x =
          ring_add k (ring_mul k q r)
            (ring_mul k (ring_pow k l i) (ring_add k c (ring_mul k l t))) /\
          ring_mul k (ring_pow k l e) v = q /\
          ring_pow k l e =
          ring_mul k (ring_pow k l i) (ring_mul k l (ring_pow k l (e - SUC i)))
          ==> ring_mul k (ring_pow k l i) c =
              ring_mul k (ring_pow k l i)
               (ring_mul k l (ring_sub k (ring_mul k (ring_pow k l (e - SUC i))
                               (ring_mul k v (ring_sub k x r))) (t:A)))`) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
        REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:A`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      MAP_EVERY EXISTS_TAC
       [`ring_add k r (ring_mul k (ring_pow k l i) b):A`; `t:A`] THEN
      REWRITE_TAC[CONJUNCT2 ring_pow] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[IN_SUBRING_ADD; IN_SUBRING_MUL; IN_SUBRING_POW];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
          lhand(concl th) = `ring_mul k q (x:A)`)) THEN
        W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[LE_REFL] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:A` (X_CHOOSE_THEN `s:A` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `x = ring_add k r (ring_mul k u s):A` SUBST1_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
      MAP_EVERY EXISTS_TAC [`k:A ring`; `q:A`] THEN
      REPEAT CONJ_TAC THEN
      TRY(ASM_SIMP_TAC[RING_ADD; RING_MUL] THEN NO_TAC) THEN
      MP_TAC(RING_RULE
       `ring_mul k q x =
        ring_add k (ring_mul k q r) (ring_mul k (ring_pow k l e) s) /\
        ring_pow k l e = ring_mul k q u
        ==> ring_mul k q x = ring_mul k q (ring_add k r (ring_mul k u (s:A)))`)
      THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN MATCH_MP_TAC] THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[IN_SUBRING_ADD; IN_SUBRING_MUL]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN
   `ring_of_num k p IN ring_carrier k /\ ~(ring_of_num k p = ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_NUM; RING_OF_NUM_EQ_0; DIVIDES_ZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_order k (ring_pow k (z:A) m) = p EXP a /\
    ring_order k (ring_pow k z (p EXP a)) = m`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_ORDER_POW; EXP_EQ_0; NUMBER_RULE `(m:num) divides q * m`;
                 NUMBER_RULE `(q:num) divides q * m`] THEN
    ASM_SIMP_TAC[DIV_MULT; EXP_EQ_0] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM;
                integral_element] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `cyclotomic_poly integer_ring (p EXP a * m)` THEN
    REWRITE_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_MONIC] THEN
    MATCH_MP_TAC CYCLOTOMIC_POLY_INTEGER_ROOT THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; MULT_EQ_0; EXP_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subring_generated k {z:A}`; `ring_pow k z m:A`;
                 `p:num`; `a:num`] RING_ASSOCIATES_PRIME_POWER_ORDER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_DOMAIN_SUBRING_GENERATED;
                 FIELD_IMP_INTEGRAL_DOMAIN] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC IN_SUBRING_POW THEN
      REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
      MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
      DISCH_TAC] THEN
    ASM_SIMP_TAC[RING_ORDER_UNIQUE] THEN
    REWRITE_TAC[RING_POW_SUBRING_GENERATED; CONJUNCT2 SUBRING_GENERATED] THEN
    ASM_SIMP_TAC[RING_POW_EQ_1; RING_POW];
    ALL_TAC] THEN
  REWRITE_TAC[ring_associates; ring_divides; RING_POW_SUBRING_GENERATED;
              RING_SUB_SUBRING_GENERATED; RING_OF_NUM_SUBRING_GENERATED;
              CONJUNCT2 SUBRING_GENERATED] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `v:A` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) o
    last o CONJUNCTS)
   (X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC o last o CONJUNCTS)) THEN
  ABBREV_TAC `R = ring_carrier(subring_generated k {z:A})` THEN
  ABBREV_TAC
   `W = ring_carrier(subring_generated k {ring_pow k z (p EXP a):A})` THEN
  ABBREV_TAC `l = ring_sub k (ring_1 k) (ring_pow k z m:A)` THEN
  ABBREV_TAC `e = phi(p EXP a)` THEN
  SUBGOAL_THEN
   `(R:A->bool) subring_of k /\ (W:A->bool) subring_of k /\
    (!y:A. y IN W ==> y IN R) /\
    (!y:A. y IN R ==> y IN ring_carrier(ring_of_integers k)) /\
    (l:A) IN R /\ ~(l = ring_0 k) /\ l IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["R"; "W"; "l"] THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED; GSYM SUBSET] THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier(subring_generated k {z})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
      ASM_SIMP_TAC[SING_SUBSET; SUBRING_SUBRING_GENERATED; IN_SUBRING_POW];
      MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
      ASM_REWRITE_TAC[SING_SUBSET; RING_OF_INTEGERS_SUBRING];
      ASM_SIMP_TAC[IN_SUBRING_SUB; IN_SUBRING_1; IN_SUBRING_POW;
                   SUBRING_SUBRING_GENERATED];
      ASM_SIMP_TAC[RING_SUB_EQ_0; RING_1; RING_POW] THEN
      DISCH_THEN(MP_TAC o SYM o AP_TERM `ring_order (k:A ring)`) THEN
      ASM_REWRITE_TAC[RING_ORDER_1; EXP_EQ_1] THEN ASM_ARITH_TAC;
      ASM_SIMP_TAC[RING_SUB; RING_1; RING_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c y:A. c IN W /\ y IN ring_carrier(ring_of_integers k) /\
            c = ring_mul k l y
            ==> ?b. b IN W /\ c = ring_mul k (ring_of_num k p) b`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
    EXPAND_TAC "W" THEN
    MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_RADICAL THEN
    MAP_EVERY EXISTS_TAC
     [`m:num`; `ring_mul k u (ring_pow k y e):A`; `e:num`] THEN
    SUBGOAL_THEN `(y:A) IN ring_carrier k /\ (u:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POW] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
      MP_TAC(ISPEC `ring_of_integers k:A ring` RING_POW) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      ASM_SIMP_TAC[RING_MUL_POW; RING_MUL_ASSOC; RING_OF_NUM; RING_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN R
        ==> ?c t. c IN W /\ t IN R /\ s = ring_add k c (ring_mul k l t:A)`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP a`; `m:num`; `s:A`]
      SUBRING_GENERATED_POW_DECOMPOSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_POW_EQ_1; DIVIDES_REFL] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[COPRIME_PRIMEPOW];
    ALL_TAC] THEN
  MATCH_MP_TAC lemma THEN
  MAP_EVERY EXISTS_TAC
   [`k:A ring`; `ring_carrier(ring_of_integers k):A->bool`; `W:A->bool`;
    `l:A`; `ring_of_num k p:A`; `u:A`; `v:A`; `e:num`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_INTEGERS_SUBRING; SUBSET]);;

(* Z[z] is p-maximal in O_k for every prime p.                               *)
let SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL = prove
 (`!k:A ring z n p x.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ prime p /\
        x IN ring_carrier(ring_of_integers k) /\
        ring_mul k (ring_of_num k p) x IN ring_carrier(subring_generated k {z})
        ==> x IN ring_carrier(subring_generated k {z})`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(p:num) divides n` THENL
   [ALL_TAC;
    MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_COPRIME THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `p:num`] THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= p ==> ~(p = 1)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL_DIVIDES THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `index p n`; `m:num`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `p EXP index p n * m = n` THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The ring of integers.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Every x in O_k has a multiple d x in Z[z] with d a nonzero integer        *)
(* (Q-basis of powers of z); then x is in Z[z] by induction on d.            *)
let CYCLOTOMIC_FIELD_RING_OF_INTEGERS = prove
 (`!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> ring_of_integers k = subring_generated k {z}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  REWRITE_TAC[RINGS_EQ; RING_OF_INTEGERS; CONJUNCT2 SUBRING_GENERATED] THEN
  ABBREV_TAC `R = ring_carrier(subring_generated k {z:A})` THEN
  SUBGOAL_THEN `(R:A->bool) subring_of k` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "R" THEN MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    REWRITE_TAC[SING_SUBSET; RING_OF_INTEGERS_SUBRING] THEN
    REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM;
                integral_element] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `cyclotomic_poly integer_ring n` THEN
    ASM_SIMP_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_MONIC;
                 CYCLOTOMIC_POLY_INTEGER_ROOT; FIELD_IMP_INTEGRAL_DOMAIN]] THEN
  SUBGOAL_THEN
   `!d. ~(d = 0)
        ==> !x:A. x IN ring_carrier(ring_of_integers k) /\
                  ring_mul k (ring_of_num k d) x IN R
                  ==> x IN R`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `d:num` THEN
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `d = 1` THENL
     [UNDISCH_TAC `ring_mul k (ring_of_num k d) x IN (R:A->bool)` THEN
      ASM_SIMP_TAC[RING_OF_NUM_1; RING_MUL_LID;
                   REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET];
      ALL_TAC] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [divides]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:num`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `e = 1 * e`] THEN
      ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_MAXIMAL THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `p:num`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
      MP_TAC(ISPEC `ring_of_integers k:A ring` RING_OF_NUM) THEN
      REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_SIMP_TAC[];
      UNDISCH_TAC `ring_mul k (ring_of_num k (p * e)) x IN (R:A->bool)` THEN
      ASM_SIMP_TAC[RING_OF_NUM_MUL; RING_MUL_ASSOC; RING_OF_NUM;
                   REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `phi n`; `\i. ring_pow k (z:A) i`; `{x:A}`]
    FREE_BASIS_PRIME_SUBFIELD_DENOMINATOR) THEN
  ASM_SIMP_TAC[CYCLOTOMIC_FIELD_FREE_BASIS; FINITE_SING; SING_SUBSET;
               FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int` (CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_TAC `c:num->int`))) THEN
  SUBGOAL_THEN `ring_mul k (ring_of_int k d) x IN (R:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
    EXPAND_TAC "R" THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`]
      SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB) THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN EXISTS_TAC `c:num->int` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `num_of_int(d * d)`) THEN
  SUBGOAL_THEN `&0 <= d * d /\ ~(d * d = &0:int)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_LE_SQUARE; INT_ENTIRE]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT;
               GSYM RING_OF_INT_OF_NUM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[RING_OF_INT_MUL] THEN
  SUBGOAL_THEN
   `ring_mul k (ring_mul k (ring_of_int k d) (ring_of_int k d)) x =
    ring_mul k (ring_of_int k d) (ring_mul k (ring_of_int k d) x):A`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN ASM_REWRITE_TAC[RING_OF_INT];
    MATCH_MP_TAC IN_SUBRING_MUL THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC IN_SUBRING_INT THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let CYCLOTOMIC_FIELD_INTEGRAL_BASIS = prove
 (`!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k) (phi n)
                       (\i. ring_pow k z i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  SIMP_TAC[FREE_BASIS_INTEGER_RING_SUBRING_GENERATED;
           SUBRING_SUBRING_GENERATED] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC IN_SUBRING_POW THEN
    REWRITE_TAC[SUBRING_SUBRING_GENERATED] THEN
    MATCH_MP_TAC SUBRING_GENERATED_INC THEN
    ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
    ASM_SIMP_TAC[SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB;
                 FIELD_IMP_INTEGRAL_DOMAIN] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN MESON_TAC[];
    X_GEN_TAC `c:num->int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`] CYCLOTOMIC_FIELD_FREE_BASIS) THEN
    ASM_REWRITE_TAC[free_basis] THEN
    DISCH_THEN(MP_TAC o SPEC `\i. ring_of_int k ((c:num->int) i):A` o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[I_THM; RING_OF_INT_IN_SUBFIELD_GENERATED;
                    CONJUNCT2 SUBFIELD_GENERATED] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0]]);;

(* ------------------------------------------------------------------------- *)
(* Norms of c - z in a cyclotomic field.                                     *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_FIELD_SUBFIELD_POW = prove
 (`!(k:A ring) z n d.
        number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
        ~(n = 0) /\ d divides n
        ==> number_field (subfield_generated k {ring_pow k z d}) /\
            ring_pow k z d IN
            ring_carrier (subfield_generated k {ring_pow k z d}) /\
            ring_order (subfield_generated k {ring_pow k z d})
                       (ring_pow k z d) = n DIV d /\
            ~(n DIV d = 0) /\
            subfield_generated (subfield_generated k {ring_pow k z d})
                               {ring_pow k z d} =
            subfield_generated k {ring_pow k z d} /\
            subfield_generated (subfield_generated k {ring_pow k z d})
              {ring_0 (subfield_generated k {ring_pow k z d})} =
            subfield_generated k {ring_0 k}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [divides]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN
   `ring_pow k (z:A) d IN ring_carrier(subfield_generated k {ring_pow k z d})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `x IN ring_carrier (k:A ring) /\ ring_carrier k INTER {x} SUBSET t
      ==> x IN t`) THEN
    ASM_SIMP_TAC[RING_POW; SUBFIELD_GENERATED_SUBSET_CARRIER];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NUMBER_FIELD_SUBFIELD_GENERATED; SUBFIELD_GENERATED_IDEMPOT;
               PRIME_SUBFIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
               RING_ORDER_SUBFIELD_GENERATED; RING_ORDER_POW; DIVIDES_RMUL;
               DIVIDES_REFL; DIV_MULT]);;

let CYCLOTOMIC_FIELD_NORM_SUB = prove
 (`!(k:A ring) z n c.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        c IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_sub k c z) =
            poly_eval k (cyclotomic_poly k n) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `c:A`]
    NUMBER_FIELD_NORM_SUB_MINIMAL_POLYNOMIAL) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`] CYCLOTOMIC_FIELD_DEGREE) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`]
    CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CYCLOTOMIC_POLY_DEG; CONJUNCT2 SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL; NUMBER_FIELD_IMP_FIELD] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                 `I:A->A`; `n:num`] CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_O_ID] THEN
  DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let CYCLOTOMIC_FIELD_NORM_SUB_POW = prove
 (`!(k:A ring) z n d c.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k /\
        d divides n /\ c IN ring_carrier(subfield_generated k {ring_0 k})
        ==> algebra_norm (subfield_generated k {ring_0 k},k) I
              (ring_sub k c (ring_pow k z d)) =
            ring_pow k (poly_eval k (cyclotomic_poly k (n DIV d)) c)
                       (phi n DIV phi(n DIV d))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`; `d:num`]
    CYCLOTOMIC_FIELD_SUBFIELD_POW) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`] CYCLOTOMIC_FIELD_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `K = subfield_generated k {ring_pow k (z:A) d}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(c:A) IN ring_carrier K` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:A ring`; `{ring_0 K:A}`]
      RING_CARRIER_SUBFIELD_GENERATED_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_sub k c (ring_pow k (z:A) d) IN ring_carrier K`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:A ring`; `c:A`; `ring_pow k (z:A) d`] RING_SUB) THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `subfield_generated k {ring_pow k (z:A) d} = K`)) THEN
    REWRITE_TAC[RING_SUB_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `K:A ring`; `ring_sub k c (ring_pow k (z:A) d)`]
    NUMBER_FIELD_NORM_TOWER) THEN
  ANTS_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `subfield_generated k {ring_pow k (z:A) d} = K`)) THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED;
                 NUMBER_FIELD_IMP_FIELD];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [MP_TAC(ISPECL [`K:A ring`; `ring_pow k (z:A) d`; `n DIV d`; `c:A`]
      CYCLOTOMIC_FIELD_NORM_SUB) THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `subfield_generated k {ring_pow k (z:A) d} = K`)) THEN
    REWRITE_TAC[RING_SUB_SUBFIELD_GENERATED] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_pow k (z:A) d}`; `k:A ring`;
                   `I:A->A`; `n DIV d`] CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE) THEN
    REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_O_ID] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_pow k (z:A) d}`; `k:A ring`;
                   `c:A`; `I:A->A`;
                   `cyclotomic_poly (subfield_generated k {ring_pow k (z:A) d})
                                    (n DIV d)`]
   POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_O_ID; I_THM;
                    CYCLOTOMIC_POLY_IN_CARRIER];
    MP_TAC(ISPECL [`K:A ring`; `ring_pow k (z:A) d`; `n DIV d`]
      CYCLOTOMIC_FIELD_DEGREE) THEN
    MP_TAC(ISPECL [`K:A ring`; `k:A ring`; `I:A->A`]
      NUMBER_FIELD_TOWER_LAW) THEN
    ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `subfield_generated k {ring_pow k (z:A) d} = K`)) THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; NUMBER_FIELD_IMP_FIELD;
                 RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_MULT THEN
    ASM_REWRITE_TAC[PHI_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* The discriminant of a cyclotomic field.                                   *)
(* ------------------------------------------------------------------------- *)

let CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV = prove
 (`!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> ring_of_int k (number_field_discriminant k) =
            ring_mul k
              (ring_pow k (ring_neg k (ring_1 k)) ((phi n * (phi n - 1)) DIV 2))
              (algebra_norm (subfield_generated k {ring_0 k},k) I
                 (poly_eval k (poly_deriv k (cyclotomic_poly k n)) z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`]
    CYCLOTOMIC_FIELD_INTEGRAL_BASIS) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`] CYCLOTOMIC_FIELD_DEGREE) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `n:num`]
    CYCLOTOMIC_POLY_MINIMAL_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `phi n`; `\i. ring_pow k (z:A) i`]
    NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`;
     `minimal_polynomial (subfield_generated k {ring_0 k},k) I (z:A)`;
     `extension_degree (subfield_generated k {ring_0 k},k:A ring) I`]
    NUMBER_FIELD_DISCRIMINANT_POWER_BASIS) THEN
  ASM_REWRITE_TAC[CYCLOTOMIC_POLY_DEG; CONJUNCT2 SUBFIELD_GENERATED] THEN
  ASM_SIMP_TAC[FIELD_NONTRIVIAL; NUMBER_FIELD_IMP_FIELD] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `k:A ring`;
                 `I:A->A`; `n:num`] CYCLOTOMIC_POLY_HOMOMORPHIC_IMAGE) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_SUBFIELD_INCLUSION; I_O_ID] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[POLY_EXTEND_EVALUATE; RING_HOMOMORPHISM_SUBFIELD_INCLUSION] THEN
  REWRITE_TAC[I_O_ID; GSYM poly_eval] THEN
  REWRITE_TAC[poly_deriv; CONJUNCT2 SUBFIELD_GENERATED;
              RING_OF_NUM_SUBFIELD_GENERATED]);;

let CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER = prove
 (`!(k:A ring) z p v.
        number_field k /\ z IN ring_carrier k /\ prime p /\
        ring_order k z = p EXP (v + 1) /\ subfield_generated k {z} = k
        ==> number_field_discriminant k =
            (-- &1) pow (phi(p EXP (v + 1)) DIV 2) *
            &p pow (p EXP v * (p * (v + 1) - v - 2))`,
  let deriv_lemma = prove
   (`!(r:A ring) f g x.
        f IN ring_carrier(poly_ring r (:1)) /\
        g IN ring_carrier(poly_ring r (:1)) /\
        x IN ring_carrier r /\ poly_eval r f x = ring_0 r
        ==> poly_eval r (poly_deriv r (poly_mul r f g)) x =
            ring_mul r (poly_eval r (poly_deriv r f) x) (poly_eval r g x)`,
    REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[POLY_DERIV_MUL; RING_POLYNOMIAL_IMP_POWERSERIES;
                 POLY_EVAL_ADD; POLY_EVAL_MUL; RING_POLYNOMIAL_MUL;
                 RING_POLYNOMIAL_POLY_DERIV; RING_MUL_LZERO; POLY_EVAL;
                 RING_ADD_RZERO; RING_MUL])
  and parity_lemma = prove
 (`!m. EVEN((m * (m - 1)) DIV 2) <=> EVEN(m DIV 2)`,
  GEN_TAC THEN
  DISJ_CASES_THEN (X_CHOOSE_THEN `a:num` SUBST1_TAC)
   (REWRITE_RULE[EVEN_EXISTS; ODD_EXISTS] (SPEC `m:num` EVEN_OR_ODD)) THENL
   [REWRITE_TAC[GSYM MULT_ASSOC] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ; EVEN_MULT; EVEN_SUB; ARITH] THEN
    ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC(TAUT `~q ==> (p \/ q <=> p)`) THEN ASM_ARITH_TAC;
    SUBGOAL_THEN `SUC(2 * a) DIV 2 = a /\
                  (SUC(2 * a) * (SUC(2 * a) - 1)) DIV 2 = SUC(2 * a) * a`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC DIV_UNIQ THENL
       [EXISTS_TAC `1` THEN ARITH_TAC;
        EXISTS_TAC `0` THEN REWRITE_TAC[SUC_SUB1; ADD_CLAUSES; ARITH] THEN
        REWRITE_TAC[MULT_AC]];
      REWRITE_TAC[EVEN_MULT; EVEN] THEN REWRITE_TAC[EVEN_MULT; ARITH]]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `~(p EXP (v + 1) = 0) /\ 2 <= p EXP (v + 1) /\ 2 <= p`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    ASM_REWRITE_TAC[EXP_EQ_0] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC LE_TRANS `p EXP 1` THEN
    ASM_REWRITE_TAC[EXP_1; LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP (v + 1)`]
    CYCLOTOMIC_FIELD_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP (v + 1)`]
    CYCLOTOMIC_FIELD_DISCRIMINANT_DERIV) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `D = poly_eval k (poly_deriv k (cyclotomic_poly k (p EXP (v + 1))))
                    (z:A)` THEN
  SUBGOAL_THEN `(D:A) IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[POLY_EVAL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `algebra_norm (subfield_generated k {ring_0 k},k) I D IN
    ring_carrier (k:A ring)`
  ASSUME_TAC THENL
   [MESON_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER;
              RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow k (ring_of_num k (p EXP (v + 1))) (phi (p EXP (v + 1))) =
    ring_mul k (algebra_norm (subfield_generated k {ring_0 k},k) I D)
               (ring_pow k (ring_of_num (k:A ring) p) (p EXP v))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
       `ring_mul k (ring_of_num k (p EXP (v + 1)))
          (ring_pow k z (p EXP (v + 1) - 1)) =
        ring_mul k D (ring_sub k (ring_pow k z (p EXP v)) (ring_1 (k:A ring)))`
      ASSUME_TAC THENL
       [SUBGOAL_THEN
         `poly_sub k (poly_pow k (poly_var k one) (p EXP (v + 1))) (poly_1 k) =
          poly_mul k (cyclotomic_poly k (p EXP (v + 1)))
            (poly_sub k (poly_pow k (poly_var k one) (p EXP v))
                      (poly_1 (k:A ring)))`
        (MP_TAC o AP_TERM `\P. poly_eval k (poly_deriv k P) (z:A)`) THENL
         [MP_TAC(ISPECL [`k:A ring`; `p EXP v`] CYCLOTOMIC_POLY_PRODUCT) THEN
          MP_TAC(ISPECL [`k:A ring`; `p EXP (v + 1)`]
            CYCLOTOMIC_POLY_PRODUCT) THEN
          SUBGOAL_THEN `~(p = 0) /\ ~(p = 1)` STRIP_ASSUME_TAC THENL
           [ASM_ARITH_TAC; ASM_REWRITE_TAC[EXP_EQ_0]] THEN
          SUBGOAL_THEN
           `{d | d divides p EXP (v + 1)} =
            p EXP (v + 1) INSERT {d | d divides p EXP v}`
          SUBST1_TAC THENL
           [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
            ASM_SIMP_TAC[DIVIDES_PRIMEPOW] THEN
            MESON_TAC[ARITH_RULE `i <= v + 1 <=> i = v + 1 \/ i <= v`];
            ALL_TAC] THEN
          SUBGOAL_THEN `~(p EXP (v + 1) IN {d | d divides p EXP v})`
          ASSUME_TAC THENL
           [ASM_SIMP_TAC[IN_ELIM_THM; DIVIDES_PRIMEPOW; EQ_EXP] THEN ARITH_TAC;
            ALL_TAC] THEN
          ASM_SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_DIVISORS; EXP_EQ_0;
                       CYCLOTOMIC_POLY_IN_CARRIER] THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[POLY_RING_CLAUSES];
          ALL_TAC] THEN
        REWRITE_TAC[] THEN
        W(MP_TAC o PART_MATCH (lhand o rand) deriv_lemma o
          rand o lhand o snd) THEN
        ASM_SIMP_TAC[CYCLOTOMIC_POLY_IN_CARRIER; CYCLOTOMIC_POLY_ROOT;
                     FIELD_IMP_INTEGRAL_DOMAIN; GSYM RING_POLYNOMIAL;
                     RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW;
                     RING_POLYNOMIAL_VAR;
                     RING_POLYNOMIAL_1] THEN
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[POLY_DERIV_SUB; POLY_DERIV_VAR_POW; POLY_DERIV_1;
                     RING_POLYNOMIAL_IMP_POWERSERIES; RING_POLYNOMIAL_POW;
                     RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_1] THEN
        ASM_SIMP_TAC[POLY_EVAL_SUB; POLY_EVAL_MUL; POLY_EVAL_CONST;
                     POLY_EVAL_POW;
                     POLY_EVAL_VAR; POLY_EVAL_0; POLY_EVAL_1;
                     RING_POLYNOMIAL_MUL;
                     RING_POLYNOMIAL_CONST; RING_POLYNOMIAL_POW;
                     RING_POLYNOMIAL_VAR;
                     RING_POLYNOMIAL_0; RING_POLYNOMIAL_1; RING_OF_NUM;
                     RING_SUB_RZERO; RING_MUL; RING_POW];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_of_num k (p EXP (v + 1)) =
        ring_mul k (ring_sub k (ring_0 k) z)
          (ring_mul k D (ring_sub k (ring_1 k) (ring_pow k (z:A) (p EXP v))))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC(GEN_ALL(REWRITE_RULE[IMP_IMP] (RING_RULE
         `ring_mul r a w = ring_mul r d (ring_sub r x (ring_1 r)) /\
          ring_mul r z w = ring_1 r
          ==> a = ring_mul r (ring_sub r (ring_0 r) z)
                    (ring_mul r d (ring_sub r (ring_1 r) (x:A)))`))) THEN
        EXISTS_TAC `ring_pow k (z:A) (p EXP (v + 1) - 1)` THEN
        ASM_SIMP_TAC[RING_OF_NUM; RING_POW] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 ring_pow)] THEN
        ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> SUC(n - 1) = n`; RING_POW_EQ_1;
                     DIVIDES_REFL];
        ALL_TAC] THEN
    SUBGOAL_THEN
       `algebra_norm (subfield_generated k {ring_0 k},k) I
          (ring_sub k (ring_1 k) (ring_pow k z (p EXP v))) =
        ring_pow k (ring_of_num (k:A ring) p) (p EXP v)`
      ASSUME_TAC THENL
       [SUBGOAL_THEN
         `p EXP (v + 1) DIV p EXP v = p /\
          phi(p EXP (v + 1)) DIV phi p = p EXP v`
        STRIP_ASSUME_TAC THENL
         [ASM_SIMP_TAC[PHI_PRIMEPOW_ALT; PHI_PRIME; ADD_EQ_0; ARITH_EQ;
                       ADD_SUB] THEN
          REWRITE_TAC[EXP_ADD; EXP_1] THEN
          ASM_SIMP_TAC[DIV_MULT; EXP_EQ_0;
                       ARITH_RULE `2 <= p ==> ~(p = 0)`] THEN
          ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT THEN
          ASM_ARITH_TAC;
          ALL_TAC] THEN
        MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP (v + 1)`; `p EXP v`;
                       `ring_1 k:A`] CYCLOTOMIC_FIELD_NORM_SUB_POW) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring` RING_1) THEN
          REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; EXP_ADD; EXP_1] THEN
          MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL];
          DISCH_THEN SUBST1_TAC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `p:num`; `1`]
          CYCLOTOMIC_POLY_EVAL_1_PRIME_POWER) THEN
        ASM_REWRITE_TAC[EXP_1; ARITH_EQ];
        ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o
      AP_TERM `algebra_norm (subfield_generated (k:A ring) {ring_0 k},k) I` o
      check
      (fun th -> lhs(concl th) = `ring_of_num (k:A ring) (p EXP (v + 1))`)) THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_of_num k (p EXP (v + 1)):A`]
      NUMBER_FIELD_NORM_RATIONAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`subfield_generated k {ring_0 k}:A ring`; `p EXP (v + 1)`]
        RING_OF_NUM) THEN
      REWRITE_TAC[RING_OF_NUM_SUBFIELD_GENERATED];
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `ring_sub k (ring_0 k) z IN ring_carrier k /\
      ring_sub k (ring_1 k) (ring_pow k z (p EXP v)) IN ring_carrier (k:A ring)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_SUB; RING_0; RING_1; RING_POW]; ALL_TAC] THEN
    ASM_SIMP_TAC[NUMBER_FIELD_NORM_MUL; RING_MUL] THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP (v + 1)`; `ring_0 k:A`]
      CYCLOTOMIC_FIELD_NORM_SUB) THEN
    MP_TAC(ISPEC `subfield_generated k {ring_0 k}:A ring` RING_0) THEN
    ASM_SIMP_TAC[CONJUNCT2 SUBFIELD_GENERATED; CYCLOTOMIC_POLY_EVAL_0] THEN
    DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL; RING_POW; RING_OF_NUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `number_field_discriminant (k:A ring) * &p pow (p EXP v) =
    (-- &1) pow ((phi (p EXP (v + 1)) * (phi (p EXP (v + 1)) - 1)) DIV 2) *
    &(p EXP (v + 1)) pow phi (p EXP (v + 1))`
  MP_TAC THENL
   [MATCH_MP_TAC(INTEGER_RULE `!x y:int. (x == y) (mod &0) ==> x = y`) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> lhs(concl th) = `ring_char (k:A ring)`)) THEN
    REWRITE_TAC[GSYM RING_OF_INT_EQ] THEN
    REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_POW; RING_OF_INT_NEG;
                RING_OF_INT_1; RING_OF_INT_OF_NUM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) =
      `ring_pow k (ring_of_num k (p EXP (v + 1)))
                  (phi (p EXP (v + 1))):A`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) =
      `ring_of_int k (number_field_discriminant (k:A ring))`)) THEN
    ASM_SIMP_TAC[RING_MUL_ASSOC; RING_POW; RING_NEG; RING_1; RING_OF_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE; parity_lemma] THEN
  ASM_SIMP_TAC[PHI_PRIMEPOW_ALT; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
  SUBGOAL_THEN
   `(p EXP (v + 1)) EXP (p EXP v * (p - 1)) =
    p EXP (p EXP v * (p * (v + 1) - v - 2)) * p EXP (p EXP v)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD; GSYM EXP_MULT] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `?q. p = q + 2` (CHOOSE_THEN SUBST1_TAC) THENL
     [EXISTS_TAC `p - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `(q + 2) - 1 = q + 1`;
                ARITH_RULE `(q + 2) * (v + 1) - v - 2 = q * v + q + v`] THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_POW] THEN ASM_REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  REWRITE_TAC[INT_MUL_ASSOC] THEN
  ASM_SIMP_TAC[INT_EQ_MUL_RCANCEL; INT_OF_NUM_EQ; EXP_EQ_0;
               ARITH_RULE `2 <= p ==> ~(p = 0)`]);;

let CYCLOTOMIC_FIELD_PRODUCT_BASIS = prove
 (`!(k:A ring) z r s.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = r * s /\ ~(r * s = 0) /\ coprime(r,s) /\
        subfield_generated k {z} = k
        ==> free_basis (integer_ring,ring_of_integers k) (ring_of_int k)
              (phi r * phi s)
              (\t. ring_mul k (ring_pow k (ring_pow k z s) (t MOD phi r))
                              (ring_pow k (ring_pow k z r) (t DIV phi r)))`,
  let span_lemma = prove
   (`!(k:A ring) x m.
          integral_domain k /\ x IN ring_carrier k /\
          ring_order k x = m /\ ~(m = 0)
          ==> ring_carrier (subring_generated k {x}) =
              {ring_sum k {i | i < phi m}
                 (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k x i)) |
               c IN (:num->int)} /\
              !j. ?c. ring_pow k x j =
                      ring_sum k {i | i < phi m}
                        (\i. ring_mul k (ring_of_int k (c i))
                                        (ring_pow k x i))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBRING_GENERATED_ROOT_OF_UNITY_LINCOMB THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `ring_pow k (x:A) j IN ring_carrier(subring_generated k {x})`
    MP_TAC THENL
     [MP_TAC(ISPECL [`subring_generated k {x:A}`; `x:A`; `j:num`]
        RING_POW) THEN
      REWRITE_TAC[RING_POW_SUBRING_GENERATED] THEN
      DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SUBRING_GENERATED_INC THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `s:num`] RING_ORDER_POW) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num`] RING_ORDER_POW) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`]
    CYCLOTOMIC_FIELD_FREE_BASIS) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`]
    CYCLOTOMIC_FIELD_RING_OF_INTEGERS) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`] CYCLOTOMIC_FIELD_DEGREE) THEN
  ASM_SIMP_TAC[MULT_EQ_0; DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL;
               PHI_MULTIPLICATIVE] THEN
  SUBGOAL_THEN `(r * s) DIV s = r /\ (r * s) DIV r = s` (fun th ->
    REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  ABBREV_TAC `eta = ring_pow k (z:A) s` THEN
  ABBREV_TAC `w = ring_pow k (z:A) r` THEN
  ABBREV_TAC `P = phi r` THEN ABBREV_TAC `R = phi s` THEN
  ABBREV_TAC `q = subfield_generated k {ring_0 k:A}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(eta:A) IN ring_carrier k /\ (w:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eta"; "w"] THEN ASM_SIMP_TAC[RING_POW]; ALL_TAC] THEN
  ABBREV_TAC
   `B = \t. ring_mul k (ring_pow k (eta:A) (t MOD P))
                        (ring_pow k w (t DIV P))` THEN
  SUBGOAL_THEN
   `!j. ?c. ring_pow k (z:A) j =
            ring_sum k {t | t < P * R}
              (\t:num. ring_mul k (ring_of_int k (c t)) (B t))`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `?u v. (s * u + r * v == 1) (mod (r * s))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPECL [`s:num`; `1`; `r:num`] CONG_SOLVE) THEN
      MP_TAC(SPECL [`r:num`; `1`; `s:num`] CONG_SOLVE) THEN
      SUBGOAL_THEN `coprime(s:num,r)` (fun th -> ASM_REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[COPRIME_SYM]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_TAC `v:num`) THEN
      DISCH_THEN(X_CHOOSE_TAC `u:num`) THEN
      MAP_EVERY EXISTS_TAC [`u:num`; `v:num`] THEN
      MATCH_MP_TAC(NUMBER_RULE
       `!r s u v. coprime(r,s) /\ (s * u == 1) (mod r) /\
                  (r * v == 1) (mod s)
                  ==> (s * u + r * v == 1) (mod (r * s))`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_pow k (z:A) j = ring_mul k (ring_pow k eta (u * j))
                                       (ring_pow k w (v * j))`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["eta"; "w"] THEN
      ASM_SIMP_TAC[GSYM RING_POW_MUL; GSYM RING_POW_ADD; RING_POW_EQ_GEN;
                   MULT_EQ_0] THEN
      UNDISCH_TAC `(s * u + r * v == 1) (mod (r * s))` THEN
      SPEC_TAC(`r * s:num`,`n:num`) THEN NUMBER_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `w:A`; `s:num`] span_lemma) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num->int` SUBST1_TAC o
      SPEC `v * j:num` o CONJUNCT2) THEN
    MP_TAC(ISPECL [`k:A ring`; `eta:A`; `r:num`] span_lemma) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num->int` SUBST1_TAC o
      SPEC `u * j:num` o CONJUNCT2) THEN
    REWRITE_TAC[ASSUME `phi r = P`; ASSUME `phi s = R`] THEN
    EXISTS_TAC `\t. (a:num->int) (t MOD P) * b (t DIV P)` THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_SUM_MUL_MOD_DIV o
      lhand o snd) THEN
    ASM_SIMP_TAC[RING_MUL; RING_POW; RING_OF_INT] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[RING_OF_INT_MUL] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r (ring_mul r a x) (ring_mul r b y) =
      ring_mul r (ring_mul r a b) (ring_mul r x (y:A))`) THEN
    ASM_SIMP_TAC[RING_OF_INT; RING_POW];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:num->num->int`) THEN
  SUBGOAL_THEN
   `field q /\ ring_homomorphism(q,k) (I:A->A) /\
    (!x. ring_of_int k x IN ring_carrier q) /\ ring_0 q = ring_0 k`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `subfield_generated k {ring_0 k:A} = q`)) THEN
    SIMP_TAC[FIELD_SUBFIELD_GENERATED; RING_HOMOMORPHISM_SUBFIELD_INCLUSION;
             CONJUNCT2 SUBFIELD_GENERATED; ASSUME `field(k:A ring)`] THEN
    MESON_TAC[RING_OF_INT; RING_OF_INT_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. (B:num->A) t IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_SIMP_TAC[RING_MUL; RING_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `free_basis (q,k) I (P * R) (B:num->A)` ASSUME_TAC THENL
   [MATCH_MP_TAC FREE_BASIS_SPANNING_DEGREE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2 o
      GEN_REWRITE_RULE I [free_basis] o check (fun th ->
        concl th = `free_basis (q,k) I (P * R) (\i. ring_pow k (z:A) i)`)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `\t. ring_sum q {i | i < P * R}
            (\i. ring_mul q ((c:num->A) i)
                          (ring_of_int k ((C:num->num->int) i t)))` THEN
    ASM_SIMP_TAC[RING_SUM] THEN
    MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `{i:num | i < P * R}`;
                   `{t:num | t < P * R}`; `c:num->A`;
                   `\i t. ring_of_int k ((C:num->num->int) i t):A`;
                   `B:num->A`] EXTENSION_LINCOMB_SUM) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; I_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`] span_lemma) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; MULT_EQ_0]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP PHI_MULTIPLICATIVE (ASSUME `coprime(r:num,s)`);
              ASSUME `phi r = P`; ASSUME `phi s = R`] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM SUBRING_GENERATED_BY_SUBRING_GENERATED] THEN
  SIMP_TAC[FREE_BASIS_INTEGER_RING_SUBRING_GENERATED;
           SUBRING_SUBRING_GENERATED] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
    is_eq(concl th) &&
    lhs(concl th) = `ring_carrier(subring_generated k {z:A})`)) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(B:num->A) t = ring_pow k z (s * t MOD P + r * t DIV P)`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["B"; "eta"; "w"] THEN
      SIMP_TAC[RING_POW_ADD; RING_POW_MUL; ASSUME `(z:A) IN ring_carrier k`];
      FIRST_ASSUM MATCH_ACCEPT_TAC];
    X_GEN_TAC `a:num->int` THEN
    EXISTS_TAC
     `\t. ring_sum integer_ring {i | i < P * R}
            (\i. ring_mul integer_ring ((a:num->int) i)
                   ((C:num->num->int) i t))` THEN
    MP_TAC(ISPECL [`ring_of_int k:int->A`; `integer_ring`; `k:A ring`;
                   `{i:num | i < P * R}`; `{t:num | t < P * R}`;
                   `a:num->int`; `C:num->num->int`; `B:num->A`]
      EXTENSION_LINCOMB_SUM) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; INTEGER_RING; IN_UNIV;
                 RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `c:num->int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`I:A->A`; `q:A ring`; `k:A ring`; `P:num * R`; `B:num->A`;
                   `\t. ring_of_int k ((c:num->int) t):A`]
      FREE_BASIS_INDEPENDENT) THEN
    ASM_SIMP_TAC[I_THM; RING_OF_INT_EQ_0_CHAR_0]]);;

(* The discriminant of Q(z) for z of order r s with r, s coprime: d_k =      *)
(* d(Q(z^s))^phi(s) d(Q(z^r))^phi(r). This is close to the case of the       *)
(* subfields Q(z^s) and Q(z^r) of NUMBER_FIELD_COMPOSITUM_DISCRIMINANT of    *)
(* ANT/discriminant_compositum.ml (which loads later), whose discriminants   *)
(* are coprime.                                                              *)
let CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM = prove
 (`!(k:A ring) z r s.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = r * s /\ ~(r * s = 0) /\ coprime(r,s) /\
        subfield_generated k {z} = k
        ==> number_field_discriminant k =
            number_field_discriminant
              (subfield_generated k {ring_pow k z s}) pow phi s *
            number_field_discriminant
              (subfield_generated k {ring_pow k z r}) pow phi r`,
  let subfield_lemma = prove
   (`!(k:A ring) z n d.
          number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
          ~(n = 0) /\ d divides n
          ==> free_basis (subfield_generated k {ring_0 k},
                          subfield_generated k {ring_pow k z d}) I
                         (phi(n DIV d)) (\i. ring_pow k (ring_pow k z d) i) /\
              ring_of_int k
                (number_field_discriminant
                   (subfield_generated k {ring_pow k z d})) =
              basis_discriminant
                (subfield_generated k {ring_0 k},
                 subfield_generated k {ring_pow k z d}) I
                (phi(n DIV d)) (\i. ring_pow k (ring_pow k z d) i)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CYCLOTOMIC_FIELD_SUBFIELD_POW) THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_pow k (z:A) d}`;
                   `ring_pow k (z:A) d`; `n DIV d`]
      CYCLOTOMIC_FIELD_INTEGRAL_BASIS) THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_pow k (z:A) d}`;
                   `ring_pow k (z:A) d`; `n DIV d`]
      CYCLOTOMIC_FIELD_FREE_BASIS) THEN
    ASM_REWRITE_TAC[RING_POW_SUBFIELD_GENERATED] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`subfield_generated k {ring_pow k (z:A) d}`; `phi(n DIV d)`;
                   `\i. ring_pow k (ring_pow k (z:A) d) i`]
      NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD) THEN
    ASM_REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num`; `s:num`]
    CYCLOTOMIC_FIELD_PRODUCT_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP RING_OF_INTEGERS_FREE_BASIS_FIELD o
    CONJ (ASSUME `number_field (k:A ring)`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_DISCRIMINANT_BASIS_FIELD o
    CONJ (ASSUME `number_field (k:A ring)`)) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`; `s:num`] subfield_lemma) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`; `r:num`] subfield_lemma) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`; `s:num`]
    CYCLOTOMIC_FIELD_SUBFIELD_POW) THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `r:num * s`; `r:num`]
    CYCLOTOMIC_FIELD_SUBFIELD_POW) THEN
  ASM_SIMP_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `(r * s) DIV s = r /\ (r * s) DIV r = s` (fun th ->
    REWRITE_TAC[th]) THENL
   [ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT];
    ALL_TAC] THEN
  ABBREV_TAC `eta = ring_pow k (z:A) s` THEN
  ABBREV_TAC `w = ring_pow k (z:A) r` THEN
  ABBREV_TAC `P = phi r` THEN ABBREV_TAC `R = phi s` THEN
  ABBREV_TAC `q = subfield_generated k {ring_0 k:A}` THEN
  ABBREV_TAC `K = subfield_generated k {eta:A}` THEN
  ABBREV_TAC `L = subfield_generated k {w:A}` THEN
  ABBREV_TAC
   `B = \t. ring_mul k (ring_pow k (eta:A) (t MOD P))
                        (ring_pow k w (t DIV P))` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(eta:A) IN ring_carrier k /\ (w:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["eta"; "w"] THEN ASM_SIMP_TAC[RING_POW]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN ring_carrier K /\ y IN ring_carrier L
          ==> algebra_trace (q,k) I (ring_mul k x y) =
              ring_mul k (algebra_trace (q,K) I x)
                         (algebra_trace (q,L) I (y:A))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `{eta:A}`; `{w:A}`; `P:num`; `R:num`;
                   `\i. ring_pow k (eta:A) i`; `\i. ring_pow k (w:A) i`;
                   `x:A`; `y:A`] ALGEBRA_TRACE_PRODUCT_BASIS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul q = ring_mul (k:A ring) /\ ring_pow q = ring_pow k /\
    ring_mul K = ring_mul k /\ ring_pow K = ring_pow k /\
    ring_mul L = ring_mul k /\ ring_pow L = ring_pow k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> SUBST1_TAC(SYM(ASSUME t)))
     [`subfield_generated k {ring_0 k:A} = q`;
      `subfield_generated k {eta:A} = K`; `subfield_generated k {w:A} = L`] THEN
    REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. ring_pow k eta i IN ring_carrier K) /\
    (!i. ring_pow k w i IN ring_carrier (L:A ring))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_TAC THENL
     [MP_TAC(ISPECL [`K:A ring`; `eta:A`; `i:num`] RING_POW);
      MP_TAC(ISPECL [`L:A ring`; `w:A`; `i:num`] RING_POW)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `basis_discriminant (q,k) I (P * R) (B:num->A) =
    ring_mul k
      (ring_pow k (basis_discriminant (q,K) I P (\i. ring_pow k eta i)) R)
      (ring_pow k (basis_discriminant (q,L) I R (\i. ring_pow k w i)) P)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`q:A ring`; `P:num`; `R:num`;
      `\i j. algebra_trace (q,K) I
               (ring_mul K (ring_pow k (eta:A) i) (ring_pow k eta j))`;
      `\i j. algebra_trace (q,L) I
               (ring_mul L (ring_pow k (w:A) i) (ring_pow k w j))`]
      RING_DET_KRONECKER_MOD_DIV) THEN
    REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
    ASM_REWRITE_TAC[basis_discriminant] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC RING_DET_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:num`; `u:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `ring_mul k (B t) (B u) =
      ring_mul k (ring_mul k (ring_pow k eta (t MOD P))
                             (ring_pow k eta (u MOD P)))
                 (ring_mul k (ring_pow k w (t DIV P))
                             (ring_pow k (w:A) (u DIV P)))`
    SUBST1_TAC THENL
     [EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul r (ring_mul r a b) (ring_mul r c d) =
        ring_mul r (ring_mul r a c) (ring_mul r b (d:A))`) THEN
      ASM_SIMP_TAC[RING_POW];
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`K:A ring`; `ring_pow k (eta:A) (t MOD P)`;
                       `ring_pow k (eta:A) (u MOD P)`] RING_MUL);
        MP_TAC(ISPECL [`L:A ring`; `ring_pow k (w:A) (t DIV P)`;
                       `ring_pow k (w:A) (u DIV P)`] RING_MUL)] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INTEGER_RULE `!x y:int. (x == y) (mod &0) ==> x = y`) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check
    (fun th -> lhs(concl th) = `ring_char (k:A ring)`)) THEN
  REWRITE_TAC[GSYM RING_OF_INT_EQ; RING_OF_INT_MUL; RING_OF_INT_POW] THEN
  ASM_REWRITE_TAC[]);;

let CYCLOTOMIC_FIELD_DISCRIMINANT = prove
 (`!(k:A ring) z n.
        number_field k /\ z IN ring_carrier k /\
        ring_order k z = n /\ ~(n = 0) /\ subfield_generated k {z} = k
        ==> number_field_discriminant k *
            &(nproduct {p | prime p /\ p divides n}
                       (\p. p EXP (phi n DIV (p - 1)))) =
            (-- &1) pow (phi n DIV 2) * &(n EXP phi n)`,
  let phi_lemma = prove
   (`!q m. prime q /\ q divides m /\ ~(m = 0) ==> (q - 1) divides phi m`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[PHI_EXPAND] THEN
    MP_TAC(ISPECL [`\p. p EXP (index p m - 1) * (p - 1)`;
                   `{p | prime p /\ p divides m}`; `q:num`]
     NPRODUCT_DELETE) THEN
    ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; IN_ELIM_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN MATCH_MP_TAC DIVIDES_LMUL THEN
    REWRITE_TAC[DIVIDES_REFL]) in
  let int_lemma = prove
   (`!p a m (dK:int) (dL:int).
          prime p /\ ~(a = 0) /\ coprime(p,m) /\ ~(m = 0) /\
          dK * &(nproduct {q | prime q /\ q divides p EXP a}
                           (\q. q EXP (phi(p EXP a) DIV (q - 1)))) =
          (-- &1) pow (phi(p EXP a) DIV 2) * &((p EXP a) EXP phi(p EXP a)) /\
          dL * &(nproduct {q | prime q /\ q divides m}
                           (\q. q EXP (phi m DIV (q - 1)))) =
          (-- &1) pow (phi m DIV 2) * &(m EXP phi m)
          ==> (dK pow phi m * dL pow phi(p EXP a)) *
              &(nproduct {q | prime q /\ q divides p EXP a * m}
                         (\q. q EXP (phi(p EXP a * m) DIV (q - 1)))) =
              (-- &1) pow (phi(p EXP a * m) DIV 2) *
              &((p EXP a * m) EXP phi(p EXP a * m))`,
    let pow_lemma = prove
     (`!(g:num->num) e s. FINITE s
                          ==> nproduct s (\x. g x EXP e) = nproduct s g EXP e`,
      GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC[NPRODUCT_CLAUSES; EXP_ONE; MULT_EXP]) in
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `coprime(p EXP a,m) /\ ~(p EXP a = 0)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[COPRIME_LEXP; EXP_EQ_0; PRIME_IMP_NZ]; ALL_TAC] THEN
    ASM_SIMP_TAC[PHI_MULTIPLICATIVE] THEN
    ABBREV_TAC `P = phi(p EXP a)` THEN ABBREV_TAC `R = phi m` THEN
    SUBGOAL_THEN
     `{q | prime q /\ q divides p EXP a * m} =
      {q | prime q /\ q divides p EXP a} UNION {q | prime q /\ q divides m}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
      MESON_TAC[PRIME_DIVPROD_EQ];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NPRODUCT_UNION o
      rand o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `q:num = p` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME]; ALL_TAC] THEN
      ASM_MESON_TAC[PRIME_COPRIME_EQ];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `nproduct {q | prime q /\ q divides p EXP a}
        (\q. q EXP ((P * R) DIV (q - 1))) =
      nproduct {q | prime q /\ q divides p EXP a}
        (\q. q EXP (P DIV (q - 1))) EXP R /\
      nproduct {q | prime q /\ q divides m}
        (\q. q EXP ((P * R) DIV (q - 1))) =
      nproduct {q | prime q /\ q divides m}
        (\q. q EXP (R DIV (q - 1))) EXP P`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_SIMP_TAC[GSYM pow_lemma; FINITE_SPECIAL_DIVISORS] THEN
      SUBGOAL_THEN
       `!d x y. ~(d = 0) /\ d divides x ==> (x * y) DIV d = x DIV d * y`
      ASSUME_TAC THENL
       [REWRITE_TAC[divides] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT];
        ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC NPRODUCT_EQ THEN
      X_GEN_TAC `q:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM EXP_MULT] THEN AP_TERM_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THENL
       [ALL_TAC; GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      MAP_EVERY EXPAND_TAC ["P"; "R"] THEN
      MATCH_MP_TAC phi_lemma THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(-- &1:int) pow ((P * R) DIV 2) =
      ((-- &1) pow (P DIV 2)) pow R * ((-- &1) pow (R DIV 2)) pow P`
    SUBST1_TAC THENL
     [REWRITE_TAC[INT_POW_POW; GSYM INT_POW_ADD] THEN
      REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
      MATCH_MP_TAC(MESON[]
       `(a <=> b) ==> ((if a then x else y):int) = (if b then x else y)`) THEN
      SUBGOAL_THEN `(P = 1 \/ EVEN P) /\ (R = 1 \/ EVEN R)` MP_TAC THENL
       [MAP_EVERY EXPAND_TAC ["P"; "R"] THEN
        REWRITE_TAC[GSYM NOT_ODD; ODD_PHI_EQ] THEN
        MESON_TAC[PHI_1; PHI_2];
        ALL_TAC] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
        GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `c:num` SUBST1_TAC o
        GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
      REWRITE_TAC[ARITH_RULE `(2 * c) * (2 * d) = 2 * (c * 2 * d)`] THEN
      SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
      REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:int. x pow P` o check
      (fun th -> free_in `dL:int` (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x:int. x pow R` o check
      (fun th -> free_in `dK:int` (concl th))) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW; INT_POW_MUL;
                INT_POW_POW] THEN
    REWRITE_TAC[MULT_AC] THEN
    MATCH_ACCEPT_TAC(INT_RING
     `!u v w x s1 a1 s2 m1:int.
        u * v = s1 * a1 ==> w * x = s2 * m1
        ==> (u * w) * v * x = (s1 * s2) * a1 * m1`)) in
  SUBGOAL_THEN
   `!n. ~(n = 0)
        ==> !(k:A ring) z.
              number_field k /\ z IN ring_carrier k /\ ring_order k z = n /\
              subfield_generated k {z} = k
              ==> number_field_discriminant k *
                  &(nproduct {p | prime p /\ p divides n}
                             (\p. p EXP (phi n DIV (p - 1)))) =
                  (-- &1) pow (phi n DIV 2) * &(n EXP phi n)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(LABEL_TAC "ih") THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`k:A ring`; `z:A`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `1`; `1`]
      CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; ARITH_EQ; COPRIME_1; RING_POW_1; PHI_1;
                 INT_POW_1] THEN
    MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DISCRIMINANT_NONZERO) THEN
    SUBGOAL_THEN `{p | prime p /\ p divides 1} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; DIVIDES_ONE] THEN
      MESON_TAC[PRIME_1];
      ASM_REWRITE_TAC[NPRODUCT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV] THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
    MATCH_MP PRIME_FACTOR) THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `a = index p n` THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num`
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(a = 0) /\ ~(m = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[EXP; MULT_CLAUSES]) THEN
      ASM_MESON_TAC[PRIME_COPRIME_EQ];
      ASM_MESON_TAC[MULT_CLAUSES]];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `m = 1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN
    REWRITE_TAC[MULT_CLAUSES] THEN
    SUBGOAL_THEN `?v. a = v + 1` (X_CHOOSE_THEN `v:num` SUBST_ALL_TAC) THENL
     [EXISTS_TAC `a - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `p:num`; `v:num`]
      CYCLOTOMIC_FIELD_DISCRIMINANT_PRIME_POWER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `{q | prime q /\ q divides p EXP (v + 1)} = {p}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `q:num` THEN
      EQ_TAC THENL
       [ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[EXP_ADD; EXP_1] THEN
        MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL]];
      ALL_TAC] THEN
    REWRITE_TAC[NPRODUCT_SING] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    ASM_SIMP_TAC[PHI_PRIMEPOW_ALT; ADD_EQ_0; ARITH_EQ; ADD_SUB] THEN
    SUBGOAL_THEN `(p EXP v * (p - 1)) DIV (p - 1) = p EXP v` SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC DIV_MULT THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(p EXP (v + 1)) EXP (p EXP v * (p - 1)) =
      p EXP (p EXP v * (p * (v + 1) - v - 2) + p EXP v)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_MULT] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `?q. p = q + 2` (CHOOSE_THEN SUBST1_TAC) THENL
       [EXISTS_TAC `p - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(q + 2) - 1 = q + 1`;
                  ARITH_RULE `(q + 2) * (v + 1) - v - 2 = q * v + q + v`] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_POW; INT_POW_ADD; INT_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `coprime(p EXP a,m) /\ p EXP a < p EXP a * m /\ m < p EXP a * m`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COPRIME_LEXP] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
    SUBGOAL_THEN `2 <= p EXP a` MP_TAC THENL
     [TRANS_TAC LE_TRANS `p EXP 1` THEN
      ASM_REWRITE_TAC[EXP_1; LE_EXP] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`~(m = 0)`; `~(m = 1)`] THEN
    SPEC_TAC(`p EXP a`,`x:num`) THEN REPEAT STRIP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      REWRITE_TAC[LT_MULT_LCANCEL];
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m`] THEN
      REWRITE_TAC[LT_MULT_RCANCEL]] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP a`; `m:num`]
    CYCLOTOMIC_FIELD_DISCRIMINANT_COMPOSITUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC int_lemma THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(p EXP a = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ]; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "ih" (fun th -> MP_TAC(MP (MP (SPEC `p EXP a` th)
      (ASSUME `p EXP a < p EXP a * m`)) (ASSUME `~(p EXP a = 0)`)));
    USE_THEN "ih" (fun th -> MP_TAC(MP (MP (SPEC `m:num` th)
      (ASSUME `m < p EXP a * m`)) (ASSUME `~(m = 0)`)))] THEN
  DISCH_THEN MATCH_MP_TAC THENL
   [EXISTS_TAC `ring_pow k (z:A) m` THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP a * m`; `m:num`]
      CYCLOTOMIC_FIELD_SUBFIELD_POW);
    EXISTS_TAC `ring_pow k (z:A) (p EXP a)` THEN
    MP_TAC(ISPECL [`k:A ring`; `z:A`; `p EXP a * m`; `p EXP a`]
      CYCLOTOMIC_FIELD_SUBFIELD_POW)] THEN
  ASM_SIMP_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT]);;
