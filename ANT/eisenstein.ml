(* ========================================================================= *)
(* Eisenstein polynomials: total ramification and the index.                 *)
(*                                                                           *)
(* Let k be a number field with ring of integers O = ring_of_integers k, a   *)
(* an element of k and m a monic integer polynomial of degree n = [k:Q] with *)
(* m(a) = 0 (m(a) = poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m), *)
(* Eisenstein at the prime p: p divides the coefficients m_i, i < n, and p^2 *)
(* does not divide m_0. Then (NUMBER_FIELD_EISENSTEIN):                      *)
(*                                                                           *)
(*  P = (p,a) = ideal_generated O {ring_of_num k p, a} is a prime ideal,     *)
(*  the only prime of O above p, pO = P^n, e(P) = n, f(P) = 1, and           *)
(*  O = Z[a] + pO, that is p does not divide [O : Z[a]]                      *)
(*                   (NUMBER_FIELD_EISENSTEIN_INDEX)                         *)
(*                                                                           *)
(* where e(P) = ramification_index (integer_ring,O) (ring_of_int k) P, f(P)  *)
(* = residue_degree (integer_ring,O) (ring_of_int k) P and Z[a] =            *)
(* subring_generated k {a}. Along the way: n v_P(a) = e(P) and v_P(a) >= 1   *)
(* for every prime P above p, v_P(x) = ideal_valuation O P (ideal_generated  *)
(* O {x}) (NUMBER_FIELD_EISENSTEIN_VALUATION); a is in O and a^n in pO       *)
(* (NUMBER_FIELD_EISENSTEIN_POW); an integer combination of 1, a, ...,       *)
(* a^(n-1) lies in pO only if all its coefficients are divisible by p        *)
(* (NUMBER_FIELD_EISENSTEIN_INDEPENDENT); O = Z[a] + pO                      *)
(* (NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME); an integer prime to p has        *)
(* valuation 0 at the primes above p (IDEAL_VALUATION_RING_OF_INT_COPRIME).  *)
(*                                                                           *)
(* Routes. Valuation: in a^n = -(m_0 + sum_(1<=i<n) m_i a^i) the term m_0 =  *)
(* p u (u prime to p) has valuation exactly e = e(P), the sum lies in        *)
(* P^(e+1) since p is in P^e and a in P, so n v_P(a) = e: otherwise one of   *)
(* the two sides would be in P^(e+1) or P^e with the wrong valuation.        *)
(* Independence: if c_0 + ... + c_(n-1) a^(n-1) is in pO and j is the least  *)
(* index with p not dividing c_j, multiplication by a^(n-1-j) and a^n IN pO  *)
(* give c_j a^(n-1) IN pO SUBSET P^e, while v_P(c_j a^(n-1)) = (n-1) v_P(a)  *)
(* < n v_P(a) = e. Index: so the p^n classes of the c_0 + ... + c_(n-1)      *)
(* a^(n-1) with 0 <= c_i < p in O/pO are distinct, and O/pO has p^n elements *)
(* (RING_OF_INTEGERS_IDEAL_NORM_INTEGER), so every class contains an element *)
(* of Z[a] (SURJECTIVE_IFF_INJECTIVE_GEN). With O = Z[a] + pO the            *)
(* Dedekind-Kummer theorem (DEDEKIND_KUMMER_Q of ANT/dedekind_kummer.ml) for *)
(* m = X^n modulo p gives the factorization.                                 *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (polynomials, integer_mod_ring, ideals,       *)
(* POLY_EXTEND_MONIC_UNIVARIATE), Library/prime.ml, ANT/integral.ml          *)
(* (integral_element), ANT/ideal_arith.ml (ideal powers and                  *)
(* products), ANT/dedekind.ml (ideal_valuation,                              *)
(* DEDEKIND_IN_IDEAL_POW_VALUATION, IDEAL_VALUATION_PRINCIPAL_MUL,           *)
(* IDEAL_VALUATION_PRINCIPAL_POW), ANT/numfield.ml, ANT/ring_of_integers.ml, *)
(* ANT/prime_split.ml (RAMIFICATION_INDEX_PRIME,                             *)
(* NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) and ANT/dedekind_kummer.ml             *)
(* (DEDEKIND_KUMMER_Q, SUBRING_GENERATED_INT_LINCOMB,                        *)
(* SUBRING_GENERATED_INDEX_COPRIME).                                         *)
(* ========================================================================= *)


needs "Library/ringtheory.ml";;
needs "Library/prime.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/integral.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/dedekind_kummer.ml";;

(* ------------------------------------------------------------------------- *)
(* Valuations at the primes above p.                                         *)
(* ------------------------------------------------------------------------- *)

(* For a root a of an Eisenstein polynomial m at p and a prime P above p,   *)
(* deg(m) v_P(a) = e(P): in a^n = -(m_0 + sum_(1<=i<n) m_i a^i) the term    *)
(* m_0 has valuation exactly e(P) and the sum lies in P^(e(P)+1).           *)
let NUMBER_FIELD_EISENSTEIN_VALUATION = prove
 (`!(k:A ring) a m p P.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m) /\
        prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P
        ==> a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
            1 <= ideal_valuation (ring_of_integers k) P
                   (ideal_generated (ring_of_integers k) {a}) /\
            poly_deg integer_ring m *
            ideal_valuation (ring_of_integers k) P
              (ideal_generated (ring_of_integers k) {a}) =
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P`,
  let lemma = prove
   (`!r x y z:A.
        x IN ring_carrier r /\ y IN ring_carrier r /\ z IN ring_carrier r /\
        ring_add r x (ring_add r y z) = ring_0 r
        ==> x = ring_neg r (ring_add r y z) /\
            y = ring_neg r (ring_add r x z)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `ring_0 r:A`)) THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_add r x (ring_add r y z) = ring_0 r
        ==> x = ring_neg r (ring_add r y (z:A))`);
      MATCH_MP_TAC(RING_RULE
       `ring_add r x (ring_add r y z) = ring_0 r
        ==> y = ring_neg r (ring_add r x (z:A))`)] THEN
    ASM_REWRITE_TAC[]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_NONTRIVIAL_RING) THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM; integral_element] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = poly_deg integer_ring (m:(1->num)->int)` THEN
  SUBGOAL_THEN `ring_carrier(ring_of_integers k) subring_of (k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[RING_OF_INTEGERS_SUBRING]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers k) (P:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]; ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_of_num k p = ring_0 (k:A ring))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; INT_OF_NUM_EQ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P = {ring_0 (ring_of_integers k:A ring)})` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ramification_index (integer_ring,ring_of_integers k) (ring_of_int k) P =
    ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k) {ring_of_num k p:A})`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
      RAMIFICATION_INDEX_INTEGER_RING) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RING_OF_NUM_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `e = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A})` THEN
  SUBGOAL_THEN `(ring_of_num k p:A) IN ideal_pow (ring_of_integers k) P e`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ring_of_num k p:A`; `e:num`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; GSYM RING_OF_INT_OF_NUM;
                    RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    ASM_REWRITE_TAC[RING_OF_INT_OF_NUM; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_add k (ring_pow k a n)
      (ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i))) =
    ring_0 (k:A ring)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `ring_0 k:A`)) THEN
    EXPAND_TAC "n" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC POLY_EXTEND_MONIC_UNIVARIATE THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `ring_add k (ring_pow k a 0)
        (ring_sum k {i | i < 0}
           (\i. ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i))) =
      ring_0 (k:A ring)` THEN
    REWRITE_TAC[LT; EMPTY_GSPEC; RING_SUM_CLAUSES; ring_pow] THEN
    ASM_SIMP_TAC[RING_ADD_RZERO; RING_1; GSYM TRIVIAL_RING_10];
    ALL_TAC] THEN
  ABBREV_TAC
   `S = ring_sum k ({i | i < n} DELETE 0)
          (\i. ring_mul k (ring_of_int k (coeff i m))
                 (ring_pow k (a:A) i))` THEN
  SUBGOAL_THEN
   `ring_add k (ring_pow k a n) (ring_add k (ring_of_int k (coeff 0 m)) S) =
    ring_0 (k:A ring)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `ring_0 k:A`)) THEN
    AP_TERM_TAC THEN EXPAND_TAC "S" THEN
    MP_TAC(ISPECL [`k:A ring`;
      `\i. ring_mul k (ring_of_int k (coeff i (m:(1->num)->int)))
                      (ring_pow k (a:A) i)`;
      `{i:num | i < n}`; `0`] RING_SUM_DELETE) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; LT_NZ; RING_MUL; RING_OF_INT;
                 RING_POW] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ring_pow] THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_OF_INT] THEN
    MATCH_MP_TAC(RING_RULE `ring_add r x (ring_sub r y x) = (y:A)`) THEN
    ASM_SIMP_TAC[RING_OF_INT; RING_SUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> ring_mul k (ring_of_int k (coeff i m)) (ring_pow k a i) IN
            ideal_generated (ring_of_integers k) {ring_of_num k p:A}`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `(divides):int->int->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[int_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:int` SUBST1_TAC) THEN
    MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
    REWRITE_TAC[ring_divides; RING_OF_INTEGERS] THEN
    REWRITE_TAC[RING_OF_INT_MUL; GSYM RING_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                 RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    EXISTS_TAC `ring_mul k (ring_of_int k t) (ring_pow k a i):A` THEN
    ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                 RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul r (ring_mul r x y) z = ring_mul r x (ring_mul r y (z:A))`) THEN
    ASM_SIMP_TAC[RING_OF_INT; RING_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_generated (ring_of_integers k) {ring_of_num k p:A} SUBSET P`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_of_int k (coeff 0 m) IN (P:A->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ideal_generated:(A ring)->(A->bool)->A->bool`))
          (concl th))) THEN
    ASM_REWRITE_TAC[LT_NZ; ring_pow] THEN
    ASM_SIMP_TAC[RING_MUL_RID; RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A) IN P` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
      lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                   RING_OF_INT_IN_RING_OF_INTEGERS];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_comb(concl th) && rand(concl th) = `P:A->bool`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_int k (coeff 0 m) IN ring_carrier(ring_of_integers k) /\
    (S:A) IN ring_carrier(ring_of_integers k) /\
    ring_pow k a n IN ring_carrier(ring_of_integers k)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IN_SUBRING_POW; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    ASM_MESON_TAC[PRIME_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_int k (coeff 0 m) IN ring_carrier k /\
    (S:A) IN ring_carrier k /\ ring_pow k a n IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN P` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `a:A`; `n:num`]
      RING_POW_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_pow k a n:A`;
     `ring_of_int k (coeff 0 m):A`; `S:A`] lemma) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ring_add k (ring_of_int k (coeff 0 m)) (S:A)`]
      IN_RING_IDEAL_NEG) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ring_of_int k (coeff 0 m):A`; `S:A`]
      IN_RING_IDEAL_ADD) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:A) IN ideal_pow (ring_of_integers k) P (e + 1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
      lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                   RING_OF_INT_IN_RING_OF_INTEGERS];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `(divides):int->int->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[int_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:int` SUBST1_TAC) THEN
    SUBGOAL_THEN
     `ring_mul k (ring_of_int k (&p * t)) (ring_pow k a i) =
      ring_mul k a (ring_mul k (ring_of_num k p)
        (ring_mul k (ring_of_int k t) (ring_pow k a (i - 1)))):A`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `i = SUC(i - 1)`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th])
      THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ring_pow; RING_OF_INT_MUL; GSYM RING_OF_INT_OF_NUM] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul r (ring_mul r p t) (ring_mul r a x) =
        ring_mul r a (ring_mul r p (ring_mul r t (x:A)))`) THEN
      ASM_SIMP_TAC[RING_OF_INT; RING_POW];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD1; IDEAL_POW_SUC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ideal_pow (ring_of_integers k) P e:A->bool`; `a:A`;
                   `ring_mul k (ring_of_num k p)
                      (ring_mul k (ring_of_int k t)
                         (ring_pow k a (i - 1))):A`]
      RING_MUL_IN_IDEAL_PROD) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_of_int k t) (ring_pow k a (i - 1)):A IN
      ring_carrier(ring_of_integers k)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                   RING_OF_INT_IN_RING_OF_INTEGERS];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                     `ideal_pow (ring_of_integers k) P e:A->bool`;
                     `ring_of_num k p:A`;
                     `ring_mul k (ring_of_int k t)
                        (ring_pow k a (i - 1)):A`]
        IN_RING_IDEAL_RMUL) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW];
      MATCH_MP_TAC IN_SUBRING_MUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_RING_OF_INTEGERS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u. coeff 0 (m:(1->num)->int) = &p * u /\ ~(&p divides u)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `(divides):int->int->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[LT_NZ; int_divides] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:int` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&p pow 2 divides coeff 0 (m:(1->num)->int))` THEN
    ASM_REWRITE_TAC[INT_POW_2; CONTRAPOS_THM] THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u:int = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((&p:int) divides &0)` THEN
    REWRITE_TAC[INTEGER_RULE `!d:int. d divides &0`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(ring_of_int k u:A = ring_0 k) /\ ~(ring_of_int k u:A IN P)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RING_OF_INT_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(fun th ->
      REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k)
         {ring_of_int k (coeff 0 m):A}) = e`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INT_MUL; GSYM RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ring_of_int k (&p):A`; `ring_of_int k u:A`]
      IDEAL_VALUATION_PRINCIPAL_MUL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    ASM_REWRITE_TAC[RING_OF_INT_OF_NUM] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `y = 0 ==> e + y = e`) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ideal_generated (ring_of_integers k) {ring_of_int k u:A}`]
      IDEAL_VALUATION_EQ_0) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0;
                    RING_OF_INTEGERS; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(ring_of_int k u:A IN P)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_IDEAL_GENERATED_SELF; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_of_int k (coeff 0 m) = ring_0 (k:A ring))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; INT_ENTIRE; INT_OF_NUM_EQ;
                 PRIME_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a = ring_0 (k:A ring))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `ring_pow k a n = ring_0 (k:A ring) /\ S = ring_0 k`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[RING_POW_ZERO] THEN EXPAND_TAC "S" THEN
      MATCH_MP_TAC RING_SUM_EQ_0 THEN
      REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[RING_POW_ZERO; RING_MUL_RZERO; RING_OF_INT];
      ALL_TAC] THEN
    UNDISCH_TAC `~(ring_of_int k (coeff 0 m) = ring_0 (k:A ring))` THEN
    REWRITE_TAC[] THEN
    UNDISCH_TAC
     `ring_add k (ring_pow k a n) (ring_add k (ring_of_int k (coeff 0 m)) S) =
      ring_0 (k:A ring)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_ADD_RZERO; RING_0; RING_OF_INT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `w = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {a:A})` THEN
  SUBGOAL_THEN `1 <= w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `a:A`; `1`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; IDEAL_POW_1];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ideal_valuation (ring_of_integers k) P
      (ideal_generated (ring_of_integers k) {ring_pow k a n:A}) = n * w`
  ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `a:A`; `n:num`]
      IDEAL_VALUATION_PRINCIPAL_POW) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_pow k a n = ring_0 (k:A ring))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `a:A`; `n:num`]
      INTEGRAL_DOMAIN_POW_EQ_0) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; DEDEKIND_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x j. x IN ring_carrier(ring_of_integers k) /\ ~(x = ring_0 k)
          ==> (x IN ideal_pow (ring_of_integers k) P j <=>
               j <= ideal_valuation (ring_of_integers k) P
                      (ideal_generated (ring_of_integers k) {x:A}))`
  (LABEL_TAC "mem") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_IN_IDEAL_POW_VALUATION THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `ring_pow k (a:A) n IN ideal_pow (ring_of_integers k) P (e + 1)`
    ASSUME_TAC THENL
     [USE_THEN "mem" (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_of_int k (coeff 0 m):A IN
      ideal_pow (ring_of_integers k) P (e + 1)`
    MP_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `ring_pow k a n:A`;
       `ring_of_int k (coeff 0 m):A`; `S:A`] lemma) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                     `ideal_pow (ring_of_integers k) P (e + 1):A->bool`;
                     `ring_add k (ring_pow k a n) (S:A)`]
        IN_RING_IDEAL_NEG) THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                     `ideal_pow (ring_of_integers k) P (e + 1):A->bool`;
                     `ring_pow k a n:A`; `S:A`]
        IN_RING_IDEAL_ADD) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW] THEN SIMP_TAC[];
      USE_THEN "mem" (fun th -> ASM_SIMP_TAC[th]) THEN ARITH_TAC];
    SUBGOAL_THEN
     `ring_pow k (a:A) n IN ideal_pow (ring_of_integers k) P e`
    MP_TAC THENL
     [ALL_TAC;
      USE_THEN "mem" (fun th -> ASM_SIMP_TAC[th]) THEN ASM_ARITH_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_pow k a n:A`;
     `ring_of_int k (coeff 0 m):A`; `S:A`] lemma) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN
     `(S:A) IN ideal_pow (ring_of_integers k) P e /\
      ring_of_int k (coeff 0 m) IN ideal_pow (ring_of_integers k) P e`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `e:num`;
                       `e + 1`] IDEAL_POW_ANTIMONO) THEN
        ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET; ARITH_RULE `e <= e + 1`] THEN
        ASM SET_TAC[];
        USE_THEN "mem" (fun th -> ASM_SIMP_TAC[th; LE_REFL])];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ideal_pow (ring_of_integers k) P e:A->bool`;
                   `ring_add k (ring_of_int k (coeff 0 m)) (S:A)`]
      IN_RING_IDEAL_NEG) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ideal_pow (ring_of_integers k) P e:A->bool`;
                   `ring_of_int k (coeff 0 m):A`; `S:A`]
      IN_RING_IDEAL_ADD) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW] THEN SIMP_TAC[]]);;

(* A root a of a monic integer polynomial whose lower coefficients are all  *)
(* divisible by p has a^deg(m) in pO.                                        *)
let NUMBER_FIELD_EISENSTEIN_POW = prove
 (`!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m)
        ==> a IN ring_carrier(ring_of_integers k) /\
            ring_pow k a (poly_deg integer_ring m) IN
            ideal_generated (ring_of_integers k) {ring_of_num k p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM; integral_element] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]] THEN
  ABBREV_TAC `n = poly_deg integer_ring (m:(1->num)->int)` THEN
  SUBGOAL_THEN `ring_carrier(ring_of_integers k) subring_of (k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[RING_OF_INTEGERS_SUBRING]; ALL_TAC] THEN
  ABBREV_TAC
   `S = ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (coeff i m))
                 (ring_pow k (a:A) i))` THEN
  SUBGOAL_THEN `(S:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC IN_SUBRING_SUM THEN
    ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                 RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow k a n = ring_neg k (S:A)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `ring_of_int k:int->A`;
                   `a:A`; `m:(1->num)->int`] POLY_EXTEND_MONIC_UNIVARIATE) THEN
    ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_0 r = ring_add r x y ==> x = ring_neg r (y:A)`) THEN
    ASM_SIMP_TAC[RING_POW] THEN ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                 `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`;
                 `S:A`] IN_RING_IDEAL_NEG) THEN
  REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED] THEN
  DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "S" THEN
  W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
    lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                 RING_OF_INT_IN_RING_OF_INTEGERS];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUM THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IN_ELIM_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `(divides):int->int->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:int` SUBST1_TAC) THEN
  MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
  REWRITE_TAC[ring_divides; RING_OF_INTEGERS] THEN
  REWRITE_TAC[RING_OF_INT_MUL; GSYM RING_OF_INT_OF_NUM] THEN
  ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
               RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  EXISTS_TAC `ring_mul k (ring_of_int k t) (ring_pow k a i):A` THEN
  ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
               RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  MATCH_MP_TAC(RING_RULE
   `ring_mul r (ring_mul r x y) z = ring_mul r x (ring_mul r y (z:A))`) THEN
  ASM_SIMP_TAC[RING_OF_INT; RING_POW] THEN
  ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]);;

(* An integer prime to p has valuation 0 at every prime above p.             *)
let IDEAL_VALUATION_RING_OF_INT_COPRIME = prove
 (`!(k:A ring) P p u.
        number_field k /\ prime p /\
        prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
        ~(&p divides u)
        ==> ~(ring_of_int k u = ring_0 k) /\
            ideal_valuation (ring_of_integers k) P
              (ideal_generated (ring_of_integers k) {ring_of_int k u}) = 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `~(u:int = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((&p:int) divides &0)` THEN
    REWRITE_TAC[INTEGER_RULE `!d:int. d divides &0`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0] THEN
  SUBGOAL_THEN `~(ring_of_int k u:A IN P)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
      RING_OF_INT_IN_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(fun th ->
      REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_of_num k p = ring_0 (k:A ring))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; INT_OF_NUM_EQ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                 `ideal_generated (ring_of_integers k) {ring_of_int k u:A}`]
    IDEAL_VALUATION_EQ_0) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
               IDEAL_GENERATED_EQ_0; RING_OF_INTEGERS;
               RING_OF_INT_IN_RING_OF_INTEGERS; RING_OF_INT_EQ_0_CHAR_0] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(ring_of_int k u:A IN P)` THEN
  REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[IN_IDEAL_GENERATED_SELF; RING_OF_INT_IN_RING_OF_INTEGERS]);;

(* For an Eisenstein root a, an integer combination of 1, a, ..., a^(n-1)  *)
(* in pO has all coefficients divisible by p: for the least index j with p  *)
(* not dividing c_j, multiplication by a^(n-1-j) gives c_j a^(n-1) in pO,   *)
(* of valuation (n-1) v_P(a) < n v_P(a) = v_P(p).                           *)
let NUMBER_FIELD_EISENSTEIN_INDEPENDENT = prove
 (`!(k:A ring) a m p c.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m) /\
        ring_sum k {i | i < poly_deg integer_ring m}
          (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN
        ideal_generated (ring_of_integers k) {ring_of_num k p}
        ==> !i. i < poly_deg integer_ring m ==> &p divides c i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  SUBGOAL_THEN `ring_carrier(ring_of_integers k) subring_of (k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[RING_OF_INTEGERS_SUBRING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`]
    NUMBER_FIELD_EISENSTEIN_POW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC o CONJUNCT1 o
    CONJUNCT2) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`; `P:A->bool`]
    NUMBER_FIELD_EISENSTEIN_VALUATION) THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`]
    NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
    RAMIFICATION_INDEX_PRIME) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = poly_deg integer_ring (m:(1->num)->int)` THEN
  ABBREV_TAC
   `w = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {a:A})` THEN
  ABBREV_TAC
   `e = ideal_valuation (ring_of_integers k) P
          (ideal_generated (ring_of_integers k) {ring_of_num k p:A})` THEN
  SUBGOAL_THEN `~(ring_of_num k p = ring_0 (k:A ring))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; INT_OF_NUM_EQ; PRIME_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(P = {ring_0 (ring_of_integers k:A ring)})` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ring_of_num k p:A) IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_generated (ring_of_integers k) {ring_of_num k p:A} SUBSET
    ideal_pow (ring_of_integers k) P e`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`;
                   `e:num`] DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0;
                    RING_OF_INTEGERS; LE_REFL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [MESON[] `(!i:num. P i) <=> ~(?i. ~P i)`] THEN
  REWRITE_TAC[NOT_IMP] THEN ONCE_REWRITE_TAC[num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (LABEL_TAC "min"))) THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `p:num`; `(c:num->int) j`]
    IDEAL_VALUATION_RING_OF_INT_COPRIME) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_mul k (ring_of_int k ((c:num->int) j)) (ring_pow k a (n - 1)):A IN
    ideal_generated (ring_of_integers k) {ring_of_num k p}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!i. ring_mul k (ring_of_int k ((c:num->int) i))
            (ring_pow k a (i + (n - 1 - j))):A IN
          ring_carrier(ring_of_integers k)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                   RING_OF_INT_IN_RING_OF_INTEGERS];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_sum k {i | i < n}
        (\i. ring_mul k (ring_of_int k ((c:num->int) i))
               (ring_pow k a (i + (n - 1 - j)))) IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}`
    ASSUME_TAC THENL
     [SUBGOAL_THEN
       `ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                 (ring_pow k a (i + (n - 1 - j)))) =
        ring_mul k (ring_pow k a (n - 1 - j))
          (ring_sum k {i | i < n}
             (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k (a:A) i)))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM RING_SUM_LMUL; FINITE_NUMSEG_LT; RING_MUL;
                     RING_OF_INT; RING_POW] THEN
        MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        ASM_SIMP_TAC[RING_POW_ADD] THEN
        MATCH_MP_TAC(RING_RULE
         `ring_mul r c (ring_mul r x y) =
          ring_mul r y (ring_mul r c (x:A))`) THEN
        ASM_SIMP_TAC[RING_OF_INT; RING_POW];
        MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                       `ideal_generated (ring_of_integers k)
                          {ring_of_num k p:A}`;
                       `ring_pow k a (n - 1 - j):A`;
                       `ring_sum k {i | i < n}
                          (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                                 (ring_pow k (a:A) i))`]
          IN_RING_IDEAL_LMUL) THEN
        ASM_SIMP_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                     IN_SUBRING_POW]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_sum k ({i | i < n} DELETE j)
        (\i. ring_mul k (ring_of_int k ((c:num->int) i))
               (ring_pow k a (i + (n - 1 - j)))) IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}`
    ASSUME_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
        lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC IN_RING_IDEAL_SUM THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IN_DELETE; IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num < j` THENL
       [USE_THEN "min" (MP_TAC o C MP (ASSUME `i:num < j`) o SPEC `i:num`) THEN
        ASM_REWRITE_TAC[int_divides] THEN
        DISCH_THEN(X_CHOOSE_THEN `t:int` SUBST1_TAC) THEN
        MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
        REWRITE_TAC[ring_divides; RING_OF_INTEGERS] THEN
        REWRITE_TAC[RING_OF_INT_MUL; GSYM RING_OF_INT_OF_NUM] THEN
        ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                     RING_OF_INT_IN_RING_OF_INTEGERS] THEN
        EXISTS_TAC
         `ring_mul k (ring_of_int k t) (ring_pow k a (i + (n - 1 - j))):A` THEN
        ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                     RING_OF_INT_IN_RING_OF_INTEGERS] THEN
        MATCH_MP_TAC(RING_RULE
         `ring_mul r (ring_mul r x y) z =
          ring_mul r x (ring_mul r y (z:A))`) THEN
        ASM_SIMP_TAC[RING_OF_INT; RING_POW];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_pow k a (i + (n - 1 - j)) =
        ring_mul k (ring_pow k a n) (ring_pow k (a:A) (i - j - 1))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM RING_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                     `ideal_generated (ring_of_integers k)
                        {ring_of_num k p:A}`;
                     `ring_of_int k ((c:num->int) i):A`;
                     `ring_mul k (ring_pow k a n)
                        (ring_pow k (a:A) (i - j - 1))`]
        IN_RING_IDEAL_LMUL) THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                     `ideal_generated (ring_of_integers k)
                        {ring_of_num k p:A}`;
                     `ring_pow k a n:A`; `ring_pow k (a:A) (i - j - 1)`]
        IN_RING_IDEAL_RMUL) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                   IN_SUBRING_POW; RING_OF_INT_IN_RING_OF_INTEGERS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`;
      `\i. ring_mul k (ring_of_int k ((c:num->int) i))
                      (ring_pow k (a:A) (i + (n - 1 - j)))`;
      `{i:num | i < n}`; `j:num`] RING_SUM_DELETE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_OF_INT;
                   RING_POW];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `j + (n - 1 - j) = n - 1` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ideal_generated (ring_of_integers k) {ring_of_num k p:A}`;
                   `ring_sum k {i | i < n}
                      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                             (ring_pow k (a:A) (i + (n - 1 - j))))`;
                   `ring_sum k ({i | i < n} DELETE j)
                      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                             (ring_pow k (a:A) (i + (n - 1 - j))))`]
      IN_RING_IDEAL_SUB) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED] THEN
    MATCH_MP_TAC(MESON[] `(a:A) = b ==> a IN s ==> b IN s`) THEN
    MATCH_MP_TAC(RING_RULE `ring_sub r y (ring_sub r y x) = (x:A)`) THEN
    ASM_SIMP_TAC[RING_SUM; RING_MUL; RING_OF_INT; RING_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(ring_pow k a (n - 1) = ring_0 (k:A ring)) /\
    ~(ring_mul k (ring_of_int k ((c:num->int) j)) (ring_pow k a (n - 1)) =
      ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`;
                   `ring_of_int k ((c:num->int) j):A`;
                   `ring_pow k a (n - 1):A`] INTEGRAL_DOMAIN_MUL_EQ_0) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `a:A`; `n - 1`]
      INTEGRAL_DOMAIN_POW_EQ_0) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; DEDEKIND_IMP_INTEGRAL_DOMAIN;
                 IN_SUBRING_POW; RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `e <= ideal_valuation (ring_of_integers k) P
           (ideal_generated (ring_of_integers k)
              {ring_mul k (ring_of_int k ((c:num->int) j))
                 (ring_pow k a (n - 1)):A})`
  MP_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `ring_mul k (ring_of_int k ((c:num->int) j))
                      (ring_pow k a (n - 1)):A`; `e:num`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS; IN_SUBRING_MUL; IN_SUBRING_POW;
                 RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_comb(concl th) && is_comb(rator(concl th)) &&
      fst(dest_const(fst(strip_comb(concl th)))) = "SUBSET")) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                 `ring_of_int k ((c:num->int) j):A`; `ring_pow k a (n - 1):A`]
    IDEAL_VALUATION_PRINCIPAL_MUL) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `a:A`; `n - 1`]
    IDEAL_VALUATION_PRINCIPAL_POW) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS; IN_SUBRING_POW;
               RING_OF_INT_IN_RING_OF_INTEGERS] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `n = SUC(n - 1)` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n = SUC(n - 1)`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th' ->
      is_eq(concl th') && lhs(concl th') = `n * w:num`)) THEN
    SUBST1_TAC th) THEN
  REWRITE_TAC[MULT_CLAUSES; SUC_SUB1] THEN ASM_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The index and the factorization of p.                                     *)
(* ------------------------------------------------------------------------- *)

(* For an Eisenstein root a with deg m = [k:Q], p does not divide the index *)
(* of Z[a] in O: the classes of the c_0 + c_1 a + ... + c_(n-1) a^(n-1)    *)
(* with 0 <= c_i < p in O/pO are distinct (NUMBER_FIELD_EISENSTEIN_        *)
(* INDEPENDENT) and there are p^n of them, as many as O/pO has elements.   *)
let NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME = prove
 (`!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m)
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `n = poly_deg integer_ring (m:(1->num)->int)` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `n:num`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
  SUBGOAL_THEN `ring_carrier(ring_of_integers k) subring_of (k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[RING_OF_INTEGERS_SUBRING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN ring_carrier(ring_of_integers k) ==> x IN ring_carrier k`
  (LABEL_TAC "sub") THENL
   [MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`]
    NUMBER_FIELD_EISENSTEIN_POW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`]
    SUBRING_GENERATED_INT_LINCOMB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`]
    NUMBER_FIELD_EISENSTEIN_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ind") THEN
  ABBREV_TAC
   `J = ideal_generated (ring_of_integers k) {ring_of_num k p:A}` THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers k) (J:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. ring_sum k {i | i < n}
          (\i. ring_mul k (ring_of_int k (c i)) (ring_pow k a i)) IN
        ring_carrier(ring_of_integers k:A ring)`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC IN_SUBRING_SUM THEN
    ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_POW;
                 RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool))
    HAS_SIZE p EXP n`
  ASSUME_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "J" THEN
      REWRITE_TAC[GSYM RING_OF_INT_OF_NUM] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s:A->bool. ring_of_int k (&p):A IN s`) THEN
      REWRITE_TAC[IN_IDEAL_GENERATED_SELF; IN_SING;
                  RING_OF_INT_IN_RING_OF_INTEGERS] THEN
      ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0; INT_OF_NUM_EQ; PRIME_IMP_NZ];
      MP_TAC(ISPECL [`k:A ring`; `&p:int`]
        RING_OF_INTEGERS_IDEAL_NORM_INTEGER) THEN
      ASM_SIMP_TAC[INT_OF_NUM_EQ; PRIME_IMP_NZ; RING_OF_INT_OF_NUM;
                   INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
      REWRITE_TAC[ideal_norm]];
    ALL_TAC] THEN
  ABBREV_TAC
   `D = {c:num->int | (!i. i IN {i | i < n} ==> c i IN IMAGE (&) {j | j < p}) /\
                      (!i. ~(i IN {i | i < n}) ==> c i = &0)}` THEN
  SUBGOAL_THEN `(D:(num->int)->bool) HAS_SIZE p EXP n` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN
    REWRITE_TAC[HAS_SIZE_NUMSEG_LT] THEN
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC[HAS_SIZE_NUMSEG_LT; INT_OF_NUM_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`D:(num->int)->bool`;
    `ring_carrier(quotient_ring (ring_of_integers k) (J:A->bool))`;
    `\c:num->int. ring_coset (ring_of_integers k) J
                    (ring_sum k {i | i < n}
                       (\i. ring_mul k (ring_of_int k (c i))
                              (ring_pow k (a:A) i)))`]
   SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->int` THEN DISCH_TAC THEN
    EXISTS_TAC `ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                       (ring_pow k (a:A) i))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`c:num->int`; `d:num->int`] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "c2"))
     (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 (LABEL_TAC "d1") (LABEL_TAC "d2")) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `J:A->bool`;
      `ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                (ring_pow k (a:A) i))`;
      `ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((d:num->int) i))
                (ring_pow k (a:A) i))`] RING_COSET_EQ) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num < n` THENL
     [ALL_TAC; USE_THEN "c2" (MP_TAC o SPEC `i:num`) THEN
      USE_THEN "d2" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]] THEN
    USE_THEN "ind" (MP_TAC o SPEC `\i. (c:num->int) i - d i`) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "J" THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th ->
        can (find_term ((=) `J:A->bool`)) (concl th) &&
        can (find_term ((=) `ring_sub:(A ring)->A->A->A`)) (concl th))) THEN
      EXPAND_TAC "J" THEN
      MATCH_MP_TAC(MESON[] `(a:A) = b ==> a IN s ==> b IN s`) THEN
      SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
       [USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM RING_SUM_SUB; FINITE_NUMSEG_LT; RING_MUL;
                   RING_OF_INT; RING_POW] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[RING_OF_INT_SUB] THEN
      ASM_SIMP_TAC[RING_SUB_RDISTRIB; RING_OF_INT; RING_POW];
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[]] THEN
    USE_THEN "c1" (MP_TAC o C MP (ASSUME `i:num < n`) o SPEC `i:num`) THEN
    USE_THEN "d1" (MP_TAC o C MP (ASSUME `i:num < n`) o SPEC `i:num`) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
    MP_TAC(SPEC `u:num` INT_POS) THEN MP_TAC(SPEC `v:num` INT_POS) THEN
    UNDISCH_TAC `u:num < p` THEN UNDISCH_TAC `v:num < p` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[ring_setadd; EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
  EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_ADD) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
      MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `ring_coset (ring_of_integers k) J (x:A)`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->int` (STRIP_ASSUME_TAC o BETA_RULE)) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `J:A->bool`;
    `ring_sum k {i | i < n}
       (\i. ring_mul k (ring_of_int k ((c:num->int) i))
              (ring_pow k (a:A) i))`; `x:A`] RING_COSET_EQ) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_TAC THEN
  EXISTS_TAC
   `ring_sum k {i | i < n}
      (\i. ring_mul k (ring_of_int k ((c:num->int) i))
             (ring_pow k (a:A) i))` THEN
  EXISTS_TAC
   `ring_sub k x
      (ring_sum k {i | i < n}
         (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                (ring_pow k (a:A) i)))` THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `c:num->int` THEN REWRITE_TAC[IN_UNIV];
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `J:A->bool`;
      `ring_sub k
         (ring_sum k {i | i < n}
            (\i. ring_mul k (ring_of_int k ((c:num->int) i))
                   (ring_pow k (a:A) i))) x`] IN_RING_IDEAL_NEG) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
    MATCH_MP_TAC(MESON[] `(a:A) = b ==> a IN s ==> b IN s`) THEN
    MATCH_MP_TAC(RING_RULE
     `ring_neg r (ring_sub r y x) = ring_sub r x (y:A)`) THEN
    CONJ_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(RING_RULE `ring_add r y (ring_sub r x y) = (x:A)`) THEN
    CONJ_TAC THEN USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Eisenstein: for a root a of an Eisenstein polynomial m at p with         *)
(* deg m = [k:Q], p is totally ramified in k: pO = P^n for the prime        *)
(* P = (p,a) with e(P) = n and f(P) = 1, P is the only prime above p, and p *)
(* does not divide the index of Z[a] in O, so that O = Z[a] + pO. With      *)
(* NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME this is the Dedekind-Kummer        *)
(* theorem for m = X^n modulo p.                                             *)
let NUMBER_FIELD_EISENSTEIN = prove
 (`!(k:A ring) a m p.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m)
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) /\
            {P | prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P} =
            {ideal_generated (ring_of_integers k) {ring_of_num k p, a}} /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a})
              (poly_deg integer_ring m) /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) =
            poly_deg integer_ring m /\
            residue_degree (integer_ring,ring_of_integers k) (ring_of_int k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, a}) =
            1 /\
            ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`]
    NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = poly_deg integer_ring (m:(1->num)->int)` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `n:num`)) THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_DEGREE_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `field(integer_mod_ring p)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FIELD_INTEGER_MOD_RING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
      (poly_var (integer_mod_ring p) one) = (a:A)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `poly_var (integer_mod_ring p) one = poly_var integer_ring one`
    SUBST1_TAC THENL
     [REWRITE_TAC[poly_var; INTEGER_MOD_RING_CLAUSES; INTEGER_RING] THEN
      SUBGOAL_THEN `&1 rem &p = &1` (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[INT_REM_EQ_SELF; INT_ABS_NUM; INT_OF_NUM_LT; INT_POS;
                  INT_OF_NUM_EQ] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      MATCH_MP_TAC POLY_EXTEND_VAR THEN
      ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_int (integer_mod_ring p) o (m:(1->num)->int) =
    poly_pow (integer_mod_ring p) (poly_var (integer_mod_ring p) one) n`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FUN_EQ_COEFF; COEFF_COMPOSE; COEFF_POLY_VARPOW] THEN
    X_GEN_TAC `d:num` THEN
    ASM_CASES_TAC `d:num < n` THENL
     [SUBGOAL_THEN `~(d:num = n)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[RING_OF_INT_EQ_0; INTEGER_MOD_RING_CHAR] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `d:num = n` THENL
     [UNDISCH_TAC `monic integer_ring (m:(1->num)->int)` THEN
      ASM_REWRITE_TAC[monic; INTEGER_RING] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RING_OF_INT_1];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`integer_ring`; `m:(1->num)->int`; `d:num`]
      COEFF_ABOVE_DEG) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INTEGER_RING] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[RING_OF_INT_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`k:A ring`; `a:A`; `p:num`; `m:(1->num)->int`; `{0}`;
    `\i:num. poly_var (integer_mod_ring p) one`; `\i:num. (n:num)`;
    `\i:num. ideal_generated (ring_of_integers k) {ring_of_num k p, a:A}`]
   DEDEKIND_KUMMER_Q) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_SING; IN_SING] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR;
                  MONIC_POLY_VAR] THEN
      MATCH_MP_TAC RING_IRREDUCIBLE_POLY_VAR THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; IN_UNIV];
      MESON_TAC[];
      SUBGOAL_THEN
       `ring_pow (poly_ring (integer_mod_ring p) (:1))
          (poly_var (integer_mod_ring p) one) n IN
        ring_carrier(poly_ring (integer_mod_ring p) (:1))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC RING_POW THEN
        REWRITE_TAC[GSYM RING_POLYNOMIAL; RING_POLYNOMIAL_VAR];
        ASM_REWRITE_TAC[RING_PRODUCT_SING] THEN
        REWRITE_TAC[POLY_RING_CLAUSES]]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SING; IMAGE_CLAUSES] THEN
  SIMP_TAC[IDEAL_PRODUCT_SING; RING_IDEAL_IDEAL_POW] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `0`))) THEN
  REWRITE_TAC[POLY_DEG_VAR] THEN
  SUBGOAL_THEN
   `~(ring_1 (integer_mod_ring p) = ring_0 (integer_mod_ring p))`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[FIELD_IMP_NONTRIVIAL_RING; TRIVIAL_RING_10]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* The index form: p does not divide [O : Z[a]].                             *)
let NUMBER_FIELD_EISENSTEIN_INDEX = prove
 (`!(k:A ring) a m p N.
        number_field k /\ a IN ring_carrier k /\
        m IN ring_carrier(poly_ring integer_ring (:1)) /\
        monic integer_ring m /\
        poly_deg integer_ring m =
        extension_degree (subfield_generated k {ring_0 k},k) I /\
        poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m = ring_0 k /\
        prime p /\
        (!i. i < poly_deg integer_ring m ==> &p divides coeff i m) /\
        ~(&p pow 2 divides coeff 0 m) /\
        {ring_coset (ring_of_integers k)
           (ring_carrier(subring_generated k {a})) x |
         x | x IN ring_carrier(ring_of_integers k)} HAS_SIZE N
        ==> ~(p divides N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `p:num`; `N:num`]
    SUBRING_GENERATED_INDEX_COPRIME) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`]
    NUMBER_FIELD_EISENSTEIN_INDEX_COPRIME) THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `m:(1->num)->int`; `p:num`]
    NUMBER_FIELD_EISENSTEIN_POW) THEN
  ASM_SIMP_TAC[]);;
