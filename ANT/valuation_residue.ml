(* ========================================================================= *)
(* Residue fields and decomposition groups of valuation subrings, valuation  *)
(* subrings over a prime p, and the valuation subrings of number fields and  *)
(* of Q-bar. For v a valuation subring of a field k with maximal ideal m of  *)
(* subring_generated k v (ANT/valuation_ring.ml) and residue field kv =      *)
(* quotient_ring (subring_generated k v) m:                                  *)
(*                                                                           *)
(*   k algebraically closed ==> kv algebraically closed                      *)
(*      (VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED)                     *)
(*   field k, ring_char k = 0, prime p ==> some v, m lie over p:             *)
(*      !n. ring_of_int k n IN m <=> &p divides n                            *)
(*      (VALUATION_SUBRING_OVER_PRIME)                                       *)
(*   decomposition_group(k0,k) h m = stabilizer of v, mapping to the         *)
(*      automorphisms of kv over the image of k0 with kernel                 *)
(*      inertia_group(k0,k) h (subring_generated k v) m                      *)
(*      (VALUATION_SUBRING_DECOMPOSITION_GROUP,                              *)
(*       VALUATION_SUBRING_RESIDUE_HOMOMORPHISM)                             *)
(*   number_field k ==> v = {ring_div k a s | a,s |                          *)
(*      a, s IN ring_carrier(ring_of_integers k) /\ ~(s IN m)}               *)
(*      (NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION)                        *)
(*                                                                           *)
(* Over p the residue field has characteristic p                             *)
(* (VALUATION_SUBRING_RESIDUE_CHAR), and for k algebraically closed of       *)
(* characteristic 0 it is an algebraically closed field of characteristic p  *)
(* (ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME). The residue map is           *)
(* DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM (ANT/decomposition.ml) for b =   *)
(* subring_generated k v and Q = m; v is stable only under D, which is all   *)
(* that it and INERTIA_GROUP ask of b.                                       *)
(*                                                                           *)
(* The algebraic integers lie in v (VALUATION_SUBRING_RING_OF_INTEGERS), Q_V *)
(* = m INTER ring_carrier(ring_of_integers k) is a prime of them             *)
(* (VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS), and the constants of    *)
(* ANT/decomposition.ml apply with b = ring_of_integers k and Q = Q_V, with  *)
(* no finiteness (VALUATION_SUBRING_DECOMPOSITION_RESIDUE). At finite        *)
(* levels, for l subfield_of k with number_field(subfield_generated k l), v  *)
(* INTER l is a valuation subring of it with maximal ideal m INTER l         *)
(* (VALUATION_SUBRING_SUBFIELD), the localization of O_L at the prime m      *)
(* INTER O_L, which contains ring_of_int k n exactly when m does             *)
(* (VALUATION_SUBRING_NUMBER_SUBFIELD). For k of characteristic 0 algebraic  *)
(* over its prime subfield (Q-bar, or any algebraic extension of Q):         *)
(*                                                                           *)
(*   v = {a / s | a, s in O_k, s NOTIN m}                                    *)
(*      (ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION)                           *)
(*   kv is algebraic over its prime subfield                                 *)
(*      (ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC)                      *)
(*   D and I at Q_V (b = O_k) equal those at m (b = v)                       *)
(*      (ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA)                  *)
(*                                                                           *)
(* so for Q-bar and p prime there is v over p whose residue field is an      *)
(* algebraic closure of F_p (ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME), the    *)
(* decomposition group at Q_V is the stabilizer of v                         *)
(* (ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP), and it maps to the     *)
(* automorphisms of kv over F_p with kernel the inertia group at Q_V         *)
(* (ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM).                       *)
(*                                                                           *)
(* Routes: a nonconstant polynomial over kv is lifted to v with the same     *)
(* zero pattern, so its leading coefficient is a unit of v; a root in k is   *)
(* integral over v, so in v (VALUATION_SUBRING_INTEGRAL_ELEMENT), and        *)
(* reduces to a root. Over p: the image of Z is a subring (PRIME_SUBRING) on *)
(* which ring_of_int is injective, and the image of pZ is a prime ideal of   *)
(* it (PRIME_INT_DIVPROD_EQ); the Chevalley extension theorem                *)
(* (VALUATION_SUBRING_DOMINATES) gives v and m. Number fields: if Q_V = 0    *)
(* then v = k; otherwise an element of negative Dedekind valuation at Q_V    *)
(* would have an inverse a / b with a in Q_V, so in m                        *)
(* (DEDEKIND_VALUATION_POS). Q-bar: x lies in the number field generated by  *)
(* x (SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC). The residue of a / s is a        *)
(* quotient of residues of algebraic integers (RING_OF_INTEGERS_ALGEBRAIC,   *)
(* ALGEBRAIC_OVER_DIV).                                                      *)
(*                                                                           *)
(* Uses: Library/fieldtheory.ml, Library/galois.ml, ANT/integral.ml,         *)
(* ANT/dedekind_valuation.ml, ANT/valuation_ring.ml, ANT/numfield.ml,        *)
(* ANT/ring_of_integers.ml, ANT/nf_valuation.ml, ANT/relative_split.ml,      *)
(* ANT/decomposition.ml, ANT/nf_decomposition.ml.                            *)
(* ========================================================================= *)

needs "Library/fieldtheory.ml";;
needs "Library/galois.ml";;
needs "ANT/integral.ml";;
needs "ANT/dedekind_valuation.ml";;
needs "ANT/valuation_ring.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/decomposition.ml";;
needs "ANT/nf_decomposition.ml";;

(* ------------------------------------------------------------------------- *)
(* Residue fields of valuation subrings of algebraically closed fields.      *)
(* ------------------------------------------------------------------------- *)

let VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED = prove
 (`!(k:A ring) v m.
        algebraically_closed_field k /\ valuation_subring k v /\
        maximal_ideal (subring_generated k v) m
        ==> algebraically_closed_field
             (quotient_ring (subring_generated k v) m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `ring_carrier(subring_generated k v) = (v:A->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]; ALL_TAC] THEN
  REWRITE_TAC[algebraically_closed_field] THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING] THEN
  X_GEN_TAC `p:(1->num)->(A->bool)` THEN STRIP_TAC THEN
  ABBREV_TAC `R = subring_generated k (v:A->bool)` THEN
  ABBREV_TAC `kq = quotient_ring R (m:A->bool)` THEN
  SUBGOAL_THEN
   `ring_0 R = ring_0 (k:A ring) /\
    ring_carrier kq = {ring_coset R (m:A->bool) a | a IN v} /\
    ring_0 kq = (m:A->bool) /\
    (!a. a IN v ==> (ring_coset R m a = m <=> a IN m))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kq" THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; QUOTIENT_RING_0] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN
      MATCH_MP_TAC RING_COSET_EQ_IDEAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!mon. (p:(1->num)->(A->bool)) mon IN ring_carrier kq`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `(p:(1->num)->(A->bool)) IN
      ring_carrier(poly_ring (kq:(A->bool)ring) (:1))` THEN
    REWRITE_TAC[POLY_RING; IN_ELIM_THM; ring_polynomial; ring_powerseries] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_0 (k:A ring) IN v /\ ring_0 k IN (m:A->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_0; IN_RING_IDEAL_0]; ALL_TAC] THEN
  ABBREV_TAC
   `P = \mon:1->num. if p mon = ring_0 kq then ring_0 k
                     else @a:A. a IN v /\ ring_coset R m a = p mon` THEN
  SUBGOAL_THEN
   `!mon:1->num. (P:(1->num)->A) mon IN v /\
                 ring_coset R m (P mon) = p mon /\
                 (P mon = ring_0 k <=> p mon = ring_0 kq)`
  ASSUME_TAC THENL
   [X_GEN_TAC `mon:1->num` THEN EXPAND_TAC "P" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?a:A. a IN v /\ ring_coset R m a = p(mon:1->num)`
    MP_TAC THENL
     [UNDISCH_TAC `!mon. (p:(1->num)->(A->bool)) mon IN ring_carrier kq` THEN
      DISCH_THEN(MP_TAC o SPEC `mon:1->num`) THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      DISCH_THEN(STRIP_ASSUME_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p:(1->num)->(A->bool)) IN ring_carrier(poly_ring kq (:1)) ==>
    (P:(1->num)->A) IN ring_carrier(poly_ring R (:1)) /\
    P IN ring_carrier(poly_ring k (:1)) /\
    poly_deg R P = poly_deg kq p /\ poly_deg k P = poly_deg kq p`
  MP_TAC THENL
   [REWRITE_TAC[POLY_RING; IN_ELIM_THM; ring_polynomial; ring_powerseries;
                SUBSET_UNIV; poly_deg] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:A->bool) subring_of k` THEN
    REWRITE_TAC[subring_of; SUBSET] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `?x. x IN ring_carrier k /\ poly_eval k (P:(1->num)->A) x = ring_0 k`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `algebraically_closed_field (k:A ring)` THEN
    REWRITE_TAC[algebraically_closed_field] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `n = poly_deg kq (p:(1->num)->(A->bool))` THEN
  SUBGOAL_THEN `~(coeff n (p:(1->num)->(A->bool)) = ring_0 kq)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`kq:(A->bool)ring`; `p:(1->num)->(A->bool)`; `n:num`]
      POLY_DEG_EQ_COEFF_EQ) THEN
    ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `coeff n (P:(1->num)->A) IN v /\ ~(coeff n P IN m) /\
    ring_unit R (coeff n P)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(coeff n (p:(1->num)->(A->bool)) = ring_0 kq)` THEN
    REWRITE_TAC[COEFF] THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o SPEC `(\v:1. n):1->num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `P:(1->num)->A`)) (concl th) &&
      can (find_term ((=) `ring_coset:(A)ring->(A->bool)->A->A->bool`))
          (concl th))) THEN
    MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      STRIP_TAC THEN EXPAND_TAC "R" THEN
      ASM_SIMP_TAC[RING_UNIT_SUBRING_OF_FIELD] THEN
      MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
        VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `maximal_ideal R (m:A->bool)` THEN EXPAND_TAC "R" THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `~((P:(1->num)->A) (\v. n) IN
          {x | x IN v /\ (x = ring_0 k \/ ~(ring_inv k x IN v))})` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONV_TAC TAUT];
    ALL_TAC] THEN
  ABBREV_TAC `y = ring_inv R (coeff n (P:(1->num)->A))` THEN
  SUBGOAL_THEN `(y:A) IN v /\ y IN ring_carrier k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_MESON_TAC[RING_INV; subring_of; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN v` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `x:A`]
      VALUATION_SUBRING_INTEGRAL_ELEMENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[integral_element] THEN
    EXISTS_TAC `poly_mul R (poly_const R y) (P:(1->num)->A)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
      MATCH_MP_TAC RING_POLYNOMIAL_MUL THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL_CONST; RING_POLYNOMIAL];
      UNDISCH_TAC `ring_inv R (coeff n (P:(1->num)->A)) = y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `coeff n (P:(1->num)->A) = coeff (poly_deg R P) P`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONIC_CMUL THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN
      EXPAND_TAC "R" THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_SUBRING_GENERATED;
                   FIELD_IMP_INTEGRAL_DOMAIN];
      SUBGOAL_THEN `ring_homomorphism(R,k) (I:A->A)` ASSUME_TAC THENL
       [EXPAND_TAC "R" THEN
        REWRITE_TAC[REWRITE_RULE[GSYM I_DEF] RING_HOMOMORPHISM_INCLUSION];
        ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_MUL o lhand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[RING_POLYNOMIAL_CONST; RING_POLYNOMIAL];
        DISCH_THEN SUBST1_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) POLY_EXTEND_CONST o
        lhand o lhand o snd) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      SUBGOAL_THEN
       `poly_extend (R,k) I (\v:1. x) (P:(1->num)->A) = poly_eval k P x`
      SUBST1_TAC THENL
       [REWRITE_TAC[poly_eval; poly_evaluate; poly_extend] THEN
        UNDISCH_TAC `ring_0 R = ring_0 (k:A ring)` THEN
        DISCH_THEN SUBST1_TAC THEN REFL_TAC;
        ASM_REWRITE_TAC[I_THM] THEN ASM_SIMP_TAC[RING_MUL_RZERO]]];
    ALL_TAC] THEN
  EXISTS_TAC `ring_coset R m (x:A)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p = ring_coset R m o (P:(1->num)->A)` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `mon:1->num` THEN
    REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:A ring`; `kq:(A->bool)ring`; `x:A`;
                 `ring_coset R (m:A->bool)`; `P:(1->num)->A`]
    POLY_EVAL_HOMOMORPHIC_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "kq" THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN `poly_eval R (P:(1->num)->A) x = ring_0 k` SUBST1_TAC THENL
   [UNDISCH_TAC `poly_eval k (P:(1->num)->A) x = ring_0 k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "R" THEN
    MATCH_MP_TAC POLY_EVAL_SUBRING_GENERATED THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Valuation subrings over a prime.                                          *)
(* ------------------------------------------------------------------------- *)

(* The Chevalley extension theorem applied to the image of Z and the image   *)
(* of pZ.                                                                    *)

let VALUATION_SUBRING_OVER_PRIME = prove
 (`!(k:A ring) p.
        field k /\ ring_char k = 0 /\ prime p
        ==> ?v m. valuation_subring k v /\
                  maximal_ideal (subring_generated k v) m /\
                  !n. ring_of_int k n IN m <=> &p divides n`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a = {ring_of_int (k:A ring) n | n IN (:int)}` THEN
  SUBGOAL_THEN `(a:A->bool) subring_of k` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[PRIME_SUBRING]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_carrier(subring_generated k a) = (a:A->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n n'. ring_of_int k n = ring_of_int (k:A ring) n' <=> n = n'`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RING_OF_INT_EQ] THEN INTEGER_TAC; ALL_TAC] THEN
  ABBREV_TAC `P = {ring_of_int (k:A ring) n | n | &p divides n}` THEN
  SUBGOAL_THEN `!n. ring_of_int (k:A ring) n IN P <=> &p divides n`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `prime_ideal (subring_generated k a) (P:A->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `a = IMAGE (ring_of_int (k:A ring)) (:int) /\
      P = IMAGE (ring_of_int k) {n | &p divides n}`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `{ring_of_int (k:A ring) n | n IN (:int)} = a` THEN
        REWRITE_TAC[SIMPLE_IMAGE; ETA_AX] THEN MESON_TAC[];
        UNDISCH_TAC `{ring_of_int (k:A ring) n | &p divides n} = P` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!e s. ring_of_int (k:A ring) e IN IMAGE (ring_of_int k) s <=> e IN s`
    ASSUME_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[prime_ideal; PROPER_IDEAL; ring_ideal] THEN
    ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV;
                SUBSET] THEN
    REWRITE_TAC[GSYM RING_OF_INT_0; GSYM RING_OF_INT_1; GSYM RING_OF_INT_NEG;
                GSYM RING_OF_INT_ADD; GSYM RING_OF_INT_MUL] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN
    CONJ_TAC THENL
     [CONV_TAC INTEGER_RULE;
      REWRITE_TAC[GSYM num_divides; DIVIDES_ONE] THEN ASM_MESON_TAC[PRIME_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ring_of_int (k:A ring) n IN a` ASSUME_TAC THENL
   [UNDISCH_TAC `{ring_of_int (k:A ring) n | n IN (:int)} = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A->bool`; `P:A->bool`]
    VALUATION_SUBRING_DOMINATES) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:A->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:int` THEN
  UNDISCH_TAC `!n. ring_of_int (k:A ring) n IN P <=> &p divides n` THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  UNDISCH_TAC `a INTER m = (P:A->bool)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER]);;

let VALUATION_SUBRING_RESIDUE_CHAR = prove
 (`!(k:A ring) v m p.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        (!n. ring_of_int k n IN m <=> &p divides n)
        ==> ring_char(quotient_ring (subring_generated k v) m) = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  REWRITE_TAC[RING_CHAR_UNIQUE] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`subring_generated k (v:A->bool)`;
                 `quotient_ring (subring_generated k v) (m:A->bool)`;
                 `ring_coset (subring_generated k v) (m:A->bool)`]
    RING_HOMOMORPHISM_RING_OF_NUM) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_NUM] THEN
  REWRITE_TAC[RING_OF_NUM_SUBRING_GENERATED; GSYM RING_OF_INT_OF_NUM] THEN
  ASM_REWRITE_TAC[num_divides; RING_OF_INT_SUBRING_GENERATED]);;

(* The residue characteristic p is 0 or a prime (INTEGRAL_DOMAIN_CHAR for    *)
(* the residue field), and the integers in m are the multiples of p: the     *)
(* converse direction of VALUATION_SUBRING_RESIDUE_CHAR.                     *)
let VALUATION_SUBRING_RESIDUE_CHAR_CASES = prove
 (`!(k:A ring) v m.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> ?p. (p = 0 \/ prime p) /\
                !n. ring_of_int k n IN m <=> &p divides n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  EXISTS_TAC
   `ring_char(quotient_ring (subring_generated k v) (m:A->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_CHAR THEN
    MATCH_MP_TAC FIELD_IMP_INTEGRAL_DOMAIN THEN
    ASM_SIMP_TAC[FIELD_QUOTIENT_RING];
    X_GEN_TAC `n:int` THEN REWRITE_TAC[GSYM RING_OF_INT_EQ_0] THEN
    MP_TAC(ISPECL [`subring_generated k (v:A->bool)`;
                   `quotient_ring (subring_generated k v) (m:A->bool)`;
                   `ring_coset (subring_generated k v) (m:A->bool)`]
      RING_HOMOMORPHISM_RING_OF_INT) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL; RING_OF_INT] THEN
    REWRITE_TAC[RING_OF_INT_SUBRING_GENERATED]]);;

let ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME = prove
 (`!(k:A ring) p.
        algebraically_closed_field k /\ ring_char k = 0 /\ prime p
        ==> ?v m. valuation_subring k v /\
                  maximal_ideal (subring_generated k v) m /\
                  (!n. ring_of_int k n IN m <=> &p divides n) /\
                  algebraically_closed_field
                   (quotient_ring (subring_generated k v) m) /\
                  ring_char(quotient_ring (subring_generated k v) m) = p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`] VALUATION_SUBRING_OVER_PRIME) THEN
  ASM_SIMP_TAC[ALGEBRAICALLY_CLOSED_FIELD_IMP_FIELD] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC VALUATION_SUBRING_RESIDUE_ALGEBRAICALLY_CLOSED THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC VALUATION_SUBRING_RESIDUE_CHAR THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The decomposition and inertia groups of a valuation subring.              *)
(* ------------------------------------------------------------------------- *)

(* v is determined by m (VALUATION_SUBRING_INV_MAXIMAL_IDEAL), so the        *)
(* decomposition group at m is the stabilizer of v, and it acts on the       *)
(* residue field.                                                            *)

let VALUATION_SUBRING_DECOMPOSITION_GROUP = prove
 (`!(h:A->B) k l v m.
        valuation_subring l v /\ maximal_ideal (subring_generated l v) m
        ==> group_carrier(decomposition_group(k,l) h m) =
            {f | f IN group_carrier(galois_group(k,l) h) /\ IMAGE f v = v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN `(v:B->bool) SUBSET ring_carrier l /\ m SUBSET v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[subring_of]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `v:B->bool`; `m:B->bool`]
      VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier(galois_group(k,l) (h:A->B))
        ==> g permutes ring_carrier l /\
            (!x. x IN ring_carrier l ==> g(ring_inv l x) = ring_inv l (g x)) /\
            g(ring_0 l) = ring_0 l`
  (LABEL_TAC "aut") THENL
   [X_GEN_TAC `g:B->B` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP GALOIS_GROUP_PERMUTES);
      MATCH_MP_TAC FIELD_HOMOMORPHISM_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE g m = m
        ==> IMAGE g v SUBSET v`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:B->B` THEN STRIP_TAC THEN
    USE_THEN "aut" (MP_TAC o SPEC `g:B->B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:B` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier l /\ (g:B->B) x IN ring_carrier l`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; PERMUTES_IN_IMAGE]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `v:B->bool`; `m:B->bool`; `x:B`]
      VALUATION_SUBRING_INV_MAXIMAL_IDEAL) THEN
    MP_TAC(ISPECL [`l:B ring`; `v:B->bool`; `m:B->bool`; `(g:B->B) x`]
      VALUATION_SUBRING_INV_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
    ASM_CASES_TAC `x:B = ring_0 l` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISJ2_TAC THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(x:B) IN ring_carrier l`))]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(g:B->B)(ring_inv l x) IN IMAGE g m` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier(galois_group(k,l) (h:A->B)) /\ IMAGE g v = v
        ==> IMAGE g m SUBSET m`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:B->B` THEN STRIP_TAC THEN
    USE_THEN "aut" (MP_TAC o SPEC `g:B->B`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `v:B->bool`; `m:B->bool`]
      VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `q:B` THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `q:B = ring_0 l` THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    SUBGOAL_THEN `~(ring_inv l (q:B) IN v)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(q:B) IN ring_carrier l`))]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(g:B->B)(ring_inv l q) IN IMAGE g v` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  REWRITE_TAC[DECOMPOSITION_GROUP] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:B->B` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `f IN group_carrier(galois_group(k,l) (h:A->B))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_INVERSE) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `m:B->bool`]
      GALOIS_GROUP_IMAGE_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (f:B->B) v SUBSET v /\ IMAGE (inverse f) v SUBSET v`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC];
    MP_TAC(ISPECL [`h:A->B`; `f:B->B`; `k:A ring`; `l:B ring`; `v:B->bool`]
      GALOIS_GROUP_IMAGE_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (f:B->B) m SUBSET m /\ IMAGE (inverse f) m SUBSET m`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]] THEN
  UNDISCH_TAC `!x:B. (f:B->B)(inverse f x) = x` THEN SET_TAC[]);;

let VALUATION_SUBRING_RESIDUE_HOMOMORPHISM = prove
 (`!(h:A->B) k l v m.
        valuation_subring l v /\ maximal_ideal (subring_generated l v) m
        ==> group_homomorphism
             (decomposition_group(k,l) h m,
              galois_group
               (subring_generated (quotient_ring (subring_generated l v) m)
                 (IMAGE (ring_coset (subring_generated l v) m o h)
                        {a | a IN ring_carrier k /\ h a IN v}),
                quotient_ring (subring_generated l v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated l v) m)
                    then IMAGE f X else X) /\
            group_kernel
             (decomposition_group(k,l) h m,
              galois_group
               (subring_generated (quotient_ring (subring_generated l v) m)
                 (IMAGE (ring_coset (subring_generated l v) m o h)
                        {a | a IN ring_carrier k /\ h a IN v}),
                quotient_ring (subring_generated l v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated l v) m)
                    then IMAGE f X else X) =
            group_carrier(inertia_group(k,l) h (subring_generated l v) m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`;
                 `subring_generated l (v:B->bool)`; `m:B->bool`]
    DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; MAXIMAL_IMP_RING_IDEAL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[VALUATION_SUBRING_DECOMPOSITION_GROUP; IN_ELIM_THM] THEN
  SIMP_TAC[SUBSET_REFL]);;

(* A homomorphism trivial on the residues of a and s, with s and its image   *)
(* units of v, is trivial on the residue of a / s.                           *)

let VALUATION_SUBRING_RESIDUE_DIV = prove
 (`!(k:A ring) v m (f:A->A) a s.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        ring_homomorphism(k,k) f /\
        a IN v /\ s IN v /\ ~(s IN m) /\ f s IN v /\ ~(f s IN m) /\
        ring_sub k (f a) a IN m /\ ring_sub k (f s) s IN m
        ==> ring_sub k (f(ring_div k a s)) (ring_div k a s) IN m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
    VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(!x y:A. x IN m /\ y IN v ==> ring_mul k x y IN m) /\
    (!x y:A. x IN v /\ y IN m ==> ring_mul k x y IN m) /\
    (!x y:A. x IN m /\ y IN m ==> ring_sub k x y IN m)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`]
      MAXIMAL_IMP_RING_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`;
                     `x:A`; `y:A`] IN_RING_IDEAL_RMUL);
      MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`;
                     `x:A`; `y:A`] IN_RING_IDEAL_LMUL);
      MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`;
                     `x:A`; `y:A`] IN_RING_IDEAL_SUB)] THEN
    ASM_SIMP_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED;
                 CARRIER_SUBRING_GENERATED_SUBRING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:A. z IN v /\ ~(z IN m)
          ==> z IN ring_carrier k /\ ~(z = ring_0 k) /\ ring_inv k z IN v`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN STRIP_TAC THEN
    UNDISCH_TAC `~((z:A) IN m)` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[subring_of; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[subring_of; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(s:A) IN ring_carrier k /\ ~(s = ring_0 k) /\ ring_inv k s IN v /\
    (f:A->A) s IN ring_carrier k /\ ~(f s = ring_0 k) /\
    ring_inv k (f s) IN v`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub k ((f:A->A)(ring_div k a s)) (ring_div k a s) =
    ring_mul k
     (ring_mul k
       (ring_sub k (ring_mul k (ring_sub k (f a) a) s)
                   (ring_mul k a (ring_sub k (f s) s)))
       (ring_inv k (f s)))
     (ring_inv k s)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `k:A ring`; `f:A->A`]
      RING_HOMOMORPHISM_MUL) THEN
    MP_TAC(ISPECL [`k:A ring`; `k:A ring`; `f:A->A`]
      FIELD_HOMOMORPHISM_INV) THEN
    ASM_SIMP_TAC[ring_div; RING_INV] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC(RING_RULE
     `!k a s b t i j:A.
        a IN ring_carrier k /\ s IN ring_carrier k /\
        b IN ring_carrier k /\ t IN ring_carrier k /\
        i IN ring_carrier k /\ j IN ring_carrier k /\
        ring_mul k s i = ring_1 k /\ ring_mul k t j = ring_1 k
        ==> ring_sub k (ring_mul k b j) (ring_mul k a i) =
            ring_mul k
             (ring_mul k
               (ring_sub k (ring_mul k (ring_sub k b a) s)
                           (ring_mul k a (ring_sub k t s))) j) i`) THEN
    ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The algebraic integers.                                                   *)
(* ------------------------------------------------------------------------- *)

let VALUATION_SUBRING_RING_OF_INTEGERS = prove
 (`!(k:A ring) v.
        valuation_subring k v
        ==> ring_carrier(ring_of_integers k) SUBSET v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  REWRITE_TAC[SUBSET; RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  MATCH_MP_TAC VALUATION_SUBRING_INTEGRAL_ELEMENT THEN
  EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`integer_ring`; `k:A ring`; `ring_of_int (k:A ring)`;
                 `v:A->bool`; `x:A`] INTEGRAL_ELEMENT_OVER_SUBRING) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT;
               CARRIER_SUBRING_GENERATED_SUBRING] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; INTEGER_RING; IN_UNIV] THEN
  X_GEN_TAC `n:int` THEN
  MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `n:int`] RING_OF_INT) THEN
  ASM_SIMP_TAC[RING_OF_INT_SUBRING_GENERATED;
               CARRIER_SUBRING_GENERATED_SUBRING]);;

let VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS = prove
 (`!(k:A ring) v m.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> prime_ideal (ring_of_integers k)
                        (m INTER ring_carrier(ring_of_integers k))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `subring_generated k v:A ring`;
                 `I:A->A`; `m:A->bool`] PRIME_IDEAL_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
    MP_TAC(ISPECL [`k:A ring`; `k:A ring`;
                   `ring_carrier(ring_of_integers k:A ring)`; `v:A->bool`;
                   `I:A->A`] RING_HOMOMORPHISM_BETWEEN_SUBRINGS) THEN
    REWRITE_TAC[RING_HOMOMORPHISM_I; IMAGE_I; RING_OF_INTEGERS_SUBRING] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[VALUATION_SUBRING_RING_OF_INTEGERS];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN REWRITE_TAC[I_THM] THEN
    SET_TAC[]]);;

(* DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM needs no finiteness, so it       *)
(* applies to the Galois group of k over its prime subfield, with b the      *)
(* algebraic integers and Q = Q_V.                                           *)

let VALUATION_SUBRING_DECOMPOSITION_RESIDUE = prove
 (`!(k:A ring) v m Q.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        Q = m INTER ring_carrier(ring_of_integers k)
        ==> group_homomorphism
             (decomposition_group (subfield_generated k {ring_0 k},k) I Q,
              galois_group
               (subring_generated (quotient_ring (ring_of_integers k) Q)
                 (IMAGE (ring_coset (ring_of_integers k) Q)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN ring_carrier(ring_of_integers k)}),
                quotient_ring (ring_of_integers k) Q) I)
             (\f X. if X IN ring_carrier(quotient_ring (ring_of_integers k) Q)
                    then IMAGE f X else X) /\
            group_kernel
             (decomposition_group (subfield_generated k {ring_0 k},k) I Q,
              galois_group
               (subring_generated (quotient_ring (ring_of_integers k) Q)
                 (IMAGE (ring_coset (ring_of_integers k) Q)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN ring_carrier(ring_of_integers k)}),
                quotient_ring (ring_of_integers k) Q) I)
             (\f X. if X IN ring_carrier(quotient_ring (ring_of_integers k) Q)
                    then IMAGE f X else X) =
            group_carrier(inertia_group (subfield_generated k {ring_0 k},k) I
                            (ring_of_integers k) Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0(k:A ring)}`;
                 `k:A ring`; `ring_of_integers k:A ring`; `Q:A->bool`]
    DECOMPOSITION_GROUP_RESIDUE_HOMOMORPHISM) THEN
  REWRITE_TAC[I_O_ID; I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[RING_OF_INTEGERS_SUBRING;
              DECOMPOSITION_GROUP_RING_OF_INTEGERS] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN
  MATCH_MP_TAC VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS THEN
  EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Valuation subrings of number fields and of number subfields.              *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION = prove
 (`!(k:A ring) v m.
        number_field k /\ valuation_subring k v /\
        maximal_ideal (subring_generated k v) m
        ==> v = {ring_div k a s | a,s |
                 a IN ring_carrier(ring_of_integers k) /\
                 s IN ring_carrier(ring_of_integers k) /\ ~(s IN m)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN
   `dedekind_domain(ring_of_integers k:A ring) /\
    field_of_fractions(ring_of_integers k,k) I /\
    ring_carrier(ring_of_integers k) SUBSET v /\
    prime_ideal (ring_of_integers k)
                (m INTER ring_carrier(ring_of_integers k)) /\
    ring_0(ring_of_integers k) = ring_0 k /\
    ring_1(ring_of_integers k) = ring_1 k /\
    ring_carrier(ring_of_integers k) SUBSET ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS_FRACTION_FIELD;
                 RING_OF_INTEGERS; RING_OF_INTEGERS_SUBSET; I_THM] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VALUATION_SUBRING_RING_OF_INTEGERS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS THEN
      EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  ABBREV_TAC `O = ring_of_integers(k:A ring)` THEN
  ABBREV_TAC `Q = m INTER ring_carrier(O:A ring)` THEN
  SUBGOAL_THEN
   `!s:A. s IN ring_carrier(O:A ring) /\ ~(s IN m)
          ==> ~(s = ring_0 k) /\ ring_inv k s IN v /\ s IN v`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
      VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `~((s:A) IN {x | x IN v /\ (x = ring_0 k \/ ~(ring_inv k x IN v))})` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:A->bool) SUBSET ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[subring_of]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:A. x IN v
          ==> ?a b. a IN ring_carrier(O:A ring) /\ b IN ring_carrier O /\
                    ~(b IN m) /\ ring_mul k b x = a`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `Q = {ring_0(O:A ring)}` THENL
     [SUBGOAL_THEN
       `?a b:A. a IN ring_carrier O /\ b IN ring_carrier O /\
                ~(b = ring_0 O) /\ ring_mul k (I b) x = I a`
      MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[I_THM]] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?a b:A. a IN ring_carrier O /\ b IN ring_carrier O /\
              ~(b IN Q) /\ ring_mul k b x = a`
    MP_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
    MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `Q:A->bool`; `x:A`]
      DEDEKIND_VALUATION_POS) THEN
    ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_CASES_TAC `x:A = ring_0 k` THEN ASM_REWRITE_TAC[GSYM INT_NOT_LT] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `ring_inv k (x:A) IN ring_carrier k /\ ~(ring_inv k x = ring_0 k) /\
      &0 < dedekind_valuation (O,k) I Q (ring_inv k x)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_INV; FIELD_INV_EQ_0] THEN
      MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `Q:A->bool`; `x:A`]
        DEDEKIND_VALUATION_INV) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `Q:A->bool`;
                   `ring_inv k x:A`] DEDEKIND_VALUATION_POS) THEN
    ASM_SIMP_TAC[INT_LT_IMP_LE; I_THM] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~((b:A) IN m) /\ (a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(b:A = ring_0 k) /\ ring_inv k b IN v` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(a:A = ring_0 k)` ASSUME_TAC THENL
     [UNDISCH_TAC `ring_mul k b (ring_inv k x) = (a:A)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:A) IN m` ASSUME_TAC THENL
     [SUBGOAL_THEN `(a:A) IN Q` MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `Q:A->bool`; `a:A`]
        DEDEKIND_VALUATION_PRIME_IDEAL) THEN
      ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `ring_mul k b (ring_inv k x) = (a:A)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `Q:A->bool`;
                     `b:A`; `ring_inv k x:A`] DEDEKIND_VALUATION_MUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `Q:A->bool`; `b:A`]
        DEDEKIND_VALUATION_IMAGE) THEN
      ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(ring_inv k (a:A) IN v)` MP_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
        VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `a:A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ring_mul k b (ring_inv k x) = (a:A)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[RING_INV_MUL; RING_INV] THEN
    SUBGOAL_THEN `ring_inv k (ring_inv k x) = (x:A)` SUBST1_TAC THENL
     [MATCH_MP_TAC RING_INV_INV THEN ASM_SIMP_TAC[FIELD_UNIT]; ALL_TAC] THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[subring_of];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[ring_div] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(RING_RULE
     `!k s x t:A. s IN ring_carrier k /\ x IN ring_carrier k /\
                  t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                  ==> x = ring_mul k (ring_mul k s x) t`) THEN
    SUBGOAL_THEN `(s:A) IN ring_carrier k /\ ~(s = ring_0 k)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV] THEN ASM SET_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; ring_div] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `s:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; subring_of]]);;

let VALUATION_SUBRING_NUMBER_SUBFIELD = prove
 (`!(k:A ring) v m l.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        l subfield_of k /\ number_field(subfield_generated k l)
        ==> prime_ideal (ring_of_integers(subfield_generated k l))
             (m INTER
              ring_carrier(ring_of_integers(subfield_generated k l))) /\
            (!n. ring_of_int (subfield_generated k l) n IN
                 m INTER
                 ring_carrier(ring_of_integers(subfield_generated k l)) <=>
                 ring_of_int k n IN m) /\
            v INTER l =
            {ring_div k a s | a,s |
             a IN ring_carrier(ring_of_integers(subfield_generated k l)) /\
             s IN ring_carrier(ring_of_integers(subfield_generated k l)) /\
             ~(s IN m)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l:A->bool`]
    VALUATION_SUBRING_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated k l) = (l:A->bool) /\
    field(subfield_generated k l) /\
    ring_carrier(ring_of_integers(subfield_generated k l)) SUBSET l /\
    ring_0 k IN m`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `valuation_subring (k:A ring) v` THEN
    REWRITE_TAC[valuation_subring] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD;
                 FIELD_SUBFIELD_GENERATED] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET;
                    CARRIER_SUBFIELD_GENERATED_SUBFIELD];
      MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`]
        MAXIMAL_IMP_RING_IDEAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP IN_RING_IDEAL_0) THEN
      REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`subfield_generated k (l:A->bool)`; `v INTER (l:A->bool)`;
                   `m INTER (l:A->bool)`]
      VALUATION_SUBRING_CONTRACTION_RING_OF_INTEGERS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RING_OF_INT_SUBFIELD_GENERATED; IN_INTER] THEN
    MATCH_MP_TAC(TAUT `q ==> (p /\ q <=> p)`) THEN
    MP_TAC(ISPECL [`ring_of_integers(subfield_generated k (l:A->bool))`;
                   `n:int`] RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS; RING_OF_INT_SUBFIELD_GENERATED];
    MP_TAC(ISPECL [`subfield_generated k (l:A->bool)`; `v INTER (l:A->bool)`;
                   `m INTER (l:A->bool)`]
      NUMBER_FIELD_VALUATION_SUBRING_LOCALIZATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN
    X_GEN_TAC `x:A` THEN
    REWRITE_TAC[ring_div; CONJUNCT2 SUBFIELD_GENERATED] THEN
    EQ_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:A` THEN STRIP_TAC THEN
    (SUBGOAL_THEN `(s:A) IN l /\ ~(s = ring_0 k)` STRIP_ASSUME_TAC THENL
      [ASM SET_TAC[]; ALL_TAC]) THEN
    ASM_SIMP_TAC[RING_INV_SUBFIELD_GENERATED] THEN ASM SET_TAC[]]);;

let VALUATION_SUBRING_NUMBER_SUBFIELD_VALUATION = prove
 (`!(k:A ring) v m l x.
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m /\
        l subfield_of k /\ number_field(subfield_generated k l) /\
        ~(m INTER ring_carrier(ring_of_integers(subfield_generated k l)) =
          {ring_0 k}) /\
        x IN l /\ ~(x = ring_0 k)
        ==> (x IN v <=>
             &0 <= dedekind_valuation
                    (ring_of_integers(subfield_generated k l),
                     subfield_generated k l) I
                    (m INTER
                     ring_carrier(ring_of_integers(subfield_generated k l)))
                    x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l:A->bool`]
    VALUATION_SUBRING_NUMBER_SUBFIELD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT2)) THEN
  MP_TAC(ISPECL
   [`ring_of_integers(subfield_generated k (l:A->bool))`;
    `subfield_generated k (l:A->bool)`; `I:A->A`;
    `m INTER
     ring_carrier(ring_of_integers(subfield_generated k (l:A->bool)))`;
    `x:A`] DEDEKIND_VALUATION_POS) THEN
  MP_TAC(ISPEC `subfield_generated k (l:A->bool)`
    RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_SIMP_TAC[CARRIER_SUBFIELD_GENERATED_SUBFIELD; RING_OF_INTEGERS;
               CONJUNCT2 SUBFIELD_GENERATED; I_THM] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(x:A) IN v <=> x IN v INTER l` SUBST1_TAC THENL
   [ASM SET_TAC[];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER]] THEN
  SUBGOAL_THEN
   `ring_carrier(ring_of_integers(subfield_generated k (l:A->bool))) SUBSET
    ring_carrier k /\ ring_0 k IN m /\ (x:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET) THEN SET_TAC[];
      MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`]
        MAXIMAL_IMP_RING_IDEAL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP IN_RING_IDEAL_0) THEN
      REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED];
      ASM_MESON_TAC[SUBFIELD_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:A`; `s:A`] THEN ASM_REWRITE_TAC[] THEN
  (SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (s:A) IN ring_carrier k /\
                 ~(s = ring_0 k)`
   STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[ring_div] THENL
   [ASM_REWRITE_TAC[ring_div] THEN
    MATCH_MP_TAC(RING_RULE
     `!k a s t:A. a IN ring_carrier k /\ s IN ring_carrier k /\
                  t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                  ==> ring_mul k s (ring_mul k a t) = a`) THEN
    ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV];
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(RING_RULE
     `!k x s t:A. x IN ring_carrier k /\ s IN ring_carrier k /\
                  t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                  ==> x = ring_mul k (ring_mul k s x) t`) THEN
    ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV]]);;

(* ------------------------------------------------------------------------- *)
(* Valuation subrings of algebraic extensions of Q, such as Q-bar.           *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION = prove
 (`!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> v = {ring_div k a s | a,s |
                 a IN ring_carrier(ring_of_integers k) /\
                 s IN ring_carrier(ring_of_integers k) /\ ~(s IN m)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN `(v:A->bool) SUBSET ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[subring_of]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    ABBREV_TAC
     `l = ring_carrier(subfield_generated k
           ((x:A) INSERT ring_carrier(subfield_generated k {ring_0 k})))` THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`; `l:A->bool`]
      VALUATION_SUBRING_NUMBER_SUBFIELD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "l" THEN
      ASM_SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED;
                   SUBFIELD_GENERATED_BY_SUBFIELD_GENERATED] THEN
      REWRITE_TAC[number_field; RING_CHAR_SUBFIELD_GENERATED;
                  PRIME_SUBFIELD_SUBFIELD_GENERATED] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                     `k:A ring`; `x:A`]
        SUBFIELD_GENERATED_SIMPLE_ALGEBRAIC) THEN
      ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED; IMAGE_I] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[algebraic_extension; SUBSET]; SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A` o GEN_REWRITE_RULE I [EXTENSION] o
      CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM;
                RING_OF_INTEGERS_SUBFIELD_GENERATED] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN l` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "l" THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[];
      MESON_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; ring_div] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `s:A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `ring_carrier(ring_of_integers k) SUBSET (v:A->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC VALUATION_SUBRING_RING_OF_INTEGERS THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
      VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:A` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(a:A) IN v /\ (s:A) IN v` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]] THEN
    ASM_MESON_TAC[subring_of]]);;

let ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC = prove
 (`!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> algebraic_extension
             (subfield_generated (quotient_ring (subring_generated k v) m)
               {ring_0(quotient_ring (subring_generated k v) m)},
              quotient_ring (subring_generated k v) m) I`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN
   `ring_ideal (subring_generated k v) (m:A->bool) /\
    field(quotient_ring (subring_generated k v) m) /\
    ring_carrier(subring_generated k v) = v /\
    ring_monomorphism(subring_generated k v,k) I /\
    ring_carrier(ring_of_integers k) SUBSET v`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MAXIMAL_IMP_RING_IDEAL; FIELD_QUOTIENT_RING;
                 CARRIER_SUBRING_GENERATED_SUBRING;
                 VALUATION_SUBRING_RING_OF_INTEGERS] THEN
    REWRITE_TAC[I_DEF; RING_MONOMORPHISM_INCLUSION];
    ALL_TAC] THEN
  ABBREV_TAC `R = subring_generated k (v:A->bool)` THEN
  ABBREV_TAC `kq = quotient_ring R (m:A->bool)` THEN
  ASM_REWRITE_TAC[algebraic_extension; FIELD_EXTENSION_SUBFIELD_GENERATED] THEN
  EXPAND_TAC "kq" THEN ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
    ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `y:A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(a:A) IN v /\ (s:A) IN v /\ ~(s = ring_0 k) /\ ring_inv k s IN v`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
      VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `s:A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:A. z IN ring_carrier(ring_of_integers k)
          ==> ring_coset R m z IN ring_carrier(ring_of_integers kq)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier(ring_of_integers R)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`R:A ring`; `k:A ring`; `I:A->A`; `z:A`]
        RING_OF_INTEGERS_MONOMORPHIC_PREIMAGE) THEN
      ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`R:A ring`; `kq:(A->bool)ring`; `ring_coset R (m:A->bool)`]
      RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "kq" THEN MATCH_MP_TAC RING_HOMOMORPHISM_RING_COSET THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[ring_homomorphism; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_coset R m (y:A) IN ring_carrier kq /\
    ring_coset R m (s:A) IN ring_carrier kq /\
    ~(ring_coset R m s = ring_0 kq)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kq" THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; QUOTIENT_RING_0;
                 RING_COSET_EQ_IDEAL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `y = ring_div k a (s:A)` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (s:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_coset R m (ring_div k a s:A) =
    ring_div kq (ring_coset R m a) (ring_coset R m s)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `ring_coset R m (a:A) =
      ring_mul kq (ring_coset R m (ring_div k a s)) (ring_coset R m s)`
    SUBST1_TAC THENL
     [EXPAND_TAC "kq" THEN ASM_SIMP_TAC[QUOTIENT_RING_MUL] THEN
      AP_TERM_TAC THEN EXPAND_TAC "R" THEN
      REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED; ring_div] THEN
      MATCH_MP_TAC(RING_RULE
       `!k a s t:A. a IN ring_carrier k /\ s IN ring_carrier k /\
                    t IN ring_carrier k /\ ring_mul k s t = ring_1 k
                    ==> a = ring_mul k (ring_mul k a t) s`) THEN
      ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV];
      GEN_REWRITE_TAC RAND_CONV [ring_div] THEN
      MATCH_MP_TAC(RING_RULE
       `!r y s t:B. y IN ring_carrier r /\ s IN ring_carrier r /\
                    t IN ring_carrier r /\ ring_mul r s t = ring_1 r
                    ==> y = ring_mul r (ring_mul r y s) t`) THEN
      ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV]];
    MATCH_MP_TAC ALGEBRAIC_OVER_DIV THEN
    ASM_SIMP_TAC[FIELD_EXTENSION_SUBFIELD_GENERATED;
                 RING_OF_INTEGERS_ALGEBRAIC]]);;

let ALGEBRAIC_CLOSURE_VALUATION_OVER_PRIME = prove
 (`!(k:A ring) p.
        algebraically_closed_field k /\ ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\ prime p
        ==> ?v m. valuation_subring k v /\
                  maximal_ideal (subring_generated k v) m /\
                  (!n. ring_of_int k n IN m <=> &p divides n) /\
                  algebraically_closed_field
                   (quotient_ring (subring_generated k v) m) /\
                  ring_char(quotient_ring (subring_generated k v) m) = p /\
                  algebraic_extension
                   (subfield_generated
                     (quotient_ring (subring_generated k v) m)
                     {ring_0(quotient_ring (subring_generated k v) m)},
                    quotient_ring (subring_generated k v) m) I`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `p:num`]
    ALGEBRAICALLY_CLOSED_VALUATION_OVER_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ALGEBRAIC_VALUATION_SUBRING_RESIDUE_ALGEBRAIC THEN
  ASM_REWRITE_TAC[]);;

let ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP = prove
 (`!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> group_carrier
             (decomposition_group (subfield_generated k {ring_0 k},k) I
                (m INTER ring_carrier(ring_of_integers k))) =
            {f | f IN group_carrier
                       (galois_group(subfield_generated k {ring_0 k},k) I) /\
                 IMAGE f v = v}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN
   `(v:A->bool) SUBSET ring_carrier k /\
    ring_carrier(ring_of_integers k) SUBSET v`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[subring_of; VALUATION_SUBRING_RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))
        ==> g permutes ring_carrier k /\
            (!x y. x IN ring_carrier k /\ y IN ring_carrier k
                   ==> g(ring_mul k x y) = ring_mul k (g x) (g y)) /\
            (!x. x IN ring_carrier k ==> g(ring_inv k x) = ring_inv k (g x)) /\
            g(ring_0 k) = ring_0 k /\
            IMAGE g (ring_carrier(ring_of_integers k)) SUBSET
            ring_carrier(ring_of_integers k)`
  (LABEL_TAC "aut") THENL
   [X_GEN_TAC `g:A->A` THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP GALOIS_GROUP_PERMUTES);
      MATCH_MP_TAC RING_HOMOMORPHISM_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIELD_HOMOMORPHISM_INV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RING_HOMOMORPHISM_0 THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A)) /\
        IMAGE g (m INTER ring_carrier(ring_of_integers k)) =
        m INTER ring_carrier(ring_of_integers k)
        ==> IMAGE g v SUBSET v`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:A->A` THEN STRIP_TAC THEN
    USE_THEN "aut" (MP_TAC o SPEC `g:A->A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
      ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `s:A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(g:A->A) a`; `(g:A->A) s`] THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (s:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[ring_div; RING_INV] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(g:A->A) s IN IMAGE g (m INTER ring_carrier(ring_of_integers k))`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A)) /\
        IMAGE g v = v
        ==> IMAGE g (m INTER ring_carrier(ring_of_integers k)) SUBSET
            m INTER ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `g:A->A` THEN STRIP_TAC THEN
    USE_THEN "aut" (MP_TAC o SPEC `g:A->A`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
      VALUATION_SUBRING_MAXIMAL_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `q:A` THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC; ASM SET_TAC[]] THEN
    ASM_CASES_TAC `q:A = ring_0 k` THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    SUBGOAL_THEN `~(ring_inv k (q:A) IN v)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(q:A) IN ring_carrier k`))]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(g:A->A)(ring_inv k q) IN IMAGE g v` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[PERMUTES_INJECTIVE];
    ALL_TAC] THEN
  REWRITE_TAC[DECOMPOSITION_GROUP] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `f IN group_carrier
          (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GALOIS_GROUP_PERMUTES) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_INVERSE) THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`I:A->A`; `f:A->A`; `subfield_generated k {ring_0 k:A}`;
                   `k:A ring`;
                   `m INTER ring_carrier(ring_of_integers k):A->bool`]
      GALOIS_GROUP_IMAGE_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (f:A->A) v SUBSET v /\ IMAGE (inverse f) v SUBSET v`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC];
    MP_TAC(ISPECL [`I:A->A`; `f:A->A`; `subfield_generated k {ring_0 k:A}`;
                   `k:A ring`; `v:A->bool`] GALOIS_GROUP_IMAGE_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `IMAGE (f:A->A) (m INTER ring_carrier(ring_of_integers k)) SUBSET
      m INTER ring_carrier(ring_of_integers k) /\
      IMAGE (inverse f) (m INTER ring_carrier(ring_of_integers k)) SUBSET
      m INTER ring_carrier(ring_of_integers k)`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]] THEN
  UNDISCH_TAC `!x:A. (f:A->A)(inverse f x) = x` THEN SET_TAC[]);;

let ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA = prove
 (`!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> decomposition_group (subfield_generated k {ring_0 k},k) I
              (m INTER ring_carrier(ring_of_integers k)) =
            decomposition_group (subfield_generated k {ring_0 k},k) I m /\
            inertia_group (subfield_generated k {ring_0 k},k) I
              (ring_of_integers k) (m INTER ring_carrier(ring_of_integers k)) =
            inertia_group (subfield_generated k {ring_0 k},k) I
              (subring_generated k v) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!f. f IN group_carrier
              (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))
        ==> (IMAGE f (m INTER ring_carrier(ring_of_integers k)) =
             m INTER ring_carrier(ring_of_integers k) <=> IMAGE f v = v) /\
            (IMAGE f m = m <=> IMAGE f v = v)`
  (LABEL_TAC "stab") THENL
   [X_GEN_TAC `f:A->A` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
        ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_GROUP);
      MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`;
                     `k:A ring`; `v:A->bool`; `m:A->bool`]
        VALUATION_SUBRING_DECOMPOSITION_GROUP)] THEN
    ASM_REWRITE_TAC[DECOMPOSITION_GROUP] THEN
    DISCH_THEN(MP_TAC o SPEC `f:A->A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[decomposition_group] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:A->A` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC
     `f IN group_carrier
            (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [valuation_subring]) THEN
  SUBGOAL_THEN
   `(v:A->bool) SUBSET ring_carrier k /\
    ring_carrier(ring_of_integers k) SUBSET v /\
    ring_carrier(subring_generated k v) = v /\
    (!x y:A. x IN m /\ y IN v ==> ring_mul k x y IN m) /\
    (!x y:A. x IN v /\ y IN m ==> ring_mul k x y IN m) /\
    (!x y:A. x IN m /\ y IN m ==> ring_sub k x y IN m)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING;
                 VALUATION_SUBRING_RING_OF_INTEGERS] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[subring_of]; ALL_TAC] THEN
    MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`]
      MAXIMAL_IMP_RING_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
    STRIP_TAC THENL
     [MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`;
                     `x:A`; `y:A`] IN_RING_IDEAL_RMUL);
      MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`;
                     `x:A`; `y:A`] IN_RING_IDEAL_LMUL);
      MP_TAC(ISPECL [`subring_generated k (v:A->bool)`; `m:A->bool`;
                     `x:A`; `y:A`] IN_RING_IDEAL_SUB)] THEN
    ASM_SIMP_TAC[CONJUNCT2 SUBRING_GENERATED; RING_SUB_SUBRING_GENERATED;
                 CARRIER_SUBRING_GENERATED_SUBRING];
    ALL_TAC] THEN
  REWRITE_TAC[inertia_group] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:A->A` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC
   `f IN group_carrier
          (galois_group(subfield_generated k {ring_0 k},k) (I:A->A))` THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "stab" (MP_TAC o SPEC `f:A->A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ASM_CASES_TAC `IMAGE (f:A->A) v = v` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(f:A->A) permutes ring_carrier k /\
    (!x y. x IN ring_carrier (k:A ring) /\ y IN ring_carrier k
           ==> f(ring_mul k x y) = ring_mul k (f x) (f y)) /\
    (!x. x IN ring_carrier k ==> f(ring_inv k x) = ring_inv k (f x)) /\
    IMAGE f (ring_carrier(ring_of_integers k)) SUBSET
    ring_carrier(ring_of_integers k) /\
    IMAGE f (m INTER ring_carrier(ring_of_integers k)) =
    m INTER ring_carrier(ring_of_integers k)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP GALOIS_GROUP_PERMUTES);
      MATCH_MP_TAC RING_HOMOMORPHISM_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FIELD_HOMOMORPHISM_INV THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(ACCEPT_TAC o MATCH_MP GALOIS_GROUP_RING_OF_INTEGERS);
      USE_THEN "stab" (MP_TAC o SPEC `f:A->A`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:A` THEN DISCH_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP GALOIS_GROUP_RING_HOMOMORPHISM) THEN
    MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
      ALGEBRAIC_VALUATION_SUBRING_LOCALIZATION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `s:A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `x = ring_div k a (s:A)` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `(a:A) IN v /\ (s:A) IN v /\ (f:A->A) s IN v /\
      (f:A->A) s IN ring_carrier(ring_of_integers k)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`ring_carrier(ring_of_integers k) SUBSET (v:A->bool)`;
        `IMAGE (f:A->A) (ring_carrier(ring_of_integers k)) SUBSET
         ring_carrier(ring_of_integers k)`;
        `(a:A) IN ring_carrier(ring_of_integers k)`;
        `(s:A) IN ring_carrier(ring_of_integers k)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((f:A->A) s IN m)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN
       `(f:A->A) s IN IMAGE f (m INTER ring_carrier(ring_of_integers k))`
      MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER]; REWRITE_TAC[IN_IMAGE; IN_INTER]] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(f:A->A) s = f w` THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INJECTIVE th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_sub k ((f:A->A) a) a IN m /\ ring_sub k ((f:A->A) s) s IN m`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC
       `!x:A. x IN ring_carrier(ring_of_integers k)
              ==> ring_sub k (f x) x IN
                  m INTER ring_carrier(ring_of_integers k)` THEN
      ASM_SIMP_TAC[IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC VALUATION_SUBRING_RESIDUE_DIV THEN EXISTS_TAC `v:A->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `(f:A->A) x`; `x:A`]
        RING_SUB) THEN
      REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM SET_TAC[]]]);;

let ALGEBRAIC_VALUATION_SUBRING_RESIDUE_HOMOMORPHISM = prove
 (`!(k:A ring) v m.
        ring_char k = 0 /\
        algebraic_extension(subfield_generated k {ring_0 k},k) I /\
        valuation_subring k v /\ maximal_ideal (subring_generated k v) m
        ==> group_homomorphism
             (decomposition_group (subfield_generated k {ring_0 k},k) I
                (m INTER ring_carrier(ring_of_integers k)),
              galois_group
               (subring_generated (quotient_ring (subring_generated k v) m)
                 (IMAGE (ring_coset (subring_generated k v) m)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN v}),
                quotient_ring (subring_generated k v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated k v) m)
                    then IMAGE f X else X) /\
            group_kernel
             (decomposition_group (subfield_generated k {ring_0 k},k) I
                (m INTER ring_carrier(ring_of_integers k)),
              galois_group
               (subring_generated (quotient_ring (subring_generated k v) m)
                 (IMAGE (ring_coset (subring_generated k v) m)
                    {a | a IN ring_carrier(subfield_generated k {ring_0 k}) /\
                         a IN v}),
                quotient_ring (subring_generated k v) m) I)
             (\f X. if X IN ring_carrier
                             (quotient_ring (subring_generated k v) m)
                    then IMAGE f X else X) =
            group_carrier
             (inertia_group (subfield_generated k {ring_0 k},k) I
                (ring_of_integers k)
                (m INTER ring_carrier(ring_of_integers k)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->bool`; `m:A->bool`]
    ALGEBRAIC_VALUATION_SUBRING_DECOMPOSITION_INERTIA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MP_TAC(ISPECL [`I:A->A`; `subfield_generated k {ring_0 k:A}`; `k:A ring`;
                 `v:A->bool`; `m:A->bool`]
    VALUATION_SUBRING_RESIDUE_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[I_O_ID; I_THM]);;
