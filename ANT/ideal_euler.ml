(* ========================================================================= *)
(* Euler and Fermat for ideals, and the number of units modulo an ideal.     *)
(*                                                                           *)
(* Main results: for an ideal j of a ring r with finite quotient and x prime *)
(* to j ((x) + j = r), x^phi(j) == 1 (mod j) with phi(j) = |(r/j)^*|         *)
(* (IDEAL_EULER); for a maximal ideal P with finite residue field, x^N(P) == *)
(* x (mod P) (IDEAL_NORM_FERMAT; with N(P) IN P,                             *)
(* MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD) and phi(P) = N(P) - 1             *)
(* (CARD_UNITS_QUOTIENT_RING_MAXIMAL). For a nonzero prime p of a Dedekind   *)
(* domain with finite residue field of order q there is an a whose powers    *)
(* meet every residue class outside p and with a^q - a IN p DIFF p^2         *)
(* (DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER, from a primitive root of the     *)
(* residue field and (x + t)^(n+1) == x^(n+1) + (n+1) x^n t modulo an ideal  *)
(* containing t^2, RING_POW_ADD_SQUARE_CONGRUENCE of Library/ringtheory.ml). *)
(* The function phi is multiplicative on coprime ideals                      *)
(* (CARD_UNITS_QUOTIENT_RING_COPRIME, by the Chinese remainder theorem and   *)
(* CARD_UNITS_PROD_RING of Library/ring_groups.ml), phi(P^n) =               *)
(* N(P)^(n-1) (N(P) - 1) for a nonzero prime P of a Dedekind domain          *)
(* (CARD_UNITS_QUOTIENT_RING_PRIME_POW), so for a nonzero ideal j of a       *)
(* Dedekind domain with finite quotient phi(j) is the product of the         *)
(* N(P)^(v_P(j)-1) (N(P) - 1) over the primes P containing j                 *)
(* (DEDEKIND_CARD_UNITS_QUOTIENT_RING), that is phi(j) = N(j) prod (1 -      *)
(* 1/N(P)) (DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL).                         *)
(*                                                                           *)
(* Routes: Euler is Lagrange in the unit group of r/j                        *)
(* (GROUP_POW_GROUP_ORDER), and Fermat follows for x not in P; the units     *)
(* modulo P^n are the classes of the elements outside P                      *)
(* (RING_UNIT_QUOTIENT_RING_IDEAL_POW of ANT/hensel.ml), counted with N(P^n) *)
(* = N(P)^n.                                                                 *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (units modulo an ideal,                       *)
(* RING_POW_ADD_SQUARE_CONGRUENCE), Library/grouptheory.ml,                  *)
(* Library/ring_groups.ml (unit_group, CARD_UNITS_PROD_RING,                 *)
(* ISOMORPHIC_RING_CARD_UNITS), Library/products.ml (nproduct, product),     *)
(* ANT/ideal_arith.ml (the Chinese remainder theorem), ANT/hensel.ml         *)
(* (RING_UNIT_QUOTIENT_RING_IDEAL_POW), ANT/dedekind.ml and                  *)
(* ANT/ideal_norm.ml.                                                        *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/ring_groups.ml";;
needs "Library/products.ml";;
needs "Library/finite_fields.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/hensel.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_norm.ml";;

(* ------------------------------------------------------------------------- *)
(* Euler: x^phi(j) == 1 (mod j) for x prime to j, phi(j) = |(r/j)^*|.        *)
(* ------------------------------------------------------------------------- *)

let IDEAL_EULER = prove
 (`!r j (x:A).
        ring_ideal r j /\ FINITE(ring_carrier(quotient_ring r j)) /\
        x IN ring_carrier r /\
        ring_setadd r (ideal_generated r {x}) j = ring_carrier r
        ==> ring_sub r
             (ring_pow r x (CARD {u | ring_unit (quotient_ring r j) u}))
             (ring_1 r) IN j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ring_unit (quotient_ring r j) (ring_coset r j (x:A))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_UNIT_QUOTIENT_RING_COSET] THEN
    UNDISCH_TAC
     `ring_setadd r (ideal_generated r {x:A}) j = ring_carrier r` THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
    DISCH_THEN(MP_TAC o SPEC `ring_1 r:A`) THEN
    REWRITE_TAC[RING_1; ring_setadd; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_SING; IN_ELIM_THM] THEN
    REWRITE_TAC[ring_divides; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM;
                LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `z:A`; `y:A`] THEN STRIP_TAC THEN
    EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_sub r (ring_mul r x y) (ring_add r (ring_mul r x y) z) =
      ring_neg r (z:A)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_sub r (ring_mul r x y) (ring_add r (ring_mul r x y) z) =
        ring_neg r (z:A)`) THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[IN_RING_IDEAL_NEG]];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  MP_TAC(ISPECL [`unit_group(quotient_ring r (j:A->bool))`;
                 `ring_coset r j (x:A)`] GROUP_POW_GROUP_ORDER) THEN
  REWRITE_TAC[UNIT_GROUP; UNIT_GROUP_POW; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `ring_carrier(quotient_ring r (j:A->bool))` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; RING_UNIT_IN_CARRIER];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    ASM_SIMP_TAC[GSYM(MATCH_MP RING_HOMOMORPHISM_POW th)]) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_1; RING_COSET_EQ; RING_POW; RING_1]);;

(* For a maximal ideal the units of the quotient are the nonzero classes.   *)

let CARD_UNITS_QUOTIENT_RING_MAXIMAL = prove
 (`!r p:A->bool.
        maximal_ideal r p /\ FINITE(ring_carrier(quotient_ring r p))
        ==> CARD {u | ring_unit (quotient_ring r p) u} = ideal_norm r p - 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `field(quotient_ring r (p:A->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_QUOTIENT_RING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{u | ring_unit (quotient_ring r p) u} =
    ring_carrier(quotient_ring r (p:A->bool)) DELETE
    ring_0(quotient_ring r p)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[EXTENSION; IN_ELIM_THM; IN_DELETE; FIELD_UNIT];
    ASM_SIMP_TAC[CARD_DELETE; RING_0; ideal_norm]]);;

(* ------------------------------------------------------------------------- *)
(* Fermat: x^N(P) == x (mod P) for a maximal ideal P with finite quotient.   *)
(* ------------------------------------------------------------------------- *)

let IDEAL_NORM_FERMAT = prove
 (`!r p (x:A).
        maximal_ideal r p /\ FINITE(ring_carrier(quotient_ring r p)) /\
        x IN ring_carrier r
        ==> ring_sub r (ring_pow r x (ideal_norm r p)) x IN p`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `1 <= ideal_norm r (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC IDEAL_NORM_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(x:A) IN p` THENL
   [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ideal_norm r (p:A->bool) = SUC(ideal_norm r p - 1)`
    SUBST1_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
    MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN ASM_SIMP_TAC[RING_POW];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `x:A`] IDEAL_EULER) THEN
  ASM_SIMP_TAC[CARD_UNITS_QUOTIENT_RING_MAXIMAL] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {x:A}`; `p:A->bool`]
      RING_SETADD_SYM) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[IDEAL_GENERATED_SUBSET; RING_IDEAL_IMP_SUBSET];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[MAXIMAL_IDEAL_COMAXIMAL; RING_IDEAL_IDEAL_GENERATED] THEN
    ASM_SIMP_TAC[IDEAL_GENERATED_MINIMAL_EQ; SET_RULE
     `(x:A) IN s ==> (s INTER {x} SUBSET u <=> x IN u)`];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r (ring_pow r x (ideal_norm r p)) x =
    ring_mul r x (ring_sub r (ring_pow r x (ideal_norm r p - 1))
                             (ring_1 r:A))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `ideal_norm r (p:A->bool) = SUC(ideal_norm r p - 1)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ring_pow]] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_sub r (ring_mul r x y) x =
      ring_mul r x (ring_sub r y (ring_1 r:A))`) THEN
    ASM_SIMP_TAC[RING_POW];
    ASM_SIMP_TAC[IN_RING_IDEAL_LMUL]]);;

(* The order q of a finite residue field r/j is in j, and x^q == x (mod j)  *)
(* (IDEAL_NORM_IN_IDEAL, IDEAL_NORM_FERMAT), with q written as the order.  *)
let MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD = prove
 (`!r j:A->bool.
        maximal_ideal r j /\ FINITE(ring_carrier(quotient_ring r j))
        ==> ring_of_num r (CARD(ring_carrier(quotient_ring r j))) IN j /\
            !x. x IN ring_carrier r
                ==> ring_sub r
                     (ring_pow r x (CARD(ring_carrier(quotient_ring r j)))) x
                    IN j`,
  REWRITE_TAC[GSYM ideal_norm] THEN
  MESON_TAC[IDEAL_NORM_IN_IDEAL; IDEAL_NORM_FERMAT; MAXIMAL_IMP_RING_IDEAL]);;

(* For a nonzero prime p with finite residue field of order q, an a whose    *)
(* powers meet every residue class outside p and such that a^q - a is a      *)
(* uniformizer (in p, not in p^2).                                           *)
let DEDEKIND_RESIDUE_GENERATOR_UNIFORMIZER = prove
 (`!r p:A->bool.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r p))
        ==> ?a. a IN ring_carrier r /\
                (!y. y IN ring_carrier r
                     ==> y IN p \/ ?m. ring_sub r y (ring_pow r a m) IN p) /\
                ring_sub r
                  (ring_pow r a (CARD(ring_carrier(quotient_ring r p)))) a
                IN p /\
                ~(ring_sub r
                   (ring_pow r a (CARD(ring_carrier(quotient_ring r p)))) a
                  IN ideal_pow r p 2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `maximal_ideal r (p:A->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL]; ALL_TAC] THEN
  SUBGOAL_THEN `field(quotient_ring r (p:A->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_QUOTIENT_RING]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`]
    MAXIMAL_IDEAL_FINITE_QUOTIENT_POW_CARD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = CARD(ring_carrier(quotient_ring r (p:A->bool)))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(q:num = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM_SIMP_TAC[CARD_EQ_0] THEN
    MESON_TAC[RING_0; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `quotient_ring r (p:A->bool)` FINITE_FIELD_PRIMITIVE_ROOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?a0:A. a0 IN ring_carrier r /\ ring_coset r p a0 = g`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:A->bool) IN ring_carrier(quotient_ring r p)` THEN
    ASM_SIMP_TAC[QUOTIENT_RING; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_HOMOMORPHISM_RING_COSET) THEN
  SUBGOAL_THEN
   `!a:A. a IN ring_carrier r /\ ring_sub r a a0 IN p
          ==> !y. y IN ring_carrier r
                  ==> y IN p \/ ?m. ring_sub r y (ring_pow r a m) IN p`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:A` THEN STRIP_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:A) IN p` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_coset r p (y:A)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ring_pow (quotient_ring r (p:A->bool))`))
        (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[QUOTIENT_RING; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN EXISTS_TAC `m:num` THEN
    SUBGOAL_THEN `ring_coset r p (a:A) = g` ASSUME_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `ring_coset r p (a0:A) = g`)) THEN
      ASM_SIMP_TAC[RING_COSET_EQ];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_coset r p (ring_pow r (a:A) m) = ring_coset r p y`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `ring_coset r p (y:A)`)) THEN
      FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW th]);
      ASM_SIMP_TAC[RING_COSET_EQ; RING_POW] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:A ring`; `p:A->bool`;
                     `ring_sub r (ring_pow r (a:A) m) y`]
        IN_RING_IDEAL_NEG) THEN
      ASM_SIMP_TAC[RING_NEG_SUB; RING_POW]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`] DEDEKIND_PRIME_IDEAL_UNIFORMIZER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC
   `ring_sub r (ring_pow r (a0:A) q) a0 IN ideal_pow r p 2` THENL
   [ALL_TAC;
    EXISTS_TAC `a0:A` THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[RING_SUB_REFL; IN_RING_IDEAL_0]] THEN
  EXISTS_TAC `ring_add r (a0:A) t` THEN ASM_SIMP_TAC[RING_ADD] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[RING_ADD] THEN
    SUBGOAL_THEN `ring_sub r (ring_add r a0 t) a0 = (t:A)` SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE `ring_sub r (ring_add r a t) a = (t:A)`) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `ring_mul r (t:A) t IN ideal_pow r p 2` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_pow r p 2:A->bool`; `a0:A`; `t:A`;
                 `q - 1`] RING_POW_ADD_SQUARE_CONGRUENCE) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; SUB_ADD; LE_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_mul r (ring_of_num r q) (ring_mul r (ring_pow r a0 (q - 1)) t) IN
    ideal_pow r p 2:A->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
    MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN ASM_SIMP_TAC[RING_POW];
    ALL_TAC] THEN
  UNDISCH_TAC `~((t:A) IN ideal_pow r p 2)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(t:A) =
    ring_add r
     (ring_sub r
       (ring_add r
         (ring_sub r (ring_pow r (ring_add r a0 t) q)
            (ring_add r (ring_pow r a0 q)
               (ring_mul r (ring_of_num r q)
                  (ring_mul r (ring_pow r a0 (q - 1)) t))))
         (ring_mul r (ring_of_num r q) (ring_mul r (ring_pow r a0 (q - 1)) t)))
       (ring_sub r (ring_pow r (ring_add r a0 t) q) (ring_add r a0 t)))
     (ring_sub r (ring_pow r a0 q) a0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `t = ring_add r
           (ring_sub r
             (ring_add r (ring_sub r u (ring_add r v w)) w)
             (ring_sub r u (ring_add r a t)))
           (ring_sub r v (a:A))`) THEN
    ASM_SIMP_TAC[RING_POW; RING_ADD; RING_MUL; RING_OF_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IN_RING_IDEAL_SUB THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN MATCH_MP_TAC IN_RING_IDEAL_ADD THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW]);;

(* ------------------------------------------------------------------------- *)
(* The number phi(j) = |(r/j)^*| of units modulo j: multiplicative on        *)
(* coprime ideals, N(P)^(n-1) (N(P) - 1) for P^n, and the product formula.   *)
(* ------------------------------------------------------------------------- *)

let CARD_UNITS_QUOTIENT_RING_COPRIME = prove
 (`!r j k:A->bool.
        ring_ideal r j /\ ring_ideal r k /\
        ring_setadd r j k = ring_carrier r /\
        FINITE(ring_carrier(quotient_ring r j)) /\
        FINITE(ring_carrier(quotient_ring r k))
        ==> CARD {u | ring_unit (quotient_ring r (ideal_prod r j k)) u} =
            CARD {u | ring_unit (quotient_ring r j) u} *
            CARD {u | ring_unit (quotient_ring r k) u}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[IDEAL_PROD_COMAXIMAL] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `k:A->bool`]
    CHINESE_REMAINDER_RING_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ISOMORPHIC_RING_SYM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`prod_ring (quotient_ring r j) (quotient_ring r (k:A->bool))`;
                 `quotient_ring r (j INTER k:A->bool)`]
    ISOMORPHIC_RING_CARD_UNITS) THEN
  ASM_SIMP_TAC[PROD_RING; FINITE_CROSS] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CARD_UNITS_PROD_RING THEN ASM_REWRITE_TAC[]);;

(* Units modulo P^n are the classes of the elements outside P.              *)

let CARD_UNITS_QUOTIENT_RING_PRIME_POW = prove
 (`!r p:A->bool n.
        dedekind_domain r /\ prime_ideal r p /\ ~(p = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r p)) /\ ~(n = 0)
        ==> CARD {u | ring_unit (quotient_ring r (ideal_pow r p n)) u} =
            ideal_norm r p EXP (n - 1) * (ideal_norm r p - 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `maximal_ideal r (p:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL]; ALL_TAC] THEN
  ABBREV_TAC `q = ideal_pow r (p:A->bool) n` THEN
  SUBGOAL_THEN `ring_ideal r (q:A->bool) /\ q SUBSET p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `1`; `n:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `n:num`] IDEAL_NORM_IDEAL_POW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{u | ring_unit (quotient_ring r q) u} =
    ring_carrier(quotient_ring r q) DIFF IMAGE (ring_coset r q) (p:A->bool)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `y:A->bool` THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_IMAGE] THEN
    ASM_CASES_TAC `?x:A. x IN ring_carrier r /\ y = ring_coset r q x` THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC);
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP RING_UNIT_IN_CARRIER) THEN
      ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN
        ASM_MESON_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `p:A->bool`; `n:num`; `x:A`]
      RING_UNIT_QUOTIENT_RING_IDEAL_POW) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[RING_UNIT_QUOTIENT_RING_MAXIMAL] THEN
    SUBGOAL_THEN `?a:A. a IN ring_carrier r /\
                       ring_coset r q x = ring_coset r q a`
    (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_sub r x (z:A) IN p` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `(q:A->bool) SUBSET p`)) THEN
      UNDISCH_TAC `ring_coset r q (x:A) = ring_coset r q z` THEN
      ASM_SIMP_TAC[RING_COSET_EQ];
      DISCH_TAC] THEN
    SUBGOAL_THEN `x:A = ring_add r (ring_sub r x z) z` SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE `x:A = ring_add r (ring_sub r x z) z`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `q:A->bool`; `p:A->bool`]
    CARD_QUOTIENT_RING_CHAIN) THEN
  ASM_REWRITE_TAC[GSYM ideal_norm] THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_DIFF o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[QUOTIENT_RING_CARRIER] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM ideal_norm] THEN
  SUBGOAL_THEN `~(ideal_norm r (p:A->bool) = 0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `p:A->bool`] IDEAL_NORM_POS) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(IMAGE (ring_coset r q) (p:A->bool)) = ideal_norm r p EXP (n - 1)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      is_eq(concl th) &&
      can (find_term ((=) `CARD(IMAGE (ring_coset r q) (p:A->bool))`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `n = SUC(n - 1)` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP]] THEN
    ASM_SIMP_TAC[EQ_MULT_LCANCEL] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    concl th = `ideal_norm r (q:A->bool) = ideal_norm r p EXP n`)) THEN
  SUBGOAL_THEN `n = SUC(n - 1)` (fun th ->
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
  THENL [ASM_ARITH_TAC; REWRITE_TAC[EXP]] THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_AC]);;

(* The units modulo a finite product of powers of distinct nonzero primes.    *)

let CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT = prove
 (`!r s (e:(A->bool)->num).
        dedekind_domain r /\ FINITE s /\
        (!p. p IN s
             ==> prime_ideal r p /\ ~(p = {ring_0 r}) /\ ~(e p = 0) /\
                 FINITE(ring_carrier(quotient_ring r p)))
        ==> FINITE(ring_carrier(quotient_ring r
                     (ideal_product r s (\p. ideal_pow r p (e p))))) /\
            CARD {u | ring_unit (quotient_ring r
                        (ideal_product r s (\p. ideal_pow r p (e p)))) u} =
            nproduct s (\p. ideal_norm r p EXP (e p - 1) *
                            (ideal_norm r p - 1))`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_NOETHERIAN) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[IDEAL_PRODUCT_EMPTY; NPRODUCT_CLAUSES] THEN
    SUBGOAL_THEN `trivial_ring(quotient_ring r (ring_carrier r:A->bool))`
    MP_TAC THENL
     [SIMP_TAC[TRIVIAL_QUOTIENT_RING; RING_IDEAL_CARRIER; PROPER_IDEAL_ALT];
      REWRITE_TAC[trivial_ring] THEN DISCH_TAC] THEN
    ASM_REWRITE_TAC[FINITE_SING] THEN
    SUBGOAL_THEN
     `{u | ring_unit (quotient_ring r (ring_carrier r:A->bool)) u} =
      {ring_0(quotient_ring r (ring_carrier r))}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `u:A->bool` THEN REWRITE_TAC[ring_unit] THEN
      ASM_REWRITE_TAC[IN_SING] THEN
      ASM_MESON_TAC[TRIVIAL_RING_10; trivial_ring; RING_0; RING_MUL;
                    IN_SING];
      REWRITE_TAC[CARD_SING]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:A->bool`; `s:(A->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `e:(A->bool)->num` THEN REWRITE_TAC[FORALL_IN_INSERT] THEN
  STRIP_TAC THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `e:(A->bool)->num`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_ideal r (ideal_pow r q ((e:(A->bool)->num) q)) /\
    FINITE(ring_carrier(quotient_ring r (ideal_pow r q (e q))))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; IDEAL_NORM_IDEAL_POW;
                 PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IDEAL_PRODUCT_INSERT; NPRODUCT_CLAUSES] THEN
  SUBGOAL_THEN
   `ring_setadd r (ideal_pow r q ((e:(A->bool)->num) q))
      (ideal_product r s (\p. ideal_pow r p (e p))) = ring_carrier r`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMAXIMAL_IDEAL_PRODUCT THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    X_GEN_TAC `p:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMAXIMAL_IDEAL_POW THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
    SUBGOAL_THEN `maximal_ideal r (q:A->bool) /\ maximal_ideal r p`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL]; ALL_TAC] THEN
    ASM_SIMP_TAC[MAXIMAL_IDEAL_COMAXIMAL; PRIME_IMP_RING_IDEAL] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `p:A->bool = q` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [maximal_ideal] o
      check (fun th -> concl th = `maximal_ideal r (p:A->bool)`)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `q:A->bool` o CONJUNCT2) THEN
    ASM_SIMP_TAC[MAXIMAL_IMP_PROPER_IDEAL; PSUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_QUOTIENT_RING_IDEAL_PROD THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_PRODUCT];
    ASM_SIMP_TAC[CARD_UNITS_QUOTIENT_RING_COPRIME; RING_IDEAL_IDEAL_PRODUCT;
                 CARD_UNITS_QUOTIENT_RING_PRIME_POW]]);;

(* The phi formula: |(r/j)^*| = product of N(P)^(v_P(j)-1) (N(P) - 1) over  *)
(* the primes P dividing j, for a nonzero ideal j with finite quotient.      *)

let DEDEKIND_CARD_UNITS_QUOTIENT_RING = prove
 (`!r j:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> CARD {u | ring_unit (quotient_ring r j) u} =
            nproduct {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
                     (\p. ideal_norm r p EXP (ideal_valuation r p j - 1) *
                          (ideal_norm r p - 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] DEDEKIND_IDEAL_FACTORIZATION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`r:A ring`;
    `{p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ (j:A->bool) SUBSET p}`;
    `\p:A->bool. ideal_valuation r p (j:A->bool)`]
   CARD_UNITS_QUOTIENT_RING_PRIME_PRODUCT) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN ANTS_TAC THENL
   [X_GEN_TAC `p:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[IDEAL_VALUATION_EQ_0] THEN
    MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN
    EXISTS_TAC `j:A->bool` THEN ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The same over the reals: phi(j) = N(j) times the product of 1 - 1/N(P). *)

let DEDEKIND_CARD_UNITS_QUOTIENT_RING_REAL = prove
 (`!r j:A->bool.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        FINITE(ring_carrier(quotient_ring r j))
        ==> &(CARD {u | ring_unit (quotient_ring r j) u}) =
            &(ideal_norm r j) *
            product {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ j SUBSET p}
                    (\p. &1 - inv(&(ideal_norm r p)))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DEDEKIND_CARD_UNITS_QUOTIENT_RING; IDEAL_NORM_FACTORIZATION] THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`] DEDEKIND_IDEAL_FACTORIZATION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\
                       (j:A->bool) SUBSET p}` THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:A->bool` THEN EXPAND_TAC "s" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ideal_valuation r p (j:A->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IDEAL_VALUATION_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= ideal_norm r (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 < n ==> 2 <= n`) THEN
    MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT];
      MATCH_MP_TAC FINITE_QUOTIENT_RING_MONO THEN
      EXISTS_TAC `j:A->bool` THEN ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_valuation r p (j:A->bool) = SUC(ideal_valuation r p j - 1)`
  (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o RAND_CONV)
               [th])
  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
               GSYM REAL_OF_NUM_SUB; ARITH_RULE `2 <= n ==> 1 <= n`] THEN
  REWRITE_TAC[real_pow] THEN
  SUBGOAL_THEN `~((&(ideal_norm r (p:A->bool)):real) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD]);;
