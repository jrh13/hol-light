(* ========================================================================= *)
(* Unique factorization domains: coprime factors of a power are powers.      *)
(*                                                                           *)
(* In a unique factorization domain, if a b = c^k with a and b coprime,      *)
(* then a is a unit times a k-th power (UFD_COPRIME_MUL_POW), equivalently   *)
(* a is associate to a k-th power (UFD_COPRIME_MUL_POW_ASSOCIATES); by       *)
(* symmetry the same holds for b. Proof by induction on the prime factors    *)
(* of c (UFD_PRIME_FACTOR_INDUCT): a prime p dividing c divides only one of  *)
(* the coprime factors, so p^k divides it; cancel and recurse.               *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml only (UFD, ring_coprime,                      *)
(* UFD_PRIME_FACTOR_INDUCT, RING_COPRIME_RPOW, RING_COPRIME_DIVPROD_RIGHT).  *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;

let UFD_COPRIME_MUL_POW =
  let lemma = prove
   (`!r p d v w:A k.
        UFD r /\ ring_prime r p /\ d IN ring_carrier r /\ ~(k = 0) /\
        v IN ring_carrier r /\ w IN ring_carrier r /\
        ring_coprime r (v,w) /\ ring_divides r p v /\
        ring_mul r v w = ring_mul r (ring_pow r p k) (ring_pow r d k)
        ==> ?v1. v1 IN ring_carrier r /\
                 v = ring_mul r (ring_pow r p k) v1 /\
                 ring_mul r v1 w = ring_pow r d k /\
                 ring_coprime r (v1,w)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP UFD_IMP_INTEGRAL_DOMAIN) THEN
    SUBGOAL_THEN
     `(p:A) IN ring_carrier r /\ ~(p = ring_0 r) /\ ~ring_unit r p`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ring_prime]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_coprime r (w:A,ring_pow r p k)` ASSUME_TAC THENL
     [MATCH_MP_TAC RING_COPRIME_RPOW THEN
      ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRIME_COPRIME_EQ] THEN
      ASM_MESON_TAC[ring_coprime];
      ALL_TAC] THEN
    SUBGOAL_THEN `ring_divides r (ring_pow r p k) (v:A)` MP_TAC THENL
     [MATCH_MP_TAC RING_COPRIME_DIVPROD_RIGHT THEN EXISTS_TAC `w:A` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_DIVIDES_RMUL THEN
      ASM_SIMP_TAC[RING_DIVIDES_REFL; RING_POW];
      REWRITE_TAC[ring_divides] THEN DISCH_THEN(X_CHOOSE_THEN `v1:A`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) o CONJUNCT2 o CONJUNCT2)]
    THEN EXISTS_TAC `v1:A` THEN
    UNDISCH_TAC `ring_coprime r (ring_mul r (ring_pow r p k) v1,w:A)` THEN
    ASM_SIMP_TAC[RING_COPRIME_LMUL; RING_POW] THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`r:A ring`; `ring_pow r p k:A`] THEN
    ASM_SIMP_TAC[RING_POW; RING_MUL; INTEGRAL_DOMAIN_POW_EQ_0;
                 RING_MUL_ASSOC]) in
  prove
   (`!r a b c:A k.
          UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
          c IN ring_carrier r /\ ring_coprime r (a,b) /\
          ring_mul r a b = ring_pow r c k
          ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                    a = ring_mul r u (ring_pow r e k)`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THENL
     [ASM_REWRITE_TAC[ring_pow] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:A`; `ring_1 r:A`] THEN
      ASM_SIMP_TAC[RING_1; RING_MUL_RID] THEN
      REWRITE_TAC[ring_unit] THEN ASM_MESON_TAC[];
      STRIP_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP UFD_IMP_INTEGRAL_DOMAIN) THEN
    SUBGOAL_THEN
     `!x:A. ring_unit r x
            ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                      x = ring_mul r u (ring_pow r e k)`
    (LABEL_TAC "unit") THENL
     [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `ring_1 r:A`] THEN
      ASM_SIMP_TAC[RING_POW_ONE; RING_1; RING_MUL_RID; RING_UNIT_IN_CARRIER];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!d:A. d IN ring_carrier r
            ==> !x y. x IN ring_carrier r /\ y IN ring_carrier r /\
                      ring_coprime r (x,y) /\ ring_mul r x y = ring_pow r d k
                      ==> ?u e. ring_unit r u /\ e IN ring_carrier r /\
                                x = ring_mul r u (ring_pow r e k)`
     (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC UFD_PRIME_FACTOR_INDUCT THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[RING_POW_ZERO] THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `x:A = ring_0 r \/ y = ring_0 r` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[INTEGRAL_DOMAIN_MUL_EQ_0];
        MAP_EVERY EXISTS_TAC [`ring_1 r:A`; `ring_0 r:A`] THEN
        ASM_SIMP_TAC[RING_UNIT_1; RING_0; RING_POW_ZERO; RING_MUL_LID];
        REMOVE_THEN "unit" MATCH_MP_TAC THEN ASM_MESON_TAC[RING_COPRIME_0]];
      X_GEN_TAC `w:A` THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
      REMOVE_THEN "unit" MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`r:A ring`; `x:A`; `y:A`] RING_UNIT_MUL_EQ) THEN
      ASM_SIMP_TAC[RING_UNIT_POW];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:A`; `d:A`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ih"))) THEN
    SUBGOAL_THEN `(p:A) IN ring_carrier r /\ ~(p = ring_0 r) /\ ~ring_unit r p`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[ring_prime]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_MUL_POW] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_divides r p (x:A) \/ ring_divides r p y`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM RING_PRIME_DIVIDES_MUL] THEN
      MATCH_MP_TAC RING_DIVIDES_RMUL THEN ASM_SIMP_TAC[RING_POW] THEN
      UNDISCH_TAC `~(k = 0)` THEN SPEC_TAC(`k:num`,`k:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[ring_pow] THEN
      ASM_SIMP_TAC[RING_DIVIDES_RMUL; RING_DIVIDES_REFL; RING_POW];
      MP_TAC(ISPECL [`r:A ring`; `p:A`; `d:A`; `x:A`; `y:A`; `k:num`]
        lemma) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `x1:A` STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "ih" (MP_TAC o SPECL [`x1:A`; `y:A`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `u:A` THEN DISCH_THEN(X_CHOOSE_THEN `e:A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ring_mul r p e:A` THEN
      ASM_SIMP_TAC[RING_MUL; RING_MUL_POW] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul r z (ring_mul r u t) = ring_mul r u (ring_mul r z (t:A))`) THEN
      ASM_SIMP_TAC[RING_POW; RING_UNIT_IN_CARRIER];
      SUBGOAL_THEN `ring_mul r y x = ring_mul r x (y:A)` ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_MUL_SYM]; ALL_TAC] THEN
      MP_TAC(ISPECL [`r:A ring`; `p:A`; `d:A`; `y:A`; `x:A`; `k:num`]
        lemma) THEN
      ANTS_TAC THENL
       [ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y1:A` STRIP_ASSUME_TAC) THEN
      REMOVE_THEN "ih" MATCH_MP_TAC THEN EXISTS_TAC `y1:A` THEN
      ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RING_MUL_SYM]]);;

let UFD_COPRIME_MUL_POW_ASSOCIATES = prove
 (`!r a b c:A k.
        UFD r /\ a IN ring_carrier r /\ b IN ring_carrier r /\
        c IN ring_carrier r /\ ring_coprime r (a,b) /\
        ring_mul r a b = ring_pow r c k
        ==> ?e. e IN ring_carrier r /\ ring_associates r a (ring_pow r e k)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP UFD_COPRIME_MUL_POW) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` (X_CHOOSE_THEN `e:A`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)))) THEN
  EXISTS_TAC `e:A` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[RING_ASSOCIATES_SYM] THEN
  MATCH_MP_TAC RING_ASSOCIATES_LMUL THEN ASM_SIMP_TAC[RING_POW]);;
