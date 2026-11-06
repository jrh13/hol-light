(* ========================================================================= *)
(* The different of an extension of number fields: local bases, traces       *)
(* modulo a prime, ramification and towers.                                  *)
(*                                                                           *)
(* For fields k, l with a ring homomorphism h : k -> l, l a number field     *)
(* (then k is one), O_k, O_l the rings of integers, Tr = algebra_trace (k,l) *)
(* h, C = number_field_codifferent (k,l) h and D = number_field_different    *)
(* (k,l) h (ANT/different.ml; D is a nonzero ideal of O_l,                   *)
(* NUMBER_FIELD_DIFFERENT_NONZERO):                                          *)
(*                                                                           *)
(*   D SUBSET P^(e(P|p) - 1) for every nonzero prime P of O_l                *)
(*                   (NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION)            *)
(*   D SUBSET P <=> 1 < e(P|p), i.e. the primes dividing D are the ramified  *)
(*   primes (NUMBER_FIELD_DIFFERENT_RAMIFIED)                                *)
(*   D_(m/k) = D_(m/l) (D_(l/k) O_m) for k -> l -> m                         *)
(*                   (NUMBER_FIELD_DIFFERENT_TOWER; for the codifferent      *)
(*                   NUMBER_FIELD_CODIFFERENT_TOWER)                         *)
(*                                                                           *)
(* with e(P|p) = ramification_index (O_k,O_l) h P, p the prime below P.      *)
(* Tools proved on the way: a local basis at p, i.e. a basis w of l over k   *)
(* inside O_l whose cosets form a basis of O_l / pO_l over O_k / p, with s   *)
(* in O_k outside p such that s O_l lies in the O_k-span of w                *)
(* (RING_OF_INTEGERS_LOCAL_BASIS, from RING_OF_INTEGERS_BASIS_MOD_PRIME,     *)
(* _FREE and IDEAL_EXTENSION_POW_SUPPLEMENT of ANT/ideal_arith.ml); the      *)
(* trace of O_l / pO_l over O_k / p is Tr reduced modulo p                   *)
(* (RING_OF_INTEGERS_QUOTIENT_TRACE); traces of elements nilpotent modulo    *)
(* pO_l lie in p (NUMBER_FIELD_TRACE_NILPOTENT); x D SUBSET pO_l iff Tr(x    *)
(* O_l) SUBSET p (NUMBER_FIELD_DIFFERENT_TRACE); a nonzero ideal of O_l is   *)
(* the dual of its dual (RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL).                *)
(*                                                                           *)
(* Routes. O_l need not be free over O_k, but it is free at p: lifts of a    *)
(* basis of O_l / pO_l are a basis of l over k                               *)
(* (NUMBER_FIELD_INDEPENDENT_MOD_IDEAL of ANT/relative_degree.ml) whose span *)
(* M satisfies O_l = M + p^t O_l for every t, and with t the valuation of a  *)
(* basis discriminant some s outside p gives s O_l SUBSET M. In such a basis *)
(* the trace of O_l / pO_l is computed from coordinates                      *)
(* (ALGEBRA_TRACE_FREE_BASIS_MATRIX of Library/ring_det.ml), which reduces   *)
(* the ramification statements to traces over finite fields:                 *)
(* for a = (pO_l : P^(e-1)) the elements of a are nilpotent modulo pO_l, and *)
(* for e = 1 the trace of the residue field O_l/P over O_k/p is not          *)
(* identically zero (ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO of             *)
(* ANT/finite_field_trace.ml); the link between D and traces is the          *)
(* cancellation lemma DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE of            *)
(* ANT/dedekind.ml for p b = (c). The tower laws come from Tr_(m/k) =        *)
(* Tr_(l/k) Tr_(m/l) (ALGEBRA_TRACE_NORM_TOWER of Library/fieldtheory.ml)    *)
(* and the double dual.                                                      *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml, Library/ring_det.ml  *)
(* (ALGEBRA_TRACE_FREE_BASIS_MATRIX, ALGEBRA_TRACE_NILPOTENT),               *)
(* ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/ideal_norm.ml, ANT/numfield.ml,  *)
(* ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/finite_field_trace.ml    *)
(* (ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO), ANT/relative_split.ml,        *)
(* ANT/relative_degree.ml, ANT/integrality.ml and ANT/different.ml.          *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/finite_field_trace.ml";;
needs "ANT/relative_split.ml";;
needs "ANT/relative_degree.ml";;
needs "ANT/integrality.ml";;
needs "ANT/different.ml";;

(* ------------------------------------------------------------------------- *)
(* Local bases: a basis of l over k inside O_l spanning O_l up to a          *)
(* denominator outside a given prime p of O_k.                               *)
(* ------------------------------------------------------------------------- *)

(* For a nonzero prime p of O_k some w_i in O_l, i < [l:k], form a basis of  *)
(* O_l / pO_l over O_k / p: every x in O_l is a combination of the w_i with  *)
(* coefficients in O_k modulo pO_l, and a combination in pO_l has all its    *)
(* coefficients in p. (pO_l has N(p)^[l:k] cosets, so the basis has [l:k]    *)
(* elements.)                                                                *)
let RING_OF_INTEGERS_BASIS_MOD_PRIME = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ?w. (!i. i < extension_degree(k,l) h
                     ==> w i IN ring_carrier(ring_of_integers l)) /\
                (!i j. i < extension_degree(k,l) h /\
                       j < extension_degree(k,l) h /\ w i = w j
                       ==> i = j) /\
                (!x. x IN ring_carrier(ring_of_integers l)
                     ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                             ring_sub l x
                              (ring_sum l {i | i < extension_degree(k,l) h}
                                 (\i. ring_mul l (h(c i)) (w i))) IN
                             ideal_generated (ring_of_integers l)
                               (IMAGE h p)) /\
                (!c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                     ring_sum l {i | i < extension_degree(k,l) h}
                       (\i. ring_mul l (h(c i)) (w i)) IN
                     ideal_generated (ring_of_integers l) (IMAGE h p)
                     ==> !i. i < extension_degree(k,l) h ==> c i IN p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `n = extension_degree(k:A ring,l:B ring) h` THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `J:B->bool`]
    RESIDUE_DEGREE_QUOTIENT_RING) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(B->bool)` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `field(quotient_ring (ring_of_integers k) (p:A->bool)) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers k) (p:A->bool))) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FIELD_QUOTIENT_RING; RING_OF_INTEGERS_FINITE_QUOTIENT;
                 MAXIMAL_IMP_RING_IDEAL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`quotient_ring (ring_of_integers k) (p:A->bool)`;
                 `quotient_ring (ring_of_integers l) (J:B->bool)`;
                 `g:(A->bool)->(B->bool)`;
                 `ring_carrier(quotient_ring (ring_of_integers l) (J:B->bool))`]
    FREE_BASIS_EXISTS) THEN
  ASM_REWRITE_TAC[ring_spanning; SUBSET_REFL; RING_SPAN_SELF] THEN
  ABBREV_TAC
   `m = extension_degree
         (quotient_ring (ring_of_integers k) (p:A->bool),
          quotient_ring (ring_of_integers l) (J:B->bool))
         (g:(A->bool)->(B->bool))` THEN
  DISCH_THEN(X_CHOOSE_TAC `G:num->(B->bool)`) THEN
  SUBGOAL_THEN `m:num = n` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`g:(A->bool)->(B->bool)`;
                   `quotient_ring (ring_of_integers k) (p:A->bool)`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`;
                   `m:num`; `G:num->(B->bool)`]
      FREE_BASIS_HAS_SIZE) THEN
    ASM_REWRITE_TAC[HAS_SIZE; GSYM ideal_norm] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
      NUMBER_FIELD_IDEAL_NORM_EXTENSION_Q) THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`]
      IDEAL_NORM_GT_1) THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_FINITE_QUOTIENT; PRIME_IMP_RING_IDEAL] THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[MAXIMAL_IDEAL_IMP_PSUBSET; PSUBSET]; ALL_TAC] THEN
    REWRITE_TAC[EQ_EXP] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?w:num->B. !i. i < n
                   ==> w i IN ring_carrier(ring_of_integers l) /\
                       G i = ring_coset (ring_of_integers l) J (w i)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:num->B` THEN ASM_SIMP_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:(A->bool)->(B->bool)`;
                   `quotient_ring (ring_of_integers k) (p:A->bool)`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`; `n:num`;
                   `G:num->(B->bool)`]
      FREE_BASIS_FIELD) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MATCH_MP_TAC th) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
  SUBGOAL_THEN
   `!c:num->A. (!i. i < n ==> c i IN ring_carrier(ring_of_integers k))
        ==> ring_coset (ring_of_integers l) J
              (ring_sum l {i | i < n}
                 (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))) =
            ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
              (\i. ring_mul (quotient_ring (ring_of_integers l) J)
                     (g(ring_coset (ring_of_integers k) p (c i))) (G i))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
        (\i. ring_mul (quotient_ring (ring_of_integers l) J)
               (ring_coset (ring_of_integers l) J ((h:A->B)((c:num->A) i)))
               (ring_coset (ring_of_integers l) J (w i)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`;
                   `ring_coset (ring_of_integers l) (J:B->bool)`;
                   `{i:num | i < n}`; `\i. (h:A->B)((c:num->A) i)`;
                   `w:num->B`] RING_HOMOMORPHISM_SUM_MUL) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET; FINITE_NUMSEG_LT;
                 IN_ELIM_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_OF_INTEGERS] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:num->A. (!i. i < n ==> c i IN ring_carrier(ring_of_integers k))
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
            ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
      lhand o snd) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_SUM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `ring_coset (ring_of_integers l) J (x:B)` o
      CONJUNCT1 o CONJUNCT2 o GEN_REWRITE_RULE I [free_basis]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num->A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?c. !i. c i IN ring_carrier(ring_of_integers k) /\
              (i < n ==> (a:num->A->bool) i =
                         ring_coset (ring_of_integers k) p (c i))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `i:num < n` THEN ASM_REWRITE_TAC[] THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
        ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN MESON_TAC[];
        MESON_TAC[IN_SUBRING_0; RING_OF_INTEGERS_SUBRING]];
      ALL_TAC] THEN
    EXISTS_TAC `c:num->A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`; `x:B`;
                   `ring_sum l {i | i < n}
                     (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))`]
      RING_COSET_EQ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[RING_OF_INTEGERS];
      DISCH_THEN(SUBST1_TAC o SYM o REWRITE_RULE[RING_OF_INTEGERS])] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) &&
      lhs(concl th) = `ring_coset (ring_of_integers l) J (x:B)`)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->A` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ring_coset (ring_of_integers l) (J:B->bool)`))
        (concl th))) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  X_GEN_TAC `c:num->A` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:(A->bool)->(B->bool)`;
                 `quotient_ring (ring_of_integers k) (p:A->bool)`;
                 `quotient_ring (ring_of_integers l) (J:B->bool)`; `n:num`;
                 `G:num->(B->bool)`;
                 `\i. ring_coset (ring_of_integers k) p ((c:num->A) i)`]
    FREE_BASIS_INDEPENDENT) THEN
  ASM_SIMP_TAC[QUOTIENT_RING_0; RING_COSET_EQ_IDEAL] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:num->A` o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `ring_coset (ring_of_integers l) (J:B->bool)`))
      (concl th))) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                 `ring_sum l {i | i < n}
                   (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))`]
    RING_COSET_EQ_IDEAL) THEN
  ASM_SIMP_TAC[]);;

(* Lifts to O_l of a basis of O_l / pO_l over O_k / p form a basis of l      *)
(* over k (independent by NUMBER_FIELD_INDEPENDENT_MOD_IDEAL, and [l:k] of   *)
(* them).                                                                    *)
let RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE = prove
 (`!k:A ring l:B ring h p w.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\
        (!i. i < extension_degree(k,l) h
             ==> w i IN ring_carrier(ring_of_integers l)) /\
        (!i j. i < extension_degree(k,l) h /\ j < extension_degree(k,l) h /\
               w i = w j ==> i = j) /\
        (!c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
             ring_sum l {i | i < extension_degree(k,l) h}
               (\i. ring_mul l (h(c i)) (w i)) IN
             ideal_generated (ring_of_integers l) (IMAGE h p)
             ==> !i. i < extension_degree(k,l) h ==> c i IN p)
        ==> free_basis (k,l) h (extension_degree(k,l) h) w`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))))) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `n = extension_degree(k:A ring,l:B ring) h` THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->B) i IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "indep") THEN
  SUBGOAL_THEN
   `ring_independent (k,l) (h:A->B) (IMAGE (w:num->B) {i | i < n})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `w:num->B`]
      FREE_BASIS_INDEPENDENT_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`;
                   `{i:num | i < n}`; `w:num->B`]
      NUMBER_FIELD_INDEPENDENT_MOD_IDEAL) THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ q /\ r ==> p /\ q /\ r`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRIME_IMP_RING_IDEAL THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PRIME_IDEAL_IMP_PSUBSET; PSUBSET_IRREFL]; ALL_TAC] THEN
    X_GEN_TAC `u:num->A` THEN STRIP_TAC THEN
    USE_THEN "indep"
     (MP_TAC o SPEC `\i. if i < n then (u:num->A) i else ring_0 k`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      SIMP_TAC[IN_SUBRING_0; RING_OF_INTEGERS_SUBRING];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `!a b s. (a:B) = b /\ b IN s ==> a IN s`) THEN
    EXISTS_TAC `ring_0 l:B` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM];
      MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                     `ideal_generated (ring_of_integers l)
                        (IMAGE (h:A->B) p)`] IN_RING_IDEAL_0) THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; RING_OF_INTEGERS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `w:num->B`]
    FREE_BASIS_FIELD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`] RING_MATROID_BASIS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MATROID_BASIS_LARGE_INDEPENDENT THEN
  UNDISCH_TAC `finite_extension(k:A ring,l:B ring) h` THEN
  ASM_SIMP_TAC[FINITE_EXTENSION_RING_MATROID; RING_MATROID_INDEPENDENT] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `extension_degree(k:A ring,l:B ring) h = n` THEN
  ASM_REWRITE_TAC[extension_degree] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`w:num->B`; `{i:num | i < n}`] CARD_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  SIMP_TAC[LE_REFL]);;

(* Local bases: for a nonzero prime p of O_k there are a basis w of l over k *)
(* inside O_l, lifting a basis of O_l / pO_l over O_k / p, and s in O_k      *)
(* outside p with s O_l inside the O_k-span of w. (With d the discriminant   *)
(* of w, d O_l lies in the span, O_l = span + p^t O_l for all t, and for t = *)
(* v_p(d) the ideal b = (dO_k : p^t) is prime to p with b p^t = dO_k.)       *)
let RING_OF_INTEGERS_LOCAL_BASIS = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ?w s. free_basis (k,l) h (extension_degree(k,l) h) w /\
                  (!i. i < extension_degree(k,l) h
                       ==> w i IN ring_carrier(ring_of_integers l)) /\
                  (!x. x IN ring_carrier(ring_of_integers l)
                       ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                               ring_sub l x
                                (ring_sum l {i | i < extension_degree(k,l) h}
                                   (\i. ring_mul l (h(c i)) (w i))) IN
                               ideal_generated (ring_of_integers l)
                                 (IMAGE h p)) /\
                  (!c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                       ring_sum l {i | i < extension_degree(k,l) h}
                         (\i. ring_mul l (h(c i)) (w i)) IN
                       ideal_generated (ring_of_integers l) (IMAGE h p)
                       ==> !i. i < extension_degree(k,l) h ==> c i IN p) /\
                  s IN ring_carrier(ring_of_integers k) /\ ~(s IN p) /\
                  !x. x IN ring_carrier(ring_of_integers l)
                      ==> ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                              ring_mul l (h s) x =
                              ring_sum l {i | i < extension_degree(k,l) h}
                                (\i. ring_mul l (h(c i)) (w i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_BASIS_MOD_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->B` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `w:num->B`]
    RING_OF_INTEGERS_BASIS_MOD_PRIME_FREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `w:num->B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  ABBREV_TAC `n = extension_degree(k:A ring,l:B ring) h` THEN
  MP_TAC(ISPEC `l:B ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  MP_TAC(ISPEC `k:A ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->B) i IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC
   `M = {y | ?c. (!i. c i IN ring_carrier(ring_of_integers k)) /\
                 y = ring_sum l {i | i < n}
                       (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))}` THEN
  SUBGOAL_THEN
   `!c. (!i. c i IN ring_carrier(ring_of_integers k))
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
            ring_carrier(ring_of_integers l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
      lhand o snd) THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_SUM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `M SUBSET ring_carrier(ring_of_integers l) /\ ring_0 l IN M /\
    (!x y. x IN M /\ y IN M ==> ring_add l x y IN M) /\
    (!a x. a IN ring_carrier(ring_of_integers k) /\ x IN M
           ==> ring_mul l ((h:A->B) a) x IN M)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[];
      EXISTS_TAC `\i:num. ring_0 k:A` THEN
      SIMP_TAC[IN_SUBRING_0; RING_OF_INTEGERS_SUBRING] THEN
      REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0
       (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`)] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_SUM_EQ_0 THEN
      ASM_SIMP_TAC[IN_ELIM_THM; RING_MUL_LZERO];
      MAP_EVERY X_GEN_TAC [`x:B`; `y:B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `d:num->A` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `\i. ring_add k ((c:num->A) i) (d i)` THEN
      ASM_SIMP_TAC[IN_SUBRING_ADD] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_LINCOMB_ADD THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
      MAP_EVERY X_GEN_TAC [`a:A`; `x:B`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `\i. ring_mul k (a:A) ((c:num->A) i)` THEN
      ASM_SIMP_TAC[IN_SUBRING_MUL] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXTENSION_LINCOMB_LMUL THEN
      ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `n:num`; `w:num->B`;
                 `ring_1 l:B`]
    NUMBER_FIELD_CODIFFERENT_BASIS_DISCRIMINANT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_OF_INTEGERS_SUBSET_CODIFFERENT) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING];
    ALL_TAC] THEN
  ABBREV_TAC `d = basis_discriminant (k:A ring,l:B ring) h n w` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!y. y IN ring_carrier(ring_of_integers l)
        ==> ring_mul l ((h:A->B) d) y IN M`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:A->B`; `k:A ring`; `l:B ring`; `n:num`; `w:num->B`;
                   `ring_carrier(ring_of_integers k:A ring)`; `y:B`]
      BASIS_DISCRIMINANT_TIMES_COORD) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN
      ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers l:B ring` RING_MUL)];
      DISCH_TAC] THEN
    EXPAND_TAC "M" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC
     `\i. if i < n
          then ring_mul k (d:A) (basis_coordinates (k,l) (h:A->B) n w y i)
          else ring_0 k` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[IN_SUBRING_0];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum l {i | i < n}
        (\i. ring_mul l ((h:A->B)
               (ring_mul k d (basis_coordinates (k,l) h n w y i)))
             ((w:num->B) i))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC RING_SUM_EQ THEN SIMP_TAC[IN_ELIM_THM]] THEN
    SUBGOAL_THEN `(d:A) IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[EXTENSION_LINCOMB_LMUL; BASIS_COORDINATES_IN_CARRIER;
                 FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC BASIS_COORDINATES_EXPAND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `p:A->bool`; `M:B->bool`]
    IDEAL_EXTENSION_POW_SUPPLEMENT) THEN
  ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET; RING_OF_INTEGERS] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(x:B) IN ring_carrier(ring_of_integers l)`) o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `J:B->bool`)) (concl th) &&
        can (find_term ((=) `ring_sub:B ring->B->B->B`)) (concl th))) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `ring_sum l {i | i < n}
        (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "M" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `c:num->A` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  ABBREV_TAC
   `t = ideal_valuation (ring_of_integers k) p
          (ideal_generated (ring_of_integers k) {d:A})` THEN
  ABBREV_TAC
   `b = ideal_quotient (ring_of_integers k)
          (ideal_generated (ring_of_integers k) {d:A})
          (ideal_pow (ring_of_integers k) p t)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL o check (fun th ->
    concl th = `prime_ideal (ring_of_integers k) (p:A->bool)`)) THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers k) (b:A->bool) /\
    ideal_prod (ring_of_integers k) (ideal_pow (ring_of_integers k) p t) b =
    ideal_generated (ring_of_integers k) {d:A} /\
    ~(b SUBSET p)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`;
                   `ideal_generated (ring_of_integers k) {d:A}`]
      DEDEKIND_IDEAL_SUBSET_POW_VALUATION) THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                 IDEAL_GENERATED_EQ_0; RING_OF_INTEGERS] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "b" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
      MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW];
      DISCH_TAC THEN EXPAND_TAC "b" THEN
      MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN
      ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED;
                   RING_IDEAL_IDEAL_POW; LE_REFL];
      STRIP_TAC THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC t`) THEN
      REWRITE_TAC[ARITH_RULE `~(SUC t <= t)`] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) &&
        rhs(concl th) = `ideal_generated (ring_of_integers k) {d:A}`)) THEN
      REWRITE_TAC[IDEAL_POW_SUC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) IDEAL_PROD_COMM o rand o snd) THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IDEAL_PROD_MONO THEN
      ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  UNDISCH_TAC `~((b:A->bool) SUBSET p)` THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `s:A` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `x:B`] o check (fun th ->
    is_forall(concl th) &&
    can (find_term ((=) `ideal_pow (ring_of_integers k) (p:A->bool)`))
      (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:B` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ring_mul l ((h:A->B) s) x IN M` MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "M" THEN REWRITE_TAC[IN_ELIM_THM]] THEN
  SUBGOAL_THEN
   `(m:B) IN ring_carrier(ring_of_integers l) /\
    (h:A->B) s IN ring_carrier(ring_of_integers l)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l ((h:A->B) s) x =
    ring_add l (ring_mul l (h s) m) (ring_mul l (h s) (ring_sub l x m))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_mul (r:B ring) a x =
      ring_add r (ring_mul r a m) (ring_mul r a (ring_sub r x m))`) THEN
    ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_generated (ring_of_integers l) {(h:A->B) d} =
    ideal_prod (ring_of_integers l)
      (ideal_generated (ring_of_integers l) (IMAGE h b))
      (ideal_generated (ring_of_integers l)
         (IMAGE h (ideal_pow (ring_of_integers k) p t)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                   `h:A->B`; `b:A->bool`;
                   `ideal_pow (ring_of_integers k) p t:A->bool`]
      IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `b:A->bool`;
                   `ideal_pow (ring_of_integers k) p t:A->bool`]
      IDEAL_PROD_COMM) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC RING_IDEAL_IMP_SUBSET THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) &&
      rhs(concl th) = `ideal_generated (ring_of_integers k) {d:A}`)) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                   `h:A->B`; `{d:A}`]
      IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[SING_SUBSET];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l ((h:A->B) s) (ring_sub l x m) IN
    ideal_generated (ring_of_integers l) {h d}`
  MP_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) &&
      lhs(concl th) = `ideal_generated (ring_of_integers l) {(h:A->B) d}`)) THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL_IN_IDEAL_PROD)) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_GENERATED_INC THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `y:A` THEN DISCH_TAC THEN
        MP_TAC(MATCH_MP RING_IDEAL_IMP_SUBSET
         (ASSUME `ring_ideal (ring_of_integers k) (b:A->bool)`)) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:A`) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC IN_SUBRING_SUB THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) d IN ring_carrier(ring_of_integers l)` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `(h:A->B) d`]
    IDEAL_GENERATED_SING_ALT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Traces modulo a prime of O_k.                                             *)
(* ------------------------------------------------------------------------- *)

(* Modulo a nonzero prime p of O_k: the cosets of a local basis are a basis  *)
(* of O_l / pO_l over the residue field O_k / p, and the trace of O_l / pO_l *)
(* is the trace of l over k reduced modulo p.                                *)
let RING_OF_INTEGERS_QUOTIENT_TRACE = prove
 (`!k:A ring l:B ring h p.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k})
        ==> ?g G.
              ring_homomorphism
               (quotient_ring (ring_of_integers k) p,
                quotient_ring (ring_of_integers l)
                  (ideal_generated (ring_of_integers l) (IMAGE h p))) g /\
              (!y. y IN ring_carrier(ring_of_integers k)
                   ==> g(ring_coset (ring_of_integers k) p y) =
                       ring_coset (ring_of_integers l)
                        (ideal_generated (ring_of_integers l) (IMAGE h p))
                        (h y)) /\
              free_basis
               (quotient_ring (ring_of_integers k) p,
                quotient_ring (ring_of_integers l)
                  (ideal_generated (ring_of_integers l) (IMAGE h p)))
               g (extension_degree(k,l) h) G /\
              !x. x IN ring_carrier(ring_of_integers l)
                  ==> algebra_trace
                       (quotient_ring (ring_of_integers k) p,
                        quotient_ring (ring_of_integers l)
                          (ideal_generated (ring_of_integers l) (IMAGE h p)))
                       g
                       (ring_coset (ring_of_integers l)
                         (ideal_generated (ring_of_integers l) (IMAGE h p)) x) =
                      ring_coset (ring_of_integers k) p
                        (algebra_trace (k,l) h x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_LOCAL_BASIS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `n = extension_degree(k:A ring,l:B ring) h` THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->B` (X_CHOOSE_THEN `s:A`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "span") (CONJUNCTS_THEN2 (LABEL_TAC "indep")
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (LABEL_TAC "loc"))))))))) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_CONTRACTION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER)) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                 `h:A->B`; `J:B->bool`]
    RESIDUE_DEGREE_QUOTIENT_RING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(B->bool)` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EXISTS_TAC `g:(A->bool)->(B->bool)` THEN
  EXISTS_TAC `\i. ring_coset (ring_of_integers l) J ((w:num->B) i)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `field(quotient_ring (ring_of_integers k) (p:A->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[FIELD_QUOTIENT_RING]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> (w:num->B) i IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. (!i. i < n ==> c i IN ring_carrier(ring_of_integers k))
        ==> ring_sum l {i | i < n}
              (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)) IN
            ring_carrier(ring_of_integers l) /\
            ring_coset (ring_of_integers l) J
              (ring_sum l {i | i < n} (\i. ring_mul l (h(c i)) (w i))) =
            ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
              (\i. ring_mul (quotient_ring (ring_of_integers l) J)
                     (g(ring_coset (ring_of_integers k) p (c i)))
                     (ring_coset (ring_of_integers l) J (w i)))`
  (LABEL_TAC "cosum") THENL
   [X_GEN_TAC `c:num->A` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_RING_OF_INTEGERS o
        lhand o snd) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers l:B ring` RING_MUL)] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_SUM];
      DISCH_TAC] THEN
    TRANS_TAC EQ_TRANS
     `ring_sum (quotient_ring (ring_of_integers l) J) {i | i < n}
        (\i. ring_mul (quotient_ring (ring_of_integers l) J)
               (ring_coset (ring_of_integers l) J ((h:A->B)((c:num->A) i)))
               (ring_coset (ring_of_integers l) J (w i)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `quotient_ring (ring_of_integers l) (J:B->bool)`;
                   `ring_coset (ring_of_integers l) (J:B->bool)`;
                   `{i:num | i < n}`; `\i. (h:A->B)((c:num->A) i)`;
                   `w:num->B`] RING_HOMOMORPHISM_SUM_MUL) THEN
    ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET; FINITE_NUMSEG_LT;
                 IN_ELIM_THM] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[RING_OF_INTEGERS] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN
    ASM_SIMP_TAC[IN_ELIM_THM; REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `free_basis
     (quotient_ring (ring_of_integers k) (p:A->bool),
      quotient_ring (ring_of_integers l) J) (g:(A->bool)->(B->bool)) n
     (\i. ring_coset (ring_of_integers l) J ((w:num->B) i))`
  ASSUME_TAC THENL
   [REWRITE_TAC[free_basis] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IMP_CONJ; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `x:B` THEN DISCH_TAC THEN
      USE_THEN "span" (MP_TAC o C MATCH_MP (ASSUME
        `(x:B) IN ring_carrier(ring_of_integers l)`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:num->A` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\i. ring_coset (ring_of_integers k) p ((c:num->A) i)` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "cosum" (MP_TAC o SPEC `c:num->A`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
      MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`; `x:B`;
                     `ring_sum l {i | i < n}
                       (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))`]
        RING_COSET_EQ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_THEN(SUBST1_TAC o REWRITE_RULE[RING_OF_INTEGERS])] THEN
      FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `a:num->A->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `?c. !i. c i IN ring_carrier(ring_of_integers k) /\
                (i < n ==> (a:num->A->bool) i =
                           ring_coset (ring_of_integers k) p (c i))`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `i:num` THEN
        ASM_CASES_TAC `i:num < n` THEN ASM_REWRITE_TAC[] THENL
         [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
            is_forall(concl th) &&
            can (find_term ((=) `a:num->A->bool`)) (concl th))) THEN
          ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN MESON_TAC[];
          MESON_TAC[IN_SUBRING_0; RING_OF_INTEGERS_SUBRING]];
        ALL_TAC] THEN
      USE_THEN "indep" (MP_TAC o SPEC `c:num->A`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "cosum" (MP_TAC o SPEC `c:num->A`) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
        MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                       `ring_sum l {i | i < n}
                         (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i))`]
          RING_COSET_EQ_IDEAL) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        FIRST_ASSUM(SUBST1_TAC o check (fun th ->
          is_eq(concl th) &&
          aconv (lhs(concl th))
          `ring_coset (ring_of_integers l) J
            (ring_sum l {i | i < n}
              (\i. ring_mul l ((h:A->B)(c i)) ((w:num->B) i)))`)) THEN
        TRANS_TAC EQ_TRANS
         `ring_0 (quotient_ring (ring_of_integers l) (J:B->bool))` THEN
        CONJ_TAC THENL
         [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
            check (fun th ->
              is_eq(concl th) &&
              rhs(concl th) =
              `ring_0 (quotient_ring (ring_of_integers l) (J:B->bool))`))
          THEN
          MATCH_MP_TAC RING_SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
          MATCH_MP_TAC QUOTIENT_RING_0 THEN FIRST_ASSUM ACCEPT_TAC];
        DISCH_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[QUOTIENT_RING_0] THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`;
                     `(c:num->A) i`] RING_COSET_EQ_IDEAL) THEN
      ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `x:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?C:num->num->A. !j. j < n
            ==> (!i. C j i IN ring_carrier(ring_of_integers k)) /\
                ring_mul l ((h:A->B) s) (ring_mul l x ((w:num->B) j)) =
                ring_sum l {i | i < n} (\i. ring_mul l (h(C j i)) (w i))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN USE_THEN "loc" MATCH_MP_TAC THEN
    REWRITE_TAC[REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)] THEN
    ASM_MESON_TAC[REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(s:A) IN ring_carrier k /\ (h:A->B) s IN ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul k s (algebra_trace (k,l) (h:A->B) x) =
    ring_sum k {i | i < n} (\i. (C:num->num->A) i i)`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) ALGEBRA_TRACE_SCALAR o lhand o snd) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC ALGEBRA_TRACE_FREE_BASIS_MATRIX THEN
    EXISTS_TAC `w:num->B` THEN ASM_SIMP_TAC[RING_MUL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `C:num->num->A`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `algebra_trace (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> (C:num->num->A) i i IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `algebra_trace
     (quotient_ring (ring_of_integers k) p,
      quotient_ring (ring_of_integers l) J) (g:(A->bool)->(B->bool))
     (ring_coset (ring_of_integers l) J (ring_mul l ((h:A->B) s) x)) =
    ring_coset (ring_of_integers k) p
     (ring_mul k s (algebra_trace (k,l) h x))`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      is_eq(concl th) &&
      lhs(concl th) = `ring_mul k s (algebra_trace (k,l) (h:A->B) x)`)) THEN
    MP_TAC(ISPECL
     [`g:(A->bool)->(B->bool)`;
      `quotient_ring (ring_of_integers k) (p:A->bool)`;
      `quotient_ring (ring_of_integers l) (J:B->bool)`; `n:num`;
      `\i. ring_coset (ring_of_integers l) J ((w:num->B) i)`;
      `\j i. ring_coset (ring_of_integers k) p ((C:num->num->A) j i)`;
      `ring_coset (ring_of_integers l) J (ring_mul l ((h:A->B) s) x)`]
     ALGEBRA_TRACE_FREE_BASIS_MATRIX) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN
        EXISTS_TAC `ring_mul l ((h:A->B) s) x` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
         (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `C:num->num->A`)) (concl th) &&
        can (find_term ((=) `ring_mul l ((h:A->B) s)`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "cosum" (MP_TAC o SPEC `(C:num->num->A) j`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2)] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN `ring_mul l x ((w:num->B) j) IN
                    ring_carrier(ring_of_integers l) /\
                    ring_mul l ((h:A->B) s) x IN
                    ring_carrier(ring_of_integers l)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
         (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                     `ring_mul l ((h:A->B) s) x`; `(w:num->B) j`]
        QUOTIENT_RING_MUL) THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(K ALL_TAC) THEN
      AP_TERM_TAC THEN MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`\i. (C:num->num->A) i i`; `{i:num | i < n}`]
     (MATCH_MP RING_HOMOMORPHISM_SUM
       (MATCH_MP RING_HOMOMORPHISM_RING_COSET
         (ASSUME `ring_ideal (ring_of_integers k) (p:A->bool)`)))) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; o_DEF] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC RING_SUM_RING_OF_INTEGERS THEN ASM_SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                 `(h:A->B) s`; `x:B`] QUOTIENT_RING_MUL) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[GSYM(MATCH_MP th (ASSUME
    `(s:A) IN ring_carrier(ring_of_integers k)`))]) o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `g:(A->bool)->(B->bool)`)) (concl th) &&
      can (find_term ((=) `ring_coset (ring_of_integers k) (p:A->bool)`))
        (concl th))) THEN
  SUBGOAL_THEN
   `ring_coset (ring_of_integers k) p (s:A) IN
    ring_carrier(quotient_ring (ring_of_integers k) p) /\
    ring_coset (ring_of_integers l) J (x:B) IN
    ring_carrier(quotient_ring (ring_of_integers l) J) /\
    ring_coset (ring_of_integers k) p (algebra_trace (k,l) (h:A->B) x) IN
    ring_carrier(quotient_ring (ring_of_integers k) p)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ALGEBRA_TRACE_SCALAR o
    lhand o lhand o snd) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`;
                 `s:A`; `algebra_trace (k,l) (h:A->B) x`]
    QUOTIENT_RING_MUL) THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_TAC THEN MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
  MAP_EVERY EXISTS_TAC
   [`quotient_ring (ring_of_integers k) (p:A->bool)`;
    `ring_coset (ring_of_integers k) p (s:A)`] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; ALGEBRA_TRACE_NORM_IN_CARRIER;
               QUOTIENT_RING_0] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`; `s:A`]
    RING_COSET_EQ_IDEAL) THEN
  ASM_SIMP_TAC[]);;

(* Elements of O_l nilpotent modulo pO_l have traces in p (the trace of a    *)
(* nilpotent element of O_l / pO_l over O_k / p vanishes).                   *)
let NUMBER_FIELD_TRACE_NILPOTENT = prove
 (`!k:A ring l:B ring h p x m.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers l) /\
        ring_pow l x m IN ideal_generated (ring_of_integers l) (IMAGE h p)
        ==> algebra_trace (k,l) h x IN p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_QUOTIENT_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(B->bool)`
   (X_CHOOSE_THEN `G:num->(B->bool)` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (J:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN
   `algebra_trace (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`;
                 `algebra_trace (k,l) (h:A->B) x`] RING_COSET_EQ_IDEAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o C MATCH_MP (ASSUME
    `(x:B) IN ring_carrier(ring_of_integers l)`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `algebra_trace:(A->bool)ring#(B->bool)ring->
                            ((A->bool)->(B->bool))->(B->bool)->A->bool`))
        (concl th))) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`] QUOTIENT_RING_0) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th])] THEN
  MATCH_MP_TAC ALGEBRA_TRACE_NILPOTENT THEN
  MAP_EVERY EXISTS_TAC [`extension_degree(k:A ring,l:B ring) h`;
                        `G:num->(B->bool)`] THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; FIELD_QUOTIENT_RING] THEN
  REWRITE_TAC[RING_NILPOTENT] THEN
  ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; EXISTS_TAC `m:num`] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                 `quotient_ring (ring_of_integers l) (J:B->bool)`;
                 `ring_coset (ring_of_integers l) (J:B->bool)`]
    RING_HOMOMORPHISM_POW) THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_RING_COSET] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:B`; `m:num`]) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`]
    QUOTIENT_RING_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                 `ring_pow l (x:B) m`] RING_COSET_EQ_IDEAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_POW)) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* If pO_l = P INTER Q with P maximal and P + Q = O_l (P unramified over p), *)
(* some element of Q has a trace outside p.                                  *)
let NUMBER_FIELD_TRACE_COMAXIMAL = prove
 (`!k:A ring l:B ring h p P Q.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        maximal_ideal (ring_of_integers l) P /\
        ring_ideal (ring_of_integers l) Q /\
        ring_setadd (ring_of_integers l) P Q =
        ring_carrier(ring_of_integers l) /\
        P INTER Q = ideal_generated (ring_of_integers l) (IMAGE h p)
        ==> ?x. x IN Q /\ ~(algebra_trace (k,l) h x IN p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_QUOTIENT_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `(P:B->bool) INTER Q`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->(B->bool)`
   (X_CHOOSE_THEN `G:num->(B->bool)` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers k) (p:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MAXIMAL_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL
   [`quotient_ring (ring_of_integers k) (p:A->bool)`;
    `ring_of_integers l:B ring`; `g:(A->bool)->(B->bool)`;
    `extension_degree(k:A ring,l:B ring) h`; `G:num->(B->bool)`;
    `P:B->bool`; `Q:B->bool`] ALGEBRA_TRACE_QUOTIENT_COMAXIMAL_NONZERO) THEN
  ASM_SIMP_TAC[FIELD_QUOTIENT_RING; RING_OF_INTEGERS_FINITE_QUOTIENT;
               NUMBER_FIELD_IMP_FIELD] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:B` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:B) IN ring_carrier(ring_of_integers l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `algebra_trace (k,l) (h:A->B) x IN ring_carrier(ring_of_integers k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `~(algebra_trace
       (quotient_ring (ring_of_integers k) p,
        quotient_ring (ring_of_integers l) ((P:B->bool) INTER Q))
       (g:(A->bool)->(B->bool))
       (ring_coset (ring_of_integers l) (P INTER Q) x) =
      ring_0 (quotient_ring (ring_of_integers k) (p:A->bool)))` THEN
  FIRST_ASSUM(SUBST1_TAC o C MATCH_MP (ASSUME
    `(x:B) IN ring_carrier(ring_of_integers l)`) o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ring_coset (ring_of_integers k) (p:A->bool)`))
        (concl th) &&
      can (find_term ((=) `algebra_trace (k:A ring,l:B ring) h`))
        (concl th))) THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`] QUOTIENT_RING_0) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`;
                 `algebra_trace (k,l) (h:A->B) x`] RING_COSET_EQ_IDEAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The different and ramification.                                           *)
(* ------------------------------------------------------------------------- *)

(* For y in O_k and nonzero c in O_k: y times the traces Tr(x z), z in O_l,  *)
(* lie in (c) iff h(c)^-1 h(y) x is in C iff h(y) x D SUBSET (h c).          *)
let NUMBER_FIELD_CODIFFERENT_TRACE_DIV = prove
 (`!k:A ring l:B ring h c y x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        c IN ring_carrier(ring_of_integers k) /\ ~(c = ring_0 k) /\
        y IN ring_carrier(ring_of_integers k) /\
        x IN ring_carrier(ring_of_integers l)
        ==> ((!z. z IN ring_carrier(ring_of_integers l)
                  ==> ring_mul k y (algebra_trace (k,l) h (ring_mul l x z)) IN
                      ideal_generated (ring_of_integers k) {c}) <=>
             (!d. d IN number_field_different (k,l) h
                  ==> ring_mul l (h y) (ring_mul l x d) IN
                      ideal_generated (ring_of_integers l) {h c}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION o CONJUNCT1) THEN
  REWRITE_TAC[field_extension] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `(c:A) IN ring_carrier k /\ (y:A) IN ring_carrier k /\
    (x:B) IN ring_carrier l /\
    (h:A->B) c IN ring_carrier(ring_of_integers l) /\
    h c IN ring_carrier l /\ ~(h c = ring_0 l) /\ h y IN ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET; RING_MONOMORPHISM_EQ_0;
                  RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `(h:A->B) c`;
                 `ring_mul l ((h:A->B) y) x`]
    NUMBER_FIELD_CODIFFERENT_DIV) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d IN number_field_different (k,l) (h:A->B) ==> d IN ring_carrier l`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN
    MP_TAC(ISPEC `l:B ring` RING_OF_INTEGERS_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d IN number_field_different (k,l) (h:A->B)
        ==> ring_mul l (ring_mul l (h y) x) d =
            ring_mul l (h y) (ring_mul l x d)`
  (fun th -> SIMP_TAC[th]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[number_field_codifferent; IN_ELIM_THM] THEN
  SUBGOAL_THEN `ring_mul k (ring_inv k c) (y:A) IN ring_carrier k`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_INV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l (ring_inv l ((h:A->B) c)) (ring_mul l (h y) x) =
    ring_mul l (h(ring_mul k (ring_inv k c) y)) x`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL
     (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`); RING_INV] THEN
    ASM_SIMP_TAC[MATCH_MP FIELD_HOMOMORPHISM_INV
                  (CONJ (ASSUME `field(k:A ring)`)
                        (ASSUME `ring_homomorphism(k:A ring,l:B ring) h`))] THEN
    MATCH_MP_TAC RING_MUL_ASSOC THEN ASM_SIMP_TAC[RING_INV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:A->B)(ring_mul k (ring_inv k c) y) IN ring_carrier l`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(z:B) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l (ring_mul l ((h:A->B) (ring_mul k (ring_inv k c) y)) x) z =
    ring_mul l (h (ring_mul k (ring_inv k c) y)) (ring_mul l x z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM RING_MUL_ASSOC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ALGEBRA_TRACE_SCALAR; RING_MUL] THEN
  SUBGOAL_THEN
   `algebra_trace (k,l) (h:A->B) (ring_mul l x z) IN ring_carrier k`
  ASSUME_TAC THENL [REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER]; ALL_TAC] THEN
  ASM_SIMP_TAC[RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING; RING_MUL;
               RING_MUL_ASSOC; RING_INV]);;

(* x D SUBSET pO_l iff the traces Tr(x y), y in O_l, all lie in p: with a    *)
(* nonzero c in p and p b = (c), both sides say that h(c)^-1 h(y) x lies in  *)
(* C for all y in b.                                                         *)
let NUMBER_FIELD_DIFFERENT_TRACE = prove
 (`!k:A ring l:B ring h p x.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers k) p /\ ~(p = {ring_0 k}) /\
        x IN ring_carrier(ring_of_integers l)
        ==> ((!d. d IN number_field_different (k,l) h
                  ==> ring_mul l x d IN
                      ideal_generated (ring_of_integers l) (IMAGE h p)) <=>
             (!y. y IN ring_carrier(ring_of_integers l)
                  ==> algebra_trace (k,l) h (ring_mul l x y) IN p))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL o check (fun th ->
    concl th = `prime_ideal (ring_of_integers k) (p:A->bool)`)) THEN
  SUBGOAL_THEN `?c:A. c IN p /\ ~(c = ring_0 k)` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP RING_IDEAL_IMP_NONEMPTY
     (ASSUME `ring_ideal (ring_of_integers k) (p:A->bool)`)) THEN
    UNDISCH_TAC `~(p = {ring_0 k:A})` THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC
   `b = ideal_quotient (ring_of_integers k)
          (ideal_generated (ring_of_integers k) {c:A}) p` THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers k) (b:A->bool) /\
    ideal_prod (ring_of_integers k) p b =
    ideal_generated (ring_of_integers k) {c:A} /\
    ~(b = {ring_0 k})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "b" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN
      ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; RING_IDEAL_IMP_SUBSET];
      EXPAND_TAC "b" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN
      ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IDEAL_GENERATED] THEN
      MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[SING_SUBSET];
      STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `ideal_prod (ring_of_integers k) p {ring_0 k} =
        ideal_generated (ring_of_integers k) {c:A}` THEN
      ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers k:A ring` IDEAL_PROD_RZERO);
                   RING_IDEAL_IMP_SUBSET] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s:A->bool. (c:A) IN s`) THEN
      ASM_REWRITE_TAC[IN_SING; IN_IDEAL_GENERATED_SELF]];
    ALL_TAC] THEN
  ABBREV_TAC `J = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers l) (J:B->bool) /\
    IMAGE (h:A->B) b SUBSET ring_carrier(ring_of_integers l) /\
    ~(ideal_generated (ring_of_integers l) (IMAGE h b) = {ring_0 l}) /\
    h c IN ring_carrier(ring_of_integers l) /\
    ideal_prod (ring_of_integers l) J
      (ideal_generated (ring_of_integers l) (IMAGE h b)) =
    ideal_generated (ring_of_integers l) {h c}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_IDEAL_IMP_SUBSET;
                    SUBSET];
      MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `b:A->bool`]
        RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                   `h:A->B`; `p:A->bool`; `b:A->bool`]
      IDEAL_PROD_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_of_integers l:B ring`;
                   `h:A->B`; `{c:A}`]
      IDEAL_GENERATED_IMAGE_IDEAL_GENERATED) THEN
    ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:A->bool`; `b:A->bool`;
                 `c:A`] DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_IDEAL_IMP_SUBSET;
               IDEAL_GENERATED_RING_IDEAL; RING_OF_INTEGERS] THEN
  DISCH_THEN(LABEL_TAC "a") THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `J:B->bool`;
                 `IMAGE (h:A->B) b`; `(h:A->B) c`]
    DEDEKIND_IDEAL_MEMBER_PRINCIPAL_MULTIPLE) THEN
  ASM_SIMP_TAC[DEDEKIND_RING_OF_INTEGERS; RING_OF_INTEGERS] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN DISCH_THEN(LABEL_TAC "b") THEN
  SUBGOAL_THEN
   `!y:A. y IN b
          ==> ((!z. z IN ring_carrier(ring_of_integers l)
                    ==> ring_mul k y (algebra_trace (k,l) h (ring_mul l x z))
                        IN ideal_generated (ring_of_integers k) {c}) <=>
               (!d. d IN number_field_different (k,l) h
                    ==> ring_mul l ((h:A->B) y) (ring_mul l x d) IN
                        ideal_generated (ring_of_integers l) {h c}))`
  (LABEL_TAC "c") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NUMBER_FIELD_CODIFFERENT_TRACE_DIV THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. d IN number_field_different (k,l) (h:A->B)
        ==> ring_mul l (x:B) d IN ring_carrier(ring_of_integers l)`
  (LABEL_TAC "xd") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`]
      RING_IDEAL_NUMBER_FIELD_DIFFERENT) THEN
    DISCH_THEN(MP_TAC o MATCH_MP RING_IDEAL_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier(ring_of_integers l)
        ==> algebra_trace (k,l) (h:A->B) (ring_mul l (x:B) z) IN
            ring_carrier(ring_of_integers k)`
  (LABEL_TAC "tr") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NUMBER_FIELD_TRACE_INTEGRAL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `z:B` THEN DISCH_TAC THEN
    USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME
      `(z:B) IN ring_carrier(ring_of_integers l)`)) THEN
    DISCH_THEN(fun th -> USE_THEN "a" (SUBST1_TAC o C MATCH_MP th)) THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "c" (MP_TAC o C MATCH_MP (ASSUME `(y:A) IN b`)) THEN
    MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `d:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
       `(d:B) IN number_field_different (k,l) (h:A->B)`)) THEN
      USE_THEN "xd" (MP_TAC o C MATCH_MP (ASSUME
       `(d:B) IN number_field_different (k,l) (h:A->B)`)) THEN
      DISCH_THEN(fun th -> USE_THEN "b" (SUBST1_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(ACCEPT_TAC o C MATCH_MP (ASSUME `(y:A) IN b`));
      DISCH_THEN(ACCEPT_TAC o C MATCH_MP (ASSUME
       `(z:B) IN ring_carrier(ring_of_integers l)`))];
    X_GEN_TAC `d:B` THEN DISCH_TAC THEN
    USE_THEN "xd" (MP_TAC o C MATCH_MP (ASSUME
      `(d:B) IN number_field_different (k,l) (h:A->B)`)) THEN
    DISCH_THEN(fun th -> USE_THEN "b" (SUBST1_TAC o C MATCH_MP th)) THEN
    X_GEN_TAC `y:A` THEN DISCH_TAC THEN
    USE_THEN "c" (MP_TAC o C MATCH_MP (ASSUME `(y:A) IN b`)) THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [X_GEN_TAC `z:B` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
       `(z:B) IN ring_carrier(ring_of_integers l)`)) THEN
      USE_THEN "tr" (MP_TAC o C MATCH_MP (ASSUME
       `(z:B) IN ring_carrier(ring_of_integers l)`)) THEN
      DISCH_THEN(fun th -> USE_THEN "a" (SUBST1_TAC o C MATCH_MP th)) THEN
      DISCH_THEN(ACCEPT_TAC o C MATCH_MP (ASSUME `(y:A) IN b`));
      DISCH_THEN(ACCEPT_TAC o C MATCH_MP (ASSUME
       `(d:B) IN number_field_different (k,l) (h:A->B)`))]]);;

(* For P above p with e = e(P|p): a = (pO_l : P^(e-1)) lies in P with        *)
(* P^(e-1) a = pO_l; the elements of a are nilpotent modulo pO_l, so their   *)
(* multiples have traces in p, hence a D SUBSET pO_l = P^(e-1) a and D       *)
(* SUBSET P^(e-1) by cancellation.                                           *)
let NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION = prove
 (`!k:A ring l:B ring h P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l})
        ==> number_field_different (k,l) h SUBSET
            ideal_pow (ring_of_integers l) P
              (ramification_index (ring_of_integers k,ring_of_integers l) h P
               - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `P:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `q = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ideal_valuation (ring_of_integers l) P (q:B->bool) =
    ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) P`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ramification_index]; ALL_TAC] THEN
  ABBREV_TAC
   `e = ramification_index (ring_of_integers k,ring_of_integers l)
          (h:A->B) P` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP INTEGRAL_DOMAIN_RING_OF_INTEGERS o
    check (fun th -> concl th = `field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL o
    check (fun th ->
      concl th = `prime_ideal (ring_of_integers l) (P:B->bool)`)) THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (q:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. q SUBSET ideal_pow (ring_of_integers (l:B ring)) P m <=> m <= e`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_IDEAL_SUBSET_POW_VALUATION; RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a. ring_ideal (ring_of_integers l) a /\
        ideal_prod (ring_of_integers l)
          (ideal_pow (ring_of_integers l) P (e - 1)) a = (q:B->bool)`
  (X_CHOOSE_THEN `a:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "aq")))
  THENL
   [EXISTS_TAC `ideal_quotient (ring_of_integers l) q
                  (ideal_pow (ring_of_integers l) P (e - 1)):B->bool` THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_QUOTIENT; RING_IDEAL_IMP_SUBSET;
                 RING_IDEAL_IDEAL_POW] THEN
    MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(ideal_pow (ring_of_integers l) P (e - 1) = {ring_0 (l:B ring)}) /\
    ~(a = {ring_0 (l:B ring)})`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `ideal_pow (ring_of_integers l) P (e - 1):B->bool`;
                   `a:B->bool`] IDEAL_PROD_EQ_ZERO) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_IDEAL_IDEAL_POW] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:B->bool) SUBSET P` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ring_of_integers l:B ring`;
                   `ideal_pow (ring_of_integers l) P (e - 1):B->bool`;
                   `a:B->bool`; `P:B->bool`]
      DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW; RING_OF_INTEGERS] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `ideal_prod (ring_of_integers l)
        (ideal_pow (ring_of_integers l) P (e - 1)) P =
      ideal_pow (ring_of_integers l) (P:B->bool) e`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P:B->bool`; `e - 1`]
        IDEAL_POW_SUC) THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= e ==> SUC(e - 1) = e`] THEN
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW];
      ASM_REWRITE_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN a ==> ring_pow l x e IN (q:B->bool)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier(ring_of_integers l)` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!x:B s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
    EXISTS_TAC `ideal_generated (ring_of_integers l) {ring_pow l x e:B}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_IDEAL_GENERATED_SELF] THEN
      MATCH_MP_TAC IN_SUBRING_POW THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS_SUBRING];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `x:B`; `e:num`]
      IDEAL_POW_PRINCIPAL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC SUBSET_TRANS `ideal_pow (ring_of_integers l) a e:B->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_POW_MONO THEN MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN
      ASM_REWRITE_TAC[SING_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `a:B->bool`; `e - 1`]
      IDEAL_POW_SUC) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= e ==> SUC(e - 1) = e`] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "aq" (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    TRANS_TAC SUBSET_TRANS
     `ideal_prod (ring_of_integers l) a
        (ideal_pow (ring_of_integers l) P (e - 1)):B->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_PROD_MONO THEN
      ASM_SIMP_TAC[IDEAL_POW_MONO; SUBSET_REFL];
      MATCH_MP_TAC(SET_RULE `(s:B->bool) = t ==> s SUBSET t`) THEN
      MATCH_MP_TAC IDEAL_PROD_COMM THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x d. x IN a /\ d IN number_field_different (k,l) (h:A->B)
          ==> ring_mul l x d IN (q:B->bool)`
  (LABEL_TAC "div") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:B) IN ring_carrier(ring_of_integers l)` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `x:B`]
      NUMBER_FIELD_DIFFERENT_TRACE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      DISCH_THEN(MP_TAC o SPEC `d:B`) THEN ASM_REWRITE_TAC[]] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    MATCH_MP_TAC NUMBER_FIELD_TRACE_NILPOTENT THEN
    EXISTS_TAC `e:num` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `ring_mul l x y IN (a:B->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers l:B ring`; `a:B->bool`; `x:B`; `y:B`]
        IN_RING_IDEAL_RMUL) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_mul l x (y:B)` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `ring_pow:B ring->B->num->B`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `a:B->bool`;
                 `number_field_different (k,l) (h:A->B)`;
                 `ideal_pow (ring_of_integers l) P (e - 1):B->bool`]
    DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW; RING_IDEAL_NUMBER_FIELD_DIFFERENT;
                  RING_OF_INTEGERS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `ideal_prod (ring_of_integers l) a
      (ideal_pow (ring_of_integers l) P (e - 1)) = (q:B->bool)`
  SUBST1_TAC THENL
   [USE_THEN "aq" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC IDEAL_PROD_COMM THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  MAP_EVERY X_GEN_TAC [`x:B`; `d:B`] THEN STRIP_TAC THEN
  USE_THEN "div" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* If e = 1 then pO_l = P Q with P + Q = O_l and P INTER Q = pO_l; some y    *)
(* in Q has a trace outside p, while D SUBSET P would give y D SUBSET P Q =  *)
(* pO_l and all traces Tr(y z) in p.                                         *)
let NUMBER_FIELD_DIFFERENT_RAMIFIED = prove
 (`!k:A ring l:B ring h P.
        field k /\ number_field l /\ ring_homomorphism(k,l) h /\
        prime_ideal (ring_of_integers l) P /\ ~(P = {ring_0 l})
        ==> (number_field_different (k,l) h SUBSET P <=>
             1 < ramification_index (ring_of_integers k,ring_of_integers l)
                   h P)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `P:B->bool`]
      NUMBER_FIELD_DIFFERENT_SUBSET_RAMIFICATION) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(SET_RULE
     `t SUBSET u ==> s SUBSET t ==> (s:B->bool) SUBSET u`) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV
     [GSYM(MATCH_MP IDEAL_POW_1 (MATCH_MP PRIME_IMP_RING_IDEAL th))]) THEN
    MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_IDEAL_IMP_SUBSET] THEN
    ASM_ARITH_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `P:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_BELOW) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:A->bool` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    RING_OF_INTEGERS_PRIME_IDEAL_CONTRACTION) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `P:B->bool`]
    NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`]
    RING_OF_INTEGERS_IDEAL_EXTENSION_PRIME) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `q = ideal_generated (ring_of_integers l) (IMAGE (h:A->B) p)` THEN
  STRIP_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ideal_valuation (ring_of_integers l) P (q:B->bool) =
    ramification_index (ring_of_integers k,ring_of_integers l) (h:A->B) P`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ramification_index]; ALL_TAC] THEN
  ABBREV_TAC
   `e = ramification_index (ring_of_integers k,ring_of_integers l)
          (h:A->B) P` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS o
    check (fun th -> concl th = `number_field(l:B ring)`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL o
    check (fun th ->
      concl th = `prime_ideal (ring_of_integers l) (P:B->bool)`)) THEN
  SUBGOAL_THEN `maximal_ideal (ring_of_integers l) (P:B->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_ideal (ring_of_integers l) (q:B->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. q SUBSET ideal_pow (ring_of_integers (l:B ring)) P m <=> m <= e`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[DEDEKIND_IDEAL_SUBSET_POW_VALUATION; RING_OF_INTEGERS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `e = 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `?Q. ring_ideal (ring_of_integers l) Q /\
        ideal_prod (ring_of_integers l) P Q = (q:B->bool)`
  (X_CHOOSE_THEN `Q:B->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pq")))
  THENL
   [EXISTS_TAC `ideal_quotient (ring_of_integers l) q (P:B->bool)` THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_QUOTIENT; RING_IDEAL_IMP_SUBSET] THEN
    MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN ASM_SIMP_TAC[IDEAL_POW_1; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Q:B->bool) SUBSET P)` ASSUME_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `2`) THEN
    REWRITE_TAC[ARITH_RULE `~(2 <= 1)`] THEN
    USE_THEN "pq" (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[num_CONV `2`; num_CONV `1`; IDEAL_POW_SUC; IDEAL_POW_0] THEN
    SIMP_TAC[IDEAL_PROD_CARRIER;
             ASSUME `ring_ideal (ring_of_integers l) (P:B->bool)`] THEN
    MATCH_MP_TAC IDEAL_PROD_MONO THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_setadd (ring_of_integers l) P Q = ring_carrier(ring_of_integers l) /\
    P INTER Q = (q:B->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MAXIMAL_IDEAL_COMAXIMAL];
      DISCH_TAC THEN USE_THEN "pq" (SUBST1_TAC o SYM) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC IDEAL_PROD_COMAXIMAL THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`;
                 `P:B->bool`; `Q:B->bool`]
    NUMBER_FIELD_TRACE_COMAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:B` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(algebra_trace (k,l) (h:A->B) y IN p)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:B) IN ring_carrier(ring_of_integers l)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h:A->B`; `p:A->bool`; `y:B`]
    NUMBER_FIELD_DIFFERENT_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `ring_1 l:B`) THEN
    SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING] THEN
    SUBGOAL_THEN `(y:B) IN ring_carrier l` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
      ASM_SIMP_TAC[RING_MUL_RID]]] THEN
  X_GEN_TAC `d:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(d:B) IN P /\ d IN ring_carrier(ring_of_integers l)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RING_IDEAL_IMP_SUBSET;
                  RING_IDEAL_NUMBER_FIELD_DIFFERENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_mul l y d = ring_mul l d (y:B)` SUBST1_TAC THENL
   [MATCH_MP_TAC RING_MUL_SYM THEN
    ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
    ALL_TAC] THEN
  USE_THEN "pq" (SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `P:B->bool`; `Q:B->bool`;
                 `d:B`; `y:B`] RING_MUL_IN_IDEAL_PROD) THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Towers.                                                                   *)
(* ------------------------------------------------------------------------- *)

(* For a nonzero ideal E of O_l, the elements y of O_l with y C SUBSET O_l   *)
(* for C = {x | x E SUBSET O_l} are those of E (E is invertible).            *)
let RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL = prove
 (`!l:B ring E.
        number_field l /\ ring_ideal (ring_of_integers l) E /\
        ~(E = {ring_0 l})
        ==> {y | y IN ring_carrier(ring_of_integers l) /\
                 !x. x IN ring_carrier l /\
                     (!e. e IN E
                          ==> ring_mul l x e IN
                              ring_carrier(ring_of_integers l))
                     ==> ring_mul l y x IN ring_carrier(ring_of_integers l)} =
            E`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  SUBGOAL_THEN `E SUBSET ring_carrier(ring_of_integers(l:B ring))` ASSUME_TAC
  THENL [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:B` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [STRIP_TAC;
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `ring_mul l y x = ring_mul l x (y:B)` SUBST1_TAC THENL
     [MATCH_MP_TAC RING_MUL_SYM THEN
      ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
      ASM_SIMP_TAC[]]] THEN
  SUBGOAL_THEN `?d:B. d IN E /\ ~(d = ring_0 l)` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP RING_IDEAL_IMP_NONEMPTY
     (ASSUME `ring_ideal (ring_of_integers l) (E:B->bool)`)) THEN
    UNDISCH_TAC `~(E = {ring_0 l:B})` THEN
    MP_TAC(ISPECL [`ring_of_integers l:B ring`; `E:B->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:B) IN ring_carrier(ring_of_integers l) /\
                d IN ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC
   `G = ideal_quotient (ring_of_integers l)
          (ideal_generated (ring_of_integers l) {d:B}) E` THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers l) (G:B->bool) /\
    ideal_prod (ring_of_integers l) E G =
    ideal_generated (ring_of_integers l) {d:B} /\
    ~(G = {ring_0 l})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ q /\ (p /\ q ==> r) ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "G" THEN MATCH_MP_TAC RING_IDEAL_IDEAL_QUOTIENT THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
      EXPAND_TAC "G" THEN MATCH_MP_TAC DEDEKIND_IDEAL_PROD_IDEAL_QUOTIENT THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
      MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[SING_SUBSET];
      STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `ideal_prod (ring_of_integers l) E {ring_0 l} =
        ideal_generated (ring_of_integers l) {d:B}` THEN
      ASM_SIMP_TAC[REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers l:B ring` IDEAL_PROD_RZERO)] THEN
      DISCH_THEN(MP_TAC o AP_TERM `\s:B->bool. (d:B) IN s`) THEN
      ASM_REWRITE_TAC[IN_SING; IN_IDEAL_GENERATED_SELF]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `G:B->bool`;
                 `ideal_generated (ring_of_integers l) {y:B}`; `E:B->bool`]
    DEDEKIND_IDEAL_PROD_SUBSET_CANCEL) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; RING_OF_INTEGERS] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_IDEAL_GENERATED_SELF]] THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `G:B->bool`; `E:B->bool`]
    IDEAL_PROD_COMM) THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
  MAP_EVERY X_GEN_TAC [`f:B`; `v:B`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_of_integers l:B ring`; `y:B`]
    IDEAL_GENERATED_SING_ALT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    UNDISCH_TAC `(v:B) IN ideal_generated (ring_of_integers l) {y}` THEN
    REWRITE_TAC[th; IN_ELIM_THM; RING_OF_INTEGERS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:B` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:B) IN ring_carrier(ring_of_integers l) /\
                f IN ring_carrier l /\ t IN ring_carrier l /\
                y IN ring_carrier l`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET; RING_OF_INTEGERS_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ring_mul l (ring_inv l d) (f:B)` o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `y:B`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; RING_INV] THEN X_GEN_TAC `e:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(e:B) IN ring_carrier(ring_of_integers l) /\
                  e IN ring_carrier l`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul l (ring_mul l (ring_inv l d) f) e =
      ring_mul l (ring_inv l d) (ring_mul l f (e:B))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(RING_RULE
       `ring_mul (r:B ring) (ring_mul r i f) e =
        ring_mul r i (ring_mul r f e)`) THEN
      ASM_SIMP_TAC[RING_INV];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:B ring`; `d:B`; `ring_mul l f (e:B)`]
      RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING) THEN
    ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(f:B) IN G` THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[ideal_quotient; IN_ELIM_THM; RING_OF_INTEGERS] THEN
    DISCH_THEN(MP_TAC o SPEC `e:B` o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `d:B`; `ring_mul l f (ring_mul l y (t:B))`]
    RING_OF_INTEGERS_IN_IDEAL_GENERATED_SING) THEN
  ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `ring_mul l (ring_inv l d) (ring_mul l f (ring_mul l y t)) =
    ring_mul l t (ring_mul l y (ring_mul l (ring_inv l d) (f:B)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(RING_RULE
     `ring_mul (r:B ring) i (ring_mul r f (ring_mul r y t)) =
      ring_mul r t (ring_mul r y (ring_mul r i f))`) THEN
    ASM_SIMP_TAC[RING_INV];
    MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
     (ISPEC `ring_of_integers l:B ring` RING_MUL)) THEN
    ASM_REWRITE_TAC[]]);;

(* The tower law for the codifferent: for k -> l -> m, C_{m/k} consists of   *)
(* the x in m with x D_{m/l} D_{l/k} SUBSET O_m (Tr_{m/k} = Tr_{l/k}         *)
(* Tr_{m/l}, and Tr_{m/l}(x O_m) is an O_l-module).                          *)
let NUMBER_FIELD_CODIFFERENT_TOWER = prove
 (`!k:A ring l:B ring m:C ring h1 h2.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2
        ==> number_field_codifferent (k,m) (h2 o h1) =
            {x | x IN ring_carrier m /\
                 !e. e IN ideal_prod (ring_of_integers m)
                            (number_field_different (l,m) h2)
                            (ideal_generated (ring_of_integers m)
                              (IMAGE h2 (number_field_different (k,l) h1)))
                     ==> ring_mul m x e IN ring_carrier(ring_of_integers m)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `h2:B->C`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `h2:B->C`] NUMBER_FIELD_TOWER_LAW) THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h1:A->B`] NUMBER_FIELD_TOWER_LAW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION o CONJUNCT1) THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP FINITE_IMP_FIELD_EXTENSION o CONJUNCT1) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD o
    check (fun th -> concl th = `number_field(m:C ring)`)) THEN
  SUBGOAL_THEN
   `ring_homomorphism(k:A ring,m:C ring) ((h2:B->C) o (h1:A->B))`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_COMPOSE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h1:A->B`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `h2:B->C`]
    RING_HOMOMORPHISM_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER) o check (fun th ->
     concl th = `ring_homomorphism
                   (ring_of_integers l,ring_of_integers m) (h2:B->C)`)) THEN
  ABBREV_TAC `D1 = number_field_different (k,l) (h1:A->B)` THEN
  ABBREV_TAC `D2 = number_field_different (l,m) (h2:B->C)` THEN
  SUBGOAL_THEN
   `(D1:B->bool) SUBSET ring_carrier(ring_of_integers (l:B ring)) /\
    (D2:C->bool) SUBSET ring_carrier(ring_of_integers(m:C ring))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D1"; "D2"] THEN
    SIMP_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_NUMBER_FIELD_DIFFERENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h2:B->C) D1 SUBSET ring_carrier(ring_of_integers m)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* The product ideal is generated by the products e2 h2(e1). *)
  SUBGOAL_THEN
   `!x. x IN ring_carrier m
        ==> ((!e. e IN ideal_prod (ring_of_integers m) D2
                         (ideal_generated (ring_of_integers m)
                            (IMAGE (h2:B->C) D1))
                  ==> ring_mul m x e IN ring_carrier(ring_of_integers m)) <=>
             (!e1 e2. e1 IN D1 /\ e2 IN D2
                      ==> ring_mul m x (ring_mul m e2 (h2 e1)) IN
                          ring_carrier(ring_of_integers m)))`
  (LABEL_TAC "gen") THENL
   [X_GEN_TAC `x:C` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `ideal_prod (ring_of_integers m) D2
        (ideal_generated (ring_of_integers m) (IMAGE (h2:B->C) D1)) =
      ideal_prod (ring_of_integers m) D2 (IMAGE h2 D1)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers m:C ring`; `D2:C->bool`;
                     `IMAGE (h2:B->C) D1`] IDEAL_PROD_IDEAL_GENERATED) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC IDEAL_GENERATED_RING_IDEAL THEN
      EXPAND_TAC "D2" THEN REWRITE_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT];
      ALL_TAC] THEN
    EQ_TAC THEN DISCH_TAC THENL
     [MAP_EVERY X_GEN_TAC [`e1:B`; `e2:C`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers m:C ring` RING_MUL_IN_IDEAL_PROD)) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `ideal_prod (ring_of_integers m) D2 (IMAGE (h2:B->C) D1) SUBSET
      {e | e IN ring_carrier(ring_of_integers m) /\
           ring_mul m x e IN ring_carrier(ring_of_integers m)}`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC IDEAL_PROD_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[ring_ideal; SUBSET; IN_ELIM_THM; RING_OF_INTEGERS] THEN
      MP_TAC(ISPEC `m:C ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
      REWRITE_TAC[subring_of; SUBSET] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[RING_MUL_RZERO; RING_MUL_RNEG; RING_ADD_LDISTRIB] THEN
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `ring_mul m x (ring_mul m x' y) =
                    ring_mul m x' (ring_mul (m:C ring) x y)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_mul (r:C ring) x (ring_mul r a z) =
          ring_mul r a (ring_mul r x z)`) THEN
        ASM_SIMP_TAC[];
        ASM_SIMP_TAC[]];
      MAP_EVERY X_GEN_TAC [`e2:C`; `b:C`] THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; RING_OF_INTEGERS] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `e1:B` STRIP_ASSUME_TAC)) THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers m:C ring` RING_MUL)) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:C` THEN
  REWRITE_TAC[number_field_codifferent; IN_ELIM_THM] THEN
  ASM_CASES_TAC `(x:C) IN ring_carrier m` THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "gen" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `(x:C) IN ring_carrier m`)]) THEN
  (* Tr_{m/k} = Tr_{l/k} Tr_{m/l}. *)
  SUBGOAL_THEN
   `!z. z IN ring_carrier m
        ==> algebra_trace (k,m) ((h2:B->C) o (h1:A->B)) z =
            algebra_trace (k,l) h1 (algebra_trace (l,m) h2 z)`
  (fun th -> SIMP_TAC[th; RING_MUL;
                      REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET;
                      ASSUME `(x:C) IN ring_carrier m`]) THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h1:A->B`; `h2:B->C`; `k:A ring`; `l:B ring`; `m:C ring`;
                   `z:C`] ALGEBRA_TRACE_NORM_TOWER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* Step A: traces over l of x O_m lie in C_{l/k}. *)
  TRANS_TAC EQ_TRANS
   `!z. z IN ring_carrier(ring_of_integers m)
        ==> algebra_trace (l,m) (h2:B->C) (ring_mul m x z) IN
            number_field_codifferent (k,l) (h1:A->B)` THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THENL
     [X_GEN_TAC `z:C` THEN DISCH_TAC THEN
      REWRITE_TAC[number_field_codifferent; IN_ELIM_THM;
                  ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
      X_GEN_TAC `y:B` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(z:C) IN ring_carrier m /\ (y:B) IN ring_carrier l /\
        (h2:B->C) y IN ring_carrier(ring_of_integers m) /\
        h2 y IN ring_carrier m`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET;
                      RING_HOMOMORPHISM_IN_CARRIER];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_mul l (algebra_trace (l,m) (h2:B->C) (ring_mul m x z)) y =
        algebra_trace (l,m) h2 (ring_mul m x (ring_mul m z (h2 y)))`
      SUBST1_TAC THENL
       [MP_TAC(ISPECL [`h2:B->C`; `l:B ring`; `m:C ring`; `y:B`;
                       `ring_mul m x (z:C)`] ALGEBRA_TRACE_SCALAR) THEN
        ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(K ALL_TAC) THEN
        CONV_TAC SYM_CONV THEN
        SUBGOAL_THEN
         `ring_mul m x (ring_mul m z ((h2:B->C) y)) =
          ring_mul m (h2 y) (ring_mul m x z)`
        SUBST1_TAC THENL
         [MATCH_MP_TAC(RING_RULE
           `ring_mul (r:C ring) x (ring_mul r z a) =
            ring_mul r a (ring_mul r x z)`) THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`h2:B->C`; `l:B ring`; `m:C ring`; `y:B`;
                       `ring_mul m x (z:C)`] ALGEBRA_TRACE_SCALAR) THEN
        ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC RING_MUL_SYM THEN
        ASM_REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[RING_OF_INTEGERS]
       (ISPEC `ring_of_integers m:C ring` RING_MUL)) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `z:C` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
       `(z:C) IN ring_carrier(ring_of_integers m)`)) THEN
      REWRITE_TAC[number_field_codifferent; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `ring_1 l:B` o CONJUNCT2) THEN
      SIMP_TAC[IN_SUBRING_1; RING_OF_INTEGERS_SUBRING] THEN
      SIMP_TAC[RING_MUL_RID; ALGEBRA_TRACE_NORM_IN_CARRIER]];
    ALL_TAC] THEN
  (* Step B: C_{l/k} = (O_l : D1). *)
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `h1:A->B`]
    NUMBER_FIELD_CODIFFERENT_DIFFERENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; ALGEBRA_TRACE_NORM_IN_CARRIER] THEN
  (* Step C: Tr_{m/l}(x z) e1 = Tr_{m/l}(x h2(e1) z) and C_{m/l}. *)
  TRANS_TAC EQ_TRANS
   `!e1. e1 IN D1
         ==> ring_mul m x ((h2:B->C) e1) IN
             number_field_codifferent (l,m) h2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[number_field_codifferent; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `!e1. e1 IN D1 ==> ring_mul m x ((h2:B->C) e1) IN ring_carrier m`
    (fun th -> SIMP_TAC[th]) THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_OF_INTEGERS_SUBSET;
                    SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!z e1. z IN ring_carrier(ring_of_integers m) /\ e1 IN D1
             ==> ring_mul l
                   (algebra_trace (l,m) (h2:B->C) (ring_mul m x z)) e1 =
                 algebra_trace (l,m) h2 (ring_mul m (ring_mul m x (h2 e1)) z)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `(z:C) IN ring_carrier m /\ (e1:B) IN ring_carrier l /\
        (h2:B->C) e1 IN ring_carrier m`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET;
                      RING_HOMOMORPHISM_IN_CARRIER];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `ring_mul m (ring_mul m x ((h2:B->C) e1)) z =
        ring_mul m (h2 e1) (ring_mul m x z)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_mul (r:C ring) (ring_mul r x a) z =
          ring_mul r a (ring_mul r x z)`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`h2:B->C`; `l:B ring`; `m:C ring`; `e1:B`;
                     `ring_mul m x (z:C)`] ALGEBRA_TRACE_SCALAR) THEN
      ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC RING_MUL_SYM THEN
      ASM_REWRITE_TAC[ALGEBRA_TRACE_NORM_IN_CARRIER];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* Step D: C_{m/l} = (O_m : D2). *)
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `h2:B->C`]
    NUMBER_FIELD_CODIFFERENT_DIFFERENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `!e1 e2. e1 IN D1 /\ e2 IN D2
            ==> ring_mul m (ring_mul m x ((h2:B->C) e1)) e2 =
                ring_mul m x (ring_mul m e2 (h2 e1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul (r:C ring) (ring_mul r x a) e =
      ring_mul r x (ring_mul r e a)`) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_OF_INTEGERS_SUBSET;
                  SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e1. e1 IN D1 ==> ring_mul m x ((h2:B->C) e1) IN ring_carrier m`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_OF_INTEGERS_SUBSET;
                  SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[]);;

(* The tower law for the different: D_{m/k} = D_{m/l} (D_{l/k} O_m).         *)
let NUMBER_FIELD_DIFFERENT_TOWER = prove
 (`!k:A ring l:B ring m:C ring h1 h2.
        field k /\ field l /\ number_field m /\
        ring_homomorphism(k,l) h1 /\ ring_homomorphism(l,m) h2
        ==> number_field_different (k,m) (h2 o h1) =
            ideal_prod (ring_of_integers m)
              (number_field_different (l,m) h2)
              (ideal_generated (ring_of_integers m)
                 (IMAGE h2 (number_field_different (k,l) h1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `h2:B->C`]
    NUMBER_FIELD_HOMOMORPHIC_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ABBREV_TAC
   `E = ideal_prod (ring_of_integers m)
          (number_field_different (l,m) (h2:B->C))
          (ideal_generated (ring_of_integers m)
             (IMAGE h2 (number_field_different (k,l) (h1:A->B))))` THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers m) (E:C->bool) /\ ~(E = {ring_0 m})`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[RING_IDEAL_IDEAL_PROD] THEN
    MP_TAC(ISPECL [`ring_of_integers m:C ring`;
                   `number_field_different (l,m) (h2:B->C)`;
                   `ideal_generated (ring_of_integers (m:C ring))
                     (IMAGE (h2:B->C)
                       (number_field_different (k,l) (h1:A->B)))`]
      IDEAL_PROD_EQ_ZERO) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD;
                 RING_IDEAL_NUMBER_FIELD_DIFFERENT;
                 RING_IDEAL_IDEAL_GENERATED; RING_OF_INTEGERS] THEN
    DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPECL [`l:B ring`; `m:C ring`; `h2:B->C`;
                   `number_field_different (k,l) (h1:A->B)`]
      RING_OF_INTEGERS_IDEAL_EXTENSION) THEN
    ASM_REWRITE_TAC[RING_IDEAL_NUMBER_FIELD_DIFFERENT] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[NUMBER_FIELD_DIFFERENT_NONZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:C ring`; `E:C->bool`]
    RING_OF_INTEGERS_IDEAL_DOUBLE_DUAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[number_field_different] THEN
  MP_TAC(ISPECL [`k:A ring`; `l:B ring`; `m:C ring`; `h1:A->B`; `h2:B->C`]
    NUMBER_FIELD_CODIFFERENT_TOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;
