(* ========================================================================= *)
(* The integral closure of a Dedekind domain in a finite separable extension *)
(* of its fraction field is a Dedekind domain.                               *)
(*                                                                           *)
(* Main results, for a domain r with fraction field k along h and an         *)
(* extension l of k along g: every x of l integral over k becomes integral   *)
(* over r after multiplication by some h(d) with d nonzero                   *)
(* (INTEGRAL_ELEMENT_DENOMINATOR), so for l algebraic over k the integral    *)
(* closure of r in l has fraction field l                                    *)
(* (FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE); for r integrally closed and l      *)
(* finite separable over k the integral closure lies in the span over r of   *)
(* finitely many elements (INTEGRAL_CLOSURE_SUBSET_SPAN, the 1/D b_i for a   *)
(* basis b of integral elements with discriminant D). The Dedekind theorem   *)
(* (DEDEKIND_INTEGRAL_CLOSURE): for r Dedekind and l finite separable over   *)
(* k, subring_generated l {y | integral_element (r,l) (g o h) y} is a        *)
(* Dedekind domain.                                                          *)
(*                                                                           *)
(* Routes: the coordinates c_i of an integral x in the basis b satisfy D c_i *)
(* IN h(r) since the traces Tr(b_i b_j) and Tr(b_i x) lie in h(r)            *)
(* (INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM, BASIS_DISCRIMINANT_TIMES_COORD),   *)
(* and D is nonzero since the trace form of a separable extension is         *)
(* nondegenerate (ALGEBRA_TRACE_SURJECTIVE, BASIS_DISCRIMINANT_EQ_0); the    *)
(* Krull-Akizuki theorem is not needed. The closure is integrally closed     *)
(* (INTEGRALLY_CLOSED_INTEGRAL_CLOSURE), Noetherian since its ideals are     *)
(* submodules of that finitely generated module over r                       *)
(* (NOETHERIAN_RING_SPAN_SUBMODULE of Library/fieldtheory.ml: over a         *)
(* Noetherian ring a submodule of a finitely generated module is finitely    *)
(* generated, with modules as spans in a ring along a homomorphism), and     *)
(* nonzero primes are maximal since they lie over nonzero, hence maximal,    *)
(* primes of r (INTEGRAL_EXTENSION_PRIME_NONZERO,                            *)
(* INTEGRAL_EXTENSION_MAXIMAL_IDEAL).                                        *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/fieldtheory.ml (ring_span, finite    *)
(* and separable extensions, ALGEBRA_TRACE_SURJECTIVE,                       *)
(* NOETHERIAN_RING_SPAN_SUBMODULE), Library/ring_det.ml (free bases,         *)
(* basis_discriminant, FREE_BASIS_SCALE), ANT/integral.ml,                   *)
(* ANT/integral_primes.ml and ANT/dedekind.ml.                               *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/ring_det.ml";;
needs "ANT/integral.ml";;
needs "ANT/integral_primes.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/numfield.ml";;

(* ------------------------------------------------------------------------- *)
(* Clearing denominators: for k a fraction field of r along h and x in l     *)
(* integral over k along g, some nonzero d in r makes h(d) x integral over r.*)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_DENOMINATOR = prove
 (`!r k l (h:A->B) (g:B->C) x.
        field_of_fractions (r,k) h /\ ring_homomorphism(k,l) g /\
        integral_element (k,l) g x
        ==> ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                integral_element (r,l) (g o h) (ring_mul l (g(h d)) x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `(x:C) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:B ring`; `l:C ring`; `g:B->C`; `x:C`]
    INTEGRAL_ELEMENT_RELATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `a:num->B`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `a:num->B`;
                 `{i:num | i < n}`] FRACTION_FIELD_COMMON_DENOMINATOR) THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->A`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism] o check (fun th ->
      concl th = `ring_homomorphism(r:A ring,k:B ring) h`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[SUBSET; FORALL_IN_IMAGE] o
    GEN_REWRITE_RULE I [ring_homomorphism] o check (fun th ->
      concl th = `ring_homomorphism(k:B ring,l:C ring) g`)) THEN
  ABBREV_TAC `D = (g:B->C)((h:A->B) d)` THEN
  SUBGOAL_THEN `(D:C) IN ring_carrier l` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_ELEMENT_FROM_RELATION THEN
  MAP_EVERY EXISTS_TAC
   [`n:num`; `\i. ring_mul r (ring_pow r d (n - 1 - i)) ((b:num->A) i)`] THEN
  ASM_SIMP_TAC[RING_MUL; RING_POW] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) d IN ring_carrier k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> (g:B->C)((a:num->B) i) IN ring_carrier l`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sum l {i | i < n}
      (\i. ring_mul l (((g:B->C) o (h:A->B))
                         (ring_mul r (ring_pow r d (n - 1 - i)) (b i)))
                      (ring_pow l (ring_mul l D x) i)) =
    ring_sum l {i | i < n}
      (\i. ring_mul l (ring_pow l D n)
                      (ring_mul l (g((a:num->B) i)) (ring_pow l x i)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(b:num->A) i IN ring_carrier r /\
      ring_mul k ((h:A->B) d) ((a:num->B) i) = h(b i) /\
      a i IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `(h:A->B)(ring_mul r (ring_pow r d (n - 1 - i)) ((b:num->A) i)) =
      ring_mul k (ring_pow k (h d) (n - 1 - i))
                 (ring_mul k (h d) ((a:num->B) i))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_POW] THEN
      FIRST_ASSUM((fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW th]) o
        check (fun th -> concl th = `ring_homomorphism(r:A ring,k:B ring) h`));
      ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POW; RING_MUL] THEN
    FIRST_ASSUM((fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_POW th]) o
      check (fun th ->
        concl th = `ring_homomorphism(k:B ring,l:C ring) g`)) THEN
    SUBGOAL_THEN `n = (n - 1 - i) + (1 + i)` (fun th ->
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_POW_ADD; RING_POW_1; RING_MUL_POW] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_mul l (ring_mul l p (ring_mul l e c))
                 (ring_mul l q y) =
      ring_mul l (ring_mul l p (ring_mul l e q)) (ring_mul l c (y:C))`)) THEN
    ASM_SIMP_TAC[RING_POW];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_SUM_LMUL; FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL;
               RING_POW; RING_MUL_POW] THEN
  ASM_SIMP_TAC[GSYM RING_ADD_LDISTRIB; RING_POW; RING_SUM; RING_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* The trace form bound: for r integrally closed with fraction field k and   *)
(* l a finite separable extension of k, the integral closure of r in l lies  *)
(* in the span over r of finitely many elements (the 1/D b_i for a basis b   *)
(* of integral elements with discriminant D).                                *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_CLOSURE_SUBSET_SPAN = prove
 (`!r k l (h:A->B) (g:B->C).
        integrally_closed r /\ field_of_fractions (r,k) h /\
        finite_extension (k,l) g /\ separable_extension (k,l) g
        ==> ?t. FINITE t /\ t SUBSET ring_carrier l /\
                {y | integral_element (r,l) (g o h) y} SUBSET
                ring_span (r,l) (g o h) t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_IMP_ALGEBRAIC_EXTENSION) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th = `ring_monomorphism(k:B ring,l:C ring) g`)) THEN
  SUBGOAL_THEN `ring_homomorphism(r,l) ((g:B->C) o (h:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `b0:num->C` o
    MATCH_MP FINITE_EXTENSION_FREE_BASIS) THEN
  ABBREV_TAC `n = extension_degree (k,l) (g:B->C)` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER) THEN
  SUBGOAL_THEN
   `!i. i < n
        ==> ?d. d IN ring_carrier r /\ ~(d = ring_0 r) /\
                integral_element (r,l) ((g:B->C) o (h:A->B))
                  (ring_mul l (g(h d)) ((b0:num->C) i))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_ELEMENT_DENOMINATOR THEN
    EXISTS_TAC `k:B ring` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC;
                 FINITE_IMP_FIELD_EXTENSION] THEN
    ASM_MESON_TAC[algebraic_extension];
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `d:num->A`)] THEN
  ABBREV_TAC
   `b = \i. ring_mul l ((g:B->C)((h:A->B)((d:num->A) i))) ((b0:num->C) i)` THEN
  SUBGOAL_THEN `free_basis (k,l) (g:B->C) n b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC FREE_BASIS_SCALE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(d:num->A) i IN ring_carrier r /\ ~(d i = ring_0 r)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
      ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> integral_element (r,l) ((g:B->C) o (h:A->B)) ((b:num->C) i)`
  ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FREE_BASIS_IN_CARRIER o check (fun th ->
    concl th = `free_basis (k,l) (g:B->C) n b`)) THEN
  ABBREV_TAC `D = basis_discriminant (k,l) (g:B->C) n b` THEN
  SUBGOAL_THEN `(D:B) IN ring_carrier k /\ ~(D = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[basis_discriminant; RING_DET];
      ALL_TAC] THEN
    EXPAND_TAC "D" THEN
    MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`; `n:num`; `b:num->C`]
      BASIS_DISCRIMINANT_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `?z:C. z IN ring_carrier l /\ algebra_trace (k,l) (g:B->C) z = ring_1 k`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`]
        ALGEBRA_TRACE_SURJECTIVE) THEN
      ASM_REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `ring_1 k:B`) THEN
      REWRITE_TAC[RING_1] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:C` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `ring_mul l (ring_inv l x) (z:C)`) THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; RING_MUL_ASSOC; FIELD_MUL_RINV;
                 RING_MUL_LID] THEN
    ASM_MESON_TAC[FIELD_NONTRIVIAL];
    ALL_TAC] THEN
  EXISTS_TAC
   `IMAGE (\i. ring_mul l ((g:B->C)(ring_inv k D)) ((b:num->C) i))
          {i | i < n}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[RING_MUL; RING_INV; RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:C` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:C) IN ring_carrier l` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRAL_ELEMENT_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:C. integral_element (r,l) ((g:B->C) o (h:A->B)) y
          ==> algebra_trace (k,l) g y IN IMAGE h (ring_carrier r)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRALLY_CLOSED_ALGEBRA_TRACE_NORM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`; `n:num`; `b:num->C`;
                 `IMAGE (h:A->B) (ring_carrier r)`; `x:C`]
    BASIS_DISCRIMINANT_TIMES_COORD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[ring_image] SUBRING_RING_IMAGE) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `algebra_trace (k,l) (g:B->C)`)) (concl th) &&
      is_forall(concl th))) THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:num->A`) THEN
  MP_TAC(ISPECL [`g:B->C`; `k:B ring`; `l:C ring`; `n:num`; `b:num->C`;
                 `x:C`] BASIS_COORDINATES_EXPAND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC RING_SPAN_SUM THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ABBREV_TAC `c = basis_coordinates (k,l) (g:B->C) n b x i` THEN
  SUBGOAL_THEN `(c:B) IN ring_carrier k` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_SIMP_TAC[BASIS_COORDINATES_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul l ((g:B->C) c) (b i) =
    ring_mul l (((g:B->C) o (h:A->B)) ((a:num->A) i))
               (ring_mul l (g(ring_inv k D)) (b i))`
  SUBST1_TAC THENL
   [REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhand(concl th) = `ring_mul k D (c:B)`)) THEN
    SUBGOAL_THEN `c = ring_mul k (ring_inv k D) (ring_mul k D (c:B))`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL
     [ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV; RING_MUL_LID];
      ALL_TAC] THEN
    FIRST_ASSUM((fun th ->
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th; RING_MUL; RING_INV]) o
      check (fun th ->
        concl th = `ring_homomorphism(k:B ring,l:C ring) g`)) THEN
    SUBGOAL_THEN
     `(g:B->C)(ring_inv k D) IN ring_carrier l /\
      (g:B->C) D IN ring_carrier l /\ (g:B->C) c IN ring_carrier l /\
      (b:num->C) i IN ring_carrier l`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_INV]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_mul l (ring_mul l u (ring_mul l p q)) w =
      ring_mul l (ring_mul l p q) (ring_mul l u (w:C))`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC RING_SPAN_MUL THEN
  ASM_SIMP_TAC[RING_HOMOMORPHISM_IN_CARRIER] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  MATCH_MP_TAC RING_SPAN_INC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[RING_MUL; RING_INV; RING_HOMOMORPHISM_IN_CARRIER]);;

(* ------------------------------------------------------------------------- *)
(* The integral closure of r in an algebraic extension l of its fraction     *)
(* field has fraction field l; for r Dedekind and l finite separable it is   *)
(* a Dedekind domain.                                                        *)
(* ------------------------------------------------------------------------- *)

let FIELD_OF_FRACTIONS_INTEGRAL_CLOSURE = prove
 (`!r k l (h:A->B) (g:B->C).
        field_of_fractions (r,k) h /\ algebraic_extension (k,l) g
        ==> field_of_fractions
             (subring_generated l {y | integral_element (r,l) (g o h) y},l)
             I`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    GEN_REWRITE_RULE I [algebraic_extension]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th = `ring_monomorphism(k:B ring,l:C ring) g`)) THEN
  SUBGOAL_THEN `ring_homomorphism(r,l) ((g:B->C) o (h:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{y | integral_element (r,l) ((g:B->C) o (h:A->B)) y} subring_of l`
  ASSUME_TAC THENL [ASM_SIMP_TAC[INTEGRAL_CLOSURE_SUBRING]; ALL_TAC] THEN
  REWRITE_TAC[field_of_fractions] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[I_DEF; RING_MONOMORPHISM_INCLUSION]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING; IN_ELIM_THM; I_THM;
               CONJUNCT2 SUBRING_GENERATED] THEN
  X_GEN_TAC `x:C` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`;
                 `x:C`] INTEGRAL_ELEMENT_DENOMINATOR) THEN
  ASM_SIMP_TAC[INTEGRAL_OVER_FIELD_EQ_ALGEBRAIC] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[algebraic_extension]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:A` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`ring_mul l ((g:B->C)((h:A->B) d)) x`; `(g:B->C)((h:A->B) d)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `l:C ring`; `(g:B->C) o (h:A->B)`; `d:A`]
      INTEGRAL_ELEMENT_IMAGE) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_monomorphism(r,l) ((g:B->C) o (h:A->B))` MP_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0; o_THM]]);;

(* The Dedekind property: a domain since l is a field, integrally closed as  *)
(* an integral closure, Noetherian since its ideals are submodules of a      *)
(* finitely generated module over r (INTEGRAL_CLOSURE_SUBSET_SPAN), and of   *)
(* dimension one since a nonzero prime lies over a nonzero, hence maximal,   *)
(* prime of r (INTEGRAL_EXTENSION_PRIME_NONZERO and                          *)
(* INTEGRAL_EXTENSION_MAXIMAL_IDEAL).                                        *)

let DEDEKIND_INTEGRAL_CLOSURE = prove
 (`!r k l (h:A->B) (g:B->C).
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        finite_extension (k,l) g /\ separable_extension (k,l) g
        ==> dedekind_domain
              (subring_generated l {y | integral_element (r,l) (g o h) y})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_extension] o
    MATCH_MP FINITE_IMP_FIELD_EXTENSION) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th = `ring_monomorphism(k:B ring,l:C ring) g`)) THEN
  SUBGOAL_THEN `ring_monomorphism(r,l) ((g:B->C) o (h:A->B))` ASSUME_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN EXISTS_TAC `k:B ring` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM o
    check (fun th -> concl th =
      `ring_monomorphism(r:A ring,l:C ring) ((g:B->C) o (h:A->B))`)) THEN
  ABBREV_TAC `S = {y | integral_element (r,l) ((g:B->C) o (h:A->B)) y}` THEN
  SUBGOAL_THEN
   `(!y. y IN S <=> integral_element (r,l) ((g:B->C) o (h:A->B)) y) /\
    S subring_of l /\ IMAGE ((g:B->C) o (h:A->B)) (ring_carrier r) SUBSET S /\
    integrally_closed(subring_generated l S)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[INTEGRAL_CLOSURE_SUBRING; INTEGRAL_CLOSURE_SUPSET_IMAGE;
                 INTEGRALLY_CLOSED_INTEGRAL_CLOSURE];
    FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
      is_eq(concl th) && rand(concl th) = `S:C->bool`))] THEN
  SUBGOAL_THEN `ring_carrier(subring_generated l S) = (S:C->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARRIER_SUBRING_GENERATED_SUBRING]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_homomorphism(r,subring_generated l S) ((g:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_HOMOMORPHISM_INTO_SUBRING_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_monomorphism(r,subring_generated l S) ((g:B->C) o (h:A->B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_MONOMORPHISM_INTO_SUBRING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> integral_element (r,subring_generated l S)
                             ((g:B->C) o (h:A->B)) y`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_ELEMENT_SUBRING_GENERATED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. integral_element (r,l) ((g:B->C) o (h:A->B)) y
        ==> integral_element (r,subring_generated l S) (g o h) y`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `integral_domain(subring_generated l (S:C->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_SUBRING_GENERATED THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  REWRITE_TAC[dedekind_domain] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[noetherian_ring; finitely_generated_ideal] THEN
    X_GEN_TAC `J:C->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `l:C ring`; `h:A->B`; `g:B->C`]
      INTEGRAL_CLOSURE_SUBSET_SPAN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[dedekind_domain]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:C->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(J:C->bool) SUBSET S` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `l:C ring`; `(g:B->C) o (h:A->B)`;
                   `t:C->bool`; `J:C->bool`]
      NOETHERIAN_RING_SPAN_SUBMODULE) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[DEDEKIND_IMP_NOETHERIAN] THEN
      MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `J:C->bool`]
        IN_RING_IDEAL_0) THEN
      MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `J:C->bool`]
        IN_RING_IDEAL_ADD) THEN
      MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `J:C->bool`]
        IN_RING_IDEAL_LMUL) THEN
      ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN
      REPEAT DISCH_TAC THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC
         `{y | integral_element (r,l) ((g:B->C) o (h:A->B)) y} SUBSET
          ring_span (r,l) (g o h) t` THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ASM_MESON_TAC[SUBSET];
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `u:C->bool` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `u:C->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
      check (fun th -> lhand(concl th) =
        `ring_span (r,l) ((g:B->C) o (h:A->B)) u`)) THEN
    MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `u:C->bool`]
      RING_IDEAL_IDEAL_GENERATED) THEN
    ABBREV_TAC `m = ideal_generated (subring_generated l S) (u:C->bool)` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(u:C->bool) SUBSET m` ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN
      MATCH_MP_TAC IDEAL_GENERATED_SUBSET_CARRIER_SUBSET THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `m:C->bool`]
      IN_RING_IDEAL_0) THEN
    MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `m:C->bool`]
      IN_RING_IDEAL_ADD) THEN
    MP_TAC(ISPECL [`subring_generated l (S:C->bool)`; `m:C->bool`]
      IN_RING_IDEAL_LMUL) THEN
    ASM_REWRITE_TAC[CONJUNCT2 SUBRING_GENERATED] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC ring_span_INDUCT THEN
    ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `q:C->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `subring_generated l (S:C->bool)`;
                   `(g:B->C) o (h:A->B)`; `q:C->bool`]
      INTEGRAL_EXTENSION_MAXIMAL_IDEAL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o last o CONJUNCTS o
      GEN_REWRITE_RULE I [dedekind_domain] o check (fun th ->
        concl th = `dedekind_domain(r:A ring)`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRIME_IDEAL_HOMOMORPHIC_PREIMAGE THEN
      EXISTS_TAC `subring_generated l (S:C->bool)` THEN
      ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INTEGRAL_EXTENSION_PRIME_NONZERO THEN
      EXISTS_TAC `subring_generated l (S:C->bool)` THEN
      ASM_SIMP_TAC[ETA_AX]]]);;
