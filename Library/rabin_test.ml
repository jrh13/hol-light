(* ======================================================================== *)
(* Rabin's test for irreducibility of polynomials over finite fields.       *)
(*                                                                          *)
(* All development (statements and proof) written by Claude Code, Opus 4.6  *)
(* ======================================================================== *)

needs "Library/fieldtheory.ml";;

(* ------------------------------------------------------------------------- *)
(* General lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

(* Iteration lemma: if p | (x^m - x) in a ring, then p | (x^(m^k) - x) *)
let RING_DIVIDES_POW_ITERATE = prove
 (`!r (p:A) x m k.
     integral_domain r /\
     p IN ring_carrier r /\ x IN ring_carrier r /\
     ring_divides r p (ring_sub r (ring_pow r x m) x) /\ ~(k = 0) /\
     1 <= m
     ==> ring_divides r p (ring_sub r (ring_pow r x (m EXP k)) x)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  INDUCT_TAC THENL
  [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NOT_SUC] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `k = 0` THENL
  [ASM_REWRITE_TAC[EXP; EXP_1; MULT_CLAUSES];
   ALL_TAC] THEN
  (* k != 0 case: use IH then telescope *)
  SUBGOAL_THEN `ring_divides r (p:A) (ring_sub r (ring_pow r x (m EXP k)) x)`
    ASSUME_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ring_pow r (x:A) (m EXP k) IN ring_carrier r`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RING_POW THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* x^(m^(SUC k)) = (x^(m^k))^m *)
  SUBGOAL_THEN `ring_pow r (x:A) (m EXP (SUC k)) =
                ring_pow r (ring_pow r x (m EXP k)) m`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
   ASM_SIMP_TAC[RING_POW_POW]; ALL_TAC] THEN
  (* Telescope: (x^(m^k))^m - x = ((x^(m^k))^m - x^m) + (x^m - x) *)
  SUBGOAL_THEN
    `ring_sub r (ring_pow r (ring_pow r (x:A) (m EXP k)) m) x =
     ring_add r
       (ring_sub r (ring_pow r (ring_pow r x (m EXP k)) m) (ring_pow r x m))
       (ring_sub r (ring_pow r x m) x)` SUBST1_TAC THENL
  [MATCH_MP_TAC(GSYM RING_SUB_TELESCOPE) THEN ASM_SIMP_TAC[RING_POW]; ALL_TAC] THEN
  MATCH_MP_TAC RING_DIVIDES_ADD THEN CONJ_TAC THENL
  [(* p | ((x^(m^k))^m - x^m): by p | (x^(m^k) - x) | ((x^(m^k))^m - x^m) *)
   MATCH_MP_TAC RING_DIVIDES_TRANS THEN
   EXISTS_TAC `ring_sub r (ring_pow r (x:A) (m EXP k)) x` THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC RING_DIVIDES_SUB_POW THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   (* p | (x^m - x): direct hypothesis *)
   ASM_REWRITE_TAC[]]);;

(* Helper: non-unit non-zero polynomial over a field has degree >= 1 *)
let POLY_NONUNIT_DEGREE_GE_1 = prove
 (`!f:A ring p (s:V->bool).
     field f /\
     p IN ring_carrier(poly_ring f s) /\
     ~(p = ring_0(poly_ring f s)) /\
     ~(ring_unit (poly_ring f s) p)
     ==> 1 <= poly_deg f p`,
  REWRITE_TAC[IN_POLY_RING_CARRIER; ARITH_RULE `1 <= d <=> ~(d = 0)`] THEN
  SIMP_TAC[POLY_DEG_EQ_0] THEN
  MESON_TAC[RING_UNIT_POLY_CONST; FIELD_UNIT; POLY_CONST_0; POLY_RING]);;

(* Helper: if p | (u - x) and p | (u^m - x) and m >= 1, then p | (x^m - x) *)
let RING_DIVIDES_REDUCE = prove
 (`!r (p:A) u x m.
    p IN ring_carrier r /\ u IN ring_carrier r /\ x IN ring_carrier r /\
    ring_divides r p (ring_sub r u x) /\
    ring_divides r p (ring_sub r (ring_pow r u m) x) /\ ~(m = 0)
    ==> ring_divides r p (ring_sub r (ring_pow r x m) x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* Step 1: p | (u^m - x^m) via (u-x) | (u^m - x^m) *)
  SUBGOAL_THEN `ring_divides r (p:A)
    (ring_sub r (ring_pow r u m) (ring_pow r x m))` ASSUME_TAC THENL
  [MATCH_MP_TAC RING_DIVIDES_TRANS THEN
   EXISTS_TAC `ring_sub r (u:A) x` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC RING_DIVIDES_SUB_POW THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 2: p | (u^m - x) - (u^m - x^m) by RING_DIVIDES_SUB *)
  SUBGOAL_THEN `ring_divides r (p:A)
    (ring_sub r (ring_sub r (ring_pow r u m) x)
                (ring_sub r (ring_pow r u m) (ring_pow r x m)))` MP_TAC THENL
  [MATCH_MP_TAC RING_DIVIDES_SUB THEN
   ASM_SIMP_TAC[RING_POW; RING_SUB];
   ALL_TAC] THEN
  (* Step 3: (u^m - x) - (u^m - x^m) = x^m - x *)
  SUBGOAL_THEN
    `ring_sub r (ring_sub r (ring_pow r (u:A) m) x)
                (ring_sub r (ring_pow r u m) (ring_pow r x m)) =
     ring_sub r (ring_pow r x m) x`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[RING_POW; RING_RULE
    `ring_sub r (ring_sub r (a:A) b) (ring_sub r a c) = ring_sub r c b`]);;

(* ------------------------------------------------------------------------- *)
(* Finite field Fermat / Frobenius                                           *)
(* ------------------------------------------------------------------------- *)

(* Product of nonzero elements is invariant under multiplication by nonzero x *)
let FIELD_NONZERO_PRODUCT_PERMUTE = prove
 (`!f:A ring x.
    field f /\ FINITE(ring_carrier f) /\
    x IN ring_carrier f /\ ~(x = ring_0 f)
    ==> ring_product f (ring_carrier f DELETE ring_0 f) (\y. ring_mul f x y) =
        ring_product f (ring_carrier f DELETE ring_0 f) (\y. y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_PRODUCT_EQ_GENERAL_INVERSES THEN
  EXISTS_TAC `\y:A. ring_mul f x y` THEN
  EXISTS_TAC `\y:A. ring_mul f (ring_inv f x) y` THEN
  SUBGOAL_THEN `ring_inv f (x:A) IN ring_carrier f /\
                ~(ring_inv f x = ring_0 f)` STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC[RING_INV; FIELD_UNIT; RING_UNIT_INV]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  CONJ_TAC THEN X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_DELETE] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
  [(* ring_mul f (inv x) y IN carrier *)
   ASM_MESON_TAC[RING_MUL];
   (* ~(ring_mul f (inv x) y = 0) *)
   ASM_SIMP_TAC[FIELD_MUL_EQ_0];
   (* ring_mul f x (ring_mul f (inv x) y) = y *)
   ASM_SIMP_TAC[RING_MUL_ASSOC; FIELD_MUL_RINV; RING_MUL_LID];
   (* ring_mul f x y IN carrier *)
   ASM_MESON_TAC[RING_MUL];
   (* ~(ring_mul f x y = 0) *)
   ASM_SIMP_TAC[FIELD_MUL_EQ_0];
   (* ring_mul f (inv x) (ring_mul f x y) = y *)
   ASM_SIMP_TAC[RING_MUL_ASSOC; FIELD_MUL_LINV; RING_MUL_LID]]);;

(* Every element of a finite field satisfies x^q = x where q = CARD(carrier) *)
let FINITE_FIELD_ELEMENT_POW = prove
 (`!f:A ring.
   field f /\ FINITE(ring_carrier f)
   ==> !x. x IN ring_carrier f
       ==> ring_pow f x (CARD(ring_carrier f)) = x`,
  REPEAT STRIP_TAC THEN
  (* Case x = 0: x^q = 0 = x *)
  ASM_CASES_TAC `x:A = ring_0 f` THENL
  [ASM_SIMP_TAC[RING_POW_ZERO] THEN
   COND_CASES_TAC THENL
   [ASM_MESON_TAC[CARD_EQ_0; RING_CARRIER_NONEMPTY]; REFL_TAC];
   ALL_TAC] THEN
  (* Rewrite q = (q-1) + 1, split x^q = x^(q-1) * x *)
  SUBGOAL_THEN `CARD(ring_carrier(f:A ring)) =
                (CARD(ring_carrier f) - 1) + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n = (n - 1) + 1`) THEN
   ASM_MESON_TAC[CARD_EQ_0; RING_CARRIER_NONEMPTY];
   ALL_TAC] THEN
  ASM_SIMP_TAC[RING_POW_ADD; RING_POW] THEN
  REWRITE_TAC[ring_pow; RING_MUL_RID] THEN
  (* Reduce to showing x^(q-1) = 1 *)
  SUBGOAL_THEN `ring_pow f x (CARD(ring_carrier(f:A ring)) - 1) = ring_1 f`
    (fun th -> ASM_SIMP_TAC[th; RING_MUL_RID; RING_MUL_LID;
                            RING_POW_1; RING_POW]) THEN
  (* Set up s = carrier \ {0} *)
  ABBREV_TAC `s = ring_carrier f DELETE (ring_0 (f:A ring))` THEN
  SUBGOAL_THEN `FINITE (s:A->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN ASM_SIMP_TAC[FINITE_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(s:A->bool) = CARD(ring_carrier(f:A ring)) - 1`
    ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN ASM_SIMP_TAC[CARD_DELETE; RING_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:A) IN s` ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN ASM_REWRITE_TAC[IN_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:A. y IN s ==> y IN ring_carrier f /\ ~(y = ring_0 f)`
    ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  (* Product P of all nonzero elements is nonzero *)
  SUBGOAL_THEN `~(ring_product f s (\y:A. y) = ring_0 f)` ASSUME_TAC THENL
  [ASM_SIMP_TAC[INTEGRAL_DOMAIN_PRODUCT_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Product permutation: product of (x*y) = product of y *)
  SUBGOAL_THEN
    `ring_product f s (\y:A. ring_mul f x y) =
     ring_product f s (\y:A. y)` ASSUME_TAC THENL
  [EXPAND_TAC "s" THEN MATCH_MP_TAC FIELD_NONZERO_PRODUCT_PERMUTE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* By RING_PRODUCT_LMUL: product of (x*y) = x^|s| * product of y *)
  SUBGOAL_THEN
    `ring_product f s (\y:A. ring_mul f x y) =
     ring_mul f (ring_pow f x (CARD(s:A->bool)))
               (ring_product f s (\y:A. y))` ASSUME_TAC THENL
  [MATCH_MP_TAC RING_PRODUCT_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Cancel: x^|s| = 1 (using x^|s| * P = P from previous equalities) *)
  SUBGOAL_THEN `ring_pow f x (CARD(s:A->bool)) = ring_1 (f:A ring)`
    (fun th -> ASM_MESON_TAC[th]) THEN
  MP_TAC (ISPECL [`f:A ring`;
                  `ring_product f s (\y:A. y)`;
                  `ring_pow f (x:A) (CARD(s:A->bool))`;
                  `ring_1 (f:A ring)`]
                 INTEGRAL_DOMAIN_MUL_RCANCEL) THEN
  ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_POW; RING_1;
               RING_MUL_LID; RING_PRODUCT] THEN
  ASM_MESON_TAC[]);;

(* Helper: The quotient F[x]/(p) for irreducible p of degree d over a
   finite field F with q elements is a finite field with q^d elements *)
let QUOTIENT_POLY_RING_FINITE_CARD = prove
 (`!f:A ring p.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ring_irreducible (poly_ring f (:1)) p
   ==> field(quotient_ring (poly_ring f (:1))
              (ideal_generated (poly_ring f (:1)) {p})) /\
       FINITE(ring_carrier(quotient_ring (poly_ring f (:1))
              (ideal_generated (poly_ring f (:1)) {p}))) /\
       CARD(ring_carrier(quotient_ring (poly_ring f (:1))
              (ideal_generated (poly_ring f (:1)) {p}))) =
       CARD(ring_carrier f) EXP (poly_deg f p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = poly_ring (f:A ring) (:1)` THEN
  ABBREV_TAC `J = ideal_generated R {p:(1->num)->A}` THEN
  ABBREV_TAC `K = quotient_ring R (J:((1->num)->A)->bool)` THEN
  ABBREV_TAC `h:A->((1->num)->A)->bool =
    ring_coset R J o poly_const (f:A ring)` THEN
  ABBREV_TAC `a:((1->num)->A)->bool =
    ring_coset R J (poly_var (f:A ring) one)` THEN
  SUBGOAL_THEN `PID (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN ASM_MESON_TAC[PID_POLY_RING];
   ALL_TAC] THEN
  SUBGOAL_THEN `maximal_ideal R (J:((1->num)->A)->bool) /\
                ring_ideal R (J:((1->num)->A)->bool)` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN
   ASM_MESON_TAC[RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL; MAXIMAL_IMP_RING_IDEAL];
   ALL_TAC] THEN
  (* field K *)
  SUBGOAL_THEN `field (K:(((1->num)->A)->bool)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN ASM_MESON_TAC[FIELD_QUOTIENT_RING]; ALL_TAC] THEN
  (* field_extension(f, K) h - expand all abbrevs for KRONECKER *)
  SUBGOAL_THEN `field_extension
    (f:A ring, K:(((1->num)->A)->bool)ring)
    (h:A->((1->num)->A)->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN EXPAND_TAC "h" THEN EXPAND_TAC "J" THEN
   EXPAND_TAC "R" THEN
   MATCH_MP_TAC KRONECKER_FIELD_EXTENSION THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* ring_homomorphism(R, K)(ring_coset R J) *)
  SUBGOAL_THEN `ring_homomorphism
    (R:((1->num)->A)ring, K:(((1->num)->A)->bool)ring)
    (ring_coset R (J:((1->num)->A)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_HOMOMORPHISM_RING_COSET];
   ALL_TAC] THEN
  (* ring_homomorphism(f, K) h *)
  SUBGOAL_THEN `ring_homomorphism
    (f:A ring, K:(((1->num)->A)->bool)ring)
    (h:A->((1->num)->A)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[field_extension; RING_MONOMORPHISM_IMP_HOMOMORPHISM];
   ALL_TAC] THEN
  (* a IN carrier K *)
  SUBGOAL_THEN `(a:((1->num)->A)->bool) IN ring_carrier K` ASSUME_TAC THENL
  [SUBGOAL_THEN `poly_var (f:A ring) one IN ring_carrier R` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_VAR_UNIV]; ALL_TAC] THEN
   ASM_MESON_TAC[ring_homomorphism; IN_IMAGE; SUBSET];
   ALL_TAC] THEN
  (* poly_extend = ring_coset R J on carrier R *)
  SUBGOAL_THEN
    `!g. g IN ring_carrier R
         ==> poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
               h (\v:1. a) g =
             ring_coset R (J:((1->num)->A)->bool) g` ASSUME_TAC THENL
  [X_GEN_TAC `g:(1->num)->A` THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`f:A ring`; `K:(((1->num)->A)->bool)ring`;
     `(:1)`; `h:A->((1->num)->A)->bool`;
     `(\v:1. a:((1->num)->A)->bool)`;
     `ring_coset R (J:((1->num)->A)->bool)`;
     `g:(1->num)->A`] POLY_EXTEND_UNIQUE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [X_GEN_TAC `c:A` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[o_THM];
    X_GEN_TAC `i:1` THEN REWRITE_TAC[IN_UNIV] THEN
    SUBGOAL_THEN `i:1 = one` SUBST1_TAC THENL
    [MESON_TAC[one]; ALL_TAC] THEN
    EXPAND_TAC "a" THEN REFL_TAC];
   ALL_TAC] THEN
  (* p IN J *)
  SUBGOAL_THEN `p:(1->num)->A IN J` ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN REWRITE_TAC[IN_IDEAL_GENERATED_SELF] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* ring_coset R J p = ring_0 K *)
  SUBGOAL_THEN
    `ring_coset R (J:((1->num)->A)->bool) (p:(1->num)->A) =
     ring_0 (K:(((1->num)->A)->bool)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN ASM_SIMP_TAC[QUOTIENT_RING_0] THEN
   ASM_MESON_TAC[RING_COSET_EQ_IDEAL];
   ALL_TAC] THEN
  (* algebraic_over *)
  SUBGOAL_THEN
    `algebraic_over (f:A ring,K:(((1->num)->A)->bool)ring)
      (h:A->((1->num)->A)->bool) (a:((1->num)->A)->bool)` ASSUME_TAC THENL
  [REWRITE_TAC[algebraic_over] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `p:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[ring_irreducible; POLY_RING_CLAUSES]; ALL_TAC] THEN
   SUBGOAL_THEN
     `poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
       h (\v:1. a) p = ring_coset R (J:((1->num)->A)->bool) p`
     SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* subring_generated K (...) = K *)
  SUBGOAL_THEN
    `subring_generated K
       ((a:((1->num)->A)->bool) INSERT
        IMAGE (h:A->((1->num)->A)->bool) (ring_carrier f)) = K`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBRING_GENERATED_SUPERSET] THEN
   MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`; `f:A ring`;
     `K:(((1->num)->A)->bool)ring`;
     `a:((1->num)->A)->bool`]
     IMAGE_POLY_EXTEND_1) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
   (* Goal: ring_carrier K ⊆ IMAGE (poly_extend ...) (ring_carrier R) *)
   SUBGOAL_THEN
     `ring_carrier(K:(((1->num)->A)->bool)ring) =
      {ring_coset R (J:((1->num)->A)->bool) x |x| x IN ring_carrier R}`
     SUBST1_TAC THENL
   [EXPAND_TAC "K" THEN ASM_SIMP_TAC[QUOTIENT_RING_CARRIER]; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_IMAGE] THEN
   X_GEN_TAC `g:(1->num)->A` THEN DISCH_TAC THEN
   EXISTS_TAC `g:(1->num)->A` THEN ASM_SIMP_TAC[];
   ALL_TAC] THEN
  (* finite_extension(f, K) h *)
  SUBGOAL_THEN `finite_extension
    (f:A ring, K:(((1->num)->A)->bool)ring)
    (h:A->((1->num)->A)->bool)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`;
     `f:A ring`; `K:(((1->num)->A)->bool)ring`;
     `a:((1->num)->A)->bool`]
     FINITE_SIMPLE_ALGEBRAIC_EXTENSION) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Extract basis *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_EXTENSION_BASIS]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun _ -> ALL_TAC)
    (X_CHOOSE_THEN `b:(((1->num)->A)->bool)->bool` STRIP_ASSUME_TAC)) THEN
  (* field K already proved *)
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* FINITE + CARD *)
  MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`;
    `f:A ring`; `K:(((1->num)->A)->bool)ring`;
    `b:(((1->num)->A)->bool)->bool`]
    HAS_SIZE_FINITE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[HAS_SIZE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th])) THEN
  ASM_REWRITE_TAC[] THEN
  (* Need: CARD(ring_carrier f) EXP CARD b = ... EXP poly_deg f p *)
  (* Suffices to show CARD b = poly_deg f p *)
  SUBGOAL_THEN `CARD (b:(((1->num)->A)->bool)->bool) =
                poly_deg (f:A ring) (p:(1->num)->A)`
    (fun th -> REWRITE_TAC[th]) THEN
  ABBREV_TAC `d = poly_deg (f:A ring) (p:(1->num)->A)` THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
  [(* Upper bound: CARD b <= d *)
   (* Establish key facts *)
   SUBGOAL_THEN `~(p:(1->num)->A = ring_0 R)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_irreducible]; ALL_TAC] THEN
   SUBGOAL_THEN `poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
     h (\v:1. a) p = ring_0 K` ASSUME_TAC THENL
   [SUBGOAL_THEN `poly_extend (f:A ring,K:(((1->num)->A)->bool)ring)
     h (\v:1. a) (p:(1->num)->A) = ring_coset R J p` SUBST1_TAC THENL
    [ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* Upper bound: CARD b <= d *)
   (* Extract ring_independent and b SUBSET from ring_basis *)
   SUBGOAL_THEN `ring_independent (f:A ring,K:(((1->num)->A)->bool)ring)
     (h:A->((1->num)->A)->bool) (b:(((1->num)->A)->bool)->bool)`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_basis]; ALL_TAC] THEN
   SUBGOAL_THEN `(b:(((1->num)->A)->bool)->bool) SUBSET
     ring_carrier (K:(((1->num)->A)->bool)ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_independent]; ALL_TAC] THEN
   (* Powers {a^n | n < d} span K *)
   MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`; `f:A ring`;
     `K:(((1->num)->A)->bool)ring`; `p:(1->num)->A`;
     `a:((1->num)->A)->bool`] RING_SIMPLE_ALGEBRAIC_EXTENSION_SPAN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   (* Apply RING_INDEPENDENT_LE_SPAN *)
   MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`; `f:A ring`;
     `K:(((1->num)->A)->bool)ring`;
     `b:(((1->num)->A)->bool)->bool`;
     `{ring_pow (K:(((1->num)->A)->bool)ring)
                (a:((1->num)->A)->bool) n | n < d}`]
     RING_INDEPENDENT_LE_SPAN) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [(* t SUBSET ring_carrier K *)
     REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     MATCH_MP_TAC RING_POW THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [(* FINITE t *)
     ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
     MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
     ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    (* b SUBSET ring_span(f,K) h {ring_pow K a n | n < d} *)
    SUBGOAL_THEN `ring_span (f:A ring,K:(((1->num)->A)->bool)ring)
       (h:A->((1->num)->A)->bool)
       {ring_pow K (a:((1->num)->A)->bool) n | n < d} =
      ring_carrier (K:(((1->num)->A)->bool)ring)`
      (fun th -> REWRITE_TAC[th]) THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* FINITE b /\ CARD b <= CARD {ring_pow K a n | n < d} *)
   DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th)) THEN
   MATCH_MP_TAC(ARITH_RULE `b <= c ==> a <= b ==> a <= c`) THEN
   ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
   TRANS_TAC LE_TRANS `CARD {n:num | n < d}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT];
    REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]];
   (* Lower bound: d <= CARD b *)
   SUBGOAL_THEN `ring_span (f:A ring,K:(((1->num)->A)->bool)ring)
     (h:A->((1->num)->A)->bool) (b:(((1->num)->A)->bool)->bool) =
     ring_carrier K` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_basis; ring_spanning]; ALL_TAC] THEN
   SUBGOAL_THEN `(b:(((1->num)->A)->bool)->bool) SUBSET
     ring_carrier (K:(((1->num)->A)->bool)ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ring_basis; ring_independent]; ALL_TAC] THEN
   MP_TAC(ISPECL [`h:A->((1->num)->A)->bool`; `f:A ring`;
     `K:(((1->num)->A)->bool)ring`;
     `a:((1->num)->A)->bool`;
     `b:(((1->num)->A)->bool)->bool`;
     `CARD (b:(((1->num)->A)->bool)->bool)`]
     FINITE_IMP_ALGEBRAIC_EXTENSION_EXPLICIT) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; SUBSET_REFL]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `q:(1->num)->A` STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN `(q:(1->num)->A) IN ring_carrier R` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `ring_coset R (J:((1->num)->A)->bool) (q:(1->num)->A) =
     ring_0 (K:(((1->num)->A)->bool)ring)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `q:(1->num)->A` th)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `(q:(1->num)->A) IN J` ASSUME_TAC THENL
   [SUBGOAL_THEN `ring_kernel(R,K) (ring_coset R (J:((1->num)->A)->bool)) = J`
      (SUBST1_TAC o SYM) THENL
    [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_KERNEL_RING_COSET]; ALL_TAC] THEN
    REWRITE_TAC[ring_kernel; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
   SUBGOAL_THEN `ring_divides R (p:(1->num)->A) q` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:((1->num)->A)ring`; `p:(1->num)->A`;
      `q:(1->num)->A`] IN_IDEAL_GENERATED_SING_EQ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]);
    ALL_TAC] THEN
   TRANS_TAC LE_TRANS `poly_deg (f:A ring) (q:(1->num)->A)` THEN
   CONJ_TAC THENL
   [EXPAND_TAC "d" THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ring_divides]) THEN
    EXPAND_TAC "R" THEN
    REWRITE_TAC[POLY_RING_CLAUSES; SUBSET_UNIV; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `s:(1->num)->A` STRIP_ASSUME_TAC))) THEN
    (* poly_deg f q = poly_deg f p + poly_deg f s *)
    SUBGOAL_THEN `poly_deg (f:A ring) (q:(1->num)->A) =
      poly_deg f (p:(1->num)->A) + poly_deg f (s:(1->num)->A)` MP_TAC THENL
    [SUBGOAL_THEN `(q:(1->num)->A) = poly_mul (f:A ring) p s`
       SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     MATCH_MP_TAC POLY_DEG_MUL THEN
     ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
     (* Remaining: p = poly_0 f <=> s = poly_0 f; both sides false *)
     SUBGOAL_THEN `poly_0 (f:A ring) = ring_0 (R:((1->num)->A)ring)`
       (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
     (* Goal: p = ring_0 R <=> s = ring_0 R *)
     MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN
     FIRST_X_ASSUM(STRIP_ASSUME_TAC o
       GEN_REWRITE_RULE I [ring_irreducible]) THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      (* ~(s = ring_0 R): if s = 0 then q = p*0 = 0, contradicting q <> 0 *)
      DISCH_TAC THEN
      SUBGOAL_THEN `ring_mul (R:((1->num)->A)ring) (p:(1->num)->A)
        (ring_0 R) = ring_0 R` ASSUME_TAC THENL
      [MATCH_MP_TAC RING_MUL_RZERO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `poly_mul (f:A ring) (p:(1->num)->A)
        (ring_0 (R:((1->num)->A)ring)) =
        ring_mul R p (ring_0 R)` ASSUME_TAC THENL
      [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
     ALL_TAC] THEN
    EXPAND_TAC "d" THEN ARITH_TAC;
    ASM_REWRITE_TAC[]]]);;

(* Generalized: irreducible p with deg(p) | n implies p | x^(q^n) - x *)
let IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN = prove
 (`!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ring_irreducible (poly_ring f (:1)) p /\
   (poly_deg f p) divides n
   ==> ring_divides (poly_ring f (:1)) p
         (ring_sub (poly_ring f (:1))
            (ring_pow (poly_ring f (:1)) (poly_var f one)
                      (CARD(ring_carrier f) EXP n))
            (poly_var f one))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = poly_ring (f:A ring) (:1)` THEN
  ABBREV_TAC `J = ideal_generated R {p:(1->num)->A}` THEN
  ABBREV_TAC `K = quotient_ring R (J:((1->num)->A)->bool)` THEN
  (* Step 1: J is maximal, hence a ring ideal *)
  SUBGOAL_THEN `PID (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN ASM_MESON_TAC[PID_POLY_RING];
   ALL_TAC] THEN
  SUBGOAL_THEN `maximal_ideal R (J:((1->num)->A)->bool) /\
                ring_ideal R (J:((1->num)->A)->bool)` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN
   ASM_MESON_TAC[RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL; MAXIMAL_IMP_RING_IDEAL];
   ALL_TAC] THEN
  (* Step 2: K is a finite field with q^d elements *)
  SUBGOAL_THEN
    `field (K:(((1->num)->A)->bool) ring) /\
     FINITE(ring_carrier K) /\
     CARD(ring_carrier K) =
     CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`] QUOTIENT_POLY_RING_FINITE_CARD) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: ring_coset R J is a ring homomorphism R -> K *)
  SUBGOAL_THEN `ring_homomorphism(R,K)
                  (ring_coset R (J:((1->num)->A)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_HOMOMORPHISM_RING_COSET];
   ALL_TAC] THEN
  (* Step 4: poly_var f one IN carrier R *)
  SUBGOAL_THEN `poly_var f one IN ring_carrier(R:((1->num)->A)ring)`
    ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_VAR_UNIV]; ALL_TAC] THEN
  (* Step 5: proj(x) IN carrier K *)
  SUBGOAL_THEN
    `ring_coset R (J:((1->num)->A)->bool)
       (poly_var (f:A ring) one) IN ring_carrier K` ASSUME_TAC THENL
  [ASM_MESON_TAC[ring_homomorphism; IN_IMAGE; SUBSET]; ALL_TAC] THEN
  (* Step 6: proj(x)^(q^d) = proj(x) by FINITE_FIELD_ELEMENT_POW *)
  SUBGOAL_THEN
    `ring_pow K
       (ring_coset R (J:((1->num)->A)->bool) (poly_var (f:A ring) one))
       (CARD(ring_carrier(f:A ring)) EXP
        (poly_deg f (p:(1->num)->A))) =
     ring_coset R J (poly_var f one)` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A)) =
      CARD(ring_carrier(K:(((1->num)->A)->bool) ring))`
     SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPEC `K:(((1->num)->A)->bool) ring` FINITE_FIELD_ELEMENT_POW) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(MP_TAC o SPEC
     `ring_coset R (J:((1->num)->A)->bool) (poly_var (f:A ring) one)`) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 7: proj(x^(q^d) - x) = 0 *)
  SUBGOAL_THEN
    `ring_coset R (J:((1->num)->A)->bool)
       (ring_sub R
          (ring_pow R (poly_var f one)
             (CARD(ring_carrier(f:A ring)) EXP
              (poly_deg f (p:(1->num)->A))))
          (poly_var f one)) =
     ring_0 (K:(((1->num)->A)->bool) ring)` ASSUME_TAC THENL
  [(* proj(a - b) = proj(a) - proj(b) *)
   FIRST_ASSUM(fun hom ->
     MP_TAC(MATCH_MP RING_HOMOMORPHISM_SUB hom)) THEN
   DISCH_THEN(fun th ->
     MP_TAC(SPECL [`ring_pow R (poly_var f one)
        (CARD(ring_carrier(f:A ring)) EXP
         (poly_deg f (p:(1->num)->A)))`;
       `poly_var (f:A ring) one`] th)) THEN
   ASM_SIMP_TAC[RING_POW] THEN DISCH_THEN SUBST1_TAC THEN
   (* proj(x^n) = proj(x)^n *)
   FIRST_ASSUM(fun hom ->
     MP_TAC(MATCH_MP RING_HOMOMORPHISM_POW hom)) THEN
   DISCH_THEN(fun th ->
     MP_TAC(SPECL [`poly_var (f:A ring) one`;
       `CARD(ring_carrier(f:A ring)) EXP
        (poly_deg f (p:(1->num)->A))`] th)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   (* Now: ring_sub K (ring_pow K proj(x) (q^d)) proj(x) = ring_0 K *)
   (* Use proj(x)^(|K|) = proj(x) and |K| = q^d *)
   ASM_REWRITE_TAC[] THEN
   ASM_MESON_TAC[RING_SUB_REFL];
   ALL_TAC] THEN
  (* Step 8: x^(q^d) - x IN J (kernel of proj = J) *)
  SUBGOAL_THEN
    `ring_sub R
       (ring_pow R (poly_var f one)
          (CARD(ring_carrier(f:A ring)) EXP
           (poly_deg f (p:(1->num)->A))))
       (poly_var (f:A ring) one) IN J`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `ring_kernel(R,K) (ring_coset R (J:((1->num)->A)->bool)) = J`
     (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_KERNEL_RING_COSET];
    ALL_TAC] THEN
   REWRITE_TAC[ring_kernel; IN_ELIM_THM] THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[RING_SUB; RING_POW];
    ASM_REWRITE_TAC[]];
   ALL_TAC] THEN
  (* Step 9: p | x^(q^d) - x from membership in ideal_generated R {p} *)
  SUBGOAL_THEN
    `ring_divides R (p:(1->num)->A)
       (ring_sub R
          (ring_pow R (poly_var f one)
             (CARD(ring_carrier(f:A ring)) EXP
              (poly_deg f (p:(1->num)->A))))
          (poly_var f one))` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`R:((1->num)->A)ring`; `p:(1->num)->A`;
     `ring_sub R
       (ring_pow R (poly_var f one)
          (CARD(ring_carrier(f:A ring)) EXP
           (poly_deg f (p:(1->num)->A))))
       (poly_var (f:A ring) one)`]
     IN_IDEAL_GENERATED_SING_EQ) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 10: Iterate for d | n *)
  (* From d divides n, extract k with n = d * k *)
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  ASM_CASES_TAC `k = 0` THENL
  [(* k = 0 case: n = 0, x^(q^0) - x = x - x = 0, p | 0 *)
   SUBGOAL_THEN `n = 0` SUBST_ALL_TAC THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES]; ALL_TAC] THEN
   REWRITE_TAC[EXP] THEN
   SUBGOAL_THEN
     `ring_sub R
        (ring_pow R (poly_var (f:A ring) one) 1)
        (poly_var f one) = ring_0 R`
     SUBST1_TAC THENL
   [ASM_SIMP_TAC[RING_POW_1] THEN
    ASM_MESON_TAC[RING_SUB_REFL];
    ALL_TAC] THEN
   REWRITE_TAC[RING_DIVIDES_0] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* k > 0 case: use RING_DIVIDES_POW_ITERATE *)
  SUBGOAL_THEN
    `CARD(ring_carrier(f:A ring)) EXP n =
     (CARD(ring_carrier f) EXP (poly_deg f (p:(1->num)->A))) EXP k`
    SUBST1_TAC THENL
  [REWRITE_TAC[EXP_EXP] THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  MP_TAC(ISPECL
    [`R:((1->num)->A)ring`;
     `p:(1->num)->A`;
     `poly_var (f:A ring) one`;
     `CARD(ring_carrier(f:A ring)) EXP poly_deg f (p:(1->num)->A)`;
     `k:num`] RING_DIVIDES_POW_ITERATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
  [ASM_MESON_TAC[FIELD_IMP_INTEGRAL_DOMAIN; INTEGRAL_DOMAIN_POLY_RING];
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* 1 <= q^d: field has >= 2 elements, so q >= 2, d >= 1, q^d >= 2 *)
  SUBGOAL_THEN `2 <= CARD(ring_carrier(f:A ring))` ASSUME_TAC THENL
  [SUBGOAL_THEN `~(ring_1 (f:A ring) = ring_0 f)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:A ring` FIELD_NONTRIVIAL) THEN
    ASM_REWRITE_TAC[TRIVIAL_RING_10]; ALL_TAC] THEN
   MP_TAC(ISPECL [`{ring_0 f, ring_1 (f:A ring)}`; `ring_carrier(f:A ring)`]
     CARD_SUBSET) THEN
   ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY;
                    INSERT_SUBSET; EMPTY_SUBSET; RING_0; RING_1] THEN
   SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY;
            IN_INSERT; NOT_IN_EMPTY] THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC;
   ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0] THEN
  ASM_ARITH_TAC);;

(* Special case: p | x^(q^(deg p)) - x *)
let IRREDUCIBLE_DIVIDES_XQ_MINUS_X = prove
 (`!f:A ring p.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ring_irreducible (poly_ring f (:1)) p
   ==> ring_divides (poly_ring f (:1)) p
         (ring_sub (poly_ring f (:1))
            (ring_pow (poly_ring f (:1)) (poly_var f one)
                      (CARD(ring_carrier f) EXP (poly_deg f p)))
            (poly_var f one))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `poly_deg f (p:(1->num)->A)`]
    IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MESON_TAC[divides; MULT_CLAUSES]);;

(* Helper: x^(q^r) = x for elements of GF(q), for any r *)
let FINITE_FIELD_POW_ITERATE = prove
 (`!f:A ring x r. field f /\ FINITE(ring_carrier f) /\ x IN ring_carrier f
     ==> ring_pow f x (CARD(ring_carrier f) EXP r) = x`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
  [SIMP_TAC[EXP; RING_POW_1];
   STRIP_TAC THEN REWRITE_TAC[EXP] THEN
   ASM_SIMP_TAC[RING_POW_MUL; FINITE_FIELD_ELEMENT_POW] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Helper: iterated Frobenius x -> x^(p^k) is a ring endomorphism *)
let RING_ENDOMORPHISM_FROBENIUS_ITERATE = prove
 (`!r:A ring k. prime(ring_char r)
     ==> ring_endomorphism r (\x. ring_pow r x (ring_char r EXP k))`,
  GEN_TAC THEN INDUCT_TAC THENL
  [(* k = 0: x^1 = identity *)
   DISCH_TAC THEN REWRITE_TAC[EXP] THEN
   MP_TAC(ISPECL [`r:A ring`; `\x:A. x`;
                   `\x:A. ring_pow r x 1`] RING_ENDOMORPHISM_EQ) THEN
   SIMP_TAC[ring_endomorphism; RING_HOMOMORPHISM_ID; RING_POW_1];
   (* k = SUC k: compose Frobenius with iterate *)
   DISCH_TAC THEN
   SUBGOAL_THEN
     `ring_endomorphism (r:A ring)
       ((\x. ring_pow r x (ring_char r)) o
        (\x. ring_pow r x (ring_char r EXP k)))`
     ASSUME_TAC THENL
   [REWRITE_TAC[ring_endomorphism] THEN
    MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
    EXISTS_TAC `r:A ring` THEN
    REWRITE_TAC[GSYM ring_endomorphism] THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
     ASM_SIMP_TAC[RING_ENDOMORPHISM_FROBENIUS]];
    ALL_TAC] THEN
   MP_TAC(ISPECL [`r:A ring`;
     `(\x:A. ring_pow r x (ring_char r)) o
      (\x. ring_pow r x (ring_char r EXP k))`;
     `\x:A. ring_pow r x (ring_char r EXP (SUC k))`]
     RING_ENDOMORPHISM_EQ) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   X_GEN_TAC `x:A` THEN DISCH_TAC THEN
   REWRITE_TAC[o_THM; EXP] THEN
   ONCE_REWRITE_TAC[MULT_SYM] THEN
   ASM_SIMP_TAC[RING_POW_POW]]);;

(* Helper: in a field, if every element satisfies x^n = x, then |field| <= n *)
let FIELD_ROOTS_BOUND = prove
 (`!r:A ring n.
     field r /\ FINITE(ring_carrier r) /\ 2 <= n /\
     (!a. a IN ring_carrier r ==> ring_pow r a n = a)
     ==> CARD(ring_carrier r) <= n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(ring_1 r:A = ring_0 r)` ASSUME_TAC THENL
  [ASM_MESON_TAC[FIELD_NONTRIVIAL; TRIVIAL_RING_10]; ALL_TAC] THEN
  ABBREV_TAC `P = poly_ring (r:A ring) (:1)` THEN
  ABBREV_TAC `g = ring_sub P
    (ring_pow P (poly_var r one) n)
    (poly_var (r:A ring) one)` THEN
  SUBGOAL_THEN `(g:(1->num)->A) IN ring_carrier P` ASSUME_TAC THENL
  [EXPAND_TAC "g" THEN EXPAND_TAC "P" THEN
   SIMP_TAC[RING_SUB; RING_POW; POLY_VAR_UNIV];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(1->num)->A = ring_0 P)` ASSUME_TAC THENL
  [DISCH_TAC THEN
   SUBGOAL_THEN `ring_pow P (poly_var r one:(1->num)->A) n =
                  poly_var r one` MP_TAC THENL
   [SUBGOAL_THEN `ring_sub P (ring_pow P (poly_var r one:(1->num)->A) n)
                    (poly_var r one) = ring_0 P` MP_TAC THENL
    [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "P" THEN
    SIMP_TAC[RING_SUB_EQ_0; RING_POW; POLY_VAR_UNIV]; ALL_TAC] THEN
   DISCH_THEN(MP_TAC o AP_TERM `poly_deg (r:A ring):((1->num)->A)->num`) THEN
   EXPAND_TAC "P" THEN REWRITE_TAC[POLY_DEG_VAR_POW; POLY_DEG_VAR] THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg r (g:(1->num)->A) <= n` ASSUME_TAC THENL
  [EXPAND_TAC "g" THEN EXPAND_TAC "P" THEN
   MP_TAC(ISPECL [`r:A ring`; `ring_pow (poly_ring r (:1))
     (poly_var r one:(1->num)->A) n`; `poly_var (r:A ring) one`]
     POLY_DEG_SUB_LE) THEN
   ANTS_TAC THENL
   [REWRITE_TAC[POLY_RING_CLAUSES; RING_POLYNOMIAL_VAR; IN_UNIV] THEN
    MATCH_MP_TAC RING_POLYNOMIAL_POW THEN
    REWRITE_TAC[RING_POLYNOMIAL_VAR; IN_UNIV]; ALL_TAC] THEN
   REWRITE_TAC[POLY_RING_CLAUSES; POLY_DEG_VAR_POW; POLY_DEG_VAR] THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  (* Every element of r is a root of g *)
  SUBGOAL_THEN `ring_carrier r SUBSET
    {x:A | x IN ring_carrier r /\ poly_eval r g x = ring_0 r}`
    ASSUME_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `a:A` THEN
   DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   EXPAND_TAC "g" THEN EXPAND_TAC "P" THEN
   REWRITE_TAC[POLY_RING_CLAUSES] THEN
   ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_VAR; IN_UNIV;
     RING_POLYNOMIAL_POW; POLY_EVAL_POW; POLY_EVAL_VAR] THEN
   ASM_SIMP_TAC[RING_SUB_EQ_0; RING_POW];
   ALL_TAC] THEN
  (* POLY_ROOT_BOUND gives finite roots and CARD bound *)
  MP_TAC(ISPECL [`r:A ring`; `g:(1->num)->A`] POLY_ROOT_BOUND) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
   EXPAND_TAC "P" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`ring_carrier r:A->bool`;
    `{x:A | x IN ring_carrier r /\ poly_eval r g x = ring_0 r}`]
    CARD_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* Helper: irreducible p of degree d divides a^(q^d) - a for ANY polynomial a *)
let IRRED_DIVIDES_POLY_EVAL_MINUS = prove
 (`!f:A ring p a.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ring_irreducible (poly_ring f (:1)) p /\
   a IN ring_carrier(poly_ring f (:1))
   ==> ring_divides (poly_ring f (:1)) p
         (ring_sub (poly_ring f (:1))
            (ring_pow (poly_ring f (:1)) a
                      (CARD(ring_carrier f) EXP (poly_deg f p)))
            a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = poly_ring (f:A ring) (:1)` THEN
  ABBREV_TAC `J = ideal_generated R {p:(1->num)->A}` THEN
  ABBREV_TAC `K = quotient_ring R (J:((1->num)->A)->bool)` THEN
  SUBGOAL_THEN `PID (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN ASM_MESON_TAC[PID_POLY_RING];
   ALL_TAC] THEN
  SUBGOAL_THEN `maximal_ideal R (J:((1->num)->A)->bool) /\
                ring_ideal R (J:((1->num)->A)->bool)` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN
   ASM_MESON_TAC[RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL; MAXIMAL_IMP_RING_IDEAL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `field (K:(((1->num)->A)->bool) ring) /\
     FINITE(ring_carrier K) /\
     CARD(ring_carrier K) =
     CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`] QUOTIENT_POLY_RING_FINITE_CARD)
   THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `ring_homomorphism(R,K)
                  (ring_coset R (J:((1->num)->A)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_HOMOMORPHISM_RING_COSET];
   ALL_TAC] THEN
  (* proj(a) IN carrier K *)
  SUBGOAL_THEN
    `ring_coset R (J:((1->num)->A)->bool) (a:(1->num)->A) IN ring_carrier K`
    ASSUME_TAC THENL
  [ASM_MESON_TAC[ring_homomorphism; IN_IMAGE; SUBSET]; ALL_TAC] THEN
  (* proj(a)^(q^d) = proj(a) by FINITE_FIELD_ELEMENT_POW *)
  SUBGOAL_THEN
    `ring_pow K
       (ring_coset R (J:((1->num)->A)->bool) (a:(1->num)->A))
       (CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))) =
     ring_coset R J a` ASSUME_TAC THENL
  [SUBGOAL_THEN
     `CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A)) =
      CARD(ring_carrier(K:(((1->num)->A)->bool) ring))`
     SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   MP_TAC(ISPEC `K:(((1->num)->A)->bool) ring` FINITE_FIELD_ELEMENT_POW) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* proj(a^(q^d) - a) = 0 *)
  SUBGOAL_THEN
    `ring_coset R (J:((1->num)->A)->bool)
       (ring_sub R
          (ring_pow R (a:(1->num)->A)
             (CARD(ring_carrier(f:A ring)) EXP
              (poly_deg f (p:(1->num)->A))))
          a) =
     ring_0 (K:(((1->num)->A)->bool) ring)` ASSUME_TAC THENL
  [FIRST_ASSUM(fun hom -> MP_TAC(MATCH_MP RING_HOMOMORPHISM_SUB hom)) THEN
   DISCH_THEN(fun th ->
     MP_TAC(SPECL [`ring_pow R (a:(1->num)->A)
        (CARD(ring_carrier(f:A ring)) EXP
         (poly_deg f (p:(1->num)->A)))`;
       `a:(1->num)->A`] th)) THEN
   ASM_SIMP_TAC[RING_POW] THEN DISCH_THEN SUBST1_TAC THEN
   FIRST_ASSUM(fun hom -> MP_TAC(MATCH_MP RING_HOMOMORPHISM_POW hom)) THEN
   DISCH_THEN(fun th ->
     MP_TAC(SPECL [`a:(1->num)->A`;
       `CARD(ring_carrier(f:A ring)) EXP
        (poly_deg f (p:(1->num)->A))`] th)) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[RING_SUB_REFL];
   ALL_TAC] THEN
  (* a^(q^d) - a IN J (kernel of proj) *)
  SUBGOAL_THEN
    `ring_sub R
       (ring_pow R (a:(1->num)->A)
          (CARD(ring_carrier(f:A ring)) EXP
           (poly_deg f (p:(1->num)->A))))
       a IN J`
    ASSUME_TAC THENL
  [SUBGOAL_THEN
     `ring_kernel(R,K) (ring_coset R (J:((1->num)->A)->bool)) = J`
     (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_KERNEL_RING_COSET]; ALL_TAC] THEN
   REWRITE_TAC[ring_kernel; IN_ELIM_THM] THEN
   ASM_MESON_TAC[RING_SUB; RING_POW];
   ALL_TAC] THEN
  (* p | a^(q^d) - a from ideal membership *)
  MP_TAC(ISPECL [`R:((1->num)->A)ring`; `p:(1->num)->A`;
     `ring_sub R
       (ring_pow R (a:(1->num)->A)
          (CARD(ring_carrier(f:A ring)) EXP
           (poly_deg f (p:(1->num)->A))))
       a`]
     IN_IDEAL_GENERATED_SING_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[]);;

(* Degree bound: if p | x^(q^n) - x with n >= 1, then deg(p) <= n *)
let IRREDUCIBLE_DIVIDES_DEGREE_BOUND = prove
 (`!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ring_irreducible (poly_ring f (:1)) p /\
   ring_divides (poly_ring f (:1)) p
     (ring_sub (poly_ring f (:1))
        (ring_pow (poly_ring f (:1)) (poly_var f one)
                  (CARD(ring_carrier f) EXP n))
        (poly_var f one)) /\
   1 <= n
   ==> poly_deg f p <= n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = poly_ring (f:A ring) (:1)` THEN
  ABBREV_TAC `q = CARD(ring_carrier(f:A ring))` THEN
  ABBREV_TAC `d = poly_deg f (p:(1->num)->A)` THEN
  ABBREV_TAC `J = ideal_generated R {p:(1->num)->A}` THEN
  ABBREV_TAC `K = quotient_ring R (J:((1->num)->A)->bool)` THEN
  (* Setup: K is finite field, |K| = q^d *)
  SUBGOAL_THEN `PID (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN ASM_MESON_TAC[PID_POLY_RING];
   ALL_TAC] THEN
  SUBGOAL_THEN `maximal_ideal R (J:((1->num)->A)->bool) /\
                ring_ideal R (J:((1->num)->A)->bool)` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "J" THEN
   ASM_MESON_TAC[RING_IRREDUCIBLE_EQ_MAXIMAL_IDEAL; MAXIMAL_IMP_RING_IDEAL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `field (K:(((1->num)->A)->bool) ring) /\
     FINITE(ring_carrier K) /\
     CARD(ring_carrier K) =
     CARD(ring_carrier(f:A ring)) EXP (poly_deg f (p:(1->num)->A))`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`] QUOTIENT_POLY_RING_FINITE_CARD)
   THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `CARD(ring_carrier(K:(((1->num)->A)->bool) ring)) = q EXP d`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* ring_char f is prime *)
  SUBGOAL_THEN `prime(ring_char(f:A ring))` ASSUME_TAC THENL
  [MATCH_MP_TAC FINITE_INTEGRAL_DOMAIN_CHAR THEN
   ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN];
   ALL_TAC] THEN
  (* ring_char K = ring_char f *)
  SUBGOAL_THEN `ring_homomorphism(R,K)
                  (ring_coset R (J:((1->num)->A)->bool))` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN ASM_MESON_TAC[RING_HOMOMORPHISM_RING_COSET];
   ALL_TAC] THEN
  SUBGOAL_THEN `ring_char(R:((1->num)->A)ring) = ring_char(f:A ring)`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `(:1)`] RING_MONOMORPHISM_POLY_CONST) THEN
   EXPAND_TAC "R" THEN
   DISCH_THEN(fun th -> MP_TAC(MATCH_MP RING_CHAR_MONOMORPHIC_IMAGE th)) THEN
   SIMP_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `ring_char(K:(((1->num)->A)->bool) ring) =
                ring_char(f:A ring)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`R:((1->num)->A)ring`;
     `K:(((1->num)->A)->bool) ring`;
     `ring_coset R (J:((1->num)->A)->bool)`]
     RING_CHAR_HOMOMORPHIC_IMAGE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   MP_TAC(ISPECL [`K:(((1->num)->A)->bool) ring`;
     `ring_char(f:A ring)`] RING_CHAR_DIVIDES_PRIME) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* q = ring_char(f)^e for some e >= 1 *)
  SUBGOAL_THEN `?e. ~(e = 0) /\ q = ring_char(f:A ring) EXP e`
    STRIP_ASSUME_TAC THENL
  [MP_TAC(ISPEC `f:A ring` FINITE_INTEGRAL_DOMAIN_SIZE) THEN
   ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
   DISCH_THEN(X_CHOOSE_THEN `pp:num`
     (X_CHOOSE_THEN `ee:num` STRIP_ASSUME_TAC)) THEN
   EXISTS_TAC `ee:num` THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `ring_char(f:A ring) = pp` (fun th -> ASM_REWRITE_TAC[th]) THEN
   ASM_MESON_TAC[DIVIDES_PRIME_PRIME; PRIME_DIVEXP; RING_CHAR_DIVIDES_ORDER];
   ALL_TAC] THEN
  (* q^n = ring_char(K)^(e*n) *)
  SUBGOAL_THEN `q EXP n = ring_char(K:(((1->num)->A)->bool) ring) EXP (e * n)`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC[EXP_EXP]; ALL_TAC] THEN
  (* Frobenius y -> y^(q^n) is a ring endomorphism of K *)
  ABBREV_TAC `frob = \y:(((1->num)->A)->bool).
    ring_pow K y (q EXP n)` THEN
  SUBGOAL_THEN `ring_endomorphism (K:(((1->num)->A)->bool) ring) frob`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `frob = (\y:(((1->num)->A)->bool).
     ring_pow K y (ring_char K EXP (e * n)))` SUBST1_TAC THENL
   [EXPAND_TAC "frob" THEN
    REWRITE_TAC[ASSUME `q EXP n = ring_char(K:(((1->num)->A)->bool) ring) EXP (e * n)`];
    ALL_TAC] THEN
   MATCH_MP_TAC RING_ENDOMORPHISM_FROBENIUS_ITERATE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* proj = ring_coset R J; proj is a surjection *)
  ABBREV_TAC `proj = ring_coset R (J:((1->num)->A)->bool)` THEN
  SUBGOAL_THEN `ring_epimorphism(R,K)
    (proj:((1->num)->A) -> ((1->num)->A)->bool)` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN EXPAND_TAC "proj" THEN
   MATCH_MP_TAC RING_EPIMORPHISM_RING_COSET THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* frob o proj is a ring homomorphism R -> K *)
  SUBGOAL_THEN `ring_homomorphism(R,K)
    ((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
     (proj:((1->num)->A) -> ((1->num)->A)->bool))` ASSUME_TAC THENL
  [REWRITE_TAC[ring_endomorphism] THEN
   MATCH_MP_TAC RING_HOMOMORPHISM_COMPOSE THEN
   EXISTS_TAC `K:(((1->num)->A)->bool) ring` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[ring_epimorphism]; ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM ring_endomorphism];
   ALL_TAC] THEN
  (* proj is a ring homomorphism R -> K *)
  SUBGOAL_THEN `ring_homomorphism(R,K)
    (proj:((1->num)->A) -> ((1->num)->A)->bool)` ASSUME_TAC THENL
  [ASM_MESON_TAC[ring_epimorphism]; ALL_TAC] THEN
  (* Agreement on constants: (frob o proj)(poly_const f c) = proj(poly_const f c) *)
  SUBGOAL_THEN
    `!c:A. c IN ring_carrier f
     ==> ((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
          (proj:((1->num)->A) -> ((1->num)->A)->bool))
           (poly_const f c) =
          proj (poly_const f c)` ASSUME_TAC THENL
  [X_GEN_TAC `c:A` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
   (* Replace frob(proj(pc)) with ring_pow K (proj(pc)) (q^n) *)
   SUBGOAL_THEN
     `(frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool)
        ((proj:((1->num)->A) -> ((1->num)->A)->bool) (poly_const (f:A ring) c)) =
      ring_pow K (proj (poly_const f c)) (q EXP n)` SUBST1_TAC THENL
   [EXPAND_TAC "frob" THEN REWRITE_TAC[]; ALL_TAC] THEN
   (* Now goal: ring_pow K (proj(poly_const f c)) (q^n) = proj(poly_const f c) *)
   SUBGOAL_THEN `poly_const (f:A ring) c IN ring_carrier (R:((1->num)->A)ring)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_CONST] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
   (* proj(poly_const f c)^(q^n) = proj(ring_pow R (poly_const f c) (q^n)) *)
   FIRST_ASSUM(fun hom -> MP_TAC(MATCH_MP RING_HOMOMORPHISM_POW hom)) THEN
   DISCH_THEN(fun th ->
     MP_TAC(SPECL [`(poly_const (f:A ring) c):(1->num)->A`;
       `q EXP n`] th)) THEN
   REWRITE_TAC[ASSUME `poly_const (f:A ring) c IN ring_carrier (R:((1->num)->A)ring)`] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   (* ring_pow R (poly_const f c) (q^n) = poly_const f (ring_pow f c (q^n)) *)
   MP_TAC(ISPECL [`f:A ring`; `(:1)`] RING_HOMOMORPHISM_POLY_CONST) THEN
   EXPAND_TAC "R" THEN
   DISCH_THEN(fun hom -> MP_TAC(MATCH_MP RING_HOMOMORPHISM_POW hom)) THEN
   DISCH_THEN(fun th -> MP_TAC(SPECL [`c:A`; `q EXP n`] th)) THEN
   REWRITE_TAC[ASSUME `(c:A) IN ring_carrier (f:A ring)`] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   (* c^(q^n) = c by FINITE_FIELD_POW_ITERATE *)
   AP_TERM_TAC THEN AP_TERM_TAC THEN
   REWRITE_TAC[GSYM(ASSUME `CARD(ring_carrier(f:A ring)) = q`)] THEN
   MATCH_MP_TAC FINITE_FIELD_POW_ITERATE THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Agreement on variable: (frob o proj)(poly_var f one) = proj(poly_var f one) *)
  SUBGOAL_THEN
    `((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
     (proj:((1->num)->A) -> ((1->num)->A)->bool))
      (poly_var (f:A ring) one) = proj (poly_var f one)` ASSUME_TAC THENL
  [REWRITE_TAC[o_THM] THEN
   (* Replace frob(proj(v)) with ring_pow K (proj v) (q^n) *)
   SUBGOAL_THEN
     `(frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool)
        ((proj:((1->num)->A) -> ((1->num)->A)->bool) (poly_var (f:A ring) one)) =
      ring_pow K (proj (poly_var f one)) (q EXP n)` SUBST1_TAC THENL
   [EXPAND_TAC "frob" THEN REWRITE_TAC[]; ALL_TAC] THEN
   (* Goal: ring_pow K (proj v) (q^n) = proj v *)
   SUBGOAL_THEN `poly_var (f:A ring) one IN ring_carrier (R:((1->num)->A)ring)`
     ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_VAR_UNIV]; ALL_TAC] THEN
   (* proj(ring_pow R v (q^n)) = ring_pow K (proj v) (q^n) by homomorphism *)
   FIRST_ASSUM(fun hom -> MP_TAC(MATCH_MP RING_HOMOMORPHISM_POW hom)) THEN
   DISCH_THEN(fun th ->
     MP_TAC(SPECL [`poly_var (f:A ring) one`; `q EXP n`] th)) THEN
   REWRITE_TAC[ASSUME `poly_var (f:A ring) one IN ring_carrier (R:((1->num)->A)ring)`] THEN
   DISCH_THEN(SUBST1_TAC o SYM) THEN
   (* Goal: proj(ring_pow R v (q^n)) = proj v *)
   EXPAND_TAC "proj" THEN
   (* Goal: ring_coset R J (ring_pow R v (q^n)) = ring_coset R J v *)
   MP_TAC(ISPECL [`R:((1->num)->A)ring`;
                   `J:((1->num)->A)->bool`;
                   `ring_pow (R:((1->num)->A)ring) (poly_var (f:A ring) one) (q EXP n)`;
                   `poly_var (f:A ring) one`] RING_COSET_EQ) THEN
   ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_POW]; ALL_TAC] THEN
   DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   (* Goal: ring_sub R (ring_pow R v (q^n)) v IN J *)
   EXPAND_TAC "J" THEN
   MATCH_MP_TAC IN_IDEAL_GENERATED_SING THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Step 1: frob o proj = proj on all of R *)
  MP_TAC(ISPECL [
    `(frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o
     (proj:((1->num)->A) -> ((1->num)->A)->bool)`;
    `proj:((1->num)->A) -> ((1->num)->A)->bool`;
    `f:A ring`;
    `(:1)`;
    `K:(((1->num)->A)->bool) ring`
  ] RING_HOMOMORPHISMS_EQ_FROM_POLY_RING) THEN
  REWRITE_TAC[ASSUME `poly_ring (f:A ring) (:1) = R`] THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[UNIV_1; FORALL_IN_INSERT; NOT_IN_EMPTY]; ALL_TAC] THEN
  DISCH_TAC THEN
  (* Step 2: every element of K satisfies y^(q^n) = y *)
  SUBGOAL_THEN
    `!y:(((1->num)->A)->bool). y IN ring_carrier K
     ==> ring_pow K y (q EXP n) = y` ASSUME_TAC THENL
  [X_GEN_TAC `y:(((1->num)->A)->bool)` THEN DISCH_TAC THEN
   SUBGOAL_THEN `?x:(1->num)->A. x IN ring_carrier R /\
     (proj:((1->num)->A) -> ((1->num)->A)->bool) x = y`
     STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `ring_epimorphism (R:((1->num)->A)ring,
      K:(((1->num)->A)->bool) ring)
      (proj:((1->num)->A) -> ((1->num)->A)->bool)`) THEN
    REWRITE_TAC[ring_epimorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
   SUBGOAL_THEN
     `ring_pow K ((proj:((1->num)->A) -> ((1->num)->A)->bool) (x:(1->num)->A))
        (q EXP n) =
      ((frob:(((1->num)->A)->bool) -> ((1->num)->A)->bool) o proj) x`
     SUBST1_TAC THENL
   [EXPAND_TAC "frob" THEN REWRITE_TAC[o_THM]; ALL_TAC] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 3: 2 <= q *)
  SUBGOAL_THEN `2 <= q` ASSUME_TAC THENL
  [SUBGOAL_THEN `2 <= ring_char(f:A ring)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
   MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `ring_char(f:A ring) EXP 1` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[EXP_1] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ASSUME `q = ring_char(f:A ring) EXP e`; LE_EXP] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  (* Step 4: CARD K <= q^n *)
  SUBGOAL_THEN `2 <= q EXP n` ASSUME_TAC THENL
  [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q EXP 1` THEN
   REWRITE_TAC[EXP_1; LE_EXP] THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; COND_CASES_TAC THEN ASM_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `CARD(ring_carrier(K:(((1->num)->A)->bool) ring)) <= q EXP n`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`K:(((1->num)->A)->bool) ring`; `q EXP n`]
    FIELD_ROOTS_BOUND) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 5: q^d <= q^n implies d <= n *)
  SUBGOAL_THEN `q EXP d <= q EXP n` MP_TAC THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* Converse: if p is monic irreducible of degree d over GF(q) and
   p divides x^(q^n) - x, then d divides n.
   Proof: Write n = k*d + r with 0 <= r < d. Show p | x^(q^(k*d))-x
   via IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN, let u = x^(q^(k*d)),
   then u^(q^r) = x^(q^n), so p | u^(q^r)-x. By RING_DIVIDES_REDUCE,
   p | x^(q^r)-x. If r > 0, IRREDUCIBLE_DIVIDES_DEGREE_BOUND gives
   d <= r < d, contradiction. So r = 0 and d | n. *)
let IRREDUCIBLE_DIVIDES_DEGREE = prove
 (`!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ring_irreducible (poly_ring f (:1)) p /\
   ring_divides (poly_ring f (:1)) p
     (ring_sub (poly_ring f (:1))
        (ring_pow (poly_ring f (:1)) (poly_var f one)
                  (CARD(ring_carrier f) EXP n))
        (poly_var f one))
   ==> (poly_deg f p) divides n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = poly_ring (f:A ring) (:1)` THEN
  ABBREV_TAC `q = CARD(ring_carrier(f:A ring))` THEN
  ABBREV_TAC `d = poly_deg (f:A ring) (p:(1->num)->A)` THEN
  ABBREV_TAC `x = poly_var (f:A ring) one` THEN
  (* Note: ABBREV_TAC modifies both goal AND existing assumptions.
     So assumptions from STRIP_TAC are now in abbreviated form:
     p IN ring_carrier R, ring_irreducible R p,
     ring_divides R p (ring_sub R (ring_pow R x (q EXP n)) x) *)
  (* Case n = 0 *)
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC[DIVIDES_0]; ALL_TAC] THEN
  (* d >= 1: irreducible polynomials have degree >= 1 *)
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
  [EXPAND_TAC "d" THEN
   MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `(:1)`] POLY_NONUNIT_DEGREE_GE_1) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ring_irreducible];
    REWRITE_TAC[]];
   ALL_TAC] THEN
  (* x IN ring_carrier R *)
  SUBGOAL_THEN `(x:(1->num)->A) IN ring_carrier R` ASSUME_TAC THENL
  [EXPAND_TAC "x" THEN EXPAND_TAC "R" THEN
   REWRITE_TAC[POLY_VAR_UNIV];
   ALL_TAC] THEN
  (* integral_domain R *)
  SUBGOAL_THEN `integral_domain (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN
   ASM_MESON_TAC[INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN];
   ALL_TAC] THEN
  (* ~(q = 0) *)
  SUBGOAL_THEN `~(q = 0)` ASSUME_TAC THENL
  [EXPAND_TAC "q" THEN ASM_MESON_TAC[CARD_EQ_0; RING_CARRIER_NONEMPTY];
   ALL_TAC] THEN
  (* p | x^(q^d) - x by IRREDUCIBLE_DIVIDES_XQ_MINUS_X *)
  SUBGOAL_THEN `ring_divides R (p:(1->num)->A)
     (ring_sub R (ring_pow R x (q EXP d)) x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`]
    IRREDUCIBLE_DIVIDES_XQ_MINUS_X) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Division: n = k*d + r, r < d *)
  ABBREV_TAC `k = n DIV d` THEN
  ABBREV_TAC `r = n MOD d` THEN
  SUBGOAL_THEN `n = k * d + r` ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["k"; "r"] THEN
   MESON_TAC[DIVISION_SIMP; ADD_SYM];
   ALL_TAC] THEN
  SUBGOAL_THEN `r < d` ASSUME_TAC THENL
  [EXPAND_TAC "r" THEN REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  (* p | x^(q^(k*d)) - x via IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN *)
  SUBGOAL_THEN `ring_divides R (p:(1->num)->A)
     (ring_sub R (ring_pow R x (q EXP (k * d))) x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `k * d`]
    IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   REWRITE_TAC[divides] THEN EXISTS_TAC `k:num` THEN ARITH_TAC;
   ALL_TAC] THEN
  (* Let u = x^(q^(k*d)). ABBREV_TAC modifies the ring_divides assumption
     about x^(q^(k*d)) to use u, giving p | (u - x) automatically. *)
  ABBREV_TAC `u = ring_pow R (x:(1->num)->A) (q EXP (k * d))` THEN
  (* u IN ring_carrier R *)
  SUBGOAL_THEN `(u:(1->num)->A) IN ring_carrier R` ASSUME_TAC THENL
  [EXPAND_TAC "u" THEN MATCH_MP_TAC RING_POW THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* p | u^(q^r) - x: prove u^(q^r) = x^(q^n), then use original hyp *)
  SUBGOAL_THEN `ring_divides R (p:(1->num)->A)
     (ring_sub R (ring_pow R u (q EXP r)) x)` ASSUME_TAC THENL
  [SUBGOAL_THEN `ring_pow R (u:(1->num)->A) (q EXP r) =
                 ring_pow R x (q EXP n)` SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN
    MP_TAC(ISPECL [`R:((1->num)->A)ring`; `x:(1->num)->A`;
                    `q EXP (k * d)`; `q EXP r`] RING_POW_POW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC];
   ALL_TAC] THEN
  (* ~(q EXP r = 0) *)
  SUBGOAL_THEN `~(q EXP r = 0)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[EXP_EQ_0]; ALL_TAC] THEN
  (* p | x^(q^r) - x via RING_DIVIDES_REDUCE *)
  SUBGOAL_THEN `ring_divides R (p:(1->num)->A)
     (ring_sub R (ring_pow R x (q EXP r)) x)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`R:((1->num)->A)ring`; `p:(1->num)->A`;
                   `u:(1->num)->A`; `x:(1->num)->A`; `q EXP r`]
    RING_DIVIDES_REDUCE) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Case split on r *)
  ASM_CASES_TAC `r = 0` THENL
  [REWRITE_TAC[divides] THEN EXISTS_TAC `k:num` THEN ASM_ARITH_TAC;
   ALL_TAC] THEN
  (* r >= 1: IRREDUCIBLE_DIVIDES_DEGREE_BOUND gives d <= r, contradicting
     r < d *)
  MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `r:num`]
    IRREDUCIBLE_DIVIDES_DEGREE_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Rabin's Irreducibility Test                                               *)
(*                                                                           *)
(* Let f be a monic polynomial of degree n > 0 over GF(q).                   *)
(* Let n = p1^a1 * ... * pk^ak be the prime factorization of n.              *)
(* Then f is irreducible over GF(q) if and only if:                          *)
(* (1) f divides x^(q^n) - x                                                 *)
(* (2) gcd(f, x^(q^(n/p)) - x) = 1 for each prime divisor p of n             *)
(*                                                                           *)
(* Note: condition (1) is equivalent to saying that all roots of f           *)
(* lie in GF(q^n), and condition (2) says no root lies in a proper subfield. *)
(* ------------------------------------------------------------------------- *)

(* Rabin's Test - forward direction: irreducible implies conditions *)
let RABIN_IRREDUCIBILITY_NECESSARY = prove
 (`!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   poly_deg f p = n /\ ~(n = 0) /\
   ring_irreducible (poly_ring f (:1)) p
   ==> ring_divides (poly_ring f (:1)) p
         (ring_sub (poly_ring f (:1))
            (ring_pow (poly_ring f (:1)) (poly_var f one)
                      (CARD(ring_carrier f) EXP n))
            (poly_var f one)) /\
       !q. prime q /\ q divides n
           ==> ring_coprime (poly_ring f (:1))
                 (p, ring_sub (poly_ring f (:1))
                       (ring_pow (poly_ring f (:1)) (poly_var f one)
                                 (CARD(ring_carrier f) EXP (n DIV q)))
                       (poly_var f one))`,
  let DIVIDES_DIV_PRIME_ABSURD = prove
   (`!n q. prime q /\ q divides n /\ ~(n = 0) /\ n divides (n DIV q) ==> F`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 <= q /\ ~(q = 0)` STRIP_ASSUME_TAC THENL
    [MP_TAC(SPEC `q:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `n = (n DIV q) * q` ASSUME_TAC THENL
    [ASM_MESON_TAC[DIVIDES_DIV_MULT]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
    DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
    SUBGOAL_THEN `n * (k * q) = n * 1` MP_TAC THENL
    [REWRITE_TAC[MULT_CLAUSES] THEN
     UNDISCH_TAC `n = (n DIV q) * q` THEN
     ASM_REWRITE_TAC[] THEN ARITH_TAC;
     ALL_TAC] THEN
    REWRITE_TAC[EQ_MULT_LCANCEL] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`; `q:num`] MULT_EQ_1) THEN
    ASM_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
  [(* Part 1: p divides x^(q^n) - x, from IRREDUCIBLE_DIVIDES_XQ_MINUS_X *)
   MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`]
     IRREDUCIBLE_DIVIDES_XQ_MINUS_X) THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Part 2: coprimality for each prime divisor of n *)
  X_GEN_TAC `q':num` THEN STRIP_TAC THEN
  (* By RING_IRREDUCIBLE_DIVIDES_OR_COPRIME: divides or coprime *)
  MP_TAC(ISPECL [`poly_ring (f:A ring) (:1)`;
                  `p:(1->num)->A`;
                  `ring_sub (poly_ring (f:A ring) (:1))
                     (ring_pow (poly_ring (f:A ring) (:1))
                               (poly_var f one)
                               (CARD(ring_carrier f) EXP (n DIV q')))
                     (poly_var (f:A ring) one)`]
                 RING_IRREDUCIBLE_DIVIDES_OR_COPRIME) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC RING_SUB THEN
   CONJ_TAC THENL [MATCH_MP_TAC RING_POW; ALL_TAC] THEN
   REWRITE_TAC[POLY_VAR_UNIV];
   ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC) THENL
  [(* Case: p divides x^(q^(n/q')) - x -- derive contradiction *)
   (* By IRREDUCIBLE_DIVIDES_DEGREE: n divides (n DIV q') *)
   MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `n DIV q'`]
     IRREDUCIBLE_DIVIDES_DEGREE) THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN
   MP_TAC(SPECL [`n:num`; `q':num`] DIVIDES_DIV_PRIME_ABSURD) THEN
   ASM_REWRITE_TAC[];
   (* Case: coprime -- this is the goal *)
   ASM_REWRITE_TAC[]]);;

(* Rabin's Test - backward direction: conditions imply irreducible *)
let RABIN_IRREDUCIBILITY_SUFFICIENT = prove
 (`!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ~(p = ring_0(poly_ring f (:1))) /\
   poly_deg f p = n /\ ~(n = 0) /\
   ring_divides (poly_ring f (:1)) p
     (ring_sub (poly_ring f (:1))
        (ring_pow (poly_ring f (:1)) (poly_var f one)
                  (CARD(ring_carrier f) EXP n))
        (poly_var f one)) /\
   (!q. prime q /\ q divides n
        ==> ring_coprime (poly_ring f (:1))
              (p, ring_sub (poly_ring f (:1))
                    (ring_pow (poly_ring f (:1)) (poly_var f one)
                              (CARD(ring_carrier f) EXP (n DIV q)))
                    (poly_var f one)))
   ==> ring_irreducible (poly_ring f (:1)) p`,
  let PROPER_DIVISOR_PRIME_FACTOR = prove
   (`!d n. d divides n /\ 1 <= d /\ d < n
           ==> ?q. prime q /\ q divides n /\ d divides (n DIV q)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(n DIV d = 1)` ASSUME_TAC THENL
    [DISCH_TAC THEN
     MP_TAC(SPECL [`d:num`; `n:num`] DIVIDES_DIV_MULT) THEN
     ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    MP_TAC(SPEC `n DIV d` PRIME_FACTOR) THEN
    ANTS_TAC THENL
    [MP_TAC(SPECL [`d:num`; `n:num`] DIVIDES_DIV_MULT) THEN
     ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
     ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:num` THEN
    SUBGOAL_THEN `(d * r) divides n` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[GSYM DIVIDES_DIVIDES_DIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `r divides n` ASSUME_TAC THENL
    [ASM_MESON_TAC[DIVIDES_TRANS; DIVIDES_DIV_SELF]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`n:num`; `r:num`; `d:num`] DIVIDES_DIVIDES_DIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[MULT_SYM]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `R = poly_ring (f:A ring) (:1)` THEN
  (* Step 1: integral_domain R *)
  SUBGOAL_THEN `integral_domain (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN
   ASM_MESON_TAC[INTEGRAL_DOMAIN_POLY_RING; FIELD_IMP_INTEGRAL_DOMAIN];
   ALL_TAC] THEN
  (* Step 2: p is not a unit (units have degree 0, but deg p = n > 0) *)
  SUBGOAL_THEN `~(ring_unit R (p:(1->num)->A))` ASSUME_TAC THENL
  [DISCH_TAC THEN
   MP_TAC(ISPECL [`f:A ring`; `(:1)`; `p:(1->num)->A`]
     RING_UNIT_POLY_DOMAIN) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[FIELD_IMP_INTEGRAL_DOMAIN]; ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
   ASM_MESON_TAC[POLY_DEG_CONST];
   ALL_TAC] THEN
  (* Step 3: proof by contradiction *)
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  (* Step 4: extract non-trivial factorization from ~irreducible *)
  SUBGOAL_THEN
    `?a b:(1->num)->A.
       a IN ring_carrier R /\ b IN ring_carrier R /\
       ring_mul R a b = p /\
       ~(ring_unit R a) /\ ~(ring_unit R b)`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_TAC `~ring_irreducible R (p:(1->num)->A)` THEN
   REWRITE_TAC[ring_irreducible; DE_MORGAN_THM; NOT_FORALL_THM;
               NOT_IMP] THEN
   ASM_REWRITE_TAC[POLY_RING_CLAUSES] THEN
   REWRITE_TAC[TAUT `~(a \/ b) <=> ~a /\ ~b`] THEN
   STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`a:(1->num)->A`; `b:(1->num)->A`] THEN
   ASM_REWRITE_TAC[GSYM POLY_RING_CLAUSES];
   ALL_TAC] THEN
  (* Step 5: a and b are nonzero *)
  SUBGOAL_THEN `~(a:(1->num)->A = ring_0 R) /\ ~(b:(1->num)->A = ring_0 R)`
    STRIP_ASSUME_TAC THENL
  [ASM_MESON_TAC[RING_MUL_LZERO; RING_MUL_RZERO]; ALL_TAC] THEN
  (* Step 6: deg(a) + deg(b) = n *)
  SUBGOAL_THEN `ring_polynomial f (a:(1->num)->A) /\
                ring_polynomial f (b:(1->num)->A)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [UNDISCH_TAC `a:(1->num)->A IN ring_carrier R`;
    UNDISCH_TAC `b:(1->num)->A IN ring_carrier R`] THEN
   EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM] THEN
   SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg f (poly_mul f (a:(1->num)->A) (b:(1->num)->A)) =
                poly_deg f a + poly_deg f b` ASSUME_TAC THENL
  [MATCH_MP_TAC POLY_DEG_MUL THEN
   ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
   SUBGOAL_THEN `ring_0 (R:((1->num)->A)ring) = poly_0 (f:A ring)`
     (SUBST1_TAC o SYM) THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
   ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg f (a:(1->num)->A) + poly_deg f (b:(1->num)->A) = n`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `poly_mul f (a:(1->num)->A) (b:(1->num)->A) = p:(1->num)->A`
     ASSUME_TAC THENL
   [ASM_MESON_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
   ASM_MESON_TAC[];
   ALL_TAC] THEN
  (* Step 7: deg(a) >= 1 and deg(b) >= 1 *)
  SUBGOAL_THEN `1 <= poly_deg f (a:(1->num)->A) /\
                1 <= poly_deg f (b:(1->num)->A)` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:A ring`; `a:(1->num)->A`; `(:1)`] POLY_NONUNIT_DEGREE_GE_1);
    MP_TAC(ISPECL [`f:A ring`; `b:(1->num)->A`; `(:1)`] POLY_NONUNIT_DEGREE_GE_1)] THEN
   (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[POLY_RING_CLAUSES]; SIMP_TAC[]]);
   ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg f (a:(1->num)->A) < n` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Step 8: a has an irreducible factor g *)
  SUBGOAL_THEN `UFD (R:((1->num)->A)ring)` ASSUME_TAC THENL
  [EXPAND_TAC "R" THEN ASM_MESON_TAC[PID_IMP_UFD; PID_POLY_RING];
   ALL_TAC] THEN
  MP_TAC(ISPECL [`R:((1->num)->A)ring`; `a:(1->num)->A`]
    NOETHERIAN_DOMAIN_IRREDUCIBLE_FACTOR_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(1->num)->A` STRIP_ASSUME_TAC) THEN
  (* Step 9: g | a | p, so g | p *)
  SUBGOAL_THEN `ring_divides R (g:(1->num)->A) p` ASSUME_TAC THENL
  [MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC `a:(1->num)->A` THEN
   ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ring_divides] THEN ASM_REWRITE_TAC[] THEN
   EXISTS_TAC `b:(1->num)->A` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  (* Step 10: g | x^(q^n) - x via transitivity *)
  SUBGOAL_THEN `ring_divides R (g:(1->num)->A)
     (ring_sub R (ring_pow R (poly_var f one)
                  (CARD(ring_carrier f) EXP n)) (poly_var f one))`
    ASSUME_TAC THENL
  [MATCH_MP_TAC RING_DIVIDES_TRANS THEN EXISTS_TAC `p:(1->num)->A` THEN
   ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[POLY_RING_CLAUSES];
   ALL_TAC] THEN
  (* Step 11: deg(g) | n by IRREDUCIBLE_DIVIDES_DEGREE *)
  SUBGOAL_THEN `g:(1->num)->A IN ring_carrier R` ASSUME_TAC THENL
  [ASM_MESON_TAC[ring_irreducible]; ALL_TAC] THEN
  SUBGOAL_THEN `(poly_deg f (g:(1->num)->A)) divides n` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `g:(1->num)->A`; `n:num`]
    IRREDUCIBLE_DIVIDES_DEGREE) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[POLY_RING_CLAUSES];
   ALL_TAC] THEN
  (* Step 12: deg(g) >= 1 (g is irreducible, hence nonzero non-unit) *)
  SUBGOAL_THEN `1 <= poly_deg f (g:(1->num)->A)` ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `g:(1->num)->A`; `(:1)`] POLY_NONUNIT_DEGREE_GE_1) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ring_irreducible; POLY_RING_CLAUSES];
    SIMP_TAC[]];
   ALL_TAC] THEN
  (* Step 13: deg(g) <= deg(a) < n, so deg(g) < n *)
  SUBGOAL_THEN `poly_deg f (g:(1->num)->A) <= poly_deg f (a:(1->num)->A)` ASSUME_TAC THENL
  [UNDISCH_TAC `ring_divides R (g:(1->num)->A) (a:(1->num)->A)` THEN
   REWRITE_TAC[ring_divides] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `h:(1->num)->A` STRIP_ASSUME_TAC))) THEN
   SUBGOAL_THEN `~(h:(1->num)->A = ring_0 R)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MUL_RZERO]; ALL_TAC] THEN
   SUBGOAL_THEN `poly_deg f (a:(1->num)->A) =
                 poly_deg f (g:(1->num)->A) + poly_deg f (h:(1->num)->A)` MP_TAC THENL
   [SUBGOAL_THEN `poly_deg f (a:(1->num)->A) =
                  poly_deg f (poly_mul f (g:(1->num)->A) (h:(1->num)->A))` SUBST1_TAC THENL
    [AP_TERM_TAC THEN ASM_MESON_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
    MATCH_MP_TAC POLY_DEG_MUL THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `g:(1->num)->A IN ring_carrier R` THEN
     EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM] THEN
     SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
    [UNDISCH_TAC `h:(1->num)->A IN ring_carrier R` THEN
     EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM] THEN
     SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `ring_0 (R:((1->num)->A)ring) = poly_0 (f:A ring)`
      (SUBST1_TAC o SYM) THENL
    [EXPAND_TAC "R" THEN REWRITE_TAC[POLY_RING_CLAUSES]; ALL_TAC] THEN
    ASM_MESON_TAC[ring_irreducible];
    ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `poly_deg f (g:(1->num)->A) < n` ASSUME_TAC THENL
  [ASM_ARITH_TAC; ALL_TAC] THEN
  (* Step 14: number theory: find prime l | n with deg(g) | (n DIV l) *)
  MP_TAC(SPECL [`poly_deg f (g:(1->num)->A)`; `n:num`]
    PROPER_DIVISOR_PRIME_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
  (* Step 15: g | x^(q^(n/l)) - x by IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN *)
  SUBGOAL_THEN `ring_divides R (g:(1->num)->A)
     (ring_sub R (ring_pow R (poly_var f one)
                  (CARD(ring_carrier f) EXP (n DIV l))) (poly_var f one))`
    ASSUME_TAC THENL
  [MP_TAC(ISPECL [`f:A ring`; `g:(1->num)->A`; `n DIV l`]
    IRREDUCIBLE_DIVIDES_XQ_MINUS_X_GEN) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[POLY_RING_CLAUSES];
   ALL_TAC] THEN
  (* Step 16: coprimality gives g is a unit *)
  SUBGOAL_THEN `ring_unit R (g:(1->num)->A)` MP_TAC THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[ring_coprime] THEN
   DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
   DISCH_THEN(MP_TAC o SPEC `g:(1->num)->A`) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
   ASM_MESON_TAC[POLY_RING_CLAUSES];
   ALL_TAC] THEN
  (* Step 17: contradiction - g is irreducible hence not a unit *)
  ASM_MESON_TAC[ring_irreducible]);;

(* Combined Rabin's Test *)
let RABIN_IRREDUCIBILITY_TEST = prove
 (`!f:A ring p n.
   field f /\ FINITE(ring_carrier f) /\
   p IN ring_carrier(poly_ring f (:1)) /\
   ~(p = ring_0(poly_ring f (:1))) /\
   ~(ring_unit (poly_ring f (:1)) p) /\
   poly_deg f p = n /\ ~(n = 0)
   ==> (ring_irreducible (poly_ring f (:1)) p <=>
        ring_divides (poly_ring f (:1)) p
          (ring_sub (poly_ring f (:1))
             (ring_pow (poly_ring f (:1)) (poly_var f one)
                       (CARD(ring_carrier f) EXP n))
             (poly_var f one)) /\
        !q. prime q /\ q divides n
            ==> ring_coprime (poly_ring f (:1))
                  (p, ring_sub (poly_ring f (:1))
                        (ring_pow (poly_ring f (:1)) (poly_var f one)
                                  (CARD(ring_carrier f) EXP (n DIV q)))
                        (poly_var f one)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THENL
  [(* Forward: irreducible ==> conditions *)
   DISCH_TAC THEN
   MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `n:num`]
     RABIN_IRREDUCIBILITY_NECESSARY) THEN
   ASM_REWRITE_TAC[];
   (* Backward: conditions ==> irreducible *)
   STRIP_TAC THEN
   MP_TAC(ISPECL [`f:A ring`; `p:(1->num)->A`; `n:num`]
     RABIN_IRREDUCIBILITY_SUFFICIENT) THEN
   ASM_REWRITE_TAC[]]);;
