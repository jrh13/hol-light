(* ========================================================================= *)
(* The decomposition law in a quadratic field k = Q(x), x^2 = d squarefree,  *)
(* d <> 1: a prime p ramifies (pO = P^2) iff p divides the discriminant      *)
(* (QUADRATIC_FIELD_RAMIFIED); an odd prime p not dividing d splits (pO = P  *)
(* Q with P <> Q) iff d is a square mod p and is inert (pO prime) otherwise  *)
(* (QUADRATIC_FIELD_ODD_PRIME); for d == 1 (mod 4) the prime 2 splits iff d  *)
(* == 1 (mod 8) and is inert iff d == 5 (mod 8) (QUADRATIC_FIELD_PRIME_TWO). *)
(*                                                                           *)
(* The primes of the decomposition law named, for x^2 = d with d squarefree, *)
(* d <> 1:                                                                   *)
(*   p odd, p not dividing d, y^2 == d (mod p): pO = (p, x - y)(p, x + y),   *)
(*     two distinct primes of norm p (QUADRATIC_FIELD_SPLIT_ODD_PRIME);      *)
(*   p odd dividing d: pO = (p, x)^2, (p, x) of norm p                       *)
(*     (QUADRATIC_FIELD_RAMIFIED_ODD_PRIME);                                 *)
(*   d == 2, 3 (mod 4): 2O = (2, x)^2 for d even and 2O = (2, 1 + x)^2 for d *)
(*     odd, of norm 2 (QUADRATIC_FIELD_RAMIFIED_TWO);                        *)
(*   d == 1 (mod 8): 2O = (2, w)(2, 1 - w) with w = (1 + x) / 2, two         *)
(*     distinct primes of norm 2 (QUADRATIC_FIELD_SPLIT_TWO).                *)
(*                                                                           *)
(* Route: ramification from the Dedekind discriminant theorem and the        *)
(* fundamental identity (in degree 2 a ramified prime is the only prime      *)
(* above p and has e = 2); splitting from the Dedekind-Kummer theorem for a  *)
(* root a of X^2 - (b X + c) with O = Z[a] + pO: two distinct roots y1, y2   *)
(* mod p give the two primes (p, a - y1), (p, a - y2) of residue degree 1    *)
(* (QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES, and                              *)
(* QUADRATIC_DEDEKIND_KUMMER_SPLIT for their existence), a double root y     *)
(* gives pO = (p, a - y)^2 (QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME), no    *)
(* root mod p gives pO prime (QUADRATIC_DEDEKIND_KUMMER_INERT); the prime    *)
(* (p, g(a)) for the factor g = X - y mod p is (p, a - y)                    *)
(* (DEDEKIND_KUMMER_LINEAR_IDEAL of ANT/dedekind_kummer.ml). This is applied *)
(* to a = x for odd p (the index of Z[x] in O divides 2) and for p = 2 when  *)
(* d == 2, 3 (mod 4), and to a = (1 + x) / 2 for the prime 2 when d == 1     *)
(* (mod 4); split and inert exclude each other.                              *)
(*                                                                           *)
(* Uses: Library/integer.ml, Library/ringtheory.ml (polynomials,             *)
(* integer_mod_ring, POLY_DEG_2_IRREDUCIBLE), Library/fieldtheory.ml,        *)
(* ANT/ideal_arith.ml, ANT/dedekind.ml, ANT/ideal_norm.ml,                   *)
(* Library/ring_det.ml (free_basis), ANT/numfield.ml,                        *)
(* ANT/ring_of_integers.ml, ANT/prime_split.ml, ANT/discriminant.ml,         *)
(* ANT/ramification.ml, ANT/dedekind_kummer.ml, ANT/quadratic.ml.            *)
(* ========================================================================= *)

needs "Library/integer.ml";;
needs "Library/ringtheory.ml";;
needs "Library/fieldtheory.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/prime_split.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/ramification.ml";;
needs "ANT/dedekind_kummer.ml";;
needs "ANT/quadratic.ml";;

(* ------------------------------------------------------------------------- *)
(* Monic quadratic polynomials.                                              *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_POLY_IN_CARRIER = prove
 (`!r:A ring b c.
        b IN ring_carrier r /\ c IN ring_carrier r
        ==> ring_sub (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
              (ring_add (poly_ring r (:1))
                (ring_mul (poly_ring r (:1)) (poly_const r b) (poly_var r one))
                (poly_const r c)) IN ring_carrier(poly_ring r (:1))`,
  SIMP_TAC[RING_SUB; RING_POW; RING_ADD; RING_MUL; POLY_VAR_UNIV; POLY_CONST]);;

let QUADRATIC_POLY_DEG = prove
 (`!r:A ring b c.
        ~trivial_ring r /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> poly_deg r
             (ring_sub (poly_ring r (:1))
               (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
               (ring_add (poly_ring r (:1))
                 (ring_mul (poly_ring r (:1)) (poly_const r b)
                   (poly_var r one))
                 (poly_const r c))) = 2 /\
            monic r
             (ring_sub (poly_ring r (:1))
               (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
               (ring_add (poly_ring r (:1))
                 (ring_mul (poly_ring r (:1)) (poly_const r b)
                   (poly_var r one))
                 (poly_const r c)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[monic]
   `poly_deg (r:A ring) p = 2 /\ coeff 2 p = ring_1 r
    ==> poly_deg r p = 2 /\ monic r p`) THEN
  MP_TAC(ISPECL [`r:A ring`; `b:A`; `c:A`] QUADRATIC_POLY_IN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[POLY_RING_CLAUSES; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d. coeff d (poly_sub r (poly_pow r (poly_var r one) 2)
                  (poly_add r (poly_mul r (poly_const r b) (poly_var r one))
                              (poly_const r c))) =
        if d = 2 then ring_1 r else if d = 1 then ring_neg r b
        else if d = 0 then ring_neg r c else ring_0 r:A`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    ASM_SIMP_TAC[COEFF_POLY_SUB; COEFF_POLY_ADD; COEFF_POLY_LMUL;
                 COEFF_POLY_VAR; COEFF_POLY_VARPOW; COEFF_POLY_CONST;
                 RING_POWERSERIES_VAR] THEN
    MAP_EVERY ASM_CASES_TAC [`d = 2`; `d = 1`; `d = 0`] THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN
    ASM_SIMP_TAC[RING_MUL_RZERO; RING_MUL_RID; RING_ADD_LZERO; RING_ADD_RZERO;
                 RING_SUB_RZERO; RING_SUB_LZERO; RING_1; RING_0; RING_NEG;
                 RING_NEG_0; ring_sub];
    ASM_REWRITE_TAC[ARITH_EQ] THEN MATCH_MP_TAC POLY_DEG_EQ_COEFF THEN
    ASM_SIMP_TAC[RING_POLYNOMIAL_IMP_POWERSERIES] THEN CONJ_TAC THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ARITH_TAC;
      ASM_MESON_TAC[TRIVIAL_RING_10]]]);;

let QUADRATIC_POLY_EXTEND = prove
 (`!r:A ring t:B ring h z b c.
        ring_homomorphism(r,t) h /\ z IN ring_carrier t /\
        b IN ring_carrier r /\ c IN ring_carrier r
        ==> poly_extend (r,t) h (\v. z)
             (ring_sub (poly_ring r (:1))
               (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
               (ring_add (poly_ring r (:1))
                 (ring_mul (poly_ring r (:1)) (poly_const r b)
                   (poly_var r one))
                 (poly_const r c))) =
            ring_sub t (ring_pow t z 2)
                       (ring_add t (ring_mul t (h b) z) (h c))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `t:B ring`; `(:1)`; `h:A->B`; `\v:1. (z:B)`]
    RING_HOMOMORPHISM_POLY_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_SUB th;
                 MATCH_MP RING_HOMOMORPHISM_ADD th;
                 MATCH_MP RING_HOMOMORPHISM_MUL th;
                 MATCH_MP RING_HOMOMORPHISM_POW th; RING_POW; RING_ADD;
                 RING_MUL; POLY_VAR_UNIV; POLY_CONST]) THEN
  ASM_SIMP_TAC[POLY_EXTEND_VAR; POLY_EXTEND_CONST]);;

let QUADRATIC_POLY_HOMOMORPHIC_IMAGE = prove
 (`!r:A ring s:B ring f b c.
        ring_homomorphism(r,s) f /\ b IN ring_carrier r /\ c IN ring_carrier r
        ==> f o ring_sub (poly_ring r (:1))
                  (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
                  (ring_add (poly_ring r (:1))
                    (ring_mul (poly_ring r (:1)) (poly_const r b)
                      (poly_var r one))
                    (poly_const r c)) =
            ring_sub (poly_ring s (:1))
              (ring_pow (poly_ring s (:1)) (poly_var s one) 2)
              (ring_add (poly_ring s (:1))
                (ring_mul (poly_ring s (:1)) (poly_const s (f b))
                  (poly_var s one))
                (poly_const s (f c)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:B ring`; `f:A->B`; `(:1)`]
    RING_HOMOMORPHISM_POLY_RINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
    MP_TAC(BETA_RULE(MATCH_MP RING_HOMOMORPHISM_SUB th)) THEN
    MP_TAC(BETA_RULE(MATCH_MP RING_HOMOMORPHISM_ADD th)) THEN
    MP_TAC(BETA_RULE(MATCH_MP RING_HOMOMORPHISM_MUL th)) THEN
    MP_TAC(BETA_RULE(MATCH_MP RING_HOMOMORPHISM_POW th))) THEN
  REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[RING_POW; RING_ADD; RING_MUL; POLY_VAR_UNIV; POLY_CONST] THEN
  ASM_SIMP_TAC[ISPECL [`r:A ring`; `s:B ring`; `f:A->B`]
                 POLY_COMPOSE_HOMOMORPHISM_VAR;
               ISPECL [`r:A ring`; `s:B ring`; `f:A->B`]
                 POLY_COMPOSE_HOMOMORPHISM_CONST]);;

let QUADRATIC_POLY_FACTOR = prove
 (`!r:A ring r1 r2.
        r1 IN ring_carrier r /\ r2 IN ring_carrier r
        ==> ring_sub (poly_ring r (:1))
              (ring_pow (poly_ring r (:1)) (poly_var r one) 2)
              (ring_add (poly_ring r (:1))
                (ring_mul (poly_ring r (:1))
                  (poly_const r (ring_add r r1 r2)) (poly_var r one))
                (poly_const r (ring_neg r (ring_mul r r1 r2)))) =
            ring_mul (poly_ring r (:1))
              (poly_sub r (poly_var r one) (poly_const r r1))
              (poly_sub r (poly_var r one) (poly_const r r2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `(:1)`] RING_HOMOMORPHISM_POLY_CONST) THEN
  DISCH_THEN(fun th ->
    ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_ADD th;
                 MATCH_MP RING_HOMOMORPHISM_NEG th;
                 MATCH_MP RING_HOMOMORPHISM_MUL th; RING_MUL]) THEN
  REWRITE_TAC[GSYM(ISPECL [`r:A ring`; `(:1)`]
                   (el 5 (CONJUNCTS POLY_RING_CLAUSES)))] THEN
  MP_TAC(ISPECL [`poly_ring (r:A ring) (:1)`; `poly_var r one:(1->num)->A`;
                 `poly_const r r1:(1->num)->A`; `poly_const r r2:(1->num)->A`]
   (RING_RULE
     `!R:B ring x a b.
        ring_sub R (ring_pow R x 2)
          (ring_add R (ring_mul R (ring_add R a b) x)
                      (ring_neg R (ring_mul R a b))) =
        ring_mul R (ring_sub R x a) (ring_sub R x b)`)) THEN
  ASM_SIMP_TAC[POLY_VAR_UNIV; POLY_CONST]);;

let QUADRATIC_POLY_INTEGER_ROOT = prove
 (`!k:A ring a b c p.
        a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c)
        ==> ?m. m IN ring_carrier(poly_ring integer_ring (:1)) /\
                monic integer_ring m /\ poly_deg integer_ring m = 2 /\
                poly_extend (integer_ring,k) (ring_of_int k) (\v. a) m =
                ring_0 k /\
                ring_of_int (integer_mod_ring p) o m =
                ring_sub (poly_ring (integer_mod_ring p) (:1))
                 (ring_pow (poly_ring (integer_mod_ring p) (:1))
                   (poly_var (integer_mod_ring p) one) 2)
                 (ring_add (poly_ring (integer_mod_ring p) (:1))
                   (ring_mul (poly_ring (integer_mod_ring p) (:1))
                     (poly_const (integer_mod_ring p)
                       (ring_of_int (integer_mod_ring p) b))
                     (poly_var (integer_mod_ring p) one))
                   (poly_const (integer_mod_ring p)
                     (ring_of_int (integer_mod_ring p) c)))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `ring_sub (poly_ring integer_ring (:1))
     (ring_pow (poly_ring integer_ring (:1)) (poly_var integer_ring one) 2)
     (ring_add (poly_ring integer_ring (:1))
       (ring_mul (poly_ring integer_ring (:1)) (poly_const integer_ring b)
         (poly_var integer_ring one))
       (poly_const integer_ring c))` THEN
  SIMP_TAC[QUADRATIC_POLY_IN_CARRIER; QUADRATIC_POLY_DEG;
           QUADRATIC_POLY_EXTEND; INTEGER_RING; IN_UNIV;
           ISPECL [`integer_ring`; `integer_mod_ring p`;
                   `ring_of_int (integer_mod_ring p)`]
             QUADRATIC_POLY_HOMOMORPHIC_IMAGE;
           RING_HOMOMORPHISM_INTEGER_RING_OF_INT; NOT_TRIVIAL_INTEGER_RING;
           ASSUME `(a:A) IN ring_carrier k`] THEN
  SIMP_TAC[RING_SUB_EQ_0; RING_POW; RING_ADD; RING_MUL; RING_OF_INT;
           ASSUME `(a:A) IN ring_carrier k`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Dedekind-Kummer theorem in degree 2.                                  *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES = prove
 (`!k:A ring a p b c y1 y2 P1 P2.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        prime p /\ a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        ~((y1 == y2) (mod &p)) /\ (y1 + y2 == b) (mod &p) /\
        (y1 * y2 == --c) (mod &p) /\
        P1 = ideal_generated (ring_of_integers k)
               {ring_of_num k p, ring_sub k a (ring_of_int k y1)} /\
        P2 = ideal_generated (ring_of_integers k)
               {ring_of_num k p, ring_sub k a (ring_of_int k y2)}
        ==> prime_ideal (ring_of_integers k) P1 /\
            prime_ideal (ring_of_integers k) P2 /\ ~(P1 = P2) /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_prod (ring_of_integers k) P1 P2 /\
            residue_degree (integer_ring,ring_of_integers k)
              (ring_of_int k) P1 = 1 /\
            residue_degree (integer_ring,ring_of_integers k)
              (ring_of_int k) P2 = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`--b:int`; `--c:int`] THEN
    ASM_REWRITE_TAC[RING_OF_INT_NEG] THEN
    MP_TAC(ISPECL [`k:A ring`; `a:A`; `ring_of_int k b:A`;
                   `ring_of_int k c:A`] (RING_RULE
     `!r a b c:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  c IN ring_carrier r
                  ==> ring_add r (ring_add r (ring_mul r b a) c)
                        (ring_add r (ring_mul r (ring_neg r b) a)
                                    (ring_neg r c)) = ring_0 r`)) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:int`; `c:int`; `p:num`]
    QUADRATIC_POLY_INTEGER_ROOT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:(1->num)->int` THEN STRIP_TAC THEN
  ABBREV_TAC `r1 = ring_of_int (integer_mod_ring p) y1` THEN
  ABBREV_TAC `r2 = ring_of_int (integer_mod_ring p) y2` THEN
  SUBGOAL_THEN
   `r1 IN ring_carrier(integer_mod_ring p) /\
    r2 IN ring_carrier(integer_mod_ring p) /\ ~(r1 = r2) /\
    ring_add (integer_mod_ring p) r1 r2 =
    ring_of_int (integer_mod_ring p) b /\
    ring_neg (integer_mod_ring p) (ring_mul (integer_mod_ring p) r1 r2) =
    ring_of_int (integer_mod_ring p) c`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r1"; "r2"] THEN
    REWRITE_TAC[RING_OF_INT; GSYM RING_OF_INT_ADD; GSYM RING_OF_INT_MUL;
                GSYM RING_OF_INT_NEG] THEN
    REWRITE_TAC[INTEGER_MOD_RING_OF_INT; INT_REM_EQ] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((y1:int) * y2 == --c) (mod &p)` THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `ring_of_int (integer_mod_ring p) o (m:(1->num)->int)`))
  THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rhs(concl th) = `ring_of_int (integer_mod_ring p) c`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rhs(concl th) = `ring_of_int (integer_mod_ring p) b`)) THEN
  ASM_SIMP_TAC[QUADRATIC_POLY_FACTOR] THEN DISCH_TAC THEN
  ABBREV_TAC
   `g = \i. if i = 0
            then poly_sub (integer_mod_ring p)
                   (poly_var (integer_mod_ring p) one)
                   (poly_const (integer_mod_ring p) r1)
            else poly_sub (integer_mod_ring p)
                   (poly_var (integer_mod_ring p) one)
                   (poly_const (integer_mod_ring p) r2)` THEN
  SUBGOAL_THEN
   `(!i. i IN {0,1}
         ==> (g:num->(1->num)->int) i IN
             ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
             monic (integer_mod_ring p) (g i) /\
             ring_irreducible (poly_ring (integer_mod_ring p) (:1)) (g i) /\
             poly_deg (integer_mod_ring p) (g i) = 1) /\
    ~(g 0 = g 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] THEN
    ASM_SIMP_TAC[MONIC_X_MINUS_A; RING_IRREDUCIBLE_X_MINUS_A;
                 FIELD_INTEGER_MOD_RING; FIELD_IMP_INTEGRAL_DOMAIN;
                 FIELD_IMP_NONTRIVIAL_RING; POLY_DEG_X_MINUS_A] THEN
    REWRITE_TAC[GSYM(ISPECL [`integer_mod_ring p`; `(:1)`]
                     (el 5 (CONJUNCTS POLY_RING_CLAUSES)))] THEN
    ASM_SIMP_TAC[RING_SUB; POLY_VAR_UNIV; POLY_CONST] THEN
    DISCH_THEN(MP_TAC o AP_TERM `coeff 0:((1->num)->int)->int`) THEN
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_SUB; COEFF_POLY_VAR;
                COEFF_POLY_CONST; ARITH_EQ] THEN
    ASM_SIMP_TAC[RING_SUB_LZERO; RING_NEG_EQ];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`k:A ring`; `a:A`; `p:num`; `m:(1->num)->int`; `{0,1}`;
    `g:num->(1->num)->int`; `\i:num. 1`;
    `\i:num. ideal_generated (ring_of_integers k)
               {ring_of_num k p,
                poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                  ((g:num->(1->num)->int) i):A}`] DEDEKIND_KUMMER_Q) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; ARITH_EQ] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN
    EXPAND_TAC "g" THEN
    SIMP_TAC[RING_PRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY; ARITH_EQ; RING_PRODUCT_SING] THEN
    REWRITE_TAC[GSYM(ISPECL [`integer_mod_ring p`; `(:1)`]
                     (el 5 (CONJUNCTS POLY_RING_CLAUSES)))] THEN
    ASM_SIMP_TAC[RING_POW_1; RING_SUB; POLY_VAR_UNIV; POLY_CONST];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_generated (ring_of_integers k)
      {ring_of_num k p,
       poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
         ((g:num->(1->num)->int) 0):A} =
    ideal_generated (ring_of_integers k)
      {ring_of_num k p, ring_sub k a (ring_of_int k y1)} /\
    ideal_generated (ring_of_integers k)
      {ring_of_num k p,
       poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
         ((g:num->(1->num)->int) 1):A} =
    ideal_generated (ring_of_integers k)
      {ring_of_num k p, ring_sub k a (ring_of_int k y2)}`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MAP_EVERY EXPAND_TAC ["r1"; "r2"] THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC DEDEKIND_KUMMER_LINEAR_IDEAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (MP_TAC o CONJUNCT2)) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              ARITH_EQ] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IDEAL_PRODUCT_INSERT; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY; ARITH_EQ; IDEAL_PRODUCT_SING;
               RING_IDEAL_IDEAL_POW; IDEAL_POW_1; RING_IDEAL_IDEAL_GENERATED]);;

let QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME = prove
 (`!k:A ring a p b c y P.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        prime p /\ a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        (y + y == b) (mod &p) /\ (y * y == --c) (mod &p) /\
        P = ideal_generated (ring_of_integers k)
              {ring_of_num k p, ring_sub k a (ring_of_int k y)}
        ==> prime_ideal (ring_of_integers k) P /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k) P 2 /\
            residue_degree (integer_ring,ring_of_integers k)
              (ring_of_int k) P = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`--b:int`; `--c:int`] THEN
    ASM_REWRITE_TAC[RING_OF_INT_NEG] THEN
    MP_TAC(ISPECL [`k:A ring`; `a:A`; `ring_of_int k b:A`;
                   `ring_of_int k c:A`] (RING_RULE
     `!r a b c:A. a IN ring_carrier r /\ b IN ring_carrier r /\
                  c IN ring_carrier r
                  ==> ring_add r (ring_add r (ring_mul r b a) c)
                        (ring_add r (ring_mul r (ring_neg r b) a)
                                    (ring_neg r c)) = ring_0 r`)) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:int`; `c:int`; `p:num`]
    QUADRATIC_POLY_INTEGER_ROOT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:(1->num)->int` THEN STRIP_TAC THEN
  ABBREV_TAC `r = ring_of_int (integer_mod_ring p) y` THEN
  SUBGOAL_THEN
   `r IN ring_carrier(integer_mod_ring p) /\
    ring_add (integer_mod_ring p) r r =
    ring_of_int (integer_mod_ring p) b /\
    ring_neg (integer_mod_ring p) (ring_mul (integer_mod_ring p) r r) =
    ring_of_int (integer_mod_ring p) c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    REWRITE_TAC[RING_OF_INT; GSYM RING_OF_INT_ADD; GSYM RING_OF_INT_MUL;
                GSYM RING_OF_INT_NEG] THEN
    REWRITE_TAC[INTEGER_MOD_RING_OF_INT; INT_REM_EQ] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `((y:int) * y == --c) (mod &p)` THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `ring_of_int (integer_mod_ring p) o (m:(1->num)->int)`))
  THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rhs(concl th) = `ring_of_int (integer_mod_ring p) c`)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    rhs(concl th) = `ring_of_int (integer_mod_ring p) b`)) THEN
  ASM_SIMP_TAC[QUADRATIC_POLY_FACTOR] THEN DISCH_TAC THEN
  ABBREV_TAC
   `g = \i:num. poly_sub (integer_mod_ring p)
                  (poly_var (integer_mod_ring p) one)
                  (poly_const (integer_mod_ring p) r)` THEN
  SUBGOAL_THEN
   `(g:num->(1->num)->int) 0 IN
    ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
    monic (integer_mod_ring p) (g 0) /\
    ring_irreducible (poly_ring (integer_mod_ring p) (:1)) (g 0) /\
    poly_deg (integer_mod_ring p) (g 0) = 1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[MONIC_X_MINUS_A; RING_IRREDUCIBLE_X_MINUS_A;
                 FIELD_INTEGER_MOD_RING; FIELD_IMP_INTEGRAL_DOMAIN;
                 FIELD_IMP_NONTRIVIAL_RING; POLY_DEG_X_MINUS_A] THEN
    REWRITE_TAC[GSYM(ISPECL [`integer_mod_ring p`; `(:1)`]
                     (el 5 (CONJUNCTS POLY_RING_CLAUSES)))] THEN
    ASM_SIMP_TAC[RING_SUB; POLY_VAR_UNIV; POLY_CONST];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`k:A ring`; `a:A`; `p:num`; `m:(1->num)->int`; `{0}`;
    `g:num->(1->num)->int`; `\i:num. 2`;
    `\i:num. ideal_generated (ring_of_integers k)
               {ring_of_num k p,
                poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                  ((g:num->(1->num)->int) i):A}`] DEDEKIND_KUMMER_Q) THEN
  ASM_REWRITE_TAC[FINITE_SING; IN_SING; FORALL_UNWIND_THM2; ARITH_EQ] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RING_PRODUCT_SING] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "g" THEN
    REWRITE_TAC[GSYM(ISPECL [`integer_mod_ring p`; `(:1)`]
                     (el 5 (CONJUNCTS POLY_RING_CLAUSES)))] THEN
    ASM_SIMP_TAC[RING_POW; RING_SUB; POLY_VAR_UNIV; POLY_CONST; RING_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ideal_generated (ring_of_integers k)
      {ring_of_num k p,
       poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
         ((g:num->(1->num)->int) 0):A} =
    ideal_generated (ring_of_integers k)
      {ring_of_num k p, ring_sub k a (ring_of_int k y)}`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN EXPAND_TAC "r" THEN
    MATCH_MP_TAC DEDEKIND_KUMMER_LINEAR_IDEAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IDEAL_PRODUCT_SING; RING_IDEAL_IDEAL_POW]);;

let QUADRATIC_DEDEKIND_KUMMER_SPLIT = prove
 (`!k:A ring a p b c y1 y2.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        prime p /\ a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        ~((y1 == y2) (mod &p)) /\ (y1 + y2 == b) (mod &p) /\
        (y1 * y2 == --c) (mod &p)
        ==> ?P Q. prime_ideal (ring_of_integers k) P /\
                  prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
                  ideal_generated (ring_of_integers k) {ring_of_num k p} =
                  ideal_prod (ring_of_integers k) P Q`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y1):A}`;
    `ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y2):A}`] THEN
  MP_TAC(ISPECL
   [`k:A ring`; `a:A`; `p:num`; `b:int`; `c:int`; `y1:int`; `y2:int`;
    `ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y1):A}`;
    `ideal_generated (ring_of_integers k)
       {ring_of_num k p, ring_sub k a (ring_of_int k y2):A}`]
   QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES) THEN
  ASM_SIMP_TAC[]);;

let QUADRATIC_DEDEKIND_KUMMER_INERT = prove
 (`!k:A ring a p b c.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        prime p /\ a IN ring_carrier k /\
        ring_pow k a 2 =
        ring_add k (ring_mul k (ring_of_int k b) a) (ring_of_int k c) /\
        ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {a}))
          (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
        ring_carrier(ring_of_integers k) /\
        (!y. ~((y pow 2 == b * y + c) (mod &p)))
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `a:A`; `b:int`; `c:int`; `p:num`]
    QUADRATIC_POLY_INTEGER_ROOT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m:(1->num)->int` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o
    GEN_REWRITE_RULE I [GSYM FIELD_INTEGER_MOD_RING]) THEN
  SUBGOAL_THEN
   `ring_of_int (integer_mod_ring p) o m IN
    ring_carrier(poly_ring (integer_mod_ring p) (:1)) /\
    monic (integer_mod_ring p) (ring_of_int (integer_mod_ring p) o m) /\
    ring_irreducible (poly_ring (integer_mod_ring p) (:1))
      (ring_of_int (integer_mod_ring p) o m)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[QUADRATIC_POLY_IN_CARRIER; QUADRATIC_POLY_DEG; RING_OF_INT;
                 FIELD_IMP_NONTRIVIAL_RING] THEN
    MATCH_MP_TAC POLY_DEG_2_IRREDUCIBLE THEN
    ASM_SIMP_TAC[QUADRATIC_POLY_IN_CARRIER; QUADRATIC_POLY_DEG; RING_OF_INT;
                 FIELD_IMP_NONTRIVIAL_RING] THEN
    X_GEN_TAC `y:int` THEN DISCH_TAC THEN REWRITE_TAC[poly_eval] THEN
    REWRITE_TAC[GSYM(REWRITE_RULE[RING_HOMOMORPHISM_I; I_O_ID]
      (ISPECL [`integer_mod_ring p`; `integer_mod_ring p`; `I:int->int`]
         POLY_EXTEND_EVALUATE))] THEN
    ASM_SIMP_TAC[QUADRATIC_POLY_EXTEND; RING_HOMOMORPHISM_I; RING_OF_INT;
                 I_THM] THEN
    SUBGOAL_THEN `y = ring_of_int (integer_mod_ring p) y` SUBST1_TAC THENL
     [REWRITE_TAC[INTEGER_MOD_RING_OF_INT] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INT_REM_LT THEN
      UNDISCH_TAC `y IN ring_carrier (integer_mod_ring p)` THEN
      ASM_SIMP_TAC[IN_INTEGER_MOD_RING_CARRIER; INT_OF_NUM_EQ; PRIME_IMP_NZ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM RING_OF_INT_POW; GSYM RING_OF_INT_MUL;
                GSYM RING_OF_INT_ADD; GSYM RING_OF_INT_SUB] THEN
    REWRITE_TAC[RING_OF_INT_EQ_0; INTEGER_MOD_RING_CHAR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:int` o check (is_forall o concl)) THEN
    REWRITE_TAC[INTEGER_RULE
     `!x y n:int. (x == y) (mod n) <=> n divides (x - y)`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhand(concl th) = `ring_of_int (integer_mod_ring p) o (m:(1->num)->int)`))
  THEN
  MP_TAC(ISPECL
   [`k:A ring`; `a:A`; `p:num`; `m:(1->num)->int`; `{0}`;
    `\i:num. ring_of_int (integer_mod_ring p) o (m:(1->num)->int)`;
    `\i:num. 1`;
    `\i:num. ideal_generated (ring_of_integers k)
               {ring_of_num k p,
                poly_extend (integer_ring,k) (ring_of_int k) (\v. a)
                  (ring_of_int (integer_mod_ring p) o (m:(1->num)->int)):A}`]
   DEDEKIND_KUMMER_Q) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_SING; IN_SING; ARITH_EQ; RING_PRODUCT_SING] THEN
    ASM_SIMP_TAC[RING_POW_1];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
    REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
    SIMP_TAC[IDEAL_PRODUCT_SING; RING_IDEAL_IDEAL_POW; IDEAL_POW_1;
             RING_IDEAL_IDEAL_GENERATED]]);;

(* ------------------------------------------------------------------------- *)
(* The ring of integers and the hypothesis O = Z[a] + pO.                    *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_RING_OF_INTEGERS = prove
 (`!k:A ring x d w.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        w = (if (d == &1) (mod &4)
             then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2) else x)
        ==> w IN ring_carrier(ring_of_integers k) /\
            (!z. z IN ring_carrier(ring_of_integers k)
                 ==> ?a b. z = ring_add k (ring_of_int k a)
                                          (ring_mul k (ring_of_int k b) w)) /\
            (if (d == &1) (mod &4)
             then ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
             else w = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `r /\ p /\ q ==> p /\ q /\ r`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[ring_div] THEN
    FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                          STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_of_num k 2:A`] FIELD_MUL_RINV) THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_OF_NUM_EQ_0; DIVIDES_ZERO; ARITH_EQ] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_add k (ring_1 k) x:A`;
                   `ring_inv k (ring_of_num k 2):A`]
     (RING_RULE
       `!k:A ring y h.
           ring_mul k (ring_of_num k 2) h = ring_1 k
           ==> ring_mul k (ring_of_num k 2) (ring_mul k y h) = y`)) THEN
    ASM_SIMP_TAC[RING_ADD; RING_1; RING_INV; RING_OF_NUM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`] QUADRATIC_FIELD_INTEGRAL_BASIS) THEN
  ASM_REWRITE_TAC[free_basis; RING_OF_INTEGERS; INTEGER_RING; IN_UNIV] THEN
  SUBGOAL_THEN `{i:num | i < 2} = {0,1}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `i < 2 <=> i = 0 \/ i = 1`; FORALL_AND_THM;
              TAUT `(p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`;
              FORALL_UNWIND_THM2; ARITH_EQ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->int` SUBST1_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(c:num->int) 0`; `(c:num->int) 1`] THEN
  MP_TAC(ISPEC `k:A ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_mul (k:A ring) (ring_of_int k (c 0)) (ring_1 k) IN
    ring_carrier(ring_of_integers k) /\
    ring_mul k (ring_of_int k (c 1)) w IN ring_carrier(ring_of_integers k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IN_SUBRING_MUL THEN
    ASM_REWRITE_TAC[RING_OF_INT_IN_RING_OF_INTEGERS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[RING_SUM_CLAUSES; FINITE_SING; IN_SING; ARITH_EQ; RING_SUM_SING] THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  SIMP_TAC[RING_MUL_RID; RING_OF_INT]);;

let RING_OF_INTEGERS_SETADD_SUBRING_GENERATED = prove
 (`!k:A ring a j.
        a IN ring_carrier(ring_of_integers k) /\
        ring_ideal (ring_of_integers k) j /\
        (!z. z IN ring_carrier(ring_of_integers k)
             ==> ?u v. u IN ring_carrier(subring_generated k {a}) /\
                       v IN j /\ z = ring_add k u v)
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a})) j =
            ring_carrier(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC RING_SETADD THEN ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
    MATCH_MP_TAC SUBRING_GENERATED_MINIMAL THEN
    ASM_REWRITE_TAC[SING_SUBSET; RING_OF_INTEGERS_SUBRING];
    REWRITE_TAC[SUBSET; ring_setadd; IN_ELIM_THM; RING_OF_INTEGERS] THEN
    ASM_MESON_TAC[]]);;

let RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR = prove
 (`!k:A ring a j.
        a IN ring_carrier(ring_of_integers k) /\
        ring_ideal (ring_of_integers k) j /\
        (!z. z IN ring_carrier(ring_of_integers k)
             ==> ?m n. z = ring_add k (ring_of_int k m)
                                      (ring_mul k (ring_of_int k n) a))
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {a})) j =
            ring_carrier(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
   (ASSUME `(z:A) IN ring_carrier(ring_of_integers k)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int` (X_CHOOSE_THEN `n:int` SUBST1_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`ring_add k (ring_of_int k m) (ring_mul k (ring_of_int k n) a):A`;
    `ring_0 k:A`] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET]
     (ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_ADD_RZERO; RING_ADD; RING_MUL; RING_OF_INT] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `{a:A}`] SUBRING_SUBRING_GENERATED) THEN
    MP_TAC(ISPECL [`k:A ring`; `{a:A}`; `a:A`] SUBRING_GENERATED_INC_GEN) THEN
    ASM_REWRITE_TAC[IN_SING] THEN
    MESON_TAC[IN_SUBRING_ADD; IN_SUBRING_MUL; IN_SUBRING_INT];
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`]
      IN_RING_IDEAL_0) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS]]);;

let QUADRATIC_FIELD_SETADD_ODD = prove
 (`!k:A ring x d p.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ODD p
        ==> ring_setadd (ring_of_integers k)
              (ring_carrier(subring_generated k {x}))
              (ideal_generated (ring_of_integers k) {ring_of_num k p}) =
            ring_carrier(ring_of_integers k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`;
                `if ((d:int) == &1) (mod &4)
                 then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
                 else x:A`] QUADRATIC_FIELD_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `w = if ((d:int) == &1) (mod &4)
                  then ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
                  else x:A` THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` (CONJUNCT1 RING_OF_INTEGERS_SUBRING)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_carrier(subring_generated k {x:A}) subring_of k /\
    x IN ring_carrier(subring_generated k {x})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUBRING_SUBRING_GENERATED; SUBRING_GENERATED_INC_GEN;
                 IN_SING];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_cond o concl)) THEN
  ASM_CASES_TAC `((d:int) == &1) (mod &4)` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED]] THEN
  MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
  SUBGOAL_THEN `(x:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `x = ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k):A`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[RING_1; RING_RULE
       `ring_sub (r:A ring) (ring_add r (ring_1 r) x) (ring_1 r) = x`];
      ASM_SIMP_TAC[IN_SUBRING_SUB; IN_SUBRING_MUL; IN_SUBRING_NUM;
                   IN_SUBRING_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:A) IN ring_carrier k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET]
     (ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `ODD p` THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  X_GEN_TAC `z:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
   (ASSUME `(z:A) IN ring_carrier(ring_of_integers k)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int` SUBST1_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`ring_add k
      (ring_add k (ring_of_int k a)
                  (ring_mul k (ring_of_int k b) (ring_of_num k (m + 1))))
      (ring_mul k (ring_mul k (ring_of_int k b) (ring_of_num k (m + 1))) x):A`;
    `ring_mul k (ring_of_num k p)
       (ring_mul k (ring_neg k (ring_of_int k b)) w):A`]
  THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST[CONJ_TAC; MATCH_MP_TAC IN_SUBRING_ADD;
                 MATCH_MP_TAC IN_SUBRING_MUL]) THEN
    ASM_SIMP_TAC[IN_SUBRING_INT; IN_SUBRING_NUM];
    SIMP_TAC[IDEAL_GENERATED_SING; RING_OF_INTEGERS; RING_OF_NUM;
             GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    REWRITE_TAC[IN_ELIM_THM; ring_divides; RING_OF_INTEGERS;
                GSYM RING_OF_INT_OF_NUM; RING_OF_INT_IN_RING_OF_INTEGERS] THEN
    SUBGOAL_THEN
     `ring_mul k (ring_neg k (ring_of_int k b)) w IN
      ring_carrier(ring_of_integers (k:A ring))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_SUBRING_MUL; IN_SUBRING_NEG;
                   RING_OF_INT_IN_RING_OF_INTEGERS];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[IN_SUBRING_MUL; RING_OF_INT_IN_RING_OF_INTEGERS];
      EXISTS_TAC `ring_mul k (ring_neg k (ring_of_int k b)) w:A` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x = ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k) /\
    ring_of_num k p =
    ring_sub k (ring_mul k (ring_of_num k 2) (ring_of_num k (m + 1)))
               (ring_1 k):A`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_SIMP_TAC[RING_1; RING_RULE
     `ring_sub (r:A ring) (ring_add r (ring_1 r) x) (ring_1 r) = x`] THEN
    REWRITE_TAC[GSYM RING_OF_NUM_MUL; GSYM RING_OF_NUM_1] THEN
    SUBGOAL_THEN `2 * (m + 1) = p + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[RING_OF_NUM_ADD; RING_OF_NUM; RING_RULE
     `ring_sub (r:A ring) (ring_add r a b) b = a`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(RING_RULE
   `!k:A ring w a b h.
       ring_add k a (ring_mul k b w) =
       ring_add k (ring_add k (ring_add k a (ring_mul k b h))
          (ring_mul k (ring_mul k b h)
             (ring_sub k (ring_mul k (ring_of_num k 2) w) (ring_1 k))))
          (ring_mul k (ring_sub k (ring_mul k (ring_of_num k 2) h) (ring_1 k))
             (ring_mul k (ring_neg k b) w))`) THEN
  ASM_SIMP_TAC[RING_OF_INT; RING_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* The decomposition law.                                                    *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_RAMIFIED_PRIME = prove
 (`!k:A ring p P.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        prime p /\ prime_ideal (ring_of_integers k) P /\ ring_of_num k p IN P /\
        1 < ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) P
        ==> ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k) P 2`,
  let lemma = prove
   (`!e f. 1 < e /\ 1 <= f /\ e * f <= 2 ==> e = 2 /\ f = 1`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `f = 1` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES] THENL [ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(SPECL [`2`; `e:num`; `2`; `f:num`] LE_MULT2) THEN
    ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `p:num`] NUMBER_FIELD_PRIME_FACTORIZATION_Q) THEN
  MP_TAC(SPECL [`k:A ring`; `p:num`] NUMBER_FIELD_FUNDAMENTAL_IDENTITY_Q) THEN
  MP_TAC(SPECL [`k:A ring`; `p:num`] NUMBER_FIELD_PRIME_IDEALS_ABOVE_Q) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = {P | prime_ideal (ring_of_integers k) P /\
                       ring_of_num k p IN (P:A->bool)}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!Q. Q IN S
        ==> 1 <= ramification_index (integer_ring,ring_of_integers k)
                   (ring_of_int k) Q /\
            1 <= residue_degree (integer_ring,ring_of_integers k)
                   (ring_of_int k) Q /\
            ramification_index (integer_ring,ring_of_integers k)
              (ring_of_int k) Q *
            residue_degree (integer_ring,ring_of_integers k)
              (ring_of_int k) (Q:A->bool) <= 2`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`k:A ring`; `Q:A->bool`; `p:num`]
      NUMBER_FIELD_RAMIFICATION_RESIDUE_BOUNDS_Q) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:A->bool) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ramification_index (integer_ring,ring_of_integers k)
      (ring_of_int k) (P:A->bool) = 2 /\
    residue_degree (integer_ring,ring_of_integers k) (ring_of_int k) P = 1`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC lemma THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `S = {P:A->bool}` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(a:A->bool) IN s /\ s DELETE a = {} ==> s = {a}`) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`\Q. ramification_index (integer_ring,ring_of_integers k)
             (ring_of_int k) Q *
           residue_degree (integer_ring,ring_of_integers k)
             (ring_of_int k) (Q:A->bool)`;
      `S:(A->bool)->bool`; `P:A->bool`] NSUM_DELETE) THEN
    ASM_SIMP_TAC[ARITH_RULE `2 * 1 + n = 2 <=> n = 0`; NSUM_EQ_0_IFF;
                 FINITE_DELETE] THEN
    REWRITE_TAC[EXTENSION; IN_DELETE; NOT_IN_EMPTY; MULT_EQ_0] THEN
    DISCH_TAC THEN X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:A->bool` o check (is_forall o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Q:A->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[IDEAL_PRODUCT_SING; RING_IDEAL_IDEAL_POW] THEN
  ASM_REWRITE_TAC[]);;

let QUADRATIC_FIELD_RAMIFIED = prove
 (`!k:A ring x d p.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ prime p
        ==> ((?P. prime_ideal (ring_of_integers k) P /\
                  ideal_generated (ring_of_integers k) {ring_of_num k p} =
                  ideal_pow (ring_of_integers k) P 2) <=>
             &p divides number_field_discriminant k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `p:num`] NUMBER_FIELD_RAMIFIED_DISCRIMINANT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `P:A->bool` THEN
  ASM_SIMP_TAC[QUADRATIC_FIELD_RAMIFIED_PRIME] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  SUBGOAL_THEN
   `ring_of_num k p IN
    ideal_generated (ring_of_integers k) {ring_of_num k p:A} /\
    ~(ring_of_num k p = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
      REWRITE_TAC[IN_SING; RING_OF_INTEGERS; GSYM RING_OF_INT_OF_NUM;
                  RING_OF_INT_IN_RING_OF_INTEGERS];
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [number_field]) THEN
      SIMP_TAC[RING_OF_NUM_EQ_0; DIVIDES_ZERO] THEN
      ASM_MESON_TAC[PRIME_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_of_num k p IN (P:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `ring_of_num k p IN
      ideal_generated (ring_of_integers k) {ring_of_num k p:A}` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `P:A->bool`;
                   `2`] IDEAL_POW_SUBSET_PRIME_IDEAL) THEN
    ASM_SIMP_TAC[PRIME_IDEAL_IMP_SUBSET; ARITH_EQ; SUBSET_REFL] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`; `p:num`]
    RAMIFICATION_INDEX_PRIME) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(P = {ring_0 k:A})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ring_of_num k p IN (P:A->bool)` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IDEAL_VALUATION_IDEAL_POW; IDEAL_VALUATION_PRIME;
               PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS] THEN
  ARITH_TAC);;

let QUADRATIC_FIELD_ODD_PRIME = prove
 (`!k:A ring x d p.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        prime p /\ ~(p = 2) /\ ~(&p divides d)
        ==> ((?P Q. prime_ideal (ring_of_integers k) P /\
                    prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
                    ideal_generated (ring_of_integers k) {ring_of_num k p} =
                    ideal_prod (ring_of_integers k) P Q) <=>
             ?y. (y pow 2 == d) (mod &p)) /\
            (prime_ideal (ring_of_integers k)
               (ideal_generated (ring_of_integers k) {ring_of_num k p}) <=>
             ~(?y. (y pow 2 == d) (mod &p)))`,
  let i3a = INTEGER_RULE
   `!p y a:int. coprime(p,a) /\ p divides (a * y) ==> p divides y`
  and i3b = INTEGER_RULE
   `!p y d:int. p divides y /\ (y * y == d) (mod p) ==> p divides d`
  and i6 = INTEGER_RULE
   `!p y d:int. (y pow 2 == d) (mod p) ==> (y * --y == --d) (mod p)`
  and i7 = INTEGER_RULE `!p y:int. (y + --y == &0) (mod p)` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`; `p:num`]
    QUADRATIC_FIELD_SETADD_ODD) THEN
  MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `~((?P Q. prime_ideal (ring_of_integers k) P /\
             prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
             ideal_generated (ring_of_integers k) {ring_of_num k p} =
             ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
      prime_ideal (ring_of_integers k)
        (ideal_generated (ring_of_integers k) {ring_of_num k p:A}))`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`k:A ring`; `p:num`; `P:A->bool`; `Q:A->bool`]
      NUMBER_FIELD_PRIME_IDEAL_PROD_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((?y. ((y:int) pow 2 == d) (mod &p)) ==>
     ?P Q. prime_ideal (ring_of_integers k) P /\
           prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
           ideal_generated (ring_of_integers k) {ring_of_num k p} =
           ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
    (~(?y. ((y:int) pow 2 == d) (mod &p)) ==>
     prime_ideal (ring_of_integers k)
       (ideal_generated (ring_of_integers k) {ring_of_num k p:A}))`
  MP_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_TAC `y:int`) THEN
      MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_SPLIT THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `&0:int`; `d:int`; `y:int`; `--y:int`] THEN
      ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO; RING_ADD_LZERO; RING_OF_INT;
                   i6; i7] THEN
      DISCH_TAC THEN UNDISCH_TAC `~(&p divides (d:int))` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC i3b THEN EXISTS_TAC `y:int` THEN
      ASM_REWRITE_TAC[GSYM INT_POW_2] THEN MATCH_MP_TAC i3a THEN
      EXISTS_TAC `&2:int` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM num_coprime] THEN
        MP_TAC(SPECL [`p:num`; `2`] COPRIME_PRIME_PRIME) THEN
        ASM_REWRITE_TAC[PRIME_2];
        UNDISCH_TAC `((y:int) == --y) (mod &p)` THEN
        REWRITE_TAC[INTEGER_RULE
         `!x y n:int. (x == y) (mod n) <=> n divides (x - y)`] THEN
        REWRITE_TAC[INT_ARITH `y - --y:int = &2 * y`]];
      MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_INERT THEN
      MAP_EVERY EXISTS_TAC [`x:A`; `&0:int`; `d:int`] THEN
      ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO; RING_ADD_LZERO; RING_OF_INT;
                   INT_MUL_LZERO; INT_ADD_LID] THEN
      ASM_REWRITE_TAC[GSYM NOT_EXISTS_THM]];
    POP_ASSUM MP_TAC THEN CONV_TAC TAUT]);;

let QUADRATIC_FIELD_PRIME_TWO = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ (d == &1) (mod &4)
        ==> ((?P Q. prime_ideal (ring_of_integers k) P /\
                    prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
                    ideal_generated (ring_of_integers k) {ring_of_num k 2} =
                    ideal_prod (ring_of_integers k) P Q) <=>
             (d == &1) (mod &8)) /\
            (prime_ideal (ring_of_integers k)
               (ideal_generated (ring_of_integers k) {ring_of_num k 2}) <=>
             (d == &5) (mod &8))`,
  let i1 = prove
   (`!t:int. (&1 + &4 * t == &1) (mod &8) <=> &2 divides t`,
    GEN_TAC THEN MP_TAC(SPECL [`&1:int`; `&4:int`; `&2:int`; `t:int`]
     (INTEGER_RULE `!a m n t:int. ~(m = &0)
        ==> ((a + m * t == a) (mod (m * n)) <=> n divides t)`)) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[])
  and i2 = prove
   (`!t:int. (&1 + &4 * t == &5) (mod &8) <=> (t == &1) (mod &2)`,
    GEN_TAC THEN MP_TAC(SPECL [`&1:int`; `&4:int`; `&2:int`; `t:int`]
     (INTEGER_RULE `!a m n t:int. ~(m = &0)
        ==> ((a + m * t == a + m) (mod (m * n)) <=> (t == &1) (mod n))`)) THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[])
  and i4 = INTEGER_RULE
   `!n y2 y t:int. n divides (y2 - y) /\ (t == &1) (mod n) /\
                   (y2 == &1 * y + t) (mod n) ==> n divides &1`
  and i5 = INTEGER_RULE `!n t:int. n divides t ==> (&0 * &1 == --t) (mod n)`
  and par = prove
   (`!y:int. &2 divides (y pow 2 - y)`,
    GEN_TAC THEN MP_TAC(SPECL [`y:int`; `&2:int`] INT_DIVISION) THEN
    REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN
    SPEC_TAC(`y rem &2`,`r:int`) THEN SPEC_TAC(`y div &2`,`q:int`) THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `r:int = &0 \/ r = &1` (DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_INT_ARITH_TAC;
      REWRITE_TAC[int_divides] THEN EXISTS_TAC `&2 * q pow 2 - q:int` THEN
      INT_ARITH_TAC;
      REWRITE_TAC[int_divides] THEN EXISTS_TAC `&2 * q pow 2 + q:int` THEN
      INT_ARITH_TAC])
  and evodd = prove
   (`!t:int. &2 divides t <=> ~((t == &1) (mod &2))`,
    GEN_TAC THEN REWRITE_TAC[GSYM INT_REM_EQ_0; GSYM INT_REM_EQ] THEN
    MP_TAC(SPECL [`t:int`; `&2:int`] INT_DIVISION) THEN
    REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN
    CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2):A` THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`; `w:A`]
    QUADRATIC_FIELD_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(MATCH_MP NUMBER_FIELD_IMP_FIELD th) THEN
                        STRIP_ASSUME_TAC(REWRITE_RULE[number_field] th)) THEN
  SUBGOAL_THEN `(w:A) IN ring_carrier k` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET]
     (ISPEC `k:A ring` RING_OF_INTEGERS_SUBSET)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(REWRITE_RULE[int_congruent] (ASSUME `((d:int) == &1) (mod &4)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:int` (SUBST_ALL_TAC o MATCH_MP
   (INT_ARITH `(d:int) - &1 = &4 * t ==> d = &1 + &4 * t`))) THEN
  REWRITE_TAC[i1; i2] THEN
  SUBGOAL_THEN
   `ring_pow k w 2 =
    ring_add k (ring_mul k (ring_of_int k (&1)) w) (ring_of_int k t):A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 4:A`] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN; RING_OF_NUM; RING_OF_NUM_EQ_0;
                 DIVIDES_ZERO; ARITH_EQ; RING_ADD; RING_POW; RING_MUL;
                 RING_OF_INT] THEN
    UNDISCH_TAC `ring_pow k x 2 = ring_of_int k (&1 + &4 * t):A` THEN
    REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN
    MP_TAC(ISPECL [`k:A ring`; `w:A`; `x:A`; `ring_of_int k t:A`]
     (RING_RULE
       `!k:A ring w x T.
           ring_mul k (ring_of_num k 2) w = ring_add k (ring_1 k) x
           ==> ring_pow k x 2 =
               ring_add k (ring_of_num k 1) (ring_mul k (ring_of_num k 4) T)
           ==> ring_mul k (ring_of_num k 4) (ring_pow k w 2) =
               ring_mul k (ring_of_num k 4)
                 (ring_add k (ring_mul k (ring_of_num k 1) w) T)`)) THEN
    ASM_SIMP_TAC[RING_OF_INT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_setadd (ring_of_integers k) (ring_carrier(subring_generated k {w}))
      (ideal_generated (ring_of_integers k) {ring_of_num k 2}) =
    ring_carrier(ring_of_integers k:A ring)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~((?P Q. prime_ideal (ring_of_integers k) P /\
             prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
             ideal_generated (ring_of_integers k) {ring_of_num k 2} =
             ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
      prime_ideal (ring_of_integers k)
        (ideal_generated (ring_of_integers k) {ring_of_num k 2:A}))`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(SPECL [`k:A ring`; `2`; `P:A->bool`; `Q:A->bool`]
      NUMBER_FIELD_PRIME_IDEAL_PROD_EQ) THEN
    ASM_REWRITE_TAC[PRIME_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 divides (t:int)
     ==> ?P Q. prime_ideal (ring_of_integers k) P /\
               prime_ideal (ring_of_integers k) Q /\ ~(P = Q) /\
               ideal_generated (ring_of_integers k) {ring_of_num k 2} =
               ideal_prod (ring_of_integers k) P (Q:A->bool)) /\
    (((t:int) == &1) (mod &2)
     ==> prime_ideal (ring_of_integers k)
           (ideal_generated (ring_of_integers k) {ring_of_num k 2:A}))`
  MP_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_SPLIT THEN
      MAP_EVERY EXISTS_TAC [`w:A`; `&1:int`; `t:int`; `&0:int`; `&1:int`] THEN
      ASM_SIMP_TAC[PRIME_2; i5] THEN
      REWRITE_TAC[GSYM INT_REM_EQ] THEN CONV_TAC INT_REDUCE_CONV;
      MATCH_MP_TAC QUADRATIC_DEDEKIND_KUMMER_INERT THEN
      MAP_EVERY EXISTS_TAC [`w:A`; `&1:int`; `t:int`] THEN
      ASM_REWRITE_TAC[PRIME_2] THEN
      X_GEN_TAC `y:int` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`&2:int`; `(y:int) pow 2`; `y:int`; `t:int`] i4) THEN
      ASM_REWRITE_TAC[par; GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV];
    MP_TAC(SPEC `t:int` evodd) THEN POP_ASSUM MP_TAC THEN CONV_TAC TAUT]);;

(* ------------------------------------------------------------------------- *)
(* The prime ideals of the decomposition law.                                *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_SPLIT_ODD_PRIME = prove
 (`!k:A ring x d p y.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        prime p /\ ~(p = 2) /\ ~(&p divides d) /\ (y pow 2 == d) (mod &p)
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_sub k x (ring_of_int k y)}) /\
            prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_add k x (ring_of_int k y)}) /\
            ~(ideal_generated (ring_of_integers k)
                {ring_of_num k p, ring_sub k x (ring_of_int k y)} =
              ideal_generated (ring_of_integers k)
                {ring_of_num k p, ring_add k x (ring_of_int k y)}) /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_prod (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_sub k x (ring_of_int k y)})
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_add k x (ring_of_int k y)}) /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_sub k x (ring_of_int k y)}) = p /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k p, ring_add k x (ring_of_int k y)}) = p`,
  let i3a = INTEGER_RULE
   `!p y a:int. coprime(p,a) /\ p divides (a * y) ==> p divides y`
  and i3b = INTEGER_RULE
   `!p y d:int. p divides y /\ (y * y == d) (mod p) ==> p divides d`
  and i6 = INTEGER_RULE
   `!p y d:int. (y pow 2 == d) (mod p) ==> (y * --y == --d) (mod p)`
  and i7 = INTEGER_RULE `!p y:int. (y + --y == &0) (mod p)` in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`; `p:num`]
    QUADRATIC_FIELD_SETADD_ODD) THEN
  MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_sub k x (ring_of_int k (--y)) = ring_add k x (ring_of_int k y):A`
  (fun th -> SUBST1_TAC(SYM th)) THENL
   [REWRITE_TAC[RING_OF_INT_NEG] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `ring_of_int k y:A`] (RING_RULE
     `!r x y:A. x IN ring_carrier r /\ y IN ring_carrier r
                ==> ring_sub r x (ring_neg r y) = ring_add r x y`)) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `p:num`; `&0:int`; `d:int`; `y:int`;
                 `--y:int`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k p, ring_sub k x (ring_of_int k y):A}`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k p, ring_sub k x (ring_of_int k (--y)):A}`]
    QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO; RING_ADD_LZERO; RING_OF_INT;
                 i6; i7] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(&p divides (d:int))` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC i3b THEN EXISTS_TAC `y:int` THEN
    ASM_REWRITE_TAC[GSYM INT_POW_2] THEN MATCH_MP_TAC i3a THEN
    EXISTS_TAC `&2:int` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM num_coprime] THEN
      MP_TAC(SPECL [`p:num`; `2`] COPRIME_PRIME_PRIME) THEN
      ASM_REWRITE_TAC[PRIME_2];
      UNDISCH_TAC `((y:int) == --y) (mod &p)` THEN
      REWRITE_TAC[INTEGER_RULE
       `!x y n:int. (x == y) (mod n) <=> n divides (x - y)`] THEN
      REWRITE_TAC[INT_ARITH `y - --y:int = &2 * y`]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. ring_of_num k p IN
        ideal_generated (ring_of_integers k) {ring_of_num k p, z:A}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
    REWRITE_TAC[IN_INSERT] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:num`] RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`;
                   `ideal_generated (ring_of_integers k)
                      {ring_of_num k p, ring_sub k x (ring_of_int k y):A}`;
                   `p:num`] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q);
    MP_TAC(ISPECL [`k:A ring`;
                   `ideal_generated (ring_of_integers k)
                      {ring_of_num k p,
                       ring_sub k x (ring_of_int k (--y)):A}`;
                   `p:num`] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q)] THEN
  ASM_REWRITE_TAC[EXP_1]);;

let QUADRATIC_FIELD_RAMIFIED_ODD_PRIME = prove
 (`!k:A ring x d p.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\
        prime p /\ ~(p = 2) /\ &p divides d
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, x}) /\
            ideal_generated (ring_of_integers k) {ring_of_num k p} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, x}) 2 /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k p, x}) = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:A ring`; `x:A`; `d:int`; `p:num`]
    QUADRATIC_FIELD_SETADD_ODD) THEN
  MP_TAC(SPEC `p:num` PRIME_ODD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `ring_sub k x (ring_of_int k (&0)) = x:A`
  (fun th -> SUBST1_TAC(SYM th)) THENL
   [ASM_SIMP_TAC[RING_OF_INT_0; RING_SUB_RZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `p:num`; `&0:int`; `d:int`; `&0:int`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k p, ring_sub k x (ring_of_int k (&0)):A}`]
    QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO; RING_ADD_LZERO; RING_OF_INT;
                 INT_ADD_LID; INT_MUL_LZERO] THEN
    UNDISCH_TAC `&p divides (d:int)` THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k p, ring_sub k x (ring_of_int k (&0)):A}`;
                 `p:num`] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN
  ASM_REWRITE_TAC[EXP_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
  REWRITE_TAC[IN_INSERT] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `p:num`] RING_OF_NUM) THEN
  REWRITE_TAC[RING_OF_INTEGERS]);;

let QUADRATIC_FIELD_RAMIFIED_TWO = prove
 (`!k:A ring x d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ~((d == &1) (mod &4))
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k 2,
                  if &2 divides d then x else ring_add k (ring_1 k) x}) /\
            ideal_generated (ring_of_integers k) {ring_of_num k 2} =
            ideal_pow (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k 2,
                  if &2 divides d then x else ring_add k (ring_1 k) x}) 2 /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k 2,
                  if &2 divides d then x else ring_add k (ring_1 k) x}) = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `x:A`]
    QUADRATIC_FIELD_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`;
                 `ideal_generated (ring_of_integers k) {ring_of_num k 2:A}`]
    RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN DISCH_TAC THEN
  ABBREV_TAC `u:int = if &2 divides d then &0 else --(&1)` THEN
  SUBGOAL_THEN
   `(if &2 divides d then x else ring_add k (ring_1 k) x) =
    ring_sub k x (ring_of_int k u:A)`
  SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[RING_OF_INT_0; RING_SUB_RZERO; RING_OF_INT_NEG;
                 RING_OF_INT_1] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`] (RING_RULE
     `!r x:A. x IN ring_carrier r
              ==> ring_add r (ring_1 r) x =
                  ring_sub r x (ring_neg r (ring_1 r))`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `2`; `&0:int`; `d:int`; `u:int`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k 2, ring_sub k x (ring_of_int k u):A}`]
    QUADRATIC_DEDEKIND_KUMMER_RAMIFIED_PRIME) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INT_0; RING_MUL_LZERO; RING_ADD_LZERO; RING_OF_INT;
                 PRIME_2] THEN
    EXPAND_TAC "u" THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `!d n:int. n divides d
                  ==> (&0 + &0 == &0) (mod n) /\ (&0 * &0 == --d) (mod n)`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[INTEGER_RULE
     `!x y n:int. (x == y) (mod n) <=> n divides (x - y)`; int_divides] THEN
    MP_TAC(SPECL [`d:int`; `&2:int`] INT_DIVISION) THEN
    UNDISCH_TAC `~(&2 divides (d:int))` THEN
    REWRITE_TAC[GSYM INT_REM_EQ_0] THEN CONV_TAC INT_REDUCE_CONV THEN
    REPEAT STRIP_TAC THENL
     [EXISTS_TAC `--(&1):int` THEN INT_ARITH_TAC;
      EXISTS_TAC `d div &2 + &1:int` THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k 2, ring_sub k x (ring_of_int k u):A}`;
                 `2`] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q) THEN
  ASM_REWRITE_TAC[EXP_1; PRIME_2] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
  REWRITE_TAC[IN_INSERT] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `2`] RING_OF_NUM) THEN
  REWRITE_TAC[RING_OF_INTEGERS]);;

let QUADRATIC_FIELD_SPLIT_TWO = prove
 (`!k:A ring x d w.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ (d == &1) (mod &8) /\
        w = ring_div k (ring_add k (ring_1 k) x) (ring_of_num k 2)
        ==> prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k 2, w}) /\
            prime_ideal (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k 2, ring_sub k (ring_1 k) w}) /\
            ~(ideal_generated (ring_of_integers k) {ring_of_num k 2, w} =
              ideal_generated (ring_of_integers k)
                {ring_of_num k 2, ring_sub k (ring_1 k) w}) /\
            ideal_generated (ring_of_integers k) {ring_of_num k 2} =
            ideal_prod (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k 2, w})
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k 2, ring_sub k (ring_1 k) w}) /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k) {ring_of_num k 2, w}) = 2 /\
            ideal_norm (ring_of_integers k)
              (ideal_generated (ring_of_integers k)
                 {ring_of_num k 2, ring_sub k (ring_1 k) w}) = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhand(concl th) = `w:A`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN `((d:int) == &1) (mod &4)` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:int == &1) (mod &8)` THEN
    REWRITE_TAC[INTEGER_RULE
     `!x y n:int. (x == y) (mod n) <=> n divides (x - y)`; int_divides] THEN
    STRIP_TAC THEN EXISTS_TAC `&2 * x':int` THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `w:A`]
    QUADRATIC_FIELD_RING_OF_INTEGERS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`;
                 `ideal_generated (ring_of_integers k) {ring_of_num k 2:A}`]
    RING_OF_INTEGERS_SETADD_SUBRING_GENERATED_LINEAR) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `c = (d - &1) div &4:int` THEN
  SUBGOAL_THEN `&4 * c:int = d - &1 /\ &2 divides c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(d:int == &1) (mod &8)` THEN
    REWRITE_TAC[INTEGER_RULE
     `!x y n:int. (x == y) (mod n) <=> n divides (x - y)`; int_divides] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:int`) THEN
    SUBGOAL_THEN `c:int = &2 * q` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "c" THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        lhand(concl th) = `d - &1:int`)) THEN
      REWRITE_TAC[INT_ARITH `&8 * q:int = (&2 * q) * &4`] THEN
      MATCH_MP_TAC(CONJUNCT1 INT_DIV_MUL) THEN CONV_TAC INT_REDUCE_CONV;
      CONJ_TAC THENL [ASM_INT_ARITH_TAC; EXISTS_TAC `q:int` THEN REFL_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_pow k w 2 =
    ring_add k (ring_mul k (ring_of_int k (&1)) w) (ring_of_int k c):A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:A ring`; `ring_of_num k 4:A`] THEN
    ASM_SIMP_TAC[RING_OF_NUM; RING_ADD; RING_MUL; RING_POW; RING_OF_INT;
                 NUMBER_FIELD_RING_OF_NUM_EQ_0; ARITH_EQ] THEN
    SUBGOAL_THEN `ring_mul k (ring_of_num k 4) (ring_of_int k c) =
                  ring_sub k (ring_of_int k d) (ring_1 k):A`
    MP_TAC THENL
     [REWRITE_TAC[GSYM RING_OF_INT_OF_NUM; GSYM RING_OF_INT_MUL;
                  GSYM RING_OF_INT_1; GSYM RING_OF_INT_SUB] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[RING_OF_INT_1] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `w:A`; `ring_of_int k c:A`;
                   `ring_of_int k d:A`] (RING_RULE
     `!r x w u e:A. x IN ring_carrier r /\ w IN ring_carrier r /\
                    u IN ring_carrier r /\ e IN ring_carrier r /\
                    ring_mul r (ring_of_num r 2) w = ring_add r (ring_1 r) x /\
                    ring_pow r x 2 = e /\
                    ring_mul r (ring_of_num r 4) u = ring_sub r e (ring_1 r)
                    ==> ring_mul r (ring_of_num r 4) (ring_pow r w 2) =
                        ring_mul r (ring_of_num r 4)
                          (ring_add r (ring_mul r (ring_1 r) w) u)`)) THEN
    ASM_REWRITE_TAC[RING_OF_INT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `w:A`; `2`; `&1:int`; `c:int`; `&0:int`;
                 `&1:int`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k 2, ring_sub k w (ring_of_int k (&0)):A}`;
                 `ideal_generated (ring_of_integers k)
                    {ring_of_num k 2, ring_sub k w (ring_of_int k (&1)):A}`]
    QUADRATIC_DEDEKIND_KUMMER_SPLIT_PRIMES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PRIME_2] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INTEGER_RULE
       `!x y n:int. (x == y) (mod n) <=> n divides (y - x)`] THEN
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_DIVIDES_ONE] THEN
      CONV_TAC INT_REDUCE_CONV;
      CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[INT_CONG_REFL];
      MATCH_MP_TAC(INTEGER_RULE
       `!c n:int. n divides c ==> (&0 * &1 == --c) (mod n)`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub k w (ring_of_int k (&0)) = w /\
    ideal_generated (ring_of_integers k)
      {ring_of_num k 2, ring_sub k w (ring_of_int k (&1))} =
    ideal_generated (ring_of_integers k)
      {ring_of_num k 2, ring_sub k (ring_1 k) w:A}`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[RING_OF_INT_0; RING_SUB_RZERO; RING_OF_INT_1] THEN
    MATCH_MP_TAC IDEAL_GENERATED_PAIR_EQ THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `2`] RING_OF_NUM) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `w:A`; `ring_1 k:A`]
      RING_SUB) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_1 k:A`; `w:A`]
      RING_SUB) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_1) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_SIMP_TAC[] THEN
    REPEAT DISCH_TAC THEN X_GEN_TAC `j:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `w:A`] (RING_RULE
     `!r w:A. w IN ring_carrier r
              ==> ring_sub r (ring_1 r) w =
                  ring_neg r (ring_sub r w (ring_1 r)) /\
                  ring_sub r w (ring_1 r) =
                  ring_neg r (ring_sub r (ring_1 r) w)`))
    THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(REWRITE_RULE[RING_OF_INTEGERS] (ISPECL
     [`ring_of_integers k:A ring`; `j:A->bool`] IN_RING_IDEAL_NEG)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!z. ring_of_num k 2 IN
        ideal_generated (ring_of_integers k) {ring_of_num k 2, z:A}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
    REWRITE_TAC[IN_INSERT] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `2`] RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`;
                   `ideal_generated (ring_of_integers k)
                      {ring_of_num k 2, w:A}`;
                   `2`] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q);
    MP_TAC(ISPECL [`k:A ring`;
                   `ideal_generated (ring_of_integers k)
                      {ring_of_num k 2, ring_sub k (ring_1 k) w:A}`;
                   `2`] RING_OF_INTEGERS_IDEAL_NORM_PRIME_Q)] THEN
  ASM_REWRITE_TAC[EXP_1; PRIME_2]);;
