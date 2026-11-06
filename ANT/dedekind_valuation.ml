(* ========================================================================= *)
(* Discrete valuations of the fraction field k of a Dedekind domain r, along *)
(* an injective ring homomorphism h : r -> k, at the nonzero primes P of r.  *)
(*                                                                           *)
(*   dedekind_valuation (r,k) h P x = v_P(x), an integer: for h(b) x = h(a)  *)
(*                                    with a, b nonzero in r,                *)
(*                                    v_P((a)) - v_P((b))                    *)
(*                                                                           *)
(* (v_P of an ideal is ideal_valuation of ANT/dedekind.ml; the value at zero *)
(* is unspecified.) Number fields are the case r = ring_of_integers k, h = I *)
(* (ANT/nf_valuation.ml). Most results assume dedekind_domain r and         *)
(* field_of_fractions (r,k) h of Library/ringtheory.ml: k is a field, h a    *)
(* monomorphism and every x IN k satisfies h(b) x = h(a) with a, b in r and  *)
(* b nonzero.                                                                *)
(*                                                                           *)
(* Main results: the value on any representation (DEDEKIND_VALUATION) and on *)
(* the image of r (DEDEKIND_VALUATION_IMAGE); v_P is a homomorphism from the *)
(* nonzero elements to the integers (_1, _MUL, _INV, _DIV, _POW, _NEG),      *)
(* ultrametric (_ADD, _ADD_STRICT), with finite support (_FINITE); x is in   *)
(* the image of r iff all v_P(x) >= 0 (_INTEGRAL), the image of a unit iff   *)
(* all v_P(x) = 0 (_UNIT), h(a) has v_P(h(a)) > 0 iff a IN P (_PRIME_IDEAL); *)
(* x, y have the same valuations iff x = h(u) y with u a unit (_EQ).         *)
(* Prescribed valuations: the nonzero ideals realize all of them             *)
(* (DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS), the nonzero x all of them at      *)
(* finitely many primes (DEDEKIND_VALUATION_WEAK_APPROXIMATION).             *)
(* Denominators: a nonzero x has a denominator ideal J with v_P(J) = max 0   *)
(* (-v_P(x)) (DEDEKIND_DENOMINATOR_IDEAL), and h(c) x is in the image of r   *)
(* for every c in an ideal J with v_P(J) + v_P(x) >= 0                       *)
(* (DEDEKIND_IDEAL_MUL_INTEGRAL). The local case: the valuation ring {x | x  *)
(* = 0 \/ v_P(x) >= 0} consists of the h(a) / h(b) with b NOTIN P            *)
(* (DEDEKIND_VALUATION_POS) and is the image of the localization r_P under   *)
(* the monomorphism extending h (DEDEKIND_VALUATION_RING_LOCALIZATION),      *)
(* hence a DVR (DEDEKIND_VALUATION_RING_DVR), and v_P is the valuation of    *)
(* r_P at its maximal ideal (DEDEKIND_VALUATION_LOCALIZATION); for a DVR r   *)
(* with maximal ideal m, the image of r is the valuation ring of v_m and the *)
(* images of the units are the elements of value 0 (DVR_DEDEKIND_VALUATION). *)
(* For e(Q|P) in extensions see DEDEKIND_VALUATION_RAMIFICATION_INDEX of     *)
(* ANT/relative_split.ml. Approximation with prescribed valuations at        *)
(* finitely many nonzero primes and nonnegative valuations at all the others *)
(* (DEDEKIND_VALUATION_APPROXIMATION, Alaca-Williams 8.4.5; it strengthens   *)
(* DEDEKIND_VALUATION_WEAK_APPROXIMATION).                                   *)
(*                                                                           *)
(* Routes: well defined because two representations h(b) x = h(a) and h(d) x *)
(* = h(c) give a d = c b in r, h being injective, hence v((a)) + v((d)) =    *)
(* v((c)) + v((b)) (IDEAL_VALUATION_PRINCIPAL_MUL of ANT/dedekind.ml);       *)
(* integrality by DEDEKIND_IDEAL_SUBSET_VALUATION ((a) SUBSET (b) iff b      *)
(* divides a); the ultrametric inequality with a common denominator and      *)
(* IDEAL_VALUATION_PRINCIPAL_ADD; approximation by                           *)
(* DEDEKIND_WEAK_APPROXIMATION of ANT/dedekind_struct.ml; the valuation ring *)
(* through the denominator ideal of x, not inside P when x has a nonnegative *)
(* valuation at P; the localization by RING_LOCALIZATION_UNIVERSAL,          *)
(* IDEAL_GENERATED_RING_LOCALIZATION and IDEAL_VALUATION_LOCALIZATION of     *)
(* ANT/dedekind_local.ml.                                                    *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (field_of_fractions, monomials,               *)
(* localization), ANT/ideal_arith.ml, ANT/dedekind.ml,                       *)
(* ANT/dedekind_struct.ml (DVR, DEDEKIND_WEAK_APPROXIMATION) and             *)
(* ANT/dedekind_local.ml (DEDEKIND_LOCALIZATION, DVR_LOCALIZATION,           *)
(* IDEAL_VALUATION_LOCALIZATION).                                            *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/dedekind_struct.ml";;
needs "ANT/dedekind_local.ml";;

let dedekind_valuation = new_definition
 `dedekind_valuation (r:A ring,k:B ring) (h:A->B) (P:A->bool) (x:B) =
  @v:int. !a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                ~(a = ring_0 r) /\ ~(b = ring_0 r) /\ ring_mul k (h b) x = h a
                ==> v = &(ideal_valuation r P (ideal_generated r {a})) -
                        &(ideal_valuation r P (ideal_generated r {b}))`;;

(* ------------------------------------------------------------------------- *)
(* Values and the homomorphism property.                                     *)
(* ------------------------------------------------------------------------- *)

(* Well defined: two representations h(b) x = h(a) and h(d) x = h(c) give    *)
(* h(a d) = h(c b), so a d = c b in r and v((a)) + v((d)) = v((c)) + v((b)). *)

let DEDEKIND_VALUATION = prove
 (`!r k (h:A->B) P x a b.
        dedekind_domain r /\ ring_monomorphism(r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ x IN ring_carrier k /\
        a IN ring_carrier r /\ b IN ring_carrier r /\
        ~(a = ring_0 r) /\ ~(b = ring_0 r) /\ ring_mul k (h b) x = h a
        ==> dedekind_valuation (r,k) h P x =
            &(ideal_valuation r P (ideal_generated r {a})) -
            &(ideal_valuation r P (ideal_generated r {b}))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dedekind_valuation] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `v:int` THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`a:A`; `b:A`]) THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN STRIP_TAC THEN
  REWRITE_TAC[INT_ARITH `(a:int) - b = c - d <=> a + d = c + b`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `ring_mul r (a:A) d = ring_mul r c b` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                   `ring_mul r (a:A) d`; `ring_mul r (c:A) b`]
      RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_SIMP_TAC[RING_MUL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
    SUBGOAL_THEN
     `(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
      h c IN ring_carrier k /\ h d IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; RING_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `a:A`; `d:A`]
    IDEAL_VALUATION_PRINCIPAL_MUL) THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `c:A`; `b:A`]
    IDEAL_VALUATION_PRINCIPAL_MUL) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let DEDEKIND_VALUATION_IMAGE = prove
 (`!r k (h:A->B) P a.
        dedekind_domain r /\ ring_monomorphism(r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> dedekind_valuation (r,k) h P (h a) =
            &(ideal_valuation r P (ideal_generated r {a}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `(h:A->B) a IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `(h:A->B) a`;
                 `a:A`; `ring_1 r:A`] DEDEKIND_VALUATION) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
  ASM_SIMP_TAC[RING_1; RING_MUL_LID] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[DEDEKIND_IMP_INTEGRAL_DOMAIN; integral_domain];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ring_1 r:A`] IDEAL_GENERATED_SING_EQ_CARRIER) THEN
  REWRITE_TAC[RING_1; RING_UNIT_1] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`] IDEAL_VALUATION_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_SUB_RZERO]]);;

(* Only a monomorphism into a field is needed: every representation of 1 is  *)
(* h(b) 1 = h(b).                                                            *)

let DEDEKIND_VALUATION_1 = prove
 (`!r k (h:A->B) P.
        field k /\ ring_monomorphism(r,k) h
        ==> dedekind_valuation (r,k) h P (ring_1 k) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  REWRITE_TAC[dedekind_valuation] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `v:int` THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL [`ring_1 r:A`; `ring_1 r:A`]) THEN
    REWRITE_TAC[INT_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_1; RING_MUL_LID] THEN
    ASM_MESON_TAC[FIELD_NONTRIVIAL; RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_1];
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(h:A->B) b IN ring_carrier k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    UNDISCH_TAC `ring_mul k ((h:A->B) b) (ring_1 k) = h a` THEN
    ASM_SIMP_TAC[RING_MUL_RID] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `b:A`; `a:A`]
      RING_MONOMORPHISM_INJECTIVE_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_SUB_REFL]]);;

(* A nonzero x of k has a representation h(b) x = h(a) with a and b nonzero. *)

let FIELD_FRACTION_NONZERO = prove
 (`!r k (h:A->B) x.
        field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                  ~(a = ring_0 r) /\ ~(b = ring_0 r) /\
                  ring_mul k (h b) x = h a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:B`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `ring_mul k ((h:A->B) b) x = h (ring_0 r)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `b:A`]
    RING_MONOMORPHISM_EQ_0) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `b:A`]
    RING_HOMOMORPHISM_IN_CARRIER) THEN
  ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN]);;

let DEDEKIND_VALUATION_MUL = prove
 (`!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_mul k x y) =
            dedekind_valuation (r,k) h P x + dedekind_valuation (r,k) h P y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `y:B`]
    FIELD_FRACTION_NONZERO) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `ring_mul k ((h:A->B) (ring_mul r b d)) (ring_mul k x y) =
    h (ring_mul r a c)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]) THEN
    SUBGOAL_THEN
     `(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
      h c IN ring_carrier k /\ h d IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; RING_TAC];
    ALL_TAC] THEN
  MAP_EVERY (fun (u,a,b) ->
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; u; a; b]
      DEDEKIND_VALUATION))
   [`ring_mul k x y:B`, `ring_mul r a c:A`, `ring_mul r b d:A`;
    `x:B`, `a:A`, `b:A`; `y:B`, `c:A`, `d:A`] THEN
  ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[IDEAL_VALUATION_PRINCIPAL_MUL] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let DEDEKIND_VALUATION_INV = prove
 (`!r k (h:A->B) P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_inv k x) =
            --(dedekind_valuation (r,k) h P x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                 `ring_inv k x:B`] DEDEKIND_VALUATION_MUL) THEN
  ASM_SIMP_TAC[FIELD_MUL_RINV; DEDEKIND_VALUATION_1; RING_INV;
               FIELD_INV_EQ_0] THEN
  INT_ARITH_TAC);;

let DEDEKIND_VALUATION_DIV = prove
 (`!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_div k x y) =
            dedekind_valuation (r,k) h P x - dedekind_valuation (r,k) h P y`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  ASM_SIMP_TAC[ring_div; DEDEKIND_VALUATION_MUL; RING_INV; FIELD_INV_EQ_0;
               DEDEKIND_VALUATION_INV] THEN
  INT_ARITH_TAC);;

let DEDEKIND_VALUATION_POW = prove
 (`!r k (h:A->B) P x n.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (r,k) h P (ring_pow k x n) =
            &n * dedekind_valuation (r,k) h P x`,
  REPLICATE_TAC 5 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[ring_pow; DEDEKIND_VALUATION_1; INT_MUL_LZERO] THEN
  ASM_SIMP_TAC[DEDEKIND_VALUATION_MUL; RING_POW; FIELD_POW_EQ_0;
               GSYM INT_OF_NUM_SUC] THEN
  INT_ARITH_TAC);;

(* Only a homomorphism and x IN ring_carrier k are needed: the               *)
(* representations of x and of --x correspond under a |-> --a, and (--a) =   *)
(* (a).                                                                      *)

let DEDEKIND_VALUATION_NEG = prove
 (`!r k (h:A->B) P x.
        ring_homomorphism(r,k) h /\ x IN ring_carrier k
        ==> dedekind_valuation (r,k) h P (ring_neg k x) =
            dedekind_valuation (r,k) h P x`,
  let lemma = prove
   (`!r k (h:A->B) P x (v:int).
        ring_homomorphism(r,k) h /\ x IN ring_carrier k /\
        (!a b. a IN ring_carrier r /\ b IN ring_carrier r /\
               ~(a = ring_0 r) /\ ~(b = ring_0 r) /\ ring_mul k (h b) x = h a
               ==> v = &(ideal_valuation r P (ideal_generated r {a})) -
                       &(ideal_valuation r P (ideal_generated r {b})))
        ==> (!a b. a IN ring_carrier r /\ b IN ring_carrier r /\
                   ~(a = ring_0 r) /\ ~(b = ring_0 r) /\
                   ring_mul k (h b) (ring_neg k x) = h a
                   ==> v = &(ideal_valuation r P (ideal_generated r {a})) -
                           &(ideal_valuation r P (ideal_generated r {b})))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ring_neg r a:A`; `b:A`]) THEN
    MP_TAC(ISPECL [`r:A ring`; `ring_neg r a:A`; `a:A`]
      IDEALS_GENERATED_SING_EQ) THEN
    MP_TAC(ISPECL [`r:A ring`; `a:A`; `a:A`] RING_ASSOCIATES_NEG) THEN
    ASM_SIMP_TAC[RING_NEG; RING_NEG_EQ_0; RING_ASSOCIATES_REFL] THEN
    REPLICATE_TAC 2 DISCH_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_NEG th]) THEN
    SUBGOAL_THEN `(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; RING_TAC]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[dedekind_valuation] THEN
  AP_TERM_TAC THEN ABS_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                   `ring_neg k x:B`; `v:int`] lemma) THEN
    ASM_SIMP_TAC[RING_NEG; RING_NEG_NEG];
    MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[]]);;

let DEDEKIND_VALUATION_COMPATIBLE = prove
 (`!r k (h:A->B) P R l (j:C->D) m (i:A->C) (t:B->D) x.
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        field_of_fractions (r,k) h /\
        dedekind_domain R /\ prime_ideal R m /\ ~(m = {ring_0 R}) /\
        ring_monomorphism(R,l) j /\ ring_monomorphism(r,R) i /\
        ring_homomorphism(k,l) t /\
        (!a. a IN ring_carrier r ==> t(h a) = j(i a)) /\
        (!a. a IN ring_carrier r /\ ~(a = ring_0 r)
             ==> ideal_valuation R m (ideal_generated R {i a}) =
                 ideal_valuation r P (ideal_generated r {a})) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation (R,l) j m (t x) =
            dedekind_valuation (r,k) h P x`,
  REWRITE_TAC[field_of_fractions] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[field_of_fractions] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                 `a:A`; `b:A`] DEDEKIND_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASSUME_TAC(MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM
   (ASSUME `ring_monomorphism(r,k) (h:A->B)`)) THEN
  ASSUME_TAC(MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM
   (ASSUME `ring_monomorphism(r,R) (i:A->C)`)) THEN
  SUBGOAL_THEN
   `(i:A->C) a IN ring_carrier R /\ i b IN ring_carrier R /\
    ~(i a = ring_0 R) /\ ~(i b = ring_0 R) /\
    (t:B->D) x IN ring_carrier l /\ (h:A->B) b IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:C ring`; `l:D ring`; `j:C->D`; `m:C->bool`;
                 `(t:B->D) x`; `(i:A->C) a`; `(i:A->C) b`]
    DEDEKIND_VALUATION) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN `(j:C->D)((i:A->C) a) = (t:B->D)((h:A->B) a) /\
                j(i b) = t(h b)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(h:A->B) b`; `x:B`] (MATCH_MP RING_HOMOMORPHISM_MUL
   (ASSUME `ring_homomorphism(k,l) (t:B->D)`))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* ------------------------------------------------------------------------- *)
(* The ultrametric inequality and finite support.                            *)
(* ------------------------------------------------------------------------- *)

(* With the common denominator b d, from the inequality for the principal    *)
(* ideals (a d), (c b) and (a d + c b) of r (IDEAL_VALUATION_PRINCIPAL_ADD). *)

let DEDEKIND_VALUATION_ADD = prove
 (`!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ y IN ring_carrier k /\
        ~(ring_add k x y = ring_0 k)
        ==> min (dedekind_valuation (r,k) h P x)
                (dedekind_valuation (r,k) h P y)
            <= dedekind_valuation (r,k) h P (ring_add k x y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  ASM_CASES_TAC `x:B = ring_0 k` THENL
   [ASM_SIMP_TAC[RING_ADD_LZERO] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `y:B = ring_0 k` THENL
   [ASM_SIMP_TAC[RING_ADD_RZERO] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `y:B`]
    FIELD_FRACTION_NONZERO) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c:A`; `d:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
    h c IN ring_carrier k /\ h d IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_mul k ((h:A->B) (ring_mul r b d)) x = h (ring_mul r a d) /\
    ring_mul k (h (ring_mul r b d)) y = h (ring_mul r c b) /\
    ring_mul k (h (ring_mul r b d)) (ring_add k x y) =
    h (ring_add r (ring_mul r a d) (ring_mul r c b))`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                                       MATCH_MP RING_HOMOMORPHISM_ADD th;
                                       RING_MUL]) THEN
    REPEAT CONJ_TAC THEN RING_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_add r (ring_mul r a d) (ring_mul r c b) = ring_0 r:A)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `ring_mul k ((h:A->B) (ring_mul r b d)) (ring_add k x y) =
      h (ring_add r (ring_mul r a d) (ring_mul r c b))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `ring_mul r b d:A`]
      RING_MONOMORPHISM_EQ_0) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `ring_mul r b d:A`]
      RING_HOMOMORPHISM_IN_CARRIER) THEN
    ASM_SIMP_TAC[RING_MUL; RING_ADD; INTEGRAL_DOMAIN_MUL_EQ_0;
                 FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  MAP_EVERY (fun (u,a) ->
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; u; a;
                   `ring_mul r b d:A`] DEDEKIND_VALUATION))
   [`ring_add k x y:B`, `ring_add r (ring_mul r a d) (ring_mul r c b):A`;
    `x:B`, `ring_mul r a d:A`; `y:B`, `ring_mul r c b:A`] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `ring_mul r a d:A`;
                 `ring_mul r c b:A`] IDEAL_VALUATION_PRINCIPAL_ADD) THEN
  ASM_SIMP_TAC[RING_MUL; RING_ADD; INTEGRAL_DOMAIN_MUL_EQ_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MIN] THEN INT_ARITH_TAC);;

let DEDEKIND_VALUATION_ADD_STRICT = prove
 (`!r k (h:A->B) P x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\ y IN ring_carrier k /\
        dedekind_valuation (r,k) h P x < dedekind_valuation (r,k) h P y
        ==> dedekind_valuation (r,k) h P (ring_add k x y) =
            dedekind_valuation (r,k) h P x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  ASM_CASES_TAC `y:B = ring_0 k` THEN ASM_SIMP_TAC[RING_ADD_RZERO] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `ring_add k (ring_add k x y) (ring_neg k y) = x:B`
  ASSUME_TAC THENL [RING_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(ring_add k x y = ring_0 k:B)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `ring_add k (ring_add k x y) (ring_neg k y) = x:B` THEN
    ASM_SIMP_TAC[RING_ADD_LZERO; RING_NEG] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `dedekind_valuation (r,k) h P (ring_neg k y:B) <
                 dedekind_valuation (r,k) (h:A->B) P y` THEN
    ASM_SIMP_TAC[DEDEKIND_VALUATION_NEG; INT_LT_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`; `y:B`]
    DEDEKIND_VALUATION_ADD) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `ring_add k x y:B`; `ring_neg k y:B`]
    DEDEKIND_VALUATION_ADD) THEN
  ASM_SIMP_TAC[RING_ADD; RING_NEG; DEDEKIND_VALUATION_NEG] THEN
  ASM_INT_ARITH_TAC);;

let DEDEKIND_VALUATION_FINITE = prove
 (`!r k (h:A->B) x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                        ~(dedekind_valuation (r,k) h P x = &0)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  SUBGOAL_THEN
   `ring_mul r a b IN ring_carrier r /\ ~(ring_mul r a b = ring_0 r:A)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {ring_mul r a b:A}`]
    DEDEKIND_IDEAL_FACTORIZATION) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET) o
             CONJUNCT1) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`;
                 `ideal_generated r {ring_mul r a b:A}`]
    IDEAL_VALUATION_EQ_0) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (TAUT `(p <=> ~q) ==> (q <=> ~p)`)) THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `a:A`; `b:A`]
    IDEAL_VALUATION_PRINCIPAL_MUL) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                 `a:A`; `b:A`] DEDEKIND_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integral elements, units and prime ideals by valuations.                  *)
(* ------------------------------------------------------------------------- *)

let DEDEKIND_VALUATION_INTEGRAL = prove
 (`!r k (h:A->B) x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> (x IN IMAGE h (ring_carrier r) <=>
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> &0 <= dedekind_valuation (r,k) h P x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A`
      (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(c:A = ring_0 r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((h:A->B)(ring_0 r) = ring_0 k)` THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]);
      ASM_SIMP_TAC[DEDEKIND_VALUATION_IMAGE; INT_POS]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {a:A}`;
                 `ideal_generated r {b:A}`]
    DEDEKIND_IDEAL_SUBSET_VALUATION) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0;
               SUBSET_IDEALS_GENERATED_SING] THEN
  MATCH_MP_TAC(TAUT `q /\ (p ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                   `a:A`; `b:A`] DEDEKIND_VALUATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_SUB_LE; INT_OF_NUM_LE];
    REWRITE_TAC[ring_divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `c:A` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`k:B ring`; `(h:A->B) b`] THEN
    SUBGOAL_THEN `(h:A->B) b IN ring_carrier k /\ h c IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0];
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th])]]);;

let DEDEKIND_VALUATION_UNIT = prove
 (`!r k (h:A->B) x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        x IN ring_carrier k
        ==> (x IN IMAGE h {u | ring_unit r u} <=>
             ~(x = ring_0 k) /\
             !P. prime_ideal r P /\ ~(P = {ring_0 r})
                 ==> dedekind_valuation (r,k) h P x = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `x:B = ring_0 k` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    ASM_MESON_TAC[RING_UNIT_IN_CARRIER; RING_MONOMORPHISM_EQ_0; RING_UNIT_0;
                  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING;
                  DEDEKIND_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x IN IMAGE (h:A->B) {u | ring_unit r u} <=>
    x IN IMAGE h (ring_carrier r) /\ ring_inv k x IN IMAGE h (ring_carrier r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:A`
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      CONJ_TAC THENL
       [EXISTS_TAC `u:A` THEN ASM_MESON_TAC[RING_UNIT_IN_CARRIER];
        EXISTS_TAC `ring_inv r u:A` THEN
        FIRST_ASSUM(fun th ->
          ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_INV th; RING_INV;
                       RING_UNIT_IN_CARRIER])];
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `a:A` THEN ASM_REWRITE_TAC[ring_unit] THEN
      EXISTS_TAC `c:A` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `ring_mul r a c:A`;
                     `ring_1 r:A`] RING_MONOMORPHISM_INJECTIVE_EQ) THEN
      ASM_SIMP_TAC[RING_MUL; RING_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_ASSUM(fun th ->
        ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th;
                     MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
      UNDISCH_TAC `ring_inv k x = (h:A->B) c` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `x = (h:A->B) a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[FIELD_MUL_RINV]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `ring_inv k x:B`]
    DEDEKIND_VALUATION_INTEGRAL) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    DEDEKIND_VALUATION_INTEGRAL) THEN
  ASM_SIMP_TAC[RING_INV; FIELD_INV_EQ_0; DEDEKIND_VALUATION_INV] THEN
  REPEAT(DISCH_THEN(K ALL_TAC)) THEN REWRITE_TAC[AND_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  REWRITE_TAC[INT_ARITH `&0 <= x /\ &0 <= --x <=> x:int = &0`]);;

let DEDEKIND_VALUATION_PRIME_IDEAL = prove
 (`!r k (h:A->B) P a.
        dedekind_domain r /\ ring_monomorphism(r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        a IN ring_carrier r /\ ~(a = ring_0 r)
        ==> (a IN P <=> &0 < dedekind_valuation (r,k) h P (h a))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DEDEKIND_VALUATION_IMAGE] THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `ideal_generated r {a:A}`]
    IDEAL_VALUATION_EQ_0) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0;
               IDEAL_GENERATED_MINIMAL_EQ; PRIME_IMP_RING_IDEAL;
               SET_RULE `(x:A) IN s ==> s INTER {x} = {x}`; SING_SUBSET] THEN
  REWRITE_TAC[INT_OF_NUM_LT; LT_NZ] THEN CONV_TAC TAUT);;

let DEDEKIND_VALUATION_EQ = prove
 (`!r k (h:A->B) x y.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k) /\
        y IN ring_carrier k /\ ~(y = ring_0 k)
        ==> ((!P. prime_ideal r P /\ ~(P = {ring_0 r})
                  ==> dedekind_valuation (r,k) h P x =
                      dedekind_valuation (r,k) h P y) <=>
             ?u. ring_unit r u /\ x = ring_mul k (h u) y)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                   `ring_mul k x (ring_inv k y):B`]
      DEDEKIND_VALUATION_UNIT) THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV; INTEGRAL_DOMAIN_MUL_EQ_0;
                 FIELD_IMP_INTEGRAL_DOMAIN; FIELD_INV_EQ_0;
                 DEDEKIND_VALUATION_MUL; DEDEKIND_VALUATION_INV;
                 INT_ADD_RINV] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
    ASM_SIMP_TAC[GSYM RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV;
                 RING_MUL_RID];
    DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(h:A->B) u IN ring_carrier k /\ h u IN IMAGE h {u | ring_unit r u}`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_UNIT_IN_CARRIER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `(h:A->B) u`]
      DEDEKIND_VALUATION_UNIT) THEN
    ASM_SIMP_TAC[DEDEKIND_VALUATION_MUL; INT_ADD_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Prescribed valuations and denominator ideals.                             *)
(* ------------------------------------------------------------------------- *)

(* In a Dedekind domain, a nonzero ideal with prescribed valuations at the   *)
(* nonzero primes, all but finitely many of them zero: a product of prime    *)
(* powers.                                                                   *)

let DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS = prove
 (`!r f:(A->bool)->num.
        dedekind_domain r /\
        FINITE {p | prime_ideal r p /\ ~(p = {ring_0 r}) /\ ~(f p = 0)}
        ==> ?j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
                !p. prime_ideal r p /\ ~(p = {ring_0 r})
                    ==> ideal_valuation r p j = f p`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `g = monomial_restrict
                   {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} f` THEN
  SUBGOAL_THEN
   `monomial {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})} g`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    ASM_REWRITE_TAC[MONOMIAL_RESTRICT_EQ; monomial_vars; INTER;
                    IN_ELIM_THM; GSYM CONJ_ASSOC];
    ALL_TAC] THEN
  EXISTS_TAC `ideal_product r (monomial_vars g)
                (\p:A->bool. ideal_pow r p (g p))` THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_PRODUCT;
               IDEAL_VALUATION_IDEAL_PRODUCT_MONOMIAL] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [monomial]) THEN
    ASM_SIMP_TAC[IDEAL_PRODUCT_EQ_ZERO; DEDEKIND_IMP_INTEGRAL_DOMAIN;
                 RING_IDEAL_IDEAL_POW] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `p:A->bool` THEN
    UNDISCH_TAC `monomial_vars g SUBSET
                 {p:A->bool | prime_ideal r p /\ ~(p = {ring_0 r})}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:A->bool`) THEN
    ASM_CASES_TAC `(p:A->bool) IN monomial_vars g` THEN
    ASM_SIMP_TAC[IDEAL_POW_EQ_ZERO; DEDEKIND_IMP_INTEGRAL_DOMAIN;
                 PRIME_IMP_RING_IDEAL];
    EXPAND_TAC "g" THEN SIMP_TAC[monomial_restrict; IN_ELIM_THM]]);;

(* The ideal with prescribed valuations. For finitely supported e,           *)
(* ideal_of_valuations r e is the nonzero ideal with valuations e P at the   *)
(* nonzero primes P (IDEAL_OF_VALUATIONS, by                                 *)
(* DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS). A nonzero ideal has finitely       *)
(* supported valuations (IDEAL_VALUATION_FINITE_SUPPORT) and is the ideal of *)
(* its valuations (IDEAL_OF_VALUATIONS_UNIQUE). The map turns sums into      *)
(* products (IDEAL_OF_VALUATIONS_ADD) and the zero function into the unit    *)
(* ideal (IDEAL_OF_VALUATIONS_0), and depends only on the values at the      *)
(* nonzero primes (IDEAL_OF_VALUATIONS_EQ).                                  *)
let ideal_of_valuations = new_definition
 `ideal_of_valuations (r:A ring) (e:(A->bool)->num) =
        @j. ring_ideal r j /\ ~(j = {ring_0 r}) /\
            !P. prime_ideal r P /\ ~(P = {ring_0 r})
                ==> ideal_valuation r P j = e P`;;

let IDEAL_OF_VALUATIONS = prove
 (`!r (e:(A->bool)->num).
        dedekind_domain r /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(e P = 0)}
        ==> ring_ideal r (ideal_of_valuations r e) /\
            ~(ideal_of_valuations r e = {ring_0 r}) /\
            !P. prime_ideal r P /\ ~(P = {ring_0 r})
                ==> ideal_valuation r P (ideal_of_valuations r e) = e P`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ideal_of_valuations] THEN
  CONV_TAC SELECT_CONV THEN
  ASM_SIMP_TAC[DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS]);;

let IDEAL_OF_VALUATIONS_UNIQUE = prove
 (`!r (e:(A->bool)->num) j.
        dedekind_domain r /\ ring_ideal r j /\ ~(j = {ring_0 r}) /\
        (!P. prime_ideal r P /\ ~(P = {ring_0 r})
             ==> ideal_valuation r P j = e P)
        ==> ideal_of_valuations r e = j`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                ~((e:(A->bool)->num) P = 0)}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `j:A->bool`]
      IDEAL_VALUATION_FINITE_SUPPORT) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `e:(A->bool)->num`] IDEAL_OF_VALUATIONS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DEDEKIND_IDEAL_EQ_VALUATION]);;

let IDEAL_OF_VALUATIONS_ADD = prove
 (`!r (e:(A->bool)->num) f.
        dedekind_domain r /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(e P = 0)} /\
        FINITE {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(f P = 0)}
        ==> ideal_of_valuations r (\P. e P + f P) =
            ideal_prod r (ideal_of_valuations r e) (ideal_of_valuations r f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_OF_VALUATIONS_UNIQUE THEN
  MP_TAC(ISPECL [`r:A ring`; `e:(A->bool)->num`] IDEAL_OF_VALUATIONS) THEN
  MP_TAC(ISPECL [`r:A ring`; `f:(A->bool)->num`] IDEAL_OF_VALUATIONS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_PROD; IDEAL_PROD_EQ_ZERO;
               DEDEKIND_IMP_INTEGRAL_DOMAIN; IDEAL_VALUATION_IDEAL_PROD]);;

let IDEAL_OF_VALUATIONS_0 = prove
 (`!r:A ring.
        dedekind_domain r ==> ideal_of_valuations r (\P. 0) = ring_carrier r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_OF_VALUATIONS_UNIQUE THEN
  ASM_REWRITE_TAC[RING_IDEAL_CARRIER] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FIELD_EQ_TRIVIAL_IDEALS; DEDEKIND_IMP_INTEGRAL_DOMAIN;
                  INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING; RING_CARRIER_NONEMPTY;
                  TRIVIAL_RING_SUBSET; SUBSET_REFL];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IDEAL_VALUATION_CARRIER THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
    ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL_ALT;
                  prime_ideal; proper_ideal]]);;

let IDEAL_OF_VALUATIONS_EQ = prove
 (`!r (e:(A->bool)->num) f.
        (!P. prime_ideal r P /\ ~(P = {ring_0 r}) ==> e P = f P)
        ==> ideal_of_valuations r e = ideal_of_valuations r f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ideal_of_valuations] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

(* Prescribed values at finitely many nonzero primes: h(a) / h(b) with a, b  *)
(* from DEDEKIND_WEAK_APPROXIMATION for the positive and the negative parts. *)

let DEDEKIND_VALUATION_WEAK_APPROXIMATION = prove
 (`!r k (h:A->B) s (e:(A->bool)->int).
        dedekind_domain r /\ field k /\ ring_monomorphism(r,k) h /\
        FINITE s /\ (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                !P. P IN s ==> dedekind_valuation (r,k) h P x = e P`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:(A->bool)->bool`;
                 `\P:A->bool. num_of_int(max (--(e P)) (&0))`]
    DEDEKIND_WEAK_APPROXIMATION) THEN
  MP_TAC(ISPECL [`r:A ring`; `s:(A->bool)->bool`;
                 `\P:A->bool. num_of_int(max (e P) (&0))`]
    DEDEKIND_WEAK_APPROXIMATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:A` THEN STRIP_TAC THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `(h:A->B) a IN ring_carrier k /\ h b IN ring_carrier k /\
    ~(h a = ring_0 k) /\ ~(h b = ring_0 k)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_inv k ((h:A->B) b) IN ring_carrier k /\
    ring_mul k (h b) (ring_inv k (h b)) = ring_1 k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV]; ALL_TAC] THEN
  EXISTS_TAC `ring_mul k ((h:A->B) a) (ring_inv k (h b))` THEN
  ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN;
               FIELD_INV_EQ_0] THEN
  X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                 `ring_mul k ((h:A->B) a) (ring_inv k (h b))`; `a:A`; `b:A`]
    DEDEKIND_VALUATION) THEN
  ASM_SIMP_TAC[RING_MUL] THEN ANTS_TAC THENL
   [RING_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&0 <= max (x:int) (&0)`] THEN
  INT_ARITH_TAC);;

let DEDEKIND_VALUATION_APPROXIMATION = prove
 (`!r k (h:A->B) s (e:(A->bool)->int).
        dedekind_domain r /\ field k /\ ring_monomorphism(r,k) h /\
        FINITE s /\ (!P. P IN s ==> prime_ideal r P /\ ~(P = {ring_0 r}))
        ==> ?x. x IN ring_carrier k /\ ~(x = ring_0 k) /\
                (!P. P IN s ==> dedekind_valuation (r,k) h P x = e P) /\
                (!P. prime_ideal r P /\ ~(P = {ring_0 r}) /\ ~(P IN s)
                     ==> &0 <= dedekind_valuation (r,k) h P x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASSUME_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] RING_MONOMORPHISM_EQ_0)
   (ASSUME `ring_monomorphism(r,k) (h:A->B)`)) THEN
  MP_TAC(ISPECL [`r:A ring`; `s:(A->bool)->bool`;
                 `\P. num_of_int(max (&0) (--((e:(A->bool)->int) P)))`]
    DEDEKIND_WEAK_APPROXIMATION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:A` THEN STRIP_TAC THEN
  ABBREV_TAC
   `t = s UNION {P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                     ideal_generated r {d:A} SUBSET P}` THEN
  SUBGOAL_THEN `FINITE(t:(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[FINITE_UNION] THEN
    ASM_SIMP_TAC[DEDEKIND_IDEAL_FACTORIZATION; RING_IDEAL_IDEAL_GENERATED;
                 IDEAL_GENERATED_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `t:(A->bool)->bool`;
                 `\P. if P IN s
                      then num_of_int((e:(A->bool)->int) P +
                                      max (&0) (--(e P)))
                      else ideal_valuation r P (ideal_generated r {d:A})`]
    DEDEKIND_WEAK_APPROXIMATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `y:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((h:A->B) d = ring_0 k) /\ ~(h y = ring_0 k) /\
                h d IN ring_carrier k /\ h y IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER];
    ALL_TAC] THEN
  EXISTS_TAC `ring_mul k ((h:A->B) y) (ring_inv k (h d))` THEN
  SUBGOAL_THEN
   `ring_mul k ((h:A->B) d) (ring_mul k (h y) (ring_inv k (h d))) = h y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:B ring`; `(h:A->B) d`] FIELD_MUL_RINV) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(RING_RULE
     `ring_mul (k:B ring) a b = ring_1 k
      ==> ring_mul k a (ring_mul k c b) = c`) THEN
    ASM_SIMP_TAC[RING_INV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL; RING_INV; FIELD_MUL_EQ_0; FIELD_INV_EQ_0] THEN
  SUBGOAL_THEN
   `!P. prime_ideal r P /\ ~(P = {ring_0 r})
        ==> dedekind_valuation (r,k) (h:A->B) P
             (ring_mul k (h y) (ring_inv k (h d))) =
            &(ideal_valuation r P (ideal_generated r {y})) -
            &(ideal_valuation r P (ideal_generated r {d}))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC DEDEKIND_VALUATION THEN
    ASM_SIMP_TAC[RING_MUL; RING_INV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `prime_ideal r P /\ ~(P = {ring_0 r:A})` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[]] THEN
    SUBGOAL_THEN `(P:A->bool) IN t` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&0:int <= max (&0) x`;
             INT_ARITH `&0:int <= e + max (&0) (--e)`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `(P:A->bool) IN t` THENL
   [ASM_SIMP_TAC[INT_SUB_REFL; INT_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `ideal_valuation r P (ideal_generated r {d:A}) = 0`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[IDEAL_VALUATION_EQ_0; RING_IDEAL_IDEAL_GENERATED;
                 IDEAL_GENERATED_EQ_0] THEN
    UNDISCH_TAC `~((P:A->bool) IN t)` THEN EXPAND_TAC "t" THEN
    ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM];
    INT_ARITH_TAC]);;

(* The denominator ideal of x: the product of the P^(-v_P(x)) over the       *)
(* finitely many P with v_P(x) < 0.                                          *)

let DEDEKIND_DENOMINATOR_IDEAL = prove
 (`!r k (h:A->B) x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> ?J. ring_ideal r J /\ ~(J = {ring_0 r}) /\
                !P. prime_ideal r P /\ ~(P = {ring_0 r})
                    ==> &(ideal_valuation r P J):int =
                        max (&0) (--(dedekind_valuation (r,k) h P x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  MP_TAC(ISPECL
   [`r:A ring`;
    `\P:A->bool. num_of_int(max (&0)
                    (--(dedekind_valuation (r,k) (h:A->B) P x)))`]
   DEDEKIND_IDEAL_PRESCRIBED_VALUATIONS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{P | prime_ideal r P /\ ~(P = {ring_0 r}) /\
                     ~(dedekind_valuation (r,k) (h:A->B) P x = &0)}` THEN
    ASM_SIMP_TAC[DEDEKIND_VALUATION_FINITE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM INT_OF_NUM_EQ] THEN
    SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&0 <= max (&0) (x:int)`] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&0 <= max (&0) (x:int)`]]);;

(* An ideal J with v_P(J) + v_P(x) >= 0 at every nonzero prime P clears the  *)
(* denominator of x: h(c) x is in the image of r for every c in J.           *)

let DEDEKIND_IDEAL_MUL_INTEGRAL = prove
 (`!r k (h:A->B) J x c.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        ring_ideal r J /\ x IN ring_carrier k /\
        (!P. prime_ideal r P /\ ~(P = {ring_0 r})
             ==> &0 <= &(ideal_valuation r P J) +
                       dedekind_valuation (r,k) h P x) /\
        c IN J
        ==> ring_mul k (h c) x IN IMAGE h (ring_carrier r)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN `(c:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:A->B) c IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
  ASM_CASES_TAC `c:A = ring_0 r \/ x:B = ring_0 k` THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_MUL_RZERO; IN_IMAGE] THEN
    EXISTS_TAC `ring_0 r:A` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
    REWRITE_TAC[RING_0];
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM])] THEN
  SUBGOAL_THEN `~((h:A->B) c = ring_0 k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`;
                 `ring_mul k ((h:A->B) c) x`]
    DEDEKIND_VALUATION_INTEGRAL) THEN
  ASM_SIMP_TAC[RING_MUL; INTEGRAL_DOMAIN_MUL_EQ_0;
               FIELD_IMP_INTEGRAL_DOMAIN] THEN
  DISCH_THEN SUBST1_TAC THEN X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[DEDEKIND_VALUATION_MUL; DEDEKIND_VALUATION_IMAGE] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_generated r {c:A}`; `J:A->bool`]
    DEDEKIND_IDEAL_SUBSET_VALUATION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `(c:A) IN {ring_0 r}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IDEAL_GENERATED_MINIMAL THEN ASM_REWRITE_TAC[SING_SUBSET];
    DISCH_THEN(MP_TAC o SPEC `P:A->bool`)] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `P:A->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The valuation ring, the localization at P and the local case.             *)
(* ------------------------------------------------------------------------- *)

(* The valuation ring of v_P consists of the fractions with denominator      *)
(* outside P: an element of the denominator ideal J outside P (v_P(J) = 0)   *)
(* is one.                                                                   *)

let DEDEKIND_VALUATION_POS = prove
 (`!r k (h:A->B) P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\ x IN ring_carrier k
        ==> ((x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x) <=>
             ?a b. a IN ring_carrier r /\ b IN ring_carrier r /\ ~(b IN P) /\
                   ring_mul k (h b) x = h a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ASM_CASES_TAC `x:B = ring_0 k` THEN ASM_REWRITE_TAC[] THENL
   [MAP_EVERY EXISTS_TAC [`ring_0 r:A`; `ring_1 r:A`] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th;
                                      MATCH_MP RING_HOMOMORPHISM_1 th]) THEN
    ASM_SIMP_TAC[RING_0; RING_1; RING_MUL_RZERO] THEN
    ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL];
    EQ_TAC] THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
      DEDEKIND_DENOMINATOR_IDEAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `J:A->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(J SUBSET (P:A->bool))` MP_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `J:A->bool`]
        IDEAL_VALUATION_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_SIMP_TAC[] THEN
      ASM_INT_ARITH_TAC;
      REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP]] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `J:A->bool`; `x:B`;
                   `c:A`] DEDEKIND_IDEAL_MUL_INTEGRAL) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `c:A`] THEN
    ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(b:A = ring_0 r)` ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL]; ALL_TAC] THEN
    SUBGOAL_THEN `~(a:A = ring_0 r)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ring_mul k ((h:A->B) b) x = h (ring_0 r)` THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]) THEN
      MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `b:A`]
        RING_MONOMORPHISM_EQ_0) THEN
      MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `b:A`]
        RING_HOMOMORPHISM_IN_CARRIER) THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                   `a:A`; `b:A`] DEDEKIND_VALUATION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `ideal_generated r {b:A}`]
      IDEAL_VALUATION_EQ_0) THEN
    ASM_SIMP_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0;
                 IDEAL_GENERATED_MINIMAL_EQ; PRIME_IMP_RING_IDEAL;
                 SET_RULE `(x:A) IN s ==> s INTER {x} = {x}`; SING_SUBSET] THEN
    DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC]);;

(* The valuation ring of v_P is the image of the localization r_P under the  *)
(* monomorphism g with g(a / 1) = h(a) (RING_LOCALIZATION_UNIVERSAL); the    *)
(* value y of g at a / b is the solution of h(b) y = h(a).                   *)

let DEDEKIND_VALUATION_RING_LOCALIZATION = prove
 (`!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> ?g. ring_monomorphism
                 (ring_localization r (ring_carrier r DIFF P),k) g /\
                (!a. a IN ring_carrier r
                     ==> g(ring_fractionate r (ring_carrier r DIFF P) a) =
                         h a) /\
                IMAGE g (ring_carrier
                          (ring_localization r (ring_carrier r DIFF P))) =
                {x | x IN ring_carrier k /\
                     (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h P x)}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  ABBREV_TAC `s = ring_carrier r DIFF (P:A->bool)` THEN
  SUBGOAL_THEN `ring_multsys r (s:A->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN ASM_SIMP_TAC[RING_MULTSYS_NONPRIME]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:A. b IN s <=> b IN ring_carrier r /\ ~(b IN P)`
  ASSUME_TAC THENL [EXPAND_TAC "s" THEN REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `k:B ring`; `h:A->B`]
    RING_LOCALIZATION_UNIVERSAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FIELD_UNIT] THEN
    ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0;
                  IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:(A#A->bool)->B` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!a b. a IN ring_carrier r /\ b IN s
          ==> g(ring_localequiv r s (a,b)) IN ring_carrier k /\
              ring_mul k ((h:A->B) b) (g(ring_localequiv r s (a,b))) = h a`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(b:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_localequiv r s (a:A,b) IN ring_carrier(ring_localization r s) /\
      ring_fractionate r s b IN ring_carrier(ring_localization r s)`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[RING_LOCALEQUIV_IN_CARRIER; RING_FRACTIONATE_IN_CARRIER];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
    MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `a:A`; `b:A`]
      LOCALEQUIV_MUL_RCANCEL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM `g:(A#A->bool)->B`) THEN
    FIRST_ASSUM(fun th ->
      ASM_SIMP_TAC[MATCH_MP RING_HOMOMORPHISM_MUL th]);
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[RING_MONOMORPHISM_ALT] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[RING_LOCALIZATION_CARRIER; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `a:A = ring_0 r` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN
      ASM_SIMP_TAC[RING_MUL_RZERO] THEN
      SUBGOAL_THEN `(h:A->B) b IN ring_carrier k` ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]; ALL_TAC] THEN
      ASM_SIMP_TAC[RING_MUL_RZERO] THEN
      ASM_MESON_TAC[RING_MONOMORPHISM_EQ_0];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RING_LOCALEQUIV_EQ_0_GEN; RING_0] THEN
    EXISTS_TAC `ring_1 r:A` THEN ASM_SIMP_TAC[RING_1; RING_MUL_RZERO] THEN
    ASM_MESON_TAC[PRIME_IMP_PROPER_IDEAL; PROPER_IDEAL];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; RING_LOCALIZATION_CARRIER;
                 FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`;
                   `g(ring_localequiv r s (a:A,b)):B`]
      DEDEKIND_VALUATION_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:A`; `b:A`] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`]
      DEDEKIND_VALUATION_POS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `ring_localequiv r s (a:A,b)` THEN
    SUBGOAL_THEN `(b:A) IN s` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `b:A`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
      MAP_EVERY EXISTS_TAC [`k:B ring`; `(h:A->B) b`] THEN
      ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_MONOMORPHISM_EQ_0;
                    IN_RING_IDEAL_0; PRIME_IMP_RING_IDEAL];
      ASM_SIMP_TAC[RING_LOCALIZATION_CARRIER] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]]);;

(* v_P is the valuation of the DVR r_P (DVR_LOCALIZATION) at its maximal     *)
(* ideal P r_P: (a) r_P is generated by a / 1 and has the valuation of (a)   *)
(* (IDEAL_VALUATION_LOCALIZATION).                                           *)

let DEDEKIND_VALUATION_LOCALIZATION = prove
 (`!r k (h:A->B) g P x.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r}) /\
        ring_monomorphism(ring_localization r (ring_carrier r DIFF P),k) g /\
        (!a. a IN ring_carrier r
             ==> g(ring_fractionate r (ring_carrier r DIFF P) a) = h a) /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> dedekind_valuation
             (ring_localization r (ring_carrier r DIFF P),k) g
             {ring_localequiv r (ring_carrier r DIFF P) (a,b) | a,b |
              a IN P /\ b IN ring_carrier r DIFF P} x =
            dedekind_valuation (r,k) h P x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN
   `ring_multsys r (ring_carrier r DIFF P) /\
    ~(ring_0 r IN ring_carrier r DIFF P) /\
    ring_carrier r DIFF P SUBSET {a:A | ring_regular r a} /\
    P INTER (ring_carrier r DIFF P) = {} /\
    (P:A->bool) SUBSET ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_MULTSYS_NONPRIME; IN_DIFF; IN_RING_IDEAL_0;
                 SUBSET; IN_ELIM_THM; INTEGRAL_DOMAIN_REGULAR;
                 PRIME_IDEAL_IMP_SUBSET] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[IN_RING_IDEAL_0]; SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `s = ring_carrier r DIFF (P:A->bool)` THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
    FIELD_FRACTION_NONZERO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`; `x:B`;
                 `a:A`; `b:A`] DEDEKIND_VALUATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!c:A. c IN ring_carrier r /\ ~(c = ring_0 r)
          ==> ring_fractionate r s c IN ring_carrier(ring_localization r s) /\
              ~(ring_fractionate r s c = ring_0(ring_localization r s)) /\
              ideal_generated (ring_localization r s)
                {ring_fractionate r s c} =
              {ring_localequiv r s (u,v) | u,v |
               u IN ideal_generated r {c} /\ v IN s}`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[RING_FRACTIONATE_IN_CARRIER] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_FRACTIONATE_EQ_0_GEN; NOT_EXISTS_THM] THEN
      X_GEN_TAC `d:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(d:A) IN ring_carrier r /\ ~(d = ring_0 r)`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[RING_MULTSYS_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
      UNDISCH_TAC `ring_mul r d c = ring_0 r:A` THEN
      ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0];
      MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `{c:A}`]
        IDEAL_GENERATED_RING_LOCALIZATION) THEN
      ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`ring_localization r (s:A->bool)`; `k:B ring`; `g:(A#A->bool)->B`;
    `{ring_localequiv r s (a,b) | a,b | a IN P /\ b IN (s:A->bool)}`;
    `x:B`; `ring_fractionate r s (a:A)`; `ring_fractionate r s (b:A)`]
   DEDEKIND_VALUATION) THEN
  ASM_SIMP_TAC[DEDEKIND_LOCALIZATION; PRIME_IDEAL_LOCALIZATION;
               IDEAL_LOCALIZATION_EQ_ZERO] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `P:A->bool`;
                 `ideal_generated r {b:A}`] IDEAL_VALUATION_LOCALIZATION) THEN
  MP_TAC(ISPECL [`r:A ring`; `s:A->bool`; `P:A->bool`;
                 `ideal_generated r {a:A}`] IDEAL_VALUATION_LOCALIZATION) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;

let ISOMORPHIC_RING_DVR = prove
 (`!(r:A ring) (r':B ring). r isomorphic_ring r' ==> (DVR r <=> DVR r')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DVR] THEN
  ASM_MESON_TAC[ISOMORPHIC_RING_PIDNESS; ISOMORPHIC_RING_LOCALITY;
                ISOMORPHIC_RING_FIELDNESS]);;

let DEDEKIND_VALUATION_RING_DVR = prove
 (`!r k (h:A->B) P.
        dedekind_domain r /\ field_of_fractions (r,k) h /\
        prime_ideal r P /\ ~(P = {ring_0 r})
        ==> DVR (subring_generated k
                  {x | x IN ring_carrier k /\
                       (x = ring_0 k \/
                        &0 <= dedekind_valuation (r,k) h P x)})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `P:A->bool`]
    DEDEKIND_VALUATION_RING_LOCALIZATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A#A->bool)->B` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`g:(A#A->bool)->B`;
                 `ring_localization r (ring_carrier r DIFF P:A->bool)`;
                 `k:B ring`] RING_ISOMORPHISM_ONTO_IMAGE) THEN
  ASM_REWRITE_TAC[ring_image] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `P:A->bool`] DVR_LOCALIZATION) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN
  MATCH_MP_TAC ISOMORPHIC_RING_DVR THEN
  REWRITE_TAC[isomorphic_ring] THEN ASM_MESON_TAC[]);;

(* In a DVR every nonzero prime is the maximal ideal m, so the integral      *)
(* elements and the units are read off from v_m alone.                       *)

let DVR_DEDEKIND_VALUATION = prove
 (`!r k (h:A->B) m.
        DVR r /\ maximal_ideal r m /\ field_of_fractions (r,k) h
        ==> IMAGE h (ring_carrier r) =
            {x | x IN ring_carrier k /\
                 (x = ring_0 k \/ &0 <= dedekind_valuation (r,k) h m x)} /\
            IMAGE h {u | ring_unit r u} =
            {x | x IN ring_carrier k /\ ~(x = ring_0 k) /\
                 dedekind_valuation (r,k) h m x = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [field_of_fractions]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DVR_IFF_LOCAL_DEDEKIND]) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM) THEN
  SUBGOAL_THEN
   `!P. prime_ideal r P /\ ~(P = {ring_0 r}) <=> P = (m:A->bool)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [local_ring]) THEN
      REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN
      ASM_MESON_TAC[DEDEKIND_NONZERO_PRIME_IMP_MAXIMAL];
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[MAXIMAL_IMP_PRIME_IDEAL] THEN
      ASM_MESON_TAC[MAXIMAL_IDEAL_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `prime_ideal r (m:A->bool) /\ ~(m = {ring_0 r})`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:B` THEN REWRITE_TAC[IN_ELIM_THM] THENL
   [ASM_CASES_TAC `x:B = ring_0 k` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[RING_0; IN_IMAGE] THEN EXISTS_TAC `ring_0 r:A` THEN
      REWRITE_TAC[RING_0] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_0 th]);
      ALL_TAC] THEN
    ASM_CASES_TAC `(x:B) IN ring_carrier k` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
        DEDEKIND_VALUATION_INTEGRAL) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER]];
    ASM_CASES_TAC `(x:B) IN ring_carrier k` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`r:A ring`; `k:B ring`; `h:A->B`; `x:B`]
        DEDEKIND_VALUATION_UNIT) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      ASM_MESON_TAC[RING_HOMOMORPHISM_IN_CARRIER; RING_UNIT_IN_CARRIER]]]);;

(* A uniformizer of P. For p IN P DIFF P^2, every a IN P^n is p^n b modulo   *)
(* P^(n+k) for some b, and p^n b IN P^(n+k) forces b IN P^k                  *)
(* (DEDEKIND_UNIFORMIZER_CRITERION): P-adic digits with respect to p.        *)
let DEDEKIND_UNIFORMIZER_CRITERION = prove
 (`!r P (p:A).
        dedekind_domain r /\ prime_ideal r P /\ ~(P = {ring_0 r}) /\
        p IN P /\ ~(p IN ideal_pow r P 2)
        ==> (!n k a. a IN ideal_pow r P n
                     ==> ?b. b IN ring_carrier r /\
                             ring_sub r a (ring_mul r (ring_pow r p n) b) IN
                             ideal_pow r P (n + k)) /\
            (!n k b. b IN ring_carrier r /\
                     ring_mul r (ring_pow r p n) b IN ideal_pow r P (n + k)
                     ==> b IN ideal_pow r P k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_IMP_INTEGRAL_DOMAIN) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  SUBGOAL_THEN `(p:A) IN ring_carrier r /\ ~(p = ring_0 r)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(ring_0 r IN ideal_pow r (P:A->bool) 2)` THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_0; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  SUBGOAL_THEN `ideal_valuation r P (ideal_generated r {p:A}) = 1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `p:A`; `2:num`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    MP_TAC(ISPECL [`r:A ring`; `P:A->bool`; `p:A`; `1:num`]
      DEDEKIND_IN_IDEAL_POW_VALUATION) THEN
    ASM_SIMP_TAC[IDEAL_POW_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ring_pow r (p:A) n IN ring_carrier r /\
        ~(ring_pow r p n = ring_0 r) /\
        ideal_valuation r P (ideal_generated r {ring_pow r p n}) = n`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[RING_POW; INTEGRAL_DOMAIN_POW_EQ_0] THEN
    ASM_SIMP_TAC[GSYM IDEAL_POW_PRINCIPAL; IDEAL_VALUATION_IDEAL_POW;
                 RING_IDEAL_IDEAL_GENERATED; IDEAL_GENERATED_EQ_0] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ring_ideal r (ideal_pow r (P:A->bool) m) /\
        ~(ideal_pow r P m = {ring_0 r})`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; IDEAL_POW_EQ_ZERO]; ALL_TAC] THEN
  CONJ_TAC THEN REPEAT STRIP_TAC THENL
   [ALL_TAC;
    ASM_CASES_TAC `b = ring_0 (r:A ring)` THENL
     [ASM_SIMP_TAC[IN_RING_IDEAL_0]; ALL_TAC] THEN
    UNDISCH_TAC
     `ring_mul r (ring_pow r p n) b IN ideal_pow r (P:A->bool) (n + k)` THEN
    ASM_SIMP_TAC[DEDEKIND_IN_IDEAL_POW_VALUATION; RING_MUL;
                 INTEGRAL_DOMAIN_MUL_EQ_0; IDEAL_VALUATION_PRINCIPAL_MUL] THEN
    ARITH_TAC] THEN
  SUBGOAL_THEN
   `ideal_pow r P n SUBSET
    ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                  (ideal_pow r P (n + k))`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `a:A`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ring_setadd; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:A`; `z:A`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:A) IN ideal_generated r {ring_pow r p n}` THEN
    ASM_SIMP_TAC[IN_IDEAL_GENERATED_SING_EQ; ring_divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `b:A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `b:A` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier r` ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_RULE `ring_sub r (ring_add r y z) y = z:A`;
                 RING_MUL]] THEN
  SUBGOAL_THEN
   `ideal_pow r P (n + k) SUBSET
    ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                  (ideal_pow r P (n + k))`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; ring_setadd; IN_ELIM_THM] THEN
    X_GEN_TAC `z:A` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`ring_0 r:A`; `z:A`] THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_0; RING_IDEAL_IDEAL_GENERATED] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC RING_ADD_LZERO THEN
    ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_ideal r (ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                               (ideal_pow r P (n + k))) /\
    ~(ring_setadd r (ideal_generated r {ring_pow r p n})
                    (ideal_pow r P (n + k)) = {ring_0 r})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_SETADD; RING_IDEAL_IDEAL_GENERATED] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ideal_pow r P (n + k) = {ring_0 r:A}` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!s t z:A. t SUBSET s /\ s = {z} /\ z IN t ==> t = {z}`) THEN
      EXISTS_TAC
       `ring_setadd r (ideal_generated r {ring_pow r (p:A) n})
                      (ideal_pow r P (n + k))` THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_0];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DEDEKIND_IDEAL_SUBSET_VALUATION] THEN
  X_GEN_TAC `q:A->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[IDEAL_VALUATION_SETADD; RING_IDEAL_IDEAL_GENERATED;
               IDEAL_GENERATED_EQ_0; IDEAL_VALUATION_IDEAL_POW;
               IDEAL_VALUATION_PRIME; PRIME_IMP_RING_IDEAL] THEN
  ASM_CASES_TAC `P:A->bool = q` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[MIN] THEN ARITH_TAC);;

let FREE_BASIS_FRACTION_FIELD_MAP = prove
 (`!r s (h:A->B) n b k (u:A->C) l (v:B->D).
        ring_monomorphism(r,s) h /\ free_basis (r,s) h n b /\
        field_of_fractions (r,k) u /\ field_of_fractions (s,l) v /\
        (!d. d IN ring_carrier s /\ ~(d = ring_0 s)
             ==> ?c z. c IN ring_carrier r /\ ~(c = ring_0 r) /\
                       z IN ring_carrier s /\ ring_mul s d z = h c)
        ==> ring_monomorphism(k,l) (fraction_field_map (r,k) u l (v o h)) /\
            (!a. a IN ring_carrier r
                 ==> fraction_field_map (r,k) u l (v o h) (u a) = v(h a)) /\
            free_basis (k,l) (fraction_field_map (r,k) u l (v o h)) n
                       (v o b)`,
  REWRITE_TAC[field_of_fractions; GSYM CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
  REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "kfrac") MP_TAC) THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lfrac") (LABEL_TAC "div")) THEN
  MP_TAC(ISPECL [`r:A ring`; `k:C ring`; `u:A->C`; `l:D ring`;
                 `(v:B->D) o (h:A->B)`] FRACTION_FIELD_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[field_of_fractions] THEN
    MATCH_MP_TAC RING_MONOMORPHISM_COMPOSE THEN
    EXISTS_TAC `s:B ring` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `H = fraction_field_map (r,k) (u:A->C) l ((v:B->D) o (h:A->B))` THEN
  REWRITE_TAC[o_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Hu")) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM
                                   (ASSUME t)))
   [`ring_monomorphism(r,s) (h:A->B)`; `ring_monomorphism(r,k) (u:A->C)`;
    `ring_monomorphism(s,l) (v:B->D)`; `ring_monomorphism(k,l) (H:C->D)`] THEN
  MAP_EVERY (fun t -> let th = ASSUME t in
     MAP_EVERY (ASSUME_TAC o C MATCH_MP th)
      [RING_HOMOMORPHISM_0; RING_HOMOMORPHISM_MUL;
       REWRITE_RULE[IMP_CONJ] RING_HOMOMORPHISM_IN_CARRIER])
   [`ring_homomorphism(r,s) (h:A->B)`; `ring_homomorphism(r,k) (u:A->C)`;
    `ring_homomorphism(s,l) (v:B->D)`; `ring_homomorphism(k,l) (H:C->D)`] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(MATCH_MP
     (REWRITE_RULE[IMP_CONJ] RING_MONOMORPHISM_EQ_0) (ASSUME t)))
   [`ring_monomorphism(r,s) (h:A->B)`; `ring_monomorphism(r,k) (u:A->C)`;
    `ring_monomorphism(s,l) (v:B->D)`] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(MATCH_MP FIELD_IMP_INTEGRAL_DOMAIN
                                   (ASSUME t)))
   [`field(k:C ring)`; `field(l:D ring)`] THEN
  MP_TAC(ASSUME `free_basis (r,s) (h:A->B) n b`) THEN
  REWRITE_TAC[free_basis] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "bspan") (LABEL_TAC "bind"))) THEN
  REWRITE_TAC[free_basis; o_THM] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    X_GEN_TAC `x:D` THEN DISCH_TAC THEN
    USE_THEN "lfrac"
     (MP_TAC o C MATCH_MP (ASSUME `(x:D) IN ring_carrier l`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:B` (X_CHOOSE_THEN `d:B` STRIP_ASSUME_TAC)) THEN
    USE_THEN "div" (MP_TAC o C MATCH_MP
     (CONJ (ASSUME `(d:B) IN ring_carrier s`)
           (ASSUME `~((d:B) = ring_0 s)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` (X_CHOOSE_THEN `z:B` STRIP_ASSUME_TAC)) THEN
    USE_THEN "bspan" (MP_TAC o SPEC `ring_mul s y z:B`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[RING_MUL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num->A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(u:A->C) c IN ring_carrier k /\ ~(u c = ring_0 k)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_inv k ((u:A->C) c) IN ring_carrier k /\
      (H:C->D)(ring_inv k (u c)) IN ring_carrier l /\
      !i. i < n
          ==> (h:A->B)((a:num->A) i) IN ring_carrier s /\
              (v:B->D)(h(a i)) IN ring_carrier l /\
              ring_mul k (u(a i)) (ring_inv k (u c)) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[RING_INV; RING_MUL]; ALL_TAC] THEN
    EXISTS_TAC
     `\i. ring_mul k ((u:A->C)((a:num->A) i)) (ring_inv k (u(c:A)))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_MUL; RING_INV]; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_DOMAIN_MUL_LCANCEL THEN
    MAP_EVERY EXISTS_TAC [`l:D ring`; `(v:B->D)((h:A->B) c)`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]; ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]; REWRITE_TAC[RING_SUM]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(v:B->D)(ring_mul s y z)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(v:B->D)((h:A->B) c) = ring_mul l (v d) (v z) /\
        v(ring_mul s y z) = ring_mul l (v y) (v z)`
      (fun th -> REWRITE_TAC[th]) THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          rhs(concl th) = `(h:A->B) c`)) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `ring_mul l ((v:B->D) d) x = v y` THEN
        MATCH_MP_TAC(RING_RULE
         `ring_mul (l:D ring) p x = q
          ==> ring_mul l (ring_mul l p w) x = ring_mul l q w`) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      lhs(concl th) = `ring_mul s (y:B) z`)) THEN
    MP_TAC(BETA_RULE(ISPECL
     [`s:B ring`; `l:D ring`; `v:B->D`; `{i:num | i < n}`;
      `\i. (h:A->B)((a:num->A) i)`; `b:num->B`]
     RING_HOMOMORPHISM_SUM_MUL)) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL; RING_INV];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_mul (l:D ring) p q = m
      ==> ring_mul l m w = ring_mul l p (ring_mul l q w)`)) THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_INV]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `(H:C->D)(ring_mul k (u(c:A))
                (ring_mul k (u((a:num->A) i)) (ring_inv k (u c))))` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[RING_MUL; RING_INV]; ALL_TAC] THEN
    SUBGOAL_THEN
     `ring_mul k ((u:A->C) c)
        (ring_mul k (u((a:num->A) i)) (ring_inv k (u c))) = u(a i)`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`k:C ring`; `(u:A->C) c`] FIELD_MUL_RINV) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(RING_RULE
       `ring_mul (k:C ring) x z = ring_1 k
        ==> ring_mul k x (ring_mul k y z) = y`) THEN
      ASM_SIMP_TAC[RING_INV];
      ASM_SIMP_TAC[]];
    X_GEN_TAC `q:num->C` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `k:C ring`; `u:A->C`; `q:num->C`;
                   `{i:num | i < n}`] FRACTION_FIELD_COMMON_DENOMINATOR) THEN
    ASM_REWRITE_TAC[field_of_fractions; FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:A` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num->A` (LABEL_TAC "a")) THEN
    USE_THEN "bind" (MP_TAC o SPEC `a:num->A`) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [USE_THEN "a" (fun th -> SIMP_TAC[th]); ALL_TAC] THEN
      SUBGOAL_THEN
       `(v:B->D)(ring_sum s {i | i < n}
                  (\i. ring_mul s ((h:A->B)((a:num->A) i)) (b i))) =
        ring_0 l`
      MP_TAC THENL [ALL_TAC; ASM_SIMP_TAC[RING_SUM]] THEN
      MP_TAC(BETA_RULE(ISPECL
       [`s:B ring`; `l:D ring`; `v:B->D`; `{i:num | i < n}`;
        `\i. (h:A->B)((a:num->A) i)`; `b:num->B`]
       RING_HOMOMORPHISM_SUM_MUL)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; DISCH_THEN SUBST1_TAC] THEN
      TRANS_TAC EQ_TRANS
       `ring_mul l ((H:C->D)(u(c:A)))
          (ring_sum l {i | i < n}
             (\i. ring_mul l (H((q:num->C) i)) (v((b:num->B) i))))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC RING_MUL_RZERO THEN
        ASM_SIMP_TAC[]] THEN
      W(MP_TAC o PART_MATCH (rand o rand) RING_SUM_LMUL o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM; RING_MUL];
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC RING_SUM_EQ THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
       `ring_mul (l:D ring) p q = m
        ==> ring_mul l m w = ring_mul l p (ring_mul l q w)`)) THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      TRANS_TAC EQ_TRANS `(H:C->D)(ring_mul k (u(c:A)) ((q:num->C) i))` THEN
      CONJ_TAC THENL [CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
      USE_THEN "a" (fun th ->
        REWRITE_TAC[CONJUNCT2(MATCH_MP th (ASSUME `i:num < n`))]) THEN
      USE_THEN "Hu" MATCH_MP_TAC THEN
      USE_THEN "a" (fun th ->
        REWRITE_TAC[CONJUNCT1(MATCH_MP th (ASSUME `i:num < n`))]);
      ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "a0") THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REMOVE_THEN "a" (MP_TAC o C MATCH_MP (ASSUME `i:num < n`)) THEN
    REMOVE_THEN "a0" (fun th ->
      REWRITE_TAC[MATCH_MP th (ASSUME `i:num < n`)]) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; RING_0]]);;
