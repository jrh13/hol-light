(* ========================================================================= *)
(* Hensel lemma at finite level: lifting roots and factorizations of         *)
(* polynomials modulo the powers of an ideal.                                *)
(*                                                                           *)
(* Let m be an ideal of a ring r, f a polynomial over r and f1 = poly_deriv  *)
(* r f its formal derivative. That x is a unit modulo m is written ring_unit *)
(* (quotient_ring r m) (ring_coset r m x), equivalently x y - 1 IN m for     *)
(* some y; for m maximal it means that x is not in m, and it only depends on *)
(* the radical of m (RING_UNIT_QUOTIENT_RING_COSET,                          *)
(* RING_UNIT_QUOTIENT_RING_MAXIMAL, RING_UNIT_QUOTIENT_RING_RADICAL of       *)
(* Library/ringtheory.ml), so a unit modulo m is a unit modulo every m^n     *)
(* with n >= 1 (RING_UNIT_QUOTIENT_RING_IDEAL_POW).                          *)
(*                                                                           *)
(* Main results. Simple roots lift: if f(a) IN m and f1(a) is a unit modulo  *)
(* m, then for every k some b = a mod m has f(b) IN m^k, and b is unique     *)
(* modulo m^k among such elements (HENSEL_LEMMA_SIMPLE; with f(a) IN m^j     *)
(* also b = a mod m^j: HENSEL_LEMMA_POW; uniqueness: HENSEL_LEMMA_UNIQUE); a *)
(* Newton step doubles the precision (HENSEL_NEWTON_STEP_SIMPLE: f(a) IN m^k *)
(* gives b = a mod m^k with f(b) IN m^(2k)). Newton form: if f(a) = f1(a)^2  *)
(* s with s IN m, then for every k some b = a + f1(a) t with t IN m has f(b) *)
(* = f1(a)^2 s1 with s1 IN m^k (HENSEL_LEMMA_NEWTON). Both forms come from   *)
(* one general lemma, for f(a) = d^2 s with s IN m^j and f1(a) = d u with u  *)
(* a unit modulo m (HENSEL_LEMMA, from the step HENSEL_NEWTON_STEP). Roots   *)
(* congruent modulo m are equal when the powers of m meet in 0               *)
(* (HENSEL_ROOT_UNIQUE). Power residues: if n and a are units modulo m, then *)
(* a is an n-th power modulo m^k (k >= 1) iff it is one modulo m             *)
(* (POWER_RESIDUE_MODULO_IDEAL_POW). Factorizations lift: if f = g h mod m   *)
(* coefficientwise, the leading coefficient of g is a unit and s g + t h = 1 *)
(* mod m, then for every k there are G = g and H = h mod m, with G - g of    *)
(* degree below deg g, such that f = G H mod m^k                             *)
(* (HENSEL_LEMMA_FACTORIZATION, from the step HENSEL_FACTORIZATION_STEP).    *)
(*                                                                           *)
(* The integer case, with congruences modulo the powers of an integer n:     *)
(* HENSEL_LEMMA_INTEGER; power residues modulo n^k                           *)
(* (INT_POWER_RESIDUE_MODULO_POWER, for d = 2 and n odd the squares modulo   *)
(* the powers of n; an integer form proved from the Hensel lemma, the num    *)
(* form is QUADRATIC_RESIDUE_MODULO_ODD_POWER of Library/primitive.ml). The  *)
(* squares modulo 2^k are INT_QUADRATIC_RESIDUE_MODULO_POWER_2 of            *)
(* Library/primitive.ml.                                                     *)
(*                                                                           *)
(* Auxiliary results: the values of X^n - c and of its derivative            *)
(* (POLY_EVAL_DERIV_VAR_POW_SUB_CONST); integer_ring bridges                 *)
(* (INTEGER_RING_IDEAL_POW_SING, RING_UNIT_QUOTIENT_INTEGER_RING); products  *)
(* of polynomials with coefficients in powers of an ideal                    *)
(* (COEFF_POLY_MUL_IN_IDEAL_POW).                                            *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (poly_eval, poly_deriv, quotient rings,       *)
(* integer_ring; units modulo an ideal: RING_UNIT_QUOTIENT_RING_COSET,       *)
(* RING_UNIT_QUOTIENT_RING_COSET_MUL, RING_UNIT_QUOTIENT_RING_COSET_POW,     *)
(* RING_UNIT_QUOTIENT_RING_RADICAL; POLY_EVAL_TAYLOR,                        *)
(* POLY_EVAL_SUB_IN_IDEAL, INTEGER_RING_SUB, RING_IDEAL_POLY_COEFF,          *)
(* POLY_DIVISION_COEFF_IDEAL) and ANT/ideal_arith.ml (ideal_pow).            *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "ANT/ideal_arith.ml";;

(* ------------------------------------------------------------------------- *)
(* A unit modulo an ideal j (x y - 1 IN j for some y) is a unit modulo every *)
(* positive power of j.                                                      *)
(* ------------------------------------------------------------------------- *)

let RING_UNIT_QUOTIENT_RING_IDEAL_POW = prove
 (`!r j n x:A.
        ring_ideal r j /\ ~(n = 0) /\ x IN ring_carrier r
        ==> (ring_unit (quotient_ring r (ideal_pow r j n))
                       (ring_coset r (ideal_pow r j n) x) <=>
             ring_unit (quotient_ring r j) (ring_coset r j x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_pow r j n:A->bool`; `x:A`]
    RING_UNIT_QUOTIENT_RING_RADICAL) THEN
  MP_TAC(ISPECL [`r:A ring`; `j:A->bool`; `x:A`]
    RING_UNIT_QUOTIENT_RING_RADICAL) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RADICAL_IDEAL_POW] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Newton step. If f(b) = d^2 s with s IN m^i and f1(b) = d u with u a   *)
(* unit modulo m, then b1 = b + d t with t IN m^i has f(b1) = d^2 s1 with s1 *)
(* IN m^(2i) and f1(b1) = d u1 with u1 = u mod m^i.                          *)
(* ------------------------------------------------------------------------- *)

let HENSEL_NEWTON_STEP = prove
 (`!r m f (b:A) d u s i.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        b IN ring_carrier r /\ d IN ring_carrier r /\ u IN ring_carrier r /\
        s IN ideal_pow r m i /\
        poly_eval r f b = ring_mul r (ring_pow r d 2) s /\
        poly_eval r (poly_deriv r f) b = ring_mul r d u /\
        ring_unit (quotient_ring r m) (ring_coset r m u)
        ==> ?t u' s'.
                t IN ideal_pow r m i /\ u' IN ring_carrier r /\
                ring_sub r u' u IN ideal_pow r m i /\
                s' IN ideal_pow r m (2 * i) /\
                poly_eval r f (ring_add r b (ring_mul r d t)) =
                ring_mul r (ring_pow r d 2) s' /\
                poly_eval r (poly_deriv r f) (ring_add r b (ring_mul r d t)) =
                ring_mul r d u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:A->bool) SUBSET ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?v:A. v IN ring_carrier r /\
          ring_sub r (ring_mul r u v) (ring_1 r) IN ideal_pow r m i`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `i = 0` THENL
     [EXISTS_TAC `ring_1 r:A` THEN
      ASM_SIMP_TAC[IDEAL_POW_0; RING_SUB; RING_MUL; RING_1];
      ASM_MESON_TAC[RING_UNIT_QUOTIENT_RING_COSET;
                    RING_UNIT_QUOTIENT_RING_IDEAL_POW; RING_IDEAL_IDEAL_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_neg r (ring_mul r s v) IN ideal_pow r m i /\
    ring_neg r (ring_mul r s v:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_NEG; RING_MUL] THEN
    ASM_SIMP_TAC[IN_RING_IDEAL_NEG; IN_RING_IDEAL_RMUL; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  ABBREV_TAC `t0 = ring_neg r (ring_mul r s v):A` THEN
  MP_TAC(ISPECL [`r:A ring`; `f:(1->num)->A`; `b:A`; `ring_mul r d t0:A`]
    POLY_EVAL_TAYLOR) THEN
  MP_TAC(ISPECL [`r:A ring`; `poly_deriv r f:(1->num)->A`; `b:A`;
                 `ring_mul r d t0:A`] POLY_EVAL_TAYLOR) THEN
  ASM_SIMP_TAC[POLY_DERIV_IN_CARRIER; RING_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':A` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `c = poly_eval r (poly_deriv r (poly_deriv r f)) (b:A)` THEN
  SUBGOAL_THEN `(c:A) IN ring_carrier r` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[POLY_EVAL]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`t0:A`;
    `ring_add r u (ring_add r (ring_mul r c t0)
                     (ring_mul r (ring_mul r d (ring_mul r t0 t0)) g')):A`;
    `ring_add r
      (ring_neg r (ring_mul r s (ring_sub r (ring_mul r u v) (ring_1 r))))
      (ring_mul r (ring_mul r t0 t0) g):A`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [RING_CARRIER_TAC;
    SUBGOAL_THEN
     `ring_sub r
       (ring_add r u (ring_add r (ring_mul r c t0)
                       (ring_mul r (ring_mul r d (ring_mul r t0 t0)) g')))
       u:A =
      ring_add r (ring_mul r c t0)
                 (ring_mul r (ring_mul r d (ring_mul r t0 t0)) g')`
    SUBST1_TAC THENL
     [W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[RING_MUL];
      ALL_TAC] THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[IN_RING_IDEAL_LMUL; RING_IDEAL_IDEAL_POW];
      MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
      ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; IN_RING_IDEAL_RMUL]];
    REWRITE_TAC[ARITH_RULE `2 * i = i + i`] THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_IDEAL_NEG THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC[]];
    UNDISCH_TAC `ring_neg r (ring_mul r s v):A = t0` THEN
    W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[RING_MUL];
    W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[RING_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* The general lifting lemma. If f(a) = d^2 s with s IN m^j (j >= 1) and     *)
(* f1(a) = d u with u a unit modulo m, then for every k some b = a + d t     *)
(* with t IN m^j has f(b) = d^2 s1 with s1 IN m^k. With d = 1 this is the    *)
(* usual form (f1(a) a unit modulo m), with u = 1 the Newton form (f(a) IN   *)
(* f1(a)^2 m).                                                               *)
(* ------------------------------------------------------------------------- *)

let HENSEL_LEMMA = prove
 (`!r m f (a:A) d u s j k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ d IN ring_carrier r /\ u IN ring_carrier r /\
        ~(j = 0) /\ s IN ideal_pow r m j /\
        poly_eval r f a = ring_mul r (ring_pow r d 2) s /\
        poly_eval r (poly_deriv r f) a = ring_mul r d u /\
        ring_unit (quotient_ring r m) (ring_coset r m u)
        ==> ?t s'. t IN ideal_pow r m j /\ s' IN ideal_pow r m k /\
                   poly_eval r f (ring_add r a (ring_mul r d t)) =
                   ring_mul r (ring_pow r d 2) s'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(m:A->bool) SUBSET ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?t u' s'.
        t IN ideal_pow r m j /\ u' IN ring_carrier r /\
        ring_unit (quotient_ring r m) (ring_coset r m u') /\
        s' IN ideal_pow r m (j + n) /\
        poly_eval r f (ring_add r a (ring_mul r d t)) =
        ring_mul r (ring_pow r d 2) s' /\
        poly_eval r (poly_deriv r f) (ring_add r a (ring_mul r d t)) =
        ring_mul r d (u':A)`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:A`; `u':A`; `s':A`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:A`; `s':A`] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `k:num`; `j + k:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_REWRITE_TAC[LE_ADDR; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]] THEN
  INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`ring_0 r:A`; `u:A`; `s:A`] THEN
    ASM_SIMP_TAC[ADD_CLAUSES; RING_MUL_RZERO; RING_ADD_RZERO;
                 IN_RING_IDEAL_0; RING_IDEAL_IDEAL_POW];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:A` (X_CHOOSE_THEN `v:A`
    (X_CHOOSE_THEN `w:A` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `f:(1->num)->A`;
                 `ring_add r a (ring_mul r d t):A`; `d:A`; `v:A`; `w:A`;
                 `j + n:num`] HENSEL_NEWTON_STEP) THEN
  ASM_SIMP_TAC[RING_ADD; RING_MUL] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t':A`; `v':A`; `w':A`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ring_add r t t':A`; `v':A`; `w':A`] THEN
  SUBGOAL_THEN `(t':A) IN ring_carrier r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_add r a (ring_mul r d (ring_add r t t')):A =
    ring_add r (ring_add r a (ring_mul r d t)) (ring_mul r d t')`
  SUBST1_TAC THENL
   [W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_RING_IDEAL_ADD THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `j:num`; `j + n:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_REWRITE_TAC[LE_ADD; SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `v':A`; `v:A`]
      RING_UNIT_QUOTIENT_RING_COSET_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `1`; `j + n:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `j + SUC n`; `2 * (j + n)`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_ARITH_TAC;
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The usual forms: f(a) IN m^k and f1(a) a unit modulo m. The Newton step   *)
(* doubles the precision; a root modulo m^j lifts to roots modulo all m^k,   *)
(* congruent to it modulo m^j, and the lift is unique modulo m^k. The Newton *)
(* form; roots in rings where the powers of m meet in 0.                     *)
(* ------------------------------------------------------------------------- *)

let HENSEL_NEWTON_STEP_SIMPLE = prove
 (`!r m f (a:A) k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ poly_eval r f a IN ideal_pow r m k /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) a))
        ==> ?b. b IN ring_carrier r /\ ring_sub r b a IN ideal_pow r m k /\
                poly_eval r f b IN ideal_pow r m (2 * k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`r:A ring`; `m:A->bool`; `f:(1->num)->A`; `a:A`; `ring_1 r:A`;
    `poly_eval r (poly_deriv r f) (a:A)`; `poly_eval r f (a:A)`; `k:num`]
   HENSEL_NEWTON_STEP) THEN
  ASM_SIMP_TAC[RING_1; POLY_EVAL; RING_POW_ONE; RING_MUL_LID] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:A`; `u:A`; `s:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_add r a (ring_mul r (ring_1 r) t):A` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r /\ (s:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW; SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_ADD; RING_1;
               RING_RULE `ring_sub r (ring_add r a t) a:A = t`]);;

let HENSEL_LEMMA_POW = prove
 (`!r m f (a:A) j k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ ~(j = 0) /\
        poly_eval r f a IN ideal_pow r m j /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) a))
        ==> ?b. b IN ring_carrier r /\ ring_sub r b a IN ideal_pow r m j /\
                poly_eval r f b IN ideal_pow r m k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`r:A ring`; `m:A->bool`; `f:(1->num)->A`; `a:A`; `ring_1 r:A`;
    `poly_eval r (poly_deriv r f) (a:A)`; `poly_eval r f (a:A)`;
    `j:num`; `k:num`] HENSEL_LEMMA) THEN
  ASM_SIMP_TAC[RING_1; POLY_EVAL; RING_POW_ONE; RING_MUL_LID] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:A`; `s:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `ring_add r a (ring_mul r (ring_1 r) t):A` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:A) IN ring_carrier r /\ (s:A) IN ring_carrier r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_IDEAL_IMP_SUBSET; RING_IDEAL_IDEAL_POW; SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_ADD; RING_1;
               RING_RULE `ring_sub r (ring_add r a t) a:A = t`]);;

let HENSEL_LEMMA_UNIQUE = prove
 (`!r m f (b:A) c k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        b IN ring_carrier r /\ c IN ring_carrier r /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) b)) /\
        ring_sub r b c IN m /\
        poly_eval r f b IN ideal_pow r m k /\
        poly_eval r f c IN ideal_pow r m k
        ==> ring_sub r b c IN ideal_pow r m k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(m:A->bool) SUBSET ring_carrier r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `m:A->bool`;
                 `poly_eval r (poly_deriv r f) (b:A)`]
    RING_UNIT_QUOTIENT_RING_COSET) THEN
  ASM_REWRITE_TAC[POLY_EVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. i <= k ==> ring_sub r c (b:A) IN ideal_pow r m i`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN REWRITE_TAC[LE_REFL] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `ring_sub r b c = ring_neg r (ring_sub r c b):A`
    SUBST1_TAC THENL
     [W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[IN_RING_IDEAL_NEG; RING_IDEAL_IDEAL_POW]]] THEN
  INDUCT_TAC THENL [ASM_SIMP_TAC[IDEAL_POW_0; RING_SUB]; ALL_TAC] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  ASM_CASES_TAC `i = 0` THENL
   [ASM_SIMP_TAC[GSYM ONE; IDEAL_POW_1] THEN
    SUBGOAL_THEN `ring_sub r c b = ring_neg r (ring_sub r b c):A`
    SUBST1_TAC THENL
     [W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[IN_RING_IDEAL_NEG]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `f:(1->num)->A`; `b:A`; `ring_sub r c b:A`]
    POLY_EVAL_TAYLOR) THEN
  ASM_SIMP_TAC[RING_SUB;
               RING_RULE `ring_add r b (ring_sub r c b):A = c`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `ideal_pow r m k SUBSET ideal_pow r m (SUC i) /\
    ideal_pow r m (i + i) SUBSET ideal_pow r (m:A->bool) (SUC i)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IDEAL_POW_ANTIMONO THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r (ring_sub r (poly_eval r f c) (poly_eval r f b))
     (ring_mul r (ring_mul r (ring_sub r c b) (ring_sub r c b)) (g:A)) IN
    ideal_pow r m (SUC i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN
      REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN ASM SET_TAC[];
      MATCH_MP_TAC IN_RING_IDEAL_RMUL THEN
      ASM_REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
        check (fun th ->
          rand(concl th) = `ideal_pow r m (SUC i):A->bool` &&
          lhand(concl th) = `ideal_pow r m (i + i):A->bool`)) THEN
      MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub r c b:A =
    ring_sub r
     (ring_mul r u
       (ring_sub r (ring_sub r (poly_eval r f c) (poly_eval r f b))
         (ring_mul r (ring_mul r (ring_sub r c b) (ring_sub r c b)) g)))
     (ring_mul r
       (ring_sub r (ring_mul r (poly_eval r (poly_deriv r f) b) u)
                   (ring_1 r))
       (ring_sub r c b))`
  SUBST1_TAC THENL
   [UNDISCH_TAC
     `poly_eval r f c =
      ring_add r
       (ring_add r (poly_eval r f b)
         (ring_mul r (poly_eval r (poly_deriv r f) b) (ring_sub r c b)))
       (ring_mul r (ring_mul r (ring_sub r c b) (ring_sub r c b)) (g:A))` THEN
    W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[POLY_EVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[IN_RING_IDEAL_LMUL; RING_IDEAL_IDEAL_POW];
    REWRITE_TAC[ARITH_RULE `SUC i = 1 + i`] THEN
    MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
    ASM_SIMP_TAC[IDEAL_POW_1]]);;

let HENSEL_LEMMA_SIMPLE = prove
 (`!r m f (a:A) k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ poly_eval r f a IN m /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) a))
        ==> (?b. b IN ring_carrier r /\ ring_sub r b a IN m /\
                 poly_eval r f b IN ideal_pow r m k) /\
            (!b c. b IN ring_carrier r /\ c IN ring_carrier r /\
                   ring_sub r b a IN m /\ ring_sub r c a IN m /\
                   poly_eval r f b IN ideal_pow r m k /\
                   poly_eval r f c IN ideal_pow r m k
                   ==> ring_sub r b c IN ideal_pow r m k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `f:(1->num)->A`; `a:A`;
                   `1`; `k:num`] HENSEL_LEMMA_POW) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; ARITH_EQ];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC HENSEL_LEMMA_UNIQUE THEN
    EXISTS_TAC `f:(1->num)->A` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`r:A ring`; `m:A->bool`;
                     `poly_eval r (poly_deriv r f) (b:A)`;
                     `poly_eval r (poly_deriv r f) (a:A)`]
        RING_UNIT_QUOTIENT_RING_COSET_EQ) THEN
      ASM_REWRITE_TAC[POLY_EVAL] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC POLY_EVAL_SUB_IN_IDEAL THEN
      ASM_SIMP_TAC[POLY_DERIV_IN_CARRIER];
      SUBGOAL_THEN
       `ring_sub r b c = ring_sub r (ring_sub r b a) (ring_sub r c a):A`
      SUBST1_TAC THENL
       [W(fun (_,w) -> MP_TAC(RING_RULE w)) THEN ASM_SIMP_TAC[];
        ASM_SIMP_TAC[IN_RING_IDEAL_SUB]]]]);;

let HENSEL_LEMMA_NEWTON = prove
 (`!r m f (a:A) s k.
        ring_ideal r m /\ f IN ring_carrier(poly_ring r (:1)) /\
        a IN ring_carrier r /\ s IN m /\
        poly_eval r f a =
        ring_mul r (ring_pow r (poly_eval r (poly_deriv r f) a) 2) s
        ==> ?t s'. t IN m /\ s' IN ideal_pow r m k /\
                   poly_eval r f
                    (ring_add r a
                      (ring_mul r (poly_eval r (poly_deriv r f) a) t)) =
                   ring_mul r (ring_pow r (poly_eval r (poly_deriv r f) a) 2)
                              s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`r:A ring`; `m:A->bool`; `f:(1->num)->A`; `a:A`;
    `poly_eval r (poly_deriv r f) (a:A)`; `ring_1 r:A`; `s:A`;
    `1`; `k:num`] HENSEL_LEMMA) THEN
  ASM_SIMP_TAC[IDEAL_POW_1; ARITH_EQ; RING_1; POLY_EVAL; RING_MUL_RID] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[RING_UNIT_QUOTIENT_RING_COSET; RING_1] THEN
  EXISTS_TAC `ring_1 r:A` THEN
  ASM_SIMP_TAC[RING_MUL_LID; RING_1; RING_SUB_REFL; IN_RING_IDEAL_0]);;

let HENSEL_ROOT_UNIQUE = prove
 (`!r m f (b:A) c.
        ring_ideal r m /\
        (!x. (!k. x IN ideal_pow r m k) ==> x = ring_0 r) /\
        f IN ring_carrier(poly_ring r (:1)) /\
        b IN ring_carrier r /\ c IN ring_carrier r /\
        ring_unit (quotient_ring r m)
                  (ring_coset r m (poly_eval r (poly_deriv r f) b)) /\
        ring_sub r b c IN m /\
        poly_eval r f b = ring_0 r /\ poly_eval r f c = ring_0 r
        ==> b = c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `b:A`; `c:A`] RING_SUB_EQ_0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  X_GEN_TAC `k:num` THEN MATCH_MP_TAC HENSEL_LEMMA_UNIQUE THEN
  EXISTS_TAC `f:(1->num)->A` THEN
  ASM_SIMP_TAC[IN_RING_IDEAL_0; RING_IDEAL_IDEAL_POW]);;

(* ------------------------------------------------------------------------- *)
(* Power residues: if n and a are units modulo m, then a is an n-th power    *)
(* modulo m^k (k >= 1) iff it is one modulo m.                               *)
(* ------------------------------------------------------------------------- *)

let POLY_EVAL_DERIV_VAR_POW_SUB_CONST = prove
 (`!r n c:A.
        c IN ring_carrier r
        ==> poly_sub r (poly_pow r (poly_var r one) n) (poly_const r c) IN
            ring_carrier(poly_ring r (:1)) /\
            !x. x IN ring_carrier r
                ==> poly_eval r (poly_sub r (poly_pow r (poly_var r one) n)
                                            (poly_const r c)) x =
                    ring_sub r (ring_pow r x n) c /\
                    poly_eval r (poly_deriv r
                                  (poly_sub r (poly_pow r (poly_var r one) n)
                                              (poly_const r c))) x =
                    ring_mul r (ring_of_num r n) (ring_pow r x (n - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM RING_POLYNOMIAL] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW;
                 RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_CONST];
    GEN_TAC THEN DISCH_TAC] THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_SUB; RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
               RING_POLYNOMIAL_CONST; POLY_EVAL_SUB; POLY_EVAL_POW;
               POLY_EVAL_VAR; POLY_EVAL_CONST] THEN
  ASM_SIMP_TAC[POLY_DERIV_SUB; RING_POLYNOMIAL_IMP_POWERSERIES;
               RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR;
               RING_POLYNOMIAL_CONST; POLY_DERIV_VAR_POW; POLY_DERIV_CONST] THEN
  ASM_SIMP_TAC[POLY_EVAL_SUB; RING_POLYNOMIAL_MUL; RING_POLYNOMIAL_CONST;
               RING_POLYNOMIAL_POW; RING_POLYNOMIAL_VAR; RING_POLYNOMIAL_0;
               RING_OF_NUM; POLY_EVAL_MUL; POLY_EVAL_CONST; POLY_EVAL_POW;
               POLY_EVAL_VAR; POLY_EVAL_0; RING_SUB_RZERO; RING_MUL;
               RING_POW]);;

let POWER_RESIDUE_MODULO_IDEAL_POW = prove
 (`!r m n (a:A) k.
        ring_ideal r m /\ a IN ring_carrier r /\
        ring_unit (quotient_ring r m) (ring_coset r m (ring_of_num r n)) /\
        ring_unit (quotient_ring r m) (ring_coset r m a)
        ==> ((?x. x IN ring_carrier r /\
                  ring_sub r (ring_pow r x n) a IN ideal_pow r m k) <=>
             k = 0 \/
             (?x. x IN ring_carrier r /\ ring_sub r (ring_pow r x n) a IN m))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[IDEAL_POW_0] THEN EXISTS_TAC `ring_0 r:A` THEN
    ASM_SIMP_TAC[RING_SUB; RING_POW; RING_0];
    ASM_REWRITE_TAC[]] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `1`; `k:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET; LE_1] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`r:A ring`; `m:A->bool`;
    `poly_sub r (poly_pow r (poly_var r one) n) (poly_const r (a:A))`;
    `x:A`; `k:num`] HENSEL_LEMMA_SIMPLE) THEN
  ASM_SIMP_TAC[POLY_EVAL_DERIV_VAR_POW_SUB_CONST] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `y:A` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `y:A` THEN
    UNDISCH_TAC
     `poly_eval r (poly_sub r (poly_pow r (poly_var r one) n)
                             (poly_const r a)) (y:A) IN ideal_pow r m k` THEN
    ASM_SIMP_TAC[POLY_EVAL_DERIV_VAR_POW_SUB_CONST]] THEN
  ASM_SIMP_TAC[RING_UNIT_QUOTIENT_RING_COSET_MUL; RING_OF_NUM; RING_POW;
               RING_UNIT_QUOTIENT_RING_COSET_POW] THEN
  SUBGOAL_THEN
   `ring_unit (quotient_ring r m) (ring_coset r m (ring_pow r (x:A) n))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `ring_pow r x n:A`; `a:A`]
      RING_UNIT_QUOTIENT_RING_COSET_EQ) THEN
    ASM_SIMP_TAC[RING_POW];
    ASM_SIMP_TAC[RING_UNIT_QUOTIENT_RING_COSET_POW] THEN
    MESON_TAC[ARITH_RULE `n = 0 ==> n - 1 = 0`]]);;

(* ------------------------------------------------------------------------- *)
(* The integer case: congruences modulo the powers of an integer n.          *)
(* ------------------------------------------------------------------------- *)

let INTEGER_RING_IDEAL_POW_SING = prove
 (`!n k. ideal_pow integer_ring (ideal_generated integer_ring {n}) k =
         {x | n pow k divides x}`,
  SIMP_TAC[IDEAL_POW_PRINCIPAL; INTEGER_RING; IN_UNIV; INTEGER_RING_POW;
           INTEGER_RING_IDEAL_GENERATED_SING]);;

let RING_UNIT_QUOTIENT_INTEGER_RING = prove
 (`!n x. ring_unit
          (quotient_ring integer_ring (ideal_generated integer_ring {n}))
          (ring_coset integer_ring (ideal_generated integer_ring {n}) x) <=>
         coprime(x,n)`,
  SIMP_TAC[RING_UNIT_QUOTIENT_RING_COSET; RING_IDEAL_IDEAL_GENERATED;
           INTEGER_RING; IN_UNIV; INTEGER_RING_IDEAL_GENERATED_SING;
           IN_ELIM_THM; INTEGER_RING_SUB] THEN
  INTEGER_TAC);;

let HENSEL_LEMMA_INTEGER = prove
 (`!f (n:int) a k.
        f IN ring_carrier(poly_ring integer_ring (:1)) /\
        (poly_eval integer_ring f a == &0) (mod n) /\
        coprime(poly_eval integer_ring (poly_deriv integer_ring f) a,n)
        ==> (?b. (b == a) (mod n) /\
                 (poly_eval integer_ring f b == &0) (mod (n pow k))) /\
            (!b c. (b == a) (mod n) /\ (c == a) (mod n) /\
                   (poly_eval integer_ring f b == &0) (mod (n pow k)) /\
                   (poly_eval integer_ring f c == &0) (mod (n pow k))
                   ==> (b == c) (mod (n pow k)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong; int_mod; INT_SUB_RZERO] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `ideal_generated integer_ring {n:int}`;
                 `f:(1->num)->int`; `a:int`; `k:num`] HENSEL_LEMMA_SIMPLE) THEN
  ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; RING_UNIT_QUOTIENT_INTEGER_RING;
                  INTEGER_RING_IDEAL_POW_SING;
                  INTEGER_RING_IDEAL_GENERATED_SING;
                  INTEGER_RING; IN_UNIV; IN_ELIM_THM; INTEGER_RING_SUB]);;

let INT_POWER_RESIDUE_MODULO_POWER = prove
 (`!n:int d a k.
        coprime(&d,n) /\ coprime(n,a)
        ==> ((?x. (x pow d == a) (mod (n pow k))) <=>
             k = 0 \/ ?x. (x pow d == a) (mod n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `ideal_generated integer_ring {n:int}`;
                 `d:num`; `a:int`; `k:num`] POWER_RESIDUE_MODULO_IDEAL_POW) THEN
  REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED; RING_UNIT_QUOTIENT_INTEGER_RING;
              INTEGER_RING_IDEAL_POW_SING; INTEGER_RING_IDEAL_GENERATED_SING;
              INTEGER_RING; IN_UNIV; IN_ELIM_THM; INTEGER_RING_SUB;
              INTEGER_RING_OF_NUM; INTEGER_RING_POW] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INTEGER_RULE `!a b:int. coprime(a,b) <=> coprime(b,a)`];
    REWRITE_TAC[cong; int_mod]]);;

(* ------------------------------------------------------------------------- *)
(* Products of polynomials with coefficients in powers of an ideal: the      *)
(* powers multiply coefficientwise.                                          *)
(* ------------------------------------------------------------------------- *)

let COEFF_POLY_MUL_IN_IDEAL_POW = prove
 (`!r m (p:(1->num)->A) q a b i.
        ring_ideal r m /\
        (!i. coeff i p IN ideal_pow r m a) /\
        (!i. coeff i q IN ideal_pow r m b)
        ==> coeff i (poly_mul r p q) IN ideal_pow r m (a + b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COEFF_POLY_MUL] THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUM THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_MUL_IN_IDEAL_POW THEN
  ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Hensel lemma for factorizations. If f = g h mod m coefficientwise, the    *)
(* leading coefficient of g is a unit and s g + t h = 1 mod m, then for      *)
(* every k there are G = g, H = h mod m with G - g of degree < deg g and     *)
(* f = G H mod m^k. The step lifts a factorization modulo m^k to one modulo  *)
(* m^(k+1), dividing t (f - G H) by g.                                       *)
(* ------------------------------------------------------------------------- *)

let HENSEL_FACTORIZATION_STEP = prove
 (`!r m f g s t G H k.
        ring_ideal r m /\ ~(k = 0) /\
        f IN ring_carrier(poly_ring r (:1)) /\
        g IN ring_carrier(poly_ring r (:1)) /\
        s IN ring_carrier(poly_ring r (:1)) /\
        t IN ring_carrier(poly_ring r (:1)) /\
        G IN ring_carrier(poly_ring r (:1)) /\
        H IN ring_carrier(poly_ring r (:1)) /\
        ring_unit r (coeff (poly_deg r g) g) /\
        (!i. coeff i (ring_sub (poly_ring r (:1))
                       (ring_add (poly_ring r (:1))
                         (ring_mul (poly_ring r (:1)) s G)
                         (ring_mul (poly_ring r (:1)) t H))
                       (ring_1 (poly_ring r (:1)))) IN m) /\
        (!i. coeff i (ring_sub (poly_ring r (:1)) G g) IN m) /\
        (!i. coeff i (ring_sub (poly_ring r (:1)) f
                       (ring_mul (poly_ring r (:1)) G H)) IN ideal_pow r m k)
        ==> ?G' H'.
              G' IN ring_carrier(poly_ring r (:1)) /\
              H' IN ring_carrier(poly_ring r (:1)) /\
              (!i. coeff i (ring_sub (poly_ring r (:1)) G' G)
                   IN ideal_pow r m k) /\
              (!i. coeff i (ring_sub (poly_ring r (:1)) H' H)
                   IN ideal_pow r m k) /\
              (!i. poly_deg r g <= i ==> coeff i G' = coeff i G) /\
              (!i. coeff i (ring_sub (poly_ring r (:1)) f
                             (ring_mul (poly_ring r (:1)) G' H'))
                   IN ideal_pow r (m:A->bool) (k + 1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_sub (poly_ring r (:1)) f (ring_mul (poly_ring r (:1)) G H)
    IN ring_carrier(poly_ring r (:1)):((1->num)->A)->bool`
  ASSUME_TAC THENL [ASM_SIMP_TAC[RING_SUB; RING_MUL]; ALL_TAC] THEN
  ABBREV_TAC
   `w = ring_sub (poly_ring r (:1)) f
         (ring_mul (poly_ring r (:1)) G H):(1->num)->A` THEN
  SUBGOAL_THEN
   `!p:(1->num)->A. p IN ring_carrier(poly_ring r (:1))
                    ==> !i. coeff i p IN ideal_pow r m 0`
  (LABEL_TAC "car") THENL
   [REWRITE_TAC[IDEAL_POW_0] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN ASM_REWRITE_TAC[RING_POLYNOMIAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q:(1->num)->A a b i.
        (!j. coeff j p IN ideal_pow r m a) /\
        (!j. coeff j q IN ideal_pow r m b)
        ==> coeff i (ring_mul (poly_ring r (:1)) p q) IN
            ideal_pow r m (a + b)`
  (LABEL_TAC "mul") THENL
   [REWRITE_TAC[POLY_RING_CLAUSES] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC COEFF_POLY_MUL_IN_IDEAL_POW THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. coeff i (ring_mul (poly_ring r (:1)) t (w:(1->num)->A)) IN
        ideal_pow r m (0 + k)`
  MP_TAC THENL
   [GEN_TAC THEN USE_THEN "mul" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`r:A ring`; `ideal_pow r m k:A->bool`;
                 `ring_mul (poly_ring r (:1)) t w:(1->num)->A`;
                 `g:(1->num)->A`] POLY_DIVISION_COEFF_IDEAL) THEN
  ASM_SIMP_TAC[RING_IDEAL_IDEAL_POW; RING_MUL] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:(1->num)->A`; `dl:(1->num)->A`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`ring_add (poly_ring r (:1)) G dl:(1->num)->A`;
    `ring_add (poly_ring r (:1)) H
      (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s w)
                                   (ring_mul (poly_ring r (:1)) q H))
      :(1->num)->A`] THEN
  ASM_SIMP_TAC[RING_ADD; RING_MUL] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[RING_RULE
     `ring_sub R (ring_add R G dl) G = dl:(1->num)->A`];
    ASM_SIMP_TAC[RING_MUL; RING_RULE
     `ring_sub R (ring_add R H (ring_add R x y)) H =
      ring_add R x (y:(1->num)->A)`] THEN
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD] THEN GEN_TAC THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    REWRITE_TAC[POLY_CLAUSES] THEN CONJ_TAC THENL
     [SUBST1_TAC(ARITH_RULE `k = 0 + k`);
      SUBST1_TAC(ARITH_RULE `k = k + 0`)] THEN
    USE_THEN "mul" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD] THEN
    SUBGOAL_THEN `coeff i (dl:(1->num)->A) = ring_0 r` SUBST1_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [MATCH_MP_TAC COEFF_ABOVE_DEG THEN
        ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_0]];
      MATCH_MP_TAC RING_ADD_RZERO THEN MATCH_MP_TAC COEFF_IN_CARRIER_ALT THEN
      ASM_REWRITE_TAC[RING_POLYNOMIAL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_sub (poly_ring r (:1)) (f:(1->num)->A)
     (ring_mul (poly_ring r (:1)) (ring_add (poly_ring r (:1)) G dl)
       (ring_add (poly_ring r (:1)) H
         (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s w)
                                      (ring_mul (poly_ring r (:1)) q H)))) =
    ring_sub (poly_ring r (:1))
     (ring_sub (poly_ring r (:1))
       (ring_neg (poly_ring r (:1))
         (ring_mul (poly_ring r (:1))
           (ring_sub (poly_ring r (:1))
             (ring_add (poly_ring r (:1))
               (ring_mul (poly_ring r (:1)) s G)
               (ring_mul (poly_ring r (:1)) t H))
             (ring_1 (poly_ring r (:1)))) w))
       (ring_mul (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) q H)
                 (ring_sub (poly_ring r (:1)) G g)))
     (ring_mul (poly_ring r (:1)) dl
       (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s w)
                                    (ring_mul (poly_ring r (:1)) q H)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] (RING_RULE
     `ring_sub R f (ring_mul R G H) = w /\
      ring_add R (ring_mul R q g) dl = ring_mul R t w
      ==> ring_sub R f (ring_mul R (ring_add R G dl)
            (ring_add R H (ring_add R (ring_mul R s w) (ring_mul R q H)))) =
          ring_sub R
           (ring_sub R
             (ring_neg R (ring_mul R
               (ring_sub R (ring_add R (ring_mul R s G) (ring_mul R t H))
                           (ring_1 R)) w))
             (ring_mul R (ring_mul R q H) (ring_sub R G g)))
           (ring_mul R dl (ring_add R (ring_mul R s w)
                                      (ring_mul R q (H:(1->num)->A))))`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_SUB; COEFF_POLY_NEG] THEN
  REWRITE_TAC[POLY_CLAUSES] THEN GEN_TAC THEN
  MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC IN_RING_IDEAL_SUB THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IN_RING_IDEAL_NEG THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      USE_THEN "mul" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IDEAL_POW_1];
      USE_THEN "mul" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[IDEAL_POW_1] THEN
      SUBST1_TAC(ARITH_RULE `k = k + 0`) THEN GEN_TAC THEN
      USE_THEN "mul" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[]];
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `k + 1:num`; `k + k:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[SUBSET]] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    USE_THEN "mul" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD] THEN GEN_TAC THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN REWRITE_TAC[RING_IDEAL_IDEAL_POW] THEN
    REWRITE_TAC[POLY_CLAUSES] THEN CONJ_TAC THENL
     [SUBST1_TAC(ARITH_RULE `k = 0 + k`);
      SUBST1_TAC(ARITH_RULE `k = k + 0`)] THEN
    USE_THEN "mul" MATCH_MP_TAC THEN
    ASM_SIMP_TAC[]]);;

let HENSEL_LEMMA_FACTORIZATION = prove
 (`!r m f g h s t k.
        ring_ideal r m /\
        f IN ring_carrier(poly_ring r (:1)) /\
        g IN ring_carrier(poly_ring r (:1)) /\
        h IN ring_carrier(poly_ring r (:1)) /\
        s IN ring_carrier(poly_ring r (:1)) /\
        t IN ring_carrier(poly_ring r (:1)) /\
        ring_unit r (coeff (poly_deg r g) g) /\
        (!i. ring_sub r (coeff i f) (coeff i (poly_mul r g h)) IN m) /\
        (!i. ring_sub r (coeff i (poly_add r (poly_mul r s g)
                                             (poly_mul r t h)))
                        (coeff i (poly_1 r)) IN m)
        ==> ?G H. G IN ring_carrier(poly_ring r (:1)) /\
                  H IN ring_carrier(poly_ring r (:1)) /\
                  poly_deg r G = poly_deg r g /\
                  (!i. poly_deg r g <= i ==> coeff i G = coeff i g) /\
                  (!i. ring_sub r (coeff i G) (coeff i g) IN m) /\
                  (!i. ring_sub r (coeff i H) (coeff i h) IN m) /\
                  (!i. ring_sub r (coeff i f) (coeff i (poly_mul r G H)) IN
                       ideal_pow r (m:A->bool) k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM COEFF_POLY_SUB; POLY_CLAUSES] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`r:A ring`; `m:A->bool`] RING_IDEAL_POLY_COEFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "id") THEN
  SUBGOAL_THEN
   `!n p:(1->num)->A i.
        (!j. coeff j p IN ideal_pow r m (n + 1)) ==> coeff i p IN m`
  (LABEL_TAC "low") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `1`; `n + 1:num`]
      IDEAL_POW_ANTIMONO) THEN
    ASM_SIMP_TAC[IDEAL_POW_1; RING_IDEAL_IMP_SUBSET] THEN
    ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[SUBSET]] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ?G H:(1->num)->A.
              G IN ring_carrier(poly_ring r (:1)) /\
              H IN ring_carrier(poly_ring r (:1)) /\
              (!i. coeff i (ring_sub (poly_ring r (:1)) G g) IN m) /\
              (!i. coeff i (ring_sub (poly_ring r (:1)) H h) IN m) /\
              (!i. poly_deg r g <= i ==> coeff i G = coeff i g) /\
              (!i. coeff i (ring_sub (poly_ring r (:1)) f
                             (ring_mul (poly_ring r (:1)) G H)) IN
                   ideal_pow r m (n + 1))`
  MP_TAC THENL
   [INDUCT_TAC THENL
     [MAP_EVERY EXISTS_TAC [`g:(1->num)->A`; `h:(1->num)->A`] THEN
      ASM_SIMP_TAC[ADD_CLAUSES; IDEAL_POW_1; RING_SUB_REFL] THEN
      REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_0] THEN
      ASM_SIMP_TAC[IN_RING_IDEAL_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `G:(1->num)->A`
     (X_CHOOSE_THEN `H:(1->num)->A` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `f:(1->num)->A`;
                   `g:(1->num)->A`; `s:(1->num)->A`; `t:(1->num)->A`;
                   `G:(1->num)->A`; `H:(1->num)->A`; `n + 1:num`]
      HENSEL_FACTORIZATION_STEP) THEN
    ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN ANTS_TAC THENL
     [SUBGOAL_THEN
       `ring_sub (poly_ring r (:1))
         (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s G)
                                      (ring_mul (poly_ring r (:1)) t H))
         (ring_1 (poly_ring r (:1))) IN
        {p | p IN ring_carrier(poly_ring r (:1)) /\
             !i. coeff i p IN (m:A->bool)}`
      (fun th -> MP_TAC th THEN SIMP_TAC[IN_ELIM_THM]) THEN
      SUBGOAL_THEN
       `ring_sub (poly_ring r (:1))
         (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s G)
                                      (ring_mul (poly_ring r (:1)) t H))
         (ring_1 (poly_ring r (:1))) =
        ring_add (poly_ring r (:1))
         (ring_sub (poly_ring r (:1))
           (ring_add (poly_ring r (:1)) (ring_mul (poly_ring r (:1)) s g)
                                        (ring_mul (poly_ring r (:1)) t h))
           (ring_1 (poly_ring r (:1))))
         (ring_add (poly_ring r (:1))
           (ring_mul (poly_ring r (:1)) s (ring_sub (poly_ring r (:1)) G g))
           (ring_mul (poly_ring r (:1)) t
             (ring_sub (poly_ring r (:1)) H (h:(1->num)->A))))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_sub R (ring_add R (ring_mul R s G) (ring_mul R t H))
                     (ring_1 R) =
          ring_add R
           (ring_sub R (ring_add R (ring_mul R s g) (ring_mul R t h))
                       (ring_1 R))
           (ring_add R (ring_mul R s (ring_sub R G g))
                       (ring_mul R t (ring_sub R H (h:(1->num)->A))))`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_SIMP_TAC[RING_SUB; RING_ADD; RING_MUL; RING_1];
        MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THEN MATCH_MP_TAC IN_RING_IDEAL_LMUL THEN
        ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[RING_SUB]];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`G':(1->num)->A`; `H':(1->num)->A`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`G':(1->num)->A`; `H':(1->num)->A`] THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC n + 1 = (n + 1) + 1`] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THENL
     [SUBGOAL_THEN
       `ring_sub (poly_ring r (:1)) G' g =
        ring_add (poly_ring r (:1)) (ring_sub (poly_ring r (:1)) G' G)
                 (ring_sub (poly_ring r (:1)) G (g:(1->num)->A))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_sub R G' g =
          ring_add R (ring_sub R G' G) (ring_sub R G (g:(1->num)->A))`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC];
      SUBGOAL_THEN
       `ring_sub (poly_ring r (:1)) H' h =
        ring_add (poly_ring r (:1)) (ring_sub (poly_ring r (:1)) H' H)
                 (ring_sub (poly_ring r (:1)) H (h:(1->num)->A))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(RING_RULE
         `ring_sub R H' h =
          ring_add R (ring_sub R H' H) (ring_sub R H (h:(1->num)->A))`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC]] THEN
    REWRITE_TAC[POLY_RING_CLAUSES; COEFF_POLY_ADD] THEN
    REWRITE_TAC[POLY_CLAUSES] THEN
    MATCH_MP_TAC IN_RING_IDEAL_ADD THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "low" MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `G:(1->num)->A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `H:(1->num)->A` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN
      MP_TAC(ISPECL [`r:A ring`; `m:A->bool`; `k:num`; `k + 1:num`]
        IDEAL_POW_ANTIMONO) THEN
      ASM_SIMP_TAC[RING_IDEAL_IMP_SUBSET] THEN
      ANTS_TAC THENL [ARITH_TAC; REWRITE_TAC[SUBSET]] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `poly_deg r (G:(1->num)->A) <= poly_deg r (g:(1->num)->A)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[POLY_DEG_LE_COEFF_EQ; RING_POLYNOMIAL] THEN
      X_GEN_TAC `d:num` THEN REWRITE_TAC[GSYM NOT_LT; CONTRAPOS_THM] THEN
      DISCH_TAC THEN ASM_SIMP_TAC[LT_IMP_LE] THEN
      MATCH_MP_TAC COEFF_ABOVE_DEG THEN ASM_REWRITE_TAC[RING_POLYNOMIAL];
      ALL_TAC] THEN
    ASM_CASES_TAC `coeff (poly_deg r g) (g:(1->num)->A) = ring_0 r` THENL
     [SUBGOAL_THEN `poly_deg r (g:(1->num)->A) = 0` MP_TAC THENL
       [MP_TAC(ISPECL [`r:A ring`; `g:(1->num)->A`] POLY_TOP_EQ_0) THEN
        ASM_REWRITE_TAC[RING_POLYNOMIAL] THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[POLY_DEG_0];
        ASM_ARITH_TAC];
      MATCH_MP_TAC POLY_DEG_EQ_FROM_LE THEN
      ASM_SIMP_TAC[RING_POLYNOMIAL; LE_REFL]]]);;
