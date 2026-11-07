(* ========================================================================= *)
(* The S-unit descent in a number field inside C, for one root of            *)
(* c0 y^m = g(x)^k H(x) (for the superelliptic equations and the             *)
(* Schinzel-Tijdeman theorem).                                               *)
(*                                                                           *)
(* Purpose: theta = r 1 is a root of the monic irreducible integer           *)
(* polynomial g = c of nf_data n c r, H is an integer polynomial with        *)
(* H(theta) <> 0, and K = Q(theta) = subfield_generated complex_ring {r 1}.  *)
(* There are a finite set W of nonzero elements of K and an integer D >= 1   *)
(* such that for every solution of c0 y^m = g(x)^k H(x) in integers          *)
(* (y <> 0, m >= 1)                                                          *)
(*   (x - theta)^k = prod_{v IN W} v^(e v) * xi^m,   e v < m,  xi IN K,      *)
(* with D xi an algebraic integer (SCHINZEL_TIJDEMAN_ROOT_DESCENT). W and D  *)
(* do not depend on m, x, y: no class number power, no unit index, no        *)
(* fractional ideals. The same S-unit descent gives the descent              *)
(* NF_POWER_DESCENT of Baker/descent.ml.                                     *)
(*                                                                           *)
(* Route (dg is the derivative of g). (1) S0 = the nonzero primes P of O_K   *)
(* containing delta = c0 dg(theta) H(theta), a nonzero algebraic integer     *)
(* (theta is a simple root, NF_DATA_SIMPLE_ROOT); S0 is finite               *)
(* (COMPLEX_SUBFIELD_PRIMES_FINITE). (2)                                     *)
(* g(x) = (x - theta) (dg(theta) + (x - theta) q1) and                       *)
(* H(x) = H(theta) + (x - theta) q2 with q1, q2 in O_K (second order Taylor  *)
(* expansion over a subring of C, COMPLEX_POLY_TAYLOR_SUBRING). For P NOTIN  *)
(* S0 with x - theta in P neither factor is in P, so                         *)
(* k v_P(x - theta) = m v_P(y); hence m divides v_P((x - theta)^k) for all P *)
(* NOTIN S0. (3) The m-th power decomposition                                *)
(* NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION gives (x - theta)^k = u z^m with u  *)
(* an (S0 UNION t)-unit, t a fixed finite set of primes; (4)                 *)
(* S_UNIT_GROUP_GENERATORS_MOD_POW writes u as prod_{v IN W} v^(e v) times   *)
(* an m-th power, e v < m, W independent of m. (5) D = prod_{v IN W} b v     *)
(* with b v >= 1 an integer and b v / v integral, so that                    *)
(* D^m / prod_v v^(e v) = prod_v b v^(m - e v) (b v / v)^(e v) is integral   *)
(* for e v <= m (COMPLEX_SUBFIELD_POW_DENOMINATOR); then                     *)
(* (D xi)^m = (D^m / prod_v v^(e v)) (x - theta)^k is an algebraic integer,  *)
(* so D xi is one (ALGEBRAIC_INTEGER_POW_ROOT). Steps (3) to (5) hold in any *)
(* number field inside C and for any finite S0                               *)
(* (SCHINZEL_TIJDEMAN_SUNIT_DESCENT); (6) the ring operations of             *)
(* subfield_generated complex_ring s are those of C, and ring_product there  *)
(* is cproduct (COMPLEX_SUBFIELD_RING_PRODUCT of                             *)
(* Baker/ant_bridge_complex.ml).                                             *)
(*                                                                           *)
(* Main results: SCHINZEL_TIJDEMAN_ROOT_DESCENT (the descent used by         *)
(* Baker/schinzel_general.ml), SCHINZEL_TIJDEMAN_SUNIT_DESCENT (the general  *)
(* descent, also used by Baker/descent.ml),                                  *)
(* SCHINZEL_TIJDEMAN_VALUATION_DIVIDES (the valuation argument),             *)
(* COMPLEX_POLY_TAYLOR_SUBRING, COMPLEX_SUBFIELD_INTEGRAL_MULTIPLE,          *)
(* COMPLEX_SUBFIELD_POW_DENOMINATOR, COMPLEX_SUBFIELD_PRIMES_FINITE,         *)
(* COMPLEX_SUBFIELD_VALUATION_MUL, COMPLEX_SUBFIELD_VALUATION_POW,           *)
(* COMPLEX_SUBFIELD_VALUATION_INTEGRAL; for integer polynomials              *)
(* NF_DESCENT_VSUM_CX (sums of values), SUPERELL_DERIV_SHIFT (the formal     *)
(* derivative), NF_DATA_ROOT_1, NF_DATA_SIMPLE_ROOT (the roots of nf_data    *)
(* are simple).                                                              *)
(*                                                                           *)
(* Uses: ANT/sunits.ml (s_unit_group, S_UNIT_GROUP,                          *)
(* S_UNIT_GROUP_GENERATORS_MOD_POW, NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION),  *)
(* Baker/sharp_tools.ml (RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED),       *)
(* ANT/dedekind_valuation.ml (dedekind_valuation; v_P(x) is                  *)
(* dedekind_valuation (ring_of_integers K,K) I P x), ANT/nf_valuation.ml     *)
(* (NUMBER_FIELD_VALUATION_MUL, _POW, _RING_OF_INTEGERS, _PRIME_IDEAL,       *)
(* _FINITE), ANT/numfield.ml (NUMBER_FIELD_INTEGRAL_MULTIPLE,                *)
(* RING_OF_INTEGERS, RING_OF_INTEGERS_SUBSET), Multivariate/complex_ring.ml  *)
(* (complex_ring, COMPLEX_RING_OF_INT), Baker/ant_bridge_complex.ml          *)
(* (BRIDGE_NF_SUBRING_INTEGER, BRIDGE_NF_SUBRING_POLY,                       *)
(* BRIDGE_NF_SUBFIELD_CLOSED, BRIDGE_NF_GEN_IN,                              *)
(* COMPLEX_SUBFIELD_RING_PRODUCT), Baker/ant_bridge_nf.ml                    *)
(* (NF_DATA_NUMBER_FIELD), Baker/nf_defs.ml (NF_DATA_1_IN),                  *)
(* Baker/nf_order.ml (NF_DATA, NF_DATA_ROOT, NF_DATA_DEGREE,                 *)
(* NF_DERIV_REINDEX, NF_DATA_ALGEBRAIC_INTEGER), Baker/algint.ml             *)
(* (algebraic_integer, ALGEBRAIC_INTEGER_POW_ROOT and the closure lemmas,    *)
(* LE_1_SUC_EXISTS), Baker/lemmas.ml (COMPLEX_SUBRING_CLOSED),               *)
(* Baker/bounds.ml (PRODUCT_GE_1), 100/transcendence.ml                      *)
(* (complex_field_clauses).                                                  *)
(* ========================================================================= *)

needs "ANT/sunits.ml";;
needs "Baker/sharp_tools.ml";;
needs "Baker/ant_bridge_nf.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Integer polynomials at the roots of nf_data: values, the derivative,      *)
(* theta = r 1 is a simple root.                                             *)
(* ------------------------------------------------------------------------- *)

let NF_DESCENT_VSUM_CX = prove
 (`!(a:num->real) x N.
        vsum(0..N) (\i. Cx(a i) * Cx x pow i) =
        Cx(sum(0..N) (\i. a i * x pow i))`,
  REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; VSUM_CX]);;

let SUPERELL_DERIV_SHIFT = prove
 (`!N (a:num->real) (z:complex).
        vsum(0..N) (\i. Cx(a i) * Cx(&i) * z pow (i - 1)) =
        vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP VSUM_CLAUSES_LEFT (SPEC `N:num` LE_0)] THEN
  REWRITE_TAC[ADD_CLAUSES; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO;
              COMPLEX_ADD_LID] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let NF_DATA_ROOT_1 = prove
 (`!n c r. nf_data n c r ==> vsum(0..n) (\i. Cx(c i) * r 1 pow i) = Cx(&0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_DATA_ROOT THEN
  ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN ASM_MESON_TAC[NF_DATA]);;

let NF_DATA_SIMPLE_ROOT = prove
 (`!n c r k. nf_data n c r /\ k IN 1..n
             ==> ~(vsum(1..n) (\i. Cx(&i * c i) * r k pow (i - 1)) =
                   Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
                MATCH_MP LE_1_SUC_EXISTS) THEN
  REWRITE_TAC[GSYM SUPERELL_DERIV_SHIFT; NF_DERIV_REINDEX] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`SUC m`; `c:num->real`; `r:num->complex`; `k:num`;
                `\i. &(i + 1) * (c:num->real)(i + 1)`] NF_DATA_DEGREE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUC_SUB1; INTEGER_MUL; INTEGER_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  ASM_REWRITE_TAC[LT_SUC_LE; LE_REFL; GSYM ADD1; REAL_MUL_RID;
                  REAL_OF_NUM_EQ; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Number fields inside C: denominators.                                     *)
(* ------------------------------------------------------------------------- *)

(* The rational integer d of NUMBER_FIELD_INTEGRAL_MULTIPLE, squared.        *)

let COMPLEX_SUBFIELD_INTEGRAL_MULTIPLE = prove
 (`!s x. number_field(subfield_generated complex_ring s) /\
         x IN ring_carrier(subfield_generated complex_ring s)
         ==> ?d. integer d /\ &1 <= d /\ algebraic_integer(Cx d * x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring s`; `x:complex`]
    NUMBER_FIELD_INTEGRAL_MULTIPLE) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM;
                  RING_OF_INT_SUBFIELD_GENERATED; COMPLEX_RING_OF_INT;
                  CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `real_of_int d pow 2` THEN
  SIMP_TAC[INTEGER_POW; INTEGER_REAL_OF_INT] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
    ASM_REWRITE_TAC[INTEGER_REAL_OF_INT; GSYM int_of_num_th; GSYM int_eq];
    REWRITE_TAC[CX_POW; COMPLEX_POW_2; GSYM COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN
    ASM_SIMP_TAC[ALGEBRAIC_INTEGER_INTEGER; INTEGER_REAL_OF_INT]]);;

(* One integer B for a finite set W of nonzero elements of K:                *)
(* B^m / prod_v v^(e v) is an algebraic integer whenever e v <= m on W.      *)

let COMPLEX_SUBFIELD_POW_DENOMINATOR = prove
 (`!s W.
        number_field(subfield_generated complex_ring s) /\ FINITE W /\
        (!v. v IN W
             ==> v IN ring_carrier(subfield_generated complex_ring s) /\
                 ~(v = Cx(&0)))
        ==> ?B. integer B /\ &1 <= B /\
                !m e. (!v. v IN W ==> e v <= m)
                      ==> algebraic_integer
                           (Cx B pow m * inv(cproduct W (\v. v pow e v)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?b. !v. v IN W
            ==> integer(b v) /\ &1 <= b v /\
                algebraic_integer(Cx(b v) * inv v)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPLEX_SUBFIELD_INTEGRAL_MULTIPLE THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM COMPLEX_RING_INV] THEN
    MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD];
    ALL_TAC] THEN
  EXISTS_TAC `product W (b:complex->real)` THEN
  ASM_SIMP_TAC[INTEGER_PRODUCT; PRODUCT_GE_1] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `Cx(product W b) pow m * inv(cproduct W (\v. v pow e v)) =
    cproduct W (\v. Cx(b v) pow (m - e v) * (Cx(b v) * inv v) pow e v)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[CX_PRODUCT; GSYM CPRODUCT_POW; GSYM CPRODUCT_INV;
                 GSYM CPRODUCT_MUL] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_INV; COMPLEX_MUL_ASSOC;
                GSYM COMPLEX_POW_ADD] THEN
    ASM_SIMP_TAC[SUB_ADD];
    MATCH_MP_TAC ALGEBRAIC_INTEGER_CPRODUCT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN
    ASM_SIMP_TAC[ALGEBRAIC_INTEGER_POW; ALGEBRAIC_INTEGER_INTEGER]]);;

(* ------------------------------------------------------------------------- *)
(* Valuations of the elements of a number field inside C.                    *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_SUBFIELD_VALUATION_MUL = prove
 (`!s P x y.
        number_field(subfield_generated complex_ring s) /\
        prime_ideal (ring_of_integers(subfield_generated complex_ring s)) P /\
        ~(P = {Cx(&0)}) /\
        x IN ring_carrier(subfield_generated complex_ring s) /\
        ~(x = Cx(&0)) /\
        y IN ring_carrier(subfield_generated complex_ring s) /\
        ~(y = Cx(&0))
        ==> dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P
              (x * y) =
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P x +
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring s`; `P:complex->bool`;
                 `x:complex`; `y:complex`] NUMBER_FIELD_VALUATION_MUL) THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES]);;

let COMPLEX_SUBFIELD_VALUATION_POW = prove
 (`!s P x n.
        number_field(subfield_generated complex_ring s) /\
        prime_ideal (ring_of_integers(subfield_generated complex_ring s)) P /\
        ~(P = {Cx(&0)}) /\
        x IN ring_carrier(subfield_generated complex_ring s) /\
        ~(x = Cx(&0))
        ==> dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P
              (x pow n) =
            &n *
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring s`; `P:complex->bool`;
                 `x:complex`; `n:num`] NUMBER_FIELD_VALUATION_POW) THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED;
                  complex_field_clauses]);;

let COMPLEX_SUBFIELD_VALUATION_INTEGRAL = prove
 (`!s P x.
        number_field(subfield_generated complex_ring s) /\
        prime_ideal (ring_of_integers(subfield_generated complex_ring s)) P /\
        ~(P = {Cx(&0)}) /\
        x IN ring_carrier(ring_of_integers
                           (subfield_generated complex_ring s)) /\
        ~(x = Cx(&0))
        ==> &0 <= dedekind_valuation
                    (ring_of_integers(subfield_generated complex_ring s),
                     subfield_generated complex_ring s) I P x /\
            (dedekind_valuation
               (ring_of_integers(subfield_generated complex_ring s),
                subfield_generated complex_ring s) I P x =
             &0 <=> ~(x IN P))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring s`; `P:complex->bool`;
                 `x:complex`] NUMBER_FIELD_VALUATION_RING_OF_INTEGERS) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring s`; `P:complex->bool`;
                 `x:complex`] NUMBER_FIELD_VALUATION_PRIME_IDEAL) THEN
  ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_POS; INT_LT_LE] THEN MESON_TAC[]);;

(* Only finitely many nonzero primes of O_K contain a given nonzero          *)
(* algebraic integer z of K.                                                 *)

let COMPLEX_SUBFIELD_PRIMES_FINITE = prove
 (`!s z.
        number_field(subfield_generated complex_ring s) /\
        z IN ring_carrier(ring_of_integers
                           (subfield_generated complex_ring s)) /\
        ~(z = Cx(&0))
        ==> FINITE {P | prime_ideal (ring_of_integers
                                      (subfield_generated complex_ring s)) P /\
                        ~(P = {Cx(&0)}) /\ z IN P}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{P | prime_ideal (ring_of_integers(subfield_generated complex_ring s)) P /\
         ~(P = {ring_0(subfield_generated complex_ring s)}) /\
         ~(dedekind_valuation
             (ring_of_integers(subfield_generated complex_ring s),
              subfield_generated complex_ring s) I P z = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NUMBER_FIELD_VALUATION_FINITE THEN
    ASM_REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
    ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET];
    REWRITE_TAC[SUBSET; IN_ELIM_THM;
                CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
    X_GEN_TAC `P:complex->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`s:complex->bool`; `P:complex->bool`; `z:complex`]
      COMPLEX_SUBFIELD_VALUATION_INTEGRAL) THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Taylor expansion to second order over a subring of C:                     *)
(*   f(z) = f(w) + (z - w) (df(w) + (z - w) q),  q in the subring,           *)
(* df the derivative of f.                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POW_TAYLOR_SUBRING = prove
 (`!s z w N.
        s subring_of complex_ring /\ z IN s /\ w IN s
        ==> ?q. q IN s /\
                z pow SUC N =
                w pow SUC N +
                (z - w) * (Cx(&(SUC N)) * w pow N + (z - w) * q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED) THEN
  SUBGOAL_THEN `!n. Cx(&n) IN s` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD]; ALL_TAC] THEN
  SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[complex_pow; ARITH] THEN
    CONV_TAC COMPLEX_RING;
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:complex` STRIP_ASSUME_TAC)] THEN
  EXISTS_TAC `Cx(&(SUC N)) * w pow N + z * q` THEN ASM_SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[complex_pow] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC; CX_ADD; complex_pow] THEN
  CONV_TAC COMPLEX_RING);;

let COMPLEX_POLY_TAYLOR_SUBRING = prove
 (`!s (c:num->real) N z w.
        s subring_of complex_ring /\ (!i. integer(c i)) /\ z IN s /\ w IN s
        ==> vsum(1..N) (\i. Cx(&i * c i) * w pow (i - 1)) IN s /\
            ?q. q IN s /\
                vsum(0..N) (\i. Cx(c i) * z pow i) =
                vsum(0..N) (\i. Cx(c i) * w pow i) +
                (z - w) * (vsum(1..N) (\i. Cx(&i * c i) * w pow (i - 1)) +
                           (z - w) * q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED) THEN
  SUBGOAL_THEN `!x. integer x ==> Cx x IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[BRIDGE_NF_SUBRING_INTEGER];
    ALL_TAC] THEN
  SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THENL
   [SIMP_TAC[VSUM_TRIV_NUMSEG; VSUM_SING_NUMSEG; ARITH; COMPLEX_VEC_0] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[complex_pow] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `q:complex` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`s:complex->bool`; `z:complex`; `w:complex`; `N:num`]
    COMPLEX_POW_TAYLOR_SUBRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q':complex` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `1 <= SUC n`;
              SUC_SUB1] THEN
  SUBGOAL_THEN `Cx(&(SUC N) * c(SUC N)) IN s` ASSUME_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN EXISTS_TAC `q + Cx(c(SUC N)) * q'` THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The S-unit descent in a number field inside C.                            *)
(* ------------------------------------------------------------------------- *)

(* For a number field K inside C and a finite set S0 of primes: one finite   *)
(* set W of nonzero elements of K and one integer D such that every nonzero  *)
(* algebraic integer a of K with m dividing v_P(a) for all P NOTIN S0 is     *)
(* prod_{v IN W} v^(e v) xi^m with e v < m, xi IN K and D xi integral. The   *)
(* (S0 UNION t)-unit u of a = u z^m is reduced modulo m-th powers and the    *)
(* integrality of D xi comes from COMPLEX_SUBFIELD_POW_DENOMINATOR.          *)

let SCHINZEL_TIJDEMAN_SUNIT_DESCENT = prove
 (`!s S0.
        number_field(subfield_generated complex_ring s) /\ FINITE S0
        ==> ?W D. FINITE W /\
                  (!v. v IN W
                       ==> v IN ring_carrier
                                 (subfield_generated complex_ring s) /\
                           ~(v = Cx(&0))) /\
                  integer D /\ &1 <= D /\
                  !m a. 1 <= m /\
                        a IN ring_carrier(subfield_generated complex_ring s) /\
                        ~(a = Cx(&0)) /\ algebraic_integer a /\
                        (!P. prime_ideal
                              (ring_of_integers
                                (subfield_generated complex_ring s)) P /\
                             ~(P = {Cx(&0)}) /\ ~(P IN S0)
                             ==> &m divides
                                 dedekind_valuation
                                  (ring_of_integers
                                    (subfield_generated complex_ring s),
                                   subfield_generated complex_ring s) I P a)
                        ==> ?e xi. (!v. v IN W ==> e v < m) /\
                                   xi IN ring_carrier
                                          (subfield_generated complex_ring
                                            s) /\
                                   algebraic_integer(Cx D * xi) /\
                                   a = cproduct W (\v. v pow e v) * xi pow m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `t:(complex->bool)->bool` STRIP_ASSUME_TAC o
    MATCH_MP NUMBER_FIELD_POW_S_UNIT_DECOMPOSITION) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring s`;
                 `S0 UNION t:(complex->bool)->bool`]
    S_UNIT_GROUP_GENERATORS_MOD_POW) THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:complex->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!v. v IN W
        ==> v IN ring_carrier(subfield_generated complex_ring s) /\
            ~(v = Cx(&0))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `W SUBSET group_carrier(s_unit_group
                    (subfield_generated complex_ring s) (S0 UNION t))` THEN
    ASM_SIMP_TAC[S_UNIT_GROUP; SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:complex->bool`; `W:complex->bool`]
    COMPLEX_SUBFIELD_POW_DENOMINATOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B")))) THEN
  MAP_EVERY EXISTS_TAC [`W:complex->bool`; `B:real`] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:complex`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`S0:(complex->bool)->bool`; `m:num`; `a:complex`]) THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:complex` (X_CHOOSE_THEN `u:complex`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `u:complex`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
                    FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:complex->num` (X_CHOOSE_THEN `z:complex`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     SUBST1_TAC)))) THEN
  SUBGOAL_THEN `z IN ring_carrier(subfield_generated complex_ring s)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `z IN group_carrier(s_unit_group
                    (subfield_generated complex_ring s) (S0 UNION t))` THEN
    MP_TAC(ISPECL [`subfield_generated complex_ring s`;
                   `S0 UNION t:(complex->bool)->bool`] S_UNIT_GROUP) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:complex->bool`; `W:complex->bool`;
                 `\v:complex. v pow n v`] COMPLEX_SUBFIELD_RING_PRODUCT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[CONJUNCT2 SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED;
              complex_field_clauses] THEN
  DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[GSYM COMPLEX_MUL_ASSOC;
                                       GSYM COMPLEX_POW_MUL]) THEN
  MAP_EVERY EXISTS_TAC [`n:complex->num`; `z * y:complex`] THEN
  ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED] THEN
  MATCH_MP_TAC ALGEBRAIC_INTEGER_POW_ROOT THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(cproduct W (\v:complex. v pow n v) = Cx(&0))` MP_TAC THENL
   [ASM_SIMP_TAC[CPRODUCT_EQ_0; COMPLEX_POW_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `a = cproduct W (\v:complex. v pow n v) * (z * y) pow m` THEN
  REWRITE_TAC[IMP_IMP; COMPLEX_POW_MUL] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (COMPLEX_FIELD
   `a = w * z * y /\ ~(w = Cx(&0))
    ==> Cx B pow m * z * y = (Cx B pow m * inv w) * a`)) THEN
  MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "B" MATCH_MP_TAC THEN ASM_SIMP_TAC[LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The valuation argument: if b y^m = (a (d1 + a q1))^k (d2 + a q2) with     *)
(* everything integral and b d1 d2 NOTIN P, then m divides v_P(a^k).         *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_VALUATION_EQ = prove
 (`!s P b y a f g m k.
        number_field(subfield_generated complex_ring s) /\
        prime_ideal (ring_of_integers(subfield_generated complex_ring s)) P /\
        ~(P = {Cx(&0)}) /\
        b IN ring_carrier(subfield_generated complex_ring s) /\
        y IN ring_carrier(subfield_generated complex_ring s) /\
        a IN ring_carrier(subfield_generated complex_ring s) /\
        f IN ring_carrier(subfield_generated complex_ring s) /\
        g IN ring_carrier(subfield_generated complex_ring s) /\
        ~(b = Cx(&0)) /\ ~(y = Cx(&0)) /\ ~(a = Cx(&0)) /\
        ~(f = Cx(&0)) /\ ~(g = Cx(&0)) /\
        b * y pow m = (a * f) pow k * g
        ==> dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P b +
            &m *
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P y =
            &k *
            (dedekind_valuation
               (ring_of_integers(subfield_generated complex_ring s),
                subfield_generated complex_ring s) I P a +
             dedekind_valuation
               (ring_of_integers(subfield_generated complex_ring s),
                subfield_generated complex_ring s) I P f) +
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P g`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM
   `dedekind_valuation
      (ring_of_integers(subfield_generated complex_ring s),
       subfield_generated complex_ring s) I P`) THEN
  ASM_SIMP_TAC[COMPLEX_SUBFIELD_VALUATION_MUL; COMPLEX_SUBFIELD_VALUATION_POW;
               BRIDGE_NF_SUBFIELD_CLOSED; COMPLEX_POW_EQ_0; COMPLEX_ENTIRE]);;

(* If a NOTIN P then v_P(a) = 0; if a IN P then d1 + a q1, d2 + a q2 and b   *)
(* are not in P, so their valuations are 0 and k v_P(a) = m v_P(y).          *)

let SCHINZEL_TIJDEMAN_VALUATION_DIVIDES = prove
 (`!s P a b d1 d2 q1 q2 y m k.
        number_field(subfield_generated complex_ring s) /\
        prime_ideal (ring_of_integers(subfield_generated complex_ring s)) P /\
        ~(P = {Cx(&0)}) /\ 1 <= k /\
        {a, b, d1, d2, q1, q2} SUBSET
        ring_carrier(ring_of_integers(subfield_generated complex_ring s)) /\
        y IN ring_carrier(subfield_generated complex_ring s) /\
        ~(b = Cx(&0)) /\ ~(y = Cx(&0)) /\
        b * y pow m = (a * (d1 + a * q1)) pow k * (d2 + a * q2) /\
        ~(b * d1 * d2 IN P)
        ==> &m divides
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring s),
               subfield_generated complex_ring s) I P
             (a pow k)`,
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:complex->bool`
    RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED o
             CONJUNCT2) THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier(ring_of_integers
                           (subfield_generated complex_ring s))
        ==> z IN ring_carrier(subfield_generated complex_ring s)`
  ASSUME_TAC THENL [MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u v. u IN P /\ v IN P ==> u - v IN P) /\
    (!u v. u IN ring_carrier(ring_of_integers
                               (subfield_generated complex_ring s)) /\
           v IN P ==> u * v IN P) /\
    (!u v. u IN P /\
           v IN ring_carrier(ring_of_integers
                               (subfield_generated complex_ring s))
           ==> u * v IN P)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
    MAP_EVERY (fun th -> MP_TAC(ISPECL
      [`ring_of_integers(subfield_generated complex_ring s)`;
       `P:complex->bool`] th))
     [IN_RING_IDEAL_SUB; IN_RING_IDEAL_LMUL; IN_RING_IDEAL_RMUL] THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; RING_SUB_SUBFIELD_GENERATED;
                    CONJUNCT2 SUBFIELD_GENERATED; complex_field_clauses] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:complex) IN P) /\ ~((d1:complex) IN P) /\
                ~((d2:complex) IN P)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((b:complex) * d1 * d2 IN P)` THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a = Cx(&0)) /\ ~(d1 + a * q1 = Cx(&0)) /\
                ~(d2 + a * q2 = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(k = 0)` MP_TAC THENL
     [UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((a * (d1 + a * q1)) pow k * (d2 + a * q2) = Cx(&0))`
    MP_TAC THENL
     [UNDISCH_TAC
       `(b:complex) * y pow m = (a * (d1 + a * q1)) pow k * (d2 + a * q2)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0];
      REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; DE_MORGAN_THM] THEN
      CONV_TAC TAUT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_SUBFIELD_VALUATION_POW] THEN
  ASM_CASES_TAC `(a:complex) IN P` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`s:complex->bool`; `P:complex->bool`; `a:complex`]
      COMPLEX_SUBFIELD_VALUATION_INTEGRAL) THEN
    ASM_SIMP_TAC[INT_MUL_RZERO; INT_DIVIDES_0]] THEN
  SUBGOAL_THEN
   `!u q. q IN ring_carrier(ring_of_integers
                              (subfield_generated complex_ring s)) /\
          u + a * q IN P ==> u IN P`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(u:complex) = (u + a * q) - a * q` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((d1:complex) + a * q1 IN P) /\
                ~((d2:complex) + a * q2 IN P)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `dedekind_valuation
      (ring_of_integers(subfield_generated complex_ring s),
       subfield_generated complex_ring s) I P b = &0 /\
    dedekind_valuation
      (ring_of_integers(subfield_generated complex_ring s),
       subfield_generated complex_ring s) I P
     (d1 + a * q1) = &0 /\
    dedekind_valuation
      (ring_of_integers(subfield_generated complex_ring s),
       subfield_generated complex_ring s) I P
     (d2 + a * q2) = &0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand o rand)
      COMPLEX_SUBFIELD_VALUATION_INTEGRAL o snd) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:complex->bool`; `P:complex->bool`; `b:complex`;
                 `y:complex`; `a:complex`; `d1 + a * q1:complex`;
                 `d2 + a * q2:complex`; `m:num`; `k:num`]
    SCHINZEL_TIJDEMAN_VALUATION_EQ) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_ADD_LID; INT_ADD_RID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INT_DIVIDES_RMUL THEN REWRITE_TAC[INT_DIVIDES_REFL]);;

(* ------------------------------------------------------------------------- *)
(* One root theta = r 1 of c0 y^m = g(x)^k H(x).                             *)
(* ------------------------------------------------------------------------- *)

(* g(x) = (x - theta) (dg(theta) + (x - theta) q1) since g(theta) = 0, and   *)
(* H(x) = H(theta) + (x - theta) q2, with q1, q2 in O_K.                     *)

let SCHINZEL_TIJDEMAN_ROOT_TAYLOR = prove
 (`!n c r M (H:num->real) x.
        nf_data n c r /\ (!i. integer(H i)) /\ integer x
        ==> r 1 IN ring_carrier(ring_of_integers
                                 (subfield_generated complex_ring {r 1})) /\
            vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) IN
            ring_carrier(ring_of_integers
                          (subfield_generated complex_ring {r 1})) /\
            vsum(0..M) (\i. Cx(H i) * r 1 pow i) IN
            ring_carrier(ring_of_integers
                          (subfield_generated complex_ring {r 1})) /\
            ?q1 q2. q1 IN ring_carrier(ring_of_integers
                                        (subfield_generated complex_ring
                                          {r 1})) /\
                    q2 IN ring_carrier(ring_of_integers
                                        (subfield_generated complex_ring
                                          {r 1})) /\
                    Cx(sum(0..n) (\i. c i * x pow i)) =
                    (Cx x - r 1) *
                    (vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) +
                     (Cx x - r 1) * q1) /\
                    Cx(sum(0..M) (\i. H i * x pow i)) =
                    vsum(0..M) (\i. Cx(H i) * r 1 pow i) + (Cx x - r 1) * q2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  ABBREV_TAC
   `oo = ring_carrier(ring_of_integers
          (subfield_generated complex_ring {(r:num->complex) 1}))` THEN
  SUBGOAL_THEN `oo subring_of complex_ring` ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN
    REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:num->complex) 1 IN oo /\ Cx x IN oo` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "oo" THEN
      REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM;
                  BRIDGE_NF_GEN_IN] THEN
      MATCH_MP_TAC NF_DATA_ALGEBRAIC_INTEGER THEN ASM_MESON_TAC[NF_DATA_1_IN];
      MATCH_MP_TAC BRIDGE_NF_SUBRING_INTEGER THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`oo:complex->bool`; `c:num->real`; `n:num`; `Cx x`;
                 `(r:num->complex) 1`] COMPLEX_POLY_TAYLOR_SUBRING) THEN
  MP_TAC(ISPECL [`oo:complex->bool`; `H:num->real`; `M:num`; `Cx x`;
                 `(r:num->complex) 1`] COMPLEX_POLY_TAYLOR_SUBRING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `q:complex` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `q1:complex` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC BRIDGE_NF_SUBRING_POLY THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`q1:complex`;
    `vsum(1..M) (\i. Cx(&i * H i) * (r:num->complex) 1 pow (i - 1)) +
     (Cx x - r 1) * q`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED) THEN
  ASM_SIMP_TAC[GSYM NF_DESCENT_VSUM_CX; NF_DATA_ROOT_1] THEN
  CONV_TAC COMPLEX_RING);;

(* delta = c0 dg(theta) H(theta) is a nonzero element of O_K.                *)

let SCHINZEL_TIJDEMAN_ROOT_DELTA = prove
 (`!n c r M (H:num->real) c0.
        nf_data n c r /\ (!i. integer(H i)) /\
        ~(vsum(0..M) (\i. Cx(H i) * r 1 pow i) = Cx(&0)) /\
        integer c0 /\ ~(c0 = &0)
        ==> Cx c0 * vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) *
            vsum(0..M) (\i. Cx(H i) * r 1 pow i) IN
            ring_carrier(ring_of_integers
                          (subfield_generated complex_ring {r 1})) /\
            ~(Cx c0 * vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) *
              vsum(0..M) (\i. Cx(H i) * r 1 pow i) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `M:num`;
                `H:num->real`; `&0`] SCHINZEL_TIJDEMAN_ROOT_TAYLOR) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPEC `{(r:num->complex) 1}`
    RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED o
             CONJUNCT2) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC BRIDGE_NF_SUBRING_INTEGER THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
    MATCH_MP_TAC NF_DATA_SIMPLE_ROOT THEN ASM_MESON_TAC[NF_DATA_1_IN]]);;

(* (x - theta)^k is a nonzero algebraic integer of K: x = theta would make   *)
(* g(x) = 0, so c0 y^m = 0.                                                  *)

let SCHINZEL_TIJDEMAN_ROOT_FACTOR = prove
 (`!n c r k M (H:num->real) c0 m x y.
        nf_data n c r /\ 1 <= k /\ ~(c0 = &0) /\ integer x /\ ~(y = &0) /\
        c0 * y pow m =
        sum(0..n) (\i. c i * x pow i) pow k * sum(0..M) (\i. H i * x pow i)
        ==> (Cx x - r 1) pow k IN
            ring_carrier(subfield_generated complex_ring {r 1}) /\
            ~((Cx x - r 1) pow k = Cx(&0)) /\
            algebraic_integer((Cx x - r 1) pow k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `Cx x - r 1 IN ring_carrier(ring_of_integers
                 (subfield_generated complex_ring {(r:num->complex) 1}))`
  MP_TAC THENL
   [MP_TAC(ISPEC `{(r:num->complex) 1}`
      RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED o
               CONJUNCT2) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC BRIDGE_NF_SUBRING_INTEGER THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED];
      REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM;
                  BRIDGE_NF_GEN_IN] THEN
      MATCH_MP_TAC NF_DATA_ALGEBRAIC_INTEGER THEN
      ASM_MESON_TAC[NF_DATA_1_IN]];
    REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM] THEN
    SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; ALGEBRAIC_INTEGER_POW] THEN
    DISCH_TAC THEN REWRITE_TAC[COMPLEX_POW_EQ_0; COMPLEX_SUB_0] THEN
    DISCH_THEN(MP_TAC o AP_TERM
     `\z. vsum(0..n) (\i. Cx(c i) * z pow i)` o CONJUNCT1) THEN
    ASM_SIMP_TAC[NF_DESCENT_VSUM_CX; NF_DATA_ROOT_1; CX_INJ] THEN
    DISCH_TAC THEN UNDISCH_TAC
     `c0 * y pow m =
      sum(0..n) (\i. c i * x pow i) pow k * sum(0..M) (\i. H i * x pow i)` THEN
    SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_POW_ZERO; REAL_MUL_LZERO; REAL_ENTIRE;
                    REAL_POW_EQ_0]]);;

(* For the nonzero primes P not containing delta, m divides                  *)
(* v_P((x - theta)^k).                                                       *)

let SCHINZEL_TIJDEMAN_ROOT_VALUATION = prove
 (`!n c r k M (H:num->real) c0 m x y P.
        nf_data n c r /\ 1 <= k /\ (!i. integer(H i)) /\
        integer c0 /\ ~(c0 = &0) /\ integer x /\ integer y /\ ~(y = &0) /\
        c0 * y pow m =
        sum(0..n) (\i. c i * x pow i) pow k *
        sum(0..M) (\i. H i * x pow i) /\
        prime_ideal (ring_of_integers(subfield_generated complex_ring {r 1}))
                    P /\
        ~(P = {Cx(&0)}) /\
        ~(Cx c0 * vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) *
          vsum(0..M) (\i. Cx(H i) * r 1 pow i) IN P)
        ==> &m divides
            dedekind_valuation
              (ring_of_integers(subfield_generated complex_ring {r 1}),
               subfield_generated complex_ring {r 1}) I P
             ((Cx x - r 1) pow k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `M:num`;
                `H:num->real`; `x:real`] SCHINZEL_TIJDEMAN_ROOT_TAYLOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q1:complex`
     (X_CHOOSE_THEN `q2:complex` STRIP_ASSUME_TAC))))) THEN
  MATCH_MP_TAC SCHINZEL_TIJDEMAN_VALUATION_DIVIDES THEN
  MAP_EVERY EXISTS_TAC
   [`Cx c0`;
    `vsum(1..n) (\i. Cx(&i * c i) * (r:num->complex) 1 pow (i - 1))`;
    `vsum(0..M) (\i. Cx(H i) * (r:num->complex) 1 pow i)`;
    `q1:complex`; `q2:complex`; `Cx y`] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; CX_INJ] THEN
  MP_TAC(ISPEC `{(r:num->complex) 1}`
    RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED o
             CONJUNCT2) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[NF_DATA_NUMBER_FIELD];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BRIDGE_NF_SUBRING_INTEGER THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED];
    MATCH_MP_TAC BRIDGE_NF_SUBRING_INTEGER THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED];
    MATCH_MP_TAC BRIDGE_NF_SUBRING_INTEGER THEN
    ASM_REWRITE_TAC[SUBRING_SUBFIELD_GENERATED];
    UNDISCH_TAC
     `c0 * y pow m =
      sum(0..n) (\i. c i * x pow i) pow k * sum(0..M) (\i. H i * x pow i)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `Cx`) THEN
    ASM_REWRITE_TAC[CX_MUL; CX_POW]]);;

(* ------------------------------------------------------------------------- *)
(* The descent for one root.                                                 *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_ROOT_DESCENT = prove
 (`!n c r k M (H:num->real) c0.
        nf_data n c r /\ 1 <= k /\ (!i. integer(H i)) /\
        ~(vsum(0..M) (\i. Cx(H i) * r 1 pow i) = Cx(&0)) /\
        integer c0 /\ ~(c0 = &0)
        ==> ?W D. FINITE W /\
                  (!v. v IN W
                       ==> v IN ring_carrier(subfield_generated complex_ring
                                               {r 1}) /\
                           ~(v = Cx(&0))) /\
                  integer D /\ &1 <= D /\
                  !m x y. 1 <= m /\ integer x /\ integer y /\ ~(y = &0) /\
                          c0 * y pow m =
                          sum(0..n) (\i. c i * x pow i) pow k *
                          sum(0..M) (\i. H i * x pow i)
                          ==> ?e xi. (!v. v IN W ==> e v < m) /\
                                     xi IN ring_carrier
                                            (subfield_generated complex_ring
                                               {r 1}) /\
                                     algebraic_integer(Cx D * xi) /\
                                     (Cx x - r 1) pow k =
                                     cproduct W (\v. v pow e v) * xi pow m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `M:num`;
                `H:num->real`; `c0:real`] SCHINZEL_TIJDEMAN_ROOT_DELTA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `delta = Cx c0 * vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) *
            vsum(0..M) (\i. Cx(H i) * (r:num->complex) 1 pow i)` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{(r:num->complex) 1}`;
    `{P | prime_ideal (ring_of_integers(subfield_generated complex_ring
                                          {(r:num->complex) 1})) P /\
          ~(P = {Cx(&0)}) /\ delta IN P}`]
   SCHINZEL_TIJDEMAN_SUNIT_DESCENT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_SUBFIELD_PRIMES_FINITE]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `W:complex->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `D:real` THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `x:real`; `y:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`; `M:num`;
                `H:num->real`; `c0:real`; `m:num`; `x:real`; `y:real`]
    SCHINZEL_TIJDEMAN_ROOT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `P:complex->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC SCHINZEL_TIJDEMAN_ROOT_VALUATION THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `M:num`; `H:num->real`;
                        `c0:real`; `y:real`] THEN
  ASM_MESON_TAC[]);;
