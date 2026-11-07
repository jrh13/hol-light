(* ========================================================================= *)
(* The descent for y^m = g(x) w, by the S-unit descent with ANT/.            *)
(*                                                                           *)
(* Purpose: for nf_data n c r (order Z[alpha], alpha = r 1, g = sum c i X^i) *)
(* and integers x, y, w, a, b with g(x) w = y^m and a g(x) + b w = R (R      *)
(* fixed, non-zero) there is a finite set D of order elements, independent   *)
(* of the solution, with d (x - alpha) = xi^m for some d IN D and xi in the  *)
(* order, as conjugate vectors on 1..n (NF_POWER_DESCENT). Route: in         *)
(* K = Q(alpha), m divides v_P(x - alpha) for every prime P of O_K not       *)
(* containing R dg(alpha) (NF_DESCENT_VALUATION: if x - alpha IN P then      *)
(* w NOTIN P, and SCHINZEL_TIJDEMAN_VALUATION_DIVIDES applies); the S-unit   *)
(* descent SCHINZEL_TIJDEMAN_SUNIT_DESCENT writes                            *)
(* x - alpha = prod_{v IN W} v^(e v) xi0^m with e v < m and D0 xi0 integral, *)
(* W and D0 fixed; with the conductor C of Z[alpha] (NF_DATA_CONDUCTOR) and  *)
(* B of COMPLEX_SUBFIELD_POW_DENOMINATOR, d = (C D0 B)^m / prod_v v^(e v)    *)
(* and xi = C D0 B xi0 lie in Z[alpha], and their conjugate vectors are the  *)
(* images under the embeddings nf_embedding n r k. For y^m = c0 g(x) h(x)    *)
(* with h(alpha) non-zero, the Bezout identity comes from the adjugate of    *)
(* h(alpha) and division by the monic g (NF_POWER_DESCENT_FACTOR).           *)
(*                                                                           *)
(* Main results: NF_POWER_DESCENT, NF_POWER_DESCENT_FACTOR,                  *)
(* NF_DESCENT_VALUATION, SCHINZEL_TIJDEMAN_MULT_DIVIDES (an integer          *)
(* polynomial F, not identically zero, vanishing at r 1 is g times an        *)
(* integer polynomial of degree deg F - n), NF_DATA_POLY_DIVIDES (the same   *)
(* without the degree).                                                      *)
(*                                                                           *)
(* Uses: Baker/schinzel_sunit.ml (SCHINZEL_TIJDEMAN_SUNIT_DESCENT,           *)
(* SCHINZEL_TIJDEMAN_VALUATION_DIVIDES, SCHINZEL_TIJDEMAN_ROOT_TAYLOR,       *)
(* SCHINZEL_TIJDEMAN_ROOT_DELTA, COMPLEX_SUBFIELD_POW_DENOMINATOR,           *)
(* COMPLEX_SUBFIELD_PRIMES_FINITE, COMPLEX_SUBFIELD_VALUATION_INTEGRAL),     *)
(* Baker/nf_box.ml (NF_DATA_CONDUCTOR), Baker/ant_bridge_nf.ml               *)
(* (NF_DATA_NUMBER_FIELD, NF_ORDER_EMBEDDINGS, NF_EMBEDDING_HOMOMORPHISM,    *)
(* NF_EMBEDDING_MONOMORPHISM), Baker/ant_bridge_complex.ml                   *)
(* (BRIDGE_NF_HOM_CLAUSES and the BRIDGE_NF_* closure lemmas),               *)
(* Baker/sharp_tools.ml (RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED),       *)
(* Baker/lemmas.ml (COMPLEX_SUBRING_OF, COMPLEX_SUBRING_CPRODUCT,            *)
(* COMPLEX_SUBRING_POLY_DIVISION_DEGREE), Baker/algint.ml (int_polyfun,      *)
(* VSUM_NUMSEG_RESTRICT_LE), Baker/nf_defs.ml (NF_DATA_1_IN),                *)
(* Baker/nf_order.ml (NF_NORM_INTEGER, NF_ADJUGATE, NF_ORDER_REDUCE,         *)
(* NF_DATA_DEGREE).                                                          *)
(* ========================================================================= *)

needs "Baker/nf_box.ml";;
needs "Baker/schinzel_sunit.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The valuation argument at the primes not containing R dg(alpha).          *)
(* ------------------------------------------------------------------------- *)

(* For g(x) w = y^m and a g(x) + b w = R: theta = r 1, x - theta is a        *)
(* nonzero algebraic integer of K = Q(theta), and m divides v_P(x - theta)   *)
(* for every nonzero prime P of O_K not containing R dg(theta) (dg the       *)
(* derivative of g): if x - theta IN P then g(x) IN P, so w NOTIN P, and     *)
(* SCHINZEL_TIJDEMAN_VALUATION_DIVIDES applies to                            *)
(* y^m = (x - theta) (dg(theta) + (x - theta) q1) w.                         *)

let NF_DESCENT_VALUATION = prove
 (`!n c r m R x y w a b.
        nf_data n c r /\ 1 <= m /\ integer R /\ integer x /\ integer y /\
        integer w /\ integer a /\ integer b /\
        ~(sum(0..n) (\i. c i * x pow i) = &0) /\
        sum(0..n) (\i. c i * x pow i) * w = y pow m /\
        a * sum(0..n) (\i. c i * x pow i) + b * w = R
        ==> Cx x - r 1 IN ring_carrier(ring_of_integers
                                (subfield_generated complex_ring {r 1})) /\
            ~(Cx x - r 1 = Cx(&0)) /\
            !P. prime_ideal (ring_of_integers
                              (subfield_generated complex_ring {r 1})) P /\
                ~(P = {Cx(&0)}) /\
                ~(Cx R * vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1))
                  IN P)
                ==> &m divides
                    dedekind_valuation
                     (ring_of_integers(subfield_generated complex_ring {r 1}),
                      subfield_generated complex_ring {r 1}) I P
                     (Cx x - r 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `0`;
                `\i:num. &0`; `x:real`] SCHINZEL_TIJDEMAN_ROOT_TAYLOR) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `q1:complex`
     (X_CHOOSE_THEN `q2:complex` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC
   `dg = vsum(1..n) (\i. Cx(&i * c i) * (r:num->complex) 1 pow (i - 1))` THEN
  ABBREV_TAC
   `oo = ring_carrier(ring_of_integers
          (subfield_generated complex_ring {(r:num->complex) 1}))` THEN
  SUBGOAL_THEN `oo subring_of complex_ring` ASSUME_TAC THENL
   [EXPAND_TAC "oo" THEN
    REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED) THEN
  SUBGOAL_THEN `!z. integer z ==> Cx z IN oo` ASSUME_TAC THENL
   [ASM_MESON_TAC[BRIDGE_NF_SUBRING_INTEGER]; ALL_TAC] THEN
  SUBGOAL_THEN `Cx x - r 1 IN oo /\ ~(Cx x - r 1 = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(sum(0..n) (\i. c i * x pow i) = &0)` THEN
    ASM_REWRITE_TAC[GSYM CX_INJ; COMPLEX_MUL_LZERO];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `P:complex->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  SUBGOAL_THEN
   `(!u v. u IN P /\ v IN P ==> u + v IN P) /\
    (!u v. u IN oo /\ v IN P ==> u * v IN P) /\
    (!u v. u IN oo /\ v IN oo /\ u * v IN P ==> u IN P \/ v IN P) /\
    Cx(&0) IN P`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [prime_ideal]) THEN
    MAP_EVERY (fun th -> MP_TAC(ISPECL
      [`ring_of_integers(subfield_generated complex_ring
                           {(r:num->complex) 1})`;
       `P:complex->bool`] th))
     [IN_RING_IDEAL_ADD; IN_RING_IDEAL_LMUL; IN_RING_IDEAL_0] THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; CONJUNCT2 SUBFIELD_GENERATED;
                    COMPLEX_RING_CLAUSES] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `Cx x - r 1 IN P` THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`{(r:num->complex) 1}`; `P:complex->bool`;
                   `Cx x - r 1`] COMPLEX_SUBFIELD_VALUATION_INTEGRAL) THEN
    ASM_SIMP_TAC[INT_DIVIDES_0]] THEN
  SUBGOAL_THEN `Cx(sum(0..n) (\i. c i * x pow i)) IN P` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx w IN P) /\ ~(dg IN P)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(Cx R * dg IN P)` THEN REWRITE_TAC[] THENL
     [ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `R:real`)) THEN
      REWRITE_TAC[CX_ADD; CX_MUL] THEN ASM_MESON_TAC[];
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{(r:num->complex) 1}`; `P:complex->bool`; `Cx x - r 1`;
                 `Cx(&1)`; `dg:complex`; `Cx w`; `q1:complex`; `Cx(&0)`;
                 `Cx y`; `m:num`; `1`] SCHINZEL_TIJDEMAN_VALUATION_DIVIDES) THEN
  REWRITE_TAC[COMPLEX_POW_1] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; LE_REFL; COMPLEX_MUL_LID;
               INTEGER_CLOSED; BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER;
               CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `sum(0..n) (\i. c i * x pow i) * w = &0 pow m` THEN
    ASM_SIMP_TAC[REAL_POW_ZERO; ARITH_RULE `1 <= m ==> ~(m = 0)`;
                 REAL_ENTIRE] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM CX_POW] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rhs(concl th) = `(y:real) pow m`)) THEN
    ASM_REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The descent theorem: the S-unit descent, the conductor and the            *)
(* embeddings.                                                               *)
(* ------------------------------------------------------------------------- *)

let NF_POWER_DESCENT = prove
 (`!n c r m R. nf_data n c r /\ 1 <= m /\ integer R /\ ~(R = &0)
   ==> ?D. FINITE D /\
           (!d. d IN D ==> nf_order n r d /\
                           !k. k IN 1..n ==> ~(d k = Cx(&0))) /\
           !x y w a b.
              integer x /\ integer y /\ integer w /\ integer a /\
              integer b /\
              ~(sum(0..n) (\i. c i * x pow i) = &0) /\
              sum(0..n) (\i. c i * x pow i) * w = y pow m /\
              a * sum(0..n) (\i. c i * x pow i) + b * w = R
              ==> ?d xi. d IN D /\ nf_order n r xi /\
                         !k. k IN 1..n ==> d k * (Cx x - r k) = xi k pow m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o
    MATCH_MP NF_DATA_CONDUCTOR) THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier(subring_generated complex_ring {(r:num->complex) 1})
        ==> z IN ring_carrier(subfield_generated complex_ring {r 1})`
  ASSUME_TAC THENL
   [MESON_TAC[SUBRING_SUBSET_SUBFIELD_GENERATED; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `0`;
                `\i:num. &1`; `R:real`] SCHINZEL_TIJDEMAN_ROOT_DELTA) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; VSUM_SING_NUMSEG; complex_pow;
                  COMPLEX_MUL_LID; COMPLEX_MUL_RID; CX_INJ; REAL_OF_NUM_EQ;
                  ARITH_EQ] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{(r:num->complex) 1}`;
    `{P | prime_ideal (ring_of_integers(subfield_generated complex_ring
                                          {(r:num->complex) 1})) P /\
          ~(P = {Cx(&0)}) /\
          Cx R * vsum(1..n) (\i. Cx(&i * c i) * r 1 pow (i - 1)) IN P}`]
   SCHINZEL_TIJDEMAN_SUNIT_DESCENT) THEN
  ASM_SIMP_TAC[COMPLEX_SUBFIELD_PRIMES_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:complex->bool` (X_CHOOSE_THEN `D0:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "desc"))))))) THEN
  MP_TAC(ISPECL [`{(r:num->complex) 1}`; `W:complex->bool`]
    COMPLEX_SUBFIELD_POW_DENOMINATOR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "B")))) THEN
  SUBGOAL_THEN
   `!q. integer q
        ==> Cx q IN ring_carrier(subfield_generated complex_ring
                                   {(r:num->complex) 1})`
  ASSUME_TAC THENL
   [SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN ring_carrier(subfield_generated complex_ring {(r:num->complex) 1})
        /\ ~(z = Cx(&0)) ==> inv z IN ring_carrier(subfield_generated
                                                     complex_ring {r 1})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_RING_INV] THEN
    MATCH_MP_TAC RING_INV_IN_SUBFIELD_GENERATED THEN
    ASM_SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. cproduct W (\v. v pow e v) IN
        ring_carrier(subfield_generated complex_ring {(r:num->complex) 1}) /\
        ~(cproduct W (\v. v pow e v) = Cx(&0))`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_SUBRING_CPRODUCT THEN
      ASM_SIMP_TAC[SUBRING_SUBFIELD_GENERATED; BRIDGE_NF_SUBFIELD_CLOSED];
      ASM_SIMP_TAC[CPRODUCT_EQ_0; COMPLEX_POW_EQ_0] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `z1 = \e. Cx C * (Cx C pow (m - 1) * Cx D0 pow m) * Cx B pow m *
             inv(cproduct W (\v:complex. v pow e v))` THEN
  SUBGOAL_THEN
   `!e. (!v. v IN W ==> e v <= m)
        ==> (z1:(complex->num)->complex) e IN
            ring_carrier(subring_generated complex_ring {(r:num->complex) 1})
            /\ ~(z1 e = Cx(&0))`
  (LABEL_TAC "z1") THENL
   [X_GEN_TAC `e:complex->num` THEN DISCH_TAC THEN EXPAND_TAC "z1" THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 BRIDGE_NF_SUBFIELD_CLOSED))
               THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED];
        MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN
          ASM_SIMP_TAC[ALGEBRAIC_INTEGER_POW; ALGEBRAIC_INTEGER_INTEGER];
          USE_THEN "B" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_INV_EQ_0; CX_INJ;
                      COMPLEX_POW_EQ_0; REAL_ENTIRE; REAL_POW_EQ_0] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC
   `IMAGE (\e k. nf_embedding n r k ((z1:(complex->num)->complex) e))
          {e | (!v. v IN W ==> e v IN {i | i < m}) /\
               (!v. ~(v IN W) ==> e v = 0)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `e:complex->num` THEN STRIP_TAC THEN
    USE_THEN "z1" (MP_TAC o SPEC `e:complex->num`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[LT_IMP_LE]; STRIP_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ORDER_EMBEDDINGS th]) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `(z1:(complex->num)->complex) e` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
      NF_EMBEDDING_MONOMORPHISM) THEN
    ASM_REWRITE_TAC[RING_MONOMORPHISM_ALT_EQ; CONJUNCT2 SUBFIELD_GENERATED;
                    COMPLEX_RING_CLAUSES] THEN
    DISCH_THEN(MP_TAC o SPEC `(z1:(complex->num)->complex) e` o
      CONJUNCT2 o CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `w:real`; `a:real`; `b:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `m:num`; `R:real`;
                `x:real`; `y:real`; `w:real`; `a:real`; `b:real`]
    NF_DESCENT_VALUATION) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  USE_THEN "desc" (MP_TAC o SPECL [`m:num`; `Cx x - r 1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `P:complex->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:complex->num` (X_CHOOSE_THEN `xi0:complex`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `e' = \v:complex. if v IN W then (e:complex->num) v else 0` THEN
  SUBGOAL_THEN
   `cproduct W (\v. v pow (e':complex->num) v) = cproduct W (\v. v pow e v)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN EXPAND_TAC "e'" THEN SIMP_TAC[];
    ALL_TAC] THEN
  USE_THEN "z1" (MP_TAC o SPEC `e':complex->num`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "e'" THEN ASM_SIMP_TAC[LT_IMP_LE]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `Cx C * Cx B * Cx D0 * xi0 IN
    ring_carrier(subring_generated complex_ring {(r:num->complex) 1})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; BRIDGE_NF_SUBFIELD_RATIONAL;
                 RATIONAL_INTEGER; ALGEBRAIC_INTEGER_MUL;
                 ALGEBRAIC_INTEGER_INTEGER];
    ALL_TAC] THEN
  EXISTS_TAC `\k. nf_embedding n r k ((z1:(complex->num)->complex) e')` THEN
  EXISTS_TAC `\k. nf_embedding n r k (Cx C * Cx B * Cx D0 * xi0)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ORDER_EMBEDDINGS th]) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `e':complex->num` THEN REWRITE_TAC[] THEN
    EXPAND_TAC "e'" THEN ASM_SIMP_TAC[];
    EXISTS_TAC `Cx C * Cx B * Cx D0 * xi0` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(z1:(complex->num)->complex) e' * (Cx x - r 1) =
    (Cx C * Cx B * Cx D0 * xi0) pow m`
  ASSUME_TAC THENL
   [EXPAND_TAC "z1" THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(cproduct W (\v. v pow (e:complex->num) v) = Cx(&0))`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `Cx C pow m = Cx C * Cx C pow (m - 1)` MP_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 complex_pow)] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[COMPLEX_POW_MUL] THEN CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_EMBEDDING_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BRIDGE_NF_HOM_CLAUSES) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
  REWRITE_TAC[RING_SUB_SUBFIELD_GENERATED; complex_field_clauses] THEN
  DISCH_TAC THEN
  UNDISCH_TAC
   `(z1:(complex->num)->complex) e' * (Cx x - r 1) =
    (Cx C * Cx B * Cx D0 * xi0) pow m` THEN
  DISCH_THEN(MP_TAC o AP_TERM `nf_embedding n r k`) THEN
  SUBGOAL_THEN
   `Cx x IN ring_carrier(subfield_generated complex_ring {(r:num->complex) 1})`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER]; ALL_TAC] THEN
  ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; BRIDGE_NF_GEN_IN;
               RATIONAL_INTEGER; NF_EMBEDDING_MONOMORPHISM] THEN
  ASM_MESON_TAC[NF_EMBEDDING_MONOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* Integer polynomials vanishing at r 1 are multiples of the defining        *)
(* polynomial of an nf_data (with an integer quotient of the exact           *)
(* degree).                                                                  *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_SUBRING_INTEGER = prove
 (`{Cx x | integer x} subring_of complex_ring`,
  REWRITE_TAC[COMPLEX_SUBRING_OF] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM CX_ADD; GSYM CX_MUL; GSYM CX_NEG; CX_INJ] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[INTEGER_CLOSED]);;

let SCHINZEL_TIJDEMAN_MULT_DIVIDES = prove
 (`!n c r N (a:num->real).
     nf_data n c r /\ (!i. integer(a i)) /\
     vsum(0..N) (\i. Cx(a i) * r 1 pow i) = Cx(&0) /\
     ~(!z. vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0))
     ==> n <= N /\
         ?h. (!i. integer(h i)) /\
             !z. vsum(0..N) (\i. Cx(a i) * z pow i) =
                 vsum(0..n) (\i. Cx(c i) * z pow i) *
                 vsum(0..N-n) (\i. Cx(h i) * z pow i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "a1") (LABEL_TAC "nz")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  SUBGOAL_THEN `n <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    REMOVE_THEN "nz" MP_TAC THEN REWRITE_TAC[] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG; COMPLEX_VEC_0] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:num->real) i = &0` SUBST1_TAC THENL
     [UNDISCH_TAC `nf_data n c r` THEN REWRITE_TAC[nf_data] THEN
      DISCH_THEN(MP_TAC o SPECL [`1`; `N:num`; `a:num->real`] o
        last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO]];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`{Cx x | integer x}`; `n:num`; `\i. Cx((c:num->real) i)`]
    COMPLEX_SUBRING_POLY_DIVISION_DEGREE) THEN
  REWRITE_TAC[COMPLEX_SUBRING_INTEGER; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      X_GEN_TAC `k:num` THEN EXISTS_TAC `(c:num->real) k` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`N - n:num`; `\i. Cx((a:num->real) i)`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:num` THEN EXISTS_TAC `(a:num->real) k` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `n + (N - n) = N` SUBST1_TAC THENL
   [UNDISCH_TAC `n <= N` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->complex` (X_CHOOSE_THEN `rr:num->complex`
    (CONJUNCTS_THEN2 (X_CHOOSE_TAC `hq:num->real` o REWRITE_RULE[SKOLEM_THM])
     (CONJUNCTS_THEN2 (X_CHOOSE_TAC `hr:num->real` o REWRITE_RULE[SKOLEM_THM])
      (LABEL_TAC "div"))))) THEN
  SUBGOAL_THEN `!i. i < n ==> (hr:num->real) i = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC NF_DATA_DEGREE THEN
    MAP_EVERY EXISTS_TAC [`c:num->real`; `r:num->complex`; `1`] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
    USE_THEN "div" (MP_TAC o SPEC `(r:num->complex) 1`) THEN
    USE_THEN "a1" (fun th -> REWRITE_TAC[th]) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `1`]
      NF_DATA_ROOT) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID] THEN
    DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `hq:num->real` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN USE_THEN "div" (fun th -> REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `v = Cx(&0) ==> u * w + v = w * u`) THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[IN_NUMSEG; COMPLEX_VEC_0] THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(hr:num->real) i = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`1 <= n`; `i <= n - 1`] THEN ARITH_TAC;
    REWRITE_TAC[COMPLEX_MUL_LZERO]]);;

let NF_DATA_POLY_DIVIDES = prove
 (`!n c r N (a:num->real).
   nf_data n c r /\ (!i. integer(a i)) /\
   vsum(0..N) (\i. Cx(a i) * r 1 pow i) = Cx(&0)
   ==> ?h. (!i. integer(h i)) /\
           !z. vsum(0..N) (\i. Cx(a i) * z pow i) =
               vsum(0..n) (\i. Cx(c i) * z pow i) *
               vsum(0..N) (\i. Cx(h i) * z pow i)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC
   `!z. vsum(0..N) (\i. Cx((a:num->real) i) * z pow i) = Cx(&0)` THENL
   [EXISTS_TAC `\i:num. &0` THEN ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `N:num`;
                `a:num->real`] SCHINZEL_TIJDEMAN_MULT_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `h:num->real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\i. if i <= N - n then (h:num->real) i else &0` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ASM_REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
    SIMP_TAC[VSUM_NUMSEG_RESTRICT_LE; ARITH_RULE `N - n <= N`]]);;

(* ------------------------------------------------------------------------- *)
(* The descent for y^m = c0 g(x) h(x) with h(alpha) non-zero: R0 = N h(alpha)*)
(* = h(alpha) B(alpha), R0 - h B = g A as integer polynomials, so            *)
(* c0 R0 = (c0 A(x)) g(x) + B(x) (c0 h(x)).                                  *)
(* ------------------------------------------------------------------------- *)

let NF_DESCENT_INTEGER_TAC =
  REPEAT(FIRST
   [MATCH_MP_TAC INTEGER_ADD THEN CONJ_TAC;
    MATCH_MP_TAC INTEGER_SUB THEN CONJ_TAC;
    MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC;
    MATCH_MP_TAC INTEGER_POW]) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED];;

let NF_POWER_DESCENT_FACTOR = prove
 (`!n c r m H (h:num->real) c0.
   nf_data n c r /\ 1 <= m /\ (!i. integer(h i)) /\
   ~(vsum(0..H) (\i. Cx(h i) * r 1 pow i) = Cx(&0)) /\
   integer c0 /\ ~(c0 = &0)
   ==> ?D. FINITE D /\
           (!d. d IN D ==> nf_order n r d /\
                           !k. k IN 1..n ==> ~(d k = Cx(&0))) /\
           !x y. integer x /\ integer y /\
                 ~(sum(0..n) (\i. c i * x pow i) = &0) /\
                 y pow m = c0 * sum(0..n) (\i. c i * x pow i) *
                                sum(0..H) (\i. h i * x pow i)
                 ==> ?d xi. d IN D /\ nf_order n r xi /\
                            !k. k IN 1..n
                                ==> d k * (Cx x - r k) = xi k pow m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  SUBGOAL_THEN
   `nf_order n r (\k. vsum(0..H) (\i. Cx(h i) * (r:num->complex) k pow i))`
  ASSUME_TAC THENL
   [REWRITE_TAC[nf_order] THEN
    MAP_EVERY EXISTS_TAC [`H:num`; `h:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `\k. vsum(0..H) (\i. Cx(h i) * (r:num->complex) k pow i)`]
    NF_NORM_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((R0:real) = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `~(vsum(0..H) (\i. Cx(h i) * (r:num->complex) 1 pow i) = Cx(&0))` THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                   `\k. vsum(0..H) (\i. Cx(h i) * (r:num->complex) k pow i)`]
      NF_NORM_EQ_0) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `\k. vsum(0..H) (\i. Cx(h i) * (r:num->complex) k pow i)`]
    NF_ADJUGATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ba:num->complex`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "adj"))) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `Ba:num->complex`]
    NF_ORDER_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bc:num->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "red"))) THEN
  SUBGOAL_THEN
   `int_polyfun (H + (n - 1))
      (\z. Cx R0 - vsum(0..H) (\i. Cx(h i) * z pow i) *
                   vsum(0..n-1) (\i. Cx(bc i) * z pow i))`
  MP_TAC THENL
   [MATCH_MP_TAC INT_POLYFUN_EQ THEN
    EXISTS_TAC
     `\z. Cx R0 + Cx(-- &1) * (vsum(0..H) (\i. Cx(h i) * z pow i) *
                               vsum(0..n-1) (\i. Cx(bc i) * z pow i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_POLYFUN_ADD THEN ASM_SIMP_TAC[INT_POLYFUN_CONST] THEN
      MATCH_MP_TAC INT_POLYFUN_CMUL THEN
      REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED] THEN
      MATCH_MP_TAC INT_POLYFUN_MUL THEN REWRITE_TAC[int_polyfun] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `h:num->real` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `bc:num->real` THEN ASM_REWRITE_TAC[]];
      GEN_TAC THEN REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  REWRITE_TAC[int_polyfun] THEN
  DISCH_THEN(X_CHOOSE_THEN `pc:num->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pc"))) THEN
  SUBGOAL_THEN
   `vsum(0..H + (n - 1)) (\i. Cx(pc i) * (r:num->complex) 1 pow i) = Cx(&0)`
  ASSUME_TAC THENL
   [USE_THEN "pc" (fun th -> REWRITE_TAC[GSYM th]) THEN
    SUBGOAL_THEN
     `vsum(0..n-1) (\i. Cx(bc i) * (r:num->complex) 1 pow i) = Ba 1`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "red" MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "adj" (MP_TAC o C MATCH_MP (ASSUME `1 IN 1..n`)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_SUB_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `H + (n - 1)`;
                 `pc:num->real`] NF_DATA_POLY_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `qa:num->real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qa"))) THEN
  SUBGOAL_THEN
   `!x. R0 = sum(0..H + (n - 1)) (\i. qa i * x pow i) *
             sum(0..n) (\i. c i * x pow i) +
             sum(0..n-1) (\i. bc i * x pow i) * sum(0..H) (\i. h i * x pow i)`
  (LABEL_TAC "id") THENL
   [X_GEN_TAC `x:real` THEN
    REWRITE_TAC[GSYM CX_INJ; CX_ADD; CX_MUL; GSYM NF_DESCENT_VSUM_CX] THEN
    USE_THEN "pc" (MP_TAC o SPEC `Cx x`) THEN
    USE_THEN "qa" (MP_TAC o SPEC `Cx x`) THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `m:num`;
                 `(c0:real) * R0`] NF_POWER_DESCENT) THEN
  ASM_SIMP_TAC[INTEGER_MUL; REAL_ENTIRE] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(num->complex)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "desc")))) THEN
  EXISTS_TAC `D:(num->complex)->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  USE_THEN "desc" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`y:real`; `c0 * sum(0..H) (\i. h i * x pow i)`;
    `c0 * sum(0..H + (n - 1)) (\i. qa i * x pow i)`;
    `sum(0..n-1) (\i. bc i * x pow i)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN NF_DESCENT_INTEGER_TAC;
    MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN NF_DESCENT_INTEGER_TAC;
    MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN NF_DESCENT_INTEGER_TAC;
    UNDISCH_TAC
     `(y:real) pow m = c0 * sum(0..n) (\i. c i * x pow i) *
                            sum(0..H) (\i. h i * x pow i)` THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;
