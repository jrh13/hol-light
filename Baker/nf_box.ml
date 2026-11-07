(* ========================================================================= *)
(* Box principle and elements of bounded norm in the order Z[theta].         *)
(*                                                                           *)
(* Purpose: a box principle for the order Z[theta]: a nonzero element whose  *)
(* conjugates lie in a conjugation symmetric box of volume at least CK       *)
(* (NF_BOX_PRINCIPLE), from the Minkowski theorem for ideals of ANT          *)
(* (NUMBER_FIELD_IDEAL_MINKOWSKI) applied to the ideal C O_K of              *)
(* K = Q(theta), where C is a positive integer with C O_K inside Z[theta]    *)
(* (NF_DATA_CONDUCTOR: [O_K : Z[theta]] is finite by                         *)
(* NUMBER_FIELD_POLY_DISCRIMINANT_INDEX, and C = N! for the index N);        *)
(* finiteness of the elements of bounded norm up to units (residues of the   *)
(* reduced coefficients modulo the norm).                                    *)
(*                                                                           *)
(* Main results: NF_DATA_CONDUCTOR, NF_BOX_PRINCIPLE,                        *)
(* NF_BOUNDED_NORM_FINITE.                                                   *)
(*                                                                           *)
(* Uses: ANT/minkowski_theory.ml (NUMBER_FIELD_IDEAL_MINKOWSKI),             *)
(* ANT/power_basis_index.ml (NUMBER_FIELD_POLY_DISCRIMINANT_INDEX,           *)
(* NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE), ANT/infinite_places.ml *)
(* (COMPLEX_EMBEDDINGS_NORM_EQ, COMPLEX_EMBEDDINGS_NORM_POS),                *)
(* Baker/lemmas.ml (PIGEONHOLE_CARD_LT), Baker/sharp_tools.ml                *)
(* (RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED), Baker/algint.ml            *)
(* (algebraic_integer, ALGEBRAIC_INTEGER_INTEGER, ALGEBRAIC_INTEGER_MUL),    *)
(* Baker/ant_bridge_complex.ml (BRIDGE_NF_* lemmas), Baker/ant_bridge_nf.ml  *)
(* (NF_DATA_NUMBER_FIELD, NF_DATA_COMPLEX_EMBEDDINGS,                        *)
(* NF_EMBEDDING_MONOMORPHISM, NF_ORDER_EMBEDDINGS), Baker/nf_defs.ml         *)
(* (nf_data, nf_order, nf_unit), Baker/nf_order.ml (NF_ORDER_REDUCE,         *)
(* NF_NORM_INTEGER, NF_ADJUGATE).                                            *)
(* ========================================================================= *)

needs "ANT/power_basis_index.ml";;
needs "Baker/sharp_tools.ml";;
needs "Baker/ant_bridge_nf.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The conductor: an integer C >= 1 with C O_K inside Z[theta] (the cosets   *)
(* of Z[theta] in O_K are finite in number, N say, so d z IN Z[theta] for    *)
(* some d IN 1..N, and N! z IN Z[theta]).                                    *)
(* ------------------------------------------------------------------------- *)

let NF_DATA_CONDUCTOR = prove
 (`!n c r.
        nf_data n c r
        ==> ?C. integer C /\ &1 <= C /\
                !z. z IN ring_carrier(subfield_generated complex_ring {r 1}) /\
                    algebraic_integer z
                    ==> Cx C * z IN
                        ring_carrier(subring_generated complex_ring {r 1})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                 `(r:num->complex) 1`]
    NUMBER_FIELD_POLY_DISCRIMINANT_INDEX) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM;
                  BRIDGE_NF_GEN_IN; SUBRING_GENERATED_SUBFIELD_GENERATED] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[NF_DATA_ALGEBRAIC_INTEGER; NF_DATA_1_IN]; ALL_TAC] THEN
    MATCH_MP_TAC NUMBER_FIELD_GENERATOR_MINIMAL_POLYNOMIAL_DEGREE THEN
    ASM_REWRITE_TAC[BRIDGE_NF_GEN_IN] THEN
    MATCH_MP_TAC SUBFIELD_GENERATED_IDEMPOT_GEN THEN
    REWRITE_TAC[SING_SUBSET; BRIDGE_NF_GEN_IN];
    ALL_TAC] THEN
  REWRITE_TAC[ring_coset; RING_OF_INTEGERS; CONJUNCT2 SUBFIELD_GENERATED;
              COMPLEX_RING_CLAUSES; HAS_SIZE] THEN
  ABBREV_TAC
   `M = ring_carrier(subring_generated complex_ring {(r:num->complex) 1})` THEN
  SUBGOAL_THEN `M subring_of complex_ring` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[SUBRING_SUBRING_GENERATED]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP COMPLEX_SUBRING_CLOSED) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&(FACT N):real` THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> 0 < n`;
              FACT_LT] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\j. {Cx(&j) * z + x | x IN M}`; `0..N`;
    `{{a + x | x IN M} | a |
      a IN ring_carrier(subfield_generated complex_ring {(r:num->complex) 1}) /\
      algebraic_integer a}`] PIGEONHOLE_CARD_LT) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG; ARITH_RULE `N < (N + 1) - 0`] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `Cx(&j) * z` THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED; BRIDGE_NF_SUBFIELD_RATIONAL;
                 RATIONAL_NUM; ALGEBRAIC_INTEGER_MUL; ALGEBRAIC_INTEGER_INTEGER;
                 INTEGER_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  SUBGOAL_THEN
   `!i j. i < j /\ j <= N /\ Cx(&j) * z - Cx(&i) * z IN M
          ==> Cx(&(FACT N)) * z IN M`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `j - i:num`] DIVIDES_FACT) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[divides]] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST1_TAC) THEN
    SUBGOAL_THEN `Cx(&((j - i) * t)) * z = Cx(&t) * (Cx(&j) * z - Cx(&i) * z)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_SUB; LT_IMP_LE;
                   CX_MUL; CX_SUB] THEN
      CONV_TAC COMPLEX_RING;
      ASM_SIMP_TAC[BRIDGE_NF_SUBRING_INTEGER; INTEGER_CLOSED]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `j:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `Cx(&i) * z - Cx(&j) * z IN M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&i) * z + Cx(&0)` o
      REWRITE_RULE[EXTENSION] o check (is_eq o concl)) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:complex` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (COMPLEX_RING
     `a + Cx(&0) = b + y ==> a - b = y`)) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> i < j \/ j < i`)) THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[COMPLEX_RING `a - b:complex = --(b - a)`] THEN
    ASM_SIMP_TAC[];
    MAP_EVERY EXISTS_TAC [`j:num`; `i:num`] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The box principle: Minkowski for the ideal C O_K; the bound c of the      *)
(* embedding nf_embedding n r k is cc k, constant on the infinite places     *)
(* since the conjugate embedding is that of cj k.                            *)
(* ------------------------------------------------------------------------- *)

let NF_BOX_PRINCIPLE = prove
 (`!n c r. nf_data n c r
           ==> ?CK. &1 <= CK /\
                    !cj cc. (!k. k IN 1..n
                                  ==> cj k IN 1..n /\ r(cj k) = cnj(r k) /\
                                      &0 < cc k /\ cc(cj k) = cc k) /\
                             CK <= product(1..n) cc
                             ==> ?a. nf_order n r a /\
                                     !k. k IN 1..n
                                         ==> ~(a k = Cx(&0)) /\
                                             norm(a k) <= cc k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o MATCH_MP NF_DATA_NUMBER_FIELD) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC o
    MATCH_MP NF_DATA_CONDUCTOR) THEN
  SUBGOAL_THEN `!k. k IN 1..n ==> nf_embedding n r k ((r:num->complex) 1) = r k`
  ASSUME_TAC THENL [ASM_MESON_TAC[NF_EMBEDDING_MONOMORPHISM]; ALL_TAC] THEN
  ABBREV_TAC `j = ideal_generated (ring_of_integers
                   (subfield_generated complex_ring {(r:num->complex) 1}))
                   {Cx C}` THEN
  EXISTS_TAC
   `max (&1) (sqrt(abs(real_of_int(number_field_discriminant
                (subfield_generated complex_ring {(r:num->complex) 1})))) *
              &(ideal_norm (ring_of_integers
                (subfield_generated complex_ring {r 1})) j))` THEN
  REWRITE_TAC[REAL_ARITH `&1 <= max (&1) x`] THEN
  MAP_EVERY X_GEN_TAC [`cj:num->num`; `cc:num->real`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NF_DATA_COMPLEX_EMBEDDINGS) THEN
  ABBREV_TAC
   `E = \k. RESTRICTION (ring_carrier(subfield_generated complex_ring
                                        {(r:num->complex) 1}))
                        (nf_embedding n r k)` THEN
  SUBGOAL_THEN
   `!k x. (E:num->complex->complex) k =
          RESTRICTION (ring_carrier(subfield_generated complex_ring
                                      {(r:num->complex) 1}))
                      (nf_embedding n r k) /\
          (k IN 1..n /\
           x IN ring_carrier(subfield_generated complex_ring {r 1})
           ==> E k x = nf_embedding n r k x)`
  MP_TAC THENL
   [EXPAND_TAC "E" THEN SIMP_TAC[RESTRICTION]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> REWRITE_TAC[GSYM th]) ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE] THEN
  DISCH_THEN(X_CHOOSE_TAC `ind:(complex->complex)->num`) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                 `j:complex->bool`;
                 `(cc:num->real) o (ind:(complex->complex)->num)`]
    NUMBER_FIELD_IDEAL_MINKOWSKI) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM] THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
      DISCH_THEN(MP_TAC o SPEC `Cx C` o REWRITE_RULE[EXTENSION]) THEN
      EXPAND_TAC "j" THEN
      REWRITE_TAC[IN_SING; CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES;
                  CX_INJ] THEN
      MATCH_MP_TAC(TAUT `p /\ ~q ==> ~(p <=> q)`) THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC IDEAL_GENERATED_INC_GEN THEN
      REWRITE_TAC[IN_SING; RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED;
                  IN_ELIM_THM] THEN
      ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER;
                   ALGEBRAIC_INTEGER_INTEGER];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      X_GEN_TAC `l:num` THEN REPEAT DISCH_TAC THEN
      MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                     `(E:num->complex->complex) k`;
                     `(E:num->complex->complex) l`]
        COMPLEX_EMBEDDINGS_NORM_EQ) THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [DISCH_THEN(MP_TAC o AP_TERM `ind:(complex->complex)->num`) THEN
        ASM_SIMP_TAC[];
        DISCH_THEN(MP_TAC o C AP_THM `(r:num->complex) 1`) THEN
        ASM_SIMP_TAC[RESTRICTION; o_THM; BRIDGE_NF_GEN_IN] THEN DISCH_TAC THEN
        SUBGOAL_THEN `l = (cj:num->num) k` (fun th -> ASM_SIMP_TAC[th]) THEN
        MATCH_MP_TAC NF_DATA_ROOTS_DISTINCT THEN
        MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
        ASM_SIMP_TAC[]];
      W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o rand o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `product(1..n) (cc:num->real)` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ THEN
        ASM_SIMP_TAC[o_THM]]];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `x IN ring_carrier(subfield_generated complex_ring {(r:num->complex) 1}) /\
    x IN ring_carrier(subring_generated complex_ring {r 1})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:complex) IN j` THEN EXPAND_TAC "j" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) IDEAL_GENERATED_SING o
      rand o lhand o snd) THEN
    REWRITE_TAC[RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER;
                 ALGEBRAIC_INTEGER_INTEGER] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[ring_divides; IN_ELIM_THM; RING_OF_INTEGERS;
                RING_OF_INTEGERS_COMPLEX_SUBFIELD_GENERATED;
                CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\k. nf_embedding n r k (x:complex)` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_ORDER_EMBEDDINGS th]) THEN
  CONJ_TAC THENL [EXISTS_TAC `x:complex` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  MP_TAC(ISPECL [`subfield_generated complex_ring {(r:num->complex) 1}`;
                 `(E:num->complex->complex) k`; `x:complex`]
    COMPLEX_EMBEDDINGS_NORM_POS) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; FIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING;
               CONJUNCT2 SUBFIELD_GENERATED; COMPLEX_RING_CLAUSES] THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Elements of bounded norm up to units.                                     *)
(* ------------------------------------------------------------------------- *)

let NF_BOX_UNIT_LEMMA = prove
 (`!n c r (a:num->complex) a' g m.
        nf_data n c r /\ nf_order n r a /\ nf_order n r a' /\
        nf_order n r g /\ cproduct(1..n) a = Cx m /\ cproduct(1..n) a' = Cx m /\
        ~(m = &0) /\ (!k. k IN 1..n ==> a' k = a k + Cx m * g k)
        ==> ?u. nf_unit n r u /\ !k. k IN 1..n ==> a' k = a k * u k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `a:num->complex`] NF_ADJUGATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `a':num->complex`] NF_ADJUGATE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b':num->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!k. k IN 1..n ==> ~((a:num->complex) k = Cx(&0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `cproduct(1..n) (a:num->complex) = Cx(&0)` MP_TAC THENL
     [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[CX_INJ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> (a:num->complex) k * (Cx(&1) + g k * b k) = a' k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:num->complex) k * b k = Cx m /\ a' k = a k + Cx m * g k`
    MP_TAC THENL [ASM_MESON_TAC[]; CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. k IN 1..n
        ==> (a':num->complex) k * (Cx(&1) - g k * b' k) = a k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(a':num->complex) k * b' k = Cx m /\ a' k = a k + Cx m * g k`
    MP_TAC THENL [ASM_MESON_TAC[]; CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  EXISTS_TAC `\k. Cx(&1) + (g:num->complex) k * b k` THEN
  REWRITE_TAC[nf_unit] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_CX THEN REWRITE_TAC[INTEGER_CLOSED];
      MATCH_MP_TAC NF_ORDER_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
    EXISTS_TAC `\k. Cx(&1) - (g:num->complex) k * b' k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_SUB THEN CONJ_TAC THENL
       [MATCH_MP_TAC NF_ORDER_CX THEN REWRITE_TAC[INTEGER_CLOSED];
        MATCH_MP_TAC NF_ORDER_MUL THEN ASM_REWRITE_TAC[ETA_AX]];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `~((a:num->complex) k = Cx(&0)) /\
        a k * (Cx(&1) + g k * b k) = a' k /\
        a' k * (Cx(&1) - g k * b' k) = a k`
      MP_TAC THENL [ASM_SIMP_TAC[]; CONV_TAC COMPLEX_FIELD]];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[]]);;

let NF_BOX_RESIDUE = prove
 (`!p m:real.
        integer p /\ integer m /\ ~(m = &0)
        ==> integer(floor(p / m)) /\ integer(p - m * floor(p / m)) /\
            abs(p - m * floor(p / m)) <= abs m /\
            p = (p - m * floor(p / m)) + m * floor(p / m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[FLOOR] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED; FLOOR]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `(p:real) - m * floor(p / m) = m * (p / m - floor(p / m))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `~((m:real) = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MP_TAC(SPEC `(p:real) / m` FLOOR) THEN REAL_ARITH_TAC);;

let NF_BOX_SAME_RESIDUES = prove
 (`!n (r:num->complex) (a:num->complex) b p p' q q' (rho:num->real) m k.
        1 <= n /\ k IN 1..n /\
        a k = vsum(0..n-1) (\i. Cx(p i) * r k pow i) /\
        b k = vsum(0..n-1) (\i. Cx(p' i) * r k pow i) /\
        (!i. i < n ==> p i = rho i + m * q i) /\
        (!i. i < n ==> p' i = rho i + m * q' i)
        ==> a k = b k + Cx m * vsum(0..n-1) (\i. Cx(q i - q' i) * r k pow i)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_ADD; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `i < n` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= n` THEN UNDISCH_TAC `i <= n - 1` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CX_ADD; CX_MUL; CX_SUB] THEN CONV_TAC COMPLEX_RING);;

let NF_BOUNDED_NORM_FINITE = prove
 (`!n c r C. nf_data n c r
             ==> ?A. FINITE A /\
                     (!b. b IN A ==> nf_order n r b /\
                                     ~(cproduct(1..n) b = Cx(&0))) /\
                     !a. nf_order n r a /\ ~(cproduct(1..n) a = Cx(&0)) /\
                         norm(cproduct(1..n) a) <= C
                         ==> ?b u. b IN A /\ nf_unit n r u /\
                                   !k. k IN 1..n ==> a k = b k * u k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [ASM_MESON_TAC[nf_data]; ALL_TAC] THEN
  ABBREV_TAC
   `P = \(a:num->complex) (kk:num->real).
          nf_order n r a /\ ~(cproduct(1..n) a = Cx(&0)) /\
          cproduct(1..n) a = Cx(kk n) /\
          ?p q. (!i. integer(p i)) /\ (!i. integer(q i)) /\
                (!k. k IN 1..n
                     ==> a k = vsum(0..n-1) (\i. Cx(p i) * r k pow i)) /\
                (!i. i < n ==> p i = kk i + kk n * q i)` THEN
  SUBGOAL_THEN
   `!kk:num->real. ?b:num->complex.
        (?a. (P:(num->complex)->(num->real)->bool) a kk) ==> P b kk`
  MP_TAC THENL [MESON_TAC[]; REWRITE_TAC[SKOLEM_THM]] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(num->real)->num->complex` (LABEL_TAC "f")) THEN
  ABBREV_TAC
   `keys = {kk:num->real |
              (!i. i IN 0..n
                   ==> kk i IN {x | integer x /\ --C <= x /\ x <= C}) /\
              (!i. ~(i IN 0..n) ==> kk i = &0)}` THEN
  SUBGOAL_THEN `FINITE(keys:(num->real)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "keys" THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_INTSEG];
    ALL_TAC] THEN
  EXISTS_TAC
   `IMAGE (f:(num->real)->num->complex)
          {kk | kk IN keys /\
                ?a. (P:(num->complex)->(num->real)->bool) a kk}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_RESTRICT];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `kk:num->real` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(P:(num->complex)->(num->real)->bool) (f kk) kk` MP_TAC THENL
     [REMOVE_THEN "f" (MP_TAC o SPEC `kk:num->real`) THEN
      ANTS_TAC THENL [EXISTS_TAC `a:num->complex` THEN
                      ASM_REWRITE_TAC[]; SIMP_TAC[]];
      EXPAND_TAC "P" THEN SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `a:num->complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `a:num->complex`] NF_NORM_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `a:num->complex`] NF_ORDER_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m = &0) /\ abs m <= C` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(cproduct(1..n) (a:num->complex) = Cx(&0))` THEN
    UNDISCH_TAC `norm(cproduct(1..n) (a:num->complex)) <= C` THEN
    ASM_REWRITE_TAC[CX_INJ; COMPLEX_NORM_CX] THEN MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `kk = \i. if i < n then p i - m * floor(p i / m)
             else if i = n then m else &0` THEN
  SUBGOAL_THEN
   `(!i. i < n ==> (kk:num->real) i = p i - m * floor(p i / m)) /\
    kk n = m /\ (!i. ~(i IN 0..n) ==> kk i = &0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REWRITE_TAC[IN_NUMSEG; LT_REFL] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i < n) /\ ~(i = n)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `~(0 <= i /\ i <= n)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> p i = (kk:num->real) i + m * floor(p i / m)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(kk:num->real) IN keys` ASSUME_TAC THENL
   [EXPAND_TAC "keys" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i < n` THENL
     [MP_TAC(ISPECL [`(p:num->real) i`; `m:real`] NF_BOX_RESIDUE) THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `(i:num) = n` SUBST1_TAC THENL
       [UNDISCH_TAC `(i:num) IN 0..n` THEN UNDISCH_TAC `~(i < n)` THEN
        REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:(num->complex)->(num->real)->bool) a kk` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`p:num->real`; `\i. floor((p:num->real) i / m)`] THEN
    ASM_REWRITE_TAC[FLOOR];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P:(num->complex)->(num->real)->bool) (f kk) kk` MP_TAC THENL
   [REMOVE_THEN "f" (MP_TAC o SPEC `kk:num->real`) THEN
    ANTS_TAC THENL [EXISTS_TAC `a:num->complex` THEN ASM_REWRITE_TAC[];
                    SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(f:(num->real)->num->complex) kk` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `a:num->complex` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(P:(num->complex)->(num->real)->bool) (f kk) kk` THEN
  EXPAND_TAC "P" THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p':num->real`
    (X_CHOOSE_THEN `q':num->real` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `(f:(num->real)->num->complex) kk`; `a:num->complex`;
                 `\k. vsum(0..n-1) (\i. Cx(floor((p:num->real) i / m) - q' i) *
                                        (r:num->complex) k pow i)`;
                 `m:real`] NF_BOX_UNIT_LEMMA) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[nf_order] THEN
    MAP_EVERY EXISTS_TAC
     [`n - 1`; `\i. floor((p:num->real) i / m) - q' i`] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED; FLOOR];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `r:num->complex`; `a:num->complex`;
                 `(f:(num->real)->num->complex) kk`; `p:num->real`;
                 `p':num->real`; `\i. floor((p:num->real) i / m)`;
                 `q':num->real`; `kk:num->real`; `m:real`; `k:num`]
                NF_BOX_SAME_RESIDUES) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;
