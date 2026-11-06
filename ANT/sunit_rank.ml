(* ========================================================================= *)
(* The S-unit theorem with the rank. For a number field k with ring of       *)
(* integers O and a finite set S of nonzero primes of O, the S-units         *)
(* (s_unit_group k S of ANT/sunits.ml) are the roots of unity times a free   *)
(* abelian group of rank r1 + r2 - 1 + |S|, where r1 + r2 =                  *)
(* CARD(infinite_places k): there is a set t of CARD(infinite_places k) - 1  *)
(* + CARD S multiplicatively independent S-units such that every S-unit is a *)
(* root of unity times a product of integer powers of the elements of t      *)
(* (S_UNIT_GROUP_FUNDAMENTAL; for S = {} this is                             *)
(* NUMBER_FIELD_FUNDAMENTAL_UNITS). Equivalently, any CARD(infinite_places   *)
(* k) + CARD S S-units satisfy a nontrivial relation                         *)
(* (S_UNIT_GROUP_DEPENDENT, for any finite S) and there are                  *)
(* CARD(infinite_places k) - 1 + CARD S independent ones                     *)
(* (S_UNIT_GROUP_INDEPENDENT).                                               *)
(*                                                                           *)
(* Main steps: the S-units with all absolute values at the infinite places   *)
(* but one and all P-adic sizes N(P)^v_P(x), P IN S, in [1 / b, b] are       *)
(* finitely many (S_UNIT_GROUP_BOUNDED_FINITE); P^h is principal for the     *)
(* class number h, with a generator a_P of valuation h at P and 0 elsewhere  *)
(* (NUMBER_FIELD_PRIME_POW_GENERATOR). The finiteness combines a common      *)
(* denominator: elements x with v_P(x) >= -N at the primes of a finite S and *)
(* v_P(x) >= 0 elsewhere have d x IN O for one integer d > 0                 *)
(* (NUMBER_FIELD_VALUATION_DENOMINATOR), with an archimedean bound: the      *)
(* product formula for S-units, prod_g |g x| = prod_(P IN S) N(P)^v_P(x)     *)
(* over the complex embeddings g (S_UNIT_GROUP_PRODUCT_FORMULA), bounds all  *)
(* conjugates of such S-units by b^(|S| + n), n the number of complex        *)
(* embeddings (S_UNIT_GROUP_BOUNDED_EMBEDDINGS).                             *)
(*                                                                           *)
(* Routes. Dependence: ABELIAN_GROUP_DISCRETE_DEPENDENT with the             *)
(* CARD(infinite_places k) - 1 + CARD S size functions above. Finiteness:    *)
(* the valuations at S are bounded, |v_P(x)| < N with b < 2^N, so d x is in  *)
(* O for d = m^N, m the product of the norms N(P), P IN S, as N(P) IN P      *)
(* (IDEAL_NORM_IN_IDEAL); the product formula (NUMBER_FIELD_PRODUCT_FORMULA) *)
(* bounds prod_g |g x| by b^|S|, so at an embedding g of the omitted place   *)
(* |g x| <= b^|S| b^(n - 1) as b |h x| >= 1 at the other embeddings h        *)
(* (PRODUCT_FACTOR_BOUND of Library/products.ml);                            *)
(* then Northcott (RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE).              *)
(* Independence: fundamental units together with the a_P, P IN S; the        *)
(* valuation at P kills the exponent of a_P (through the logarithms of the   *)
(* multiplicative functions N(P)^v_P), and the rest is a relation between    *)
(* fundamental units (the inclusion of the units into the S-units is a group *)
(* homomorphism, GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP). The theorem:   *)
(* FINITELY_GENERATED_S_UNIT_GROUP, the two bounds and                       *)
(* FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS of ANT/fingen_group.ml *)
(* (an independent set of maximal size generating modulo torsion).           *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/grouptheory.ml, Library/products.ml  *)
(* (PRODUCT_FACTOR_BOUND), ANT/dedekind.ml, ANT/ideal_arith.ml,              *)
(* ANT/ideal_norm.ml, ANT/numfield.ml, ANT/ring_of_integers.ml,              *)
(* ANT/nf_valuation.ml, ANT/classgroup.ml                                    *)
(* (NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2), ANT/classgroup_group.ml             *)
(* (NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER), ANT/fingen_group.ml      *)
(* (FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS),                     *)
(* ANT/complex_embeddings.ml, ANT/sunits.ml, ANT/infinite_places.ml,         *)
(* ANT/unit_theorem.ml, ANT/product_formula.ml and ANT/regulator.ml          *)
(* (GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW, the infinite places as functions *)
(* on k). Also Multivariate/complex_ring.ml (COMPLEX_RING_OF_NUM) and        *)
(* Multivariate/transcendentals.ml (log, LOG_ZPOW).                          *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/products.ml";;
needs "ANT/dedekind.ml";;
needs "ANT/ideal_arith.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/classgroup.ml";;
needs "ANT/classgroup_group.ml";;
needs "ANT/fingen_group.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/sunits.ml";;
needs "ANT/infinite_places.ml";;
needs "ANT/unit_theorem.ml";;
needs "ANT/product_formula.ml";;
needs "ANT/regulator.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* S-units: the inclusion of the units, the size functions.                  *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP = prove
 (`!k:A ring S.
        number_field k
        ==> group_homomorphism(unit_group(ring_of_integers k),s_unit_group k S)
                              I`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM; I_THM; IMAGE_I] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:A ring`; `{}:(A->bool)->bool`; `S:(A->bool)->bool`]
      S_UNIT_GROUP_MONO) THEN
    ASM_SIMP_TAC[EMPTY_SUBSET; S_UNIT_GROUP_EMPTY; UNIT_GROUP];
    ASM_SIMP_TAC[S_UNIT_GROUP; UNIT_GROUP; RING_OF_INTEGERS]]);;

let S_UNIT_GROUP_INFINITE_PLACES = prove
 (`!k S v:A->real.
        number_field k /\ v IN infinite_places k
        ==> (!x. x IN group_carrier(s_unit_group k S) ==> &0 < v x) /\
            (!x y. x IN group_carrier(s_unit_group k S) /\
                   y IN group_carrier(s_unit_group k S)
                   ==> v(group_mul (s_unit_group k S) x y) = v x * v y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  ASM_SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM] THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC INFINITE_PLACES_POS; MATCH_MP_TAC INFINITE_PLACES_MUL] THEN
  ASM_MESON_TAC[]);;

let S_UNIT_GROUP_PRIME_SIZE = prove
 (`!k S P:A->bool.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
        ==> (!x. x IN group_carrier(s_unit_group k S)
                 ==> &0 < &(ideal_norm (ring_of_integers k) P) zpow
                          dedekind_valuation (ring_of_integers k,k) I P x) /\
            (!x y. x IN group_carrier(s_unit_group k S) /\
                   y IN group_carrier(s_unit_group k S)
                   ==> &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P
                          (group_mul (s_unit_group k S) x y) =
                       &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P x *
                       &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= ideal_norm (ring_of_integers k) (P:A->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC IDEAL_NORM_POS THEN
    MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM] THEN CONJ_TAC THEN
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[NUMBER_FIELD_VALUATION_MUL] THEN
    MATCH_MP_TAC REAL_ZPOW_ADD THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness of S-units with bounded sizes (a common denominator for        *)
(* bounded valuations, the archimedean bound from the product formula), and  *)
(* dependence.                                                               *)
(* ------------------------------------------------------------------------- *)

(* Elements whose valuations are at least -n at the primes of a finite S and *)
(* nonnegative elsewhere have the common denominator d = m^n, m the product  *)
(* of the norms N(P), P in S, as N(P) is in P (IDEAL_NORM_IN_IDEAL).         *)
let NUMBER_FIELD_VALUATION_DENOMINATOR = prove
 (`!k (S:(A->bool)->bool) n.
        number_field k /\ FINITE S
        ==> ?d. ~(d = 0) /\
                !x. x IN ring_carrier k /\
                    (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k})
                         ==> --(&n) <=
                             dedekind_valuation (ring_of_integers k,k) I P x) /\
                    (!P. prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\ ~(P IN S)
                         ==> &0 <=
                             dedekind_valuation (ring_of_integers k,k) I P x)
                    ==> ring_mul k (ring_of_num k d) x
                        IN ring_carrier(ring_of_integers k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  ABBREV_TAC `S' = {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k:A})}` THEN
  SUBGOAL_THEN `FINITE(S':(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S'" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN S' <=>
        P IN S /\ prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k:A})`
  ASSUME_TAC THENL [EXPAND_TAC "S'" THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `m = nproduct S' (\P. ideal_norm (ring_of_integers k) (P:A->bool))` THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[GSYM LT_NZ] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2;
                  ARITH_RULE `2 <= n ==> 0 < n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_num k m IN ring_carrier(ring_of_integers k) /\
    ~(ring_of_num k m = ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_RING_OF_NUM_EQ_0] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `m:num`] RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN S'
        ==> &1 <= dedekind_valuation (ring_of_integers k,k) I P
                    (ring_of_num k m:A)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `prime_ideal (ring_of_integers k) (P:A->bool) /\ ~(P = {ring_0 k}) /\
      FINITE(ring_carrier(quotient_ring (ring_of_integers k) P))`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`; `ring_of_num k m:A`]
      NUMBER_FIELD_VALUATION_PRIME_IDEAL) THEN
    ASM_REWRITE_TAC[INT_ARITH `&0:int < x <=> &1 <= x`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`\P. ideal_norm (ring_of_integers k) (P:A->bool)`;
                   `S':(A->bool)->bool`; `P:A->bool`] NPRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL
     [`ring_of_integers k:A ring`; `P:A->bool`;
      `ring_of_num k (ideal_norm (ring_of_integers k) P):A`;
      `ring_of_num k (nproduct (S' DELETE P)
                       (\P. ideal_norm (ring_of_integers k) P)):A`]
     IN_RING_IDEAL_RMUL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS; GSYM RING_OF_NUM_MUL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`]
        IDEAL_NORM_IN_IDEAL) THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS];
      MP_TAC(ISPECL [`ring_of_integers k:A ring`;
        `nproduct ((S':(A->bool)->bool) DELETE P)
                  (\P. ideal_norm (ring_of_integers (k:A ring)) P)`]
        RING_OF_NUM) THEN
      REWRITE_TAC[RING_OF_INTEGERS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN S'
        ==> &n <= dedekind_valuation (ring_of_integers k,k) I P
                    (ring_of_num k (m EXP n):A)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `prime_ideal (ring_of_integers k) (P:A->bool) /\ ~(P = {ring_0 k})`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[RING_OF_NUM_EXP; NUMBER_FIELD_VALUATION_POW; RING_OF_NUM] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_RID] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN ASM_SIMP_TAC[INT_POS];
    ALL_TAC] THEN
  EXISTS_TAC `m EXP n` THEN ASM_REWRITE_TAC[EXP_EQ_0] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = ring_0(k:A ring)` THENL
   [ASM_SIMP_TAC[RING_MUL_RZERO; RING_OF_NUM] THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_0) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_num k (m EXP n) IN ring_carrier(ring_of_integers k) /\
    ring_of_num k (m EXP n) IN ring_carrier k /\
    ~(ring_of_num k (m EXP n) = ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[NUMBER_FIELD_RING_OF_NUM_EQ_0; RING_OF_NUM; EXP_EQ_0] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `m EXP n`] RING_OF_NUM) THEN
    REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_mul k (ring_of_num k (m EXP n)) (x:A)`]
    NUMBER_FIELD_VALUATION_INTEGRAL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[RING_MUL; FIELD_IMP_INTEGRAL_DOMAIN;
                 INTEGRAL_DOMAIN_MUL_EQ_0];
    DISCH_THEN SUBST1_TAC] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_VALUATION_MUL] THEN
  ASM_CASES_TAC `(P:A->bool) IN S` THENL
   [MATCH_MP_TAC(INT_ARITH
     `!n:int. n <= a /\ --n <= b ==> &0 <= a + b`) THEN
    EXISTS_TAC `&n:int` THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC(INT_ARITH `&0:int <= a /\ &0 <= b ==> &0 <= a + b`) THEN
    ASM_SIMP_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_of_num k (m EXP n):A`]
      NUMBER_FIELD_VALUATION_INTEGRAL) THEN
    ASM_SIMP_TAC[]]);;

(* For an S-unit x the archimedean product is the product of the sizes       *)
(* N(P)^v_P(x) over the nonzero primes P of S (the product formula).         *)
let S_UNIT_GROUP_PRODUCT_FORMULA = prove
 (`!k (S:(A->bool)->bool) x.
        number_field k /\ x IN group_carrier(s_unit_group k S)
        ==> product (complex_embeddings k) (\g. norm(g x)) =
            product {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k})}
                    (\P. &(ideal_norm (ring_of_integers k) P) zpow
                         dedekind_valuation (ring_of_integers k,k) I P x)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `number_field(k:A ring)` THEN ASM_SIMP_TAC[S_UNIT_GROUP] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_PRODUCT_FORMULA) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `V = {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
             ~(dedekind_valuation (ring_of_integers k,k) I P (x:A) = &0)}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!P:A->bool. P IN V ==> (&0:real) < &(ideal_norm (ring_of_integers k) P)`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
      NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < product V (\P. &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P (x:A))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN ASM_SIMP_TAC[REAL_ZPOW_LT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN
  ASM_SIMP_TAC[REAL_ZPOW_NEG; PRODUCT_INV] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `( * ) (product V (\P. &(ideal_norm (ring_of_integers k) P) zpow
            dedekind_valuation (ring_of_integers k,k) I P (x:A)))`) THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
               REAL_MUL_LID; REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC PRODUCT_SUPERSET THEN EXPAND_TAC "V" THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `dedekind_valuation (ring_of_integers k,k) I P (x:A) = &0`
   (fun th -> REWRITE_TAC[th; REAL_ZPOW_0]) THEN
  ASM_MESON_TAC[]);;

(* The archimedean bound: if the sizes of an S-unit x at the infinite places *)
(* other than v0 are in [1 / b, b] and its P-adic sizes N(P)^v_P(x), P in S, *)
(* are at most b, then all its conjugates are at most b^(|S| + n), n the     *)
(* number of complex embeddings (at v0 by PRODUCT_FACTOR_BOUND).             *)
let S_UNIT_GROUP_BOUNDED_EMBEDDINGS = prove
 (`!k (S:(A->bool)->bool) v0 b x.
        number_field k /\ FINITE S /\ v0 IN infinite_places k /\ &1 <= b /\
        x IN group_carrier(s_unit_group k S) /\
        (!v. v IN infinite_places k /\ ~(v = v0)
             ==> inv b <= v x /\ v x <= b) /\
        (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
             ~(P = {ring_0 k})
             ==> &(ideal_norm (ring_of_integers k) P) zpow
                 dedekind_valuation (ring_of_integers k,k) I P x <= b)
        ==> !g. g IN complex_embeddings k
                ==> norm(g x) <= b pow (CARD S + CARD(complex_embeddings k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_COMPLEX_EMBEDDINGS) THEN
  SUBGOAL_THEN
   `product (complex_embeddings k) (\g. norm((g:A->complex) x)) <=
    b pow CARD(S:(A->bool)->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[S_UNIT_GROUP_PRODUCT_FORMULA] THEN
    TRANS_TAC REAL_LE_TRANS
     `product {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                   ~(P = {ring_0 k:A})} (\P. b)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
      MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
        NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ARITH_TAC;
      ASM_SIMP_TAC[PRODUCT_CONST; FINITE_RESTRICT] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(b:real) <= b pow (CARD(S:(A->bool)->bool) +
                       CARD(complex_embeddings(k:A ring)))`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= s + n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0; COMPLEX_EMBEDDINGS_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:A->complex. h IN complex_embeddings k
                   ==> (\y. norm(h y)) IN infinite_places k`
  ASSUME_TAC THENL
   [REWRITE_TAC[infinite_places; IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(\y. norm((g:A->complex) y)) = v0` THENL
   [ALL_TAC;
    TRANS_TAC REAL_LE_TRANS `b:real` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\y:A. norm((g:A->complex) y)` o check
     (fun th -> can (find_term ((=) `inv(b:real)`)) (concl th))) THEN
    ASM_SIMP_TAC[]] THEN
  ASM_CASES_TAC `norm((g:A->complex) x) <= &1` THENL
   [TRANS_TAC REAL_LE_TRANS `b:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE])] THEN
  MP_TAC(ISPECL [`\h:A->complex. norm(h(x:A))`; `complex_embeddings(k:A ring)`;
                 `g:A->complex`; `b:real`;
                 `(b:real) pow CARD(S:(A->bool)->bool)`]
    PRODUCT_FACTOR_BOUND) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL
   [X_GEN_TAC `h:A->complex` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(\y. norm((h:A->complex) y)) = v0` THENL
     [SUBGOAL_THEN `norm((h:A->complex) x) = norm((g:A->complex) x)`
      SUBST1_TAC THENL
       [UNDISCH_TAC `(\y. norm((h:A->complex) y)) = v0` THEN
        UNDISCH_TAC `(\y. norm((g:A->complex) y)) = v0` THEN
        REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[];
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `(&1:real) * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `\y:A. norm((h:A->complex) y)` o check
       (fun th -> can (find_term ((=) `inv(b:real)`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN STRIP_TAC THEN
      TRANS_TAC REAL_LE_TRANS `(b:real) * inv b` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `&1 <= (b:real) ==> ~(b = &0)`;
                     REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `(y:real) <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Finitely many S-units have all sizes but one in [1 / b, b]: with b < 2^N  *)
(* their valuations at S are above -N (local lemma valbound), so d x is      *)
(* integral for the denominator d of NUMBER_FIELD_VALUATION_DENOMINATOR, its *)
(* conjugates are bounded by S_UNIT_GROUP_BOUNDED_EMBEDDINGS, and Northcott  *)
(* (RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE) applies.                     *)
let S_UNIT_GROUP_BOUNDED_FINITE =
  let valbound = prove
   (`!a b v N. &2 <= a /\ inv b <= a zpow v /\ a zpow v <= b /\ b < &2 pow N
               ==> abs v < &N`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `!m. (a:real) pow m <= b ==> m < N` ASSUME_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 pow N <= (a:real) pow m` MP_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `(&2:real) pow m` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV;
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISJ_CASES_THEN (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)
     (SPEC `v:int` INT_IMAGE) THEN
    REWRITE_TAC[INT_ABS_NEG; INT_ABS_NUM; INT_OF_NUM_LT] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_ZPOW_NUM; REAL_ZPOW_NEG]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < (a:real) pow m /\ &0 < (b:real)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv((a:real) pow m)` THEN
        ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
        MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`b:real`; `(a:real) pow m`] REAL_LT_INV2) THEN
    ASM_REAL_ARITH_TAC) in
  prove
   (`!k (S:(A->bool)->bool) v0 b.
          number_field k /\ FINITE S /\ v0 IN infinite_places k /\ &1 <= b
          ==> FINITE
               {x | x IN group_carrier(s_unit_group k S) /\
                    (!v. v IN infinite_places k /\ ~(v = v0)
                         ==> inv b <= v x /\ v x <= b) /\
                    (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k})
                         ==> inv b <= &(ideal_norm (ring_of_integers k) P) zpow
                                      dedekind_valuation
                                        (ring_of_integers k,k) I P x /\
                             &(ideal_norm (ring_of_integers k) P) zpow
                             dedekind_valuation (ring_of_integers k,k) I P x
                             <= b)}`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    X_CHOOSE_TAC `N:num` (SPEC `b:real` REAL_ARCH_POW2) THEN
    MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `N:num`]
      NUMBER_FIELD_VALUATION_DENOMINATOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "den"))) THEN
    ABBREV_TAC `D = ring_of_num k d:A` THEN
    SUBGOAL_THEN `(D:A) IN ring_carrier k /\ ~(D = ring_0 k)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN ASM_SIMP_TAC[RING_OF_NUM;
                                       NUMBER_FIELD_RING_OF_NUM_EQ_0];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\y. ring_mul k (ring_inv k D) y)
       {y | y IN ring_carrier(ring_of_integers k) /\
            !g. g IN complex_embeddings k
                ==> norm((g:A->complex) y) <=
                    &d * b pow (CARD(S:(A->bool)->bool) +
                                CARD(complex_embeddings k))}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_SIMP_TAC[RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `x:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "pl") (LABEL_TAC "pr"))) THEN
    SUBGOAL_THEN
     `(x:A) IN ring_carrier k /\ ~(x = ring_0 k) /\
      !P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
          ~(P IN S)
          ==> dedekind_valuation (ring_of_integers k,k) I P x = &0`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN group_carrier(s_unit_group k S)` THEN
      ASM_SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM];
      ALL_TAC] THEN
    EXISTS_TAC `ring_mul k D (x:A)` THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[RING_MUL_ASSOC; RING_INV; FIELD_MUL_LINV; RING_MUL_LID];
      (* denominator control *)
      USE_THEN "den" MATCH_MP_TAC THEN
      ASM_SIMP_TAC[INT_LE_REFL] THEN
      X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(INT_ARITH `abs(v:int) < &N ==> --(&N) <= v`) THEN
      MATCH_MP_TAC valbound THEN
      EXISTS_TAC `&(ideal_norm (ring_of_integers k) (P:A->bool)):real` THEN
      EXISTS_TAC `b:real` THEN
      USE_THEN "pr" (MP_TAC o SPEC `P:A->bool`) THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; NUMBER_FIELD_PRIME_IDEAL_NORM_GE_2];
      (* archimedean bound *)
      X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `g:A->complex`; `D:A`; `x:A`]
        COMPLEX_EMBEDDINGS_NORM_MUL) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `norm((g:A->complex) D) = &d` SUBST1_TAC THENL
       [EXPAND_TAC "D" THEN
        UNDISCH_TAC `(g:A->complex) IN complex_embeddings k` THEN
        REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN STRIP_TAC THEN
        FIRST_ASSUM(fun th ->
          REWRITE_TAC[MATCH_MP RING_HOMOMORPHISM_RING_OF_NUM th]) THEN
        REWRITE_TAC[COMPLEX_RING_OF_NUM; COMPLEX_NORM_CX; REAL_ABS_NUM];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `v0:A->real`; `b:real`;
                     `x:A`] S_UNIT_GROUP_BOUNDED_EMBEDDINGS) THEN
      ASM_SIMP_TAC[]]);;

let S_UNIT_GROUP_DEPENDENT =
  let lemma = prove
   (`!y b. &0 < y /\ inv b <= y /\ y <= b
           ==> inv(max (&1) b) <= y /\ y <= max (&1) b`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&1 <= (b:real)` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < (b:real)` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`b:real`; `(&1:real)`] REAL_LT_INV2) THEN
      ASM_REWRITE_TAC[REAL_INV_1] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `max (&1) (b:real) = b` SUBST1_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]) in
  prove
   (`!k (S:(A->bool)->bool) t.
        number_field k /\ FINITE S /\ FINITE t /\
        t SUBSET group_carrier(s_unit_group k S) /\
        (CARD(infinite_places k) - 1) + CARD S < CARD t
        ==> ?n. (?x. x IN t /\ ~(n x = &0)) /\
                group_sum (s_unit_group k S) t
                  (\x. group_zpow (s_unit_group k S) x (n x)) =
                ring_1 k`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_INFINITE_PLACES) THEN
    SUBGOAL_THEN `?v0:A->real. v0 IN infinite_places k` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY; infinite_places; IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NONEMPTY];
      ALL_TAC] THEN
    ABBREV_TAC `S' = {P | P IN S /\ prime_ideal (ring_of_integers k) P /\
                          ~(P = {ring_0 k:A})}` THEN
    SUBGOAL_THEN
     `FINITE(S':(A->bool)->bool) /\ CARD S' <= CARD(S:(A->bool)->bool)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "S'" THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CARD_SUBSET THEN ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `group_id(s_unit_group k (S:(A->bool)->bool)) = ring_1 k`
      (SUBST1_TAC o SYM) THENL
     [ASM_SIMP_TAC[S_UNIT_GROUP]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`s_unit_group k (S:(A->bool)->bool)`;
      `(infinite_places k DELETE v0) UNION
       IMAGE (\P (x:A). &(ideal_norm (ring_of_integers k) P) zpow
                        dedekind_valuation (ring_of_integers k,k) I P x)
             (S':(A->bool)->bool)`;
      `\(i:A->real) (x:A). i x`; `t:A->bool`]
     ABELIAN_GROUP_DISCRETE_DEPENDENT) THEN
    REWRITE_TAC[ABELIAN_S_UNIT_GROUP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_DELETE; FINITE_IMAGE] THEN
    REWRITE_TAC[IN_UNION; IN_DELETE] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:A->real`; `x:A`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [STRIP_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `i:A->real`]
          S_UNIT_GROUP_INFINITE_PLACES) THEN ASM_SIMP_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `P:A->bool`
          (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
        REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `P:A->bool`]
          S_UNIT_GROUP_PRIME_SIZE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(P:A->bool) IN S'` THEN
          EXPAND_TAC "S'" THEN SIMP_TAC[IN_ELIM_THM];
          ASM_SIMP_TAC[]]];
      MAP_EVERY X_GEN_TAC [`i:A->real`; `x:A`; `y:A`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
       [STRIP_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `i:A->real`]
          S_UNIT_GROUP_INFINITE_PLACES) THEN ASM_SIMP_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN
        DISCH_THEN(X_CHOOSE_THEN `P:A->bool`
          (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC)) THEN
        REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `P:A->bool`]
          S_UNIT_GROUP_PRIME_SIZE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(P:A->bool) IN S'` THEN
          EXPAND_TAC "S'" THEN SIMP_TAC[IN_ELIM_THM];
          ASM_SIMP_TAC[]]];
      X_GEN_TAC `b:real` THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{x | x IN group_carrier(s_unit_group k S) /\
             (!v. v IN infinite_places k /\ ~(v = v0)
                  ==> inv(max (&1) b) <= v x /\ v x <= max (&1) b) /\
             (!P. P IN S /\ prime_ideal (ring_of_integers k) P /\
                  ~(P = {ring_0 k})
                  ==> inv(max (&1) b) <=
                      &(ideal_norm (ring_of_integers k) P) zpow
                      dedekind_valuation (ring_of_integers k,k) I P (x:A) /\
                      &(ideal_norm (ring_of_integers k) P) zpow
                      dedekind_valuation (ring_of_integers k,k) I P x
                      <= max (&1) b)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC S_UNIT_GROUP_BOUNDED_FINITE THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `v:A->real` THEN STRIP_TAC THEN
        MATCH_MP_TAC lemma THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `v:A->real`]
            S_UNIT_GROUP_INFINITE_PLACES) THEN ASM_SIMP_TAC[];
          USE_THEN "bd" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC lemma THEN CONJ_TAC THENL
         [MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `P:A->bool`]
            S_UNIT_GROUP_PRIME_SIZE) THEN ASM_SIMP_TAC[];
          USE_THEN "bd" (MP_TAC o SPEC
           `\x:A. &(ideal_norm (ring_of_integers k) P) zpow
                  dedekind_valuation (ring_of_integers k,k) I P x`) THEN
          REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN DISJ2_TAC THEN
          REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `P:A->bool` THEN
          REWRITE_TAC[] THEN EXPAND_TAC "S'" THEN
          ASM_REWRITE_TAC[IN_ELIM_THM]]];
      TRANS_TAC LET_TRANS
       `CARD(infinite_places(k:A ring) DELETE v0) +
        CARD(IMAGE (\P (x:A). &(ideal_norm (ring_of_integers k) P) zpow
                              dedekind_valuation (ring_of_integers k,k) I P x)
                   (S':(A->bool)->bool))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_UNION_LE THEN
        ASM_SIMP_TAC[FINITE_DELETE; FINITE_IMAGE];
        ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_DELETE] THEN
      MP_TAC(ISPECL
       [`\P (x:A). &(ideal_norm (ring_of_integers k) P) zpow
                   dedekind_valuation (ring_of_integers k,k) I P x`;
        `S':(A->bool)->bool`] CARD_IMAGE_LE) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Independent S-units, the S-unit theorem.                                  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_PRIME_POW_GENERATOR = prove
 (`!k P:A->bool.
        number_field k /\
        prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
        ==> ?a. a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k) /\
                !Q. prime_ideal (ring_of_integers k) Q /\ ~(Q = {ring_0 k})
                    ==> dedekind_valuation (ring_of_integers k,k) I Q a =
                        &(if Q = P then class_number(ring_of_integers k)
                          else 0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DEDEKIND_RING_OF_INTEGERS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_RING_IDEAL) THEN
  MP_TAC(ISPECL [`k:A ring`; `P:A->bool`]
    NUMBER_FIELD_PRINCIPAL_IDEAL_POW_CLASS_NUMBER) THEN
  ASM_REWRITE_TAC[principal_ideal] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(a:A = ring_0 k)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `P:A->bool`;
                   `class_number(ring_of_integers(k:A ring))`]
      IDEAL_POW_EQ_ZERO) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_RING_OF_INTEGERS; NUMBER_FIELD_IMP_FIELD] THEN
    UNDISCH_TAC
     `ideal_generated (ring_of_integers k) {a:A} =
      ideal_pow (ring_of_integers k) P (class_number(ring_of_integers k))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IDEAL_GENERATED_EQ_0; RING_OF_INTEGERS];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_VALUATION_RING_OF_INTEGERS] THEN
  ASM_SIMP_TAC[IDEAL_VALUATION_IDEAL_POW; IDEAL_VALUATION_PRIME;
               RING_OF_INTEGERS] THEN
  REWRITE_TAC[INT_OF_NUM_EQ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let S_UNIT_GROUP_INDEPENDENT = prove
 (`!k (S:(A->bool)->bool).
        number_field k /\ FINITE S /\
        (!P. P IN S ==> prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}))
        ==> ?t. t HAS_SIZE ((CARD(infinite_places k) - 1) + CARD S) /\
                t SUBSET group_carrier(s_unit_group k S) /\
                !n. group_sum (s_unit_group k S) t
                      (\x. group_zpow (s_unit_group k S) x (n x)) = ring_1 k
                    ==> !x. x IN t ==> n x = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS) THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:A->bool` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ind")
     (K ALL_TAC))))) THEN
  SUBGOAL_THEN
   `?x. !P. P IN (S:(A->bool)->bool)
            ==> (x P) IN ring_carrier(ring_of_integers(k:A ring)) /\
                ~(x P = ring_0 k) /\
                !Q. prime_ideal (ring_of_integers k) Q /\ ~(Q = {ring_0 k})
                    ==> dedekind_valuation (ring_of_integers k,k) I Q (x P) =
                        &(if Q = P then class_number(ring_of_integers k)
                          else 0)`
  (X_CHOOSE_THEN `x:(A->bool)->A` (LABEL_TAC "x")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC NUMBER_FIELD_PRIME_POW_GENERATOR THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `h = class_number(ring_of_integers(k:A ring))` THEN
  SUBGOAL_THEN `1 <= h` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN ASM_SIMP_TAC[NUMBER_FIELD_CLASS_NUMBER_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:A. u IN t0 ==> u IN ring_carrier k /\ ~(u = ring_0 k) /\
                     !Q. prime_ideal (ring_of_integers k) Q /\
                         ~(Q = {ring_0 k})
                         ==> dedekind_valuation (ring_of_integers k,k) I Q u =
                             &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `ring_unit (ring_of_integers k) (u:A)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `u:A`] RING_OF_INTEGERS_UNIT_NONZERO) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:A ring`; `u:A`] NUMBER_FIELD_VALUATION_UNIT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P Q. P IN S /\ prime_ideal (ring_of_integers k) Q /\ ~(Q = {ring_0 k})
          ==> dedekind_valuation (ring_of_integers k,k) I Q
                ((x:(A->bool)->A) P) = &(if Q = P then h else 0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "x" (MP_TAC o SPEC `P:A->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN S ==> (x:(A->bool)->A) P IN group_carrier(s_unit_group k S)`
  ASSUME_TAC THENL
   [X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM] THEN
    USE_THEN "x" (MP_TAC o SPEC `P:A->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `Q:A->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P:A->bool`; `Q:A->bool`] o check
      (fun th -> is_forall(concl th) &&
                 can (find_term ((=) `h:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!P Q. P IN S /\ Q IN S /\ (x:(A->bool)->A) P = x Q ==> P = Q`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`P:A->bool`; `P:A->bool`] o check
      (fun th -> is_forall(concl th) &&
                 can (find_term ((=) `h:num`)) (concl th))) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`Q:A->bool`; `P:A->bool`] o check
      (fun th -> is_forall(concl th) &&
                 can (find_term ((=) `h:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    ASM_CASES_TAC `P:A->bool = Q` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `dedekind_valuation (ring_of_integers k,k) I P ((x:(A->bool)->A) P) =
      &(if P = P then h else 0)` THEN
    UNDISCH_TAC
     `dedekind_valuation (ring_of_integers k,k) I P ((x:(A->bool)->A) Q) =
      &(if P = Q then h else 0)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (t0:A->bool) (IMAGE (x:(A->bool)->A) S)`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `u:A` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `P:A->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `prime_ideal (ring_of_integers k) (P:A->bool) /\
                  ~(P = {ring_0 k})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `dedekind_valuation (ring_of_integers k,k) I P (u:A) = &0`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `dedekind_valuation (ring_of_integers k,k) I P (u:A) = &h`
    (fun th -> REWRITE_TAC[th; INT_OF_NUM_EQ]) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`P:A->bool`; `P:A->bool`] o check
        (fun th -> is_forall(concl th) &&
                   can (find_term ((=) `h:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(t0:A->bool) UNION IMAGE (x:(A->bool)->A) S` THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(t0:A->bool) HAS_SIZE CARD(infinite_places(k:A ring)) - 1` THEN
    REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE; CARD_UNION; GSYM DISJOINT] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNION_SUBSET; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:A->int` THEN DISCH_THEN(LABEL_TAC "rel") THEN
  ABBREV_TAC `t = (t0:A->bool) UNION IMAGE (x:(A->bool)->A) S` THEN
  SUBGOAL_THEN
   `FINITE(t:A->bool) /\ t SUBSET group_carrier(s_unit_group k S) /\
    (t0:A->bool) SUBSET t /\ !P. P IN S ==> (x:(A->bool)->A) P IN t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    UNDISCH_TAC `(t0:A->bool) HAS_SIZE CARD(infinite_places(k:A ring)) - 1` THEN
    SIMP_TAC[HAS_SIZE; FINITE_UNION; FINITE_IMAGE] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_UNION; IN_UNION; UNION_SUBSET] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; FINITE_IMAGE] THEN
    X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Q y. Q IN S /\ y IN t
          ==> dedekind_valuation (ring_of_integers k,k) I Q y =
              &(if y = (x:(A->bool)->A) Q then h else 0)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`Q:A->bool`; `y:A`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `prime_ideal (ring_of_integers k) (Q:A->bool) /\
                  ~(Q = {ring_0 k})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:A) IN t` THEN EXPAND_TAC "t" THEN
    REWRITE_TAC[IN_UNION; IN_IMAGE] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `~(y = (x:(A->bool)->A) Q)` (fun th -> REWRITE_TAC[th])
      THENL
       [UNDISCH_TAC `DISJOINT (t0:A->bool) (IMAGE (x:(A->bool)->A) S)` THEN
        REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x':A->bool`; `Q:A->bool`] o check
        (fun th -> is_forall(concl th) &&
                   can (find_term ((=) `h:num`)) (concl th) &&
                   can (find_term ((=) `ring_0:A ring->A`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      AP_TERM_TAC THEN ASM_CASES_TAC `Q:A->bool = x'` THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Q. Q IN S ==> (n:A->int)((x:(A->bool)->A) Q) = &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `Q:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `prime_ideal (ring_of_integers k) (Q:A->bool) /\
                  ~(Q = {ring_0 k})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `2 <= ideal_norm (ring_of_integers k) (Q:A->bool)`
    ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= n <=> 1 < n`] THEN
      MATCH_MP_TAC IDEAL_NORM_GT_1 THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL; RING_OF_INTEGERS_FINITE_QUOTIENT] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_PROPER_IDEAL) THEN
      SIMP_TAC[proper_ideal; PSUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&0:real) < &(ideal_norm (ring_of_integers k) (Q:A->bool))`
    ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `Q:A->bool`]
      S_UNIT_GROUP_PRIME_SIZE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL
     [`s_unit_group k (S:(A->bool)->bool)`;
      `\y:A. &(ideal_norm (ring_of_integers k) (Q:A->bool)) zpow
             dedekind_valuation (ring_of_integers k,k) I Q y`;
      `\y:A. y`; `n:A->int`; `t:A->bool`]
     GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ABELIAN_S_UNIT_GROUP] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN USE_THEN "rel" SUBST1_TAC THEN
    SIMP_TAC[NUMBER_FIELD_VALUATION_1; ASSUME `field(k:A ring)`;
             REAL_ZPOW_0; LOG_1] THEN
    SUBGOAL_THEN
     `!i:A. i IN t
            ==> real_of_int(n i) *
                log(&(ideal_norm (ring_of_integers k) (Q:A->bool)) zpow
                    dedekind_valuation (ring_of_integers k,k) I Q i) =
                if i = (x:(A->bool)->A) Q
                then real_of_int(n i) *
                     (&h * log(&(ideal_norm (ring_of_integers k) Q)))
                else &0`
    MP_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[LOG_ZPOW] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[int_of_num_th] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP SUM_EQ th]) THEN
    ASM_SIMP_TAC[SUM_DELTA] THEN
    GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN REWRITE_TAC[REAL_ENTIRE] THEN
    SUBGOAL_THEN
     `~(&h:real = &0) /\
      ~(log(&(ideal_norm (ring_of_integers k) (Q:A->bool))) = &0)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC LOG_POS_LT THEN
        REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
      REWRITE_TAC[int_eq; int_of_num_th]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:A. u IN t0 ==> (n:A->int) u = &0` ASSUME_TAC THENL
   [USE_THEN "ind" MATCH_MP_TAC THEN
    MP_TAC(ISPECL
     [`unit_group(ring_of_integers k):A group`;
      `s_unit_group k (S:(A->bool)->bool)`; `I:A->A`; `t0:A->bool`;
      `\y:A. group_zpow (unit_group(ring_of_integers k)) y (n y)`]
     GROUP_SUM_HOMOMORPHIC_IMAGE) THEN
    ASM_SIMP_TAC[ABELIAN_UNIT_GROUP; ABELIAN_S_UNIT_GROUP;
                 GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN
        UNDISCH_TAC
         `(t0:A->bool) HAS_SIZE CARD(infinite_places(k:A ring)) - 1` THEN
        SIMP_TAC[HAS_SIZE];
        X_GEN_TAC `u:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC GROUP_ZPOW THEN
        REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[I_THM; o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
    USE_THEN "rel" (SUBST1_TAC o SYM) THEN
    CONV_TAC SYM_CONV THEN
    TRANS_TAC EQ_TRANS
     `group_sum (s_unit_group k S) t0
        (\x:A. group_zpow (s_unit_group k S) x ((n:A->int) x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GROUP_SUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `y:A` THEN STRIP_TAC THEN
      SUBGOAL_THEN `?Q. Q IN S /\ y = (x:(A->bool)->A) Q` STRIP_ASSUME_TAC
      THENL
       [UNDISCH_TAC `(y:A) IN t` THEN EXPAND_TAC "t" THEN
        REWRITE_TAC[IN_UNION; IN_IMAGE] THEN ASM_MESON_TAC[];
        ASM_SIMP_TAC[GROUP_ZPOW_0]];
      MATCH_MP_TAC GROUP_SUM_EQ THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`;
                     `s_unit_group k (S:(A->bool)->bool)`; `I:A->A`]
        GROUP_HOMOMORPHISM_ZPOW) THEN
      ASM_SIMP_TAC[GROUP_HOMOMORPHISM_UNIT_GROUP_S_UNIT_GROUP; I_THM] THEN
      DISCH_THEN(MATCH_MP_TAC o GSYM) THEN
      REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:A) IN t` THEN EXPAND_TAC "t" THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let S_UNIT_GROUP_FUNDAMENTAL = prove
 (`!k (S:(A->bool)->bool).
        number_field k /\ FINITE S /\
        (!P. P IN S ==> prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}))
        ==> ?t. t HAS_SIZE ((CARD(infinite_places k) - 1) + CARD S) /\
                t SUBSET group_carrier(s_unit_group k S) /\
                (!n. group_sum (s_unit_group k S) t
                       (\u. group_zpow (s_unit_group k S) u (n u)) =
                     ring_1 k
                     ==> !u. u IN t ==> n u = &0) /\
                !x. x IN group_carrier(s_unit_group k S)
                    ==> ?z n. z IN ring_carrier k /\
                              (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                              x = ring_mul k z
                                   (group_sum (s_unit_group k S) t
                                     (\u. group_zpow (s_unit_group k S) u
                                                     (n u)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s_unit_group k (S:(A->bool)->bool)`
    FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS) THEN
  ASM_SIMP_TAC[ABELIAN_S_UNIT_GROUP; FINITELY_GENERATED_S_UNIT_GROUP] THEN
  SUBGOAL_THEN `group_id(s_unit_group k (S:(A->bool)->bool)) = ring_1 k`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_SIMP_TAC[S_UNIT_GROUP]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "ind") (CONJUNCTS_THEN2 (LABEL_TAC "rep")
     (LABEL_TAC "rank"))))) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`; `t:A->bool`]
        S_UNIT_GROUP_DEPENDENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:A->int` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:A` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `~((n:A->int) u = &0)` THEN REWRITE_TAC[] THEN
      USE_THEN "ind" (MP_TAC o SPEC `n:A->int`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPECL [`k:A ring`; `S:(A->bool)->bool`]
        S_UNIT_GROUP_INDEPENDENT) THEN
      ASM_REWRITE_TAC[HAS_SIZE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) STRIP_ASSUME_TAC)) THEN
      USE_THEN "rank" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[S_UNIT_GROUP; ASSUME `number_field(k:A ring)`] THEN
      FIRST_ASSUM ACCEPT_TAC];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    USE_THEN "rep" (MP_TAC o SPEC `x:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:A->int` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:A) IN ring_carrier k` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:A) IN group_carrier(s_unit_group k S)` THEN
      SIMP_TAC[S_UNIT_GROUP; IN_ELIM_THM; ASSUME `number_field(k:A ring)`];
      ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [EXISTS_TAC
       `group_element_order (s_unit_group k (S:(A->bool)->bool)) (z:A)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`s_unit_group k (S:(A->bool)->bool)`; `z:A`;
        `group_element_order (s_unit_group k (S:(A->bool)->bool)) (z:A)`]
        GROUP_POW_EQ_ID) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      SIMP_TAC[S_UNIT_GROUP_POW; S_UNIT_GROUP; DIVIDES_REFL;
               ASSUME `number_field(k:A ring)`];
      FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
      SIMP_TAC[S_UNIT_GROUP; ASSUME `number_field(k:A ring)`]]]);;
