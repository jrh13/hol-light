(* ========================================================================= *)
(* The Dirichlet unit theorem for a number field k with ring of integers O   *)
(* and r = CARD(infinite_places k) - 1 = r1 + r2 - 1: there are r            *)
(* multiplicatively independent units (NUMBER_FIELD_UNITS_INDEPENDENT), any  *)
(* r + 1 units satisfy a nontrivial relation (NUMBER_FIELD_UNITS_DEPENDENT), *)
(* and there are fundamental units: r independent units e_1, ..., e_r such   *)
(* that every unit is a root of unity times a product of integer powers of   *)
(* the e_i (NUMBER_FIELD_FUNDAMENTAL_UNITS). The roots of unity of k are the *)
(* powers of one of them (NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC), and all units *)
(* are roots of unity iff k has one infinite place, i.e. k = Q or k is       *)
(* imaginary quadratic (NUMBER_FIELD_UNITS_ROOTS_OF_UNITY,                   *)
(* CARD_INFINITE_PLACES_EQ_1). Products and powers are those of the group    *)
(* unit_group(ring_of_integers k), as in ANT/fingen_group.ml.                *)
(*                                                                           *)
(* The first step is a unit dominant at a given place: for every embedding g *)
(* there is a unit u with |h u| < 1 for all embeddings h that do not induce  *)
(* the absolute value of g (NUMBER_FIELD_UNIT_DOMINANT_PLACE).               *)
(*                                                                           *)
(* Routes. Dominant place (the classical decreasing sequence): let s be the  *)
(* embeddings at the place of g. For a nonzero a in O the bounds |h a| / 2   *)
(* for h outside s, with product p, and the constant root (CARD s)           *)
(* (sqrt|d_K| / p) on s are constant on places, with product sqrt|d_K| =     *)
(* sqrt|d_K| N(O); so NUMBER_FIELD_IDEAL_MINKOWSKI (j = O) gives a nonzero b *)
(* in O with |h b| <= |h a| / 2 for h outside s and N((b)) = prod |h b| <=   *)
(* sqrt|d_K| (NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS). Iterating gives *)
(* a sequence a_m whose principal ideals have bounded norm, so two of them   *)
(* coincide (NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM): (a_m) = (a_n) with m  *)
(* < n, and the quotient u = a_n / a_m is a unit with |h u| < 1 for h        *)
(* outside s.                                                                *)
(*                                                                           *)
(* Independence without logarithms (van der Waerden; Alaca-Williams, Lemma   *)
(* 13.2.13), as a criterion for abelian groups with positive multiplicative  *)
(* size functions satisfying a product formula: fix a place v0 and a unit    *)
(* u_v dominant at v for each place v <> v0. In a relation prod u_v^(n_v) =  *)
(* 1 with some n_v > 0 (after a change of sign) let P = {v | n_v > 0} and    *)
(* beta(x) the product of |h x| over the embeddings h at the places outside  *)
(* P (v0 among them). Then beta(u_v) < 1 for v in P, and beta(u_v) >= 1 for  *)
(* the other v by the product formula prod |h u| = 1 for units               *)
(* (RING_OF_INTEGERS_UNIT_NORM_PRODUCT), so beta of the relation is < 1 =    *)
(* beta(1). The u_v are distinct, since no unit has |h u| < 1 for all h.     *)
(*                                                                           *)
(* Dependence: ABELIAN_GROUP_DISCRETE_DEPENDENT with the r size functions of *)
(* the places other than one place v0 (the product formula bounds v0, and    *)
(* Northcott gives finiteness). Fundamental units:                           *)
(* FINITELY_GENERATED_ABELIAN_SUBGROUP_STRUCTURE_ISOMORPHISM decomposes the  *)
(* unit group into cyclic subgroups; the finite ones consist of roots of     *)
(* unity, and there are exactly r infinite ones by the two rank theorems.    *)
(* Roots of unity: INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC.                    *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/products.ml (product, nproduct,      *)
(* PRODUCT_LT_1), Library/grouptheory.ml, ANT/ideal_norm.ml,                 *)
(* ANT/numfield.ml, ANT/classgroup.ml                                        *)
(* (NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM), ANT/discriminant.ml,           *)
(* ANT/fingen_group.ml (ABELIAN_GROUP_DISCRETE_DEPENDENT,                    *)
(* FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS),                      *)
(* Library/ring_groups.ml (unit_group, GROUP_REAL_MULTIPLICATIVE_SUM),       *)
(* ANT/complex_embeddings.ml (and with it Multivariate/cauchy.ml: root,      *)
(* exp), ANT/infinite_places.ml (COMPLEX_EMBEDDINGS_NORM_POS,                *)
(* COMPLEX_EMBEDDINGS_NORM_MUL, RING_OF_INTEGERS_UNIT_NORM_PRODUCT) and      *)
(* ANT/minkowski_theory.ml (NUMBER_FIELD_IDEAL_MINKOWSKI). Also              *)
(* Multivariate/complex_ring.ml (complex_ring) and                           *)
(* Multivariate/transcendentals.ml (root).                                   *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/products.ml";;
needs "Library/grouptheory.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/ideal_norm.ml";;
needs "ANT/numfield.ml";;
needs "ANT/classgroup.ml";;
needs "ANT/discriminant.ml";;
needs "ANT/fingen_group.ml";;
needs "Library/ring_groups.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "ANT/minkowski_theory.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* 1. Units with one dominant place.                                         *)
(* ------------------------------------------------------------------------- *)

(* The step of the sequence: for a union s of places and a nonzero a in O,  *)
(* NUMBER_FIELD_IDEAL_MINKOWSKI with the bounds |h a| / 2 outside s and a    *)
(* constant on s, chosen so that the product of the bounds is sqrt|d_K|.     *)

let NUMBER_FIELD_UNIT_DOMINANT_PLACE =
  let lemma = prove
   (`!k s.
        number_field k /\ s SUBSET complex_embeddings k /\ ~(s = {}) /\
        (!g h. g IN s /\ h IN complex_embeddings k /\
               (!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
               ==> h IN s)
        ==> !a:A. a IN ring_carrier(ring_of_integers k) /\ ~(a = ring_0 k)
                  ==> ?b. (b IN ring_carrier(ring_of_integers k) /\
                           ~(b = ring_0 k)) /\
                          (!h. h IN complex_embeddings k DIFF s
                               ==> norm(h b) <= norm(h a) / &2) /\
                          product (complex_embeddings k) (\h. norm(h b)) <=
                          sqrt(abs(real_of_int(number_field_discriminant k)))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `a:A` THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(complex_embeddings(k:A ring)) /\
                  FINITE(s:(A->complex)->bool) /\ (a:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_COMPLEX_EMBEDDINGS; FINITE_SUBSET;
                    RING_OF_INTEGERS_SUBSET; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `!h:A->complex. h IN complex_embeddings k ==> &0 < norm(h a)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_POS; NUMBER_FIELD_IMP_FIELD];
      ALL_TAC] THEN
    ABBREV_TAC
     `D = sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))` THEN
    ABBREV_TAC `p = product (complex_embeddings k DIFF s)
                            (\h:A->complex. norm(h(a:A)) / &2)` THEN
    SUBGOAL_THEN `&0:real < D /\ &0:real < p` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["D"; "p"] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[SQRT_POS_LT; GSYM REAL_ABS_NZ; REAL_OF_INT_CLAUSES;
                     NUMBER_FIELD_DISCRIMINANT_NONZERO];
        MATCH_MP_TAC PRODUCT_POS_LT THEN
        ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF; REAL_HALF]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `product (complex_embeddings k)
        (\h:A->complex. if h IN s then root (CARD s) (D / p)
                        else norm(h(a:A)) / &2) = D`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[product; MATCH_MP ITERATE_CASES MONOIDAL_REAL_MUL] THEN
      REWRITE_TAC[GSYM product] THEN
      ASM_SIMP_TAC[SET_RULE `!s t:(A->complex)->bool.
                     s SUBSET t ==> {x | x IN t /\ x IN s} = s`] THEN
      REWRITE_TAC[SET_RULE `!s t:(A->complex)->bool.
                    {x | x IN t /\ ~(x IN s)} = t DIFF s`] THEN
      ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_ROOT; CARD_EQ_0; REAL_LE_DIV;
                   REAL_LT_IMP_LE; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_carrier(ring_of_integers k):A->bool`;
     `\h:A->complex. if h IN s then root (CARD(s:(A->complex)->bool)) (D / p)
                     else norm(h(a:A)) / &2`] NUMBER_FIELD_IDEAL_MINKOWSKI) THEN
    ASM_REWRITE_TAC[RING_IDEAL_CARRIER; IDEAL_NORM_CARRIER; REAL_MUL_RID;
                    REAL_LE_REFL] THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[ROOT_POS_LT; REAL_LT_DIV; REAL_HALF];
        MAP_EVERY X_GEN_TAC [`g:A->complex`; `h:A->complex`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(h:A->complex) IN s <=> g IN s` SUBST1_TAC THENL
         [EQ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
           [EXISTS_TAC `h:A->complex`; EXISTS_TAC `g:A->complex`] THEN
          ASM_SIMP_TAC[];
          ASM_SIMP_TAC[]]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `b:A` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `h:A->complex` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `h:A->complex`) THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
        MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[NORM_POS_LE]]]) in
  prove
   (`!k (g:A->complex).
        number_field k /\ g IN complex_embeddings k
        ==> ?u. ring_unit (ring_of_integers k) u /\
                !h. h IN complex_embeddings k /\
                    ~(!x. x IN ring_carrier k ==> norm(h x) = norm(g x))
                    ==> norm(h u) < &1`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    SUBGOAL_THEN
     `?a:num->A.
        (!m. (a m IN ring_carrier(ring_of_integers k) /\ ~(a m = ring_0 k)) /\
             product (complex_embeddings k) (\h. norm(h(a m))) <=
             sqrt(abs(real_of_int(number_field_discriminant k)))) /\
        (!h. h IN complex_embeddings k /\
             ~(!x. x IN ring_carrier k ==> norm(h x) = norm((g:A->complex) x))
             ==> !m n. m < n ==> norm(h(a n)) < norm(h(a m)))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`k:A ring`;
        `{h | h IN complex_embeddings k /\
              !x. x IN ring_carrier k ==> norm(h x) = norm((g:A->complex) x)}`]
       lemma) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
        ASM_MESON_TAC[];
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM]] THEN
      DISCH_THEN(X_CHOOSE_TAC `f:A->A` o REWRITE_RULE[SKOLEM_THM] o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
      SUBGOAL_THEN `ring_1 k IN ring_carrier(ring_of_integers k) /\
                    ~(ring_1 k:A = ring_0 k)` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_1) THEN
        ASM_SIMP_TAC[RING_OF_INTEGERS; FIELD_NONTRIVIAL];
        ALL_TAC] THEN
      EXISTS_TAC `\m. ITER m (f:A->A) (f(ring_1 k))` THEN BETA_TAC THEN
      MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
       [INDUCT_TAC THEN ASM_SIMP_TAC[ITER];
        DISCH_TAC THEN X_GEN_TAC `h:A->complex` THEN STRIP_TAC THEN
        MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; X_GEN_TAC `m:num`] THEN
        REWRITE_TAC[ITER] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < y /\ x <= y / &2 ==> x < y`) THEN
        ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_POS;
                     REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?m n. m < n /\
            ideal_generated (ring_of_integers k) {(a:num->A) n} =
            ideal_generated (ring_of_integers k) {a m}`
    STRIP_ASSUME_TAC THENL
     [X_CHOOSE_TAC `c:num` (SPEC
       `sqrt(abs(real_of_int(number_field_discriminant(k:A ring))))`
       REAL_ARCH_SIMPLE) THEN
      FIRST_ASSUM(ASSUME_TAC o SPEC `c:num` o
        MATCH_MP NUMBER_FIELD_FINITE_IDEALS_BOUNDED_NORM) THEN
      MP_TAC(ISPECL
       [`\m. ideal_generated (ring_of_integers k) {(a:num->A) m}`;
        `(:num)`] FINITE_IMAGE_INJ_EQ) THEN
      MATCH_MP_TAC(TAUT
       `~r /\ q /\ (~p ==> s) ==> (p ==> (q <=> r)) ==> s`) THEN
      REWRITE_TAC[GSYM INFINITE; num_INFINITE] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
         (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
        X_GEN_TAC `m:num` THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
        CONJ_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_SING] THEN
          DISCH_THEN(MP_TAC o SPEC `(a:num->A) m`) THEN
          ASM_REWRITE_TAC[IN_IDEAL_GENERATED_SELF];
          REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
          ASM_SIMP_TAC[NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS] THEN
          ASM_MESON_TAC[REAL_LE_TRANS]];
        REWRITE_TAC[IN_UNIV; NOT_FORALL_THM; NOT_IMP] THEN
        MESON_TAC[LT_CASES]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `(a:num->A) n`;
                   `(a:num->A) m`] IDEALS_GENERATED_SING_EQ) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_ASSOCIATES;
                 INTEGRAL_DOMAIN_RING_OF_INTEGERS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A` THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `h:A->complex` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:num->A) m IN ring_carrier k /\ u IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_UNIT_IN_CARRIER; RING_OF_INTEGERS_SUBSET; SUBSET];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:A->complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_MUL] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; COMPLEX_EMBEDDINGS_NORM_POS]);;

(* ------------------------------------------------------------------------- *)
(* 2. Independent units.                                                     *)
(* ------------------------------------------------------------------------- *)

(* Local lemma, the criterion of van der Waerden: if positive multiplicative *)
(* size functions f i (i IN s) satisfy the product formula prod_i f i x = 1, *)
(* t is a finite set of functions missing some f i, and u v (v IN t) has f i *)
(* (u v) < 1 for all f i <> v, then only the trivial relation between the u  *)
(* v gives 1.                                                                *)

let NUMBER_FIELD_UNITS_INDEPENDENT =
  let lemma = prove
   (`!G (f:K->A->real) s t (u:(A->real)->A).
        abelian_group G /\ FINITE s /\ FINITE t /\
        (!i x. i IN s /\ x IN group_carrier G ==> &0 < f i x) /\
        (!i x y. i IN s /\ x IN group_carrier G /\ y IN group_carrier G
                 ==> f i (group_mul G x y) = f i x * f i y) /\
        (!x. x IN group_carrier G ==> product s (\i. f i x) = &1) /\
        (?j. j IN s /\ ~(f j IN t)) /\
        (!v. v IN t ==> u v IN group_carrier G) /\
        (!i v. i IN s /\ v IN t /\ ~(f i = v) ==> f i (u v) < &1)
        ==> !n. group_sum G t (\v. group_zpow G (u v) (n v)) = group_id G
                ==> !v. v IN t ==> n v = &0`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!n. group_sum G t (\v. group_zpow G ((u:(A->real)->A) v) (n v)) =
          group_id G
          ==> !v. v IN t ==> n v <= &0`
    ASSUME_TAC THENL
     [X_GEN_TAC `n:(A->real)->int` THEN DISCH_TAC THEN
      X_GEN_TAC `w:A->real` THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN
      REPEAT STRIP_TAC THEN
      ABBREV_TAC `beta = \x:A. product {i:K | i IN s /\
                           ~(f i IN t /\ &0 < (n:(A->real)->int)(f i))}
                           (\i. f i x)` THEN
      SUBGOAL_THEN
       `(!x. x IN group_carrier G ==> &0 < (beta:A->real) x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> beta(group_mul G x y) = beta x * beta y)`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "beta" THEN
        SIMP_TAC[GSYM PRODUCT_MUL; FINITE_RESTRICT;
                 ASSUME `FINITE(s:K->bool)`] THEN
        CONJ_TAC THEN REPEAT STRIP_TAC THENL
         [MATCH_MP_TAC PRODUCT_POS_LT THEN
          ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
          MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`G:A group`; `beta:A->real`]
        GROUP_REAL_MULTIPLICATIVE_ID_INV_POW) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `!v. v IN t /\ &0 < (n:(A->real)->int) v
            ==> (beta:A->real)((u:(A->real)->A) v) < &1`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "beta" THEN
        MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC `j:K` THEN
        ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN CONJ_TAC THENL
         [X_GEN_TAC `i:K` THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
          MATCH_MP_TAC REAL_LT_IMP_LE;
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!v. v IN t /\ ~(&0 < (n:(A->real)->int) v)
            ==> &1 <= (beta:A->real)((u:(A->real)->A) v)`
      ASSUME_TAC THENL
       [REPEAT STRIP_TAC THEN EXPAND_TAC "beta" THEN
        MP_TAC(SPEC `(u:(A->real)->A) v` (ASSUME
         `!x. x IN group_carrier G
              ==> product s (\i. (f:K->A->real) i x) = &1`)) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
        MP_TAC(ISPECL
         [`s:K->bool`;
          `\i. (f:K->A->real) i IN t /\ &0 < (n:(A->real)->int)(f i)`;
          `\i. (f:K->A->real) i ((u:(A->real)->A) v)`;
          `\i. (f:K->A->real) i ((u:(A->real)->A) v)`]
         (MATCH_MP ITERATE_CASES MONOIDAL_REAL_MUL)) THEN
        ASM_REWRITE_TAC[COND_ID; GSYM product] THEN
        MATCH_MP_TAC(REAL_ARITH
         `a:real * b <= &1 * b ==> &1 = a * b ==> &1 <= b`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC PRODUCT_LE_1; MATCH_MP_TAC PRODUCT_POS_LE] THEN
        ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; REAL_LT_IMP_LE] THEN
        X_GEN_TAC `i:K` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        UNDISCH_TAC `&0 < (n:(A->real)->int)((f:K->A->real) i)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `!v. v IN t
            ==> (beta:A->real)(group_zpow G ((u:(A->real)->A) v) (n v)) <= &1 /\
                (&0 < n v ==> beta(group_zpow G (u v) (n v)) < &1)`
      ASSUME_TAC THENL
       [X_GEN_TAC `v:A->real` THEN DISCH_TAC THEN REWRITE_TAC[group_zpow] THEN
        ASM_CASES_TAC `&0:int < n(v:A->real)` THEN
        ASM_SIMP_TAC[INT_LT_IMP_LE; GROUP_POW] THENL
         [MATCH_MP_TAC(REAL_ARITH `x:real < &1 ==> x <= &1 /\ x < &1`) THEN
          MATCH_MP_TAC REAL_POW_1_LT THEN
          ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT;
                       INT_LT_IMP_LE; INT_LT_IMP_NE];
          COND_CASES_TAC THENL
           [SUBGOAL_THEN `(n:(A->real)->int) v = &0` SUBST1_TAC THENL
             [ASM_INT_ARITH_TAC;
              ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM; group_pow]] THEN
            REAL_ARITH_TAC;
            ASM_SIMP_TAC[GROUP_POW] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
            MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_SIMP_TAC[]]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`G:A group`; `beta:A->real`;
                     `\v:A->real. group_zpow G ((u:(A->real)->A) v) (n v)`;
                     `t:(A->real)->bool`] GROUP_REAL_MULTIPLICATIVE_SUM) THEN
      ASM_SIMP_TAC[GROUP_ZPOW] THEN
      MATCH_MP_TAC(REAL_ARITH `x:real < &1 ==> ~(&1 = x)`) THEN
      MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC `w:A->real` THEN
      ASM_SIMP_TAC[] THEN X_GEN_TAC `v:A->real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[GROUP_ZPOW];
      ALL_TAC] THEN
    X_GEN_TAC `n:(A->real)->int` THEN DISCH_TAC THEN
    X_GEN_TAC `v:A->real` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ONCE_REWRITE_TAC[INT_ARITH `&0:int <= x <=> --x <= &0`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `\v:A->real. --((n:(A->real)->int) v)`) THEN
      ASM_SIMP_TAC[GROUP_ZPOW_NEG; ABELIAN_GROUP_SUM_INV; GROUP_ZPOW;
                   FINITE_RESTRICT; GROUP_INV_ID]]) in
  prove
   (`!k:A ring.
        number_field k
        ==> ?t. t HAS_SIZE (CARD(infinite_places k) - 1) /\
                (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
                !n. group_sum (unit_group(ring_of_integers k)) t
                      (\u. group_zpow (unit_group(ring_of_integers k)) u
                                      (n u)) =
                    ring_1 k
                    ==> !u. u IN t ==> n u = &0`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    SUBGOAL_THEN
     `!v. v IN infinite_places k
          ==> ?u. ring_unit (ring_of_integers k) u /\
                  !h. h IN complex_embeddings k /\ ~((\x. norm(h x)) = v)
                      ==> norm((h:A->complex) u) < &1`
    MP_TAC THENL
     [REWRITE_TAC[infinite_places; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
        NUMBER_FIELD_UNIT_DOMINANT_PLACE) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:A` THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:A->complex` THEN
      MATCH_MP_TAC(TAUT `(q ==> p) ==> (p ==> r) ==> (q ==> r)`) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `~((\x:A. norm((h:A->complex) x)) = (\x. norm((g:A->complex) x)))` THEN
      REWRITE_TAC[CONTRAPOS_THM; FUN_EQ_THM] THEN DISCH_TAC THEN
      X_GEN_TAC `x:A` THEN ASM_CASES_TAC `(x:A) IN ring_carrier k` THEN
      ASM_SIMP_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [complex_embeddings; EXTENSIONAL; IN_ELIM_THM]) THEN
      ASM_SIMP_TAC[];
      DISCH_THEN(X_CHOOSE_TAC `u:(A->real)->A` o REWRITE_RULE[SKOLEM_THM] o
        GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM])] THEN
    SUBGOAL_THEN
     `!x. ring_unit (ring_of_integers k) x
          ==> (x:A) IN ring_carrier k /\ ~(x = ring_0 k)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP RING_UNIT_IN_CARRIER) THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[RING_OF_INTEGERS_SUBSET; SUBSET]; DISCH_TAC] THEN
      UNDISCH_TAC `ring_unit (ring_of_integers k) (x:A)` THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM(CONJUNCT1 RING_OF_INTEGERS)] THEN
      ASM_SIMP_TAC[RING_UNIT_0; INTEGRAL_DOMAIN_RING_OF_INTEGERS;
                   INTEGRAL_DOMAIN_IMP_NONTRIVIAL_RING];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
    SUBGOAL_THEN
     `FINITE(complex_embeddings(k:A ring)) /\ FINITE(infinite_places k) /\
      (\x:A. norm((g:A->complex) x)) IN infinite_places k`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[FINITE_COMPLEX_EMBEDDINGS; FINITE_INFINITE_PLACES] THEN
      REWRITE_TAC[infinite_places; IN_IMAGE] THEN
      EXISTS_TAC `g:A->complex` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `infinite_places k DELETE (\x:A. norm((g:A->complex) x)) HAS_SIZE
      CARD(infinite_places k) - 1`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. group_sum (unit_group(ring_of_integers k))
            (infinite_places k DELETE (\x. norm((g:A->complex) x)))
            (\v. group_zpow (unit_group(ring_of_integers k))
                            ((u:(A->real)->A) v) (n v)) = ring_1 k
          ==> !v. v IN infinite_places k DELETE (\x. norm(g x)) ==> n v = &0`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`;
                     `\h:A->complex x:A. norm(h x)`;
                     `complex_embeddings(k:A ring)`;
                     `infinite_places k DELETE (\x:A. norm((g:A->complex) x))`;
                     `u:(A->real)->A`] lemma) THEN
      REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM; RING_OF_INTEGERS;
                  ABELIAN_UNIT_GROUP] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[FINITE_DELETE; COMPLEX_EMBEDDINGS_NORM_POS;
                   COMPLEX_EMBEDDINGS_NORM_MUL; IN_DELETE] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `x:A`]
          RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN
        ASM_SIMP_TAC[];
        EXISTS_TAC `g:A->complex` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!v w. v IN infinite_places k DELETE (\x. norm((g:A->complex) x)) /\
            w IN infinite_places k DELETE (\x. norm(g x)) /\
            (u:(A->real)->A) v = u w ==> v = w`
    (fun th -> MP_TAC(MATCH_MP HAS_SIZE_IMAGE_INJ (CONJ th (ASSUME
                `infinite_places k DELETE (\x:A. norm((g:A->complex) x))
                 HAS_SIZE CARD(infinite_places k) - 1`))) THEN
               MP_TAC(MATCH_MP GROUP_SUM_IMAGE
                (CONJ (ISPEC `ring_of_integers k:A ring` ABELIAN_UNIT_GROUP)
                      th))) THENL
     [REWRITE_TAC[IN_DELETE] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `!h. h IN complex_embeddings k
            ==> norm((h:A->complex)((u:(A->real)->A) w)) < &1`
      ASSUME_TAC THENL
       [X_GEN_TAC `h:A->complex` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th ->
          MP_TAC(SPEC `h:A->complex` (CONJUNCT2(MATCH_MP th
            (ASSUME `(v:A->real) IN infinite_places k`)))) THEN
          MP_TAC(SPEC `h:A->complex` (CONJUNCT2(MATCH_MP th
            (ASSUME `(w:A->real) IN infinite_places k`))))) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(v:A->real = w)` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `product (complex_embeddings k)
          (\h. norm((h:A->complex)((u:(A->real)->A) w))) = &1`
      MP_TAC THENL
       [MP_TAC(ISPECL [`k:A ring`; `(u:(A->real)->A) w`]
          RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x:real < &1 ==> x = &1 ==> F`) THEN
      MATCH_MP_TAC PRODUCT_LT_1 THEN EXISTS_TAC `g:A->complex` THEN
      ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    EXISTS_TAC
     `IMAGE (u:(A->real)->A)
            (infinite_places k DELETE (\x. norm((g:A->complex) x)))` THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_DELETE; o_DEF] THEN
    X_GEN_TAC `n:A->int` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\v. (n:A->int)((u:(A->real)->A) v)`) THEN
    REWRITE_TAC[IN_DELETE]);;

(* ------------------------------------------------------------------------- *)
(* 3. Any r + 1 units are dependent.                                         *)
(* ------------------------------------------------------------------------- *)

(* The sizes u |-> v(u) of the infinite places v other than one place v0     *)
(* are positive and multiplicative on the units. If all of them lie in       *)
(* [1 / b, b] at a unit u, then B = max 1 b bounds every conjugate of u by   *)
(* B^n: at an embedding g of the place v0 with |g u| > 1 the product formula *)
(* prod |h u| = 1 and the lower bounds B |h u| >= 1 for h <> g give |g u| <= *)
(* B^(n - 1) (local lemma bound). Northcott then gives the finiteness that   *)
(* ABELIAN_GROUP_DISCRETE_DEPENDENT needs.                                   *)

let NUMBER_FIELD_UNITS_DEPENDENT =
  let lemma = prove
   (`!a c p. &0 <= a:real /\ a * p = &1 /\ &1 <= c * p ==> a <= c`,
    REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `a * c * p:real` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `a * c * p:real = c * (a * p)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_MUL_AC];
        ASM_REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]]]) in
  let bound = prove
   (`!k (g:A->complex) x B.
        number_field k /\ ring_unit (ring_of_integers k) x /\
        g IN complex_embeddings k /\
        (!h. h IN complex_embeddings k /\ ~(h = g) ==> &1 <= B * norm(h x))
        ==> norm(g x) <= B pow (CARD(complex_embeddings k) - 1)`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_COMPLEX_EMBEDDINGS) THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\h:A->complex. norm(h(x:A))`;
                   `complex_embeddings(k:A ring)`; `g:A->complex`]
      PRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC lemma THEN
    EXISTS_TAC `product (complex_embeddings k DELETE g)
                        (\h:A->complex. norm(h(x:A)))` THEN
    ASM_REWRITE_TAC[NORM_POS_LE] THEN
    SUBGOAL_THEN
     `product (complex_embeddings k DELETE g) (\h:A->complex. &1) <=
      product (complex_embeddings k DELETE g) (\h. B * norm(h(x:A)))`
    MP_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN
      ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE; REAL_POS];
      ASM_SIMP_TAC[PRODUCT_ONE; PRODUCT_MUL; FINITE_DELETE; PRODUCT_CONST;
                   CARD_DELETE]]) in
  prove
   (`!k t:A->bool.
        number_field k /\ FINITE t /\
        (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
        CARD(infinite_places k) <= CARD t
        ==> ?n. (?u. u IN t /\ ~(n u = &0)) /\
                group_sum (unit_group(ring_of_integers k)) t
                  (\u. group_zpow (unit_group(ring_of_integers k)) u (n u)) =
                ring_1 k`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_COMPLEX_EMBEDDINGS) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `g0:A->complex`) THEN
    SUBGOAL_THEN
     `!g x. g IN complex_embeddings k /\ ring_unit (ring_of_integers k) x
            ==> &0 < norm((g:A->complex) x)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `x:A`] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\g:A->complex. norm(g(x:A))`;
                     `complex_embeddings(k:A ring)`] PRODUCT_EQ_0) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `g:A->complex`) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `(g:A->complex) x` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(\x:A. norm((g0:A->complex) x)) IN infinite_places k`
    ASSUME_TAC THENL
     [REWRITE_TAC[infinite_places; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`unit_group(ring_of_integers k):A group`;
      `infinite_places k DELETE (\x:A. norm((g0:A->complex) x))`;
      `\(v:A->real) (x:A). v x`; `t:A->bool`]
     ABELIAN_GROUP_DISCRETE_DEPENDENT) THEN
    REWRITE_TAC[UNIT_GROUP; RING_OF_INTEGERS; IN_ELIM_THM; SUBSET;
                ABELIAN_UNIT_GROUP] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_DELETE; FINITE_INFINITE_PLACES; CARD_DELETE] THEN
    MATCH_MP_TAC(TAUT `d /\ a /\ b /\ c ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(p = 0) /\ p <= t ==> p - 1 < t`) THEN
      ASM_SIMP_TAC[CARD_EQ_0; FINITE_INFINITE_PLACES] THEN
      ASM_MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[infinite_places; IN_DELETE; IMP_CONJ; RIGHT_FORALL_IMP_THM;
                FORALL_IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN
      X_GEN_TAC `g:A->complex` THEN STRIP_TAC THEN DISCH_TAC THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
        RING_HOMOMORPHISM_MUL) THEN
      ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET) THEN
        ASM_SIMP_TAC[RING_UNIT_IN_CARRIER];
        SIMP_TAC[COMPLEX_NORM_MUL]];
      ALL_TAC] THEN
    X_GEN_TAC `b:real` THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{x | x IN ring_carrier(ring_of_integers k) /\
           !g. g IN complex_embeddings k
               ==> norm((g:A->complex) x) <=
                   max (&1) b pow CARD(complex_embeddings k)}` THEN
    ASM_SIMP_TAC[RING_OF_INTEGERS_BOUNDED_CONJUGATES_FINITE] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:A` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[RING_UNIT_IN_CARRIER] THEN
    X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `1 <= CARD(complex_embeddings(k:A ring))` ASSUME_TAC THENL
     [ASM_SIMP_TAC[LE_1; CARD_EQ_0; COMPLEX_EMBEDDINGS_NONEMPTY]; ALL_TAC] THEN
    ASM_CASES_TAC
     `(\x:A. norm((g:A->complex) x)) = (\x. norm((g0:A->complex) x))`
    THENL
     [ALL_TAC;
      TRANS_TAC REAL_LE_TRANS `max (&1:real) b pow 1` THEN
      ASM_SIMP_TAC[REAL_POW_MONO; REAL_ARITH `&1:real <= max (&1) b`] THEN
      REWRITE_TAC[REAL_POW_1] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `g:A->complex`) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `norm((g:A->complex) x) <= &1` THENL
     [TRANS_TAC REAL_LE_TRANS `&1:real` THEN
      ASM_SIMP_TAC[REAL_POW_LE_1; REAL_ARITH `&1:real <= max (&1) b`];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE])] THEN
    TRANS_TAC REAL_LE_TRANS
     `max (&1:real) b pow (CARD(complex_embeddings(k:A ring)) - 1)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN
      REWRITE_TAC[REAL_ARITH `&1:real <= max (&1) b`] THEN ARITH_TAC] THEN
    MATCH_MP_TAC bound THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `h:A->complex` THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `(\x:A. norm((h:A->complex) x)) = (\x. norm((g0:A->complex) x))`
    THENL
     [SUBGOAL_THEN `norm((h:A->complex) x) = norm((g:A->complex) x)`
      SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `&1:real * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL2] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `h:A->complex`) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0:real < b` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `norm((h:A->complex) x)` THEN ASM_SIMP_TAC[];
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `b * inv b:real` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_LE_REFL];
        MATCH_MP_TAC REAL_LE_MUL2] THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. Roots of unity and fundamental units.                                  *)
(* ------------------------------------------------------------------------- *)

(* The roots of unity are finitely many, so they have a common exponent N    *)
(* (the product of their exponents) and are the N-th roots of unity.         *)

let NUMBER_FIELD_ROOTS_OF_UNITY_CYCLIC = prove
 (`!k:A ring.
        number_field k
        ==> ?z. z IN ring_carrier k /\
                (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                !x. x IN ring_carrier k /\
                    (?m. 1 <= m /\ ring_pow k x m = ring_1 k)
                    ==> ?j. x = ring_pow k z j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_ROOTS_OF_UNITY_FINITE) THEN
  ABBREV_TAC `w = {x:A | x IN ring_carrier k /\
                         ?m. 1 <= m /\ ring_pow k x m = ring_1 k}` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?d. !x:A. x IN w ==> 1 <= d x /\ ring_pow k x (d x) = ring_1 k`
  (X_CHOOSE_TAC `d:A->num`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    EXPAND_TAC "w" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= nproduct w (d:A->num)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < n <=> 1 <= n`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:A. x IN w ==> ring_pow k x (nproduct w d) = ring_1 k`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:A->num`; `w:A->bool`; `x:A`] NPRODUCT_DELETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(x:A) IN ring_carrier k` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:A) IN w` THEN EXPAND_TAC "w" THEN SIMP_TAC[IN_ELIM_THM];
      ASM_SIMP_TAC[RING_POW_MUL; RING_POW_ONE]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `nproduct w (d:A->num)`]
    INTEGRAL_DOMAIN_ROOTS_OF_UNITY_CYCLIC) THEN
  ASM_SIMP_TAC[NUMBER_FIELD_IMP_FIELD; FIELD_IMP_INTEGRAL_DOMAIN] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `nproduct w (d:A->num)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  SUBGOAL_THEN `(x:A) IN w` (fun th -> ASM_SIMP_TAC[th]) THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MESON_TAC[]]);;

(* Fundamental units: FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS of  *)
(* ANT/fingen_group.ml for the unit group (an independent set t of maximal   *)
(* size, generating modulo torsion); the torsion elements are the roots of   *)
(* unity, and CARD t = r by NUMBER_FIELD_UNITS_DEPENDENT and                 *)
(* NUMBER_FIELD_UNITS_INDEPENDENT.                                           *)

let NUMBER_FIELD_FUNDAMENTAL_UNITS = prove
 (`!k:A ring.
      number_field k
      ==> ?t. t HAS_SIZE (CARD(infinite_places k) - 1) /\
              (!u. u IN t ==> ring_unit (ring_of_integers k) u) /\
              (!n. group_sum (unit_group(ring_of_integers k)) t
                     (\u. group_zpow (unit_group(ring_of_integers k)) u
                                     (n u)) =
                   ring_1 k
                   ==> !u. u IN t ==> n u = &0) /\
              !u. ring_unit (ring_of_integers k) u
                  ==> ?z n. z IN ring_carrier k /\
                            (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                            u = ring_mul k z
                                 (group_sum (unit_group(ring_of_integers k)) t
                                   (\x. group_zpow
                                         (unit_group(ring_of_integers k)) x
                                         (n x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `unit_group(ring_of_integers k):A group`
    FINITELY_GENERATED_ABELIAN_GROUP_INDEPENDENT_BASIS) THEN
  ASM_SIMP_TAC[ABELIAN_UNIT_GROUP;
               NUMBER_FIELD_UNIT_GROUP_FINITELY_GENERATED] THEN
  REWRITE_TAC[UNIT_GROUP; RING_OF_INTEGERS; SUBSET; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:A->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "rep")
     (LABEL_TAC "rank"))))) THEN
  REWRITE_TAC[HAS_SIZE; GSYM CONJ_ASSOC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `~(p <= t) ==> t <= p - 1`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `t:A->bool`]
        NUMBER_FIELD_UNITS_DEPENDENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
      MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_UNITS_INDEPENDENT) THEN
      ASM_REWRITE_TAC[HAS_SIZE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:A->bool` (CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) STRIP_ASSUME_TAC)) THEN
      USE_THEN "rank" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    USE_THEN "rep" (MP_TAC o SPEC `u:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:A->int` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RING_OF_INTEGERS_SUBSET) THEN
      ASM_SIMP_TAC[RING_UNIT_IN_CARRIER];
      EXISTS_TAC
       `group_element_order (unit_group(ring_of_integers k)) (z:A)` THEN
      ASM_SIMP_TAC[LE_1] THEN
      MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`; `z:A`;
        `group_element_order (unit_group(ring_of_integers k)) (z:A)`]
        GROUP_POW_EQ_ID) THEN
      ASM_REWRITE_TAC[UNIT_GROUP; UNIT_GROUP_POW; RING_OF_INTEGERS;
                      IN_ELIM_THM; DIVIDES_REFL]]]);;

(* All units are roots of unity iff the rank is 0: a unit v in the set t of  *)
(* fundamental units with v^m = 1, m >= 1, would give the relation with the  *)
(* exponent m at v.                                                          *)

let NUMBER_FIELD_UNITS_ROOTS_OF_UNITY = prove
 (`!k:A ring.
        number_field k
        ==> ((!u. ring_unit (ring_of_integers k) u
                  ==> ?m. 1 <= m /\ ring_pow k u m = ring_1 k) <=>
             CARD(infinite_places k) = 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "units") (CONJUNCTS_THEN2 (LABEL_TAC "indep")
     (LABEL_TAC "rep"))))) THEN
  SUBGOAL_THEN `~(infinite_places(k:A ring) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[infinite_places; IMAGE_EQ_EMPTY; COMPLEX_EMBEDDINGS_NONEMPTY];
    ASM_SIMP_TAC[GSYM CARD_EQ_0; FINITE_INFINITE_PLACES]] THEN
  ASM_CASES_TAC `CARD(infinite_places(k:A ring)) = 1` THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[th; SUB_REFL; HAS_SIZE_0; ARITH_EQ]) THENL
   [DISCH_THEN SUBST_ALL_TAC THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    REMOVE_THEN "rep" (MP_TAC o SPEC `u:A`) THEN
    ASM_REWRITE_TAC[CONJUNCT1(SPEC_ALL GROUP_SUM_CLAUSES_EXISTS); UNIT_GROUP;
                    RING_OF_INTEGERS] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[RING_MUL_RID] THEN ASM_MESON_TAC[];
    REWRITE_TAC[HAS_SIZE] THEN DISCH_TAC THEN STRIP_TAC THEN
    DISCH_THEN(LABEL_TAC "ru")] THEN
  SUBGOAL_THEN `?v:A. v IN t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CARD_CLAUSES]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "units" (MP_TAC o SPEC `v:A`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  USE_THEN "ru" (MP_TAC o SPEC `v:A`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "indep" (MP_TAC o SPEC `\x:A. if x = v then &m else &0:int`) THEN
  ANTS_TAC THENL
   [BETA_TAC THEN TRANS_TAC EQ_TRANS
     `group_sum (unit_group(ring_of_integers k)) {v:A}
       (\x. group_zpow (unit_group(ring_of_integers k)) x
              (if x = v then &m else &0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC GROUP_SUM_SUPERSET THEN
      ASM_SIMP_TAC[SING_SUBSET; IN_SING; GROUP_ZPOW_0];
      ASM_REWRITE_TAC[GROUP_SUM_SING; GROUP_NPOW; UNIT_GROUP_POW; UNIT_GROUP;
                      RING_OF_INTEGERS; COND_ID]];
    DISCH_THEN(MP_TAC o SPEC `v:A`) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;
