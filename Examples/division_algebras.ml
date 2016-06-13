(* ========================================================================= *)
(* Some nonexistence proofs for division algebras in higher dimensions.      *)
(* This does not (yet...) include the much more difficult restriction from   *)
(* Bott-Milnor-Kervaire to 1, 2, 4 or 8 dimensions, but does have these:     *)
(*                                                                           *)
(*  - Any division algebra must have even (or 1) dimension. This is simple   *)
(*    linear algebra, but given that Hamilton tried hard to find an example  *)
(*    in 3 dimensions, it's perhaps not completely trivial.                  *)
(*                                                                           *)
(*  - Any commutative division algebra must have dimension 1 or 2. This is   *)
(*    originally due to Hopf.                                                *)
(*                                                                           *)
(*  - Any associative division algebra must have dimension 1, 2 or 4. This   *)
(*    goes back to Frobenius.                                                *)
(*                                                                           *)
(* It would need only a little more work to show that the 2-dim and 4-dim    *)
(* examples in the latter must be isomorphic to complexes or quaternions.    *)
(* Most of the required reasoning is already buried inside the proofs, and   *)
(* the structures themselves are both available in the libraries:            *)
(*                                                                           *)
(*      Multivariate/make_complex.ml --- the complex numbers                 *)
(*      Quaternions/make.ml          --- the quaternions                     *)
(* ------------------------------------------------------------------------- *)

needs "Multivariate/moretop.ml";;

(* ------------------------------------------------------------------------- *)
(* First the easy fact that any division algebra must have even dimension    *)
(* (or trivially 1). This essentially follows from the fact that every       *)
(* linear operator has an eigenvector when the dimension is odd. One proof   *)
(* would be that the characteristic polynomial has odd degree and hence has  *)
(* a root, but we get it from a convenient topological generalization.       *)
(* ------------------------------------------------------------------------- *)

let DIVISION_ALGEBRA = prove
 (`!m:real^N->real^N->real^N.
        bilinear m /\ (!x y. m x y = vec 0 ==> x = vec 0 \/ y = vec 0)
        ==> dimindex(:N) = 1 \/ EVEN(dimindex(:N))`,
  REWRITE_TAC[ETA_AX; bilinear; linear; FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `dimindex(:N) = 1` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `~(n = 1) ==> 1 <= n ==> 2 <= n`)) THEN
  REWRITE_TAC[DIMINDEX_GE_1] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM NOT_ODD] THEN
  SUBGOAL_THEN
   `?g. linear g /\
        (!x. g (m (basis 1) x) = x) /\
        (!x. (m:real^N->real^N->real^N) (basis 1) (g x) = x)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_ISOMORPHISM THEN
    ASM_REWRITE_TAC[linear] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `basis 1:real^N = vec 0 \/ x + --(&1) % y:real^N = vec 0`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC;
      SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1]] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `x + --(&1) % y:real^N = vec 0 <=> x = y`];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
   SPEC `(m:real^N->real^N->real^N) (basis 2) o (g:real^N->real^N)` o
   MATCH_MP(REWRITE_RULE[IMP_CONJ]
     CONTINUOUS_FUNCTION_HAS_EIGENVALUES_ODD_DIM)) THEN
  REWRITE_TAC[NOT_IMP; NOT_EXISTS_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    ASM_SIMP_TAC[DIMINDEX_GE_1; ARITH] THEN
    ASM_REWRITE_TAC[linear];
    MAP_EVERY X_GEN_TAC [`v:real^N`; `c:real`] THEN
    ASM_CASES_TAC `v:real^N = vec 0` THEN
    ASM_REWRITE_TAC[IN_SPHERE_0; NORM_0; o_THM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `?w. v = (m:real^N->real^N->real^N) (basis 1) w`
    (CHOOSE_THEN SUBST_ALL_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(w:real^N = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[VECTOR_MUL_LZERO]; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `basis 2 + --c % basis 1:real^N = vec 0 \/ w:real^N = vec 0`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH
       `x + --c % y:real^N = vec 0 <=> x = c % y`];
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. x$2`) THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT] THEN
      ASM_SIMP_TAC[BASIS_COMPONENT; ARITH; VEC_COMPONENT] THEN
      REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The fact that there is no *commutative* division algebra for dim > 2,     *)
(* even without assuming associativity. This is based on the paper by        *)
(* W. B. Gordon, "An Application of Hadamard's Inverse Function Theorem      *)
(* to Algebra", American Mathematical Monthly vol. 84 (1977), pp. 28-29.     *)
(* The original proof of this result is due to Hopf.                         *)
(* ------------------------------------------------------------------------- *)

let COMMUTATIVE_DIVISION_ALGEBRA_GEN = prove
 (`!m:real^N->real^N->real^N s.
        bilinear m /\
        subspace s /\
        (!x y. m x y = vec 0 ==> x = vec 0 \/ y = vec 0) /\
        (!x y. x IN s /\ y IN s ==> m x y IN s /\ m x y = m y x)
        ==> dim s <= 2`,
  REWRITE_TAC[ARITH_RULE `n <= 2 <=> ~(3 <= n)`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!x y c. (m:real^N->real^N->real^N) x (c % y) = c % m x y) /\
    (!x y z. m x (y + z) = m x y + m x z)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[bilinear; linear]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f:real^N->real^N = \x. m x x` THEN
  MP_TAC(ISPECL
   [`f:real^N->real^N`;
    `s DELETE (vec 0:real^N)`; `s DELETE (vec 0:real^N)`]
   PROPER_LOCAL_HOMEOMORPHISM_GLOBAL) THEN
  ASM_SIMP_TAC[SIMPLY_CONNECTED_PUNCTURED_CONVEX; INT_OF_NUM_LE;
               SUBSPACE_IMP_CONVEX; AFF_DIM_DIM_SUBSPACE;
               SIMPLY_CONNECTED_IMP_PATH_CONNECTED; NOT_IMP] THEN
  SUBGOAL_THEN `!x. (f:real^N->real^N) x = vec 0 <=> x = vec 0`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[VECTOR_ARITH `x + y:real^N = x <=> y = vec 0`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{x | x IN s DELETE vec 0 /\ (f:real^N->real^N) x IN k} =
      s INTER {x | x IN UNIV /\ (f:real^N->real^N) x IN k}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_INTER_COMPACT THEN
    ASM_SIMP_TAC[CLOSED_SUBSPACE; COMPACT_EQ_BOUNDED_CLOSED] THEN
    SUBGOAL_THEN `(f:real^N->real^N) continuous_on UNIV` ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        (REWRITE_RULE[CONJ_ASSOC] BILINEAR_CONTINUOUS_ON_COMPOSE))) THEN
      REWRITE_TAC[CONTINUOUS_ON_ID];
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
       [COMPACT_EQ_BOUNDED_CLOSED])] THEN
    ASM_SIMP_TAC[CONTINUOUS_CLOSED_PREIMAGE; CLOSED_UNIV] THEN
    MP_TAC(ISPECL [`IMAGE (f:real^N->real^N) (sphere(vec 0,&1))`;
                   `vec 0:real^N`] DISTANCE_ATTAINS_INF) THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[IN_SPHERE_0; SPHERE_EQ_EMPTY; DIST_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV; COMPACT_IMP_CLOSED;
                    COMPACT_CONTINUOUS_IMAGE; COMPACT_SPHERE];
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` MP_TAC)] THEN
    ASM_CASES_TAC `a:real^N = vec 0` THEN
    ASM_REWRITE_TAC[NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < norm((f:real^N->real^N) a)` ASSUME_TAC THENL
     [ASM_MESON_TAC[NORM_POS_LT; NORM_EQ_0]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[bounded] THEN
    EXISTS_TAC `sqrt(B / norm((f:real^N->real^N) a))` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `~((f:real^N->real^N) x = vec 0) /\ ~(x = vec 0)`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_POS_LT; REAL_POW_LT] THEN
    TRANS_TAC REAL_LE_TRANS `norm((f:real^N->real^N) (inv(norm x) % x))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; NORM_POS_LT; REAL_POW_LT] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
        [GSYM REAL_ABS_NORM] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM REAL_ABS_POW; GSYM NORM_MUL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (SET_RULE `x IN k ==> y = x ==> y IN k`)) THEN
      EXPAND_TAC "f" THEN
      RULE_ASSUM_TAC(REWRITE_RULE[bilinear; linear]) THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; NORM_EQ_0; VECTOR_MUL_LID; REAL_FIELD
       `~(x = &0) ==> x pow 2 * inv x * inv x = &1`]];
    X_GEN_TAC `a:real^N` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^N->real^N`;
                   `\x h. &2 % (m:real^N->real^N->real^N) h x`;
                   `s DELETE (vec 0:real^N)`; `s:real^N->bool`; `a:real^N`]
      INVERSE_FUNCTION_THEOREM_SUBSPACE) THEN
    ASM_SIMP_TAC[OPEN_IN_DELETE; IN_DELETE; OPEN_IN_REFL] THEN
    ANTS_TAC THENL
     [EXPAND_TAC "f" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`m:real^N->real^N->real^N`; `\x:real^N. x`;
                       `\x:real^N. x`; `\x:real^N. x`; `\x:real^N. x`;
                       `x:real^N`; `s:real^N->bool`]
          HAS_DERIVATIVE_BILINEAR_WITHIN) THEN
        ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
        REWRITE_TAC[has_derivative] THEN MATCH_MP_TAC MONO_AND THEN
        CONJ_TAC THENL
         [DISCH_TAC THEN MATCH_MP_TAC LINEAR_COMPOSE_CMUL THEN
          RULE_ASSUM_TAC(REWRITE_RULE[bilinear]) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        ASM_CASES_TAC `trivial_limit(at (x:real^N) within s)` THENL
         [ASM_REWRITE_TAC[LIM]; ASM_SIMP_TAC[NETLIMIT_WITHIN]] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
        REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
        REWRITE_TAC[REAL_LT_01] THEN X_GEN_TAC `z:real^N` THEN
        STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[] THEN
        AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
         `x:real^N = y ==> x + y = &2 % y`) THEN
        ASM_MESON_TAC[SUBSPACE_SUB];
        MATCH_MP_TAC LINEAR_INJECTIVE_IMP_SURJECTIVE_ON THEN
        ASM_REWRITE_TAC[LE_REFL; SUBSET; FORALL_IN_IMAGE] THEN
        ASM_SIMP_TAC[SUBSPACE_MUL] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[bilinear]) THEN
        ASM_SIMP_TAC[LINEAR_COMPOSE_CMUL] THEN
        MAP_EVERY X_GEN_TAC [`y:real^N`; `z:real^N`] THEN
        REWRITE_TAC[VECTOR_ARITH `&2 % x:real^N = &2 % y <=> x = y`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN
         `x:real^N = vec 0 \/ y + --(&1) % z:real^N = vec 0`
        MP_TAC THENL
         [ALL_TAC; ASM_REWRITE_TAC[] THEN CONV_TAC VECTOR_ARITH] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[linear]) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[VECTOR_ARITH
         `x + --(&1) % y:real^N = vec 0 <=> x = y`] THEN
        ASM_MESON_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^N->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^N` THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        OPEN_IN_SUBSET_TRANS)) THEN
      REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_IMP_SUBSET)) THENL
       [ASM SET_TAC[]; REWRITE_TAC[DELETE_SUBSET]] THEN
      SUBGOAL_THEN `v = IMAGE (f:real^N->real^N) u` SUBST1_TAC THENL
       [ASM_MESON_TAC[homeomorphism]; SIMP_TAC[SUBSET; FORALL_IN_IMAGE]] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_DELETE] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXPAND_TAC "f"; ASM SET_TAC[]] THEN
      ASM_MESON_TAC[SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` MP_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `3 <= n ==> ~(n = 0)`)) THEN
    REWRITE_TAC[DIM_EQ_0; LEFT_IMP_EXISTS_THM; SET_RULE
     `~(s SUBSET {a}) <=> ?x. x IN s /\ ~(x = a)`] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    REWRITE_TAC[homeomorphism] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `--(&1) % x:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
    ASM_REWRITE_TAC[IN_DELETE; VECTOR_MUL_EQ_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[bilinear; linear]) THEN
    EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[VECTOR_MUL_LID; SUBSPACE_MUL; VECTOR_ARITH
     `x = --(&1) % x <=> x:real^N = vec 0`]]);;

let COMMUTATIVE_DIVISION_ALGEBRA = prove
 (`!m:real^N->real^N->real^N.
        bilinear m /\
        (!x y. m x y = m y x) /\
        (!x y. m x y = vec 0 ==> x = vec 0 \/ y = vec 0)
        ==> dimindex(:N) IN {1,2}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC(ARITH_RULE `1 <= n /\ n <= 2 ==> n = 1 \/ n = 2`) THEN
  REWRITE_TAC[DIMINDEX_GE_1] THEN REWRITE_TAC[GSYM DIM_UNIV] THEN
  MATCH_MP_TAC COMMUTATIVE_DIVISION_ALGEBRA_GEN THEN
  EXISTS_TAC `m:real^N->real^N->real^N` THEN
  ASM_REWRITE_TAC[SUBSPACE_UNIV; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Frobenius's theorem that there is no associative division algebra except  *)
(* in dimensions 1, 2 and 4. This has a more elementary purely algebraic     *)
(* proof, but since we have the commutative case proved above, we can make   *)
(* good use of it.                                                           *)
(* ------------------------------------------------------------------------- *)

let ASSOCIATIVE_DIVISION_ALGEBRA_HAS_IDENTITY = prove
 (`!m:real^N->real^N->real^N.
        bilinear m /\
        (!x y z. m (m x y) z = m x (m y z)) /\
        (!x y. m x y = vec 0 ==> x = vec 0 \/ y = vec 0)
        ==> ?e. (!x. m e x = x) /\ (!x. m x e = x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
  REWRITE_TAC[linear; FORALL_AND_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(basis 1:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. (m:real^N->real^N->real^N) (basis 1) e = basis 1`
  MP_TAC THENL
   [MP_TAC(ISPEC `(m:real^N->real^N->real^N) (basis 1)`
        LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[linear]; MESON_TAC[]] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `x:real^N = y <=> x + -- &1 % y = vec 0`] THEN
    SUBGOAL_THEN
     `!x y. (m:real^N->real^N->real^N) (basis 1) x + -- &1 % m (basis 1) y =
            m (basis 1) (x + -- &1 % y)`
     (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N` THEN
  ASM_CASES_TAC `e:real^N = vec 0` THENL
   [ASM_MESON_TAC[VECTOR_MUL_LZERO]; DISCH_TAC] THEN
  SUBGOAL_THEN `basis 1:real^N = vec 0 \/
                (m:real^N->real^N->real^N) e e + --(&1) % e = vec 0`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `x + --(&1) % y = vec 0 <=> x:real^N = y`] THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN
   `!x. (e:real^N = vec 0 \/ m e x - x:real^N = vec 0) /\
        (m x e - x = vec 0 \/ e = vec 0)`
   (fun th -> ASM_MESON_TAC[VECTOR_SUB_EQ; th]) THEN
  GEN_TAC THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x - y:real^N = x + --(&1) % y`] THEN
  ASM_MESON_TAC[VECTOR_ARITH `x + --(&1) % x:real^N = vec 0`]);;

let ASSOCIATIVE_DIVISION_ALGEBRA = prove
 (`!m:real^N->real^N->real^N.
        bilinear m /\
        (!x y z. m (m x y) z = m x (m y z)) /\
        (!x y. m x y = vec 0 ==> x = vec 0 \/ y = vec 0)
        ==> dimindex(:N) IN {1,2,4}`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `m:real^N->real^N->real^N`
    ASSOCIATIVE_DIVISION_ALGEBRA_HAS_IDENTITY) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
  REWRITE_TAC[linear; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(e:real^N = vec 0)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(basis 1:real^N = vec 0)` ASSUME_TAC THENL
     [SIMP_TAC[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1];
      ASM_MESON_TAC[VECTOR_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_CASES_TAC `span {e} = (:real^N)` THENL
   [FIRST_X_ASSUM(MP_TAC o SYM o AP_TERM `dim:(real^N->bool)->num`) THEN
    ASM_SIMP_TAC[DIM_SPAN; DIM_SING; DIM_UNIV; IN_INSERT];
    ONCE_REWRITE_TAC[IN_INSERT] THEN DISJ2_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `~(s = UNIV) ==> ?x. ~(x IN s)`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `j:real^N`) THEN
  SUBGOAL_THEN
   `!s. (!x y. x IN s /\ y IN s ==> (m:real^N->real^N->real^N) x y = m y x)
        ==> dim s <= 2`
  (LABEL_TAC "*") THENL
   [REPEAT STRIP_TAC THEN
    (X_CHOOSE_THEN `C:real^N->bool` MP_TAC o prove_inductive_relations_exist)
     `(!x:real^N. x IN s ==> C x) /\
      (!c x. C x ==> C(c % x)) /\
      (!x y. C x /\ C y ==> C(x + y)) /\
      (!x y. C x /\ C y ==> C(m x y))` THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    MP_TAC(SET_RULE `!x:real^N. C x <=> x IN C`) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x y. x IN C /\ y IN C ==> (m:real^N->real^N->real^N) x y = m y x`
    ASSUME_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
        TRANS_TAC EQ_TRANS `(m:real^N->real^N->real^N) (m z x) y` THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        TRANS_TAC EQ_TRANS `(m:real^N->real^N->real^N) (m x z) y` THEN
        ASM_MESON_TAC[];
        SIMP_TAC[] THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
        REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
        X_GEN_TAC `z:real^N` THEN ASM_CASES_TAC `(z:real^N) IN C` THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    TRANS_TAC LE_TRANS `dim(C:real^N->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIM_SUBSET THEN ASM_REWRITE_TAC[SUBSET]; ALL_TAC] THEN
    ASM_CASES_TAC `C:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[DIM_EMPTY; ARITH] THEN
    MATCH_MP_TAC COMMUTATIVE_DIVISION_ALGEBRA_GEN THEN
    EXISTS_TAC `m:real^N->real^N->real^N` THEN
    ASM_REWRITE_TAC[subspace] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY; VECTOR_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. (m:real^N->real^N->real^N) x (vec 0) = vec 0) /\
    (!x. (m:real^N->real^N->real^N) (vec 0) x = vec 0)`
  ASSUME_TAC THENL [ASM_MESON_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
  ABBREV_TAC `C = span{j:real^N,e}` THEN
  SUBGOAL_THEN `(e:real^N) IN C /\ j IN C` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN SIMP_TAC[SPAN_SUPERSET; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `subspace(C:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[SUBSPACE_SPAN]; REWRITE_TAC[subspace] THEN STRIP_TAC] THEN
  SUBGOAL_THEN `dim(C:real^N->bool) = 2` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN REWRITE_TAC[DIM_INSERT; DIM_SPAN] THEN
    ASM_REWRITE_TAC[SPAN_EMPTY; DIM_EMPTY; IN_SING] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^N. x IN C /\ y IN C ==> m x y IN C` ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN EXPAND_TAC "C" THEN
    MATCH_MP_TAC SPAN_INDUCT THEN ASM_REWRITE_TAC[subspace; IN_ELIM_THM] THEN
    EXPAND_TAC "C" THEN SIMP_TAC[SPAN_ADD; SPAN_MUL; SPAN_0] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "C" THEN MATCH_MP_TAC SPAN_INDUCT THEN
    ASM_REWRITE_TAC[subspace; IN_ELIM_THM] THEN EXPAND_TAC "C" THEN
    SIMP_TAC[SPAN_ADD; SPAN_MUL; SPAN_0] THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    EXPAND_TAC "C" THEN SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `{m j j:real^N,j,e}`) THEN
    ASM_REWRITE_TAC[DIM_INSERT; DIM_SING] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. i IN C /\ (m:real^N->real^N->real^N) i i = --e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(m:real^N->real^N->real^N) j j IN C` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "C" THEN
      SIMP_TAC[SPAN_SUPERSET; IN_INSERT];
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [SYM th])] THEN
    REWRITE_TAC[SPAN_2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
    ABBREV_TAC `k:real^N = j + (--a / &2) % e` THEN
    SUBGOAL_THEN `(m:real^N->real^N->real^N) k k = (b + a pow 2 / &4) % e`
    ASSUME_TAC THENL
     [EXPAND_TAC "k" THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "k" THEN
      REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `(k:real^N) IN C` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `inv(sqrt(--(b + a pow 2 / &4))) % k:real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; GSYM REAL_POW_2; REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_FIELD
     `x pow 2 = --y /\ ~(y = &0) ==> inv x pow 2 * y = --(&1)`) THEN
    REWRITE_TAC[SQRT_POW2; REAL_ARITH
     `&0 <= --x /\ ~(x = &0) <=> ~(&0 <= x)`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?c. k:real^N = --c % e` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [REWRITE_TAC[VECTOR_ARITH `k:real^N = --c % e <=> k + c % e = vec 0`] THEN
      MATCH_MP_TAC(MESON[] `(?c:real. P c \/ P(--c)) ==> ?c. P c`) THEN
      EXISTS_TAC `sqrt(b + a pow 2 / &4)` THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(x % e + --y % k) + (y % k + w % z % e):real^N = (x + w * z) % e`] THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_MUL_RNEG] THEN DISJ1_TAC THEN
      ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_ADD_RINV];
      UNDISCH_TAC `~(j IN span{e:real^N})` THEN
      REWRITE_TAC[SPAN_SING; IN_ELIM_THM; IN_UNIV] THEN
      ASM_MESON_TAC[VECTOR_ARITH
       `j + x % e:real^N = y % e ==> j = (y - x) % e`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i IN span {e:real^N})` ASSUME_TAC THENL
   [REWRITE_TAC[SPAN_SING; IN_ELIM_THM; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
    UNDISCH_TAC `(m:real^N->real^N->real^N) i i = --e` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH
     `c % c % e:real^N = --e <=> (c pow 2 + &1) % e = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> ~(x + &1 = &0)`) THEN
    REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i:real^N = vec 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SPAN_0]; ALL_TAC] THEN
  SUBGOAL_THEN `span{j:real^N,e} = span{i,e}` SUBST_ALL_TAC THENL
   [REWRITE_TAC[SPAN_EQ; SUBSET; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IN_SPAN_INSERT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `j:real^N`) o concl)) THEN
  SUBGOAL_THEN
   `{x | (m:real^N->real^N->real^N) i x = m x i} = C`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `t SUBSET s /\ (!a. a IN s /\ ~(a IN t) ==> F) ==> s = t`) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "C" THEN MATCH_MP_TAC SPAN_SUBSET_SUBSPACE THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; subspace; IN_ELIM_THM] THEN
      SIMP_TAC[];
      X_GEN_TAC `k:real^N` THEN EXPAND_TAC "C" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `{k:real^N,i,e}`) THEN
    REWRITE_TAC[DIM_INSERT] THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SPAN_EMPTY; IN_SING; DIM_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = {x | --((m:real^N->real^N->real^N) i x) = m x i}` THEN
  SUBGOAL_THEN `subspace(C:real^N->bool) /\ subspace(D:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "D"] THEN
    REWRITE_TAC[subspace; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `--x:real^N = y <=> x = --y`] THEN
    SIMP_TAC[] THEN CONV_TAC VECTOR_ARITH;
    MP_TAC(ASSUME `subspace(D:real^N->bool)`) THEN
    REWRITE_TAC[subspace] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL [`C:real^N->bool`; `D:real^N->bool`]
    DIM_UNION_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `C INTER D:real^N->bool = {vec 0}` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "D"] THEN
    REWRITE_TAC[IN_ELIM_THM; EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_ARITH
     `a:real^N = b /\ --a = b <=> a = vec 0 /\ b = vec 0`] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[DIM_SING; ADD_CLAUSES]] THEN
  SUBGOAL_THEN
   `dim(C UNION D:real^N->bool) = dimindex(:N)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM DIM_SPAN; GSYM DIM_UNIV] THEN AP_TERM_TAC THEN
    REWRITE_TAC[SPAN_UNION; SET_RULE `s = UNIV <=> !x. x IN s`] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `inv(&2) % (x + --(&1) % m i (m x i)):real^N` THEN
    EXISTS_TAC `inv(&2) % (x + m i (m x i)):real^N` THEN
    CONJ_TAC THENL [ALL_TAC; CONV_TAC VECTOR_ARITH] THEN
    CONJ_TAC THEN MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    MAP_EVERY EXPAND_TAC ["C"; "D"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN
    UNDISCH_THEN `!x y z. (m:real^N->real^N->real^N) (m x y) z = m x (m y z)`
     (fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  ASM_CASES_TAC `dim(D:real^N->bool) = 0` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; IN_INSERT] THEN DISCH_TAC THEN
  DISJ2_TAC THEN DISJ1_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 + d = 4 <=> d = 2`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [DIM_EQ_0]) THEN
  REWRITE_TAC[SET_RULE `~(s SUBSET {z}) <=> ?a. a IN s /\ ~(a = z)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `linear((m:real^N->real^N->real^N) k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[linear]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. (m:real^N->real^N->real^N) k x = m k y <=> x = y`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INJECTIVE_ALT] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `k:real^N = vec 0 \/ x + --(&1) % y:real^N = vec 0`
    MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `D = IMAGE ((m:real^N->real^N->real^N) k) C`
   (fun th -> ASM_SIMP_TAC[th; DIM_INJECTIVE_LINEAR_IMAGE]) THEN
  SUBGOAL_THEN
   `IMAGE ((m:real^N->real^N->real^N) k) C SUBSET D /\
    IMAGE ((m:real^N->real^N->real^N) k) D SUBSET C`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    UNDISCH_TAC `(k:real^N) IN D` THEN MAP_EVERY EXPAND_TAC ["C"; "D"] THEN
    REWRITE_TAC[VECTOR_ARITH `--x:real^N = y <=> x = --y`] THEN
    SIMP_TAC[IN_ELIM_THM] THEN
    UNDISCH_THEN `!x y z. (m:real^N->real^N->real^N) (m x y) z = m x (m y z)`
     (fun th -> REWRITE_TAC[GSYM th] THEN
                ASM_SIMP_TAC[VECTOR_NEG_MINUS1] THEN
                ASSUME_TAC th) THEN
    SIMP_TAC[] THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
    CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
  `IMAGE f c SUBSET d /\ IMAGE f d SUBSET c /\
   (!x y. f x = f y ==> x = y) /\
   IMAGE f (IMAGE f c) = c
   ==> d = IMAGE f c`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[SPAN_EQ_SELF]
   `subspace s /\ subspace t /\ span s = span t ==> s = t`) THEN
  ASM_SIMP_TAC[SUBSPACE_LINEAR_IMAGE] THEN
  MATCH_MP_TAC DIM_EQ_SPAN THEN
  ASM_SIMP_TAC[DIM_INJECTIVE_LINEAR_IMAGE; LE_REFL] THEN
  ASM SET_TAC[]);;
