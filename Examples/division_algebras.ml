(* ========================================================================= *)
(* Some nonexistence proofs for division algebras in higher dimensions.      *)
(* This does not (yet...) include the much more difficult restriction from   *)
(* Bott-Milnor-Kervaire to 1, 2, 4 or 8 dimensions, but does have the Hopf   *)
(* result that there is no *commutative* division algebra for dim > 2. Note  *)
(* also that there is no assumption of associativity or identity.            *)
(* ========================================================================= *)

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

let COMMUTATIVE_DIVISION_ALGEBRA = prove
 (`!m:real^N->real^N->real^N.
        bilinear m /\
        (!x y. m x y = m y x) /\
        (!x y. m x y = vec 0 ==> x = vec 0 \/ y = vec 0)
        ==> dimindex(:N) <= 2`,
  REWRITE_TAC[ARITH_RULE `n <= 2 <=> ~(3 <= n)`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!x y c. (m:real^N->real^N->real^N) x (c % y) = c % m x y) /\
    (!x y z. m x (y + z) = m x y + m x z)`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[bilinear; linear]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f:real^N->real^N = \x. m x x` THEN
  MP_TAC(ISPECL
   [`f:real^N->real^N`; `\x h. &2 % (m:real^N->real^N->real^N) x h`;
    `(:real^N) DELETE vec 0`; `(:real^N) DELETE vec 0`]
   INVERSE_FUNCTION_THEOREM_GLOBAL) THEN
  ASM_SIMP_TAC[NOT_IMP; SIMPLY_CONNECTED_PUNCTURED_UNIVERSE] THEN
  ASM_SIMP_TAC[GSYM CONJ_ASSOC; OPEN_DELETE; OPEN_UNIV; CONNECTED_OPEN_DELETE;
               CONNECTED_UNIV; ARITH_RULE `3 <= n ==> 2 <= n`] THEN
  SUBGOAL_THEN
   `!x. ((f:real^N->real^N) has_derivative (\h. &2 % m h x)) (at x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[VECTOR_ARITH `&2 % x:real^N = x + x`] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o ABS_CONV o LAND_CONV) [th]) THEN
    MP_TAC(ISPECL [`m:real^N->real^N->real^N`;
        `\x:real^N. x`; `\x:real^N. x`] HAS_DERIVATIVE_BILINEAR_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_DERIVATIVE_ID];
    ASM_REWRITE_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand o rand) PROPER_MAP o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_DELETE] THEN
      EXPAND_TAC "f" THEN ASM_MESON_TAC[];
      MATCH_MP_TAC(TAUT `p ==> (p <=> q /\ r) ==> q`)] THEN
    SUBGOAL_THEN `!x. (f:real^N->real^N) x = vec 0 <=> x = vec 0`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      ASM_MESON_TAC[VECTOR_ARITH `x + y:real^N = x <=> y = vec 0`];
      ALL_TAC] THEN
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN UNIV DELETE vec 0 /\ (f:real^N->real^N) x IN k} =
                  {x | x IN UNIV /\ (f:real^N->real^N) x IN k}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^N->real^N) continuous_on UNIV` ASSUME_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[DIFFERENTIABLE_ON_EQ_DIFFERENTIABLE_AT; OPEN_UNIV] THEN
      ASM_MESON_TAC[differentiable];
      ALL_TAC] THEN
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
      EXPAND_TAC "f" THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ASSUME
       `!x y. (m:real^N->real^N->real^N) x y = m y x`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_ASSOC; NORM_EQ_0; VECTOR_MUL_LID; REAL_FIELD
       `~(x = &0) ==> (x pow 2 * inv x) * inv x = &1`]];
    RULE_ASSUM_TAC(REWRITE_RULE[has_derivative]) THEN
    ASM_SIMP_TAC[MATRIX_INVERTIBLE_LEFT; GSYM INVERTIBLE_DET_NZ] THEN
    ASM_SIMP_TAC[GSYM LINEAR_INJECTIVE_LEFT_INVERSE_EQ;
                 LINEAR_INJECTIVE_0] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; IN_DELETE; IN_UNIV] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` (MP_TAC o CONJUNCT1)) THEN
    REWRITE_TAC[HOMEOMORPHISM; IN_DELETE; IN_UNIV] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(f:real^N->real^N) (--basis 1) = f (basis 1)
      ==> --basis 1:real^N = vec 0 \/ basis 1:real^N = vec 0 \/
          --basis 1:real^N = basis 1`
    MP_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "f"] THEN
    SIMP_TAC[VECTOR_NEG_EQ_0; VECTOR_ARITH `--x:real^N = x <=> x = vec 0`;
             BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[VECTOR_NEG_MINUS1] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC VECTOR_ARITH]);;
