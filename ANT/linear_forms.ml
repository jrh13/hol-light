(* ========================================================================= *)
(* The Minkowski linear forms theorem for real matrices, type-free: the      *)
(* rows and columns of a real matrix A are indexed by a finite set s in any  *)
(* type K (no type real^N) and the determinant is ring_det real_ring. If     *)
(* |det A| < prod c_i for positive c_i, some nonzero integer vector x has    *)
(* |(A x)_i| < c_i for all i; if s is nonempty and |det A| <= prod c_i, some *)
(* nonzero integer vector x has |(A x)_i| <= c_i for all i.                  *)
(*                                                                           *)
(* Main results: MINKOWSKI_LINEAR_FORMS_STRICT, MINKOWSKI_LINEAR_FORMS. On   *)
(* the way: the perturbation bound for products |prod f - prod g| <= B^(n-1) *)
(* sum |f - g| (PRODUCT_SUB_BOUND) and the Lipschitz bound for determinants  *)
(* of bounded real matrices (REAL_DET_SUB_BOUND), the left inverse of a real *)
(* matrix with nonzero determinant (REAL_MATRIX_LEFT_INVERSE), the case of   *)
(* integer matrices and cubes (INT_MATRIX_PIGEONHOLE) and the rounding of    *)
(* real matrices to integer matrices with controlled determinant             *)
(* (REAL_DET_ROUNDING).                                                      *)
(*                                                                           *)
(* Route (no measure theory). Strict version: scale the rows to c_i = 1. Let *)
(* C be a left inverse of A, K = sum |C_ij| and D >= 2 K. For a large        *)
(* integer Q the integer matrix M = floor(Q A) has 0 < |det M| < (Q - D)^n   *)
(* (REAL_DET_ROUNDING: det(M / Q) is close to det A). Two of the (Q - D)^n   *)
(* integer points of the cube [0, Q - D)^n are congruent modulo the image of *)
(* M (the coset count INT_COSETS_MATRIX_IMAGE of ANT/zlattice.ml), so M x    *)
(* has all coordinates in (D - Q, Q - D) for some nonzero integer vector x.  *)
(* Since |Q A_ij - M_ij| <= 1, the left inverse gives sum |x_j| <= 2 K, and  *)
(* then |(A x)_i| < (Q - D + 2 K) / Q <= 1. Compact version: apply the       *)
(* strict one with c_i (1 + 1 / (N + 1)); the integer points with            *)
(* |(A x)_i| <= 2 c_i are finitely many, which gives one N for all of them.  *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml (real_ring, REAL_RING_SUM,                    *)
(* REAL_RING_PRODUCT), Library/permutations.ml, Library/isum.ml,             *)
(* Library/products.ml (product), Library/floor.ml (floor), ANT/algmisc.ml   *)
(* (HAS_SIZE_INT_SEG_LT), Library/ring_det.ml (ring_det, cofactors and the   *)
(* adjugate), ANT/zlattice.ml (the coset count). No Multivariate files.      *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/permutations.ml";;
needs "Library/isum.ml";;
needs "Library/products.ml";;
needs "Library/floor.ml";;
needs "ANT/algmisc.ml";;
needs "Library/ring_det.ml";;
needs "ANT/zlattice.ml";;

(* ------------------------------------------------------------------------- *)
(* Perturbation bounds for products and for determinants of real matrices.   *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_SUB_BOUND = prove
 (`!s (f:A->real) g B.
        FINITE s /\ (!i. i IN s ==> abs(f i) <= B /\ abs(g i) <= B)
        ==> abs(product s f - product s g) <=
            B pow (CARD s - 1) * sum s (\i. abs(f i - g i))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; SUM_CLAUSES; CARD_CLAUSES; FORALL_IN_INSERT] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[SUC_SUB1] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(product t (f:A->real)) <= B pow CARD(t:A->bool)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_ABS; GSYM PRODUCT_CONST] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `B * B pow (CARD(t:A->bool) - 1) * sum t (\i. abs(f i - g i)) =
    B pow CARD t * sum t (\i. abs((f:A->real) i - g i))`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `t:A->bool = {}` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES; REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_MUL_ASSOC; GSYM(CONJUNCT2 real_pow); CARD_EQ_0;
                 ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((f:A->real) a - g a) * B pow CARD(t:A->bool) +
              B * B pow (CARD t - 1) * sum t (\i. abs(f i - g i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `abs(x * p - y * q) <= abs((x - y) * p) + abs(y * (p - q)) /\
      abs((x - y) * p) <= u /\ abs(y * (p - q)) <= v
      ==> abs(x * p - y * q:real) <= u + v`) THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let REAL_DET_SUB_BOUND = prove
 (`!s (f:A->A->real) g B d.
        FINITE s /\
        (!i j. i IN s /\ j IN s
               ==> abs(f i j) <= B /\ abs(g i j) <= B /\
                   abs(f i j - g i j) <= d)
        ==> abs(ring_det real_ring s f - ring_det real_ring s g) <=
            &(FACT(CARD s)) * &(CARD s) * B pow (CARD s - 1) * d`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ring_det; ring_sign; REAL_RING_CLAUSES; REAL_RING_SUM;
              REAL_RING_PRODUCT] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB; FINITE_PERMUTATIONS; GSYM CARD_PERMUTATIONS] THEN
  MATCH_MP_TAC SUM_ABS_BOUND THEN
  ASM_SIMP_TAC[FINITE_PERMUTATIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `p:A->A` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(if evenperm(p:A->A) then &1 else -- &1) = &1:real`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN REAL_ARITH_TAC; REWRITE_TAC[REAL_MUL_LID]] THEN
  MP_TAC(ISPECL [`s:A->bool`; `\i. (f:A->A->real) i (p i)`;
                 `\i. (g:A->A->real) i (p i)`; `B:real`] PRODUCT_SUB_BOUND) THEN
  ASM_SIMP_TAC[PERMUTES_IN_IMAGE] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> x <= a ==> x <= b`) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `n * b * d:real = b * n * d`] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES; CARD_CLAUSES; REAL_MUL_RZERO; REAL_MUL_LZERO;
                  REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN
    FIRST_X_ASSUM(X_CHOOSE_TAC `a:A` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((f:A->A->real) a a)` THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    MATCH_MP_TAC SUM_BOUND THEN ASM_SIMP_TAC[PERMUTES_IN_IMAGE]]);;

(* ------------------------------------------------------------------------- *)
(* A left inverse of a real matrix with nonzero determinant (the adjugate).  *)
(* ------------------------------------------------------------------------- *)

let REAL_MATRIX_LEFT_INVERSE = prove
 (`!s (A:K->K->real).
        FINITE s /\ ~(ring_det real_ring s A = &0)
        ==> ?C. !z i. i IN s
                      ==> sum s (\j. C i j * sum s (\k. A j k * z k)) = z i`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i j. ring_cofactor real_ring s (A:K->K->real) j i /
                    ring_det real_ring s A` THEN
  MAP_EVERY X_GEN_TAC [`z:K->real`; `i:K`] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `A:K->K->real`; `i:K`]
    RING_DET_ADJUGATE_COLUMNS) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; REAL_RING_SUM; IN_UNIV] THEN
  DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `sum s (\k. if k = i then (z:K->real) i else &0)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[SUM_DELTA]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:K`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `c / d * a * z:real = (c * a) * z / d`] THEN
  REWRITE_TAC[SUM_RMUL] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_CASES_TAC `k:K = i` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[REAL_DIV_LMUL];
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(i:K = k)` (fun th -> REWRITE_TAC[th; REAL_MUL_LZERO]) THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Integer matrices and cubes: the pigeonhole principle on the cosets of the *)
(* image, and the rounding of a real matrix to an integer one.               *)
(* ------------------------------------------------------------------------- *)

let INT_MATRIX_PIGEONHOLE = prove
 (`!s (M:K->K->int) N.
        FINITE s /\ ~(ring_det integer_ring s M = &0) /\
        num_of_int(abs(ring_det integer_ring s M)) < N EXP CARD s
        ==> ?x. (!j. ~(j IN s) ==> x j = &0) /\
                (?j. j IN s /\ ~(x j = &0)) /\
                !i. i IN s ==> abs(isum s (\j. M i j * x j)) < &N`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = int_matrix_image s (M:K->K->int)` THEN
  ABBREV_TAC
   `G = {g:K->int | (!i. i IN s ==> g i IN {k | &0 <= k /\ k < &N}) /\
                    (!i. ~(i IN s) ==> g i = &0)}` THEN
  SUBGOAL_THEN `(G:(K->int)->bool) HAS_SIZE N EXP CARD(s:K->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN
    ASM_REWRITE_TAC[HAS_SIZE_INT_SEG_LT; HAS_SIZE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\i:K. &0:int) IN L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN MATCH_MP_TAC INT_LATTICE_0 THEN
    EXISTS_TAC `s:K->bool` THEN ASM_SIMP_TAC[INT_LATTICE_INT_MATRIX_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!g:K->int. g IN G <=>
               (!i. i IN s ==> &0 <= g i /\ g i < &N) /\
               (!i. ~(i IN s) ==> g i = &0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g g'. g IN G /\ g' IN G /\ ~(g = g') /\
           (\i. (g:K->int) i - g' i) IN L`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(LABEL_TAC "inj" o REWRITE_RULE[NOT_EXISTS_THM;
      TAUT `~(a /\ b /\ ~c /\ d) <=> a /\ b /\ d ==> c`]) THEN
    MP_TAC(ISPECL [`s:K->bool`; `M:K->K->int`] INT_COSETS_MATRIX_IMAGE) THEN
    MP_TAC(ISPECL
     [`\g:K->int. {y | (!i. ~(i IN s) ==> y i = &0) /\
                       (\i. y i - g i) IN L}`;
      `G:(K->int)->bool`; `N EXP CARD(s:K->bool)`] HAS_SIZE_IMAGE_INJ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`g:K->int`; `g':K->int`] THEN
      REWRITE_TAC[] THEN STRIP_TAC THEN
      REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `g:K->int` o REWRITE_RULE[EXTENSION]) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; INT_SUB_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`IMAGE (\g:K->int. {y | (!i. ~(i IN s) ==> y i = &0) /\
                             (\i. y i - g i) IN L}) G`;
      `int_cosets s (L:(K->int)->bool)`] CARD_SUBSET) THEN
    ASM_REWRITE_TAC[NOT_IMP; NOT_LE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; int_cosets; IN_ELIM_THM] THEN
    X_GEN_TAC `g:K->int` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `g:K->int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. i IN s ==> abs((g:K->int) i - g' i) < &N) /\
    (!i. ~(i IN s) ==> g i = g' i)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(g:K->int) IN G`; `(g':K->int) IN G`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC(INT_ARITH
     `&0 <= x /\ x < n /\ &0 <= y /\ y < n ==> abs(x - y:int) < n`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(\i. (g:K->int) i - g' i) IN L` THEN EXPAND_TAC "L" THEN
  REWRITE_TAC[INT_MATRIX_IMAGE_IN; FUN_EQ_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:K->int`) THEN
  EXISTS_TAC `\j. if j IN s then (z:K->int) j else &0` THEN
  SUBGOAL_THEN
   `!i. isum s (\j. (M:K->K->int) i j * (if j IN s then z j else &0)) =
        isum s (\j. M i j * z j)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    UNDISCH_TAC `~(g:K->int = g')` THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`] THEN
    DISCH_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:K` THEN
    ASM_CASES_TAC `(i:K) IN s` THEN ASM_SIMP_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM INT_SUB_0] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ISUM_EQ_0 THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_SIMP_TAC[INT_MUL_RZERO];
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[]]);;

let REAL_DET_ROUNDING = prove
 (`!s (A:K->K->real) D.
        FINITE s /\ ~(ring_det real_ring s A = &0) /\
        abs(ring_det real_ring s A) < &1
        ==> ?Q M:K->K->int.
                D < Q /\
                (!i j. real_of_int(M i j) <= &Q * A i j /\
                       &Q * A i j < real_of_int(M i j) + &1) /\
                ~(ring_det integer_ring s M = &0) /\
                num_of_int(abs(ring_det integer_ring s M)) <
                (Q - D) EXP CARD s`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `n = CARD(s:K->bool)` THEN
  ABBREV_TAC `a = ring_det real_ring s (A:K->K->real)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
    UNDISCH_TAC `ring_det real_ring s (A:K->K->real) = a` THEN
    ASM_REWRITE_TAC[RING_DET_EMPTY; REAL_RING_CLAUSES] THEN
    UNDISCH_TAC `abs(a:real) < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?R. &0 <= R /\ !i j. i IN s /\ j IN s ==> abs((A:K->K->real) i j) <= R`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `sum s (\i. sum s (\j. abs((A:K->K->real) i j)))` THEN
    SIMP_TAC[SUM_POS_LE; REAL_ABS_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\j. abs((A:K->K->real) i j))` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\j. abs((A:K->K->real) i j)`;
                     `sum s (\j. abs((A:K->K->real) i j))`; `s:K->bool`]
        SUM_POS_BOUND);
      MP_TAC(ISPECL [`\i. sum s (\j. abs((A:K->K->real) i j))`;
                     `sum s (\i. sum s (\j. abs((A:K->K->real) i j)))`;
                     `s:K->bool`] SUM_POS_BOUND)] THEN
    ASM_SIMP_TAC[REAL_LE_REFL; REAL_ABS_POS; SUM_POS_LE];
    ALL_TAC] THEN
  ABBREV_TAC `L = &(FACT n) * &n * (R + &1:real) pow (n - 1)` THEN
  SUBGOAL_THEN `&0 <= L:real` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
    UNDISCH_TAC `&0 <= R:real` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `min (abs a) (&1 - abs(a:real))` REAL_ARCH) THEN
  ASM_SIMP_TAC[REAL_LT_MIN; GSYM REAL_ABS_NZ; REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_TAC `Q:num` o SPEC `&n * &D + L:real`) THEN
  SUBGOAL_THEN
   `L < &Q * abs a /\ &n * &D + L < &Q * (&1 - abs(a:real))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 <= &n * &D:real /\ &Q * min (abs a) (&1 - abs a) <= &Q * abs a /\
      &Q * min (abs a) (&1 - abs a) <= &Q * (&1 - abs(a:real))`
    MP_TAC THENL
     [SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_MIN_MIN];
      UNDISCH_TAC `&n * &D + L < &Q * min (abs a) (&1 - abs(a:real))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `D < Q /\ &1 <= &Q:real` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LT; REAL_OF_NUM_LE; ARITH_RULE
     `1 <= Q <=> 0 < Q`; GSYM REAL_OF_NUM_LT] THEN
    SUBGOAL_THEN `&0 <= &Q * abs(a:real) /\ &D <= &n * &D:real` MP_TAC THENL
     [SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_ABS_POS] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS] THEN
      UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`&0 <= L:real`; `&n * &D + L < &Q * (&1 - abs(a:real))`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?M:K->K->int. !i j. real_of_int(M i j) <= &Q * A i j /\
                        &Q * A i j < real_of_int(M i j) + &1`
  (X_CHOOSE_TAC `M:K->K->int`) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN REPEAT GEN_TAC THEN
    EXISTS_TAC `int_of_real(floor(&Q * (A:K->K->real) i j))` THEN
    SIMP_TAC[REAL_OF_INT_OF_REAL; FLOOR];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Q:num`; `M:K->K->int`] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `P = (&Q:real) pow (n - 1)` THEN
  SUBGOAL_THEN `&0 < P /\ (&Q:real) pow n = &Q * P` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&1 <= &Q:real` THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM(CONJUNCT2 real_pow);
                   ARITH_RULE `~(n = 0) ==> SUC(n - 1) = n`]];
    ALL_TAC] THEN
  ABBREV_TAC
   `m = ring_det real_ring s (\i j. real_of_int((M:K->K->int) i j))` THEN
  SUBGOAL_THEN `abs(&Q * P * a - m:real) <= P * L` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:K->bool`; `\i j. &Q * (A:K->K->real) i j`;
                   `\i j. real_of_int((M:K->K->int) i j)`;
                   `&Q * (R + &1):real`; `&1:real`] REAL_DET_SUB_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `abs(&Q * (A:K->K->real) i j) <= &Q * R` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_LE_LMUL; REAL_POS];
        ALL_TAC] THEN
      UNDISCH_TAC `&1 <= &Q:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`i:K`; `j:K`]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `A:K->K->real`; `&Q:real`]
      RING_DET_CMUL) THEN
    ASM_REWRITE_TAC[REAL_FIELD_CLAUSES; IN_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[REAL_POW_MUL; REAL_MUL_RID] THEN
    EXPAND_TAC "L" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&Q * P - (&Q - &D) pow n) <= P * &n * &D:real`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:K->bool`; `\i:K. (&Q:real)`; `\i:K. &Q - &D:real`;
                   `&Q:real`] PRODUCT_SUB_BOUND) THEN
    ASM_SIMP_TAC[PRODUCT_CONST; SUM_CONST; REAL_OF_NUM_LE; REAL_ABS_NUM;
                 LE_REFL; REAL_LE_REFL; LT_IMP_LE; REAL_ARITH
                  `&D <= q ==> abs(q - &D) <= q /\ abs(q - (q - &D)) = &D:real`]
    THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(&Q * P * a:real) = &Q * P * abs a` ASSUME_TAC THENL
   [SIMP_TAC[REAL_ABS_MUL; REAL_ABS_NUM; ASSUME `&0 < P:real`;
             REAL_ARITH `&0 < p ==> abs p = p:real`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < P * (&Q * abs a - L) /\
                &0 < P * (&Q * (&1 - abs a) - (&n * &D + L:real))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_SUB_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_of_int(ring_det integer_ring s (M:K->K->int)) = m`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC RING_DET_HOMOMORPHISM THEN
    ASM_REWRITE_TAC[INTEGER_RING; IN_UNIV; REWRITE_RULE[REAL_RING_OF_INT]
     (ISPEC `real_ring` RING_HOMOMORPHISM_INTEGER_RING_OF_INT)];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_LT; int_eq; int_of_num_th] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS] THEN
  ASM_REWRITE_TAC[int_lt; int_abs_th; int_of_num_th] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs(&Q * P * a - m:real) <= P * L`;
    `abs(&Q * P - (&Q - &D) pow n) <= P * &n * &D:real`;
    `abs(&Q * P * a:real) = &Q * P * abs a`;
    `&0 < P * (&Q * abs a - L:real)`;
    `&0 < P * (&Q * (&1 - abs a) - (&n * &D + L:real))`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Minkowski linear forms theorem.                                       *)
(* ------------------------------------------------------------------------- *)

let MINKOWSKI_LINEAR_FORMS_STRICT = prove
 (`!s (A:K->K->real) c.
        FINITE s /\ ~(ring_det real_ring s A = &0) /\
        (!i. i IN s ==> &0 < c i) /\
        abs(ring_det real_ring s A) < product s c
        ==> ?x:K->int.
                (!j. ~(j IN s) ==> x j = &0) /\
                (?j. j IN s /\ ~(x j = &0)) /\
                !i. i IN s
                    ==> abs(sum s (\j. A i j * real_of_int(x j))) < c i`,
  let scale = prove
   (`!c y. &0 < c ==> (abs(inv c * y) < &1 <=> abs y < c)`,
    SIMP_TAC[REAL_ABS_MUL; REAL_ABS_INV; REAL_ARITH `&0 < c ==> abs c = c:real`;
             ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div);
             REAL_LT_LDIV_EQ; REAL_MUL_LID]) in
  let lemma = prove
   (`!s (A:K->K->real).
        FINITE s /\ ~(ring_det real_ring s A = &0) /\
        abs(ring_det real_ring s A) < &1
        ==> ?x:K->int.
                (!j. ~(j IN s) ==> x j = &0) /\
                (?j. j IN s /\ ~(x j = &0)) /\
                !i. i IN s
                    ==> abs(sum s (\j. A i j * real_of_int(x j))) < &1`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:K->bool`; `A:K->K->real`] REAL_MATRIX_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:K->K->real` (LABEL_TAC "inv")) THEN
    ABBREV_TAC `b = sum s (\i. sum s (\j. abs((C:K->K->real) i j)))` THEN
    X_CHOOSE_TAC `D:num` (SPEC `&2 * b:real` REAL_ARCH_SIMPLE) THEN
    MP_TAC(ISPECL [`s:K->bool`; `A:K->K->real`; `D:num`]
      REAL_DET_ROUNDING) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`Q:num`; `M:K->K->int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "fl") STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `&0 < &Q:real /\ &D <= &Q:real` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `D:num < Q` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:K->bool`; `M:K->K->int`; `Q:num - D`]
      INT_MATRIX_PIGEONHOLE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `x:K->int` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `w = sum s (\j. abs(real_of_int((x:K->int) j)))` THEN
    SUBGOAL_THEN `&0 <= w:real` ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[REAL_ABS_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. i IN s
          ==> abs(&Q * sum s (\j. (A:K->K->real) i j * real_of_int(x j))) <
              (&Q - &D) + w`
    (LABEL_TAC "Ax") THENL
     [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      REMOVE_THEN "small" (MP_TAC o SPEC `i:K`) THEN
      ASM_REWRITE_TAC[int_lt; int_abs_th; int_isum; int_mul_th;
                      int_of_num_th] THEN
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(v - u) <= w ==> abs u < q ==> abs v < q + w:real`) THEN
      EXPAND_TAC "w" THEN
      SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB; ASSUME `FINITE(s:K->bool)`] THEN
      MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_ARITH `q * a * x - m * x:real = (q * a - m) * x`;
                  REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      USE_THEN "fl" (MP_TAC o SPECL [`i:K`; `j:K`]) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&Q * w <= b * (&Q + w:real)` ASSUME_TAC THENL
     [SUBGOAL_THEN
       `&Q * w = sum s (\r. &Q * abs(real_of_int((x:K->int) r))) /\
        b * (&Q + w) =
        sum s (\r. sum s (\j. abs((C:K->K->real) r j)) * (&Q + w))`
      (fun th -> REWRITE_TAC[th]) THENL
       [MAP_EVERY EXPAND_TAC ["w"; "b"] THEN REWRITE_TAC[SUM_LMUL; SUM_RMUL];
        ALL_TAC] THEN
      MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:K` THEN DISCH_TAC THEN
      REMOVE_THEN "inv"
       (MP_TAC o SPECL [`\j. real_of_int((x:K->int) j)`; `r:K`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `abs(sum s (\j. (C:K->K->real) r j *
                       (&Q * sum s (\k. A j k * real_of_int((x:K->int) k)))))`
      THEN CONJ_TAC THENL
       [SUBGOAL_THEN
         `sum s (\j. (C:K->K->real) r j *
                     (&Q * sum s (\k. A j k * real_of_int((x:K->int) k)))) =
          &Q * sum s (\j. C r j * sum s (\k. A j k * real_of_int(x k)))`
        SUBST1_TAC THENL
         [TRANS_TAC EQ_TRANS
           `sum s (\j. &Q * ((C:K->K->real) r j *
                      sum s (\k. A j k * real_of_int((x:K->int) k))))` THEN
          CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_LMUL]] THEN
          MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
          REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_LE_REFL]];
        MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `j:K` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
        MATCH_MP_TAC(REAL_ARITH `abs y < q - &D + w ==> abs y <= q + w:real`)
        THEN
        USE_THEN "Ax" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `w <= &2 * b:real` ASSUME_TAC THENL
     [SUBGOAL_THEN `(&2 * b) * w <= &Q * w:real` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&D:real` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `&Q * w <= b * (&Q + w:real)` THEN
      MATCH_MP_TAC(REAL_ARITH
       `(&Q * w <= &Q * (&2 * b) ==> w <= &2 * b:real)
        ==> &Q * w <= b * (&Q + w) ==> (&2 * b) * w <= &Q * w
            ==> w <= &2 * b`) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ];
      ALL_TAC] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REMOVE_THEN "Ax" (MP_TAC o SPEC `i:K`) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(&Q * y < &Q * &1 ==> y < &1) /\ w <= &2 * b /\ &2 * b <= &D:real
      ==> &Q * y < (&Q - &D) + w ==> y < &1`) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `\i j. inv((c:K->real) i) * (A:K->K->real) i j`]
    lemma) THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `\i. inv((c:K->real) i)`;
                 `A:K->K->real`] RING_DET_ROWS_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_PRODUCT] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[PRODUCT_INV; REAL_ENTIRE; REAL_INV_EQ_0; scale;
               PRODUCT_POS_LT; REAL_LT_IMP_NZ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:K->int` THEN
  MATCH_MP_TAC(TAUT `(c ==> d) ==> a /\ b /\ c ==> a /\ b /\ d`) THEN
  DISCH_TAC THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; SUM_LMUL; scale]);;

let MINKOWSKI_LINEAR_FORMS = prove
 (`!s (A:K->K->real) c.
        FINITE s /\ ~(s = {}) /\ ~(ring_det real_ring s A = &0) /\
        (!i. i IN s ==> &0 < c i) /\
        abs(ring_det real_ring s A) <= product s c
        ==> ?x:K->int.
                (!j. ~(j IN s) ==> x j = &0) /\
                (?j. j IN s /\ ~(x j = &0)) /\
                !i. i IN s
                    ==> abs(sum s (\j. A i j * real_of_int(x j))) <= c i`,
  let finite = prove
   (`!s (A:K->K->real) b.
        FINITE s /\ ~(ring_det real_ring s A = &0)
        ==> FINITE {x:K->int | (!j. ~(j IN s) ==> x j = &0) /\
                               !i. i IN s
                                   ==> abs(sum s (\j. A i j *
                                                      real_of_int(x j)))
                                       <= b i}`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:K->bool`; `A:K->K->real`] REAL_MATRIX_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `C:K->K->real`) THEN
    X_CHOOSE_TAC `N:num`
     (SPEC `sum s (\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i)))`
       REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{x:K->int | (!j. j IN s ==> x j IN {k | --(&N) <= k /\ k <= &N}) /\
                  (!j. ~(j IN s) ==> x j = &0)}` THEN
    ASM_SIMP_TAC[FINITE_FUNSPACE; FINITE_INT_SEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:K->int` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM INT_ABS_BOUNDS; int_le; int_abs_th; int_of_num_th] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`\j. real_of_int((x:K->int) j)`; `k:K`] o
      check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum s (\i. abs((C:K->K->real) k i) * abs(b i))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `i:K` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= abs b:real`) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sum s (\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i)))` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL
       [`\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i))`;
        `sum s (\k. sum s (\i. abs((C:K->K->real) k i) * abs(b i)))`;
        `s:K->bool`] SUM_POS_BOUND) THEN
      ASM_SIMP_TAC[REAL_LE_REFL; SUM_POS_LE; REAL_LE_MUL; REAL_ABS_POS]]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:K->bool`; `A:K->K->real`; `\i. &2 * (c:K->real) i`]
    finite) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `S = {x:K->int | (!j. ~(j IN s) ==> x j = &0) /\
                    !i. i IN s
                        ==> abs(sum s (\j. (A:K->K->real) i j *
                                           real_of_int(x j))) <= &2 * c i}` THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!x. x IN S /\ (?j. j IN s /\ ~(x j = &0))
        ==> ?n. ~(n = 0) /\
                ?i. i IN s /\
                    (c:K->real) i * (&1 + inv(&n)) <
                    abs(sum s (\j. (A:K->K->real) i j * real_of_int(x j)))`
  MP_TAC THENL
   [X_GEN_TAC `x:K->int` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:K->int`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:K` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC
     `(abs(sum s (\j. (A:K->K->real) i j * real_of_int((x:K->int) j))) -
       c i) / c i` REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_RDIV_EQ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:K` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(K->int)->num` (LABEL_TAC "m")) THEN
  MP_TAC(ISPEC `IMAGE (m:(K->int)->num) S` num_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "N")) THEN
  MP_TAC(ISPECL [`s:K->bool`; `A:K->K->real`;
                 `\i. (c:K->real) i * (&1 + inv(&N + &1))`]
    MINKOWSKI_LINEAR_FORMS_STRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 < &1 + inv(&N + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `product s (c:K->real)` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_LMUL THEN
      ASM_SIMP_TAC[PRODUCT_POS_LT; REAL_POW_LT_1; CARD_EQ_0]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:K->int` (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lt" o BETA_RULE)))) THEN
  SUBGOAL_THEN `(x:K->int) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    USE_THEN "lt" (MP_TAC o C MATCH_MP (ASSUME `(i:K) IN s`)) THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < c /\ c * t <= c * &1 ==> y < c * (&1 + t) ==> y <= &2 * c:real`)
    THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "N" (MP_TAC o C MATCH_MP (ASSUME `(x:K->int) IN S`)) THEN
  REMOVE_THEN "m" (MP_TAC o SPEC `x:K->int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `i:K`
    STRIP_ASSUME_TAC)) THEN
  DISCH_TAC THEN
  USE_THEN "lt" (MP_TAC o C MATCH_MP (ASSUME `(i:K) IN s`)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `c * (&1 + t) <= c * (&1 + inv(&((m:(K->int)->num) x))) /\
    c * (&1 + inv(&(m x))) < y
    ==> y < c * (&1 + t) ==> F`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_LADD] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; REAL_OF_NUM_ADD; REAL_OF_NUM_LE;
               ARITH_RULE `m <= N ==> m <= N + 1`]);;

(* ------------------------------------------------------------------------- *)
(* Real quadratic forms: completing the square and the Schur complement.     *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FORM_COMPLETE_SQUARE = prove
 (`!a t (A:K->K->real) (x:K->real).
        FINITE t /\ ~(a IN t) /\ ~(A a a = &0) /\
        (!i. i IN t ==> A i a = A a i)
        ==> sum (a INSERT t) (\i. sum (a INSERT t) (\j. A i j * x i * x j)) =
            A a a * (x a + sum t (\j. A a j * x j) / A a a) pow 2 +
            sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) *
                                   x i * x j))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; ASSUME `FINITE(t:K->bool)`] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u = sum t (\j. (A:K->K->real) a j * x j)` THEN
  SUBGOAL_THEN `sum t (\j. (A:K->K->real) a j * x a * x j) = x a * u`
  SUBST1_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\i. (A:K->K->real) i a * x i * x a +
               sum t (\j. A i j * x i * x j)) =
    x a * u + sum t (\i. sum t (\j. A i j * x i * x j))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    EXPAND_TAC "u" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
                          x i * x j)) =
    sum t (\i. sum t (\j. A i j * x i * x j)) - u pow 2 / A a a`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `(a - b * c / d) * x * y:real = a * x * y - (b * x / d) * (c * y)`] THEN
    ASM_SIMP_TAC[SUM_SUB; SUM_LMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[SUM_RMUL] THEN
    SUBGOAL_THEN `sum t (\i. (A:K->K->real) i a * x i / A a a) = u / A a a`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC; SUM_RMUL] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN EXPAND_TAC "u" THEN
      MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
      REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  UNDISCH_TAC `~((A:K->K->real) a a = &0)` THEN CONV_TAC REAL_FIELD);;

let REAL_DET_SCHUR_COMPLEMENT = prove
 (`!a t (A:K->K->real).
        FINITE t /\ ~(a IN t) /\ ~(A a a = &0)
        ==> ring_det real_ring (a INSERT t) A =
            A a a *
            ring_det real_ring t (\i j. A i j - A i a * A a j / A a a)`,
  let lemma = prove
   (`!p (c:real) x. (if p then c else &0) * x = if p then c * x else &0`,
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`real_ring`; `(a:K) INSERT t`;
    `\i k. (if k = i then &1 else &0) +
           (if k = a then (if i IN t then (A:K->K->real) i a / A a a else &0)
            else &0)`;
    `\i j. if i IN t then (A:K->K->real) i j - A i a * A a j / A a a
           else A i j`] RING_DET_MUL) THEN
  REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM; FINITE_INSERT] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[]
   `x = x' /\ y = y' ==> x' = y' ==> (x:real) = y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
    STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; lemma; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[SUM_ADD; FINITE_INSERT; SUM_DELTA; IN_INSERT;
                 REAL_MUL_LID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ADD_RID] THEN
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_det real_ring ((a:K) INSERT t)
     (\i k. (if k = i then &1 else &0) +
            (if k = a then (if i IN t then (A:K->K->real) i a / A a a else &0)
             else &0)) = &1`
  SUBST1_TAC THENL
   [SUBST1_TAC(SET_RULE `(a:K) INSERT t = {a} UNION t`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_BLOCK_TRIANGULAR o
      lhand o snd) THEN
    ASM_REWRITE_TAC[FINITE_SING; REAL_RING_CLAUSES; IN_UNIV; IN_SING] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(j:K = a)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[REAL_ADD_RID]];
      DISCH_THEN SUBST1_TAC] THEN
    SIMP_TAC[RING_DET_SING; REAL_RING_CLAUSES; IN_UNIV] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID; REAL_MUL_LID] THEN
    TRANS_TAC EQ_TRANS
     `ring_det real_ring t (\i j:K. if i = j then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC RING_DET_EQ THEN MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN
      STRIP_TAC THEN SUBGOAL_THEN `~(j:K = a)` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
      SUBGOAL_THEN `(j:K = i) <=> (i = j)` SUBST1_TAC THENL
       [MESON_TAC[]; REWRITE_TAC[]];
      MP_TAC(ISPECL [`real_ring`; `t:K->bool`] RING_DET_I) THEN
      ASM_REWRITE_TAC[REAL_RING_CLAUSES]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  SUBST1_TAC(SET_RULE `(a:K) INSERT t = t UNION {a}`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_BLOCK_TRIANGULAR o
    rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_SING; REAL_RING_CLAUSES; IN_UNIV; IN_SING] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((A:K->K->real) a a = &0)` THEN CONV_TAC REAL_FIELD;
    DISCH_THEN SUBST1_TAC] THEN
  SIMP_TAC[RING_DET_SING; REAL_RING_CLAUSES; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_RING `x = y ==> a * x = y * a:real`) THEN
  MATCH_MP_TAC RING_DET_EQ THEN SIMP_TAC[]);;

let QUADRATIC_FORM_BASIS_VECTOR = prove
 (`!s (A:K->K->real) a.
        FINITE s /\ a IN s
        ==> sum s (\i. sum s (\j. A i j * (if i = a then &1 else &0) *
                                          (if j = a then &1 else &0))) =
            A a a`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH
              `(a:real) * (if p then &1 else &0) * (if q then &1 else &0) =
                          if q then if p then a else &0 else &0`] THEN
  ASM_SIMP_TAC[SUM_DELTA]);;

let QUADRATIC_FORM_SCHUR_POSITIVE = prove
 (`!a t (A:K->K->real).
        FINITE t /\ ~(a IN t) /\
        (!i j. i IN a INSERT t /\ j IN a INSERT t ==> A i j = A j i) /\
        (!x. (?i. i IN a INSERT t /\ ~(x i = &0))
             ==> &0 < sum (a INSERT t) (\i. sum (a INSERT t)
                                              (\j. A i j * x i * x j)))
        ==> &0 < A a a /\
            (!i j. i IN t /\ j IN t
                   ==> A i j - A i a * A a j / A a a =
                       A j i - A j a * A a i / A a a) /\
            (!y. (?i. i IN t /\ ~(y i = &0))
                 ==> &0 < sum t (\i. sum t
                                 (\j. (A i j - A i a * A a j / A a a) *
                                                y i * y j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) ==> p /\ q /\ r`) THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\i:K. if i = a then &1:real else &0`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [EXISTS_TAC `a:K` THEN REWRITE_TAC[IN_INSERT] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[QUADRATIC_FORM_BASIS_VECTOR; FINITE_INSERT; IN_INSERT]];
    DISCH_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(A:K->K->real) i j = A j i /\ A i a = A a i /\ A a j = A j a`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  X_GEN_TAC `y:K->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\i:K. if i = a then --(sum t (\j. (A:K->K->real) a j * y j)) / A a a
          else y i`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [EXISTS_TAC `i:K` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`a:K`; `t:K->bool`; `A:K->K->real`;
    `\i:K. if i = a then --(sum t (\j. (A:K->K->real) a j * y j)) / A a a
           else y i`] QUADRATIC_FORM_COMPLETE_SQUARE)) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN ASM_MESON_TAC[IN_INSERT];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN t
        ==> (if j = a then --(sum t (\j. (A:K->K->real) a j * y j)) / A a a
             else y j) = y j`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\j. (A:K->K->real) a j *
               (if j = a then --(sum t (\j. A a j * y j)) / A a a else y j)) =
    sum t (\j. A a j * y j)`
  SUBST1_TAC THENL [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum t (\i. sum t (\j. ((A:K->K->real) i j - A i a * A a j / A a a) *
     (if i = a then --(sum t (\j. A a j * y j)) / A a a else y i) *
     (if j = a then --(sum t (\j. A a j * y j)) / A a a else y j))) =
    sum t (\i. sum t (\j. (A i j - A i a * A a j / A a a) * y i * y j))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `(x:real) = &0 ==> &0 < x + y ==> &0 < y`) THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0] THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    REWRITE_TAC[real_div] THEN CONV_TAC REAL_RING]);;

let QUADRATIC_FORM_POS_LE = prove
 (`!s (A:K->K->real) x.
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j)))
        ==> &0 <= sum s (\i. sum s (\j. A i j * x i * x j))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
    `?i:K. i IN s /\ ~((x:K->real) i = &0)` THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EXISTS_THM; TAUT
     `~(p /\ ~q) <=> p ==> q`]) THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* A nonzero integer vector of least value under a positive definite form is *)
(* primitive.                                                                *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FORM_MINIMAL_PRIMITIVE = prove
 (`!s (A:K->K->real) (x:K->int).
        FINITE s /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j))) /\
        (!i. ~(i IN s) ==> x i = &0) /\ (?i. i IN s /\ ~(x i = &0)) /\
        (!y:K->int.
           (!i. ~(i IN s) ==> y i = &0) /\ (?i. i IN s /\ ~(y i = &0))
           ==> sum s (\i. sum s (\j. A i j * real_of_int(x i) *
                                    real_of_int(x j))) <=
               sum s (\i. sum s (\j. A i j * real_of_int(y i) *
                                    real_of_int(y j))))
        ==> !d. (!i. i IN s ==> d divides x i) ==> d divides &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `d:int` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(d:int = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `!i:K. i IN s ==> &0 divides (x:K->int) i` THEN
    REWRITE_TAC[INTEGER_RULE `(&0:int) divides x <=> x = &0`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:K->int. !i. (x:K->int) i = d * w i` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `k:K` THEN
    ASM_CASES_TAC `(k:K) IN s` THENL
     [ASM_MESON_TAC[int_divides]; EXISTS_TAC `&0:int`] THEN
    ASM_SIMP_TAC[INT_MUL_RZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:K->int`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `k:K` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(d:int) * (w:K->int) k = &0` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_REWRITE_TAC[INT_ENTIRE]];
      EXISTS_TAC `i:K` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((x:K->int) i = &0)` THEN
      ASM_REWRITE_TAC[INT_MUL_RZERO]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[int_mul_th] THEN
  REWRITE_TAC[REAL_ARITH
   `a * (d * x) * d * y:real = (d pow 2) * (a * x * y)`] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN
   `&0 < sum s (\i. sum s (\j. (A:K->K->real) i j * real_of_int(w i) *
                               real_of_int((w:K->int) j)))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\i. real_of_int((w:K->int) i)` o
      check (fun th -> is_forall(concl th) &&
                       free_in `A:K->K->real` (concl th))) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `i:K` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM int_of_num_th; GSYM int_eq] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:K->int) i = &0)` THEN
    ASM_REWRITE_TAC[INT_MUL_RZERO];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs(real_of_int d) <= &1` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_LE_SQUARE_ABS] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(&1:real) pow 2`; `real_of_int d pow 2`;
      `sum s (\i. sum s (\j. (A:K->K->real) i j * real_of_int(w i) *
                             real_of_int((w:K->int) j)))`] REAL_LT_RMUL) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM int_abs_th; GSYM int_of_num_th; GSYM int_le] THEN
    DISCH_TAC THEN SUBGOAL_THEN `d:int = &1 \/ d = -- &1` MP_TAC THENL
     [ASM_INT_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC INTEGER_RULE]]);;

(* ------------------------------------------------------------------------- *)
(* Congruent forms.                                                          *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FORM_CHANGE_BASIS = prove
 (`!s (A:K->K->real) (U:K->K->real) (y:K->real).
        FINITE s
        ==> sum s (\i. sum s
                   (\j. sum s (\k. sum s (\l. U k i * A k l * U l j)) *
                                  y i * y j)) =
            sum s (\k. sum s (\l. A k l * sum s (\i. U k i * y i) *
                                          sum s (\j. U l j * y j)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  SUBGOAL_THEN
   `!f:K->K->real. sum s (\i. sum s (f i)) = sum s (\j. sum s (\i. f i j))`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_SWAP THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV) [th]) THEN
  BETA_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN BETA_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
    (LAND_CONV o RAND_CONV o ABS_CONV o RAND_CONV o ABS_CONV) [th]) THEN
  BETA_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ABS_CONV) [th]) THEN
  BETA_TAC THEN
  REPEAT(MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN BETA_TAC) THEN
  REAL_ARITH_TAC);;

let REAL_DET_CONGRUENT_MATRIX = prove
 (`!s (A:K->K->real) (U:K->K->real).
        FINITE s
        ==> ring_det real_ring s
              (\i j. sum s (\k. sum s (\l. U k i * A k l * U l j))) =
            ring_det real_ring s U pow 2 * ring_det real_ring s A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `\i k:K. (U:K->K->real) k i`;
                 `\k j:K. sum s (\l. (A:K->K->real) k l * U l j)`]
    RING_DET_MUL) THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `A:K->K->real`; `U:K->K->real`]
    RING_DET_MUL) THEN
  REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `U:K->K->real`] RING_DET_TRANSP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RING);;

let QUADRATIC_FORM_CONGRUENT_POSITIVE = prove
 (`!s (A:K->K->real) (U:K->K->real).
        FINITE s /\ (!i j. i IN s /\ j IN s ==> A i j = A j i) /\
        (!x. (?i. i IN s /\ ~(x i = &0))
             ==> &0 < sum s (\i. sum s (\j. A i j * x i * x j))) /\
        ~(ring_det real_ring s U = &0)
        ==> (!i j. i IN s /\ j IN s
                   ==> sum s (\k. sum s (\l. U k i * A k l * U l j)) =
                       sum s (\k. sum s (\l. U k j * A k l * U l i))) /\
            (!y. (?i. i IN s /\ ~(y i = &0))
                 ==> &0 < sum s (\i. sum s (\j.
                            sum s (\k. sum s (\l. U k i * A k l * U l j)) *
                            y i * y j)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [MATCH_MP SUM_SWAP (CONJ (ASSUME `FINITE(s:K->bool)`)
                              (ASSUME `FINITE(s:K->bool)`))] THEN
    BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:K` THEN
    DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `l:K` THEN DISCH_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(A:K->K->real) k l = A l k` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `y:K->real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[QUADRATIC_FORM_CHANGE_BASIS] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    free_in `A:K->K->real` (concl th) && is_imp(snd(dest_forall(concl th))) &&
    is_exists(lhand(snd(dest_forall(concl th)))))) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE
   [NOT_EXISTS_THM; TAUT `~(p /\ ~q) <=> p ==> q`]) THEN
  UNDISCH_TAC `~(ring_det real_ring s (U:K->K->real) = &0)` THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `U:K->K->real`; `y:K->real`]
    RING_DET_DEPENDENT_COLUMNS) THEN
  REWRITE_TAC[INTEGRAL_DOMAIN_REAL_RING; REAL_RING_CLAUSES; IN_UNIV;
              REAL_RING_SUM] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;
