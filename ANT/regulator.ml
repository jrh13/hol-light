(* ========================================================================= *)
(* The logarithmic embedding of the units of a number field and the          *)
(* regulator. For a number field k with ring of integers O, the infinite     *)
(* places v of ANT/infinite_places.ml (the absolute values x |-> |g x| of    *)
(* the complex embeddings g) have the local degrees                          *)
(*                                                                           *)
(*   n_v = CARD {g | g IN complex_embeddings k /\ (\x. norm(g x)) = v}       *)
(*                                                                           *)
(* (1 at the real and 2 at the complex places,                               *)
(* CARD_INFINITE_PLACE_EMBEDDINGS of ANT/infinite_places.ml), and the        *)
(* logarithmic embedding sends a unit u to the vector (n_v log v(u)) indexed *)
(* by the places. With r = CARD(infinite_places k) - 1 (the rank of the      *)
(* units):                                                                   *)
(*                                                                           *)
(*   number_field_regulator k = |det(n_(v_i) log v_i(e_j))|, i, j < r, for   *)
(*                              units e_j that generate the units modulo the *)
(*                              roots of unity and distinct places v_i       *)
(*                              (one such system, chosen)                    *)
(*                                                                           *)
(* Main results: the image of the units lies in the trace-zero hyperplane,   *)
(* sum_v n_v log v(u) = 0 (NUMBER_FIELD_LOG_UNIT_SUM), the kernel consists   *)
(* of the roots of unity (NUMBER_FIELD_LOG_UNIT_EQ_0), and the images of a   *)
(* system of fundamental units are a basis of the hyperplane over R whose    *)
(* integer combinations are the images of the units, so the units go onto a  *)
(* full lattice of the hyperplane (NUMBER_FIELD_LOG_UNITS_LATTICE). The      *)
(* determinant |det(n_(v_i) log v_i(e_j))| is the same for every system of r *)
(* units generating the units modulo the roots of unity, indexed by any set  *)
(* of size r, and for every choice of r of the r + 1 places                  *)
(* (NUMBER_FIELD_REGULATOR; with e the identity, for the sets of             *)
(* NUMBER_FIELD_FUNDAMENTAL_UNITS); it is positive                           *)
(* (NUMBER_FIELD_REGULATOR_POS), and it is 1 when r = 0                      *)
(* (NUMBER_FIELD_REGULATOR_RANK_0). The general facts used: the logarithms   *)
(* of positive multiplicative functions on groups                            *)
(* (GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW), strictly diagonally dominant    *)
(* real matrices are nonsingular (RING_DET_REAL_DIAGONALLY_DOMINANT of       *)
(* Library/ring_det.ml, the Levy-Desplanques theorem), real linear systems   *)
(* with a nonzero determinant are solvable (REAL_MATRIX_SOLVE, the real form *)
(* of RING_MATRIX_SOLVE), and the r x r minors of an (r + 1) x r real matrix *)
(* whose rows sum to zero all have the same absolute value                   *)
(* (RING_DET_REAL_ROWS_OMIT, the real form of RING_DET_ROWS_OMIT of          *)
(* Library/ring_det.ml, up to sign over any ring).                           *)
(*                                                                           *)
(* Routes. Nonvanishing (Neukirch I.7.6): for each of the r chosen places w  *)
(* a unit d_w with v(d_w) < 1 at all places v <> w                          *)
(* (NUMBER_FIELD_UNIT_DOMINANT_PLACE); in the matrix (n_v log v(d_w)) the    *)
(* entries off the diagonal are negative and, by the trace-zero identity and *)
(* the omitted place, every column has a positive sum, so it is diagonally   *)
(* dominant. Writing d_w = z prod e_j^(a_wj) with z a root of unity gives    *)
(* this matrix as the product of (n_v log v(e_j)) with the integer matrix    *)
(* (a_wj) (NUMBER_FIELD_LOG_MATRIX_CHANGE, RING_DET_MUL), so                 *)
(* det(n_v log v(e_j)) <> 0 (NUMBER_FIELD_LOG_MATRIX_NONZERO).               *)
(* Independence of the system: two systems are integer combinations of each  *)
(* other modulo roots of unity; the two integer determinants multiply to 1,  *)
(* so they are +-1 (NUMBER_FIELD_LOG_MATRIX_SYSTEM). Independence of the     *)
(* places: by the trace-zero identity the omitted row is minus the sum of    *)
(* the others (RING_DET_REAL_ROWS_OMIT). The basis and lattice statements    *)
(* follow from det <> 0 (RING_DET_DEPENDENT_COLUMNS, REAL_MATRIX_SOLVE) and  *)
(* the trace-zero identity at the omitted place. The regulator is defined by *)
(* choice over the systems indexed by {i | i < r}; the systems exist by      *)
(* NUMBER_FIELD_FUNDAMENTAL_UNITS. The NUMBER_FIELD_LOG_MATRIX lemmas and    *)
(* NUMBER_FIELD_LOG_UNITS_LATTICE hold for any positive weights c_v with     *)
(* sum_v c_v log v(u) = 0 for the units, of which the local degrees are the  *)
(* instance used (INFINITE_PLACES_LOCAL_DEGREES).                            *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/grouptheory.ml, Library/ring_det.ml  *)
(* (ring_det, RING_DET_MUL, RING_MATRIX_SOLVE, RING_DET_REINDEX,             *)
(* RING_DET_REAL_DIAGONALLY_DOMINANT, RING_DET_ROW_NEG_SUM,                  *)
(* RING_DET_ROWS_SAME_IMAGE, RING_DET_ROWS_OMIT), Library/products.ml,       *)
(* ANT/numfield.ml, Library/ring_groups.ml (unit_group,                      *)
(* GROUP_REAL_MULTIPLICATIVE_ZPOW, GROUP_REAL_MULTIPLICATIVE_SUM),           *)
(* ANT/complex_embeddings.ml (and with it Multivariate/cauchy.ml: log, norm, *)
(* cnj), ANT/infinite_places.ml (COMPLEX_EMBEDDINGS_NORM_EQ,                 *)
(* RING_OF_INTEGERS_UNIT_NORM_PRODUCT, the local degrees:                    *)
(* INFINITE_PLACES_DEGREE, INFINITE_PLACES_SUM, INFINITE_PLACES_UNIT_GROUP)  *)
(* and ANT/unit_theorem.ml (NUMBER_FIELD_UNIT_DOMINANT_PLACE,                *)
(* NUMBER_FIELD_FUNDAMENTAL_UNITS). Also Multivariate/transcendentals.ml     *)
(* (log, LOG_ZPOW).                                                          *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/permutations.ml";;
needs "Library/products.ml";;
needs "Library/ring_det.ml";;
needs "ANT/numfield.ml";;
needs "ANT/fingen_group.ml";;
needs "Library/ring_groups.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "ANT/unit_theorem.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* Real matrices: solving linear systems, integer determinants, and the      *)
(* minors of a matrix whose rows sum to zero.                                *)
(* ------------------------------------------------------------------------- *)

let REAL_MATRIX_SOLVE = prove
 (`!s (m:K->K->real) v.
        FINITE s /\ ~(ring_det real_ring s m = &0)
        ==> ?t. !i. i IN s ==> sum s (\j. m i j * t j) = v i`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `m:K->K->real`; `v:K->real`]
    RING_MATRIX_SOLVE) THEN
  ASM_SIMP_TAC[FIELD_UNIT; FIELD_REAL_RING; REAL_RING_CLAUSES;
               IN_UNIV; REAL_RING_SUM] THEN MESON_TAC[]);;

let RING_DET_REAL_OF_INT = prove
 (`!s (m:K->K->int).
        FINITE s
        ==> ring_det real_ring s (\i j. real_of_int(m i j)) =
            real_of_int(ring_det integer_ring s m)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `real_ring`; `ring_of_int real_ring`;
                 `s:K->bool`; `m:K->K->int`] RING_DET_HOMOMORPHISM) THEN
  ASM_REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; REAL_RING_OF_INT;
                  INTEGER_RING; IN_UNIV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let RING_DET_REAL_ROW_NEG_SUM = prove
 (`!s (f:K->K->real) k.
        FINITE s /\ k IN s
        ==> ring_det real_ring s
              (\i j. if i = k then --(sum s (\l. f l j)) else f i j) =
            --(ring_det real_ring s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `f:K->K->real`; `k:K`]
    RING_DET_ROW_NEG_SUM) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; REAL_RING_SUM; IN_UNIV]);;

let RING_DET_REAL_ROWS_SAME_IMAGE = prove
 (`!s (f:B->K->real) p p'.
        FINITE s /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j) /\
        (!i j. i IN s /\ j IN s /\ p' i = p' j ==> i = j) /\
        IMAGE p s = IMAGE p' s
        ==> abs(ring_det real_ring s (\i j. f (p' i) j)) =
            abs(ring_det real_ring s (\i j. f (p i) j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `f:B->K->real`; `p:K->B`;
                 `p':K->B`] RING_DET_ROWS_SAME_IMAGE) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NEG]);;

let RING_DET_REAL_ROWS_OMIT = prove
 (`!(P:B->bool) (s:K->bool) (f:B->K->real) p p'.
        FINITE P /\ FINITE s /\ CARD s = CARD P - 1 /\
        (!j. j IN s ==> sum P (\v. f v j) = &0) /\
        (!i. i IN s ==> p i IN P) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j) /\
        (!i. i IN s ==> p' i IN P) /\
        (!i j. i IN s /\ j IN s /\ p' i = p' j ==> i = j)
        ==> abs(ring_det real_ring s (\i j. f (p' i) j)) =
            abs(ring_det real_ring s (\i j. f (p i) j))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`real_ring`; `P:B->bool`; `s:K->bool`; `f:B->K->real`;
                 `p:K->B`; `p':K->B`] RING_DET_ROWS_OMIT) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; REAL_RING_SUM; IN_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_ABS_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Logarithms of positive multiplicative functions on abelian groups.        *)
(* ------------------------------------------------------------------------- *)

let GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW = prove
 (`!G (g:A->real) (x:K->A) n t.
        abelian_group G /\
        (!x. x IN group_carrier G ==> &0 < g x) /\
        (!x y. x IN group_carrier G /\ y IN group_carrier G
               ==> g(group_mul G x y) = g x * g y) /\
        FINITE t /\ (!i. i IN t ==> x i IN group_carrier G)
        ==> log(g(group_sum G t (\i. group_zpow G (x i) (n i)))) =
            sum t (\i. real_of_int(n i) * log(g(x i)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g:A->real)(group_id G) = &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[GROUP_REAL_MULTIPLICATIVE_ID_INV_POW]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_REAL_MULTIPLICATIVE_SUM o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[GROUP_ZPOW] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LOG_PRODUCT o lhand o snd) THEN
  ASM_SIMP_TAC[GROUP_ZPOW] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) GROUP_REAL_MULTIPLICATIVE_ZPOW o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[LOG_ZPOW]);;

(* ------------------------------------------------------------------------- *)
(* The logarithmic embedding of the units: the trace-zero identity, the      *)
(* kernel, integer combinations, units dominant at one place.                *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_LOG_UNIT_SUM = prove
 (`!k u:A.
        number_field k /\ ring_unit (ring_of_integers k) u
        ==> sum (infinite_places k)
              (\v. &(CARD {g | g IN complex_embeddings k /\
                               (\x. norm(g x)) = v}) * log(v u)) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `u:A`] RING_OF_INTEGERS_UNIT_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INFINITE_PLACES_SUM] THEN
  W(MP_TAC o PART_MATCH (rand o rand) LOG_PRODUCT o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_COMPLEX_EMBEDDINGS; COMPLEX_EMBEDDINGS_NORM_POS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`k:A ring`; `u:A`] RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN
  ASM_SIMP_TAC[LOG_1]);;

let NUMBER_FIELD_LOG_UNIT_EQ_0 = prove
 (`!k u:A.
        number_field k /\ ring_unit (ring_of_integers k) u
        ==> ((!v. v IN infinite_places k ==> log(v u) = &0) <=>
             ?m. 1 <= m /\ ring_pow k u m = ring_1 k)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPECL [`k:A ring`; `u:A`] RING_OF_INTEGERS_UNIT_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `u:A`] RING_OF_INTEGERS_ROOT_OF_UNITY) THEN
  ASM_SIMP_TAC[RING_UNIT_IN_CARRIER] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[infinite_places; FORALL_IN_IMAGE] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  DISCH_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LOG_1] THEN
  MATCH_MP_TAC LOG_INJ THEN
  ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NORM_POS; REAL_LT_01]);;

let NUMBER_FIELD_LOG_UNIT_COMBINATION = prove
 (`!k (s:K->bool) (e:K->A) n z v.
        number_field k /\ FINITE s /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        z IN ring_carrier k /\ (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
        v IN infinite_places k
        ==> log(v(ring_mul k z
                    (group_sum (unit_group(ring_of_integers k)) s
                       (\i. group_zpow (unit_group(ring_of_integers k))
                                       (e i) (n i))))) =
            sum s (\i. real_of_int(n i) * log(v(e i)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)
    ASSUME_TAC))))) THEN
  ABBREV_TAC
   `y = group_sum (unit_group(ring_of_integers k)) s
          (\i. group_zpow (unit_group(ring_of_integers k))
                          ((e:K->A) i) (n i))` THEN
  SUBGOAL_THEN `ring_unit (ring_of_integers k) (y:A)` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`;
     `s:K->bool`;
     `\i. group_zpow (unit_group(ring_of_integers k)) ((e:K->A) i) (n i)`]
     GROUP_SUM) THEN
    REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO; NUMBER_FIELD_IMP_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->real`; `z:A`; `y:A`]
    INFINITE_PLACES_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->real`; `z:A`; `m:num`]
    INFINITE_PLACES_ROOT_OF_UNITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_LID] THEN EXPAND_TAC "y" THEN
  MATCH_MP_TAC GROUP_REAL_MULTIPLICATIVE_LOG_SUM_ZPOW THEN
  MP_TAC(ISPECL [`k:A ring`; `v:A->real`] INFINITE_PLACES_UNIT_GROUP) THEN
  ASM_SIMP_TAC[ABELIAN_UNIT_GROUP; UNIT_GROUP; IN_ELIM_THM]);;

let NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE = prove
 (`!k v:A->real.
        number_field k /\ v IN infinite_places k
        ==> ?u. ring_unit (ring_of_integers k) u /\
                !w. w IN infinite_places k /\ ~(w = v) ==> w u < &1`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; infinite_places] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:A ring` THEN DISCH_TAC THEN
  X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    NUMBER_FIELD_UNIT_DOMINANT_PLACE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `u:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `h:A->complex` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[COMPLEX_EMBEDDINGS_NORM_EQ; COMPLEX_EMBEDDINGS_NORM_FUN_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Logarithmic matrices of systems of units, for positive weights c on       *)
(* the places with sum_v c_v log v(u) = 0 for all units u.                   *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_LOG_MATRIX_CHANGE = prove
 (`!k (c:(A->real)->real) (s:K->bool) (e:K->A) (x:K->A) z a (p:K->A->real).
        number_field k /\ FINITE s /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!j. j IN s
             ==> z j IN ring_carrier k /\
                 (?m. 1 <= m /\ ring_pow k (z j) m = ring_1 k) /\
                 x j = ring_mul k (z j)
                        (group_sum (unit_group(ring_of_integers k)) s
                          (\l. group_zpow (unit_group(ring_of_integers k))
                                          (e l) (a j l))))
        ==> ring_det real_ring s (\i j. c(p i) * log(p i (x j))) =
            ring_det real_ring s (\i j. c(p i) * log(p i (e j))) *
            ring_det real_ring s (\l j. real_of_int(a j l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`real_ring`; `s:K->bool`;
    `\i l. (c:(A->real)->real)(p i) * log((p:K->A->real) i ((e:K->A) l))`;
    `\l j. real_of_int((a:K->K->int) j l)`] RING_DET_MUL) THEN
  ASM_REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV; REAL_RING_SUM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC RING_DET_EQ THEN
  MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NUMBER_FIELD_LOG_UNIT_COMBINATION o
    rand o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let NUMBER_FIELD_LOG_MATRIX_NONZERO = prove
 (`!k (c:(A->real)->real) (s:K->bool) (e:K->A) (p:K->A->real).
        number_field k /\
        (!v. v IN infinite_places k ==> &0 < c v) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
        FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j)
        ==> ~(ring_det real_ring s (\i j. c(p i) * log(p i (e j))) = &0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sum") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gen") STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_INFINITE_PLACES) THEN
  SUBGOAL_THEN
   `?v0:A->real. v0 IN infinite_places k /\ ~(v0 IN IMAGE p (s:K->bool))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~(t SUBSET u) ==> ?x:A->real. x IN t /\ ~(x IN u)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`p:K->A->real`; `s:K->bool`] CARD_IMAGE_LE) THEN
    MP_TAC(ISPECL [`infinite_places(k:A ring)`; `IMAGE (p:K->A->real) s`]
      CARD_SUBSET) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    SUBGOAL_THEN `~(CARD(infinite_places(k:A ring)) = 0)` MP_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0; infinite_places; IMAGE_EQ_EMPTY;
                   COMPLEX_EMBEDDINGS_NONEMPTY];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. !i. i IN s
            ==> ring_unit (ring_of_integers k) (d i:A) /\
                !w. w IN infinite_places k /\ ~(w = (p:K->A->real) i)
                    ==> w(d i) < &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC
      NUMBER_FIELD_UNIT_DOMINANT_INFINITE_PLACE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(ring_det real_ring s
       (\i j. (c:(A->real)->real)(p i) * log((p:K->A->real) i ((d:K->A) j)))
      = &0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_DET_REAL_DIAGONALLY_DOMINANT THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!w. w IN infinite_places k /\ ~(w = (p:K->A->real) j)
          ==> (c:(A->real)->real) w * log(w((d:K->A) j)) < &0`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < (x:real) * --y ==> x * y < &0`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `&0 < --(x:real) <=> x < &0`] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_1] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC INFINITE_PLACES_POS THEN EXISTS_TAC `k:A ring` THEN
      ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&0 < sum s (\i. (c:(A->real)->real)(p i) *
                      log((p:K->A->real) i ((d:K->A) j)))`
    ASSUME_TAC THENL
     [USE_THEN "sum" (MP_TAC o SPEC `(d:K->A) j`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL
       [`\v:A->real. (c:(A->real)->real) v * log(v((d:K->A) j))`;
        `infinite_places(k:A ring)`; `IMAGE (p:K->A->real) s`] SUM_DIFF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE]; ALL_TAC] THEN
      MP_TAC(ISPECL
       [`p:K->A->real`;
        `\v:A->real. (c:(A->real)->real) v * log(v((d:K->A) j))`;
        `s:K->bool`] SUM_IMAGE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[o_DEF] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!a b c x y:real. x = y /\ c < &0 ==> b = y ==> c = a - b ==> a = &0
                         ==> &0 < x`) THEN
      CONJ_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL
       [`\v:A->real. (c:(A->real)->real) v * log(v((d:K->A) j))`;
        `infinite_places(k:A ring) DIFF IMAGE (p:K->A->real) s`;
        `v0:A->real`] SUM_DELETE) THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_DIFF; IN_DIFF]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x < &0 /\ (s':real) <= &0 ==> s' = s - x ==> s < &0`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[FUN_IN_IMAGE];
        REWRITE_TAC[REAL_ARITH `(x:real) <= &0 <=> &0 <= --x`;
                    GSYM SUM_NEG] THEN
        MATCH_MP_TAC SUM_POS_LE THEN
        ASM_SIMP_TAC[FINITE_DELETE; FINITE_DIFF; IN_DELETE; IN_DIFF] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `(x:real) < &0 ==> &0 <= --x`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[FUN_IN_IMAGE]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum (s DELETE j)
        (\i. abs((c:(A->real)->real)(p i) *
                 log((p:K->A->real) i ((d:K->A) j)))) =
      --(sum (s DELETE j)
           (\i. c(p i) * log(p i (d j))))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `i:K` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `(x:real) < &0 ==> abs x = --x`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\i. (c:(A->real)->real)(p i) * log((p:K->A->real) i ((d:K->A) j))`;
      `s:K->bool`; `j:K`] SUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z a. !j. j IN s
              ==> z j IN ring_carrier k /\
                  (?m. 1 <= m /\ ring_pow k (z j) m = ring_1 k) /\
                  (d:K->A) j =
                  ring_mul k (z j)
                   (group_sum (unit_group(ring_of_integers k)) s
                     (\l. group_zpow (unit_group(ring_of_integers k))
                                     ((e:K->A) l) (a j l)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `j:K` THEN DISCH_TAC THEN REMOVE_THEN "gen" MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:K`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `c:(A->real)->real`; `s:K->bool`; `e:K->A`;
                 `d:K->A`; `z:K->A`; `a:K->K->int`; `p:K->A->real`]
    NUMBER_FIELD_LOG_MATRIX_CHANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST_ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN SIMP_TAC[]);;

let NUMBER_FIELD_LOG_MATRIX_SYSTEM = prove
 (`!k (c:(A->real)->real) (s:K->bool) (e:K->A) e' (p:K->A->real).
        number_field k /\
        (!v. v IN infinite_places k ==> &0 < c v) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
        FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e' i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e' i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j)
        ==> abs(ring_det real_ring s (\i j. c(p i) * log(p i (e' j)))) =
            abs(ring_det real_ring s (\i j. c(p i) * log(p i (e j))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gen'") STRIP_ASSUME_TAC))))))))) THEN
  MP_TAC(ISPECL [`k:A ring`; `c:(A->real)->real`; `s:K->bool`; `e:K->A`;
                 `p:K->A->real`] NUMBER_FIELD_LOG_MATRIX_NONZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `?z a. !j. j IN s
              ==> z j IN ring_carrier k /\
                  (?m. 1 <= m /\ ring_pow k (z j) m = ring_1 k) /\
                  (e':K->A) j =
                  ring_mul k (z j)
                   (group_sum (unit_group(ring_of_integers k)) s
                     (\l. group_zpow (unit_group(ring_of_integers k))
                                     ((e:K->A) l) (a j l)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    USE_THEN "gen" (MP_TAC o SPEC `(e':K->A) j`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?z' b. !j. j IN s
               ==> z' j IN ring_carrier k /\
                   (?m. 1 <= m /\ ring_pow k (z' j) m = ring_1 k) /\
                   (e:K->A) j =
                   ring_mul k (z' j)
                    (group_sum (unit_group(ring_of_integers k)) s
                      (\l. group_zpow (unit_group(ring_of_integers k))
                                      ((e':K->A) l) (b j l)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `j:K` THEN DISCH_TAC THEN
    USE_THEN "gen'" (MP_TAC o SPEC `(e:K->A) j`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `c:(A->real)->real`; `s:K->bool`; `e:K->A`;
                 `e':K->A`; `z:K->A`; `a:K->K->int`; `p:K->A->real`]
    NUMBER_FIELD_LOG_MATRIX_CHANGE) THEN
  MP_TAC(ISPECL [`k:A ring`; `c:(A->real)->real`; `s:K->bool`; `e':K->A`;
                 `e:K->A`; `z':K->A`; `b:K->K->int`; `p:K->A->real`]
    NUMBER_FIELD_LOG_MATRIX_CHANGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; POP_ASSUM MP_TAC] THEN
  MAP_EVERY (fun t ->
    MP_TAC(BETA_RULE(ISPECL [`s:K->bool`; t] RING_DET_REAL_OF_INT)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC])
   [`\l j. (a:K->K->int) j l`; `\l j. (b:K->K->int) j l`] THEN
  ABBREV_TAC `X = ring_det integer_ring s (\l j. (a:K->K->int) j l)` THEN
  ABBREV_TAC `Y = ring_det integer_ring s (\l j. (b:K->K->int) j l)` THEN
  ABBREV_TAC
   `D = ring_det real_ring s
          (\i j. (c:(A->real)->real)(p i) *
                 log((p:K->A->real) i ((e:K->A) j)))` THEN
  ABBREV_TAC
   `D' = ring_det real_ring s
          (\i j. (c:(A->real)->real)(p i) *
                 log((p:K->A->real) i ((e':K->A) j)))` THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_of_int X * real_of_int Y = &1` MP_TAC THENL
   [SUBGOAL_THEN `D * (real_of_int X * real_of_int Y) = D * &1` MP_TAC
    THENL
     [REWRITE_TAC[REAL_MUL_ASSOC; REAL_MUL_RID] THEN
      UNDISCH_TAC `D' = D * real_of_int X` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `D = D' * real_of_int Y` THEN
      DISCH_THEN(ACCEPT_TAC o SYM);
      ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM int_mul_th; GSYM int_of_num_th; GSYM int_eq] THEN
  REWRITE_TAC[INT_MUL_EQ_1] THEN
  DISCH_THEN(DISJ_CASES_THEN (MP_TAC o AP_TERM `real_of_int` o CONJUNCT1)) THEN
  REWRITE_TAC[int_of_num_th; int_neg_th] THEN DISCH_TAC THEN
  UNDISCH_TAC `D' = D * real_of_int X` THEN DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM SUBST1_TAC THEN REAL_ARITH_TAC);;

let NUMBER_FIELD_LOG_MATRIX_INVARIANT = prove
 (`!k (c:(A->real)->real) (s:K->bool) (e:K->A) (p:K->A->real)
     (s':L->bool) (e':L->A) (p':L->A->real).
        number_field k /\
        (!v. v IN infinite_places k ==> &0 < c v) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
        FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j) /\
        FINITE s' /\ CARD s' = CARD(infinite_places k) - 1 /\
        (!i. i IN s' ==> ring_unit (ring_of_integers k) (e' i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s'
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e' i) (n i)))) /\
        (!i. i IN s' ==> p' i IN infinite_places k) /\
        (!i j. i IN s' /\ j IN s' /\ p' i = p' j ==> i = j)
        ==> abs(ring_det real_ring s' (\i j. c(p' i) * log(p' i (e' j)))) =
            abs(ring_det real_ring s (\i j. c(p i) * log(p i (e j))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gen") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "pinj") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "gen'") (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "p'inj"))))))))))))))) THEN
  MP_TAC(ISPECL [`s:K->bool`; `s':L->bool`] CARD_EQ_BIJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:K->L` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "binj")))) THEN
  SUBGOAL_THEN `s' = IMAGE (b:K->L) s` SUBST_ALL_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`real_ring`; `b:K->L`; `s:K->bool`;
    `\i j. (c:(A->real)->real)((p':L->A->real) i) * log(p' i ((e':L->A) j))`]
    RING_DET_REINDEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`infinite_places(k:A ring)`; `s:K->bool`;
    `\v j. (c:(A->real)->real) v * log(v((e':L->A)((b:K->L) j)))`;
    `p:K->A->real`; `\i. (p':L->A->real)((b:K->L) i)`]
   RING_DET_REAL_ROWS_OMIT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_INFINITE_PLACES] THEN CONJ_TAC THENL
     [USE_THEN "pinj" ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`i:K`; `j:K`] THEN STRIP_TAC THEN
      USE_THEN "binj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "p'inj" MATCH_MP_TAC THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `c:(A->real)->real`; `s:K->bool`; `e:K->A`;
                 `\i. (e':L->A)((b:K->L) i)`; `p:K->A->real`]
    NUMBER_FIELD_LOG_MATRIX_SYSTEM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
  X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  REMOVE_THEN "gen'" (MP_TAC o SPEC `u:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `n:L->int`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST1_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`z:A`; `\i. (n:L->int)((b:K->L) i)`] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`; `b:K->L`;
    `\i. group_zpow (unit_group(ring_of_integers k)) ((e':L->A) i)
                    ((n:L->int) i)`; `s:K->bool`] GROUP_SUM_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ABELIAN_UNIT_GROUP] THEN USE_THEN "binj" ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let NUMBER_FIELD_LOG_UNITS_LATTICE = prove
 (`!k (c:(A->real)->real) (s:K->bool) (e:K->A).
        number_field k /\
        (!v. v IN infinite_places k ==> &0 < c v) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> sum (infinite_places k) (\v. c v * log(v u)) = &0) /\
        FINITE s /\ CARD s = CARD(infinite_places k) - 1 /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i))))
        ==> (!x. (!v. v IN infinite_places k
                      ==> sum s (\i. x i * c v * log(v(e i))) = &0)
                 ==> !i. i IN s ==> x i = &0) /\
            (!y. sum (infinite_places k) y = &0
                 ==> ?x. !v. v IN infinite_places k
                             ==> y v = sum s (\i. x i * c v * log(v(e i)))) /\
            (!u. ring_unit (ring_of_integers k) u
                 ==> ?n. !v. v IN infinite_places k
                             ==> c v * log(v u) =
                                 sum s (\i. real_of_int(n i) * c v *
                                            log(v(e i))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "sum") (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "gen"))))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FINITE_INFINITE_PLACES) THEN
  SUBGOAL_THEN `?v0:A->real. v0 IN infinite_places k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY; infinite_places; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NONEMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:K->bool`; `infinite_places(k:A ring) DELETE v0`]
    CARD_EQ_BIJECTION) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:K->A->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pinj")))) THEN
  SUBGOAL_THEN `infinite_places k = (v0:A->real) INSERT IMAGE p (s:K->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i IN s ==> (p:K->A->real) i IN infinite_places k /\
                               ~(p i = v0)`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `c:(A->real)->real`; `s:K->bool`; `e:K->A`;
                 `p:K->A->real`] NUMBER_FIELD_LOG_MATRIX_NONZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `M = \i j. (c:(A->real)->real)((p:K->A->real) i) *
                        log(p i ((e:K->A) j))` THEN
  DISCH_TAC THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:K->real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `?i. i IN s /\ ~((x:K->real) i = &0)` THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `~(ring_det real_ring s (M:K->K->real) = &0)` THEN
    MATCH_MP_TAC(TAUT `q ==> ~q ==> p`) THEN
    MP_TAC(ISPECL [`real_ring`; `s:K->bool`; `M:K->K->real`; `x:K->real`]
      RING_DET_DEPENDENT_COLUMNS) THEN
    REWRITE_TAC[INTEGRAL_DOMAIN_REAL_RING; REAL_RING_CLAUSES; IN_UNIV;
                REAL_RING_SUM] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:K` THEN DISCH_TAC THEN EXPAND_TAC "M" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(p:K->A->real) i` o check
      (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. sum (infinite_places k) f = f v0 + sum s (\i. f((p:K->A->real) i))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV)
      [th]) THEN
    MP_TAC(ISPECL [`v0:A->real`; `f:(A->real)->real`;
                   `IMAGE (p:K->A->real) s`] (CONJUNCT2 SUM_CLAUSES)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `~((v0:A->real) IN IMAGE p (s:K->bool))`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p:K->A->real`; `f:(A->real)->real`; `s:K->bool`]
      SUM_IMAGE) THEN
    ANTS_TAC THENL [USE_THEN "pinj" ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:(A->real)->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:K->bool`; `M:K->K->real`;
                   `\i. (y:(A->real)->real)((p:K->A->real) i)`]
      REAL_MATRIX_SOLVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:K->real` (LABEL_TAC "sol" o BETA_RULE)) THEN
    EXISTS_TAC `x:K->real` THEN
    SUBGOAL_THEN
     `!i. i IN s
          ==> (y:(A->real)->real)(p i) =
              sum s (\j. x j * (c:(A->real)->real)(p i) *
                         log((p:K->A->real) i ((e:K->A) j)))`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      USE_THEN "sol" (MP_TAC o SPEC `i:K`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN EXPAND_TAC "M" THEN
      MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `v:A->real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `v = (v0:A->real) \/ ?i. i IN s /\ v = (p:K->A->real) i`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(v:A->real) IN infinite_places k` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      REWRITE_TAC[IN_INSERT; IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC;
      FIRST_X_ASSUM SUBST1_TAC THEN ASM_SIMP_TAC[]] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    UNDISCH_TAC `sum (infinite_places k) (y:(A->real)->real) = &0` THEN
    ASM_REWRITE_TAC[REAL_ARITH `(a:real) + b = &0 <=> a = --b`] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `!j. j IN s
          ==> (c:(A->real)->real) v0 * log(v0((e:K->A) j)) =
              --sum s (\i. c((p:K->A->real) i) * log(p i (e j)))`
    ASSUME_TAC THENL
     [X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      USE_THEN "sum" (MP_TAC o SPEC `(e:K->A) j`) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_ARITH `(a:real) + b = &0 <=> a = --b`];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `sum s (\j. (x:K->real) j *
                 --sum s (\i. (c:(A->real)->real)((p:K->A->real) i) *
                              log(p i ((e:K->A) j))))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `j:K` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[]] THEN
    REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG; REAL_NEG_EQ; REAL_NEG_NEG] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `u:A` THEN DISCH_TAC THEN
  USE_THEN "gen" (MP_TAC o SPEC `u:A`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z:A`; `n:K->int`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    SUBST1_TAC)) THEN
  EXISTS_TAC `n:K->int` THEN X_GEN_TAC `v:A->real` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NUMBER_FIELD_LOG_UNIT_COMBINATION o
    rand o lhand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The regulator.                                                            *)
(* ------------------------------------------------------------------------- *)

let INFINITE_PLACES_LOCAL_DEGREES = prove
 (`!k:A ring.
        number_field k
        ==> (!v. v IN infinite_places k
                 ==> (&0:real) < &(CARD {g | g IN complex_embeddings k /\
                                      (\x. norm(g x)) = v})) /\
            (!u. ring_unit (ring_of_integers k) u
                 ==> sum (infinite_places k)
                       (\v. &(CARD {g | g IN complex_embeddings k /\
                                        (\x. norm(g x)) = v}) *
                            log(v u)) = &0)`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> 1 <= n`] THEN
    ASM_MESON_TAC[INFINITE_PLACES_DEGREE];
    ASM_SIMP_TAC[NUMBER_FIELD_LOG_UNIT_SUM]]);;

let number_field_regulator = new_definition
 `number_field_regulator (k:A ring) =
  @R. ?(e:num->A) (w:num->A->real).
        (!i. i < CARD(infinite_places k) - 1
             ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k))
                              {i | i < CARD(infinite_places k) - 1}
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i < CARD(infinite_places k) - 1 ==> w i IN infinite_places k) /\
        (!i j. i < CARD(infinite_places k) - 1 /\
               j < CARD(infinite_places k) - 1 /\ w i = w j
               ==> i = j) /\
        R = abs(ring_det real_ring {i | i < CARD(infinite_places k) - 1}
                  (\i j. &(CARD {g | g IN complex_embeddings k /\
                                     (\x. norm(g x)) = w i}) *
                         log(w i (e j))))`;;

let NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS = prove
 (`!k:A ring.
        number_field k
        ==> ?(e:num->A) (w:num->A->real).
              (!i. i < CARD(infinite_places k) - 1
                   ==> ring_unit (ring_of_integers k) (e i)) /\
              (!u. ring_unit (ring_of_integers k) u
                   ==> ?z n. z IN ring_carrier k /\
                             (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                             u = ring_mul k z
                                  (group_sum (unit_group(ring_of_integers k))
                                    {i | i < CARD(infinite_places k) - 1}
                                    (\i. group_zpow
                                          (unit_group(ring_of_integers k))
                                          (e i) (n i)))) /\
              (!i. i < CARD(infinite_places k) - 1
                   ==> w i IN infinite_places k) /\
              (!i j. i < CARD(infinite_places k) - 1 /\
                     j < CARD(infinite_places k) - 1 /\ w i = w j
                     ==> i = j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS) THEN
  ABBREV_TAC `r = CARD(infinite_places(k:A ring)) - 1` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` (CONJUNCTS_THEN2 MP_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
     (LABEL_TAC "gen"))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->A` STRIP_ASSUME_TAC o
    MATCH_MP HAS_SIZE_INDEX) THEN
  SUBGOAL_THEN `t = IMAGE (e:num->A) {i | i < r}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i j. i IN {i | i < r} /\ j IN {i | i < r} /\
                      (e:num->A) i = e j ==> i = j`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `infinite_places(k:A ring)` HAS_SIZE_INDEX) THEN
  DISCH_THEN(MP_TAC o SPEC `CARD(infinite_places(k:A ring))`) THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_INFINITE_PLACES] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->A->real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`e:num->A`; `w:num->A->real`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    REMOVE_THEN "gen" (MP_TAC o SPEC `u:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `n:A->int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST1_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`z:A`; `\i. (n:A->int)((e:num->A) i)`] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`; `e:num->A`;
      `\x. group_zpow (unit_group(ring_of_integers k)) x ((n:A->int) x)`;
      `{i:num | i < r}`] GROUP_SUM_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ABELIAN_UNIT_GROUP] THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(w:num->A->real) i` o
      check (is_forall o concl)) THEN
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC]]);;

let NUMBER_FIELD_REGULATOR = prove
 (`!k (s:K->bool) (e:K->A) (p:K->A->real).
        number_field k /\ s HAS_SIZE (CARD(infinite_places k) - 1) /\
        (!i. i IN s ==> ring_unit (ring_of_integers k) (e i)) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?z n. z IN ring_carrier k /\
                       (?m. 1 <= m /\ ring_pow k z m = ring_1 k) /\
                       u = ring_mul k z
                            (group_sum (unit_group(ring_of_integers k)) s
                              (\i. group_zpow (unit_group(ring_of_integers k))
                                              (e i) (n i)))) /\
        (!i. i IN s ==> p i IN infinite_places k) /\
        (!i j. i IN s /\ j IN s /\ p i = p j ==> i = j)
        ==> number_field_regulator k =
            abs(ring_det real_ring s
                  (\i j. &(CARD {g | g IN complex_embeddings k /\
                                     (\x. norm(g x)) = p i}) *
                         log(p i (e j))))`,
  REWRITE_TAC[HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFINITE_PLACES_LOCAL_DEGREES) THEN
  REWRITE_TAC[number_field_regulator] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `y:real` THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`e':num->A`; `w:num->A->real`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(BETA_RULE(ISPECL
     [`k:A ring`;
      `\v. &(CARD {g | g IN complex_embeddings (k:A ring) /\
                       (\x. norm(g x)) = v}):real`;
      `s:K->bool`; `e:K->A`; `p:K->A->real`;
      `{i:num | i < CARD(infinite_places(k:A ring)) - 1}`;
      `e':num->A`; `w:num->A->real`]
     NUMBER_FIELD_LOG_MATRIX_INVARIANT)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM];
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e':num->A` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:num->A->real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(BETA_RULE(ISPECL
     [`k:A ring`;
      `\v. &(CARD {g | g IN complex_embeddings (k:A ring) /\
                       (\x. norm(g x)) = v}):real`;
      `s:K->bool`; `e:K->A`; `p:K->A->real`;
      `{i:num | i < CARD(infinite_places(k:A ring)) - 1}`;
      `e':num->A`; `w:num->A->real`]
     NUMBER_FIELD_LOG_MATRIX_INVARIANT)) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM]]);;

let NUMBER_FIELD_REGULATOR_POS = prove
 (`!k:A ring. number_field k ==> &0 < number_field_regulator k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP INFINITE_PLACES_LOCAL_DEGREES) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:num->A` (X_CHOOSE_THEN `w:num->A->real`
    STRIP_ASSUME_TAC) o MATCH_MP NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS) THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `{i:num | i < CARD(infinite_places(k:A ring)) - 1}`;
                 `e:num->A`; `w:num->A->real`] NUMBER_FIELD_REGULATOR) THEN
  ASM_REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM REAL_ABS_NZ] THEN
  MP_TAC(BETA_RULE(ISPECL
     [`k:A ring`;
      `\v. &(CARD {g | g IN complex_embeddings (k:A ring) /\
                       (\x. norm(g x)) = v}):real`;
      `{i:num | i < CARD(infinite_places(k:A ring)) - 1}`;
      `e:num->A`; `w:num->A->real`]
     NUMBER_FIELD_LOG_MATRIX_NONZERO)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM]);;

let NUMBER_FIELD_REGULATOR_RANK_0 = prove
 (`!k:A ring.
        number_field k /\ CARD(infinite_places k) = 1
        ==> number_field_regulator k = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `e:num->A` (X_CHOOSE_THEN `w:num->A->real`
    STRIP_ASSUME_TAC) o MATCH_MP NUMBER_FIELD_REGULATOR_SYSTEM_EXISTS) THEN
  MP_TAC(ISPECL [`k:A ring`;
                 `{i:num | i < CARD(infinite_places(k:A ring)) - 1}`;
                 `e:num->A`; `w:num->A->real`] NUMBER_FIELD_REGULATOR) THEN
  REWRITE_TAC[HAS_SIZE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  ASM_REWRITE_TAC[SUB_REFL; LT; EMPTY_GSPEC; RING_DET_EMPTY;
                  REAL_RING_CLAUSES] THEN
  REAL_ARITH_TAC);;
