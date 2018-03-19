(* ========================================================================= *)
(* Basic setup of singular homology.                                         *)
(* ========================================================================= *)

needs "Library/frag.ml";;               (* Free Abelian groups               *)
needs "Library/grouptheory.ml";;        (* Basic group theory machinery      *)
needs "Multivariate/metric.ml";;        (* General topology                  *)

(* ------------------------------------------------------------------------- *)
(* Standard simplices, all of which are topological subspaces of R^num.      *)
(* ------------------------------------------------------------------------- *)

let standard_simplex = new_definition
 `standard_simplex p =
    { x:num->real | (!i. &0 <= x i /\ x i <= &1) /\
                    (!i. p < i ==> x i = &0) /\
                    sum (0..p) x = &1}`;;

let TOPSPACE_STANDARD_SIMPLEX = prove
 (`!p. topspace(subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex p)) = standard_simplex p`,
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
  REWRITE_TAC[INTER_UNIV]);;

let BASIS_IN_STANDARD_SIMPLEX = prove
 (`!p i. (\j. if j = i then &1 else &0) IN standard_simplex p <=> i <= p`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[REAL_POS; REAL_LE_REFL; NOT_LE; REAL_ARITH `~(&1 = &0)`]);;

let NONEMPTY_STANDARD_SIMPLEX = prove
 (`!p. ~(standard_simplex p = {})`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `(\i. if i = 0 then &1 else &0):num->real` THEN
  REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX; LE_0]);;

let STANDARD_SIMPLEX_0 = prove
 (`standard_simplex 0 = {(\j. if j = 0 then &1 else &0)}`,
  REWRITE_TAC[EXTENSION; standard_simplex; IN_ELIM_THM; IN_SING] THEN
  GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [FUN_EQ_THM] THEN
  REWRITE_TAC[SUM_SING_NUMSEG] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LE_1] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC);;

let STANDARD_SIMPLEX_MONO = prove
 (`!p q. p <= q ==> standard_simplex p SUBSET standard_simplex q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; standard_simplex; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_SUPERSET THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0; NOT_LE; SUBSET] THEN ASM_ARITH_TAC);;

let CLOSED_IN_STANDARD_SIMPLEX = prove
 (`!p. closed_in (product_topology (:num) (\i. euclideanreal))
                 (standard_simplex p)`,
  GEN_TAC THEN
  ABBREV_TAC `top = product_topology (:num) (\i. euclideanreal)` THEN
  SUBGOAL_THEN
   `standard_simplex p =
    INTERS { {x | x IN topspace top /\ x i IN real_interval[&0,&1]} |
             i IN (:num)} INTER
    INTERS { {x | x IN topspace top /\ x i IN {&0}} | p < i} INTER
    {x | x IN topspace top /\ sum(0..p) x IN {&1}}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[standard_simplex; IN_ELIM_THM; INTERS_GSPEC; IN_INTER] THEN
    EXPAND_TAC "top" THEN REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY] THEN
    REWRITE_TAC[CARTESIAN_PRODUCT_UNIV; o_DEF; TOPSPACE_EUCLIDEANREAL] THEN
    REWRITE_TAC[IN_SING; IN_UNIV; IN_ELIM_THM; IN_REAL_INTERVAL];
    REPEAT(MATCH_MP_TAC CLOSED_IN_INTER THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC CLOSED_IN_INTERS) THEN
    REWRITE_TAC[SET_RULE `~({f x | P x} = {}) <=> ?x. P x`] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
    TRY(CONJ_TAC THENL [MESON_TAC[LT]; ALL_TAC]) THEN
    TRY(X_GEN_TAC `i:num`) THEN TRY DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[GSYM REAL_CLOSED_IN] THEN
    REWRITE_TAC[REAL_CLOSED_SING; REAL_CLOSED_REAL_INTERVAL] THEN
    EXPAND_TAC "top" THEN
    SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN
    SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV] THEN
    REWRITE_TAC[FINITE_NUMSEG]]);;

let COMPACT_IN_STANDARD_SIMPLEX = prove
 (`!p. compact_in (product_topology (:num) (\i. euclideanreal))
                  (standard_simplex p)`,
  GEN_TAC THEN MATCH_MP_TAC CLOSED_COMPACT_IN THEN
  EXISTS_TAC `cartesian_product (:num) (\i. real_interval[&0,&1])` THEN
  REWRITE_TAC[COMPACT_IN_CARTESIAN_PRODUCT] THEN
  REWRITE_TAC[CLOSED_IN_STANDARD_SIMPLEX] THEN
  REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
  REWRITE_TAC[SUBSET; standard_simplex; cartesian_product] THEN
  REWRITE_TAC[IN_UNIV; EXTENSIONAL_UNIV; IN_ELIM_THM] THEN
  SIMP_TAC[IN_REAL_INTERVAL]);;

let CONVEX_STANDARD_SIMPLEX = prove
 (`!p x y u.
        x IN standard_simplex p /\ y IN standard_simplex p /\
        &0 <= u /\ u <= &1
        ==> (\i. (&1 - u) * x i + u * y i) IN standard_simplex p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_SUB_LE] THEN
  GEN_TAC THEN MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN
  ASM_SIMP_TAC[REAL_SUB_LE] THEN REAL_ARITH_TAC);;

let PATH_CONNECTED_IN_STANDARD_SIMPLEX = prove
 (`!p. path_connected_in (product_topology (:num) (\i. euclideanreal))
                         (standard_simplex p)`,
  GEN_TAC THEN
  REWRITE_TAC[path_connected_in; path_connected_space; path_in] THEN
  REWRITE_TAC[TOPSPACE_STANDARD_SIMPLEX; TOPSPACE_PRODUCT_TOPOLOGY;
              CONTINUOUS_MAP_IN_SUBTOPOLOGY; o_DEF; TOPSPACE_EUCLIDEANREAL;
              TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; CARTESIAN_PRODUCT_UNIV;
              SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real`; `y:num->real`] THEN STRIP_TAC THEN
  EXISTS_TAC `(\u i. (&1 - u) * x i + u * y i):real->num->real` THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; CONVEX_STANDARD_SIMPLEX] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; FUN_EQ_THM] THEN
  REWRITE_TAC[SET_RULE `s SUBSET P <=> !x. x IN s ==> P x`] THEN
  REWRITE_TAC[EXTENSIONAL_UNIV; IN_UNIV] THEN
  CONJ_TAC THENL [GEN_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THEN
  TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB) THEN
  REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; CONTINUOUS_MAP_ID]);;

let CONNECTED_IN_STANDARD_SIMPLEX = prove
 (`!p. connected_in (product_topology (:num) (\i. euclideanreal))
                    (standard_simplex p)`,
  GEN_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IN_IMP_CONNECTED_IN THEN
  REWRITE_TAC[PATH_CONNECTED_IN_STANDARD_SIMPLEX]);;

(* ------------------------------------------------------------------------- *)
(* Face map.                                                                 *)
(* ------------------------------------------------------------------------- *)

let face_map = new_definition
 `face_map k (x:num->real) =
  \i. if i < k then x i else if i = k then &0 else x(i - 1)`;;

let FACE_MAP_IN_STANDARD_SIMPLEX = prove
 (`!p k (x:num->real).
        1 <= p /\ k <= p /\ x IN standard_simplex (p - 1)
        ==> (face_map k x) IN standard_simplex p`,
  REWRITE_TAC[standard_simplex; face_map; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POS]);
    GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CASES; FINITE_NUMSEG; IN_NUMSEG; ARITH_RULE
     `(0 <= i /\ i <= p) /\ ~(i < k) <=> k <= i /\ i <= p`] THEN
    REWRITE_TAC[GSYM numseg] THEN
    ASM_SIMP_TAC[SUM_CLAUSES_LEFT; REAL_ADD_LID] THEN
    SUBGOAL_THEN `p = (p - 1) + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SPEC `1` SUM_OFFSET; ADD_SUB] THEN
    SIMP_TAC[ARITH_RULE `k <= i ==> ~(i + 1 = k)`] THEN
    REWRITE_TAC[GSYM IN_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_RESTRICT] THEN ANTS_TAC THENL
     [SIMP_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Singular simplices, forcing canonicity outside the intended domain.       *)
(* ------------------------------------------------------------------------- *)

let singular_simplex = new_definition
 `singular_simplex (p,top) (f:(num->real)->A) <=>
    continuous_map(subtopology (product_topology (:num) (\i. euclideanreal))
                               (standard_simplex p),
                   top) f /\
    EXTENSIONAL (standard_simplex p) f`;;

let SINGULAR_SIMPLEX_EMPTY = prove
 (`!p (top:A topology) f. topspace top = {} ==> ~(singular_simplex (p,top) f)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[singular_simplex; CONTINUOUS_MAP] THEN MATCH_MP_TAC(SET_RULE
   `~(s = {}) ==> (IMAGE f s SUBSET t /\ P) /\ Q ==> ~(t = {})`) THEN
  REWRITE_TAC[TOPSPACE_STANDARD_SIMPLEX; NONEMPTY_STANDARD_SIMPLEX]);;

let SINGULAR_SIMPLEX_MONO = prove
 (`!p (top:A topology) s t f.
        t SUBSET s /\ singular_simplex (p,subtopology top t) f
        ==> singular_simplex (p,subtopology top s) f`,
  REWRITE_TAC[singular_simplex; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  MESON_TAC[SUBSET_TRANS]);;

let SINGULAR_SIMPLEX_SUBTOPOLOGY = prove
 (`!p (top:A topology) s f.
        singular_simplex (p,subtopology top s) f <=>
        singular_simplex (p,top) f /\ IMAGE f (standard_simplex p) SUBSET s`,
  REWRITE_TAC[singular_simplex; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
  REWRITE_TAC[INTER_UNIV; CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Singular face.                                                            *)
(* ------------------------------------------------------------------------- *)

let singular_face = new_definition
 `singular_face p k f =
    RESTRICTION (standard_simplex (p - 1)) (f o face_map k)`;;

let SINGULAR_SIMPLEX_SINGULAR_FACE = prove
 (`!p (top:A topology) k f.
        singular_simplex (p,top) f /\ 1 <= p /\ k <= p
        ==> singular_simplex (p - 1,top) (singular_face p k f)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[singular_simplex] THEN STRIP_TAC THEN
  REWRITE_TAC[singular_face; REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_STANDARD_SIMPLEX;
           SUBSET_REFL] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                          (standard_simplex p)` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_STANDARD_SIMPLEX;
               SUBSET; FORALL_IN_IMAGE; FACE_MAP_IN_STANDARD_SIMPLEX] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; IN_UNIV] THEN
  REWRITE_TAC[SUBSET; EXTENSIONAL_UNIV; IN] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[face_map] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  MAP_EVERY ASM_CASES_TAC [`i:num < k`; `i:num = k`] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV] THEN
  REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_EUCLIDEANREAL; IN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Singular chains.                                                          *)
(* ------------------------------------------------------------------------- *)

let singular_chain = new_definition
 `singular_chain (p,top) (c:((num->real)->A)frag) <=>
        frag_support c SUBSET singular_simplex(p,top)`;;

let SINGULAR_CHAIN_EMPTY = prove
 (`!p (top:A topology) c.
        topspace top = {}
        ==> (singular_chain(p,top) c <=> c = frag_0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c:((num->real)->A)frag = frag_0` THEN
  ASM_REWRITE_TAC[singular_chain; FRAG_SUPPORT_0; EMPTY_SUBSET] THEN
  ASM_SIMP_TAC[FRAG_SUPPORT_EQ_EMPTY; SINGULAR_SIMPLEX_EMPTY; SET_RULE
   `(!x. ~t x) ==> (s SUBSET t <=> s = {})`]);;

let SINGULAR_CHAIN_MONO = prove
 (`!p (top:A topology) s t c.
        t SUBSET s /\ singular_chain (p,subtopology top t) c
        ==> singular_chain (p,subtopology top s) c`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  REWRITE_TAC[SUBSET; IN] THEN ASM_MESON_TAC[SINGULAR_SIMPLEX_MONO]);;

let SINGULAR_CHAIN_SUBTOPOLOGY = prove
 (`!p (top:A topology) s c.
        singular_chain (p,subtopology top s) c <=>
        singular_chain (p,top) c /\
        !f. f IN frag_support c ==> IMAGE f (standard_simplex p) SUBSET s`,
  SIMP_TAC[singular_chain; SET_RULE `s SUBSET P <=> !x. x IN s ==> P x`] THEN
  REWRITE_TAC[SINGULAR_SIMPLEX_SUBTOPOLOGY] THEN SET_TAC[]);;

let SINGULAR_CHAIN_0 = prove
 (`!p (top:A topology). singular_chain (p,top) frag_0`,
  REWRITE_TAC[singular_chain; FRAG_SUPPORT_0; EMPTY_SUBSET]);;

let SINGULAR_CHAIN_OF = prove
 (`!p (top:A topology) c.
        singular_chain (p,top) (frag_of c) <=> singular_simplex (p,top) c`,
  REWRITE_TAC[singular_chain; FRAG_SUPPORT_OF] THEN SET_TAC[]);;

let SINGULAR_CHAIN_CMUL = prove
 (`!p (top:A topology) a c.
        singular_chain (p,top) c ==> singular_chain (p,top) (frag_cmul a c)`,
  REWRITE_TAC[singular_chain] THEN
  MESON_TAC[FRAG_SUPPORT_CMUL; SUBSET_TRANS]);;

let SINGULAR_CHAIN_NEG = prove
 (`!p (top:A topology) c.
        singular_chain (p,top) (frag_neg c) <=> singular_chain (p,top) c`,
  REWRITE_TAC[singular_chain; FRAG_SUPPORT_NEG]);;

let SINGULAR_CHAIN_ADD = prove
 (`!p (top:A topology) c1 c2.
        singular_chain (p,top) c1 /\ singular_chain (p,top) c2
        ==> singular_chain (p,top) (frag_add c1 c2)`,
  REWRITE_TAC[singular_chain] THEN
  MESON_TAC[FRAG_SUPPORT_ADD; SUBSET_TRANS; UNION_SUBSET]);;

let SINGULAR_CHAIN_SUB = prove
 (`!p (top:A topology) c1 c2.
        singular_chain (p,top) c1 /\ singular_chain (p,top) c2
        ==> singular_chain (p,top) (frag_sub c1 c2)`,
  REWRITE_TAC[singular_chain] THEN
  MESON_TAC[FRAG_SUPPORT_SUB; SUBSET_TRANS; UNION_SUBSET]);;

let SINGULAR_CHAIN_SUM = prove
 (`!p (top:A topology) f k. (!c. c IN k ==> singular_chain (p,top) (f c))
             ==> singular_chain (p,top) (iterate frag_add k f)`,
  REWRITE_TAC[singular_chain] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUM o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC]);;

let SINGULAR_CHAIN_EXTEND = prove
 (`!p top (f:((num->real)->A)->((num->real)->B)frag) x.
        (!c. c IN frag_support x ==> singular_chain (p,top) (f c))
        ==> singular_chain (p,top) (frag_extend f x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frag_extend] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_SUM THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* Boundary homomorphism for singular chains.                                *)
(* ------------------------------------------------------------------------- *)

let chain_boundary = new_definition
 `chain_boundary p (c:((num->real)->A)frag) =
        if p = 0 then frag_0 else
        frag_extend
          (\f. iterate frag_add (0..p)
                (\k. frag_cmul (--(&1) pow k)
                               (frag_of(singular_face p k f)))) c`;;

let SINGULAR_CHAIN_BOUNDARY = prove
 (`!p (top:A topology) c.
        singular_chain (p,top) c
        ==> singular_chain (p - 1,top) (chain_boundary p c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chain_boundary] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SINGULAR_CHAIN_0] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `~(p = 0) ==> 1 <= p`)) THEN
  MATCH_MP_TAC SINGULAR_CHAIN_EXTEND THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SINGULAR_CHAIN_SUM THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SINGULAR_CHAIN_CMUL THEN REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
  MATCH_MP_TAC SINGULAR_SIMPLEX_SINGULAR_FACE THEN
  RULE_ASSUM_TAC(REWRITE_RULE[singular_chain]) THEN ASM SET_TAC[]);;

let SINGULAR_CHAIN_BOUNDARY_ALT = prove
 (`!p (top:A topology) c.
        singular_chain (p + 1,top) c
        ==> singular_chain (p,top) (chain_boundary (p + 1) c)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_CHAIN_BOUNDARY) THEN
  REWRITE_TAC[ADD_SUB]);;

let CHAIN_BOUNDARY_0 = prove
 (`!p. chain_boundary p frag_0 :((num->real)->A)frag = frag_0`,
  GEN_TAC THEN REWRITE_TAC[chain_boundary] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FRAG_EXTEND_0]);;

let CHAIN_BOUNDARY_CMUL = prove
 (`!p a c:((num->real)->A)frag.
        chain_boundary p (frag_cmul a c) =
        frag_cmul a (chain_boundary p c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chain_boundary] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FRAG_EXTEND_CMUL] THEN CONV_TAC FRAG_MODULE);;

let CHAIN_BOUNDARY_NEG = prove
 (`!p c:((num->real)->A)frag.
        chain_boundary p (frag_neg c) = frag_neg (chain_boundary p c)`,
  REWRITE_TAC[FRAG_MODULE `frag_neg x = frag_cmul (-- &1) x`] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_CMUL]);;

let CHAIN_BOUNDARY_ADD = prove
 (`!p c1 c2:((num->real)->A)frag.
        chain_boundary p (frag_add c1 c2) =
        frag_add (chain_boundary p c1) (chain_boundary p c2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chain_boundary] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FRAG_EXTEND_ADD] THEN CONV_TAC FRAG_MODULE);;

let CHAIN_BOUNDARY_SUB = prove
 (`!p c1 c2:((num->real)->A)frag.
        chain_boundary p (frag_sub c1 c2) =
        frag_sub (chain_boundary p c1) (chain_boundary p c2)`,
  REWRITE_TAC[FRAG_MODULE `frag_sub x y = frag_add x (frag_neg y)`] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_ADD; SINGULAR_CHAIN_NEG; CHAIN_BOUNDARY_NEG]);;

let CHAIN_BOUNDARY_SUM = prove
 (`!p g:K->((num->real)->A)frag k.
        FINITE k
        ==> chain_boundary p (iterate frag_add k g) =
            iterate frag_add k (chain_boundary p o g)`,
  GEN_TAC THEN GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  REWRITE_TAC[NEUTRAL_FRAG_ADD; CHAIN_BOUNDARY_0] THEN
  REWRITE_TAC[o_THM; CHAIN_BOUNDARY_ADD]);;

let CHAIN_BOUNDARY_OF = prove
 (`!p f:(num->real)->A.
         chain_boundary p (frag_of f) =
         if p = 0 then frag_0
         else iterate frag_add (0..p)
               (\k. frag_cmul (-- &1 pow k) (frag_of(singular_face p k f)))`,
  REWRITE_TAC[chain_boundary; FRAG_EXTEND_OF]);;

(* ------------------------------------------------------------------------- *)
(* Factoring out chains in a subtopology for relative homology.              *)
(* ------------------------------------------------------------------------- *)

let mod_subset = new_definition
 `mod_subset (p,top) c1 c2 <=> singular_chain (p,top) (frag_sub c1 c2)`;;

let MOD_SUBSET_EMPTY = prove
 (`!p (top:A topology) c1 c2.
        (c1 == c2) (mod_subset (p,subtopology top {})) <=> c1 = c2`,
  SIMP_TAC[cong; mod_subset; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY;
           SINGULAR_CHAIN_EMPTY] THEN
  REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE);;

let MOD_SUBSET_REFL = prove
 (`!p (top:A topology) c. (c == c) (mod_subset(p,top))`,
  REWRITE_TAC[cong; mod_subset; FRAG_MODULE `frag_sub x x = frag_0`] THEN
  REWRITE_TAC[SINGULAR_CHAIN_0]);;

let MOD_SUBSET_CMUL = prove
 (`!p (top:A topology) a c1 c2.
     (c1 == c2) (mod_subset(p,top))
     ==> (frag_cmul a c1 == frag_cmul a c2) (mod_subset(p,top))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong; mod_subset] THEN
  DISCH_THEN(MP_TAC o SPEC `a:int` o MATCH_MP SINGULAR_CHAIN_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

let MOD_SUBSET_ADD = prove
 (`!p (top:A topology) c1 c2 d1 d2.
     (c1 == c2) (mod_subset(p,top)) /\ (d1 == d2) (mod_subset(p,top))
     ==> (frag_add c1 d1 == frag_add c2 d2) (mod_subset(p,top))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[cong; mod_subset] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_CHAIN_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

(* ------------------------------------------------------------------------- *)
(* Relative cycles Z_p(top,s) where top is a topology and s a subset.        *)
(* ------------------------------------------------------------------------- *)

let singular_relcycle = new_definition
 `singular_relcycle(p,top,s) c <=>
        singular_chain (p,top) c /\
        (chain_boundary p c == frag_0) (mod_subset(p-1,subtopology top s))`;;

let SINGULAR_RELCYCLE_RESTRICT = prove
 (`!p (top:A topology) s.
        singular_relcycle(p,top,s) =
        singular_relcycle(p,top,topspace top INTER s)`,
  REWRITE_TAC[FUN_EQ_THM; singular_relcycle; GSYM SUBTOPOLOGY_RESTRICT]);;

let SINGULAR_RELCYCLE = prove
 (`!p (top:A topology) s c.
        singular_relcycle(p,top,s) c <=>
        singular_chain (p,top) c /\
        singular_chain (p-1,subtopology top s) (chain_boundary p c)`,
  REWRITE_TAC[singular_relcycle; cong; mod_subset] THEN
  REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`]);;

let SINGULAR_RELCYCLE_0 = prove
 (`!p (top:A topology) s. singular_relcycle (p,top,s) frag_0`,
  REWRITE_TAC[singular_relcycle; SINGULAR_CHAIN_0; CHAIN_BOUNDARY_0] THEN
  REWRITE_TAC[MOD_SUBSET_REFL]);;

let SINGULAR_RELCYCLE_CMUL = prove
 (`!p (top:A topology) s a c.
        singular_relcycle (p,top,s) c
        ==> singular_relcycle (p,top,s) (frag_cmul a c)`,
  SIMP_TAC[singular_relcycle; SINGULAR_CHAIN_CMUL] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_CMUL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:int` o MATCH_MP MOD_SUBSET_CMUL) THEN
  REWRITE_TAC[FRAG_MODULE `frag_cmul x frag_0 = frag_0`]);;

let SINGULAR_RELCYCLE_NEG = prove
 (`!p (top:A topology) s c.
        singular_relcycle (p,top,s) (frag_neg c) <=>
        singular_relcycle (p,top,s) c`,
  MESON_TAC[SINGULAR_RELCYCLE_CMUL;
            FRAG_MODULE `frag_neg(frag_neg x) = x`;
            FRAG_MODULE `frag_neg x = frag_cmul (-- &1) x`]);;

let SINGULAR_RELCYCLE_ADD = prove
 (`!p (top:A topology) s c1 c2.
        singular_relcycle (p,top,s) c1 /\ singular_relcycle (p,top,s) c2
        ==> singular_relcycle (p,top,s) (frag_add c1 c2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[singular_relcycle; SINGULAR_CHAIN_ADD] THEN
  DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOD_SUBSET_ADD) THEN
  REWRITE_TAC[CHAIN_BOUNDARY_ADD; FRAG_MODULE `frag_add x frag_0 = x`]);;

let SINGULAR_RELCYCLE_SUM = prove
 (`!p top s (f:K->((num->real)->A)frag) k.
        FINITE k /\ (!c. c IN k ==> singular_relcycle (p,top,s) (f c))
        ==> singular_relcycle (p,top,s) (iterate frag_add k f)`,
  REPLICATE_TAC 4 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  REWRITE_TAC[NEUTRAL_FRAG_ADD; SINGULAR_RELCYCLE_0] THEN
  SIMP_TAC[FORALL_IN_INSERT; SINGULAR_RELCYCLE_ADD]);;

let SINGULAR_RELCYCLE_SUB = prove
 (`!p (top:A topology) s c1 c2.
        singular_relcycle (p,top,s) c1 /\ singular_relcycle (p,top,s) c2
        ==> singular_relcycle (p,top,s) (frag_sub c1 c2)`,
  REWRITE_TAC[FRAG_MODULE `frag_sub x y = frag_add x (frag_neg y)`] THEN
  SIMP_TAC[SINGULAR_RELCYCLE_ADD; SINGULAR_RELCYCLE_NEG]);;

let SINGULAR_CYCLE = prove
 (`!p (top:A topology) c.
        singular_relcycle(p,top,{}) c <=>
        singular_chain(p,top) c /\ chain_boundary p c = frag_0`,
  REWRITE_TAC[singular_relcycle; MOD_SUBSET_EMPTY]);;

let SINGULAR_CYCLE_MONO = prove
 (`!p (top:A topology) s t c.
        t SUBSET s /\ singular_relcycle (p,subtopology top t,{}) c
        ==> singular_relcycle (p,subtopology top s,{}) c`,
  REWRITE_TAC[SINGULAR_CYCLE] THEN MESON_TAC[SINGULAR_CHAIN_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Relative boundaries B_p(top,s), where top is a topology and s a subset.   *)
(* ------------------------------------------------------------------------- *)

let singular_relboundary = new_definition
 `singular_relboundary(p,top,s) c <=>
    ?d. singular_chain (p + 1,top) d /\
        (chain_boundary (p + 1) d == c) (mod_subset (p,subtopology top s))`;;

let SINGULAR_RELBOUNDARY_RESTRICT = prove
 (`!p (top:A topology) s.
        singular_relboundary(p,top,s) =
        singular_relboundary(p,top,topspace top INTER s)`,
  REWRITE_TAC[FUN_EQ_THM; singular_relboundary; GSYM SUBTOPOLOGY_RESTRICT]);;

let SINGULAR_RELBOUNDARY_ALT = prove
 (`!p (top:A topology) s c.
        singular_relboundary(p,top,s) c <=>
        ?d e. singular_chain (p + 1,top) d /\
              singular_chain(p,subtopology top s) e /\
              chain_boundary (p + 1) d = frag_add c e`,
  REWRITE_TAC[singular_relboundary; cong; mod_subset] THEN
  REWRITE_TAC[FRAG_MODULE `d = frag_add c e <=> e = frag_sub d c`] THEN
  MESON_TAC[]);;

let SINGULAR_RELBOUNDARY = prove
 (`!p (top:A topology) s c.
        singular_relboundary(p,top,s) c <=>
        ?d e. singular_chain (p + 1,top) d /\
              singular_chain(p,subtopology top s) e /\
              frag_add (chain_boundary (p + 1) d) e = c`,
  REWRITE_TAC[SINGULAR_RELBOUNDARY_ALT; FRAG_MODULE
   `d = frag_add c e <=> frag_add d (frag_neg e) = c`] THEN
  MESON_TAC[SINGULAR_CHAIN_NEG; FRAG_MODULE `frag_neg(frag_neg x) = x`]);;

let SINGULAR_BOUNDARY = prove
 (`!p (top:A topology) c.
        singular_relboundary (p,top,{}) c <=>
        ?d. singular_chain(p+1,top) d /\ chain_boundary (p+1) d = c`,
  REWRITE_TAC[singular_relboundary; MOD_SUBSET_EMPTY]);;

let SINGULAR_BOUNDARY_IMP_CHAIN = prove
 (`!p (top:A topology) c.
        singular_relboundary (p,top,{}) c ==> singular_chain(p,top) c`,
  REWRITE_TAC[singular_relboundary; MOD_SUBSET_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SINGULAR_CHAIN_BOUNDARY) THEN
  REWRITE_TAC[ADD_SUB]);;

let SINGULAR_BOUNDARY_MONO = prove
 (`!p (top:A topology) s t c.
        t SUBSET s /\ singular_relboundary (p,subtopology top t,{}) c
        ==> singular_relboundary (p,subtopology top s,{}) c`,
  REWRITE_TAC[SINGULAR_BOUNDARY] THEN MESON_TAC[SINGULAR_CHAIN_MONO]);;

let SINGULAR_RELBOUNDARY_IMP_CHAIN = prove
 (`!p (top:A topology) s c.
        singular_relboundary (p,top,s) c
        ==> singular_chain(p,top) c`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [SINGULAR_RELBOUNDARY] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SINGULAR_CHAIN_ADD THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_BOUNDARY_ALT] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_TOPSPACE] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_MONO THEN
  EXISTS_TAC `topspace top INTER s:A->bool` THEN
  REWRITE_TAC[INTER_SUBSET; GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]);;

let SINGULAR_CHAIN_IMP_RELBOUNDARY = prove
 (`!p (top:A topology) s c.
     singular_chain (p,subtopology top s) c
     ==> singular_relboundary (p,top,s) c`,
  REWRITE_TAC[singular_relboundary] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `frag_0:((num->real)->A)frag` THEN
  REWRITE_TAC[SINGULAR_CHAIN_0; cong; mod_subset] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN
  ASM_REWRITE_TAC[SINGULAR_CHAIN_0; CHAIN_BOUNDARY_0]);;

let SINGULAR_RELBOUNDARY_0 = prove
 (`!p (top:A topology) s. singular_relboundary (p,top,s) frag_0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[singular_relboundary] THEN
  EXISTS_TAC `frag_0:((num->real)->A)frag` THEN
  REWRITE_TAC[SINGULAR_CHAIN_0; CHAIN_BOUNDARY_0; MOD_SUBSET_REFL]);;

let SINGULAR_RELBOUNDARY_CMUL = prove
 (`!p (top:A topology) s a c.
        singular_relboundary (p,top,s) c
        ==> singular_relboundary (p,top,s) (frag_cmul a c)`,
  REWRITE_TAC[singular_relboundary] THEN
  MESON_TAC[SINGULAR_CHAIN_CMUL; CHAIN_BOUNDARY_CMUL; MOD_SUBSET_CMUL]);;

let SINGULAR_RELBOUNDARY_NEG = prove
 (`!p (top:A topology) s c.
        singular_relboundary (p,top,s) (frag_neg c) <=>
        singular_relboundary (p,top,s) c`,
  MESON_TAC[SINGULAR_RELBOUNDARY_CMUL;
            FRAG_MODULE `frag_neg(frag_neg x) = x`;
            FRAG_MODULE `frag_neg x = frag_cmul (-- &1) x`]);;

let SINGULAR_RELBOUNDARY_ADD = prove
 (`!p (top:A topology) s c1 c2.
        singular_relboundary (p,top,s) c1 /\ singular_relboundary (p,top,s) c2
        ==> singular_relboundary (p,top,s) (frag_add c1 c2)`,
  REWRITE_TAC[singular_relboundary] THEN
  MESON_TAC[SINGULAR_CHAIN_ADD; CHAIN_BOUNDARY_ADD; MOD_SUBSET_ADD]);;

let SINGULAR_RELBOUNDARY_SUB = prove
 (`!p (top:A topology) s c1 c2.
        singular_relboundary (p,top,s) c1 /\ singular_relboundary (p,top,s) c2
        ==> singular_relboundary (p,top,s) (frag_sub c1 c2)`,
  REWRITE_TAC[FRAG_MODULE `frag_sub x y = frag_add x (frag_neg y)`] THEN
  SIMP_TAC[SINGULAR_RELBOUNDARY_ADD; SINGULAR_RELBOUNDARY_NEG]);;

(* ------------------------------------------------------------------------- *)
(* The (relative) homology relation.                                         *)
(* ------------------------------------------------------------------------- *)

let homologous_rel = new_definition
 `homologous_rel (p,top,s) (c1:((num->real)->A)frag) c2 <=>
    singular_relboundary (p,top,s) (frag_sub c1 c2)`;;

let HOMOLOGOUS_REL_RESTRICT = prove
 (`!p (top:A topology) s.
        homologous_rel (p,top,s) =
        homologous_rel (p,top,topspace top INTER s)`,
  REWRITE_TAC[FUN_EQ_THM; homologous_rel;
              GSYM SINGULAR_RELBOUNDARY_RESTRICT]);;

let HOMOLOGOUS_REL_REFL = prove
 (`!p (top:A topology) s c. homologous_rel (p,top,s) c c`,
  REWRITE_TAC[homologous_rel; FRAG_MODULE `frag_sub x x = frag_0`] THEN
  REWRITE_TAC[SINGULAR_RELBOUNDARY_0]);;

let HOMOLOGOUS_REL_SYM = prove
 (`!p (top:A topology) s c1 c2.
        homologous_rel (p,top,s) c1 c2 <=> homologous_rel (p,top,s) c2 c1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homologous_rel] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SINGULAR_RELBOUNDARY_NEG] THEN
  REWRITE_TAC[FRAG_MODULE `frag_neg(frag_sub x y) = frag_sub y x`]);;

let HOMOLOGOUS_REL_TRANS = prove
 (`!p (top:A topology) s c1 c2 c3.
        homologous_rel (p,top,s) c1 c2 /\  homologous_rel (p,top,s) c2 c3
        ==>  homologous_rel (p,top,s) c1 c3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homologous_rel] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

let HOMOLOGOUS_REL_EQ = prove
 (`!p (top:A topology) s c1 c2.
        homologous_rel (p,top,s) c1 = homologous_rel (p,top,s) c2 <=>
        homologous_rel (p,top,s) c1 c2`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[HOMOLOGOUS_REL_REFL; HOMOLOGOUS_REL_SYM; HOMOLOGOUS_REL_TRANS]);;

let HOMOLOGOUS_REL_SINGULAR_CHAIN = prove
 (`!p (top:A topology) s c1 c2.
        homologous_rel (p,top,s) c1 c2
        ==> (singular_chain (p,top) c1 <=> singular_chain (p,top) c2)`,
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!x y. R x y ==> R y x) /\
    (!x y. R x y ==> P y ==> P x)
    ==> (!x y. R x y ==> (P x <=> P y))`) THEN
  CONJ_TAC THENL [MESON_TAC[HOMOLOGOUS_REL_SYM]; REPEAT GEN_TAC] THEN
  REWRITE_TAC[homologous_rel] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_IMP_CHAIN) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_CHAIN_ADD) THEN
  REWRITE_TAC[FRAG_MODULE `frag_add (frag_sub c1 c2) c2 = c1`]);;

let HOMOLOGOUS_REL_ADD = prove
 (`!p (top:A topology) s c1 c1' c2 c2'.
        homologous_rel (p,top,s) c1 c1' /\ homologous_rel (p,top,s) c2 c2'
        ==> homologous_rel (p,top,s) (frag_add c1 c2) (frag_add c1' c2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homologous_rel] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

let HOMOLOGOUS_REL_SUB = prove
 (`!p (top:A topology) s c1 c1' c2 c2'.
        homologous_rel (p,top,s) c1 c1' /\ homologous_rel (p,top,s) c2 c2'
        ==> homologous_rel (p,top,s) (frag_sub c1 c2) (frag_sub c1' c2')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homologous_rel] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC FRAG_MODULE);;

let HOMOLOGOUS_REL_SUM = prove
 (`!p top s f (g:K->((num->real)->A)frag) k.
        (!i. i IN k ==> homologous_rel(p,top,s) (f i) (g i)) /\
        FINITE {i | i IN k /\ ~(f i = frag_0)} /\
        FINITE {i | i IN k /\ ~(g i = frag_0)}
        ==> homologous_rel (p,top,s)
             (iterate frag_add k f) (iterate frag_add k g)`,
  REWRITE_TAC[GSYM FINITE_UNION] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `l = {i | i IN k /\ ~((f:K->((num->real)->A)frag) i = frag_0)} UNION
        {i | i IN k /\ ~((g:K->((num->real)->A)frag) i = frag_0)}` THEN
  SUBGOAL_THEN
   `iterate frag_add k (f:K->((num->real)->A)frag) = iterate frag_add l f /\
    iterate frag_add k (g:K->((num->real)->A)frag) = iterate frag_add l g`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[support; NEUTRAL_FRAG_ADD] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN l
        ==> homologous_rel (p,top,s) ((f:K->((num->real)->A)frag) i) (g i)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `FINITE(l:K->bool)` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`l:K->bool`,`l:K->bool`) THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FORALL_IN_INSERT; MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
  SIMP_TAC[HOMOLOGOUS_REL_REFL; HOMOLOGOUS_REL_ADD]);;

let CHAIN_HOMOTOPIC_IMP_HOMOLOGOUS_REL = prove
 (`!p (top:A topology) s (top':B topology) t h h' f g.
        (!c. singular_chain (p,top) c ==> singular_chain(p + 1,top') (h c)) /\
        (!c. singular_chain (p - 1,subtopology top s) c
             ==> singular_chain(p,subtopology top' t) (h' c)) /\
        (!c. singular_chain (p,top) c
             ==> frag_add (chain_boundary (p + 1) (h c))
                          (h'(chain_boundary p c)) =
                 frag_sub (f c) (g c))
         ==> !c. singular_relcycle (p,top,s) c
                 ==> homologous_rel (p,top',t) (f c) (g c)`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN
  REWRITE_TAC[singular_relcycle; cong; mod_subset] THEN
  REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`] THEN STRIP_TAC THEN
  REWRITE_TAC[homologous_rel; singular_relboundary] THEN
  EXISTS_TAC `(h:((num->real)->A)frag->((num->real)->B)frag) c` THEN
  ASM_SIMP_TAC[cong; mod_subset; SINGULAR_CHAIN_NEG; FRAG_MODULE
   `frag_sub a (frag_add a b) = frag_neg b`]);;

(* ------------------------------------------------------------------------- *)
(* Show that all boundaries are cycles, the key "chain complex" property.    *)
(* ------------------------------------------------------------------------- *)

let CHAIN_BOUNDARY_BOUNDARY = prove
 (`!p (top:A topology) c.
        singular_chain (p,top) c
        ==> chain_boundary (p - 1) (chain_boundary p c) = frag_0`,
  GEN_TAC THEN GEN_TAC THEN ASM_CASES_TAC `p - 1 = 0` THENL
   [ASM_REWRITE_TAC[chain_boundary]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(p - 1 = 0) ==> 2 <= p`)) THEN
  REWRITE_TAC[singular_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[CHAIN_BOUNDARY_0; CHAIN_BOUNDARY_SUB] THEN
  REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`] THEN
  X_GEN_TAC `g:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CHAIN_BOUNDARY_OF; ARITH_RULE `2 <= p ==> ~(p = 0)`] THEN
  SIMP_TAC[CHAIN_BOUNDARY_SUM; FINITE_NUMSEG; o_DEF] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_CMUL] THEN
  ASM_REWRITE_TAC[chain_boundary; FRAG_EXTEND_OF] THEN
  SIMP_TAC[FRAG_CMUL_SUM; FINITE_NUMSEG; o_DEF; FRAG_MODULE
   `frag_cmul a (frag_cmul b c) = frag_cmul (a * b) c`] THEN
  REWRITE_TAC[GSYM INT_POW_ADD] THEN
  SIMP_TAC[MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_FRAG_ADD;
           FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x,y | P x y} = {x,y | P x y /\ (y:num) < x} UNION
                    {x,y | P x y /\ ~(y < x)}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
     (MATCH_MP ITERATE_UNION MONOIDAL_FRAG_ADD) o lhand o snd) THEN
  SIMP_TAC[PAIR_EQ; SET_RULE
   `(!a b a' b'. f a b = f a' b' <=> a = a' /\ b = b')
    ==> DISJOINT {f x y | P x y /\ Q x y} {f x y | P x y /\ ~Q x y}`] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{i,j | (i IN s /\ j IN t) /\ P i j} =
    {i,j | i IN s /\ j IN {k | k IN t /\ P i k}}`] THEN
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(FRAG_MODULE
   `frag_cmul (-- &1) c1 = c2 ==> frag_add c1 c2 = frag_0`) THEN
  REWRITE_TAC[FRAG_CMUL_SUM; o_DEF] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 INT_POW); FRAG_MODULE
   `frag_cmul a (frag_cmul b c) = frag_cmul (a * b) c`] THEN
  REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM; LE_0; NOT_LT; GSYM CONJ_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE
   `i <= p /\ j <= p - 1 /\ j < i <=> j < i /\ i <= p`] THEN
  REWRITE_TAC[ARITH_RULE
   `i <= p /\ j <= p - 1 /\ i <= j <=> i <= j /\ j <= p - 1`] THEN
  SUBGOAL_THEN
   `{i,j | j < i /\ i <= p} =
    IMAGE (\(j,i). i+1,j) {i,j | i <= j /\ j <= p - 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REWRITE_TAC[PAIR_EQ] THEN
    EQ_TAC THENL [STRIP_TAC; ASM_ARITH_TAC] THEN
    MAP_EVERY EXISTS_TAC [`j:num`; `i - 1`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
        (MATCH_MP ITERATE_IMAGE MONOIDAL_FRAG_ADD) o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC((j + 1) + i) = SUC(SUC(i + j))`] THEN
  REWRITE_TAC[INT_POW; INT_MUL_LNEG; INT_MUL_LID; INT_NEG_NEG] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; singular_face] THEN
  X_GEN_TAC `t:(num->real)` THEN
  ASM_CASES_TAC `(t:(num->real)) IN standard_simplex (p - 1 - 1)` THEN
  ASM_REWRITE_TAC[RESTRICTION; o_THM] THEN
  SUBGOAL_THEN `face_map i (t:num->real) IN standard_simplex (p - 1) /\
                face_map j (t:num->real) IN standard_simplex (p - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FACE_MAP_IN_STANDARD_SIMPLEX THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[standard_simplex; IN_ELIM_THM]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[face_map; FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC);;

let CHAIN_BOUNDARY_BOUNDARY_ALT = prove
 (`!p (top:A topology) c.
        singular_chain (p + 1,top) c
        ==> chain_boundary p (chain_boundary (p + 1) c) = frag_0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `p + 2 = (p + 1) + 1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CHAIN_BOUNDARY_BOUNDARY) THEN
  REWRITE_TAC[ADD_SUB]);;

let SINGULAR_RELBOUNDARY_IMP_RELCYCLE = prove
 (`!p s (top:A topology) c.
        singular_relboundary(p,top,s) c ==> singular_relcycle(p,top,s) c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[SINGULAR_RELBOUNDARY; SINGULAR_RELCYCLE] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[CHAIN_BOUNDARY_ADD] THEN
  CONJ_TAC THEN MATCH_MP_TAC SINGULAR_CHAIN_ADD THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_BOUNDARY; SINGULAR_CHAIN_BOUNDARY_ALT] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CHAIN_BOUNDARY_BOUNDARY_ALT) THEN
  REWRITE_TAC[SINGULAR_CHAIN_0] THEN
  ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_TOPSPACE] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_MONO THEN
  EXISTS_TAC `topspace top INTER s:A->bool` THEN
  REWRITE_TAC[INTER_SUBSET; GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE]);;

let HOMOLOGOUS_REL_SINGULAR_RELCYCLE = prove
 (`!p (top:A topology) s c1 c2.
        homologous_rel (p,top,s) c1 c2
        ==> (singular_relcycle (p,top,s) c1 <=>
             singular_relcycle (p,top,s) c2)`,
  REPLICATE_TAC 3 GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!x y. R x y ==> R y x) /\
    (!x y. R x y ==> P y ==> P x)
    ==> (!x y. R x y ==> (P x <=> P y))`) THEN
  CONJ_TAC THENL [MESON_TAC[HOMOLOGOUS_REL_SYM]; REPEAT GEN_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[singular_relcycle] THEN MATCH_MP_TAC MONO_AND THEN
  CONJ_TAC THENL [ASM_MESON_TAC[HOMOLOGOUS_REL_SINGULAR_CHAIN]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[homologous_rel] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELBOUNDARY_IMP_RELCYCLE) THEN
  REWRITE_TAC[singular_relcycle; CHAIN_BOUNDARY_SUB] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOD_SUBSET_ADD) THEN
  REWRITE_TAC[FRAG_MODULE `frag_add (frag_sub c1 c2) c2 = c1`] THEN
  REWRITE_TAC[FRAG_MODULE `frag_add frag_0 x = x`]);;

(* ------------------------------------------------------------------------- *)
(* Operations induced by a continuous map g between topological spaces.      *)
(* ------------------------------------------------------------------------- *)

let simplex_map = new_definition
 `simplex_map p (g:A->B) (c:(num->real)->A) =
        RESTRICTION (standard_simplex p) (g o c)`;;

let SINGULAR_SIMPLEX_SIMPLEX_MAP = prove
 (`!p top top' f g:A->B.
        singular_simplex (p,top) f /\ continuous_map (top,top') g
        ==> singular_simplex (p,top') (simplex_map p g f)`,
  REWRITE_TAC[singular_simplex; simplex_map] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_SUBTOPOLOGY; INTER_SUBSET] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN ASM_MESON_TAC[]);;

let SIMPLEX_MAP_EQ = prove
 (`!p (f:A->B) g top c.
        singular_simplex (p,top) c /\
        (!x. x IN topspace top ==> f x = g x)
        ==>  simplex_map p f c = simplex_map p g c`,
  REWRITE_TAC[simplex_map; singular_simplex; FUN_EQ_THM] THEN
  SIMP_TAC[RESTRICTION; o_DEF; EXTENSIONAL; IN_ELIM_THM] THEN
  REWRITE_TAC[continuous_map] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
  SET_TAC[]);;

let SIMPLEX_MAP_ID_GEN = prove
 (`!p f top (c:(num->real)->A).
        singular_simplex (p,top) c /\
        (!x. x IN topspace top ==> f x = x)
        ==> simplex_map p f c = c`,
  REWRITE_TAC[simplex_map; singular_simplex; FUN_EQ_THM] THEN
  SIMP_TAC[RESTRICTION; o_DEF; EXTENSIONAL; IN_ELIM_THM] THEN
  REWRITE_TAC[continuous_map] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
  REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
  SET_TAC[]);;

let SIMPLEX_MAP_I = prove
 (`!p. simplex_map p (I:A->A) =
       RESTRICTION (standard_simplex p:(num->real)->bool)`,
  REWRITE_TAC[simplex_map; FUN_EQ_THM; I_O_ID]);;

let SIMPLEX_MAP_COMPOSE = prove
 (`!p (g:A->B) (h:B->C).
        simplex_map p (h o g) :((num->real)->A)->((num->real)->C) =
        simplex_map p h o simplex_map p g`,
  REWRITE_TAC[simplex_map; FUN_EQ_THM; o_THM; RESTRICTION_COMPOSE_RIGHT] THEN
  REWRITE_TAC[o_ASSOC]);;

let SINGULAR_FACE_SIMPLEX_MAP = prove
 (`!p k f:A->B c.
        1 <= p /\ k <= p
        ==> singular_face p k (simplex_map p f c) =
            simplex_map (p - 1) f (c o face_map k)`,
  REWRITE_TAC[FUN_EQ_THM; simplex_map; singular_face] THEN
  SIMP_TAC[FACE_MAP_IN_STANDARD_SIMPLEX; RESTRICTION; o_THM]);;

let chain_map = new_definition
 `chain_map p (g:A->B) (c:((num->real)->A)frag) =
        frag_extend (frag_of o simplex_map p g) c`;;

let SINGULAR_CHAIN_CHAIN_MAP = prove
 (`!p top top' (g:A->B) c.
        singular_chain (p,top) c /\ continuous_map (top,top') g
        ==> singular_chain (p,top') (chain_map p g c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chain_map] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_EXTEND THEN
  REWRITE_TAC[SINGULAR_CHAIN_OF; o_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[singular_chain]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SINGULAR_SIMPLEX_SIMPLEX_MAP THEN
  ASM SET_TAC[]);;

let CHAIN_MAP_0 = prove
 (`!p (g:A->B). chain_map p g frag_0 = frag_0`,
  REWRITE_TAC[chain_map; FRAG_EXTEND_0]);;

let CHAIN_MAP_OF = prove
 (`!p (g:A->B) f. chain_map p g (frag_of f) = frag_of (simplex_map p g f)`,
  REWRITE_TAC[chain_map; FRAG_EXTEND_OF; o_THM]);;

let CHAIN_MAP_CMUL = prove
 (`!p (g:A->B) a c.
        chain_map p g (frag_cmul a c) =
        frag_cmul a (chain_map p g c)`,
  REWRITE_TAC[chain_map; FRAG_EXTEND_CMUL]);;

let CHAIN_MAP_NEG = prove
 (`!p (g:A->B) c.
        chain_map p g (frag_neg c) = frag_neg(chain_map p g c)`,
  REWRITE_TAC[chain_map; FRAG_EXTEND_NEG]);;

let CHAIN_MAP_ADD = prove
 (`!p (g:A->B) c1 c2.
        chain_map p g (frag_add c1 c2) =
        frag_add (chain_map p g c1) (chain_map p g c2)`,
  REWRITE_TAC[chain_map; FRAG_EXTEND_ADD]);;

let CHAIN_MAP_SUB = prove
 (`!p (g:A->B) c1 c2.
        chain_map p g (frag_sub c1 c2) =
        frag_sub (chain_map p g c1) (chain_map p g c2)`,
  REWRITE_TAC[chain_map; FRAG_EXTEND_SUB]);;

let CHAIN_MAP_SUM = prove
 (`!p (g:A->B) (f:K->((num->real)->A)frag) k.
        FINITE k
        ==> chain_map p g (iterate frag_add k f) =
            iterate frag_add k (chain_map p g o f)`,
  SIMP_TAC[chain_map; FRAG_EXTEND_SUM; o_DEF]);;

let CHAIN_MAP_EQ = prove
 (`!p (f:A->B) g top c.
        singular_chain (p,top) c /\
        (!x. x IN topspace top ==> f x = g x)
        ==> chain_map p f c = chain_map p g c`,
  REPLICATE_TAC 4 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[CHAIN_MAP_0; CHAIN_MAP_SUB; CHAIN_MAP_OF] THEN
  MESON_TAC[SIMPLEX_MAP_EQ; IN]);;

let CHAIN_MAP_ID_GEN = prove
 (`!p f top (c:((num->real)->A)frag).
        singular_chain (p,top) c /\
        (!x. x IN topspace top ==> f x = x)
        ==> chain_map p f c = c`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[CHAIN_MAP_0; CHAIN_MAP_SUB; CHAIN_MAP_OF] THEN
  MESON_TAC[SIMPLEX_MAP_ID_GEN; IN]);;

let CHAIN_MAP_ID = prove
 (`!p top (c:((num->real)->B)frag).
        singular_chain (p,top) c ==> chain_map p (\x. x) c = c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CHAIN_MAP_ID_GEN THEN
  REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let CHAIN_MAP_I = prove
 (`!p. chain_map p I =
       frag_extend (frag_of o RESTRICTION (standard_simplex p))`,
  REWRITE_TAC[FUN_EQ_THM; chain_map; SIMPLEX_MAP_I; o_DEF]);;

let CHAIN_MAP_COMPOSE = prove
 (`!p (g:A->B) (h:B->C).
        chain_map p (h o g):((num->real)->A)frag->((num->real)->C)frag =
        chain_map p h o chain_map p g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MATCH_MP_TAC(MESON[SUBSET_UNIV]
   `(!c. frag_support c SUBSET (:B) ==> P c) ==> (!c. P c)`) THEN
   MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[CHAIN_MAP_SUB; CHAIN_MAP_0; CHAIN_MAP_OF; o_THM] THEN
  REWRITE_TAC[SIMPLEX_MAP_COMPOSE; o_THM]);;

let SINGULAR_SIMPLEX_CHAIN_MAP_I = prove
 (`!p top f:(num->real)->A.
      singular_simplex (p,top) f
      ==> chain_map p f (frag_of (RESTRICTION (standard_simplex p) I)) =
          frag_of f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[singular_simplex; EXTENSIONAL; IN_ELIM_THM] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[CHAIN_MAP_OF; simplex_map] THEN
  REWRITE_TAC[RESTRICTION_COMPOSE_RIGHT; I_O_ID] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
  ASM_MESON_TAC[]);;

let CHAIN_BOUNDARY_CHAIN_MAP = prove
 (`!p top g:A->B c:((num->real)->A)frag.
        singular_chain (p,top) c
        ==> chain_boundary p (chain_map p g c) =
            chain_map (p - 1) g (chain_boundary p c)`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[CHAIN_MAP_0; CHAIN_BOUNDARY_0] THEN
  SIMP_TAC[CHAIN_BOUNDARY_SUB; CHAIN_MAP_SUB] THEN
  X_GEN_TAC `f:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  REWRITE_TAC[CHAIN_MAP_OF; CHAIN_BOUNDARY_OF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CHAIN_MAP_0] THEN
  SIMP_TAC[CHAIN_MAP_SUM; FINITE_NUMSEG; o_DEF; CHAIN_MAP_CMUL] THEN
  REWRITE_TAC[CHAIN_MAP_OF] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
  REWRITE_TAC[IN_NUMSEG; o_THM] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[singular_face; simplex_map; FUN_EQ_THM] THEN
  REWRITE_TAC[RESTRICTION_COMPOSE_RIGHT] THEN
  ASM_SIMP_TAC[RESTRICTION; o_THM; FACE_MAP_IN_STANDARD_SIMPLEX; LE_1]);;

let SINGULAR_RELCYCLE_CHAIN_MAP = prove
 (`!p top s top' t g:A->B c:((num->real)->A)frag.
        singular_relcycle (p,top,s) c /\
        continuous_map (top,top') g /\ IMAGE g s SUBSET t
        ==> singular_relcycle (p,top',t) (chain_map p g c)`,
  REWRITE_TAC[SINGULAR_RELCYCLE] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SINGULAR_CHAIN_CHAIN_MAP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`p:num`; `top:A topology`; `g:A->B`]
        CHAIN_BOUNDARY_CHAIN_MAP) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC SINGULAR_CHAIN_CHAIN_MAP THEN
  EXISTS_TAC `subtopology top (s:A->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_INTO_SUBTOPOLOGY THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  ASM SET_TAC[]);;

let SINGULAR_RELBOUNDARY_CHAIN_MAP = prove
 (`!p top s top' t g:A->B c:((num->real)->A)frag.
        singular_relboundary (p,top,s) c /\
        continuous_map (top,top') g /\ IMAGE g s SUBSET t
         ==> singular_relboundary (p,top',t) (chain_map p g c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SINGULAR_RELBOUNDARY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN INTRO_TAC "!d e" THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MAP_EVERY EXISTS_TAC
   [`chain_map (p + 1) (g:A->B) d`; `chain_map p (g:A->B) e`] THEN
  REWRITE_TAC[CHAIN_MAP_ADD; CONJ_ASSOC] THEN CONJ_TAC
  THENL [ALL_TAC; ASM_MESON_TAC[CHAIN_BOUNDARY_CHAIN_MAP; ADD_SUB]] THEN
  CONJ_TAC THEN MATCH_MP_TAC SINGULAR_CHAIN_CHAIN_MAP THENL
   [ASM_MESON_TAC[]; EXISTS_TAC `subtopology top (s:A->bool)`] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
               CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Homology of one-point spaces degenerates except for p = 0.                *)
(* ------------------------------------------------------------------------- *)

let SINGULAR_SIMPLEX_SING = prove
 (`!p top a f:(num->real)->A.
        topspace top = {a}
        ==> (singular_simplex(p,top) f <=>
             f = RESTRICTION (standard_simplex p) (\x. a))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_simplex] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        (REWRITE_RULE[IN] EXTENSIONAL_EQ))) THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
    REWRITE_TAC[CARTESIAN_PRODUCT_UNIV; o_DEF; TOPSPACE_EUCLIDEANREAL] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_SING; INTER_UNIV] THEN
    SIMP_TAC[IN; RESTRICTION];
    ASM_REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    ASM_SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_SUBTOPOLOGY;
                 INTER_SUBSET; CONTINUOUS_MAP_CONST; IN_SING]]);;

let SINGULAR_CHAIN_SING = prove
 (`!p top a c:((num->real)->A)frag.
        topspace top = {a}
        ==> (singular_chain(p,top) c <=>
             ?b. c = frag_cmul b
                      (frag_of(RESTRICTION (standard_simplex p) (\x. a))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_chain] THEN
  REWRITE_TAC[SET_RULE `s SUBSET t <=> !x. x IN s ==> t x`] THEN
  ASM_SIMP_TAC[SINGULAR_SIMPLEX_SING; SET_RULE
   `(!x. x IN s ==> x = a) <=> s SUBSET {a}`] THEN
  EQ_TAC THENL
   [ALL_TAC; MESON_TAC[FRAG_SUPPORT_CMUL; FRAG_SUPPORT_OF; SUBSET_TRANS]] THEN
  REWRITE_TAC[FRAG_SUPPORT_EQ_EMPTY; SET_RULE
   `s SUBSET {a} <=> s = {} \/ s = {a}`] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[FRAG_MODULE `frag_cmul (&0) x = frag_0`]; ALL_TAC] THEN
  GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [FRAG_EXPANSION] THEN
  ASM_REWRITE_TAC[frag_extend; MATCH_MP ITERATE_SING MONOIDAL_FRAG_ADD] THEN
  REWRITE_TAC[o_THM] THEN MESON_TAC[]);;

let CHAIN_BOUNDARY_OF_SING = prove
 (`!p top a c:((num->real)->A)frag.
        topspace top = {a} /\ singular_chain (p,top) c
        ==> chain_boundary p c =
                if p = 0 \/ ODD p then frag_0 else
                frag_extend
                  (\f. frag_of(RESTRICTION (standard_simplex (p - 1)) (\x. a)))
                  c`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[chain_boundary] THEN
  TRANS_TAC EQ_TRANS
    `frag_extend (\f. if ODD p then frag_0 else
                      frag_of(RESTRICTION (standard_simplex (p - 1))
                                          ((\x. a):(num->real)->A)))
                 (c:((num->real)->A)frag)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FRAG_EXTEND_EQ;
    ASM_CASES_TAC `ODD p` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FRAG_EXTEND_EQ_0 THEN REWRITE_TAC[]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[singular_chain]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s SUBSET t ==> (!x. t x ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
  REWRITE_TAC[] THEN X_GEN_TAC `f:(num->real)->A` THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `iterate frag_add (0..p)
         (\k. frag_cmul (-- &1 pow k)
                (frag_of(RESTRICTION (standard_simplex (p - 1))
                             ((\x. a):(num->real)->A))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM SINGULAR_SIMPLEX_SING] THEN
    MATCH_MP_TAC SINGULAR_SIMPLEX_SINGULAR_FACE THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ABBREV_TAC `c:((num->real)->A)frag =
                frag_of(RESTRICTION (standard_simplex (p - 1)) (\x. a))` THEN
    SPEC_TAC(`p:num`,`p:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC num_INDUCTION THEN
    SIMP_TAC[MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_FRAG_ADD; LE_0] THEN
    SIMP_TAC[ODD] THEN CONJ_TAC THENL [CONV_TAC FRAG_MODULE; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `ODD p` THEN
    ASM_SIMP_TAC[INT_POW_NEG; GSYM NOT_ODD; ODD; INT_POW_ONE] THEN
    DISCH_THEN(K ALL_TAC) THEN CONV_TAC FRAG_MODULE]);;

let SINGULAR_CYCLE_SING = prove
 (`!p top a c:((num->real)->A)frag.
        topspace top = {a}
        ==> (singular_relcycle (p,top,{}) c <=>
             singular_chain (p,top) c /\ (p = 0 \/ ODD p \/ c = frag_0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SINGULAR_CYCLE] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`) THEN
  DISCH_TAC THEN REWRITE_TAC[DISJ_ASSOC] THEN
  MP_TAC(ISPECL [`p:num`; `top:A topology`; `a:A`]
        CHAIN_BOUNDARY_OF_SING) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`p:num`; `top:A topology`; `a:A`; `c:((num->real)->A)frag`]
        SINGULAR_CHAIN_SING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[FRAG_EXTEND_CMUL; FRAG_EXTEND_OF; FRAG_OF_NONZERO; FRAG_MODULE
    `frag_cmul b c = frag_0 <=> b = &0 \/ c = frag_0`]);;

let SINGULAR_BOUNDARY_SING = prove
 (`!p top a c:((num->real)->A)frag.
        topspace top = {a}
        ==> (singular_relboundary (p,top,{}) c <=>
             singular_chain (p,top) c /\ (ODD p \/ c = frag_0))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `singular_chain(p,top) (c:((num->real)->A)frag)` THENL
   [ASM_REWRITE_TAC[]; ASM_MESON_TAC[SINGULAR_BOUNDARY_IMP_CHAIN]] THEN
  REWRITE_TAC[SINGULAR_BOUNDARY; TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  MP_TAC(ISPECL [`p + 1`; `top:A topology`; `a:A`] CHAIN_BOUNDARY_OF_SING) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[ADD_EQ_0; ODD_ADD; NOT_IMP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(ISPECL [`p + 1`; `top:A topology`; `a:A`] SINGULAR_CHAIN_SING) THEN
  ASM_SIMP_TAC[LEFT_AND_EXISTS_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[UNWIND_THM2; FRAG_EXTEND_CMUL; FRAG_EXTEND_OF; ADD_SUB] THEN
  ASM_CASES_TAC `ODD p` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  ASM_MESON_TAC[GSYM SINGULAR_CHAIN_SING]);;

let SINGULAR_BOUNDARY_EQ_CYCLE_SING = prove
 (`!p top a c:((num->real)->A)frag.
      topspace top = {a} /\ 1 <= p
      ==> (singular_relboundary (p,top,{}) c <=>
           singular_relcycle (p,top,{}) c)`,
  METIS_TAC[LE_1; SINGULAR_CYCLE_SING; SINGULAR_BOUNDARY_SING]);;

(* ------------------------------------------------------------------------- *)
(* Simplicial chains, effectively those resulting from linear maps.          *)
(* We still allow the map to be singular, so the name is questionable.       *)
(* These are intended as building-blocks for singular subdivision, rather    *)
(* than as a basis for simplicial homology.                                  *)
(* ------------------------------------------------------------------------- *)

let oriented_simplex = new_definition
 `oriented_simplex p l =
    RESTRICTION (standard_simplex p)
                (\x i:num. sum(0..p) (\j. l j i * x j))`;;

let ORIENTED_SIMPLEX_EQ = prove
 (`(!i. i <= p ==> l i = m i)
   ==> oriented_simplex p l = oriented_simplex p m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[oriented_simplex] THEN
  AP_TERM_TAC THEN ABS_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN ASM_SIMP_TAC[]);;

let simplicial_simplex = new_definition
 `simplicial_simplex (p,s) f <=>
        singular_simplex
         (p,subtopology (product_topology (:num) (\i. euclideanreal)) s) f /\
        ?l. f = oriented_simplex p l`;;

let SIMPLICIAL_SIMPLEX = prove
 (`!p s f.
        simplicial_simplex (p,s) f <=>
        IMAGE f (standard_simplex p) SUBSET s /\
        ?l. f = oriented_simplex p l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simplicial_simplex; SINGULAR_SIMPLEX_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(TAUT `(r ==> p) ==> ((p /\ q) /\ r <=> q /\ r)`) THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; singular_simplex; oriented_simplex] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_SUBTOPOLOGY; INTER_SUBSET] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; IN_UNIV] THEN
  REWRITE_TAC[SUBSET; IN; EXTENSIONAL_UNIV] THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC CONTINUOUS_MAP_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `n:num` THEN
  STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_REAL_LMUL THEN
  MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
  SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV]);;

let SIMPLICIAL_SIMPLEX_EMPTY = prove
 (`!p s f. ~(simplicial_simplex (p,{}) f)`,
  SIMP_TAC[simplicial_simplex; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY;
           SINGULAR_SIMPLEX_EMPTY]);;

let simplicial_chain = new_definition
 `simplicial_chain (p,s) c <=>
  frag_support c SUBSET simplicial_simplex (p,s)`;;

let SIMPLICIAL_CHAIN_0 = prove
 (`!p s. simplicial_chain (p,s) frag_0`,
  REWRITE_TAC[simplicial_chain; FRAG_SUPPORT_0; EMPTY_SUBSET]);;

let SIMPLICIAL_CHAIN_OF = prove
 (`!p s c. simplicial_chain (p,s) (frag_of c) <=> simplicial_simplex (p,s) c`,
  REWRITE_TAC[simplicial_chain; FRAG_SUPPORT_OF] THEN SET_TAC[]);;

let SIMPLICIAL_CHAIN_CMUL = prove
 (`!p s a c. simplicial_chain (p,s) c
             ==> simplicial_chain (p,s) (frag_cmul a c)`,
  REWRITE_TAC[simplicial_chain] THEN
  MESON_TAC[FRAG_SUPPORT_CMUL; SUBSET_TRANS]);;

let SIMPLICIAL_CHAIN_SUB = prove
 (`!p s c1 c2.
        simplicial_chain (p,s) c1 /\ simplicial_chain (p,s) c2
        ==> simplicial_chain (p,s) (frag_sub c1 c2)`,
  REWRITE_TAC[simplicial_chain] THEN
  MESON_TAC[FRAG_SUPPORT_SUB; SUBSET_TRANS; UNION_SUBSET]);;

let SIMPLICIAL_CHAIN_SUM = prove
 (`!p s f k. (!c. c IN k ==> simplicial_chain (p,s) (f c))
             ==> simplicial_chain (p,s) (iterate frag_add k f)`,
  REWRITE_TAC[simplicial_chain] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_SUM o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC]);;

let SIMPLICIAL_SIMPLEX_ORIENTED_SIMPLEX = prove
 (`!p s l. simplicial_simplex (p,s) (oriented_simplex p l) <=>
           IMAGE (\x i. sum (0..p) (\j. l j i * x j)) (standard_simplex p)
           SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIMPLICIAL_SIMPLEX] THEN
  MATCH_MP_TAC(TAUT `q /\ (p <=> p') ==> (p /\ q <=> p')`) THEN
  CONJ_TAC THENL [MESON_TAC[]; REWRITE_TAC[oriented_simplex]] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION]);;

let SIMPLICIAL_IMP_SINGULAR_SIMPLEX = prove
 (`!p s f.
      simplicial_simplex (p,s) f
      ==> singular_simplex
            (p,subtopology (product_topology (:num) (\i. euclideanreal)) s) f`,
  SIMP_TAC[simplicial_simplex]);;

let SIMPLICIAL_IMP_SINGULAR_CHAIN = prove
 (`!p s c. simplicial_chain (p,s) c
         ==> singular_chain
            (p,subtopology (product_topology (:num) (\i. euclideanreal)) s) c`,
  REWRITE_TAC[simplicial_chain; singular_chain] THEN
  SIMP_TAC[SUBSET; IN; SIMPLICIAL_IMP_SINGULAR_SIMPLEX]);;

let ORIENTED_SIMPLEX_EQ = prove
 (`!p l l'. oriented_simplex p l = oriented_simplex p l' <=>
            !i. i <= p ==> l i = l' i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oriented_simplex] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `(\j:num. if j = i then &1 else &0)`) THEN
    ASM_REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX; RESTRICTION] THEN
    SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; REAL_MUL_RID; ETA_AX];
    DISCH_TAC THEN AP_TERM_TAC THEN REPEAT ABS_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_NUMSEG; LE_0]]);;

let SINGULAR_FACE_ORIENTED_SIMPLEX = prove
 (`!p k l.
        1 <= p /\ k <= p
        ==> singular_face p k (oriented_simplex p l) =
            oriented_simplex (p - 1)
                             (\j. if j < k then l j else l (j + 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[singular_face; oriented_simplex] THEN
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real`; `j:num`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[RESTRICTION; o_DEF; FACE_MAP_IN_STANDARD_SIMPLEX] THEN
  REWRITE_TAC[face_map] THEN REPLICATE_TAC 2
   (REWRITE_TAC[COND_RATOR] THEN ONCE_REWRITE_TAC[COND_RAND]) THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; SUM_0] THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; SUM_0] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0; IN_ELIM_THM] THEN
  SUBGOAL_THEN `!i. i <= p - 1 /\ i < k <=> i <= p /\ i < k`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!i. (i <= p /\ ~(i < k)) /\ ~(i = k) <=>
         k + 1 <= i /\ i <= (p - 1) + 1`
   (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM numseg; NOT_LT; SUM_OFFSET; ADD_SUB] THEN
  BINOP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC);;

let SIMPLICIAL_SIMPLEX_SINGULAR_FACE = prove
 (`!p s k f.
      simplicial_simplex (p,s) f /\ 1 <= p /\ k <= p
      ==> simplicial_simplex (p - 1,s) (singular_face p k f)`,
  SIMP_TAC[simplicial_simplex; SINGULAR_SIMPLEX_SINGULAR_FACE] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num->num->real` SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[singular_face; oriented_simplex] THEN
  ASM_SIMP_TAC[RESTRICTION_COMPOSE_LEFT; SUBSET; FORALL_IN_IMAGE;
               FACE_MAP_IN_STANDARD_SIMPLEX] THEN
  EXISTS_TAC `\i. if i < k then (m:num->num->real) i else m (i + 1)` THEN
  REWRITE_TAC[face_map; o_DEF] THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:num->real`; `i:num`] THEN
  REPLICATE_TAC 2
   (ONCE_REWRITE_TAC[COND_RAND] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR]) THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0; ARITH_RULE
   `k <= p ==> (j <= p - 1 /\ j < k <=> j <= p /\ j < k)`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; NOT_LT] THEN
  REWRITE_TAC[ARITH_RULE `j:num <= p /\ k <= j <=> k <= j /\ j <= p`] THEN
  SIMP_TAC[SUM_CASES; FINITE_NUMSEG; GSYM numseg] THEN
  REWRITE_TAC[SUM_0; REAL_ADD_LID; IN_NUMSEG] THEN ASM_SIMP_TAC[ARITH_RULE
   `1 <= p ==> ((k <= j /\ j <= p) /\ ~(j = k) <=>
                k + 1 <= j /\ j <= (p - 1) + 1)`] THEN
  REWRITE_TAC[GSYM numseg; SUM_OFFSET; ADD_SUB]);;

let SIMPLICIAL_CHAIN_BOUNDARY = prove
 (`!p s c. simplicial_chain (p,s) c
           ==> simplicial_chain (p - 1,s) (chain_boundary p c)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[simplicial_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[CHAIN_BOUNDARY_0; FRAG_SUPPORT_0; EMPTY_SUBSET] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_SUB; GSYM UNION_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[IN]; MESON_TAC[SUBSET; FRAG_SUPPORT_SUB]] THEN
  X_GEN_TAC `f:(num->real)->(num->real)` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM simplicial_chain] THEN
  REWRITE_TAC[chain_boundary; FRAG_EXTEND_OF] THEN
  COND_CASES_TAC THEN REWRITE_TAC[SIMPLICIAL_CHAIN_0] THEN
  MATCH_MP_TAC SIMPLICIAL_CHAIN_SUM THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC SIMPLICIAL_CHAIN_CMUL THEN
  REWRITE_TAC[SIMPLICIAL_CHAIN_OF; simplicial_simplex] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplicial_simplex]) THEN
  ASM_SIMP_TAC[SINGULAR_SIMPLEX_SINGULAR_FACE; LE_1] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SINGULAR_FACE_ORIENTED_SIMPLEX; LE_1] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The cone construction on simplicial simplices.                            *)
(* ------------------------------------------------------------------------- *)

let simplex_cone =
  let exth = prove
   (`?cone. !p v l.
          cone p v (oriented_simplex p l) =
          oriented_simplex (p + 1) (\i. if i = 0 then v else l(i - 1))`,
    REWRITE_TAC[GSYM SKOLEM_THM] THEN REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
    GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [GSYM o_DEF] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    GEN_REWRITE_TAC I [GSYM FUNCTION_FACTORS_LEFT] THEN
    REWRITE_TAC[ORIENTED_SIMPLEX_EQ] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC) in
  new_specification ["simplex_cone"] exth;;

let SIMPLICIAL_SIMPLEX_SIMPLEX_CONE = prove
 (`!p s t v f.
        simplicial_simplex (p,s) f /\
        (!x u. &0 <= u /\ u <= &1 /\ x IN s
               ==> (\i. (&1 - u) * v i + u * x i) IN t)
        ==> simplicial_simplex (p + 1,t) (simplex_cone p v f)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:(num->real)->bool = {}` THEN
  ASM_REWRITE_TAC[SIMPLICIAL_SIMPLEX_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  SIMP_TAC[SIMPLICIAL_SIMPLEX; IMP_CONJ_ALT; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l:num->num->real` THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; simplex_cone] THEN
  DISCH_THEN(fun th -> CONJ_TAC THENL [MP_TAC th; MESON_TAC[]]) THEN
  SIMP_TAC[oriented_simplex; RESTRICTION; standard_simplex; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `x:num->real` THEN STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN REWRITE_TAC[SUM_OFFSET] THEN
  REWRITE_TAC[ADD_SUB; ARITH_RULE `~(i + 1 = 0)`] THEN
  ASM_CASES_TAC `(x:num->real) 0 = &1` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `a:num->real` o
       REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:num->real`; `&0`]) THEN
    ASM_REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `n:num` THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_MUL_LID; REAL_MUL_RID] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    UNDISCH_TAC `sum (0..p + 1) x = &1` THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN REWRITE_TAC[SUM_OFFSET] THEN
    ASM_REWRITE_TAC[REAL_ARITH `&1 + x = &1 <=> x = &0`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        SUM_POS_EQ_0_NUMSEG)) THEN
    ASM_REWRITE_TAC[LE_0] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = &1)
      ==> v * x + s = (&1 - (&1 - x)) * v + (&1 - x) * inv(&1 - x) * s`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_ARITH `&1 - x <= &1 <=> &0 <= x`] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `inv x * y * z:real = y * z / x`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_LE; REAL_SUB_LT;
                 ARITH_RULE `p < i ==> p + 1 < i + 1`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; real_div; REAL_MUL_LID] THEN
    UNDISCH_TAC `sum (0..p + 1) x = &1` THEN
    MP_TAC(ARITH_RULE `0 <= p + 1`) THEN SIMP_TAC[SUM_CLAUSES_LEFT] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[SUM_OFFSET] THEN
    REWRITE_TAC[REAL_ARITH `x + s = &1 <=> s = &1 - x`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SUM_RMUL; REAL_MUL_RINV; REAL_SUB_0] THEN
    X_GEN_TAC `n:num` THEN
    ASM_CASES_TAC `p + 1 < n + 1` THEN ASM_SIMP_TAC[REAL_SUB_LE] THEN
    TRANS_TAC REAL_LE_TRANS `sum {n} (\i. (x:num->real)(i + 1))` THEN
    CONJ_TAC THENL [REWRITE_TAC[SUM_SING; REAL_LE_REFL]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; SING_SUBSET; IN_NUMSEG] THEN
    ASM_ARITH_TAC]);;

let simplicial_cone = new_definition
 `simplicial_cone p v = frag_extend (frag_of o simplex_cone p v)`;;

let SIMPLICIAL_CHAIN_SIMPLICIAL_CONE = prove
 (`!p s t v c.
        simplicial_chain (p,s) c /\
        (!x u. &0 <= u /\ u <= &1 /\ x IN s
               ==> (\i. (&1 - u) * v i + u * x i) IN t)
        ==> simplicial_chain (p + 1,t) (simplicial_cone p v c)`,
  REWRITE_TAC[IMP_CONJ_ALT; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN DISCH_TAC THEN
  REWRITE_TAC[simplicial_chain] THEN
  REWRITE_TAC[simplicial_cone] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[FRAG_EXTEND_0; FRAG_EXTEND_SUB; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET; FRAG_SUPPORT_OF; o_THM] THEN
  REWRITE_TAC[GSYM UNION_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SING_SUBSET] THEN REWRITE_TAC[IN] THEN
    ASM_MESON_TAC[SIMPLICIAL_SIMPLEX_SIMPLEX_CONE];
    MESON_TAC[SUBSET; FRAG_SUPPORT_SUB]]);;

let CHAIN_BOUNDARY_SIMPLICIAL_CONE_OF = prove
 (`!p s v f.
        simplicial_simplex (p,s) f
        ==> chain_boundary (p + 1) (simplicial_cone p v (frag_of f)) =
            frag_sub (frag_of f)
             (if p = 0 then frag_of(RESTRICTION (standard_simplex p) (\u. v))
              else simplicial_cone (p - 1) v (chain_boundary p (frag_of f)))`,
  REPLICATE_TAC 3 GEN_TAC THEN
  REWRITE_TAC[simplicial_simplex; IMP_CONJ_ALT; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN X_GEN_TAC `l:num->num->real` THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[simplicial_cone; FRAG_EXTEND_OF; o_THM; CHAIN_BOUNDARY_OF] THEN
  REWRITE_TAC[ADD_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THENL
   [SIMP_TAC[GSYM ADD1; MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_FRAG_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
    SIMP_TAC[simplex_cone; SINGULAR_FACE_ORIENTED_SIMPLEX; ARITH] THEN
    REWRITE_TAC[CONJUNCT1 LT; ADD_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[ARITH_RULE `j < 1 <=> j = 0`; ADD_SUB; ETA_AX; FRAG_MODULE
     `frag_add (frag_cmul (&1) x) (frag_cmul (-- &1) y) = frag_sub x y`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[oriented_simplex] THEN
    SIMP_TAC[SUM_SING_NUMSEG; RESTRICTION; FUN_EQ_THM; standard_simplex;
             IN_ELIM_THM; REAL_MUL_RID; ETA_AX];
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [GSYM(REWRITE_RULE[LE_0] (SPEC `0` NUMSEG_LREC))] THEN
    SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD; FINITE_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `~(0 + 1 <= 0)`; IN_NUMSEG; FRAG_MODULE
     `frag_add (frag_cmul (-- &1 pow 0) x) y =
      frag_sub x (frag_cmul (-- &1) y)`] THEN
    BINOP_TAC THENL
     [AP_TERM_TAC THEN
      SIMP_TAC[simplex_cone; SINGULAR_FACE_ORIENTED_SIMPLEX; LE_0;
               ADD_SUB; ARITH_RULE `1 <= p + 1 /\ ~(j + 1 = 0)`] THEN
      REWRITE_TAC[ORIENTED_SIMPLEX_EQ; CONJUNCT1 LT];
      REWRITE_TAC[FRAG_CMUL_SUM; NUMSEG_OFFSET_IMAGE] THEN
      W(MP_TAC o PART_MATCH (lhand o rand)
        (MATCH_MP ITERATE_IMAGE MONOIDAL_FRAG_ADD) o lhand o snd) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      SIMP_TAC[FRAG_EXTEND_SUM; FINITE_NUMSEG] THEN
      MATCH_MP_TAC (MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
      X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG; o_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[FRAG_EXTEND_CMUL; FRAG_MODULE
       `frag_cmul a (frag_cmul b c) = frag_cmul (a * b) c`] THEN
      REWRITE_TAC[INT_POW_ADD; INT_MUL_LNEG; INT_MUL_RNEG; INT_POW_1] THEN
      REWRITE_TAC[INT_NEG_NEG; INT_MUL_RID; INT_MUL_LID] THEN AP_TERM_TAC THEN
      REWRITE_TAC[o_THM; FRAG_EXTEND_OF] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[simplex_cone; SINGULAR_FACE_ORIENTED_SIMPLEX; LE_1;
                   LE_ADD_RCANCEL; ARITH_RULE `1 <= k + 1`; ADD_SUB; SUB_ADD;
                   ORIENTED_SIMPLEX_EQ] THEN
      REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_ARITH_TAC]]);;

let CHAIN_BOUNDARY_SIMPLICIAL_CONE = prove
 (`!p s v c.
        simplicial_chain (p,s) c
        ==> chain_boundary (p + 1) (simplicial_cone p v c) =
            frag_sub c
             (if p = 0 then
              frag_extend
               (\f. frag_of(RESTRICTION (standard_simplex p) (\u. v))) c
              else simplicial_cone (p - 1) v (chain_boundary p c))`,
  REPLICATE_TAC 3 GEN_TAC THEN
  REWRITE_TAC[simplicial_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CHAIN_BOUNDARY_0; simplicial_cone; FRAG_EXTEND_0] THEN
    REWRITE_TAC[COND_ID] THEN CONV_TAC FRAG_MODULE;
    REWRITE_TAC[IN; FRAG_EXTEND_OF; o_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CHAIN_BOUNDARY_SIMPLICIAL_CONE_OF o
        lhand o snd) THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[CHAIN_BOUNDARY_SUB; simplicial_cone; FRAG_EXTEND_SUB] THEN
    REWRITE_TAC[GSYM simplicial_cone] THEN
    REWRITE_TAC[COND_ID] THEN CONV_TAC FRAG_MODULE]);;

let SIMPLEX_MAP_ORIENTED_SIMPLEX = prove
 (`!p q r g l s.
        simplicial_simplex(p,standard_simplex q) (oriented_simplex p l) /\
        simplicial_simplex(r,s) g /\ q <= r
        ==> simplex_map p g (oriented_simplex p l) =
            oriented_simplex p (g o l)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[oriented_simplex; simplex_map; RESTRICTION_COMPOSE_RIGHT] THEN
  REWRITE_TAC[o_DEF] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `x:num->real` THEN
  REWRITE_TAC[RESTRICTION] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ASSUME `simplicial_simplex (r,s) g`) THEN
  REWRITE_TAC[simplicial_simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num->num->real` SUBST_ALL_TAC) THEN
  REWRITE_TAC[oriented_simplex] THEN
  GEN_REWRITE_TAC LAND_CONV [RESTRICTION] THEN
  UNDISCH_TAC
   `simplicial_simplex (p,standard_simplex q) (oriented_simplex p l)` THEN
  REWRITE_TAC[SIMPLICIAL_SIMPLEX_ORIENTED_SIMPLEX] THEN
  FIRST_ASSUM(MP_TAC o
    REWRITE_RULE[SUBSET] o MATCH_MP STANDARD_SIMPLEX_MONO) THEN
  ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o GEN `i:num` o
    SPEC `(\j. if j = i then &1 else &0):num->real`) THEN
  REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX; COND_RAND] THEN
  SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; LE_0; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[ETA_AX; RESTRICTION; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  DISCH_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;

let CHAIN_MAP_SIMPLICIAL_CONE = prove
 (`!s p q r v c g.
        simplicial_simplex (r,s) g /\
        simplicial_chain (p,standard_simplex q) c /\
        v IN standard_simplex q /\ q <= r
        ==> chain_map (p + 1) g (simplicial_cone p v c) =
            simplicial_cone p (g v) (chain_map p g c)`,
  REWRITE_TAC[chain_map; simplicial_cone; FRAG_EXTEND_COMPOSE] THEN
  REWRITE_TAC[simplicial_chain] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRAG_EXTEND_EQ THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:(num->real)->(num->real)` o
    REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  MP_TAC(ASSUME `simplicial_simplex (p,standard_simplex q) f`) THEN
  REWRITE_TAC[simplicial_simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num->num->real` SUBST_ALL_TAC) THEN
  REWRITE_TAC[simplex_cone] THEN
  MP_TAC(ISPECL
   [`p + 1`; `q:num`; `r:num`; `g:(num->real)->(num->real)`;
    `(\i. if i = 0 then v else m (i - 1)):num->num->real`;
     `s:(num->real)->bool`] SIMPLEX_MAP_ORIENTED_SIMPLEX) THEN
  REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM ADD1; GSYM simplex_cone] THEN
    REWRITE_TAC[ADD1] THEN MATCH_MP_TAC SIMPLICIAL_SIMPLEX_SIMPLEX_CONE THEN
    EXISTS_TAC `standard_simplex q` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_STANDARD_SIMPLEX THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    MATCH_MP_TAC STANDARD_SIMPLEX_MONO THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL
   [`p:num`; `q:num`; `r:num`; `g:(num->real)->(num->real)`;
    `m:num->num->real`; `s:(num->real)->bool`]
   SIMPLEX_MAP_ORIENTED_SIMPLEX) THEN
  ASM_REWRITE_TAC[GSYM ADD1; ARITH_RULE `p <= SUC p`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[simplex_cone] THEN
  REWRITE_TAC[o_DEF; COND_RAND; ADD1]);;

(* ------------------------------------------------------------------------- *)
(* Barycentric subdivision of a linear ("simplicial") simplex's image.       *)
(* ------------------------------------------------------------------------- *)

let simplicial_vertex = new_definition
 `simplicial_vertex i (f:(num->real)->(num->real)) =
        f(\j. if j = i then &1 else &0)`;;

let SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX = prove
 (`!i p l. simplicial_vertex i (oriented_simplex p l) =
           if i <= p then l i else ARB`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simplicial_vertex; oriented_simplex] THEN
  REWRITE_TAC[RESTRICTION; BASIS_IN_STANDARD_SIMPLEX] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  ASM_REWRITE_TAC[IN_NUMSEG; LE_0; REAL_MUL_RID; ETA_AX]);;

let simplicial_subdivision = new_recursive_definition num_RECURSION
 `simplicial_subdivision 0 = I /\
  simplicial_subdivision (SUC p) =
     frag_extend
      (\f. simplicial_cone p
            (\i. sum(0..SUC p) (\j. simplicial_vertex j f i) / (&p + &2))
            (simplicial_subdivision p (chain_boundary (SUC p) (frag_of f))))`;;

let SIMPLICIAL_SUBDIVISION_0 = prove
 (`!p. simplicial_subdivision p frag_0 = frag_0`,
  INDUCT_TAC THEN REWRITE_TAC[simplicial_subdivision; FRAG_EXTEND_0; I_THM]);;

let SIMPLICIAL_SUBDIVISION_SUB = prove
 (`!p c1 c2.
        simplicial_subdivision p (frag_sub c1 c2) =
        frag_sub (simplicial_subdivision p c1)
                 (simplicial_subdivision p c2)`,
  INDUCT_TAC THEN
  REWRITE_TAC[simplicial_subdivision; FRAG_EXTEND_SUB; I_THM]);;

let SIMPLICIAL_SUBDIVISION_OF = prove
 (`!p f. simplicial_subdivision p (frag_of f) =
         if p = 0 then frag_of f
         else simplicial_cone (p - 1)
               (\i. sum(0..p) (\j. simplicial_vertex j f i) / (&p + &1))
               (simplicial_subdivision (p - 1) (chain_boundary p (frag_of f)))`,
  INDUCT_TAC THEN REWRITE_TAC[simplicial_subdivision; I_THM] THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; ARITH_RULE `SUC p + 1 = p + 2`]);;

let SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION = prove
 (`!p s c. simplicial_chain (p,s) c
           ==> simplicial_chain (p,s) (simplicial_subdivision p c)`,
  MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [SIMP_TAC[simplicial_subdivision; I_THM]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN X_GEN_TAC `s:(num->real)->bool` THEN
  REWRITE_TAC[simplicial_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[SIMPLICIAL_SUBDIVISION_0; SIMPLICIAL_SUBDIVISION_SUB] THEN
  REWRITE_TAC[FRAG_SUPPORT_0; EMPTY_SUBSET; GSYM UNION_SUBSET] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[SUBSET; FRAG_SUPPORT_SUB]] THEN
  REWRITE_TAC[simplicial_subdivision; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[IN; GSYM simplicial_chain; ADD1] THEN
  X_GEN_TAC `f:(num->real)->(num->real)` THEN DISCH_TAC THEN
  MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_CONE THEN EXISTS_TAC
   `IMAGE (f:(num->real)->(num->real)) (standard_simplex(p + 1))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE `p = (p + 1) - 1`] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF] THEN POP_ASSUM MP_TAC THEN
    SIMP_TAC[SIMPLICIAL_SIMPLEX; SUBSET_REFL];
    GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `u:real` THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:num->real` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC o
      REWRITE_RULE[SIMPLICIAL_SIMPLEX]) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num->num->real` SUBST1_TAC) THEN
    SIMP_TAC[SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX] THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; oriented_simplex; RESTRICTION] THEN
    REWRITE_TAC[GSYM SUM_LMUL; real_div; GSYM SUM_RMUL; GSYM SUM_ADD_NUMSEG;
      REAL_ARITH `v * l * i + u * l * x:real = l * (v * i + u * x)`] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[SET_RULE
      `0..n = {x | x IN 0..n /\ x IN 0..n}`] THEN
    REWRITE_TAC[SUM_RESTRICT_SET; MESON[REAL_MUL_RZERO]
     `(if p then x * y else &0) = x * (if p then y else &0)`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `x IN standard_simplex (p + 1)` THEN
    REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
    SIMP_TAC[SUM_ADD_NUMSEG; SUM_LMUL; IN_NUMSEG; GSYM NOT_LT] THEN
    STRIP_TAC THEN REWRITE_TAC[CONJUNCT1 LT; SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; SUB_0] THEN
    CONJ_TAC THENL [X_GEN_TAC `k:num`; CONV_TAC REAL_FIELD] THEN
    REWRITE_TAC[NOT_LT] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_MUL; REAL_SUB_LE;
                 REAL_LE_INV_EQ; REAL_POS] THEN
    MATCH_MP_TAC REAL_CONVEX_BOUND_LE THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_ARITH `&1 - u + u = &1`] THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC]);;

let CHAIN_BOUNDARY_SIMPLICIAL_SUBDIVISION = prove
 (`!p s c. simplicial_chain (p,s) c
           ==> chain_boundary p (simplicial_subdivision p c) =
               simplicial_subdivision (p - 1) (chain_boundary p c)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REWRITE_TAC[chain_boundary; SIMPLICIAL_SUBDIVISION_0]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[simplicial_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[SIMPLICIAL_SUBDIVISION_0; SIMPLICIAL_SUBDIVISION_SUB;
              CHAIN_BOUNDARY_0; CHAIN_BOUNDARY_SUB] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC FRAG_MODULE] THEN
  X_GEN_TAC `f:(num->real)->(num->real)` THEN
  REWRITE_TAC[IN] THEN DISCH_TAC THEN
  REWRITE_TAC[simplicial_subdivision; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[ADD1; ADD_SUB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    CHAIN_BOUNDARY_SIMPLICIAL_CONE o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE `p = (p + 1) - 1`] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(FRAG_MODULE `y = frag_0 ==> frag_sub x y = x`) THENL
   [REWRITE_TAC[CHAIN_BOUNDARY_OF] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[simplicial_subdivision; I_THM] THEN
    SIMP_TAC[FRAG_EXTEND_SUM; FINITE_NUMSEG; o_DEF] THEN
    REWRITE_TAC[FRAG_EXTEND_CMUL; FRAG_EXTEND_OF] THEN
    CONV_TAC (LAND_CONV (LAND_CONV (RAND_CONV num_CONV))) THEN
    SIMP_TAC[MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_FRAG_ADD] THEN
    REWRITE_TAC[LE_0; INT_POW] THEN CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  FIRST_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) th o rand o lhand o snd)) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ARITH_RULE `p = (p + 1) - 1`] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[simplicial_cone; o_DEF] THEN MATCH_MP_TAC
   (MESON[FRAG_EXTEND_0] `c = frag_0 ==> frag_extend f c = frag_0`) THEN
  MATCH_MP_TAC(MESON[SIMPLICIAL_SUBDIVISION_0]
        `c = frag_0 ==> simplicial_subdivision q c = frag_0`) THEN
  MATCH_MP_TAC CHAIN_BOUNDARY_BOUNDARY_ALT THEN
  MATCH_MP_TAC(MESON[SIMPLICIAL_IMP_SINGULAR_CHAIN]
   `simplicial_chain (p,s) c ==> ?s. singular_chain(p,s) c`) THEN
  ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF]);;

let SIMPLICIAL_SUBDIVISION_SHRINKS = prove
 (`!s k p d c.
        simplicial_chain(p,s) c /\
        (!f x y. f IN frag_support c /\
                 x IN standard_simplex p /\ y IN standard_simplex p
                 ==> abs(f x k - f y k) <= d)
        ==> (!f x y. f IN frag_support(simplicial_subdivision p c) /\
                     x IN standard_simplex p /\ y IN standard_simplex p
                     ==> abs(f x k - f y k) <= &p / (&p + &1) * d)`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[simplicial_subdivision] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN
    SIMP_TAC[STANDARD_SIMPLEX_0; IN_SING; REAL_SUB_REFL] THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`d:real`; `c:((num->real)->(num->real))frag`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    DISCH_TAC] THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_FRAG_EXTEND o
    rand o lhand o snd o dest_forall o snd) THEN
  MATCH_MP_TAC(SET_RULE
   `t SUBSET P ==> s SUBSET t ==> (!x. x IN s ==> P x)`) THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplicial_chain]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `(!x. x IN s ==> P x)
    ==> (!x. t x /\ P x ==> Q x)
    ==> s SUBSET t ==> !x. x IN s ==> Q x`)) THEN
  X_GEN_TAC `f:(num->real)->(num->real)` THEN STRIP_TAC THEN
  REWRITE_TAC[simplicial_cone] THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_FRAG_EXTEND o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `g:(num->real)->(num->real)` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM; FRAG_SUPPORT_OF; SING_SUBSET] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d:real`;
    `chain_boundary (SUC p) (frag_of(f:(num->real)->(num->real)))`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
      MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
      ASM_REWRITE_TAC[SIMPLICIAL_CHAIN_OF];
      SUBGOAL_THEN
       `simplicial_chain (SUC p,IMAGE f (standard_simplex(SUC p))) (frag_of f)`
      MP_TAC THENL
       [REWRITE_TAC[SIMPLICIAL_CHAIN_OF] THEN
        ASM_MESON_TAC[SIMPLICIAL_SIMPLEX; SUBSET_REFL];
        DISCH_THEN(MP_TAC o MATCH_MP SIMPLICIAL_CHAIN_BOUNDARY) THEN
        REWRITE_TAC[SUC_SUB1; simplicial_chain; IMP_CONJ;
                    RIGHT_FORALL_IMP_THM] THEN
        MATCH_MP_TAC(SET_RULE
         `(!x. t x ==> P x) ==> s SUBSET t ==> !x. x IN s ==> P x`) THEN
        REWRITE_TAC[SIMPLICIAL_SIMPLEX] THEN ASM SET_TAC[]]];
     DISCH_THEN(MP_TAC o SPEC `g:(num->real)->(num->real)`) THEN
     ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= d` ASSUME_TAC THENL
   [ASM_MESON_TAC[NONEMPTY_STANDARD_SIMPLEX; MEMBER_NOT_EMPTY;
                  REAL_ARITH `abs x <= d ==> &0 <= d`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `simplicial_simplex (p,IMAGE f (standard_simplex(SUC p))) g`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `g IN s ==> s SUBSET P ==> P g`)) THEN
    REWRITE_TAC[GSYM simplicial_chain; ETA_AX] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF] THEN
    ASM_MESON_TAC[SIMPLICIAL_SIMPLEX; SUBSET_REFL];
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    MP_TAC(ASSUME `simplicial_simplex (SUC p,s) f`)] THEN
  REWRITE_TAC[SIMPLICIAL_SIMPLEX; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `l:num->num->real` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN DISCH_TAC THEN
  X_GEN_TAC `m:num->num->real` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  ONCE_REWRITE_TAC[IN] THEN EXPAND_TAC "g" THEN
  MAP_EVERY X_GEN_TAC [`x:num->real`; `y:num->real`] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN STRIP_TAC THEN
  EXPAND_TAC "f" THEN REWRITE_TAC[SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX] THEN
  SIMP_TAC[] THEN REWRITE_TAC[simplex_cone] THEN
  ASM_REWRITE_TAC[oriented_simplex; RESTRICTION; GSYM ADD1] THEN
  MATCH_MP_TAC REAL_CONVEX_SUM_BOUND_LE THEN
  ASM_REWRITE_TAC[ADD1; IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  MATCH_MP_TAC REAL_CONVEX_SUM_BOUND_LE THEN
  ASM_REWRITE_TAC[GSYM ADD1; IN_NUMSEG; LE_0] THEN
  UNDISCH_TAC `j:num <= p + 1` THEN SPEC_TAC(`j:num`,`j:num`) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[REAL_SUB_REFL] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_ADD; REAL_POS];
    REWRITE_TAC[ADD1; REAL_ABS_SUB; CONJ_ACI];
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`]] THEN
  DISCH_TAC THEN REWRITE_TAC[ADD1] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE `m < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i. i <= p ==> (m:num->num->real) i IN IMAGE g (standard_simplex p)`
  (LABEL_TAC "*") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(\j. if j = i then &1 else &0):num->real` THEN
    SIMP_TAC[BASIS_IN_STANDARD_SIMPLEX; oriented_simplex; RESTRICTION] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; ETA_AX; REAL_MUL_RID];
    ALL_TAC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REMOVE_THEN "*" (fun th ->
      MP_TAC(SPEC `n - 1` th) THEN MP_TAC(SPEC `m - 1` th)) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(n = 0) /\ n <= p + 1 ==> n - 1 <= p`] THEN
    REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&p / (&p + &1) * d` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < (&p + &1) + &1`] THEN
    REWRITE_TAC[REAL_ARITH `a / b * c:real = (a * c) / b`] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &p + &1`] THEN
    REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
   `(m:num->num->real) (n - 1) IN IMAGE f (standard_simplex (SUC p))`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[IN_IMAGE; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `z:num->real` THEN EXPAND_TAC "f" THEN
  SIMP_TAC[oriented_simplex; RESTRICTION] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  REWRITE_TAC[standard_simplex; IN_ELIM_THM; ADD1] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONVEX_SUM_BOUND_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(l:num->num->real) i k = sum(0..p+1) (\j. l i k) / (&p + &2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD] THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div; GSYM SUM_RMUL; GSYM SUM_SUB_NUMSEG]] THEN
  W(MP_TAC o PART_MATCH lhand SUM_ABS_NUMSEG o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  TRANS_TAC REAL_LE_TRANS
   `sum((0..p+1) DELETE i) (\j. abs(l i (k:num) - l j k) / (&p + &2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    REWRITE_TAC[real_div; GSYM REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[GSYM real_div; REAL_ABS_DIV] THEN
    REWRITE_TAC[REAL_ARITH `abs(&p + &2) = &p + &2`] THEN
    MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `x IN s /\ ~(x IN s DELETE a) ==> x = a`)) THEN
    SIMP_TAC[REAL_SUB_REFL; real_div; REAL_MUL_LZERO; REAL_ABS_NUM];
    MATCH_MP_TAC SUM_BOUND_GEN THEN SIMP_TAC[CARD_DELETE; FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[CARD_NUMSEG; GSYM REAL_OF_NUM_ADD;
                ARITH_RULE `(x + 1) - 0 - 1 = x`] THEN
    REWRITE_TAC[SET_RULE `s DELETE a = {} <=> s SUBSET {a}`] THEN
    REWRITE_TAC[GSYM NUMSEG_SING; SUBSET_NUMSEG] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN REWRITE_TAC[IN_DELETE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &p + &2`] THEN
    REWRITE_TAC[REAL_FIELD
    `(((&p + &1) * inv((&p + &1) + &1)) * d) / (&p + &1) * (&p + &2) = d`] THEN
    SUBGOAL_THEN
     `!r. r <= p + 1
          ==> (l:num->num->real) r IN IMAGE f (standard_simplex(SUC p))`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(\j. if j = r then &1 else &0):num->real` THEN
    REWRITE_TAC[RESTRICTION; BASIS_IN_STANDARD_SIMPLEX; oriented_simplex] THEN
    ASM_REWRITE_TAC[ADD1] THEN  REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; ETA_AX; REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* Now singular subdivision.                                                 *)
(* ------------------------------------------------------------------------- *)

let singular_subdivision = new_definition
 `singular_subdivision p =
        frag_extend
           (\f. chain_map p f
                  (simplicial_subdivision p
                         (frag_of(RESTRICTION (standard_simplex p) I))))`;;

let SINGULAR_SUBDIVISION_0 = prove
 (`!p. singular_subdivision p frag_0 = frag_0`,
  REWRITE_TAC[singular_subdivision; FRAG_EXTEND_0]);;

let SINGULAR_SUBDIVISION_SUB = prove
 (`!p c1 c2. singular_subdivision p (frag_sub c1 c2) =
             frag_sub (singular_subdivision p c1) (singular_subdivision p c2)`,
  REWRITE_TAC[singular_subdivision; FRAG_EXTEND_SUB]);;

let SINGULAR_SUBDIVISION_ADD = prove
 (`!p c1 c2. singular_subdivision p (frag_add c1 c2) =
             frag_add (singular_subdivision p c1) (singular_subdivision p c2)`,
  REWRITE_TAC[singular_subdivision; FRAG_EXTEND_ADD]);;

let SIMPLICIAL_SIMPLEX_I = prove
 (`!p s. simplicial_simplex (p,s) (RESTRICTION (standard_simplex p) I) <=>
         standard_simplex p SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_simplex; singular_simplex] THEN
  SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_SUBTOPOLOGY; INTER_UNIV;
           CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY; o_DEF;
           CARTESIAN_PRODUCT_UNIV; SUBSET_REFL; TOPSPACE_EUCLIDEANREAL] THEN
  SIMP_TAC[I_DEF; IMAGE_ID; CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
           REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
  SIMP_TAC[SUBSET; FORALL_IN_IMAGE; RESTRICTION] THEN
  MATCH_MP_TAC(TAUT `q ==> (p /\ q <=> p)`) THEN
  EXISTS_TAC `(\i j. if i = j then &1 else &0):num->num->real` THEN
  REWRITE_TAC[oriented_simplex; RESTRICTION_EXTENSION] THEN
  X_GEN_TAC `x:num->real` THEN REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  REWRITE_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO; REAL_MUL_LID] THEN
  SIMP_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN ASM_MESON_TAC[NOT_LT]);;

let SINGULAR_CHAIN_SINGULAR_SUBDIVISION = prove
 (`!p s c:((num->real)->A)frag.
        singular_chain (p,s) c
        ==> singular_chain (p,s) (singular_subdivision p c)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[singular_subdivision] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_EXTEND THEN
  X_GEN_TAC `f:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  MATCH_MP_TAC SINGULAR_CHAIN_CHAIN_MAP THEN
  EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                          (standard_simplex p)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_CHAIN THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [singular_chain]) THEN
    ASM_SIMP_TAC[SUBSET; IN; singular_simplex]]);;

let NATURALITY_SINGULAR_SUBDIVISION = prove
 (`!p s (g:A->B) c.
        singular_chain (p,s) c
        ==> singular_subdivision p (chain_map p g c) =
            chain_map p g (singular_subdivision p c)`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[singular_subdivision; FRAG_EXTEND_0; CHAIN_MAP_0] THEN
  REWRITE_TAC[FRAG_EXTEND_SUB; CHAIN_MAP_SUB] THEN
  REWRITE_TAC[GSYM singular_subdivision] THEN SIMP_TAC[] THEN
  X_GEN_TAC `f:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  REWRITE_TAC[singular_subdivision; CHAIN_MAP_OF; FRAG_EXTEND_OF] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN
  MP_TAC(ISPECL
    [`p:num`; `standard_simplex p:(num->real)->bool`;
     `frag_of (RESTRICTION (standard_simplex p:(num->real)->bool) I)`]
   SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION) THEN
  REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
  SPEC_TAC(`simplicial_subdivision p
             (frag_of (RESTRICTION (standard_simplex p:(num->real)->bool) I))`,
           `d:((num->real)->(num->real))frag`) THEN
  REWRITE_TAC[simplicial_chain; o_DEF] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[CHAIN_MAP_0; CHAIN_MAP_SUB; CHAIN_MAP_OF] THEN
  REWRITE_TAC[IN; SIMPLICIAL_SIMPLEX] THEN
  REWRITE_TAC[simplex_map; RESTRICTION_COMPOSE_RIGHT] THEN
  SIMP_TAC[RESTRICTION_COMPOSE_LEFT; SUBSET_REFL] THEN
  REWRITE_TAC[o_ASSOC]);;

let SIMPLICIAL_CHAIN_CHAIN_MAP = prove
 (`!p q s f c.
        simplicial_simplex (q,s) f /\
        simplicial_chain (p,standard_simplex q) c
        ==> simplicial_chain (p,s) (chain_map p f c)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[simplicial_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[GSYM simplicial_chain] THEN
  REWRITE_TAC[CHAIN_MAP_0; CHAIN_MAP_SUB; CHAIN_MAP_OF] THEN
  SIMP_TAC[SIMPLICIAL_CHAIN_0; SIMPLICIAL_CHAIN_SUB; SIMPLICIAL_CHAIN_OF] THEN
  X_GEN_TAC `g:(num->real)->(num->real)` THEN
  REWRITE_TAC[IN] THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[simplicial_simplex] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `l:num->num->real` THEN DISCH_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `m:num->num->real` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SINGULAR_SIMPLEX_SIMPLEX_MAP THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex q)` THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[oriented_simplex; simplex_map] THEN
    REWRITE_TAC[RESTRICTION_COMPOSE_RIGHT] THEN
    EXISTS_TAC `\(j:num) (k:num). sum (0..q) (\i. l i k * m j i)` THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `x:num->real` THEN REWRITE_TAC[RESTRICTION] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[o_DEF; RESTRICTION] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o
      REWRITE_RULE[singular_simplex])) THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; INTER_UNIV] THEN
    ASM_SIMP_TAC[oriented_simplex; RESTRICTION] THEN
    REPEAT(DISCH_THEN(K ALL_TAC)) THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
    REWRITE_TAC[REAL_MUL_ASSOC; SUM_RMUL]]);;

let SINGULAR_SUBDIVISION_SIMPLICIAL_SIMPLEX = prove
 (`!p s c. simplicial_chain (p,s) c
           ==> singular_subdivision p c = simplicial_subdivision p c`,
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REWRITE_TAC[singular_subdivision; simplicial_subdivision; I_THM] THEN
    X_GEN_TAC `s:(num->real)->bool` THEN
    REWRITE_TAC[simplicial_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
    SIMP_TAC[FRAG_EXTEND_0; FRAG_EXTEND_SUB; FRAG_EXTEND_OF] THEN
    REWRITE_TAC[IN] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SINGULAR_SIMPLEX_CHAIN_MAP_I THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLICIAL_IMP_SINGULAR_SIMPLEX) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:(num->real)->bool` THEN
  REWRITE_TAC[simplicial_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subdivision; singular_subdivision; FRAG_EXTEND_0];
    X_GEN_TAC `f:(num->real)->(num->real)` THEN REWRITE_TAC[IN] THEN DISCH_TAC;
    REWRITE_TAC[simplicial_subdivision; singular_subdivision] THEN
    SIMP_TAC[FRAG_EXTEND_SUB]] THEN
  REWRITE_TAC[singular_subdivision; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[SIMPLICIAL_SUBDIVISION_OF; NOT_SUC; SUC_SUB1] THEN
  MP_TAC(ISPECL [`s:(num->real)->bool`; `p:num`; `p + 1`; `p + 1`]
        CHAIN_MAP_SIMPLICIAL_CONE) THEN
  REWRITE_TAC[ADD1] THEN DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ASM_REWRITE_TAC[GSYM ADD1; LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
      MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
      REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
      REWRITE_TAC[simplicial_vertex; RESTRICTION; I_THM] THEN
      SIMP_TAC[BASIS_IN_STANDARD_SIMPLEX] THEN
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN
      SIMP_TAC[standard_simplex; IN_ELIM_THM; GSYM NOT_LE] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO; SUM_CONST_NUMSEG] THEN
      REWRITE_TAC[SUB_0; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_FIELD] THEN
      GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[RESTRICTION; simplicial_vertex; BASIS_IN_STANDARD_SIMPLEX] THEN
    SIMP_TAC[I_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    SIMP_TAC[SUM_DELTA] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[simplicial_simplex]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num->num->real` SUBST1_TAC) THEN
    REWRITE_TAC[oriented_simplex; RESTRICTION; BASIS_IN_STANDARD_SIMPLEX] THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_RID]
     `a * (if p then &1 else &0) = if p then a else &0`] THEN
    SIMP_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN
    SIMP_TAC[standard_simplex; IN_ELIM_THM; GSYM NOT_LE] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[SUB_0; GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUC] THEN
    COND_CASES_TAC THENL
     [REWRITE_TAC[GSYM SUM_RMUL] THEN
      ABS_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
      SIMP_TAC[REAL_MUL_LID];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT `~p ==> p ==> q`)) THEN
      CONJ_TAC THENL [ALL_TAC; CONV_TAC REAL_FIELD] THEN
      GEN_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLICIAL_IMP_SINGULAR_SIMPLEX) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_SIMPLEX_CHAIN_MAP_I) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`SUC p`; `standard_simplex (SUC p)`]
        SIMPLICIAL_SIMPLEX_I) THEN
  REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIMPLICIAL_IMP_SINGULAR_SIMPLEX) THEN
  REWRITE_TAC[GSYM SINGULAR_CHAIN_OF] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP CHAIN_BOUNDARY_CHAIN_MAP th]) THEN
  REWRITE_TAC[SUC_SUB1] THEN
  FIRST_ASSUM(MP_TAC o SPECL
   [`standard_simplex (SUC p)`;
    `chain_boundary (SUC p)
         (frag_of (RESTRICTION (standard_simplex (SUC p)) I))`]) THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`s:(num->real)->bool`;
    `chain_map p (f:(num->real)->(num->real))
       (chain_boundary (SUC p)
         (frag_of (RESTRICTION (standard_simplex (SUC p)) I)))`]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_CHAIN_CHAIN_MAP THEN
    EXISTS_TAC `SUC p` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NATURALITY_SINGULAR_SUBDIVISION THEN
  EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                          (standard_simplex (SUC p))` THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
  MATCH_MP_TAC SINGULAR_CHAIN_BOUNDARY THEN
  REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
  MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_SIMPLEX THEN
  REWRITE_TAC[SIMPLICIAL_SIMPLEX_I; SUBSET_REFL]);;

let NATURALITY_SIMPLICIAL_SUBDIVISION = prove
 (`!p q s g c.
        simplicial_chain(p,standard_simplex q) c /\
        simplicial_simplex (q,s) g
        ==> simplicial_subdivision p (chain_map p g c) =
            chain_map p g (simplicial_subdivision p c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o
    MATCH_MP SINGULAR_SUBDIVISION_SIMPLICIAL_SIMPLEX) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM
     (MATCH_MP NATURALITY_SINGULAR_SUBDIVISION
        (MATCH_MP SIMPLICIAL_IMP_SINGULAR_CHAIN th))]) THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SINGULAR_SUBDIVISION_SIMPLICIAL_SIMPLEX THEN
  EXISTS_TAC `s:(num->real)->bool` THEN
  MATCH_MP_TAC SIMPLICIAL_CHAIN_CHAIN_MAP THEN
  EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[]);;

let CHAIN_BOUNDARY_SINGULAR_SUBDIVISION = prove
 (`!p s c:((num->real)->A)frag.
        singular_chain (p,s) c
        ==> chain_boundary p (singular_subdivision p c) =
            singular_subdivision (p - 1) (chain_boundary p c)`,
  REPLICATE_TAC 2 GEN_TAC THEN  REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[singular_subdivision; FRAG_EXTEND_0; CHAIN_BOUNDARY_0] THEN
  REWRITE_TAC[FRAG_EXTEND_SUB; CHAIN_BOUNDARY_SUB; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[GSYM singular_subdivision] THEN SIMP_TAC[] THEN
  X_GEN_TAC `f:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num`;
                 `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex p)`;
                 `f:(num->real)->A`] CHAIN_BOUNDARY_CHAIN_MAP) THEN
  SIMP_TAC[SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION;
           SIMPLICIAL_IMP_SINGULAR_CHAIN; SIMPLICIAL_CHAIN_OF;
           SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPECL [`p:num`; `standard_simplex p:(num->real)->bool`]
        CHAIN_BOUNDARY_SIMPLICIAL_SUBDIVISION) THEN
  DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o rand o lhand o snd)) THEN
  REWRITE_TAC[SIMPLICIAL_CHAIN_OF;
           SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`p - 1`; `standard_simplex p`;
    `chain_boundary p (frag_of (RESTRICTION (standard_simplex p) I))`]
   SINGULAR_SUBDIVISION_SIMPLICIAL_SIMPLEX) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
    REWRITE_TAC[SIMPLICIAL_SIMPLEX_I; SIMPLICIAL_CHAIN_OF; SUBSET_REFL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL [`p - 1`;
                 `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex p)`;
                 `f:(num->real)->A`;
                 `chain_boundary p (frag_of
            (RESTRICTION (standard_simplex p) I))`]
          NATURALITY_SINGULAR_SUBDIVISION) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SINGULAR_CHAIN_BOUNDARY THEN
    REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
    MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_SIMPLEX THEN
    REWRITE_TAC[SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`p:num`;
                 `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex p)`;
                 `f:(num->real)->A`;
        `frag_of (RESTRICTION (standard_simplex p) I)`]
        CHAIN_BOUNDARY_CHAIN_MAP) THEN
  REWRITE_TAC[SINGULAR_CHAIN_OF] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_SIMPLEX THEN
    REWRITE_TAC[SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SINGULAR_SIMPLEX_CHAIN_MAP_I THEN
  ASM_MESON_TAC[]);;

let SINGULAR_SUBDIVISION_ZERO = prove
 (`!s c. singular_chain(0,s) c ==> singular_subdivision 0 c = c`,
  GEN_TAC THEN REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[singular_subdivision; FRAG_EXTEND_0; FRAG_EXTEND_SUB] THEN
  REWRITE_TAC[simplicial_subdivision; FRAG_EXTEND_OF] THEN
  REWRITE_TAC[I_THM; CHAIN_MAP_OF; simplex_map] THEN
  REWRITE_TAC[RESTRICTION_COMPOSE_RIGHT; I_O_ID] THEN
  REWRITE_TAC[IN; singular_simplex] THEN
  REWRITE_TAC[EXTENSIONAL; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN
  ASM_MESON_TAC[]);;

let CHAIN_HOMOTOPIC_SIMPLICIAL_SUBDIVISION = prove
 (`?h. (!p. h p frag_0 = frag_0) /\
       (!p c1 c2. h p (frag_sub c1 c2) = frag_sub (h p c1) (h p c2)) /\
       (!p q r g c.
                simplicial_chain (p,standard_simplex q) c /\
                simplicial_simplex (q,standard_simplex r) g
                ==> chain_map (p + 1) g (h p c) = h p (chain_map p g c)) /\
       (!p q c. simplicial_chain (p,standard_simplex q) c
                ==> simplicial_chain (p + 1,standard_simplex q) (h p c)) /\
       (!p q c. simplicial_chain (p,standard_simplex q) c
                ==> frag_add (chain_boundary (p + 1) (h p c))
                             (h (p - 1) (chain_boundary p c)) =
                    frag_sub (simplicial_subdivision p c) c)`,
  REPEAT STRIP_TAC THEN
  (STRIP_ASSUME_TAC o prove_recursive_functions_exist num_RECURSION)
   `h 0 = (\x. frag_0) /\
    !p. h(SUC p) =
          frag_extend
             (\f. simplicial_cone (SUC p)
                   (\i. sum (0..SUC p)
                        (\j. simplicial_vertex j f i) / (&(SUC p) + &1))
                   (frag_sub
                      (frag_sub (simplicial_subdivision (SUC p) (frag_of f))
                                (frag_of f))
                      (h p (chain_boundary (SUC p) (frag_of f)))))` THEN
  EXISTS_TAC
   `h:num->((num->real)->num->real)frag->((num->real)->num->real)frag` THEN
  GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC num_INDUCTION THEN
    ASM_REWRITE_TAC[FRAG_EXTEND_0; FRAG_EXTEND_SUB] THEN
    CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN X_GEN_TAC `s:num` THEN
  ONCE_REWRITE_TAC[MESON[] `(!r g c. P r c g) <=> (!c r g. P r c g)`] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[CONJUNCT1 simplicial_subdivision; I_THM; CHAIN_MAP_0] THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_0; CHAIN_BOUNDARY_0] THEN
    REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE;
    X_GEN_TAC `p:num`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_FORALL_THM; TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`;
    FORALL_AND_THM; IMP_IMP] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!p. (h:num->((num->real)->num->real)frag->((num->real)->num->real)frag)
        p frag_0 = frag_0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[FRAG_EXTEND_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p c1 c2.
      (h:num->((num->real)->num->real)frag->((num->real)->num->real)frag)
      p (frag_sub c1 c2) = frag_sub (h p c1) (h p c2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[FRAG_EXTEND_SUB] THEN
    CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  ABBREV_TAC `q = SUC p` THEN REWRITE_TAC[simplicial_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN REWRITE_TAC[GSYM simplicial_chain] THEN
  ASM_REWRITE_TAC[CHAIN_BOUNDARY_0; SIMPLICIAL_SUBDIVISION_0; CHAIN_MAP_0] THEN
  ASM_SIMP_TAC[CHAIN_BOUNDARY_SUB; SIMPLICIAL_SUBDIVISION_SUB;
               CHAIN_MAP_SUB] THEN
  REWRITE_TAC[SIMPLICIAL_CHAIN_0] THEN
  CONJ_TAC THENL [CONV_TAC FRAG_MODULE; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:(num->real)->(num->real)` THEN REWRITE_TAC[IN] THEN
    DISCH_TAC THEN
    UNDISCH_THEN `SUC p = q` (SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[SUC_SUB1; FRAG_EXTEND_OF];
    REWRITE_TAC[FRAG_MODULE `frag_add x y = z <=> x = frag_sub z y`] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIMPLICIAL_CHAIN_SUB] THENL
     [ASM_MESON_TAC[]; CONV_TAC FRAG_MODULE]] THEN
  SUBGOAL_THEN
   `(\i. sum (0..SUC p) (\j. simplicial_vertex j f i) / (&(SUC p) + &1))
    IN standard_simplex s`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `simplicial_simplex (SUC p,standard_simplex s) f`) THEN
    REWRITE_TAC[simplicial_simplex] THEN DISCH_THEN(X_CHOOSE_THEN
     `m:num->num->real` SUBST_ALL_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [SIMPLICIAL_SIMPLEX_ORIENTED_SIMPLEX]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o GEN `i:num` o
      SPEC `(\j. if j = i then &1 else &0):num->real`) THEN
    REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX; COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA; IN_NUMSEG; LE_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[ETA_AX; RESTRICTION; GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
    SPEC_TAC(`SUC p`,`n:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; REAL_ADD_LID; REAL_DIV_1] THEN
    ASM_SIMP_TAC[ETA_AX; LE_0; GSYM REAL_OF_NUM_SUC; REAL_FIELD
      `(a + b) / ((&n + &1) + &1) =
       (&1 - inv(&n + &2)) * ((a / (&n + &1))) + inv(&n + &2) * b`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_STANDARD_SIMPLEX THEN
    ASM_SIMP_TAC[ETA_AX; LE_REFL; REAL_LE_INV_EQ; REAL_INV_LE_1;
                 REAL_ARITH `&1 <= &n + &2 /\ &0 <= &n + &2`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `i <= n ==> i <= SUC n`];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`r:num`; `g:(num->real)->(num->real)`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL
     [`standard_simplex r`; `SUC p`; `s:num`; `s:num`]
       CHAIN_MAP_SIMPLICIAL_CONE) THEN
    DISCH_THEN(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
    ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
     [REPEAT(MATCH_MP_TAC SIMPLICIAL_CHAIN_SUB THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION;
                   SIMPLICIAL_CHAIN_OF] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [ARITH_RULE `p = (p + 1) - 1`] THEN
      MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
      ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[CHAIN_MAP_OF; FRAG_EXTEND_OF] THEN BINOP_TAC THENL
     [MP_TAC(ASSUME `simplicial_simplex (s,standard_simplex r) g`) THEN
      REWRITE_TAC[simplicial_simplex] THEN DISCH_THEN(X_CHOOSE_THEN
        `m:num->num->real` SUBST_ALL_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[oriented_simplex; RESTRICTION] THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[real_div; SUM_RMUL; REAL_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[GSYM oriented_simplex; GSYM SUM_LMUL] THEN
      GEN_REWRITE_TAC LAND_CONV [SUM_SWAP_NUMSEG] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN
      STRIP_TAC THEN REWRITE_TAC[] THEN
      MP_TAC(ASSUME
       `simplicial_simplex (SUC p,standard_simplex s) f`) THEN
      REWRITE_TAC[simplicial_simplex] THEN DISCH_THEN(X_CHOOSE_THEN
        `l:num->num->real` SUBST_ALL_TAC o CONJUNCT2) THEN
      MP_TAC(ISPECL
       [`SUC p`; `s:num`; `s:num`;
        `oriented_simplex s m`; `l:num->num->real`;
        `standard_simplex r`] SIMPLEX_MAP_ORIENTED_SIMPLEX) THEN
      ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[SIMPLICIAL_VERTEX_ORIENTED_SIMPLEX] THEN
      MP_TAC(ASSUME
       `simplicial_simplex (SUC p,standard_simplex s)
                           (oriented_simplex (SUC p) l)`) THEN
      REWRITE_TAC[SIMPLICIAL_SIMPLEX_ORIENTED_SIMPLEX; SUBSET] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `(\i. if i = m then &1 else &0):num->real`) THEN
      ASM_REWRITE_TAC[BASIS_IN_STANDARD_SIMPLEX; COND_RAND] THEN
      SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA; REAL_MUL_RID] THEN
      ASM_REWRITE_TAC[IN_NUMSEG; oriented_simplex; o_THM; RESTRICTION] THEN
      SIMP_TAC[ETA_AX];
      REWRITE_TAC[CHAIN_MAP_SUB] THEN
      REPEAT BINOP_TAC THEN REWRITE_TAC[CHAIN_MAP_OF] THENL
       [REWRITE_TAC[GSYM CHAIN_MAP_OF] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC NATURALITY_SIMPLICIAL_SUBDIVISION THEN
        REWRITE_TAC[SIMPLICIAL_CHAIN_OF] THEN ASM_MESON_TAC[];
        REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o
           GEN_REWRITE_RULE I [SWAP_FORALL_THM]) THEN
        DISCH_THEN(fun th ->
          W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
           [ARITH_RULE `p = (p + 1) - 1`] THEN
          MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
          ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF];
          DISCH_THEN SUBST1_TAC] THEN
        AP_TERM_TAC THEN
        REWRITE_TAC[GSYM CHAIN_MAP_OF] THEN CONV_TAC SYM_CONV THEN
        GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o LAND_CONV)
         [ARITH_RULE `p = (p + 1) - 1`] THEN
        MATCH_MP_TAC CHAIN_BOUNDARY_CHAIN_MAP THEN
        REWRITE_TAC[GSYM ADD1; SINGULAR_CHAIN_OF] THEN
        ASM_MESON_TAC[SIMPLICIAL_IMP_SINGULAR_SIMPLEX]]];
    MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_CONE THEN
    EXISTS_TAC `standard_simplex s` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC SIMPLICIAL_CHAIN_SUB THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION;
                   SIMPLICIAL_CHAIN_OF] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [ARITH_RULE `p = (p + 1) - 1`] THEN
      MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
      ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_STANDARD_SIMPLEX THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`SUC p`; `standard_simplex s`]
      CHAIN_BOUNDARY_SIMPLICIAL_CONE) THEN
    DISCH_THEN(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o lhand o snd)) THEN
    ASM_REWRITE_TAC[NOT_SUC] THEN ANTS_TAC THENL
     [REPEAT(MATCH_MP_TAC SIMPLICIAL_CHAIN_SUB THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION;
                   SIMPLICIAL_CHAIN_OF] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
       [ARITH_RULE `p = (p + 1) - 1`] THEN
      MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
      ASM_REWRITE_TAC[GSYM ADD1; SIMPLICIAL_CHAIN_OF];
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(FRAG_MODULE
      `z = frag_0
       ==> frag_add (frag_sub (frag_sub (frag_sub ff f) t) z) t =
           frag_sub ff f`) THEN
    REWRITE_TAC[simplicial_cone] THEN MATCH_MP_TAC(MESON[FRAG_EXTEND_0]
     `z = frag_0 ==> frag_extend f z = frag_0`) THEN
    REWRITE_TAC[CHAIN_BOUNDARY_SUB] THEN
    FIRST_ASSUM(MP_TAC o
     SPEC `chain_boundary (SUC p) (frag_of(f:(num->real)->(num->real)))`) THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM SUC_SUB1] THEN
      MATCH_MP_TAC SIMPLICIAL_CHAIN_BOUNDARY THEN
      ASM_REWRITE_TAC[SIMPLICIAL_CHAIN_OF];
      REWRITE_TAC[ADD1]] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (FRAG_MODULE
     `frag_add w z = x ==> w = frag_sub x z`)) THEN
    REWRITE_TAC[CHAIN_BOUNDARY_SUB] THEN
    MP_TAC(ISPECL [`p + 1`;
                   `subtopology (product_topology (:num) (\i. euclideanreal))
                                (standard_simplex s)`;
                   `frag_of(f:(num->real)->(num->real))`]
      CHAIN_BOUNDARY_BOUNDARY) THEN
    ASM_SIMP_TAC[SIMPLICIAL_IMP_SINGULAR_CHAIN; SIMPLICIAL_CHAIN_OF;
                 GSYM ADD1; SUC_SUB1] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`SUC p`; `standard_simplex s`;
                   `frag_of(f:(num->real)->(num->real))`]
          CHAIN_BOUNDARY_SIMPLICIAL_SUBDIVISION) THEN
    ASM_REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SUC_SUB1] THEN
    CONV_TAC FRAG_MODULE]);;

let CHAIN_HOMOTOPIC_SINGULAR_SUBDIVISION = prove
 (`?h:num->((num->real)->A)frag->((num->real)->A)frag.
        (!p. h p frag_0 = frag_0) /\
        (!p c1 c2. h p (frag_sub c1 c2) = frag_sub (h p c1) (h p c2)) /\
        (!p top c. singular_chain (p,top) c
                   ==> singular_chain (p + 1,top) (h p c)) /\
        (!p top c. singular_chain (p,top) c
                   ==> frag_add (chain_boundary (p + 1) (h p c))
                                (h (p - 1) (chain_boundary p c)) =
                       frag_sub (singular_subdivision p c) c)`,
  X_CHOOSE_THEN
   `h:num->((num->real)->(num->real))frag->((num->real)->(num->real))frag`
   STRIP_ASSUME_TAC CHAIN_HOMOTOPIC_SIMPLICIAL_SUBDIVISION THEN
  ABBREV_TAC
   `k:num->((num->real)->A)frag->((num->real)->A)frag =
        \p. frag_extend
              (\f. chain_map (p + 1) (f:(num->real)->A)
               (h p (frag_of(RESTRICTION (standard_simplex p)
                      (I:(num->real)->(num->real))))))` THEN
  EXISTS_TAC `k:num->((num->real)->A)frag->((num->real)->A)frag` THEN
  SUBGOAL_THEN
   `!p. (k:num->((num->real)->A)frag->((num->real)->A)frag) p frag_0 = frag_0`
  ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[FRAG_EXTEND_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p c1 c2. (k:num->((num->real)->A)frag->((num->real)->A)frag) p
                (frag_sub c1 c2) = frag_sub (k p c1) (k p c2)`
  ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REWRITE_TAC[FRAG_EXTEND_SUB];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[AND_FORALL_THM; TAUT
   `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `s:A topology`] THEN
  REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN
  ASM_REWRITE_TAC[GSYM singular_chain] THEN
  ASM_SIMP_TAC[CHAIN_BOUNDARY_0; SINGULAR_CHAIN_0; CHAIN_BOUNDARY_SUB;
               singular_subdivision; FRAG_EXTEND_0; FRAG_EXTEND_SUB] THEN
  REWRITE_TAC[GSYM singular_subdivision] THEN SIMP_TAC[SINGULAR_CHAIN_SUB] THEN
  CONJ_TAC THENL [CONV_TAC FRAG_MODULE; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:(num->real)->A` THEN REWRITE_TAC[IN] THEN DISCH_TAC;
    REWRITE_TAC[FRAG_MODULE `frag_add x y = z <=> x = frag_sub z y`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC FRAG_MODULE] THEN
  EXPAND_TAC "k" THEN REWRITE_TAC[FRAG_EXTEND_OF; ADD_SUB] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SINGULAR_CHAIN_CHAIN_MAP THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex p)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_CHAIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`p + 1`;
                 `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex p)`;
                 `f:(num->real)->A`]
        CHAIN_BOUNDARY_CHAIN_MAP) THEN
  DISCH_THEN(fun th ->
   W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o lhand o snd)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_CHAIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ADD_SUB] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE
   (funpow 3 BINDER_CONV o RAND_CONV)
   [FRAG_MODULE `frag_add x y = z <=> x = frag_sub z y`]) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`p:num`; `p:num`;
     `frag_of(RESTRICTION (standard_simplex p) I)`]) THEN
  REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FRAG_MODULE `frag_add x y = z <=> x = frag_sub z y`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CHAIN_MAP_SUB; CHAIN_MAP_OF] THEN
  MATCH_MP_TAC(FRAG_MODULE
   `b = y /\ frag_sub a c = frag_sub x z
    ==> frag_sub (frag_sub a b) c = frag_sub (frag_sub x y) z`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM CHAIN_MAP_OF] THEN
    MATCH_MP_TAC SINGULAR_SIMPLEX_CHAIN_MAP_I THEN ASM_MESON_TAC[];
    REWRITE_TAC[GSYM CHAIN_MAP_SUB; singular_subdivision]] THEN
  REWRITE_TAC[FRAG_EXTEND_OF; CHAIN_MAP_SUB] THEN AP_TERM_TAC THEN
  REWRITE_TAC[chain_boundary] THEN
  ASM_REWRITE_TAC[CHAIN_MAP_0; FRAG_EXTEND_0] THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[FRAG_EXTEND_0; CHAIN_MAP_0] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; FRAG_EXTEND_OF] THEN
  SIMP_TAC[FRAG_EXTEND_SUM; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF; FRAG_EXTEND_CMUL; FRAG_EXTEND_OF] THEN
  TRANS_TAC EQ_TRANS
    `chain_map p (f:(num->real)->A)
      (iterate frag_add (0..p)
       (\k. frag_cmul (-- &1 pow k)
              (chain_map p (singular_face p k I)
               ((h:num->((num->real)->(num->real))frag
                   ->((num->real)->(num->real))frag) (p - 1)
                (frag_of (RESTRICTION (standard_simplex (p - 1)) I))))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `!k z. FINITE k
            ==> (h:num->((num->real)->(num->real))frag
                     ->((num->real)->(num->real))frag) (p - 1)
                (iterate frag_add (k:num->bool) z) =
                iterate frag_add k (h (p - 1) o z)`
     (fun th -> SIMP_TAC[th; FINITE_NUMSEG])
    THENL
     [GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN GEN_TAC THEN
      MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
      SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
      ASM_REWRITE_TAC[NEUTRAL_FRAG_ADD; o_DEF] THEN
      ASM_SIMP_TAC[FRAG_MODULE
       `frag_add x y = frag_sub x (frag_sub frag_0 y)`];
      ALL_TAC] THEN
    MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG; o_DEF] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!k c. (h:num->((num->real)->(num->real))frag
                 ->((num->real)->(num->real))frag) (p - 1)
            (frag_cmul (-- &1 pow k) c) =
            frag_cmul (-- &1 pow k) (h (p - 1) c)`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[INT_POW_NEG; INT_POW_ONE] THEN
      COND_CASES_TAC THEN REWRITE_TAC[FRAG_MODULE `frag_cmul (&1) c = c`] THEN
      ASM_REWRITE_TAC[FRAG_MODULE
       `frag_cmul (-- &1) c = frag_sub frag_0 c`];
      AP_TERM_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`p - 1`; `p - 1`; `p:num`;
      `singular_face p k (RESTRICTION (standard_simplex p) I)`;
      `frag_of(RESTRICTION
        (standard_simplex (p - 1)) (I:(num->real)->(num->real)))`]) THEN
    ASM_REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I] THEN
    REWRITE_TAC[SUBSET_REFL] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SIMPLICIAL_SIMPLEX_SINGULAR_FACE THEN
      ASM_SIMP_TAC[LE_1; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
      MATCH_MP_TAC(MESON[] `x = y' /\ y = x' ==> x = y ==> x' = y'`) THEN
      REWRITE_TAC[CHAIN_MAP_OF] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[LE_1; SUB_ADD];
        ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
        AP_TERM_TAC THEN REWRITE_TAC[CHAIN_MAP_OF] THEN AP_TERM_TAC THEN
        REWRITE_TAC[singular_face; simplex_map; RESTRICTION; FUN_EQ_THM;
                    o_THM; I_THM] THEN
        ASM_SIMP_TAC[LE_1; FACE_MAP_IN_STANDARD_SIMPLEX]]];
    SIMP_TAC[CHAIN_MAP_SUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[o_DEF; CHAIN_MAP_CMUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] (GSYM CHAIN_MAP_COMPOSE)] THEN
    ASM_REWRITE_TAC[singular_face; I_O_ID]] THEN
 (SUBGOAL_THEN
   `simplicial_chain((p-1)+1,standard_simplex(p - 1))
       ((h:num->((num->real)->(num->real))frag
           ->((num->real)->(num->real))frag) (p - 1)
            (frag_of (RESTRICTION (standard_simplex (p - 1)) I)))`
  MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL];
    ASM_SIMP_TAC[SUB_ADD; LE_1]] THEN
  SPEC_TAC(`(h:num->((num->real)->(num->real))frag
                     ->((num->real)->(num->real))frag) (p - 1)
            (frag_of (RESTRICTION (standard_simplex (p - 1)) I))`,
           `c:((num->real)->(num->real))frag`) THEN
  REWRITE_TAC[simplicial_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
  SIMP_TAC[CHAIN_MAP_0; CHAIN_MAP_SUB] THEN
  X_GEN_TAC `f:(num->real)->(num->real)` THEN REWRITE_TAC[IN] THEN
  REWRITE_TAC[CHAIN_MAP_OF; singular_simplex; simplicial_simplex] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
              TOPSPACE_PRODUCT_TOPOLOGY; TOPSPACE_SUBTOPOLOGY; INTER_UNIV;
              TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV; o_DEF] THEN
  STRIP_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; simplex_map] THEN
  ASM_SIMP_TAC[singular_face; I_THM; o_THM; RESTRICTION;
               FACE_MAP_IN_STANDARD_SIMPLEX; LE_1]));;

let HOMOLOGOUS_REL_SINGULAR_SUBDIVISION = prove
 (`!p s t c:((num->real)->A)frag.
        singular_relcycle (p,s,t) c
        ==> homologous_rel (p,s,t) (singular_subdivision p c) c`,
  REPLICATE_TAC 3 GEN_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [ASM_MESON_TAC[singular_relcycle; SINGULAR_SUBDIVISION_ZERO;
                  HOMOLOGOUS_REL_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC CHAIN_HOMOTOPIC_IMP_HOMOLOGOUS_REL THEN
  X_CHOOSE_THEN
   `k:num->((num->real)->A)frag->((num->real)->A)frag`
   STRIP_ASSUME_TAC CHAIN_HOMOTOPIC_SINGULAR_SUBDIVISION THEN
  EXISTS_TAC `(k:num->((num->real)->A)frag->((num->real)->A)frag) p` THEN
  EXISTS_TAC `(k:num->((num->real)->A)frag->((num->real)->A)frag) (p - 1)` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUB_ADD; LE_1]);;

(* ------------------------------------------------------------------------- *)
(* Excision argument that we keep doing singular subdivision                 *)
(* ------------------------------------------------------------------------- *)

let ITERATED_SINGULAR_SUBDIVISION = prove
 (`!p s n c.
        singular_chain(p,s) c
        ==> ITER n (singular_subdivision p) c =
            frag_extend
             (\f:(num->real)->A.
                  chain_map p f
                       (ITER n (simplicial_subdivision p)
                         (frag_of(RESTRICTION (standard_simplex p) I)))) c`,
  GEN_TAC THEN GEN_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[ITER] THEN CONJ_TAC THENL
   [ALL_TAC; X_GEN_TAC `n:num` THEN DISCH_TAC] THEN
  REWRITE_TAC[singular_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
  REWRITE_TAC[GSYM singular_chain] THENL
   [SIMP_TAC[FRAG_EXTEND_0; FRAG_EXTEND_SUB; FRAG_EXTEND_OF] THEN
    REWRITE_TAC[IN; SINGULAR_SIMPLEX_CHAIN_MAP_I];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[singular_subdivision; FRAG_EXTEND_0] THEN
    MATCH_MP_TAC(MESON[FRAG_EXTEND_0]
     `c = frag_0 ==> frag_0 = frag_extend f c`) THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; FRAG_EXTEND_0];
    ALL_TAC;
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[FRAG_EXTEND_SUB] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC num_INDUCTION THEN
    SIMP_TAC[ITER; singular_subdivision; GSYM FRAG_EXTEND_SUB]] THEN
  X_GEN_TAC `f:(num->real)->A` THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  DISCH_TAC THEN REWRITE_TAC[FRAG_EXTEND_OF] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `frag_of(f:(num->real)->A)`) THEN
  ASM_REWRITE_TAC[SINGULAR_CHAIN_OF; FRAG_EXTEND_OF] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`p:num`;
                `subtopology (product_topology (:num) (\i. euclideanreal))
                              (standard_simplex p)`;
                 `f:(num->real)->A`] NATURALITY_SINGULAR_SUBDIVISION) THEN
  DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o rand o snd)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SIMPLICIAL_IMP_SINGULAR_CHAIN THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
    ASM_SIMP_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
    MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SINGULAR_SUBDIVISION_SIMPLICIAL_SIMPLEX THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `standard_simplex p` THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  SIMP_TAC[ITER; SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
  MATCH_MP_TAC SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION THEN
  ASM_REWRITE_TAC[]);;

let CHAIN_HOMOTOPIC_ITERATED_SINGULAR_SUBDIVISION = prove
 (`!n. ?h:num->((num->real)->A)frag->((num->real)->A)frag.
        (!p. h p frag_0 = frag_0) /\
        (!p c1 c2. h p (frag_sub c1 c2) = frag_sub (h p c1) (h p c2)) /\
        (!p top c. singular_chain (p,top) c
                   ==> singular_chain (p + 1,top) (h p c)) /\
        (!p top c. singular_chain (p,top) c
                   ==> frag_add (chain_boundary (p + 1) (h p c))
                                (h (p - 1) (chain_boundary p c)) =
                       frag_sub (ITER n (singular_subdivision p) c) c)`,
  INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
   [EXISTS_TAC
     `(\p x. frag_0):num->((num->real)->A)frag->((num->real)->A)frag` THEN
    REWRITE_TAC[SINGULAR_CHAIN_0; CHAIN_BOUNDARY_0] THEN
    REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN
   `k:num->((num->real)->A)frag->((num->real)->A)frag`
   STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN
   `h:num->((num->real)->A)frag->((num->real)->A)frag`
   STRIP_ASSUME_TAC
   CHAIN_HOMOTOPIC_SINGULAR_SUBDIVISION THEN
  EXISTS_TAC
   `(\p c. frag_add (singular_subdivision (p + 1) (k p c)) (h p c))
    :num->((num->real)->A)frag->((num->real)->A)frag` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SINGULAR_SUBDIVISION_0] THEN
    REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SINGULAR_SUBDIVISION_SUB] THEN
    REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`p:num`; `top:A topology`; `c:((num->real)->A)frag`] THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_ADD; SINGULAR_CHAIN_SINGULAR_SUBDIVISION] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[FRAG_MODULE
   `frag_sub (singular_subdivision p (ITER n (singular_subdivision p) c)) c =
    frag_add
     (frag_sub (singular_subdivision p (ITER n (singular_subdivision p) c))
               (singular_subdivision p c))
     (frag_sub (singular_subdivision p c) c)`] THEN
  FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (rand o rand) th o rand o rand o snd)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SINGULAR_SUBDIVISION_SUB] THEN
  FIRST_X_ASSUM(fun th ->
   W(MP_TAC o PART_MATCH (rand o rand) th o rand o lhand o rand o snd)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `singular_subdivision (p - 1 + 1) (k (p - 1) (chain_boundary p c)) =
    singular_subdivision p
      ((k:num->((num->real)->A)frag->((num->real)->A)frag) (p - 1)
      (chain_boundary p c))`
  SUBST1_TAC THENL
   [ASM_CASES_TAC `p = 0` THEN ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_REWRITE_TAC[chain_boundary; SINGULAR_SUBDIVISION_0];
    ALL_TAC] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_ADD; SINGULAR_SUBDIVISION_ADD] THEN
  MP_TAC(ISPECL [`p + 1`; `top:A topology`]
    CHAIN_BOUNDARY_SINGULAR_SUBDIVISION) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN
  REPEAT STRIP_TAC THEN CONV_TAC FRAG_MODULE);;

let SUFFICIENT_ITERATED_SINGULAR_SUBDIVISION_EXISTS = prove
 (`!p top u c:((num->real)->A)frag.
        (!v. v IN u ==> open_in top v) /\
        topspace top SUBSET UNIONS u /\
        singular_chain (p,top) c
        ==> ?n. !m f. n <= m /\
                      f IN frag_support (ITER m (singular_subdivision p) c)
                      ==> ?v. v IN u /\ IMAGE f (standard_simplex p) SUBSET v`,
  let llemma = prove
   (`!p c. standard_simplex p SUBSET UNIONS c /\
           (!u. u IN c
                ==> open_in (product_topology (:num) (\i. euclideanreal)) u)
           ==> ?d. &0 < d /\
                   !k. k SUBSET standard_simplex p /\
                       (!x y i.
                          x IN k /\ y IN k /\ i <= p ==> abs (x i - y i) <= d)
                       ==> ?u. u IN c /\ k SUBSET u`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!x. x IN standard_simplex p
          ==> ?e u. &0 < e /\ u IN c /\ x IN u /\
                    !y. (!i. i <= p ==> abs(y i - x i) <= &2 * e) /\
                        (!i. p < i ==> y i = &0)
                        ==> y IN u`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:num->real` o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `u:(num->real)->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:(num->real)->bool`) THEN
      ASM_REWRITE_TAC[OPEN_IN_PRODUCT_TOPOLOGY_ALT] THEN
      DISCH_THEN(MP_TAC o SPEC `x:num->real`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; cartesian_product; IN_UNIV] THEN
      REWRITE_TAC[EXTENSIONAL_UNIV; IN_ELIM_THM] THEN
      X_GEN_TAC `v:num->(real->bool)` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE BINDER_CONV [GSYM REAL_OPEN_IN]) THEN
      REWRITE_TAC[real_open] THEN
      DISCH_THEN(MP_TAC o GEN `i:num` o SPECL [`i:num`; `(x:num->real) i`]) THEN
      ASM_REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      X_GEN_TAC `d:num->real` THEN STRIP_TAC THEN EXISTS_TAC
       `inf ((&1) INSERT IMAGE (d:num->real) {i | ~(v i = (:real))}) / &3` THEN
      REWRITE_TAC[REAL_ARITH `&0 < x / &3 <=> &0 < x`] THEN
      REWRITE_TAC[REAL_ARITH `x <= &2 * y / &3 <=> &3 / &2 * x <= y`] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; REAL_LE_INF_FINITE; NOT_INSERT_EMPTY;
                   FINITE_IMAGE; FINITE_INSERT] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; FORALL_IN_INSERT; REAL_LT_01] THEN
      X_GEN_TAC `y:num->real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      MP_TAC(ASSUME `x IN standard_simplex p`) THEN
      REWRITE_TAC[IN_ELIM_THM; standard_simplex] THEN STRIP_TAC THEN
      X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `p:num < i` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
      ASM_CASES_TAC `(v:num->real->bool) i = UNIV` THEN
      ASM_REWRITE_TAC[IN_UNIV] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&3 / &2 * x <= y /\ &0 < y ==> x < y`) THEN
      ASM_SIMP_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`e:(num->real)->real`; `v:(num->real)->(num->real)->bool`] THEN
    DISCH_TAC THEN MP_TAC(SPEC `p:num` COMPACT_IN_STANDARD_SIMPLEX) THEN
    REWRITE_TAC[compact_in] THEN DISCH_THEN(MP_TAC o
      SPEC `{cartesian_product (:num)
              (\i. if i <= p then real_interval(x i - e x,x i + e x)
                   else (:real)) | x | x IN standard_simplex p}` o
      CONJUNCT2) THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; EXISTS_FINITE_SUBSET_IMAGE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN
      CONJ_TAC THEN X_GEN_TAC `x:num->real` THEN DISCH_TAC THENL
       [REWRITE_TAC[OPEN_IN_CARTESIAN_PRODUCT_GEN] THEN DISJ2_TAC THEN
        REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; IN_UNIV] THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i <= p}` THEN
          REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
          GEN_TAC THEN REWRITE_TAC[GSYM REAL_OPEN_IN] THEN
          MESON_TAC[REAL_OPEN_REAL_INTERVAL; REAL_OPEN_UNIV]];
        EXISTS_TAC `x:num->real` THEN
        ASM_REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL_UNIV] THEN
        GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[IN_UNIV] THEN
        ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_ARITH
         `x - e < x /\ x < x + e <=> &0 < e`]];
      DISCH_THEN(X_CHOOSE_THEN `s:(num->real)->bool` MP_TAC)] THEN
    ASM_CASES_TAC `s:(num->real)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUBSET_EMPTY] THEN
    REWRITE_TAC[NONEMPTY_STANDARD_SIMPLEX] THEN STRIP_TAC THEN
    EXISTS_TAC `inf(IMAGE (e:(num->real)->real) s)` THEN
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; REAL_LE_INF_FINITE;
                 FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `k:(num->real)->bool` THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN STRIP_TAC THEN
    ASM_CASES_TAC `k:(num->real)->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
      ASM_MESON_TAC[MEMBER_NOT_EMPTY; NONEMPTY_STANDARD_SIMPLEX];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY])] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x IN standard_simplex p` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_IMAGE]) THEN
    GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `x:num->real`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; cartesian_product; EXTENSIONAL_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num->real`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IN_UNIV] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[COND_EXPAND; FORALL_AND_THM; IN_UNIV] THEN
    REWRITE_TAC[TAUT `~p \/ q <=> p ==> q`; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_ARITH `a - e < x /\ x < a + e <=> abs(x - a) < e`] THEN
    DISCH_TAC THEN EXISTS_TAC `(v:(num->real)->(num->real)->bool) a` THEN
    SUBGOAL_THEN `a IN standard_simplex p` (fun th -> ASSUME_TAC th THEN
      FIRST_X_ASSUM(MP_TAC o C MATCH_MP th))
    THENL [ASM SET_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:num->real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `y IN standard_simplex p`
     (fun th -> ASSUME_TAC th THEN MP_TAC th)
    THENL [ASM SET_TAC[]; SIMP_TAC[standard_simplex; IN_ELIM_THM]] THEN
    DISCH_THEN(K ALL_TAC) THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:num->real`; `y:num->real`; `i:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `a:num->real`) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c:((num->real)->A)frag = frag_0` THENL
   [STRIP_TAC THEN EXISTS_TAC `0` THEN
    SUBGOAL_THEN
     `!k. ITER k (singular_subdivision p) frag_0:((num->real)->A)frag =
          frag_0`
     (fun th -> ASM_REWRITE_TAC[th; FRAG_SUPPORT_0; NOT_IN_EMPTY]) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; SINGULAR_SUBDIVISION_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `topspace top:A->bool = {}` THENL
   [ASM_MESON_TAC[SINGULAR_CHAIN_EMPTY]; ALL_TAC] THEN
  ASM_CASES_TAC `u:(A->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; SUBSET_EMPTY] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !f k. f IN frag_support c /\ k SUBSET standard_simplex p /\
             (!x y i. x IN k /\ y IN k /\ i <= p ==> abs(x i - y i) <= d)
             ==> ?v. v IN u /\ IMAGE (f:(num->real)->A) k SUBSET v`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!f:(num->real)->A.
          f IN frag_support c
          ==> ?e. &0 < e /\
                  !k. k SUBSET standard_simplex p /\
                      (!x y i. x IN k /\ y IN k /\ i <= p
                               ==> abs(x i - y i) <= e)
                      ==> ?v. v IN u /\ IMAGE f k SUBSET v`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `!v. v IN u
            ==> ?t. open_in (product_topology (:num) (\i. euclideanreal)) t /\
                    {x | x IN standard_simplex p /\ (f:(num->real)->A) x IN v}
                    = t INTER standard_simplex p`
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM OPEN_IN_SUBTOPOLOGY] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [singular_chain]) THEN
        REWRITE_TAC[SUBSET] THEN
        DISCH_THEN(MP_TAC o SPEC `f:(num->real)->A`) THEN
        ASM_REWRITE_TAC[singular_simplex; IN; continuous_map] THEN
        DISCH_THEN(MP_TAC o SPEC `v:A->bool` o CONJUNCT2 o CONJUNCT1) THEN
        REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
        REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
        ASM_SIMP_TAC[INTER_UNIV];
        GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM]] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `g:(A->bool)->((num->real)->bool)` THEN DISCH_TAC THEN
      MP_TAC(SPECL
       [`p:num`; `IMAGE (g:(A->bool)->((num->real)->bool)) u`]
        llemma) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
      ASM_SIMP_TAC[UNIONS_IMAGE] THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [singular_chain]) THEN
       REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `f:(num->real)->A`) THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
      REWRITE_TAC[singular_simplex] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE o
                 CONJUNCT1) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
      REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
      REWRITE_TAC[INTER_UNIV] THEN DISCH_TAC THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:(num->real)->bool` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `e:((num->real)->A)->real` THEN DISCH_TAC THEN
      EXISTS_TAC `inf {e f | (f:(num->real)->A) IN frag_support c}` THEN
      REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[REAL_LT_INF_FINITE; FINITE_FRAG_SUPPORT;
                   FRAG_SUPPORT_EQ_EMPTY; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                   REAL_LE_INF_FINITE] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&p / (&p + &1)`; `d:real`] REAL_ARCH_POW_INV) THEN
  SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_POS;
           REAL_ARITH `&0 <= x ==> &0 < x + &1`; REAL_ABS_POS] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  ABBREV_TAC `c':((num->real)->A)frag = ITER m (singular_subdivision p) c` THEN
  MP_TAC(ISPECL
   [`p:num`; `top:A topology`; `m:num`;
    `c:((num->real)->A)frag`] ITERATED_SINGULAR_SUBDIVISION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_FRAG_EXTEND o
    rand o lhand o snd o dest_forall o snd) THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> P x) ==> top SUBSET s ==> (!x. x IN top ==> P x)`) THEN
  REWRITE_TAC[FORALL_IN_UNIONS] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `f:(num->real)->A` THEN DISCH_TAC THEN
  REWRITE_TAC[chain_map] THEN
  W(MP_TAC o PART_MATCH lhand FRAG_SUPPORT_FRAG_EXTEND o
    rand o lhand o snd o dest_forall o snd) THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> P x) ==> top SUBSET s ==> (!x. x IN top ==> P x)`) THEN
  REWRITE_TAC[FORALL_IN_UNIONS] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[FRAG_SUPPORT_OF; o_THM; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  SIMP_TAC[simplex_map; IMAGE_RESTRICTION; SUBSET_REFL] THEN
  X_GEN_TAC `d:(num->real)->(num->real)` THEN DISCH_THEN(LABEL_TAC "*") THEN
  REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MESON[]
   `P /\ (!x y i. Q x y i) <=> !i. P /\ (!x y. Q x y i)`] THEN
  X_GEN_TAC `i:num` THEN
  SUBGOAL_THEN
   `!n. simplicial_chain (p,standard_simplex p)
         (ITER n (simplicial_subdivision p)
                        (frag_of (RESTRICTION (standard_simplex p) I))) /\
        !f x y.
          f IN frag_support(ITER n (simplicial_subdivision p)
                        (frag_of (RESTRICTION (standard_simplex p) I))) /\
          x IN standard_simplex p /\
          y IN standard_simplex p
          ==> abs (f x i - f y i) <= (&p / (&p + &1)) pow n`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN REWRITE_TAC[ITER] THEN CONJ_TAC THENL
     [REWRITE_TAC[SIMPLICIAL_CHAIN_OF; SIMPLICIAL_SIMPLEX_I; SUBSET_REFL] THEN
      SIMP_TAC[FRAG_SUPPORT_OF; IN_SING; RESTRICTION; real_pow; I_THM] THEN
      REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
      MESON_TAC[REAL_ARITH
       `&0 <= x /\ &0 <= y /\ x <= &1 /\ y <= &1 ==> abs(x - y) <= &1`];
      GEN_TAC THEN STRIP_TAC THEN
      ASM_SIMP_TAC[SIMPLICIAL_CHAIN_SIMPLICIAL_SUBDIVISION] THEN
      REWRITE_TAC[real_pow] THEN
      MATCH_MP_TAC SIMPLICIAL_SUBDIVISION_SHRINKS THEN ASM_MESON_TAC[]];
    DISCH_THEN(MP_TAC o SPEC `m:num`)] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[simplicial_chain] THEN
  GEN_REWRITE_TAC LAND_CONV [SUBSET] THEN
  DISCH_THEN(MP_TAC o SPEC `d:(num->real)->(num->real)`) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  SIMP_TAC[SIMPLICIAL_SIMPLEX] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_CASES_TAC `i:num <= p` THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE_2] THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(&p / (&p + &1)) pow n` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  TRANS_TAC REAL_LE_TRANS `(&p / (&p + &1)) pow m` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ;
               REAL_ARITH `&0 < &p + &1`] THEN
  REAL_ARITH_TAC);;

let SMALL_HOMOLOGOUS_REL_RELCYCLE_EXISTS = prove
 (`!p top s u c:((num->real)->A)frag.
        (!v. v IN u ==> open_in top v) /\ topspace top SUBSET UNIONS u /\
        singular_relcycle (p,top,s) c
        ==> ?c'. singular_relcycle (p,top,s) c' /\
                 homologous_rel (p,top,s) c c' /\
                 !f. f IN frag_support c'
                      ==> ?v. v IN u /\ IMAGE f (standard_simplex p) SUBSET v`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[singular_relcycle]) THEN
  MP_TAC(ISPECL
   [`p:num`; `top:A topology`; `u:(A->bool)->bool`; `c:((num->real)->A)frag`]
   SUFFICIENT_ITERATED_SINGULAR_SUBDIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
  ABBREV_TAC `c':((num->real)->A)frag = ITER n (singular_subdivision p) c` THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  EXISTS_TAC `c':((num->real)->A)frag` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) /\ q ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOMOLOGOUS_REL_SINGULAR_RELCYCLE]; ALL_TAC] THEN
  EXPAND_TAC "c'" THEN SPEC_TAC(`n:num`,`m:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; HOMOLOGOUS_REL_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      HOMOLOGOUS_REL_TRANS)) THEN
  ONCE_REWRITE_TAC[HOMOLOGOUS_REL_SYM] THEN
  MATCH_MP_TAC HOMOLOGOUS_REL_SINGULAR_SUBDIVISION THEN
  ASM_MESON_TAC[HOMOLOGOUS_REL_SINGULAR_RELCYCLE]);;

let EXCISED_CHAIN_EXISTS = prove
 (`!p top s t u c:((num->real)->A)frag.
      top closure_of u SUBSET top interior_of t /\ t SUBSET s /\
      singular_chain(p,subtopology top s) c
      ==> ?n d e. singular_chain(p,subtopology top (s DIFF u)) d /\
                  singular_chain(p,subtopology top t) e /\
                  ITER n (singular_subdivision p) c = frag_add d e`,
  SUBGOAL_THEN
   `!p top s t u c:((num->real)->A)frag.
      top closure_of u SUBSET top interior_of t /\
      u SUBSET topspace top /\ t SUBSET s /\ s SUBSET topspace top /\
      singular_chain(p,subtopology top s) c
      ==> ?n d e. singular_chain(p,subtopology top (s DIFF u)) d /\
                  singular_chain(p,subtopology top t) e /\
                  ITER n (singular_subdivision p) c = frag_add d e`
  MP_TAC THENL
   [REPEAT STRIP_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`p:num`; `top:A topology`; `topspace top INTER s:A->bool`;
      `topspace top INTER t:A->bool`; `topspace top INTER u:A->bool`;
      `c:((num->real)->A)frag`]) THEN
    REWRITE_TAC[SET_RULE `s INTER t DIFF s INTER u = s INTER (t DIFF u)`] THEN
    REWRITE_TAC[GSYM SUBTOPOLOGY_RESTRICT; INTER_SUBSET] THEN
    ASM_REWRITE_TAC[GSYM INTERIOR_OF_RESTRICT; GSYM CLOSURE_OF_RESTRICT] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
  MP_TAC(ISPECL
   [`p:num`; `subtopology top (s:A->bool)`;
    `{s INTER top interior_of t:A->bool,s DIFF top closure_of u}`;
    `c:((num->real)->A)frag`]
   SUFFICIENT_ITERATED_SINGULAR_SUBDIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ANTS_TAC THENL
   [SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN; OPEN_IN_INTERIOR_OF] THEN
    ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_DIFF_CLOSED; CLOSED_IN_CLOSURE_OF] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; UNIONS_2] THEN ASM SET_TAC[];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num`] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[LE_REFL] THEN
  ABBREV_TAC `c':((num->real)->A)frag = ITER n (singular_subdivision p) c` THEN
  REWRITE_TAC[EXISTS_IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_SPLIT THEN REWRITE_TAC[SUBSET; IN_UNION] THEN
  X_GEN_TAC `f:(num->real)->A` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [DISJ_SYM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:(num->real)->A`) THEN
  SUBGOAL_THEN `singular_chain(p,subtopology top s:A topology) c'`
  (MP_TAC o REWRITE_RULE[singular_chain; SUBSET]) THENL
   [EXPAND_TAC "c'" THEN SPEC_TAC(`n:num`,`m:num`) THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[ITER; SINGULAR_CHAIN_0] THEN
    ASM_SIMP_TAC[SINGULAR_CHAIN_SINGULAR_SUBDIVISION];
    DISCH_THEN(MP_TAC o SPEC `f:(num->real)->A`) THEN
    ASM_SIMP_TAC[IN; SINGULAR_SIMPLEX_SUBTOPOLOGY; SUBSET_INTER] THEN
    STRIP_TAC THEN MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC[INTERIOR_OF_SUBSET] THEN
    MP_TAC(ISPECL [`top:A topology`; `u:A->bool`] CLOSURE_OF_SUBSET) THEN
    ASM SET_TAC[]]);;

let EXCISED_RELCYCLE_EXISTS = prove
 (`!p top s t u c:((num->real)->A)frag.
      top closure_of u SUBSET top interior_of t /\ t SUBSET s /\
      singular_relcycle (p,subtopology top s,t) c
      ==> ?c'. singular_relcycle (p,subtopology top (s DIFF u),t DIFF u) c' /\
               homologous_rel (p,subtopology top s,t) c c'`,
  REWRITE_TAC[singular_relcycle; cong; mod_subset] THEN
  REWRITE_TAC[IMP_CONJ; FRAG_MODULE `frag_sub x frag_0 = x`] THEN
  SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE
   `t SUBSET s
    ==> s INTER t = t /\ (s DIFF u) INTER (t DIFF u) = t DIFF u`] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p:num`; `top:A topology`; `s:A->bool`; `t:A->bool`; `u:A->bool`;
    `c:((num->real)->A)frag`]
   EXCISED_CHAIN_EXISTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`n:num`; `d:((num->real)->A)frag`; `e:((num->real)->A)frag`] THEN
  STRIP_TAC THEN EXISTS_TAC `d:((num->real)->A)frag` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `singular_chain(p - 1,subtopology top (t:A->bool)) (chain_boundary p d) /\
      singular_chain(p - 1,subtopology top (s DIFF u)) (chain_boundary p d)`
    MP_TAC THENL
     [ASM_SIMP_TAC[SINGULAR_CHAIN_BOUNDARY] THEN
      FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (FRAG_MODULE
       `c' = frag_add d e ==> d = frag_sub c' e`)) THEN
      REWRITE_TAC[CHAIN_BOUNDARY_SUB] THEN
      MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN
      ASM_SIMP_TAC[SINGULAR_CHAIN_BOUNDARY] THEN
      SPEC_TAC(`n:num`,`m:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[ITER] THEN
      MP_TAC(ISPECL [`p:num`; `subtopology top s:A topology`;
                     `ITER m (singular_subdivision p) c:((num->real)->A)frag`]
        CHAIN_BOUNDARY_SINGULAR_SUBDIVISION) THEN
      ANTS_TAC THENL
       [SPEC_TAC(`m:num`,`r:num`) THEN
        INDUCT_TAC THEN ASM_SIMP_TAC[SINGULAR_CHAIN_0; ITER] THEN
        ASM_SIMP_TAC[SINGULAR_CHAIN_SINGULAR_SUBDIVISION];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[SINGULAR_CHAIN_SINGULAR_SUBDIVISION];
      REWRITE_TAC[SINGULAR_CHAIN_SUBTOPOLOGY] THEN ASM SET_TAC[]];
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (FRAG_MODULE
       `c' = frag_add d e ==> d = frag_sub c' e`)) THEN
    GEN_REWRITE_TAC LAND_CONV [FRAG_MODULE `x = frag_sub x frag_0`] THEN
    MATCH_MP_TAC HOMOLOGOUS_REL_SUB THEN CONJ_TAC THENL
     [SPEC_TAC(`n:num`,`m:num`) THEN INDUCT_TAC THEN
      ASM_REWRITE_TAC[ITER; HOMOLOGOUS_REL_REFL] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HOMOLOGOUS_REL_TRANS)) THEN
      ONCE_REWRITE_TAC[HOMOLOGOUS_REL_SYM] THEN
      MATCH_MP_TAC HOMOLOGOUS_REL_SINGULAR_SUBDIVISION THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o
       MATCH_MP HOMOLOGOUS_REL_SINGULAR_RELCYCLE) THEN
      REWRITE_TAC[singular_relcycle; cong; mod_subset] THEN
      ASM_REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`];
      REWRITE_TAC[homologous_rel] THEN
      MATCH_MP_TAC SINGULAR_RELBOUNDARY_SUB THEN
      REWRITE_TAC[SINGULAR_RELBOUNDARY_0] THEN
      MATCH_MP_TAC SINGULAR_CHAIN_IMP_RELBOUNDARY] THEN
    ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE
       `t SUBSET s ==> s INTER t = t`]]);;

(* ------------------------------------------------------------------------- *)
(* Homotopy invariance.                                                      *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_IMP_HOMOLOGOUS_REL_CHAIN_MAPS = prove
 (`!p f g:A->B s t u v c:((num->real)->A)frag.
        homotopic_with (\h. IMAGE h t SUBSET v) (s,u) f g /\
        singular_relcycle (p,s,t) c
        ==> homologous_rel (p,u,v) (chain_map p f c) (chain_map p g c)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?prism:num->(((num->real)->A)frag)->(((num->real)->B)frag).
        (!q. prism q frag_0 = frag_0) /\
        (!q c. singular_chain (q,s) c
               ==> singular_chain (q + 1,u) (prism q c)) /\
        (!q c. singular_chain (q,subtopology s t) c
               ==> singular_chain (q + 1,subtopology u v) (prism q c)) /\
        (!q c. singular_chain (q,s) c
               ==> chain_boundary (q + 1) (prism q c) =
                   frag_sub (frag_sub (chain_map q g c) (chain_map q f c))
                            (prism (q - 1) (chain_boundary q c)))`
  STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `c:((num->real)->A)frag` THEN
    REWRITE_TAC[singular_relcycle; homologous_rel; singular_relboundary;
                cong; mod_subset; FRAG_MODULE `frag_sub x frag_0 = x`] THEN
    STRIP_TAC THEN
    EXISTS_TAC
     `frag_neg((prism:num->(((num->real)->A)frag)->((num->real)->B)frag)
                p c)` THEN
    ASM_SIMP_TAC[SINGULAR_CHAIN_NEG; CHAIN_BOUNDARY_NEG] THEN
    REWRITE_TAC[FRAG_MODULE
     `frag_sub (frag_neg (frag_sub (frag_sub g f) d))
               (frag_sub f g) = d`] THEN
    ASM_CASES_TAC `p = 0` THENL
     [ASM_REWRITE_TAC[chain_boundary; SINGULAR_CHAIN_0]; ALL_TAC] THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
        [MATCH_MP (ARITH_RULE `~(p = 0) ==> p = (p - 1) + 1`) th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homotopic_with]) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real#A->B` STRIP_ASSUME_TAC) THEN
  MAP_EVERY ABBREV_TAC
   [`vv:num->num->real = \j i. if i = j + 1 then &1 else &0`;
    `ww:num->num->real = \j i. if i = 0 \/ i = j + 1 then &1 else &0`;
    `simp =
     \q i. oriented_simplex (q + 1) (\j. if j <= i then vv j else ww(j - 1))`;
    `prism:num->((num->real)->A)->((num->real)->B)frag =
       \q c. iterate frag_add (0..q)
              (\i. frag_cmul (int_pow (-- &1) i)
                             (frag_of (simplex_map (q + 1)
                                             (\z. h(z 0,c(z o SUC)))
                            (simp q i:(num->real)->(num->real)))))`] THEN
  EXISTS_TAC
  `\q. frag_extend((prism:num->((num->real)->A)->((num->real)->B)frag) q)` THEN
  REWRITE_TAC[FRAG_EXTEND_0] THEN
  SUBGOAL_THEN
   `!q i. i <= q
        ==> simplicial_simplex
              (q + 1,{x | x 0 IN real_interval[&0,&1] /\
                          (x o SUC) IN standard_simplex q})
              ((simp:num->num->(num->real)->(num->real)) q i)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`q:num`; `i:num`] THEN DISCH_TAC THEN
    EXPAND_TAC "simp" THEN
    REWRITE_TAC[SIMPLICIAL_SIMPLEX_ORIENTED_SIMPLEX] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; o_DEF] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    X_GEN_TAC `x:num->real` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["vv"; "ww"] THEN
    REWRITE_TAC[NOT_SUC; ARITH_RULE `~(0 = j + 1)`] THEN
    REWRITE_TAC[standard_simplex; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [standard_simplex]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH
       `&0 <= x /\ x <= &1 <=> abs(x - &0) <= &1 /\ abs(x - &1) <= &1`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_CONVEX_SUM_BOUND_LE THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN REWRITE_TAC[REAL_ARITH
      `&0 <= x /\ x <= &1 <=> abs(x - &0) <= &1 /\ abs(x - &1) <= &1`] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_CONVEX_SUM_BOUND_LE THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LZERO]) THEN
      REWRITE_TAC[REAL_MUL_LID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; SUM_0; REAL_MUL_LID; ETA_AX] THEN
      REWRITE_TAC[IN_ELIM_THM; REAL_ADD_RID] THEN
      REWRITE_TAC[IN_NUMSEG; LE_0; GSYM CONJ_ASSOC] THEN
      REWRITE_TAC[ARITH_RULE
       `(j <= q + 1 /\ j <= i /\ SUC k = j + 1 <=>
         j = k /\ k <= q + 1 /\ k <= i) /\
        (j <= q + 1 /\ ~(j <= i) /\ SUC k = j - 1 + 1 <=>
        j = k + 1 /\ k + 1 <= q + 1 /\ ~(k + 1 <= i))`] THEN
      REWRITE_TAC[SET_RULE `{x | x = a /\ P} = if P then {a} else {}`] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SING; SUM_CLAUSES] THEN
      REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
      ASM_SIMP_TAC[ARITH_RULE
       `i <= q ==> (k <= q /\ k <= q + 1 /\ k <= i <=> 0 <= k /\ k <= i)`] THEN
      ASM_SIMP_TAC[ARITH_RULE
        `k <= q /\ k + 1 <= q + 1 /\ ~(k + 1 <= i) <=>
         i <= k /\ k <= q`] THEN
      REWRITE_TAC[GSYM numseg] THEN REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
      MP_TAC(ISPECL
       [`x:num->real`; `0`; `i:num`; `(q + 1) - i`] SUM_ADD_SPLIT) THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= q ==> i + (q + 1) - i = q + 1`; LE_0]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `q:num` THEN REWRITE_TAC[singular_chain] THEN
    MATCH_MP_TAC FRAG_INDUCTION THEN REWRITE_TAC[GSYM singular_chain] THEN
    REWRITE_TAC[FRAG_EXTEND_0; SINGULAR_CHAIN_0; FRAG_EXTEND_OF] THEN
    SIMP_TAC[FRAG_EXTEND_SUB; SINGULAR_CHAIN_SUB] THEN
    X_GEN_TAC `m:(num->real)->A` THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
    DISCH_TAC THEN EXPAND_TAC "prism" THEN
    MATCH_MP_TAC SINGULAR_CHAIN_SUM THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC SINGULAR_CHAIN_CMUL THEN REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
    MATCH_MP_TAC SINGULAR_SIMPLEX_SIMPLEX_MAP THEN
    EXISTS_TAC
     `subtopology (product_topology (:num) (\i. euclideanreal))
                  {x | x 0 IN real_interval[&0,&1] /\
                       (x o SUC) IN standard_simplex q}` THEN
    ASM_SIMP_TAC[SIMPLICIAL_IMP_SINGULAR_SIMPLEX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
     `prod_topology (subtopology euclideanreal (real_interval [&0,&1]))
                    (s:(A)topology)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN
      REWRITE_TAC[IN_UNIV];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [singular_simplex]) THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
       (standard_simplex q)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; IN_UNIV] THEN
      REWRITE_TAC[SUBSET; IN; EXTENSIONAL_UNIV] THEN GEN_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN
      REWRITE_TAC[IN_UNIV]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `q:num` THEN REWRITE_TAC[singular_chain] THEN
    MATCH_MP_TAC FRAG_INDUCTION THEN REWRITE_TAC[GSYM singular_chain] THEN
    REWRITE_TAC[FRAG_EXTEND_0; SINGULAR_CHAIN_0; FRAG_EXTEND_OF] THEN
    SIMP_TAC[FRAG_EXTEND_SUB; SINGULAR_CHAIN_SUB] THEN
    X_GEN_TAC `m:(num->real)->A` THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
    DISCH_TAC THEN EXPAND_TAC "prism" THEN
    MATCH_MP_TAC SINGULAR_CHAIN_SUM THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
    MATCH_MP_TAC SINGULAR_CHAIN_CMUL THEN REWRITE_TAC[SINGULAR_CHAIN_OF] THEN
    MATCH_MP_TAC SINGULAR_SIMPLEX_SIMPLEX_MAP THEN
    EXISTS_TAC
     `subtopology (product_topology (:num) (\i. euclideanreal))
                  {x | x 0 IN real_interval[&0,&1] /\
                       (x o SUC) IN standard_simplex q}` THEN
    ASM_SIMP_TAC[SIMPLICIAL_IMP_SINGULAR_SIMPLEX] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN EXISTS_TAC
     `prod_topology (subtopology euclideanreal (real_interval [&0,&1]))
                    (subtopology s t:(A)topology)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN
      REWRITE_TAC[IN_UNIV];
      GEN_REWRITE_TAC RAND_CONV [GSYM o_DEF] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o
        GEN_REWRITE_RULE I [singular_simplex]) THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
       (standard_simplex q)` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE; IN_UNIV] THEN
      REWRITE_TAC[SUBSET; IN; EXTENSIONAL_UNIV] THEN GEN_TAC THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN
      REWRITE_TAC[IN_UNIV];
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SUBTOPOLOGY_RESTRICT] THEN
        REWRITE_TAC[GSYM SUBTOPOLOGY_CROSS] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
        EXISTS_TAC `real_interval [&0,&1] CROSS (topspace s:A->bool)` THEN
        ASM_REWRITE_TAC[SUBTOPOLOGY_CROSS; SUBTOPOLOGY_TOPSPACE] THEN
        REWRITE_TAC[SUBSET_CROSS; INTER_SUBSET];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS;
          TOPSPACE_SUBTOPOLOGY; TOPSPACE_PROD_TOPOLOGY; IN_INTER] THEN
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `q:num` THEN REWRITE_TAC[singular_chain] THEN
  MATCH_MP_TAC FRAG_INDUCTION THEN REWRITE_TAC[GSYM singular_chain] THEN
  REWRITE_TAC[FRAG_EXTEND_0; CHAIN_BOUNDARY_0; CHAIN_MAP_0] THEN
  REWRITE_TAC[FRAG_MODULE `frag_sub x x = frag_0`] THEN
  REWRITE_TAC[FRAG_EXTEND_SUB; CHAIN_BOUNDARY_SUB; CHAIN_MAP_SUB] THEN
  CONJ_TAC THENL [ALL_TAC; REPEAT GEN_TAC THEN CONV_TAC FRAG_MODULE] THEN
  X_GEN_TAC `a:(num->real)->A` THEN GEN_REWRITE_TAC LAND_CONV [IN] THEN
  DISCH_TAC THEN REWRITE_TAC[CHAIN_MAP_OF; FRAG_EXTEND_OF] THEN
  FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o funpow 2 RATOR_CONV) [SYM th]) THEN
  SIMP_TAC[CHAIN_BOUNDARY_SUM; FINITE_NUMSEG; o_DEF; CHAIN_BOUNDARY_CMUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [chain_boundary] THEN
  REWRITE_TAC[FRAG_EXTEND_OF; ARITH_RULE `~(q + 1 = 0)`] THEN
  REWRITE_TAC[FRAG_CMUL_SUM] THEN
  SIMP_TAC[MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_FRAG_ADD;
           FINITE_NUMSEG] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{i,j | i IN 0..q /\ j IN 0..q + 1} =
    {i,j | i IN 0..q /\ j IN {j | j IN 0..q + 1 /\ j <= i}} UNION
    {i,j | i IN 0..q /\ j IN {j | j IN 0..q + 1 /\ ~(j <= i)}}`] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
   (MATCH_MP ITERATE_UNION MONOIDAL_FRAG_ADD) o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_NUMSEG; FINITE_RESTRICT] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!i. {j | j IN 0..q + 1 /\ ~(j <= i)} = i+1..q+1`
  (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[GSYM(MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_FRAG_ADD);
           FINITE_NUMSEG; FINITE_RESTRICT] THEN
  REWRITE_TAC[NUMSEG_OFFSET_IMAGE] THEN
  SIMP_TAC[MATCH_MP ITERATE_IMAGE MONOIDAL_FRAG_ADD; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_FRAG_ADD;
           FINITE_NUMSEG; FINITE_RESTRICT] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{i,j | i IN s /\ j IN t i} =
    IMAGE (\i. (i,i)) {i | i IN s /\ i IN t i} UNION
    {i,j | i IN s /\ j IN (t i DELETE i)}`] THEN
  MAP_EVERY (fun conv ->
    W(MP_TAC o PART_MATCH (lhand o rand)
      (MATCH_MP ITERATE_UNION MONOIDAL_FRAG_ADD) o conv o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT_DEPENDENT;
               FINITE_NUMSEG; FINITE_DELETE; FINITE_RESTRICT] THEN
      REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN
      SET_TAC[];
      DISCH_THEN SUBST1_TAC]) [lhand;rand] THEN
  MATCH_MP_TAC(FRAG_MODULE
   `frag_add x1 y1 = w /\ frag_add x2 y2 = frag_neg z
    ==> frag_add (frag_add x1 x2) (frag_add y1 y2) = frag_sub w z`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[MATCH_MP ITERATE_IMAGE MONOIDAL_FRAG_ADD; PAIR_EQ] THEN
    REWRITE_TAC[o_DEF; IN_ELIM_THM; IN_NUMSEG] THEN
    REWRITE_TAC[LE_REFL; LE_0; ARITH_RULE
      `i <= q /\ i <= q + 1 <=> i <= q`] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `i <= k <=> 0 <= i /\ i <= k`] THEN
    REWRITE_TAC[GSYM numseg] THEN
    REWRITE_TAC[INT_POW_ADD; INT_POW_1; FRAG_MODULE
     `frag_cmul a (frag_cmul b c) = frag_cmul (a * b) c`] THEN
    REWRITE_TAC[INT_MUL_ASSOC; GSYM INT_POW_ADD] THEN
    SIMP_TAC[INT_POW_NEG; EVEN_ADD; INT_POW_ONE] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[FRAG_MODULE `frag_cmul (&1) x = x`] THEN
    SUBGOAL_THEN `0..q = 0 INSERT IMAGE (\i. i + 1) {i | i < q}` (fun th ->
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [SIMP_TAC[GSYM NUMSEG_LREC; LE_0] THEN AP_TERM_TAC THEN
      ASM_CASES_TAC `q = 0` THENL
       [ASM_REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; IMAGE_CLAUSES] THEN
        REWRITE_TAC[NUMSEG_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
        ASM_SIMP_TAC[ARITH_RULE
         `~(q = 0) ==> (i < q <=> 0 <= i /\ i <= q - 1)`] THEN
        REWRITE_TAC[GSYM numseg; GSYM NUMSEG_OFFSET_IMAGE] THEN
        AP_TERM_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `0..q = q INSERT {i | i < q}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD;
             FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[IN_ELIM_THM; LT_REFL; IN_IMAGE; ARITH_RULE `~(0 = i + 1)`] THEN
    SIMP_TAC[MATCH_MP ITERATE_IMAGE MONOIDAL_FRAG_ADD; EQ_ADD_RCANCEL] THEN
    MATCH_MP_TAC(FRAG_MODULE
     `(x1 = w /\ frag_neg y1 = z) /\ frag_cmul (-- &1) x2 = y2
      ==> frag_add (frag_add x1 x2) (frag_add y1 y2) = frag_sub w z`) THEN
    CONJ_TAC THENL
     [SIMP_TAC[SINGULAR_FACE_SIMPLEX_MAP; LE_REFL; LE_0; ADD_SUB;
               FRAG_MODULE `frag_neg (frag_cmul (-- &1) x) = x`;
               ARITH_RULE `1 <= p + 1`] THEN
      REWRITE_TAC[simplex_map] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `x:num->real` THEN
      REWRITE_TAC[RESTRICTION] THEN
      ASM_CASES_TAC `x IN standard_simplex q` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[o_DEF] THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `(!x. h(a,x) = c x) ==> w = a /\ z = y ==> h(w,z) = c y`)) THEN
      (CONJ_TAC THENL [ALL_TAC; AP_TERM_TAC]) THEN
      EXPAND_TAC "simp" THEN REWRITE_TAC[oriented_simplex] THEN
      ASM_SIMP_TAC[RESTRICTION; FACE_MAP_IN_STANDARD_SIMPLEX; ADD_SUB;
                   LE_REFL; LE_0; ARITH_RULE `1 <= p + 1`] THEN
      REWRITE_TAC[face_map; CONJUNCT1 LE; CONJUNCT1 LT] THEN
      REWRITE_TAC[ARITH_RULE `j < q + 1 <=> j <= q`] THEN
      REWRITE_TAC[MESON[]
       `(if p then f1 else f2) a * (if p then y1 else y2):real =
        if p then f1 a * y1 else f2 a * y2`] THEN
      MAP_EVERY EXPAND_TAC ["vv"; "ww"] THEN
      REWRITE_TAC[NOT_SUC; ARITH_RULE `~(0 = j + 1)`;
                  REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; SUM_0; REAL_ADD_LID] THEN
      REWRITE_TAC[MESON[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_LID]
       `(if p then &1 else &0) * (if q then &0 else x):real =
        if p /\ ~q then x else &0`] THEN
      REWRITE_TAC[COND_RAND; COND_RATOR] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; SUM_0] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      REWRITE_TAC[EMPTY_GSPEC; CONJUNCT1 SUM_CLAUSES; ARITH_RULE
       `~((j <= q + 1 /\ ~(j <= q)) /\ ~(j = q + 1))`] THEN
      REWRITE_TAC[ARITH_RULE
       `(j <= q + 1 /\ ~(j = 0)) /\ SUC k = j - 1 + 1 <=>
        j = k + 1 /\ k <= q`] THEN
      REWRITE_TAC[EMPTY_GSPEC; CONJUNCT1 SUM_CLAUSES; REAL_ADD_RID; ARITH_RULE
       `~((j <= q + 1 /\ ~(j <= q)) /\ k = j - 1 + 1 /\ ~(j = q + 1))`] THEN
      REWRITE_TAC[ARITH_RULE
       `(j <= q + 1 /\ j <= q) /\ SUC k = j + 1 <=> j = k /\ k <= q`] THEN
      REWRITE_TAC[SET_RULE `{x | x = a /\ P} = if P then {a} else {}`] THEN
      ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      REWRITE_TAC[CONJUNCT1 SUM_CLAUSES; SUM_SING] THEN
      REWRITE_TAC[ADD_SUB; REAL_MUL_LID; ARITH_RULE
       `j <= q + 1 /\ ~(j = 0) <=> 0 + 1 <= j /\ j <= q + 1`] THEN
      REWRITE_TAC[GSYM numseg; SUM_OFFSET; ADD_SUB; ETA_AX] THEN
      UNDISCH_TAC `x IN standard_simplex q` THEN
      SIMP_TAC[standard_simplex; IN_ELIM_THM] THEN STRIP_TAC THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN REWRITE_TAC[GSYM NOT_LT] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[GSYM FRAG_CMUL_SUM] THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[o_THM; IN_ELIM_THM] THEN
      DISCH_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[SINGULAR_FACE_SIMPLEX_MAP; ARITH_RULE `1 <= q + 1`;
                   ARITH_RULE `i < q ==> i + 1 <= q + 1`] THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `x:num->real` THEN
      REWRITE_TAC[simplex_map; RESTRICTION; ADD_SUB] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC BINOP_CONV [o_THM] THEN AP_TERM_TAC THEN
      EXPAND_TAC "simp" THEN REWRITE_TAC[o_THM; oriented_simplex] THEN
      ASM_SIMP_TAC[RESTRICTION; FACE_MAP_IN_STANDARD_SIMPLEX;
                   ARITH_RULE `1 <= p + 1`; ADD_SUB;
                   ARITH_RULE `i < q ==> i + 1 <= q + 1`] THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
      ONCE_REWRITE_TAC[COND_RATOR] THEN ASM_CASES_TAC `j:num <= i` THEN
      ASM_SIMP_TAC[ARITH_RULE `j <= i ==> j <= i + 1`] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(j <= i) ==> (j <= i + 1 <=> j = i + 1)`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["vv"; "ww"] THEN
      REWRITE_TAC[ADD_SUB; face_map; LT_REFL; REAL_MUL_RZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[chain_boundary] THEN
  ASM_CASES_TAC `q = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; FRAG_EXTEND_0; IN_DELETE; LE_0] THEN
    REWRITE_TAC[ARITH_RULE `~(x <= 0 /\ (j <= 0 + 1 /\ j <= x) /\ ~(j = x))`;
                ARITH_RULE `~(x <= 0 /\ (x <= j /\ j <= 0) /\ ~(j = x))`] THEN
    REWRITE_TAC[SET_RULE `{i,j | F} = {}`] THEN
    REWRITE_TAC[MATCH_MP ITERATE_CLAUSES MONOIDAL_FRAG_ADD] THEN
    REWRITE_TAC[NEUTRAL_FRAG_ADD] THEN CONV_TAC FRAG_MODULE;
    ALL_TAC] THEN
  REWRITE_TAC[FRAG_EXTEND_OF] THEN
  SIMP_TAC[FRAG_EXTEND_SUM; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF; FRAG_EXTEND_CMUL; FRAG_EXTEND_OF] THEN
  EXPAND_TAC "prism" THEN REWRITE_TAC[FRAG_CMUL_SUM; FRAG_MODULE
   `frag_neg c = frag_cmul (-- &1) c`] THEN
  REWRITE_TAC[FRAG_MODULE `frag_cmul a (frag_cmul b c) = frag_cmul (a * b) c`;
               GSYM INT_POW_ADD; GSYM(CONJUNCT2 INT_POW)] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
        (MATCH_MP ITERATE_SWAP MONOIDAL_FRAG_ADD) o rand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
  SIMP_TAC[MATCH_MP ITERATE_ITERATE_PRODUCT MONOIDAL_FRAG_ADD;
           FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `{i,j | i IN 0..q-1 /\ j IN 0..q} =
    {i,j | i IN 0..q-1 /\ j IN {j | j IN 0..q /\ j <= i}} UNION
    {i,j | i IN 0..q /\ j IN {j | j IN 0..q /\ i < j}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_UNION; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
     (MATCH_MP ITERATE_UNION MONOIDAL_FRAG_ADD) o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_NUMSEG; FINITE_RESTRICT] THEN
    REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC(MATCH_MP ITERATE_EQ_GENERAL_INVERSES MONOIDAL_FRAG_ADD) THEN
    EXISTS_TAC `\(a:num,b:num). (a - 1,b)` THEN
    EXISTS_TAC `\(a:num,b:num). (a + 1,b)` THEN
    REWRITE_TAC[IN_DELETE; IMP_CONJ; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM; IN_NUMSEG; PAIR_EQ; LE_0] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN REPLICATE_TAC 3 STRIP_TAC THEN
    REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    SUBGOAL_THEN `SUC j + i - 1 = i + j` SUBST1_TAC THENL
     [ASM_ARITH_TAC; AP_TERM_TAC THEN AP_TERM_TAC] THEN
    ASM_SIMP_TAC[SINGULAR_FACE_SIMPLEX_MAP; ARITH_RULE `1 <= q + 1`] THEN
    REWRITE_TAC[ADD_SUB] THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    REWRITE_TAC[simplex_map; RESTRICTION] THEN
    X_GEN_TAC `x:num->real` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[singular_face; o_THM; RESTRICTION] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`q - 1`; `i - 1`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIMPLICIAL_SIMPLEX; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1; IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `k:num` THEN REWRITE_TAC[o_THM]] THEN
    EXPAND_TAC "simp" THEN
    REWRITE_TAC[oriented_simplex; RESTRICTION] THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[FACE_MAP_IN_STANDARD_SIMPLEX; ADD_SUB;
                 ARITH_RULE `1 <= j + 1`] THEN
    MAP_EVERY EXPAND_TAC ["vv"; "ww"] THEN
    REWRITE_TAC[face_map; o_DEF] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[ARITH_RULE `~(0 = k + 1)`; NOT_SUC] THENL
     [ONCE_REWRITE_TAC[MESON[]
       `(if p then x else y) * z:real = if p then x * z else y * z`] THEN
      SIMP_TAC[REAL_MUL_LZERO; FINITE_NUMSEG; SUM_CASES; SUM_0] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_ADD_LID] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[SUM_0; REAL_ADD_LID] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_1; NOT_LE; LE_0; NOT_LT] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE o rand o rand o snd) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[IMAGE; IN_ELIM_THM; ARITH_RULE
       `(((x <= q + 1 /\ i < x) /\ j <= x) /\ ~(x = j)) /\ y = x - 1
        <=> x = y + 1 /\ y <= q /\ i <= y /\ j <= y`] THEN
      REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[CONJ_ASSOC; DISJOINT; EXTENSION; IN_ELIM_THM;
                    NOT_IN_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN CONJ_TAC THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..q+1` THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
        ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[ETA_AX] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
      ASM_CASES_TAC `k:num = j` THEN ASM_REWRITE_TAC[LT_REFL] THENL
       [CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[MESON[]
       `(if p then if q then a else b else if r then a else b) =
        (if p /\ q \/ ~p /\ r then a else b)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `(if p then a else b) * x:real = if p then a * x else b * x`] THEN
      REWRITE_TAC[REAL_MUL_LZERO; GSYM SUM_RESTRICT_SET; REAL_MUL_LID] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[SUM_0; REAL_ADD_LID] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE o rand o rand o snd) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[IN_NUMSEG; ADD1; EQ_ADD_RCANCEL; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC; LE_0; NOT_LE; NOT_LT] THEN
      REWRITE_TAC[IMAGE; IN_ELIM_THM; ARITH_RULE
       `j:num <= k /\ ~(k = j) <=> j < k`] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC; ARITH_RULE
       `j < k /\ m = k - 1 <=> j <= m /\ k = m + 1`] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> s /\ p /\ q /\ r`] THEN
      REWRITE_TAC[UNWIND_THM2; ETA_AX] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o rand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[CONJ_ASSOC; DISJOINT; EXTENSION; IN_ELIM_THM;
                    NOT_IN_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN CONJ_TAC THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..q+1` THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
        ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      ASM_CASES_TAC `k:num < j` THEN ASM_REWRITE_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; ADD_SUB] THEN
      (SUBGOAL_THEN `1 <= i` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
      SIMP_TAC[ARITH_RULE `1 <= i ==> (j <= i - 1 <=> j < i)`;
               ARITH_RULE `1 <= i ==> (i - 1 <= k <=> i <= k + 1)`]
      THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `1 <= k` MP_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[SUB_ADD]] THEN
      SIMP_TAC[ARITH_RULE `1 <= k ==> (k - 1 = j <=> k = j + 1)`] THEN
      ASM_ARITH_TAC];
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; IN_DELETE; LE_0] THEN
    REWRITE_TAC[ARITH_RULE
     `i <= q /\ (i <= j /\ j <= q) /\ ~(j = i) <=>
      i:num <= q /\ j <= q /\ i < j`] THEN
    MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC j + i = i + j + 1`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[SINGULAR_FACE_SIMPLEX_MAP; ARITH_RULE `1 <= q + 1`;
                 ARITH_RULE `j <= q ==> j + 1 <= q + 1`] THEN
    REWRITE_TAC[ADD_SUB] THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    REWRITE_TAC[simplex_map; RESTRICTION] THEN
    X_GEN_TAC `x:num->real` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[singular_face; o_THM; RESTRICTION] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`q - 1`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SIMPLICIAL_SIMPLEX; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1; IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN
    AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `k:num` THEN REWRITE_TAC[o_THM]] THEN
    EXPAND_TAC "simp" THEN
    REWRITE_TAC[oriented_simplex; RESTRICTION] THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1] THEN
    ASM_SIMP_TAC[FACE_MAP_IN_STANDARD_SIMPLEX; ADD_SUB;
                 LE_ADD_RCANCEL; ARITH_RULE `1 <= j + 1`] THEN
    MAP_EVERY EXPAND_TAC ["vv"; "ww"] THEN
    REWRITE_TAC[face_map; o_DEF] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[ARITH_RULE `~(0 = k + 1)`; NOT_SUC] THENL
     [ONCE_REWRITE_TAC[MESON[]
       `(if p then x else y) * z:real = if p then x * z else y * z`] THEN
      SIMP_TAC[REAL_MUL_LZERO; FINITE_NUMSEG; SUM_CASES; SUM_0] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_ADD_LID] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[SUM_0; REAL_ADD_LID] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_1; NOT_LE; LE_0; NOT_LT] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE o rand o lhand o snd) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[IMAGE; IN_ELIM_THM; ARITH_RULE
       `(((x <= q + 1 /\ i < x) /\ j + 1 <= x) /\ ~(x = j + 1)) /\ y = x - 1
        <=> x = y + 1 /\ y <= q /\ i <= y /\ j < y`] THEN
      REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[CONJ_ASSOC; DISJOINT; EXTENSION; IN_ELIM_THM;
                    NOT_IN_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN CONJ_TAC THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..q+1` THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
        ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[ETA_AX] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
      ASM_CASES_TAC `k:num = j` THEN ASM_REWRITE_TAC[LT_REFL] THENL
       [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[MESON[]
       `(if p then if q then a else b else if r then a else b) =
        (if p /\ q \/ ~p /\ r then a else b)`] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `(if p then a else b) * x:real = if p then a * x else b * x`] THEN
      REWRITE_TAC[REAL_MUL_LZERO; GSYM SUM_RESTRICT_SET; REAL_MUL_LID] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      REWRITE_TAC[SUM_0; REAL_ADD_LID] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE o rand o lhand o snd) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
      REWRITE_TAC[IN_NUMSEG; ADD1; EQ_ADD_RCANCEL; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC; LE_0; NOT_LE; NOT_LT] THEN
      REWRITE_TAC[IMAGE; IN_ELIM_THM; ARITH_RULE
       `j:num <= k /\ ~(k = j) <=> j < k`] THEN
      REWRITE_TAC[GSYM CONJ_ASSOC; ARITH_RULE
       `j + 1 < k /\ m = k - 1 <=> j < m /\ k = m + 1`] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> s /\ p /\ q /\ r`] THEN
      REWRITE_TAC[UNWIND_THM2; ETA_AX] THEN
      W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[CONJ_ASSOC; DISJOINT; EXTENSION; IN_ELIM_THM;
                    NOT_IN_EMPTY; IN_INTER; IN_ELIM_THM] THEN
        CONJ_TAC THENL [ALL_TAC; ARITH_TAC] THEN CONJ_TAC THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..q+1` THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN
        ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      ASM_CASES_TAC `k:num < j` THEN ASM_REWRITE_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; ADD_SUB] THEN
      REWRITE_TAC[ARITH_RULE `i < j /\ k = j - 1 <=> i < j /\ j = k + 1`] THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `1 <= k` MP_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[SUB_ADD]] THEN
      SIMP_TAC[ARITH_RULE `1 <= k ==> (k - 1 = j <=> k = j + 1)`] THEN
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Now actually connect to group theory and set up homology groups. Note     *)
(* that we define homomogy groups for all *integers* p, since this seems to  *)
(* avoid some special-case reasoning, though they are trivial for p < 0.     *)
(* ------------------------------------------------------------------------- *)

let chain_group = new_definition
 `chain_group (p,top:A topology) =
  free_abelian_group (singular_simplex(p,top))`;;

let CHAIN_GROUP = prove
 (`(!p top:A topology.
        group_carrier(chain_group(p,top)) = singular_chain(p,top)) /\
   (!p top:A topology. group_id(chain_group(p,top)) = frag_0) /\
   (!p top:A topology. group_inv(chain_group(p,top)) = frag_neg) /\
   (!p top:A topology. group_mul(chain_group(p,top)) = frag_add)`,
  REWRITE_TAC[chain_group; FREE_ABELIAN_GROUP] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REWRITE_TAC[IN; singular_chain]);;

let ABELIAN_CHAIN_GROUP = prove
 (`!p top:A topology. abelian_group(chain_group (p,top))`,
  REWRITE_TAC[chain_group; ABELIAN_FREE_ABELIAN_GROUP]);;

let SUBGROUP_SINGULAR_RELCYCLE = prove
 (`!p top s:A->bool.
        singular_relcycle(p,top,s) subgroup_of chain_group(p,top)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subgroup_of; CHAIN_GROUP] THEN
  REWRITE_TAC[SUBSET; IN; SINGULAR_RELCYCLE_0] THEN
  REWRITE_TAC[SINGULAR_RELCYCLE_ADD; SINGULAR_RELCYCLE_NEG] THEN
  SIMP_TAC[singular_relcycle]);;

let relcycle_group = new_definition
 `relcycle_group(p,top:A topology,s) =
        subgroup_generated (chain_group(p,top)) (singular_relcycle(p,top,s))`;;

let RELCYCLE_GROUP = prove
 (`(!p top s:A->bool. group_carrier(relcycle_group(p,top,s)) =
                      singular_relcycle(p,top,s)) /\
   (!p top s:A->bool. group_id(relcycle_group(p,top,s)) = frag_0) /\
   (!p top s:A->bool. group_inv(relcycle_group(p,top,s)) = frag_neg) /\
   (!p top s:A->bool. group_mul(relcycle_group(p,top,s)) = frag_add)`,
  SIMP_TAC[relcycle_group; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
           SUBGROUP_SINGULAR_RELCYCLE] THEN
  REWRITE_TAC[SUBGROUP_GENERATED; CHAIN_GROUP]);;

let ABELIAN_RELCYCLE_GROUP = prove
 (`!p top s:A->bool. abelian_group(relcycle_group(p,top,s))`,
  SIMP_TAC[relcycle_group; ABELIAN_SUBGROUP_GENERATED;
            ABELIAN_CHAIN_GROUP]);;

let RELCYCLE_GROUP_RESTRICT = prove
 (`!p top s:A->bool.
        relcycle_group(p,top,s) =
        relcycle_group(p,top,topspace top INTER s)`,
  REWRITE_TAC[relcycle_group; GSYM SINGULAR_RELCYCLE_RESTRICT]);;

let relative_homology_group = new_definition
 `relative_homology_group(p,top:A topology,s) =
        if p < &0 then singleton_group ARB else
        quotient_group (relcycle_group(num_of_int p,top,s))
                       (singular_relboundary(num_of_int p,top,s))`;;

let homology_group = new_definition
 `homology_group(p,top:A topology) = relative_homology_group(p,top,{})`;;

let RELATIVE_HOMOLOGY_GROUP_RESTRICT = prove
 (`!p top s:A->bool.
        relative_homology_group(p,top,s) =
        relative_homology_group(p,top,topspace top INTER s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relative_homology_group] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[relcycle_group] THEN
  REWRITE_TAC[GSYM SINGULAR_RELBOUNDARY_RESTRICT;
              GSYM SINGULAR_RELCYCLE_RESTRICT]);;

let NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP = prove
 (`!p top s:A->bool.
        relative_homology_group(&p,top,s) =
        quotient_group (relcycle_group(p,top,s))
                       (singular_relboundary(p,top,s))`,
  REWRITE_TAC[relative_homology_group; INT_ARITH `~(&p:int < &0)`] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM]);;

let TRIVIAL_RELATIVE_HOMOLOGY_GROUP = prove
 (`!p top s:A->bool.
        p < &0 ==> trivial_group(relative_homology_group(p,top,s))`,
  SIMP_TAC[relative_homology_group; TRIVIAL_GROUP_SINGLETON_GROUP]);;

let SUBGROUP_SINGULAR_RELBOUNDARY = prove
 (`!p top s:A->bool.
        singular_relboundary(p,top,s) subgroup_of chain_group(p,top)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[subgroup_of; CHAIN_GROUP] THEN
  REWRITE_TAC[SUBSET; IN; SINGULAR_RELBOUNDARY_0] THEN
  REWRITE_TAC[SINGULAR_RELBOUNDARY_ADD; SINGULAR_RELBOUNDARY_NEG] THEN
  REWRITE_TAC[SINGULAR_RELBOUNDARY_IMP_CHAIN]);;

let SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE = prove
 (`!p top s:A->bool.
        singular_relboundary(p,top,s) subgroup_of relcycle_group(p,top,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relcycle_group] THEN
  MATCH_MP_TAC SUBGROUP_OF_SUBGROUP_GENERATED THEN
  REWRITE_TAC[SUBGROUP_SINGULAR_RELBOUNDARY; SUBSET; IN] THEN
  REWRITE_TAC[SINGULAR_RELBOUNDARY_IMP_RELCYCLE]);;

let NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE = prove
 (`!p top s:A->bool.
     singular_relboundary(p,top,s) normal_subgroup_of relcycle_group(p,top,s)`,
  SIMP_TAC[ABELIAN_GROUP_NORMAL_SUBGROUP; ABELIAN_RELCYCLE_GROUP;
           SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE]);;

let RIGHT_COSET_SINGULAR_RELBOUNDARY = prove
 (`!p top s:A->bool.
      right_coset (relcycle_group(p,top,s)) (singular_relboundary (p,top,s)) =
      homologous_rel (p,top,s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN
  REWRITE_TAC[right_coset; homologous_rel; group_setmul] THEN
  REWRITE_TAC[IN_IMAGE; RELCYCLE_GROUP; SET_RULE
   `{f x y | x IN s /\ y IN {a}} = IMAGE (\x. f x a) s`] THEN
  REWRITE_TAC[UNWIND_THM2; FRAG_MODULE
   `c2 = frag_add x c1 <=> x = frag_neg(frag_sub c1 c2)`] THEN
  REWRITE_TAC[IN; SINGULAR_RELBOUNDARY_NEG]);;

let RELATIVE_HOMOLOGY_GROUP = prove
 (`(!p top s:A->bool.
        group_carrier(relative_homology_group(&p,top,s)) =
        {homologous_rel (p,top,s) c | c | singular_relcycle (p,top,s) c}) /\
   (!p top s:A->bool.
        group_id(relative_homology_group(&p,top,s)) =
        singular_relboundary (p,top,s)) /\
   (!p top s:A->bool.
        group_inv(relative_homology_group(&p,top,s)) =
        \r. {frag_neg c | c IN r}) /\
   (!p top s:A->bool.
        group_mul(relative_homology_group(&p,top,s)) =
        \r1 r2. {frag_add c1 c2 | c1 IN r1 /\ c2 IN r2})`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
  SIMP_TAC[QUOTIENT_GROUP; RIGHT_COSET_SINGULAR_RELBOUNDARY; RELCYCLE_GROUP;
           NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[group_setinv; group_setmul; RELCYCLE_GROUP; FUN_EQ_THM]);;

let HOMOLOGOUS_REL_EQ_RELBOUNDARY = prove
 (`!p top (s:A->bool) c.
        homologous_rel(p,top,s) c = singular_relboundary(p,top,s) <=>
        singular_relboundary(p,top,s) c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; homologous_rel] THEN
  MESON_TAC[SINGULAR_RELBOUNDARY_SUB; SINGULAR_RELBOUNDARY_0;
      FRAG_MODULE `frag_sub c c:((num->real)->A)frag = frag_0`;
      FRAG_MODULE `d:((num->real)->A)frag = frag_sub c (frag_sub c d)`]);;

(* ------------------------------------------------------------------------- *)
(* Lift the boundary and induced maps to homology groups. We totalize both   *)
(* quite aggressively to the appropriate group identity in all "undefined"   *)
(* situations, which makes several of the properties cleaner and simpler.    *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_CHAIN_BOUNDARY = prove
 (`!p top s:A->bool.
     group_homomorphism (relcycle_group(p,top,s),
                         relcycle_group(p-1,subtopology top s,{}))
                        (chain_boundary p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[group_homomorphism; RELCYCLE_GROUP; CHAIN_BOUNDARY_0; SUBSET] THEN
  REWRITE_TAC[CHAIN_BOUNDARY_NEG; CHAIN_BOUNDARY_ADD; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN; singular_relcycle] THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN
  SIMP_TAC[cong; mod_subset; FRAG_MODULE `frag_sub x frag_0 = x`] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP CHAIN_BOUNDARY_BOUNDARY o CONJUNCT1) THEN
  REWRITE_TAC[SINGULAR_CHAIN_0]);;

let [HOM_BOUNDARY_DEFAULT;
     GROUP_HOMOMORPHISM_HOM_BOUNDARY; HOM_BOUNDARY_CHAIN_BOUNDARY;
     HOM_BOUNDARY_RESTRICT; HOM_BOUNDARY;
     HOM_BOUNDARY_TRIVIAL] =
  let oth = prove
   (`?d. !p (top:A topology) s.
          group_homomorphism
           (relative_homology_group (&p,top,s),
            homology_group (&(p - 1),subtopology top s))
           (d p (top,s)) /\
          !c. singular_relcycle (p,top,s) c
              ==> d p (top,s) (homologous_rel (p,top,s) c) =
                  homologous_rel (p - 1,subtopology top s,{})
                                 (chain_boundary p c)`,
    REWRITE_TAC[homology_group] THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
    REWRITE_TAC[EXISTS_CURRY] THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
    REPEAT GEN_TAC THEN MP_TAC(ISPECL
     [`relcycle_group(p,top:A topology,s)`;
      `relative_homology_group(&(p-1),subtopology top s:A topology,{})`;
      `singular_relboundary(p,top:A topology,s)`;
      `right_coset (relcycle_group(p-1,subtopology top s:A topology,{}))
                   (singular_relboundary(p - 1,subtopology top s,{})) o
       (chain_boundary p:((num->real)->A)frag->((num->real)->A)frag)`]
          QUOTIENT_GROUP_UNIVERSAL) THEN
    REWRITE_TAC[GSYM NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
    GEN_REWRITE_TAC LAND_CONV [IMP_CONJ] THEN ANTS_TAC THENL
     [MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `relcycle_group (p-1,subtopology top s:A topology,{})` THEN
      REWRITE_TAC[NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
      ASM_SIMP_TAC[GROUP_HOMOMORPHISM_RIGHT_COSET;
                   NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
      REWRITE_TAC[GROUP_HOMOMORPHISM_CHAIN_BOUNDARY];
      REWRITE_TAC[NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE]] THEN
    REWRITE_TAC[RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
    REWRITE_TAC[RELCYCLE_GROUP] THEN ANTS_TAC THENL
     [ALL_TAC; REWRITE_TAC[IN; o_THM]] THEN
    REWRITE_TAC[HOMOLOGOUS_REL_EQ; o_DEF] THEN
    REWRITE_TAC[homologous_rel; GSYM CHAIN_BOUNDARY_SUB] THEN
    MAP_EVERY X_GEN_TAC
     [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)) THEN
    SPEC_TAC(`frag_sub c1 c2:((num->real)->A)frag`,
             `c:((num->real)->A)frag`) THEN
    GEN_TAC THEN ASM_CASES_TAC `p = 0` THENL
     [ASM_REWRITE_TAC[chain_boundary; SINGULAR_RELBOUNDARY_0]; ALL_TAC] THEN
    REWRITE_TAC[singular_relboundary; SINGULAR_BOUNDARY] THEN
    ASM_SIMP_TAC[SUB_ADD; LE_1; cong; mod_subset] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:((num->real)->A)frag` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `frag_neg(frag_sub (chain_boundary (p + 1) d) c):
                ((num->real)->A)frag` THEN
    ASM_SIMP_TAC[SINGULAR_CHAIN_NEG] THEN
    REWRITE_TAC[CHAIN_BOUNDARY_SUB; CHAIN_BOUNDARY_NEG] THEN
    REWRITE_TAC[FRAG_MODULE `frag_neg(frag_sub x y) = y <=> x = frag_0`] THEN
    ASM_MESON_TAC[CHAIN_BOUNDARY_BOUNDARY_ALT]) in
  let eth = prove
   (`?d. (!p (top:A topology) s.
            group_homomorphism
             (relative_homology_group (p,top,s),
              homology_group (p - &1,subtopology top s))
             (d p (top,s))) /\
         (!p (top:A topology) s c.
              singular_relcycle (p,top,s) c /\ 1 <= p
              ==> d (&p) (top,s) (homologous_rel (p,top,s) c) =
                  homologous_rel (p - 1,subtopology top s,{})
                                 (chain_boundary p c)) /\
         (!p. p <= &0 ==> d p = \q r. ARB)`,
    MATCH_MP_TAC(MESON[]
    `(?f. P(\p. if p <= &0 then \q r. ARB else f(num_of_int p)))
     ==> ?f. P f`) THEN
    MP_TAC oth THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[INT_OF_NUM_LE; ARITH_RULE `1 <= p ==> ~(p <= 0)`;
                 NUM_OF_INT_OF_NUM] THEN
    MAP_EVERY X_GEN_TAC [`p:int`; `top:A topology`; `s:A->bool`] THEN
    COND_CASES_TAC THENL
     [ASM_SIMP_TAC[homology_group; relative_homology_group;
                   INT_ARITH `p:int <= &0 ==> p - &1 < &0`] THEN
      REWRITE_TAC[group_homomorphism; SINGLETON_GROUP] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SING];
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPECL
       [`num_of_int p`; `top:A topology`; `s:A->bool`]) THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `~(p:int <= &0) ==> &0 <= p`;
                   GSYM INT_OF_NUM_SUB; GSYM INT_OF_NUM_LE;
                   INT_ARITH `~(p:int <= &0) ==> &1 <= p`]]) in
  let fth = prove
   (`?d. (!p (top:A topology) s c.
                ~(c IN group_carrier(relative_homology_group (p,top,s)))
                ==> d p (top,s) c =
                    group_id(homology_group (p - &1,subtopology top s))) /\
         (!p (top:A topology) s.
            group_homomorphism
             (relative_homology_group (p,top,s),
              homology_group (p - &1,subtopology top s))
             (d p (top,s))) /\
         (!p (top:A topology) s c.
              singular_relcycle (p,top,s) c /\ 1 <= p
              ==> d (&p) (top,s) (homologous_rel (p,top,s) c) =
                  homologous_rel (p - 1,subtopology top s,{})
                                 (chain_boundary p c)) /\
         (!p (top:A topology) s.
                d p (top,s) = d p (top,topspace top INTER s)) /\
         (!p (top:A topology) s c.
                d p (top,s) c IN
                group_carrier(homology_group (p - &1,subtopology top s))) /\
         (!p. p <= &0 ==> d p = \q r. ARB)`,
    REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(MESON[]
     `(!x. Q x ==> R x) /\ (?x. P x /\ Q x)
      ==> ?x. (P x /\ Q x) /\ R x`) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:int` THEN
      ASM_CASES_TAC `p:int <= &0` THEN
      ASM_REWRITE_TAC[homology_group; relative_homology_group] THEN
      ASM_REWRITE_TAC[INT_ARITH `p - &1:int < &0 <=> p <= &0`] THEN
      REWRITE_TAC[FUN_EQ_THM; SINGLETON_GROUP; IN_SING] THEN
      REWRITE_TAC[FORALL_PAIR_THM];
      REWRITE_TAC[GSYM CONJ_ASSOC]] THEN
    MP_TAC eth THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INTRO_TAC "!d; hom rel triv" THEN EXISTS_TAC
     `\p (top:A topology,s) c.
         if c IN group_carrier(relative_homology_group (p,top,s))
         then d p (top,topspace top INTER s) c
         else group_id(homology_group (p - &1,subtopology top s))` THEN
    REWRITE_TAC[homology_group; GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
    REWRITE_TAC[SET_RULE `u INTER u INTER s = u INTER s`] THEN
    REWRITE_TAC[GSYM SUBTOPOLOGY_RESTRICT] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`p:int`; `top:A topology`; `s:A->bool`] THEN
      REMOVE_THEN "hom" (MP_TAC o SPECL
       [`p:int`; `top:A topology`; `topspace top INTER s:A->bool`]) THEN
      REWRITE_TAC[homology_group; GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
      REWRITE_TAC[GSYM SUBTOPOLOGY_RESTRICT] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] GROUP_HOMOMORPHISM_EQ) THEN
      SIMP_TAC[];
      REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
        STRIP_ASSUME_TAC th THEN MP_TAC th) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [SINGULAR_RELCYCLE_RESTRICT] THEN
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      REWRITE_TAC[GSYM HOMOLOGOUS_REL_RESTRICT; GSYM SUBTOPOLOGY_RESTRICT] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`p:int`; `top:A topology`; `s:A->bool`] THEN
      REMOVE_THEN "hom" (MP_TAC o SPECL
       [`p:int`; `top:A topology`; `topspace top INTER s:A->bool`]) THEN
      REWRITE_TAC[group_homomorphism; homology_group] THEN
      REWRITE_TAC[GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
      REWRITE_TAC[GSYM SUBTOPOLOGY_RESTRICT] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. (x IN s ==> f x IN t) ==> P x)
        ==> IMAGE f s SUBSET t /\ Q ==> !x. P x`) THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[GROUP_ID]]) in
  let dth = new_specification ["hom_boundary"] fth in
  CONJUNCTS dth;;

let GROUP_HOMOMORPHISM_CHAIN_MAP = prove
 (`!p top s top' t (f:A->B).
        continuous_map (top,top') f /\ IMAGE f s SUBSET t
        ==> group_homomorphism
             (relcycle_group (p,top,s),relcycle_group (p,top',t))
             (chain_map p f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_homomorphism; RELCYCLE_GROUP] THEN
  REWRITE_TAC[CHAIN_MAP_0; CHAIN_MAP_NEG; CHAIN_MAP_ADD] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN] THEN
  ASM_MESON_TAC[SINGULAR_RELCYCLE_CHAIN_MAP]);;

let [HOM_INDUCED_DEFAULT;
     GROUP_HOMOMORPHISM_HOM_INDUCED; HOM_INDUCED_CHAIN_MAP_GEN;
     HOM_INDUCED_RESTRICT; HOM_INDUCED; HOM_INDUCED_TRIVIAL] =
  let oth = prove
   (`?hom_relmap.
      (!p top s top' t (f:A->B).
          continuous_map(top,top') f /\
          IMAGE f (topspace top INTER s) SUBSET t
          ==> group_homomorphism(relative_homology_group(&p,top,s),
                                 relative_homology_group(&p,top',t))
                                (hom_relmap p (top,s) (top',t) f)) /\
      (!p top s top' t (f:A->B) c.
          continuous_map(top,top') f /\
          IMAGE f (topspace top INTER s) SUBSET t /\
          singular_relcycle (p,top,s) c
          ==> hom_relmap p (top,s) (top',t) f (homologous_rel (p,top,s) c) =
              homologous_rel (p,top',t) (chain_map p f c))`,
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[EXISTS_CURRY; GSYM SKOLEM_THM] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
    REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`relcycle_group(p,top:A topology,s)`;
      `relative_homology_group(&p,top':B topology,t)`;
      `singular_relboundary(p,top:A topology,s)`;
      `right_coset (relcycle_group(p,top',t))
                   (singular_relboundary(p,top',t)) o
       chain_map p (f:A->B)`]
          QUOTIENT_GROUP_UNIVERSAL) THEN
    REWRITE_TAC[GSYM NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
    GEN_REWRITE_TAC LAND_CONV [IMP_CONJ] THEN ANTS_TAC THENL
     [MATCH_MP_TAC GROUP_HOMOMORPHISM_COMPOSE THEN
      EXISTS_TAC `relcycle_group (p,top':B topology,t)` THEN
      REWRITE_TAC[NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
      ASM_SIMP_TAC[GROUP_HOMOMORPHISM_RIGHT_COSET;
                   NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
      ONCE_REWRITE_TAC[RELCYCLE_GROUP_RESTRICT] THEN
      MATCH_MP_TAC GROUP_HOMOMORPHISM_CHAIN_MAP THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM
       (MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      ASM SET_TAC[];
      REWRITE_TAC[NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE]] THEN
    REWRITE_TAC[RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
    REWRITE_TAC[RELCYCLE_GROUP] THEN ANTS_TAC THENL
     [ALL_TAC; REWRITE_TAC[IN; o_THM]] THEN
    REWRITE_TAC[HOMOLOGOUS_REL_EQ; o_DEF] THEN
    REWRITE_TAC[homologous_rel; GSYM CHAIN_MAP_SUB] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SINGULAR_RELBOUNDARY_CHAIN_MAP THEN
    MAP_EVERY EXISTS_TAC
     [`top:A topology`; `topspace top INTER s:A->bool`] THEN
    ASM_REWRITE_TAC[GSYM SINGULAR_RELBOUNDARY_RESTRICT]) in
  let eth = prove
   (`?hom_relmap.
      (!p top s top' t (f:A->B).
          continuous_map(top,top') f /\
          IMAGE f (topspace top INTER s) SUBSET t
          ==> group_homomorphism(relative_homology_group(p,top,s),
                                 relative_homology_group(p,top',t))
                                (hom_relmap p (top,s) (top',t) f)) /\
      (!p top s top' t (f:A->B) c.
          continuous_map(top,top') f /\
          IMAGE f (topspace top INTER s) SUBSET t /\
          singular_relcycle (p,top,s) c
          ==> hom_relmap (&p) (top,s) (top',t) f (homologous_rel (p,top,s) c) =
              homologous_rel (p,top',t) (chain_map p f c)) /\
      (!p. p < &0 ==> hom_relmap p = \q r s t. ARB)`,
    MATCH_MP_TAC(MESON[]
    `(?f. P(\p. if p < &0 then \q r s t. ARB else f(num_of_int p)))
     ==> ?f. P f`) THEN
    MP_TAC oth THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[INT_ARITH `~(&p:int < &0)`; NUM_OF_INT_OF_NUM] THEN
    MAP_EVERY X_GEN_TAC
     [`p:int`; `top:A topology`; `s:A->bool`;
      `top':B topology`; `t:B->bool`; `f:A->B`] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_REWRITE_TAC[relative_homology_group; group_homomorphism] THEN
      REWRITE_TAC[SINGLETON_GROUP] THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `num_of_int p` o CONJUNCT1) THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH
       `~(p:int < &0) ==> &0 <= p`]]) in
  let fth = prove
   (`?hom_relmap.
      (!p top s top' t (f:A->B) c.
          ~(continuous_map (top,top') f /\
            IMAGE f (topspace top INTER s) SUBSET t /\
            c IN group_carrier(relative_homology_group (p,top,s)))
          ==> hom_relmap p (top,s) (top',t) f c =
              group_id(relative_homology_group (p,top',t))) /\
      (!p top s top' t (f:A->B).
          group_homomorphism(relative_homology_group(p,top,s),
                             relative_homology_group(p,top',t))
                            (hom_relmap p (top,s) (top',t) f)) /\
      (!p top s top' t (f:A->B) c.
          continuous_map(top,top') f /\
          IMAGE f (topspace top INTER s) SUBSET t /\
          singular_relcycle (p,top,s) c
          ==> hom_relmap (&p) (top,s) (top',t) f (homologous_rel (p,top,s) c) =
              homologous_rel (p,top',t) (chain_map p f c)) /\
      (!p top s top' t.
          hom_relmap p (top,s) (top',t) =
          hom_relmap p (top,topspace top INTER s)
                       (top',topspace top' INTER t)) /\
      (!p top s top' f t c.
          hom_relmap p (top,s) (top',t) f c IN
          group_carrier(relative_homology_group(p,top',t))) /\
      (!p. p < &0 ==> hom_relmap p = \q r s t. ARB)`,
    REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(MESON[]
     `(!x. Q x ==> R x) /\ (?x. P x /\ Q x)
      ==> ?x. (P x /\ Q x) /\ R x`) THEN
    CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `p:int` THEN
      ASM_CASES_TAC `p:int < &0` THEN
      ASM_REWRITE_TAC[homology_group; relative_homology_group] THEN
      REWRITE_TAC[FUN_EQ_THM; SINGLETON_GROUP; IN_SING] THEN
      SIMP_TAC[FORALL_PAIR_THM];
      REWRITE_TAC[GSYM CONJ_ASSOC]] THEN
    MP_TAC eth THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INTRO_TAC "!hom_relmap; hom rel triv" THEN EXISTS_TAC
     `\p (top:A topology,s) (top':B topology,t) (f:A->B) c.
         if continuous_map (top,top') f /\
            IMAGE f (topspace top INTER s) SUBSET t /\
            c IN group_carrier(relative_homology_group (p,top,s))
         then hom_relmap p (top,topspace top INTER s)
                           (top',topspace top' INTER t) f c
         else group_id(relative_homology_group (p,top',t))` THEN
    REWRITE_TAC[homology_group; GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
    REWRITE_TAC[SET_RULE `u INTER u INTER s = u INTER s`] THEN
    REWRITE_TAC[GSYM SUBTOPOLOGY_RESTRICT] THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      INTRO_TAC "!p top s top' t f" THEN
      ASM_CASES_TAC ` continuous_map (top,top') (f:A->B)` THEN
      ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL] THEN
      ASM_CASES_TAC `IMAGE (f:A->B) (topspace top INTER s) SUBSET t` THEN
      ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL] THEN
      REMOVE_THEN "hom" (MP_TAC o SPECL
       [`p:int`; `top:A topology`; `topspace top INTER s:A->bool`;
        `top':B topology`; `topspace top' INTER t:B->bool`; `f:A->B`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
        REWRITE_TAC[GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] GROUP_HOMOMORPHISM_EQ) THEN
        SIMP_TAC[]];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      REMOVE_THEN "rel" (MP_TAC o SPECL
       [`p:num`; `top:A topology`; `topspace top INTER s:A->bool`;
        `top':B topology`; `topspace top' INTER t:B->bool`; `f:A->B`]) THEN
      ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
        REWRITE_TAC[GSYM SINGULAR_RELCYCLE_RESTRICT]] THEN
      SIMP_TAC[GSYM HOMOLOGOUS_REL_RESTRICT] THEN DISCH_THEN(K ALL_TAC) THEN
      GEN_TAC THEN REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM SET_TAC[];
      REPEAT GEN_TAC THEN REPEAT ABS_TAC THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[continuous_map] THEN SET_TAC[];
      INTRO_TAC "!p top s top' t f c" THEN
      COND_CASES_TAC THEN REWRITE_TAC[GROUP_ID] THEN
      REMOVE_THEN "hom" (MP_TAC o SPECL
       [`p:int`; `top:A topology`; `topspace top INTER s:A->bool`;
        `top':B topology`; `topspace top' INTER t:B->bool`; `f:A->B`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
        REWRITE_TAC[group_homomorphism] THEN
        REWRITE_TAC[GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
        ASM SET_TAC[]]]) in
  let dth = new_specification ["hom_induced"] fth in
  CONJUNCTS dth;;

let HOM_INDUCED_CHAIN_MAP = prove
 (`!p top s top' t (f:A->B) c.
        continuous_map (top,top') f /\
        IMAGE f s SUBSET t /\
        singular_relcycle (p,top,s) c
        ==> hom_induced (&p) (top,s) (top',t) f (homologous_rel (p,top,s) c) =
            homologous_rel (p,top',t) (chain_map p f c)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOM_INDUCED_CHAIN_MAP_GEN THEN
  ASM SET_TAC[]);;

let HOM_INDUCED_EQ = prove
 (`!p top s top' t (f:A->B) g.
        (!x. x IN topspace top ==> f x = g x)
        ==> hom_induced p (top,s) (top',t) f =
            hom_induced p (top,s) (top',t) g`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL [SIMP_TAC[HOM_INDUCED_TRIVIAL]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `c:((num->real)->A)frag->bool` THEN
  SUBGOAL_THEN
   `continuous_map (top,top') (f:A->B) /\
    IMAGE f (topspace top INTER s) SUBSET t /\
    c IN group_carrier (relative_homology_group (&p,top,s)) <=>
    continuous_map (top,top') (g:A->B) /\
    IMAGE g (topspace top INTER s) SUBSET t /\
    c IN group_carrier (relative_homology_group (&p,top,s))`
  MP_TAC THENL
   [BINOP_TAC THENL [ASM_MESON_TAC[CONTINUOUS_MAP_EQ]; ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `(p <=> q) <=> ~p /\ ~q \/ p /\ q`] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[HOM_INDUCED_DEFAULT]; ALL_TAC] THEN
  UNDISCH_TAC
   `c IN group_carrier (relative_homology_group (&p,top,s:A->bool))` THEN
  SPEC_TAC(`c:((num->real)->A)frag->bool`,`c:((num->real)->A)frag->bool`) THEN
  REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; FORALL_IN_GSPEC] THEN
  ONCE_REWRITE_TAC[HOMOLOGOUS_REL_RESTRICT; SINGULAR_RELCYCLE_RESTRICT] THEN
  ONCE_REWRITE_TAC[HOM_INDUCED_RESTRICT] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    HOM_INDUCED_CHAIN_MAP o lhand o snd) THEN
  ASM_REWRITE_TAC[SUBSET_INTER] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    HOM_INDUCED_CHAIN_MAP o rand o snd) THEN
  ASM_REWRITE_TAC[SUBSET_INTER] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_MAP_EQ THEN
  ASM_MESON_TAC[singular_relcycle; SINGULAR_RELCYCLE_RESTRICT]);;

(* ------------------------------------------------------------------------- *)
(* First prove we get functors into abelian groups with the boundary map     *)
(* being a natural transformation between them, and prove Eilenberg-Steenrod *)
(* axioms (we also prove additivity a bit later on if one counts that).      *)
(*                                                                           *)
(* 1. Exact sequence from the inclusions and boundary map                    *)
(*    H_{p+1}(X) --(j')--> H_{p+1}(X,A) --(d')--> H_p(A) --(i')--> H_p(X)    *)
(*                                                                           *)
(* 2. Dimension axiom: H_p(X) is trivial for one-point X and p =/= 0         *)
(*                                                                           *)
(* 3. Homotopy invariance of the induced map                                 *)
(*                                                                           *)
(* 4. Excision: inclusion (X - U,A - U) --(i')--> (X,A) induces an           *)
(*    isomorphism when cl(U) SUBSET int(A)                                   *)
(* ------------------------------------------------------------------------- *)

let ABELIAN_RELATIVE_HOMOLOGY_GROUP = prove
 (`!p top s:A->bool. abelian_group(relative_homology_group(p,top,s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[relative_homology_group] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ABELIAN_SINGLETON_GROUP] THEN
  SIMP_TAC[ABELIAN_QUOTIENT_GROUP;
           SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE; ABELIAN_RELCYCLE_GROUP]);;

let HOM_INDUCED_ID_GEN = prove
 (`!p top (f:A->A) s c.
        continuous_map(top,top) f /\
        (!x. x IN topspace top ==> f x = x) /\
        c IN group_carrier (relative_homology_group (p,top,s))
        ==> hom_induced p (top,s) (top,s) f c = c`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[relative_homology_group; SINGLETON_GROUP;
             HOM_INDUCED_TRIVIAL; IN_SING];
    ALL_TAC] THEN
  REWRITE_TAC[NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
  SIMP_TAC[QUOTIENT_GROUP; NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
  REWRITE_TAC[RELCYCLE_GROUP; IN] THEN REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOM_INDUCED_CHAIN_MAP_GEN o
    lhand o snd) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_MAP_ID_GEN THEN
  ASM_MESON_TAC[singular_relcycle; IN]);;

let HOM_INDUCED_ID = prove
 (`!p top (s:A->bool) c.
        c IN group_carrier (relative_homology_group (p,top,s))
        ==> hom_induced p (top,s) (top,s) (\x. x) c = c`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOM_INDUCED_ID_GEN THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_ID]);;

let HOM_INDUCED_COMPOSE = prove
 (`!p top s top' t top'' u (f:A->B) (g:B->C).
        continuous_map(top,top') f /\ IMAGE f s SUBSET t /\
        continuous_map(top',top'') g /\ IMAGE g t SUBSET u
        ==> hom_induced p (top,s) (top'',u) (g o f) =
            hom_induced p (top',t) (top'',u) g o
            hom_induced p (top,s) (top',t) f`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL [SIMP_TAC[HOM_INDUCED_TRIVIAL; o_DEF]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN MATCH_MP_TAC(MESON[]
   `!P. (!x. ~P x ==> Q x) /\ (!x. P x ==> Q x) ==> !x. Q x`) THEN
  EXISTS_TAC
   `\c. c IN group_carrier(relative_homology_group(&p,top:A topology,s))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[HOM_INDUCED_DEFAULT; o_DEF; REWRITE_RULE[group_homomorphism]
               GROUP_HOMOMORPHISM_HOM_INDUCED];
    REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; FORALL_IN_GSPEC; o_THM]] THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOM_INDUCED_CHAIN_MAP o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[SINGULAR_RELCYCLE_CHAIN_MAP]; DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOM_INDUCED_CHAIN_MAP o
    lhand o snd) THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]; ASM SET_TAC[]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CHAIN_MAP_COMPOSE; o_THM]]);;

let NATURALITY_HOM_INDUCED = prove
 (`!p top s top' t (f:A->B).
    continuous_map(top,top') f /\ IMAGE f s SUBSET t
    ==> hom_boundary p (top',t) o
        hom_induced p (top,s) (top',t) f =
        hom_induced (p - &1) (subtopology top s,{}) (subtopology top' t,{}) f o
        hom_boundary p (top,s)`,
  X_GEN_TAC `q:int` THEN ASM_CASES_TAC `q:int <= &0` THENL
   [ASM_SIMP_TAC[o_DEF; HOM_BOUNDARY_TRIVIAL; HOM_INDUCED_TRIVIAL; INT_ARITH
     `q:int <= &0 ==> q - &1 < &0`];
    FIRST_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `~(q:int <= &0) ==> &0 <= q /\ &1 <= q`)) THEN
    SPEC_TAC(`q:int`,`q:int`) THEN
    REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS; INT_OF_NUM_LE; LE_0] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN MATCH_MP_TAC(MESON[]
   `!P. (!x. ~P x ==> Q x) /\ (!x. P x ==> Q x) ==> !x. Q x`) THEN
  EXISTS_TAC
   `\c. c IN group_carrier(relative_homology_group(&p,top:A topology,s))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[HOM_INDUCED_DEFAULT; HOM_BOUNDARY_DEFAULT; o_DEF; homology_group;
             REWRITE_RULE[group_homomorphism] (CONJ
              GROUP_HOMOMORPHISM_HOM_INDUCED GROUP_HOMOMORPHISM_HOM_BOUNDARY)];
    REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; FORALL_IN_GSPEC; o_THM]] THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HOM_BOUNDARY_CHAIN_BOUNDARY; HOM_INDUCED_CHAIN_MAP] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOM_BOUNDARY_CHAIN_BOUNDARY o
    lhand o snd) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SINGULAR_RELCYCLE_CHAIN_MAP]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[INT_OF_NUM_SUB] THEN
  FIRST_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
    REWRITE_RULE[singular_relcycle]) THEN
  SIMP_TAC[cong; mod_subset; FRAG_MODULE `frag_sub x frag_0 = x`] THEN
  DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) HOM_INDUCED_CHAIN_MAP o
    rand o snd) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; SUBSET_REFL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[SINGULAR_CYCLE] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[CHAIN_BOUNDARY_BOUNDARY]] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_BOUNDARY_CHAIN_MAP THEN
  ASM_MESON_TAC[]);;

let HOMOLOGY_EXACTNESS_AXIOM_1 = prove
 (`!p top s:A->bool.
        group_exactness(homology_group(p,top),
                        relative_homology_group(p,top,s),
                        homology_group(p - &1,subtopology top s))
                       (hom_induced p (top,{}) (top,s) (\x. x),
                        hom_boundary p (top,s))`,
  REWRITE_TAC[group_exactness; GROUP_HOMOMORPHISM_HOM_BOUNDARY] THEN
  SIMP_TAC[homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED;
           CONTINUOUS_MAP_ID; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  REWRITE_TAC[group_image; group_kernel] THEN
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[relative_homology_group; SINGLETON_GROUP; HOM_INDUCED_TRIVIAL;
             HOM_BOUNDARY_TRIVIAL; INT_ARITH
              `q:int < &0 ==> q <= &0 /\ q - &1 < &0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [SIMP_TAC[HOM_BOUNDARY_TRIVIAL; INT_LE_REFL] THEN
    SIMP_TAC[relative_homology_group; INT_ARITH `&0 - &1:int < &0`] THEN
    REWRITE_TAC[GSYM relative_homology_group; SINGLETON_GROUP] THEN
    REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
     `s = {x | x IN t} <=> s SUBSET t /\ t SUBSET s`] THEN
    MP_TAC(ISPECL [`&0:int`; `top:A topology`; `{}:A->bool`;
                   `top:A topology`; `s:A->bool`; `\x:A. x`]
          GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
    REWRITE_TAC[CONTINUOUS_MAP_ID; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
    SIMP_TAC[group_homomorphism; homology_group] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[SUBSET; RELATIVE_HOMOLOGY_GROUP; IN_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `c:((num->real)->A)frag` THEN
    REWRITE_TAC[singular_relcycle] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `c:((num->real)->A)frag` THEN
    ASM_REWRITE_TAC[singular_relcycle; chain_boundary; MOD_SUBSET_REFL] THEN
    ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP; CONTINUOUS_MAP_ID; IMAGE_CLAUSES;
        EMPTY_SUBSET; singular_relcycle; chain_boundary; MOD_SUBSET_REFL] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CHAIN_MAP_ID THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_THEN(K ALL_TAC) THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `(p + &1) - &1:int = p`] THEN
  REWRITE_TAC[INT_OF_NUM_ADD; RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[SET_RULE
     `{x | x IN {f y | P y} /\ Q x} = {f y |y| P y /\ Q(f y)}`] THEN
  REWRITE_TAC[SET_RULE `IMAGE g {f y | P y} = { g(f y) | P y}`] THEN
  TRANS_TAC EQ_TRANS
   `{ homologous_rel (p+1,top:A topology,s) c | c |
      singular_relcycle (p+1,top,{}) c}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP; CONTINUOUS_MAP_ID; IMAGE_CLAUSES;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY; EMPTY_SUBSET] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_MAP_ID THEN
    ASM_MESON_TAC[singular_relcycle];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `{ homologous_rel (p+1,top:A topology,s) c | c |
      singular_relcycle (p+1,top,s) c /\
      singular_relboundary (p,subtopology top s,{})
                           (chain_boundary (p+1) c)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> (Q x <=> R x))
      ==> {f x | P x /\ Q x} = {f x | P x /\ R x}`) THEN
    SIMP_TAC[HOM_BOUNDARY_CHAIN_BOUNDARY; ARITH_RULE `1 <= p + 1`] THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[ETA_AX; ADD_SUB; HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
    REWRITE_TAC[SINGULAR_BOUNDARY]] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. P x ==> ?y. Q y /\ f x = f y) /\
    (!x. Q x ==> ?y. P y /\ f x = f y)
    ==> {f x | P x} = {f x | Q x}`) THEN
  REWRITE_TAC[HOMOLOGOUS_REL_EQ] THEN CONJ_TAC THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN STRIP_TAC THENL
   [EXISTS_TAC `c:((num->real)->A)frag` THEN
    REWRITE_TAC[HOMOLOGOUS_REL_REFL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SINGULAR_CYCLE]) THEN
    ASM_REWRITE_TAC[SINGULAR_RELBOUNDARY_0; singular_relcycle] THEN
    REWRITE_TAC[cong; mod_subset; FRAG_MODULE `frag_sub x x = frag_0`] THEN
    REWRITE_TAC[SINGULAR_CHAIN_0];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SINGULAR_BOUNDARY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:((num->real)->A)frag` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `frag_sub c d:((num->real)->A)frag` THEN
    ASM_REWRITE_TAC[SINGULAR_CYCLE] THEN
    ASM_REWRITE_TAC[CHAIN_BOUNDARY_SUB; FRAG_MODULE
     `frag_sub x x = frag_0`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN
      CONJ_TAC THENL [ASM_MESON_TAC[singular_relcycle]; ALL_TAC] THEN
      ASM_MESON_TAC[SINGULAR_CHAIN_SUBTOPOLOGY];
      REWRITE_TAC[homologous_rel; singular_relboundary] THEN
      EXISTS_TAC `frag_0:((num->real)->A)frag` THEN
      REWRITE_TAC[SINGULAR_CHAIN_0; CHAIN_BOUNDARY_0] THEN
      ASM_REWRITE_TAC[cong; mod_subset; SINGULAR_CHAIN_NEG; FRAG_MODULE
       `frag_sub frag_0 (frag_sub c (frag_sub c d)) = frag_neg d`]]]);;

let HOMOLOGY_EXACTNESS_AXIOM_2 = prove
 (`!p top s:A->bool.
      group_exactness(relative_homology_group(p,top,s),
                      homology_group(p - &1,subtopology top s),
                      homology_group(p - &1,top))
               (hom_boundary p (top,s),
                hom_induced (p - &1) (subtopology top s,{}) (top,{}) (\x. x))`,
  REWRITE_TAC[group_exactness; GROUP_HOMOMORPHISM_HOM_BOUNDARY] THEN
  SIMP_TAC[homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED;
           CONTINUOUS_MAP_FROM_SUBTOPOLOGY; GROUP_HOMOMORPHISM_HOM_BOUNDARY;
           CONTINUOUS_MAP_ID; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  REWRITE_TAC[group_image; group_kernel] THEN
  X_GEN_TAC `q:int` THEN ASM_CASES_TAC `q:int <= &0` THENL
   [ASM_SIMP_TAC[HOM_BOUNDARY_TRIVIAL; HOM_INDUCED_TRIVIAL; INT_ARITH
     `q:int <= &0 ==> q - &1 < &0`; relative_homology_group] THEN
    REWRITE_TAC[GSYM relative_homology_group; SINGLETON_GROUP] THEN
    REPEAT GEN_TAC THEN MATCH_MP_TAC(SET_RULE
    `(?x. x IN s) ==> IMAGE (\x. a) s = {x | x IN {a}}`) THEN
    MESON_TAC[GROUP_ID];
    FIRST_ASSUM(MP_TAC o MATCH_MP (INT_ARITH
     `~(q:int <= &0) ==> &0 <= q /\ &1 <= q`)) THEN
    SPEC_TAC(`q:int`,`q:int`) THEN
    REWRITE_TAC[IMP_CONJ; GSYM INT_FORALL_POS; INT_OF_NUM_LE; LE_0] THEN
    MATCH_MP_TAC num_INDUCTION THEN CONV_TAC NUM_REDUCE_CONV] THEN
  X_GEN_TAC `p:num` THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `(p + &1) - &1:int = p`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[INT_OF_NUM_ADD] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[SET_RULE
     `{x | x IN {f y | P y} /\ Q x} = {f y |y| P y /\ Q(f y)}`] THEN
  REWRITE_TAC[SET_RULE `IMAGE g {f y | P y} = { g(f y) | P y}`] THEN
  TRANS_TAC EQ_TRANS
   `{ homologous_rel (p,subtopology top s,{}) (chain_boundary (p + 1) c) | c |
      singular_relcycle (p+1,top:A topology,s) c}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[HOM_BOUNDARY_CHAIN_BOUNDARY; ADD_SUB;
                 ARITH_RULE `1 <= p + 1`] THEN
    REWRITE_TAC[FUN_EQ_THM];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `{ homologous_rel (p,subtopology top s:A topology,{}) c | c |
      singular_relcycle (p,subtopology top s,{}) c /\
      singular_relboundary (p,top,{}) c}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> (Q x <=> R x))
      ==> {f x | P x /\ Q x} = {f x | P x /\ R x}`) THEN
    SIMP_TAC[HOM_INDUCED_CHAIN_MAP; CONTINUOUS_MAP_ID; IMAGE_CLAUSES;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY; EMPTY_SUBSET] THEN
    REWRITE_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CHAIN_MAP_ID THEN ASM_MESON_TAC[singular_relcycle]] THEN
  REWRITE_TAC[SINGULAR_BOUNDARY] THEN
  REWRITE_TAC[SET_RULE
   `{f x | P x /\ ?y. Q y /\ g y = x} = {f(g z) |z| Q z /\ P(g z)}`] THEN
  REWRITE_TAC[SINGULAR_CYCLE] THEN
  REWRITE_TAC[singular_relcycle; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. P x ==> (Q x <=> R x))
    ==> {f x | P x /\ Q x} = {f x | P x /\ R x}`) THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CHAIN_BOUNDARY_BOUNDARY_ALT) THEN
  REWRITE_TAC[ADD_SUB; cong; mod_subset; FRAG_MODULE
   `frag_sub x frag_0 = x`]);;

let HOMOLOGY_EXACTNESS_AXIOM_3 = prove
 (`!p top s:A->bool.
        group_exactness(homology_group(p,subtopology top s),
                        homology_group(p,top),
                        relative_homology_group(p,top,s))
                       (hom_induced p (subtopology top s,{}) (top,{}) (\x. x),
                        hom_induced p (top,{}) (top,s) (\x. x))`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[group_exactness; homology_group; relative_homology_group;
             HOM_INDUCED_TRIVIAL; group_image; group_kernel;
             group_homomorphism; SINGLETON_GROUP] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[homology_group; group_exactness] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
  REWRITE_TAC[group_image; group_kernel; RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[SET_RULE
   `{x | x IN {f y | P y} /\ Q x} = {f y |y| P y /\ Q(f y)}`] THEN
  REWRITE_TAC[SET_RULE `IMAGE g {f y | P y} = { g(f y) | P y}`] THEN
  TRANS_TAC EQ_TRANS
   `{ homologous_rel (p,top:A topology,{}) c | c |
      singular_relcycle (p,subtopology top s,{}) c}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP; CONTINUOUS_MAP_ID; IMAGE_CLAUSES;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY; EMPTY_SUBSET] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_MAP_ID THEN
    ASM_MESON_TAC[singular_relcycle];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `{ homologous_rel (p,top:A topology,{}) c | c |
      singular_relcycle (p,top,{}) c /\
      singular_relboundary (p,top,s) c}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> (Q x <=> R x))
      ==> {f x | P x /\ Q x} = {f x | P x /\ R x}`) THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP; CONTINUOUS_MAP_ID;
                 IMAGE_CLAUSES; EMPTY_SUBSET] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_MAP_ID THEN
    ASM_MESON_TAC[singular_relcycle]] THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. P x ==> ?y. Q y /\ f x = f y) /\
    (!x. Q x ==> ?y. P y /\ f x = f y)
    ==> {f x | P x} = {f x | Q x}`) THEN
  REWRITE_TAC[HOMOLOGOUS_REL_EQ] THEN CONJ_TAC THEN
  X_GEN_TAC `c:((num->real)->A)frag` THEN STRIP_TAC THENL
   [EXISTS_TAC `c:((num->real)->A)frag` THEN
    REWRITE_TAC[HOMOLOGOUS_REL_REFL] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM SUBTOPOLOGY_TOPSPACE] THEN
      MATCH_MP_TAC SINGULAR_CYCLE_MONO THEN
      EXISTS_TAC `topspace top INTER s:A->bool` THEN
      REWRITE_TAC[INTER_SUBSET; GSYM SUBTOPOLOGY_RESTRICT] THEN
      ASM_REWRITE_TAC[GSYM SINGULAR_CYCLE];
      MATCH_MP_TAC SINGULAR_CHAIN_IMP_RELBOUNDARY THEN
      ASM_MESON_TAC[singular_relcycle]];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SINGULAR_RELBOUNDARY_ALT]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`e:((num->real)->A)frag`; `d:((num->real)->A)frag`] THEN
    STRIP_TAC THEN EXISTS_TAC `frag_neg d:((num->real)->A)frag` THEN
    REWRITE_TAC[homologous_rel; SINGULAR_RELCYCLE_NEG; FRAG_MODULE
     `frag_sub c (frag_neg d) = frag_add c d`] THEN
    CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[SINGULAR_CYCLE]) THEN
      ASM_REWRITE_TAC[SINGULAR_CYCLE] THEN
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP (FRAG_MODULE
        `e = frag_add c d ==> d = frag_sub e c`)) THEN
      ASM_REWRITE_TAC[CHAIN_BOUNDARY_SUB] THEN
      REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`] THEN
      ASM_MESON_TAC[CHAIN_BOUNDARY_BOUNDARY_ALT];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SINGULAR_BOUNDARY] THEN
      ASM_MESON_TAC[]]]);;

let HOMOLOGY_DIMENSION_AXIOM = prove
 (`!p top (a:A).
        topspace top = {a} /\ ~(p = &0)
        ==> trivial_group(homology_group(p,top))`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  SIMP_TAC[homology_group; INT_OF_NUM_EQ; TRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[trivial_group] THEN
  REWRITE_TAC[SET_RULE `s = {a} <=> a IN s /\ !b. b IN s ==> b = a`] THEN
  REWRITE_TAC[GROUP_ID] THEN REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
  ASM_MESON_TAC[SINGULAR_BOUNDARY_EQ_CYCLE_SING; LE_1]);;

let HOMOLOGY_HOMOTOPY_AXIOM = prove
 (`!p top s top' t (f:A->B) g.
           homotopic_with (\h. IMAGE h s SUBSET t) (top,top') f g
           ==> hom_induced p (top,s) (top',t) f =
               hom_induced p (top,s) (top',t) g`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  SIMP_TAC[HOM_INDUCED_TRIVIAL] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [FUN_EQ_THM] THEN MATCH_MP_TAC(MESON[]
   `!P. (!x. ~P x ==> Q x) /\ (!x. P x ==> Q x) ==> !x. Q x`) THEN
  EXISTS_TAC
   `\c. c IN group_carrier(relative_homology_group(&p,top:A topology,s))` THEN
  SIMP_TAC[HOM_INDUCED_DEFAULT] THEN
  REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[RELCYCLE_GROUP; IN] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_PROPERTY) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP] THEN
  REWRITE_TAC[HOMOLOGOUS_REL_EQ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPIC_IMP_HOMOLOGOUS_REL_CHAIN_MAPS THEN
  ASM_MESON_TAC[]);;

let HOMOLOGY_EXCISION_AXIOM = prove
 (`!p top s t (u:A->bool).
        top closure_of u SUBSET top interior_of t /\ t SUBSET s
        ==> group_isomorphism
             (relative_homology_group(p,subtopology top (s DIFF u),t DIFF u),
              relative_homology_group(p,subtopology top s,t))
             (hom_induced p (subtopology top (s DIFF u),t DIFF u)
                            (subtopology top s,t) (\x. x))`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[relative_homology_group; HOM_INDUCED_TRIVIAL] THEN
    REWRITE_TAC[GROUP_ISOMORPHISM; group_homomorphism; SINGLETON_GROUP] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GROUP_ISOMORPHISM] THEN
  REWRITE_TAC[group_homomorphism; SET_RULE
   `(IMAGE f s SUBSET t /\ P) /\ IMAGE f s = t /\ Q <=>
    (IMAGE f s SUBSET t /\ P) /\ t SUBSET IMAGE f s /\ Q`] THEN
  REWRITE_TAC[GSYM group_homomorphism] THEN
  SUBGOAL_THEN
   `continuous_map (subtopology top (s DIFF u),subtopology top s) (\x. x) /\
    IMAGE (\x:A. x) (t DIFF u) SUBSET t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    ONCE_REWRITE_TAC[SET_RULE `s DIFF u = s INTER (s DIFF u)`] THEN
    SIMP_TAC[GSYM SUBTOPOLOGY_SUBTOPOLOGY; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
             CONTINUOUS_MAP_ID];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
    SIMP_TAC[QUOTIENT_GROUP;
             NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN
    GEN_REWRITE_TAC LAND_CONV [IN] THEN
    REWRITE_TAC[RELCYCLE_GROUP] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN MP_TAC(ISPECL
     [`p:num`; `top:A topology`; `s:A->bool`; `t:A->bool`; `u:A->bool`;
      `c:((num->real)->A)frag`] EXCISED_RELCYCLE_EXISTS) THEN
    ASM_REWRITE_TAC[IN] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:((num->real)->A)frag` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP] THEN
    FIRST_X_ASSUM(SUBST1_TAC o
      GEN_REWRITE_RULE I [GSYM HOMOLOGOUS_REL_EQ]) THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CHAIN_MAP_ID THEN ASM_MESON_TAC[singular_relcycle];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[NONTRIVIAL_RELATIVE_HOMOLOGY_GROUP] THEN
    SIMP_TAC[QUOTIENT_GROUP;
             NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
    REWRITE_TAC[RELCYCLE_GROUP; IN] THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN DISCH_TAC THEN
    X_GEN_TAC `d:((num->real)->A)frag` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP] THEN
    SUBGOAL_THEN
     `singular_chain(p,subtopology top (s DIFF u:A->bool)) c /\
      singular_chain(p,subtopology top (s DIFF u)) d`
    MP_TAC THENL [ASM_MESON_TAC[singular_relcycle]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o MATCH_MP CHAIN_MAP_ID)) THEN
    REWRITE_TAC[HOMOLOGOUS_REL_EQ] THEN
    REWRITE_TAC[homologous_rel] THEN MAP_EVERY UNDISCH_TAC
     [`singular_relcycle (p,subtopology top (s DIFF u:A->bool),t DIFF u) d`;
      `singular_relcycle
        (p,subtopology top (s DIFF u:A->bool),t DIFF u) c`] THEN
    GEN_REWRITE_TAC I [IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SINGULAR_RELCYCLE_SUB) THEN
    SPEC_TAC(`frag_sub c d:((num->real)->A)frag`,
             `c:((num->real)->A)frag`) THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN
    REWRITE_TAC[singular_relcycle; cong; mod_subset] THEN
    REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`] THEN
    ASM_SIMP_TAC[SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE
     `t SUBSET s ==> (s DIFF u) INTER (t DIFF u) = t DIFF u`] THEN
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [SINGULAR_RELBOUNDARY_ALT] THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; SUBTOPOLOGY_SUBTOPOLOGY; SET_RULE
     `t SUBSET s ==> s INTER t = t`] THEN
    MAP_EVERY X_GEN_TAC
     [`d:((num->real)->A)frag`; `e:((num->real)->A)frag`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`p + 1`; `top:A topology`; `s:A->bool`; `t:A->bool`; `u:A->bool`;
      `d:((num->real)->A)frag`] EXCISED_CHAIN_EXISTS) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`n:num`; `f:((num->real)->A)frag`; `g:((num->real)->A)frag`] THEN
    STRIP_TAC THEN
    X_CHOOSE_THEN `h:num->((num->real)->A)frag->((num->real)->A)frag` MP_TAC
     (SPEC `n:num` CHAIN_HOMOTOPIC_ITERATED_SINGULAR_SUBDIVISION) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`p + 1`; `subtopology top (s:A->bool)`; `d:((num->real)->A)frag`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM
     `chain_boundary (p + 1):((num->real)->A)frag->((num->real)->A)frag`) THEN
    REWRITE_TAC[CHAIN_BOUNDARY_ADD; CHAIN_BOUNDARY_SUB] THEN
    MP_TAC(ISPECL [`p + 1`; `subtopology top s:A topology`]
        CHAIN_BOUNDARY_BOUNDARY_ALT) THEN
    ASM_SIMP_TAC[FRAG_MODULE `frag_add frag_0 c = c`; ADD_SUB] THEN
    DISCH_THEN(K ALL_TAC) THEN
    SUBST1_TAC(FRAG_MODULE
     `frag_add c e:((num->real)->A)frag = frag_sub c (frag_sub frag_0 e)`) THEN
    ASM_REWRITE_TAC[CHAIN_BOUNDARY_SUB; CHAIN_BOUNDARY_0] THEN
    REWRITE_TAC[FRAG_MODULE
     `frag_sub x (frag_sub frag_0 y) = frag_add x y`] THEN
    REWRITE_TAC[FRAG_MODULE
     `frag_add c' e' = frag_sub (frag_add f g) (frag_add c e) <=>
      c = frag_add (frag_sub f c') (frag_sub (frag_sub g e) e')`] THEN
    REWRITE_TAC[GSYM CHAIN_BOUNDARY_SUB] THEN
    ONCE_REWRITE_TAC[FRAG_MODULE
     `c = frag_add c1 (frag_sub c2 c3) <=>
      c1 = frag_add c (frag_sub c3 c2)`] THEN
    REWRITE_TAC[SINGULAR_RELBOUNDARY_ALT] THEN
    MAP_EVERY ABBREV_TAC
     [`c1 =
       frag_sub f ((h:num->((num->real)->A)frag->((num->real)->A)frag) p c)`;
      `c2:((num->real)->A)frag =
       frag_sub (chain_boundary (p + 1) (h p e))
                (frag_sub (chain_boundary (p + 1) g) e)`] THEN
    DISCH_TAC THEN REWRITE_TAC[SINGULAR_RELBOUNDARY_ALT] THEN
    MAP_EVERY EXISTS_TAC
     [`c1:((num->real)->A)frag`; `c2:((num->real)->A)frag`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SINGULAR_CHAIN_SUB]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `singular_chain (p,subtopology top (s DIFF u:A->bool)) c2 /\
      singular_chain (p,subtopology top t) c2`
    MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (FRAG_MODULE
         `c1 = frag_add c c2 ==> c2 = frag_sub c1 c`)) THEN
        MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SINGULAR_CHAIN_BOUNDARY; ADD_SUB];
        EXPAND_TAC "c2" THEN
        REPEAT(MATCH_MP_TAC SINGULAR_CHAIN_SUB THEN CONJ_TAC) THEN
        ASM_MESON_TAC[SINGULAR_CHAIN_BOUNDARY; ADD_SUB]];
      REWRITE_TAC[SINGULAR_CHAIN_SUBTOPOLOGY] THEN ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Additivity axiom; not in the original Eilenberg-Steenrod list but usually *)
(* included nowadays, following Milnor's "On Axiomatic Homology Theory".     *)
(* ------------------------------------------------------------------------- *)

let GROUP_ISOMORPHISM_CHAIN_GROUP_SUM = prove
 (`!p top u:(A->bool)->bool.
     pairwise DISJOINT u /\ UNIONS u = topspace top /\
     (!c t. compact_in top c /\ path_connected_in top c /\
            t IN u /\ ~(DISJOINT c t)
            ==> c SUBSET t)
     ==> group_isomorphism (sum_group u (\s. chain_group(p,subtopology top s)),
                            chain_group(p,top))
                           (iterate frag_add u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chain_group] THEN
  W(MP_TAC o PART_MATCH (lhand o lhand o rand)
        GROUP_ISOMORPHISM_FREE_ABELIAN_GROUP_SUM o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[pairwise] THEN
    MAP_EVERY X_GEN_TAC [`s:A->bool`; `t:A->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. s x /\ t x ==> F`] THEN
    X_GEN_TAC `f:(num->real)->A` THEN
    REWRITE_TAC[SINGULAR_SIMPLEX_SUBTOPOLOGY] THEN
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o CONJUNCT2)) THEN MATCH_MP_TAC(SET_RULE
     `DISJOINT s t /\ ~(p = {})
      ==> IMAGE f p SUBSET t ==> IMAGE f p SUBSET s ==> F`) THEN
    REWRITE_TAC[NONEMPTY_STANDARD_SIMPLEX] THEN
    ASM_MESON_TAC[pairwise];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    REPLICATE_TAC 3 AP_TERM_TAC THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET] THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; SUBSET; SET_RULE
     `c IN singular_simplex (p,top) <=> singular_simplex (p,top) c`] THEN
    SIMP_TAC[SINGULAR_SIMPLEX_SUBTOPOLOGY] THEN
    X_GEN_TAC `f:(num->real)->A` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
     [GSYM SUBTOPOLOGY_TOPSPACE] THEN
    REWRITE_TAC[SINGULAR_SIMPLEX_SUBTOPOLOGY] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o MATCH_MP (SET_RULE
     `IMAGE f p SUBSET s ==> ~(p = {})
      ==> ?x. x IN s /\ x IN IMAGE f p`))) THEN
    REWRITE_TAC[NONEMPTY_STANDARD_SIMPLEX] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXISTS_IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:A->bool` THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; SET_RULE
     `(?x. x IN t /\ x IN s) <=> ~(DISJOINT s t)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_COMPACT_IN;
      MATCH_MP_TAC PATH_CONNECTED_IN_CONTINUOUS_MAP_IMAGE] THEN
    EXISTS_TAC `subtopology (product_topology (:num) (\i. euclideanreal))
                            (standard_simplex p)` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[singular_simplex]) THEN
    ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; PATH_CONNECTED_IN_SUBTOPOLOGY;
        COMPACT_IN_STANDARD_SIMPLEX; PATH_CONNECTED_IN_STANDARD_SIMPLEX;
        SUBSET_REFL]]);;

let GROUP_ISOMORPHISM_CYCLE_GROUP_SUM = prove
 (`!p top u:(A->bool)->bool.
     pairwise DISJOINT u /\ UNIONS u = topspace top /\
     (!c t. compact_in top c /\ path_connected_in top c /\
            t IN u /\ ~(DISJOINT c t)
            ==> c SUBSET t)
     ==> group_isomorphism
          (sum_group u (\t. relcycle_group(p,subtopology top t,{})),
           relcycle_group(p,top,{}))
          (iterate frag_add u)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [SUBGOAL_THEN
     `!top:A topology. relcycle_group(p,top,{}) = chain_group(p,top)`
      (fun th -> REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[GROUPS_EQ; RELCYCLE_GROUP; CHAIN_GROUP] THEN
      REWRITE_TAC[FUN_EQ_THM; SINGULAR_CYCLE] THEN
      ASM_REWRITE_TAC[chain_boundary];
      MATCH_MP_TAC GROUP_ISOMORPHISM_CHAIN_GROUP_SUM THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[relcycle_group] THEN
  SIMP_TAC[SUM_GROUP_SUBGROUP_GENERATED; SUBGROUP_SINGULAR_RELCYCLE] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
   [SUBGROUP_GENERATED_RESTRICT] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_BETWEEN_SUBGROUPS THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC GROUP_ISOMORPHISM_CHAIN_GROUP_SUM THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[group_isomorphism; group_isomorphisms; group_homomorphism;
                LEFT_IMP_EXISTS_THM]] THEN
  GEN_TAC THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET u /\ t SUBSET v /\
    (!x. x IN u ==> (f x IN t <=> x IN s))
    ==> (IMAGE f u SUBSET v /\ P) /\ (IMAGE f' v SUBSET u /\ Q) /\
        (!x. x IN u ==> f'(f x) = x) /\ (!y. y IN v ==> f(f' y) = y)
        ==> IMAGE f s = t`) THEN
  SIMP_TAC[INTER_SUBSET; IN_INTER] THEN CONJ_TAC THENL
   [REWRITE_TAC[CHAIN_GROUP; SUBSET; IN] THEN SIMP_TAC[SINGULAR_CYCLE];
    X_GEN_TAC `z:(A->bool)->((num->real)->A)frag`] THEN
  REWRITE_TAC[SUM_GROUP_CLAUSES; cartesian_product;
              IN_ELIM_THM; CHAIN_GROUP] THEN
  REWRITE_TAC[SET_RULE `z IN singular_relcycle q <=> singular_relcycle q z`;
              SET_RULE `z IN singular_chain q <=> singular_chain q z`] THEN
  REWRITE_TAC[SINGULAR_CYCLE] THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_FRAG_ADD] THEN
  MATCH_MP_TAC(TAUT `p /\ (q <=> r) ==> (p /\ q <=> r)`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SINGULAR_CHAIN_SUM THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SINGULAR_CHAIN_SUBTOPOLOGY]) THEN
    ASM_SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[CHAIN_BOUNDARY_SUM]] THEN
  MP_TAC(ISPECL [`p - 1`; `top:A topology`; `u:(A->bool)->bool`]
        GROUP_ISOMORPHISM_CHAIN_GROUP_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_IMP_MONOMORPHISM) THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_ALT_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC
   `RESTRICTION u (chain_boundary p o (z:(A->bool)->((num->real)->A)frag))` o
   CONJUNCT2) THEN
  REWRITE_TAC[SUM_GROUP_CLAUSES; CHAIN_GROUP; RESTRICTION_EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; RESTRICTION_IN_CARTESIAN_PRODUCT; o_THM] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[IN] THEN
      ASM_SIMP_TAC[SINGULAR_CHAIN_BOUNDARY];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:A->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[CONTRAPOS_THM; RESTRICTION; o_THM] THEN
      SIMP_TAC[CHAIN_BOUNDARY_0]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(MESON[]
     `iterate f u (RESTRICTION u x) = iterate f u x /\ iterate f u x = y
      ==> y = iterate f u (RESTRICTION u x)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(MATCH_MP ITERATE_EQ MONOIDAL_FRAG_ADD) THEN
      SIMP_TAC[RESTRICTION];
      MATCH_MP_TAC(MATCH_MP ITERATE_SUPERSET MONOIDAL_FRAG_ADD) THEN
      SIMP_TAC[SUBSET_RESTRICT; IN_ELIM_THM; IMP_CONJ] THEN
      SIMP_TAC[o_THM; NEUTRAL_FRAG_ADD; CHAIN_BOUNDARY_0]]]);;

let HOMOLOGY_ADDITIVITY_AXIOM_GEN = prove
 (`!p top u:(A->bool)->bool.
     pairwise DISJOINT u /\ UNIONS u = topspace top /\
     (!c t. compact_in top c /\ path_connected_in top c /\
            t IN u /\ ~(DISJOINT c t)
            ==> c SUBSET t)
     ==> group_isomorphism
          (sum_group u (\s. homology_group(p,subtopology top s)),
           homology_group(p,top))
          (\x. iterate (group_add (homology_group(p,top))) u
           (\v. hom_induced p (subtopology top v,{}) (top,{}) (\z. z) (x v)))`,
  MATCH_MP_TAC(MESON[INT_OF_NUM_OF_INT; INT_NOT_LT]
   `(!x. x < &0 ==> P x) /\ (!p. P(&p)) ==> !x:int. P x`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[homology_group; relative_homology_group] THEN
    ASM_SIMP_TAC[HOM_INDUCED_TRIVIAL] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[GSYM ITERATE_SUPPORT] THEN
    REWRITE_TAC[support; NEUTRAL_GROUP_ADD; SINGLETON_GROUP; EMPTY_GSPEC] THEN
    SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_GROUP_ADD; ABELIAN_SINGLETON_GROUP] THEN
    REWRITE_TAC[NEUTRAL_GROUP_ADD; GROUP_ISOMORPHISM_TRIVIAL] THEN
    REWRITE_TAC[TRIVIAL_GROUP_SINGLETON_GROUP] THEN
    REWRITE_TAC[sum_group] THEN
    MATCH_MP_TAC TRIVIAL_GROUP_SUBGROUP_GENERATED THEN
    REWRITE_TAC[TRIVIAL_PRODUCT_GROUP; TRIVIAL_GROUP_SINGLETON_GROUP];
    REPEAT STRIP_TAC] THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM;
              GROUP_EPIMORPHISM_ALT; GROUP_MONOMORPHISM_ALT] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q /\ r) ==> (p /\ q) /\ (p /\ r)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABELIAN_GROUP_HOMOMORPHISM_GROUP_SUM THEN
    REWRITE_TAC[homology_group; ETA_AX; ABELIAN_RELATIVE_HOMOLOGY_GROUP] THEN
    REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED];
    DISCH_TAC] THEN
  REWRITE_TAC[group_image] THEN
  SUBGOAL_THEN
   `group_carrier(sum_group u
       (\s:A->bool. homology_group (&p,subtopology top s))) =
    IMAGE (\x. RESTRICTION u
                  (\s. homologous_rel (p,subtopology top s,{}) (x s)))
          (group_carrier
            (sum_group u (\s. relcycle_group(p,subtopology top s,{}))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP; SUM_GROUP_CLAUSES; homology_group] THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN
    REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
      SIMP_TAC[RESTRICTION; HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
      REWRITE_TAC[RELCYCLE_GROUP] THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_AND THEN
      CONJ_TAC THENL [MESON_TAC[IN]; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; NOT_IMP] THEN
      MESON_TAC[SINGULAR_RELBOUNDARY_0]] THEN
    X_GEN_TAC `z:(A->bool)->((num->real)->A)frag->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
    REWRITE_TAC[SKOLEM_THM; IN_IMAGE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `c:(A->bool)->((num->real)->A)frag` THEN STRIP_TAC THEN
    EXISTS_TAC `RESTRICTION u
     (\s. if singular_relboundary (p,subtopology top s,{}) (c s)
          then frag_0
          else (c:(A->bool)->((num->real)->A)frag) s)` THEN
    REWRITE_TAC[IN_ELIM_THM; REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`] THEN
    SIMP_TAC[RESTRICTION] THEN REPEAT CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[EXTENSIONAL; IN_ELIM_THM]) THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[HOMOLOGOUS_REL_EQ] THEN
      ASM_REWRITE_TAC[homologous_rel; FRAG_MODULE `frag_sub c frag_0 = c`];
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[RELCYCLE_GROUP; IN] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[SINGULAR_RELCYCLE_0];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; NOT_IMP; IN_ELIM_THM] THEN
      GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_SIMP_TAC[CONTRAPOS_THM] THEN
      SIMP_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
      REWRITE_TAC[RELCYCLE_GROUP]];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN REWRITE_TAC[SET_RULE
   `t SUBSET IMAGE f s <=> !y. y IN t ==> ~(!x. x IN s ==> ~(f x = y))`] THEN
  SUBGOAL_THEN
   `!x. x IN group_carrier
          (sum_group u (\s. relcycle_group (p,subtopology top s,{})))
        ==> iterate (group_add (homology_group (&p,top))) u
             (\v. hom_induced (&p) (subtopology top v,{}) (top,{}) (\z:A. z)
                  (RESTRICTION u
                   (\s. homologous_rel (p,subtopology top s,{}) (x s)) v)) =
            homologous_rel(p,top,{}) (iterate frag_add u x)`
   (fun th -> SIMP_TAC[th])
  THENL
   [REWRITE_TAC[SUM_GROUP_CLAUSES; cartesian_product; IN_ELIM_THM] THEN
    REWRITE_TAC[RELCYCLE_GROUP; SET_RULE
     `x IN singular_relcycle q <=> singular_relcycle q x`] THEN
    X_GEN_TAC `z:(A->bool)->((num->real)->A)frag` THEN STRIP_TAC THEN
    TRANS_TAC EQ_TRANS
     `iterate (group_add (homology_group (&p,top:A topology))) u
              (\s:A->bool. homologous_rel (p,top,{}) (z s))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        ITERATE_EQ) THEN
      REWRITE_TAC[MONOIDAL_GROUP_ADD; ABELIAN_RELATIVE_HOMOLOGY_GROUP;
                  homology_group] THEN
      SIMP_TAC[RESTRICTION] THEN X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[HOM_INDUCED_CHAIN_MAP; CONTINUOUS_MAP_ID;
        CONTINUOUS_MAP_FROM_SUBTOPOLOGY; IMAGE_CLAUSES; EMPTY_SUBSET] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC CHAIN_MAP_ID THEN
      ASM_MESON_TAC[SINGULAR_CYCLE];
      ALL_TAC] THEN
    TRANS_TAC EQ_TRANS
     `iterate (group_add (homology_group (&p,top:A topology)))
              {s:A->bool | s IN u /\ ~(z s = frag_0)}
              (\s. homologous_rel (p,top,{}) (z s))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        ITERATE_SUPERSET) THEN
      REWRITE_TAC[MONOIDAL_GROUP_ADD; ABELIAN_RELATIVE_HOMOLOGY_GROUP;
                  homology_group; SUBSET_RESTRICT; IN_ELIM_THM] THEN
      SIMP_TAC[IMP_CONJ; RELATIVE_HOMOLOGY_GROUP; NEUTRAL_GROUP_ADD] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
      REWRITE_TAC[SINGULAR_RELBOUNDARY_0];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [GSYM ITERATE_SUPPORT] THEN
    REWRITE_TAC[support; NEUTRAL_FRAG_ADD] THEN
    SUBGOAL_THEN
     `!s:A->bool. s IN {i | i IN u /\ ~(z i = frag_0)}
                  ==> singular_relcycle (p,subtopology top s,{}) (z s)`
    MP_TAC THENL [ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    UNDISCH_TAC `FINITE {s:A->bool | s IN u /\
                      ~(z s:((num->real)->A)frag = frag_0)}` THEN
    SPEC_TAC(`{s:A->bool | s IN u /\ ~(z s:((num->real)->A)frag = frag_0)}`,
             `v:(A->bool)->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
    SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_FRAG_ADD; MONOIDAL_GROUP_ADD;
             homology_group; ABELIAN_RELATIVE_HOMOLOGY_GROUP] THEN
    REWRITE_TAC[NEUTRAL_GROUP_ADD; NEUTRAL_FRAG_ADD] THEN
    REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
    REWRITE_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN
    REWRITE_TAC[SINGULAR_RELBOUNDARY_0] THEN
    MAP_EVERY X_GEN_TAC [`s:A->bool`; `v:(A->bool)->bool`] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_ADD_EQ_MUL o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[ETA_AX] THEN
      CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[SINGULAR_CYCLE; SINGULAR_CHAIN_SUBTOPOLOGY;
                    SINGULAR_RELCYCLE_SUM];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[relative_homology_group] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; INT_ARITH `~(&p:int < &0)`] THEN
    REWRITE_TAC[GSYM RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) QUOTIENT_GROUP_MUL o
        lhand o snd) THEN
    REWRITE_TAC[NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[RELCYCLE_GROUP] THEN REWRITE_TAC[IN] THEN
      ASM_MESON_TAC[SINGULAR_CYCLE; SINGULAR_CHAIN_SUBTOPOLOGY;
                    SINGULAR_RELCYCLE_SUM];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[RELCYCLE_GROUP]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP; FORALL_IN_GSPEC] THEN
    MP_TAC(ISPECL [`p:num`; `top:A topology`; `u:(A->bool)->bool`]
        GROUP_ISOMORPHISM_CYCLE_GROUP_SUM) THEN
    ASM_REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
    REWRITE_TAC[group_epimorphism] THEN
    DISCH_THEN(MP_TAC o MATCH_MP(SET_RULE
      `IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`) o
      last o CONJUNCTS) THEN
    REWRITE_TAC[RELCYCLE_GROUP] THEN MESON_TAC[IN]] THEN
  REWRITE_TAC[SUM_GROUP_CLAUSES; RESTRICTION_EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY; RELCYCLE_GROUP] THEN
  SIMP_TAC[cartesian_product; IN_ELIM_THM; SINGULAR_BOUNDARY; SET_RULE
   `x IN singular_relcycle p <=> singular_relcycle p x`] THEN
  X_GEN_TAC `z:(A->bool)->((num->real)->A)frag` THEN
  STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:((num->real)->A)frag` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`p + 1`; `top:A topology`; `u:(A->bool)->bool`]
        GROUP_ISOMORPHISM_CHAIN_GROUP_SUM) THEN
  ASM_REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o
    GEN_REWRITE_RULE I [group_epimorphism]) THEN
  GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN
  DISCH_THEN(MP_TAC o SPEC `d:((num->real)->A)frag`) THEN
  REWRITE_TAC[SET_RULE
   `(y IN IMAGE f s <=> x IN t) <=> ((?x. x IN s /\ f x = y) <=> t x)`] THEN
  ASM_REWRITE_TAC[CHAIN_GROUP; SUM_GROUP_CLAUSES; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `w:(A->bool)->((num->real)->A)frag` THEN
  REWRITE_TAC[cartesian_product; IN_ELIM_THM; SET_RULE
    `x IN singular_chain p <=> singular_chain p x`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  MP_TAC(ISPECL [`p:num`; `top:A topology`; `u:(A->bool)->bool`]
        GROUP_ISOMORPHISM_CHAIN_GROUP_SUM) THEN
  ASM_REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN
  REWRITE_TAC[group_monomorphism] THEN DISCH_THEN(MP_TAC o SPECL
   [`RESTRICTION u
       (\s. chain_boundary (p + 1)
              ((w:(A->bool)->((num->real)->A)frag) s))`;
    `z:(A->bool)->((num->real)->A)frag`] o
   CONJUNCT2 o CONJUNCT1) THEN
  REWRITE_TAC[SUM_GROUP_CLAUSES; IN_ELIM_THM; RESTRICTION_IN_CARTESIAN_PRODUCT] THEN
  ASM_REWRITE_TAC[CHAIN_GROUP; cartesian_product; IN_ELIM_THM; SET_RULE
    `x IN singular_chain p <=> singular_chain p x`] THEN
  ASM_SIMP_TAC[SINGULAR_CHAIN_BOUNDARY_ALT] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `s:A->bool` THEN
    ASM_CASES_TAC `(s:A->bool) IN u` THEN ASM_REWRITE_TAC[RESTRICTION] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SET_RULE `p /\ ~q <=> ~(p ==> q)`] THEN
    SIMP_TAC[RESTRICTION] THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `{s:A->bool | s IN u /\ ~(w s:((num->real)->A)frag = frag_0)}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[CHAIN_BOUNDARY_0];
    ASM_MESON_TAC[SINGULAR_CYCLE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_FRAG_ADD] THEN
  ASM_SIMP_TAC[CHAIN_BOUNDARY_SUM] THEN TRANS_TAC EQ_TRANS
   `iterate frag_add u
      (chain_boundary (p + 1) o (w:(A->bool)->((num->real)->A)frag))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        ITERATE_EQ) THEN
    SIMP_TAC[MONOIDAL_FRAG_ADD; RESTRICTION; o_THM];
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        ITERATE_SUPERSET) THEN
    REWRITE_TAC[SUBSET_RESTRICT; MONOIDAL_FRAG_ADD] THEN
    SIMP_TAC[NEUTRAL_FRAG_ADD; IMP_CONJ; IN_ELIM_THM; o_THM] THEN
    REWRITE_TAC[CHAIN_BOUNDARY_0]]);;

let HOMOLOGY_ADDITIVITY_AXIOM = prove
 (`!p top u:(A->bool)->bool.
     (!v. v IN u ==> open_in top v) /\
     pairwise DISJOINT u /\
     UNIONS u = topspace top
     ==> group_isomorphism
          (sum_group u (\s. homology_group(p,subtopology top s)),
           homology_group(p,top))
          (\x. iterate (group_add (homology_group(p,top))) u
           (\v. hom_induced p (subtopology top v,{}) (top,{}) (\z. z) (x v)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOLOGY_ADDITIVITY_AXIOM_GEN THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:A->bool`; `t:A->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PATH_CONNECTED_IN_IMP_CONNECTED_IN) THEN
  REWRITE_TAC[CONNECTED_IN] THEN
  MATCH_MP_TAC(TAUT `(p /\ ~r ==> q) ==> p /\ ~q ==> r`) THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:A->bool`; `UNIONS (u DIFF {t:A->bool})`] THEN
  ASM_SIMP_TAC[OPEN_IN_UNIONS; IN_DIFF] THEN
  ASM_SIMP_TAC[GSYM DIFF_UNIONS_PAIRWISE_DISJOINT; SING_SUBSET] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Special properties of singular homology, in particular the fact that the  *)
(* zeroth homology group is isomorphic to the free abelian group generated   *)
(* by the path components, and so the "coefficient group" is the integers.   *)
(* ------------------------------------------------------------------------- *)

let GROUP_ISOMORPHISM_INTEGER_ZEROTH_HOMOLOGY_GROUP = prove
 (`!(top:A topology) f.
        path_connected_space top /\ singular_simplex(0,top) f
        ==> group_isomorphism (integer_group,homology_group(&0,top))
              (group_zpow (homology_group(&0,top))
                          (homologous_rel(0,top,{}) (frag_of f)))`,
  let lemma = prove
   (`!(top:A topology) f f'.
          path_connected_space top /\
          singular_simplex (0,top) f /\ singular_simplex (0,top) f'
          ==> homologous_rel (0,top,{}) (frag_of f) (frag_of f')`,
    REPEAT GEN_TAC THEN REWRITE_TAC[singular_simplex; STANDARD_SIMPLEX_0] THEN
    ABBREV_TAC `p:num->real = \j. if j = 0 then &1 else &0` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL
     [`(f:(num->real)->A) p`; `(f':(num->real)->A) p`] o
     GEN_REWRITE_RULE I [path_connected_space]) THEN
    ANTS_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_map])) THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
      REWRITE_TAC[o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
      SET_TAC[];
      REWRITE_TAC[path_in; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `g:real->A` THEN STRIP_TAC THEN
    REWRITE_TAC[homologous_rel; SINGULAR_BOUNDARY] THEN
    EXISTS_TAC `frag_of(RESTRICTION (standard_simplex 1)
                   ((g:real->A) o (\x:num->real. x 0)))` THEN
    REWRITE_TAC[SINGULAR_CHAIN_OF; CHAIN_BOUNDARY_OF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[NUMSEG_CONV `0..1`] THEN
    SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_FRAG_ADD; FINITE_INSERT; FINITE_EMPTY;
             NOT_IN_EMPTY; IN_INSERT; NEUTRAL_FRAG_ADD] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [REWRITE_TAC[singular_simplex] THEN
      REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
      SIMP_TAC[RESTRICTION_CONTINUOUS_MAP; TOPSPACE_SUBTOPOLOGY;
               INTER_SUBSET] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
      EXISTS_TAC `subtopology euclideanreal (real_interval [&0,&1])` THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV;
               CONTINUOUS_MAP_FROM_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x IN t) ==> IMAGE f (u INTER s) SUBSET t`) THEN
      SIMP_TAC[standard_simplex; IN_REAL_INTERVAL; IN_ELIM_THM];
      CONV_TAC INT_REDUCE_CONV THEN MATCH_MP_TAC(FRAG_MODULE
       `x = x' /\ y = y'
        ==> frag_add (frag_cmul (&1) x)
                     (frag_add (frag_cmul (-- &1) y) frag_0) =
            frag_sub x' y'`) THEN
      CONJ_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[singular_face] THEN
      ASM_REWRITE_TAC[SUB_REFL; STANDARD_SIMPLEX_0] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[EXTENSIONAL; IN_ELIM_THM; IN_SING]) THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `x:num->real` THEN
      ASM_CASES_TAC `x:num->real = p` THEN
      ASM_SIMP_TAC[RESTRICTION; IN_SING; o_THM] THEN
      REWRITE_TAC[face_map; CONJUNCT1 LT] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_REWRITE_TAC[standard_simplex; IN_ELIM_THM] THEN
      UNDISCH_THEN `x:num->real = p` SUBST1_TAC THEN
      REWRITE_TAC[num_CONV `1`; SUM_CLAUSES_NUMSEG] THEN
      EXPAND_TAC "p" THEN REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[] `p ==> (if p then x else y) = x`) THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `singular_relcycle(0,top:A topology,{}) (frag_of f)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SINGULAR_CYCLE; SINGULAR_CHAIN_OF] THEN
    REWRITE_TAC[chain_boundary];
    ALL_TAC] THEN
  ABBREV_TAC `q = homologous_rel(0,top:A topology,{}) (frag_of f)` THEN
  SUBGOAL_THEN `q IN group_carrier (homology_group (&0,top:A topology))`
  ASSUME_TAC THENL
   [REWRITE_TAC[homology_group; RELATIVE_HOMOLOGY_GROUP] THEN
    EXPAND_TAC "q" THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM;
              GROUP_EPIMORPHISM_ALT; GROUP_MONOMORPHISM_ALT] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_GROUP_ZPOW] THEN
  SUBGOAL_THEN
   `group_zpow (homology_group (&0,top)) q =
    \n. homologous_rel(0,top:A topology,{}) (frag_cmul n (frag_of f))`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `n:int` THEN
    EXPAND_TAC "q" THEN SIMP_TAC[GSYM RIGHT_COSET_SINGULAR_RELBOUNDARY] THEN
    SIMP_TAC[homology_group; relative_homology_group; INT_LT_REFL;
             NUM_OF_INT_OF_NUM] THEN
    ASM_SIMP_TAC[QUOTIENT_GROUP_ZPOW; CONJUNCT1 RELCYCLE_GROUP; IN;
                 NORMAL_SUBGROUP_SINGULAR_RELBOUNDARY_RELCYCLE] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[GROUP_ZPOW_SUBGROUP_GENERATED; relcycle_group] THEN
    REWRITE_TAC[FREE_ABELIAN_GROUP_ZPOW; chain_group];
    ALL_TAC] THEN
  REWRITE_TAC[INTEGER_GROUP; IN_UNIV; homology_group] THEN
  REWRITE_TAC[group_image; SUBSET; RELATIVE_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; INTEGER_GROUP; IN_UNIV] THEN
  REWRITE_TAC[HOMOLOGOUS_REL_EQ_RELBOUNDARY] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:int` THEN REWRITE_TAC[SINGULAR_BOUNDARY; ADD_CLAUSES] THEN
    SUBGOAL_THEN
     `!d. singular_chain (1,top:A topology) d
          ==> frag_extend (\x. frag_of(f:(num->real)->A))
                          (chain_boundary 1 d) = frag_0`
    MP_TAC THENL
     [REWRITE_TAC[singular_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
      REWRITE_TAC[GSYM singular_chain] THEN
      REWRITE_TAC[FRAG_EXTEND_0; CHAIN_BOUNDARY_0] THEN
      SIMP_TAC[FRAG_EXTEND_SUB; CHAIN_BOUNDARY_SUB] THEN
      REWRITE_TAC[FRAG_MODULE `frag_sub x frag_0 = x`; IN] THEN
      X_GEN_TAC `g:(num->real)->A` THEN DISCH_TAC THEN
      REWRITE_TAC[CHAIN_BOUNDARY_OF] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SIMP_TAC[MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_FRAG_ADD; num_CONV `1`;
               LE_0; FRAG_EXTEND_ADD; FRAG_EXTEND_CMUL; FRAG_EXTEND_OF] THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV THEN
      CONV_TAC FRAG_MODULE;
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[FRAG_EXTEND_OF; FRAG_EXTEND_CMUL; FRAG_MODULE
       `frag_cmul n t = frag_0 <=> n = &0 \/ t = frag_0`] THEN
      REWRITE_TAC[FRAG_OF_NONZERO]];
    REWRITE_TAC[SINGULAR_CYCLE; IN_IMAGE; IN_UNIV; HOMOLOGOUS_REL_EQ] THEN
    MATCH_MP_TAC(MESON[] `(!x. P x ==> R x) ==> (!x. P x /\ Q x ==> R x)`) THEN
    REWRITE_TAC[singular_chain] THEN MATCH_MP_TAC FRAG_INDUCTION THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `&0:int` THEN REWRITE_TAC[HOMOLOGOUS_REL_REFL;
        FRAG_MODULE `frag_cmul (&0) x = frag_0`];
      ALL_TAC;
      REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP HOMOLOGOUS_REL_SUB) THEN
      REWRITE_TAC[FRAG_MODULE
       `frag_sub (frag_cmul a c) (frag_cmul b c) = frag_cmul (a - b) c`] THEN
      MESON_TAC[]] THEN
    REWRITE_TAC[IN] THEN X_GEN_TAC `f':(num->real)->A` THEN DISCH_TAC THEN
    EXISTS_TAC `&1:int` THEN
    REWRITE_TAC[FRAG_MODULE `frag_cmul (&1) x = x`] THEN
    ASM_MESON_TAC[lemma]]);;

let ISOMORPHIC_GROUP_INTEGER_ZEROTH_HOMOLOGY_GROUP = prove
 (`!top:A topology.
        path_connected_space top /\ ~(topspace top = {})
        ==> homology_group(&0,top) isomorphic_group integer_group`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?f. singular_simplex(0,top:A topology) f`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    EXISTS_TAC `RESTRICTION (standard_simplex 0) (\x. (a:A))` THEN
    SIMP_TAC[singular_simplex; RESTRICTION_CONTINUOUS_MAP;
             TOPSPACE_SUBTOPOLOGY; INTER_SUBSET; CONTINUOUS_MAP_CONST;
             REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL] THEN
    ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN
    ASM_MESON_TAC[GROUP_ISOMORPHISM_INTEGER_ZEROTH_HOMOLOGY_GROUP]]);;

let HOMOLOGY_COEFFICIENTS = prove
 (`!top (a:A).
        topspace top = {a}
        ==> homology_group(&0,top) isomorphic_group integer_group`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ISOMORPHIC_GROUP_INTEGER_ZEROTH_HOMOLOGY_GROUP THEN
  ASM_REWRITE_TAC[GSYM PATH_CONNECTED_IN_TOPSPACE; NOT_INSERT_EMPTY] THEN
  ASM_REWRITE_TAC[PATH_CONNECTED_IN_SING; IN_SING]);;

let ZEROTH_HOMOLOGY_GROUP = prove
 (`!top:A topology.
        homology_group(&0,top) isomorphic_group
        free_abelian_group (path_components_of top)`,
  GEN_TAC THEN TRANS_TAC ISOMORPHIC_GROUP_TRANS
   `sum_group (path_components_of top)
       (\s:A->bool. homology_group(&0,subtopology top s))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    MP_TAC(ISPECL [`&0:int`; `top:A topology`;
                   `path_components_of(top:A topology)`]
      HOMOLOGY_ADDITIVITY_AXIOM_GEN) THEN
    REWRITE_TAC[isomorphic_group] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    REWRITE_TAC[PAIRWISE_DISJOINT_PATH_COMPONENTS_OF] THEN
    REWRITE_TAC[UNIONS_PATH_COMPONENTS_OF] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PATH_COMPONENTS_OF_MAXIMAL THEN
    EXISTS_TAC `top:A topology` THEN ASM SET_TAC[];
    TRANS_TAC ISOMORPHIC_GROUP_TRANS
     `sum_group (path_components_of (top:A topology)) (\i. integer_group)` THEN
    REWRITE_TAC[ISOMORPHIC_SUM_INTEGER_GROUP] THEN
    MATCH_MP_TAC ISOMORPHIC_GROUP_SUM_GROUP THEN
    REWRITE_TAC[] THEN X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC ISOMORPHIC_GROUP_INTEGER_ZEROTH_HOMOLOGY_GROUP THEN
    ASM_SIMP_TAC[TOPSPACE_SUBTOPOLOGY_SUBSET; PATH_COMPONENTS_OF_SUBSET;
     REWRITE_RULE[path_connected_in] PATH_CONNECTED_IN_PATH_COMPONENTS_OF] THEN
    ASM_MESON_TAC[NONEMPTY_PATH_COMPONENTS_OF]]);;

(* ------------------------------------------------------------------------- *)
(* More basic properties of homology groups, deduced from the E-S axioms.    *)
(* ------------------------------------------------------------------------- *)

let TRIVIAL_HOMOLOGY_GROUP = prove
 (`!p top:A topology. p < &0 ==> trivial_group(homology_group(p,top))`,
  REWRITE_TAC[TRIVIAL_RELATIVE_HOMOLOGY_GROUP; homology_group]);;

let ABELIAN_HOMOLOGY_GROUP = prove
 (`!p top:A topology. abelian_group(homology_group(p,top))`,
  REWRITE_TAC[homology_group; ABELIAN_RELATIVE_HOMOLOGY_GROUP]);;

let GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY = prove
 (`!p top top' f:A->B.
        group_homomorphism
         (homology_group (p,top),homology_group (p,top'))
         (hom_induced p (top,{}) (top',{}) f)`,
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED; homology_group]);;

let HOM_INDUCED_COMPOSE_EMPTY = prove
 (`!p top top' top'' (f:A->B) (g:B->C).
        continuous_map(top,top') f /\
        continuous_map(top',top'') g
        ==> hom_induced p (top,{}) (top'',{}) (g o f) =
            hom_induced p (top',{}) (top'',{}) g o
            hom_induced p (top,{}) (top',{}) f`,
  REWRITE_TAC[homology_group] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOM_INDUCED_COMPOSE THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET]);;

let HOMOLOGY_HOMOTOPY_EMPTY = prove
 (`!p (top:A topology) (top':B topology) f g.
        homotopic_with (\h. T) (top,top') f g
        ==> hom_induced p (top,{}) (top',{}) f =
            hom_induced p (top,{}) (top',{}) g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMOLOGY_HOMOTOPY_AXIOM THEN
  ASM_REWRITE_TAC[GSYM homology_group; IMAGE_CLAUSES; EMPTY_SUBSET]);;

let HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS = prove
 (`!p top top' s t (f:A->B) g.
        continuous_map (top,top') f /\ IMAGE f s SUBSET t /\
        continuous_map (top',top) g /\ IMAGE g t SUBSET s /\
        homotopic_with (\h. IMAGE h s SUBSET s) (top,top) (g o f) I /\
        homotopic_with (\k. IMAGE k t SUBSET t) (top',top') (f o g) I
        ==> group_isomorphisms (relative_homology_group (p,top,s),
                                relative_homology_group (p,top',t))
                               (hom_induced p (top,s) (top',t) f,
                                hom_induced p (top',t) (top,s) g)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN REWRITE_TAC[group_isomorphisms] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED] THEN
  FIRST_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `p:int` o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMOLOGY_HOMOTOPY_AXIOM))) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT; homology_group] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THEN ASM_SIMP_TAC[I_DEF; HOM_INDUCED_ID] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN AP_THM_TAC THEN
  MATCH_MP_TAC HOM_INDUCED_COMPOSE THEN ASM_REWRITE_TAC[]);;

let HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM = prove
 (`!p top top' s t (f:A->B) g.
        continuous_map (top,top') f /\ IMAGE f s SUBSET t /\
        continuous_map (top',top) g /\ IMAGE g t SUBSET s /\
        homotopic_with (\h. IMAGE h s SUBSET s) (top,top) (g o f) I /\
        homotopic_with (\k. IMAGE k t SUBSET t) (top',top') (f o g) I
        ==> group_isomorphism (relative_homology_group (p,top,s),
                               relative_homology_group (p,top',t))
                              (hom_induced p (top,s) (top',t) f)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
    HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS) THEN
  REWRITE_TAC[group_isomorphism] THEN MESON_TAC[]);;

let HOMOTOPY_EQUIVALENCE_HOMOLOGY_GROUP_ISOMORPHISM = prove
 (`!p top top' (f:A->B) g.
        continuous_map (top,top') f /\ continuous_map (top',top) g /\
        homotopic_with (\h. T) (top,top) (g o f) I /\
        homotopic_with (\k. T) (top',top') (f o g) I
        ==> group_isomorphism (homology_group (p,top),homology_group (p,top'))
                              (hom_induced p (top,{}) (top',{}) f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homology_group] THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM THEN
  EXISTS_TAC `g:B->A` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET]);;

let HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_RELATIVE_HOMOLOGY_GROUPS = prove
 (`!p top top' s t (f:A->B) g.
        continuous_map (top,top') f /\ IMAGE f s SUBSET t /\
        continuous_map (top',top) g /\ IMAGE g t SUBSET s /\
        homotopic_with (\h. IMAGE h s SUBSET s) (top,top) (g o f) I /\
        homotopic_with (\k. IMAGE k t SUBSET t) (top',top') (f o g) I
        ==> relative_homology_group (p,top,s) isomorphic_group
            relative_homology_group (p,top',t)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
    HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS) THEN
  REWRITE_TAC[isomorphic_group; group_isomorphism] THEN MESON_TAC[]);;

let HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS = prove
 (`!p (top:A topology) (top':B topology).
        top homotopy_equivalent_space top'
        ==> homology_group(p,top) isomorphic_group homology_group(p,top')`,
  REWRITE_TAC[homotopy_equivalent_space] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[homology_group] THEN MATCH_MP_TAC
   HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_RELATIVE_HOMOLOGY_GROUPS THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN ASM_MESON_TAC[]);;

let HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS = prove
 (`!p (top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> homology_group(p,top) isomorphic_group homology_group(p,top')`,
  SIMP_TAC[HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS;
           HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT_SPACE]);;

let TRIVIAL_RELATIVE_HOMOLOGY_GROUP_GEN = prove
 (`!p top s f:A->A.
        continuous_map (top,subtopology top s) f /\
        homotopic_with (\h. T) (subtopology top s,subtopology top s) f I /\
        homotopic_with (\k. T) (top,top) f I
        ==> trivial_group(relative_homology_group(p,top,s))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`hom_induced p (subtopology top s:A topology,{}) (top,{}) (\x. x)`;
    `hom_induced p (top:A topology,{}) (top,s) (\x. x)`;
    `hom_boundary p (top:A topology,s)`;
    `hom_induced (p - &1) (subtopology top s:A topology,{}) (top,{}) (\x. x)`;
    `homology_group (p,subtopology top (s:A->bool))`;
    `homology_group (p,top:A topology)`;
    `relative_homology_group (p,top,s:A->bool)`;
    `homology_group (p - &1,subtopology top (s:A->bool))`;
    `homology_group (p - &1,top:A topology)`]
  GROUP_EXACTNESS_IMP_TRIVIALITY) THEN
  REWRITE_TAC[HOMOLOGY_EXACTNESS_AXIOM_1;
              HOMOLOGY_EXACTNESS_AXIOM_2;
              HOMOLOGY_EXACTNESS_AXIOM_3] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[homology_group] THEN CONJ_TAC THEN MATCH_MP_TAC
   HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM THEN
  SIMP_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  SIMP_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
  REWRITE_TAC[o_DEF; ETA_AX] THEN ASM_MESON_TAC[]);;

let TRIVIAL_RELATIVE_HOMOLOGY_GROUP_TOPSPACE = prove
 (`!p top:A topology.
        trivial_group(relative_homology_group(p,top,topspace top))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC TRIVIAL_RELATIVE_HOMOLOGY_GROUP_GEN THEN
  EXISTS_TAC `\x:A. x` THEN
  REWRITE_TAC[HOMOTOPIC_WITH_REFL; I_DEF; SUBTOPOLOGY_TOPSPACE] THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID]);;

let TRIVIAL_RELATIVE_HOMOLOGY_GROUP_EMPTY = prove
 (`!p top s:A->bool.
        topspace top = {}
        ==> trivial_group(relative_homology_group(p,top,s))`,
  ONCE_REWRITE_TAC[RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
  SIMP_TAC[INTER_EMPTY] THEN
  MESON_TAC[TRIVIAL_RELATIVE_HOMOLOGY_GROUP_TOPSPACE]);;

let TRIVIAL_HOMOLOGY_GROUP_EMPTY = prove
 (`!p top:A topology.
        topspace top = {} ==> trivial_group(homology_group(p,top))`,
  REWRITE_TAC[homology_group; TRIVIAL_RELATIVE_HOMOLOGY_GROUP_EMPTY]);;

let TRIVIAL_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE = prove
 (`!p top:A topology.
        contractible_space top /\ ~(p = &0)
        ==> trivial_group(homology_group(p,top))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[CONTRACTIBLE_EQ_HOMOTOPY_EQUIVALENT_SINGLETON_SUBTOPOLOGY] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  REWRITE_TAC[TRIVIAL_HOMOLOGY_GROUP_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY o SPEC`p:int` o
   MATCH_MP HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_HOMOLOGY_GROUPS) THEN
  MATCH_MP_TAC HOMOLOGY_DIMENSION_AXIOM THEN EXISTS_TAC `a:A` THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

let HOMEOMORPHIC_MAPS_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS = prove
 (`!p top top' s t (f:A->B) g.
        homeomorphic_maps (top,top') (f,g) /\
        IMAGE f s SUBSET t /\ IMAGE g t SUBSET s
        ==> group_isomorphisms (relative_homology_group (p,top,s),
                                relative_homology_group (p,top',t))
                               (hom_induced p (top,s) (top',t) f,
                                hom_induced p (top',t) (top,s) g)`,
  ONCE_REWRITE_TAC[HOM_INDUCED_RESTRICT; RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
  REWRITE_TAC[homeomorphic_maps] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC
    HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
    CONJ_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
    ASM_SIMP_TAC[o_THM; SUBSET; FORALL_IN_IMAGE; I_THM; IN_INTER] THEN
    ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]]);;

let HOMEOMORPHIC_MAP_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM = prove
 (`!p top top' s t (f:A->B).
        homeomorphic_map (top,top') f /\ s SUBSET topspace top /\ IMAGE f s = t
        ==> group_isomorphism (relative_homology_group (p,top,s),
                               relative_homology_group (p,top',t))
                              (hom_induced p (top,s) (top',t) f)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HOMEOMORPHIC_MAP_MAPS]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:B->A`) THEN REWRITE_TAC[group_isomorphism] THEN
  EXISTS_TAC `hom_induced p (top',t) (top,s) (g:B->A)` THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAPS_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphic_maps; continuous_map]) THEN
  ASM SET_TAC[]);;

let GROUP_MONOMORPHISM_HOM_INDUCED_SECTION_MAP = prove
 (`!p top top' f:A->B.
        section_map (top,top') f
        ==> group_monomorphism (homology_group (p,top),
                                homology_group (p,top'))
                               (hom_induced p (top,{}) (top',{}) f)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[section_map; retraction_maps; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:B->A` THEN STRIP_TAC THEN
  MATCH_MP_TAC GROUP_MONOMORPHISM_LEFT_INVERTIBLE THEN
  EXISTS_TAC `hom_induced p (top',{}) (top,{}) (g:B->A)` THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY] THEN
  MP_TAC(GSYM(ISPECL [`p:int`; `top:A topology`; `top':B topology`;
                 `top:A topology`;
                 `f:A->B`; `g:B->A`]
        HOM_INDUCED_COMPOSE_EMPTY)) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN
  SIMP_TAC[o_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOM_INDUCED_ID_GEN THEN
   ASM_REWRITE_TAC[o_THM; GSYM homology_group] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

let GROUP_EPIMORPHISM_HOM_INDUCED_RETRACTION_MAP = prove
 (`!p top top' f:A->B.
        retraction_map (top,top') f
        ==> group_epimorphism (homology_group (p,top),
                               homology_group (p,top'))
                              (hom_induced p (top,{}) (top',{}) f)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[retraction_map; retraction_maps; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:B->A` THEN STRIP_TAC THEN
  MATCH_MP_TAC GROUP_EPIMORPHISM_RIGHT_INVERTIBLE THEN
  EXISTS_TAC `hom_induced p (top',{}) (top,{}) (g:B->A)` THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY] THEN
  MP_TAC(GSYM(ISPECL [`p:int`; `top':B topology`; `top:A topology`;
                 `top':B topology`;
                 `g:B->A`; `f:A->B`]
        HOM_INDUCED_COMPOSE_EMPTY)) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN
  SIMP_TAC[o_THM] THEN DISCH_THEN(K ALL_TAC)  THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOM_INDUCED_ID_GEN THEN
  ASM_REWRITE_TAC[o_THM; GSYM homology_group] THEN
  ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

let HOMEOMORPHIC_MAP_HOMOLOGY_GROUP_ISOMORPHISM = prove
 (`!p top top' f:A->B.
        homeomorphic_map (top,top') f
        ==> group_isomorphism (homology_group (p,top),
                               homology_group (p,top'))
                               (hom_induced p (top,{}) (top',{}) f)`,
  REWRITE_TAC[GSYM SECTION_AND_RETRACTION_EQ_HOMEOMORPHIC_MAP] THEN
  REWRITE_TAC[GSYM GROUP_MONOMORPHISM_EPIMORPHISM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_MONOMORPHISM_HOM_INDUCED_SECTION_MAP;
               GROUP_EPIMORPHISM_HOM_INDUCED_RETRACTION_MAP]);;

let GROUP_MONOMORPHISM_HOM_INDUCED_INCLUSION = prove
 (`!p top s:A->bool.
        s = {} \/ s retract_of_space top
        ==> group_monomorphism
             (homology_group(p,subtopology top s),homology_group(p,top))
             (hom_induced p (subtopology top s,{}) (top,{}) (\x. x))`,
  REWRITE_TAC[RETRACT_OF_SPACE_SECTION_MAP] THEN REPEAT STRIP_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand)
      GROUP_MONOMORPHISM_FROM_TRIVIAL_GROUP o snd) THEN
    ASM_SIMP_TAC[TRIVIAL_HOMOLOGY_GROUP_EMPTY; TOPSPACE_SUBTOPOLOGY;
                 INTER_EMPTY] THEN
    ASM_SIMP_TAC[homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED;
                 CONTINUOUS_MAP_ID; CONTINUOUS_MAP_FROM_SUBTOPOLOGY;
                 IMAGE_CLAUSES; EMPTY_SUBSET];
    MATCH_MP_TAC GROUP_MONOMORPHISM_HOM_INDUCED_SECTION_MAP THEN
    ASM_REWRITE_TAC[]]);;

let TRIVIAL_HOMOMORPHISM_HOM_BOUNDARY_INCLUSION = prove
 (`!p top s:A->bool.
        s = {} \/ s retract_of_space top
        ==> trivial_homomorphism
             (relative_homology_group(p,top,s),
              homology_group (p - &1,subtopology top s))
             (hom_boundary p (top,s))`,
  REPEAT GEN_TAC THEN
  MP_TAC(CONJ (SPEC `p:int` HOMOLOGY_EXACTNESS_AXIOM_1)
              (SPEC `p:int` HOMOLOGY_EXACTNESS_AXIOM_2)) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `s:A->bool`]) THEN
  DISCH_THEN(SUBST1_TAC o SYM o
    MATCH_MP GROUP_EXACTNESS_MONOMORPHISM_EQ_TRIVIALITY) THEN
  REWRITE_TAC[GROUP_MONOMORPHISM_HOM_INDUCED_INCLUSION]);;

let GROUP_EPIMORPHISM_HOM_INDUCED_RELATIVIZATION = prove
 (`!p top s:A->bool.
        s = {} \/ s retract_of_space top
        ==> group_epimorphism
             (homology_group(p,top),relative_homology_group(p,top,s))
             (hom_induced p (top,{}) (top,s) (\x. x))`,
  REPEAT GEN_TAC THEN
  MP_TAC(CONJ (SPEC `p:int` HOMOLOGY_EXACTNESS_AXIOM_1)
              (SPEC `p:int` HOMOLOGY_EXACTNESS_AXIOM_2)) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`top:A topology`; `s:A->bool`]) THEN
  DISCH_THEN(SUBST1_TAC o
    MATCH_MP GROUP_EXACTNESS_EPIMORPHISM_EQ_TRIVIALITY) THEN
  REWRITE_TAC[TRIVIAL_HOMOMORPHISM_HOM_BOUNDARY_INCLUSION]);;

let SHORT_EXACT_SEQUENCE_HOM_INDUCED_INCLUSION = prove
 (`!p top s:A->bool.
        s = {} \/ s retract_of_space top
        ==> short_exact_sequence
               (homology_group(p,subtopology top s),
                homology_group(p,top),
                relative_homology_group(p,top,s))
               (hom_induced p (subtopology top s,{}) (top,{}) (\x. x),
                hom_induced p (top,{}) (top,s) (\x. x))`,
  REWRITE_TAC[short_exact_sequence; HOMOLOGY_EXACTNESS_AXIOM_3] THEN
  SIMP_TAC[GROUP_MONOMORPHISM_HOM_INDUCED_INCLUSION] THEN
  REWRITE_TAC[GROUP_EPIMORPHISM_HOM_INDUCED_RELATIVIZATION]);;

let GROUP_ISOMORPHISMS_HOMOLOGY_GROUP_PROD_RETRACT = prove
 (`!p top s:A->bool.
        s = {} \/ s retract_of_space top
        ==> ?h k. h subgroup_of homology_group(p,top) /\
                  k subgroup_of homology_group(p,top) /\
                  group_isomorphism
                   (prod_group (subgroup_generated (homology_group(p,top)) h)
                               (subgroup_generated (homology_group(p,top)) k),
                     (homology_group(p,top)))
                   (\(x,y). group_mul(homology_group(p,top)) x y) /\
                  group_isomorphism
                  (homology_group(p,subtopology top s),
                   subgroup_generated (homology_group(p,top)) h)
                  (hom_induced p (subtopology top s,{}) (top,{}) (\x. x)) /\
                  group_isomorphism
                  (subgroup_generated (homology_group(p,top)) k,
                   relative_homology_group(p,top,s))
                  (hom_induced p (top,{}) (top,s) (\x. x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `p:int` o
    MATCH_MP SHORT_EXACT_SEQUENCE_HOM_INDUCED_INCLUSION) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    SPLITTING_LEMMA_LEFT)) THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; IMP_IMP] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC) THENL
     [EXISTS_TAC `(\x. group_id(homology_group(p,subtopology top {})))
             :(((num->real)->A)frag->bool)->((num->real)->A)frag->bool` THEN
      REWRITE_TAC[GROUP_HOMOMORPHISM_TRIVIAL] THEN
      MATCH_MP_TAC(SET_RULE `s = {a} ==> !x. x IN s ==> a = x`) THEN
      REWRITE_TAC[GSYM trivial_group] THEN
      MATCH_MP_TAC TRIVIAL_HOMOLOGY_GROUP_EMPTY THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_EMPTY];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [retract_of_space]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `r:A->A` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `hom_induced p (top,{}) (subtopology top s,{}) (r:A->A)` THEN
      ASM_SIMP_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY] THEN
      REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_THM] THEN
      W(MP_TAC o PART_MATCH (rand o rand)
        HOM_INDUCED_COMPOSE o rator o lhand o snd) THEN
      REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
      ASM_REWRITE_TAC[GSYM homology_group] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_DEF; ETA_AX] THEN
      MATCH_MP_TAC HOM_INDUCED_ID_GEN THEN
      ASM_REWRITE_TAC[GSYM homology_group] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
      ASM SET_TAC[]];
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC[normal_subgroup_of] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GROUP_ISOMORPHISM_GROUP_MUL; ABELIAN_HOMOLOGY_GROUP]]);;

let ISOMORPHIC_GROUP_HOMOLOGY_GROUP_PROD_RETRACT = prove
 (`!p top s:A->bool.
        s = {} \/ s retract_of_space top
        ==> homology_group(p,top) isomorphic_group
            prod_group (homology_group(p,subtopology top s))
                       (relative_homology_group(p,top,s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `p:int` o
    MATCH_MP GROUP_ISOMORPHISMS_HOMOLOGY_GROUP_PROD_RETRACT) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
   [`h:(((num->real)->A)frag->bool)->bool`;
    `k:(((num->real)->A)frag->bool)->bool`] THEN
  STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_GROUP_TRANS
   `prod_group (subgroup_generated (homology_group(p,top:A topology)) h)
               (subgroup_generated (homology_group(p,top)) k)` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC ISOMORPHIC_GROUP_PROD_GROUPS THEN
    GEN_REWRITE_TAC LAND_CONV [ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN ASM_MESON_TAC[]]);;

let HOMOLOGY_ADDITIVITY_EXPLICIT = prove
 (`!p top s t:A->bool.
        open_in top s /\ open_in top t /\
        DISJOINT s t /\ s UNION t = topspace top
        ==> group_isomorphism
             (prod_group (homology_group (p,subtopology top s))
                         (homology_group (p,subtopology top t)),
              homology_group (p,top))
             (\(a,b). group_mul (homology_group (p,top))
                (hom_induced p (subtopology top s,{}) (top,{}) (\x. x) a)
                (hom_induced p (subtopology top t,{}) (top,{}) (\x. x) b))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed_in top (s:A->bool) /\ closed_in top t`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[closed_in; OPEN_IN_SUBSET] THEN CONJ_TAC THENL
     [UNDISCH_TAC `open_in top (t:A->bool)`;
      UNDISCH_TAC `open_in top (s:A->bool)`] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`hom_induced p (top,{}) (top,t) (\x:A. x)`;
    `hom_induced p (top,{}) (top,s) (\x:A. x)`;
    `hom_induced p (subtopology top s,{}) (top,t) (\x:A. x)`;
    `hom_induced p (subtopology top s,{}) (top,{}) (\x:A. x)`;
    `hom_induced p (subtopology top t,{}) (top,{}) (\x:A. x)`;
    `hom_induced p (subtopology top t,{}) (top,s) (\x:A. x)`;
    `homology_group(p,subtopology top s:A topology)`;
    `homology_group(p,subtopology top t:A topology)`;
    `relative_homology_group(p,top,t:A->bool)`;
    `relative_homology_group(p,top,s:A->bool)`;
    `homology_group(p,top:A topology)`]
   EXACT_SEQUENCE_SUM_LEMMA) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  REWRITE_TAC[ABELIAN_HOMOLOGY_GROUP; HOMOLOGY_EXACTNESS_AXIOM_3] THEN
  GEN_REWRITE_TAC I [CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:int`; `top:A topology`; `s UNION t:A->bool`;
                     `t:A->bool`; `t:A->bool`] HOMOLOGY_EXCISION_AXIOM);
      MP_TAC(ISPECL [`p:int`; `top:A topology`; `s UNION t:A->bool`;
                     `s:A->bool`; `s:A->bool`] HOMOLOGY_EXCISION_AXIOM)] THEN
    REWRITE_TAC[DIFF_EQ_EMPTY; SUBSET_UNION] THEN
    ASM_SIMP_TAC[SET_RULE
     `DISJOINT s t ==> (s UNION t) DIFF t = s /\ (s UNION t) DIFF s = t`] THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_TOPSPACE; GSYM homology_group] THEN
    ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN; INTERIOR_OF_OPEN_IN; SUBSET_REFL];
    REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_THM] THEN
    ASM_SIMP_TAC[GSYM HOM_INDUCED_COMPOSE; IMAGE_CLAUSES; EMPTY_SUBSET;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[o_DEF]]);;

(* ------------------------------------------------------------------------- *)
(* Reduced homology.                                                         *)
(* ------------------------------------------------------------------------- *)

let reduced_homology_group = new_definition
 `reduced_homology_group(p,(top:A topology)) =
        subgroup_generated (homology_group(p,top))
          (group_kernel (homology_group(p,top),
                         homology_group(p,discrete_topology {one}))
                        (hom_induced p (top,{}) (discrete_topology {one},{})
                                     (\x. one)))`;;

let GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP = prove
 (`!p top:A topology.
        group_carrier (reduced_homology_group(p,top)) =
        group_kernel (homology_group(p,top),
                      homology_group(p,discrete_topology {one}))
             (hom_induced p (top,{}) (discrete_topology {one},{}) (\x. one))`,
  SIMP_TAC[reduced_homology_group; CARRIER_SUBGROUP_GENERATED_SUBGROUP;
           SUBGROUP_GROUP_KERNEL; GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY;
           CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING]);;

let GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP_SUBSET = prove
 (`!p top:A topology.
        group_carrier (reduced_homology_group(p,top))
        SUBSET group_carrier (homology_group(p,top))`,
  REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET;
              reduced_homology_group]);;

let UN_REDUCED_HOMOLOGY_GROUP = prove
 (`!p top:A topology.
        ~(p = &0)
        ==> reduced_homology_group(p,top) = homology_group(p,top)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[reduced_homology_group] THEN
  MATCH_MP_TAC(MESON[SUBGROUP_GENERATED_GROUP_CARRIER]
   `s = group_carrier G ==> subgroup_generated G s = G`) THEN
  MATCH_MP_TAC GROUP_KERNEL_TO_TRIVIAL_GROUP THEN
  SIMP_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY; CONTINUOUS_MAP_CONST;
           TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
  MATCH_MP_TAC HOMOLOGY_DIMENSION_AXIOM THEN EXISTS_TAC `one` THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY]);;

let TRIVIAL_REDUCED_HOMOLOGY_GROUP = prove
 (`!p top:A topology.
        p < &0 ==> trivial_group(reduced_homology_group(p,top))`,
  SIMP_TAC[UN_REDUCED_HOMOLOGY_GROUP; INT_LT_IMP_NE] THEN
  REWRITE_TAC[TRIVIAL_HOMOLOGY_GROUP]);;

let GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED = prove
 (`!p top top' f:A->B.
        group_homomorphism
          (reduced_homology_group (p,top),reduced_homology_group (p,top'))
          (hom_induced p (top,{}) (top',{}) f)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `continuous_map(top,top') (f:A->B)` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `hom_induced p (top,{}) (top',{}) (f:A->B) =
        \c. group_id(reduced_homology_group (p,top'))`
     (fun th -> REWRITE_TAC[th; GROUP_HOMOMORPHISM_TRIVIAL]) THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN ASM_SIMP_TAC[HOM_INDUCED_DEFAULT] THEN
    REWRITE_TAC[reduced_homology_group; homology_group] THEN
    REWRITE_TAC[SUBGROUP_GENERATED]] THEN
  REWRITE_TAC[reduced_homology_group] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_INTO_SUBGROUP_EQ;
               GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY;
               GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED;
               CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING;
               CARRIER_SUBGROUP_GENERATED_SUBGROUP;
               SUBGROUP_GROUP_KERNEL] THEN
  REWRITE_TAC[group_kernel] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> k(f x) = h x) /\ IMAGE f s SUBSET t
    ==> IMAGE f {x | x IN s /\ h x = z} SUBSET
        {y | y IN t /\ k y = z}`) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; HOM_INDUCED; homology_group] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_THM] THEN
  ASM_SIMP_TAC[GSYM HOM_INDUCED_COMPOSE_EMPTY; CONTINUOUS_MAP_CONST;
               TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
  REWRITE_TAC[o_DEF]);;

let HOM_INDUCED_REDUCED = prove
 (`!p top top' f c.
        c IN group_carrier(reduced_homology_group(p,top))
        ==> hom_induced p (top,{}) (top',{}) f c IN
            group_carrier(reduced_homology_group (p,top'))`,
  REWRITE_TAC[REWRITE_RULE[group_homomorphism; SUBSET; FORALL_IN_IMAGE]
    GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED]);;

let GROUP_HOMOMORPHISM_HOM_BOUNDARY_REDUCED = prove
 (`!p top s:A->bool.
        group_homomorphism
         (relative_homology_group (p,top,s),
          reduced_homology_group (p - &1,subtopology top s))
         (hom_boundary p (top,s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[reduced_homology_group] THEN
  MATCH_MP_TAC GROUP_HOMOMORPHISM_INTO_SUBGROUP THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_BOUNDARY] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; group_kernel; IN_ELIM_THM] THEN
  X_GEN_TAC `c:((num->real)->A)frag->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[HOM_BOUNDARY] THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_THM] THEN
  MP_TAC(ISPECL
   [`p:int`; `top:A topology`; `s:A->bool`; `discrete_topology {one}`; `{one}`;
    `\x:A. one`] NATURALITY_HOM_INDUCED) THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY] THEN
  REWRITE_TAC[SUBTOPOLOGY_DISCRETE_TOPOLOGY; INTER_IDEMPOT] THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MP_TAC(ISPECL
   [`relative_homology_group(p,discrete_topology {one},{one})`;
    `homology_group (p - &1,discrete_topology {one})`;
    `hom_boundary p (discrete_topology {one},{one})`]
   GROUP_IMAGE_FROM_TRIVIAL_GROUP) THEN
  MP_TAC(ISPECL
   [`p:int`; `discrete_topology {one}`; `{one}`]
   GROUP_HOMOMORPHISM_HOM_BOUNDARY) THEN
  REWRITE_TAC[SUBTOPOLOGY_DISCRETE_TOPOLOGY; INTER_IDEMPOT] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ANTS_TAC THENL
   [MESON_TAC[TRIVIAL_RELATIVE_HOMOLOGY_GROUP_TOPSPACE;
              TOPSPACE_DISCRETE_TOPOLOGY];
    REWRITE_TAC[group_image; o_THM] THEN MATCH_MP_TAC(SET_RULE
     `x IN s ==> IMAGE f s = {z} ==> f x = z`) THEN
    REWRITE_TAC[HOM_INDUCED]]);;

let HOMOTOPY_EQUIVALENCE_REDUCED_HOMOLOGY_GROUP_ISOMORPHISMS = prove
 (`!p top top' (f:A->B) g.
        continuous_map (top,top') f /\
        continuous_map (top',top) g /\
        homotopic_with (\h. T) (top,top) (g o f) I /\
        homotopic_with (\k. T) (top',top') (f o g) I
        ==> group_isomorphisms (reduced_homology_group (p,top),
                                reduced_homology_group (p,top'))
                               (hom_induced p (top,{}) (top',{}) f,
                                hom_induced p (top',{}) (top,{}) g)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN REWRITE_TAC[group_isomorphisms] THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED] THEN
  FIRST_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `p:int` o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] HOMOLOGY_HOMOTOPY_EMPTY))) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [FUN_EQ_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
  ASM_SIMP_TAC[I_DEF; HOM_INDUCED_ID; REWRITE_RULE[SUBSET; homology_group]
    GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP_SUBSET] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN AP_THM_TAC THEN
  MATCH_MP_TAC HOM_INDUCED_COMPOSE THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET]);;

let HOMOTOPY_EQUIVALENCE_REDUCED_HOMOLOGY_GROUP_ISOMORPHISM = prove
 (`!p top top' (f:A->B) g.
        continuous_map (top,top') f /\ continuous_map (top',top) g /\
        homotopic_with (\h. T) (top,top) (g o f) I /\
        homotopic_with (\k. T) (top',top') (f o g) I
        ==> group_isomorphism (reduced_homology_group (p,top),
                               reduced_homology_group (p,top'))
                              (hom_induced p (top,{}) (top',{}) f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[group_isomorphism] THEN
  EXISTS_TAC `hom_induced p (top',{}) (top,{}) (g:B->A)` THEN
  ASM_SIMP_TAC[HOMOTOPY_EQUIVALENCE_REDUCED_HOMOLOGY_GROUP_ISOMORPHISMS]);;

let HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_REDUCED_HOMOLOGY_GROUPS = prove
 (`!p (top:A topology) (top':B topology).
        top homotopy_equivalent_space top'
        ==> reduced_homology_group(p,top) isomorphic_group
            reduced_homology_group(p,top')`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopy_equivalent_space; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `g:B->A`] THEN STRIP_TAC THEN
  REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `hom_induced p (top,{}) (top',{}) (f:A->B)` THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENCE_REDUCED_HOMOLOGY_GROUP_ISOMORPHISM THEN
  ASM_MESON_TAC[]);;

let HOMEOMORPHIC_SPACE_IMP_ISOMORPHIC_REDUCED_HOMOLOGY_GROUPS = prove
 (`!p (top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> reduced_homology_group(p,top) isomorphic_group
            reduced_homology_group(p,top')`,
  SIMP_TAC[HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_REDUCED_HOMOLOGY_GROUPS;
           HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT_SPACE]);;

let TRIVIAL_REDUCED_HOMOLOGY_GROUP_EMPTY = prove
 (`!p top:A topology.
        topspace top = {} ==> trivial_group(reduced_homology_group(p,top))`,
  SIMP_TAC[reduced_homology_group; TRIVIAL_GROUP_SUBGROUP_GENERATED;
           TRIVIAL_HOMOLOGY_GROUP_EMPTY]);;

let HOMOLOGY_DIMENSION_REDUCED = prove
 (`!p top a:A.
        topspace top = {a} ==> trivial_group (reduced_homology_group (p,top))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[reduced_homology_group] THEN
  MATCH_MP_TAC TRIVIAL_GROUP_SUBGROUP_GENERATED_TRIVIAL THEN
  MATCH_MP_TAC(MESON[GROUP_ISOMORPHISM_GROUP_KERNEL_GROUP_IMAGE; SUBSET_REFL]
   `group_isomorphism (G,G') f
     ==> group_kernel(G,G') f SUBSET {group_id G}`) THEN
  MATCH_MP_TAC HOMEOMORPHIC_MAP_HOMOLOGY_GROUP_ISOMORPHISM THEN
  REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN EXISTS_TAC `(\x. a):1->A` THEN
  ASM_REWRITE_TAC[homeomorphic_maps; CONTINUOUS_MAP_CONST;
    TOPSPACE_DISCRETE_TOPOLOGY] THEN
  SIMP_TAC[IN_SING]);;

let TRIVIAL_REDUCED_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE = prove
 (`!p top:A topology.
         contractible_space top
         ==> trivial_group (reduced_homology_group (p,top))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONTRACTIBLE_EQ_HOMOTOPY_EQUIVALENT_SINGLETON_SUBTOPOLOGY] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  REWRITE_TAC[TRIVIAL_REDUCED_HOMOLOGY_GROUP_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY o SPEC`p:int` o
   MATCH_MP
    HOMOTOPY_EQUIVALENT_SPACE_IMP_ISOMORPHIC_REDUCED_HOMOLOGY_GROUPS) THEN
  MATCH_MP_TAC HOMOLOGY_DIMENSION_REDUCED THEN EXISTS_TAC `a:A` THEN
  ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]);;

let GROUP_IMAGE_REDUCED_HOMOLOGY_GROUP = prove
 (`!p top s:A->bool.
        ~(topspace top INTER s = {})
        ==> group_image (reduced_homology_group (p,top),
                         relative_homology_group (p,top,s))
                        (hom_induced p (top,{}) (top,s) (\x. x)) =
            group_image (homology_group (p,top),
                         relative_homology_group (p,top,s))
                        (hom_induced p (top,{}) (top,s) (\x. x))`,
  let lemma = prove(`(\y. a) o f = \x. a`,REWRITE_TAC[o_DEF]) in
  REPEAT STRIP_TAC THEN
  SIMP_TAC[reduced_homology_group; GROUP_IMAGE_FROM_SUBGROUP_GENERATED;
           SUBGROUP_GROUP_KERNEL; GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY;
           CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
  REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
  REWRITE_TAC[group_image; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[group_kernel; IN_ELIM_THM; IN_IMAGE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[IN_INTER; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:A` THEN DISCH_TAC THEN
  X_GEN_TAC `y:((num->real)->A)frag->bool` THEN DISCH_TAC THEN
  EXISTS_TAC
   `group_div (homology_group (p,top)) y
    (hom_induced p (discrete_topology {one},{}) (top,{}) (\x. a)
     (hom_induced p (top,{}) (discrete_topology {one},{}) (\x:A. one) y))` THEN
  MP_TAC(ISPECL
   [`p:int`;`discrete_topology {one}`;  `top:A topology`; `(\x. a):1->A`]
   GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
  MP_TAC(ISPECL
   [`p:int`; `top:A topology`; `discrete_topology {one}`; `\x:A. one`]
   GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
  MP_TAC(ISPECL
   [`p:int`; `top:A topology`; `{}:A->bool`; `top:A topology`; `s:A->bool`;
    `\x:A. x`]
   GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
  MP_TAC(ISPECL
   [`p:int`;`discrete_topology {one}`; `{one}`;
    `top:A topology`; `s:A->bool`; `(\x. a):1->A`]
   GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
  MP_TAC(ISPECL
   [`p:int`; `top:A topology`; `s:A->bool`;
    `discrete_topology {one}`; `{one}`; `\x:A. one`]
   GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
  MP_TAC(ISPECL
   [`p:int`;`discrete_topology {one}`; `{}:1->bool`;
    `discrete_topology {one}`; `{one}`; `\x:1. x`]
   GROUP_HOMOMORPHISM_HOM_INDUCED) THEN
  SIMP_TAC[CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; IN_SING; SING_SUBSET] THEN
  REWRITE_TAC[SET_RULE `IMAGE (\x. a) s SUBSET {a}`] THEN
  REWRITE_TAC[group_homomorphism; GSYM homology_group] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THENL
   [ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [group_div; GROUP_INV] THEN
    MATCH_MP_TAC(MESON[GROUP_MUL_RID]
     `x IN group_carrier G /\ y = group_id G ==> x = group_mul G x y`) THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [GROUP_INV_EQ_ID] THEN
    TRANS_TAC EQ_TRANS
     `hom_induced p (discrete_topology {one},{one}) (top,s) (\x. (a:A))
        (hom_induced p (discrete_topology {one},{})
           (discrete_topology {one},{one}) (\x:1. x)
           (hom_induced p (top,{}) (discrete_topology {one},{}) (\x:A. one)
            y))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM o_THM] THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
        rator o lhand o snd) THEN
      REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; CONTINUOUS_MAP_CONST] THEN
      REWRITE_TAC[CONTINUOUS_MAP_ID] THEN
      ASM_SIMP_TAC[GSYM homology_group] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
        rator o rand o snd) THEN
      REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; CONTINUOUS_MAP_CONST] THEN
      ASM_REWRITE_TAC[CONTINUOUS_MAP_ID; SING_SUBSET] THEN
      ASM_SIMP_TAC[GSYM homology_group] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[o_DEF];
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `f w = z ==> x = w ==> f x = z`)) THEN
      MP_TAC(ISPECL [`p:int`; `discrete_topology {one}`]
        TRIVIAL_RELATIVE_HOMOLOGY_GROUP_TOPSPACE) THEN
      REWRITE_TAC[trivial_group; TOPSPACE_DISCRETE_TOPOLOGY] THEN
      ASM SET_TAC[]];
    MATCH_MP_TAC GROUP_DIV THEN ASM_SIMP_TAC[];
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [group_div; GROUP_INV] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [GSYM group_div; GROUP_DIV_EQ_ID] THEN
    REPLICATE_TAC 2 (GEN_REWRITE_TAC RAND_CONV [GSYM o_THM]) THEN
    ASM_SIMP_TAC[GSYM HOM_INDUCED_COMPOSE; CONTINUOUS_MAP_CONST;
                 TOPSPACE_DISCRETE_TOPOLOGY; IN_SING; IMAGE_CLAUSES;
                 EMPTY_SUBSET; lemma]]);;

let HOMOLOGY_EXACTNESS_REDUCED_1 = prove
 (`!p top s:A->bool.
        ~(topspace top INTER s = {})
        ==> group_exactness(reduced_homology_group(p,top),
                            relative_homology_group(p,top,s),
                            reduced_homology_group(p - &1,subtopology top s))
                           (hom_induced p (top,{}) (top,s) (\x. x),
                            hom_boundary p (top,s))`,
  REWRITE_TAC[group_exactness; GROUP_HOMOMORPHISM_HOM_BOUNDARY_REDUCED] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[reduced_homology_group] THEN
    MATCH_MP_TAC GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED THEN
    REWRITE_TAC[homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED];
    ALL_TAC] THEN
  REWRITE_TAC[reduced_homology_group;
              GROUP_KERNEL_TO_SUBGROUP_GENERATED;
              GROUP_IMAGE_TO_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[GSYM reduced_homology_group] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`]
        HOMOLOGY_EXACTNESS_AXIOM_1) THEN
  REWRITE_TAC[group_exactness] THEN
  DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
  MATCH_MP_TAC GROUP_IMAGE_REDUCED_HOMOLOGY_GROUP THEN
  ASM_REWRITE_TAC[]);;

let HOMOLOGY_EXACTNESS_REDUCED_2 = prove
 (`!p top s:A->bool.
      group_exactness(relative_homology_group(p,top,s),
                      reduced_homology_group(p - &1,subtopology top s),
                      reduced_homology_group(p - &1,top))
               (hom_boundary p (top,s),
                hom_induced (p - &1) (subtopology top s,{}) (top,{}) (\x. x))`,
  REWRITE_TAC[group_exactness; GROUP_HOMOMORPHISM_HOM_BOUNDARY_REDUCED] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED] THEN
  REWRITE_TAC[reduced_homology_group;
              GROUP_KERNEL_TO_SUBGROUP_GENERATED;
              GROUP_IMAGE_TO_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[GSYM reduced_homology_group] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`]
        HOMOLOGY_EXACTNESS_AXIOM_2) THEN
  REWRITE_TAC[group_exactness] THEN
  DISCH_THEN(MP_TAC o SYM o last o CONJUNCTS) THEN
  SIMP_TAC[reduced_homology_group; GROUP_KERNEL_FROM_SUBGROUP_GENERATED;
           SUBGROUP_GROUP_KERNEL; GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY;
           CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SET_RULE `s = s INTER t <=> s SUBSET t`] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`]
    GROUP_HOMOMORPHISM_HOM_BOUNDARY_REDUCED) THEN
  REWRITE_TAC[group_homomorphism; group_image] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP]);;

let HOMOLOGY_EXACTNESS_REDUCED_3 = prove
 (`!p top s:A->bool.
        group_exactness(reduced_homology_group(p,subtopology top s),
                        reduced_homology_group(p,top),
                        relative_homology_group(p,top,s))
                       (hom_induced p (subtopology top s,{}) (top,{}) (\x. x),
                        hom_induced p (top,{}) (top,s) (\x. x))`,
  REWRITE_TAC[group_exactness; GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[reduced_homology_group] THEN
    MATCH_MP_TAC GROUP_HOMOMORPHISM_FROM_SUBGROUP_GENERATED THEN
    REWRITE_TAC[homology_group; GROUP_HOMOMORPHISM_HOM_INDUCED];
    ALL_TAC] THEN
   REWRITE_TAC[reduced_homology_group;
              GROUP_KERNEL_TO_SUBGROUP_GENERATED;
              GROUP_IMAGE_TO_SUBGROUP_GENERATED] THEN
  REWRITE_TAC[GSYM reduced_homology_group] THEN
  MP_TAC(ISPECL [`p:int`; `top:A topology`; `s:A->bool`]
        HOMOLOGY_EXACTNESS_AXIOM_3) THEN
  REWRITE_TAC[group_exactness] THEN
  DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  MATCH_MP_TAC(SET_RULE
   `!u. s' SUBSET u /\ s' SUBSET s /\ u INTER t = t' /\ u INTER s SUBSET s'
        ==> s = t ==> s' = t'`) THEN
  EXISTS_TAC
   `group_carrier(reduced_homology_group (p,top:A topology))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:int`; `subtopology top s:A topology`;
                   `top:A topology`; `\x:A. x`]
        GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED) THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    SIMP_TAC[group_image; group_homomorphism];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[reduced_homology_group; group_image] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[GROUP_CARRIER_SUBGROUP_GENERATED_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP] THEN
  SIMP_TAC[reduced_homology_group; GROUP_KERNEL_FROM_SUBGROUP_GENERATED;
           SUBGROUP_GROUP_KERNEL; GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY;
           CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING;
           GROUP_IMAGE_FROM_SUBGROUP_GENERATED] THEN
  CONJ_TAC THENL [MATCH_ACCEPT_TAC INTER_COMM; ALL_TAC] THEN
  REWRITE_TAC[group_image] THEN MATCH_MP_TAC(SET_RULE
   `(!x. x IN s /\ f x IN k ==> x IN c)
    ==> k INTER IMAGE f s SUBSET IMAGE f s INTER IMAGE f c`) THEN
  X_GEN_TAC `x:((num->real)->A)frag->bool` THEN
  REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_THM] THEN
  W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
        rator o lhand o lhand o snd) THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; CONTINUOUS_MAP_CONST] THEN
  ASM_REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
  ASM_REWRITE_TAC[GSYM homology_group] THEN
  SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID; o_DEF]);;

let GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_OF_CONTRACTIBLE = prove
 (`!p top s:A->bool.
      contractible_space top /\ ~(topspace top INTER s = {})
      ==> group_isomorphism (relative_homology_group(p,top,s),
                             reduced_homology_group(p - &1,subtopology top s))
                            (hom_boundary p (top,s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`hom_induced p (top,{}) (top,s) (\x:A. x)`;
    `hom_boundary p (top:A topology,s)`;
    `hom_induced (p - &1) (subtopology top s,{}) (top,{}) (\x:A. x)`;
    `reduced_homology_group (p,top:A topology)`;
    `relative_homology_group (p,top:A topology,s)`;
    `reduced_homology_group (p - &1,subtopology top s:A topology)`;
    `reduced_homology_group (p - &1,top:A topology)`]
    VERY_SHORT_EXACT_SEQUENCE) THEN
  ASM_SIMP_TAC[TRIVIAL_REDUCED_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[HOMOLOGY_EXACTNESS_REDUCED_2] THEN
  ASM_SIMP_TAC[HOMOLOGY_EXACTNESS_REDUCED_1]);;

let ISOMORPHIC_GROUP_RELATIVE_HOMOLOGY_OF_CONTRACTIBLE = prove
 (`!p top s:A->bool.
        contractible_space top /\ ~(topspace top INTER s = {})
        ==> relative_homology_group(p,top,s) isomorphic_group
            reduced_homology_group(p - &1,subtopology top s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:int` o MATCH_MP
    GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_OF_CONTRACTIBLE) THEN
  REWRITE_TAC[isomorphic_group] THEN MESON_TAC[]);;

let ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_OF_CONTRACTIBLE = prove
 (`!p top s:A->bool.
        contractible_space top /\ ~(topspace top INTER s = {})
        ==> reduced_homology_group(p,subtopology top s) isomorphic_group
            relative_homology_group(p + &1,top,s)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  DISCH_THEN(MP_TAC o SPEC `p + &1:int` o MATCH_MP
    ISOMORPHIC_GROUP_RELATIVE_HOMOLOGY_OF_CONTRACTIBLE) THEN
  REWRITE_TAC[INT_ARITH `(x + &1) - &1:int = x`]);;

let GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_BY_CONTRACTIBLE = prove
 (`!p top s:A->bool.
      contractible_space(subtopology top s) /\ ~(topspace top INTER s = {})
      ==> group_isomorphism (reduced_homology_group(p,top),
                             relative_homology_group(p,top,s))
                            (hom_induced p (top,{}) (top,s) (\x. x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`hom_induced p (subtopology top s,{}) (top,{}) (\x:A. x)`;
    `hom_induced p (top,{}) (top,s) (\x:A. x)`;
    `hom_boundary p (top:A topology,s)`;
    `reduced_homology_group (p,subtopology top s:A topology)`;
    `reduced_homology_group (p,top:A topology)`;
    `relative_homology_group (p,top:A topology,s)`;
    `reduced_homology_group (p - &1,subtopology top s:A topology)`]
    VERY_SHORT_EXACT_SEQUENCE) THEN
  ASM_SIMP_TAC[TRIVIAL_REDUCED_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[HOMOLOGY_EXACTNESS_REDUCED_3] THEN
  ASM_SIMP_TAC[HOMOLOGY_EXACTNESS_REDUCED_1]);;

let ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_CONTRACTIBLE = prove
 (`!p top s:A->bool.
      contractible_space(subtopology top s) /\ ~(topspace top INTER s = {})
      ==> reduced_homology_group(p,top) isomorphic_group
          relative_homology_group(p,top,s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:int` o MATCH_MP
    GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_BY_CONTRACTIBLE) THEN
  REWRITE_TAC[isomorphic_group] THEN MESON_TAC[]);;

let ISOMORPHIC_GROUP_RELATIVE_HOMOLOGY_BY_CONTRACTIBLE = prove
 (`!p top s:A->bool.
      contractible_space(subtopology top s) /\ ~(topspace top INTER s = {})
      ==> relative_homology_group(p,top,s) isomorphic_group
          reduced_homology_group(p,top)`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_CONTRACTIBLE]);;

let ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_SING = prove
 (`!p top a:A.
        a IN topspace top
        ==> reduced_homology_group(p,top) isomorphic_group
            relative_homology_group(p,top,{a})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_CONTRACTIBLE THEN
  REWRITE_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_SING] THEN ASM SET_TAC[]);;

let ISOMORPHIC_GROUP_RELATIVE_HOMOLOGY_BY_SING = prove
 (`!p top a:A.
        a IN topspace top
        ==> relative_homology_group(p,top,{a}) isomorphic_group
            reduced_homology_group(p,top)`,
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_SING]);;

let REDUCED_HOMOLOGY_GROUP_PAIR = prove
 (`!p top a b:A.
        t1_space top /\ a IN topspace top /\ b IN topspace top /\ ~(a = b)
        ==> reduced_homology_group(p,subtopology top {a,b}) isomorphic_group
            homology_group(p,subtopology top {a})`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC ISOMORPHIC_GROUP_TRANS
   `relative_homology_group(p,subtopology top {a,b},{b:A})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISOMORPHIC_GROUP_REDUCED_HOMOLOGY_BY_SING THEN
    ASM_REWRITE_TAC[IN_INTER; TOPSPACE_SUBTOPOLOGY; IN_INSERT];
    ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group; homology_group] THEN MP_TAC(ISPECL
     [`p:int`; `subtopology top {a:A,b}`;
      `{a:A,b}`; `{b:A}`; `{b:A}`]
     HOMOLOGY_EXCISION_AXIOM) THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; DIFF_EQ_EMPTY; INTER_IDEMPOT] THEN
    ASM_SIMP_TAC[SET_RULE
     `~(a = b) ==> {a, b} INTER ({a, b} DIFF {b}) = {a}`] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    ASM_SIMP_TAC[SUBTOPOLOGY_EQ_DISCRETE_TOPOLOGY_FINITE;
                 TOPSPACE_SUBTOPOLOGY; INTER_SUBSET;
                 INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT; FINITE_EMPTY] THEN
    SIMP_TAC[DISCRETE_TOPOLOGY_CLOSURE_OF; DISCRETE_TOPOLOGY_INTERIOR_OF] THEN
    SET_TAC[]]);;

let DEFORMATION_RETRACTION_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS = prove
 (`!p top top' u v (r:A->B) s.
        retraction_maps(top,top') (r,s) /\
        IMAGE r u SUBSET v /\ IMAGE s v SUBSET u /\
        homotopic_with (\h. IMAGE h u SUBSET u) (top,top) (s o r) I
        ==> group_isomorphisms
             (relative_homology_group (p,top,u),
              relative_homology_group (p,top',v))
             (hom_induced p (top,u) (top',v) r,
              hom_induced p (top',v) (top,u) s)`,
  REWRITE_TAC[retraction_maps] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOMOTOPY_EQUIVALENCE_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_REWRITE_TAC[o_THM; I_DEF; IMAGE_ID; SUBSET_REFL; IMAGE_o] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]]);;

let DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS = prove
 (`!p top top' u v (r:A->A).
        retraction_maps(top,top') (r,I) /\ v SUBSET u /\ IMAGE r u SUBSET v /\
        homotopic_with (\h. IMAGE h u SUBSET u) (top,top) r I
        ==> group_isomorphisms
             (relative_homology_group (p,top,u),
              relative_homology_group (p,top',v))
             (hom_induced p (top,u) (top',v) r,
              hom_induced p (top',v) (top,u) (\x. x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM I_DEF] THEN
  MATCH_MP_TAC DEFORMATION_RETRACTION_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS THEN
  ASM_REWRITE_TAC[I_O_ID; IMAGE_I]);;

let DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM = prove
 (`!p top top' u v (r:A->A).
        retraction_maps(top,top') (r,I) /\ v SUBSET u /\ IMAGE r u SUBSET v /\
        homotopic_with (\h. IMAGE h u SUBSET u) (top,top) r I
        ==> group_isomorphism
             (relative_homology_group (p,top,u),
              relative_homology_group (p,top',v))
             (hom_induced p (top,u) (top',v) r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:int` o MATCH_MP
   DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS) THEN
  REWRITE_TAC[GROUP_ISOMORPHISMS_IMP_ISOMORPHISM]);;

let DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM_ID = prove
 (`!p top top' u v (r:A->A).
        retraction_maps(top,top') (r,I) /\ v SUBSET u /\ IMAGE r u SUBSET v /\
        homotopic_with (\h. IMAGE h u SUBSET u) (top,top) r I
        ==> group_isomorphism
             (relative_homology_group (p,top',v),
              relative_homology_group (p,top,u))
             (hom_induced p (top',v) (top,u) (\x. x))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:int` o MATCH_MP
   DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS) THEN
  REWRITE_TAC[GROUP_ISOMORPHISMS_IMP_ISOMORPHISM_ALT]);;

let DEFORMATION_RETRACTION_IMP_ISOMORPHIC_RELATIVE_HOMOLOGY_GROUPS = prove
 (`!p top top' u v (r:A->B) s.
        retraction_maps(top,top') (r,s) /\
        IMAGE r u SUBSET v /\ IMAGE s v SUBSET u /\
        homotopic_with (\h. IMAGE h u SUBSET u) (top,top) (s o r) I
        ==> relative_homology_group (p,top,u) isomorphic_group
            relative_homology_group (p,top',v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:int` o MATCH_MP
   DEFORMATION_RETRACTION_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS) THEN
  REWRITE_TAC[group_isomorphism; isomorphic_group] THEN MESON_TAC[]);;

let DEFORMATION_RETRACTION_IMP_ISOMORPHIC_HOMOLOGY_GROUPS = prove
 (`!p top top' (r:A->B) s.
        retraction_maps(top,top') (r,s) /\
        homotopic_with (\h. T) (top,top) (s o r) I
        ==> homology_group (p,top) isomorphic_group
            homology_group (p,top')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homology_group] THEN MATCH_MP_TAC
    DEFORMATION_RETRACTION_IMP_ISOMORPHIC_RELATIVE_HOMOLOGY_GROUPS THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN ASM_MESON_TAC[]);;

let DEFORMATION_RETRACT_IMP_ISOMORPHIC_RELATIVE_HOMOLOGY_GROUPS = prove
 (`!p top top' u v (r:A->A).
        retraction_maps(top,top') (r,I) /\ v SUBSET u /\ IMAGE r u SUBSET v /\
        homotopic_with (\h. IMAGE h u SUBSET u) (top,top) r I
        ==> relative_homology_group (p,top,u) isomorphic_group
            relative_homology_group (p,top',v)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `p:int` o MATCH_MP
   DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISMS) THEN
  REWRITE_TAC[group_isomorphism; isomorphic_group] THEN MESON_TAC[]);;

let DEFORMATION_RETRACT_IMP_ISOMORPHIC_HOMOLOGY_GROUPS = prove
 (`!p top top' (r:A->A).
        retraction_maps(top,top') (r,I) /\
        homotopic_with (\h. T) (top,top) r I
        ==> homology_group (p,top) isomorphic_group
            homology_group (p,top')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[homology_group] THEN MATCH_MP_TAC
    DEFORMATION_RETRACT_IMP_ISOMORPHIC_RELATIVE_HOMOLOGY_GROUPS THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Homology groups of spheres.                                               *)
(* ------------------------------------------------------------------------- *)

let GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_GROUP_LOWER_HEMISPHERE = prove
 (`!p n k. k IN 1..n+1
           ==> group_isomorphism
                (reduced_homology_group (p,nsphere n),
                 relative_homology_group (p,nsphere n,{x | x k <= &0}))
                (hom_induced p (nsphere n,{}) (nsphere n,{x | x k <= &0})
                               (\x. x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_BY_CONTRACTIBLE THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_LOWER_HEMISPHERE; GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `(\i. if i = k then -- &1 else &0):num->real` THEN
  REWRITE_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_UNIV; IN_UNIV] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[SUM_DELTA]);;

let GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_GROUP_UPPER_HEMISPHERE = prove
 (`!p n k.
        group_isomorphism
         (relative_homology_group
               (p,subtopology (nsphere n) {x | x k >= &0},{x | x k = &0}),
          relative_homology_group
               (p,nsphere n,{x | x k <= &0}))
         (hom_induced p
               (subtopology (nsphere n) {x | x k >= &0},{x | x k = &0})
               (nsphere n,{x | x k <= &0})
               (\x. x))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`p:int`;
    `nsphere n`;
    `(:num->real)`;
    `{x:num->real | x k <= &0}`;
    `{x:num->real | x k < -- &1 / &2}`]
   HOMOLOGY_EXCISION_AXIOM) THEN
  REWRITE_TAC[SET_RULE `UNIV DIFF {x | P x} = {x | ~P x}`] THEN
  REWRITE_TAC[SET_RULE `{x | P x} DIFF {x | Q x} = {x | ~Q x /\ P x}`] THEN
  REWRITE_TAC[REAL_NOT_LT; SUBSET_UNIV; SUBTOPOLOGY_UNIV] THEN
  ANTS_TAC THENL
   [TRANS_TAC SUBSET_TRANS
     `{x | x IN topspace(nsphere n) /\ x k IN {a | a <= -- &1 / &2}}` THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT] THEN
      MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN CONJ_TAC THENL
       [SIMP_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
        EXISTS_TAC `euclideanreal` THEN
        REWRITE_TAC[REAL_CLOSED_HALFSPACE_LE; GSYM REAL_CLOSED_IN] THEN
        REWRITE_TAC[NSPHERE] THEN
        MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
        SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV]];
      ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS
     `{x | x IN topspace(nsphere n) /\ x k IN {a | a < &0}}` THEN
    CONJ_TAC THENL
     [SIMP_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
     [SIMP_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN
    REWRITE_TAC[REAL_OPEN_HALFSPACE_LT; GSYM REAL_OPEN_IN] THEN
    REWRITE_TAC[NSPHERE] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    SIMP_TAC[CONTINUOUS_MAP_PRODUCT_PROJECTION; IN_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`p:int`;
    `subtopology (nsphere n) {x | -- &1 / &2 <= x k}`;
    `subtopology (nsphere n) {x | &0 <= x k}`;
    `topspace(subtopology (nsphere n) {x | -- &1 / &2 <= x k}) INTER
     {x:num->real | -- &1 / &2 <= x k /\ x k <= &0}`;
    `topspace(subtopology (nsphere n) {x | &0 <= x k}) INTER
     {x:num->real | x k = &0}`]
   DEFORMATION_RETRACT_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM_ID) THEN
  REWRITE_TAC[GSYM HOM_INDUCED_RESTRICT;
             GSYM RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_ISOMORPHISM_COMPOSE) THEN
    REWRITE_TAC[real_ge] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[o_DEF]] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_IN_SUBTOPOLOGY;
             CONTINUOUS_MAP_ID; IMAGE_ID] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; IN_INTER; IN_ELIM_THM] THEN
    REAL_ARITH_TAC] THEN
  ABBREV_TAC
   `h = \(t,x). let y = max (x k) (--t) in
                \i. if i:num = k then y
                    else sqrt(&1 - y pow 2) / sqrt(&1 - x k pow 2) * x i` THEN
  SUBGOAL_THEN
   `!t x. &0 <= t /\ t <= &1 /\ x IN topspace(nsphere n) /\ --t <= x k
          ==> h(t,x) = x`
  ASSUME_TAC THENL
   [REWRITE_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_ARITH `t <= x ==> max x t = x`] THEN
    CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(x:num->real) k pow 2 = &1` THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; REAL_MUL_LID; SQRT_EQ_0; REAL_SUB_0] THEN
    ASM_CASES_TAC `k IN 1..n+1` THENL
     [ALL_TAC; ASM_MESON_TAC[REAL_ARITH `~(&0 pow 2 = &1)`]] THEN
    MATCH_MP_TAC(REAL_RING `x = &0 ==> a * x = x`) THEN
    ASM_CASES_TAC `i IN 1..n+1` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[MESON[REAL_LT_POW_2] `x = &0 <=> ~(&0 < x pow 2)`] THEN
    DISCH_TAC THEN UNDISCH_TAC `sum (1..n + 1) (\i. x i pow 2) = &1` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a = &1 ==> a < b ==> b = &1 ==> F`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&0 < x ==> x + y <= s ==> y < s`)) THEN
    TRANS_TAC REAL_LE_TRANS `sum {i:num,k} (\j. x j pow 2)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ADD_RID; REAL_LE_REFL];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; FINITE_NUMSEG] THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
     (prod_topology (subtopology euclideanreal (real_interval [&0,&1]))
                    (subtopology (nsphere n) {x | -- &1 / &2 <= x k}),
      nsphere n) h`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [NSPHERE] THEN
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_COMPONENTWISE_UNIV];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY] THEN
      REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `x:num->real`] THEN
      REWRITE_TAC[NSPHERE; TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `--t <= (x:num->real) k` THEN
      ASM_SIMP_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      ASM_CASES_TAC `~(&0 <= (x:num->real) k)` THENL
       [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      SUBGOAL_THEN `k IN 1..n+1` ASSUME_TAC THENL
       [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
      EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
      ABBREV_TAC `y = max ((x:num->real) k) (--t)` THEN
      CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
      ASM_SIMP_TAC[REAL_MUL_RZERO] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      REWRITE_TAC[COND_RAND; COND_RATOR; REAL_POW_MUL] THEN
      SIMP_TAC[SUM_CASES; FINITE_NUMSEG; SUM_LMUL; FINITE_RESTRICT] THEN
      ASM_SIMP_TAC[SET_RULE `k IN s ==> {x | x IN s /\ x = k} = {k}`] THEN
      REWRITE_TAC[SUM_SING; REAL_POW_DIV] THEN
      SUBGOAL_THEN `(x:num->real) k pow 2 <= &1 pow 2 /\ y pow 2 <= &1 pow 2`
      MP_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
        CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC] THEN
      SUBGOAL_THEN `abs((x:num->real) k) <= &1 /\ abs y <= &1`
      STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_SUB_LE; GSYM DELETE] THEN
      ASM_SIMP_TAC[SUM_DELETE; FINITE_NUMSEG] THEN
      MATCH_MP_TAC(REAL_FIELD
       `~(x = &1) ==> y + (&1 - y) / (&1 - x) * (&1 - x) = &1`) THEN
      MATCH_MP_TAC(REAL_ARITH `x < &1 pow 2 ==> ~(x = &1)`) THEN
      REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
      ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `i:num` THEN MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `\(t,x). if &0 <= x k then x i
                        else (h:real#(num->real)->(num->real)) (t,x) i` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      MAP_EVERY X_GEN_TAC [`t:real`; `x:num->real`] THEN
      REWRITE_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC SYM_CONV THEN AP_THM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[LAMBDA_PAIR] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_CASES_LE THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_OF_SND] THEN REWRITE_TAC[NSPHERE] THEN
      DISJ2_TAC THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN REWRITE_TAC[IN_UNIV];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_OF_SND] THEN REWRITE_TAC[NSPHERE] THEN
      DISJ2_TAC THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN REWRITE_TAC[IN_UNIV];
      ALL_TAC;
      REWRITE_TAC[FORALL_PAIR_THM; TOPSPACE_PROD_TOPOLOGY; IN_CROSS] THEN
      REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; IN_REAL_INTERVAL] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
      REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
      AP_THM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [LAMBDA_PAIR_THM] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [LAMBDA_PAIR] THEN
    ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN
      REWRITE_TAC[CONTINUOUS_MAP_OF_FST; CONTINUOUS_MAP_OF_SND] THEN
      CONJ_TAC THEN DISJ2_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
      SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_REAL_NEG;
               CONTINUOUS_MAP_ID] THEN
      REWRITE_TAC[NSPHERE] THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN REWRITE_TAC[IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
      REWRITE_TAC[CONTINUOUS_MAP_OF_SND] THEN
      REWRITE_TAC[NSPHERE] THEN DISJ2_TAC THEN
      REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
      MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN
      REWRITE_TAC[IN_UNIV]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_DIV THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; SQRT_EQ_0;
                  FORALL_PAIR_THM; IN_CROSS; TOPSPACE_PROD_TOPOLOGY] THEN
      REWRITE_TAC[REAL_RING `&1 - x pow 2 = &0 <=> x = &1 \/ x = -- &1`] THEN
      REAL_ARITH_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY THEN
    MATCH_MP_TAC CONTINUOUS_MAP_SQRT THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_POW THENL
     [MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX; ALL_TAC] THEN
    REWRITE_TAC[CONTINUOUS_MAP_REAL_NEG_EQ; CONTINUOUS_MAP_OF_SND;
                CONTINUOUS_MAP_OF_FST] THEN
    REPEAT CONJ_TAC THEN DISJ2_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_REAL_NEG;
             CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[NSPHERE] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_PRODUCT_PROJECTION THEN
    REWRITE_TAC[IN_UNIV] THEN
    AP_THM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `(h:real#(num->real)->(num->real)) o (\x. &0,x)` THEN
  REWRITE_TAC[retraction_maps] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        CONTINUOUS_MAP_COMPOSE)) THEN
      REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF; CONTINUOUS_MAP_ID] THEN
      REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      REWRITE_TAC[CONTINUOUS_MAP_REAL_CONST; SUBSET; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY] THEN
      EXPAND_TAC "h" THEN REWRITE_TAC[IN_ELIM_THM; IN_INTER; o_DEF] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; I_DEF] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; o_DEF; I_DEF] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_NEG_0];
    SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM; SUBSET] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SET_RULE
     `(s INTER {x | P x}) INTER {x | Q x} = s INTER {x | P x /\ Q x}`] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x /\ x = &0 <=> x = &0`] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN CONJ_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(MP_TAC o
        MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
      MATCH_MP_TAC(SET_RULE
       `s SUBSET t ==> IMAGE h t SUBSET u ==> IMAGE h s SUBSET u`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; TOPSPACE_PROD_TOPOLOGY] THEN
      SIMP_TAC[IN_CROSS; IN_INTER; IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY;
               TOPSPACE_EUCLIDEANREAL; IN_UNIV; IN_REAL_INTERVAL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      EXPAND_TAC "h" THEN REWRITE_TAC[SUBSET; o_DEF; FORALL_IN_IMAGE] THEN
      CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
    W(MP_TAC o PART_MATCH (lhand o rand) HOMOTOPIC_WITH o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET; FORALL_IN_IMAGE] THEN
      SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    EXISTS_TAC `h:real#(num->real)->(num->real)`] THEN
  REWRITE_TAC[o_THM; I_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN EXPAND_TAC "h" THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    REWRITE_TAC[TOPSPACE_PROD_TOPOLOGY; IN_CROSS; TOPSPACE_SUBTOPOLOGY;
                IN_INTER; IN_ELIM_THM] THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM o_DEF] THEN
    REWRITE_TAC[SET_RULE
     `(s INTER {x | P x}) INTER {x | P x /\ Q x} =
      s INTER {x | P x /\ Q x}`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[IMAGE_o; TOPSPACE_PROD_TOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN MATCH_MP_TAC(SET_RULE
     `i SUBSET p /\ (!x. x IN i ==> h x IN v)
      ==> IMAGE h p SUBSET u
          ==> IMAGE h i SUBSET u INTER v`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CROSS; IN_ELIM_THM; IN_INTER] THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL] THEN EXPAND_TAC "h" THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let GROUP_ISOMORPHISM_UPPER_HEMISPHERE_REDUCED_HOMOLOGY_GROUP = prove
 (`!p n. group_isomorphism
           (relative_homology_group
                (p + &1,subtopology (nsphere (n + 1)) {x | x(n+2) >= &0},
                        {x | x(n+2) = &0}),
            reduced_homology_group(p,nsphere n))
           (hom_boundary (p + &1)
                         (subtopology (nsphere (n + 1)) {x | x(n+2) >= &0},
                         {x | x(n+2) = &0}))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `nsphere n =
    subtopology (subtopology (nsphere (n + 1)) {x | x(n+2) >= &0})
                {x | x(n+2) = &0}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM SUBTOPOLOGY_NSPHERE_EQUATOR] THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `q:int = p + &1` THEN
  SUBGOAL_THEN `p:int = q - &1` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_OF_CONTRACTIBLE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTRACTIBLE_SPACE_UPPER_HEMISPHERE THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM; real_ge; IN_UNIV;
                TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY; NSPHERE;
                o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
    EXISTS_TAC `(\i. if i = n + 1 then &1 else &0):num->real` THEN
    ASM_REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
    REWRITE_TAC[ARITH_RULE `~(n + 2 = n + 1)`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [REWRITE_TAC[COND_RAND; COND_RATOR] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_GROUP_UPPER_HEMISPHERE = prove
 (`!p n k. k IN 1..n+1
           ==> group_isomorphism
                (reduced_homology_group (p,nsphere n),
                 relative_homology_group (p,nsphere n,{x | x k >= &0}))
                (hom_induced p (nsphere n,{}) (nsphere n,{x | x k >= &0})
                               (\x. x))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_BY_CONTRACTIBLE THEN
  ASM_SIMP_TAC[CONTRACTIBLE_SPACE_UPPER_HEMISPHERE; GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `(\i. if i = k then &1 else &0):num->real` THEN
  REWRITE_TAC[NSPHERE; TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_ELIM_THM] THEN
  REWRITE_TAC[TOPSPACE_PRODUCT_TOPOLOGY; o_DEF; TOPSPACE_EUCLIDEANREAL] THEN
  REWRITE_TAC[CARTESIAN_PRODUCT_UNIV; IN_UNIV] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[SUM_DELTA]);;

let GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_GROUP_LOWER_HEMISPHERE = prove
 (`!p n k.
        group_isomorphism
         (relative_homology_group
               (p,subtopology (nsphere n) {x | x k <= &0},{x | x k = &0}),
          relative_homology_group
               (p,nsphere n,{x | x k >= &0}))
         (hom_induced p
               (subtopology (nsphere n) {x | x k <= &0},{x | x k = &0})
               (nsphere n,{x | x k >= &0})
               (\x. x))`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC_ALL
    GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_GROUP_UPPER_HEMISPHERE) THEN
  MATCH_MP_TAC(MESON[GROUP_ISOMORPHISM_COMPOSE]
    `!f h. group_isomorphism(G',G) f /\
           group_isomorphism(H,H') h /\ h o g o f = k
           ==> group_isomorphism(G,H) g
               ==> group_isomorphism(G',H') k`) THEN
  ABBREV_TAC `r = \(x:num->real) i. if i = k then --x i else x i` THEN
  MP_TAC(SPECL [`n:num`; `k:num`] CONTINUOUS_MAP_NSPHERE_REFLECTION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!x:num->real. r(r x) = x` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN SIMP_TAC[FUN_EQ_THM; REAL_NEG_NEG] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`hom_induced p (subtopology (nsphere n) {x | x k <= &0},{x | x k = &0})
       (subtopology (nsphere n) {x | x k >= &0},{x | x k = &0}) r`;
    `hom_induced p (nsphere n,{x | x k <= &0})
                   (nsphere n,{x | x k >= &0}) r`] THEN
  ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN
    ONCE_REWRITE_TAC[HOM_INDUCED_RESTRICT;
                    RELATIVE_HOMOLOGY_GROUP_RESTRICT] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_RELATIVE_HOMOLOGY_GROUP_ISOMORPHISM THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
       EXISTS_TAC `r:(num->real)->(num->real)` THEN
       ASM_REWRITE_TAC[homeomorphic_maps];
       ALL_TAC]);
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
      rand o lhand o snd) THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    ANTS_TAC THENL
     [ALL_TAC;
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [ALL_TAC;
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[o_DEF]]]] THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; o_DEF; ETA_AX] THEN
  ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; SET_RULE
   `(!x. r(r x) = x)
    ==> (IMAGE r s = t <=> IMAGE r s SUBSET t /\ IMAGE r t SUBSET s)`] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM;
              TOPSPACE_SUBTOPOLOGY] THEN
  FIRST_X_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[continuous_map]) THEN
  ASM_SIMP_TAC[] THEN EXPAND_TAC "r" THEN REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let GROUP_ISOMORPHISM_LOWER_HEMISPHERE_REDUCED_HOMOLOGY_GROUP = prove
 (`!p n. group_isomorphism
           (relative_homology_group
                (p + &1,subtopology (nsphere (n + 1)) {x | x(n+2) <= &0},
                        {x | x(n+2) = &0}),
            reduced_homology_group(p,nsphere n))
           (hom_boundary (p + &1)
                         (subtopology (nsphere (n + 1)) {x | x(n+2) <= &0},
                         {x | x(n+2) = &0}))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `nsphere n =
    subtopology (subtopology (nsphere (n + 1)) {x | x(n+2) <= &0})
                {x | x(n+2) = &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[NSPHERE; SUBTOPOLOGY_SUBTOPOLOGY] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:num->real` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = SUC(n + 1)`; SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`; NUMSEG_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `SUC(n + 1) = n + 2`; IN_INSERT] THEN
    REWRITE_TAC[REAL_ARITH `x >= &0 /\ x = &0 <=> x = &0`; IN_NUMSEG] THEN
    ASM_CASES_TAC `(x:num->real)(n + 2) = &0` THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `~(n + 2 <= n + 1)`]] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ADD_RID] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q:int = p + &1` THEN
  SUBGOAL_THEN `p:int = q - &1` SUBST1_TAC THENL
   [EXPAND_TAC "q" THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_OF_CONTRACTIBLE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTRACTIBLE_SPACE_LOWER_HEMISPHERE THEN
    REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM; real_ge; IN_UNIV;
                TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY; NSPHERE;
                o_DEF; TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
    EXISTS_TAC `(\i. if i = n + 1 then &1 else &0):num->real` THEN
    ASM_REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
    REWRITE_TAC[ARITH_RULE `~(n + 2 = n + 1)`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [REWRITE_TAC[COND_RAND; COND_RATOR] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
      GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let REDUCED_HOMOLOGY_GROUP_NSPHERE_STEP = prove
 (`!p n. ?f.
        group_isomorphism(reduced_homology_group (p,nsphere n),
                          reduced_homology_group(p + &1,nsphere (n + 1))) f /\
        !c. c IN group_carrier(reduced_homology_group(p,nsphere n))
            ==> hom_induced (p + &1) (nsphere(n + 1),{}) (nsphere(n + 1),{})
                            (\x i. if i = 1 then --x i else x i)
                            (f c) =
                f (hom_induced p (nsphere n,{}) (nsphere n,{})
                               (\x i. if i = 1 then --x i else x i) c)`,
  let isomorphism_sym = prove
   (`!G1 G2 (r:A->A) (r':A->A).
        (?f. group_isomorphism(G1,G2) f /\
             !x. x IN group_carrier G1 ==> r'(f x) = f(r x))
        ==> (!x. x IN group_carrier G1 ==> r x IN group_carrier G1)
            ==> (?f. group_isomorphism(G2,G1) f /\
                     !x. x IN group_carrier G2 ==> r(f x) = f(r' x))`,
    REPEAT GEN_TAC THEN REWRITE_TAC[TAUT
     `p ==> q ==> r <=> q ==> p ==> r`] THEN DISCH_TAC THEN
    REWRITE_TAC[group_isomorphism; LEFT_AND_EXISTS_THM] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC[group_isomorphisms; group_homomorphism] THEN
    ASM SET_TAC[])
  and isomorphism_trans = prove
   (`!G1 G2 G3 (r:A->A) (r':A->A) (r'':A->A).
        (?f. group_isomorphism(G1,G2) f /\
             !x. x IN group_carrier G1 ==> r'(f x) = f(r x)) /\
        (?f. group_isomorphism(G2,G3) f /\
             !x. x IN group_carrier G2 ==> r''(f x) = f(r' x))
        ==> (?f. group_isomorphism(G1,G3) f /\
                 !x. x IN group_carrier G1 ==> r''(f x) = f(r x))`,
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `f:A->A` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `g:A->A` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `(g:A->A) o (f:A->A)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[GROUP_ISOMORPHISM_COMPOSE]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GROUP_ISOMORPHISM]) THEN
    REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]) in
  REPEAT GEN_TAC THEN
  ABBREV_TAC `r = \(x:num->real) i. if i = 1 then --x i else x i` THEN
  SUBGOAL_THEN
   `!n. continuous_map (nsphere n,nsphere n) r`
  ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[CONTINUOUS_MAP_NSPHERE_REFLECTION];
    ALL_TAC] THEN
  MATCH_MP_TAC isomorphism_trans THEN
  MAP_EVERY EXISTS_TAC
   [`relative_homology_group(p + &1,
           subtopology (nsphere (n + 1)) {x | x (n + 2) >= &0},
           {x | x (n + 2) = &0})`;
    `hom_induced (p + &1)
                 (subtopology (nsphere (n + 1)) {x | x (n + 2) >= &0},
                  {x | x (n + 2) = &0})
                 (subtopology (nsphere (n + 1)) {x | x (n + 2) >= &0},
                  {x | x (n + 2) = &0}) r`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_IMP] isomorphism_sym) THEN
    REWRITE_TAC[HOM_INDUCED] THEN
    EXISTS_TAC `hom_boundary (p + &1)
         (subtopology (nsphere (n + 1)) {x | x (n + 2) >= &0},
          {x | x (n + 2) = &0})` THEN
    SIMP_TAC[GROUP_ISOMORPHISM_UPPER_HEMISPHERE_REDUCED_HOMOLOGY_GROUP] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINOP_CONV [GSYM o_THM] THEN AP_THM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NATURALITY_HOM_INDUCED o
      rand o snd) THEN
    REWRITE_TAC[INT_ARITH `(p + &1) - &1:int = p`] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                   CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM;
                  TOPSPACE_SUBTOPOLOGY] THEN
      EXPAND_TAC "r" THEN SIMP_TAC[ARITH_RULE `~(n + 2 = 1)`];
      DISCH_THEN SUBST1_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      REWRITE_TAC[SET_RULE `{x | P x} INTER {x | Q x} = {x | P x /\ Q x}`] THEN
      REWRITE_TAC[REAL_ARITH `x:real >= &0 /\ x = &0 <=> x = &0`] THEN
      REWRITE_TAC[SUBTOPOLOGY_NSPHERE_EQUATOR]];
    ALL_TAC] THEN
  MATCH_MP_TAC isomorphism_trans THEN
  MAP_EVERY EXISTS_TAC
   [`relative_homology_group(p + &1,nsphere (n + 1),{x | x(n + 2) <= &0})`;
    `hom_induced (p + &1)
                 (nsphere (n + 1),{x | x (n + 2) <= &0})
                 (nsphere (n + 1),{x | x (n + 2) <= &0}) r`] THEN
  CONJ_TAC THENL
   [EXISTS_TAC
     `hom_induced (p + &1)
          (subtopology (nsphere(n + 1)) {x | x(n+2) >= &0},{x | x(n+2) = &0})
          (nsphere(n+1),{x | x(n+2) <= &0})
         (\x. x)` THEN
    SIMP_TAC[GROUP_ISOMORPHISM_RELATIVE_HOMOLOGY_GROUP_UPPER_HEMISPHERE] THEN
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC BINOP_CONV [GSYM o_THM] THEN AP_THM_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
      rand o snd) THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_ID;
                 CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    ANTS_TAC THENL
     [EXPAND_TAC "r" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IN_ELIM_THM; TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      SIMP_TAC[ARITH_RULE `~(n + 2 = 1)`; REAL_LE_REFL];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
      lhand o snd) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[o_DEF]] THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    SIMP_TAC[IN_ELIM_THM; ARITH_RULE `~(n + 2 = 1)`; REAL_LE_REFL];
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_IMP] isomorphism_sym) THEN
    SIMP_TAC[HOM_INDUCED_REDUCED] THEN
    EXISTS_TAC `hom_induced (p + &1) (nsphere(n + 1),{})
                        (nsphere (n + 1),{x | x(n + 2) <= &0}) (\x. x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC
        GROUP_ISOMORPHISM_REDUCED_HOMOLOGY_GROUP_LOWER_HEMISPHERE THEN
      REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC BINOP_CONV [GSYM o_THM] THEN AP_THM_TAC THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
        rand o snd) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONTINUOUS_MAP_ID; EMPTY_SUBSET] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
        lhand o snd) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONTINUOUS_MAP_ID; EMPTY_SUBSET] THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[o_DEF]] THEN
      EXPAND_TAC "r" THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      REWRITE_TAC[ARITH_RULE `~(n + 2 = 1)`]]]);;

let REDUCED_HOMOLOGY_GROUP_NSPHERE = prove
 (`(!n. reduced_homology_group(&n,nsphere n) isomorphic_group integer_group) /\
   (!n p. ~(p = &n) ==> trivial_group(reduced_homology_group(p,nsphere n)))`,
  ONCE_REWRITE_TAC[MESON[]
   `(!n. P (&n:int) n) /\ (!n p. ~(p = &n) ==> Q p n) <=>
    !n p. (p = &n ==> P p n) /\ (~(p = &n) ==> Q p n)`] THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [X_GEN_TAC `p:int` THEN
    SUBGOAL_THEN
     `subtopology (product_topology (:num) (\i. euclideanreal))
                  {(\i. if i = 1 then &1 else &0),
                   (\i. if i = 1 then -- &1 else &0)} =
      nsphere 0`
    ASSUME_TAC THENL
     [REWRITE_TAC[NSPHERE; ADD_CLAUSES; NUMSEG_SING; SUM_SING; IN_SING] THEN
      AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:num->real` THEN REWRITE_TAC[FUN_EQ_THM; IN_ELIM_THM] THEN
      REWRITE_TAC[REAL_RING `x pow 2 = &1 <=> x = &1 \/ x = -- &1`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`p:int`; `product_topology (:num) (\i. euclideanreal)`;
      `(\i. if i = 1 then &1 else &0):num->real`;
      `(\i. if i = 1 then -- &1 else &0):num->real`]
      REDUCED_HOMOLOGY_GROUP_PAIR) THEN
    REWRITE_TAC[T1_SPACE_PRODUCT_TOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY] THEN
    REWRITE_TAC[T1_SPACE_EUCLIDEANREAL; o_DEF; TOPSPACE_EUCLIDEANREAL] THEN
    ASM_REWRITE_TAC[CARTESIAN_PRODUCT_UNIV; IN_UNIV] THEN ANTS_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `1`) THEN
      REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    ABBREV_TAC `a:num->real = \i. if i = 1 then &1 else &0` THEN
    ASM_CASES_TAC `p:int = &0` THEN ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL
       [`subtopology (product_topology (:num) (\i. euclideanreal)) {a}`;
        `a:num->real`] HOMOLOGY_COEFFICIENTS);
      MP_TAC(ISPECL
       [`p:int`;
        `subtopology (product_topology (:num) (\i. euclideanreal)) {a}`;
        `a:num->real`] HOMOLOGY_DIMENSION_AXIOM)] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY; o_DEF] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV] THEN
    ASM_REWRITE_TAC[INTER_UNIV; GSYM IMP_CONJ_ALT] THEN
    REWRITE_TAC[ISOMORPHIC_GROUP_TRANS; IMP_CONJ] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `p:int` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p - &1:int`) THEN
  SUBST1_TAC(INT_ARITH `p:int = (p - &1) + &1`) THEN
  REWRITE_TAC[INT_EQ_ADD_RCANCEL; INT_ARITH `(x + &1) - &1:int = x`] THEN
  SPEC_TAC(`p - &1:int`,`p:int`) THEN X_GEN_TAC `p:int` THEN
  REWRITE_TAC[ADD1] THEN
  SUBGOAL_THEN
   `reduced_homology_group (p + &1,nsphere (n + 1))
    isomorphic_group reduced_homology_group (p,nsphere n)`
  MP_TAC THENL
   [ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
    REWRITE_TAC[isomorphic_group] THEN
    MESON_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE_STEP];
    ASM_CASES_TAC `p:int = &n` THEN
    ASM_REWRITE_TAC[IMP_IMP; ISOMORPHIC_GROUP_TRANS] THEN
    REWRITE_TAC[IMP_CONJ] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP ISOMORPHIC_GROUP_TRIVIALITY) THEN
    REWRITE_TAC[]]);;

let CYCLIC_REDUCED_HOMOLOGY_GROUP_NSPHERE = prove
 (`!p n. cyclic_group(reduced_homology_group(p,nsphere n))`,
  ASM_MESON_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE;
                TRIVIAL_IMP_CYCLIC_GROUP; ISOMORPHIC_GROUP_CYCLICITY;
                CYCLIC_INTEGER_GROUP]);;

let TRIVIAL_REDUCED_HOMOLOGY_GROUP_NSPHERE = prove
 (`!p n. trivial_group(reduced_homology_group (p,nsphere n)) <=> ~(p = &n)`,
  MESON_TAC[NON_TRIVIAL_INTEGER_GROUP; REDUCED_HOMOLOGY_GROUP_NSPHERE;
            ISOMORPHIC_GROUP_TRIVIALITY]);;

(* ------------------------------------------------------------------------- *)
(* Brouwer degree of a map f:S^n->S^n.                                       *)
(* ------------------------------------------------------------------------- *)

let brouwer_degree2 = new_definition
 `brouwer_degree2 p f =
    @d. !x. x IN group_carrier(reduced_homology_group(&p,nsphere p))
            ==> hom_induced (&p) (nsphere p,{}) (nsphere p,{}) f x =
                group_zpow (reduced_homology_group (&p,nsphere p)) x d`;;

let BROUWER_DEGREE2_EQ = prove
 (`!p f g.
    (!x. x IN topspace(nsphere p) ==> f x = g x)
    ==> brouwer_degree2 p f = brouwer_degree2 p g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP HOM_INDUCED_EQ) THEN
  ASM_REWRITE_TAC[brouwer_degree2]);;

let BROUWER_DEGREE2 = prove
 (`!p f x. x IN group_carrier(reduced_homology_group(&p,nsphere p))
            ==> hom_induced (&p) (nsphere p,{}) (nsphere p,{}) f x =
                group_zpow (reduced_homology_group (&p,nsphere p))
                           x (brouwer_degree2 p f)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[brouwer_degree2] THEN
  CONV_TAC SELECT_CONV THEN
  ASM_CASES_TAC `continuous_map(nsphere p,nsphere p) f` THENL
   [ALL_TAC;
    EXISTS_TAC `&0:int` THEN
    ASM_SIMP_TAC[HOM_INDUCED_DEFAULT; GROUP_ZPOW_POW; group_pow] THEN
    SIMP_TAC[reduced_homology_group; SUBGROUP_GENERATED; homology_group]] THEN
  MP_TAC(ISPECL [`&p:int`; `p:num`] CYCLIC_REDUCED_HOMOLOGY_GROUP_NSPHERE) THEN
  REWRITE_TAC[cyclic_group; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:((num->real)->num->real)frag->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CARRIER_SUBGROUP_GENERATED_BY_SING) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `hom_induced (&p) (nsphere p,{}) (nsphere p,{}) f a` o
    MATCH_MP(SET_RULE `s = t ==> !x. x IN t ==> x IN s`)) THEN
  ASM_SIMP_TAC[HOM_INDUCED_REDUCED; IN_ELIM_THM; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:int` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV o RAND_CONV) [GSYM th]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:int` THEN
  ASM_SIMP_TAC[GSYM GROUP_ZPOW_MUL] THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  ASM_SIMP_TAC[GROUP_ZPOW_MUL] THEN
  FIRST_X_ASSUM(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
        GROUP_HOMOMORPHISM_ZPOW) THEN
  ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED]);;

let BROUWER_DEGREE2_IFF = prove
 (`!p f x d.
        continuous_map (nsphere p,nsphere p) f /\
        x IN group_carrier(reduced_homology_group(&p,nsphere p))
        ==> (hom_induced (&p) (nsphere p,{}) (nsphere p,{}) f x =
             group_zpow (reduced_homology_group (&p,nsphere p)) x d <=>
             x = group_id(reduced_homology_group(&p,nsphere p)) \/
             brouwer_degree2 p f = d)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`&p:int`; `p:num`]
   CYCLIC_REDUCED_HOMOLOGY_GROUP_NSPHERE) THEN
  REWRITE_TAC[cyclic_group; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:((num->real)->num->real)frag->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
    (BINDER_CONV o LAND_CONV o funpow 2 RAND_CONV) [GSYM th]) THEN
  ASM_SIMP_TAC[CARRIER_SUBGROUP_GENERATED_BY_SING; FORALL_IN_GSPEC;
               BROUWER_DEGREE2; GROUP_ZPOW] THEN
  ASM_SIMP_TAC[IN_UNIV; GSYM GROUP_ZPOW_MUL; GROUP_ZPOW_EQ] THEN
  REPEAT GEN_TAC THEN ASM_SIMP_TAC[GROUP_ZPOW_EQ_ID] THEN
  MATCH_MP_TAC(INTEGER_RULE
   `d:int = &0 ==> (d divides n * a - n * b <=> d divides n \/ b = a)`) THEN
  ASM_SIMP_TAC[INT_OF_NUM_EQ; GSYM INFINITE_CYCLIC_SUBGROUP_ORDER] THEN
  MP_TAC INFINITE_INTEGER_GROUP THEN MATCH_MP_TAC EQ_IMP THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ISOMORPHIC_GROUP_INFINITENESS THEN
  REWRITE_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE]);;

let BROUWER_DEGREE2_UNIQUE = prove
 (`!p f d. continuous_map (nsphere p,nsphere p) f /\
           (!x. x IN group_carrier(reduced_homology_group(&p,nsphere p))
                ==> hom_induced (&p) (nsphere p,{}) (nsphere p,{}) f x =
                    group_zpow (reduced_homology_group (&p,nsphere p)) x d)
           ==> brouwer_degree2 p f = d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&p:int`; `p:num`] CYCLIC_REDUCED_HOMOLOGY_GROUP_NSPHERE) THEN
  REWRITE_TAC[cyclic_group; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:((num->real)->num->real)frag->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `a:((num->real)->num->real)frag->bool`) THEN
  ASM_SIMP_TAC[BROUWER_DEGREE2; GROUP_ZPOW_EQ] THEN
  MATCH_MP_TAC(INTEGER_RULE `d:int = &0 ==> d divides b - a ==> a = b`) THEN
  ASM_SIMP_TAC[INT_OF_NUM_EQ; GSYM INFINITE_CYCLIC_SUBGROUP_ORDER] THEN
  MP_TAC INFINITE_INTEGER_GROUP THEN MATCH_MP_TAC EQ_IMP THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ISOMORPHIC_GROUP_INFINITENESS THEN
  REWRITE_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE]);;

let BROUWER_DEGREE2_UNIQUE_GENERATOR = prove
 (`!p f d a.
        continuous_map (nsphere p,nsphere p) f /\
        subgroup_generated (reduced_homology_group (&p,nsphere p)) {a} =
        reduced_homology_group (&p,nsphere p) /\
        hom_induced (&p) (nsphere p,{}) (nsphere p,{}) f a =
        group_zpow (reduced_homology_group (&p,nsphere p)) a d
        ==> brouwer_degree2 p f = d`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC
   `a IN group_carrier(reduced_homology_group (&p,nsphere p))`
  THENL
   [ASM_SIMP_TAC[BROUWER_DEGREE2; GROUP_ZPOW_EQ] THEN
    MATCH_MP_TAC(INTEGER_RULE `d:int = &0 ==> d divides b - a ==> a = b`) THEN
    ASM_SIMP_TAC[INT_OF_NUM_EQ; GSYM INFINITE_CYCLIC_SUBGROUP_ORDER] THEN
    MP_TAC INFINITE_INTEGER_GROUP THEN MATCH_MP_TAC EQ_IMP THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC ISOMORPHIC_GROUP_INFINITENESS THEN
    REWRITE_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE];
    MP_TAC(SPECL [`&p:int`; `p:num`]
      TRIVIAL_REDUCED_HOMOLOGY_GROUP_NSPHERE) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    REWRITE_TAC[TRIVIAL_GROUP_SUBGROUP_GENERATED_EQ] THEN
    ASM SET_TAC[]]);;

let BROUWER_DEGREE2_HOMOTOPIC = prove
 (`!p f g. homotopic_with (\x. T) (nsphere p,nsphere p) f g
           ==> brouwer_degree2 p f = brouwer_degree2 p g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    HOMOLOGY_HOMOTOPY_EMPTY)) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_DEGREE2_UNIQUE THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET]
    GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP_SUBSET] THEN
  ASM_SIMP_TAC[BROUWER_DEGREE2]);;

let BROUWER_DEGREE2_ID = prove
 (`!p. brouwer_degree2 p (\x. x) = &1`,
  GEN_TAC THEN MATCH_MP_TAC BROUWER_DEGREE2_UNIQUE THEN
  REWRITE_TAC[CONTINUOUS_MAP_ID] THEN
  SIMP_TAC[INT_MUL_LID;HOM_INDUCED_ID; GROUP_ZPOW_1;
    REWRITE_RULE[SUBSET; homology_group]
           GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP_SUBSET]);;

let BROUWER_DEGREE2_COMPOSE = prove
 (`!p f g.
        continuous_map (nsphere p,nsphere p) f /\
        continuous_map (nsphere p,nsphere p) g
        ==> brouwer_degree2 p (g o f) =
            brouwer_degree2 p g * brouwer_degree2 p f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BROUWER_DEGREE2_UNIQUE THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
  SIMP_TAC[GROUP_ZPOW_MUL; GSYM BROUWER_DEGREE2; HOM_INDUCED_REDUCED] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN
  AP_THM_TAC THEN MATCH_MP_TAC HOM_INDUCED_COMPOSE THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET]);;

let BROUWER_DEGREE2_HOMOTOPY_EQUIVALENCE = prove
 (`!p f g. continuous_map (nsphere p,nsphere p) f /\
           continuous_map (nsphere p,nsphere p) g /\
           homotopic_with (\x. T) (nsphere p,nsphere p) (f o g) I
           ==> abs(brouwer_degree2 p f) = &1 /\
               abs(brouwer_degree2 p g) = &1 /\
               brouwer_degree2 p g = brouwer_degree2 p f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BROUWER_DEGREE2_HOMOTOPIC) THEN
  ASM_SIMP_TAC[BROUWER_DEGREE2_COMPOSE; I_DEF; BROUWER_DEGREE2_ID] THEN
  REWRITE_TAC[INT_MUL_EQ_1] THEN INT_ARITH_TAC);;

let BROUWER_DEGREE2_HOMEOMORPHIC_MAPS = prove
 (`!p f g. homeomorphic_maps (nsphere p,nsphere p) (f,g)
           ==> abs(brouwer_degree2 p f) = &1 /\
               abs(brouwer_degree2 p g) = &1 /\
               brouwer_degree2 p g = brouwer_degree2 p f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
  MATCH_MP_TAC BROUWER_DEGREE2_HOMOTOPY_EQUIVALENCE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_REWRITE_TAC[o_THM; I_THM] THEN ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

let BROUWER_DEGREE2_RETRACTION_MAP = prove
 (`!p f. retraction_map(nsphere p,nsphere p) f
         ==> abs(brouwer_degree2 p f) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[retraction_map; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:(num->real)->(num->real)` THEN
  REWRITE_TAC[retraction_maps] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p:num`; `f:(num->real)->(num->real)`; `g:(num->real)->(num->real)`]
   BROUWER_DEGREE2_HOMOTOPY_EQUIVALENCE) THEN
  ANTS_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_REWRITE_TAC[o_THM; I_THM] THEN ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

let BROUWER_DEGREE2_SECTION_MAP = prove
 (`!p f. section_map (nsphere p,nsphere p) f
         ==> abs(brouwer_degree2 p f) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[section_map; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:(num->real)->(num->real)` THEN
  REWRITE_TAC[retraction_maps] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`p:num`; `g:(num->real)->(num->real)`; `f:(num->real)->(num->real)`]
   BROUWER_DEGREE2_HOMOTOPY_EQUIVALENCE) THEN
  ANTS_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQUAL THEN
  ASM_REWRITE_TAC[o_THM; I_THM] THEN ASM_MESON_TAC[CONTINUOUS_MAP_COMPOSE]);;

let BROUWER_DEGREE2_HOMEOMORPHIC_MAP = prove
 (`!p f. homeomorphic_map (nsphere p,nsphere p) f
         ==> abs(brouwer_degree2 p f) = &1`,
  SIMP_TAC[GSYM SECTION_AND_RETRACTION_EQ_HOMEOMORPHIC_MAP;
           BROUWER_DEGREE2_SECTION_MAP]);;

let BROUWER_DEGREE2_NULLHOMOTOPIC = prove
 (`!p f a. homotopic_with (\x. T) (nsphere p,nsphere p) f (\x. a)
           ==> brouwer_degree2 p f = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP BROUWER_DEGREE2_HOMOTOPIC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  MATCH_MP_TAC BROUWER_DEGREE2_UNIQUE THEN
  ASM_REWRITE_TAC[GROUP_ZPOW_0] THEN
  X_GEN_TAC `c:((num->real)->num->real)frag->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `hom_induced (&p) (nsphere p,{}) (nsphere p,{}) (\x. a) =
    hom_induced (&p) (subtopology (nsphere p) {a},{})
                     (nsphere p,{}) (\x. x) o
    hom_induced (&p) (nsphere p,{})
                     (subtopology (nsphere p) {a},{}) (\x. a)`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE o
      rand o snd) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET;
                    SET_RULE `IMAGE (\x. a) s SUBSET {a}`;
                    CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
    SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_DEF];
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC
     (MESON[REWRITE_RULE[group_homomorphism]
            GROUP_HOMOMORPHISM_HOM_INDUCED_REDUCED]
      `a = group_id(reduced_homology_group(p,top))
       ==> hom_induced p (top,{}) (top',{}) f a =
           group_id(reduced_homology_group(p,top'))`) THEN
    MP_TAC(ISPECL [`&p:int`; `subtopology (nsphere p) {a}`]
      TRIVIAL_REDUCED_HOMOLOGY_GROUP_CONTRACTIBLE_SPACE) THEN
    SIMP_TAC[CONTRACTIBLE_SPACE_SUBTOPOLOGY_SING; TRIVIAL_GROUP_SUBSET] THEN
    REWRITE_TAC[SUBSET; IN_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HOM_INDUCED_REDUCED THEN ASM_REWRITE_TAC[]]);;

let BROUWER_DEGREE2_CONST = prove
 (`!p a. brouwer_degree2 p (\x. a) = &0`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `continuous_map(nsphere p,nsphere p) (\x. a)` THENL
   [MATCH_MP_TAC BROUWER_DEGREE2_NULLHOMOTOPIC THEN
    EXISTS_TAC `a:num->real` THEN ASM_REWRITE_TAC[HOMOTOPIC_WITH_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[brouwer_degree2; HOM_INDUCED_DEFAULT] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  SUBGOAL_THEN `group_id(relative_homology_group(&p,nsphere p,{})) =
                group_id(reduced_homology_group(&p,nsphere p))`
  SUBST1_TAC THENL
   [REWRITE_TAC[reduced_homology_group; GSYM homology_group] THEN
    REWRITE_TAC[CONJUNCT2 SUBGROUP_GENERATED];
    SIMP_TAC[GROUP_ZPOW_EQ_ID]] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `d:int` THEN EQ_TAC THEN
  SIMP_TAC[INTEGER_RULE `!x:int. x divides &0`] THEN
  MP_TAC(ISPECL [`&p:int`; `p:num`]
   CYCLIC_REDUCED_HOMOLOGY_GROUP_NSPHERE) THEN
  REWRITE_TAC[cyclic_group; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `c:((num->real)->num->real)frag->bool` THEN
  STRIP_TAC THEN DISCH_THEN(MP_TAC o SPEC
   `c:((num->real)->num->real)frag->bool`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INTEGER_RULE
   `c = &0 ==> c divides d ==> d = &0`) THEN
  ASM_SIMP_TAC[INT_OF_NUM_EQ; GSYM INFINITE_CYCLIC_SUBGROUP_ORDER] THEN
  MP_TAC INFINITE_INTEGER_GROUP THEN MATCH_MP_TAC EQ_IMP THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ISOMORPHIC_GROUP_INFINITENESS THEN
  REWRITE_TAC[REDUCED_HOMOLOGY_GROUP_NSPHERE]);;

let BROUWER_DEGREE2_NONSURJECTIVE = prove
 (`!p f. continuous_map(nsphere p,nsphere p) f /\
         ~(IMAGE f (topspace(nsphere p)) = topspace(nsphere p))
         ==> brouwer_degree2 p f = &0`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BROUWER_DEGREE2_NULLHOMOTOPIC THEN
  MATCH_MP_TAC NULLHOMOTOPIC_NONSURJECTIVE_SPHERE_MAP THEN
  ASM_REWRITE_TAC[]);;

let BROUWER_DEGREE2_REFLECTION = prove
 (`!p. brouwer_degree2 p (\x i. if i = 1 then --x i else x i) = -- &1`,
  ABBREV_TAC `r = \(x:num->real) i. if i = 1 then --x i else x i` THEN
  MP_TAC(GEN `p:num` (SPECL [`p:num`; `1`]
    CONTINUOUS_MAP_NSPHERE_REFLECTION)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC BROUWER_DEGREE2_UNIQUE THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`&p:int`; `p:num`]
      REDUCED_HOMOLOGY_GROUP_NSPHERE_STEP) THEN
    ASM_REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SYM o el 1 o CONJUNCTS o
      GEN_REWRITE_RULE I [GROUP_ISOMORPHISM]) THEN
    REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; BROUWER_DEGREE2] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_ZPOW o
          MATCH_MP GROUP_ISOMORPHISM_IMP_HOMOMORPHISM) THEN
    SIMP_TAC[]] THEN
  SUBGOAL_THEN `!c. c IN group_carrier(reduced_homology_group(&0,nsphere 0))
                    ==> hom_induced (&0) (nsphere 0,{}) (nsphere 0,{}) r c =
                        group_inv (homology_group(&0,nsphere 0)) c`
  ASSUME_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC BROUWER_DEGREE2_UNIQUE THEN ASM_SIMP_TAC[] THEN
    SIMP_TAC[GROUP_ZPOW_POW; GROUP_POW_1] THEN
    REWRITE_TAC[reduced_homology_group; CONJUNCT2 SUBGROUP_GENERATED]] THEN
  X_GEN_TAC `c:((num->real)->num->real)frag->bool` THEN
  REWRITE_TAC[GROUP_CARRIER_REDUCED_HOMOLOGY_GROUP] THEN
  REWRITE_TAC[group_kernel; IN_ELIM_THM] THEN STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`p:num->real = \i. if i = 1 then &1 else &0`;
    `n:num->real = \i. if i = 1 then -- &1 else &0`] THEN
  SUBGOAL_THEN `topspace(nsphere 0) = {p,n}` ASSUME_TAC THENL
   [REWRITE_TAC[NSPHERE] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_PRODUCT_TOPOLOGY; o_DEF] THEN
    SIMP_TAC[TOPSPACE_EUCLIDEANREAL; CARTESIAN_PRODUCT_UNIV; INTER_UNIV] THEN
    REWRITE_TAC[ADD_CLAUSES; NUMSEG_SING; SUM_SING; IN_SING] THEN
    MAP_EVERY EXPAND_TAC ["p"; "n"] THEN
    REWRITE_TAC[SET_RULE `s = {a,b} <=> !x. x IN s <=> x = a \/ x = b`] THEN
    REWRITE_TAC[REAL_RING `(x:real) pow 2 = &1 <=> x = &1 \/ x = -- &1`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:num->real = n)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "n"] THEN REWRITE_TAC[FUN_EQ_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `r(p:num->real) = n /\ r n = p` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "n"; "p"] THEN SIMP_TAC[REAL_NEG_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:num->real. r(r x) = x` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN SIMP_TAC[FUN_EQ_THM; REAL_NEG_NEG] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. d IN group_carrier(homology_group(&0,subtopology (nsphere 0) {p})) /\
        group_div (homology_group (&0,nsphere 0))
                  (hom_induced (&0) (subtopology (nsphere 0) {p},{})
                                    (nsphere 0,{}) (\x. x) d)
                  (hom_induced (&0) (subtopology (nsphere 0) {p},{})
                                    (nsphere 0,{}) r d) = c`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&0:int`; `nsphere 0`; `{p:num->real}`; `{n:num->real}`]
          HOMOLOGY_ADDITIVITY_EXPLICIT) THEN
    ANTS_TAC THENL
     [ONCE_REWRITE_TAC[CONJ_ASSOC] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MP_TAC(fst(EQ_IMP_RULE(ISPECL [`nsphere 0`; `{p:num->real,n}`]
          DISCRETE_TOPOLOGY_UNIQUE))) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[IN_INSERT]] THEN
      CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC FINITE_T1_SPACE_IMP_DISCRETE_TOPOLOGY THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
      REWRITE_TAC[NSPHERE] THEN MATCH_MP_TAC T1_SPACE_SUBTOPOLOGY THEN
      REWRITE_TAC[T1_SPACE_PRODUCT_TOPOLOGY; T1_SPACE_EUCLIDEANREAL];
      REWRITE_TAC[GROUP_ISOMORPHISM] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
       `P /\ IMAGE f s = t /\ Q
        ==> !y. y IN t ==> ?x. x IN s /\ f x = y`))] THEN
    DISCH_THEN(MP_TAC o SPEC `c:((num->real)->num->real)frag->bool`) THEN
    ASM_REWRITE_TAC[PROD_GROUP; EXISTS_PAIR_THM; IN_CROSS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:((num->real)->num->real)frag->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `d':((num->real)->num->real)frag->bool`
        STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[group_div] THEN EXPAND_TAC "c" THEN AP_TERM_TAC THEN
    SUBGOAL_THEN
     `group_epimorphism(homology_group(&0,subtopology (nsphere 0) {p}),
                        homology_group(&0,subtopology (nsphere 0) {n}))
        (hom_induced (&0) (subtopology (nsphere 0) {p},{})
                          (subtopology (nsphere 0) {n},{}) r)`
    MP_TAC THENL
     [MATCH_MP_TAC GROUP_EPIMORPHISM_HOM_INDUCED_RETRACTION_MAP THEN
      REWRITE_TAC[retraction_map] THEN
      EXISTS_TAC `r:(num->real)->num->real` THEN
      REWRITE_TAC[retraction_maps; CONTINUOUS_MAP_IN_SUBTOPOLOGY] THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[];
      REWRITE_TAC[group_epimorphism] THEN DISCH_THEN(MP_TAC o MATCH_MP
       (SET_RULE `P /\ IMAGE f s = t
                  ==> !y. y IN t ==> ?x. x IN s /\ f x = y`))] THEN
    DISCH_THEN(MP_TAC o SPEC `d':((num->real)->num->real)frag->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN
     `e:((num->real)->num->real)frag->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `group_monomorphism(homology_group(&0,subtopology (nsphere 0) {p}),
                         homology_group(&0,discrete_topology {one}))
        (hom_induced (&0) (subtopology (nsphere 0) {p},{})
                          (discrete_topology {one},{}) (\x. one))`
    MP_TAC THENL
     [MATCH_MP_TAC GROUP_MONOMORPHISM_HOM_INDUCED_SECTION_MAP THEN
      REWRITE_TAC[section_map; retraction_maps] THEN
      EXISTS_TAC `(\w. p):1->num->real` THEN
      SIMP_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER; IN_SING] THEN
      REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_SUBTOPOLOGY] THEN
      REWRITE_TAC[TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN ASM SET_TAC[];
      REWRITE_TAC[GROUP_MONOMORPHISM_ALT]] THEN
    DISCH_THEN(MP_TAC o SPEC
     `group_mul (homology_group (&0,subtopology (nsphere 0) {p})) d e` o
     CONJUNCT2) THEN
    ASM_SIMP_TAC[GROUP_MUL; GSYM GROUP_LINV_EQ] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      W(MP_TAC o PART_MATCH rand
        GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY o rator o lhand o snd) THEN
      SIMP_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
      ASM_SIMP_TAC[group_homomorphism] THEN DISCH_THEN(K ALL_TAC) THEN
      EXPAND_TAC "c" THEN
      W(MP_TAC o PART_MATCH rand
        GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY o rator o rand o snd) THEN
      SIMP_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY; IN_SING] THEN
      REWRITE_TAC[group_homomorphism] THEN DISCH_THEN(fun th ->
        W(MP_TAC o PART_MATCH (lhand o rand) (last(CONJUNCTS th)) o
          rand o snd)) THEN
      ANTS_TAC THENL
       [CONJ_TAC THEN
        W(MP_TAC o PART_MATCH rand GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY
          o rator o lhand o snd) THEN
        SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
        REWRITE_TAC[GROUP_HOMOMORPHISM; SUBSET; FORALL_IN_IMAGE] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      BINOP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE_EMPTY o
        rator o rand o snd) THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID; IN_SING;
                   CONTINUOUS_MAP_CONST; TOPSPACE_DISCRETE_TOPOLOGY] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[o_DEF] THEN
      EXPAND_TAC "d'" THEN GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN
      AP_THM_TAC THEN
      W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE_EMPTY o
        rand o snd) THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_CONST;
                   CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
      SIMP_TAC[TOPSPACE_DISCRETE_TOPOLOGY; IN_SING; SUBSET; FORALL_IN_IMAGE;
               TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST_ALL_TAC o SYM)] THEN
    REWRITE_TAC[o_DEF] THEN EXPAND_TAC "d'" THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM o_THM] THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE_EMPTY o
      rator o rand o snd) THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_ID;
                 GROUP_INV; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    W(MP_TAC o PART_MATCH rand
        GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY o rator o rand o snd) THEN
    ASM_SIMP_TAC[ETA_AX; o_DEF; CONTINUOUS_MAP_FROM_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[group_homomorphism];
    EXPAND_TAC "c" THEN W(MP_TAC o PART_MATCH (lhand o rand)
        (GROUP_RULE `group_inv G (group_div G x y) = group_div G y x`) o
        rand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN
      W(MP_TAC o PART_MATCH rand GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY
         o rator o lhand o snd) THEN
      ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
      ASM_SIMP_TAC[group_homomorphism; SUBSET; FORALL_IN_IMAGE];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH rand
        GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY o rator o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP GROUP_HOMOMORPHISM_DIV) THEN
    EXPAND_TAC "c" THEN DISCH_THEN(fun th ->
      W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
    REWRITE_TAC[HOM_INDUCED; homology_group] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM homology_group] THEN
    BINOP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_THM] THEN AP_THM_TAC THEN
    W(MP_TAC o PART_MATCH (rand o rand) HOM_INDUCED_COMPOSE_EMPTY o
      lhand o snd) THEN
    ASM_SIMP_TAC[CONTINUOUS_MAP_FROM_SUBTOPOLOGY; CONTINUOUS_MAP_ID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[o_DEF; ETA_AX]]);;
