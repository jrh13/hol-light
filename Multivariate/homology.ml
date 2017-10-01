(* ========================================================================= *)
(* Basic setup of singular homology.                                         *)
(* ========================================================================= *)

needs "Library/frag.ml";;               (* Free Abelian groups               *)
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

let CONNECTED_IN_STANDARD_SIMPLEX = prove
 (`!p. connected_in (product_topology (:num) (\i. euclideanreal))
                    (standard_simplex p)`,
  GEN_TAC THEN MATCH_MP_TAC PATH_CONNECTED_IN_IMP_CONNECTED_IN THEN
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
