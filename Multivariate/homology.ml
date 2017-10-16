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
(* Lift the boundary map to homology groups.                                 *)
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

(* ------------------------------------------------------------------------- *)
(* Now lift the induced map.                                                 *)
(* ------------------------------------------------------------------------- *)

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
(* Functoriality, naturality and easier Eilenberg-Steenrod axioms.           *)
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

(* ------------------------------------------------------------------------- *)
(* Fact that our coefficient group is the integers.                          *)
(* ------------------------------------------------------------------------- *)

let HOMOLOGY_COEFFICIENTS = prove
 (`!top (a:A).
        topspace top = {a}
        ==> homology_group(&0,top) isomorphic_group integer_group`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[relative_homology_group; homology_group] THEN
  REWRITE_TAC[INT_LT_REFL; NUM_OF_INT_OF_NUM] THEN
  SUBGOAL_THEN
   `singular_relboundary (0,top:A topology,{}) =
    {group_id(relcycle_group(0,top,{}))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[RELCYCLE_GROUP; FUN_EQ_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SINGULAR_BOUNDARY_SING th]) THEN
    X_GEN_TAC `c:((num->real)->A)frag` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INSERT; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[SINGULAR_CHAIN_0];
    W(MP_TAC o PART_MATCH lhand QUOTIENT_GROUP_TRIVIAL o lhand o snd)] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] ISOMORPHIC_GROUP_TRANS) THEN
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[isomorphic_group] THEN EXISTS_TAC
    `\b. frag_cmul b
           (frag_of (RESTRICTION (standard_simplex 0) (\x. (a:A))))` THEN
  REWRITE_TAC[GROUP_ISOMORPHISM_ALT; RELCYCLE_GROUP; INTEGER_GROUP] THEN
  REWRITE_TAC[IN_UNIV; FRAG_MODULE
   `frag_cmul (x + y) c = frag_add (frag_cmul x c) (frag_cmul y c)`] THEN
  REWRITE_TAC[FRAG_OF_NONZERO; FRAG_MODULE
   `frag_cmul a b = frag_0 <=> a = &0 \/ b = frag_0`] THEN
  TRANS_TAC EQ_TRANS `singular_chain(0,top:A topology)` THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `0` o MATCH_MP SINGULAR_CHAIN_SING) THEN
    SET_TAC[];
    REWRITE_TAC[FUN_EQ_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP SINGULAR_CYCLE_SING th])]);;
