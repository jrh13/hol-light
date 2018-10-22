(* ========================================================================= *)
(* Geometric algebra G(P,Q,R) is formalized with the multivector structure   *)
(* (P,Q,R)multivector, which can formulate positive definite, negative       *)
(* definite and zero quadratic forms.                                        *)
(*                                                                           *)
(*        (c) Copyright, Capital Normal University, China, 2018.             *)
(*     Authors: Liming Li, Zhiping Shi, Yong Guan, Guohui Wang, Sha Ma.      *)
(* ========================================================================= *)

needs "Multivariate/clifford.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Add some theorems to clifford.ml                                          *)
(* ------------------------------------------------------------------------- *)

let GEOM_MBASIS_LID = prove
 (`!x. mbasis{} * x = x`,
  MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC[GEOM_RMUL; GEOM_RADD] THEN
  SIMP_TAC[GEOM_MBASIS; DIFF_EMPTY; EMPTY_DIFF; UNION_EMPTY; EMPTY_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN {} /\ j IN s /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; REAL_MUL_LID; VECTOR_MUL_LID]);;

let GEOM_MBASIS_RID = prove
 (`!x. x * mbasis{} = x`,
  MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC[GEOM_LMUL; GEOM_LADD] THEN
  SIMP_TAC[GEOM_MBASIS; DIFF_EMPTY; EMPTY_DIFF; UNION_EMPTY; EMPTY_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN s /\ j IN {} /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; REAL_MUL_LID; VECTOR_MUL_LID]);;

let GEOM_MBASIS_SKEWSYM = prove
 (`!i j. mbasis{i} * mbasis{j} =
  if i = j then mbasis{j} * mbasis{i} else --(mbasis{j} * mbasis{i})`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[GEOM_MBASIS_SING] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> i < j /\ ~(j < i) \/ j < i /\ ~(i < j)`)) THEN
  ASM_REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_NEG_0] THEN
  REPEAT AP_TERM_TAC THEN SET_TAC[]);;

let GEOM_MBASIS_REFL = prove
 (`!i. mbasis{i}:real^(N)multivector * mbasis{i} =
       if i IN 1..dimindex (:N) then mbasis {}
       else vec 0`,
  GEN_TAC THEN REWRITE_TAC[GEOM_MBASIS_SING]);;

(* ------------------------------------------------------------------------- *)
(* Add some basic theorems to the library of clifford                        *)
(* ------------------------------------------------------------------------- *)

let G_P_Q_R_WITH_G_N = prove
 (`!p q r i e.
    1 <= p + q + r /\ p + 3 * q + 4 * r <= dimindex(:N) /\
    (e i = if 1 <= i /\ i <= p then (mbasis {i}:real^(N)multivector)
           else if p + 1 <= i /\ i <= p + q then
                 (mbasis {(3 * i - 2 * p + r) - 2} * mbasis {(3 * i - 2 * p + r) - 1} * mbasis {3 * i - 2 * p + r })
           else if p + q + 1 <= i /\ i <= p + q + r then
                 (mbasis {i - q} + mbasis {(4 * i - 3 * p - q) - 2} * mbasis {(4 * i - 3 * p - q) - 1} * mbasis {(4 * i - 3 * p) - q })
           else vec 0) ==>
     e i * e i = if 1 <= i /\ i <= p then mbasis {}
                 else if p + 1 <= i /\ i <= p + q then -- mbasis {}
                 else vec 0`,
  let lemma = prove
   (`!i. 2 < i /\ i<= dimindex(:N) ==>
     (mbasis {i-2} * mbasis {i-1} * (mbasis {i}:real^(N)multivector)) * (mbasis {i-2} * mbasis {i-1} * mbasis {i}) = --mbasis {}`,
    REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOM_MBASIS_SKEWSYM] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i ==> ~(i - 1 = i)`] THEN
    REWRITE_TAC[GEOM_RNEG] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOM_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOM_MBASIS_SKEWSYM] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i ==> ~(i - 2 = i)`] THEN
    REWRITE_TAC[GEOM_LNEG; GEOM_RNEG; GSYM GEOM_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOM_ASSOC] THEN
    ASM_REWRITE_TAC[IN_NUMSEG; GEOM_MBASIS_REFL] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i ==> 1 <= i`; GEOM_MBASIS_LID] THEN
    ONCE_REWRITE_TAC[GEOM_MBASIS_SKEWSYM]  THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i ==> ~(i - 2 = i - 1)`] THEN
    REWRITE_TAC[GEOM_RNEG; VECTOR_NEG_NEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOM_ASSOC] THEN
    REWRITE_TAC[GEOM_MBASIS_REFL; IN_NUMSEG] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i /\ i <= dimindex (:N) ==> 1 <= i - 1 /\ i - 1 <= dimindex (:N)`] THEN
    REWRITE_TAC[GEOM_MBASIS_LID; GEOM_MBASIS_REFL; IN_NUMSEG] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 < i /\ i <= dimindex (:N) ==> 1 <= i - 2 /\ i - 2 <= dimindex (:N)`]) in
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[GEOM_MBASIS_REFL; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `2  <  3 * i - 2 * p + r  /\  3 * i - 2 * p + r <= dimindex (:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[lemma]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[GEOM_LADD; GEOM_RADD; GEOM_RZERO] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `(a + b) + c + d = (a + d)+(b + c:real^N)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM VECTOR_ADD_LID] THEN
  BINOP_TAC THEN REWRITE_TAC[VECTOR_ARITH `a + b = vec 0 <=> b = --a`] THENL
   [REWRITE_TAC[GEOM_MBASIS_REFL; IN_NUMSEG] THEN
    SUBGOAL_THEN `2 < 4 * i - 3 * p - q  /\ 4 * i - 3 * p - q <= dimindex (:N)` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN ASM_SIMP_TAC[lemma] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM GEOM_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[GEOM_MBASIS_SKEWSYM] THEN
  ASM_SIMP_TAC[ARITH_RULE `p + q + 1<= i ==> ~(4 * i - 3 * p - q = i - q:num)`] THEN
  REWRITE_TAC[GEOM_RNEG] THEN AP_TERM_TAC THEN REWRITE_TAC[GEOM_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GEOM_MBASIS_SKEWSYM] THEN
  ASM_SIMP_TAC[ARITH_RULE `p + q + 1<= i ==> ~(4 * i - 3 * p - q - 2 = i - q:num)`] THEN
  REWRITE_TAC[GEOM_LNEG; GSYM GEOM_ASSOC] THEN ONCE_REWRITE_TAC[GSYM GEOM_RNEG] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[GEOM_MBASIS_SKEWSYM] THEN
  ASM_SIMP_TAC[ARITH_RULE `p + q + 1<= i ==> ~(4 * i - 3 * p - q - 1 = i - q:num)`]);;

(* ------------------------------------------------------------------------- *)
(* Some basic lemmas, mostly set theory.                                     *)
(* ------------------------------------------------------------------------- *)

let FINITE_POWERSET_CART_SUBSET_LEMMA = prove
 (`!P m n. FINITE {i,j | i IN {s | s SUBSET 1..m} /\ j IN {s | s SUBSET 1..n} /\ P i j}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i,j | i IN {s | s SUBSET 1..m} /\ j IN {s | s SUBSET 1..n}}` THEN
  SIMP_TAC[SUBSET; FINITE_PRODUCT; FINITE_NUMSEG; FINITE_POWERSET] THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM]);;

let FINITE_CART_SUBSET_LEMMA1 = prove (*More convenient than FINITE_CART_SUBSET_LEMMA. *)
 (`!P m n m' n'. FINITE {i,j | i IN m..n /\ j IN m'..n' /\ P i j}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i,j | i IN m..n /\ j IN m'..n'}` THEN
  SIMP_TAC[SUBSET; FINITE_PRODUCT; FINITE_NUMSEG] THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Pseudo dimindex.                                                           *)
(* ------------------------------------------------------------------------- *)

let pdimindex = new_definition
  `pdimindex(s:A->bool) = dimindex(s) - 1`;;

let PDIMINDEX_SUC_DIMINDEX = prove
 (`dimindex(s:A->bool) = pdimindex(s) + 1`,
  SIMP_TAC[pdimindex; DIMINDEX_GE_1; SUB_ADD]);;

let PDIMINDEX_LT_DIMINDEX = prove
 (`pdimindex(s:A->bool) < dimindex(s)`,
  REWRITE_TAC[PDIMINDEX_SUC_DIMINDEX; LT_ADD] THEN ARITH_TAC);;

let PDIMINDEX_LE_IMP_DIMINDEX_LE = prove
 (`!x. x <= pdimindex s ==> x <= dimindex s`,
 MESON_TAC[PDIMINDEX_LT_DIMINDEX; LET_TRANS; LT_IMP_LE]);;

let PDIMINDEX_UNIQUE = prove
 (`(:A) HAS_SIZE n + 1 ==> pdimindex(:A) = n`,
  MESON_TAC[dimindex; HAS_SIZE; pdimindex; ADD_SUB]);;

let define_pseudo_finite_type =
  let lemma_pre = prove
   (`?x. x IN 1..n+1`,
    EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC)
  and lemma_post = prove
   (`(!a:A. mk(dest a) = a) /\ (!r. r IN 1..n+1 <=> dest(mk r) = r)
     ==> (:A) HAS_SIZE n+1`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(:A) = IMAGE mk (1..n+1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV];
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ] THEN
    ASM_MESON_TAC[HAS_SIZE_NUMSEG_1]) in
  let POST_RULE = MATCH_MP lemma_post and n_tm = `n:num` in
  fun n ->
    let ns = "'"^string_of_int n in
    let ns' = "auto_define_finite_type_"^ns in
    let th = INST [mk_small_numeral n,n_tm] lemma_pre in
    POST_RULE(new_type_definition ns ("mk_"^ns',"dest_"^ns') th);;

let HAS_PSEUDO_SIZE_0 = define_pseudo_finite_type 0;;
let HAS_PSEUDO_SIZE_1 = define_pseudo_finite_type 1;;
let HAS_PSEUDO_SIZE_2 = define_pseudo_finite_type 2;;
let HAS_PSEUDO_SIZE_3 = define_pseudo_finite_type 3;;
let HAS_PSEUDO_SIZE_4 = define_pseudo_finite_type 4;;

let PDIMINDEX_0 = MATCH_MP PDIMINDEX_UNIQUE HAS_PSEUDO_SIZE_0;;
let PDIMINDEX_1 = MATCH_MP PDIMINDEX_UNIQUE HAS_PSEUDO_SIZE_1;;
let PDIMINDEX_2 = MATCH_MP PDIMINDEX_UNIQUE HAS_PSEUDO_SIZE_2;;
let PDIMINDEX_3 = MATCH_MP PDIMINDEX_UNIQUE HAS_PSEUDO_SIZE_3;;
let PDIMINDEX_4 = MATCH_MP PDIMINDEX_UNIQUE HAS_PSEUDO_SIZE_4;;

(* ------------------------------------------------------------------------- *)
(* Index type for "trip_fin_sum", denote the vector of (P,Q,R).              *)
(* ------------------------------------------------------------------------- *)

let trip_fin_sum_tybij =
  let th = prove
   (`?x. x IN 1..(if 1 <= pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
                  then pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) else 1)`,
     EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC) in
  new_type_definition "trip_fin_sum" ("mk_trip_fin_sum","dest_trip_fin_sum") th;;

let TRIPLE_FINITE_SUM_IMAGE = prove
 (`UNIV:(P,Q,R)trip_fin_sum->bool =
       IMAGE mk_trip_fin_sum
             (1..(if 1 <= pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
                  then pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) else 1))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[trip_fin_sum_tybij]);;

let DIMINDEX_HAS_SIZE_TRIPLE_FINITE_SUM = prove
 (`(UNIV:(P,Q,R)trip_fin_sum->bool) HAS_SIZE
            (if 1 <= pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
             then pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) else 1)`,
  SIMP_TAC[TRIPLE_FINITE_SUM_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[trip_fin_sum_tybij]);;

let DIMINDEX_TRIPLE_FINITE_SUM = prove
 (`dimindex(:(P,Q,R)trip_fin_sum) =
             if 1 <= pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
             then pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) else 1`,
  GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_TRIPLE_FINITE_SUM] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Index type for "multivectors" of (P,Q,R).(k-vectors for all k <= P+Q+R).  *)
(* ------------------------------------------------------------------------- *)

let geomalg_tybij_th = prove
 (`?s. s SUBSET (1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)))`,
  MESON_TAC[EMPTY_SUBSET]);;

let geomalg_tybij =
  new_type_definition "geomalg" ("mk_geomalg","dest_geomalg")
    geomalg_tybij_th;;

let GEOMALG_IMAGE = prove
 (`(:(P,Q,R)geomalg) = IMAGE mk_geomalg {s | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[geomalg_tybij]);;

let HAS_SIZE_GEOMALG = prove
 (`(:(P,Q,R)geomalg) HAS_SIZE (2 EXP (pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)))`,
  REWRITE_TAC[GEOMALG_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  SIMP_TAC[HAS_SIZE_POWERSET; HAS_SIZE_NUMSEG_1; IN_ELIM_THM] THEN
  MESON_TAC[geomalg_tybij]);;

let FINITE_GEOMALG = prove
 (`FINITE(:(P,Q,R)geomalg)`,
  MESON_TAC[HAS_SIZE; HAS_SIZE_GEOMALG]);;

let DIMINDEX_GEOMALG = prove
 (`dimindex(:(P,Q,R)geomalg) = 2 EXP (pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))`,
  MESON_TAC[DIMINDEX_UNIQUE; HAS_SIZE_GEOMALG]);;

let DEST_MK_GEOMALG = prove
 (`!s. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
         ==> dest_geomalg(mk_geomalg s:(P,Q,R)geomalg) = s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM geomalg_tybij] THEN
  ASM_REWRITE_TAC[]);;

let FORALL_GEOMALG = prove
 (`(!s. s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) ==> P(mk_geomalg s)) <=>
   (!m:(P,Q,R)geomalg. P m)`,
  EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN DISCH_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `m:(P,Q,R)geomalg`
   (REWRITE_RULE[EXTENSION] GEOMALG_IMAGE)) THEN
  REWRITE_TAC[IN_UNIV; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Indexing directly via subsets.                                            *)
(* ------------------------------------------------------------------------- *)

make_overloadable "$$" `:real^N->(num->bool)->real`;;
overload_interface("$$",`setindex:real^(P,Q,R)geomalg->(num->bool)->real`);;

let setindex = new_definition
  `(x:real^(P,Q,R)geomalg) $$ s = x$(setcode s)`;;

make_overloadable "lambdas" `:((num->bool)->real)->real^N`;;
overload_interface("lambdas",`lambdaset:((num->bool)->real)->real^(P,Q,R)geomalg`);;

let lambdaset = new_definition
 `(lambdaset) (g:(num->bool)->real) =
    (lambda i. g(codeset i)):real^(P,Q,R)geomalg`;;

(* ------------------------------------------------------------------------- *)
(* Crucial properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let GEOMALG_EQ = prove
 (`!x y:real^(P,Q,R)geomalg.
        x = y <=> !s. s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) ==> x$$s = y$$s`,
  SIMP_TAC[CART_EQ; setindex; FORALL_SETCODE; GSYM IN_NUMSEG;
           DIMINDEX_GEOMALG]);;

let GEOMALG_BETA = prove
 (`!s. s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))
         ==> ((lambdas) g :real^(P,Q,R)geomalg)$$s = g s`,
  SIMP_TAC[setindex; lambdaset; LAMBDA_BETA; SETCODE_BOUNDS;
           DIMINDEX_GEOMALG; GSYM IN_NUMSEG] THEN
  MESON_TAC[CODESET_SETCODE_BIJECTIONS]);;

let GEOMALG_UNIQUE = prove
 (`!m:real^(P,Q,R)geomalg g.
        (!s. s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) ==> m$$s = g s)
        ==> (lambdas) g = m`,
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA] THEN MESON_TAC[]);;

let GEOMALG_ETA = prove(*lambdas s. m$$s =lambdas (\s. m$$s) *)
 (`(lambdas s. m$$s) = m`,
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Also componentwise operations; they all work in this style.               *)
(* ------------------------------------------------------------------------- *)

let GEOMALG_ADD_COMPONENT = prove
 (`!x y:real^(P,Q,R)geomalg s.
      s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) ==> (x + y)$$s = x$$s + y$$s`,
  SIMP_TAC[setindex; SETCODE_BOUNDS; DIMINDEX_GEOMALG;
           GSYM IN_NUMSEG; VECTOR_ADD_COMPONENT]);;

let GEOMALG_MUL_COMPONENT = prove
 (`!c x:real^(P,Q,R)geomalg s.
      s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) ==> (c % x)$$s = c * x$$s`,
  SIMP_TAC[setindex; SETCODE_BOUNDS; DIMINDEX_GEOMALG;
           GSYM IN_NUMSEG; VECTOR_MUL_COMPONENT]);;

let GEOMALG_VEC_COMPONENT = prove
 (`!k s. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) ==> (vec k :real^(P,Q,R)geomalg)$$s = &k`,
  SIMP_TAC[setindex; SETCODE_BOUNDS; DIMINDEX_GEOMALG;
           GSYM IN_NUMSEG; VEC_COMPONENT]);;

let GEOMALG_VSUM_COMPONENT = prove
 (`!f:A->real^(P,Q,R)geomalg t s.
        s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
        ==> (vsum t f)$$s = sum t (\x. (f x)$$s)`,
  SIMP_TAC[vsum; setindex; LAMBDA_BETA; SETCODE_BOUNDS; GSYM IN_NUMSEG;
           DIMINDEX_GEOMALG]);;

let GEOMALG_VSUM = prove
 (`!t f. vsum t f = lambdas s. sum t (\x. (f x)$$s)`,
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA; GEOMALG_VSUM_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* Basis vectors indexed by subsets of 1..p+q+r.                             *)
(* ------------------------------------------------------------------------- *)

make_overloadable "mbasis" `:(num->bool)->real^N`;;
overload_interface("mbasis",`mvbasis:(num->bool)->real^(P,Q,R)geomalg`);;

let mvbasis = new_definition
 `mvbasis i = lambdas s. if i = s then &1 else &0`;;

let MVBASIS_COMPONENT = prove
 (`!s t. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
         ==> (mbasis t :real^(P,Q,R)geomalg)$$s = if s = t then &1 else &0`,
  SIMP_TAC[mvbasis; IN_ELIM_THM; GEOMALG_BETA] THEN MESON_TAC[]);;

let MVBASIS_EQ_0 = prove
 (`!s. (mbasis s :real^(P,Q,R)geomalg = vec 0) <=>
       ~(s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))`,
  SIMP_TAC[GEOMALG_EQ; MVBASIS_COMPONENT; GEOMALG_VEC_COMPONENT] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

let MVBASIS_NONZERO = prove
 (`!s. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) ==> ~(mbasis s :real^(P,Q,R)geomalg = vec 0)`,
  REWRITE_TAC[MVBASIS_EQ_0]);;

let MVBASIS_EXPANSION = prove
 (`!x:real^(P,Q,R)geomalg.
        vsum {s | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)} (\s. x$$s % mbasis s) = x`,
  SIMP_TAC[GEOMALG_EQ; GEOMALG_VSUM_COMPONENT;
           GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `x * (if p then &1 else &0) = if p then x else &0`;
               SUM_DELTA; IN_ELIM_THM]);;

let SPAN_MVBASIS = prove
 (`span {mbasis s :real^(P,Q,R)geomalg | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)} = UNIV`,
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `x:real^(P,Q,R)geomalg` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MVBASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let MVBASIS_BASIS = prove
 (`s SUBSET 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)
   ==> (mbasis s):real^(P,Q,R)geomalg = basis (setcode s)`,
  SIMP_TAC[mvbasis; basis; lambdaset; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; DIMINDEX_GEOMALG; GSYM FORALL_SETCODE] THEN
  ASM_MESON_TAC[CODESET_SETCODE_BIJECTIONS]);;


let MVBASIS_INJ = prove
 (`!s t. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         (mbasis s :real^(P,Q,R)geomalg = mbasis t)
         ==> (s = t)`,
  SIMP_TAC[mvbasis; GEOMALG_EQ; GEOMALG_BETA] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:num->bool`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; ARITH_EQ]);;

let MVBASIS_INJ_SING = prove
 (`!i j. i IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         j IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         (mbasis {i}:real^(P,Q,R)geomalg) = mbasis {j}
         ==> i = j`,
  SIMP_TAC[mvbasis; GEOMALG_EQ; GEOMALG_BETA] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `{i}:num->bool`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_SING] THEN
  ASM_MESON_TAC[REAL_OF_NUM_EQ; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Dot of Multivector.                                                        *)
(* ------------------------------------------------------------------------- *)

let DOT_MVBASIS = prove
 (`!x:real^(P,Q,R)geomalg s.
        s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
        ==> ((mbasis s) dot x = x$$s) /\ (x dot (mbasis s) = x$$s)`,
  REPEAT GEN_TAC THEN SIMP_TAC[MVBASIS_BASIS] THEN REWRITE_TAC[setindex] THEN
  ASM_SIMP_TAC[SETCODE_BOUNDS; DIMINDEX_GEOMALG; GSYM IN_NUMSEG; DOT_BASIS]);;

let DOT_MVBASIS_MVBASIS = prove
 (`!s t. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
         ==> (mbasis s:real^(P,Q,R)geomalg) dot (mbasis t) = if s = t then &1 else &0`,
  SIMP_TAC[DOT_MVBASIS; MVBASIS_COMPONENT]);;

let DOT_MVBASIS_MVBASIS_UNEQUAL = prove
 (`!s t. ~(s = t) ==> (mbasis s) dot (mbasis t) = &0`,
  SIMP_TAC[mvbasis; dot; lambdaset; LAMBDA_BETA] THEN
 ONCE_REWRITE_TAC[COND_RAND] THEN REPEAT STRIP_TAC THEN
 MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[] THEN
 REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUM_0; REAL_MUL_RZERO; REAL_MUL_LZERO; COND_ID]);;

let IN_SPAN_IMAGE_MVBASIS = prove
 (`!x:real^(P,Q,R)geomalg s.
        x IN span(IMAGE mbasis s) <=>
          !t. t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\ ~(t IN s) ==> x$$t = &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`x:real^(P,Q,R)geomalg`,`x:real^(P,Q,R)geomalg`) THEN MATCH_MP_TAC SPAN_INDUCT THEN
    SIMP_TAC[subspace; IN_ELIM_THM; GEOMALG_VEC_COMPONENT; GEOMALG_ADD_COMPONENT;
             GEOMALG_MUL_COMPONENT; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    SIMP_TAC[FORALL_IN_IMAGE; MVBASIS_COMPONENT] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[SPAN_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `(IMAGE mbasis ({t|t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)} INTER s)):real^(P,Q,R)geomalg->bool` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG; FINITE_POWERSET] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `\v:real^(P,Q,R)geomalg. x dot v` THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG; FINITE_POWERSET] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[MVBASIS_INJ]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[GEOMALG_EQ; GEOMALG_VSUM_COMPONENT; GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(if x = y then p else q) = (if y = x then p else q)`] THEN
  SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; IN_INTER; IN_ELIM_THM; DOT_MVBASIS] THEN
  ASM_MESON_TAC[REAL_MUL_RID]);;

let INDEPENDENT_STDMVBASIS = prove
 (`independent {mbasis s :real^(P,Q,R)geomalg | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}`,
  SUBGOAL_THEN
   `{mbasis s:real^(P,Q,R)geomalg | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)} =
    {basis i| 1 <= i /\ i <= dimindex (:(P,Q,R)geomalg)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM IN_NUMSEG; DIMINDEX_GEOMALG] THEN
    MESON_TAC[CODESET_SETCODE_BIJECTIONS; MVBASIS_BASIS]; ALL_TAC] THEN
  MATCH_ACCEPT_TAC INDEPENDENT_STDBASIS);;

let INDEPENDENT_STDMVBASIS_SING = prove
 (`independent {mbasis {i} :real^(P,Q,R)geomalg | 1 <= i /\ i <= pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}`,
  MATCH_MP_TAC INDEPENDENT_MONO THEN
  EXISTS_TAC `{mbasis s :real^(P,Q,R)geomalg | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}` THEN
  REWRITE_TAC[INDEPENDENT_STDMVBASIS] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x | P x} = IMAGE f {x | P x}`] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `t:real^(P,Q,R)geomalg` THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` ASSUME_TAC) THEN
  EXISTS_TAC `{i}:num->bool` THEN ASM_MESON_TAC[IN_SING; IN_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* About norm.                                                               *)
(* ------------------------------------------------------------------------- *)

let NORM_MVBASIS = prove
(`!s. s SUBSET 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)
       ==>   (norm(mbasis s :real^(P,Q,R)geomalg) = &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
     `(mbasis s):real^(P,Q,R)geomalg =
     (basis (setcode s)):real^(P,Q,R)geomalg` SUBST1_TAC THENL
   [REWRITE_TAC[mvbasis; lambdaset] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; BASIS_COMPONENT] THEN
    SIMP_TAC[GSYM FORALL_SETCODE; DIMINDEX_GEOMALG; GSYM IN_NUMSEG] THEN
    ASM_MESON_TAC[CODESET_SETCODE_BIJECTIONS]; ALL_TAC] THEN
  ASM_SIMP_TAC[SETCODE_BOUNDS; DIMINDEX_GEOMALG; GSYM IN_NUMSEG; NORM_BASIS]);;

(* ------------------------------------------------------------------------- *)
(* Linear and bilinear functions are determined by their effect on basis.    *)
(* ------------------------------------------------------------------------- *)

let LINEAR_EQ_MVBASIS = prove
 (`!f:real^(P,Q,R)geomalg->real^N g b s.
        linear f /\ linear g /\
        (!s. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) ==> f(mbasis s) = g(mbasis s))
        ==> f = g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN UNIV ==> (f:real^(P,Q,R)geomalg->real^N) x = g x`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_EQ THEN
  EXISTS_TAC `{mbasis s :real^(P,Q,R)geomalg | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}` THEN
  ASM_REWRITE_TAC[SPAN_MVBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let BILINEAR_EQ_MVBASIS = prove
 (`!f:real^(P,Q,R)geomalg->real^(P',Q',R')geomalg->real^N g b s.
        bilinear f /\ bilinear g /\
        (!s t.  s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
                t SUBSET 1..pdimindex(:P') + pdimindex(:Q') + pdimindex(:R')
                ==> f (mbasis s) (mbasis t) = g (mbasis s) (mbasis t))
        ==> f = g`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!x y. x IN UNIV /\ y IN UNIV
          ==> (f:real^(P,Q,R)geomalg->real^(P',Q',R')geomalg->real^N) x y = g x y`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC BILINEAR_EQ THEN
  EXISTS_TAC `{mbasis s :real^(P,Q,R)geomalg | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}` THEN
  EXISTS_TAC `{mbasis t :real^(P',Q',R')geomalg | t SUBSET 1..pdimindex(:P') + pdimindex(:Q') + pdimindex(:R')}` THEN
  ASM_REWRITE_TAC[SPAN_MVBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A way of proving linear properties by extension from basis.               *)
(* ------------------------------------------------------------------------- *)

let MVBASIS_EXTENSION = prove
 (`!P. (!s. s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) ==> P(mbasis s)) /\
       (!c x. P x ==> P(c % x)) /\ (!x y. P x /\ P y ==> P(x + y))
       ==> !x:real^(P,Q,R)geomalg. P x`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM MVBASIS_EXPANSION] THEN
  MATCH_MP_TAC(SIMP_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] LINEAR_PROPERTY) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG; IN_ELIM_THM] THEN
  ASM_MESON_TAC[EMPTY_SUBSET; VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Injection from regular vectors.                                           *)
(* ------------------------------------------------------------------------- *)

make_overloadable "multivec" `:real^M->real^N`;;
overload_interface("multivec",`multivect:real^(P, Q, R)trip_fin_sum->real^(P,Q,R)geomalg`);;

let multivect = new_definition
 `(multivect:real^(P,Q,R)trip_fin_sum->real^(P,Q,R)geomalg) x =
      vsum(1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) (\i. x$i % mbasis{i})`;;

let LINEAR_MULTIVECT = prove
 (`linear (multivec:real^(P,Q,R)trip_fin_sum->real^(P,Q,R)geomalg)`,
  REWRITE_TAC[linear; multivect; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VECTOR_ADD_RDISTRIB; GSYM VECTOR_MUL_ASSOC] THEN
  SIMP_TAC[FINITE_NUMSEG; VSUM_ADD; VSUM_LMUL]);;

let MULTIVECT_ADD = CONJUNCT1 (REWRITE_RULE[LINEAR_MULTIVECT]
  (ISPEC `multivec:real^(P,Q,R)trip_fin_sum->real^(P,Q,R)geomalg` linear));;

let MULTIVECT_MUL = CONJUNCT2 (REWRITE_RULE[LINEAR_MULTIVECT]
  (ISPEC `multivec:real^(P,Q,R)trip_fin_sum->real^(P,Q,R)geomalg` linear));;

let MULTIVECT_0 = REWRITE_RULE[VECTOR_MUL_LZERO](SPEC `&0:real` MULTIVECT_MUL);;

let MULTIVECT_BASIS = prove
 (`!i. multivec (basis i:real^(P,Q,R)trip_fin_sum) = mbasis {i}`,
  GEN_TAC THEN REWRITE_TAC[multivect] THEN
  SUBGOAL_THEN
   `mbasis {i}:real^(P,Q,R)geomalg =
      vsum (1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) (\i'. if i' = i then mbasis {i} else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VSUM_DELTA] THEN COND_CASES_TAC THEN REWRITE_TAC[MVBASIS_EQ_0] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_NUMSEG]  THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `1 <= pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)` THENL[ALL_TAC; ASM_ARITH_TAC] THEN
  ASM_SIMP_TAC[DIMINDEX_TRIPLE_FINITE_SUM; BASIS_COMPONENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO]);;

let MULTIVECT_EQ_0 = prove
 (`!x:real^(P, Q, R)trip_fin_sum.
   1 <= pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) ==> (x = vec 0 <=> multivec x = vec 0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [DISCH_TAC THEN ASM_REWRITE_TAC[MULTIVECT_0]; ALL_TAC] THEN
  REWRITE_TAC[multivect] THEN
  MP_TAC(ISPEC `{mbasis {i} :real^(P,Q,R)geomalg | 1 <= i /\ i <= pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}` INDEPENDENT_EXPLICIT) THEN
  REWRITE_TAC[INDEPENDENT_STDMVBASIS_SING; GSYM IN_NUMSEG; SIMPLE_IMAGE] THEN SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE] THEN
  ASSUME_TAC MVBASIS_INJ_SING THEN FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INJECTIVE_ON_LEFT_INVERSE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^(P,Q,R)geomalg->num`) THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_FORALL_THM] THEN REWRITE_TAC[TAUT `~(a==>b) <=> a /\ ~b`] THEN
  STRIP_TAC THEN EXISTS_TAC `\v. (x:real^(P, Q, R)trip_fin_sum)$((g:real^(P,Q,R)geomalg->num) v)` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN REWRITE_TAC[FINITE_NUMSEG; MVBASIS_INJ_SING; o_DEF] THEN
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC VSUM_EQ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN SIMP_TAC[CART_EQ; VEC_COMPONENT; DIMINDEX_TRIPLE_FINITE_SUM] THEN
  ASM_REWRITE_TAC[GSYM IN_NUMSEG] THEN ASM_MESON_TAC[IN_IMAGE]);;

let MULTIVECT_EQ = prove
 (`!x y:real^(P, Q, R)trip_fin_sum.
     1 <= pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) ==>
       (x = y <=> multivec x = multivec y)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM REAL_SUB_0] THEN
  SIMP_TAC[LINEAR_MULTIVECT; GSYM LINEAR_SUB; GSYM VECTOR_SUB_COMPONENT] THEN
  ASM_SIMP_TAC[MULTIVECT_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Subspace of k-vectors.                                                    *)
(* ------------------------------------------------------------------------- *)

make_overloadable "multivector" `:num->real^N->bool`;;
overload_interface("multivector",`multivectorga:num->real^(P,Q,R)geomalg->bool`);;

let multivectorga = new_definition
 `k multivector (p:real^(P,Q,R)geomalg) <=>
        !s. s SUBSET (1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\ ~(p$$s = &0)
               ==> s HAS_SIZE k`;;

let FORALL_MULTIVECTORGA_VEC0 = prove
 (`!k. k multivector (vec 0:real^(P,Q,R)geomalg)`,
  MESON_TAC[multivectorga; GEOMALG_VEC_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* k-grade part of a multivector.                                            *)
(* ------------------------------------------------------------------------- *)

make_overloadable "grade" `:num->real^N->real^N`;;
overload_interface("grade",`grade_geomalg:num->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`);;

let grade_geomalg = new_definition
 `k grade (p:real^(P,Q,R)geomalg) =
     (lambdas s. if s HAS_SIZE k then p$$s else &0):real^(P,Q,R)geomalg`;;

let GEOMALG_GRADE = prove
 (`!k x. k multivector (k grade x)`,
  SIMP_TAC[multivectorga; grade_geomalg; GEOMALG_BETA; IMP_CONJ] THEN
  MESON_TAC[]);;

let GRADE_ADD_GEOMALG = prove
 (`!x y k. k grade (x + y) = (k grade x) + (k grade y)`,
  SIMP_TAC[grade_geomalg; GEOMALG_EQ; GEOMALG_ADD_COMPONENT;
           GEOMALG_BETA; COND_COMPONENT] THEN
  REAL_ARITH_TAC);;

let GRADE_CMUL_GEOMALG = prove
 (`!c x k. k grade (c % x) = c % (k grade x)`,
  SIMP_TAC[grade_geomalg; GEOMALG_EQ; GEOMALG_MUL_COMPONENT;
           GEOMALG_BETA; COND_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* General product construct.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("SYMDIFF",(18,"left"));;
let SYMDIFF = new_definition `s SYMDIFF t = (s DIFF t) UNION (t DIFF s)`;;

let SYMDIFF_EMPTY = prove
 (`(!s. s SYMDIFF {} = s) /\  (!s. {} SYMDIFF s = s)`,
  REWRITE_TAC[SYMDIFF; DIFF_EMPTY; EMPTY_DIFF; UNION_EMPTY]);;

let SYMDIFF_COMM = prove
 (`(!s t. s SYMDIFF t = t SYMDIFF s)`,
  REWRITE_TAC[SYMDIFF; UNION_COMM]);;

let SYMDIFF_SUBSET = prove
 (`!s t u. s SUBSET u /\ t SUBSET u ==> (s SYMDIFF t) SUBSET u`,
  REWRITE_TAC[SYMDIFF] THEN SET_TAC[]);;

let SYMDIFF_ASSOC = prove
 (`!s t u. s SYMDIFF (t SYMDIFF u) = (s SYMDIFF t) SYMDIFF u`,
  REWRITE_TAC[SYMDIFF] THEN SET_TAC[]);;

let Productga_DEF = new_definition
 `(Productga sgn
     :real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg) x y =
        vsum {s | s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))}
         (\s. vsum {s | s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))}
                (\t. (sgn s t * x$$s * y$$t) % mbasis (s SYMDIFF t)))`;;

(* ------------------------------------------------------------------------- *)
(* This is always bilinear.                                                  *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_PRODUCTGA = prove
 (`!sgn. bilinear(Productga sgn)`,
  REWRITE_TAC[bilinear; linear; Productga_DEF] THEN
  SIMP_TAC[GSYM VSUM_LMUL; GEOMALG_MUL_COMPONENT] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_AC] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_POWERSET; FINITE_NUMSEG] THEN
  REPEAT(MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
         REPEAT STRIP_TAC) THEN
  ASM_SIMP_TAC[GEOMALG_ADD_COMPONENT] THEN VECTOR_ARITH_TAC);;

let PRODUCTGA_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_PRODUCTGA;;
let PRODUCTGA_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_PRODUCTGA;;

(* ------------------------------------------------------------------------- *)
(* Under suitable conditions, it's also associative.                         *)
(* ------------------------------------------------------------------------- *)

let PRODUCTGA_ASSOCIATIVE = prove
 (`!sgn1 sgn2.
       (!s t u. sgn1 t u * sgn2 s (t SYMDIFF u) = sgn2 s t * sgn1 (s SYMDIFF t) u)
             ==> !x y z:real^(P,Q,R)geomalg.
                        Productga sgn2 x (Productga sgn1 y z) =
                        Productga sgn1 (Productga sgn2 x y) z`,
  let SUM_SWAP_POWERSET =
    SIMP_RULE[FINITE_POWERSET; FINITE_NUMSEG]
     (repeat(SPEC `{s | s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))}`)
        (ISPEC `f:(num->bool)->(num->bool)->real` SUM_SWAP)) in
  let SWAP_TAC cnv n =
    GEN_REWRITE_TAC (cnv o funpow n BINDER_CONV) [SUM_SWAP_POWERSET] THEN
    REWRITE_TAC[] in
  let SWAPS_TAC cnv ns x =
    MAP_EVERY (SWAP_TAC cnv) ns THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC x THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC in
  REWRITE_TAC[Productga_DEF] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[GEOMALG_EQ; GEOMALG_VSUM_COMPONENT; MVBASIS_COMPONENT;
           GEOMALG_MUL_COMPONENT] THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  X_GEN_TAC `r:num->bool` THEN STRIP_TAC THEN
  SWAPS_TAC RAND_CONV [1;0] `s:num->bool` THEN
  SWAP_TAC LAND_CONV 0 THEN SWAPS_TAC RAND_CONV [1;0] `t:num->bool` THEN
  SWAP_TAC RAND_CONV 0 THEN SWAPS_TAC LAND_CONV [0] `u:num->bool` THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC;
    REAL_ARITH `(if p then a else &0) * b = if p then a * b else &0`;
    REAL_ARITH `a * (if p then b else &0) = if p then a * b else &0`] THEN
  SIMP_TAC[SUM_DELTA] THEN ASM_SIMP_TAC[IN_ELIM_THM; SYMDIFF_SUBSET; SYMDIFF_ASSOC] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_MUL_AC]THEN  ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* --------------------------------------------------------------------------*)
(* Geometric product.                                                        *)
(* ------------------------------------------------------------------------- *)

overload_interface
 ("*",`geomga_mul:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`);;

let geomga_mul = new_definition
 `(x:real^(P,Q,R)geomalg) * y =
     Productga (\s t.
       --(&1) pow CARD {i,j | i IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
                              j IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
                              i IN s /\ j IN t /\ i > j} *
       --(&1) pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
           &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t))
        x y`;;

let BILINEAR_GEOMGA = prove
 (`bilinear(geomga_mul)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] geomga_mul] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCTGA);;

let GEOMGA_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_GEOMGA;;
let GEOMGA_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_GEOMGA;;

let GEOMGA_ASSOC = prove
 (`!x y z:real^(P,Q,R)geomalg. x * (y * z) = (x * y) * z`,
  REWRITE_TAC[geomga_mul] THEN MATCH_MP_TAC PRODUCTGA_ASSOCIATIVE THEN
  REPEAT GEN_TAC THEN SIMP_TAC[REAL_ARITH`(a:real * b*c) * (d*e*f) = (a*d)*(b*e)*(c*f)`] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD; SYMDIFF] THEN BINOP_TAC THENL[ALL_TAC; BINOP_TAC THENL[ALL_TAC;
   REWRITE_TAC[REAL_POW_ZERO] THEN
   AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   SIMP_TAC[ADD_EQ_0; FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0] THEN
   SIMP_TAC[GSYM EMPTY_UNION] THEN
   AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]]] THEN
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EVEN_ADD] THEN
  W(fun (_,w) -> let tu = funpow 2 lhand w in
                 let su = vsubst[`s:num->bool`,`t:num->bool`] tu in
                 let st = vsubst[`t:num->bool`,`u:num->bool`] su in
                 MATCH_MP_TAC EQ_TRANS THEN
                 EXISTS_TAC(end_itlist (curry mk_eq) [st; su; tu])) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(x <=> y <=> z) ==> ((a <=> x) <=> (y <=> z <=> a))`);
    AP_TERM_TAC THEN CONV_TAC SYM_CONV;
    MATCH_MP_TAC(TAUT `(x <=> y <=> z) ==> ((a <=> x) <=> (y <=> z <=> a))`);
    AP_TERM_TAC THEN CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC SYMDIFF_PARITY_LEMMA THEN
  SIMP_TAC[FINITE_CART_SUBSET_LEMMA1; FINITE_NUMSEG; FINITE_INTER] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM;
              IN_UNION; IN_DIFF; IN_INTER] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Outer product.                                                            *)
(* ------------------------------------------------------------------------- *)

make_overloadable "outer" `:real^N->real^N->real^N`;;
overload_interface
 ("outer",`outerga:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`);;

let outerga = new_definition
 `x outer y:real^(P,Q,R)geomalg =
        Productga (\s t. if ~(s INTER t = {}) then &0
                       else --(&1) pow CARD {i,j | i IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                   j IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                   i IN s /\ j IN t /\ i > j})
                               x y`;;

let BILINEAR_OUTERGA = prove
 (`bilinear(outer)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] outerga] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCTGA);;

let OUTERGA_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_OUTERGA;;
let OUTERGA_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_OUTERGA;;

let OUTERGA_ASSOC = prove
 (`!x y z:real^(P,Q,R)geomalg. x outer (y outer z) = (x outer y) outer z`,
  REWRITE_TAC[outerga] THEN MATCH_MP_TAC PRODUCTGA_ASSOCIATIVE THEN
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`s INTER t :num->bool = {}`;
    `s INTER u :num->bool = {}`;
    `t INTER u :num->bool = {}`] THEN
  ASM_SIMP_TAC[SYMDIFF;
     SET_RULE `(s INTER t = {}) ==> (s DIFF t) UNION (t DIFF s) = s UNION t`;
     SET_RULE `s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`;
     SET_RULE `(t UNION u) INTER s = (t INTER s) UNION (u INTER s)`] THEN
  REWRITE_TAC[EMPTY_UNION] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CARD_UNION_LEMMA THEN REWRITE_TAC[FINITE_CART_SUBSET_LEMMA1] THEN
  SIMP_TAC[EXTENSION; FORALL_PAIR_THM; NOT_IN_EMPTY; IN_UNION; IN_INTER] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN ASM SET_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Inner product.                                                            *)
(* ------------------------------------------------------------------------- *)

make_overloadable "inner" `:real^N->real^N->real^N`;;
overload_interface
 ("inner",`innerga:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`);;

let innerga = new_definition
 `x inner y:real^(P,Q,R)geomalg=
      Productga (\s t. if s = {} \/ t = {} \/ ~(s SUBSET t) /\ ~(t SUBSET s)
                     then &0
                     else --(&1) pow CARD {i,j | i IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                 j IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                 i IN s /\ j IN t /\ i > j} *
                          --(&1) pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
                              &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t))
               x y`;;

parse_as_infix("lcinner",(20,"right"));;
let lcinner = new_definition
 `!x y:real^(P,Q,R)geomalg.
    x lcinner y =
        Productga (\s t. if s = {} \/ t = {} \/ ~(s SUBSET t)
                       then &0
                       else --(&1) pow CARD {i,j | i IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                   j IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                   i IN s /\ j IN t /\ i > j}*
                            --(&1) pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
                                &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t))
                 x y`;;

parse_as_infix("rcinner",(20,"right"));;
let rcinner = new_definition
 `!x y:real^(P,Q,R)geomalg.
    x rcinner y =
        Productga (\s t. if s = {} \/ t = {} \/ ~(t SUBSET s)
                       then &0
                       else --(&1) pow CARD {i,j | i IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                                                   j IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\

                                                   i IN s /\ j IN t /\ i > j}*

                            --(&1) pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
                                &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t))
                 x y`;;

parse_as_infix("scalarinner",(20,"right"));;
let scalarinner = new_definition
 `!x y:real^(P,Q,R)geomalg.
    x scalarinner y =
        Productga (\s t. if s = {} \/ t = {} \/ ~(s = t)
                       then &0
                       else --(&1) pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
                                &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t))
                 x y`;;

let BILINEAR_INNERGA = prove
 (`bilinear(inner)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] innerga] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCTGA);;

let INNERGA_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_INNERGA;;
let INNERGA_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_INNERGA;;

let BILINEAR_LCINNER = prove
 (`bilinear(lcinner)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] lcinner] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCTGA);;

let LCINNER_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_LCINNER;;
let LCINNER_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_LCINNER;;

let BILINEAR_RCINNER = prove
 (`bilinear(rcinner)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] rcinner] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCTGA);;

let RCINNER_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_RCINNER;;
let RCINNER_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_RCINNER;;

let BILINEAR_SCALARINNER = prove
 (`bilinear(scalarinner)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] scalarinner] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCTGA);;

let SCALARINNER_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_SCALARINNER;;
let SCALARINNER_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_SCALARINNER;;

(* ------------------------------------------------------------------------- *)
(* Actions of products on basis and singleton basis.                         *)
(* ------------------------------------------------------------------------- *)

let PRODUCTGA_MVBASIS = prove
 (`!s t. Productga sgn (mbasis s) (mbasis t) :real^(P,Q,R)geomalg =
            if s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
               t SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))
            then sgn s t % mbasis(s SYMDIFF t)
            else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[Productga_DEF] THEN
  SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH
   `x * (if p then &1 else &0) * (if q then &1 else &0) =
    if q then if p then x else &0 else &0`] THEN
  REPEAT
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
    SIMP_TAC[VECTOR_MUL_LZERO; COND_ID; VSUM_DELTA; IN_ELIM_THM; VSUM_0] THEN
    ASM_CASES_TAC `t SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))` THEN
    ASM_REWRITE_TAC[]));;

let PRODUCTGA_MVBASIS_SING = prove
 (`!i j. Productga sgn (mbasis{i}) (mbasis{j}) :real^(P,Q,R)geomalg =
            if i IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
               j IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
            then sgn {i} {j} % mbasis({i} SYMDIFF {j})
            else vec 0`,
  REWRITE_TAC[PRODUCTGA_MVBASIS; SET_RULE `{x} SUBSET s <=> x IN s`]);;

let GEOM_MVBASIS = prove
 (`!s t.
     mbasis s * mbasis t:real^(P,Q,R)geomalg =
     (if s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
      then (-- &1 pow CARD {i,j | i IN s /\ j IN t /\ i > j} *
            -- &1 pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
               &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t)) %
           mbasis (s SYMDIFF t)
      else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geomga_mul; PRODUCTGA_MVBASIS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[SUBSET]);;

let INNER_MVBASIS = prove
 (`!s t.
     mbasis s inner mbasis t:real^(P,Q,R)geomalg =
     (if s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
         ~(s = {}) /\ ~(t = {}) /\ (s SUBSET t \/ t SUBSET s)
      then (-- &1 pow CARD {i,j | i IN s /\ j IN t /\ i > j} *
            -- &1 pow CARD ((pdimindex(:P) + 1..pdimindex(:P) + pdimindex(:Q)) INTER s INTER t) *
               &0 pow CARD ((pdimindex(:P) + pdimindex(:Q) + 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) INTER s INTER t)) %
           mbasis (s SYMDIFF t)
      else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[innerga; PRODUCTGA_MVBASIS] THEN
  COND_CASES_TAC THENL[ALL_TAC; ASM_MESON_TAC[]] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[TAUT `~(s = {}) /\ ~(t = {}) /\ (s SUBSET t \/ t SUBSET s) <=>
                       ~(s = {} \/ t = {} \/ ~(s SUBSET t) /\ ~(t SUBSET s))`;
                  VECTOR_MUL_LZERO] THEN
  REPEAT(AP_THM_TAC THEN AP_TERM_TAC) THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[SUBSET]);;

let GEOM_MVBASIS_SING = prove
(`!i j.
     mbasis {i} * mbasis {j} :real^(P,Q,R)geomalg=
     (if i IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\
         j IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)
      then if i = j
           then if i IN 1..pdimindex (:P)
                then mbasis {}
                else if i IN pdimindex (:P) + 1..pdimindex (:P) + pdimindex (:Q)
                     then --mbasis {}
                     else vec 0
           else if i < j then mbasis {i, j} else --mbasis {i, j}
      else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geomga_mul; PRODUCTGA_MVBASIS_SING; IN_NUMSEG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
  SUBGOAL_THEN
    `{i',j' | (1 <= i' /\ i' <= pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)) /\
              (1 <= j' /\ j' <= (pdimindex(:P) + pdimindex(:Q) + pdimindex (:R)))  /\
                i' = i /\
                j' = j /\
           i' > j'}   =
    if i > j then {(i,j)} else {}`SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_SING] THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; PAIR_EQ] THEN
     ASM_MESON_TAC[LT_REFL];
     ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[GT; LT_REFL] THENL
   [ALL_TAC;
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
      `~(i:num = j) ==> (j < i <=> ~(i < j))`)) THEN ASM_CASES_TAC `i:num < j`] THEN
  ASM_REWRITE_TAC[CARD_SING; GSYM ONE; CARD_CLAUSES; real_pow; REAL_MUL_LID; REAL_ARITH `(-- &1) pow 1 = -- &1`] THENL
    [COND_CASES_TAC THENL [ALL_TAC; COND_CASES_TAC];
     ALL_TAC;
     ALL_TAC] THEN
  ASM_SIMP_TAC[SYMDIFF; DIFF_EQ_EMPTY; UNION_EMPTY;
               SET_RULE `~(i = j) ==> ({i} DIFF {j}) UNION ({j} DIFF {i}) = {i,j}`] THENL
    [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_MUL_LID];
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_MUL_LID] THEN REWRITE_TAC[VECTOR_MUL_RNEG; GSYM VECTOR_MUL_LNEG];
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (ISPEC `(mbasis {}):real^(P,Q,R)geomalg` VECTOR_MUL_LZERO)];
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_MUL_LID];
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_MUL_LID] THEN REWRITE_TAC[VECTOR_MUL_RNEG; GSYM VECTOR_MUL_LNEG]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_LID];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID] THEN AP_TERM_TAC THEN
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID]] THEN
   BINOP_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 0 = &1`)];
      REWRITE_TAC[GSYM (REAL_ARITH `&0 pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 1 = -- &1`)];
      REWRITE_TAC[GSYM (REAL_ARITH `&0 pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM (REAL_ARITH `&0 pow 1 = &0`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 0 = &1`)];
      REWRITE_TAC[GSYM (REAL_ARITH `&0 pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 0 = &1`)];
      REWRITE_TAC[GSYM (REAL_ARITH `&0 pow 0 = &1`)]] THEN
    AP_TERM_TAC THENL
     [SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (prove(`CARD {j:num} = 1`, REWRITE_TAC[CARD_SING]))] THEN AP_TERM_TAC;
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (prove(`CARD {j:num} = 1`, REWRITE_TAC[CARD_SING]))] THEN AP_TERM_TAC;
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0]] THEN
    REWRITE_TAC[IN_INTER; CARD_SING; IN_NUMSEG; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_SING] THEN
    ASM_MESON_TAC[NOT_LE; LT_SUC_LE; ADD1; ADD_ASSOC; ARITH_RULE `j:num<=p ==> j< p + q + 1`]);;

let INNER_MVBASIS_SING = prove
 (`!i j.
     mbasis {i} inner mbasis {j} :real^(P,Q,R)geomalg =
     (if i IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\
         j IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\
         i = j
       then if i IN 1..pdimindex (:P)
             then mbasis {}
             else if i IN pdimindex (:P) + 1..pdimindex (:P) + pdimindex (:Q)
                     then --mbasis {}
                     else vec 0
        else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[innerga; PRODUCTGA_MVBASIS_SING; IN_NUMSEG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONJ_ASSOC; AND_CLAUSES; IN_SING; SET_RULE `~({i} = {})`] THEN
  ASM_CASES_TAC `i:num = j` THENL[ALL_TAC; ASM_REWRITE_TAC[SING_SUBSET; IN_SING; VECTOR_MUL_LZERO]] THEN
  SUBGOAL_THEN
    `{i',j' | (((((1 <= i' /\ i' <= (pdimindex (:P) + pdimindex (:Q) + pdimindex (:R))) /\
              1 <= j') /\ j' <= pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)) /\
                i' = i) /\ j' = j) /\ i' > j'}  = {}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
     ASM_REWRITE_TAC[NOT_IN_EMPTY; PAIR_EQ] THEN
     MESON_TAC[GT; LT_REFL];
     ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_REFL; CARD_CLAUSES; real_pow; REAL_MUL_LID] THEN
  COND_CASES_TAC THENL [ALL_TAC; COND_CASES_TAC] THEN
  ASM_SIMP_TAC[SYMDIFF; DIFF_EQ_EMPTY; UNION_EMPTY] THENL
    [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_MUL_LID];
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM VECTOR_MUL_LID] THEN REWRITE_TAC[VECTOR_MUL_RNEG; GSYM VECTOR_MUL_LNEG];
     GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (ISPEC `(mbasis {}):real^(P,Q,R)geomalg` VECTOR_MUL_LZERO)]] THEN
  AP_THM_TAC THEN AP_TERM_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_RID];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_MUL_LID]] THEN
   BINOP_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 0 = &1`)];
      REWRITE_TAC[GSYM (REAL_ARITH `&0 pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 1 = -- &1`)];
      REWRITE_TAC[GSYM (REAL_ARITH `&0 pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (REAL_ARITH `(-- &1) pow 0 = &1`)];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[GSYM (REAL_ARITH `&0 pow 1 = &0`)]] THEN
    AP_TERM_TAC THENL
     [SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (prove(`CARD {j:num} = 1`, REWRITE_TAC[CARD_SING]))] THEN AP_TERM_TAC;
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      SIMP_TAC[FINITE_NUMSEG; FINITE_INTER; CARD_EQ_0];
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM (prove(`CARD {j:num} = 1`, REWRITE_TAC[CARD_SING]))] THEN AP_TERM_TAC] THEN
    REWRITE_TAC[IN_INTER; CARD_SING; IN_NUMSEG; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_SING] THEN
    ASM_MESON_TAC[NOT_LE; LT_SUC_LE; ADD1; ADD_ASSOC; ARITH_RULE `j:num<=p ==> j< p + q + 1`]);;

let OUTER_MVBASIS = prove
 (`!s t. (mbasis s) outer (mbasis t) :real^(P,Q,R)geomalg =
                if s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\ t SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\
                   s INTER t = {}
                then --(&1) pow CARD {i,j | i IN s /\ j IN t /\ i > j} %
                     mbasis(s UNION t)
                else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[outerga; PRODUCTGA_MVBASIS] THEN
  ASM_CASES_TAC `(s:num->bool) INTER t = {}` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[SYMDIFF; SET_RULE `s INTER t = {} ==> s DIFF t UNION t DIFF s = s UNION t`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[SUBSET]);;

let OUTER_MVBASIS_SING = prove
 (`!i j. mbasis{i} outer mbasis{j} :real^(P,Q,R)geomalg =
                if i IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\ j IN 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)) /\ ~(i = j)
                then if i < j then mbasis{i,j} else --(mbasis{i,j})
                else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[outerga; PRODUCTGA_MVBASIS_SING] THEN
  REWRITE_TAC[SET_RULE `{i} INTER {j} = {} <=> ~(i = j)`] THEN
  ASM_CASES_TAC `i:num = j` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
  SUBGOAL_THEN
   `{i',j' | i' IN 1 .. pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
             j' IN 1 .. pdimindex(:P) + pdimindex(:Q) + pdimindex(:R) /\
             i' = i /\
             j' = j /\
             i' > j'} =
    if i > j then {(i,j)} else {}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; PAIR_EQ] THEN
    ASM_MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GT; SYMDIFF; SET_RULE `~(i = j) ==> ({i} DIFF {j}) UNION ({j} DIFF {i}) = {i,j}`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> (j < i <=> ~(i < j))`)) THEN
  ASM_CASES_TAC `i:num < j` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID; FINITE_RULES;
               NOT_IN_EMPTY] THEN
  VECTOR_ARITH_TAC);;

let GEOM_OUTER_MVBASIS_EQ = prove
 (`!s t. s INTER t = {} ==>
  (mbasis s) * (mbasis t) :real^(P,Q,R)geomalg = (mbasis s) outer (mbasis t)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GEOM_MVBASIS; OUTER_MVBASIS; INTER_EMPTY; CARD_CLAUSES; real_pow; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[SYMDIFF; SET_RULE `s INTER t = {} ==> s DIFF t UNION t DIFF s = s UNION t`]);;

let MVBASIS_OUTER_GEOM = prove
 (`!s t. (mbasis s) outer (mbasis t) :real^(P,Q,R)geomalg =
    if s INTER t = {} then mbasis s * mbasis t else vec 0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[GEOM_MVBASIS; OUTER_MVBASIS; INTER_EMPTY; CARD_CLAUSES; real_pow; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[SYMDIFF; SET_RULE `s INTER t = {} ==> s DIFF t UNION t DIFF s = s UNION t`]);;

let MVBASIS_INNER_GEOM = prove
 (`!s t. (mbasis s) inner (mbasis t) :real^(P,Q,R)geomalg =
    if  ~(s = {}) /\ ~(t = {}) /\ (s SUBSET t \/ t SUBSET s) then mbasis s * mbasis t else vec 0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[GEOM_MVBASIS; INNER_MVBASIS] THEN ASM_MESON_TAC[]);;

let OUTER_GEOM_MVBASIS_LASSOC = prove
(`!s t u.
     s INTER u = {} ==>
       (mbasis s):real^(P,Q,R)geomalg * (mbasis t outer mbasis u) =
       (mbasis s * mbasis t) outer mbasis u`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)`;
    `t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)`;
    `u SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)`] THEN
  ASM_CASES_TAC `t:num->bool INTER u = {}` THEN
  ASM_REWRITE_TAC[OUTER_MVBASIS; GEOM_MVBASIS; OUTERGA_LMUL; GEOMGA_RMUL; UNION_SUBSET] THEN
  ASSUME_TAC (prove(`(s INTER u = {} ==> t INTER u = {} ==> (s SYMDIFF t) INTER u = {}) /\
                     (s INTER u = {} ==> ~(t INTER u = {}) ==> ~((s SYMDIFF t) INTER u = {}))`,
                      REWRITE_TAC[SYMDIFF] THEN SET_TAC[])) THEN
  ASM_SIMP_TAC[SYMDIFF_SUBSET; SET_RULE `t INTER u = {} ==> t UNION u = t DIFF u UNION u DIFF t`;
               GSYM SYMDIFF; SYMDIFF_ASSOC; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO; GEOMGA_RZERO; OUTERGA_LZERO] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `(a * c * d) * b = a:real * b * c * d`; REAL_MUL_ASSOC; SYMDIFF] THEN
  BINOP_TAC THENL
    [BINOP_TAC THENL
       [ALL_TAC;
        AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]
       ];
     AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_NEG; REAL_POW_ONE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EVEN_ADD] THEN
  W(fun (_,w) -> let tu = funpow 2 lhand w in
                 let su = vsubst[`s:num->bool`,`t:num->bool`] tu in
                 let st = vsubst[`t:num->bool`,`u:num->bool`] su in
                 MATCH_MP_TAC EQ_TRANS THEN
                 EXISTS_TAC(end_itlist (curry mk_eq) [st; su; tu])) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(x <=> y <=> z) ==> ((a <=> x) <=> (y <=> z <=> a))`);
    AP_TERM_TAC THEN CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC SYMDIFF_PARITY_LEMMA THEN CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
      [ALL_TAC;
       REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
              IN_UNION; IN_DIFF] THEN CONV_TAC TAUT];
    ALL_TAC;
    CONJ_TAC THENL
      [ALL_TAC;
       REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
              IN_UNION; IN_DIFF] THEN CONV_TAC TAUT]] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i,j | i IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\
                     j IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\ i > j}` THEN
  ASM SET_TAC[FINITE_CART_SUBSET_LEMMA1]);;

let OUTER_GEOM_MVBASIS_RASSOC = prove
(`!s t u.
     s INTER u = {} ==>
       (mbasis s outer mbasis t) * (mbasis u):real^(P,Q,R)geomalg =
       mbasis s outer (mbasis t * mbasis u)`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)`;
    `t SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)`;
    `u SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)`] THEN
  ASM_CASES_TAC `s:num->bool INTER t = {}` THEN
  ASM_REWRITE_TAC[OUTER_MVBASIS; GEOM_MVBASIS; OUTERGA_RMUL; GEOMGA_LMUL; UNION_SUBSET] THEN
  ASSUME_TAC (prove(`(s INTER u = {} ==> s INTER t = {} ==> s INTER (t SYMDIFF u) = {}) /\
                     (s INTER u = {} ==> ~(s INTER t = {}) ==> ~(s INTER (t SYMDIFF u) = {}))`,
                      REWRITE_TAC[SYMDIFF] THEN SET_TAC[])) THEN
  ASM_SIMP_TAC[SYMDIFF_SUBSET; SET_RULE `s INTER t = {} ==> s UNION t = s DIFF t UNION t DIFF s`;
               GSYM SYMDIFF; SYMDIFF_ASSOC; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO; GEOMGA_LZERO; OUTERGA_RZERO] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `(a * c * d) * b = a:real * b * c * d`; REAL_MUL_ASSOC; SYMDIFF] THEN
  BINOP_TAC THENL
    [BINOP_TAC THENL
       [ALL_TAC;
        AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]
       ];
     AP_TERM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_NEG; REAL_POW_ONE] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EVEN_ADD] THEN
  W(fun (_,w) -> let st = funpow 2 lhand w in
                 let su = vsubst[`u:num->bool`,`t:num->bool`] st in
                 let tu = vsubst[`t:num->bool`,`s:num->bool`] su in
                 MATCH_MP_TAC EQ_TRANS THEN
                 EXISTS_TAC(end_itlist (curry mk_eq) [tu; su; st])) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `(x <=> y <=> z) ==> ((a <=> x) <=> (y <=> z <=> a))`);
    AP_TERM_TAC THEN CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC SYMDIFF_PARITY_LEMMA THEN CONJ_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL
      [ALL_TAC;
       REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
              IN_UNION; IN_DIFF] THEN CONV_TAC TAUT];
    ALL_TAC;
    CONJ_TAC THENL
      [ALL_TAC;
       REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
              IN_UNION; IN_DIFF] THEN CONV_TAC TAUT]] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i,j | i IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\
                     j IN 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R) /\ i > j}` THEN
  ASM SET_TAC[FINITE_CART_SUBSET_LEMMA1]);;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences about outer product.                             *)
(* ------------------------------------------------------------------------- *)

let OUTER_MVBASIS_SKEWSYM = prove
 (`!i j. mbasis{i} outer mbasis{j} = --(mbasis{j} outer mbasis{i})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OUTER_MVBASIS_SING] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[VECTOR_NEG_0] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> i < j /\ ~(j < i) \/ j < i /\ ~(i < j)`)) THEN
  ASM_REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_NEG_0] THEN
  REPEAT AP_TERM_TAC THEN SET_TAC[]);;

let OUTER_MVBASIS_REFL = prove
 (`!i. mbasis{i} outer mbasis{i} = vec 0`,
  GEN_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
   `!x:real^N. x = --x ==> x = vec 0`) THEN
  MATCH_ACCEPT_TAC OUTER_MVBASIS_SKEWSYM);;

let OUTER_MVBASIS_LSCALAR = prove
 (`!x. mbasis{} outer x = x`,
  MATCH_MP_TAC MVBASIS_EXTENSION THEN SIMP_TAC[OUTERGA_RMUL; OUTERGA_RADD] THEN
  SIMP_TAC[OUTER_MVBASIS; EMPTY_SUBSET; INTER_EMPTY; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN {} /\ j IN s /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID]);;

let OUTER_MVBASIS_RSCALAR = prove
 (`!x. x outer mbasis{} = x`,
  MATCH_MP_TAC MVBASIS_EXTENSION THEN SIMP_TAC[OUTERGA_LMUL; OUTERGA_LADD] THEN
  SIMP_TAC[OUTER_MVBASIS; EMPTY_SUBSET; INTER_EMPTY; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN s /\ j IN {} /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID]);;

let OUTER_MVBASIS_SING_EQ_0 = prove
 (`!i j.
   mbasis{i} outer (mbasis{j}:real^(P,Q,R)geomalg) = vec 0
       <=> ~(i IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
          /\ j IN 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)
          /\ ~(i = j))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OUTER_MVBASIS_SING] THEN REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0] THEN MATCH_MP_TAC MVBASIS_NONZERO THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]);;

let MVBASIS_SPLIT = prove
 (`!a s. (!x. x IN s ==> a < x)
         ==> mbasis (a INSERT s) = mbasis{a} outer mbasis s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OUTER_MVBASIS] THEN
  SUBGOAL_THEN `{a:num} INTER s = {}` SUBST1_TAC THENL
   [ASM SET_TAC [LT_REFL]; ALL_TAC] THEN
  SIMP_TAC[SET_RULE`{a} SUBSET t /\ s SUBSET t <=> (a INSERT s) SUBSET t`] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[MVBASIS_EQ_0]] THEN
  REWRITE_TAC[SET_RULE `{a} UNION s = a INSERT s`] THEN
  SUBGOAL_THEN `{(i:num),(j:num) | i IN {a} /\ j IN s /\ i > j} = {}`
   (fun th -> SIMP_TAC[th; CARD_CLAUSES; real_pow; VECTOR_MUL_LID]) THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_SING;
              NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[ARITH_RULE `~(n < m /\ n:num > m)`]);;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences about geometric product.                          *)
(* ------------------------------------------------------------------------- *)

let GEOM_MVBASIS_SKEWSYM = prove
 (`!i j. mbasis{i} * mbasis{j} =
  if i = j then mbasis{j} * mbasis{i} else --(mbasis{j} * mbasis{i})`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[GEOM_MVBASIS_SING] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> i < j /\ ~(j < i) \/ j < i /\ ~(i < j)`)) THEN
  ASM_REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_NEG_0] THEN
  REPEAT AP_TERM_TAC THEN SET_TAC[]);;

let GEOM_MVBASIS_REFL = prove
 (`!i. mbasis{i}:real^(P,Q,R)geomalg * mbasis{i} =
       if i IN 1..pdimindex (:P)
                then mbasis {}
                else if i IN pdimindex (:P) + 1..pdimindex (:P) + pdimindex (:Q)
                     then --mbasis {}
                     else vec 0`,
  GEN_TAC THEN REWRITE_TAC[GEOM_MVBASIS_SING] THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let GEOM_MVBASIS_LID = prove
 (`!x. mbasis{} * x = x`,
  MATCH_MP_TAC MVBASIS_EXTENSION THEN SIMP_TAC[GEOMGA_RMUL; GEOMGA_RADD] THEN
  SIMP_TAC[GEOM_MVBASIS; SYMDIFF_EMPTY; EMPTY_SUBSET; INTER_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN {} /\ j IN s /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; REAL_MUL_LID; VECTOR_MUL_LID]);;

let GEOM_MVBASIS_RID = prove
 (`!x. x * mbasis{} = x`,
  MATCH_MP_TAC MVBASIS_EXTENSION THEN SIMP_TAC[GEOMGA_LMUL; GEOMGA_LADD] THEN
  SIMP_TAC[GEOM_MVBASIS; SYMDIFF_EMPTY; EMPTY_SUBSET; INTER_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN s /\ j IN {} /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; REAL_MUL_LID; VECTOR_MUL_LID]);;

let MVBASIS_SPLIT_GEOM = prove
 (`!a s. (!x. x IN s ==> a < x)
         ==> mbasis (a INSERT s) = mbasis{a} * mbasis s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a:num} INTER s = {}` ASSUME_TAC THENL
   [ASM SET_TAC [LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MVBASIS_SPLIT; GEOM_OUTER_MVBASIS_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences about inner product.                             *)
(* ------------------------------------------------------------------------- *)

let INNER_MVBASIS_SKEWSYM = prove
 (`!i j. mbasis{i} inner mbasis{j} = mbasis{j} inner mbasis{i}`,
  REPEAT GEN_TAC THEN ASM_REWRITE_TAC[INNER_MVBASIS_SING] THEN
  ASM_CASES_TAC `i:num = j` THEN
  ASM_REWRITE_TAC[]);;

let INNER_MVBASIS_REFL = prove
 (`!i. mbasis{i}:real^(P,Q,R)geomalg inner mbasis{i} =
       if i IN 1..pdimindex (:P)
                then mbasis {}
                else if i IN pdimindex (:P) + 1..pdimindex (:P) + pdimindex (:Q)
                     then --mbasis {}
                     else vec 0`,
  GEN_TAC THEN REWRITE_TAC[INNER_MVBASIS_SING] THEN
  COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences about vector.                                    *)
(* ------------------------------------------------------------------------- *)

let swappair = new_definition
  `swappair p = (SND p, FST p)`;;

let VECTOR_GEOM_EQ_OUTER_ADD_INNER = prove
(`!x y:real^(P,Q,R)trip_fin_sum.
  (multivec x) * (multivec y) = (multivec x) outer (multivec y) + (multivec x) inner (multivec y)`,
  REWRITE_TAC[multivect] THEN
  SIMP_TAC[FINITE_NUMSEG; BILINEAR_INNERGA; BILINEAR_OUTERGA; BILINEAR_GEOMGA ;BILINEAR_VSUM] THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_CROSS; GSYM VSUM_ADD] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS]THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GEOMGA_RMUL; GEOMGA_LMUL; OUTERGA_RMUL; OUTERGA_LMUL; INNERGA_RMUL; INNERGA_LMUL] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[GEOM_MVBASIS_SING; OUTER_MVBASIS_SING; INNER_MVBASIS_SING] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID]);;

let VECTOR_OUTERGA_SKEWSYM = prove
 ( `!x y:real^(P,Q,R)trip_fin_sum. (multivec x) outer (multivec y) = --((multivec y) outer (multivec x))`,
   REPEAT STRIP_TAC THEN REWRITE_TAC[multivect] THEN
   SIMP_TAC[FINITE_NUMSEG; BILINEAR_OUTERGA; BILINEAR_VSUM] THEN
   REWRITE_TAC[CROSS; OUTERGA_LMUL; OUTERGA_RMUL] THEN
   GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[OUTER_MVBASIS_SKEWSYM] THEN
   REWRITE_TAC[VECTOR_MUL_RNEG; LAMBDA_PAIR; VSUM_NEG] THEN
   REWRITE_TAC[VECTOR_NEG_NEG; GSYM LAMBDA_PAIR] THEN
   GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)[prove(`!P. (\(x,y). P x y) = (\(x,y). P y x) o swappair`,
   REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM; swappair])] THEN
   REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[
        prove(`!s. {x,y | x IN s /\ y IN s} = IMAGE swappair {x,y | x IN s /\ y IN s}`,
        REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM; swappair] THEN MESON_TAC[PAIR_EQ])] THEN
   GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[REAL_MUL_SYM] THEN
   MATCH_MP_TAC VSUM_IMAGE THEN REWRITE_TAC[GSYM IN_CROSS; GSYM SET_PAIR_THM; IN_ELIM_THM; IN_GSPEC] THEN
   SIMP_TAC[FINITE_NUMSEG; FINITE_CROSS] THEN REWRITE_TAC[swappair; FORALL_PAIR_THM] THEN
   MESON_TAC[PAIR_EQ]);;

let VECTOR_OUTERGA_REFL = prove
 (`!x:real^(P,Q,R)trip_fin_sum. (multivec x) outer (multivec x) = vec 0`,
   GEN_TAC THEN MATCH_MP_TAC (VECTOR_ARITH `x = --x ==> x = vec 0:real^N`) THEN
   MATCH_ACCEPT_TAC VECTOR_OUTERGA_SKEWSYM);;

let VECTOR_INNERGA_REFL = prove
 (`!x:real^(P,Q,R)trip_fin_sum.
     multivec x inner multivec x =
        (sum(1..pdimindex (:P))(\i. x$i * x$i) - sum(1..pdimindex (:Q)) (\i. x$(i+pdimindex (:P)) * x$(i+pdimindex (:P)))) % mbasis {}`,
  GEN_TAC THEN
  REWRITE_TAC[multivect] THEN SIMP_TAC[FINITE_NUMSEG; BILINEAR_INNERGA; BILINEAR_VSUM] THEN REWRITE_TAC[CROSS] THEN
  SIMP_TAC[FINITE_NUMSEG; GSYM VSUM_VSUM_PRODUCT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `vsum(1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))
       (\i. ((x:real^(P,Q,R)trip_fin_sum)$i * x$i) % (mbasis {i} inner mbasis {i})):real^(P,Q,R)geomalg` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[INNERGA_RMUL; INNERGA_LMUL; VECTOR_MUL_ASSOC] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[INNER_MVBASIS_SING] THEN ONCE_REWRITE_TAC[COND_RAND] THEN GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ; VECTOR_MUL_RZERO] THEN
    ASM_SIMP_TAC[VSUM_DELTA]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB_RDISTRIB; VECTOR_SUB] THEN SIMP_TAC[LE_ADDR; VSUM_ADD_SPLIT] THEN BINOP_TAC THENL
   [REWRITE_TAC[GSYM VSUM_RMUL] THEN MATCH_MP_TAC VSUM_EQ THEN MESON_TAC[INNER_MVBASIS_REFL]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_RNEG; GSYM VSUM_RMUL] THEN MATCH_MP_TAC VSUM_EQ_SUPERSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INNER_MVBASIS_REFL; IN_NUMSEG] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= (i:num) ==> ~(i + n <= n)`] THEN
  ASM_MESON_TAC[ADD_SYM; LE_ADD_LCANCEL; VECTOR_MUL_RZERO]);;

let VECTOR_GEOMGA_INNER_REFL_EQ = prove
 (`!x:real^(P,Q,R)trip_fin_sum.
     multivec x * multivec x = multivec x inner multivec x`,
  REWRITE_TAC[VECTOR_GEOM_EQ_OUTER_ADD_INNER; VECTOR_OUTERGA_REFL; VECTOR_ADD_LID]);;

let VECTOR_GEOMGA_REFL = prove
 (`!x:real^(P,Q,R)trip_fin_sum.
     multivec x * multivec x =
        (sum(1..pdimindex (:P))(\i. x$i * x$i) - sum(1..pdimindex (:Q)) (\i. x$(i+pdimindex (:P)) * x$(i+pdimindex (:P)))) % mbasis {}`,
  REWRITE_TAC[VECTOR_GEOM_EQ_OUTER_ADD_INNER; VECTOR_OUTERGA_REFL; VECTOR_INNERGA_REFL; VECTOR_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Conversion to split extended basis combinations.                          *)
(* From Harrision's library.                                                 *)
(* Also 1-step merge from left, which can be DEPTH_CONV'd. In this case the  *)
(* order must be correct.                                                    *)
(* ------------------------------------------------------------------------- *)

let MVBASIS_SPLIT_CONV,MVBASIS_MERGE_CONV =
  let setlemma = SET_RULE
   `((!x:num. x IN {} ==> a < x) <=> T) /\
    ((!x:num. x IN (y INSERT s) ==> a < x) <=>
              a < y /\ (!x. x IN s ==> a < x))` in
  let SET_CHECK_CONV =
    GEN_REWRITE_CONV TOP_SWEEP_CONV [setlemma] THENC NUM_REDUCE_CONV
  and INST_SPLIT = PART_MATCH (lhs o rand) MVBASIS_SPLIT
  and INST_MERGE = PART_MATCH (lhs o rand) (GSYM MVBASIS_SPLIT) in
  let rec conv tm =
    if length(dest_setenum(rand tm)) <= 1 then REFL tm else
    let th = MP_CONV SET_CHECK_CONV (INST_SPLIT tm) in
    let th' = RAND_CONV conv (rand(concl th)) in
    TRANS th th' in
  (fun tm ->
    try let op,se = dest_comb tm in
        if fst(dest_const op) = "mvbasis" && forall is_numeral (dest_setenum se)
        then (RAND_CONV SETENUM_NORM_CONV THENC conv) tm
        else fail()
    with Failure _ -> failwith "MVBASIS_SPLIT_CONV"),
  (fun tm -> try MP_CONV SET_CHECK_CONV (INST_MERGE tm)
             with Failure _ -> failwith "MVBASIS_MERGE_CONV");;

MVBASIS_SPLIT_CONV `mbasis {1,2}`;;

(* ------------------------------------------------------------------------- *)
(* Conversion to split extended basis combinations(with geometric product).  *)
(* Also 1-step merge from left, which can be DEPTH_CONV'd. In this case the  *)
(* order must be correct.                                                    *)
(* ------------------------------------------------------------------------- *)

let GEOM_MVBASIS_SPLIT_CONV,GEOM_MVBASIS_MERGE_CONV =
  let setlemma = SET_RULE
   `((!x:num. x IN {} ==> a < x) <=> T) /\
    ((!x:num. x IN (y INSERT s) ==> a < x) <=>
              a < y /\ (!x. x IN s ==> a < x))` in
  let SET_CHECK_CONV =
    GEN_REWRITE_CONV TOP_SWEEP_CONV [setlemma] THENC NUM_REDUCE_CONV
  and INST_SPLIT = PART_MATCH (lhs o rand) MVBASIS_SPLIT_GEOM
  and INST_MERGE = PART_MATCH (lhs o rand) (GSYM MVBASIS_SPLIT_GEOM) in
  let rec conv tm =
    if length(dest_setenum(rand tm)) <= 1 then REFL tm else
    let th = MP_CONV SET_CHECK_CONV (INST_SPLIT tm) in
    let th' = RAND_CONV conv (rand(concl th)) in
    TRANS th th' in
  (fun tm ->
    try let op,se = dest_comb tm in
        if fst(dest_const op) = "mvbasis" && forall is_numeral (dest_setenum se)
        then (RAND_CONV SETENUM_NORM_CONV THENC conv) tm
        else fail()
    with Failure _ -> failwith "GEOM_MVBASIS_SPLIT_CONV"),
  (fun tm -> try MP_CONV SET_CHECK_CONV (INST_MERGE tm)
             with Failure _ -> failwith "GEOM_MVBASIS_MERGE_CONV");;

GEOM_MVBASIS_SPLIT_CONV `mbasis {1,2}`;;

(* ------------------------------------------------------------------------------------ *)
(* Convergent (if slow) rewrite set to bubble into position. From Harrision's library.  *)
(* ------------------------------------------------------------------------------------ *)

let OUTERGA_ACI = prove
 (`(!x y z. (x outer y) outer z = x outer (y outer z)) /\
   (!i j. i > j
          ==> mbasis{i} outer mbasis{j} =
              --(&1) % (mbasis{j} outer mbasis{i})) /\
   (!i j x. i > j
            ==> mbasis{i} outer mbasis{j} outer x =
                --(&1) % (mbasis{j} outer mbasis{i} outer x)) /\
   (!i. mbasis{i} outer mbasis{i} = vec 0) /\
   (!i x. mbasis{i} outer mbasis{i} outer x = vec 0) /\
   (!x. mbasis{} outer x = x) /\
   (!x. x outer mbasis{} = x)`,
  REWRITE_TAC[OUTERGA_ASSOC; OUTERGA_LZERO; OUTERGA_RZERO; OUTERGA_LADD;
            OUTERGA_RADD; OUTERGA_LMUL; OUTERGA_RMUL; OUTERGA_LZERO; OUTERGA_RZERO] THEN
  REWRITE_TAC[OUTER_MVBASIS_REFL; OUTERGA_LZERO] THEN
  REWRITE_TAC[OUTER_MVBASIS_LSCALAR; OUTER_MVBASIS_RSCALAR] THEN
  SIMP_TAC[GSYM VECTOR_NEG_MINUS1; VECTOR_ARITH `x - y:real^N = x + --y`] THEN
  MESON_TAC[OUTER_MVBASIS_SKEWSYM; OUTERGA_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* Geometric product ACI.                                                    *)
(* ------------------------------------------------------------------------- *)

let GEOM_ACI = prove
 (`(!x y z:real^(P,Q,R)geomalg. (x * y) * z = x * (y * z)) /\
   (!i j. i > j
          ==> mbasis{i}:real^(P,Q,R)geomalg * mbasis{j} =
              --(&1) % (mbasis{j} * mbasis{i})) /\
   (!i j x:real^(P,Q,R)geomalg. i > j
            ==> mbasis{i} * mbasis{j} * x =
                --(&1) % (mbasis{j} * mbasis{i} * x)) /\
   (!i. mbasis{i}:real^(P,Q,R)geomalg * mbasis{i} = (if i IN 1..pdimindex (:P)
          then mbasis{}
          else if i IN pdimindex (:P) + 1..pdimindex (:P) + pdimindex (:Q)
               then --(&1) % mbasis{}
               else vec 0)) /\
   (!i x:real^(P,Q,R)geomalg. mbasis{i} * mbasis{i} * x = if i IN 1..pdimindex (:P)
          then x
          else if i IN pdimindex (:P) + 1..pdimindex (:P) + pdimindex (:Q)
               then --(&1) % x
               else vec 0) /\
   (!x:real^(P,Q,R)geomalg. mbasis{} * x = x) /\
   (!x:real^(P,Q,R)geomalg. x * mbasis{} = x) /\
   (!p x y z:real^(P,Q,R)geomalg. x * (if p then y else z) =
       if p then x * y else x * z)`,
  REWRITE_TAC[GEOMGA_ASSOC; GEOM_MVBASIS_REFL; GEOM_MVBASIS_LID; GEOM_MVBASIS_RID] THEN
  SIMP_TAC[GSYM VECTOR_NEG_MINUS1] THEN
  MESON_TAC[ARITH_RULE `i:num > j ==> ~(i = j)`; GEOM_MVBASIS_SKEWSYM;
            GEOMGA_LNEG; GEOM_MVBASIS_LID; GEOMGA_LZERO; COND_RAND]);;

(* ------------------------------------------------------------------------- *)
(* Group the final "c1 % mbasis s1 + ... + cn % mbasis sn".                  *)
(* From Harrision's library.                                                 *)
(* ------------------------------------------------------------------------- *)

MBASIS_GROUP_CONV `&2 % mbasis{1,2} + &3 % mbasis{2} + &2 % mbasis{1,3} + --(&3) % mbasis{1}:real^('4,'1,'1)geomalg`;;

(* ------------------------------------------------------------------------- *)
(* Overall conversion.                                                       *)
(* ------------------------------------------------------------------------- *)

let OUTERGA_CANON_CONV =
  ONCE_DEPTH_CONV MVBASIS_SPLIT_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [VECTOR_SUB; VECTOR_NEG_MINUS1;
    OUTERGA_LADD; OUTERGA_RADD; OUTERGA_LMUL; OUTERGA_RMUL; OUTERGA_LZERO; OUTERGA_RZERO;
    VECTOR_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC;
    VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THENC
  REAL_RAT_REDUCE_CONV THENC
  PURE_SIMP_CONV[OUTERGA_ACI; ARITH_GT; ARITH_GE; OUTERGA_LMUL; OUTERGA_RMUL;
                 OUTERGA_LZERO; OUTERGA_RZERO] THENC
  PURE_REWRITE_CONV[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO;
                    VECTOR_ADD_LID; VECTOR_ADD_RID; VECTOR_MUL_ASSOC] THENC
  GEN_REWRITE_CONV I [GSYM VECTOR_MUL_LID] THENC
  PURE_REWRITE_CONV
   [VECTOR_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC] THENC
  REAL_RAT_REDUCE_CONV THENC PURE_REWRITE_CONV[GSYM VECTOR_ADD_ASSOC] THENC
  DEPTH_CONV MVBASIS_MERGE_CONV THENC
  MBASIS_GROUP_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [GSYM VECTOR_ADD_RDISTRIB] THENC
  REAL_RAT_REDUCE_CONV;;

let GEOM_CANON_CONV =
  ONCE_DEPTH_CONV GEOM_MVBASIS_SPLIT_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [VECTOR_SUB; VECTOR_NEG_MINUS1;
    GEOMGA_LADD; GEOMGA_RADD; GEOMGA_LMUL; GEOMGA_RMUL; GEOMGA_LZERO; GEOMGA_RZERO;
    VECTOR_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC;
    VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THENC
  REAL_RAT_REDUCE_CONV THENC
  PURE_SIMP_CONV[GEOM_ACI; ARITH_GT; ARITH_GE; GEOMGA_LMUL; GEOMGA_RMUL;
                 GEOMGA_LZERO; GEOMGA_RZERO] THENC
  PURE_REWRITE_CONV[PDIMINDEX_0; PDIMINDEX_1; PDIMINDEX_2; PDIMINDEX_3; PDIMINDEX_4; IN_NUMSEG] THENC
  NUM_REDUCE_CONV THENC
  PURE_REWRITE_CONV[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO;
                    VECTOR_ADD_LID; VECTOR_ADD_RID; VECTOR_MUL_ASSOC] THENC
  GEN_REWRITE_CONV I [GSYM VECTOR_MUL_LID] THENC
  PURE_REWRITE_CONV
   [VECTOR_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC] THENC
  REAL_RAT_REDUCE_CONV THENC PURE_REWRITE_CONV[GSYM VECTOR_ADD_ASSOC] THENC
  DEPTH_CONV GEOM_MVBASIS_MERGE_CONV THENC
  MBASIS_GROUP_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [GSYM VECTOR_ADD_RDISTRIB] THENC
  REAL_RAT_REDUCE_CONV THENC
  PURE_REWRITE_CONV[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_ADD_RID];;

GEOM_CANON_CONV `(mbasis{2,3}:real^('3,'0,'1)geomalg) * mbasis{1,2,3,4}`;;

let GA_GEOM_CONV =
  PURE_REWRITE_CONV[MVBASIS_OUTER_GEOM; MVBASIS_INNER_GEOM] THENC
  SIMP_CONV[EXTENSION; IN_INTER; IN_INSERT; SUBSET; NOT_IN_EMPTY;
            NOT_FORALL_THM; GSYM NOT_EXISTS_THM; EXISTS_REFL;
            ARITH_RULE `!a b x:num. ~(a=b) ==> ~(x=a /\ x=b)`;
             EXISTS_OR_THM; ARITH_EQ];;

GA_GEOM_CONV `mbasis{1} *(mbasis{1} inner mbasis{1,3} +
                      mbasis{1} outer mbasis{2}:real^('4,'1,'1)geomalg)`;;

(GA_GEOM_CONV THENC GEOM_CANON_CONV)
  `mbasis{1} *(mbasis{1} inner mbasis{1,3} +
       mbasis{1} outer mbasis{2}:real^('4,'1,'1)geomalg)`;;

let GEOM_ARITH tm =
   let l,r = dest_eq tm in
   let th,th' = GEOM_CANON_CONV l, GEOM_CANON_CONV r in
   TRANS th (SYM th');;

let OUTERGA_VECTOR_CONV =
  REWRITE_CONV[REWRITE_RULE[LINEAR_MULTIVECT](ISPEC `multivec:real^(P,Q,R)trip_fin_sum->real^(P,Q,R)geomalg` linear);
               MULTIVECT_BASIS; VECTOR_SUB; VECTOR_NEG_MINUS1] THENC OUTERGA_CANON_CONV;;

OUTERGA_VECTOR_CONV
`(multivec (basis 1 + basis 2)) outer (multivec (basis 2 + basis 3)) outer (multivec (basis 1 - (basis 3)))`;;

OUTERGA_VECTOR_CONV
`(multivec (basis 1 + basis 2)) outer (multivec (basis 2 + basis 3)) outer (multivec (basis 1 + (basis 3)))`;;

(* ------------------------------------------------------------------------- *)
(* Invertibility of geomalgs.                                                *)
(* ------------------------------------------------------------------------- *)

let mvinvertible = new_definition
 `mvinvertible (x:real^(P,Q,R)geomalg) <=> (?x'. x' * x = mbasis {} /\ x * x' = mbasis {})`;;

let mvinverse = new_definition
  `mvinverse (x:real^(P,Q,R)geomalg) = (@x'. x' * x = mbasis {} /\ x * x' = mbasis {})`;;

let MVINVERTIBLE_MVINVERSE = prove
 (`!x:real^(P,Q,R)geomalg.
    mvinvertible x <=> mvinverse x * x = mbasis {} /\ x * mvinverse x = mbasis {}`,
  MESON_TAC[mvinvertible; mvinverse]);;

let MV_LEFT_RIGHT_INVERSE = prove
 (`!x y:real^(P,Q,R)geomalg. x * y = mbasis {} <=> y * x = mbasis {}`,
  SUBGOAL_THEN
      `!x y:real^(P,Q,R)geomalg. (x * y = mbasis {}) ==> (y * x = mbasis {})`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\z:real^(P,Q,R)geomalg. x:(real^(P,Q,R)geomalg) * z`
    LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  REWRITE_TAC[REWRITE_RULE[bilinear] BILINEAR_GEOMGA] THEN ANTS_TAC THENL
  [X_GEN_TAC `z:real^(P,Q,R)geomalg` THEN
   EXISTS_TAC `(y:real^(P,Q,R)geomalg) * (z:real^(P,Q,R)geomalg)` THEN
   ASM_REWRITE_TAC[GEOMGA_ASSOC; GEOM_MVBASIS_LID]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^(P,Q,R)geomalg->real^(P,Q,R)geomalg` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f':real^(P,Q,R)geomalg->real^(P,Q,R)geomalg) (x:real^(P,Q,R)geomalg) = mbasis {}`
  MP_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GSYM GEOM_MVBASIS_RID] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GSYM GEOM_MVBASIS_LID] THEN
  ASSUM_LIST(fun thl -> REWRITE_TAC(map GSYM thl)) THEN
  ASM_REWRITE_TAC[GSYM GEOMGA_ASSOC]);;

let MVINVERTIBLE_LEFT_INVERSE = prove
 (`mvinvertible (x:real^(P,Q,R)geomalg) <=> (?x'. x' * x = mbasis {})`,
  MESON_TAC[mvinvertible; MV_LEFT_RIGHT_INVERSE]);;

let MVINVERTIBLE_RIGHT_INVERSE = prove
 (`mvinvertible (x:real^(P,Q,R)geomalg) <=> (?x'. x * x' = mbasis {})`,
  MESON_TAC[mvinvertible; MV_LEFT_RIGHT_INVERSE]);;

let is_null = new_definition
 `is_null (x:real^(P,Q,R)geomalg) <=> x inner x = vec 0`;;

let MVINVERTIBLE_VECTOR_EQ = prove
 (`!x:real^(P, Q, R)trip_fin_sum. ~(is_null(multivec x)) <=> mvinvertible (multivec x)`,
  GEN_TAC THEN REWRITE_TAC[is_null; MVINVERTIBLE_LEFT_INVERSE; GSYM VECTOR_GEOMGA_INNER_REFL_EQ] THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC
     `inv(sum (1..pdimindex (:P)) (\i. x$i * x$i) -
           sum (1..pdimindex (:Q))
              (\i. x$(i + pdimindex (:P)) * x$(i + pdimindex (:P)))) % multivec (x:real^(P, Q, R)trip_fin_sum)` THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[GEOMGA_LMUL] THEN REWRITE_TAC[VECTOR_GEOMGA_REFL] THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; MVBASIS_EQ_0; EMPTY_SUBSET; VECTOR_MUL_ASSOC] THEN SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `x':real^(P,Q,R)geomalg`) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\y:real^(P,Q,R)geomalg. (x':real^(P,Q,R)geomalg) * x' * y`) THEN
  ASM_REWRITE_TAC[GEOM_ARITH `a * b * c * d = a * (b * c) * d:real^(P,Q,R)geomalg`; GEOM_MVBASIS_LID; GEOMGA_RZERO] THEN
  REWRITE_TAC[MVBASIS_EQ_0; EMPTY_SUBSET]);;

let MVINVERTIBLE_GEOM = prove
  (`!a b:real^(P,Q,R)geomalg. mvinvertible a /\ mvinvertible b==> mvinvertible (a * b)`,
   REWRITE_TAC[MVINVERTIBLE_LEFT_INVERSE] THEN REPEAT GEN_TAC THEN
   REWRITE_TAC[GSYM RIGHT_EXISTS_AND_THM; GSYM LEFT_EXISTS_AND_THM] THEN
   DISCH_THEN(X_CHOOSE_THEN `a':real^(P,Q,R)geomalg` MP_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `b':real^(P,Q,R)geomalg` MP_TAC) THEN
   STRIP_TAC THEN EXISTS_TAC `b' * (a':real^(P,Q,R)geomalg)` THEN
   REWRITE_TAC[GSYM GEOMGA_ASSOC] THEN
   GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOMGA_ASSOC] THEN
   ASM_REWRITE_TAC[GEOM_MVBASIS_LID]);;

let MVINVERTIBLE_LMUL_EQ= prove
 (`!a b x:real^(P,Q,R)geomalg. mvinvertible x ==> (a = b <=> (x * a = x * b))`,
  REWRITE_TAC[MVINVERTIBLE_MVINVERSE] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[GEOMGA_ASSOC; GEOM_MVBASIS_LID]);;

let MVINVERTIBLE_EQ_LMUL = prove
 (`!a b x:real^(P,Q,R)geomalg. mvinvertible x /\ x * a = x * b ==> a = b`,
   MESON_TAC[MVINVERTIBLE_LMUL_EQ]);;

let MVINVERSE_GEOM = prove
 (`!a b:real^(P,Q,R)geomalg. mvinvertible a /\ mvinvertible b ==> mvinverse b * mvinverse a = mvinverse (a * b)`,
  REPEAT STRIP_TAC THEN
  ASSUME_TAC(SPECL [`a:real^(P,Q,R)geomalg`; `b:real^(P,Q,R)geomalg`]MVINVERTIBLE_GEOM) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MVINVERTIBLE_EQ_LMUL THEN
  EXISTS_TAC `a * b:real^(P,Q,R)geomalg` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM GEOMGA_ASSOC] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GEOMGA_ASSOC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[MVINVERTIBLE_MVINVERSE] THEN
  STRIP_TAC THEN ASSUME_TAC(SPEC `b:real^(P,Q,R)geomalg` MVINVERTIBLE_MVINVERSE) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASSUME_TAC(SPEC `a:real^(P,Q,R)geomalg` MVINVERTIBLE_MVINVERSE) THEN
  POP_ASSUM MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GEOM_MVBASIS_LID]);;

(* ------------------------------------------------------------------------- *)
(* Outermorphism extension.                                                  *)
(* ------------------------------------------------------------------------- *)
make_overloadable "outermorphism" `:(real^M->real^N)->real^A->real^B`;;
overload_interface ("outermorphism",`outergamorphism:(real^(P,Q,R)trip_fin_sum->real^(S,T,U)trip_fin_sum)->real^(P,Q,R)geomalg->real^(S,T,U)geomalg`);;

let outergamorphism = new_definition
 `outermorphism(f:real^(P,Q,R)trip_fin_sum->real^(S,T,U)trip_fin_sum) (x:real^(P,Q,R)geomalg) =
        vsum {s | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}
             (\s. x$$s % seqiterate(outer) s (multivec o f o basis))`;;

let NEUTRAL_OUTERGA = prove
 (`neutral(outer) = mbasis{}`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[OUTER_MVBASIS_LSCALAR; OUTER_MVBASIS_RSCALAR]);;

let NEUTRAL_GEOMGA = prove
 (`neutral( * ) = mbasis{}`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[GEOM_MVBASIS_LID; GEOM_MVBASIS_RID]);;

let OUTERMORPHISM_MVBASIS = prove
 (`!f:real^(P,Q,R)trip_fin_sum->real^(S,T,U)trip_fin_sum s t.
        s SUBSET 1..(pdimindex(:P) + pdimindex(:Q) + pdimindex(:R))
        ==> outermorphism f (mbasis s) =
            seqiterate(outer) s (multivec o f o basis)`,
  REWRITE_TAC[outergamorphism] THEN SIMP_TAC[MVBASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  SIMP_TAC[VECTOR_MUL_LZERO; VSUM_DELTA; IN_ELIM_THM; VECTOR_MUL_LID]);;

let OUTERMORPHISM_MVBASIS_EMPTY = prove
 (`!f. outermorphism f (mbasis {}) = mbasis {}`,
  SIMP_TAC[OUTERMORPHISM_MVBASIS; EMPTY_SUBSET; SEQITERATE_CLAUSES] THEN
  REWRITE_TAC[NEUTRAL_OUTERGA]);;

(* ------------------------------------------------------------------------- *)
(* Properties about SEQITERATE.                                              *)
(* ------------------------------------------------------------------------- *)

let SEQITERATE_NUMSEG_IMAGE = prove
 (`!n op m p f:num->real^(P,Q,R)geomalg.
   seqiterate op (IMAGE (\i. i + p) (m..n)) f = seqiterate op (m..n) (f o (\i. i + p))`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0:num` THENL
    [ALL_TAC;
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC[REWRITE_RULE[LT_NZ](GSYM (SPECL [`m:num`; `0:num`] NUMSEG_EMPTY))] THEN
     DISCH_THEN(SUBST1_TAC)] THEN ASM_REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; SEQITERATE_CLAUSES; o_THM]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m:num <= SUC n` THENL
   [ASM_SIMP_TAC[GSYM NUMSEG_LREC; IMAGE_CLAUSES; o_THM] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
     [MP_TAC
       (ISPECL [`op:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`;
                `f:num->real^(P,Q,R)geomalg`; `m + p:num`; `(IMAGE (\i. i + p) (m + 1..SUC n)):num->bool`]
            (last(CONJUNCTS SEQITERATE_CLAUSES))) THEN
      MP_TAC
       (ISPECL [`op:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`;
                `(f o (\i. i + p)):num->real^(P,Q,R)geomalg`; `m:num`; `(m + 1..SUC n):num->bool`]
          (last(CONJUNCTS SEQITERATE_CLAUSES))) THEN
      SIMP_TAC[FINITE_NUMSEG; FINITE_IMAGE; IMAGE_EQ_EMPTY; EXTENSION; IN_NUMSEG; NOT_IN_EMPTY; IN_IMAGE] THEN
      REPEAT
       (ANTS_TAC THENL
         [CONJ_TAC THENL[REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `SUC n:num`; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC)) THEN
      REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[ADD1; NUMSEG_OFFSET_IMAGE; GSYM IMAGE_o; o_DEF; GSYM ADD_ASSOC]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`] NUMSEG_EMPTY))] THEN
    REWRITE_TAC[IMAGE_CLAUSES; SEQITERATE_CLAUSES; o_THM]; ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[REWRITE_RULE[GSYM NOT_LE](GSYM (SPECL [`m:num`; `SUC n:num`] NUMSEG_EMPTY))] THEN
  DISCH_THEN(SUBST1_TAC) THEN REWRITE_TAC[IMAGE_CLAUSES; SEQITERATE_CLAUSES; o_THM]);;

let SEQITERATE_NUMSEG_SUC = prove
 (`!n m op f:num->real^(P,Q,R)geomalg.
    (!x y z. op (op x y) z = op x (op y z) /\ op (neutral op) x = x) ==>
       m <= SUC n ==>
          seqiterate op (m..SUC n) f = op (seqiterate op (m..n) f) (f (SUC n))`,
  INDUCT_TAC THEN SIMP_TAC[GSYM NUMSEG_LREC] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[LE_LT] THEN REWRITE_TAC[LT_SUC_LE] THEN STRIP_TAC THENL
   [FIRST_ASSUM(fun th ->REWRITE_TAC[REWRITE_RULE[LE]th]) THEN
    REWRITE_TAC[ARITH; NUMSEG_SING] THEN REWRITE_TAC[SEQITERATE_CLAUSES] THEN
    GEN_REWRITE_TAC(RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[GSYM SEQITERATE_CLAUSES] THEN
    MATCH_MP_TAC (last(CONJUNCTS SEQITERATE_CLAUSES)) THEN
    REWRITE_TAC[FINITE_SING; EXTENSION; IN_SING; NOT_IN_EMPTY] THEN
    MESON_TAC[ARITH_RULE `0 < 1`];
    ASM_REWRITE_TAC[GSYM ONE] THEN
    GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o DEPTH_CONV)[ONE; ADD1] THEN
    REWRITE_TAC[REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`]NUMSEG_EMPTY))] THEN
    ASM_REWRITE_TAC[SEQITERATE_CLAUSES];
    MP_TAC
       (ISPECL [`op:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`;
               `f:num->real^(P,Q,R)geomalg`; `m:num`; `(m + 1..SUC (SUC n)):num->bool`]
         (last(CONJUNCTS SEQITERATE_CLAUSES))) THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM NUMSEG_LREC] THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
     [MP_TAC
       (ISPECL [`op:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`;
                `f:num->real^(P,Q,R)geomalg`; `m:num`; `(m + 1..SUC n):num->bool`]
         (last(CONJUNCTS SEQITERATE_CLAUSES))) THEN
      REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_NUMSEG; NOT_IN_EMPTY] THEN
      REPEAT
       (ANTS_TAC THENL
         [CONJ_TAC THENL[REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `SUC n:num`; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC)) THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC[ADD1] THEN
      REWRITE_TAC[NUMSEG_OFFSET_IMAGE; SEQITERATE_NUMSEG_IMAGE] THEN
      POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[LT_IMP_LE; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_NUMSEG; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL[REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `SUC (SUC n):num`; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC) THEN
    ASM_REWRITE_TAC[REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`]NUMSEG_EMPTY))] THEN
    REWRITE_TAC[ADD1; NUMSEG_SING; SEQITERATE_CLAUSES; o_THM];
    ASM_REWRITE_TAC[ADD1; REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`]NUMSEG_EMPTY))] THEN
    ASM_REWRITE_TAC[SEQITERATE_CLAUSES]]);;

let SEQITERATE_OUTERGA_LREC = prove
 (`!n m f:num->real^(P,Q,R)geomalg.
       m <= n ==>
            seqiterate (outer) (m..n) f = (f m) outer (seqiterate (outer) (m + 1..n) f)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
   [MP_TAC
      (ISPECL [`outerga:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`;
               `f:num->real^(P,Q,R)geomalg`; `m:num`; `(m + 1..n):num->bool`]
     (last(CONJUNCTS SEQITERATE_CLAUSES))) THEN
    REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_NUMSEG; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL
      [CONJ_TAC THENL[REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `n:num`; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->REWRITE_TAC[th]); ALL_TAC] THEN
  ASM_REWRITE_TAC[REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`]NUMSEG_EMPTY))] THEN
  REWRITE_TAC[SEQITERATE_CLAUSES; NEUTRAL_OUTERGA; OUTER_MVBASIS_RSCALAR]);;

let SEQITERATE_OUTERGA_RREC =
  GENL[`n:num`; `m:num`]
    (REWRITE_RULE[OUTERGA_ASSOC; NEUTRAL_OUTERGA; OUTER_MVBASIS_LSCALAR]
      (ISPECL[`n:num`; `m:num`; `outerga:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`]
         SEQITERATE_NUMSEG_SUC));;

let SEQITERATE_GEOMGA_LREC = prove
 (`!n m f:num->real^(P,Q,R)geomalg.
       m <= n ==>
            seqiterate ( * ) (m..n) f = (f m) * (seqiterate ( * ) (m + 1..n) f)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM NUMSEG_LREC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
   [MP_TAC
      (ISPECL [`geomga_mul:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`;
               `f:num->real^(P,Q,R)geomalg`; `m:num`; `(m + 1..n):num->bool`]
     (last(CONJUNCTS SEQITERATE_CLAUSES))) THEN
    REWRITE_TAC[FINITE_NUMSEG; EXTENSION; IN_NUMSEG; NOT_IN_EMPTY] THEN
    ANTS_TAC THENL
      [CONJ_TAC THENL[REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `n:num`; ALL_TAC] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th ->REWRITE_TAC[th]); ALL_TAC] THEN
  ASM_REWRITE_TAC[REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`]NUMSEG_EMPTY))] THEN
  REWRITE_TAC[SEQITERATE_CLAUSES; NEUTRAL_GEOMGA; GEOM_MVBASIS_RID]);;

let SEQITERATE_GEOMGA_RREC =
    GENL[`n:num`; `m:num`]
     (REWRITE_RULE[GEOMGA_ASSOC; NEUTRAL_GEOMGA; GEOM_MVBASIS_LID]
      (ISPECL[`n:num`; `m:num`; `geomga_mul:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`] SEQITERATE_NUMSEG_SUC));;

let OUTER_SEQITERATE_SYM = prove
 (`!n m x:real^(P, Q, R)trip_fin_sum f.
   m <= n ==>
   (multivec x) outer seqiterate (outer) (m..n) (multivec o f) =
      (--(&1)) pow (n - m + 1) % (seqiterate (outer) (m..n) (multivec o f) outer (multivec x))`,
  INDUCT_TAC THEN REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMSEG_SING; SEQITERATE_CLAUSES; ARITH; o_THM; ARITH_RULE `m <= n ==> m <= SUC n`; SEQITERATE_OUTERGA_RREC] THEN
  ASM_SIMP_TAC[OUTERGA_ASSOC] THEN REWRITE_TAC[OUTERGA_LMUL; GSYM OUTERGA_ASSOC] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[VECTOR_OUTERGA_SKEWSYM] THEN
  REWRITE_TAC[VECTOR_NEG_MINUS1; VECTOR_MUL_ASSOC; OUTERGA_RNEG; VECTOR_MUL_RNEG; GSYM VECTOR_MUL_LNEG] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> SUC n - m + 1 = SUC (n - m + 1)`] THEN
  REWRITE_TAC[SUB_REFL; ARITH; real_pow] THEN REAL_ARITH_TAC);;

let SEQITERATE_SPLIT_NUMSEG_OUTERGA = prove
 (`!i m n f:num->real^(P,Q,R)geomalg.
       m <= i /\  i <= n
       ==> seqiterate (outer) (m..n) f =
       seqiterate (outer) (m..i) f outer
                    seqiterate (outer) (i + 1..n) f`,
  INDUCT_TAC THEN REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES];
    ASM_REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES];
    SUBGOAL_THEN `m <= i /\ i <= n:num` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `m <= i ==> m <= SUC i`; SEQITERATE_OUTERGA_RREC] THEN
    REWRITE_TAC[GSYM OUTERGA_ASSOC] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV)[GSYM ADD1]] THEN
  MATCH_MP_TAC SEQITERATE_OUTERGA_LREC THEN
  ASM_REWRITE_TAC[]);;

let SEQITERATE_SPLIT_NUMSEG_GEOMGA = prove
 (`!i m n f:num->real^(P,Q,R)geomalg.
       m <= i /\  i <= n
       ==> seqiterate ( * ) (m..n) f =
       seqiterate ( * ) (m..i) f *
                    seqiterate ( * ) (i + 1..n) f`,
    INDUCT_TAC THEN REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES];
    ASM_REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES];
    SUBGOAL_THEN `m <= i /\ i <= n:num` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `m <= i ==> m <= SUC i`; SEQITERATE_GEOMGA_RREC] THEN
    REWRITE_TAC[GSYM GEOMGA_ASSOC] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC (LAND_CONV o DEPTH_CONV)[GSYM ADD1]] THEN
  MATCH_MP_TAC SEQITERATE_GEOMGA_LREC THEN
  ASM_REWRITE_TAC[]);;

let SEQITERATE_OUTERGA_SPLIT3 = prove
 (`!i j m n f:num->real^(P,Q,R)geomalg.
       0 < i /\ m <= i /\  i <= n /\
       m <= j /\ j <= n /\ i < j
       ==> seqiterate (outer) (m..n) f =
       seqiterate (outer) (m..i-1) f outer
       f i outer
       seqiterate (outer) (i+1..j-1) f outer
       f j outer
       seqiterate (outer) (j + 1..n) f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SEQITERATE_SPLIT_NUMSEG_OUTERGA] THEN
  SUBGOAL_THEN `i = SUC (i - 1)` ASSUME_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM (fun th -> GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o DEPTH_CONV)[th]) THEN
  SUBGOAL_THEN `m <= SUC (i - 1)` ASSUME_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SEQITERATE_OUTERGA_RREC] THEN REWRITE_TAC[GSYM OUTERGA_ASSOC] THEN
  AP_TERM_TAC THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `j = SUC (j - 1)` ASSUME_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM (fun th -> GEN_REWRITE_TAC(RAND_CONV o RAND_CONV o LAND_CONV o DEPTH_CONV)[th]) THEN
  REWRITE_TAC[OUTERGA_ASSOC] THEN
  SUBGOAL_THEN `i + 1 <= SUC (j - 1)` ASSUME_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SEQITERATE_OUTERGA_RREC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SEQITERATE_SPLIT_NUMSEG_OUTERGA THEN
  ASM_ARITH_TAC);;

let SEQITERATE_ZERO_OUTERGA = prove
 (`!a:num->real^(P,Q,R)geomalg i m n.
       m <= i /\ i <= n /\ a i = vec 0  ==> seqiterate (outer) (m..n) a = vec 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `i:num = 0` THENL
   [ASM_REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[SEQITERATE_OUTERGA_LREC] THEN REWRITE_TAC[OUTERGA_LZERO];
    ALL_TAC] THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE[GSYM LT_NZ]) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SEQITERATE_SPLIT_NUMSEG_OUTERGA] THEN
  SUBGOAL_THEN `i = SUC (i - 1)` SUBST_ALL_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SEQITERATE_OUTERGA_RREC] THEN
  REWRITE_TAC[OUTERGA_LZERO; OUTERGA_RZERO]);;

let SEQITERATE_OUTERGA_NUMSEG_EQ = prove
 (`!n m f:num->real^(P,Q,R)geomalg g.
     (!x. m <= x /\ x <= n ==> f x = g x) ==>
         seqiterate (outer) (m..n) f = seqiterate (outer) (m..n) g`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`m:num`; `n:num`] LET_CASES) THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THENL
   [SPEC_TAC  (`n:num`,`n:num`) THEN SPEC_TAC  (`m:num`,`m:num`) THEN MATCH_MP_TAC LE_INDUCT; ALL_TAC] THEN
  MESON_TAC[NUMSEG_EMPTY; NUMSEG_SING; SEQITERATE_CLAUSES; ARITH_RULE `m <= n ==> m <= SUC n`;  SEQITERATE_OUTERGA_RREC; LE_REFL]);;


let SEQITERATE_IDENTICAL_OUTERGA = prove
 (`!a:num->real^(P, Q, R)trip_fin_sum i j m n.
       m <= i /\ i <= n /\
       m <= j /\ j <= n /\
       ~(i = j) /\ a i = a j
       ==> seqiterate (outer) (m..n) (multivec o a) = vec 0`,
  REWRITE_TAC[ARITH_RULE `~(i = j:num) <=> i < j \/ j < i`] THEN
  SUBGOAL_THEN
    `!a:num->real^(P, Q, R)trip_fin_sum i j m n.
        m <= i /\ i <= n /\
        m <= j /\ j <= n /\
        i < j /\  a i = a j
        ==> seqiterate (outer) (m..n) (multivec o a) = vec 0`
    (fun th -> MESON_TAC[th]) THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i:num = 0` THENL
   [ASM_REWRITE_TAC[LE] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SEQITERATE_OUTERGA_LREC] THEN
    UNDISCH_TAC `0 < j:num` THEN REWRITE_TAC[GSYM LE_SUC_LT; ARITH] THEN
    REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
     [ALL_TAC;
      POP_ASSUM (SUBST_ALL_TAC o SYM) THEN
      ASM_SIMP_TAC[SEQITERATE_OUTERGA_LREC; OUTERGA_ASSOC; o_THM; VECTOR_OUTERGA_REFL; OUTERGA_LZERO]] THEN
    MP_TAC
     (SPECL [`j:num`; `1:num`; `n:num`; `(multivec o a):num->real^(P,Q,R)geomalg`]
       SEQITERATE_SPLIT_NUMSEG_OUTERGA) THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `j:num = SUC (j - 1)` SUBST_ALL_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LT_IMP_LE; SEQITERATE_OUTERGA_RREC] THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE[LT_SUC_LE]) THEN
    REWRITE_TAC[GSYM OUTERGA_ASSOC] THEN REWRITE_TAC[OUTERGA_ASSOC] THEN
    SIMP_TAC[o_THM; OUTER_SEQITERATE_SYM] THEN
    ONCE_REWRITE_TAC[OUTERGA_LMUL] THEN REWRITE_TAC[GSYM OUTERGA_ASSOC] THEN
    ASM_REWRITE_TAC[VECTOR_OUTERGA_REFL; OUTERGA_RZERO; VECTOR_MUL_RZERO; OUTERGA_LZERO]; ALL_TAC] THEN
  POP_ASSUM (MP_TAC o REWRITE_RULE[GSYM LT_NZ]) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SEQITERATE_OUTERGA_SPLIT3] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[OUTERGA_ASSOC] THEN
  ASM_CASES_TAC `i:num  = j - 1` THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REWRITE_RULE[ARITH_RULE `n < n + 1`](GSYM (SPECL [`n + 1:num`; `n:num`]NUMSEG_EMPTY))] THEN
    REWRITE_TAC[SEQITERATE_CLAUSES; NEUTRAL_OUTERGA; OUTER_MVBASIS_RSCALAR; o_THM] THEN
    GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[OUTERGA_ASSOC] THEN
    ASM_REWRITE_TAC[VECTOR_OUTERGA_REFL; OUTERGA_LZERO; OUTERGA_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `i + 1 <= j:num - 1` ASSUME_TAC  THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM; OUTER_SEQITERATE_SYM] THEN
  REWRITE_TAC[OUTERGA_LMUL; GSYM OUTERGA_ASSOC] THEN
  GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[OUTERGA_ASSOC] THEN
  REWRITE_TAC[VECTOR_OUTERGA_REFL; OUTERGA_LZERO; OUTERGA_RZERO; VECTOR_MUL_RZERO]);;

let SEQITERATE_ADD_OUTERGA = prove
 (`!a b c:num->real^(P,Q,R)geomalg k m n.
    m <= k /\ k <= n ==>
       seqiterate (outer) (m..n) (\i. if i = k then a + b else c i) =
         seqiterate (outer) (m..n) (\i. if i = k then a else c i) +
         seqiterate (outer) (m..n) (\i. if i = k then b else c i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
  (SPECL [`k:num`; `m:num`; `n:num`; `(\i. if i = k then a + b else c i):num->real^(P,Q,R)geomalg`]
  SEQITERATE_SPLIT_NUMSEG_OUTERGA) THEN
  MP_TAC
  (SPECL [`k:num`; `m:num`; `n:num`; `(\i. if i = k then a else c i):num->real^(P,Q,R)geomalg`]
  SEQITERATE_SPLIT_NUMSEG_OUTERGA) THEN
  MP_TAC
  (SPECL [`k:num`; `m:num`; `n:num`; `(\i. if i = k then b else c i):num->real^(P,Q,R)geomalg`]
  SEQITERATE_SPLIT_NUMSEG_OUTERGA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN
  ASM_CASES_TAC `k:num = 0` THENL
   [UNDISCH_TAC `m <= k:num` THEN ASM_REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES] THEN
    REWRITE_TAC[OUTERGA_LADD] THEN BINOP_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SEQITERATE_OUTERGA_NUMSEG_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k:num = SUC (k - 1)` SUBST_ALL_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SEQITERATE_OUTERGA_RREC] THEN
  REWRITE_TAC[OUTERGA_RADD; OUTERGA_LADD] THEN
  BINOP_TAC THEN BINOP_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC; AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SEQITERATE_OUTERGA_NUMSEG_EQ THEN ASM_ARITH_TAC);;

let SEQITERATE_MUL_OUTERGA = prove
(`!a b:num->real^(P,Q,R)geomalg c k m n.
       m <= k /\ k <= n
       ==> seqiterate (outer) (m..n) (\i. if i = k then c % a else b i) =
            c % seqiterate (outer) (m..n) (\i. if i = k then a else b i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
  (SPECL [`k:num`; `m:num`; `n:num`; `(\i. if i = k then c % a else b i):num->real^(P,Q,R)geomalg`]
  SEQITERATE_SPLIT_NUMSEG_OUTERGA) THEN
  MP_TAC
  (SPECL [`k:num`; `m:num`; `n:num`; `(\i. if i = k then a else b i):num->real^(P,Q,R)geomalg`]
  SEQITERATE_SPLIT_NUMSEG_OUTERGA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT (DISCH_THEN SUBST1_TAC) THEN
  ASM_CASES_TAC `k:num = 0` THENL
   [UNDISCH_TAC `m <= k:num` THEN ASM_REWRITE_TAC[LE] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES] THEN
    REWRITE_TAC[OUTERGA_LMUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SEQITERATE_OUTERGA_NUMSEG_EQ THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k:num = SUC (k - 1)` SUBST_ALL_TAC THENL[ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SEQITERATE_OUTERGA_RREC] THEN
  REWRITE_TAC[OUTERGA_RMUL; OUTERGA_LMUL] THEN
  AP_TERM_TAC THEN BINOP_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC; ALL_TAC] THEN
  MATCH_MP_TAC SEQITERATE_OUTERGA_NUMSEG_EQ THEN ASM_ARITH_TAC);;

let SEQITERATE_OPERATION_OUTERGA = prove
(`!a:num->real^(P, Q, R)trip_fin_sum c i j m n.
       m <= i /\ i <= n /\
       m <= j /\ j <= n /\ ~(i = j)
        ==> seqiterate (outer) (m..n) (\k. if k = i then (multivec o a) i + c % (multivec o a) j else (multivec o a) k) =
            seqiterate (outer) (m..n) (multivec o a)`,
  SIMP_TAC[SEQITERATE_ADD_OUTERGA; SEQITERATE_MUL_OUTERGA] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[GSYM VECTOR_ADD_RID] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SEQITERATE_OUTERGA_NUMSEG_EQ THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC (prove(`x = vec 0:real^N ==> c % x = vec 0:real^N`, SIMP_TAC[VECTOR_MUL_RZERO])) THEN
  REWRITE_TAC[GSYM COND_RAND; GSYM o_DEF; GSYM o_ASSOC] THEN
  MATCH_MP_TAC SEQITERATE_IDENTICAL_OUTERGA THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[o_THM]);;

let SEQITERATE_SPAN_OUTERGA = prove
 (`!a:num->real^(P, Q, R)trip_fin_sum i m n x.
        m <= i /\ i <= n /\
        x IN span {a j| m <= j /\ j <= n /\ ~(j = i)}
        ==> seqiterate (outer) (m..n) (\k. if k = i then (multivec o a) i + multivec x else (multivec o a) k) =
            seqiterate (outer) (m..n) (multivec o a)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC SPAN_INDUCT_ALT THEN CONJ_TAC THENL
   [MATCH_MP_TAC SEQITERATE_OUTERGA_NUMSEG_EQ THEN
    MESON_TAC[o_THM; MULTIVECT_0; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) (SUBST_ALL_TAC o SYM)) THEN
  REWRITE_TAC[o_THM; MULTIVECT_ADD; MULTIVECT_MUL] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
     `a + c % x + y:real^N = (a + y) + c % x`] THEN
  ASM_SIMP_TAC[SEQITERATE_ADD_OUTERGA; SEQITERATE_MUL_OUTERGA; VECTOR_EQ_ADDR] THEN
  MATCH_MP_TAC (prove(`x = vec 0:real^N ==> c % x = vec 0:real^N`, SIMP_TAC[VECTOR_MUL_RZERO])) THEN
  REWRITE_TAC[GSYM COND_RAND; GSYM o_DEF; GSYM o_ASSOC] THEN
  MATCH_MP_TAC SEQITERATE_IDENTICAL_OUTERGA THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `j:num`] THEN ASM_REWRITE_TAC[o_THM]);;

let SEQITERATE_DEPENDENT_OUTERGA = prove
 (`!a:num->real^(P,Q,R)trip_fin_sum m n.
  dependent {a i | i IN m..n} ==>
           seqiterate (outer) (m..n) (multivec o a) = vec 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[dependent; IN_ELIM_THM; LEFT_AND_EXISTS_THM; IN_NUMSEG] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEN_TAC THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC
   `?i j. m <= i /\ i <= n /\
          m <= j /\ j <= n /\ ~(i = j) /\
          (a:num->real^(P,Q,R)trip_fin_sum) i = a j`
  THENL [ASM_MESON_TAC[SEQITERATE_IDENTICAL_OUTERGA]; ALL_TAC] THEN
  MP_TAC
    (SPECL[`a:num->real^(P,Q,R)trip_fin_sum`; `i:num`;
            `m:num`; `n:num`; `--((a:num->real^(P,Q,R)trip_fin_sum) i)`]
     SEQITERATE_SPAN_OUTERGA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_NEG THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN]) THEN
    MATCH_MP_TAC(TAUT `a = b ==> a ==> b`) THEN
    REWRITE_TAC[IN] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DELETE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC SEQITERATE_ZERO_OUTERGA THEN
    EXISTS_TAC `i:num` THEN
    ASM_REWRITE_TAC[o_THM; GSYM MULTIVECT_ADD; VECTOR_ADD_RINV; MULTIVECT_0]]);;

let SEQITERATE_OUTERGA_VSUM = prove
 (`!m n a:num->real^(P, Q, R)trip_fin_sum.
     seqiterate (outer) (m..n) (multivec o a) =
       vsum {s | s SUBSET 1..pdimindex(:P) + pdimindex(:Q) + pdimindex(:R)}
        (\s.
          if CARD s = (n + 1) - m
          then (seqiterate (outer) (m..n) (multivec o a))$$s % mbasis s
          else vec 0)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n < m:num` THEN POP_ASSUM MP_TAC THENL
   [SIMP_TAC[ARITH_RULE `n < (m:num) ==> (n + 1) - m = 0`] THEN
    REWRITE_TAC[GSYM NUMSEG_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SEQITERATE_CLAUSES; NEUTRAL_OUTERGA] THEN
    GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_ELIM_THM; MVBASIS_COMPONENT] THEN
    MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET; CARD_EQ_0; VECTOR_MUL_LZERO]; ALL_TAC] THEN
  REWRITE_TAC[NOT_LT] THEN MAP_EVERY SPEC_TAC[(`n:num`, `n:num`); (`m:num`, `m:num`)] THEN
  MATCH_MP_TAC LE_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[NUMSEG_SING; SEQITERATE_CLAUSES; o_THM; ADD_SUB2] THEN
    GEN_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[multivect] THEN
    MATCH_MP_TAC (prove(`c = &0 ==> c % x = vec 0:real^N`, SIMP_TAC[VECTOR_MUL_LZERO])) THEN
    ASM_SIMP_TAC[GEOMALG_VSUM_COMPONENT] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    REWRITE_TAC[SET_RULE `x IN s <=> {x} SUBSET s`] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
    ASM_MESON_TAC[CARD_SING; REAL_MUL_RZERO]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM MVBASIS_EXPANSION] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[ARITH_RULE `m <= n ==> m <= SUC n`; SEQITERATE_OUTERGA_RREC] THEN
  DISCH_TAC THEN MATCH_MP_TAC (prove(`c = &0 ==> c % x = vec 0:real^N`, SIMP_TAC[VECTOR_MUL_LZERO])) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[o_THM; multivect] THEN
  SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG; BILINEAR_OUTERGA; BILINEAR_VSUM] THEN
  REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[OUTERGA_RMUL; OUTERGA_LMUL; OUTERGA_LZERO] THEN
  ASM_SIMP_TAC[GEOMALG_VSUM_COMPONENT] THEN MATCH_MP_TAC SUM_EQ_0 THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; SET_RULE `x IN s <=> {x} SUBSET s`] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[GEOMALG_VEC_COMPONENT; OUTER_MVBASIS] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT; GEOMALG_VEC_COMPONENT; REAL_MUL_RZERO] THEN
  ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SING; FINITE_SUBSET; CARD_SING; CARD_UNION;
                ARITH_RULE `m <= n ==> (SUC n + 1) - m =  ((n + 1) - m) + 1`; REAL_MUL_RZERO]);;

let SEQITERATE_OUTERGA_EQ_0 = prove
 (`!m n a:num->real^(P, Q, R)trip_fin_sum.
     seqiterate (outer) (m..n) (multivec o a) = vec 0
     <=> !s. s SUBSET 1..pdimindex (:P) + pdimindex (:Q) + pdimindex (:R)
          /\ CARD s = (n + 1) - m
          ==> (seqiterate (outer) (m..n) (multivec o a))$$s = &0`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL[SIMP_TAC[GEOMALG_EQ; GEOMALG_VEC_COMPONENT]; ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[SEQITERATE_OUTERGA_VSUM] THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Reversion operation.                                                      *)
(* ------------------------------------------------------------------------- *)

make_overloadable "reversion" `:real^N->real^N`;;
overload_interface ("reversion",`reversionga:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg`);;

let reversionga = new_definition
 `(reversion:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg) x =
    lambdas s. --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2) * x$$s`;;

let REVERSION_MVBASIS = prove
 (`!s. reversion (mbasis s) = --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2) % mbasis s`,
  REWRITE_TAC[reversionga] THEN SIMP_TAC[GEOMALG_BETA; GEOMALG_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

let REVERSIONGA_LINEAR = prove
 (`(!x y. reversion (x + y) = reversion x + reversion y) /\
  (!c x. reversion (c % x) = c % (reversion x))`,
  REWRITE_TAC[reversionga] THEN SIMP_TAC[GEOMALG_BETA; GEOMALG_EQ] THEN
  SIMP_TAC[GEOMALG_ADD_COMPONENT; GEOMALG_MUL_COMPONENT; GEOMALG_BETA] THEN
  REAL_ARITH_TAC);;

let REVERSION_CONV = SIMP_CONV[REVERSIONGA_LINEAR; REVERSION_MVBASIS; CARD_CLAUSES; IN_INSERT; FINITE_EMPTY; FINITE_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV
 THENC REAL_RAT_REDUCE_CONV;;

REVERSION_CONV `reversion (mbasis{1} + mbasis{1,2})`;;

let REVERSION_VECTOR = prove
(`!x:real^(P, Q, R)trip_fin_sum. multivec x = reversion (multivec x)`,
  REWRITE_TAC[reversionga; multivect] THEN
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA; GSYM GEOMALG_MUL_COMPONENT] THEN
  REWRITE_TAC[GSYM VSUM_LMUL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GEOMALG_VSUM_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  COND_CASES_TAC THENL
   [FIRST_ASSUM SUBST1_TAC THEN
    SIMP_TAC[CARD_CLAUSES; IN_INSERT; FINITE_EMPTY; FINITE_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC (NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV); ALL_TAC] THEN
  REAL_ARITH_TAC);;

let REVERSION_VECTOR_OUTER = prove
(`!x y:real^(P, Q, R)trip_fin_sum.
  reversion( multivec x outer multivec y) = multivec y outer multivec x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[VECTOR_OUTERGA_SKEWSYM] THEN
  REWRITE_TAC[reversionga; multivect] THEN
  SIMP_TAC[FINITE_NUMSEG; BILINEAR_OUTERGA; BILINEAR_VSUM] THEN
  REWRITE_TAC[CROSS; OUTERGA_LMUL; OUTERGA_RMUL] THEN
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA; GSYM GEOMALG_MUL_COMPONENT] THEN
  REWRITE_TAC[VECTOR_NEG_MINUS1; GSYM VSUM_LMUL] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GEOMALG_VSUM_COMPONENT] THEN
  MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[OUTER_MVBASIS_SING] THEN
  COND_CASES_TAC THENL
   [COND_CASES_TAC THENL
    [ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
     COND_CASES_TAC THENL
      [ASM_SIMP_TAC[CARD_CLAUSES; IN_INSERT; FINITE_EMPTY; FINITE_INSERT; NOT_IN_EMPTY] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REAL_ARITH_TAC;
       REAL_ARITH_TAC];
     REWRITE_TAC[VECTOR_NEG_MINUS1; VECTOR_MUL_ASSOC] THEN
     ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
     COND_CASES_TAC THENL
      [ASM_SIMP_TAC[CARD_CLAUSES; IN_INSERT; FINITE_EMPTY; FINITE_INSERT; NOT_IN_EMPTY] THEN
       CONV_TAC NUM_REDUCE_CONV THEN
       REAL_ARITH_TAC;
       REAL_ARITH_TAC]];
     REWRITE_TAC[VECTOR_MUL_RZERO]]);;

let REVERSION_MBASIS = prove
(`!s. reversion (mbasis s):real^(P, Q, R)geomalg =
          --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2) % mbasis s`,
  GEN_TAC THEN REWRITE_TAC[reversionga] THEN
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

let EVEN_POW_EQ = prove
(`!m n.(EVEN(n) <=> EVEN(m))  ==>
      --(&1) pow n = --(&1) pow m`,
  REWRITE_TAC[GSYM EVEN_ADD; EVEN_EXISTS] THEN
  ONCE_REWRITE_TAC
   [SIMP_RULE
     [REAL_POW_NZ; REAL_ARITH `~(--(&1) = &0)`]
      (SPEC `--(&1) pow m` (REAL_FIELD `!z:real. ~(z = &0) ==> (x = y <=> x * z = y * z)`))] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[GSYM MULT_2] THEN ONCE_REWRITE_TAC[GSYM REAL_POW_POW] THEN
   REWRITE_TAC[REAL_ARITH `-- &1 pow 2  = &1`; REAL_POW_ONE]);;

let REVERSION_OUTERGA = prove
 (`!x y:real^(P, Q, R)geomalg.
  reversion( x outer y) = reversion y outer reversion x`,
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN MATCH_MP_TAC BILINEAR_EQ_MVBASIS THEN
  REWRITE_TAC[bilinear; linear; OUTERGA_RADD; OUTERGA_LADD; OUTERGA_LMUL; OUTERGA_RMUL; REVERSIONGA_LINEAR; REVERSION_MBASIS] THEN
  REWRITE_TAC[reversionga; OUTER_MVBASIS] THEN
  SIMP_TAC[GEOMALG_EQ; GEOMALG_BETA; GSYM GEOMALG_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[INTER_COMM; VECTOR_MUL_ASSOC; VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[UNION_COMM; REAL_MUL_RZERO; REAL_MUL_RID; GSYM REAL_POW_ADD] THEN
  MATCH_MP_TAC EVEN_POW_EQ THEN REWRITE_TAC[GSYM EVEN_ADD; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[EVEN_ADD] THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[GSYM (REWRITE_RULE[ARITH] (SPECL [`m:num`; `n:num`; `2`] EQ_MULT_RCANCEL))] THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  SUBGOAL_THEN `!m. EVEN m==> (m DIV 2) * 2 = m` ASSUME_TAC THENL
   [REWRITE_TAC[EVEN_MOD] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM ADD_0] THEN
    FIRST_ASSUM (SUBST1_TAC o SYM) THEN
    MESON_TAC[DIVISION; ARITH_RULE `~(2 = 0)`]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. EVEN (n * (n - 1))` ASSUME_TAC THENL
   [MESON_TAC[EVEN_MULT; EVEN_SUB; LE_LT; EVEN; ONE]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL[`s:num->bool`; `t:num->bool`] CARD_UNION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; LEFT_SUB_DISTRIB; RIGHT_SUB_DISTRIB] THEN
  MATCH_MP_TAC
   (ARITH_RULE
     `c <= a /\ f <= e /\ (b:num) + d = g + h ==>
       (a + b) - c + (d + e) - f =
        g + a - c + e - f + h`) THEN
  REWRITE_TAC[MULT_CLAUSES; LE_SQUARE_REFL] THEN
  REWRITE_TAC[MULT_AC; GSYM MULT_2; GSYM RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MP_TAC (ISPECL [`s:num->bool`; `t:num->bool`] CARD_PRODUCT) THEN
  ANTS_TAC THENL[ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET]; ALL_TAC] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  CONV_TAC SYM_CONV THEN
  SUBGOAL_THEN
    `CARD {i,j| i IN (t:num->bool) /\ j IN (s:num->bool) /\ i > j} =
     CARD {i,j | i IN s /\ j IN t /\ i < j}` SUBST1_TAC THENL
   [REWRITE_TAC[prove(`!s t:num->bool.
                        {x,y | x IN t /\ y IN s /\ x > y} =
                        IMAGE swappair {x,y | x IN s /\ y IN t /\  x < y}`,
                REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM;
                EXISTS_PAIR_THM; IN_ELIM_PAIR_THM; swappair] THEN
                MESON_TAC[PAIR_EQ; GT])] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    CONJ_TAC THENL
     [REWRITE_TAC[swappair; FORALL_PAIR_THM] THEN
      MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{i,j | i IN (s:num->bool) /\ j IN (t:num->bool)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT THEN
      ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET]; ALL_TAC] THEN
    SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT THEN
    ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; NOT_IN_EMPTY; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  ASM SET_TAC[GT; LT_ANTISYM; LT_CASES]);;

let REVERSION_SEQITERATE_OUTERGA = prove
(`!a:num->real^(P, Q, R)trip_fin_sum k.
     reversion(seqiterate (outer) (1..k) (multivec o a)) =
     seqiterate (outer) (1..k) (multivec o a o (\i. SUC k -i))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[REWRITE_RULE[ARITH_RULE `0 < 1`](GSYM (SPECL [`1:num`; `0:num`]NUMSEG_EMPTY))] THEN
    REWRITE_TAC[SEQITERATE_CLAUSES; o_THM; NEUTRAL_OUTERGA] THEN
    CONV_TAC REVERSION_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID]; ALL_TAC] THEN
  GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[ADD1] THEN
  SIMP_TAC[ARITH_RULE `1 <= SUC k`; SEQITERATE_OUTERGA_RREC] THEN
  SIMP_TAC[ARITH_RULE `1 <= k + 1`; SEQITERATE_OUTERGA_LREC] THEN
  SIMP_TAC[REVERSION_OUTERGA; o_THM; GSYM REVERSION_VECTOR] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[ADD_SUB] THEN
  AP_TERM_TAC THEN REWRITE_TAC[NUMSEG_OFFSET_IMAGE; SEQITERATE_NUMSEG_IMAGE] THEN
  REWRITE_TAC[GSYM o_ASSOC] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[o_DEF; FUN_EQ_THM] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conjugation operation.                                                    *)
(* ------------------------------------------------------------------------- *)

let conjugation = new_definition
 `(conjugation:real^(P,Q,R)geomalg->real^(P,Q,R)geomalg) x =
    lambdas s. --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2 +
                        CARD(s INTER (pdimindex(:P)+1..pdimindex(:P)+pdimindex(:Q)))) * x$$s`;;

let CONJUGATION_MVBASIS = prove
 (`!s. conjugation (mbasis s:real^(P,Q,R)geomalg) =  --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2 +
                        CARD(s INTER (pdimindex(:P)+1..pdimindex(:P)+pdimindex(:Q)))) % mbasis s`,
  REWRITE_TAC[conjugation] THEN SIMP_TAC[GEOMALG_BETA; GEOMALG_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GEOMALG_MUL_COMPONENT; MVBASIS_COMPONENT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO]);;

let CONJUGATION_LINEAR = prove
 (`(!x y. conjugation (x + y) = conjugation x + conjugation y) /\
  (!c x. conjugation (c % x) = c % (conjugation x))`,
  REWRITE_TAC[conjugation] THEN SIMP_TAC[GEOMALG_BETA; GEOMALG_EQ] THEN
  SIMP_TAC[GEOMALG_ADD_COMPONENT; GEOMALG_MUL_COMPONENT; GEOMALG_BETA] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Blades.                                                                   *)
(* ------------------------------------------------------------------------- *)
parse_as_infix("blade",(8,"left"));;

let blade = new_definition
 `k blade (A:real^(P,Q,R)geomalg) <=>
         (?a. independent {a i | i IN 1..k} /\ {a i | i IN 1..k} HAS_SIZE k /\
                      A = seqiterate (outer) (1..k) (multivec o a))`;;

let is_blade = new_definition
  `is_blade (A:real^(P,Q,R)geomalg) <=> ?k. k blade A`;;

let pseudoscalar = new_definition
  `pseudoscalar:real^(P,Q,R)geomalg = mbasis (1..pdimindex(:P)+pdimindex(:Q)+pdimindex(:R))`;;

(* ------------------------------------------------------------------------- *)
(* Versors.                                                                  *)
(* ------------------------------------------------------------------------- *)

let is_versor = new_definition
  `is_versor (A:real^(P,Q,R)geomalg) <=>
      ?k a:num->real^(P, Q, R)trip_fin_sum.
         (!i. i IN 1..k ==> ~(is_null(multivec (a i)))) /\
         (A = seqiterate( * ) (1..k) (multivec o a))`;;

let MVINVERTIBLE_VERSOR = prove
 (`!x:real^(P,Q,R)geomalg. is_versor x ==> mvinvertible x`,
  REWRITE_TAC[is_versor] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  FIRST_X_ASSUM MP_TAC THEN SPEC_TAC (`k:num`,`k:num`) THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[REWRITE_RULE[ARITH_RULE `0 < 1`](GSYM (SPECL [`1:num`; `0:num`]NUMSEG_EMPTY)); NOT_IN_EMPTY] THEN
    REWRITE_TAC[SEQITERATE_CLAUSES; o_THM; NEUTRAL_GEOMGA; MVINVERTIBLE_LEFT_INVERSE] THEN MESON_TAC[GEOM_MVBASIS_RID]; ALL_TAC] THEN
   DISCH_TAC THEN
   SIMP_TAC[ARITH_RULE `1 <= SUC k:num`; SEQITERATE_GEOMGA_RREC] THEN
   REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MVINVERTIBLE_GEOM THEN
   CONJ_TAC THENL
    [FIRST_ASSUM MATCH_MP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN POP_ASSUM MP_TAC THEN
     REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
     REWRITE_TAC[GSYM MVINVERTIBLE_VECTOR_EQ] THEN
   FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Geometric relations.                                                      *)
(* ------------------------------------------------------------------------- *)

let dual = new_definition
 `(dual:real^(P,Q,'0)geomalg->real^(P,Q,'0)geomalg) x =
     vsum {s | s SUBSET 1..pdimindex(:P) + pdimindex(:Q)}
      (\s.x$$s % mbasis s inner (mvinverse pseudoscalar))`;;

let meet = new_definition
 `meet A B = (dual A) inner B`;;

let project = new_definition
 `project B A = (A inner B) * (mvinverse B)`;;

let reject = new_definition
 `reject B A = (A outer B) * (mvinverse B)`;;

let transform = new_definition
 `transform v x = v * x * mvinverse v`;;

let SUPERPOSE_TRANSFORM = prove
(`!x a b. is_versor a /\ is_versor b ==>
   a *(b * x * mvinverse b) * mvinverse a =
   (a * b) * x * mvinverse (a *b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM GEOMGA_ASSOC] THEN
  ONCE_REWRITE_TAC[GEOMGA_ASSOC] THEN
  ONCE_REWRITE_TAC[GEOMGA_ASSOC] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC MVINVERSE_GEOM THEN
  ASM_SIMP_TAC[MVINVERTIBLE_VERSOR]);;

(* ------------------------------------------------------------------------- *)
(* Cross_product.                                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cross_product",(20,"right"));;
let cross_product = new_definition
 `(u:real^('3,'0,'0)trip_fin_sum) cross_product v = dual ((multivec u) outer (multivec v))`;;
