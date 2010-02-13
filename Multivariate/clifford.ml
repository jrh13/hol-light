(* ========================================================================= *)
(* Geometric algebra.                                                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Multivariate/vectors.ml";;
needs "Library/binary.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Some basic lemmas, mostly set theory.                                     *)
(* ------------------------------------------------------------------------- *)

let CARD_UNION_LEMMA = prove
 (`FINITE s /\ FINITE t /\ FINITE u /\ FINITE v /\
   s INTER t = {} /\ u INTER v = {} /\ s UNION t = u UNION v
   ==> CARD(s) + CARD(t) = CARD(u) + CARD(v)`,
  MESON_TAC[CARD_UNION]);;

let CARD_DIFF_INTER = prove
 (`!s t. FINITE s ==> CARD s = CARD(s DIFF t) + CARD(s INTER t)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let CARD_ADD_SYMDIFF_INTER = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t
        ==> CARD s + CARD t =
            CARD((s DIFF t) UNION (t DIFF s)) + 2 * CARD(s INTER t)`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SPEC `t:A->bool`(MATCH_MP CARD_DIFF_INTER
   (ASSUME `FINITE(s:A->bool)`))) THEN
  SUBST1_TAC(SPEC `s:A->bool`(MATCH_MP CARD_DIFF_INTER
   (ASSUME `FINITE(t:A->bool)`))) THEN
  REWRITE_TAC[INTER_ACI] THEN
  MATCH_MP_TAC(ARITH_RULE `c = a + b ==> (a + x) + (b + x) = c + 2 * x`) THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

let SYMDIFF_PARITY_LEMMA = prove
 (`!s t u. FINITE s /\ FINITE t /\ (s DIFF t) UNION (t DIFF s) = u
           ==> EVEN(CARD u) = (EVEN(CARD s) <=> EVEN(CARD t))`,
  ONCE_REWRITE_TAC[GSYM EVEN_ADD] THEN
  SIMP_TAC[CARD_ADD_SYMDIFF_INTER] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH]);;

let FINITE_CART_SUBSET_LEMMA = prove
 (`!P m n. FINITE {i,j | i IN 1..m /\ j IN 1..n /\ P i j}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{i,j | i IN 1..m /\ j IN 1..n}` THEN
  SIMP_TAC[SUBSET; FINITE_PRODUCT; FINITE_NUMSEG] THEN
  SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Index type for "multivectors" (k-vectors for all k <= N).                 *)
(* ------------------------------------------------------------------------- *)

let multivector_tybij =
  let th = prove
   (`?s. s SUBSET (1..dimindex(:N))`,
    MESON_TAC[EMPTY_SUBSET]) in
  new_type_definition "multivector" ("mk_multivector","dest_multivector") th;;

let MULTIVECTOR_IMAGE = prove
 (`(:(N)multivector) = IMAGE mk_multivector {s | s SUBSET 1..dimindex(:N)}`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[multivector_tybij]);;

let HAS_SIZE_MULTIVECTOR = prove
 (`(:(N)multivector) HAS_SIZE (2 EXP dimindex(:N))`,
  REWRITE_TAC[MULTIVECTOR_IMAGE] THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  SIMP_TAC[HAS_SIZE_POWERSET; HAS_SIZE_NUMSEG_1; IN_ELIM_THM] THEN
  MESON_TAC[multivector_tybij]);;

let FINITE_MULTIVECTOR = prove
 (`FINITE(:(N)multivector)`,
  MESON_TAC[HAS_SIZE; HAS_SIZE_MULTIVECTOR]);;

let DIMINDEX_MULTIVECTOR = prove
 (`dimindex(:(N)multivector) = 2 EXP dimindex(:N)`,
  MESON_TAC[DIMINDEX_UNIQUE; HAS_SIZE_MULTIVECTOR]);;

let DEST_MK_MULTIVECTOR = prove
 (`!s. s SUBSET 1..dimindex(:N)
         ==> dest_multivector(mk_multivector s :(N)multivector) = s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM multivector_tybij] THEN
  ASM_REWRITE_TAC[]);;

let FORALL_MULTIVECTOR = prove
 (`(!s. s SUBSET 1..dimindex(:N) ==> P(mk_multivector s)) <=>
   (!m:(N)multivector. P m)`,
  EQ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN DISCH_TAC THEN GEN_TAC THEN
  MP_TAC(ISPEC `m:(N)multivector`
   (REWRITE_RULE[EXTENSION] MULTIVECTOR_IMAGE)) THEN
  REWRITE_TAC[IN_UNIV; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The bijections we use for indexing.                                       *)
(*                                                                           *)
(* Note that we need a *single* bijection over the entire space that also    *)
(* works for the various subsets. Hence the tedious explicit construction.   *)
(* ------------------------------------------------------------------------- *)

let setcode = new_definition
 `setcode s = 1 + binarysum (IMAGE PRE s)`;;

let codeset = new_definition
 `codeset n = IMAGE SUC (bitset(n - 1))`;;

let CODESET_SETCODE_BIJECTIONS = prove
 (`(!i. i IN 1..(2 EXP n)
        ==> codeset i SUBSET 1..n /\ setcode(codeset i) = i) /\
   (!s. s SUBSET (1..n)
        ==> (setcode s) IN 1..(2 EXP n) /\ codeset(setcode s) = s)`,
  REWRITE_TAC[codeset; setcode; ADD_SUB2; GSYM IMAGE_o; o_DEF; PRE] THEN
  REWRITE_TAC[SET_RULE `IMAGE (\x. x) s = s`] THEN CONJ_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `1 <= i ==> (1 + b = i <=> b = i - 1)`] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n /\ SUC n <= k <=> n < k`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (ARITH_RULE `1 <= i /\ i <= t ==> i - 1 < t`)) THEN
    MESON_TAC[BITSET_BOUND; BINARYSUM_BITSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `PRE` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[IN_NUMSEG; SUBSET] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < n ==> 1 <= 1 + x /\ 1 + x <= n`) THEN
    MATCH_MP_TAC BINARYSUM_BOUND THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE SUC (IMAGE PRE s)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET; FINITE_NUMSEG; BITSET_BINARYSUM];
    ALL_TAC] THEN
  UNDISCH_TAC `s SUBSET 1..n` THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `1 <= n ==> SUC(PRE n) = n`]);;

let FORALL_SETCODE = prove
 (`(!s. s SUBSET (1..n) ==> P(setcode s)) <=> (!i. i IN 1..(2 EXP n) ==> P i)`,
  MESON_TAC[CODESET_SETCODE_BIJECTIONS; SUBSET]);;

let SETCODE_BOUNDS = prove
 (`!s n. s SUBSET 1..n ==> setcode s IN (1..(2 EXP n))`,
  MESON_TAC[CODESET_SETCODE_BIJECTIONS]);;

(* ------------------------------------------------------------------------- *)
(* Indexing directly via subsets.                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("$$",(25,"left"));;

let sindex = new_definition
  `(x:real^(N)multivector)$$s = x$(setcode s)`;;

parse_as_binder "lambdas";;

let lambdas = new_definition
 `(lambdas) (g:(num->bool)->real) =
    (lambda i. g(codeset i)):real^(N)multivector`;;

(* ------------------------------------------------------------------------- *)
(* Crucial properties.                                                       *)
(* ------------------------------------------------------------------------- *)

let MULTIVECTOR_EQ = prove
 (`!x y:real^(N)multivector.
        x = y <=> !s. s SUBSET 1..dimindex(:N) ==> x$$s = y$$s`,
  SIMP_TAC[CART_EQ; sindex; FORALL_SETCODE; GSYM IN_NUMSEG;
           DIMINDEX_MULTIVECTOR]);;

let MULTIVECTOR_BETA = prove
 (`!s. s SUBSET 1..dimindex(:N)
         ==> ((lambdas) g :real^(N)multivector)$$s = g s`,
  SIMP_TAC[sindex; lambdas; LAMBDA_BETA; SETCODE_BOUNDS;
           DIMINDEX_MULTIVECTOR; GSYM IN_NUMSEG] THEN
  MESON_TAC[CODESET_SETCODE_BIJECTIONS]);;

let MULTIVECTOR_UNIQUE = prove
 (`!m:real^(N)multivector g.
        (!s. s SUBSET 1..dimindex(:N) ==> m$$s = g s)
        ==> (lambdas) g = m`,
  SIMP_TAC[MULTIVECTOR_EQ; MULTIVECTOR_BETA] THEN MESON_TAC[]);;

let MULTIVECTOR_ETA = prove
 (`(lambdas s. m$$s) = m`,
  SIMP_TAC[MULTIVECTOR_EQ; MULTIVECTOR_BETA]);;

(* ------------------------------------------------------------------------- *)
(* Also componentwise operations; they all work in this style.               *)
(* ------------------------------------------------------------------------- *)

let MULTIVECTOR_ADD_COMPONENT = prove
 (`!x y:real^(N)multivector s.
      s SUBSET (1..dimindex(:N)) ==> (x + y)$$s = x$$s + y$$s`,
  SIMP_TAC[sindex; SETCODE_BOUNDS; DIMINDEX_MULTIVECTOR;
           GSYM IN_NUMSEG; VECTOR_ADD_COMPONENT]);;

let MULTIVECTOR_MUL_COMPONENT = prove
 (`!c x:real^(N)multivector s.
      s SUBSET (1..dimindex(:N)) ==> (c % x)$$s = c * x$$s`,
  SIMP_TAC[sindex; SETCODE_BOUNDS; DIMINDEX_MULTIVECTOR;
           GSYM IN_NUMSEG; VECTOR_MUL_COMPONENT]);;

let MULTIVECTOR_VEC_COMPONENT = prove
 (`!k s. s SUBSET (1..dimindex(:N)) ==> (vec k :real^(N)multivector)$$s = &k`,
  SIMP_TAC[sindex; SETCODE_BOUNDS; DIMINDEX_MULTIVECTOR;
           GSYM IN_NUMSEG; VEC_COMPONENT]);;

let MULTIVECTOR_VSUM_COMPONENT = prove
 (`!f:A->real^(N)multivector t s.
        s SUBSET (1..dimindex(:N))
        ==> (vsum t f)$$s = sum t (\x. (f x)$$s)`,
  SIMP_TAC[vsum; sindex; LAMBDA_BETA; SETCODE_BOUNDS; GSYM IN_NUMSEG;
           DIMINDEX_MULTIVECTOR]);;

let MULTIVECTOR_VSUM = prove
 (`!t f. vsum t f = lambdas s. sum t (\x. (f x)$$s)`,
  SIMP_TAC[MULTIVECTOR_EQ; MULTIVECTOR_BETA; MULTIVECTOR_VSUM_COMPONENT]);;

(* ------------------------------------------------------------------------- *)
(* Basis vectors indexed by subsets of 1..N.                                 *)
(* ------------------------------------------------------------------------- *)

let mbasis = new_definition
 `mbasis i = lambdas s. if i = s then &1 else &0`;;

let MBASIS_COMPONENT = prove
 (`!s t. s SUBSET (1..dimindex(:N))
         ==> (mbasis t :real^(N)multivector)$$s = if s = t then &1 else &0`,
  SIMP_TAC[mbasis; IN_ELIM_THM; MULTIVECTOR_BETA] THEN MESON_TAC[]);;

let MBASIS_EQ_0 = prove
 (`!s. (mbasis s :real^(N)multivector = vec 0) <=>
       ~(s SUBSET 1..dimindex(:N))`,
  SIMP_TAC[MULTIVECTOR_EQ; MBASIS_COMPONENT; MULTIVECTOR_VEC_COMPONENT] THEN
  MESON_TAC[REAL_ARITH `~(&1 = &0)`]);;

let MBASIS_NONZERO = prove
 (`!s. s SUBSET 1..dimindex(:N) ==> ~(mbasis s :real^(N)multivector = vec 0)`,
  REWRITE_TAC[MBASIS_EQ_0]);;

let MBASIS_EXPANSION = prove
 (`!x:real^(N)multivector.
        vsum {s | s SUBSET 1..dimindex(:N)} (\s. x$$s % mbasis s) = x`,
  SIMP_TAC[MULTIVECTOR_EQ; MULTIVECTOR_VSUM_COMPONENT;
           MULTIVECTOR_MUL_COMPONENT; MBASIS_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `x * (if p then &1 else &0) = if p then x else &0`;
               SUM_DELTA; IN_ELIM_THM]);;

let SPAN_MBASIS = prove
 (`span {mbasis s :real^(N)multivector | s SUBSET 1..dimindex(:N)} = UNIV`,
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `x:real^(N)multivector` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MBASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Linear and bilinear functions are determined by their effect on basis.    *)
(* ------------------------------------------------------------------------- *)

let LINEAR_EQ_MBASIS = prove
 (`!f:real^(M)multivector->real^N g b s.
        linear f /\ linear g /\
        (!s. s SUBSET 1..dimindex(:M) ==> f(mbasis s) = g(mbasis s))
        ==> f = g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN UNIV ==> (f:real^(M)multivector->real^N) x = g x`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC LINEAR_EQ THEN
  EXISTS_TAC `{mbasis s :real^(M)multivector | s SUBSET 1..dimindex(:M)}` THEN
  ASM_REWRITE_TAC[SPAN_MBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

let BILINEAR_EQ_MBASIS = prove
 (`!f:real^(M)multivector->real^(N)multivector->real^P g b s.
        bilinear f /\ bilinear g /\
        (!s t.  s SUBSET 1..dimindex(:M) /\ t SUBSET 1..dimindex(:N)
                ==> f (mbasis s) (mbasis t) = g (mbasis s) (mbasis t))
        ==> f = g`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!x y. x IN UNIV /\ y IN UNIV
          ==> (f:real^(M)multivector->real^(N)multivector->real^P) x y = g x y`
   (fun th -> MP_TAC th THEN REWRITE_TAC[FUN_EQ_THM; IN_UNIV]) THEN
  MATCH_MP_TAC BILINEAR_EQ THEN
  EXISTS_TAC `{mbasis s :real^(M)multivector | s SUBSET 1..dimindex(:M)}` THEN
  EXISTS_TAC `{mbasis t :real^(N)multivector | t SUBSET 1..dimindex(:N)}` THEN
  ASM_REWRITE_TAC[SPAN_MBASIS; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A way of proving linear properties by extension from basis.               *)
(* ------------------------------------------------------------------------- *)

let LINEAR_PROPERTY = prove
 (`!P. P(vec 0) /\ (!x y. P x /\ P y ==> P(x + y))
       ==> !f s. FINITE s /\ (!i. i IN s ==> P(f i)) ==> P(vsum s f)`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; IN_INSERT]);;

let MBASIS_EXTENSION = prove
 (`!P. (!s. s SUBSET 1..dimindex(:N) ==> P(mbasis s)) /\
       (!c x. P x ==> P(c % x)) /\ (!x y. P x /\ P y ==> P(x + y))
       ==> !x:real^(N)multivector. P x`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM MBASIS_EXPANSION] THEN
  MATCH_MP_TAC(SIMP_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP] LINEAR_PROPERTY) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG; IN_ELIM_THM] THEN
  ASM_MESON_TAC[EMPTY_SUBSET; VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Injection from regular vectors.                                           *)
(* ------------------------------------------------------------------------- *)

let multivec = new_definition
 `(multivec:real^N->real^(N)multivector) x =
      vsum(1..dimindex(:N)) (\i. x$i % mbasis{i})`;;

(* ------------------------------------------------------------------------- *)
(* Subspace of k-vectors.                                                    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("multivector",(12,"right"));;

let multivector = new_definition
 `k multivector (p:real^(N)multivector) <=>
        !s. s SUBSET (1..dimindex(:N)) /\ ~(p$$s = &0) ==> s HAS_SIZE k`;;

(* ------------------------------------------------------------------------- *)
(* k-grade part of a multivector.                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("grade",(22,"right"));;

let grade = new_definition
 `k grade (p:real^(N)multivector) =
     (lambdas s. if s HAS_SIZE k then p$$s else &0):real^(N)multivector`;;

let MULTIVECTOR_GRADE = prove
 (`!k x. k multivector (k grade x)`,
  SIMP_TAC[multivector; grade; MULTIVECTOR_BETA; IMP_CONJ] THEN
  MESON_TAC[]);;

let GRADE_ADD = prove
 (`!x y k. k grade (x + y) = (k grade x) + (k grade y)`,
  SIMP_TAC[grade; MULTIVECTOR_EQ; MULTIVECTOR_ADD_COMPONENT;
           MULTIVECTOR_BETA; COND_COMPONENT] THEN
  REAL_ARITH_TAC);;

let GRADE_CMUL = prove
 (`!c x k. k grade (c % x) = c % (k grade x)`,
  SIMP_TAC[grade; MULTIVECTOR_EQ; MULTIVECTOR_MUL_COMPONENT;
           MULTIVECTOR_BETA; COND_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* General product construct.                                                *)
(* ------------------------------------------------------------------------- *)

let Product_DEF = new_definition
 `(Product mult op
     :real^(N)multivector->real^(N)multivector->real^(N)multivector) x y =
        vsum {s | s SUBSET 1..dimindex(:N)}
         (\s. vsum {s | s SUBSET 1..dimindex(:N)}
                (\t. (x$$s * y$$t * mult s t) % mbasis (op s t)))`;;

(* ------------------------------------------------------------------------- *)
(* This is always bilinear.                                                  *)
(* ------------------------------------------------------------------------- *)

let BILINEAR_PRODUCT = prove
 (`!mult op. bilinear(Product mult op)`,
  REWRITE_TAC[bilinear; linear; Product_DEF] THEN
  SIMP_TAC[GSYM VSUM_LMUL; MULTIVECTOR_MUL_COMPONENT] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_AC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[Product_DEF] THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_POWERSET; FINITE_NUMSEG] THEN
  REPEAT(MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
         REPEAT STRIP_TAC) THEN
  ASM_SIMP_TAC[MULTIVECTOR_ADD_COMPONENT] THEN VECTOR_ARITH_TAC);;

let PRODUCT_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_PRODUCT;;
let PRODUCT_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_PRODUCT;;

(* ------------------------------------------------------------------------- *)
(* Under suitable conditions, it's also associative.                         *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_ASSOCIATIVE = prove
 (`!op mult. (!s t. s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N)
                    ==> (op s t) SUBSET 1..dimindex(:N)) /\
             (!s t u. op s (op t u) = op (op s t) u) /\
             (!s t u. mult t u * mult s (op t u) = mult s t * mult (op s t) u)
             ==> !x y z:real^(N)multivector.
                        Product mult op x (Product mult op y z) =
                        Product mult op (Product mult op x y) z`,
  let SUM_SWAP_POWERSET =
    SIMP_RULE[FINITE_POWERSET; FINITE_NUMSEG]
     (repeat(SPEC `{s | s SUBSET 1..dimindex(:N)}`)
        (ISPEC `f:(num->bool)->(num->bool)->real` SUM_SWAP)) in
  let SWAP_TAC cnv n =
    GEN_REWRITE_TAC (cnv o funpow n BINDER_CONV) [SUM_SWAP_POWERSET] THEN
    REWRITE_TAC[] in
  let SWAPS_TAC cnv ns x =
    MAP_EVERY (SWAP_TAC cnv) ns THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC x THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC in
  REWRITE_TAC[Product_DEF] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[MULTIVECTOR_EQ; MULTIVECTOR_VSUM_COMPONENT; MBASIS_COMPONENT;
           MULTIVECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  X_GEN_TAC `r:num->bool` THEN STRIP_TAC THEN
  SWAPS_TAC RAND_CONV [1;0] `s:num->bool` THEN
  SWAP_TAC LAND_CONV 0 THEN SWAPS_TAC RAND_CONV [1;0] `t:num->bool` THEN
  SWAP_TAC RAND_CONV 0 THEN SWAPS_TAC LAND_CONV [0] `u:num->bool` THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC;
    REAL_ARITH `(if p then a else &0) * b = if p then a * b else &0`;
    REAL_ARITH `a * (if p then b else &0) = if p then a * b else &0`] THEN
  SIMP_TAC[SUM_DELTA] THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Geometric product.                                                        *)
(* ------------------------------------------------------------------------- *)

overload_interface
 ("*",
  `geom_mul:real^(N)multivector->real^(N)multivector->real^(N)multivector`);;

let geom_mul = new_definition
 `(x:real^(N)multivector) * y =
        Product (\s t. --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                              j IN 1..dimindex(:N) /\
                                              i IN s /\ j IN t /\ i > j})
                (\s t. (s DIFF t) UNION (t DIFF s))
                x y`;;

let BILINEAR_GEOM = prove
 (`bilinear(geom_mul)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] geom_mul] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCT);;

let GEOM_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_GEOM;;
let GEOM_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_GEOM;;

let GEOM_ASSOC = prove
 (`!x y z:real^(N)multivector. x * (y * z) = (x * y) * z`,
  REWRITE_TAC[geom_mul] THEN MATCH_MP_TAC PRODUCT_ASSOCIATIVE THEN
  REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_POW_ADD] THEN
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
    AP_TERM_TAC THEN CONV_TAC SYM_CONV] THEN
  MATCH_MP_TAC SYMDIFF_PARITY_LEMMA THEN
  REWRITE_TAC[FINITE_CART_SUBSET_LEMMA] THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM;
              IN_UNION; IN_DIFF] THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Outer product.                                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("outer",(20,"right"));;

let outer = new_definition
 `!x y:real^(N)multivector.
    x outer y =
        Product (\s t. if ~(s INTER t = {}) then &0
                       else --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                                   j IN 1..dimindex(:N) /\
                                                   i IN s /\ j IN t /\ i > j})
                (\s t. (s DIFF t) UNION (t DIFF s))
                x y`;;

let OUTER = prove
 (`!x y:real^(N)multivector.
    x outer y =
        Product (\s t. if ~(s INTER t = {}) then &0
                       else --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                                   j IN 1..dimindex(:N) /\
                                                   i IN s /\ j IN t /\ i > j})
                (UNION)
                x y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[outer; Product_DEF] THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  ASM_CASES_TAC `s INTER t :num->bool = {}` THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[SET_RULE
   `(s INTER t = {}) ==> (s DIFF t) UNION (t DIFF s) = s UNION t`]);;

let BILINEAR_OUTER = prove
 (`bilinear(outer)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] outer] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCT);;

let OUTER_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_OUTER;;
let OUTER_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_OUTER;;

let OUTER_ASSOC = prove
 (`!x y z:real^(N)multivector. x outer (y outer z) = (x outer y) outer z`,
  REWRITE_TAC[OUTER] THEN MATCH_MP_TAC PRODUCT_ASSOCIATIVE THEN
  SIMP_TAC[UNION_SUBSET; UNION_ASSOC;
     SET_RULE `s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`;
     SET_RULE `(t UNION u) INTER s = (t INTER s) UNION (u INTER s)`] THEN
  REWRITE_TAC[EMPTY_UNION] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`s INTER t :num->bool = {}`;
    `s INTER u :num->bool = {}`;
    `t INTER u :num->bool = {}`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CARD_UNION_LEMMA THEN REWRITE_TAC[FINITE_CART_SUBSET_LEMMA] THEN
  SIMP_TAC[EXTENSION; FORALL_PAIR_THM; NOT_IN_EMPTY; IN_UNION; IN_INTER] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN ASM SET_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Inner product.                                                            *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("inner",(20,"right"));;

let inner = new_definition
 `!x y:real^(N)multivector.
    x inner y =
        Product (\s t. if s = {} \/ t = {} \/
                          ~((s DIFF t) = {} /\ ~(t DIFF s = {}))
                       then &0
                       else --(&1) pow CARD {i,j | i IN 1..dimindex(:N) /\
                                                   j IN 1..dimindex(:N) /\
                                                   i IN s /\ j IN t /\ i > j})
                (\s t. (s DIFF t) UNION (t DIFF s))
                x y`;;

let BILINEAR_INNER = prove
 (`bilinear(inner)`,
  REWRITE_TAC[REWRITE_RULE[GSYM FUN_EQ_THM; ETA_AX] inner] THEN
  MATCH_ACCEPT_TAC BILINEAR_PRODUCT);;

let INNER_LADD = (MATCH_MP BILINEAR_LADD o SPEC_ALL) BILINEAR_INNER;;
let INNER_RADD = (MATCH_MP BILINEAR_RADD o SPEC_ALL) BILINEAR_INNER;;
let INNER_LMUL = (MATCH_MP BILINEAR_LMUL o SPEC_ALL) BILINEAR_INNER;;
let INNER_RMUL = (MATCH_MP BILINEAR_RMUL o SPEC_ALL) BILINEAR_INNER;;
let INNER_LNEG = (MATCH_MP BILINEAR_LNEG o SPEC_ALL) BILINEAR_INNER;;
let INNER_RNEG = (MATCH_MP BILINEAR_RNEG o SPEC_ALL) BILINEAR_INNER;;
let INNER_LZERO = (MATCH_MP BILINEAR_LZERO o SPEC_ALL) BILINEAR_INNER;;
let INNER_RZERO = (MATCH_MP BILINEAR_RZERO o SPEC_ALL) BILINEAR_INNER;;

(* ------------------------------------------------------------------------- *)
(* Actions of products on basis and singleton basis.                         *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_MBASIS = prove
 (`!s t. Product mult op (mbasis s) (mbasis t) :real^(N)multivector =
            if s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N)
            then mult s t % mbasis(op s t)
            else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[Product_DEF] THEN
  SIMP_TAC[MULTIVECTOR_MUL_COMPONENT; MBASIS_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then &1 else &0) * (if q then &1 else &0) * x =
    if q then if p then x else &0 else &0`] THEN
  REPEAT
   (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RAND] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [COND_RATOR] THEN
    SIMP_TAC[VECTOR_MUL_LZERO; COND_ID; VSUM_DELTA; IN_ELIM_THM; VSUM_0] THEN
    ASM_CASES_TAC `t SUBSET 1..dimindex(:N)` THEN ASM_REWRITE_TAC[]));;

let PRODUCT_MBASIS_SING = prove
 (`!i j. Product mult op (mbasis{i}) (mbasis{j}) :real^(N)multivector =
            if i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N)
            then mult {i} {j} % mbasis(op {i} {j})
            else vec 0`,
  REWRITE_TAC[PRODUCT_MBASIS; SET_RULE `{x} SUBSET s <=> x IN s`]);;

let GEOM_MBASIS = prove
 (`!s t. mbasis s * mbasis t :real^(N)multivector =
                if s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N)
                then --(&1) pow CARD {i,j | i IN s /\ j IN t /\ i > j} %
                     mbasis((s DIFF t) UNION (t DIFF s))
                else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geom_mul; PRODUCT_MBASIS] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[SUBSET]);;

let GEOM_MBASIS_SING = prove
 (`!i j. mbasis{i} * mbasis{j} :real^(N)multivector =
                if i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N)
                then if i = j then mbasis{}
                     else if i < j then mbasis{i,j}
                     else --(mbasis{i,j})
                else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[geom_mul; PRODUCT_MBASIS_SING] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
  SUBGOAL_THEN
   `{i',j' | i' IN 1 .. dimindex (:N) /\
             j' IN 1 .. dimindex (:N) /\
             i' = i /\
             j' = j /\
             i' > j'} =
    if i > j then {(i,j)} else {}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; PAIR_EQ] THEN
    ASM_MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[GT; LT_REFL] THENL
   [REWRITE_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID] THEN
    AP_TERM_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SET_RULE
   `~(i = j) ==> ({i} DIFF {j}) UNION ({j} DIFF {i}) = {i,j}`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> (j < i <=> ~(i < j))`)) THEN
  ASM_CASES_TAC `i:num < j` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID; FINITE_RULES;
               NOT_IN_EMPTY] THEN
  VECTOR_ARITH_TAC);;

let OUTER_MBASIS = prove
 (`!s t. (mbasis s) outer (mbasis t) :real^(N)multivector =
                if s SUBSET 1..dimindex(:N) /\ t SUBSET 1..dimindex(:N) /\
                   s INTER t = {}
                then --(&1) pow CARD {i,j | i IN s /\ j IN t /\ i > j} %
                     mbasis(s UNION t)
                else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OUTER; PRODUCT_MBASIS] THEN
  ASM_CASES_TAC `(s:num->bool) INTER t = {}` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_PAIR_THM; FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[SUBSET]);;

let OUTER_MBASIS_SING = prove
 (`!i j. mbasis{i} outer mbasis{j} :real^(N)multivector =
                if i IN 1..dimindex(:N) /\ j IN 1..dimindex(:N) /\ ~(i = j)
                then if i < j then mbasis{i,j} else --(mbasis{i,j})
                else vec 0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OUTER; PRODUCT_MBASIS_SING] THEN
  REWRITE_TAC[SET_RULE `{i} INTER {j} = {} <=> ~(i = j)`] THEN
  ASM_CASES_TAC `i:num = j` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; COND_ID] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING] THEN
  SUBGOAL_THEN
   `{i',j' | i' IN 1 .. dimindex (:N) /\
             j' IN 1 .. dimindex (:N) /\
             i' = i /\
             j' = j /\
             i' > j'} =
    if i > j then {(i,j)} else {}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_SING] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY; PAIR_EQ] THEN
    ASM_MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GT; SET_RULE `{i} UNION {j} = {i,j}`] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> (j < i <=> ~(i < j))`)) THEN
  ASM_CASES_TAC `i:num < j` THEN
  ASM_SIMP_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID; FINITE_RULES;
               NOT_IN_EMPTY] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences.                                                 *)
(* ------------------------------------------------------------------------- *)

let OUTER_MBASIS_SKEWSYM = prove
 (`!i j. mbasis{i} outer mbasis{j} = --(mbasis{j} outer mbasis{i})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OUTER_MBASIS_SING] THEN
  ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[VECTOR_NEG_0] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(i:num = j) ==> i < j /\ ~(j < i) \/ j < i /\ ~(i < j)`)) THEN
  ASM_REWRITE_TAC[CONJ_ACI] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG; VECTOR_NEG_0] THEN
  REPEAT AP_TERM_TAC THEN SET_TAC[]);;

let OUTER_MBASIS_REFL = prove
 (`!i. mbasis{i} outer mbasis{i} = vec 0`,
  GEN_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
   `!x:real^N. x = --x ==> x = vec 0`) THEN
  MATCH_ACCEPT_TAC OUTER_MBASIS_SKEWSYM);;

let OUTER_MBASIS_LSCALAR = prove
 (`!x. mbasis{} outer x = x`,
  MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC[OUTER_RMUL; OUTER_RADD] THEN
  SIMP_TAC[OUTER_MBASIS; EMPTY_SUBSET; INTER_EMPTY; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN {} /\ j IN s /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID]);;

let OUTER_MBASIS_RSCALAR = prove
 (`!x. x outer mbasis{} = x`,
  MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC[OUTER_LMUL; OUTER_LADD] THEN
  SIMP_TAC[OUTER_MBASIS; EMPTY_SUBSET; INTER_EMPTY; UNION_EMPTY] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN s /\ j IN {} /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; VECTOR_MUL_LID]);;

let MBASIS_SPLIT = prove
 (`!a s. (!x. x IN s ==> a < x)
         ==> mbasis (a INSERT s) = mbasis{a} outer mbasis s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OUTER_MBASIS] THEN
  SUBGOAL_THEN `{a:num} INTER s = {}` SUBST1_TAC THENL
   [ASM SET_TAC [LT_REFL]; ALL_TAC] THEN
  SIMP_TAC[SET_RULE`{a} SUBSET t /\ s SUBSET t <=> (a INSERT s) SUBSET t`] THEN
  COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[MBASIS_EQ_0]] THEN
  REWRITE_TAC[SET_RULE `{a} UNION s = a INSERT s`] THEN
  SUBGOAL_THEN `{(i:num),(j:num) | i IN {a} /\ j IN s /\ i > j} = {}`
   (fun th -> SIMP_TAC[th; CARD_CLAUSES; real_pow; VECTOR_MUL_LID]) THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_SING;
              NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[ARITH_RULE `~(n < m /\ n:num > m)`]);;

(* ------------------------------------------------------------------------- *)
(* Just for generality, normalize a set enumeration.                         *)
(* ------------------------------------------------------------------------- *)

let SETENUM_NORM_CONV =
  let conv =
    GEN_REWRITE_CONV I [EXTENSION] THENC
    GEN_REWRITE_CONV TOP_SWEEP_CONV [IN_SING; IN_INSERT] THENC
    BINDER_CONV(EQT_INTRO o DISJ_ACI_RULE) THENC
    GEN_REWRITE_CONV I [FORALL_SIMP] in
  fun tm ->
    let nums = dest_setenum tm in
    let nums' = map mk_numeral (sort (</) (map dest_numeral (setify nums))) in
    if nums' = nums then REFL tm else
    let eq = mk_eq(tm,mk_setenum(nums',fst(dest_fun_ty(type_of tm)))) in
    EQT_ELIM(conv eq);;

(* ------------------------------------------------------------------------- *)
(* Conversion to split extended basis combinations.                          *)
(*                                                                           *)
(* Also 1-step merge from left, which can be DEPTH_CONV'd. In this case the  *)
(* order must be correct.                                                    *)
(* ------------------------------------------------------------------------- *)

let MBASIS_SPLIT_CONV,MBASIS_MERGE_CONV =
  let setlemma = SET_RULE
   `((!x:num. x IN {} ==> a < x) <=> T) /\
    ((!x:num. x IN (y INSERT s) ==> a < x) <=>
              a < y /\ (!x. x IN s ==> a < x))` in
  let SET_CHECK_CONV =
    GEN_REWRITE_CONV TOP_SWEEP_CONV [setlemma] THENC NUM_REDUCE_CONV
  and INST_SPLIT = PART_MATCH (lhs o rand) MBASIS_SPLIT
  and INST_MERGE = PART_MATCH (lhs o rand) (GSYM MBASIS_SPLIT) in
  let rec conv tm =
    if length(dest_setenum(rand tm)) <= 1 then REFL tm else
    let th = MP_CONV SET_CHECK_CONV (INST_SPLIT tm) in
    let th' = RAND_CONV conv (rand(concl th)) in
    TRANS th th' in
  (fun tm ->
    try let op,se = dest_comb tm in
        if fst(dest_const op) = "mbasis" & forall is_numeral (dest_setenum se)
        then (RAND_CONV SETENUM_NORM_CONV THENC conv) tm
        else fail()
    with Failure _ -> failwith "MBASIS_SPLIT_CONV"),
  (fun tm -> try MP_CONV SET_CHECK_CONV (INST_MERGE tm)
             with Failure _ -> failwith "MBASIS_MERGE_CONV");;

(* ------------------------------------------------------------------------- *)
(* Convergent (if slow) rewrite set to bubble into position.                 *)
(* ------------------------------------------------------------------------- *)

let OUTER_ACI = prove
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
  REWRITE_TAC[OUTER_ASSOC; OUTER_LZERO; OUTER_RZERO; OUTER_LADD;
            OUTER_RADD; OUTER_LMUL; OUTER_RMUL; OUTER_LZERO; OUTER_RZERO] THEN
  REWRITE_TAC[OUTER_MBASIS_REFL; OUTER_LZERO] THEN
  REWRITE_TAC[OUTER_MBASIS_LSCALAR; OUTER_MBASIS_RSCALAR] THEN
  SIMP_TAC[GSYM VECTOR_NEG_MINUS1; VECTOR_ARITH `x - y:real^N = x + --y`] THEN
  MESON_TAC[OUTER_MBASIS_SKEWSYM; OUTER_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* Group the final "c1 % mbasis s1 + ... + cn % mbasis sn".                  *)
(* ------------------------------------------------------------------------- *)

let MBASIS_GROUP_CONV tm =
  let tms = striplist(dest_binary "vector_add") tm in
  if length tms = 1 then LAND_CONV REAL_POLY_CONV tm else
  let vadd_tm = rator(rator tm) in
  let mk_vadd = mk_binop vadd_tm in
  let mbs = map (snd o dest_binary "%") tms in
  let tmbs = zip mbs tms and mset = setify mbs in
  let grps = map (fun x -> map snd (filter (fun (x',_) -> x' = x) tmbs))
                 mset in
  let tm' = end_itlist mk_vadd (map (end_itlist mk_vadd) grps) in
  let th1 = AC VECTOR_ADD_AC (mk_eq(tm,tm'))
  and th2 =
   (GEN_REWRITE_CONV DEPTH_CONV [GSYM VECTOR_ADD_RDISTRIB] THENC
    DEPTH_BINOP_CONV vadd_tm (LAND_CONV REAL_POLY_CONV)) tm' in
  TRANS th1 th2;;

(* ------------------------------------------------------------------------- *)
(* Overall conversion.                                                       *)
(* ------------------------------------------------------------------------- *)

let OUTER_CANON_CONV =
  ONCE_DEPTH_CONV MBASIS_SPLIT_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV
   [VECTOR_SUB; VECTOR_NEG_MINUS1;
    OUTER_LADD; OUTER_RADD; OUTER_LMUL; OUTER_RMUL; OUTER_LZERO; OUTER_RZERO;
    VECTOR_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC;
    VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THENC
  REAL_RAT_REDUCE_CONV THENC
  PURE_SIMP_CONV[OUTER_ACI; ARITH_GT; ARITH_GE; OUTER_LMUL; OUTER_RMUL;
                 OUTER_LZERO; OUTER_RZERO] THENC
  PURE_REWRITE_CONV[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO;
                    VECTOR_ADD_LID; VECTOR_ADD_RID; VECTOR_MUL_ASSOC] THENC
  GEN_REWRITE_CONV I [GSYM VECTOR_MUL_LID] THENC
  PURE_REWRITE_CONV
   [VECTOR_ADD_LDISTRIB; VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC] THENC
  REAL_RAT_REDUCE_CONV THENC PURE_REWRITE_CONV[GSYM VECTOR_ADD_ASSOC] THENC
  DEPTH_CONV MBASIS_MERGE_CONV THENC
  MBASIS_GROUP_CONV THENC
  GEN_REWRITE_CONV DEPTH_CONV [GSYM VECTOR_ADD_RDISTRIB] THENC
  REAL_RAT_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Iterated operation in order.                                              *)
(* I guess this ought to be added to the core...                             *)
(* ------------------------------------------------------------------------- *)

let seqiterate_EXISTS = prove
 (`!op f. ?h.
        !s. h s = if INFINITE s \/ s = {} then neutral op else
                  let i = minimal x. x IN s in
                  if s = {i} then f(i) else op (f i) (h (s DELETE i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC(MATCH_MP WF_REC (ISPEC `CARD:(num->bool)->num` WF_MEASURE)) THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  LET_TAC THEN CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[MEASURE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `?i:num. i IN s` MP_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [MINIMAL] THEN
  ASM_SIMP_TAC[CARD_DELETE; CARD_EQ_0; ARITH_RULE `n - 1 < n <=> ~(n = 0)`]);;

let EXISTS_SWAP = prove
 (`!P. (?f. P f) <=> (?f:A->B->C. P (\b a. f a b))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_THEN CHOOSE_TAC THENL
   [EXISTS_TAC `\a b. (f:B->A->C) b a` THEN ASM_REWRITE_TAC[ETA_AX];
    ASM_MESON_TAC[]]);;

let seqiterate = new_specification ["seqiterate"]
 (REWRITE_RULE[SKOLEM_THM]
   (ONCE_REWRITE_RULE[EXISTS_SWAP]
    (ONCE_REWRITE_RULE[SKOLEM_THM] seqiterate_EXISTS)));;

let MINIMAL_IN_INSERT = prove
 (`!s i. (!j. j IN s ==> i < j) ==> (minimal j. j IN (i INSERT s)) = i`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[minimal] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[LT_ANTISYM]);;

let SEQITERATE_CLAUSES = prove
 (`(!op f. seqiterate op {} f = neutral op) /\
   (!op f i. seqiterate op {i} f = f(i)) /\
   (!op f i s. FINITE s /\ ~(s = {}) /\ (!j. j IN s ==> i < j)
               ==> seqiterate op (i INSERT s) f =
                   op (f i) (seqiterate op s f))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [seqiterate] THEN
  ASM_SIMP_TAC[NOT_INSERT_EMPTY; INFINITE; FINITE_INSERT; FINITE_RULES] THEN
  ASM_SIMP_TAC[MINIMAL_IN_INSERT; NOT_IN_EMPTY; LET_DEF; LET_END_DEF] THEN
  SUBGOAL_THEN `~((i:num) IN s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[DELETE_INSERT; SET_RULE
   `~(i IN s) /\ ~(s = {}) ==> (s DELETE i = s) /\ ~(i INSERT s = {i})`]);;

(* ------------------------------------------------------------------------- *)
(* In the "common" case this agrees with ordinary iteration.                 *)
(* ------------------------------------------------------------------------- *)

let SEQITERATE_ITERATE = prove
 (`!op f s. monoidal op /\ FINITE s ==> seqiterate op s f = iterate op s f`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_DELETE THEN
  ASM_SIMP_TAC[SEQITERATE_CLAUSES; ITERATE_CLAUSES] THEN
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `i IN s ==> s = i INSERT (s DELETE i)`)) THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
  ASM_CASES_TAC `s DELETE (i:num) = {}` THEN
  ASM_SIMP_TAC[SEQITERATE_CLAUSES; ITERATE_CLAUSES] THENL
   [ASM_MESON_TAC[monoidal]; FIRST_X_ASSUM(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(last(CONJUNCTS SEQITERATE_CLAUSES)) THEN
  ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
  ASM_MESON_TAC[LT_ANTISYM; LT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Outermorphism extension.                                                  *)
(* ------------------------------------------------------------------------- *)

let outermorphism = new_definition
 `outermorphism(f:real^N->real^P) (x:real^(N)multivector) =
        vsum {s | s SUBSET 1..dimindex(:N)}
             (\s. x$$s % seqiterate(outer) s (multivec o f o basis))`;;

let NEUTRAL_OUTER = prove
 (`neutral(outer) = mbasis{}`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[OUTER_MBASIS_LSCALAR; OUTER_MBASIS_RSCALAR]);;

let OUTERMORPHISM_MBASIS = prove
 (`!f:real^M->real^N s t.
        s SUBSET 1..dimindex(:M)
        ==> outermorphism f (mbasis s) =
            seqiterate(outer) s (multivec o f o basis)`,
  REWRITE_TAC[outermorphism] THEN SIMP_TAC[MBASIS_COMPONENT] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  SIMP_TAC[VECTOR_MUL_LZERO; VSUM_DELTA; IN_ELIM_THM; VECTOR_MUL_LID]);;

let OUTERMORPHISM_MBASIS_EMPTY = prove
 (`!f. outermorphism f (mbasis {}) = mbasis {}`,
  SIMP_TAC[OUTERMORPHISM_MBASIS; EMPTY_SUBSET; SEQITERATE_CLAUSES] THEN
  REWRITE_TAC[NEUTRAL_OUTER]);;

(* ------------------------------------------------------------------------- *)
(* Reversion operation.                                                      *)
(* ------------------------------------------------------------------------- *)

let reversion = new_definition
 `(reversion:real^(N)multivector->real^(N)multivector) x =
    lambdas s. --(&1) pow ((CARD(s) * (CARD(s) - 1)) DIV 2) * x$$s`;;
