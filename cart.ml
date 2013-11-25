(* ========================================================================= *)
(* Definition of finite Cartesian product types.                             *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "iterate.ml";;

(* ------------------------------------------------------------------------- *)
(* Association of a number with an indexing type.                            *)
(* ------------------------------------------------------------------------- *)

let dimindex = new_definition
  `dimindex(s:A->bool) = if FINITE(:A) then CARD(:A) else 1`;;

let DIMINDEX_NONZERO = prove
 (`!s:A->bool. ~(dimindex(s) = 0)`,
  GEN_TAC THEN REWRITE_TAC[dimindex] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[CARD_EQ_0; ARITH] THEN SET_TAC[]);;

let DIMINDEX_GE_1 = prove
 (`!s:A->bool. 1 <= dimindex(s)`,
  REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; DIMINDEX_NONZERO]);;

let DIMINDEX_UNIV = prove
 (`!s. dimindex(s:A->bool) = dimindex(:A)`,
  REWRITE_TAC[dimindex]);;

let DIMINDEX_UNIQUE = prove
 (`(:A) HAS_SIZE n ==> dimindex(:A) = n`,
  MESON_TAC[dimindex; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* An indexing type with that size, parametrized by base type.               *)
(* ------------------------------------------------------------------------- *)

let finite_image_tybij =
  new_type_definition "finite_image" ("finite_index","dest_finite_image")
  (prove
   (`?x. x IN 1..dimindex(:A)`,
    EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1]));;

let FINITE_IMAGE_IMAGE = prove
 (`UNIV:(A)finite_image->bool = IMAGE finite_index (1..dimindex(:A))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_image_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Dimension of such a type, and indexing over it.                           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_FINITE_IMAGE = prove
 (`!s. (UNIV:(A)finite_image->bool) HAS_SIZE dimindex(s:A->bool)`,
  GEN_TAC THEN SIMP_TAC[FINITE_IMAGE_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_image_tybij]);;

let CARD_FINITE_IMAGE = prove
 (`!s. CARD(UNIV:(A)finite_image->bool) = dimindex(s:A->bool)`,
  MESON_TAC[HAS_SIZE_FINITE_IMAGE; HAS_SIZE]);;

let FINITE_FINITE_IMAGE = prove
 (`FINITE(UNIV:(A)finite_image->bool)`,
  MESON_TAC[HAS_SIZE_FINITE_IMAGE; HAS_SIZE]);;

let DIMINDEX_FINITE_IMAGE = prove
 (`!s t. dimindex(s:(A)finite_image->bool) = dimindex(t:A->bool)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  MP_TAC(ISPEC `t:A->bool` HAS_SIZE_FINITE_IMAGE) THEN
  SIMP_TAC[FINITE_FINITE_IMAGE; HAS_SIZE]);;

let FINITE_INDEX_WORKS = prove
 (`!i:(A)finite_image.
        ?!n. 1 <= n /\ n <= dimindex(:A) /\ (finite_index n = i)`,
  REWRITE_TAC[CONJ_ASSOC; GSYM IN_NUMSEG] THEN MESON_TAC[finite_image_tybij]);;

let FINITE_INDEX_INJ = prove
 (`!i j. 1 <= i /\ i <= dimindex(:A) /\
         1 <= j /\ j <= dimindex(:A)
         ==> ((finite_index i :A finite_image = finite_index j) <=>
              (i = j))`,
  MESON_TAC[FINITE_INDEX_WORKS]);;

let FORALL_FINITE_INDEX = prove
 (`(!k:(N)finite_image. P k) =
   (!i. 1 <= i /\ i <= dimindex(:N) ==> P(finite_index i))`,
  MESON_TAC[FINITE_INDEX_WORKS]);;

(* ------------------------------------------------------------------------- *)
(* Hence finite Cartesian products, with indexing and lambdas.               *)
(* ------------------------------------------------------------------------- *)

let cart_tybij =
  new_type_definition "cart" ("mk_cart","dest_cart")
   (prove(`?f:(B)finite_image->A. T`,REWRITE_TAC[]));;

parse_as_infix("$",(25,"left"));;

let finite_index = new_definition
  `x$i = dest_cart x (finite_index i)`;;

let CART_EQ = prove
 (`!x:A^B y.
    (x = y) <=> !i. 1 <= i /\ i <= dimindex(:B) ==> (x$i = y$i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[finite_index; GSYM FORALL_FINITE_INDEX] THEN
  REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN MESON_TAC[cart_tybij]);;

parse_as_binder "lambda";;

let lambda = new_definition
  `(lambda) g =
     @f:A^B. !i. 1 <= i /\ i <= dimindex(:B) ==> (f$i = g i)`;;

let LAMBDA_BETA = prove
 (`!i. 1 <= i /\ i <= dimindex(:B)
       ==> (((lambda) g:A^B) $i = g i)`,
  REWRITE_TAC[lambda] THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `mk_cart(\k. g(@i. 1 <= i /\  i <= dimindex(:B) /\
                                (finite_index i = k))):A^B` THEN
  REWRITE_TAC[finite_index; REWRITE_RULE[] cart_tybij] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  GEN_TAC THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[FINITE_INDEX_INJ; DIMINDEX_FINITE_IMAGE]);;

let LAMBDA_UNIQUE = prove
 (`!f:A^B g.
        (!i. 1 <= i /\ i <= dimindex(:B) ==> (f$i = g i)) <=>
        ((lambda) g = f)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN MESON_TAC[]);;

let LAMBDA_ETA = prove
 (`!g. (lambda i. g$i) = g`,
  REWRITE_TAC[CART_EQ; LAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* For some purposes we can avoid side-conditions on the index.              *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDEX_INRANGE = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\ !x:A^N. x$i = x$k`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

let FINITE_INDEX_INRANGE_2 = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\
           (!x:A^N. x$i = x$k) /\ (!y:B^N. y$i = y$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

let CART_EQ_FULL = prove
 (`!x y:A^N. x = y <=> !i. x$i = y$i`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN SIMP_TAC[CART_EQ]);;

(* ------------------------------------------------------------------------- *)
(* We need a non-standard sum to "paste" together Cartesian products.        *)
(* ------------------------------------------------------------------------- *)

let finite_sum_tybij =
  let th = prove
   (`?x. x IN 1..(dimindex(:A) + dimindex(:B))`,
    EXISTS_TAC `1` THEN SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1;
      ARITH_RULE `1 <= a ==> 1 <= a + b`]) in
  new_type_definition "finite_sum" ("mk_finite_sum","dest_finite_sum") th;;

let pastecart = new_definition
  `(pastecart:A^M->A^N->A^(M,N)finite_sum) f g =
        lambda i. if i <= dimindex(:M) then f$i
                  else g$(i - dimindex(:M))`;;

let fstcart = new_definition
  `(fstcart:A^(M,N)finite_sum->A^M) f = lambda i. f$i`;;

let sndcart = new_definition
  `(sndcart:A^(M,N)finite_sum->A^N) f =
        lambda i. f$(i + dimindex(:M))`;;

let FINITE_SUM_IMAGE = prove
 (`UNIV:(A,B)finite_sum->bool =
       IMAGE mk_finite_sum (1..(dimindex(:A)+dimindex(:B)))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_sum_tybij]);;

let DIMINDEX_HAS_SIZE_FINITE_SUM = prove
 (`(UNIV:(M,N)finite_sum->bool) HAS_SIZE (dimindex(:M) + dimindex(:N))`,
  SIMP_TAC[FINITE_SUM_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_sum_tybij]);;

let DIMINDEX_FINITE_SUM = prove
 (`dimindex(:(M,N)finite_sum) = dimindex(:M) + dimindex(:N)`,
  GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_SUM]);;

let FSTCART_PASTECART = prove
 (`!x y. fstcart(pastecart (x:A^M) (y:A^N)) = x`,
  SIMP_TAC[pastecart; fstcart; CART_EQ; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
           ARITH_RULE `a <= b ==> a <= b + c`]);;

let SNDCART_PASTECART = prove
 (`!x y. sndcart(pastecart (x:A^M) (y:A^N)) = y`,
  SIMP_TAC[pastecart; sndcart; CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  W(fun (_,w) -> MP_TAC (PART_MATCH (lhs o rand) LAMBDA_BETA (lhand w))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM] THEN MATCH_MP_TAC
     (ARITH_RULE `1 <= i /\ i <= b ==> 1 <= i + a /\ i + a <= a + b`) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ADD_SUB; ARITH_RULE `1 <= i ==> ~(i + a <= a)`]]);;

let PASTECART_FST_SND = prove
 (`!z. pastecart (fstcart z) (sndcart z) = z`,
  SIMP_TAC[pastecart; fstcart; sndcart; CART_EQ; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[DIMINDEX_FINITE_SUM; LAMBDA_BETA;
     ARITH_RULE `i <= a + b ==> i - a <= b`;
     ARITH_RULE `~(i <= a) ==> 1 <= i - a`;
     ARITH_RULE `~(i <= a) ==> ((i - a) + a = i)`]);;

let PASTECART_EQ = prove
 (`!x y. (x = y) <=> (fstcart x = fstcart y) /\ (sndcart x = sndcart y)`,
  MESON_TAC[PASTECART_FST_SND]);;

let FORALL_PASTECART = prove
 (`(!p. P p) <=> !x y. P (pastecart x y)`,
  MESON_TAC[PASTECART_FST_SND; FSTCART_PASTECART; SNDCART_PASTECART]);;

let EXISTS_PASTECART = prove
 (`(?p. P p) <=> ?x y. P (pastecart x y)`,
  MESON_TAC[PASTECART_FST_SND; FSTCART_PASTECART; SNDCART_PASTECART]);;

let PASTECART_INJ = prove
 (`!x:real^M y:real^N w z. pastecart x y = pastecart w z <=> x = w /\ y = z`,
  REWRITE_TAC[PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART]);;

(* ------------------------------------------------------------------------- *)
(* Automatically define a type of size n.                                    *)
(* ------------------------------------------------------------------------- *)

let define_finite_type =
  let lemma_pre = prove
   (`~(n = 0) ==> ?x. x IN 1..n`,
    DISCH_TAC THEN EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC)
  and lemma_post = prove
   (`(!a:A. mk(dest a) = a) /\ (!r. r IN 1..n <=> dest(mk r) = r)
     ==> (:A) HAS_SIZE n`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(:A) = IMAGE mk (1..n)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV];
      MATCH_MP_TAC HAS_SIZE_IMAGE_INJ] THEN
    ASM_MESON_TAC[HAS_SIZE_NUMSEG_1]) in
  let POST_RULE = MATCH_MP lemma_post and n_tm = `n:num` in
  fun n ->
    let ns = string_of_int n in
    let ns' = "auto_define_finite_type_"^ns in
    let th0 = INST [mk_small_numeral n,n_tm] lemma_pre in
    let th1 = MP th0 (EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th0))))) in
    POST_RULE(new_type_definition ns ("mk_"^ns',"dest_"^ns') th1);;

(* ------------------------------------------------------------------------- *)
(* Predefine the cases 2, 3 and 4, which are especially useful for real^N.   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_1 = prove
 (`(:1) HAS_SIZE 1`,
  SUBGOAL_THEN `(:1) = {one}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING] THEN MESON_TAC[one];
    SIMP_TAC[NOT_IN_EMPTY; HAS_SIZE; FINITE_RULES; CARD_CLAUSES; ARITH]]);;

let HAS_SIZE_2 = define_finite_type 2;;

let HAS_SIZE_3 = define_finite_type 3;;

let HAS_SIZE_4 = define_finite_type 4;;

let DIMINDEX_1 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_1;;
let DIMINDEX_2 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_2;;
let DIMINDEX_3 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_3;;
let DIMINDEX_4 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_4;;

(* ------------------------------------------------------------------------- *)
(* Finiteness lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let FINITE_CART = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N) ==> FINITE {x | P i x})
       ==> FINITE {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)}`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N)
        ==> FINITE {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                 ==> P i (v$i)) /\
                            (!i. 1 <= i /\ i <= dimindex(:N) /\ n < i
                                 ==> v$i = @x. F)}`
   (MP_TAC o SPEC `dimindex(:N)`) THEN REWRITE_TAC[LE_REFL; LET_ANTISYM] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= n /\ i <= 0 <=> F`] THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n /\ 0 < i <=> 1 <= i /\ i <= n`] THEN
    SUBGOAL_THEN
     `{v | !i. 1 <= i /\ i <= dimindex (:N) ==> v$i = (@x. F)} =
      {(lambda i. @x. F):A^N}`
     (fun th -> SIMP_TAC[FINITE_RULES;th]) THEN
    SIMP_TAC[EXTENSION; IN_SING; IN_ELIM_THM; CART_EQ; LAMBDA_BETA];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE (\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)
          {x,v | x IN {x:A | P (SUC n) x} /\
                 v IN {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                ==> P i (v$i)) /\
                           (!i. 1 <= i /\ i <= dimindex (:N) /\ n < i
                                ==> v$i = (@x. F))}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    ASM_SIMP_TAC[FINITE_PRODUCT; ARITH_RULE `1 <= SUC n`;
                 ARITH_RULE `SUC n <= m ==> n <= m`];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_PAIR_THM; EXISTS_PAIR_THM] THEN
  X_GEN_TAC `v:A^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN EXISTS_TAC `(v:A^N)$(SUC n)` THEN
  EXISTS_TAC `(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N` THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; ARITH_RULE `i <= n ==> ~(i = SUC n)`] THEN
  ASM_MESON_TAC[LE; ARITH_RULE `1 <= SUC n`;
                ARITH_RULE `n < i /\ ~(i = SUC n) ==> SUC n < i`]);;

(* ------------------------------------------------------------------------- *)
(* More cardinality results for whole universe.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CART_UNIV = prove
 (`!m. (:A) HAS_SIZE m ==> (:A^N) HAS_SIZE m EXP (dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(:(N)finite_image->A) HAS_SIZE m EXP (dimindex(:N))`
  MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE_FUNSPACE_UNIV; HAS_SIZE_FINITE_IMAGE];
    DISCH_THEN(MP_TAC o ISPEC `mk_cart:((N)finite_image->A)->A^N` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] HAS_SIZE_IMAGE_INJ)) THEN
    REWRITE_TAC[IN_UNIV] THEN
    ANTS_TAC THENL [MESON_TAC[cart_tybij]; MATCH_MP_TAC EQ_IMP] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    REWRITE_TAC[IN_UNIV] THEN MESON_TAC[cart_tybij]]);;

let CARD_CART_UNIV = prove
 (`FINITE(:A) ==> CARD(:A^N) = CARD(:A) EXP dimindex(:N)`,
  MESON_TAC[HAS_SIZE_CART_UNIV; HAS_SIZE]);;

let FINITE_CART_UNIV = prove
 (`FINITE(:A) ==> FINITE(:A^N)`,
  MESON_TAC[HAS_SIZE_CART_UNIV; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Explicit construction of a vector from a list of components.              *)
(* ------------------------------------------------------------------------- *)

let vector = new_definition
  `(vector l):A^N = lambda i. EL (i - 1) l`;;

(* ------------------------------------------------------------------------- *)
(* Convenient set membership elimination theorem.                            *)
(* ------------------------------------------------------------------------- *)

let IN_ELIM_PASTECART_THM = prove
 (`!P a b. pastecart a b IN {pastecart x y | P x y} <=> P a b`,
  REWRITE_TAC[IN_ELIM_THM; PASTECART_EQ;
              FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Variant of product types using pasting of vectors.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("PCROSS",(22,"right"));;

let PCROSS = new_definition
 `s PCROSS t = {pastecart (x:A^M) (y:A^N) | x IN s /\ y IN t}`;;

let FORALL_IN_PCROSS = prove
 (`(!z. z IN s PCROSS t ==> P z) <=>
   (!x y. x IN s /\ y IN t ==> P(pastecart x y))`,
  REWRITE_TAC[PCROSS; FORALL_IN_GSPEC]);;

let EXISTS_IN_PCROSS = prove
 (`(?z. z IN s PCROSS t /\ P z) <=>
   (?x y. x IN s /\ y IN t /\ P(pastecart x y))`,
  REWRITE_TAC[PCROSS; EXISTS_IN_GSPEC; CONJ_ASSOC]);;

let PASTECART_IN_PCROSS = prove
 (`!s t x y. (pastecart x y) IN (s PCROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[PCROSS; IN_ELIM_PASTECART_THM]);;

let PCROSS_EQ_EMPTY = prove
 (`!s t. s PCROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[PCROSS] THEN SET_TAC[]);;

let PCROSS_EMPTY = prove
 (`(!s. s PCROSS {} = {}) /\ (!t. {} PCROSS t = {})`,
  REWRITE_TAC[PCROSS_EQ_EMPTY]);;

let SUBSET_PCROSS = prove
 (`!s t s' t'. s PCROSS t SUBSET s' PCROSS t' <=>
                s = {} \/ t = {} \/ s SUBSET s' /\ t SUBSET t'`,
  SIMP_TAC[PCROSS; EXTENSION; IN_ELIM_PASTECART_THM; SUBSET;
   FORALL_PASTECART; PASTECART_IN_PCROSS; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let PCROSS_MONO = prove
 (`!s t s' t'. s SUBSET s' /\ t SUBSET t' ==> s PCROSS t SUBSET s' PCROSS t'`,
  SIMP_TAC[SUBSET_PCROSS]);;

let PCROSS_EQ = prove
 (`!s s':real^M->bool t t':real^N->bool.
        s PCROSS t = s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/ s = s' /\ t = t'`,
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_PCROSS] THEN SET_TAC[]);;

let UNIV_PCROSS_UNIV = prove
 (`(:A^M) PCROSS (:A^N) = (:A^(M,N)finite_sum)`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIV]);;

let HAS_SIZE_PCROSS = prove
 (`!(s:A^M->bool) (t:A^N->bool) m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s PCROSS t) HAS_SIZE (m * n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_SIZE_PRODUCT) THEN
  MATCH_MP_TAC EQ_IMP THEN SPEC_TAC(`m * n:num`,`k:num`) THEN
  MATCH_MP_TAC BIJECTIONS_HAS_SIZE_EQ THEN
  EXISTS_TAC `\(x:A^M,y:A^N). pastecart x y` THEN
  EXISTS_TAC `\z:A^(M,N)finite_sum. fstcart z,sndcart z` THEN
  REWRITE_TAC[FORALL_IN_GSPEC; PASTECART_IN_PCROSS] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; PASTECART_FST_SND] THEN
  REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART]);;

let FINITE_PCROSS = prove
 (`!(s:A^M->bool) (t:A^N->bool).
        FINITE s /\ FINITE t ==> FINITE(s PCROSS t)`,
  MESON_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_PCROSS]);;

let FINITE_PCROSS_EQ = prove
 (`!(s:A^M->bool) (t:A^N->bool).
        FINITE(s PCROSS t) <=> s = {} \/ t = {} \/ FINITE s /\ FINITE t`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`s:A^M->bool = {}`; `t:A^N->bool = {}`] THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; FINITE_EMPTY] THEN
  EQ_TAC THEN SIMP_TAC[FINITE_PCROSS] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THENL
   [EXISTS_TAC `IMAGE fstcart ((s PCROSS t):A^(M,N)finite_sum->bool)`;
    EXISTS_TAC `IMAGE sndcart ((s PCROSS t):A^(M,N)finite_sum->bool)`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; EXISTS_PASTECART] THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM SET_TAC[]);;

let IMAGE_FSTCART_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        IMAGE fstcart (s PCROSS t) = if t = {} then {} else s`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; FSTCART_PASTECART] THEN ASM SET_TAC[]);;

let IMAGE_SNDCART_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        IMAGE sndcart (s PCROSS t) = if s = {} then {} else t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[PCROSS_EMPTY; IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[EXISTS_IN_PCROSS; SNDCART_PASTECART] THEN ASM SET_TAC[]);;

let PCROSS_INTER = prove
 (`(!s t u. s PCROSS (t INTER u) = (s PCROSS t) INTER (s PCROSS u)) /\
   (!s t u. (s INTER t) PCROSS u = (s PCROSS u) INTER (t PCROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let PCROSS_UNION = prove
 (`(!s t u. s PCROSS (t UNION u) = (s PCROSS t) UNION (s PCROSS u)) /\
   (!s t u. (s UNION t) PCROSS u = (s PCROSS u) UNION (t PCROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let PCROSS_DIFF = prove
 (`(!s t u. s PCROSS (t DIFF u) = (s PCROSS t) DIFF (s PCROSS u)) /\
   (!s t u. (s DIFF t) PCROSS u = (s PCROSS u) DIFF (t PCROSS u))`,
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; PASTECART_IN_PCROSS] THEN
  REPEAT STRIP_TAC THEN CONV_TAC TAUT);;

let INTER_PCROSS = prove
 (`!s s' t t'.
      (s PCROSS t) INTER (s' PCROSS t') = (s INTER s') PCROSS (t INTER t')`,
  REWRITE_TAC[EXTENSION; IN_INTER; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  CONV_TAC TAUT);;

let PCROSS_UNIONS_UNIONS,PCROSS_UNIONS = (CONJ_PAIR o prove)
 (`(!f g. (UNIONS f) PCROSS (UNIONS g) =
          UNIONS {s PCROSS t | s IN f /\ t IN g}) /\
   (!s f. s PCROSS (UNIONS f) = UNIONS {s PCROSS t | t IN f}) /\
   (!f t. (UNIONS f) PCROSS t = UNIONS {s PCROSS t | s IN f})`,
  REWRITE_TAC[UNIONS_GSPEC; EXTENSION; FORALL_PASTECART; IN_ELIM_THM;
              PASTECART_IN_PCROSS] THEN
  SET_TAC[]);;
