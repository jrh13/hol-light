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
(* Predefine the cases 2 and 3, which are useful for real^2 and real^3.      *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_1 = prove
 (`(:1) HAS_SIZE 1`,
  SUBGOAL_THEN `(:1) = {one}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIV; IN_SING] THEN MESON_TAC[one];
    SIMP_TAC[NOT_IN_EMPTY; HAS_SIZE; FINITE_RULES; CARD_CLAUSES; ARITH]]);;

let HAS_SIZE_2 = define_finite_type 2;;

let HAS_SIZE_3 = define_finite_type 3;;

let DIMINDEX_1 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_1;;
let DIMINDEX_2 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_2;;
let DIMINDEX_3 = MATCH_MP DIMINDEX_UNIQUE HAS_SIZE_3;;

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
(* Explicit construction of a vector from a list of components.              *)
(* ------------------------------------------------------------------------- *)

let vector = new_definition
  `(vector l):A^N = lambda i. EL (i - 1) l`;;
