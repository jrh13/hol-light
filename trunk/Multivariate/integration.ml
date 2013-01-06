(* ========================================================================= *)
(* Kurzweil-Henstock gauge integration in many dimensions.                   *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "Library/floor.ml";;
needs "Multivariate/derivatives.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Some useful lemmas about intervals.                                       *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_SUBSET_UNION_INTERVALS = prove
 (`!s i j. (?a b:real^N. i = interval[a,b]) /\ (?c d. j = interval[c,d]) /\
           ~(interior j = {}) /\
           i SUBSET j UNION s /\
           interior(i) INTER interior(j) = {}
           ==> interior i SUBSET interior s`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
  MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_INTERIOR] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERIOR_CLOSED_INTERVAL]) THEN
  SUBGOAL_THEN `interval(a:real^N,b) INTER interval[c,d] = {}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTER_INTERVAL_MIXED_EQ_EMPTY];
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]]);;

let INTER_INTERIOR_UNIONS_INTERVALS = prove
 (`!s f. FINITE f /\ open s /\
         (!t. t IN f ==> ?a b:real^N. t = interval[a,b]) /\
         (!t. t IN f ==> s INTER (interior t) = {})
         ==> s INTER interior(UNIONS f) = {}`,
  ONCE_REWRITE_TAC[TAUT
    `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> ~e ==> ~d`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; GSYM MEMBER_NOT_EMPTY] THEN
  SIMP_TAC[OPEN_CONTAINS_BALL_EQ; OPEN_INTER; OPEN_INTERIOR] THEN
  SIMP_TAC[OPEN_SUBSET_INTERIOR; OPEN_BALL; SUBSET_INTER] THEN
  REWRITE_TAC[GSYM SUBSET_INTER] THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_0; INTER_EMPTY; SUBSET_EMPTY] THEN
    MESON_TAC[CENTRE_IN_BALL; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  DISCH_TAC THEN
  REWRITE_TAC[UNIONS_INSERT; IN_INSERT] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; FORALL_AND_THM; EXISTS_OR_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `i:real^N->bool`) THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    SUBST_ALL_TAC)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(r ==> s \/ p) ==> (p ==> q) ==> r ==> s \/ q`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN interval[a,b]` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `?d. &0 < d /\ ball(x,d) SUBSET ((:real^N) DIFF interval[a,b])`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[closed; OPEN_CONTAINS_BALL; CLOSED_INTERVAL;
                    IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `min d e`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
    SIMP_TAC[IN_BALL; REAL_LT_MIN; IN_DIFF; IN_INTER; IN_UNIV; IN_UNION] THEN
    ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `(x:real^N) IN interval(a,b)` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN
     `?d. &0 < d /\ ball(x:real^N,d) SUBSET interval(a,b)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_CONTAINS_BALL; OPEN_INTERVAL]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `min d e`] THEN
    ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET])) THEN
    SIMP_TAC[IN_BALL; REAL_LT_MIN; IN_DIFF; IN_INTER; IN_UNIV; IN_UNION] THEN
    ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_INTERVAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN ASM_SIMP_TAC[REAL_LT_LE] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[GSYM REAL_LT_LE; DE_MORGAN_THM] THEN
  STRIP_TAC THEN DISJ2_TAC THENL
   [EXISTS_TAC `x + --e / &2 % basis k :real^N`;
    EXISTS_TAC `x + e / &2 % basis k :real^N`] THEN
  EXISTS_TAC `e / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `b1 SUBSET k INTER (i UNION s)
    ==> b2 SUBSET b1 /\ b2 INTER i = {}
        ==> b2 SUBSET k INTER s`)) THEN
  (CONJ_TAC THENL
    [REWRITE_TAC[SUBSET; IN_BALL] THEN
     GEN_TAC THEN MATCH_MP_TAC(NORM_ARITH `norm(d) = e / &2 ==>
        dist(x + d,y) < e / &2 ==> dist(x,y) < e`) THEN
     ASM_SIMP_TAC[NORM_MUL; NORM_BASIS] THEN UNDISCH_TAC `&0 < e` THEN
     REAL_ARITH_TAC;
     ALL_TAC]) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_INTERVAL; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_BALL; dist] THEN
  REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  W(MP_TAC o C ISPEC COMPONENT_LE_NORM o rand o lhand o lhand o snd) THEN
  DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH `x <= y /\ y < e ==> x < e`)) THEN
  ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o SPEC `k:num`) THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* This lemma about iterations comes up in a few places.                     *)
(* ------------------------------------------------------------------------- *)

let ITERATE_NONZERO_IMAGE_LEMMA = prove
 (`!op s f g a.
      monoidal op /\ FINITE s /\
      g(a) = neutral op /\
      (!x y. x IN s /\ y IN s /\ f x = f y /\ ~(x = y) ==> g(f x) = neutral op)
      ==> iterate op {f x | x | x IN s /\ ~(f x = a)} g =
          iterate op s (g o f)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ITERATE_SUPPORT] THEN
  REWRITE_TAC[support] THEN
  ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                             IMAGE f {x | x IN s /\ ~(f x = a)}`] THEN
  W(fun (asl,w) -> FIRST_ASSUM(fun th ->
   MP_TAC(PART_MATCH (rand o rand)
       (MATCH_MP ITERATE_IMAGE th) (rand w)))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; o_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_SUPERSET) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; SUBSET] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; o_THM] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on intervals where they exist.                                     *)
(* ------------------------------------------------------------------------- *)

let interval_upperbound = new_definition
  `(interval_upperbound:(real^M->bool)->real^M) s =
        lambda i. sup {a | ?x. x IN s /\ (x$i = a)}`;;

let interval_lowerbound = new_definition
  `(interval_lowerbound:(real^M->bool)->real^M) s =
        lambda i. inf {a | ?x. x IN s /\ (x$i = a)}`;;

let INTERVAL_UPPERBOUND = prove
 (`!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> interval_upperbound(interval[a,b]) = b`,
  SIMP_TAC[interval_upperbound; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

let INTERVAL_LOWERBOUND = prove
 (`!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> interval_lowerbound(interval[a,b]) = a`,
  SIMP_TAC[interval_lowerbound; CART_EQ; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INF_UNIQUE THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_REFL]);;

let INTERVAL_UPPERBOUND_1 = prove
 (`!a b. drop a <= drop b ==> interval_upperbound(interval[a,b]) = b`,
  SIMP_TAC[INTERVAL_UPPERBOUND; DIMINDEX_1; FORALL_1; drop]);;

let INTERVAL_LOWERBOUND_1 = prove
 (`!a b. drop a <= drop b ==> interval_lowerbound(interval[a,b]) = a`,
  SIMP_TAC[INTERVAL_LOWERBOUND; DIMINDEX_1; FORALL_1; drop]);;

(* ------------------------------------------------------------------------- *)
(* Content (length, area, volume...) of an interval.                         *)
(* ------------------------------------------------------------------------- *)

let content = new_definition
   `content(s:real^M->bool) =
       if s = {} then &0 else
       product(1..dimindex(:M))
              (\i. (interval_upperbound s)$i - (interval_lowerbound s)$i)`;;

let CONTENT_CLOSED_INTERVAL = prove
 (`!a b:real^N. (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i)
                ==> content(interval[a,b]) =
                        product(1..dimindex(:N)) (\i. b$i - a$i)`,
  SIMP_TAC[content; INTERVAL_UPPERBOUND; INTERVAL_EQ_EMPTY;
           INTERVAL_LOWERBOUND] THEN
  MESON_TAC[REAL_NOT_LT]);;

let CONTENT_1 = prove
 (`!a b. drop a <= drop b ==> content(interval[a,b]) = drop b - drop a`,
  SIMP_TAC[CONTENT_CLOSED_INTERVAL; FORALL_1; drop; DIMINDEX_1] THEN
  REWRITE_TAC[PRODUCT_SING_NUMSEG]);;

let CONTENT_UNIT = prove
 (`content(interval[vec 0:real^N,vec 1]) = &1`,
  REWRITE_TAC[content] THEN COND_CASES_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_POS];
    MATCH_MP_TAC PRODUCT_EQ_1 THEN
    SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
             VEC_COMPONENT; REAL_POS; IN_NUMSEG; REAL_SUB_RZERO]]);;

let CONTENT_UNIT_1 = prove
 (`content(interval[vec 0:real^1,vec 1]) = &1`,
  MATCH_ACCEPT_TAC CONTENT_UNIT);;

let CONTENT_POS_LE = prove
 (`!a b:real^N. &0 <= content(interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC PRODUCT_POS_LE_NUMSEG THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_SUB_LE]);;

let CONTENT_POS_LT = prove
 (`!a b:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i)
        ==> &0 < content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_SUB_LT;
               REAL_LT_IMP_LE]);;

let CONTENT_POS_LT_1 = prove
 (`!a b. drop a < drop b ==> &0 < content(interval[a,b])`,
  SIMP_TAC[CONTENT_POS_LT; FORALL_1; DIMINDEX_1; GSYM drop]);;

let CONTENT_EQ_0_GEN = prove
 (`!s:real^N->bool.
     bounded s
     ==> (content s = &0 <=>
          ?i a. 1 <= i /\ i <= dimindex(:N) /\ !x. x IN s ==> x$i = a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THENL
   [MESON_TAC[DIMINDEX_GE_1; LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_SUB_0] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN
  ASM_CASES_TAC `1 <= k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[interval_upperbound; interval_lowerbound; LAMBDA_BETA] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_SUP_EQ_INF o lhs o snd) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS];
    DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]]);;

let CONTENT_EQ_0 = prove
 (`!a b:real^N.
        content(interval[a,b]) = &0 <=>
        ?i. 1 <= i /\ i <= dimindex(:N) /\ b$i <= a$i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content; INTERVAL_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_EQ_0_NUMSEG; REAL_SUB_0] THEN
  AP_TERM_TAC THEN ABS_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  SIMP_TAC[REAL_NOT_LT; INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
  MESON_TAC[REAL_NOT_LE; REAL_LE_LT]);;

let CONTENT_0_SUBSET_GEN = prove
 (`!s t:real^N->bool.
      s SUBSET t /\ bounded t /\ content t = &0 ==> content s = &0`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `bounded(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONTENT_EQ_0_GEN] THEN ASM SET_TAC[]);;

let CONTENT_0_SUBSET = prove
 (`!s a b:real^N.
        s SUBSET interval[a,b] /\ content(interval[a,b]) = &0
        ==> content s = &0`,
  MESON_TAC[CONTENT_0_SUBSET_GEN; BOUNDED_INTERVAL]);;

let CONTENT_CLOSED_INTERVAL_CASES = prove
 (`!a b:real^N.
        content(interval[a,b]) =
                if !i. 1 <= i /\ i <= dimindex(:N) ==> a$i <= b$i
                then product(1..dimindex(:N)) (\i. b$i - a$i)
                else &0`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CONTENT_EQ_0; CONTENT_CLOSED_INTERVAL] THEN
  ASM_MESON_TAC[REAL_LE_TOTAL]);;

let CONTENT_EQ_0_INTERIOR = prove
 (`!a b:real^N.
        content(interval[a,b]) = &0 <=> interior(interval[a,b]) = {}`,
  REWRITE_TAC[CONTENT_EQ_0; INTERIOR_CLOSED_INTERVAL; INTERVAL_EQ_EMPTY]);;

let CONTENT_EQ_0_1 = prove
 (`!a b:real^1.
        content(interval[a,b]) = &0 <=> drop b <= drop a`,
  REWRITE_TAC[CONTENT_EQ_0; drop; DIMINDEX_1; CONJ_ASSOC; LE_ANTISYM] THEN
  MESON_TAC[]);;

let CONTENT_POS_LT_EQ = prove
 (`!a b:real^N.
        &0 < content(interval[a,b]) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[CONTENT_POS_LT] THEN
  REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
  REWRITE_TAC[CONTENT_POS_LE; CONTENT_EQ_0] THEN MESON_TAC[REAL_NOT_LE]);;

let CONTENT_EMPTY = prove
 (`content {} = &0`,
  REWRITE_TAC[content]);;

let CONTENT_SUBSET = prove
 (`!a b c d:real^N.
        interval[a,b] SUBSET interval[c,d]
        ==> content(interval[a,b]) <= content(interval[c,d])`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [content] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTENT_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[IN_INTERVAL] THEN DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
  ASM_SIMP_TAC[REAL_LE_REFL; content] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(if b then c else d) = (if ~b then d else c)`] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN COND_CASES_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS]] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let CONTENT_LT_NZ = prove
 (`!a b. &0 < content(interval[a,b]) <=> ~(content(interval[a,b]) = &0)`,
  REWRITE_TAC[CONTENT_POS_LT_EQ; CONTENT_EQ_0] THEN MESON_TAC[REAL_NOT_LE]);;

let INTERVAL_BOUNDS_NULL_1 = prove
 (`!a b:real^1.
        content(interval[a,b]) = &0
        ==> interval_upperbound(interval[a,b]) =
            interval_lowerbound(interval[a,b])`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [ASM_REWRITE_TAC[interval_upperbound; interval_lowerbound] THEN
    REWRITE_TAC[sup; inf; NOT_IN_EMPTY; EMPTY_GSPEC] THEN DISCH_TAC THEN
    REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC) THEN
    MESON_TAC[REAL_ARITH `~(x <= x - &1) /\ ~(x + &1 <= x)`];
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
    ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
    REWRITE_TAC[CONTENT_EQ_0_1; GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC]);;

let INTERVAL_BOUNDS_EMPTY_1 = prove
 (`interval_upperbound({}:real^1->bool) =
   interval_lowerbound({}:real^1->bool)`,
  MESON_TAC[INTERVAL_BOUNDS_NULL_1; CONTENT_EMPTY; EMPTY_AS_INTERVAL]);;

let CONTENT_PASTECART = prove
 (`!a b:real^M c d:real^N.
        content(interval[pastecart a c,pastecart b d]) =
        content(interval[a,b]) * content(interval[c,d])`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[CONTENT_CLOSED_INTERVAL_CASES; LAMBDA_BETA] THEN
  MATCH_MP_TAC(MESON[REAL_MUL_LZERO; REAL_MUL_RZERO]
   `(p <=> p1 /\ p2) /\ z = x * y
    ==> (if p then z else &0) =
        (if p1 then x else &0) * (if p2 then y else &0)`) THEN
  CONJ_TAC THENL
   [EQ_TAC THEN DISCH_TAC THEN TRY CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i + dimindex(:M)`) THEN
      ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[ADD_SUB]] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM]) THEN
      ASM_CASES_TAC `i <= dimindex(:M)` THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o CONJUNCT1);
        FIRST_X_ASSUM(MP_TAC o SPEC `i - dimindex(:M)` o CONJUNCT2)] THEN
      ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                   ARITH_RULE `i:num <= m ==> i <= m + n`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    SIMP_TAC[DIMINDEX_FINITE_SUM; ARITH_RULE `1 <= n + 1`;
             PRODUCT_ADD_SPLIT] THEN
    BINOP_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[PRODUCT_OFFSET]] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM; ADD_SUB;
             ARITH_RULE `i:num <= m ==> i <= m + n`;
             ARITH_RULE `i:num <= n ==> i + m <= m + n`] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The notion of a gauge --- simply an open set containing the point.        *)
(* ------------------------------------------------------------------------- *)

let gauge = new_definition
  `gauge d <=> !x. x IN d(x) /\ open(d(x))`;;

let GAUGE_BALL_DEPENDENT = prove
 (`!e. (!x. &0 < e(x)) ==> gauge(\x. ball(x,e(x)))`,
  SIMP_TAC[gauge; OPEN_BALL; IN_BALL; DIST_REFL]);;

let GAUGE_BALL = prove
 (`!e. &0 < e ==> gauge (\x. ball(x,e))`,
  SIMP_TAC[gauge; OPEN_BALL; IN_BALL; DIST_REFL]);;

let GAUGE_TRIVIAL = prove
 (`gauge (\x. ball(x,&1))`,
  SIMP_TAC[GAUGE_BALL; REAL_LT_01]);;

let GAUGE_INTER = prove
 (`!d1 d2. gauge d1 /\ gauge d2 ==> gauge (\x. (d1 x) INTER (d2 x))`,
  SIMP_TAC[gauge; IN_INTER; OPEN_INTER]);;

let GAUGE_INTERS = prove
 (`!s. FINITE s /\ (!d. d IN s ==> gauge (f d))
       ==> gauge(\x. INTERS {f d x | d IN s})`,
  REWRITE_TAC[gauge; IN_INTERS] THEN
  REWRITE_TAC[SET_RULE `{f d x | d IN s} = IMAGE (\d. f d x) s`] THEN
  SIMP_TAC[FORALL_IN_IMAGE; OPEN_INTERS; FINITE_IMAGE]);;

let GAUGE_EXISTENCE_LEMMA = prove
 (`(!x. ?d. p x ==> &0 < d /\ q d x) <=>
   (!x. ?d. &0 < d /\ (p x ==> q d x))`,
  MESON_TAC[REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* Divisions.                                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("division_of",(12,"right"));;

let division_of = new_definition
 `s division_of i <=>
        FINITE s /\
        (!k. k IN s
             ==> k SUBSET i /\ ~(k = {}) /\ ?a b. k = interval[a,b]) /\
        (!k1 k2. k1 IN s /\ k2 IN s /\ ~(k1 = k2)
                 ==> interior(k1) INTER interior(k2) = {}) /\
        (UNIONS s = i)`;;

let DIVISION_OF = prove
 (`s division_of i <=>
        FINITE s /\
        (!k. k IN s ==> ~(k = {}) /\ ?a b. k = interval[a,b]) /\
        (!k1 k2. k1 IN s /\ k2 IN s /\ ~(k1 = k2)
                 ==> interior(k1) INTER interior(k2) = {}) /\
        UNIONS s = i`,
  REWRITE_TAC[division_of] THEN SET_TAC[]);;

let DIVISION_OF_FINITE = prove
 (`!s i. s division_of i ==> FINITE s`,
  MESON_TAC[division_of]);;

let DIVISION_OF_SELF = prove
 (`!a b. ~(interval[a,b] = {}) ==> {interval[a,b]} division_of interval[a,b]`,
  REWRITE_TAC[division_of; FINITE_INSERT; FINITE_RULES; IN_SING; UNIONS_1] THEN
  MESON_TAC[SUBSET_REFL]);;

let DIVISION_OF_TRIVIAL = prove
 (`!s. s division_of {} <=> s = {}`,
  REWRITE_TAC[division_of; SUBSET_EMPTY; CONJ_ASSOC] THEN
  REWRITE_TAC[TAUT `~(p /\ ~p)`; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[AC CONJ_ACI `((a /\ b) /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FINITE_RULES; UNIONS_0; NOT_IN_EMPTY]);;

let EMPTY_DIVISION_OF = prove
 (`!s. {} division_of s <=> s = {}`,
  REWRITE_TAC[division_of; UNIONS_0; FINITE_EMPTY; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let DIVISION_OF_SING = prove
 (`!s a. s division_of interval[a,a] <=> s = {interval[a,a]}`,
  let lemma = prove
   (`s SUBSET {{a}} /\ p /\ UNIONS s = {a} <=> s = {{a}} /\ p`,
    EQ_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE `UNIONS {a} = a`] THEN ASM SET_TAC[]) in
  REWRITE_TAC[division_of; INTERVAL_SING] THEN
  REWRITE_TAC[SET_RULE `k SUBSET {a} /\ ~(k = {}) /\ p <=> k = {a} /\ p`] THEN
  REWRITE_TAC[GSYM INTERVAL_SING] THEN
  REWRITE_TAC[MESON[] `(k = interval[a,b] /\ ?c d. k = interval[c,d]) <=>
                       (k = interval[a,b])`] THEN
  REWRITE_TAC[SET_RULE `(!k. k IN s ==> k = a) <=> s SUBSET {a}`] THEN
  REWRITE_TAC[INTERVAL_SING; lemma] THEN MESON_TAC[FINITE_RULES; IN_SING]);;

let ELEMENTARY_EMPTY = prove
 (`?p. p division_of {}`,
  REWRITE_TAC[DIVISION_OF_TRIVIAL; EXISTS_REFL]);;

let ELEMENTARY_INTERVAL = prove
 (`!a b. ?p. p division_of interval[a,b]`,
  MESON_TAC[DIVISION_OF_TRIVIAL; DIVISION_OF_SELF]);;

let DIVISION_CONTAINS = prove
 (`!s i. s division_of i ==> !x. x IN i ==> ?k. x IN k /\ k IN s`,
  REWRITE_TAC[division_of; EXTENSION; IN_UNIONS] THEN MESON_TAC[]);;

let FORALL_IN_DIVISION = prove
 (`!P d i. d division_of i
           ==> ((!x. x IN d ==> P x) <=>
               (!a b. interval[a,b] IN d ==> P(interval[a,b])))`,
  REWRITE_TAC[division_of] THEN MESON_TAC[]);;

let FORALL_IN_DIVISION_NONEMPTY = prove
 (`!P d i.
         d division_of i
         ==> ((!x. x IN d ==> P x) <=>
              (!a b. interval [a,b] IN d /\ ~(interval[a,b] = {})
                     ==> P (interval [a,b])))`,
  REWRITE_TAC[division_of] THEN MESON_TAC[]);;

let DIVISION_OF_SUBSET = prove
 (`!p q:(real^N->bool)->bool.
        p division_of (UNIONS p) /\ q SUBSET p ==> q division_of (UNIONS q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[division_of] THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ASM SET_TAC[]; ASM SET_TAC[]]);;

let DIVISION_OF_UNION_SELF = prove
 (`!p s. p division_of s ==> p division_of (UNIONS p)`,
  REWRITE_TAC[division_of] THEN MESON_TAC[]);;

let DIVISION_OF_CONTENT_0 = prove
 (`!a b d. content(interval[a,b]) = &0 /\ d division_of interval[a,b]
           ==> !k. k IN d ==> content k = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REWRITE_TAC[GSYM REAL_LE_ANTISYM; CONTENT_POS_LE] THEN
  ASM_MESON_TAC[CONTENT_SUBSET; division_of]);;

let DIVISION_INTER = prove
 (`!s1 s2:real^N->bool p1 p2.
        p1 division_of s1 /\
        p2 division_of s2
        ==> {k1 INTER k2 | k1 IN p1 /\ k2 IN p2 /\ ~(k1 INTER k2 = {})}
            division_of (s1 INTER s2)`,
  let lemma = prove
   (`{k1 INTER k2 | k1 IN p1 /\ k2 IN p2 /\ ~(k1 INTER k2 = {})} =
        {s | s IN IMAGE (\(k1,k2). k1 INTER k2) (p1 CROSS p2) /\
             ~(s = {})}`,
    REWRITE_TAC[EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM; IN_CROSS] THEN
    MESON_TAC[]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[DIVISION_OF] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[lemma; FINITE_RESTRICT; FINITE_CROSS; FINITE_IMAGE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INTER_INTERVAL];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(interior x1 INTER interior x2 = {} \/
       interior y1 INTER interior y2 = {}) /\
      interior(x1 INTER y1) SUBSET interior(x1) /\
      interior(x1 INTER y1) SUBSET interior(y1) /\
      interior(x2 INTER y2) SUBSET interior(x2) /\
      interior(x2 INTER y2) SUBSET interior(y2)
      ==> interior(x1 INTER y1) INTER interior(x2 INTER y2) = {}`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[];
    REWRITE_TAC[SET_RULE `UNIONS {x | x IN s /\ ~(x = {})} = UNIONS s`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o SYM)) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; IN_INTER] THEN
    MESON_TAC[IN_INTER]]);;

let DIVISION_INTER_1 = prove
 (`!d i a b:real^N.
        d division_of i /\ interval[a,b] SUBSET i
        ==> { interval[a,b] INTER k | k |
                 k IN d /\ ~(interval[a,b] INTER k = {}) }
            division_of interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_REWRITE_TAC[INTER_EMPTY; SET_RULE `{{} | F} = {}`;
                  DIVISION_OF_TRIVIAL] THEN
  MP_TAC(ISPECL [`interval[a:real^N,b]`; `i:real^N->bool`;
                 `{interval[a:real^N,b]}`; `d:(real^N->bool)->bool`]
                DIVISION_INTER) THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF; SET_RULE `s SUBSET t ==> s INTER t = s`] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let ELEMENTARY_INTER = prove
 (`!s t. (?p. p division_of s) /\ (?p. p division_of t)
         ==> ?p. p division_of (s INTER t)`,
  MESON_TAC[DIVISION_INTER]);;

let ELEMENTARY_INTERS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ ~(f = {}) /\
        (!s. s IN f ==> ?p. p division_of s)
        ==> ?p. p division_of (INTERS f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s:(real^N->bool)->bool`] THEN
  ASM_CASES_TAC `s:(real^N->bool)->bool = {}` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[INTERS_0; INTER_UNIV; IN_SING] THEN MESON_TAC[];
    REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ELEMENTARY_INTER THEN ASM_MESON_TAC[]]);;

let DIVISION_DISJOINT_UNION = prove
 (`!s1 s2:real^N->bool p1 p2.
        p1 division_of s1 /\
        p2 division_of s2 /\
        interior s1 INTER interior s2 = {}
        ==> (p1 UNION p2) division_of (s1 UNION s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[division_of] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION; EXISTS_OR_THM; SET_RULE
   `UNIONS {x | P x \/ Q x} = UNIONS {x | P x} UNION UNIONS {x | Q x}`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC; ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE
   `!s' t'. s SUBSET s' /\ t SUBSET t' /\ s' INTER t' = {}
            ==> s INTER t = {}`)
  THENL
   [MAP_EVERY EXISTS_TAC
     [`interior s1:real^N->bool`; `interior s2:real^N->bool`];
    MAP_EVERY EXISTS_TAC
     [`interior s2:real^N->bool`; `interior s1:real^N->bool`]] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC SUBSET_INTERIOR) THEN
  ASM SET_TAC[]);;

let PARTIAL_DIVISION_EXTEND_1 = prove
 (`!a b c d:real^N.
        interval[c,d] SUBSET interval[a,b] /\ ~(interval[c,d] = {})
        ==> ?p. p division_of interval[a,b] /\
                interval[c,d] IN p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY])) THEN
  EXISTS_TAC
   `{interval
      [(lambda i. if i < l then (c:real^N)$i else (a:real^N)$i):real^N,
       (lambda i. if i < l then d$i else if i = l then c$l else b$i)] |
       l IN 1..(dimindex(:N)+1)} UNION
    {interval
      [(lambda i. if i < l then c$i else if i = l then d$l else a$i),
       (lambda i. if i < l then (d:real^N)$i else (b:real^N)$i):real^N] |
       l IN 1..(dimindex(:N)+1)}` THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `dimindex(:N)+1` THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= n + 1`] THEN
    AP_TERM_TAC THEN SIMP_TAC[CONS_11; PAIR_EQ; CART_EQ; LAMBDA_BETA] THEN
    SIMP_TAC[ARITH_RULE `i <= n ==> i < n + 1`];
    DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL]) THEN
  ASM_REWRITE_TAC[DIVISION_OF] THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SIMPLE_IMAGE] THEN
    SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUMSEG];
    REWRITE_TAC[IN_UNION; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_AND_THM; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[IN_NUMSEG; INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
    CONJ_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    (CONJ_TAC THENL [ALL_TAC; MESON_TAC[]]) THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    REWRITE_TAC[IN_UNION; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[SET_RULE
      `(!y. y IN {f x | x IN s} \/ y IN {g x | x IN s} ==> P y) <=>
       (!x. x IN s ==> P(f x) /\ P(g x))`] THEN
    REWRITE_TAC[AND_FORALL_THM; IN_NUMSEG] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN
      REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      REWRITE_TAC[INTER_ACI; CONJ_ACI] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`l:num`; `m:num`] THEN
    DISCH_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `(~p ==> q) <=> (~q ==> p)`] THEN
     REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
    REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x. ~(x IN s /\ x IN t)`] THEN
    ASM_SIMP_TAC[IN_NUMSEG; INTERVAL_NE_EMPTY; LAMBDA_BETA; IN_INTERVAL;
                 INTERIOR_CLOSED_INTERVAL] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN REPEAT CONJ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (LABEL_TAC "*")) THEN
    AP_TERM_TAC THEN SIMP_TAC[CONS_11; PAIR_EQ; CART_EQ; LAMBDA_BETA] THENL
     (let tac1 =
        UNDISCH_TAC `l:num <= m` THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REMOVE_THEN "*" (MP_TAC o SPEC `l:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC
      and tac2 =
        UNDISCH_TAC `l:num <= m` THEN GEN_REWRITE_TAC LAND_CONV [LE_LT] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
         [REMOVE_THEN "*" (MP_TAC o SPEC `l:num`) THEN ANTS_TAC THENL
           [ASM_ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
        CONJ_TAC THEN X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i:num = l` THEN
        ASM_REWRITE_TAC[LT_REFL] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
        DISCH_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `l:num`)) THEN
        ASM_REWRITE_TAC[LT_REFL] THEN REAL_ARITH_TAC in
      [tac1; tac2; tac2; tac1]);
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; SUBSET; FORALL_IN_UNIONS; SIMPLE_IMAGE] THEN
      REWRITE_TAC[IN_UNIONS; IN_INSERT; IN_UNION; FORALL_IN_IMAGE;
        RIGHT_FORALL_IMP_THM; FORALL_AND_THM;
        TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`] THEN
      ASM_SIMP_TAC[IN_INTERVAL; IN_NUMSEG; LAMBDA_BETA] THEN
      REPEAT CONJ_TAC THEN GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `a IN s ==> (c DIFF a) SUBSET UNIONS s ==> c SUBSET UNIONS s`)) THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ ~c) <=> a /\ b ==> c`] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; SIMPLE_IMAGE; EXISTS_IN_IMAGE; IN_UNION;
                EXISTS_OR_THM; RIGHT_OR_DISTRIB] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN EXISTS_TAC `l:num` THEN
    ASM_SIMP_TAC[IN_NUMSEG; IN_INTERVAL; LAMBDA_BETA;
                 ARITH_RULE `x <= n ==> x <= n + 1`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    MATCH_MP_TAC MONO_OR THEN REWRITE_TAC[REAL_NOT_LE] THEN
    REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]]);;

let PARTIAL_DIVISION_EXTEND_INTERVAL = prove
 (`!p a b:real^N.
        p division_of (UNIONS p) /\ (UNIONS p) SUBSET interval[a,b]
        ==> ?q. p SUBSET q /\ q division_of interval[a,b]`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[EMPTY_SUBSET] THENL
   [MESON_TAC[ELEMENTARY_INTERVAL]; STRIP_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN `!k:real^N->bool. k IN p ==> ?q. q division_of interval[a,b] /\
                                                k IN q`
  MP_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real^N->bool` o el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC PARTIAL_DIVISION_EXTEND_1 THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:(real^N->bool)->(real^N->bool)->bool`) THEN
  SUBGOAL_THEN
   `?d. d division_of INTERS {UNIONS(q i DELETE i) | (i:real^N->bool) IN p}`
  MP_TAC THENL
   [MATCH_MP_TAC ELEMENTARY_INTERS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[IMAGE_EQ_EMPTY; FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^N->bool` THEN
    DISCH_TAC THEN EXISTS_TAC `(q k) DELETE (k:real^N->bool)` THEN
    MATCH_MP_TAC DIVISION_OF_SUBSET THEN
    EXISTS_TAC `(q:(real^N->bool)->(real^N->bool)->bool) k` THEN
    REWRITE_TAC[DELETE_SUBSET] THEN ASM_MESON_TAC[division_of];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `d:(real^N->bool)->bool`) THEN
  EXISTS_TAC `(d UNION p):(real^N->bool)->bool` THEN
  REWRITE_TAC[SUBSET_UNION] THEN
  SUBGOAL_THEN `interval[a:real^N,b] =
                INTERS {UNIONS (q i DELETE i) | i IN p} UNION
                UNIONS p`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC(SET_RULE
     `~(s = {}) /\
      (!i. i IN s ==> f i UNION i = t)
     ==> t = INTERS (IMAGE f s) UNION (UNIONS s)`) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `UNIONS k = s /\ i IN k ==> UNIONS (k DELETE i) UNION i = s`) THEN
    ASM_MESON_TAC[division_of];
    ALL_TAC] THEN
  MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!s. u SUBSET s /\ s INTER t = {} ==> u INTER t = {}`) THEN
  EXISTS_TAC `interior(UNIONS(q k DELETE (k:real^N->bool)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN
    MATCH_MP_TAC(SET_RULE `x IN s ==> INTERS s SUBSET x`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  REWRITE_TAC[OPEN_INTERIOR; FINITE_DELETE; IN_DELETE] THEN
  ASM_MESON_TAC[division_of]);;

let ELEMENTARY_BOUNDED = prove
 (`!s. (?p. p division_of s) ==> bounded s`,
  REWRITE_TAC[division_of] THEN
  ASM_MESON_TAC[BOUNDED_UNIONS; BOUNDED_INTERVAL]);;

let ELEMENTARY_SUBSET_INTERVAL = prove
 (`!s. (?p. p division_of s) ==> ?a b. s SUBSET interval[a,b]`,
  MESON_TAC[ELEMENTARY_BOUNDED; BOUNDED_SUBSET_CLOSED_INTERVAL]);;

let DIVISION_UNION_INTERVALS_EXISTS = prove
 (`!a b c d:real^N.
        ~(interval[a,b] = {})
        ==> ?p. (interval[a,b] INSERT p) division_of
                (interval[a,b] UNION interval[c,d])`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[c:real^N,d] = {}` THENL
   [ASM_REWRITE_TAC[UNION_EMPTY] THEN ASM_MESON_TAC[DIVISION_OF_SELF];
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^N,b] INTER interval[c,d] = {}` THENL
   [EXISTS_TAC `{interval[c:real^N,d]}` THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
    MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN
    ASM_SIMP_TAC[DIVISION_OF_SELF] THEN
    MATCH_MP_TAC(SET_RULE
     `interior s SUBSET s /\ interior t SUBSET t /\ s INTER t = {}
      ==> interior s INTER interior t = {}`) THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u v:real^N. interval[a,b] INTER interval[c,d] = interval[u,v]`
  STRIP_ASSUME_TAC THENL [MESON_TAC[INTER_INTERVAL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^N`; `d:real^N`; `u:real^N`; `v:real^N`]
                PARTIAL_DIVISION_EXTEND_1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTER_SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p DELETE interval[u:real^N,v]` THEN
  SUBGOAL_THEN `interval[a:real^N,b] UNION interval[c,d] =
                interval[a,b] UNION UNIONS(p DELETE interval[u,v])`
  SUBST1_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS o
                GEN_REWRITE_RULE I [division_of]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `x INSERT s = {x} UNION s`] THEN
  MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIVISION_OF_SUBSET THEN
    EXISTS_TAC `p:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[DIVISION_OF_UNION_SELF; DELETE_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INTERIOR_INTER] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `interior(interval[u:real^N,v] INTER
              UNIONS (p DELETE interval[u,v]))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `!cd. p SUBSET cd /\ uv = ab INTER cd
           ==> (ab INTER p = uv INTER p)`) THEN
    EXISTS_TAC `interval[c:real^N,d]` THEN
    ASM_REWRITE_TAC[UNIONS_SUBSET; IN_DELETE] THEN
    ASM_MESON_TAC[division_of];
    REWRITE_TAC[INTERIOR_INTER] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    REWRITE_TAC[IN_DELETE; OPEN_INTERIOR; FINITE_DELETE] THEN
    ASM_MESON_TAC[division_of]]);;

let DIVISION_OF_UNIONS = prove
 (`!f. FINITE f /\
       (!p. p IN f ==> p division_of (UNIONS p)) /\
       (!k1 k2. k1 IN UNIONS f /\ k2 IN UNIONS f /\ ~(k1 = k2)
                ==> interior k1 INTER interior k2 = {})
       ==> (UNIONS f) division_of UNIONS(UNIONS f)`,
  REWRITE_TAC[division_of] THEN
  SIMP_TAC[FINITE_UNIONS] THEN REWRITE_TAC[FORALL_IN_UNIONS] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN SET_TAC[]);;

let ELEMENTARY_UNION_INTERVAL_STRONG = prove
 (`!p a b:real^N.
        p division_of (UNIONS p)
        ==> ?q. p SUBSET q /\ q division_of (interval[a,b] UNION UNIONS p)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[UNIONS_0; UNION_EMPTY; EMPTY_SUBSET] THEN
    MESON_TAC[ELEMENTARY_INTERVAL];
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THENL [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  ASM_CASES_TAC `interior(interval[a:real^N,b]) = {}` THENL
   [EXISTS_TAC `interval[a:real^N,b] INSERT p` THEN
    REWRITE_TAC[division_of] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    SIMP_TAC[FINITE_INSERT; UNIONS_INSERT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^N,b] SUBSET UNIONS p` THENL
   [ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s UNION t = t`] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k:real^N->bool. k IN p
                     ==> ?q. ~(k IN q) /\ ~(q = {}) /\
                             (k INSERT q) division_of (interval[a,b] UNION k)`
  MP_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:real^N`; `d:real^N`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN
    MP_TAC(ISPECL [`c:real^N`; `d:real^N`; `a:real^N`; `b:real^N`]
        DIVISION_UNION_INTERVALS_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:(real^N->bool)->bool`) THEN
    EXISTS_TAC `q DELETE interval[c:real^N,d]` THEN
    ASM_REWRITE_TAC[IN_DELETE; SET_RULE
     `x INSERT (q DELETE x) = x INSERT q`] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `(interval[c:real^N,d] INSERT q) division_of
                 (interval [c,d] UNION interval [a,b])` THEN
    ASM_SIMP_TAC[SET_RULE `s DELETE x = {} ==> x INSERT s = {x}`] THEN
    REWRITE_TAC[division_of; UNIONS_1] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `q:(real^N->bool)->(real^N->bool)->bool`) THEN
  MP_TAC(ISPEC `IMAGE (UNIONS o (q:(real^N->bool)->(real^N->bool)->bool)) p`
    ELEMENTARY_INTERS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `(q:(real^N->bool)->(real^N->bool)->bool) k` THEN
    REWRITE_TAC[o_THM] THEN MATCH_MP_TAC DIVISION_OF_SUBSET THEN
    EXISTS_TAC `(k:real^N->bool) INSERT q k` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_UNION_SELF]; SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `r:(real^N->bool)->bool`)] THEN
  EXISTS_TAC `p UNION r:(real^N->bool)->bool` THEN SIMP_TAC[SUBSET_UNION] THEN
  SUBGOAL_THEN
   `interval[a:real^N,b] UNION UNIONS p =
    UNIONS p UNION INTERS(IMAGE (UNIONS o q) p)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(y:real^N) IN UNIONS p` THEN ASM_REWRITE_TAC[IN_INTERS] THEN
    REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; FORALL_IN_IMAGE;
                RIGHT_FORALL_IMP_THM] THEN
    SUBGOAL_THEN
     `!k. k IN p ==> UNIONS(k INSERT q k) = interval[a:real^N,b] UNION k`
    MP_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    REWRITE_TAC[UNIONS_INSERT; o_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IN_UNION] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    UNDISCH_TAC `~((y:real^N) IN UNIONS p)` THEN
    SIMP_TAC[IN_UNIONS; NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    ASM_CASES_TAC `(y:real^N) IN interval[a,b]` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTERIOR_FINITE_INTERS; FINITE_IMAGE] THEN
  MATCH_MP_TAC(SET_RULE `(?x. x IN p /\ f x INTER s = {})
                        ==> INTERS (IMAGE f p) INTER s = {}`) THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; o_THM] THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[division_of; FINITE_INSERT; IN_INSERT];
    ASM_MESON_TAC[division_of; FINITE_INSERT; IN_INSERT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN
  ASM_REWRITE_TAC[division_of; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let ELEMENTARY_UNION_INTERVAL = prove
 (`!p a b:real^N.
        p division_of (UNIONS p)
        ==> ?q. q division_of (interval[a,b] UNION UNIONS p)`,
  MESON_TAC[ELEMENTARY_UNION_INTERVAL_STRONG]);;

let ELEMENTARY_UNIONS_INTERVALS = prove
 (`!f. FINITE f /\
       (!s. s IN f ==> ?a b:real^N. s = interval[a,b])
       ==> (?p. p division_of (UNIONS f))`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; ELEMENTARY_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:(real^N->bool)->bool`) THEN
  SUBGOAL_THEN `UNIONS f:real^N->bool = UNIONS p` SUBST1_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  MATCH_MP_TAC ELEMENTARY_UNION_INTERVAL THEN ASM_MESON_TAC[division_of]);;

let ELEMENTARY_UNION = prove
 (`!s t:real^N->bool.
        (?p. p division_of s) /\ (?p. p division_of t)
        ==> (?p. p division_of (s UNION t))`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p1:(real^N->bool)->bool`)
                    (X_CHOOSE_TAC `p2:(real^N->bool)->bool`)) THEN
  SUBGOAL_THEN `s UNION t :real^N->bool = UNIONS p1 UNION UNIONS p2`
  SUBST1_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `UNIONS p1 UNION UNIONS p2 = UNIONS(p1 UNION p2)`] THEN
  MATCH_MP_TAC ELEMENTARY_UNIONS_INTERVALS THEN
  REWRITE_TAC[IN_UNION; FINITE_UNION] THEN
  ASM_MESON_TAC[division_of]);;

let PARTIAL_DIVISION_EXTEND = prove
 (`!p q s t:real^N->bool.
        p division_of s /\ q division_of t /\ s SUBSET t
        ==> ?r. p SUBSET r /\ r division_of t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a b:real^N. t SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[ELEMENTARY_SUBSET_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?r1. p SUBSET r1 /\ r1 division_of interval[a:real^N,b]`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC PARTIAL_DIVISION_EXTEND_INTERVAL THEN
    ASM_MESON_TAC[division_of; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r2:(real^N->bool)->bool.
        r2 division_of (UNIONS(r1 DIFF p)) INTER (UNIONS q)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ELEMENTARY_INTER THEN
    ASM_MESON_TAC[FINITE_DIFF; IN_DIFF; division_of;
                  ELEMENTARY_UNIONS_INTERVALS];
    ALL_TAC] THEN
  EXISTS_TAC `p UNION r2:(real^N->bool)->bool` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `t:real^N->bool = UNIONS p UNION (UNIONS(r1 DIFF p) INTER UNIONS q)`
  SUBST1_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o
                GEN_REWRITE_RULE I [division_of])) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[];
    MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!t'. t SUBSET t' /\ s INTER t' = {} ==> s INTER t = {}`) THEN
    EXISTS_TAC `interior(UNIONS(r1 DIFF p)):real^N->bool` THEN
    CONJ_TAC THENL [MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
           REWRITE_TAC[OPEN_INTERIOR] THEN
           REPEAT(CONJ_TAC THENL
            [ASM_MESON_TAC[IN_DIFF; FINITE_DIFF; division_of]; ALL_TAC]) THEN
           REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
           ONCE_REWRITE_TAC[INTER_COMM]) THEN
    ASM_MESON_TAC[division_of; SUBSET]]);;

let INTERVAL_SUBDIVISION = prove
 (`!a b c:real^N.
        c IN interval[a,b]
        ==> IMAGE (\s. interval[(lambda i. if i IN s then c$i else a$i),
                                (lambda i. if i IN s then b$i else c$i)])
                  {s | s SUBSET 1..dimindex(:N)}
            division_of interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
  REWRITE_TAC[DIVISION_OF] THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET; FINITE_NUMSEG] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; SUBSET_INTERVAL; INTERVAL_NE_EMPTY] THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[LAMBDA_BETA] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    X_GEN_TAC `s:num->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `s':num->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[SET_RULE
     `(~p ==> s INTER t = {}) <=> (!x. x IN s /\ x IN t ==> p)`] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERVAL; AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    SIMP_TAC[LAMBDA_BETA] THEN
    ASM_CASES_TAC `s':num->bool = s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
     `~(s' = s) ==> ?x. x IN s' /\ ~(x IN s) \/ x IN s /\ ~(x IN s')`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; IN_NUMSEG]; REAL_ARITH_TAC]);
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    GEN_REWRITE_TAC I [SUBSET] THENL
     [REWRITE_TAC[FORALL_IN_UNIONS] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; GSYM SUBSET] THEN
      SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN EXISTS_TAC
       `{i | i IN 1..dimindex(:N) /\ (c:real^N)$i <= (x:real^N)$i}` THEN
      CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[IN_INTERVAL]] THEN
      SIMP_TAC[LAMBDA_BETA; IN_ELIM_THM; IN_NUMSEG] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
      ASM_MESON_TAC[REAL_LE_TOTAL]]]);;

let DIVISION_OF_NONTRIVIAL = prove
 (`!s a b:real^N.
        s division_of interval[a,b] /\ ~(content(interval[a,b]) = &0)
        ==> {k | k IN s /\ ~(content k = &0)} division_of interval[a,b]`,
  REPEAT GEN_TAC THEN WF_INDUCT_TAC `CARD(s:(real^N->bool)->bool)` THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `{k:real^N->bool | k IN s /\ ~(content k = &0)} = s` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ ~b <=> a) <=> a /\ b`] THEN
  X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (k:real^N->bool)`) THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM SET_TAC[]] THEN
  REWRITE_TAC[DIVISION_OF] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:real^N->bool) IN s`)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N`; `d:real^N`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC(SET_RULE
    `UNIONS s = i /\ k SUBSET UNIONS(s DELETE k)
     ==> UNIONS(s DELETE k) = i`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[CLOSED_LIMPT; SUBSET]
   `closed s /\ (!x. x IN k ==> x limit_point_of s) ==> k SUBSET s`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    ASM_MESON_TAC[CLOSED_INTERVAL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[LIMPT_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `?y:real^N. y IN UNIONS s /\ ~(y IN interval[c,d]) /\
                           ~(y = x) /\ norm(y - x) < e`
  MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(content(interval[a:real^N,b]) = &0)`;
    `content(interval[c:real^N,d]) = &0`] THEN
  REWRITE_TAC[CONTENT_EQ_0; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[REAL_NOT_LE] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(interval[c:real^N,d] = {})` THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[REAL_NOT_LT] THEN
  ASM_SIMP_TAC[REAL_ARITH `a <= b ==> (b <= a <=> a = b)`] THEN
  DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
  UNDISCH_TAC `interval[c:real^N,d] SUBSET interval[a,b]` THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ASSUME `(x:real^N) IN interval[c,d]`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_ARITH `d = c ==> (c <= x /\ x <= d <=> x = c)`] THEN
  DISCH_TAC THEN
  MP_TAC(ASSUME `(x:real^N) IN interval[a,b]`) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_INTERVAL] THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN EXISTS_TAC
   `(lambda j. if j = i then
                 if (c:real^N)$i <= ((a:real^N)$i + (b:real^N)$i) / &2
                 then c$i + min e (b$i - c$i) / &2
                 else c$i - min e (c$i - a$i) / &2
               else (x:real^N)$j):real^N` THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; CART_EQ] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `(x:real^N) IN interval[a,b]` THEN
    REWRITE_TAC[IN_INTERVAL] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[vector_norm; dot] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT; GSYM REAL_POW_2] THEN
    REWRITE_TAC[REAL_ARITH
     `((if p then x else y) - y) pow 2 = if p then (x - y) pow 2 else &0`] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; POW_2_SQRT_ABS] THEN
    ASM_REAL_ARITH_TAC]);;

let DIVISION_OF_AFFINITY = prove
 (`!d s:real^N->bool m c.
    IMAGE (IMAGE (\x. m % x + c)) d division_of (IMAGE (\x. m % x + c) s) <=>
    if m = &0 then if s = {} then d = {}
                   else ~(d = {}) /\ !k. k IN d ==> ~(k = {})
    else d division_of s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; DIVISION_OF_TRIVIAL; IMAGE_EQ_EMPTY] THEN
    ASM_CASES_TAC `d:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; EMPTY_DIVISION_OF; UNIONS_0;
                    IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
    ASM_SIMP_TAC[SET_RULE `~(s = {}) ==> IMAGE (\x. c) s = {c}`] THEN
    ASM_CASES_TAC `!k:real^N->bool. k IN d ==> ~(k = {})` THEN
    ASM_REWRITE_TAC[division_of] THENL
     [ALL_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[IMAGE_EQ_EMPTY]] THEN
    SUBGOAL_THEN
     `IMAGE (IMAGE ((\x. c):real^N->real^N)) d = {{c}}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_IMAGE; IN_SING] THEN ASM SET_TAC[];
      SIMP_TAC[UNIONS_1; FINITE_SING; IN_SING; IMP_CONJ] THEN
      REWRITE_TAC[SUBSET_REFL; NOT_INSERT_EMPTY] THEN
      MESON_TAC[INTERVAL_SING]];
    REWRITE_TAC[division_of] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM INTERIOR_INTER] THEN
    ASM_SIMP_TAC[FINITE_IMAGE_INJ_EQ; GSYM IMAGE_UNIONS;
         VECTOR_ARITH `x + a:real^N = y + a <=> x = y`;
             VECTOR_MUL_LCANCEL;
     SET_RULE `(!x y. f x = f y <=> x = y)
               ==> (IMAGE f s SUBSET IMAGE f t <=> s SUBSET t) /\
                   (IMAGE f s = IMAGE f t <=> s = t) /\
                   (IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t))`] THEN
    AP_TERM_TAC THEN BINOP_TAC THENL
     [AP_TERM_TAC THEN ABS_TAC THEN REPLICATE_TAC 3 AP_TERM_TAC THEN
      EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[IMAGE_AFFINITY_INTERVAL] THENL [ALL_TAC; MESON_TAC[]] THEN
      FIRST_X_ASSUM(MP_TAC o AP_TERM
       `IMAGE (\x:real^N. inv m % x + --(inv m % c))`) THEN
      ASM_SIMP_TAC[GSYM IMAGE_o; AFFINITY_INVERSES] THEN
      ASM_REWRITE_TAC[IMAGE_I; IMAGE_AFFINITY_INTERVAL] THEN MESON_TAC[];
      SUBGOAL_THEN `(\x:real^N. m % x + c) = (\x. c + x) o (\x. m % x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN VECTOR_ARITH_TAC;
        REWRITE_TAC[IMAGE_o; INTERIOR_TRANSLATION] THEN
        ASM_SIMP_TAC[INTERIOR_INJECTIVE_LINEAR_IMAGE; LINEAR_SCALING;
                     VECTOR_MUL_LCANCEL; IMAGE_EQ_EMPTY]]]]);;

let DIVISION_OF_TRANSLATION = prove
 (`!d s:real^N->bool.
        IMAGE (IMAGE (\x. a + x)) d division_of (IMAGE (\x. a + x) s) <=>
        d division_of s`,
  ONCE_REWRITE_TAC[VECTOR_ARITH `a + x:real^N = &1 % x + a`] THEN
  REWRITE_TAC[DIVISION_OF_AFFINITY] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let DIVISION_OF_REFLECT = prove
 (`!d s:real^N->bool.
        IMAGE (IMAGE (--)) d division_of IMAGE (--) s <=>
        d division_of s`,
  REPEAT GEN_TAC THEN SUBGOAL_THEN `(--) = \x:real^N. --(&1) % x + vec 0`
  SUBST1_TAC THENL
  [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
   REWRITE_TAC[DIVISION_OF_AFFINITY] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let ELEMENTARY_COMPACT = prove
 (`!s. (?d. d division_of s) ==> compact s`,
  REWRITE_TAC[division_of] THEN
  MESON_TAC[COMPACT_UNIONS; COMPACT_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Tagged (partial) divisions.                                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("tagged_partial_division_of",(12,"right"));;
parse_as_infix("tagged_division_of",(12,"right"));;

let tagged_partial_division_of = new_definition
  `s tagged_partial_division_of i <=>
        FINITE s /\
        (!x k. (x,k) IN s
               ==> x IN k /\ k SUBSET i /\ ?a b. k = interval[a,b]) /\
        (!x1 k1 x2 k2. (x1,k1) IN s /\ (x2,k2) IN s /\ ~((x1,k1) = (x2,k2))
                       ==> (interior(k1) INTER interior(k2) = {}))`;;

let tagged_division_of = new_definition
  `s tagged_division_of i <=>
        s tagged_partial_division_of i /\ (UNIONS {k | ?x. (x,k) IN s} = i)`;;

let TAGGED_DIVISION_OF_FINITE = prove
 (`!s i. s tagged_division_of i ==> FINITE s`,
  SIMP_TAC[tagged_division_of; tagged_partial_division_of]);;

let TAGGED_DIVISION_OF = prove
 (`s tagged_division_of i <=>
        FINITE s /\
        (!x k. (x,k) IN s
               ==> x IN k /\ k SUBSET i /\ ?a b. k = interval[a,b]) /\
        (!x1 k1 x2 k2. (x1,k1) IN s /\ (x2,k2) IN s /\ ~((x1,k1) = (x2,k2))
                       ==> (interior(k1) INTER interior(k2) = {})) /\
        (UNIONS {k | ?x. (x,k) IN s} = i)`,
  REWRITE_TAC[tagged_division_of; tagged_partial_division_of; CONJ_ASSOC]);;

let DIVISION_OF_TAGGED_DIVISION = prove
 (`!s i. s tagged_division_of i ==> (IMAGE SND s) division_of i`,
  REWRITE_TAC[TAGGED_DIVISION_OF; division_of] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; FORALL_PAIR_THM; PAIR_EQ] THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNIONS] THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

let PARTIAL_DIVISION_OF_TAGGED_DIVISION = prove
 (`!s i. s tagged_partial_division_of i
         ==> (IMAGE SND s) division_of UNIONS(IMAGE SND s)`,
  REWRITE_TAC[tagged_partial_division_of; division_of] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; DE_MORGAN_THM] THEN
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE];
    ALL_TAC;
    ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[MEMBER_NOT_EMPTY]] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; EXISTS_PAIR_THM] THEN
  CONV_TAC(ONCE_DEPTH_CONV UNWIND_CONV) THEN ASM SET_TAC[]);;

let TAGGED_PARTIAL_DIVISION_SUBSET = prove
 (`!s t i. s tagged_partial_division_of i /\ t SUBSET s
           ==> t tagged_partial_division_of i`,
  REWRITE_TAC[tagged_partial_division_of] THEN
  MESON_TAC[FINITE_SUBSET; SUBSET]);;

let VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA = prove
 (`!d:(real^M->bool)->real^N p i.
        p tagged_partial_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`,
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\(x:real^M,k:real^M->bool). d k:real^N) = d o SND`
  SUBST1_TAC THENL [SIMP_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:real^M->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^M` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k':real^M->bool` THEN
  ASM_CASES_TAC `k':real^M->bool = k` THEN
  ASM_REWRITE_TAC[PAIR_EQ; INTER_ACI] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[]);;

let VSUM_OVER_TAGGED_DIVISION_LEMMA = prove
 (`!d:(real^M->bool)->real^N p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`,
  REWRITE_TAC[tagged_division_of] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA THEN
  EXISTS_TAC `i:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let SUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA = prove
 (`!d:(real^N->bool)->real p i.
        p tagged_partial_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[tagged_partial_division_of]) THEN
  ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  ASM_SIMP_TAC[LIFT_SUM; FINITE_IMAGE; o_DEF; LAMBDA_PAIR_THM] THEN
  MATCH_MP_TAC VSUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA THEN
  ASM_SIMP_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_MESON_TAC[]);;

let SUM_OVER_TAGGED_DIVISION_LEMMA = prove
 (`!d:(real^N->bool)->real p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`,
  REWRITE_TAC[tagged_division_of] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUM_OVER_TAGGED_PARTIAL_DIVISION_LEMMA THEN
  EXISTS_TAC `i:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let TAG_IN_INTERVAL = prove
 (`!p i k. p tagged_division_of i /\ (x,k) IN p ==> x IN i`,
  REWRITE_TAC[TAGGED_DIVISION_OF] THEN SET_TAC[]);;

let TAGGED_DIVISION_OF_EMPTY = prove
 (`{} tagged_division_of {}`,
  REWRITE_TAC[tagged_division_of; tagged_partial_division_of] THEN
  REWRITE_TAC[FINITE_RULES; EXTENSION; NOT_IN_EMPTY; IN_UNIONS; IN_ELIM_THM]);;

let TAGGED_PARTIAL_DIVISION_OF_TRIVIAL = prove
 (`!p. p tagged_partial_division_of {} <=> p = {}`,
  REWRITE_TAC[tagged_partial_division_of; SUBSET_EMPTY; CONJ_ASSOC] THEN
  REWRITE_TAC[SET_RULE `x IN k /\ k = {} <=> F`] THEN
  REWRITE_TAC[GSYM FORALL_PAIR_THM; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
  REWRITE_TAC[AC CONJ_ACI `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FINITE_RULES; UNIONS_0; NOT_IN_EMPTY]);;

let TAGGED_DIVISION_OF_TRIVIAL = prove
 (`!p. p tagged_division_of {} <=> p = {}`,
  REWRITE_TAC[tagged_division_of; TAGGED_PARTIAL_DIVISION_OF_TRIVIAL] THEN
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b <=> a)`) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN SET_TAC[]);;

let TAGGED_DIVISION_OF_SELF = prove
 (`!x a b. x IN interval[a,b]
           ==> {(x,interval[a,b])} tagged_division_of interval[a,b]`,
  REWRITE_TAC[TAGGED_DIVISION_OF; FINITE_INSERT; FINITE_RULES; IN_SING] THEN
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL; UNWIND_THM2; SET_RULE `{k | k = a} = {a}`] THEN
  REWRITE_TAC[UNIONS_1] THEN ASM_MESON_TAC[]);;

let TAGGED_DIVISION_UNION = prove
 (`!s1 s2:real^N->bool p1 p2.
        p1 tagged_division_of s1 /\
        p2 tagged_division_of s2 /\
        interior s1 INTER interior s2 = {}
        ==> (p1 UNION p2) tagged_division_of (s1 UNION s2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[TAGGED_DIVISION_OF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION; EXISTS_OR_THM; SET_RULE
   `UNIONS {x | P x \/ Q x} = UNIONS {x | P x} UNION UNIONS {x | Q x}`] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC;
    ONCE_REWRITE_TAC[INTER_COMM]; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC(SET_RULE
   `!s' t'. s SUBSET s' /\ t SUBSET t' /\ s' INTER t' = {}
            ==> s INTER t = {}`) THEN
  MAP_EVERY EXISTS_TAC
   [`interior s1:real^N->bool`; `interior s2:real^N->bool`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
  ASM_MESON_TAC[]);;

let TAGGED_DIVISION_UNIONS = prove
 (`!iset pfn. FINITE iset /\
              (!i:real^M->bool. i IN iset ==> pfn(i) tagged_division_of i) /\
              (!i1 i2. i1 IN iset /\ i2 IN iset /\ ~(i1 = i2)
                       ==> (interior(i1) INTER interior(i2) = {}))
              ==> UNIONS(IMAGE pfn iset) tagged_division_of (UNIONS iset)`,
  let lemma1 = prove
    (`(?t. (?x. (t = f x) /\ P x) /\ Q t) <=> ?x. P x /\ Q(f x)`,
     MESON_TAC[])
  and lemma2 = prove
   (`!s1 t1 s2 t2. s1 SUBSET t1 /\ s2 SUBSET t2 /\ (t1 INTER t2 = {})
                   ==> (s1 INTER s2 = {})`,
    SET_TAC[]) in
  REPEAT GEN_TAC THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[EXTENSION] tagged_division_of] THEN
  REWRITE_TAC[tagged_partial_division_of; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS; IN_IMAGE] THEN
  SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC; ASM_MESON_TAC[]] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[lemma1] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i1:real^M->bool`; `i2:real^M->bool`] THEN
  ASM_CASES_TAC `i1 = i2:real^M->bool` THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma2 THEN
  MAP_EVERY EXISTS_TAC
   [`interior(i1:real^M->bool)`; `interior(i2:real^M->bool)`] THEN
  ASM_MESON_TAC[SUBSET; SUBSET_INTERIOR]);;

let TAGGED_PARTIAL_DIVISION_OF_UNION_SELF = prove
 (`!p s. p tagged_partial_division_of s
         ==> p tagged_division_of (UNIONS(IMAGE SND p))`,
  SIMP_TAC[tagged_partial_division_of; TAGGED_DIVISION_OF] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; EXISTS_PAIR_THM] THEN
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

let TAGGED_DIVISION_OF_UNION_SELF = prove
 (`!p s. p tagged_division_of s
         ==> p tagged_division_of (UNIONS(IMAGE SND p))`,
  SIMP_TAC[TAGGED_DIVISION_OF] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(c ==> a /\ b) /\ c ==> a /\ b /\ c`) THEN CONJ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[]]);;

let TAGGED_DIVISION_OF_ALT = prove
 (`!p s. p tagged_division_of s <=>
         p tagged_partial_division_of s /\
         (!x. x IN s ==> ?t k. (t,k) IN p /\ x IN k)`,
  REWRITE_TAC[tagged_division_of; GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_PAIR_THM; IN_ELIM_THM] THEN
  REWRITE_TAC[tagged_partial_division_of; SUBSET] THEN MESON_TAC[]);;

let TAGGED_DIVISION_OF_ANOTHER = prove
 (`!p s s'.
        p tagged_partial_division_of s' /\
        (!t k. (t,k) IN p ==> k SUBSET s) /\
        (!x. x IN s ==> ?t k. (t,k) IN p /\ x IN k)
        ==> p tagged_division_of s`,
  REWRITE_TAC[TAGGED_DIVISION_OF_ALT; tagged_partial_division_of] THEN
  SET_TAC[]);;

let TAGGED_PARTIAL_DIVISION_OF_SUBSET = prove
 (`!p s t. p tagged_partial_division_of s /\ s SUBSET t
           ==> p tagged_partial_division_of t`,
  REWRITE_TAC[tagged_partial_division_of] THEN SET_TAC[]);;

let TAGGED_DIVISION_OF_NONTRIVIAL = prove
 (`!s a b:real^N.
        s tagged_division_of interval[a,b] /\ ~(content(interval[a,b]) = &0)
        ==> {(x,k) | (x,k) IN s /\ ~(content k = &0)}
            tagged_division_of interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TAGGED_DIVISION_OF_ALT] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_SUBSET THEN
    EXISTS_TAC `s:(real^N#(real^N->bool))->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[tagged_division_of]) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
    DISCH_THEN(MP_TAC o
     MATCH_MP(REWRITE_RULE[IMP_CONJ] DIVISION_OF_NONTRIVIAL)) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_THM;
                GSYM CONJ_ASSOC] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Fine-ness of a partition w.r.t. a gauge.                                  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("fine",(12,"right"));;

let fine = new_definition
  `d fine s <=> !x k. (x,k) IN s ==> k SUBSET d(x)`;;

let FINE_INTER = prove
 (`!p d1 d2. (\x. d1(x) INTER d2(x)) fine p <=> d1 fine p /\ d2 fine p`,
  let lemma = prove
   (`s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,SET_TAC[]) in
  REWRITE_TAC[fine; IN_INTER; lemma] THEN MESON_TAC[]);;

let FINE_INTERS = prove
 (`!f s p. (\x. INTERS {f d x | d IN s}) fine p <=>
           !d. d IN s ==> (f d) fine p`,
  REWRITE_TAC[fine; SET_RULE `s SUBSET INTERS u <=> !t. t IN u ==> s SUBSET t`;
              IN_ELIM_THM] THEN MESON_TAC[]);;

let FINE_UNION = prove
 (`!d p1 p2. d fine p1 /\ d fine p2 ==> d fine (p1 UNION p2)`,
  REWRITE_TAC[fine; IN_UNION] THEN MESON_TAC[]);;

let FINE_UNIONS = prove
 (`!d ps. (!p. p IN ps ==> d fine p) ==> d fine (UNIONS ps)`,
  REWRITE_TAC[fine; IN_UNIONS] THEN MESON_TAC[]);;

let FINE_SUBSET = prove
 (`!d p q. p SUBSET q /\ d fine q ==> d fine p`,
  REWRITE_TAC[fine; SUBSET] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Gauge integral. Define on compact intervals first, then use a limit.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_integral_compact_interval",(12,"right"));;
parse_as_infix("has_integral",(12,"right"));;
parse_as_infix("integrable_on",(12,"right"));;

let has_integral_compact_interval = new_definition
  `(f has_integral_compact_interval y) i <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p. p tagged_division_of i /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) - y) < e`;;

let has_integral_def = new_definition
  `(f has_integral y) i <=>
        if ?a b. i = interval[a,b] then (f has_integral_compact_interval y) i
        else !e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball(vec 0,B) SUBSET interval[a,b]
                               ==> ?z. ((\x. if x IN i then f(x) else vec 0)
                                        has_integral_compact_interval z)
                                        (interval[a,b]) /\
                                       norm(z - y) < e`;;

let has_integral = prove
 (`(f has_integral y) (interval[a,b]) <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p. p tagged_division_of interval[a,b] /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) - y) < e`,
  REWRITE_TAC[has_integral_def; has_integral_compact_interval] THEN
  MESON_TAC[]);;

let has_integral_alt = prove
 (`(f has_integral y) i <=>
        if ?a b. i = interval[a,b] then (f has_integral y) i
        else !e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball(vec 0,B) SUBSET interval[a,b]
                               ==> ?z. ((\x. if x IN i then f(x) else vec 0)
                                        has_integral z) (interval[a,b]) /\
                                       norm(z - y) < e`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_integral_def] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [POP_ASSUM(REPEAT_TCL CHOOSE_THEN SUBST1_TAC); ALL_TAC] THEN
  REWRITE_TAC[has_integral_compact_interval; has_integral]);;

let integrable_on = new_definition
 `f integrable_on i <=> ?y. (f has_integral y) i`;;

let integral = new_definition
 `integral i f = @y. (f has_integral y) i`;;

let INTEGRABLE_INTEGRAL = prove
 (`!f i. f integrable_on i ==> (f has_integral (integral i f)) i`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable_on; integral] THEN
  CONV_TAC(RAND_CONV SELECT_CONV) THEN REWRITE_TAC[]);;

let HAS_INTEGRAL_INTEGRABLE = prove
 (`!f i s. (f has_integral i) s ==> f integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[]);;

let HAS_INTEGRAL_INTEGRAL = prove
 (`!f s. f integrable_on s <=> (f has_integral (integral s f)) s`,
  MESON_TAC[INTEGRABLE_INTEGRAL; HAS_INTEGRAL_INTEGRABLE]);;

let VSUM_CONTENT_NULL = prove
 (`!f:real^M->real^N a b p.
        content(interval[a,b]) = &0 /\
        p tagged_division_of interval[a,b]
        ==> vsum p (\(x,k). content k % f x) = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M`; `k:real^M->bool`] THEN
  DISCH_TAC THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL [`p:real^M`; `k:real^M->bool`]) THEN
  ASM_MESON_TAC[CONTENT_SUBSET; CONTENT_POS_LE; REAL_ARITH
   `&0 <= x /\ x <= y /\ y = &0 ==> x = &0`]);;

(* ------------------------------------------------------------------------- *)
(* Some basic combining lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_UNIONS_EXISTS = prove
 (`!d iset i:real^M->bool.
        FINITE iset /\
        (!i. i IN iset ==> ?p. p tagged_division_of i /\ d fine p) /\
        (!i1 i2. i1 IN iset /\ i2 IN iset /\ ~(i1 = i2)
                 ==> (interior(i1) INTER interior(i2) = {})) /\
        (UNIONS iset = i)
        ==> ?p. p tagged_division_of i /\ d fine p`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  EXISTS_TAC `UNIONS (IMAGE(p:(real^M->bool)->((real^M#(real^M->bool))->bool))
                      iset)` THEN
  ASM_SIMP_TAC[TAGGED_DIVISION_UNIONS] THEN
  ASM_MESON_TAC[FINE_UNIONS; IN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* The set we're concerned with must be closed.                              *)
(* ------------------------------------------------------------------------- *)

let DIVISION_OF_CLOSED = prove
 (`!s i. s division_of i ==> closed i`,
  REWRITE_TAC[division_of] THEN MESON_TAC[CLOSED_UNIONS; CLOSED_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* General bisection principle for intervals; might be useful elsewhere.     *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_BISECTION_STEP = prove
 (`!P. P {} /\
       (!s t. P s /\ P t /\ interior(s) INTER interior(t) = {}
              ==> P(s UNION t))
       ==> !a b:real^N.
                ~(P(interval[a,b]))
                ==> ?c d. ~(P(interval[c,d])) /\
                          !i. 1 <= i /\ i <= dimindex(:N)
                              ==> a$i <= c$i /\ c$i <= d$i /\ d$i <= b$i /\
                                  &2 * (d$i - c$i) <= b$i - a$i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `!i. 1 <= i /\ i <= dimindex(:N)
                     ==> (a:real^N)$i <= (b:real^N)$i` THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INTERVAL_NE_EMPTY]) THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!f. FINITE f /\
        (!s:real^N->bool. s IN f ==> P s) /\
        (!s:real^N->bool. s IN f ==> ?a b. s = interval[a,b]) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t)
               ==> interior(s) INTER interior(t) = {})
        ==> P(UNIONS f)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[UNIONS_0; UNIONS_INSERT; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
    REWRITE_TAC[IMP_IMP] THEN REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
      FIRST_X_ASSUM MATCH_MP_TAC THEN STRIP_ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{ interval[c,d] |
      !i. 1 <= i /\ i <= dimindex(:N)
          ==> ((c:real^N)$i = (a:real^N)$i) /\ (d$i = (a$i + b$i) / &2) \/
              (c$i = (a$i + b$i) / &2) /\ ((d:real^N)$i = (b:real^N)$i)}`) THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN ANTS_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\s. closed_interval
       [(lambda i. if i IN s then (a:real^N)$i else (a$i + b$i) / &2):real^N,
        (lambda i. if i IN s then (a$i + b$i) / &2 else (b:real^N)$i)])
         {s | s SUBSET (1..dimindex(:N))}` THEN
    CONJ_TAC THENL
     [SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE; FINITE_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `k:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N` (X_CHOOSE_THEN `d:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    EXISTS_TAC `{i | 1 <= i /\ i <= dimindex(:N) /\
                     ((c:real^N)$i = (a:real^N)$i)}` THEN
    CONJ_TAC THENL [ALL_TAC; SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]] THEN
    AP_TERM_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; IN_ELIM_THM] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN `i:num` o SPEC `i:num`)) THEN
    REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~P(interval[a:real^N,b])` THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[UNWIND_THM2; IN_INTERVAL] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
    REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))`) THEN
    STRIP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `(a \/ b) /\ c <=> ~(a ==> ~c) \/ ~(b ==> ~c)`] THEN
    SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `~(a ==> ~b) <=> a /\ b`; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[EXISTS_OR_THM; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MATCH_MP_TAC(TAUT `b /\ (~a ==> e) /\ c ==> ~(a /\ b /\ c) ==> e`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_IMP; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`c1:real^N`; `d1:real^N`; `c2:real^N`; `d2:real^N`] THEN
  ASM_CASES_TAC `(c1 = c2:real^N) /\ (d1 = d2:real^N)` THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN MP_TAC th) THEN
  REWRITE_TAC[IMP_IMP] THEN
  UNDISCH_TAC `~((c1 = c2:real^N) /\ (d1 = d2:real^N))` THEN
  REWRITE_TAC[CART_EQ; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` (fun th ->
    DISCH_THEN(MP_TAC o SPEC `j:num`) THEN MP_TAC th)) THEN
  REWRITE_TAC[NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[EXTENSION; IN_INTERVAL; NOT_IN_EMPTY; IN_INTER] THEN
  SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_EQ_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[
    REAL_ARITH `~((a * &2 = a + b) /\ (a + b = b * &2)) <=> ~(a = b)`;
    REAL_ARITH `~((a + b = a * &2) /\ (b * &2 = a + b)) <=> ~(a = b)`] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `x:real^N` THEN MP_TAC th) THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> (a ==> b /\ c)`] THEN
  ASM_REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let INTERVAL_BISECTION = prove
 (`!P. P {} /\
       (!s t. P s /\ P t /\ interior(s) INTER interior(t) = {}
              ==> P(s UNION t))
       ==> !a b:real^N.
                ~(P(interval[a,b]))
                ==> ?x. x IN interval[a,b] /\
                        !e. &0 < e
                            ==> ?c d. x IN interval[c,d] /\
                                      interval[c,d] SUBSET ball(x,e) /\
                                      interval[c,d] SUBSET interval[a,b] /\
                                      ~P(interval[c,d])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?A B. (A(0) = a:real^N) /\ (B(0) = b) /\
          !n. ~(P(interval[A(SUC n),B(SUC n)])) /\
              !i. 1 <= i /\ i <= dimindex(:N)
                       ==> A(n)$i <= A(SUC n)$i /\
                           A(SUC n)$i <= B(SUC n)$i /\
                           B(SUC n)$i <= B(n)$i /\
                           &2 * (B(SUC n)$i - A(SUC n)$i) <= B(n)$i - A(n)$i`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `P:(real^N->bool)->bool` INTERVAL_BISECTION_STEP) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `C:real^N->real^N->real^N`
     (X_CHOOSE_THEN `D:real^N->real^N->real^N` ASSUME_TAC)) THEN
    MP_TAC(prove_recursive_functions_exist num_RECURSION
     `(E 0 = a:real^N,b:real^N) /\
      (!n. E(SUC n) = C (FST(E n)) (SND(E n)),
                      D (FST(E n)) (SND(E n)))`) THEN
    DISCH_THEN(X_CHOOSE_THEN `E:num->real^N#real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\n. FST((E:num->real^N#real^N) n)` THEN
    EXISTS_TAC `\n. SND((E:num->real^N#real^N) n)` THEN
    ASM_REWRITE_TAC[] THEN INDUCT_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. &0 < e
        ==> ?n:num. !x y. x IN interval[A(n),B(n)] /\ y IN interval[A(n),B(n)]
                          ==> dist(x,y:real^N) < e`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(SPEC
     `sum(1..dimindex(:N)) (\i. (b:real^N)$i - (a:real^N)$i) / e`
     REAL_ARCH_POW2) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))(\i. abs((x - y:real^N)$i))` THEN
    REWRITE_TAC[dist; NORM_LE_L1] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N))
                   (\i. (B:num->real^N)(n)$i - (A:num->real^N)(n)$i)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `a <= x /\ x <= b /\ a <= y /\ y <= b
                               ==> abs(x - y) <= b - a`) THEN
      UNDISCH_TAC `x IN interval[(A:num->real^N) n,B n]` THEN
      UNDISCH_TAC `y IN interval[(A:num->real^N) n,B n]` THEN
      REWRITE_TAC[IN_INTERVAL] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\i. (b:real^N)$i - (a:real^N)$i) /
      &2 pow n` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ]] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    SPEC_TAC(`n:num`,`m:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[real_pow; REAL_DIV_1; REAL_LE_REFL] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_MESON_TAC[REAL_LE_TRANS; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. !n:num. a IN interval[A(n),B(n)]` MP_TAC THENL
   [MATCH_MP_TAC DECREASING_CLOSED_NEST THEN
    ASM_REWRITE_TAC[CLOSED_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN
      ASM_MESON_TAC[REAL_NOT_LT; REAL_LE_TRANS];
      ALL_TAC] THEN
    REWRITE_TAC[LE_EXISTS] THEN SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[GSYM LEFT_IMP_EXISTS_THM; EXISTS_REFL] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUBSET_REFL] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[A(m + d:num):real^N,B(m + d)]` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x0:real^N` THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC [`(A:num->real^N) n`; `(B:num->real^N) n`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN ASM_MESON_TAC[];
    ALL_TAC;
    SPEC_TAC(`n:num`,`p:num`) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `!m n. m <= n ==> interval[(A:num->real^N) n,B n] SUBSET interval[A m,B m]`
   (fun th -> ASM_MESON_TAC[SUBSET; LE_0; th]) THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[SUBSET_INTERVAL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cousin's lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let FINE_DIVISION_EXISTS = prove
 (`!g a b:real^M.
        gauge g ==> ?p. p tagged_division_of (interval[a,b]) /\ g fine p`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\s:real^M->bool. ?p. p tagged_division_of s /\ g fine p`
        INTERVAL_BISECTION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [MESON_TAC[TAGGED_DIVISION_UNION; FINE_UNION;
              TAGGED_DIVISION_OF_EMPTY; fine; NOT_IN_EMPTY];
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`])] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^M` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^M` o REWRITE_RULE[gauge]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL; NOT_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{(x:real^M,interval[c:real^M,d])}`) THEN
  ASM_SIMP_TAC[TAGGED_DIVISION_OF_SELF] THEN
  REWRITE_TAC[fine; IN_SING; PAIR_EQ] THEN ASM_MESON_TAC[SUBSET_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Basic theorems about integrals.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_UNIQUE = prove
 (`!f:real^M->real^N i k1 k2.
        (f has_integral k1) i /\ (f has_integral k2) i ==> k1 = k2`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!f:real^M->real^N a b k1 k2.
       (f has_integral k1) (interval[a,b]) /\
       (f has_integral k2) (interval[a,b])
       ==> k1 = k2`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_integral] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN
    REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM NORM_POS_LT] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `norm(k1 - k2 :real^N) / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPEC `\x. ((d1:real^M->real^M->bool) x) INTER (d2 x)`
                 FINE_DIVISION_EXISTS) THEN
    ASM_SIMP_TAC[GAUGE_INTER] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_forall o concl))) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[IMP_IMP; NOT_EXISTS_THM] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN
    MATCH_MP_TAC(TAUT
     `(f0 ==> f1 /\ f2) /\ ~(n1 /\ n2)
      ==> (t /\ f1 ==> n1) /\ (t /\ f2 ==> n2) ==> ~(t /\ f0)`) THEN
    CONJ_TAC THENL [SIMP_TAC[fine; SUBSET_INTER]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `c <= a + b ==> ~(a < c / &2 /\ b < c / &2)`) THEN
    MESON_TAC[NORM_SUB; NORM_TRIANGLE; VECTOR_ARITH
     `k1 - k2:real^N = (k1 - x) + (x - k2)`];
    ALL_TAC] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
   `~(&0 < norm(x - y)) ==> x = y`) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `norm(k1 - k2:real^N) / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
   `ball(vec 0,B1) UNION ball(vec 0:real^M,B2)`
   BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_UNION; BOUNDED_BALL; UNION_SUBSET; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `w:real^N = z:real^N` SUBST_ALL_TAC THEN
  ASM_MESON_TAC[NORM_ARITH
   `~(norm(z - k1) < norm(k1 - k2) / &2 /\
      norm(z - k2) < norm(k1 - k2) / &2)`]);;

let INTEGRAL_UNIQUE = prove
 (`!f y k.
      (f has_integral y) k ==> integral k f = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[HAS_INTEGRAL_UNIQUE]);;

let HAS_INTEGRAL_INTEGRABLE_INTEGRAL = prove
 (`!f:real^M->real^N i s.
        (f has_integral i) s <=> f integrable_on s /\ integral s f = i`,
  MESON_TAC[INTEGRABLE_INTEGRAL; INTEGRAL_UNIQUE; integrable_on]);;

let INTEGRAL_EQ_HAS_INTEGRAL = prove
 (`!s f y. f integrable_on s ==> (integral s f = y <=> (f has_integral y) s)`,
  MESON_TAC[INTEGRABLE_INTEGRAL; INTEGRAL_UNIQUE]);;

let HAS_INTEGRAL_IS_0 = prove
 (`!f:real^M->real^N s.
        (!x. x IN s ==> (f(x) = vec 0)) ==> (f has_integral vec 0) s`,
  SUBGOAL_THEN
   `!f:real^M->real^N a b.
        (!x. x IN interval[a,b] ==> (f(x) = vec 0))
        ==> (f has_integral vec 0) (interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[has_integral] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^M. ball(x,&1)` THEN
    SIMP_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    UNDISCH_TAC `&0 < e` THEN MATCH_MP_TAC(TAUT `(a <=> b) ==> b ==> a`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ; VECTOR_ADD_LID] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `x:real^M` THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN interval[a,b]`
     (fun th -> ASM_SIMP_TAC[th; VECTOR_MUL_RZERO]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tagged_division_of]) THEN
    REWRITE_TAC[tagged_partial_division_of; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `vec 0:real^N` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let HAS_INTEGRAL_0 = prove
 (`!s. ((\x. vec 0) has_integral vec 0) s`,
  SIMP_TAC[HAS_INTEGRAL_IS_0]);;

let HAS_INTEGRAL_0_EQ = prove
 (`!i s. ((\x. vec 0) has_integral i) s <=> i = vec 0`,
  MESON_TAC[HAS_INTEGRAL_UNIQUE; HAS_INTEGRAL_0]);;

let HAS_INTEGRAL_LINEAR = prove
 (`!f:real^M->real^N y s h:real^N->real^P.
        (f has_integral y) s /\ linear h ==> ((h o f) has_integral h(y)) s`,
  SUBGOAL_THEN
    `!f:real^M->real^N y a b h:real^N->real^P.
          (f has_integral y) (interval[a,b]) /\ linear h
          ==> ((h o f) has_integral h(y)) (interval[a,b])`
  MP_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_integral] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real / B`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^M#(real^M->bool)->bool`) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
    FIRST_ASSUM(fun th -> W(fun (asl,w) ->
      MP_TAC(PART_MATCH rand th (rand w)))) THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= e ==> x <= e`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[LINEAR_SUB; LINEAR_VSUM; o_DEF; LAMBDA_PAIR_THM;
                 LINEAR_CMUL; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP
    LINEAR_BOUNDED_POS) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / B:real`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:real` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(h:real^N->real^P) z` THEN
  SUBGOAL_THEN
   `(\x. if x IN s then ((h:real^N->real^P) o (f:real^M->real^N)) x else vec 0)
    = h o (\x. if x IN s then f x else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[LINEAR_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `B * norm(z - y:real^N)` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]);;

let HAS_INTEGRAL_CMUL = prove
 (`!(f:real^M->real^N) k s c.
        (f has_integral k) s
        ==> ((\x. c % f(x)) has_integral (c % k)) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[linear] THEN CONJ_TAC THEN VECTOR_ARITH_TAC);;

let HAS_INTEGRAL_NEG = prove
 (`!f k s. (f has_integral k) s ==> ((\x. --(f x)) has_integral (--k)) s`,
  ONCE_REWRITE_TAC[VECTOR_NEG_MINUS1] THEN REWRITE_TAC[HAS_INTEGRAL_CMUL]);;

let HAS_INTEGRAL_ADD = prove
 (`!f:real^M->real^N g s.
        (f has_integral k) s /\ (g has_integral l) s
        ==> ((\x. f(x) + g(x)) has_integral (k + l)) s`,
  SUBGOAL_THEN
   `!f:real^M->real^N g k l a b.
        (f has_integral k) (interval[a,b]) /\
        (g has_integral l) (interval[a,b])
        ==> ((\x. f(x) + g(x)) has_integral (k + l)) (interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[has_integral; AND_FORALL_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `\x. ((d1:real^M->real^M->bool) x) INTER (d2 x)` THEN
    ASM_SIMP_TAC[GAUGE_INTER] THEN
    REWRITE_TAC[tagged_division_of; tagged_partial_division_of] THEN
    SIMP_TAC[VSUM_ADD; VECTOR_ADD_LDISTRIB; LAMBDA_PAIR] THEN
    REWRITE_TAC[GSYM LAMBDA_PAIR] THEN
    REWRITE_TAC[GSYM tagged_partial_division_of] THEN
    REWRITE_TAC[GSYM tagged_division_of; FINE_INTER] THEN
    SIMP_TAC[VECTOR_ARITH `(a + b) - (c + d) = (a - c) + (b - d):real^N`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_TRIANGLE_LT THEN
    MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B1 B2:real` THEN ASM_REWRITE_TAC[REAL_LT_MAX] THEN
  REWRITE_TAC[BALL_MAX_UNION; UNION_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `w + z:real^N` THEN
  SUBGOAL_THEN
    `(\x. if x IN s then (f:real^M->real^N) x + g x else vec 0) =
     (\x. (if x IN s then f x else vec 0) + (if x IN s then g x else vec 0))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
  NORM_ARITH_TAC);;

let HAS_INTEGRAL_SUB = prove
 (`!f:real^M->real^N g s.
        (f has_integral k) s /\ (g has_integral l) s
        ==> ((\x. f(x) - g(x)) has_integral (k - l)) s`,
  SIMP_TAC[VECTOR_SUB; HAS_INTEGRAL_NEG; HAS_INTEGRAL_ADD]);;

let INTEGRAL_0 = prove
 (`!s. integral s (\x. vec 0) = vec 0`,
  MESON_TAC[INTEGRAL_UNIQUE; HAS_INTEGRAL_0]);;

let INTEGRAL_ADD = prove
 (`!f:real^M->real^N g k l s.
        f integrable_on s /\ g integrable_on s
        ==> integral s (\x. f x + g x) = integral s f + integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_CMUL = prove
 (`!f:real^M->real^N c s.
        f integrable_on s ==> integral s (\x. c % f(x)) = c % integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_NEG = prove
 (`!f:real^M->real^N s.
        f integrable_on s ==> integral s (\x. --f(x)) = --integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_NEG THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_SUB = prove
 (`!f:real^M->real^N g k l s.
        f integrable_on s /\ g integrable_on s
        ==> integral s (\x. f x - g x) = integral s f - integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_SUB THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRABLE_0 = prove
 (`!s. (\x. vec 0) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_0]);;

let INTEGRABLE_ADD = prove
 (`!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> (\x. f x + g x) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_ADD]);;

let INTEGRABLE_CMUL = prove
 (`!f:real^M->real^N c s.
        f integrable_on s ==> (\x. c % f(x)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_CMUL]);;

let INTEGRABLE_NEG = prove
 (`!f:real^M->real^N s.
        f integrable_on s ==> (\x. --f(x)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_NEG]);;

let INTEGRABLE_SUB = prove
 (`!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s
        ==> (\x. f x - g x) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_SUB]);;

let INTEGRABLE_LINEAR = prove
 (`!f h s. f integrable_on s /\ linear h ==> (h o f) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_LINEAR]);;

let INTEGRAL_LINEAR = prove
 (`!f:real^M->real^N s h:real^N->real^P.
        f integrable_on s /\ linear h
        ==> integral s (h o f) = h(integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_UNIQUE THEN
  MAP_EVERY EXISTS_TAC
   [`(h:real^N->real^P) o (f:real^M->real^N)`; `s:real^M->bool`] THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_INTEGRAL_LINEAR] THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_LINEAR]);;

let HAS_INTEGRAL_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> ((f a) has_integral (i a)) s)
        ==> ((\x. vsum t (\a. f a x)) has_integral (vsum t i)) s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; HAS_INTEGRAL_0; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_ADD THEN
  ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

let INTEGRAL_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) integrable_on s)
        ==> integral s (\x. vsum t (\a. f a x)) =
                vsum t (\a. integral s (f a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRABLE_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) integrable_on s)
        ==>  (\x. vsum t (\a. f a x)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_VSUM]);;

let HAS_INTEGRAL_EQ = prove
 (`!f:real^M->real^N g k s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        (f has_integral k) s
        ==> (g has_integral k) s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP HAS_INTEGRAL_IS_0) MP_TAC) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  SIMP_TAC[VECTOR_ARITH `x - (x - y:real^N) = y`; ETA_AX; VECTOR_SUB_RZERO]);;

let INTEGRABLE_EQ = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> (f(x) = g(x))) /\
        f integrable_on s
        ==> g integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_EQ]);;

let HAS_INTEGRAL_EQ_EQ = prove
 (`!f:real^M->real^N g k s.
        (!x. x IN s ==> (f(x) = g(x)))
        ==> ((f has_integral k) s <=> (g has_integral k) s)`,
  MESON_TAC[HAS_INTEGRAL_EQ]);;

let HAS_INTEGRAL_NULL = prove
 (`!f:real^M->real^N a b.
    content(interval[a,b]) = &0 ==> (f has_integral vec 0) (interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_integral] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 < e ==> x < e`) THEN
  ASM_REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[VSUM_CONTENT_NULL]);;

let HAS_INTEGRAL_NULL_EQ = prove
 (`!f a b i. content(interval[a,b]) = &0
             ==> ((f has_integral i) (interval[a,b]) <=> i = vec 0)`,
  ASM_MESON_TAC[INTEGRAL_UNIQUE; HAS_INTEGRAL_NULL]);;

let INTEGRAL_NULL = prove
 (`!f a b. content(interval[a,b]) = &0
           ==> integral(interval[a,b]) f = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_MESON_TAC[HAS_INTEGRAL_NULL]);;

let INTEGRABLE_ON_NULL = prove
 (`!f a b. content(interval[a,b]) = &0
           ==> f integrable_on interval[a,b]`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_NULL]);;

let HAS_INTEGRAL_EMPTY = prove
 (`!f. (f has_integral vec 0) {}`,
  MESON_TAC[HAS_INTEGRAL_NULL; CONTENT_EMPTY; EMPTY_AS_INTERVAL]);;

let HAS_INTEGRAL_EMPTY_EQ = prove
 (`!f i. (f has_integral i) {} <=> i = vec 0`,
  MESON_TAC[HAS_INTEGRAL_UNIQUE; HAS_INTEGRAL_EMPTY]);;

let INTEGRABLE_ON_EMPTY = prove
 (`!f. f integrable_on {}`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_EMPTY]);;

let INTEGRAL_EMPTY = prove
 (`!f. integral {} f = vec 0`,
  MESON_TAC[EMPTY_AS_INTERVAL; INTEGRAL_UNIQUE; HAS_INTEGRAL_EMPTY]);;

let HAS_INTEGRAL_REFL = prove
 (`!f a. (f has_integral vec 0) (interval[a,a])`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
  SIMP_TAC[INTERVAL_SING; INTERIOR_CLOSED_INTERVAL; CONTENT_EQ_0_INTERIOR]);;

let INTEGRABLE_ON_REFL = prove
 (`!f a. f integrable_on interval[a,a]`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_REFL]);;

let INTEGRAL_REFL = prove
 (`!f a. integral (interval[a,a]) f = vec 0`,
  MESON_TAC[INTEGRAL_UNIQUE; HAS_INTEGRAL_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type criterion for integrability.                                  *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CAUCHY = prove
 (`!f:real^M->real^N a b.
    f integrable_on interval[a,b] <=>
        !e. &0 < e
            ==> ?d. gauge d /\
                    !p1 p2. p1 tagged_division_of interval[a,b] /\ d fine p1 /\
                            p2 tagged_division_of interval[a,b] /\ d fine p2
                            ==> norm(vsum p1 (\(x,k). content k % f x) -
                                     vsum p2 (\(x,k). content k % f x)) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integrable_on; has_integral] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` (MP_TAC o SPEC `e / &2`)) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real^M->real^M->bool` THEN
    REWRITE_TAC[GSYM dist] THEN MESON_TAC[DIST_TRIANGLE_HALF_L];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real^M->real^M->bool` MP_TAC) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  MP_TAC(GEN `n:num`
   (ISPECL [`\x. INTERS {(d:num->real^M->real^M->bool) i x | i IN 0..n}`;
            `a:real^M`; `b:real^M`]
     FINE_DIVISION_EXISTS)) THEN
  ASM_SIMP_TAC[GAUGE_INTERS; FINE_INTERS; FINITE_NUMSEG; SKOLEM_THM] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->(real^M#(real^M->bool))->bool`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `cauchy (\n. vsum (p n)
                   (\(x,k:real^M->bool). content k % (f:real^M->real^N) x))`
  MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
     [MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&m + &1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY; LIM_SEQUENTIALLY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[dist] THEN STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN EXISTS_TAC
   `(d:num->real^M->real^M->bool) (N1 + N2)` THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `q:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_L THEN
  EXISTS_TAC `vsum (p(N1+N2:num))
                  (\(x,k:real^M->bool). content k % (f:real^M->real^N) x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `inv(&(N1 + N2) + &1)` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&N1)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Additivity of integral on abutting intervals.                             *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_SPLIT = prove
 (`!a b:real^N c k.
    1 <= k /\ k <= dimindex(:N)
    ==> interval[a,b] INTER {x | x$k <= c} =
        interval[a,(lambda i. if i = k then min (b$k) c else b$i)] /\
        interval[a,b] INTER {x | x$k >= c} =
        interval[(lambda i. if i = k then max (a$k) c else a$i),b]`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_INTER; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `y:real^N` THEN
  MATCH_MP_TAC(TAUT `(c ==> b) /\ (c ==> a) /\ (a /\ b ==> c)
                     ==> (a /\ b <=> c)`) THEN
  (CONJ_TAC THENL
    [ASM_MESON_TAC[REAL_MAX_LE; REAL_LE_MIN; real_ge];  ALL_TAC]) THEN
  REWRITE_TAC[LEFT_AND_FORALL_THM; real_ge] THEN CONJ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN ASM_MESON_TAC[REAL_MAX_LE; REAL_LE_MIN]);;

let CONTENT_SPLIT = prove
 (`!a b:real^N k.
    1 <= k /\ k <= dimindex(:N)
    ==> content(interval[a,b]) =
        content(interval[a,b] INTER {x | x$k <= c}) +
        content(interval[a,b] INTER {x | x$k >= c})`,
  SIMP_TAC[INTERVAL_SPLIT; CONTENT_CLOSED_INTERVAL_CASES; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ARITH
   `((a <= if p then b else c) <=> (p ==> a <= b) /\ (~p ==> a <= c)) /\
    ((if p then b else c) <= a <=> (p ==> b <= a) /\ (~p ==> c <= a))`] THEN
  REWRITE_TAC[REAL_LE_MIN; REAL_MAX_LE] THEN
  REWRITE_TAC[MESON[] `(i = k ==> p i k) <=> (i = k ==> p i i)`] THEN
  REWRITE_TAC[TAUT `(p ==> a /\ b) /\ (~p ==> a) <=> a /\ (p ==> b)`] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `!i. 1 <= i /\ i <= dimindex(:N) ==> (a:real^N)$i <= (b:real^N)$i` THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  REWRITE_TAC[MESON[] `(!i. P i ==> i = k ==> Q i) <=> (P k ==> Q k)`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `min b c = if c <= b then c else b`;
              REAL_ARITH `max a c = if a <= c then c else a`] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
  REWRITE_TAC[MESON[] `(if i = k then a k else a i) = a i`] THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL]] THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `p'' = p /\ p':real = p
    ==> (b - a) * p = (c - a) * p' + (b - c) * p''`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_DELETE]);;

let DIVISION_SPLIT_LEFT_INJ,DIVISION_SPLIT_RIGHT_INJ = (CONJ_PAIR o prove)
 (`(!d i k1 k2 k c.
        d division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        k1 IN d /\ k2 IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k <= c} = k2 INTER {x | x$k <= c}
        ==> content(k1 INTER {x:real^N | x$k <= c}) = &0) /\
   (!d i k1 k2 k c.
        d division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        k1 IN d /\ k2 IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k >= c} = k2 INTER {x | x$k >= c}
        ==> content(k1 INTER {x:real^N | x$k >= c}) = &0)`,
  let lemma = prove
   (`!a b:real^N c k.
      1 <= k /\ k <= dimindex(:N)
      ==> (content(interval[a,b] INTER {x | x$k <= c}) = &0 <=>
           interior(interval[a,b] INTER {x | x$k <= c}) = {}) /\
          (content(interval[a,b] INTER {x | x$k >= c}) = &0 <=>
           interior(interval[a,b] INTER {x | x$k >= c}) = {})`,
    SIMP_TAC[INTERVAL_SPLIT; CONTENT_EQ_0_INTERIOR]) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (MP_TAC o CONJUNCT1) o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`k1:real^N->bool`; `k2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[PAIR_EQ] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `k2:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `v:real^N`
    SUBST_ALL_TAC)) THEN
  ASM_SIMP_TAC[lemma] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s INTER t = {}
    ==> u SUBSET s /\ u SUBSET t ==> u = {}`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]);;

let TAGGED_DIVISION_SPLIT_LEFT_INJ = prove
 (`!d i x1 k1 x2 k2 k c.
        d tagged_division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        (x1,k1) IN d /\ (x2,k2) IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k <= c} = k2 INTER {x | x$k <= c}
        ==> content(k1 INTER {x:real^N | x$k <= c}) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
  MATCH_MP_TAC DIVISION_SPLIT_LEFT_INJ THEN
  EXISTS_TAC `IMAGE SND (d:(real^N#(real^N->bool))->bool)` THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[SND]);;

let TAGGED_DIVISION_SPLIT_RIGHT_INJ = prove
 (`!d i x1 k1 x2 k2 k c.
        d tagged_division_of i /\ 1 <= k /\ k <= dimindex(:N) /\
        (x1,k1) IN d /\ (x2,k2) IN d /\ ~(k1 = k2) /\
        k1 INTER {x | x$k >= c} = k2 INTER {x | x$k >= c}
        ==> content(k1 INTER {x:real^N | x$k >= c}) = &0`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
  MATCH_MP_TAC DIVISION_SPLIT_RIGHT_INJ THEN
  EXISTS_TAC `IMAGE SND (d:(real^N#(real^N->bool))->bool)` THEN
  ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[SND]);;

let DIVISION_SPLIT = prove
 (`!p a b:real^N k c.
     p division_of interval[a,b] /\ 1 <= k /\ k <= dimindex(:N)
     ==> {l INTER {x | x$k <= c} |l| l IN p /\ ~(l INTER {x | x$k <= c} = {})}
         division_of (interval[a,b] INTER {x | x$k <= c}) /\
         {l INTER {x | x$k >= c} |l| l IN p /\ ~(l INTER {x | x$k >= c} = {})}
         division_of (interval[a,b] INTER {x | x$k >= c})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  SIMP_TAC[division_of; FINITE_IMAGE] THEN
  SIMP_TAC[SET_RULE `(!x. x IN {f x | P x} ==> Q x) <=> (!x. P x ==> Q (f x))`;
           MESON[] `(!x y. x IN s /\ y IN t /\ Q x y ==> P x y) <=>
                    (!x. x IN s ==> !y. y IN t ==> Q x y ==> P x y)`;
           RIGHT_FORALL_IMP_THM] THEN
  REPEAT(MATCH_MP_TAC(TAUT
   `(a ==> a' /\ a'') /\ (b ==> b' /\ b'')
      ==> a /\ b ==> (a' /\ b') /\ (a'' /\ b'')`) THEN CONJ_TAC)
  THENL
   [ONCE_REWRITE_TAC[SET_RULE
    `{f x |x| x IN s /\ ~(f x = {})} = {y | y IN IMAGE f s /\ ~(y = {})}`] THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE];
    REWRITE_TAC[AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `l:real^N->bool` THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
    (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN
     CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
     STRIP_TAC THEN ASM_MESON_TAC[INTERVAL_SPLIT]);
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
    (REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
     REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
     DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
     ANTS_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
     MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t'
       ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
     CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]);
   DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INTER_UNIONS] THEN
   ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS] THEN
   CONJ_TAC THEN GEN_TAC THEN AP_TERM_TAC THEN
   GEN_REWRITE_TAC I [FUN_EQ_THM] THEN GEN_TAC THEN
   REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[NOT_IN_EMPTY]]);;

let HAS_INTEGRAL_SPLIT = prove
 (`!f:real^M->real^N k a b c.
      (f has_integral i) (interval[a,b] INTER {x | x$k <= c}) /\
      (f has_integral j) (interval[a,b] INTER {x | x$k >= c}) /\
      1 <= k /\ k <= dimindex(:M)
      ==> (f has_integral (i + j)) (interval[a,b])`,
  let lemma1 = prove
   (`(!x k. (x,k) IN {x,f k | P x k} ==> Q x k) <=>
     (!x k. P x k ==> Q x (f k))`,
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    SET_TAC[]) in
  let lemma2 = prove
   (`!f:B->B s:(A#B)->bool.
      FINITE s ==> FINITE {x,f k | (x,k) IN s /\ P x k}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\(x:A,k:B). x,(f k:B)) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; lemma1; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]) in
  let lemma3 = prove
   (`!f:real^M->real^N g:(real^M->bool)->(real^M->bool) p.
     FINITE p
     ==> vsum {x,g k |x,k| (x,k) IN p /\ ~(g k = {})}
              (\(x,k). content k % f x) =
         vsum (IMAGE (\(x,k). x,g k) p) (\(x,k). content k % f x)`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE; lemma2] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM; SUBSET; IN_IMAGE; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; VECTOR_MUL_EQ_0] THEN
    MESON_TAC[CONTENT_EMPTY]) in
  let lemma4 = prove
   (`(\(x,l). content (g l) % f x) =
     (\(x,l). content l % f x) o (\(x,l). x,g l)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `1 <= k /\ k <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN REWRITE_TAC[has_integral] THEN
  ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &2`) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I1"))) THEN
  EXISTS_TAC `\x. if x$k = c then (d1(x:real^M) INTER d2(x)):real^M->bool
                  else ball(x,abs(x$k - c)) INTER d1(x) INTER d2(x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[gauge] THEN GEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; OPEN_BALL; IN_BALL] THEN
    ASM_REWRITE_TAC[DIST_REFL; GSYM REAL_ABS_NZ; REAL_SUB_0];
    ALL_TAC] THEN
  X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(!x:real^M kk. (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})
                    ==> x$k <= c) /\
     (!x:real^M kk. (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})
                    ==> x$k >= c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `kk:real^M->bool` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; real_ge] THEN DISCH_THEN
     (MP_TAC o MATCH_MP (SET_RULE `k SUBSET (a INTER b) ==> k SUBSET a`)) THEN
    REWRITE_TAC[SUBSET; IN_BALL; dist] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M` MP_TAC) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((x - u:real^M)$k)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "I2" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k >= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})}`) THEN
  REMOVE_THEN "I1" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k <= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})}`) THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b) /\ (a' /\ b' ==> c) ==> (a ==> a') ==> (b ==> b') ==> c`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    REPEAT(MATCH_MP_TAC(TAUT
     `(a ==> (a' /\ a'')) /\ (b ==> (b' /\ d) /\ (b'' /\ e))
      ==> a /\ b ==> ((a' /\ b') /\ d) /\ ((a'' /\ b'') /\ e)`) THEN
      CONJ_TAC) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[lemma1] THEN REWRITE_TAC[IMP_IMP] THENL
     [SIMP_TAC[lemma2];
      REWRITE_TAC[AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `kk:real^M->bool` THEN
      DISCH_THEN(fun th -> CONJ_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
      (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
        [SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
      (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
      ASM_MESON_TAC[INTERVAL_SPLIT];
      DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
      (REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
       DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
       REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
       DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
       ANTS_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
       MATCH_MP_TAC(SET_RULE
        `s SUBSET s' /\ t SUBSET t'
         ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
       CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]);
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b /\ c) /\ d /\ e
                       ==> (a ==> (b /\ d) /\ (c /\ e))`) THEN
    CONJ_TAC THENL
     [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INTER_UNIONS] THEN
      ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS] THEN
      X_GEN_TAC `x:real^M` THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `kk:real^M->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    REWRITE_TAC[fine; lemma1] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &2 /\ y < e / &2 ==> x + y < e`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP NORM_TRIANGLE_LT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a - i) + (b - j) = c - (i + j) <=> a + b = c:real^N`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
 MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum p (\(x,l). content (l INTER {x:real^M | x$k <= c}) %
                     (f:real^M->real^N) x) +
    vsum p (\(x,l). content (l INTER {x:real^M | x$k >= c}) %
                     (f:real^M->real^N) x)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GSYM VSUM_ADD] THEN MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM; GSYM VECTOR_ADD_RDISTRIB] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`] o
               el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CONTENT_SPLIT]] THEN
  ASM_SIMP_TAC[lemma3] THEN BINOP_TAC THEN
  (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lemma4] THEN
   MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
   REWRITE_TAC[PAIR_EQ] THEN
   ASM_MESON_TAC[TAGGED_DIVISION_SPLIT_LEFT_INJ; VECTOR_MUL_LZERO;
                 TAGGED_DIVISION_SPLIT_RIGHT_INJ]));;

(* ------------------------------------------------------------------------- *)
(* A sort of converse, integrability on subintervals.                        *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_UNION_INTERVAL = prove
 (`!a b:real^N p1 p2 c k.
        1 <= k /\ k <= dimindex(:N) /\
        p1 tagged_division_of (interval[a,b] INTER {x | x$k <= c}) /\
        p2 tagged_division_of (interval[a,b] INTER {x | x$k >= c})
        ==> (p1 UNION p2) tagged_division_of (interval[a,b])`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `interval[a,b] = (interval[a,b] INTER {x:real^N | x$k <= c}) UNION
                    (interval[a,b] INTER {x:real^N | x$k >= c})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(t UNION u = UNIV) ==> s = (s INTER t) UNION (s INTER u)`) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC TAGGED_DIVISION_UNION THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTERIOR_CLOSED_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_INTERVAL] THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `k:num`)) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let HAS_INTEGRAL_SEPARATE_SIDES = prove
 (`!f:real^M->real^N i a b k.
        (f has_integral i) (interval[a,b]) /\
        1 <= k /\ k <= dimindex(:M)
        ==> !e. &0 < e
                ==> ?d. gauge d /\
                        !p1 p2. p1 tagged_division_of
                                     (interval[a,b] INTER {x | x$k <= c}) /\
                                d fine p1 /\
                                p2 tagged_division_of
                                     (interval[a,b] INTER {x | x$k >= c}) /\
                                d fine p2
                                ==> norm((vsum p1 (\(x,k). content k % f x) +
                                          vsum p2 (\(x,k). content k % f x)) -
                                         i) < e`,
  REWRITE_TAC[has_integral] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
  ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum p1 (\(x,k). content k % f x) + vsum p2 (\(x,k). content k % f x) =
    vsum (p1 UNION p2) (\(x,k:real^M->bool). content k % (f:real^M->real^N) x)`
  SUBST1_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[TAGGED_DIVISION_UNION_INTERVAL; FINE_UNION]] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
   [TAGGED_DIVISION_OF])) THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
  REWRITE_TAC[IN_INTER; VECTOR_MUL_EQ_0] THEN STRIP_TAC THEN DISJ1_TAC THEN
  SUBGOAL_THEN
   `(?a b:real^M. l = interval[a,b]) /\
    l SUBSET (interval[a,b] INTER {x | x$k <= c}) /\
    l SUBSET (interval[a,b] INTER {x | x$k >= c})`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[SET_RULE
   `s SUBSET t /\ s SUBSET u <=> s SUBSET (t INTER u)`] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTER_INTERVAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUBSET_INTERIOR) THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; CONTENT_EQ_0_INTERIOR] THEN
  MATCH_MP_TAC(SET_RULE `t = {} ==> s SUBSET t ==> s = {}`) THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN EXISTS_TAC `k:num` THEN
  ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let INTEGRABLE_SPLIT = prove
 (`!f:real^M->real^N a b.
        f integrable_on (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:M)
        ==> f integrable_on (interval[a,b] INTER {x | x$k <= c}) /\
            f integrable_on (interval[a,b] INTER {x | x$k >= c})`,
  let lemma = prove
   (`b - a = c
     ==> norm(a:real^N) < e / &2 ==> norm(b) < e / &2 ==> norm(c) < e`,
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM dist] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DIST_TRIANGLE_HALF_L THEN
    EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[dist; VECTOR_SUB_LZERO; VECTOR_SUB_RZERO; NORM_NEG]) in
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [integrable_on] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN CONJ_TAC THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTEGRABLE_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2` o
    MATCH_MP HAS_INTEGRAL_SEPARATE_SIDES) THEN
  MAP_EVERY ABBREV_TAC
   [`b' = (lambda i. if i = k then min ((b:real^M)$k) c else b$i):real^M`;
    `a' = (lambda i. if i = k then max ((a:real^M)$k) c else a$i):real^M`] THEN
  ASM_SIMP_TAC[REAL_HALF; INTERVAL_SPLIT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THENL
   [DISCH_THEN(MP_TAC o SPECL [`a':real^M`; `b:real^M`]) THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[SWAP_FORALL_THM]);
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b':real^M`])] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M#(real^M->bool))->bool`
    STRIP_ASSUME_TAC) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`p:(real^M#(real^M->bool))->bool`;
                  `p1:(real^M#(real^M->bool))->bool`] th) THEN
    MP_TAC(SPECL [`p:(real^M#(real^M->bool))->bool`;
                  `p2:(real^M#(real^M->bool))->bool`] th)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lemma THEN VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Generalized notion of additivity.                                         *)
(* ------------------------------------------------------------------------- *)

let operative = new_definition
 `operative op (f:(real^N->bool)->A) <=>
    (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = neutral(op)) /\
    (!a b c k. 1 <= k /\ k <= dimindex(:N)
               ==> f(interval[a,b]) =
                   op (f(interval[a,b] INTER {x | x$k <= c}))
                      (f(interval[a,b] INTER {x | x$k >= c})))`;;

let OPERATIVE_TRIVIAL = prove
 (`!op f a b.
        operative op f /\ content(interval[a,b]) = &0
        ==> f(interval[a,b]) = neutral op`,
  REWRITE_TAC[operative] THEN MESON_TAC[]);;

let PROPERTY_EMPTY_INTERVAL = prove
 (`!P. (!a b:real^N. content(interval[a,b]) = &0 ==> P(interval[a,b]))
       ==> P {}`,
  MESON_TAC[EMPTY_AS_INTERVAL; CONTENT_EMPTY]);;

let OPERATIVE_EMPTY = prove
 (`!op f:(real^N->bool)->A. operative op f ==> f {} = neutral op`,
  REPEAT GEN_TAC THEN REWRITE_TAC[operative] THEN
  DISCH_THEN(ACCEPT_TAC o MATCH_MP PROPERTY_EMPTY_INTERVAL o CONJUNCT1));;

(* ------------------------------------------------------------------------- *)
(* Using additivity of lifted function to encode definedness.                *)
(* ------------------------------------------------------------------------- *)

let FORALL_OPTION = prove
 (`(!x. P x) <=> P NONE /\ !x. P(SOME x)`,
  MESON_TAC[cases "option"]);;

let EXISTS_OPTION = prove
 (`(?x. P x) <=> P NONE \/ ?x. P(SOME x)`,
  MESON_TAC[cases "option"]);;

let lifted = define
 `(lifted op NONE _ = NONE) /\
  (lifted op _ NONE = NONE) /\
  (lifted op (SOME x) (SOME y) = SOME(op x y))`;;

let NEUTRAL_LIFTED = prove
 (`!op. monoidal op ==> neutral(lifted op) = SOME(neutral op)`,
  REWRITE_TAC[neutral; monoidal] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN
  REWRITE_TAC[FORALL_OPTION; lifted; distinctness "option";
              injectivity "option"] THEN
  ASM_MESON_TAC[]);;

let MONOIDAL_LIFTED = prove
 (`!op. monoidal op ==> monoidal(lifted op)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[NEUTRAL_LIFTED; monoidal] THEN
  REWRITE_TAC[FORALL_OPTION; lifted; distinctness "option";
              injectivity "option"] THEN
  ASM_MESON_TAC[monoidal]);;

let ITERATE_SOME = prove
 (`!op. monoidal op
        ==> !f s. FINITE s
                  ==> iterate (lifted op) s (\x. SOME(f x)) =
                      SOME(iterate op s f)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_LIFTED; NEUTRAL_LIFTED] THEN
  REWRITE_TAC[lifted]);;

(* ------------------------------------------------------------------------- *)
(* Two key instances of additivity.                                          *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_CONTENT = prove
 (`operative(+) content`,
  REWRITE_TAC[operative; NEUTRAL_REAL_ADD; CONTENT_SPLIT]);;

let OPERATIVE_INTEGRAL = prove
 (`!f:real^M->real^N.
       operative(lifted(+))
         (\i. if f integrable_on i then SOME(integral i f) else NONE)`,
  SIMP_TAC[operative; NEUTRAL_LIFTED; MONOIDAL_VECTOR_ADD] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[lifted; distinctness "option"; injectivity "option"] THENL
   [REWRITE_TAC[integral] THEN ASM_MESON_TAC[HAS_INTEGRAL_NULL_EQ];
    RULE_ASSUM_TAC(REWRITE_RULE[integrable_on]) THEN
    ASM_MESON_TAC[HAS_INTEGRAL_NULL];
    REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL)) THEN
    ASM_MESON_TAC[HAS_INTEGRAL_SPLIT; HAS_INTEGRAL_UNIQUE];
    ASM_MESON_TAC[INTEGRABLE_SPLIT; integrable_on];
    ASM_MESON_TAC[INTEGRABLE_SPLIT];
    ASM_MESON_TAC[INTEGRABLE_SPLIT];
    RULE_ASSUM_TAC(REWRITE_RULE[integrable_on]) THEN
    ASM_MESON_TAC[HAS_INTEGRAL_SPLIT]]);;

(* ------------------------------------------------------------------------- *)
(* Points of division of a partition.                                        *)
(* ------------------------------------------------------------------------- *)

let division_points = new_definition
 `division_points (k:real^N->bool) (d:(real^N->bool)->bool) =
    {j,x | 1 <= j /\ j <= dimindex(:N) /\
           (interval_lowerbound k)$j < x /\ x < (interval_upperbound k)$j /\
           ?i. i IN d /\
               ((interval_lowerbound i)$j = x \/
                (interval_upperbound i)$j = x)}`;;

let DIVISION_POINTS_FINITE = prove
 (`!d i:real^N->bool. d division_of i ==> FINITE(division_points i d)`,
  REWRITE_TAC[division_of; division_points] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONJ_ASSOC; GSYM IN_NUMSEG] THEN
  REWRITE_TAC[IN; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IN] FINITE_PRODUCT_DEPENDENT) THEN
  REWRITE_TAC[ETA_AX; FINITE_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
   `IMAGE (\i:real^N->bool. (interval_lowerbound i)$j) d UNION
    IMAGE (\i:real^N->bool. (interval_upperbound i)$j) d` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[IN]);;

let DIVISION_POINTS_SUBSET = prove
 (`!a b:real^N c d k.
        d division_of interval[a,b] /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i) /\
        1 <= k /\ k <= dimindex(:N) /\ a$k < c /\ c < b$k
        ==> division_points (interval[a,b] INTER {x | x$k <= c})
                            {l INTER {x | x$k <= c} | l |
                             l IN d /\ ~(l INTER {x | x$k <= c} = {})}
            SUBSET division_points (interval[a,b]) d /\
            division_points (interval[a,b] INTER {x | x$k >= c})
                            {l INTER {x | x$k >= c} | l |
                             l IN d /\ ~(l INTER {x | x$k >= c} = {})}
            SUBSET division_points (interval[a,b]) d`,
  REPEAT STRIP_TAC THEN
  (REWRITE_TAC[SUBSET; division_points; FORALL_PAIR_THM] THEN
   MAP_EVERY X_GEN_TAC [`j:num`; `x:real`] THEN
   REWRITE_TAC[IN_ELIM_PAIR_THM] THEN REWRITE_TAC[IN_ELIM_THM] THEN
   ASM_SIMP_TAC[INTERVAL_SPLIT; INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
                REAL_LT_IMP_LE] THEN
   ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
                REAL_ARITH `c < b ==> min b c = c`] THEN
   REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; LAMBDA_BETA;
     REAL_LT_IMP_LE; COND_ID;
     TAUT `(a <= if p then x else y) <=> (if p then a <= x else a <= y)`;
     TAUT `(if p then x else y) <= a <=> (if p then x <= a else y <= a)`] THEN
   REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
    [DISCH_THEN(K ALL_TAC) THEN REPEAT(POP_ASSUM MP_TAC) THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     ALL_TAC] THEN
   REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
   MATCH_MP_TAC MONO_EXISTS THEN
   ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ c <=> b /\ a /\ c`] THEN
   REWRITE_TAC[UNWIND_THM2] THEN SIMP_TAC[GSYM CONJ_ASSOC] THEN
   ONCE_REWRITE_TAC[IMP_CONJ] THEN
   FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
   MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
   ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
   SUBGOAL_THEN
    `!i. 1 <= i /\ i <= dimindex(:N) ==> (u:real^N)$i <= (v:real^N)$i`
   ASSUME_TAC THENL
    [REWRITE_TAC[GSYM INTERVAL_NE_EMPTY] THEN ASM_MESON_TAC[division_of];
     ALL_TAC] THEN
   REWRITE_TAC[INTERVAL_NE_EMPTY] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND] THEN
   ASM_SIMP_TAC[LAMBDA_BETA] THEN REPEAT(POP_ASSUM MP_TAC) THEN
   COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC));;

let DIVISION_POINTS_PSUBSET = prove
 (`!a b:real^N c d k.
        d division_of interval[a,b] /\
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i) /\
        1 <= k /\ k <= dimindex(:N) /\ a$k < c /\ c < b$k /\
        (?l. l IN d /\
             (interval_lowerbound l$k = c \/ interval_upperbound l$k = c))
        ==> division_points (interval[a,b] INTER {x | x$k <= c})
                            {l INTER {x | x$k <= c} | l |
                             l IN d /\ ~(l INTER {x | x$k <= c} = {})}
            PSUBSET division_points (interval[a,b]) d /\
            division_points (interval[a,b] INTER {x | x$k >= c})
                            {l INTER {x | x$k >= c} | l |
                             l IN d /\ ~(l INTER {x | x$k >= c} = {})}
            PSUBSET division_points (interval[a,b]) d`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[PSUBSET_MEMBER; DIVISION_POINTS_SUBSET] THENL
   [EXISTS_TAC `k,(interval_lowerbound l:real^N)$k`;
    EXISTS_TAC `k,(interval_lowerbound l:real^N)$k`;
    EXISTS_TAC `k,(interval_upperbound l:real^N)$k`;
    EXISTS_TAC `k,(interval_upperbound l:real^N)$k`] THEN
  ASM_REWRITE_TAC[division_points; IN_ELIM_PAIR_THM] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
               REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
               REAL_ARITH `c < b ==> min b c = c`] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; LAMBDA_BETA;
    REAL_LT_IMP_LE; COND_ID;
    TAUT `(a <= if p then x else y) <=> (if p then a <= x else a <= y)`;
    TAUT `(if p then x else y) <= a <=> (if p then x <= a else y <= a)`] THEN
  REWRITE_TAC[REAL_LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Preservation by divisions and tagged divisions.                           *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_DIVISION = prove
 (`!op d a b f:(real^N->bool)->A.
    monoidal op /\ operative op f /\ d division_of interval[a,b]
    ==> iterate(op) d f = f(interval[a,b])`,
  REPEAT GEN_TAC THEN CONV_TAC(RAND_CONV SYM_CONV) THEN WF_INDUCT_TAC
   `CARD (division_points (interval[a,b]:real^N->bool) d)` THEN
  POP_ASSUM(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `content(interval[a:real^N,b]) = &0` THENL
   [SUBGOAL_THEN `iterate op d (f:(real^N->bool)->A) = neutral op`
     (fun th -> ASM_MESON_TAC[th; operative]) THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     ITERATE_EQ_NEUTRAL) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    ASM_MESON_TAC[operative; DIVISION_OF_CONTENT_0];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_CASES_TAC `division_points (interval[a,b]:real^N->bool) d = {}` THENL
   [DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN
     `!i. i IN d
          ==> ?u v:real^N. i = interval[u,v] /\
                           !j. 1 <= j /\ j <= dimindex(:N)
                               ==> u$j = (a:real^N)$j /\ v$j = a$j \/
                                   u$j = (b:real^N)$j /\ v$j = b$j \/
                                   u$j = a$j /\ v$j = b$j`
    (LABEL_TAC "*") THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`u:real^N`; `v:real^N`] THEN REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `interval[u:real^N,v]` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[INTERVAL_NE_EMPTY] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (ASSUME_TAC o CONJUNCT1)) THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `a <= u /\ u <= v /\ v <= b /\ ~(a < u /\ u < b \/ a < v /\ v < b)
        ==> u = a /\ v = a \/ u = b /\ v = b \/ u = a /\ v = b`) THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[division_points; NOT_IN_EMPTY; FORALL_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `interval[u:real^N,v]`) THEN
      ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
                   REAL_LT_IMP_LE] THEN
      DISCH_THEN(fun th ->
        MP_TAC(SPEC `(u:real^N)$j` th) THEN
        MP_TAC(SPEC `(v:real^N)$j` th)) THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN MP_TAC) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `interval[a:real^N,b] IN d` MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_UNIONS] THEN
      DISCH_THEN(MP_TAC o SPEC `inv(&2) % (a + b:real^N)`) THEN
      MATCH_MP_TAC(TAUT `b /\ (a ==> c) ==> (a <=> b) ==> c`) THEN
      CONJ_TAC THENL
       [SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:real^N->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `i:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
      SIMP_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
      REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
      ASM_SIMP_TAC[REAL_ARITH
       `a < b
        ==> ((u = a /\ v = a \/ u = b /\ v = b \/ u = a /\ v = b) /\
             u <= inv(&2) * (a + b) /\ inv(&2) * (a +  b) <= v <=>
             u = a /\ v = b)`] THEN
      ASM_MESON_TAC[CART_EQ];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (SET_RULE
     `a IN d ==> d = a INSERT (d DELETE a)`)) THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN
     `iterate op (d DELETE interval[a,b]) (f:(real^N->bool)->A) = neutral op`
     (fun th -> ASM_MESON_TAC[th; monoidal]) THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     ITERATE_EQ_NEUTRAL) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:real^N->bool` THEN
    REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    SUBGOAL_THEN `content(l:real^N->bool) = &0`
     (fun th -> ASM_MESON_TAC[th; operative]) THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `l:real^N->bool`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    UNDISCH_TAC `~(interval[u:real^N,v] = interval[a,b])` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> AP_TERM_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[CONS_11; PAIR_EQ; CART_EQ; CONTENT_EQ_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [TAUT `a ==> b <=> ~a \/ b`] THEN
    REWRITE_TAC[NOT_FORALL_THM; OR_EXISTS_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; AND_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `1 <= j /\ j <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [division_points] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`whatever:num#real`; `k:num`; `c:real`] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real`; `d:(real^N->bool)->bool`;
        `k:num`] DIVISION_POINTS_PSUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o MATCH_MP (REWRITE_RULE [IMP_CONJ] CARD_PSUBSET))) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `k:num`;
                 `c:real`]
      DIVISION_SPLIT) THEN
  ASM_SIMP_TAC[DIVISION_POINTS_FINITE] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
  ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
               REAL_ARITH `c < b ==> min b c = c`] THEN
  MAP_EVERY ABBREV_TAC
   [`d1:(real^N->bool)->bool =
     {l INTER {x | x$k <= c} | l | l IN d /\ ~(l INTER {x | x$k <= c} = {})}`;
    `d2:(real^N->bool)->bool =
     {l INTER {x | x$k >= c} | l | l IN d /\ ~(l INTER {x | x$k >= c} = {})}`;
    `cb:real^N = (lambda i. if i = k then c else (b:real^N)$i)`;
    `ca:real^N = (lambda i. if i = k then c else (a:real^N)$i)`] THEN
  STRIP_TAC THEN STRIP_TAC THEN STRIP_TAC THEN DISCH_THEN(fun th ->
   MP_TAC(SPECL [`a:real^N`; `cb:real^N`; `d1:(real^N->bool)->bool`] th) THEN
   MP_TAC(SPECL [`ca:real^N`; `b:real^N`; `d2:(real^N->bool)->bool`] th)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `op (iterate op d1 (f:(real^N->bool)->A))
                 (iterate op d2 (f:(real^N->bool)->A))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [operative]) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `c:real`; `k:num`]) THEN
    ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
    ASM_SIMP_TAC[REAL_ARITH `a < c ==> max a c = c`;
                 REAL_ARITH `c < b ==> min b c = c`];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `op (iterate op d (\l. f(l INTER {x | x$k <= c}):A))
       (iterate op d (\l. f(l INTER {x:real^N | x$k >= c})))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GSYM ITERATE_OP] THEN
    MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
     ITERATE_EQ) THEN
    ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION
     (ASSUME `d division_of interval[a:real^N,b]`)] THEN
    ASM_MESON_TAC[operative]] THEN
  MAP_EVERY EXPAND_TAC ["d1"; "d2"] THEN BINOP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  MATCH_MP_TAC ITERATE_NONZERO_IMAGE_LEMMA THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[OPERATIVE_EMPTY]; ALL_TAC] THEN
   MAP_EVERY X_GEN_TAC [`l:real^N->bool`; `m:real^N->bool`] THEN STRIP_TAC THEN
   MATCH_MP_TAC(MESON[OPERATIVE_TRIVIAL]
    `operative op f /\ (?a b. l = interval[a,b]) /\ content l = &0
     ==> f l = neutral op`) THEN
   ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [ALL_TAC; ASM_MESON_TAC[DIVISION_SPLIT_LEFT_INJ;
                                 DIVISION_SPLIT_RIGHT_INJ]] THEN
   SUBGOAL_THEN `?a b:real^N. m = interval[a,b]` STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
   ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]));;

let OPERATIVE_TAGGED_DIVISION = prove
 (`!op d a b f:(real^N->bool)->A.
    monoidal op /\ operative op f /\ d tagged_division_of interval[a,b]
    ==> iterate(op) d (\(x,l). f l) = f(interval[a,b])`,
  let lemma = prove
   (`(\(x,l). f l) = (f o SND)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `iterate op (IMAGE SND (d:(real^N#(real^N->bool)->bool))) f :A` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[DIVISION_OF_TAGGED_DIVISION; OPERATIVE_DIVISION]] THEN
  REWRITE_TAC[lemma] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
               ITERATE_IMAGE_NONZERO) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF_FINITE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1 o CONJUNCT2)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[INTER_ACI] THEN
  ASM_MESON_TAC[CONTENT_EQ_0_INTERIOR; OPERATIVE_TRIVIAL;
                TAGGED_DIVISION_OF]);;

(* ------------------------------------------------------------------------- *)
(* Additivity of content.                                                    *)
(* ------------------------------------------------------------------------- *)

let ADDITIVE_CONTENT_DIVISION = prove
 (`!d a b:real^N.
    d division_of interval[a,b]
    ==> sum d content = content(interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  OPERATIVE_DIVISION)
     (CONJ MONOIDAL_REAL_ADD OPERATIVE_CONTENT))) THEN
  REWRITE_TAC[sum]);;

let ADDITIVE_CONTENT_TAGGED_DIVISION = prove
 (`!d a b:real^N.
    d tagged_division_of interval[a,b]
    ==> sum d (\(x,l). content l) = content(interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  OPERATIVE_TAGGED_DIVISION)
     (CONJ MONOIDAL_REAL_ADD OPERATIVE_CONTENT))) THEN
  REWRITE_TAC[sum]);;

let SUBADDITIVE_CONTENT_DIVISION = prove
 (`!d s a b:real^M.
        d division_of s /\ s SUBSET interval[a,b]
        ==> sum d content <= content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^M->bool)->bool`; `a:real^M`; `b:real^M`]
        PARTIAL_DIVISION_EXTEND_INTERVAL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN
    ASM_MESON_TAC[division_of; DIVISION_OF_UNION_SELF; SUBSET_TRANS];
    DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (p:(real^M->bool)->bool) content` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_MESON_TAC[division_of; CONTENT_POS_LE; IN_DIFF];
      ASM_MESON_TAC[ADDITIVE_CONTENT_DIVISION; REAL_LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Finally, the integral of a constant!                                      *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_CONST = prove
 (`!a b:real^M c:real^N.
    ((\x. c) has_integral (content(interval[a,b]) % c)) (interval[a,b])`,
  REWRITE_TAC[has_integral] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  FIRST_X_ASSUM(fun th ->
  ONCE_REWRITE_TAC[GSYM(MATCH_MP ADDITIVE_CONTENT_TAGGED_DIVISION th)]) THEN
  ASM_SIMP_TAC[VSUM_VMUL; GSYM VSUM_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; VECTOR_SUB_REFL] THEN
  ASM_REWRITE_TAC[GSYM LAMBDA_PAIR_THM; VSUM_0; NORM_0]);;

let INTEGRABLE_CONST = prove
 (`!a b:real^M c:real^N. (\x. c) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integrable_on] THEN
  EXISTS_TAC `content(interval[a:real^M,b]) % c:real^N` THEN
  REWRITE_TAC[HAS_INTEGRAL_CONST]);;

let INTEGRAL_CONST = prove
 (`!a b c. integral (interval[a,b]) (\x. c) = content(interval[a,b]) % c`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_INTEGRAL_CONST]);;

let INTEGRAL_PASTECART_CONST = prove
 (`!a b:real^M c d:real^N k:real^P.
     integral (interval[pastecart a c,pastecart b d]) (\x. k) =
     integral (interval[a,b])
              (\x. integral (interval[c,d]) (\y. k))`,
  REWRITE_TAC[INTEGRAL_CONST; CONTENT_PASTECART; VECTOR_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on the norm of Riemann sums and the integral itself.               *)
(* ------------------------------------------------------------------------- *)

let DSUM_BOUND = prove
 (`!p a b:real^M c:real^N e.
       p division_of interval[a,b] /\ norm(c) <= e
       ==> norm(vsum p (\l. content l % c)) <= e * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `y <= e ==> x <= y ==> x <= e`) THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum p (\k:real^M->bool. content k * e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    X_GEN_TAC `l:real^M->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(x) <= x`) THEN
    ASM_MESON_TAC[DIVISION_OF; CONTENT_POS_LE];
    REWRITE_TAC[SUM_RMUL; ETA_AX] THEN
    ASM_MESON_TAC[ADDITIVE_CONTENT_DIVISION; REAL_LE_REFL; REAL_MUL_SYM]]);;

let RSUM_BOUND = prove
 (`!p a b f:real^M->real^N e.
       p tagged_division_of interval[a,b] /\
       (!x. x IN interval[a,b] ==> norm(f x) <= e)
       ==> norm(vsum p (\(x,k). content k % f x))
            <= e * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `y <= e ==> x <= y ==> x <= e`) THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum p (\(x:real^M,k:real^M->bool). content k * e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE; REAL_ABS_REFL;
                    REAL_LE_REFL];
      ASM_MESON_TAC[TAG_IN_INTERVAL]];
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [GSYM(MATCH_MP ADDITIVE_CONTENT_TAGGED_DIVISION th)]) THEN
    REWRITE_TAC[GSYM SUM_LMUL; LAMBDA_PAIR_THM] THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

let RSUM_DIFF_BOUND = prove
 (`!p a b f g:real^M->real^N.
       p tagged_division_of interval[a,b] /\
       (!x. x IN interval[a,b] ==> norm(f x - g x) <= e)
       ==> norm(vsum p (\(x,k). content k % f x) -
                vsum p (\(x,k). content k % g x))
           <= e * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum p (\(x,k).
      content(k:real^M->bool) % ((f:real^M->real^N) x - g x)))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_SUB; VECTOR_SUB_LDISTRIB] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM; REAL_LE_REFL];
    ASM_SIMP_TAC[RSUM_BOUND]]);;

let HAS_INTEGRAL_BOUND = prove
 (`!f:real^M->real^N a b i B.
        &0 <= B /\
        (f has_integral i) (interval[a,b]) /\
        (!x. x IN interval[a,b] ==> norm(f x) <= B)
        ==> norm i <= B * content(interval[a,b])`,
  let lemma = prove
   (`norm(s) <= B ==> ~(norm(s - i) < norm(i) - B)`,
    MATCH_MP_TAC(REAL_ARITH `n1 <= n + n2 ==> n <= B ==> ~(n2 < n1 - B)`) THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[NORM_TRIANGLE_SUB]) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < content(interval[a:real^M,b])` THENL
   [ALL_TAC;
    SUBGOAL_THEN `i:real^N = vec 0` SUBST1_TAC THEN
    ASM_SIMP_TAC[REAL_LE_MUL; NORM_0; CONTENT_POS_LE] THEN
    ASM_MESON_TAC[HAS_INTEGRAL_NULL_EQ; CONTENT_LT_NZ]] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPEC
    `norm(i:real^N) - B * content(interval[a:real^M,b])`) THEN
  ASM_REWRITE_TAC[REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real^M->real^M->bool`; `a:real^M`; `b:real^M`]
        FINE_DIVISION_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN
   (X_CHOOSE_THEN `p:(real^M#(real^M->bool)->bool)` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool)->bool)`) THEN
  ASM_MESON_TAC[lemma; RSUM_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Similar theorems about relationship among components.                     *)
(* ------------------------------------------------------------------------- *)

let RSUM_COMPONENT_LE = prove
 (`!p a b f:real^M->real^N g:real^M->real^N.
       p tagged_division_of interval[a,b] /\ 1 <= i /\ i <= dimindex(:N) /\
       (!x. x IN interval[a,b] ==> (f x)$i <= (g x)$i)
       ==> vsum p (\(x,k). content k % f x)$i <=
           vsum p (\(x,k). content k % g x)$i`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[VSUM_COMPONENT] THEN
  MATCH_MP_TAC SUM_LE THEN
  ASM_SIMP_TAC[FORALL_PAIR_THM; VECTOR_MUL_COMPONENT] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  ASM_MESON_TAC[SUBSET; REAL_LE_LMUL; CONTENT_POS_LE]);;

let HAS_INTEGRAL_COMPONENT_LE = prove
 (`!f:real^M->real^N g:real^M->real^N s i j k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`,
  SUBGOAL_THEN
   `!f:real^M->real^N g:real^M->real^N a b i j k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) (interval[a,b]) /\
        (g has_integral j) (interval[a,b]) /\
        (!x. x IN interval[a,b] ==> (f x)$k <= (g x)$k)
        ==> i$k <= j$k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `~(&0 < i - j) ==> i <= j`) THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `((i:real^N)$k - (j:real^N)$k) / &3` o
       GEN_REWRITE_RULE I [has_integral])) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?p. p tagged_division_of interval[a:real^M,b] /\
                      d1 fine p /\ d2 fine p`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM FINE_INTER] THEN MATCH_MP_TAC FINE_DIVISION_EXISTS THEN
      ASM_SIMP_TAC[GAUGE_INTER];
      ALL_TAC] THEN
    REPEAT
     (FIRST_X_ASSUM(MP_TAC o SPEC `p:real^M#(real^M->bool)->bool`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
      DISCH_THEN(MP_TAC o SPEC `k:num` o MATCH_MP NORM_BOUND_COMPONENT_LE) THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT]) THEN
    SUBGOAL_THEN
     `vsum p (\(x,l:real^M->bool). content l % (f:real^M->real^N) x)$k <=
      vsum p (\(x,l). content l % (g:real^M->real^N) x)$k`
    MP_TAC THENL
     [MATCH_MP_TAC RSUM_COMPONENT_LE THEN ASM_MESON_TAC[];
      UNDISCH_TAC `&0 < (i:real^N)$k - (j:real^N)$k` THEN
      SPEC_TAC(`vsum p (\(x:real^M,l:real^M->bool).
                                content l % (f x):real^N)$k`,
               `fs:real`) THEN
      SPEC_TAC(`vsum p (\(x:real^M,l:real^M->bool).
                                content l % (g x):real^N)$k`,
               `gs:real`) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC
   `((i:real^N)$k - (j:real^N)$k) / &2`)) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC
   `ball(vec 0,B1) UNION ball(vec 0:real^M,B2)`
   BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_UNION; BOUNDED_BALL; UNION_SUBSET; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(z:real^N)$k <= (w:real^N)$k` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. if x IN s then f x else vec 0):real^M->real^N`;
      `(\x. if x IN s then g x else vec 0):real^M->real^N`;
      `a:real^M`; `b:real^M`] THEN
    ASM_MESON_TAC[REAL_LE_REFL];
    MP_TAC(ISPECL [`w - j:real^N`; `k:num`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`z - i:real^N`; `k:num`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; ASSUME `1 <= k`;
              ASSUME `k <= dimindex(:N)`] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
    NORM_ARITH_TAC]);;

let INTEGRAL_COMPONENT_LE = prove
 (`!f:real^M->real^N g:real^M->real^N s k.
        1 <= k /\ k <= dimindex(:N) /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> (f x)$k <= (g x)$k)
        ==> (integral s f)$k <= (integral s g)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_DROP_LE = prove
 (`!f:real^M->real^1 g:real^M->real^1 s i j.
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop i <= drop j`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_DROP_LE = prove
 (`!f:real^M->real^1 g:real^M->real^1 s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_COMPONENT_POS = prove
 (`!f:real^M->real^N s i k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\
        (!x. x IN s ==> &0 <= (f x)$k)
        ==> &0 <= i$k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. vec 0):real^M->real^N`; `f:real^M->real^N`;
                 `s:real^M->bool`; `vec 0:real^N`;
                 `i:real^N`; `k:num`] HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VEC_COMPONENT; HAS_INTEGRAL_0]);;

let INTEGRAL_COMPONENT_POS = prove
 (`!f:real^M->real^N s k.
        1 <= k /\ k <= dimindex(:N) /\
        f integrable_on s /\
        (!x. x IN s ==> &0 <= (f x)$k)
        ==> &0 <= (integral s f)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_POS THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_DROP_POS = prove
 (`!f:real^M->real^1 s i.
        (f has_integral i) s /\
        (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop i`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_POS THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_DROP_POS = prove
 (`!f:real^M->real^1 s.
        f integrable_on s /\
        (!x. x IN s ==> &0 <= drop(f x))
        ==> &0 <= drop(integral s f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_DROP_POS THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_COMPONENT_NEG = prove
 (`!f:real^M->real^N s i k.
        1 <= k /\ k <= dimindex(:N) /\
        (f has_integral i) s /\
        (!x. x IN s ==> (f x)$k <= &0)
        ==> i$k <= &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(\x. vec 0):real^M->real^N`;
                 `s:real^M->bool`; `i:real^N`; `vec 0:real^N`;
                 `k:num`] HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VEC_COMPONENT; HAS_INTEGRAL_0]);;

let HAS_INTEGRAL_DROP_NEG = prove
 (`!f:real^M->real^1 s i.
        (f has_integral i) s /\
        (!x. x IN s ==> drop(f x) <= &0)
        ==> drop i <= &0`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_NEG THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let HAS_INTEGRAL_COMPONENT_LBOUND = prove
 (`!f:real^M->real^N a b i k.
        (f has_integral i) (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> B <= f(x)$k)
        ==> B * content(interval[a,b]) <= i$k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(\x. lambda i. B):real^M->real^N`; `f:real^M->real^N`;
                 `interval[a:real^M,b]`;
                 `content(interval[a:real^M,b]) % (lambda i. B):real^N`;
                 `i:real^N`; `k:num`]
                HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; HAS_INTEGRAL_CONST] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let HAS_INTEGRAL_COMPONENT_UBOUND = prove
 (`!f:real^M->real^N a b i k.
        (f has_integral i) (interval[a,b]) /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f(x)$k <= B)
        ==> i$k <= B * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(\x. lambda i. B):real^M->real^N`;
                 `interval[a:real^M,b]`; `i:real^N`;
                 `content(interval[a:real^M,b]) % (lambda i. B):real^N`;
                 `k:num`]
                HAS_INTEGRAL_COMPONENT_LE) THEN
  ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; HAS_INTEGRAL_CONST] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let INTEGRAL_COMPONENT_LBOUND = prove
 (`!f:real^M->real^N a b k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> B <= f(x)$k)
        ==> B * content(interval[a,b]) <= (integral(interval[a,b]) f)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LBOUND THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let INTEGRAL_COMPONENT_UBOUND = prove
 (`!f:real^M->real^N a b k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN interval[a,b] ==> f(x)$k <= B)
        ==> (integral(interval[a,b]) f)$k <= B * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_UBOUND THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* Uniform limit of integrable functions is integrable.                      *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_UNIFORM_LIMIT = prove
 (`!f a b. (!e. &0 < e
                ==> ?g. (!x. x IN interval[a,b] ==> norm(f x - g x) <= e) /\
                        g integrable_on interval[a,b] )
           ==> (f:real^M->real^N) integrable_on interval[a,b]`,
  let lemma = prove
   (`x <= norm(a + b) + c ==> x <= norm(a) + norm(b) + c`,
    MESON_TAC[REAL_ADD_AC; NORM_TRIANGLE; REAL_LE_TRANS; REAL_LE_RADD]) in
  let (lemma1,lemma2) = (CONJ_PAIR o prove)
   (`(norm(s2 - s1) <= e / &2 /\
      norm(s1 - i1) < e / &4 /\ norm(s2 - i2) < e / &4
      ==> norm(i1 - i2) < e) /\
     (norm(sf - sg) <= e / &3
      ==> norm(i - s) < e / &3 ==> norm(sg - i) < e / &3 ==> norm(sf - s) < e)`,
    CONJ_TAC THENL
     [REWRITE_TAC[CONJ_ASSOC] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [NORM_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH
       `w <= x + y + z + &0
        ==> (x <= e / &2 /\ y < e / &4) /\ z < e / &4 ==> w < e`);
      MATCH_MP_TAC(REAL_ARITH
      `w <= x + y + z + &0
      ==> x <= e / &3 ==> y < e / &3 ==> z < e / &3 ==> w < e`)] THEN
    REPEAT(MATCH_MP_TAC lemma) THEN REWRITE_TAC[REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 < content(interval[a:real^M,b])` THENL
   [ALL_TAC;
    ASM_MESON_TAC[HAS_INTEGRAL_NULL; CONTENT_LT_NZ; integrable_on]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[FORALL_AND_THM; SKOLEM_THM; integrable_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` (CONJUNCTS_THEN2
   ASSUME_TAC (X_CHOOSE_TAC `i:num->real^N`))) THEN
  SUBGOAL_THEN `cauchy(i:num->real^N)` MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e / &4 / content(interval[a:real^M,b])`
        REAL_ARCH_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [has_integral]) THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `m:num` th) THEN
      MP_TAC(SPEC `n:num` th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `gn:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `gm:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`(\x. gm(x) INTER gn(x)):real^M->real^M->bool`;
                   `a:real^M`; `b:real^M`] FINE_DIVISION_EXISTS) THEN
    ASM_SIMP_TAC[GAUGE_INTER; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`)) THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[CONV_RULE(REWR_CONV FINE_INTER) th]) THEN
    SUBGOAL_THEN `norm(vsum p (\(x,k:real^M->bool). content k % g (n:num) x) -
                       vsum p (\(x:real^M,k). content k % g m x :real^N))
                  <= e / &2`
    MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[dist] THEN MESON_TAC[lemma1]] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 / &N * content(interval[a:real^M,b])` THEN CONJ_TAC THENL
     [MATCH_MP_TAC RSUM_DIFF_BOUND;
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPECL [`n:num`; `x:real^M`] th) THEN
      MP_TAC(SPECL [`m:num`; `x:real^M`] th)) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [NORM_SUB] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP NORM_TRIANGLE_LE) THEN
    MATCH_MP_TAC(REAL_ARITH `u = v /\ a <= inv(x) /\ b <= inv(x) ==>
                                u <= a + b ==> v <= &2 / x`) THEN
    CONJ_TAC THENL [AP_TERM_TAC THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3` o GEN_REWRITE_RULE I
   [LIM_SEQUENTIALLY]) THEN
  ASM_SIMP_TAC[dist; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `e / &3 / content(interval[a:real^M,b])` REAL_ARCH_INV) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPECL [`N1 + N2:num`; `e / &3`]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^M#(real^M->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `N1:num <= N1 + N2`)) THEN
  MATCH_MP_TAC lemma2 THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&(N1 + N2) + &1) * content(interval[a:real^M,b])` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RSUM_DIFF_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a ==> y <= x ==> y <= a`)) THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Negligible sets.                                                          *)
(* ------------------------------------------------------------------------- *)

let indicator = new_definition
  `indicator s :real^M->real^1 = \x. if x IN s then vec 1 else vec 0`;;

let DROP_INDICATOR = prove
 (`!s x. drop(indicator s x) = if x IN s then &1 else &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[indicator] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC]);;

let DROP_INDICATOR_POS_LE = prove
 (`!s x. &0 <= drop(indicator s x)`,
  REWRITE_TAC[DROP_INDICATOR] THEN REAL_ARITH_TAC);;

let DROP_INDICATOR_LE_1 = prove
 (`!s x. drop(indicator s x) <= &1`,
  REWRITE_TAC[DROP_INDICATOR] THEN REAL_ARITH_TAC);;

let DROP_INDICATOR_ABS_LE_1 = prove
 (`!s x. abs(drop(indicator s x)) <= &1`,
  REWRITE_TAC[DROP_INDICATOR] THEN REAL_ARITH_TAC);;

let negligible = new_definition
 `negligible s <=> !a b. (indicator s has_integral (vec 0)) (interval[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Negligibility of hyperplane.                                              *)
(* ------------------------------------------------------------------------- *)

let VSUM_NONZERO_IMAGE_LEMMA = prove
 (`!s f:A->B g:B->real^N a.
        FINITE s /\ g(a) = vec 0 /\
        (!x y. x IN s /\ y IN s /\ f x = f y /\ ~(x = y) ==> g(f x) = vec 0)
       ==> vsum {f x |x| x IN s /\ ~(f x = a)} g =
           vsum s (g o f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {(f:A->B) x |x| x IN s /\ ~(f x = a)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `IMAGE (f:A->B) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_SIMP_TAC[VSUM] THEN MATCH_MP_TAC ITERATE_NONZERO_IMAGE_LEMMA THEN
    ASM_REWRITE_TAC[NEUTRAL_VECTOR_ADD; MONOIDAL_VECTOR_ADD]]);;

let INTERVAL_DOUBLESPLIT = prove
 (`1 <= k /\ k <= dimindex(:N)
      ==> interval[a,b] INTER {x:real^N | abs(x$k - c) <= e} =
          interval[(lambda i. if i = k then max (a$k) (c - e) else a$i),
                   (lambda i. if i = k then min (b$k) (c + e) else b$i)]`,
   REWRITE_TAC[REAL_ARITH `abs(x - c) <= e <=> x >= c - e /\ x <= c + e`] THEN
   REWRITE_TAC[SET_RULE `s INTER {x | P x /\ Q x} =
                        (s INTER {x | Q x}) INTER {x | P x}`] THEN
   SIMP_TAC[INTERVAL_SPLIT]);;

let DIVISION_DOUBLESPLIT = prove
 (`!p a b:real^N k c e.
        p division_of interval[a,b] /\ 1 <= k /\ k <= dimindex(:N)
        ==> {l INTER {x | abs(x$k - c) <= e} |l|
                l IN p /\ ~(l INTER {x | abs(x$k - c) <= e} = {})}
            division_of (interval[a,b] INTER {x | abs(x$k - c) <= e})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `c + e:real` o MATCH_MP DIVISION_SPLIT) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
  FIRST_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (TAUT
   `(a /\ b /\ c) /\ d ==> d /\ b /\ c`)) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o SPEC `c - e:real` o
    MATCH_MP DIVISION_SPLIT) THEN
  ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT; INTERVAL_SPLIT] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `abs(x - c) <= e <=> x >= c - e /\ x <= c + e`] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ a /\ b /\ d`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

let CONTENT_DOUBLESPLIT = prove
 (`!a b:real^N k c e.
        &0 < e /\ 1 <= k /\ k <= dimindex(:N)
        ==> ?d. &0 < d /\
                content(interval[a,b] INTER {x | abs(x$k - c) <= d}) < e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^N,b]) = &0` THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `content(interval[a:real^N,b])` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM(K ALL_TAC o SYM); ASM_REWRITE_TAC[]] THEN
    ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT] THEN MATCH_MP_TAC CONTENT_SUBSET THEN
    ASM_SIMP_TAC[GSYM INTERVAL_DOUBLESPLIT] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONTENT_EQ_0]) THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < product ((1..dimindex (:N)) DELETE k)
                              (\i. (b:real^N)$i - (a:real^N)$i)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LT THEN
    ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE; IN_NUMSEG;
                 REAL_SUB_LT];
    ALL_TAC] THEN
  ABBREV_TAC `d = e / &3 / product ((1..dimindex (:N)) DELETE k)
                                   (\i. (b:real^N)$i - (a:real^N)$i)` THEN
  EXISTS_TAC `d:real` THEN SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  ASM_SIMP_TAC[content; INTERVAL_DOUBLESPLIT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
  SUBGOAL_THEN `1..dimindex(:N) = k INSERT ((1..dimindex(:N)) DELETE k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_DELETE; IN_DELETE] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE;
                LAMBDA_BETA; IN_DELETE; IN_NUMSEG] THEN
  SUBGOAL_THEN
   `product ((1..dimindex (:N)) DELETE k)
     (\j. ((lambda i. if i = k then min (b$k) (c + d) else b$i):real^N)$j -
          ((lambda i. if i = k then max (a$k) (c - d) else a$i):real^N)$j) =
    product ((1..dimindex (:N)) DELETE k)
            (\i. (b:real^N)$i - (a:real^N)$i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * d` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < d /\ &3 * d <= x ==> &2 * d < x`) THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "d" THEN REAL_ARITH_TAC);;

let NEGLIGIBLE_STANDARD_HYPERPLANE = prove
 (`!c k. 1 <= k /\ k <= dimindex(:N) ==> negligible {x:real^N | x$k = c}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[negligible; has_integral] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `k:num`; `c:real`; `e:real`]
        CONTENT_DOUBLESPLIT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. ball(x,d)` THEN ASM_SIMP_TAC[GAUGE_BALL] THEN
  ABBREV_TAC `i = indicator {x:real^N | x$k = c}` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum p (\(x,l). content l % i x) =
    vsum p (\(x,l). content(l INTER {x:real^N | abs(x$k - c) <= d}) %
                    (i:real^N->real^1) x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `l:real^N->bool`] THEN
    DISCH_TAC THEN EXPAND_TAC "i" THEN REWRITE_TAC[indicator] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `l:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> l SUBSET s ==> l = l INTER t`) THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_ELIM_THM; dist] THEN
    UNDISCH_THEN `(x:real^N)$k = c` (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `norm(vsum p (\(x:real^N,l).
          content(l INTER {x:real^N | abs(x$k - c) <= d}) %
         vec 1:real^1))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[VSUM_REAL; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs(x) <= abs(y)`) THEN
    REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; DROP_CMUL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE; MATCH_MP_TAC SUM_LE] THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `l:real^N->bool`] THEN STRIP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_LMUL] THEN
    EXPAND_TAC "i" THEN REWRITE_TAC[DROP_VEC] THEN
    REWRITE_TAC[DROP_INDICATOR_POS_LE; DROP_INDICATOR_LE_1] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `l:real^N->bool`] o
        el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT; CONTENT_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\l. content (l INTER {x | abs (x$k - c) <= d}) % vec 1):
                  (real^N->bool)->real^1`;
                 `p:real^N#(real^N->bool)->bool`;
                 `interval[a:real^N,b]`]
        VSUM_OVER_TAGGED_DIVISION_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!x. x = &0 /\ &0 <= y /\ y <= x ==> y = &0`) THEN
    EXISTS_TAC `content(interval[u:real^N,v])` THEN
    CONJ_TAC THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[] THEN
    DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[CONTENT_POS_LE; INTERVAL_DOUBLESPLIT] THEN
    MATCH_MP_TAC CONTENT_SUBSET THEN
    ASM_SIMP_TAC[GSYM INTERVAL_DOUBLESPLIT] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
     [`IMAGE SND (p:real^N#(real^N->bool)->bool)`;
      `\l. l INTER {x:real^N | abs (x$k - c) <= d}`;
      `\l:real^N->bool. content l % vec 1 :real^1`;
      `{}:real^N->bool`] VSUM_NONZERO_IMAGE_LEMMA) THEN
    REWRITE_TAC[o_DEF] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_TAGGED_DIVISION) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC] THEN
    REWRITE_TAC[CONTENT_EMPTY; VECTOR_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
    X_GEN_TAC `m:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    SIMP_TAC[INTERVAL_DOUBLESPLIT; ASSUME `1 <= k`;
             ASSUME `k <= dimindex(:N)`] THEN
    REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN
    ASM_SIMP_TAC[GSYM INTERVAL_DOUBLESPLIT] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPECL [`interval[u:real^N,v]`; `m:real^N->bool`] o
      el 2 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
      `u SUBSET s /\ u SUBSET t ==> s INTER t = {} ==> u = {}`) THEN
    CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC
   `&1 * content(interval[a,b] INTER {x:real^N | abs (x$k - c) <= d})` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[REAL_MUL_LID]] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
    DIVISION_DOUBLESPLIT)) THEN
  DISCH_THEN(MP_TAC o SPECL [`k:num`; `c:real`; `d:real`]) THEN
  ASM_SIMP_TAC[INTERVAL_DOUBLESPLIT] THEN DISCH_TAC THEN
  MATCH_MP_TAC DSUM_BOUND THEN
  ASM_SIMP_TAC[NORM_REAL; VEC_COMPONENT; DIMINDEX_1; LE_REFL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A technical lemma about "refinement" of division.                         *)
(* ------------------------------------------------------------------------- *)

let TAGGED_DIVISION_FINER = prove
 (`!p a b:real^N d. p tagged_division_of interval[a,b] /\ gauge d
             ==> ?q. q tagged_division_of interval[a,b] /\ d fine q /\
                     !x k. (x,k) IN p /\ k SUBSET d(x) ==> (x,k) IN q`,
  let lemma1 = prove
   (`{k | ?x. (x,k) IN p} = IMAGE SND p`,
    REWRITE_TAC[EXTENSION; EXISTS_PAIR_THM; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[]) in
  SUBGOAL_THEN
   `!a b:real^N d p.
       FINITE p
       ==> p tagged_partial_division_of interval[a,b] /\ gauge d
           ==> ?q. q tagged_division_of (UNIONS {k | ?x. x,k IN p}) /\
                   d fine q /\
                   !x k. (x,k) IN p /\ k SUBSET d(x) ==> (x,k) IN q`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [tagged_division_of] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
    FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    ASM_MESON_TAC[tagged_partial_division_of]] THEN
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[SET_RULE `UNIONS {k | ?x. x,k IN {}} = {}`] THEN
    EXISTS_TAC `{}:real^N#(real^N->bool)->bool` THEN
    REWRITE_TAC[fine; NOT_IN_EMPTY; TAGGED_DIVISION_OF_EMPTY];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN MAP_EVERY X_GEN_TAC
   [`x:real^N`; `k:real^N->bool`; `p:real^N#(real^N->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_SUBSET THEN
    EXISTS_TAC `(x:real^N,k:real^N->bool) INSERT p` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^N#(real^N->bool)->bool`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `UNIONS {l:real^N->bool | ?y:real^N. (y,l) IN (x,k) INSERT p} =
    k UNION UNIONS {l | ?y. (y,l) IN p}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNION; IN_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; PAIR_EQ] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u v:real^N. k = interval[u,v]` MP_TAC THENL
   [ASM_MESON_TAC[IN_INSERT; tagged_partial_division_of]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  ASM_CASES_TAC `interval[u,v] SUBSET ((d:real^N->real^N->bool) x)` THENL
   [EXISTS_TAC `{(x:real^N,interval[u:real^N,v])} UNION q1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAGGED_DIVISION_UNION THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TAGGED_DIVISION_OF_SELF THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
         [tagged_partial_division_of]) THEN
        REWRITE_TAC[IN_INSERT; PAIR_EQ] THEN MESON_TAC[];
        ALL_TAC];
      CONJ_TAC THENL
       [MATCH_MP_TAC FINE_UNION THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[fine; IN_SING; PAIR_EQ] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; PAIR_EQ; IN_UNION; IN_SING] THEN
      ASM_MESON_TAC[]];
    FIRST_ASSUM(MP_TAC o SPECL [`u:real^N`; `v:real^N`] o MATCH_MP
      FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `q2:real^N#(real^N->bool)->bool`
      STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q2 UNION q1:real^N#(real^N->bool)->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC TAGGED_DIVISION_UNION THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FINE_UNION] THEN
      ASM_REWRITE_TAC[IN_INSERT; PAIR_EQ; IN_UNION; IN_SING] THEN
      ASM_MESON_TAC[]]] THEN
  (MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
   REWRITE_TAC[lemma1; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
   FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
      [tagged_partial_division_of]) THEN
   REWRITE_TAC[IN_INSERT; FINITE_INSERT; PAIR_EQ] THEN
   STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
    [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; OPEN_INTERVAL]; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_MESON_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* Hence the main theorem about negligible sets.                             *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_NEGLIGIBLE = prove
 (`!f:real^M->real^N s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> f x = vec 0)
        ==> (f has_integral (vec 0)) t`,
  let lemma = prove
   (`!f:B->real g:A#B->real s t.
          FINITE s /\ FINITE t /\
          (!x y. (x,y) IN t ==> &0 <= g(x,y)) /\
          (!y. y IN s ==> ?x. (x,y) IN t /\ f(y) <= g(x,y))
          ==> sum s f <= sum t g`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_LE_INCLUDED THEN
    EXISTS_TAC `SND:A#B->B` THEN
    REWRITE_TAC[EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[]) in
  SUBGOAL_THEN
   `!f:real^M->real^N s a b.
        negligible s /\ (!x. ~(x IN s) ==> f x = vec 0)
        ==> (f has_integral (vec 0)) (interval[a,b])`
  ASSUME_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_DIFF] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[has_integral_alt] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
      EXISTS_TAC `\x. if x IN t then (f:real^M->real^N) x else vec 0` THEN
      SIMP_TAC[] THEN
      FIRST_X_ASSUM(CHOOSE_THEN(CHOOSE_THEN SUBST_ALL_TAC)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN
    REPEAT STRIP_TAC THEN EXISTS_TAC `vec 0:real^N` THEN
    ASM_REWRITE_TAC[NORM_0; VECTOR_SUB_REFL] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[negligible; has_integral; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MAP_EVERY(fun t -> MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC t)
   [`a:real^M`; `b:real^M`] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o
      SPEC `e / &2 / ((&n + &1) * &2 pow n)`) THEN
  REWRITE_TAC[real_div; REAL_MUL_POS_LT] THEN REWRITE_TAC[GSYM real_div] THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_LT_MUL; REAL_POW_LT; REAL_OF_NUM_LT;
           FORALL_AND_THM; ARITH; REAL_ARITH `&0 < &n + &1`; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (d:num->real^M->real^M->bool)
                  (num_of_int(int_of_real(floor(norm(f x:real^N))))) x` THEN
  CONJ_TAC THENL [REWRITE_TAC[gauge] THEN ASM_MESON_TAC[gauge]; ALL_TAC] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_CASES_TAC `p:real^M#(real^M->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES; NORM_0] THEN
  MP_TAC(SPEC `sup(IMAGE (\(x,k:real^M->bool). norm((f:real^M->real^N) x)) p)`
    REAL_ARCH_SIMPLE) THEN
  ASM_SIMP_TAC[REAL_SUP_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MP_TAC(GEN `i:num`
   (ISPECL [`p:real^M#(real^M->bool)->bool`; `a:real^M`; `b:real^M`;
                `(d:num->real^M->real^M->bool) i`]
                TAGGED_DIVISION_FINER)) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; RIGHT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real^M#(real^M->bool)->bool`
        STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
   `sum(0..N+1) (\i. (&i + &1) *
                     norm(vsum (q i) (\(x:real^M,k:real^M->bool).
                                            content k % indicator s x)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `sum (0..N+1) (\i. e / &2 / &2 pow i)` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div; SUM_LMUL; GSYM REAL_POW_INV] THEN
      REWRITE_TAC[SUM_GP; LT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `(e * &1 / &2) * (&1 - x) / (&1 / &2) < e <=>
                                &0 < e * x`] THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT; REAL_ARITH `&0 < &1 / &2`]] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  FIRST_ASSUM(ASSUME_TAC o GEN `i:num` o
    MATCH_MP TAGGED_DIVISION_OF_FINITE o SPEC `i:num`) THEN
  ASM_SIMP_TAC[VSUM_REAL; NORM_LIFT] THEN
  REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; DROP_CMUL] THEN
  REWRITE_TAC[real_abs] THEN
  SUBGOAL_THEN
   `!i:num. &0 <= sum (q i) (\(x:real^M,y:real^M->bool).
              content y * drop (indicator s x))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[DROP_INDICATOR_POS_LE] THEN
    ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SUM_LMUL] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> n <= x ==> n <= y`) THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC lemma THEN
  ASM_SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FORALL_PAIR_THM; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL] THEN
    REWRITE_TAC[DROP_INDICATOR_POS_LE] THEN
    ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC
   `n = num_of_int(int_of_real(floor(norm((f:real^M->real^N) x))))` THEN
  SUBGOAL_THEN `&n <= norm((f:real^M->real^N) x) /\
                norm(f x) < &n + &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&n = floor(norm((f:real^M->real^N) x))`
     (fun th -> MESON_TAC[th; FLOOR]) THEN
    EXPAND_TAC "n" THEN
    MP_TAC(ISPEC `norm((f:real^M->real^N) x)` FLOOR_POS) THEN
    REWRITE_TAC[NORM_POS_LE; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM int_of_num; NUM_OF_INT_OF_NUM];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((f:real^M->real^N) x)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= n ==> x <= n + &1`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_SIMP_TAC[indicator] THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RZERO; NORM_0;
              VECTOR_MUL_RZERO; REAL_LE_REFL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[DROP_VEC; REAL_MUL_RID; NORM_MUL] THEN
  SUBGOAL_THEN `&0 <= content(k:real^M->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[real_abs] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let HAS_INTEGRAL_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`,
  SUBGOAL_THEN
   `!f:real^M->real^N g s a b y.
        negligible s /\ (!x. x IN (interval[a,b] DIFF s) ==> g x = f x)
        ==> (f has_integral y) (interval[a,b])
            ==> (g has_integral y) (interval[a,b])`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `((\x. (f:real^M->real^N)(x) + (g(x) - f(x))) has_integral (y + vec 0))
      (interval[a,b])`
    MP_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[VECTOR_ARITH `f + g - f = g /\ f + vec 0 = f`; ETA_AX]] THEN
    MATCH_MP_TAC HAS_INTEGRAL_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[has_integral_alt] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN(CHOOSE_THEN SUBST_ALL_TAC)) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let HAS_INTEGRAL_SPIKE_EQ = prove
 (`!f:real^M->real^N g s t y.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THENL
   [EXISTS_TAC `f:real^M->real^N`; EXISTS_TAC `g:real^M->real^N`] THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NORM_SUB]);;

let INTEGRABLE_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t ==> g integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE) THEN ASM_REWRITE_TAC[]);;

let INTEGRAL_SPIKE = prove
 (`!f:real^M->real^N g s t y.
        negligible s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> integral t f = integral t g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some other trivialities about negligible sets.                            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_SUBSET = prove
 (`!s:real^N->bool t:real^N->bool.
        negligible s /\ t SUBSET s ==> negligible t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[negligible] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC [`(\x. vec 0):real^N->real^1`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[HAS_INTEGRAL_0] THEN
  REWRITE_TAC[indicator] THEN ASM SET_TAC[]);;

let NEGLIGIBLE_DIFF = prove
 (`!s t:real^N->bool. negligible s ==> negligible(s DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_DIFF]);;

let NEGLIGIBLE_INTER = prove
 (`!s t. negligible s \/ negligible t ==> negligible(s INTER t)`,
  MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET]);;

let NEGLIGIBLE_UNION = prove
 (`!s t:real^N->bool.
        negligible s /\ negligible t ==> negligible (s UNION t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FIRST_ASSUM MP_TAC THEN
  REWRITE_TAC[negligible; AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `a:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `b:real^N` THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[VECTOR_ADD_LID] THEN MATCH_MP_TAC EQ_IMP THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[indicator; IN_UNION; IN_DIFF; VECTOR_ADD_LID]);;

let NEGLIGIBLE_UNION_EQ = prove
 (`!s t:real^N->bool.
        negligible (s UNION t) <=> negligible s /\ negligible t`,
  MESON_TAC[NEGLIGIBLE_UNION; SUBSET_UNION; NEGLIGIBLE_SUBSET]);;

let NEGLIGIBLE_SING = prove
 (`!a:real^N. negligible {a}`,
  GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | (x:real^N)$1 = (a:real^N)$1}` THEN
  SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; LE_REFL; DIMINDEX_GE_1] THEN
  SET_TAC[]);;

let NEGLIGIBLE_INSERT = prove
 (`!a:real^N s. negligible(a INSERT s) <=> negligible s`,
  ONCE_REWRITE_TAC[SET_RULE `a INSERT s = {a} UNION s`] THEN
  REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_SING]);;

let NEGLIGIBLE_EMPTY = prove
 (`negligible {}`,
  MESON_TAC[EMPTY_SUBSET; NEGLIGIBLE_SUBSET; NEGLIGIBLE_SING]);;

let NEGLIGIBLE_FINITE = prove
 (`!s. FINITE s ==> negligible s`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NEGLIGIBLE_EMPTY; NEGLIGIBLE_INSERT]);;

let NEGLIGIBLE_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> negligible t)
       ==> negligible(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; NEGLIGIBLE_EMPTY; IN_INSERT] THEN
  SIMP_TAC[NEGLIGIBLE_UNION]);;

let NEGLIGIBLE = prove
 (`!s:real^N->bool. negligible s <=> !t. (indicator s has_integral vec 0) t`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; REWRITE_TAC[negligible] THEN SIMP_TAC[]] THEN
  DISCH_TAC THEN GEN_TAC THEN ONCE_REWRITE_TAC[has_integral_alt] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[negligible]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `vec 0:real^1` THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s INTER t:real^N->bool`]
        NEGLIGIBLE_SUBSET) THEN
  ASM_REWRITE_TAC[INTER_SUBSET; negligible; VECTOR_SUB_REFL; NORM_0] THEN
  REWRITE_TAC[indicator; IN_INTER] THEN
  SIMP_TAC[TAUT `(if p /\ q then r else s) =
                 (if q then if p then r else s else s)`]);;

(* ------------------------------------------------------------------------- *)
(* Finite or empty cases of the spike theorem are quite commonly needed.     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SPIKE_FINITE = prove
 (`!f:real^M->real^N g s t y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`,
  MESON_TAC[HAS_INTEGRAL_SPIKE; NEGLIGIBLE_FINITE]);;

let HAS_INTEGRAL_SPIKE_FINITE_EQ = prove
 (`!f:real^M->real^N g s y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_FINITE]);;

let INTEGRABLE_SPIKE_FINITE = prove
 (`!f:real^M->real^N g s.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t
            ==> g integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE_FINITE) THEN ASM_REWRITE_TAC[]);;

let INTEGRAL_EQ = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> f x = g x) ==> integral s f = integral s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{}:real^M->bool` THEN ASM_SIMP_TAC[NEGLIGIBLE_EMPTY; IN_DIFF]);;

let INTEGRAL_EQ_0 = prove
 (`!f:real^M->real^N s. (!x. x IN s ==> f x = vec 0) ==> integral s f = vec 0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral s ((\x. vec 0):real^M->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_EQ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[INTEGRAL_0]]);;

(* ------------------------------------------------------------------------- *)
(* In particular, the boundary of an interval is negligible.                 *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_FRONTIER_INTERVAL = prove
 (`!a b:real^N. negligible(interval[a,b] DIFF interval(a,b))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `UNIONS (IMAGE (\k. {x:real^N | x$k = (a:real^N)$k} UNION
                                 {x:real^N | x$k = (b:real^N)$k})
                            (1..dimindex(:N)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    SIMP_TAC[IN_NUMSEG; NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_STANDARD_HYPERPLANE];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[IN_NUMSEG; IN_UNION; IN_ELIM_THM; REAL_LT_LE] THEN
    MESON_TAC[]]);;

let HAS_INTEGRAL_SPIKE_INTERIOR = prove
 (`!f:real^M->real^N g a b y.
        (!x. x IN interval(a,b) ==> g x = f x) /\
        (f has_integral y) (interval[a,b])
        ==> (g has_integral y) (interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                           HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `interval[a:real^M,b] DIFF interval(a,b)` THEN
  REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN ASM SET_TAC[]);;

let HAS_INTEGRAL_SPIKE_INTERIOR_EQ = prove
 (`!f:real^M->real^N g a b y.
        (!x. x IN interval(a,b) ==> g x = f x)
        ==> ((f has_integral y) (interval[a,b]) <=>
             (g has_integral y) (interval[a,b]))`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_INTERIOR]);;

let INTEGRABLE_SPIKE_INTERIOR = prove
 (`!f:real^M->real^N g a b.
        (!x. x IN interval(a,b) ==> g x = f x)
        ==> f integrable_on (interval[a,b])
            ==> g integrable_on  (interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE_INTERIOR) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrability of continuous functions.                                    *)
(* ------------------------------------------------------------------------- *)

let NEUTRAL_AND = prove
 (`neutral(/\) = T`,
  REWRITE_TAC[neutral; FORALL_BOOL_THM] THEN MESON_TAC[]);;

let MONOIDAL_AND = prove
 (`monoidal(/\)`,
  REWRITE_TAC[monoidal; NEUTRAL_AND; CONJ_ACI]);;

let ITERATE_AND = prove
 (`!p s. FINITE s ==> (iterate(/\) s p <=> !x. x IN s ==> p x)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[MONOIDAL_AND; NEUTRAL_AND; ITERATE_CLAUSES] THEN SET_TAC[]);;

let OPERATIVE_DIVISION_AND = prove
 (`!P d a b. operative(/\) P /\ d division_of interval[a,b]
             ==> ((!i. i IN d ==> P i) <=> P(interval[a,b]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o CONJ MONOIDAL_AND) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPERATIVE_DIVISION) THEN
  ASM_MESON_TAC[ITERATE_AND; DIVISION_OF_FINITE]);;

let OPERATIVE_APPROXIMABLE = prove
 (`!f:real^M->real^N e.
        &0 <= e
        ==> operative(/\)
               (\i. ?g. (!x. x IN i ==> norm (f x - g x) <= e) /\
                        g integrable_on i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[operative; NEUTRAL_AND] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `f:real^M->real^N` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; integrable_on] THEN
    ASM_MESON_TAC[HAS_INTEGRAL_NULL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`; `c:real`; `k:num`] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_SPLIT; IN_INTER]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `g1:real^M->real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `g2:real^M->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x. if x$k = c then (f:real^M->real^N)(x) else
                  if x$k <= c then g1(x) else g2(x)` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER; IN_ELIM_THM]) THEN
    ASM_MESON_TAC[REAL_ARITH `x <= c \/ x >= c`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^M. if x$k = c then f x else if x$k <= c then g1 x else g2 x)
    integrable_on (interval[u,v] INTER {x | x$k <= c}) /\
    (\x. if x$k = c then f x :real^N else if x$k <= c then g1 x else g2 x)
    integrable_on (interval[u,v] INTER {x | x$k >= c})`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[HAS_INTEGRAL_SPLIT]] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC
     `(g1:real^M->real^N) integrable_on (interval[u,v] INTER {x | x$k <= c})`;
    UNDISCH_TAC
    `(g2:real^M->real^N) integrable_on (interval[u,v] INTER {x | x$k >= c})`
   ] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MATCH_MP_TAC INTEGRABLE_SPIKE THEN
  ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN
  EXISTS_TAC `{x:real^M | x$k = c}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; IN_DIFF; IN_INTER; IN_ELIM_THM;
               REAL_ARITH `x >= c /\ ~(x = c) ==> ~(x <= c)`] THEN
  EXISTS_TAC `e:real` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]);;

let APPROXIMABLE_ON_DIVISION = prove
 (`!f:real^M->real^N d a b.
        &0 <= e /\
        (d division_of interval[a,b]) /\
        (!i. i IN d
             ==> ?g. (!x. x IN i ==> norm (f x - g x) <= e) /\
                     g integrable_on i)
        ==> ?g. (!x. x IN interval[a,b] ==> norm (f x - g x) <= e) /\
                g integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(/\)`; `d:(real^M->bool)->bool`;
                 `a:real^M`; `b:real^M`;
                 `\i. ?g:real^M->real^N.
                       (!x. x IN i ==> norm (f x - g x) <= e) /\
                       g integrable_on i`]
                OPERATIVE_DIVISION) THEN
  ASM_SIMP_TAC[OPERATIVE_APPROXIMABLE; MONOIDAL_AND] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[ITERATE_AND]);;

let INTEGRABLE_CONTINUOUS = prove
 (`!f:real^M->real^N a b.
        f continuous_on interval[a,b] ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_UNIFORM_LIMIT THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC APPROXIMABLE_ON_DIVISION THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    COMPACT_UNIFORMLY_CONTINUOUS)) THEN
  REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?p. p tagged_division_of interval[a:real^M,b] /\ (\x. ball(x,d)) fine p`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINE_DIVISION_EXISTS; GAUGE_BALL]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE SND (p:real^M#(real^M->bool)->bool)` THEN
  ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
  DISCH_TAC THEN EXISTS_TAC `\y:real^M. (f:real^M->real^N) x` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(MP_TAC o
    SPECL [`x:real^M`; `l:real^M->bool`] o el 1 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[SUBSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
   FIRST_X_ASSUM SUBST_ALL_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[REAL_LT_IMP_LE; NORM_SUB];
    REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `content(interval[a':real^M,b']) % (f:real^M->real^N) x` THEN
    REWRITE_TAC[HAS_INTEGRAL_CONST]]);;

(* ------------------------------------------------------------------------- *)
(* Specialization of additivity to one dimension.                            *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_1_LT = prove
 (`!op. monoidal op
        ==> !f. operative op f <=>
                (!a b. drop b <= drop a ==> f(interval[a,b]) = neutral op) /\
                (!a b c. drop a < drop c /\ drop c < drop b
                         ==> op (f(interval[a,c])) (f(interval[c,b])) =
                             f(interval[a,b]))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[operative; CONTENT_EQ_0_1] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[FORALL_1; DIMINDEX_1] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `a:real^1` THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `b:real^1` THEN
  EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `c:real^1` THEN FIRST_ASSUM(SUBST1_TAC o SPEC `drop c`) THEN
    DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
    ASM_SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_1; LE_REFL; REAL_LT_IMP_LE] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11; PAIR_EQ] THEN
    SIMP_TAC[FORALL_1; CART_EQ; DIMINDEX_1; LAMBDA_BETA; LE_REFL] THEN
    REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `d:real` THEN ABBREV_TAC `c = lift d` THEN
  SUBGOAL_THEN `d = drop c` SUBST1_TAC THENL
   [ASM_MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
  SIMP_TAC[INTERVAL_SPLIT; LE_REFL; drop; DIMINDEX_1] THEN
  REWRITE_TAC[GSYM drop] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop c <= drop a \/ drop a < drop c`) THENL
   [SUBGOAL_THEN
     `content(interval[a:real^1,
        (lambda i. if i = 1 then min (drop b) (drop c) else b$i)]) = &0 /\
      interval[(lambda i. if i = 1 then max (drop a) (drop c) else a$i),b] =
      interval[a,b]`
    (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [SIMP_TAC[CONTENT_EQ_0_1];
        AP_TERM_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ]] THEN
      SIMP_TAC[drop; CART_EQ; FORALL_1; LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN
      UNDISCH_TAC `drop c <= drop a` THEN REWRITE_TAC[drop] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[CONTENT_EQ_0_1] THEN
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN ASM_MESON_TAC[monoidal]];
    ALL_TAC] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop b <= drop c \/ drop c < drop b`) THENL
   [SUBGOAL_THEN
     `interval[a,(lambda i. if i = 1 then min (drop b) (drop c) else b$i)] =
      interval[a,b] /\
      content(interval
        [(lambda i. if i = 1 then max (drop a) (drop c) else a$i),b]) = &0`
      (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THENL
     [CONJ_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[CONS_11; PAIR_EQ];
        SIMP_TAC[CONTENT_EQ_0_1]] THEN
      SIMP_TAC[drop; CART_EQ; FORALL_1; LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN
      UNDISCH_TAC `drop b <= drop c` THEN REWRITE_TAC[drop] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[CONTENT_EQ_0_1] THEN
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN ASM_MESON_TAC[monoidal]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lambda i. if i = 1 then min (drop b) (drop c) else b$i) = c /\
    (lambda i. if i = 1 then max (drop a) (drop c) else a$i) = c`
   (fun th -> REWRITE_TAC[th] THEN ASM_MESON_TAC[]) THEN
  SIMP_TAC[CART_EQ; FORALL_1; DIMINDEX_1; LE_REFL; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC);;

let OPERATIVE_1_LE = prove
 (`!op. monoidal op
        ==> !f. operative op f <=>
                (!a b. drop b <= drop a ==> f(interval[a,b]) = neutral op) /\
                (!a b c. drop a <= drop c /\ drop c <= drop b
                         ==> op (f(interval[a,c])) (f(interval[c,b])) =
                             f(interval[a,b]))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[OPERATIVE_1_LT] THEN MESON_TAC[REAL_LT_IMP_LE]] THEN
  REWRITE_TAC[operative; CONTENT_EQ_0_1] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_1; DIMINDEX_1] THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC t)
   [`a:real^1`; `b:real^1`] THEN DISCH_TAC THEN
  X_GEN_TAC `c:real^1` THEN FIRST_ASSUM(SUBST1_TAC o SPEC `drop c`) THEN
  DISCH_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LE_TRANS) THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_1; LE_REFL] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[CONS_11; PAIR_EQ] THEN
  SIMP_TAC[FORALL_1; CART_EQ; DIMINDEX_1; LAMBDA_BETA; LE_REFL] THEN
  REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Special case of additivity we need for the FCT.                           *)
(* ------------------------------------------------------------------------- *)

let ADDITIVE_TAGGED_DIVISION_1 = prove
 (`!f:real^1->real^N p a b.
        drop a <= drop b /\
        p tagged_division_of interval[a,b]
        ==> vsum p
             (\(x,k). f(interval_upperbound k) - f(interval_lowerbound k)) =
            f b - f a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(+):real^N->real^N->real^N`;
    `p:(real^1#(real^1->bool)->bool)`;
    `a:real^1`; `b:real^1`;
    `(\k. if k = {} then vec 0
          else f(interval_upperbound k) - f(interval_lowerbound k)):
     ((real^1->bool)->real^N)`] OPERATIVE_TAGGED_DIVISION) THEN
  ASM_SIMP_TAC[MONOIDAL_VECTOR_ADD; OPERATIVE_1_LT; NEUTRAL_VECTOR_ADD;
               INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_ARITH `a <= b ==> ~(b < a)`;
                 REAL_LT_IMP_LE; CONTENT_EQ_0_1;
                 INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
    SIMP_TAC[REAL_ARITH `b <= a ==> (b < a <=> ~(b = a))`] THEN
    SIMP_TAC[DROP_EQ; TAUT
      `(if ~p then x else y) = (if p then y else x)`] THEN
    SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1; REAL_LE_REFL] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; COND_ID; EQ_SYM_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_TRANS) THEN
    ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1;
                 REAL_ARITH `b < a ==> ~(a < b)`; REAL_LT_IMP_LE] THEN
    MESON_TAC[VECTOR_ARITH `(c - a) + (b - c):real^N = b - a`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; GSYM REAL_NOT_LE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM] THEN MATCH_MP_TAC VSUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  ASM_MESON_TAC[TAGGED_DIVISION_OF; MEMBER_NOT_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* A useful lemma allowing us to factor out the content size.                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_FACTOR_CONTENT = prove
 (`!f:real^M->real^N i a b.
      (f has_integral i) (interval[a,b]) <=>
      (!e. &0 < e
           ==> ?d. gauge d /\
                   (!p. p tagged_division_of interval[a,b] /\ d fine p
                        ==> norm (vsum p (\(x,k). content k % f x) - i)
                            <= e * content(interval[a,b])))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
   [MP_TAC(SPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
     VSUM_CONTENT_NULL) THEN
    ASM_SIMP_TAC[HAS_INTEGRAL_NULL_EQ; VECTOR_SUB_LZERO; NORM_NEG] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; NORM_LE_0] THEN
    ASM_MESON_TAC[FINE_DIVISION_EXISTS; GAUGE_TRIVIAL; REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[has_integral] THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `e * content(interval[a:real^M,b])`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; CONTENT_LT_NZ] THEN MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / content(interval[a:real^M,b])`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; CONTENT_LT_NZ; REAL_OF_NUM_LT; ARITH] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN
  ASM_MESON_TAC[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`]);;

(* ------------------------------------------------------------------------- *)
(* Attempt a systematic general set of "offset" results for components.      *)
(* ------------------------------------------------------------------------- *)

let GAUGE_MODIFY = prove
 (`!f:real^M->real^N.
      (!s. open s ==> open {x | f(x) IN s})
      ==> !d. gauge d ==> gauge (\x y. d (f x) (f y))`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  SIMP_TAC[gauge; IN] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^M` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(f:real^M->real^N) x`) THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[IN]);;

(* ------------------------------------------------------------------------- *)
(* Integrabibility on subintervals.                                          *)
(* ------------------------------------------------------------------------- *)

let OPERATIVE_INTEGRABLE = prove
 (`!f. operative (/\) (\i. f integrable_on i)`,
  GEN_TAC THEN REWRITE_TAC[operative; NEUTRAL_AND] THEN CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_NULL_EQ];
    REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[INTEGRABLE_SPLIT] THEN
    REWRITE_TAC[integrable_on] THEN ASM_MESON_TAC[HAS_INTEGRAL_SPLIT]]);;

let INTEGRABLE_SUBINTERVAL = prove
 (`!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        interval[c,d] SUBSET interval[a,b]
        ==> f integrable_on interval[c,d]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[c:real^M,d] = {}` THENL
   [ASM_REWRITE_TAC[integrable_on] THEN
    MESON_TAC[HAS_INTEGRAL_NULL; CONTENT_EMPTY; EMPTY_AS_INTERVAL];
    ASM_MESON_TAC[OPERATIVE_INTEGRABLE; OPERATIVE_DIVISION_AND;
                  PARTIAL_DIVISION_EXTEND_1]]);;

(* ------------------------------------------------------------------------- *)
(* Combining adjacent intervals in 1 dimension.                              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE = prove
 (`!f i:real^N j a b c.
        drop a <= drop c /\ drop c <= drop b /\
        (f has_integral i) (interval[a,c]) /\
        (f has_integral j) (interval[c,b])
        ==> (f has_integral (i + j)) (interval[a,b])`,
  REPEAT STRIP_TAC THEN MP_TAC
   ((CONJUNCT2 o GEN_REWRITE_RULE I
     [MATCH_MP OPERATIVE_1_LE(MATCH_MP MONOIDAL_LIFTED MONOIDAL_VECTOR_ADD)])
    (ISPEC `f:real^1->real^N` OPERATIVE_INTEGRAL)) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`; `c:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(COND_CASES_TAC THEN
   ASM_REWRITE_TAC[lifted; distinctness "option"; injectivity "option"]) THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL; HAS_INTEGRAL_UNIQUE; integrable_on;
                INTEGRAL_UNIQUE]);;

let INTEGRAL_COMBINE = prove
 (`!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b /\ f integrable_on (interval[a,b])
        ==> integral(interval[a,c]) f + integral(interval[c,b]) f =
            integral(interval[a,b]) f`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN
  EXISTS_TAC `c:real^1` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRABLE_INTEGRAL THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
  MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL]);;

let INTEGRABLE_COMBINE = prove
 (`!f a b c.
        drop a <= drop c /\ drop c <= drop b /\
        f integrable_on interval[a,c] /\
        f integrable_on interval[c,b]
        ==> f integrable_on interval[a,b]`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_COMBINE]);;

(* ------------------------------------------------------------------------- *)
(* Reduce integrability to "local" integrability.                            *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_ON_LITTLE_SUBINTERVALS = prove
 (`!f:real^M->real^N a b.
        (!x. x IN interval[a,b]
             ==> ?d. &0 < d /\
                     !u v. x IN interval[u,v] /\
                           interval[u,v] SUBSET ball(x,d) /\
                           interval[u,v] SUBSET interval[a,b]
                           ==> f integrable_on interval[u,v])
        ==> f integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; GAUGE_EXISTENCE_LEMMA] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\x:real^M. ball(x,d x)`; `a:real^M`; `b:real^M`]
                FINE_DIVISION_EXISTS) THEN
  ASM_SIMP_TAC[GAUGE_BALL_DEPENDENT; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP (REWRITE_RULE[IMP_CONJ] OPERATIVE_DIVISION_AND)
         (ISPEC `f:real^M->real^N` OPERATIVE_INTEGRABLE)) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`IMAGE SND (p:real^M#(real^M->bool)->bool)`; `a:real^M`; `b:real^M`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
   GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
  ASM_REWRITE_TAC[] THEN  ASM_MESON_TAC[SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Second FCT or existence of antiderivative.                                *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_HAS_VECTOR_DERIVATIVE = prove
 (`!f:real^1->real^N a b.
     (f continuous_on interval[a,b])
     ==> !x. x IN interval[a,b]
             ==> ((\u. integral (interval[a,u]) f) has_vector_derivative f(x))
                 (at x within interval[a,b])`,
  REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN_ALT] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    COMPACT_UNIFORMLY_CONTINUOUS)) THEN
  REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[dist] THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
  DISJ_CASES_TAC(REAL_ARITH `drop x <= drop y \/ drop y <= drop x`) THENL
   [ASM_SIMP_TAC[REAL_ARITH `x <= y ==> abs(y - x) = y - x`];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `fy - fx - (x - y) % c = --(fx - fy - (y - x) % c)`] THEN
    ASM_SIMP_TAC[NORM_NEG; REAL_ARITH `x <= y ==> abs(x - y) = y - x`]] THEN
  ASM_SIMP_TAC[GSYM CONTENT_1] THEN MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
  EXISTS_TAC `(\u. f(u) - f(x)):real^1->real^N` THEN
  (ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[IN_INTERVAL_1; NORM_REAL; DROP_SUB; GSYM drop] THEN
    REAL_ARITH_TAC] THEN
   MATCH_MP_TAC HAS_INTEGRAL_SUB THEN REWRITE_TAC[HAS_INTEGRAL_CONST]) THENL
    [SUBGOAL_THEN
      `integral(interval[a,x]) f + integral(interval[x,y]) f =
       integral(interval[a,y]) f /\
       ((f:real^1->real^N) has_integral integral(interval[x,y]) f)
        (interval[x,y])`
      (fun th -> MESON_TAC[th;
          VECTOR_ARITH `a + b = c:real^N ==> c - a = b`]);
     SUBGOAL_THEN
      `integral(interval[a,y]) f + integral(interval[y,x]) f =
       integral(interval[a,x]) f /\
       ((f:real^1->real^N) has_integral integral(interval[y,x]) f)
        (interval[y,x])`
       (fun th -> MESON_TAC[th;
         VECTOR_ARITH `a + b = c:real^N ==> c - a = b`])] THEN
   (CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_COMBINE;
      MATCH_MP_TAC INTEGRABLE_INTEGRAL] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_SIMP_TAC[INTEGRABLE_CONTINUOUS; SUBSET_INTERVAL_1] THEN
    ASM_REAL_ARITH_TAC));;

let ANTIDERIVATIVE_CONTINUOUS = prove
 (`!f:real^1->real^N a b.
     (f continuous_on interval[a,b])
     ==> ?g. !x. x IN interval[a,b]
                 ==> (g has_vector_derivative f(x))
                     (at x within interval[a,b])`,
  MESON_TAC[INTEGRAL_HAS_VECTOR_DERIVATIVE]);;

(* ------------------------------------------------------------------------- *)
(* General "twiddling" for interval-to-interval function image.              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_TWIDDLE = prove
 (`!f:real^N->real^P (g:real^M->real^N) h r i a b.
      &0 < r /\
      (!x. h(g x) = x) /\ (!x. g(h x) = x) /\ (!x. g continuous at x) /\
      (!u v. ?w z. IMAGE g (interval[u,v]) = interval[w,z]) /\
      (!u v. ?w z. IMAGE h (interval[u,v]) = interval[w,z]) /\
      (!u v. content(IMAGE g (interval[u,v])) = r * content(interval[u,v])) /\
      (f has_integral i) (interval[a,b])
      ==> ((\x. f(g x)) has_integral (inv r) % i) (IMAGE h (interval[a,b]))`,
  let lemma0 = prove
   (`(!x k. (x,k) IN IMAGE (\(x,k). f x,g k) p ==> P x k) <=>
     (!x k. (x,k) IN p ==> P (f x) (g k))`,
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[])
  and lemma1 = prove
   (`{k | ?x. (x,k) IN p} = IMAGE SND p`,
    REWRITE_TAC[EXTENSION; EXISTS_PAIR_THM; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[])
  and lemma2 = prove
   (`SND o (\(x,k). f x,g k) = g o SND`,
    REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_DEF]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^N,b] = {}` THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_INTEGRAL_EMPTY_EQ; VECTOR_MUL_RZERO] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[has_integral] THEN
  ASM_REWRITE_TAC[has_integral_def; has_integral_compact_interval] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e * r:real`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x y:real^M. (d:real^N->real^N->bool) (g x) (g y)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    SIMP_TAC[gauge; IN; FORALL_AND_THM] THEN
    STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN
    SUBGOAL_THEN `(\y:real^M. (d:real^N->real^N->bool) (g x) (g y)) =
                  {y | g y IN (d (g x))}` SUBST1_TAC
    THENL [SET_TAC[]; ASM_SIMP_TAC[CONTINUOUS_OPEN_PREIMAGE_UNIV]];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\(x,k). (g:real^M->real^N) x, IMAGE g k) p`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      REWRITE_TAC[fine; lemma0] THEN
      STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      ASM SET_TAC[]] THEN
    SUBGOAL_THEN
     `interval[a,b] = IMAGE ((g:real^M->real^N) o h) (interval[a,b])`
    SUBST1_TAC THENL [SIMP_TAC[o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?u v. IMAGE (h:real^N->real^M) (interval[a,b]) =
                        interval[u,v]`
    (REPEAT_TCL CHOOSE_THEN
      (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)) THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[lemma0] THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
      DISCH_TAC THEN
      UNDISCH_TAC
       `!x:real^M k.
             x,k IN p
             ==> x IN k /\
                 k SUBSET interval[u,v] /\
                 ?w z. k = interval[w,z]` THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
       [SET_TAC[];
        REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[IMAGE_o] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[lemma1; GSYM IMAGE_o; lemma2] THEN
      REWRITE_TAC[IMAGE_o; GSYM IMAGE_UNIONS; ETA_AX]] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^M`; `k1:real^M->bool`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x2:real^M`; `k2:real^M->bool`] THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!x1:real^M k1:real^M->bool.
             x1,k1 IN p
             ==> (!x2 k2.
                      x2,k2 IN p /\ ~(x1,k1 = x2,k2)
                      ==> interior k1 INTER interior k2 = {})` THEN
    DISCH_THEN(MP_TAC o SPECL [`x1:real^M`; `k1:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`x2:real^M`; `k2:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `interior(IMAGE f s) SUBSET IMAGE f (interior s) /\
      interior(IMAGE f t) SUBSET IMAGE f (interior t) /\
      (!x y. f x = f y ==> x = y)
      ==> interior s INTER interior t = {}
          ==> interior(IMAGE f s) INTER interior(IMAGE f t) = {}`) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC INTERIOR_IMAGE_SUBSET) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) VSUM_IMAGE
                (lhand(rand(lhand(lhand w)))))) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `abs r` THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> &0 < abs x`] THEN
  REWRITE_TAC[GSYM NORM_MUL] THEN ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a * b ==> x = y ==> y < b * a`)) THEN
  AP_TERM_TAC THEN REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_MUL_LID; GSYM VSUM_LMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM; VECTOR_MUL_ASSOC] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC[TAGGED_DIVISION_OF]);;

(* ------------------------------------------------------------------------- *)
(* Special case of a basic affine transformation.                            *)
(* ------------------------------------------------------------------------- *)

let INTERVAL_IMAGE_AFFINITY_INTERVAL = prove
 (`!a b m c. ?u v. IMAGE (\x. m % x + c) (interval[a,b]) = interval[u,v]`,
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  MESON_TAC[EMPTY_AS_INTERVAL]);;

let CONTENT_IMAGE_AFFINITY_INTERVAL = prove
 (`!a b:real^N m c.
        content(IMAGE (\x. m % x + c) (interval[a,b])) =
        (abs m) pow (dimindex(:N)) * content(interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTENT_EMPTY; REAL_MUL_RZERO] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN COND_CASES_TAC THEN
  W(fun (asl,w) -> MP_TAC(PART_MATCH (lhand o rand) CONTENT_CLOSED_INTERVAL
                (lhs w))) THEN
  (ANTS_TAC THENL
    [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  REAL_LE_RADD; REAL_LE_LMUL] THEN
     ONCE_REWRITE_TAC[REAL_ARITH `m * b <= m * a <=> --m * a <= --m * b`] THEN
     ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> &0 <= --x`; REAL_LE_LMUL];
     ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[GSYM PRODUCT_CONST_NUMSEG_1] THEN
  ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; GSYM PRODUCT_MUL_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_NUMSEG; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_INTEGRAL_AFFINITY = prove
 (`!f:real^M->real^N i a b m c.
        (f has_integral i) (interval[a,b]) /\ ~(m = &0)
        ==> ((\x. f(m % x + c)) has_integral
             (inv(abs(m) pow dimindex(:M)) % i))
            (IMAGE (\x. inv m % x + --(inv(m) % c)) (interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_TWIDDLE THEN
  ASM_SIMP_TAC[INTERVAL_IMAGE_AFFINITY_INTERVAL; GSYM REAL_ABS_NZ;
        REAL_POW_LT; PRODUCT_EQ_0_NUMSEG; CONTENT_IMAGE_AFFINITY_INTERVAL] THEN
  ASM_SIMP_TAC[CONTINUOUS_CMUL; CONTINUOUS_AT_ID; CONTINUOUS_CONST;
               CONTINUOUS_ADD] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV] THEN
  CONJ_TAC THEN VECTOR_ARITH_TAC);;

let INTEGRABLE_AFFINITY = prove
 (`!f:real^M->real^N a b m c.
        f integrable_on interval[a,b] /\ ~(m = &0)
        ==> (\x. f(m % x + c)) integrable_on
            (IMAGE (\x. inv m % x + --(inv(m) % c)) (interval[a,b]))`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_AFFINITY]);;

(* ------------------------------------------------------------------------- *)
(* Special case of stretching coordinate axes separately.                    *)
(* ------------------------------------------------------------------------- *)

let CONTENT_IMAGE_STRETCH_INTERVAL = prove
 (`!a b:real^N m.
        content(IMAGE (\x. lambda k. m k * x$k) (interval[a,b]):real^N->bool) =
        abs(product(1..dimindex(:N)) m) * content(interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[content; IMAGE_EQ_EMPTY] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; LAMBDA_BETA;
               REAL_ARITH `min a b <= max a b`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `max a b - min a b = abs(b - a)`;
                  GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG;
               REAL_ARITH `a <= b ==> abs(b - a) = b - a`] THEN
  ASM_SIMP_TAC[PRODUCT_ABS; FINITE_NUMSEG]);;

let HAS_INTEGRAL_STRETCH = prove
 (`!f:real^M->real^N i m a b.
        (f has_integral i) (interval[a,b]) /\
        (!k. 1 <= k /\ k <= dimindex(:M) ==>  ~(m k = &0))
        ==> ((\x:real^M. f(lambda k. m k * x$k)) has_integral
             (inv(abs(product(1..dimindex(:M)) m)) % i))
            (IMAGE (\x. lambda k. inv(m k) * x$k) (interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_TWIDDLE THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_MUL_RINV; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; PRODUCT_EQ_0_NUMSEG] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    SIMP_TAC[linear; LAMBDA_BETA; CART_EQ; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CONTENT_IMAGE_STRETCH_INTERVAL] THEN
    REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN MESON_TAC[EMPTY_AS_INTERVAL]]);;

let INTEGRABLE_STRETCH = prove
 (`!f:real^M->real^N m a b.
        f integrable_on interval[a,b] /\
        (!k. 1 <= k /\ k <= dimindex(:M) ==>  ~(m k = &0))
        ==> (\x:real^M. f(lambda k. m k * x$k)) integrable_on
            (IMAGE (\x. lambda k. inv(m k) * x$k) (interval[a,b]))`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_STRETCH]);;

(* ------------------------------------------------------------------------- *)
(* Even more special cases.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_REFLECT_LEMMA = prove
 (`!f:real^M->real^N i a b.
     (f has_integral i) (interval[a,b])
     ==> ((\x. f(--x)) has_integral i) (interval[--b,--a])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o C CONJ (REAL_ARITH `~(-- &1 = &0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  DISCH_THEN(MP_TAC o SPEC `vec 0:real^M`) THEN
  REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0] THEN
  REWRITE_TAC[REAL_INV_NEG; REAL_INV_1] THEN
  REWRITE_TAC[VECTOR_ARITH `-- &1 % x + vec 0 = --x`] THEN
  REWRITE_TAC[VECTOR_MUL_LID] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[INTERVAL_EQ_EMPTY] THEN
  REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
  SIMP_TAC[VECTOR_NEG_COMPONENT; REAL_LT_NEG2]);;

let HAS_INTEGRAL_REFLECT = prove
 (`!f:real^M->real^N i a b.
     ((\x. f(--x)) has_integral i) (interval[--b,--a]) <=>
     (f has_integral i) (interval[a,b])`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_REFLECT_LEMMA) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let INTEGRABLE_REFLECT = prove
 (`!f:real^M->real^N a b.
     (\x. f(--x)) integrable_on (interval[--b,--a]) <=>
     f integrable_on (interval[a,b])`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_REFLECT]);;

let INTEGRAL_REFLECT = prove
 (`!f:real^M->real^N a b.
     integral (interval[--b,--a]) (\x. f(--x)) =
     integral (interval[a,b]) f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_REFLECT]);;

(* ------------------------------------------------------------------------- *)
(* Technical lemmas about how many non-trivial intervals of a division a     *)
(* point can be in (we sometimes need this for bounding sums).               *)
(* ------------------------------------------------------------------------- *)

let DIVISION_COMMON_POINT_BOUND = prove
 (`!d s:real^N->bool x.
        d division_of s
        ==> CARD {k | k IN d /\ ~(content k = &0) /\ x IN k}
            <= 2 EXP (dimindex(:N))`,
  let lemma = prove
   (`!f s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
           FINITE s /\ CARD(IMAGE f s) <= n
           ==> CARD(s) <= n`,
    MESON_TAC[CARD_IMAGE_INJ]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. k IN d ==> ?a b:real^N. interval[a,b] = k` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`A:(real^N->bool)->real^N`; `B:(real^N->bool)->real^N`] THEN
  STRIP_TAC THEN MATCH_MP_TAC(ISPEC
   `\d. (lambda i. (x:real^N)$i = (A:(real^N->bool)->real^N)(d)$i):bool^N`
   lemma) THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[division_of];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(:bool^N)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[SUBSET_UNIV] THEN
      SIMP_TAC[FINITE_CART_UNIV; FINITE_BOOL];
      SIMP_TAC[FINITE_BOOL; CARD_CART_UNIV; CARD_BOOL; LE_REFL]]] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
  SIMP_TAC[IN_ELIM_THM; CART_EQ; LAMBDA_BETA] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(MP_TAC o SPECL [`k:real^N->bool`; `l:real^N->bool`] o
        el 2 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[GSYM INTERIOR_INTER] THEN
  MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
  MAP_EVERY UNDISCH_TAC
   [`(x:real^N) IN k`; `(x:real^N) IN l`;
    `~(content(k:real^N->bool) = &0)`;
    `~(content(l:real^N->bool) = &0)`] THEN
  SUBGOAL_THEN
   `k = interval[A k:real^N,B k] /\ l = interval[A l,B l]`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [ASM_MESON_TAC[]; REWRITE_TAC[INTER_INTERVAL]] THEN
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL] THEN
  SIMP_TAC[IN_INTERVAL; INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let TAGGED_PARTIAL_DIVISION_COMMON_POINT_BOUND = prove
 (`!p s:real^N->bool y.
        p tagged_partial_division_of s
        ==> CARD {(x,k) | (x,k) IN p /\ y IN k /\ ~(content k = &0)}
            <= 2 EXP (dimindex(:N))`,
  let lemma = prove
   (`!f s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
           FINITE s /\ CARD(IMAGE f s) <= n
           ==> CARD(s) <= n`,
    MESON_TAC[CARD_IMAGE_INJ]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `SND` lemma) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IMP_CONJ; FORALL_IN_GSPEC; RIGHT_FORALL_IMP_THM; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `k1:real^N->bool`] THEN
    REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x2:real^N`; `k2:real^N->bool`] THEN
    REPEAT DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x1:real^N`; `k1:real^N->bool`; `x2:real^N`; `k2:real^N->bool`] o
     CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
    REWRITE_TAC[INTER_ACI] THEN
    ASM_MESON_TAC[CONTENT_EQ_0_INTERIOR; tagged_partial_division_of];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:real^N#(real^N->bool)->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; SET_TAC[]];
    FIRST_ASSUM(MP_TAC o MATCH_MP PARTIAL_DIVISION_OF_TAGGED_DIVISION) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o
      MATCH_MP DIVISION_COMMON_POINT_BOUND) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN MESON_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_MESON_TAC[tagged_partial_division_of]]]);;

let TAGGED_PARTIAL_DIVISION_COMMON_TAGS = prove
 (`!p s:real^N->bool x.
        p tagged_partial_division_of s
        ==> CARD {(x,k) | k | (x,k) IN p /\ ~(content k = &0)}
            <= 2 EXP (dimindex(:N))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o
   MATCH_MP TAGGED_PARTIAL_DIVISION_COMMON_POINT_BOUND) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN
    ASM_MESON_TAC[tagged_partial_division_of];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:real^N#(real^N->bool)->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Integrating characteristic function of an interval.                       *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_RESTRICT_OPEN_SUBINTERVAL = prove
 (`!f:real^M->real^N a b c d i.
        (f has_integral i) (interval[c,d]) /\
        interval[c,d] SUBSET interval[a,b]
        ==> ((\x. if x IN interval(c,d) then f x else vec 0) has_integral i)
             (interval[a,b])`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[c:real^M,d] = {}` THENL
   [FIRST_ASSUM(MP_TAC o AP_TERM
     `interior:(real^M->bool)->(real^M->bool)`) THEN
    SIMP_TAC[INTERIOR_CLOSED_INTERVAL; INTERIOR_EMPTY] THEN
    ASM_SIMP_TAC[NOT_IN_EMPTY; HAS_INTEGRAL_0_EQ; HAS_INTEGRAL_EMPTY_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `g:real^M->real^N =
                 \x. if x IN interval(c,d) then f x else vec 0` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP PARTIAL_DIVISION_EXTEND_1) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`lifted((+):real^N->real^N->real^N)`;
    `p:(real^M->bool)->bool`;
    `a:real^M`; `b:real^M`;
    `\i. if (g:real^M->real^N) integrable_on i
         then SOME (integral i g) else NONE`]
   OPERATIVE_DIVISION) THEN
  ASM_SIMP_TAC[OPERATIVE_INTEGRAL; MONOIDAL_LIFTED; MONOIDAL_VECTOR_ADD] THEN
  SUBGOAL_THEN
   `iterate (lifted (+)) p
     (\i. if (g:real^M->real^N) integrable_on i
          then SOME (integral i g) else NONE) =
    SOME i`
  SUBST1_TAC THENL
   [ALL_TAC;
    COND_CASES_TAC THEN
    REWRITE_TAC[distinctness "option"; injectivity "option"] THEN
    ASM_MESON_TAC[INTEGRABLE_INTEGRAL]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s ==> s = x INSERT (s DELETE x)`)) THEN
  ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_LIFTED; MONOIDAL_VECTOR_ADD;
               FINITE_DELETE; IN_DELETE] THEN
  SUBGOAL_THEN `(g:real^M->real^N) integrable_on interval[c,d]`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
    MATCH_MP_TAC INTEGRABLE_SPIKE_INTERIOR THEN
    EXPAND_TAC "g" THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `iterate (lifted (+)) (p DELETE interval[c,d])
      (\i. if (g:real^M->real^N) integrable_on i
           then SOME (integral i g) else NONE) = SOME(vec 0)`
  SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[lifted; VECTOR_ADD_RID] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_INTEGRAL_SPIKE_INTERIOR THEN
    EXISTS_TAC `f:real^M->real^N` THEN
    EXPAND_TAC "g" THEN ASM_SIMP_TAC[]] THEN
  SIMP_TAC[GSYM NEUTRAL_VECTOR_ADD; GSYM NEUTRAL_LIFTED;
           MONOIDAL_VECTOR_ADD] THEN
  MATCH_MP_TAC(MATCH_MP ITERATE_EQ_NEUTRAL
        (MATCH_MP MONOIDAL_LIFTED(SPEC_ALL MONOIDAL_VECTOR_ADD))) THEN
  SIMP_TAC[NEUTRAL_LIFTED; NEUTRAL_VECTOR_ADD; MONOIDAL_VECTOR_ADD] THEN
  X_GEN_TAC `k:real^M->bool` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((g:real^M->real^N) has_integral (vec 0)) k`
   (fun th -> MESON_TAC[th; integrable_on; INTEGRAL_UNIQUE]) THEN
  SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_INTERIOR THEN
  EXISTS_TAC `(\x. vec 0):real^M->real^N` THEN
  REWRITE_TAC[HAS_INTEGRAL_0] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`interval[c:real^M,d]`; `interval[u:real^M,v]`]) THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM SET_TAC[]);;

let HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL = prove
 (`!f:real^M->real^N a b c d i.
        (f has_integral i) (interval[c,d]) /\
        interval[c,d] SUBSET interval[a,b]
        ==> ((\x. if x IN interval[c,d] then f x else vec 0) has_integral i)
             (interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_RESTRICT_OPEN_SUBINTERVAL) THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
    HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `interval[c:real^M,d] DIFF interval(c,d)` THEN
  REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN REWRITE_TAC[IN_DIFF] THEN
  MP_TAC(ISPECL [`c:real^M`; `d:real^M`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  SET_TAC[]);;

let HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ = prove
 (`!f:real^M->real^N a b c d i.
        interval[c,d] SUBSET interval[a,b]
        ==> (((\x. if x IN interval[c,d] then f x else vec 0) has_integral i)
              (interval[a,b]) <=>
             (f has_integral i) (interval[c,d]))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[c:real^M,d] = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; HAS_INTEGRAL_0_EQ; HAS_INTEGRAL_EMPTY_EQ];
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL] THEN
  SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[c,d]` MP_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. if x IN interval[c:real^M,d]
                    then f x:real^N else vec 0` THEN
    SIMP_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    ASM_MESON_TAC[integrable_on];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  MP_TAC(ASSUME `interval[c:real^M,d] SUBSET interval[a,b]`) THEN
  REWRITE_TAC[IMP_IMP] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL) THEN
  ASM_MESON_TAC[HAS_INTEGRAL_UNIQUE; INTEGRABLE_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can apply the limit process uniformly to all integrals.          *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL = prove
 (`!f:real^M->real^N i s.
     (f has_integral i) s <=>
        !e. &0 < e
            ==> ?B. &0 < B /\
                    !a b. ball(vec 0,B) SUBSET interval[a,b]
                          ==> ?z. ((\x. if x IN s then f(x) else vec 0)
                                   has_integral z) (interval[a,b]) /\
                                  norm(z - i) < e`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [has_integral_alt] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(X_CHOOSE_THEN `a:real^M` (X_CHOOSE_THEN `b:real^M`
   SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^M`] (CONJUNCT1 BOUNDED_INTERVAL)) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    EXISTS_TAC `B + &1` THEN ASM_SIMP_TAC[REAL_LT_ADD; REAL_LT_01] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN
    REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    DISCH_TAC THEN EXISTS_TAC `i:real^N` THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    MATCH_MP_TAC HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVAL THEN
    ASM_MESON_TAC[SUBSET; REAL_ARITH `n <= B ==> n < B + &1`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?y. ((f:real^M->real^N) has_integral y) (interval[a,b])`
  MP_TAC THENL
   [SUBGOAL_THEN
     `?c d. interval[a,b] SUBSET interval[c,d] /\
            (\x. if x IN interval[a,b] then (f:real^M->real^N) x
                 else vec 0) integrable_on interval[c,d]`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP REAL_LT_01) THEN
      DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `c:real^M = lambda i. --(max B C)` THEN
      ABBREV_TAC `d:real^M = lambda i. max B C` THEN
      MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN
        DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
        X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
        SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
        ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
        MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^M`; `d:real^M`]) THEN ANTS_TAC THENL
       [REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
        X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
        SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
        ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
        MATCH_MP_TAC(REAL_ARITH `x < C ==> x <= max B C`) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MESON_TAC[integrable_on];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [integrable_on]) THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  SUBGOAL_THEN `i:real^N = y` ASSUME_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH `~(&0 < norm(y - i)) ==> i = y`) THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `norm(y - i:real^N)`) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `C:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  ABBREV_TAC `c:real^M = lambda i. --(max B C)` THEN
  ABBREV_TAC `d:real^M = lambda i. max B C` THEN
  MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
    X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
    SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    MATCH_MP_TAC(REAL_ARITH `x < C ==> x <= max B C`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^M,b] SUBSET interval[c,d]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_INTERVAL] THEN
    X_GEN_TAC `k:num` THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
    SIMP_TAC[LAMBDA_BETA; REAL_BOUNDS_LE] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_CLOSED_SUBINTERVALS_EQ] THEN
  ASM_MESON_TAC[REAL_LT_REFL; HAS_INTEGRAL_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* Hence a general restriction property.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_RESTRICT = prove
 (`!f:real^M->real^N s t i.
        s SUBSET t
        ==> (((\x. if x IN s then f x else vec 0) has_integral i) t <=>
             (f has_integral i) s)`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[MESON[] `(if p then if q then x else y else y) =
                            (if q then if p then x else y else y)`] THEN
  ASM_SIMP_TAC[]);;

let INTEGRAL_RESTRICT = prove
 (`!f:real^M->real^N s t.
        s SUBSET t
        ==> integral t (\x. if x IN s then f x else vec 0) =
            integral s f`,
  SIMP_TAC[integral; HAS_INTEGRAL_RESTRICT]);;

let INTEGRABLE_RESTRICT = prove
 (`!f:real^M->real^N s t.
        s SUBSET t
        ==> ((\x. if x IN s then f x else vec 0) integrable_on t <=>
             f integrable_on s)`,
  SIMP_TAC[integrable_on; HAS_INTEGRAL_RESTRICT]);;

let HAS_INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real^M->real^N s i.
        ((\x. if x IN s then f x else vec 0) has_integral i) (:real^M) <=>
         (f has_integral i) s`,
  SIMP_TAC[HAS_INTEGRAL_RESTRICT; SUBSET_UNIV]);;

let INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real^M->real^N s.
        integral (:real^M) (\x. if x IN s then f x else vec 0) =
        integral s f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_RESTRICT_UNIV]);;

let INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else vec 0) integrable_on (:real^M) <=>
         f integrable_on s`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_RESTRICT_UNIV]);;

let HAS_INTEGRAL_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        ((\x. if x IN s then f x else vec 0) has_integral i) t <=>
        (f has_integral i) (s INTER t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[IN_INTER] THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let INTEGRAL_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        integral t (\x. if x IN s then f x else vec 0) =
        integral (s INTER t) f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_RESTRICT_INTER]);;

let INTEGRABLE_RESTRICT_INTER = prove
 (`!f:real^M->real^N s t.
        (\x. if x IN s then f x else vec 0) integrable_on t <=>
        f integrable_on (s INTER t)`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_RESTRICT_INTER]);;

let HAS_INTEGRAL_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ (f has_integral i) s
        ==> (f has_integral i) t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_MESON_TAC[]);;

let INTEGRABLE_ON_SUPERSET = prove
 (`!f s t.
        (!x. ~(x IN s) ==> f x = vec 0) /\ s SUBSET t /\ f integrable_on s
        ==> f integrable_on t`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_ON_SUPERSET]);;

let NEGLIGIBLE_ON_INTERVALS = prove
 (`!s. negligible s <=> !a b:real^N. negligible(s INTER interval[a,b])`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[negligible] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  FIRST_ASSUM(ASSUME_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
  EXISTS_TAC `s INTER interval[a:real^N,b]` THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[indicator; IN_DIFF; IN_INTER] THEN
  MESON_TAC[]);;

let HAS_INTEGRAL_SPIKE_SET_EQ = prove
 (`!f:real^M->real^N s t y.
        negligible(s DIFF t UNION t DIFF s)
        ==> ((f has_integral y) s <=> (f has_integral y) t)`,
  REPEAT STRIP_TAC THEN  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ THEN
  EXISTS_TAC `s DIFF t UNION t DIFF s:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let HAS_INTEGRAL_SPIKE_SET = prove
 (`!f:real^M->real^N s t y.
        negligible(s DIFF t UNION t DIFF s) /\
        (f has_integral y) s
        ==> (f has_integral y) t`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_SET_EQ]);;

let INTEGRABLE_SPIKE_SET = prove
 (`!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> f integrable_on s ==> f integrable_on t`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_SPIKE_SET_EQ]);;

let INTEGRABLE_SPIKE_SET_EQ = prove
 (`!f:real^M->real^N s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> (f integrable_on s <=> f integrable_on t)`,
  MESON_TAC[INTEGRABLE_SPIKE_SET; UNION_COMM]);;

let INTEGRAL_SPIKE_SET = prove
 (`!f:real^M->real^N g s t.
        negligible(s DIFF t UNION t DIFF s)
        ==> integral s f = integral t f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[integral] THEN
  AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  ASM_MESON_TAC[]);;

let HAS_INTEGRAL_INTERIOR = prove
 (`!f:real^M->real^N y s.
        negligible(frontier s)
        ==> ((f has_integral y) (interior s) <=> (f has_integral y) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

let HAS_INTEGRAL_CLOSURE = prove
 (`!f:real^M->real^N y s.
        negligible(frontier s)
        ==> ((f has_integral y) (closure s) <=> (f has_integral y) s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SPIKE_SET_EQ THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  REWRITE_TAC[frontier] THEN
  MP_TAC(ISPEC `s:real^M->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^M->bool` CLOSURE_SUBSET) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas that are useful later.                                        *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SUBSET_COMPONENT_LE = prove
 (`!f:real^M->real^N s t i j k.
        s SUBSET t /\ (f has_integral i) s /\ (f has_integral j) t /\
        1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN t ==> &0 <= f(x)$k)
        ==> i$k <= j$k`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_COMPONENT_LE THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN s then f x else vec 0):real^M->real^N`;
    `(\x. if x IN t then f x else vec 0):real^M->real^N`;
    `(:real^M)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
  ASM_SIMP_TAC[VEC_COMPONENT] THEN ASM SET_TAC[]);;

let INTEGRAL_SUBSET_COMPONENT_LE = prove
 (`!f:real^M->real^N s t k.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        1 <= k /\ k <= dimindex(:N) /\
        (!x. x IN t ==> &0 <= f(x)$k)
        ==> (integral s f)$k <= (integral t f)$k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SUBSET_COMPONENT_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_SUBSET_DROP_LE = prove
 (`!f:real^M->real^1 s t i j.
        s SUBSET t /\ (f has_integral i) s /\ (f has_integral j) t /\
        (!x. x IN t ==> &0 <= drop(f x))
        ==> drop i <= drop j`,
  REWRITE_TAC[drop] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SUBSET_COMPONENT_LE THEN
  REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN ASM_MESON_TAC[]);;

let INTEGRAL_SUBSET_DROP_LE = prove
 (`!f:real^M->real^1 s t.
        s SUBSET t /\ f integrable_on s /\ f integrable_on t /\
        (!x. x IN t ==> &0 <= drop(f(x)))
        ==> drop(integral s f) <= drop(integral t f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_INTEGRAL_SUBSET_DROP_LE THEN
  ASM_MESON_TAC[INTEGRABLE_INTEGRAL]);;

let HAS_INTEGRAL_ALT = prove
 (`!f:real^M->real^N s i.
        (f has_integral i) s <=>
            (!a b. (\x. if x IN s then f x else vec 0)
                   integrable_on interval[a,b]) /\
            (!e. &0 < e
                 ==> ?B. &0 < B /\
                         !a b. ball (vec 0,B) SUBSET interval[a,b]
                               ==> norm(integral(interval[a,b])
                                          (\x. if x IN s then f x else vec 0) -
                                        i) < e)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL] THEN
  SPEC_TAC(`\x. if x IN s then (f:real^M->real^N) x else vec 0`,
           `f:real^M->real^N`) THEN
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[INTEGRAL_UNIQUE; integrable_on]] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[INTEGRAL_UNIQUE]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  POP_ASSUM(MP_TAC o C MATCH_MP REAL_LT_01) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
  EXISTS_TAC `(lambda i. min ((a:real^M)$i) (--B)):real^M` THEN
  EXISTS_TAC `(lambda i. max ((b:real^M)$i) B):real^M` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
     [`(lambda i. min ((a:real^M)$i) (--B)):real^M`;
      `(lambda i. max ((b:real^M)$i) B):real^M`]) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[integrable_on]];
    SIMP_TAC[SUBSET; IN_INTERVAL; IN_BALL; LAMBDA_BETA;
             REAL_MIN_LE; REAL_LE_MAX]] THEN
  SIMP_TAC[SUBSET; IN_BALL; IN_INTERVAL; LAMBDA_BETA] THEN
  GEN_TAC THEN REWRITE_TAC[NORM_ARITH `dist(vec 0,x) = norm x`] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
    `abs(x) <= B ==> min a (--B) <= x /\ x <= max b B`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^M)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; COMPONENT_LE_NORM]);;

let INTEGRABLE_ALT = prove
 (`!f:real^M->real^N s.
        f integrable_on s <=>
          (!a b. (\x. if x IN s then f x else vec 0) integrable_on
                 interval[a,b]) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !a b c d.
                          ball(vec 0,B) SUBSET interval[a,b] /\
                          ball(vec 0,B) SUBSET interval[c,d]
                          ==> norm(integral (interval[a,b])
                                    (\x. if x IN s then f x else vec 0) -
                                   integral (interval[c,d])
                                    (\x. if x IN s then f x else vec 0)) < e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [integrable_on] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    MESON_TAC[NORM_ARITH `norm(a - y) < e / &2 /\ norm(b - y) < e / &2
                          ==> norm(a - b) < e`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `cauchy (\n. integral (interval[(lambda i. --(&n)),(lambda i. &n)])
                         (\x. if x IN s then (f:real^M->real^N) x else vec 0))`
  MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `B:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`] THEN
    CONJ_TAC;
    REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:real^N` THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN DISCH_THEN(LABEL_TAC "C") THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "C" (MP_TAC o SPEC `e / &2`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` ASSUME_TAC) THEN
    MP_TAC(SPEC `max (&N) B` REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC[REAL_MAX_LE; REAL_OF_NUM_LE] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&n` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(i1 - i2) < e / &2 ==> dist(i1,i) < e / &2 ==> norm(i2 - i) < e`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^M,&n)` THEN
    ASM_SIMP_TAC[SUBSET_BALL] THEN
    REWRITE_TAC[SUBSET; IN_BALL; NORM_ARITH `dist(vec 0,x) = norm x`]] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_BOUNDS_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(x:real^M)` THEN ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM REAL_OF_NUM_GE] THEN
  REAL_ARITH_TAC);;

let INTEGRABLE_ALT_SUBSET = prove
 (`!f:real^M->real^N s.
        f integrable_on s <=>
          (!a b. (\x. if x IN s then f x else vec 0) integrable_on
                 interval[a,b]) /\
          (!e. &0 < e
               ==> ?B. &0 < B /\
                       !a b c d.
                          ball(vec 0,B) SUBSET interval[a,b] /\
                          interval[a,b] SUBSET interval[c,d]
                          ==> norm(integral (interval[a,b])
                                    (\x. if x IN s then f x else vec 0) -
                                   integral (interval[c,d])
                                    (\x. if x IN s then f x else vec 0)) < e)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [INTEGRABLE_ALT] THEN
  ABBREV_TAC `g:real^M->real^N = \x. if x IN s then f x else vec 0` THEN
  POP_ASSUM(K ALL_TAC) THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real^M`; `d:real^M`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(lambda i. max ((a:real^M)$i) ((c:real^M)$i)):real^M`;
    `(lambda i. min ((b:real^M)$i) ((d:real^M)$i)):real^M`]) THEN
  ASM_REWRITE_TAC[GSYM INTER_INTERVAL; SUBSET_INTER] THEN
  DISCH_THEN(fun th ->
    MP_TAC(ISPECL [`a:real^M`; `b:real^M`] th) THEN
    MP_TAC(ISPECL [`c:real^M`; `d:real^M`] th)) THEN
  ASM_REWRITE_TAC[INTER_SUBSET] THEN NORM_ARITH_TAC);;

let INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real^M->real^N s a b.
        f integrable_on s /\ interval[a,b] SUBSET s
        ==> f integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [INTEGRABLE_ALT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONJUNCT1) ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] INTEGRABLE_EQ) THEN
  ASM SET_TAC[]);;

let INTEGRAL_SPLIT = prove
 (`!f:real^M->real^N a b t k.
        f integrable_on interval[a,b] /\ 1 <= k /\ k <= dimindex(:M)
        ==> integral (interval[a,b]) f =
                integral(interval
                 [a,(lambda i. if i = k then min (b$k) t else b$i)]) f +
                integral(interval
                 [(lambda i. if i = k then max (a$k) t else a$i),b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPLIT THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `t:real`] THEN
  ASM_SIMP_TAC[INTERVAL_SPLIT; GSYM HAS_INTEGRAL_INTEGRAL] THEN
  CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN
  ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let INTEGRAL_SPLIT_SIGNED = prove
 (`!f:real^M->real^N a b t k.
        1 <= k /\ k <= dimindex(:M) /\ a$k <= t /\ a$k <= b$k /\
        f integrable_on
        interval[a,(lambda i. if i = k then max (b$k) t else b$i)]
        ==> integral (interval[a,b]) f =
                integral(interval
                 [a,(lambda i. if i = k then t else b$i)]) f +
                (if b$k < t then -- &1 else &1) %
                integral(interval
                 [(lambda i. if i = k then min (b$k) t else a$i),
                  (lambda i. if i = k then max (b$k) t else b$i)]) f`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL
    [`f:real^M->real^N`;
     `a:real^M`;
     `(lambda i. if i = k then t else (b:real^M)$i):real^M`;
     `(b:real^M)$k`; `k:num`]
        INTEGRAL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL)) THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
       `x = y /\ w = z
        ==> x:real^N = (y + z) + --(&1) % w`) THEN
      CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ; CART_EQ] THEN TRY CONJ_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN
      GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(ISPECL
    [`f:real^M->real^N`;
     `a:real^M`;
     `b:real^M`;
     `t:real`; `k:num`]
        INTEGRAL_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL)) THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
      BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ; CART_EQ] THEN TRY CONJ_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA] THEN
      GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION = prove
 (`!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b]
        ==> integral(interval[a,d]) f =
                vsum {s | s SUBSET 1..dimindex(:M)}
                    (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                         integral
                          (interval[(lambda i. if i IN s
                                               then min (c$i) (d$i)
                                               else (a:real^M)$i),
                                    (lambda i. if i IN s
                                               then max (c$i) (d$i)
                                               else c$i)]) f)`,
  let lemma1 = prove
   (`!f:(num->bool)->real^N n.
          vsum {s | s SUBSET 1..SUC n} f =
          vsum {s | s SUBSET 1..n} f +
          vsum {s | s SUBSET 1..n} (\s. f(SUC n INSERT s))`,
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`; POWERSET_CLAUSES] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_UNION o lhs o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POWERSET; FINITE_NUMSEG] THEN
      REWRITE_TAC[SET_RULE
       `DISJOINT s (IMAGE f t) <=> !x. x IN t ==> ~(f x IN s)`] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM; SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `SUC n`) THEN
      REWRITE_TAC[IN_INSERT; IN_NUMSEG] THEN ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] VSUM_IMAGE) THEN
      SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG] THEN
      MAP_EVERY X_GEN_TAC [`s:num->bool`; `t:num->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC(SET_RULE
       `~(a IN i)
        ==> s SUBSET i /\ t SUBSET i /\ a INSERT s = a INSERT t
            ==> s = t`) THEN
      REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]) in
  let lemma2 = prove
   (`!f:real^M->real^N m a:real^M c:real^M d:real^M.
          f integrable_on (:real^M) /\ m <= dimindex(:M) /\
          (!i. m < i /\ i <= dimindex(:M) ==> a$i = c$i \/ d$i = c$i) /\
          (!i. m < i /\ i <= dimindex(:M) ==> a$i = c$i ==> a$i = d$i) /\
          (!i. 1 <= i /\ i <= dimindex(:M) ==> a$i <= c$i /\ a$i <= d$i)
          ==> integral(interval[a,d]) f =
                  vsum {s | s SUBSET 1..m}
                      (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                           integral
                            (interval[(lambda i. if i IN s
                                                 then min (c$i) (d$i)
                                                 else (a:real^M)$i),
                                      (lambda i. if i IN s
                                                 then max (c$i) (d$i)
                                                 else c$i)]) f)`,
    GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[NUMSEG_CLAUSES; ARITH; SUBSET_EMPTY; SING_GSPEC] THEN
      REWRITE_TAC[VSUM_SING; NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES] THEN
      REWRITE_TAC[real_pow; LAMBDA_ETA; VECTOR_MUL_LID] THEN
      REWRITE_TAC[ARITH_RULE `0 < i <=> 1 <= i`] THEN REPEAT STRIP_TAC THEN
      ASM_CASES_TAC
       `?k. 1 <= k /\ k <= dimindex(:M) /\ (a:real^M)$k = (c:real^M)$k`
      THENL
       [MATCH_MP_TAC(MESON[] `i = vec 0 /\ j = vec 0 ==> i:real^N = j`) THEN
        CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_NULL THEN
        REWRITE_TAC[CONTENT_EQ_0] THEN ASM_MESON_TAC[];
        SUBGOAL_THEN `d:real^M = c:real^M` (fun th -> REWRITE_TAC[th]) THEN
        REWRITE_TAC[CART_EQ] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[lemma1] THEN
    SUBGOAL_THEN
     `!s. s SUBSET 1..m
          ==> --(&1) pow CARD {i | i IN SUC m INSERT s /\ d$i < c$i} =
              (if (d:real^M)$(SUC m) < (c:real^M)$(SUC m) then -- &1 else &1) *
              --(&1) pow CARD {i | i IN s /\ d$i < c$i}`
     (fun th -> SIMP_TAC[th; IN_ELIM_THM]) THENL
     [X_GEN_TAC `s:num->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `FINITE(s:num->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[FINITE_NUMSEG; FINITE_SUBSET]; ALL_TAC] THEN
      COND_CASES_TAC THENL
       [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT; SET_RULE
         `P a ==> {x | x IN a INSERT s /\ P x} =
                  a INSERT {x | x IN s /\ P x}`] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[real_pow] THEN
        SUBGOAL_THEN `~(SUC m IN 1..m)` (fun th -> ASM SET_TAC[th]) THEN
        REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
        ASM_SIMP_TAC[REAL_MUL_LID; SET_RULE
         `~(P a) ==> {x | x IN a INSERT s /\ P x} = {x | x IN s /\ P x}`]];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`f:real^M->real^N`; `a:real^M`; `d:real^M`; `(c:real^M)$SUC m`; `SUC m`]
         INTEGRAL_SPLIT_SIGNED) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`; INTEGRABLE_ON_SUBINTERVAL;
                    SUBSET_UNIV];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    BINOP_TAC THENL [ALL_TAC; AP_TERM_TAC] THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL
       [`a:real^M`;
        `c:real^M`;
        `(lambda i. if i = SUC m then (c:real^M)$SUC m
                    else (d:real^M)$i):real^M`]);
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`(lambda i. if i = SUC m
                    then min ((d:real^M)$SUC m) ((c:real^M)$SUC m)
                    else (a:real^M)$i):real^M`;
        `(lambda i. if i = SUC m
                    then max ((d:real^M)$SUC m) ((c:real^M)$SUC m)
                    else (c:real^M)$i):real^M`;
        `(lambda i. if i = SUC m
                    then max ((d:real^M)$SUC m) ((c:real^M)$SUC m)
                    else d$i):real^M`])] THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN
       CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
       CONJ_TAC THENL
        [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
         SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
         ALL_TAC] THEN
       CONJ_TAC THENL
        [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
         SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
         ASM_MESON_TAC[ARITH_RULE `m < i <=> i = SUC m \/ SUC m < i`];
         X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN TRY REAL_ARITH_TAC THEN
         FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
         ASM_MESON_TAC[]];
       DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
       X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       DISCH_TAC THEN BINOP_TAC THENL
        [AP_TERM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
         X_GEN_TAC `i:num` THEN
         ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[] THEN
         SUBGOAL_THEN `i IN 1..m` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
         REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
         SUBGOAL_THEN `i <= dimindex(:M)` ASSUME_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         ASM_SIMP_TAC[LAMBDA_BETA] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
         AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
         REWRITE_TAC[CONS_11; PAIR_EQ] THEN
         SIMP_TAC[CART_EQ; LAMBDA_BETA; AND_FORALL_THM] THEN
         X_GEN_TAC `i:num` THEN
         ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THEN
         ASM_REWRITE_TAC[] THEN
         ASM_CASES_TAC `(i:num) IN s` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
         COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN TRY REAL_ARITH_TAC THEN
         SUBGOAL_THEN `~(SUC m IN 1..m)` (fun th -> ASM SET_TAC[th]) THEN
         REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]])) in
  REWRITE_TAC[IN_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN interval[a,b] then (f:real^M->real^N) x else vec 0`;
    `dimindex(:M)`; `a:real^M`; `c:real^M`; `d:real^M`]
   lemma2) THEN
  ASM_SIMP_TAC[LTE_ANTISYM; INTEGRABLE_RESTRICT_UNIV; LE_REFL] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `s:num->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN AP_TERM_TAC] THEN
  MATCH_MP_TAC INTEGRAL_EQ THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `i SUBSET j ==> !x. x IN i ==> (if x IN j then f x else b) = f x`) THEN
  ASM_SIMP_TAC[SUBSET_INTERVAL; REAL_LE_REFL; LAMBDA_BETA] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let INTEGRAL_INTERVALS_DIFF_INCLUSION_EXCLUSION = prove
 (`!f:real^M->real^N a b c d.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b]
        ==> integral(interval[a,d]) f - integral(interval[a,c]) f =
                vsum {s | ~(s = {}) /\ s SUBSET 1..dimindex(:M)}
                    (\s. --(&1) pow CARD {i | i IN s /\ d$i < c$i} %
                         integral
                          (interval[(lambda i. if i IN s
                                               then min (c$i) (d$i)
                                               else (a:real^M)$i),
                                    (lambda i. if i IN s
                                               then max (c$i) (d$i)
                                               else c$i)]) f)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o
   MATCH_MP INTEGRAL_INTERVALS_INCLUSION_EXCLUSION) THEN
  REWRITE_TAC[SET_RULE `{s | ~(s = a) /\ P s} = {s | P s} DELETE a`] THEN
  SIMP_TAC[VSUM_DELETE; FINITE_POWERSET; FINITE_NUMSEG; EMPTY_SUBSET;
           IN_ELIM_THM] THEN
  REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; CARD_CLAUSES; LAMBDA_ETA] THEN
  REWRITE_TAC[real_pow; VECTOR_MUL_LID]);;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_RIGHT = prove
 (`!f:real^M->real^N a b c.
        f integrable_on interval[a,b] /\ c IN interval[a,b]
        ==> integral(interval[a,c]) f =
                vsum {s | s SUBSET 1..dimindex (:M)}
                     (\s. --(&1) pow CARD s %
                          integral
                           (interval[(lambda i. if i IN s then c$i else a$i),
                                     b])
                           f)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `a:real^M`; `b:real^M`; `b:real^M`; `c:real^M`]
        INTEGRAL_INTERVALS_INCLUSION_EXCLUSION) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_INTERVAL; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_CASES_TAC `?k. k IN s /\ (c:real^M)$k = (b:real^M)$k` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `1 <= k /\ k <= dimindex(:M)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_NUMSEG; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[] `a:real^N = vec 0 /\ b = vec 0 ==> a = b`) THEN
    CONJ_TAC THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
    MATCH_MP_TAC INTEGRAL_NULL THEN REWRITE_TAC[CONTENT_EQ_0] THEN
    EXISTS_TAC `k:num` THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN BINOP_TAC THENL
   [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[REAL_LT_LE; SUBSET; IN_NUMSEG];
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; PAIR_EQ; LAMBDA_BETA] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_LEFT = prove
 (`!f:real^M->real^N a b c.
        f integrable_on interval[a,b] /\ c IN interval[a,b]
        ==> integral(interval[c,b]) f =
                vsum {s | s SUBSET 1..dimindex (:M)}
                     (\s. --(&1) pow CARD s %
                          integral
                           (interval[a,(lambda i. if i IN s then c$i else b$i)])
                           f)`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`\x. (f:real^M->real^N) (--x)`;
    `--b:real^M`;
    `--a:real^M`;
    `--c:real^M`]
        INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_RIGHT) THEN
  REWRITE_TAC[REAL_ARITH `min (--a) (--b) = --(max a b)`;
              REAL_ARITH `max (--a) (--b) = --(min a b)`;
              VECTOR_NEG_COMPONENT] THEN
  SUBGOAL_THEN
   `!P x y. (lambda i. if P i then --(x i) else --(y i)):real^M =
            --(lambda i. if P i then x i else y i)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SIMP_TAC[CART_EQ; VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTEGRAL_REFLECT; INTEGRABLE_REFLECT;
                  IN_INTERVAL_REFLECT]);;

(* ------------------------------------------------------------------------- *)
(* A straddling criterion for integrability.                                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_STRADDLE_INTERVAL = prove
 (`!f:real^N->real^1 a b.
        (!e. &0 < e
             ==> ?g h i j. (g has_integral i) (interval[a,b]) /\
                           (h has_integral j) (interval[a,b]) /\
                           norm(i - j) < e /\
                           !x. x IN interval[a,b]
                               ==> drop(g x) <= drop(f x) /\
                                   drop(f x) <= drop(h x))
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTEGRABLE_CAUCHY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^1`; `h:real^N->real^1`; `i:real^1`; `j:real^1`] THEN
  REWRITE_TAC[has_integral] THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `(\x. d1 x INTER d2 x):real^N->real^N->bool` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  MAP_EVERY X_GEN_TAC
   [`p1:(real^N#(real^N->bool))->bool`;
    `p2:(real^N#(real^N->bool))->bool`] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `p1:(real^N#(real^N->bool))->bool` th) THEN
   MP_TAC(SPEC `p2:(real^N#(real^N->bool))->bool` th))) THEN
  EVERY_ASSUM(fun th -> try ASSUME_TAC(MATCH_MP TAGGED_DIVISION_OF_FINITE th)
                        with Failure _ -> ALL_TAC) THEN
  ASM_SIMP_TAC[VSUM_REAL] THEN REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN
  SUBST1_TAC(SYM(ISPEC `i:real^1` (CONJUNCT1 LIFT_DROP))) THEN
  SUBST1_TAC(SYM(ISPEC `j:real^1` (CONJUNCT1 LIFT_DROP))) THEN
  REWRITE_TAC[GSYM LIFT_SUB; DROP_CMUL; NORM_LIFT] THEN
  MATCH_MP_TAC(REAL_ARITH
   `g1 - h2 <= f1 - f2 /\ f1 - f2 <= h1 - g2 /\
    abs(i - j) < e / &3
    ==> abs(g2 - i) < e / &3
        ==> abs(g1 - i) < e / &3
            ==> abs(h2 - j) < e / &3
                ==> abs(h1 - j) < e / &3
                    ==> abs(f1 - f2) < e`) THEN
  ASM_REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_LIFT; LIFT_DROP] THEN CONJ_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x <= x' /\ y' <= y ==> x - y <= x' - y'`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_POS_LE; SUBSET]);;

let INTEGRABLE_STRADDLE = prove
 (`!f:real^N->real^1 s.
        (!e. &0 < e
             ==> ?g h i j. (g has_integral i) s /\
                           (h has_integral j) s /\
                           norm(i - j) < e /\
                           !x. x IN s
                               ==> drop(g x) <= drop(f x) /\
                                   drop(f x) <= drop(h x))
        ==> f integrable_on s`,
  let lemma = prove
   (`&0 <= drop x /\ drop x <= drop y ==> norm x <= norm y`,
    REWRITE_TAC[NORM_REAL; GSYM drop] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b. (\x. if x IN s then (f:real^N->real^1) x else vec 0)
          integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[HAS_INTEGRAL_ALT]) THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    MATCH_MP_TAC INTEGRABLE_STRADDLE_INTERVAL THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`g:real^N->real^1`; `h:real^N->real^1`; `i:real^1`; `j:real^1`] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &4`) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &4`) STRIP_ASSUME_TAC) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `B2:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
    DISCH_THEN(X_CHOOSE_THEN `B1:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))) THEN
    MAP_EVERY EXISTS_TAC
     [`\x. if x IN s then (g:real^N->real^1) x else vec 0`;
      `\x. if x IN s then (h:real^N->real^1) x else vec 0`;
      `integral(interval[a:real^N,b])
         (\x. if x IN s then (g:real^N->real^1) x else vec 0:real^1)`;
      `integral(interval[a:real^N,b])
         (\x. if x IN s then (h:real^N->real^1) x else vec 0:real^1)`] THEN
    ASM_SIMP_TAC[INTEGRABLE_INTEGRAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_REFL]] THEN
    ABBREV_TAC `c:real^N = lambda i. min ((a:real^N)$i) (--(max B1 B2))` THEN
    ABBREV_TAC `d:real^N = lambda i. max ((b:real^N)$i) (max B1 B2)` THEN
    REMOVE_THEN "H" (MP_TAC o SPECL [`c:real^N`; `d:real^N`]) THEN
    REMOVE_THEN "G" (MP_TAC o SPECL [`c:real^N`; `d:real^N`]) THEN
    MATCH_MP_TAC(TAUT
        `(a /\ c) /\ (b /\ d ==> e) ==> (a ==> b) ==> (c ==> d) ==> e`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
      SIMP_TAC[SUBSET; IN_BALL; IN_INTERVAL; LAMBDA_BETA] THEN
      GEN_TAC THEN REWRITE_TAC[NORM_ARITH `dist(vec 0,x) = norm x`] THEN
      DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
        `abs(x) <= B ==> min a (--B) <= x /\ x <= max b B`) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(x:real^N)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; COMPONENT_LE_NORM; REAL_LE_MAX];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
       `norm(i - j) < e / &4 /\
        norm(ah - ag) <= norm(ch - cg)
        ==> norm(cg - i) < e / &4 /\
            norm(ch - j) < e / &4
            ==> norm(ag - ah) < e`) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM INTEGRAL_SUB] THEN
    MATCH_MP_TAC lemma THEN CONJ_TAC THENL
     [MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] HAS_INTEGRAL_DROP_POS) THEN
      MAP_EVERY EXISTS_TAC
       [`(\x. (if x IN s then h x else vec 0) - (if x IN s then g x else vec 0))
         :real^N->real^1`;
        `interval[a:real^N,b]`] THEN
      ASM_SIMP_TAC[INTEGRABLE_INTEGRAL; HAS_INTEGRAL_SUB] THEN
      ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_INTEGRAL] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[DROP_SUB; DROP_VEC; REAL_SUB_LE; REAL_POS] THEN
      ASM_MESON_TAC[REAL_LE_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] HAS_INTEGRAL_SUBSET_DROP_LE) THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. (if x IN s then h x else vec 0) - (if x IN s then g x else vec 0))
       :real^N->real^1`;
      `interval[a:real^N,b]`; `interval[c:real^N,d]`] THEN
    ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRABLE_INTEGRAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL] THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["c"; "d"] THEN
      SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[DROP_SUB; DROP_VEC; REAL_SUB_LE; REAL_POS] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[INTEGRABLE_ALT] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &3`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; HAS_INTEGRAL_ALT] THEN
  MAP_EVERY X_GEN_TAC
   [`g:real^N->real^1`; `h:real^N->real^1`; `i:real^1`; `j:real^1`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e / &3`)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `e / &3`)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "G"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))) THEN
  EXISTS_TAC `max B1 B2` THEN
  ASM_REWRITE_TAC[REAL_LT_MAX; BALL_MAX_UNION; UNION_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `c:real^N`; `d:real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[ABS_DROP; DROP_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!ga gc ha hc i j.
        ga <= fa /\ fa <= ha /\
        gc <= fc /\ fc <= hc /\
        abs(ga - i) < e / &3 /\
        abs(gc - i) < e / &3 /\
        abs(ha - j) < e / &3 /\
        abs(hc - j) < e / &3 /\
        abs(i - j) < e / &3
        ==> abs(fa - fc) < e`) THEN
  MAP_EVERY EXISTS_TAC
   [`drop(integral(interval[a:real^N,b]) (\x. if x IN s then g x else vec 0))`;
    `drop(integral(interval[c:real^N,d]) (\x. if x IN s then g x else vec 0))`;
    `drop(integral(interval[a:real^N,b]) (\x. if x IN s then h x else vec 0))`;
    `drop(integral(interval[c:real^N,d]) (\x. if x IN s then h x else vec 0))`;
    `drop i`; `drop j`] THEN
  REWRITE_TAC[GSYM DROP_SUB; GSYM ABS_DROP] THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]);;

let HAS_INTEGRAL_STRADDLE_NULL = prove
 (`!f g:real^N->real^1 s.
        (!x. x IN s ==> &0 <= drop(f x) /\ drop(f x) <= drop(g x)) /\
        (g has_integral (vec 0)) s
        ==> (f has_integral (vec 0)) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
    GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(\x. vec 0):real^N->real^1`; `g:real^N->real^1`;
      `vec 0:real^1`; `vec 0:real^1`] THEN
    ASM_REWRITE_TAC[DROP_VEC; HAS_INTEGRAL_0; VECTOR_SUB_REFL; NORM_0];
    DISCH_TAC THEN ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`f:real^N->real^1`; `g:real^N->real^1`]
        HAS_INTEGRAL_DROP_LE);
      MATCH_MP_TAC(ISPECL [`(\x. vec 0):real^N->real^1`; `f:real^N->real^1`]
        HAS_INTEGRAL_DROP_LE)] THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; DROP_VEC; HAS_INTEGRAL_0]]);;

(* ------------------------------------------------------------------------- *)
(* Adding integrals over several sets.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_UNION = prove
 (`!f:real^M->real^N i j s t.
        (f has_integral i) s /\ (f has_integral j) t /\ negligible(s INTER t)
        ==> (f has_integral (i + j)) (s UNION t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  EXISTS_TAC `(\x. if x IN (s INTER t) then &2 % f(x)
                   else if x IN (s UNION t) then f(x)
                   else vec 0):real^M->real^N` THEN
  EXISTS_TAC `s INTER t:real^M->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_UNIV] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let INTEGRAL_UNION = prove
 (`!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(s INTER t)
        ==> integral (s UNION t) f = integral s f + integral t f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_UNION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_INTEGRAL_UNIONS = prove
 (`!f:real^M->real^N i t.
        FINITE t /\
        (!s. s IN t ==> (f has_integral (i s)) s) /\
        (!s s'. s IN t /\ s' IN t /\ ~(s = s') ==> negligible(s INTER s'))
        ==> (f has_integral (vsum t i)) (UNIONS t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_VSUM) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\(a,b). a INTER b :real^M->bool)
                  {a,b | a IN t /\ b IN {y | y IN t /\ ~(a = y)}})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      ASM_SIMP_TAC[FINITE_RESTRICT];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      ASM_SIMP_TAC[IN_ELIM_THM]];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNIV; IN_DIFF] THEN
    ASM_CASES_TAC `(x:real^M) IN UNIONS t` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[SET_RULE
       `~(x IN UNIONS t) <=> !s. s IN t ==> ~(x IN s)`]) THEN
      ASM_SIMP_TAC[VSUM_0]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^M->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^M->bool`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
    ASM_SIMP_TAC[MESON[]
     `x IN a /\ a IN t
      ==> ((!b. ~((b IN t /\ ~(a = b)) /\ x IN b)) <=>
           (!b. b IN t ==> (x IN b <=> b = a)))`] THEN
    ASM_REWRITE_TAC[VSUM_DELTA]]);;

let HAS_INTEGRAL_DIFF = prove
 (`!f:real^M->real^N i j s t.
    (f has_integral i) s /\
    (f has_integral j) t /\
    negligible (t DIFF s)
    ==> (f has_integral (i - j)) (s DIFF t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  EXISTS_TAC `(\x. if x IN (t DIFF s) then --(f x)
                   else if x IN (s DIFF t) then f x
                   else vec 0):real^M->real^N` THEN
  EXISTS_TAC `t DIFF s:real^M->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_UNIV] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let INTEGRAL_DIFF = prove
 (`!f:real^M->real^N s t.
        f integrable_on s /\ f integrable_on t /\ negligible(t DIFF s)
        ==> integral (s DIFF t) f = integral s f - integral t f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_DIFF THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

(* ------------------------------------------------------------------------- *)
(* In particular adding integrals over a division, maybe not of an interval. *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE_DIVISION = prove
 (`!f:real^M->real^N s d i.
        d division_of s /\
        (!k. k IN d ==> (f has_integral (i k)) k)
        ==> (f has_integral (vsum d i)) s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS o
              GEN_REWRITE_RULE I [division_of]) THEN
  MATCH_MP_TAC HAS_INTEGRAL_UNIONS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?u v:real^M x y:real^M.
                k1 = interval[u,v] /\ k2 = interval[x,y]`
   (REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC))
  THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o
              GEN_REWRITE_RULE I [division_of]) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`interval[u:real^M,v]`; `interval[x:real^M,y]`]) THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN DISCH_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `(interval[u,v:real^M] DIFF interval(u,v)) UNION
              (interval[x,y] DIFF interval(x,y))` THEN
  SIMP_TAC[NEGLIGIBLE_FRONTIER_INTERVAL; NEGLIGIBLE_UNION] THEN
  ASM SET_TAC[]);;

let INTEGRAL_COMBINE_DIVISION_BOTTOMUP = prove
 (`!f:real^M->real^N d s.
        d division_of s /\ (!k. k IN d ==> f integrable_on k)
        ==> integral s f = vsum d (\i. integral i f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_INTEGRAL_COMBINE_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N s d k.
        f integrable_on s /\ d division_of k /\ k SUBSET s
        ==> (f has_integral (vsum d (\i. integral i f))) k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let INTEGRAL_COMBINE_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N d s.
        f integrable_on s /\ d division_of s
        ==> integral s f = vsum d (\i. integral i f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let INTEGRABLE_COMBINE_DIVISION = prove
 (`!f d s.
        d division_of s /\ (!i. i IN d ==> f integrable_on i)
        ==> f integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_COMBINE_DIVISION]);;

let INTEGRABLE_ON_SUBDIVISION = prove
 (`!f:real^M->real^N s d i.
        d division_of i /\
        f integrable_on s /\ i SUBSET s
        ==> f integrable_on i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_COMBINE_DIVISION THEN
  EXISTS_TAC `d:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  ASM_MESON_TAC[division_of; UNIONS_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Also tagged divisions.                                                    *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMBINE_TAGGED_DIVISION = prove
 (`!f:real^M->real^N s p i.
        p tagged_division_of s /\
        (!x k. (x,k) IN p ==> (f has_integral (i k)) k)
        ==> (f has_integral (vsum p (\(x,k). i k))) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^M k:real^M->bool.
      (x,k) IN p ==> ((f:real^M->real^N) has_integral integral k f) k`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[HAS_INTEGRAL_INTEGRAL; integrable_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:real^M->real^N) has_integral
     (vsum (IMAGE SND (p:real^M#(real^M->bool)->bool))
           (\k. integral k f))) s`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum p (\(x:real^M,k:real^M->bool). integral k f:real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[HAS_INTEGRAL_UNIQUE];
    MATCH_MP_TAC VSUM_OVER_TAGGED_DIVISION_LEMMA THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[INTEGRAL_NULL]]);;

let INTEGRAL_COMBINE_TAGGED_DIVISION_BOTTOMUP = prove
 (`!f:real^M->real^N p a b.
        p tagged_division_of interval[a,b] /\
        (!x k. (x,k) IN p ==> f integrable_on k)
        ==> integral (interval[a,b]) f = vsum p (\(x,k). integral k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_TAGGED_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let HAS_INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N a b p.
        f integrable_on interval[a,b] /\ p tagged_division_of interval[a,b]
        ==> (f has_integral (vsum p (\(x,k). integral k f))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_TAGGED_DIVISION THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL; TAGGED_DIVISION_OF]);;

let INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN = prove
 (`!f:real^M->real^N a b p.
        f integrable_on interval[a,b] /\ p tagged_division_of interval[a,b]
        ==> integral (interval[a,b]) f = vsum p (\(x,k). integral k f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Henstock's lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let HENSTOCK_LEMMA_PART1 = prove
 (`!f:real^M->real^N a b d e.
        f integrable_on interval[a,b] /\
        &0 < e /\ gauge d /\
        (!p. p tagged_division_of interval[a,b] /\ d fine p
             ==> norm (vsum p (\(x,k). content k % f x) -
                       integral(interval[a,b]) f) < e)
        ==> !p. p tagged_partial_division_of interval[a,b] /\ d fine p
                            ==> norm(vsum p (\(x,k). content k % f x -
                                                     integral k f)) <= e`,
  let lemma = prove
   (`(!k. &0 < k ==> x <= e + k) ==> x <= e`,
    DISCH_THEN(MP_TAC o SPEC `(x - e) / &2`) THEN REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN X_GEN_TAC `k:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
    [`IMAGE SND (p:(real^M#(real^M->bool))->bool)`; `a:real^M`; `b:real^M`]
    PARTIAL_DIVISION_EXTEND_INTERVAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[PARTIAL_DIVISION_OF_TAGGED_DIVISION]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[tagged_partial_division_of; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP(SET_RULE
   `s SUBSET t ==> t = s UNION (t DIFF s)`)) THEN
  ABBREV_TAC `r = q DIFF IMAGE SND (p:(real^M#(real^M->bool))->bool)` THEN
  SUBGOAL_THEN `IMAGE SND (p:(real^M#(real^M->bool))->bool) INTER r = {}`
  ASSUME_TAC THENL [EXPAND_TAC "r" THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `FINITE(r:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[division_of; FINITE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN r
        ==> ?p. p tagged_division_of i /\ d fine p /\
                norm(vsum p (\(x,j). content j % f x) -
                     integral i (f:real^M->real^N))
                < k / (&(CARD(r:(real^M->bool)->bool)) + &1)`
  MP_TAC THENL
   [X_GEN_TAC `i:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:real^M->bool) SUBSET interval[a,b]` ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of; IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `?u v:real^M. i = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[division_of; IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[u,v]` MP_TAC THENL
     [ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    REWRITE_TAC[has_integral] THEN
    DISCH_THEN(MP_TAC o SPEC `k / (&(CARD(r:(real^M->bool)->bool)) + &1)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `dd:real^M->real^M->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPECL [`d:real^M->real^M->bool`; `dd:real^M->real^M->bool`]
      GAUGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^M`; `v:real^M`]) THEN
    REWRITE_TAC[FINE_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:(real^M->bool)->(real^M#(real^M->bool))->bool`
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `p UNION UNIONS {q (i:real^M->bool) | i IN r}
     :(real^M#(real^M->bool))->bool`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC FINE_UNION THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINE_UNIONS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE]] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o last o CONJUNCTS o
                GEN_REWRITE_RULE I [division_of]) THEN
    REWRITE_TAC[UNIONS_UNION] THEN
    MATCH_MP_TAC TAGGED_DIVISION_UNION THEN CONJ_TAC THENL
     [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC TAGGED_DIVISION_UNIONS THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      SIMP_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN
    REPEAT(CONJ_TAC THENL
            [ASM_MESON_TAC[division_of; FINITE_UNION; IN_UNION]; ALL_TAC]) THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC INTER_INTERIOR_UNIONS_INTERVALS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; OPEN_INTERIOR] THEN
    REPEAT(CONJ_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of; FINITE_IMAGE]; ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM] THEN
    ASM_REWRITE_TAC[EXISTS_PAIR_THM; IN_IMAGE; IN_INTER; IN_UNION] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum (p UNION UNIONS {q i | i IN r}) (\(x,k). content k % f x) =
    vsum p (\(x:real^M,k:real^M->bool). content k % f x:real^N) +
    vsum (UNIONS {q i | (i:real^M->bool) IN r}) (\(x,k). content k % f x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_UNION_NONZERO THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF_FINITE]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_UNIONS; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(l:real^M->bool) SUBSET k` ASSUME_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o SPECL [`k:real^M->bool`; `l:real^M->bool`] o
               el 2 o CONJUNCTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_UNION; IN_IMAGE; EXISTS_PAIR_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM] THEN
      ASM_REWRITE_TAC[EXISTS_PAIR_THM; IN_IMAGE; IN_INTER; IN_UNION] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUBSET_INTERIOR; SET_RULE `s SUBSET t ==> t INTER s = s`] THEN
    SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
     (fun th -> REPEAT_TCL CHOOSE_THEN SUBST1_TAC th THEN
                SIMP_TAC[VECTOR_MUL_LZERO; GSYM CONTENT_EQ_0_INTERIOR]) THEN
    ASM_MESON_TAC[tagged_partial_division_of];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_UNIONS_NONZERO o
    rand o lhand o rand o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF; IN_UNION]; ALL_TAC] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `l:real^M->bool` THEN DISCH_TAC THEN
    DISCH_TAC THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `m:real^M->bool`] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    SUBGOAL_THEN `?u v:real^M. m = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF; IN_UNION]; ALL_TAC] THEN
    REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN
    MATCH_MP_TAC(SET_RULE `!t. s SUBSET t /\ t = {} ==> s = {}`) THEN
    EXISTS_TAC `interior(k INTER l:real^M->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[SUBSET_INTER] THEN
      ASM_MESON_TAC[TAGGED_DIVISION_OF];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    REWRITE_TAC[INTERIOR_INTER] THEN
    DISCH_THEN(MATCH_MP_TAC o SPECL [`k:real^M->bool`; `l:real^M->bool`] o
               el 2 o CONJUNCTS) THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE_NONZERO o
    rand o lhand o rand o lhand o lhand o snd) THEN
  ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `l:real^M->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `m:real^M->bool`] THEN DISCH_TAC THEN
    MP_TAC(ASSUME `!i:real^M->bool. i IN r ==> q i tagged_division_of i`) THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `l:real^M->bool` th) THEN
                         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
                         MP_TAC(SPEC `k:real^M->bool` th) THEN
                         ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[tagged_division_of] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `vsum p (\(x,k). content k % (f:real^M->real^N) x - integral k f) =
    vsum p (\(x,k). content k % f x) - vsum p (\(x,k). integral k f)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[GSYM VSUM_SUB; LAMBDA_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!ir. ip + ir = i /\
         norm(cr - ir) < k
         ==> norm((cp + cr) - i) < e ==> norm(cp - ip) <= e + k`) THEN
  EXISTS_TAC `vsum r (\k. integral k (f:real^M->real^N))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum (IMAGE SND (p:(real^M#(real^M->bool))->bool) UNION r)
                     (\k. integral k (f:real^M->real^N))` THEN
    CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[INTEGRAL_COMBINE_DIVISION_TOPDOWN]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum (IMAGE SND (p:(real^M#(real^M->bool))->bool))
                     (\k. integral k (f:real^M->real^N)) +
                vsum r (\k. integral k f)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_UNION_NONZERO THEN
      ASM_SIMP_TAC[FINITE_IMAGE; NOT_IN_EMPTY]] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(\(x:real^M,k). integral k (f:real^M->real^N)) =
                  (\k. integral k f) o SND`
    SUBST1_TAC THENL
     [SIMP_TAC[o_THM; FUN_EQ_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`x:real^M`; `l:real^M->bool`; `y:real^M`; `m:real^M->bool`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
    DISCH_THEN(CONJUNCTS_THEN MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x:real^M`; `l:real^M->bool`; `y:real^M`; `l:real^M->bool`]) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC o last o CONJUNCTS) THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
    ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum (r:(real^M->bool)->bool) (\x. k / (&(CARD r) + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[SUM_CONST] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &x + &1`] THEN
    REWRITE_TAC[REAL_ARITH `a * k < k * b <=> &0 < k * (b - a)`] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let HENSTOCK_LEMMA_PART2 = prove
 (`!f:real^M->real^N a b d e.
        f integrable_on interval[a,b] /\
        &0 < e /\ gauge d /\
        (!p. p tagged_division_of interval[a,b] /\ d fine p
             ==> norm (vsum p (\(x,k). content k % f x) -
                       integral(interval[a,b]) f) < e)
        ==> !p. p tagged_partial_division_of interval[a,b] /\ d fine p
                            ==> sum p (\(x,k). norm(content k % f x -
                                                    integral k f))
                                <= &2 * &(dimindex(:N)) * e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LAMBDA_PAIR] THEN
  MATCH_MP_TAC VSUM_NORM_ALLSUBSETS_BOUND THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
  X_GEN_TAC `q:(real^M#(real^M->bool))->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
    HENSTOCK_LEMMA_PART1) THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^M`; `b:real^M`; `d:real^M->real^M->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FINE_SUBSET; TAGGED_PARTIAL_DIVISION_SUBSET]);;

let HENSTOCK_LEMMA = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> !e. &0 < e
                ==> ?d. gauge d /\
                        !p. p tagged_partial_division_of interval[a,b] /\
                            d fine p
                            ==> sum p (\(x,k). norm(content k % f x -
                                                    integral k f)) < e`,
  MP_TAC HENSTOCK_LEMMA_PART2 THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN X_GEN_TAC `e:real` THEN
                       STRIP_TAC THEN MP_TAC th) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  GEN_REWRITE_TAC LAND_CONV [has_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&2 * (&(dimindex(:N)) + &1))`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2 * (&n + &1)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`d:real^M->real^M->bool`; `e / (&2 * (&(dimindex(:N)) + &1))`]) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &2 * (&n + &1)`] THEN
  DISCH_THEN(fun th -> EXISTS_TAC `d:real^M->real^M->bool` THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `d < e ==> x <= d ==> x < e`) THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV; REAL_MUL_ASSOC] THEN
  SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Monotone convergence (bounded interval first).                            *)
(* ------------------------------------------------------------------------- *)

let MONOTONE_CONVERGENCE_INTERVAL = prove
 (`!f:num->real^N->real^1 g a b.
        (!k. (f k) integrable_on interval[a,b]) /\
        (!k x. x IN interval[a,b] ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN interval[a,b] ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral (interval[a,b]) (f k) | k IN (:num)}
        ==> g integrable_on interval[a,b] /\
            ((\k. integral (interval[a,b]) (f k))
             --> integral (interval[a,b]) g) sequentially`,
  let lemma = prove
   (`{(x,y) | P x y} = {p | P (FST p) (SND p)}`,
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^N,b]) = &0` THENL
   [ASM_SIMP_TAC[INTEGRAL_NULL; INTEGRABLE_ON_NULL; LIM_CONST];
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONTENT_LT_NZ])] THEN
  SUBGOAL_THEN
   `!x:real^N k:num. x IN interval[a,b] ==> drop(f k x) <= drop(g x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\k. (f:num->real^N->real^1) k x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[REAL_LE_TRANS] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. ((\k. integral (interval[a,b]) (f k:real^N->real^1)) --> i)
        sequentially`
  CHOOSE_TAC THENL
   [MATCH_MP_TAC BOUNDED_INCREASING_CONVERGENT THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. drop(integral(interval[a,b]) ((f:num->real^N->real^1) k)) <= drop i`
  ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
     EXISTS_TAC `\k. integral(interval[a,b]) ((f:num->real^N->real^1) k)` THEN
     ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
     MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
     ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN
     GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `((g:real^N->real^1) has_integral i) (interval[a,b])`
  ASSUME_TAC THENL
   [REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
     [HAS_INTEGRAL_INTEGRAL]) THEN
    REWRITE_TAC[has_integral] THEN
    DISCH_THEN(MP_TAC o GEN `k:num` o
      SPECL [`k:num`; `e / &2 pow (k + 2)`]) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC LAND_CONV [SKOLEM_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
    X_GEN_TAC `b:num->real^N->real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?r. !k. r:num <= k
               ==> &0 <= drop i - drop(integral(interval[a:real^N,b]) (f k)) /\
                   drop i - drop(integral(interval[a,b]) (f k)) < e / &4`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[ABS_DROP; dist; DROP_SUB] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= y ==> abs(x - y) < e ==> &0 <= y - x /\ y - x < e`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. x IN interval[a:real^N,b]
          ==> ?n. r:num <= n /\
                  !k. n <= k ==> &0 <= drop(g x) - drop(f k x) /\
                                 drop(g x) - drop(f k x) <
                                   e / (&4 * content(interval[a,b]))`
    MP_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o RAND_CONV)
        [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_SIMP_TAC[REAL_SUB_LE] THEN
      DISCH_THEN(MP_TAC o SPEC `e / (&4 * content(interval[a:real^N,b]))`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[dist; ABS_DROP; DROP_SUB] THEN
      ASM_SIMP_TAC[REAL_ARITH `f <= g ==> abs(f - g) = g - f`] THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      EXISTS_TAC `N + r:num` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[ARITH_RULE `N + r:num <= k ==> N <= k`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_AND_THM; TAUT
     `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^N->num` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `d:real^N->real^N->bool = \x. b(m x:num) x` THEN
    EXISTS_TAC `d:real^N->real^N->bool` THEN CONJ_TAC THENL
     [EXPAND_TAC "d" THEN REWRITE_TAC[gauge] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [gauge]) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:(real^N#(real^N->bool))->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `!b c. norm(a - b) <= e / &4 /\
            norm(b - c) < e / &2 /\
            norm(c - d) < e / &4
            ==> norm(a - d) < e`) THEN
    EXISTS_TAC `vsum p (\(x:real^N,k:real^N->bool).
                  content k % (f:num->real^N->real^1) (m x) x)` THEN
    EXISTS_TAC `vsum p (\(x:real^N,k:real^N->bool).
                  integral k ((f:num->real^N->real^1) (m x)))` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    SUBGOAL_THEN `?s:num. !t:real^N#(real^N->bool). t IN p ==> m(FST t) <= s`
    MP_TAC THENL [ASM_SIMP_TAC[UPPER_BOUND_FINITE_SET]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN DISCH_THEN(X_CHOOSE_TAC `s:num`) THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM VSUM_SUB] THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `y <= e ==> x <= y ==> x <= e`) THEN
      REWRITE_TAC[LAMBDA_PAIR_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sum p (\(x:real^N,k:real^N->bool).
                 content k * e / (&4 * content (interval[a:real^N,b])))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^N`; `k:real^N->bool`] THEN
        DISCH_TAC THEN REWRITE_TAC[NORM_MUL; GSYM VECTOR_SUB_LDISTRIB] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN
        REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        REWRITE_TAC[ABS_DROP; DROP_SUB] THEN
        REWRITE_TAC[REAL_ARITH `abs(x) <= x <=> &0 <= x`] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF]; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= g - f /\ g - f < e ==> abs(g - f) <= e`) THEN
        CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET];
        ALL_TAC] THEN
      REWRITE_TAC[LAMBDA_PAIR; SUM_RMUL] THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP
       ADDITIVE_CONTENT_TAGGED_DIVISION th]) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < content(interval[a:real^N,b])` THEN
      CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[GSYM VSUM_SUB] THEN REWRITE_TAC[LAMBDA_PAIR_THM] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
        `norm(vsum (0..s)
               (\j. vsum {(x:real^N,k:real^N->bool) | (x,k) IN p /\ m(x) = j}
                         (\(x,k). content k % f (m x) x :real^1 -
                                  integral k (f (m x)))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[lemma] THEN
        AP_TERM_TAC THEN MATCH_MP_TAC(GSYM VSUM_GROUP) THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
        ASM_REWRITE_TAC[FORALL_PAIR_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sum (0..s) (\i. e / &2 pow (i + 2))` THEN CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[real_div; GSYM REAL_POW_INV; SUM_LMUL] THEN
        REWRITE_TAC[REAL_POW_ADD; SUM_RMUL] THEN REWRITE_TAC[SUM_GP] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_SIMP_TAC[REAL_LT_LMUL_EQ; CONJUNCT1 LT] THEN
        REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < x * y ==> (&1 - x) * y < y`) THEN
        MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_POW_LT THEN CONV_TAC REAL_RAT_REDUCE_CONV] THEN
      MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `t:num` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
       `norm(vsum {x:real^N,k:real^N->bool | x,k IN p /\ m x:num = t}
                  (\(x,k). content k % f t x - integral k (f t)):real^1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
        MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
        HENSTOCK_LEMMA_PART1) THEN
      MAP_EVERY EXISTS_TAC
       [`a:real^N`; `b:real^N`; `(b(t:num)):real^N->real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_SUBSET THEN
        EXISTS_TAC `p:(real^N#(real^N->bool))->bool` THEN
        SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[tagged_division_of];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      EXPAND_TAC "d" THEN REWRITE_TAC[fine; IN_ELIM_PAIR_THM] THEN MESON_TAC[];

      MP_TAC(ISPECL [`(f:num->real^N->real^1) s`; `a:real^N`; `b:real^N`;
                     `p:(real^N#(real^N->bool))->bool`]
                    INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
      MP_TAC(ISPECL [`(f:num->real^N->real^1) r`; `a:real^N`; `b:real^N`;
                     `p:(real^N#(real^N->bool))->bool`]
                    INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
      ASM_SIMP_TAC[ABS_DROP; DROP_SUB; DROP_VSUM; GSYM DROP_EQ] THEN
      REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM] THEN MATCH_MP_TAC(REAL_ARITH
       `sr <= sx /\ sx <= ss /\ ks <= i /\ &0 <= i - kr /\ i - kr < e
        ==> kr = sr ==> ks = ss ==> abs(sx - i) < e`) THEN
      ASM_SIMP_TAC[LE_REFL] THEN CONJ_TAC THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:real^N->bool`] THEN DISCH_TAC THEN
      (SUBGOAL_THEN `i SUBSET interval[a:real^N,b]` ASSUME_TAC THENL
        [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
       SUBGOAL_THEN `?u v:real^N. i = interval[u,v]`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
       THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC]) THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      REPEAT(CONJ_TAC THENL
       [ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL]; ALL_TAC]) THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPEC
        `\m n:num. drop (f m (y:real^N)) <= drop (f n y)`
        TRANSITIVE_STEPWISE_LE) THEN
      REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL] THEN
      (ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC]) THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[]);;

let MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f:num->real^N->real^1 g s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  SUBGOAL_THEN
   `!f:num->real^N->real^1 g s.
        (!k x. x IN s ==> &0 <= drop(f k x)) /\
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL
     [`\n x:real^N. f(SUC n) x - f 0 x:real^1`;
      `\x. (g:real^N->real^1) x - f 0 x`; `s:real^N->bool`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      MP_TAC(ISPEC
        `\m n:num. drop (f m (x:real^N)) <= drop (f n x)`
        TRANSITIVE_STEPWISE_LE) THEN
      REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL] THEN ASM_MESON_TAC[LE_0];
      GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `x - a <= y - a <=> x <= y`];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_SUB THEN SIMP_TAC[LIM_CONST] THEN
      REWRITE_TAC[ADD1] THEN
      MATCH_MP_TAC(ISPECL[`f:num->real^1`; `l:real^1`; `1`] SEQ_OFFSET) THEN
      ASM_SIMP_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX; bounded] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real`
        (fun th -> EXISTS_TAC `B + norm(integral s (f 0:real^N->real^1))` THEN
                   X_GEN_TAC `k:num` THEN MP_TAC(SPEC `SUC k` th))) THEN
      NORM_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX; IMP_CONJ] THEN
      SUBGOAL_THEN `(f 0:real^N->real^1) integrable_on s` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ONCE_REWRITE_TAC[IMP_IMP]] THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_ADD) THEN
      REWRITE_TAC[ETA_AX; VECTOR_ARITH `f + (g - f):real^N = g`] THEN
      DISCH_TAC THEN ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX] THEN
      MP_TAC(ISPECL [`sequentially`; `integral s (f 0:real^N->real^1)`]
                    LIM_CONST) THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
      REWRITE_TAC[ETA_AX; VECTOR_ARITH `f + (g - f):real^N = g`] THEN
      REWRITE_TAC[ADD1] THEN
      SIMP_TAC[ISPECL[`f:num->real^1`; `l:real^1`; `1`] SEQ_OFFSET_REV]]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N k:num. x IN s ==> drop(f k x) <= drop(g x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\k. (f:num->real^N->real^1) k x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN REWRITE_TAC[REAL_LE_TRANS] THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i. ((\k. integral s (f k:real^N->real^1)) --> i)
        sequentially`
  CHOOSE_TAC THENL
   [MATCH_MP_TAC BOUNDED_INCREASING_CONVERGENT THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. drop(integral s ((f:num->real^N->real^1) k)) <= drop i`
  ASSUME_TAC THENL
    [GEN_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
     EXISTS_TAC `\k. integral(s) ((f:num->real^N->real^1) k)` THEN
     ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `k:num` THEN SPEC_TAC(`k:num`,`k:num`) THEN
     MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
     ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN
     GEN_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[];
     ALL_TAC] THEN
  SUBGOAL_THEN `((g:real^N->real^1) has_integral i) s` ASSUME_TAC THENL
   [ALL_TAC;
    CONJ_TAC THENL [ASM_MESON_TAC[integrable_on]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[HAS_INTEGRAL_ALT] THEN
  MP_TAC(ISPECL
   [`\k x. if x IN s then (f:num->real^N->real^1) k x else vec 0`;
    `\x. if x IN s then (g:real^N->real^1) x else vec 0`]
   (MATCH_MP(MESON[] `(!a b c d. P a b c d ==> Q a b c d)
                      ==> !a b. (!c d. P a b c d) ==> (!c d. Q a b c d)`)
            MONOTONE_CONVERGENCE_INTERVAL)) THEN
  ANTS_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [INTEGRABLE_ALT]) THEN
      SIMP_TAC[];
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LIM_CONST];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[ABS_DROP] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 <= y /\ y <= x ==> abs(x) <= a ==> abs(y) <= a`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_REFL; DROP_VEC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN
    ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; ETA_AX] THEN
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; DROP_VEC; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ASM_SIMP_TAC[dist; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
   [HAS_INTEGRAL_INTEGRAL]) THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [HAS_INTEGRAL_ALT] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`N:num`; `e / &4`]) THEN
  ASM_SIMP_TAC[dist; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `N:num <= N`)) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
   `norm(x - y) < e / &4 /\ norm(z - x) < e / &4
    ==> norm(z - y) < e / &2`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV)
        [LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `e / &2`]) THEN
  ASM_REWRITE_TAC[dist; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M + N:num`)) THEN
  REWRITE_TAC[LE_ADD; ABS_DROP; DROP_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `f1 <= f2 /\ f2 <= i
    ==> abs(f2 - g) < e / &2 ==> abs(f1 - i) < e / &2 ==> abs(g - i) < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MP_TAC(ISPEC
        `\m n:num. drop (f m (x:real^N)) <= drop (f n x)`
        TRANSITIVE_STEPWISE_LE) THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s ((f:num->real^N->real^1) (M + N)))` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN
  ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; ETA_AX] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_LE_REFL; DROP_VEC; REAL_LE_REFL]);;

let MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f:num->real^N->real^1 g s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`(\k x. --(f k x)):num->real^N->real^1`;
    `(\x. --(g x)):real^N->real^1`; `s:real^N->bool`]
        MONOTONE_CONVERGENCE_INCREASING) THEN
  FIRST_ASSUM MP_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (c ==> d) ==> a ==> (b ==> c) ==> d`) THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THENL
     [MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_NEG) THEN REWRITE_TAC[];
      SIMP_TAC[DROP_NEG; REAL_LE_NEG2];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NEG THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (\x. --x)
                      {integral s (f k:real^N->real^1) | k IN (:num)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
      ASM_SIMP_TAC[LINEAR_COMPOSE_NEG; LINEAR_ID];
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[GSYM IMAGE_o] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[o_THM] THEN
      MATCH_MP_TAC INTEGRAL_NEG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (MP_TAC o MATCH_MP INTEGRABLE_NEG) (MP_TAC o MATCH_MP LIM_NEG)) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  BINOP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN TRY GEN_TAC THEN
  MATCH_MP_TAC(VECTOR_ARITH `x:real^N = --y ==> --x = y`) THEN
  MATCH_MP_TAC INTEGRAL_NEG THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas about existence and bounds between integrals.                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_NORM_BOUND_INTEGRAL = prove
 (`!f:real^M->real^N g s.
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> norm(integral s f) <= drop(integral s g)`,
  let lemma = prove
   (`(!e. &0 < e ==> x < y + e) ==> x <= y`,
    DISCH_THEN(MP_TAC o SPEC `x - y:real`) THEN REAL_ARITH_TAC) in
  SUBGOAL_THEN
   `!f:real^M->real^N g a b.
        f integrable_on interval[a,b] /\ g integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> norm(f x) <= drop(g x))
        ==> norm(integral(interval[a,b]) f) <= drop(integral(interval[a,b]) g)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(f:real^M->real^N) integrable_on interval[a,b]` THEN
    DISCH_THEN(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    REWRITE_TAC[has_integral] THEN DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d1:real^M->real^M->bool` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d2:real^M->real^M->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPECL [`d1:real^M->real^M->bool`; `d2:real^M->real^M->bool`]
                  GAUGE_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
    REWRITE_TAC[FINE_INTER; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    ASM_REWRITE_TAC[ABS_DROP; DROP_SUB] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(sg) <= dsa
      ==> abs(dsa - dia) < e / &2 ==> norm(sg - ig) < e / &2
          ==> norm(ig) < dia + e`) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[DROP_VSUM] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_REWRITE_TAC[o_DEF; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_MUL; DROP_CMUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
    REWRITE_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
    ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF; SUBSET];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th ->
     ASSUME_TAC(CONJUNCT1(GEN_REWRITE_RULE I [INTEGRABLE_ALT] th)) THEN
     MP_TAC(MATCH_MP INTEGRABLE_INTEGRAL th))) THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN
  DISCH_THEN(LABEL_TAC "A") THEN DISCH_TAC THEN MATCH_MP_TAC lemma THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "A" (MP_TAC o SPEC `e / &2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))) THEN
  MP_TAC(ISPEC `ball(vec 0,max B1 B2):real^M->bool`
    BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[BALL_MAX_UNION; UNION_SUBSET] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  DISCH_THEN(CONJUNCTS_THEN(ANTE_RES_THEN MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^1` (CONJUNCTS_THEN2 ASSUME_TAC
     (fun th -> DISCH_THEN(X_CHOOSE_THEN `w:real^N`
                (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN MP_TAC th))) THEN
  ASM_REWRITE_TAC[ABS_DROP; DROP_SUB] THEN MATCH_MP_TAC(NORM_ARITH
     `norm(sg) <= dsa
      ==> abs(dsa - dia) < e / &2 ==> norm(sg - ig) < e / &2
          ==> norm(ig) < dia + e`) THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE)) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; DROP_VEC; REAL_LE_REFL]);;

let INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N g:real^M->real^P s k.
        1 <= k /\ k <= dimindex(:P) /\
        f integrable_on s /\ g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= (g x)$k)
        ==> norm(integral s f) <= (integral s g)$k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s ((\y. lift(y$k)) o (g:real^M->real^P)))` THEN
  SUBGOAL_THEN `linear(\y:real^P. lift(y$k))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 LIFT_ADD; LIFT_CMUL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[o_THM; LIFT_DROP] THEN MATCH_MP_TAC INTEGRABLE_LINEAR THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral s ((\y. lift (y$k)) o (g:real^M->real^P)) =
        (\y. lift (y$k)) (integral s g)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_LINEAR THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]]);;

let HAS_INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N g:real^M->real^P s i j k.
        1 <= k /\ k <= dimindex(:P) /\
        (f has_integral i) s /\ (g has_integral j) s /\
        (!x. x IN s ==> norm(f x) <= (g x)$k)
        ==> norm(i) <= j$k`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(fun th ->
   SUBST1_TAC(SYM(MATCH_MP INTEGRAL_UNIQUE th)) THEN
   ASSUME_TAC(MATCH_MP HAS_INTEGRAL_INTEGRABLE th))) THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_COMPONENT THEN
  ASM_REWRITE_TAC[]);;

let INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND = prove
 (`!f:real^M->real^N g s.
        (!a b. (\x. if x IN s then f x else vec 0)
               integrable_on interval[a,b]) /\
        (!x. x IN s ==> norm(f x) <= drop(g x)) /\
        g integrable_on s
        ==> f integrable_on s`,
  let lemma = prove
   (`!f:real^M->real^N g.
          (!a b. f integrable_on interval[a,b]) /\
          (!x. norm(f x) <= drop(g x)) /\
          g integrable_on (:real^M)
          ==> f integrable_on (:real^M)`,
    REPEAT GEN_TAC THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ONCE_REWRITE_TAC[INTEGRABLE_ALT_SUBSET] THEN
    ASM_REWRITE_TAC[IN_UNIV; ETA_AX] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b < c ==> a < c`) THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_DIFF; NEGLIGIBLE_EMPTY;
                 SET_RULE `s SUBSET t ==> s DIFF t = {}`] THEN
    REWRITE_TAC[ABS_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_MESON_TAC[integrable_on; HAS_INTEGRAL_DIFF; NEGLIGIBLE_EMPTY;
                 SET_RULE `s SUBSET t ==> s DIFF t = {}`]) in
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC `(\x. if x IN s then g x else vec 0):real^M->real^1` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; DROP_VEC; REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* Interval functions of bounded variation on a set.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_setvariation_on",(12,"right"));;

let set_variation = new_definition
 `set_variation s (f:(real^M->bool)->real^N) =
        sup { sum d (\k. norm(f k)) | ?t. d division_of t /\ t SUBSET s}`;;

let has_bounded_setvariation_on = new_definition
  `(f:(real^M->bool)->real^N) has_bounded_setvariation_on s <=>
        ?B. !d t. d division_of t /\ t SUBSET s
                  ==> sum d (\k. norm(f k)) <= B`;;

let HAS_BOUNDED_SETVARIATION_ON = prove
 (`!f:(real^M->bool)->real^N s.
        f  has_bounded_setvariation_on s <=>
        ?B. &0 < B /\ !d t. d division_of t /\ t SUBSET s
                            ==> sum d (\k. norm(f k)) <= B`,
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MESON_TAC[REAL_ARITH `&0 < abs B + &1 /\ (x <= B ==> x <= abs B + &1)`]);;

let HAS_BOUNDED_SETVARIATION_ON_EQ = prove
 (`!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b])) /\
        f has_bounded_setvariation_on s
        ==> g has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `d:(real^M->bool)->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^M->bool` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= B ==> y <= B`) THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
  GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let SET_VARIATION_EQ = prove
 (`!f g:(real^M->bool)->real^N s.
        (!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b]))
        ==> set_variation s f = set_variation s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_variation] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
  GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let HAS_BOUNDED_SETVARIATION_ON_COMPONENTWISE = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\k. lift(f k$i)) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on; NORM_LIFT] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `B:real` THEN
    MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
      [`d:(real^M->bool)->bool`; `t:real^M->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    ASM_MESON_TAC[DIVISION_OF_FINITE];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `B:num->real` THEN DISCH_TAC THEN
    EXISTS_TAC `sum (1..dimindex(:N)) B` THEN
    MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum d (\k. sum (1..dimindex(:N))
                           (\i. abs(((f:(real^M->bool)->real^N) k)$i)))` THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[SUM_LE; NORM_LE_L1] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_MESON_TAC[]]);;

let SETVARIATION_EQUAL_LEMMA = prove
 (`!mf:((real^M->bool)->real^N)->((real^M->bool)->real^N) ms ms'.
        (!s. ms'(ms s) = s /\ ms(ms' s) = s) /\
        (!f a b. ~(interval[a,b] = {})
                 ==> mf f (ms (interval[a,b])) = f (interval[a,b]) /\
                     ?a' b'. ~(interval[a',b'] = {}) /\
                             ms' (interval[a,b]) = interval[a',b']) /\
        (!t u. t SUBSET u ==> ms t SUBSET ms u /\ ms' t SUBSET ms' u) /\
        (!d t. d division_of t
               ==> (IMAGE ms d) division_of ms t /\
                   (IMAGE ms' d) division_of ms' t)
   ==> (!f s. (mf f) has_bounded_setvariation_on (ms s) <=>
              f has_bounded_setvariation_on s) /\
       (!f s. set_variation (ms s) (mf f) = set_variation s f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on; set_variation] THEN
  MATCH_MP_TAC(MESON[]
   `((!f s. s1 f s = s2 f s) ==> P) /\
    (!f s. s1 f s = s2 f s)
    ==> P /\ (!f s. sup (s1 f s) = sup (s2 f s))`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `IMAGE (ms':(real^M->bool)->real^M->bool) d`;
    EXISTS_TAC `IMAGE (ms:(real^M->bool)->real^M->bool) d`] THEN
  (CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
   ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[o_THM] THEN FIRST_ASSUM
   (fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `?a' b':real^M. ~(interval[a',b'] = {}) /\
                        ms' (interval[a:real^M,b]) = interval[a',b']`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let HAS_BOUNDED_SETVARIATION_ON_ELEMENTARY = prove
 (`!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> (f has_bounded_setvariation_on s <=>
             ?B. !d. d division_of s ==> sum d (\k. norm(f k)) <= B)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN EQ_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  GEN_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(X_CHOOSE_TAC `d':(real^M->bool)->bool`) THEN
  MP_TAC(ISPECL [`d:(real^M->bool)->bool`; `d':(real^M->bool)->bool`;
             `t:real^M->bool`; `s:real^M->bool`] PARTIAL_DIVISION_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `d'':(real^M->bool)->bool`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d'' (\k:real^M->bool. norm(f k:real^N))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[DIVISION_OF_FINITE]);;

let HAS_BOUNDED_SETVARIATION_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b.
        f has_bounded_setvariation_on interval[a,b] <=>
        ?B. !d. d division_of interval[a,b] ==> sum d (\k. norm(f k)) <= B`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_BOUNDED_SETVARIATION_ON_ELEMENTARY THEN
  REWRITE_TAC[ELEMENTARY_INTERVAL]);;

let HAS_BOUNDED_SETVARIATION_ON_UNIV = prove
 (`!f:(real^M->bool)->real^N.
        f has_bounded_setvariation_on (:real^M) <=>
        ?B. !d. d division_of UNIONS d ==> sum d (\k. norm(f k)) <= B`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_setvariation_on; SUBSET_UNIV] THEN
  MESON_TAC[DIVISION_OF_UNION_SELF]);;

let HAS_BOUNDED_SETVARIATION_ON_SUBSET = prove
 (`!f:(real^M->bool)->real^N s t.
        f has_bounded_setvariation_on s /\ t SUBSET s
        ==> f has_bounded_setvariation_on t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[SUBSET_TRANS]);;

let HAS_BOUNDED_SETVARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> bounded { f(interval[c,d]) | interval[c,d] SUBSET s}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_setvariation_on; bounded] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  EXISTS_TAC `max (abs B) (norm((f:(real^M->bool)->real^N) {}))` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `interval[c:real^M,d] = {}` THEN
  ASM_REWRITE_TAC[REAL_ARITH `a <= max b a`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`{interval[c:real^M,d]}`; `interval[c:real^M,d]`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF; SUM_SING] THEN REAL_ARITH_TAC);;

let HAS_BOUNDED_SETVARIATION_ON_NORM = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> (\x. lift(norm(f x))) has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on; NORM_REAL; GSYM drop] THEN
  REWRITE_TAC[REAL_ABS_NORM; LIFT_DROP]);;

let HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR = prove
 (`!f:(real^M->bool)->real^N g:real^N->real^P s.
        f has_bounded_setvariation_on s /\ linear g
        ==> (g o f) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `B:real`) ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `C:real` o MATCH_MP LINEAR_BOUNDED_POS) THEN
  EXISTS_TAC `B * C:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[o_THM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. C * norm((f:(real^M->bool)->real^N) k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC[DIVISION_OF_FINITE];
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
    ASM_MESON_TAC[]]);;

let HAS_BOUNDED_SETVARIATION_ON_0 = prove
 (`!s:real^N->bool. (\x. vec 0) has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on; NORM_0; SUM_0] THEN
  MESON_TAC[REAL_LE_REFL]);;

let SET_VARIATION_0 = prove
 (`!s:real^N->bool. set_variation s (\x. vec 0) = &0`,
  GEN_TAC THEN REWRITE_TAC[set_variation; NORM_0; SUM_0] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUP_SING] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
  MESON_TAC[ELEMENTARY_EMPTY; EMPTY_SUBSET]);;

let HAS_BOUNDED_SETVARIATION_ON_CMUL = prove
 (`!f:(real^M->bool)->real^N c s.
        f has_bounded_setvariation_on s
        ==> (\x. c % f x) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT; o_DEF]
     HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR) THEN
  REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC);;

let HAS_BOUNDED_SETVARIATION_ON_NEG = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> (\x. --(f x)) has_bounded_setvariation_on s`,
  REWRITE_TAC[VECTOR_ARITH `--x:real^N = -- &1 % x`] THEN
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_CMUL]);;

let HAS_BOUNDED_SETVARIATION_ON_ADD = prove
 (`!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. f x + g x) has_bounded_setvariation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_setvariation_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `B + C:real` THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. norm((f:(real^M->bool)->real^N) k)) +
              sum d (\k. norm((g:(real^M->bool)->real^N) k))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_ADD2]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[NORM_TRIANGLE]);;

let HAS_BOUNDED_SETVARIATION_ON_SUB = prove
 (`!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> (\x. f x - g x) has_bounded_setvariation_on s`,
  REWRITE_TAC[VECTOR_ARITH `x - y:real^N = x + --y`] THEN
  SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_ADD; HAS_BOUNDED_SETVARIATION_ON_NEG]);;

let HAS_BOUNDED_SETVARIATION_ON_NULL = prove
 (`!f:(real^M->bool)->real^N s.
        (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> f has_bounded_setvariation_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_setvariation_on] THEN
  EXISTS_TAC `&0` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[NORM_EQ_0] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC CONTENT_0_SUBSET_GEN THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[division_of; SUBSET_TRANS]);;

let SET_VARIATION_ELEMENTARY_LEMMA = prove
 (`!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> ((!d t. d division_of t /\ t SUBSET s
                    ==> sum d (\k. norm(f k)) <= b) <=>
             (!d. d division_of s ==> sum d (\k. norm(f k)) <= b))`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `d1:(real^M->bool)->bool`) THEN
  EQ_TAC THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `d2:(real^M->bool)->bool` THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN MP_TAC(ISPECL
   [`d2:(real^M->bool)->bool`; `d1:(real^M->bool)->bool`;
    `t:real^M->bool`; `s:real^M->bool`] PARTIAL_DIVISION_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `d3:(real^M->bool)->bool`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d3 (\k:real^M->bool. norm(f k:real^N))` THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_MESON_TAC[DIVISION_OF_FINITE]);;

let SET_VARIATION_ON_ELEMENTARY = prove
 (`!f:(real^M->bool)->real^N s.
        (?d. d division_of s)
        ==> set_variation s f =
             sup { sum d (\k. norm(f k)) | d division_of s}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[set_variation; sup] THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM] THEN
  ASM_SIMP_TAC[SET_VARIATION_ELEMENTARY_LEMMA]);;

let SET_VARIATION_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b.
        set_variation (interval[a,b]) f =
        sup { sum d (\k. norm(f k)) | d division_of interval[a,b]}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SET_VARIATION_ON_ELEMENTARY THEN
  REWRITE_TAC[ELEMENTARY_INTERVAL]);;

let HAS_BOUNDED_SETVARIATION_WORKS = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s
        ==> (!d t. d division_of t /\ t SUBSET s
                   ==> sum d (\k. norm(f k)) <= set_variation s f) /\
            (!B. (!d t. d division_of t /\ t SUBSET s
                        ==> sum d (\k. norm (f k)) <= B)
                 ==> set_variation s f <= B)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_setvariation_on] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `{ sum d (\k. norm((f:(real^M->bool)->real^N) k)) |
                  ?t. d division_of t /\ t SUBSET s}`
         SUP) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[set_variation] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&0`; `{}:(real^M->bool)->bool`] THEN
  REWRITE_TAC[SUM_CLAUSES] THEN EXISTS_TAC `{}:real^M->bool` THEN
  SIMP_TAC[division_of; EMPTY_SUBSET; NOT_IN_EMPTY; FINITE_EMPTY; UNIONS_0]);;

let HAS_BOUNDED_SETVARIATION_WORKS_ON_ELEMENTARY = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s /\ (?d. d division_of s)
        ==> (!d. d division_of s
                 ==> sum d (\k. norm(f k)) <= set_variation s f) /\
            (!B. (!d. d division_of s ==> sum d (\k. norm(f k)) <= B)
                 ==> set_variation s f <= B)`,
  SIMP_TAC[GSYM SET_VARIATION_ELEMENTARY_LEMMA] THEN
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS]);;

let HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b.
      f has_bounded_setvariation_on interval[a,b]
      ==> (!d. d division_of interval[a,b]
               ==> sum d (\k. norm(f k)) <= set_variation (interval[a,b]) f) /\
          (!B. (!d. d division_of interval[a,b]
                    ==> sum d (\k. norm(f k)) <= B)
               ==> set_variation (interval[a,b]) f <= B)`,
  SIMP_TAC[HAS_BOUNDED_SETVARIATION_WORKS_ON_ELEMENTARY; ELEMENTARY_INTERVAL]);;

let SET_VARIATION_UBOUND = prove
 (`!f:(real^M->bool)->real^N s B.
        f has_bounded_setvariation_on s /\
        (!d t. d division_of t /\ t SUBSET s ==> sum d (\k. norm(f k)) <= B)
        ==> set_variation s f <= B`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS]);;

let SET_VARIATION_UBOUND_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b B.
        f has_bounded_setvariation_on interval[a,b] /\
        (!d. d division_of interval[a,b] ==> sum d (\k. norm(f k)) <= B)
        ==> set_variation (interval[a,b]) f <= B`,
  SIMP_TAC[GSYM SET_VARIATION_ELEMENTARY_LEMMA; ELEMENTARY_INTERVAL] THEN
  MESON_TAC[SET_VARIATION_UBOUND]);;

let SET_VARIATION_LBOUND = prove
 (`!f:(real^M->bool)->real^N s B.
        f has_bounded_setvariation_on s /\
        (?d t. d division_of t /\ t SUBSET s /\ B <= sum d (\k. norm(f k)))
        ==> B <= set_variation s f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS; REAL_LE_TRANS]);;

let SET_VARIATION_LBOUND_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b B.
        f has_bounded_setvariation_on interval[a,b] /\
        (?d. d division_of interval[a,b] /\ B <= sum d (\k. norm(f k)))
        ==> B <= set_variation (interval[a,b]) f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL; REAL_LE_TRANS]);;

let SET_VARIATION = prove
 (`!f:(real^M->bool)->real^N s d t.
        f has_bounded_setvariation_on s /\ d division_of t /\ t SUBSET s
        ==> sum d (\k. norm(f k)) <= set_variation s f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS]);;

let SET_VARIATION_WORKS_ON_INTERVAL = prove
 (`!f:(real^M->bool)->real^N a b d.
        f has_bounded_setvariation_on interval[a,b] /\
        d division_of interval[a,b]
        ==> sum d (\k. norm(f k)) <= set_variation (interval[a,b]) f`,
  MESON_TAC[HAS_BOUNDED_SETVARIATION_WORKS_ON_INTERVAL]);;

let SET_VARIATION_POS_LE = prove
 (`!f:(real^M->bool)->real^N s.
        f has_bounded_setvariation_on s ==> &0 <= set_variation s f`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] SET_VARIATION)) THEN
  DISCH_THEN(MP_TAC o SPECL[`{}:(real^M->bool)->bool`; `{}:real^M->bool`]) THEN
  REWRITE_TAC[EMPTY_SUBSET; SUM_CLAUSES; DIVISION_OF_TRIVIAL]);;

let SET_VARIATION_GE_FUNCTION = prove
 (`!f:(real^M->bool)->real^N s a b.
        f has_bounded_setvariation_on s /\
        interval[a,b] SUBSET s /\ ~(interval[a,b] = {})
        ==> norm(f(interval[a,b])) <= set_variation s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SET_VARIATION_LBOUND THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `{interval[a:real^M,b]}` THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN
  ASM_REWRITE_TAC[SUM_SING; REAL_LE_REFL] THEN
  ASM_SIMP_TAC[DIVISION_OF_SELF]);;

let SET_VARIATION_ON_NULL = prove
 (`!f:(real^M->bool)->real^N s.
        (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = vec 0) /\
        content s = &0 /\ bounded s
        ==> set_variation s f = &0`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SET_VARIATION_UBOUND THEN
    ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[NORM_EQ_0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC CONTENT_0_SUBSET_GEN THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[division_of; SUBSET_TRANS];
    MATCH_MP_TAC SET_VARIATION_POS_LE THEN
    ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL]]);;

let SET_VARIATION_TRIANGLE = prove
 (`!f:(real^M->bool)->real^N g s.
        f has_bounded_setvariation_on s /\
        g has_bounded_setvariation_on s
        ==> set_variation s (\x. f x + g x)
             <= set_variation s f + set_variation s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SET_VARIATION_UBOUND THEN
  ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_ADD] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. norm((f:(real^M->bool)->real^N) k)) +
              sum d (\k. norm((g:(real^M->bool)->real^N) k))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[NORM_TRIANGLE];
    MATCH_MP_TAC REAL_LE_ADD2 THEN
    CONJ_TAC THEN MATCH_MP_TAC SET_VARIATION THEN ASM_MESON_TAC[]]);;

let OPERATIVE_LIFTED_SETVARIATION = prove
 (`!f:(real^M->bool)->real^N.
        operative(+) f
        ==> operative (lifted(+))
                      (\i. if f has_bounded_setvariation_on i
                           then SOME(set_variation i f) else NONE)`,
  let lemma1 = prove
   (`!f:(real^M->bool)->real B1 B2 k a b.
      1 <= k /\ k <= dimindex(:M) /\
      (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = &0) /\
      (!a b c. f(interval[a,b]) <=
               f(interval[a,b] INTER {x | x$k <= c}) +
               f(interval[a,b] INTER {x | x$k >= c})) /\
      (!d. d division_of (interval[a,b] INTER {x | x$k <= c})
           ==> sum d f <= B1) /\
      (!d. d division_of (interval[a,b] INTER {x | x$k >= c})
           ==> sum d f <= B2)
      ==> !d. d division_of interval[a,b] ==> sum d f <= B1 + B2`,
    REPEAT GEN_TAC THEN
    REPLICATE_TAC 4 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "L") (LABEL_TAC "R")) THEN
    GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {l INTER {x:real^M | x$k <= c} | l | l IN d /\
                                        ~(l INTER {x | x$k <= c} = {})} f +
      sum {l INTER {x | x$k >= c} | l | l IN d /\
                                        ~(l INTER {x | x$k >= c} = {})} f` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[DIVISION_SPLIT]] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    W(fun (asl,w) ->
         MP_TAC(PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO (lhand(rand w))) THEN
         MP_TAC(PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO (rand(rand w)))) THEN
    MATCH_MP_TAC(TAUT
     `(a1 /\ a2) /\ (b1 /\ b2 ==> c)
      ==> (a1 ==> b1) ==> (a2 ==> b2) ==> c`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THENL
       [MATCH_MP_TAC DIVISION_SPLIT_RIGHT_INJ;
        MATCH_MP_TAC DIVISION_SPLIT_LEFT_INJ] THEN
      ASM_MESON_TAC[];
      DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum d (f o (\l. l INTER {x | x$k <= c})) +
      sum d (f o (\l. l INTER {x:real^M | x$k >= c}))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[o_THM] THEN
      FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]);
      MATCH_MP_TAC(REAL_ARITH `x = y /\ w = z ==> x + w <= y + z`) THEN
      CONJ_TAC THEN MATCH_MP_TAC SUM_SUPERSET THEN
      REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} SUBSET s`] THEN
      REWRITE_TAC[SET_RULE `(x IN s /\ ~(x IN {x | x IN s /\ ~P x}) ==> Q x) <=>
                            (x IN s ==> P x ==> Q x)`] THEN
      SIMP_TAC[o_THM] THEN ASM_MESON_TAC[EMPTY_AS_INTERVAL; CONTENT_EMPTY]])
  and lemma2 = prove
   (`!f:(real^M->bool)->real B k.
      1 <= k /\ k <= dimindex(:M) /\
      (!a b. content(interval[a,b]) = &0 ==> f(interval[a,b]) = &0) /\
      (!d. d division_of interval[a,b] ==> sum d f <= B)
      ==> !d1 d2. d1 division_of (interval[a,b] INTER {x | x$k <= c}) /\
                  d2 division_of (interval[a,b] INTER {x | x$k >= c})
                  ==> sum d1 f + sum d2 f <= B`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d1 UNION d2:(real^M->bool)->bool`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `interval[a,b] = (interval[a,b] INTER {x:real^M | x$k <= c}) UNION
                        (interval[a,b] INTER {x:real^M | x$k >= c})`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `(!x. x IN t \/ x IN u) ==> (s = s INTER t UNION s INTER u)`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC DIVISION_DISJOINT_UNION THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM INTERIOR_INTER] THEN
        MATCH_MP_TAC(SET_RULE
         `!t. interior s SUBSET interior t /\ interior t = {}
              ==> interior s = {}`) THEN
        EXISTS_TAC `{x:real^M | x$k = c}` THEN CONJ_TAC THENL
         [ALL_TAC; REWRITE_TAC[INTERIOR_STANDARD_HYPERPLANE]] THEN
        MATCH_MP_TAC SUBSET_INTERIOR THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= b ==> y <= b`) THEN
      MATCH_MP_TAC SUM_UNION_NONZERO THEN
      REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC]) THEN
      X_GEN_TAC `k:real^M->bool` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
        (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC CONTENT_0_SUBSET_GEN THEN
      EXISTS_TAC `interval[a,b] INTER {x:real^M | x$k = c}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `(interval[a,b] INTER {x:real^M | x$k <= c}) INTER
                    (interval[a,b] INTER {x:real^M | x$k >= c})` THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC[SUBSET_INTER] THEN ASM_MESON_TAC[division_of];
          REWRITE_TAC[SET_RULE
            `(s INTER t) INTER (s INTER u) = s INTER t INTER u`] THEN
          SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC];
        SIMP_TAC[BOUNDED_INTER; BOUNDED_INTERVAL] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
         [REAL_ARITH `x = y <=> x <= y /\ x >= y`] THEN
        REWRITE_TAC[SET_RULE
         `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
        ASM_SIMP_TAC[GSYM INTER_ASSOC; INTERVAL_SPLIT] THEN
        REWRITE_TAC[CONTENT_EQ_0] THEN EXISTS_TAC `k:num` THEN
        ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC]]) in
  REWRITE_TAC[operative; NEUTRAL_VECTOR_ADD] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
  ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL; BOUNDED_INTERVAL;
   MONOIDAL_REAL_ADD; SET_VARIATION_ON_NULL; NEUTRAL_LIFTED;
   NEUTRAL_REAL_ADD] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real`; `k:num`] THEN
  STRIP_TAC THEN ASM_CASES_TAC
   `(f:(real^M->bool)->real^N) has_bounded_setvariation_on interval[a,b]` THEN
  ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `(f:(real^M->bool)->real^N) has_bounded_setvariation_on
      interval[a,b] INTER {x | x$k <= c} /\
      (f:(real^M->bool)->real^N) has_bounded_setvariation_on
      interval[a,b] INTER {x | x$k >= c}`
    ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_SETVARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[lifted] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SET_VARIATION_UBOUND_ON_INTERVAL THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] lemma1) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `a:real^M`; `b:real^M`] THEN
      ASM_SIMP_TAC[NORM_0] THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
          `x:real^N = y + z ==> norm(x) <= norm y + norm z`) THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_AND) THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; SET_VARIATION_WORKS_ON_INTERVAL]];
      ONCE_REWRITE_TAC[REAL_ARITH `x + y <= z <=> x <= z - y`] THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
      MATCH_MP_TAC SET_VARIATION_UBOUND_ON_INTERVAL THEN
      ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN
      X_GEN_TAC `d1:(real^M->bool)->bool` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x <= y - z <=> z <= y - x`] THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
      MATCH_MP_TAC SET_VARIATION_UBOUND_ON_INTERVAL THEN
      ASM_SIMP_TAC[GSYM INTERVAL_SPLIT] THEN
      X_GEN_TAC `d2:(real^M->bool)->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ARITH `x <= y - z <=> z + x <= y`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] lemma2) THEN
      EXISTS_TAC `k:num` THEN
      ASM_SIMP_TAC[NORM_0; SET_VARIATION_WORKS_ON_INTERVAL]];
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[lifted]) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_INTERVAL] THEN
    EXISTS_TAC `set_variation (interval[a,b] INTER {x | x$k <= c})
                              (f:(real^M->bool)->real^N) +
                set_variation (interval[a,b] INTER {x | x$k >= c}) f` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC
       (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM] lemma1) THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `a:real^M`; `b:real^M`] THEN
      ASM_SIMP_TAC[NORM_0] THEN REPEAT CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
          `x:real^N = y + z ==> norm(x) <= norm y + norm z`) THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC
         `(f:(real^M->bool)->real^N) has_bounded_setvariation_on
          (interval[a,b] INTER {x | x$k <= c})` THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; SET_VARIATION_WORKS_ON_INTERVAL];
        UNDISCH_TAC
         `(f:(real^M->bool)->real^N) has_bounded_setvariation_on
          (interval[a,b] INTER {x | x$k >= c})` THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; SET_VARIATION_WORKS_ON_INTERVAL]]]);;

let HAS_BOUNDED_SETVARIATION_ON_DIVISION = prove
 (`!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b]
        ==> ((!k. k IN d ==> f has_bounded_setvariation_on k) <=>
             f has_bounded_setvariation_on interval[a,b])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPERATIVE_DIVISION_AND THEN
  ASM_REWRITE_TAC[operative; NEUTRAL_AND] THEN CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[operative; NEUTRAL_VECTOR_ADD]) THEN
    ASM_SIMP_TAC[HAS_BOUNDED_SETVARIATION_ON_NULL; BOUNDED_INTERVAL];
    FIRST_ASSUM(MP_TAC o MATCH_MP OPERATIVE_LIFTED_SETVARIATION) THEN
    REWRITE_TAC[operative] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[lifted; distinctness "option"])]);;

let SET_VARIATION_ON_DIVISION = prove
 (`!f:(real^M->bool)->real^N a b d.
        operative (+) f /\ d division_of interval[a,b] /\
        f has_bounded_setvariation_on interval[a,b]
        ==> sum d (\k. set_variation k f) = set_variation (interval[a,b]) f`,
  let lemma0 = prove
   (`!op x y. lifted op (SOME x) y = SOME z <=> ?w. y = SOME w /\ op x w = z`,
    GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC option_INDUCT THEN
    REWRITE_TAC[lifted; distinctness "option"; injectivity "option"] THEN
    MESON_TAC[]) in
  let lemma = prove
   (`!P op f s z.
          monoidal op /\ FINITE s /\
          iterate(lifted op) s (\i. if P i then SOME(f i) else NONE) = SOME z
          ==> iterate op s f = z`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_LIFTED; NEUTRAL_LIFTED] THEN
    REWRITE_TAC[injectivity "option"] THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[lifted; distinctness "option"] THEN ASM_MESON_TAC[lemma0]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPERATIVE_LIFTED_SETVARIATION) THEN
  DISCH_THEN(MP_TAC o SPECL[`d:(real^M->bool)->bool`; `a:real^M`; `b:real^M`] o
    MATCH_MP (REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
        OPERATIVE_DIVISION)) THEN
  ASM_SIMP_TAC[MONOIDAL_LIFTED; MONOIDAL_REAL_ADD] THEN
  MP_TAC(ISPECL
   [`\k. (f:(real^M->bool)->real^N) has_bounded_setvariation_on k`;
    `(+):real->real->real`;
    `\k. set_variation k (f:(real^M->bool)->real^N)`;
    `d:(real^M->bool)->bool`;
    `set_variation (interval[a,b]) (f:(real^M->bool)->real^N)`]
   lemma) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_REWRITE_TAC[sum; MONOIDAL_REAL_ADD]);;

let SET_VARIATION_MONOTONE = prove
 (`!f:(real^M->bool)->real^N s t.
        f has_bounded_setvariation_on s /\ t SUBSET s
        ==> set_variation t f <= set_variation s f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_variation] THEN
  MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&0`; `{}:(real^M->bool)->bool`] THEN
    REWRITE_TAC[SUM_CLAUSES] THEN EXISTS_TAC `{}:real^M->bool` THEN
    REWRITE_TAC[EMPTY_SUBSET; DIVISION_OF_TRIVIAL];
    MATCH_MP_TAC(SET_RULE
     `(!d. P d ==> Q d) ==> {f d | P d} SUBSET {f d | Q d}`) THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    REWRITE_TAC[FORALL_IN_GSPEC; LEFT_IMP_EXISTS_THM] THEN
    ASM_REWRITE_TAC[GSYM has_bounded_setvariation_on]]);;

let HAS_BOUNDED_SETVARIATION_REFLECT2_EQ,SET_VARIATION_REFLECT2 =
 (CONJ_PAIR o prove)
 (`(!f:(real^M->bool)->real^N s.
        (\k. f(IMAGE (--) k)) has_bounded_setvariation_on (IMAGE (--) s) <=>
        f has_bounded_setvariation_on s) /\
   (!f:(real^M->bool)->real^N s.
        set_variation (IMAGE (--) s) (\k. f(IMAGE (--) k)) =
        set_variation s f)`,
  MATCH_MP_TAC SETVARIATION_EQUAL_LEMMA THEN
  EXISTS_TAC `IMAGE ((--):real^M->real^M)` THEN
  SIMP_TAC[IMAGE_SUBSET; GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; IMAGE_ID; REFLECT_INTERVAL] THEN
  SIMP_TAC[ETA_AX; DIVISION_OF_REFLECT] THEN
  SIMP_TAC[EQ_INTERVAL; TAUT `~q /\ (p /\ q \/ r) <=> ~q /\ r`] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ q /\ p`] THEN
  REWRITE_TAC[UNWIND_THM1; CONTRAPOS_THM] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; VECTOR_NEG_COMPONENT; REAL_LT_NEG2]);;

let HAS_BOUNDED_SETVARIATION_TRANSLATION2_EQ, SET_VARIATION_TRANSLATION2 =
 (CONJ_PAIR o prove)
 (`(!a f:(real^M->bool)->real^N s.
          (\k. f(IMAGE (\x. a + x) k))
          has_bounded_setvariation_on (IMAGE (\x. --a + x) s) <=>
          f has_bounded_setvariation_on s) /\
   (!a f:(real^M->bool)->real^N s.
          set_variation (IMAGE (\x. --a + x) s) (\k. f(IMAGE (\x. a + x) k)) =
          set_variation s f)`,
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `a:real^M` THEN
  MATCH_MP_TAC SETVARIATION_EQUAL_LEMMA THEN
  EXISTS_TAC `\s. IMAGE (\x:real^M. a + x) s` THEN
  SIMP_TAC[IMAGE_SUBSET; GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`; IMAGE_ID;
              VECTOR_ARITH `--a + a + x:real^N = x`] THEN
  REWRITE_TAC[GSYM INTERVAL_TRANSLATION] THEN
  SIMP_TAC[EQ_INTERVAL; TAUT `~q /\ (p /\ q \/ r) <=> ~q /\ r`] THEN
  REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ q /\ p`] THEN
  REWRITE_TAC[UNWIND_THM1; CONTRAPOS_THM] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY; VECTOR_ADD_COMPONENT; REAL_LT_LADD] THEN
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [ETA_AX] THEN
  ASM_SIMP_TAC[DIVISION_OF_TRANSLATION]);;

let HAS_BOUNDED_SETVARIATION_TRANSLATION = prove
 (`!f:(real^M->bool)->real^N s a.
        f has_bounded_setvariation_on s
        ==> (\k. f(IMAGE (\x. a + x) k))
            has_bounded_setvariation_on (IMAGE (\x. --a + x) s)`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_TRANSLATION2_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Absolute integrability (this is the same as Lebesgue integrability).      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("absolutely_integrable_on",(12,"right"));;

let absolutely_integrable_on = new_definition
 `f absolutely_integrable_on s <=>
        f integrable_on s /\ (\x. lift(norm(f x))) integrable_on s`;;

let ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f absolutely_integrable_on s ==> f integrable_on s`,
  SIMP_TAC[absolutely_integrable_on]);;

let ABSOLUTELY_INTEGRABLE_LE = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> norm(integral s f) <= drop(integral s (\x. lift(norm(f x))))`,
  REWRITE_TAC[absolutely_integrable_on] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]);;

let ABSOLUTELY_INTEGRABLE_0 = prove
 (`!s. (\x. vec 0) absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on; NORM_0; LIFT_NUM; INTEGRABLE_0]);;

let ABSOLUTELY_INTEGRABLE_CMUL = prove
 (`!f s c. f absolutely_integrable_on s
           ==> (\x. c % f(x)) absolutely_integrable_on s`,
  SIMP_TAC[absolutely_integrable_on; INTEGRABLE_CMUL; NORM_MUL; LIFT_CMUL]);;

let ABSOLUTELY_INTEGRABLE_NEG = prove
 (`!f s. f absolutely_integrable_on s
         ==> (\x. --f(x)) absolutely_integrable_on s`,
  SIMP_TAC[absolutely_integrable_on; INTEGRABLE_NEG; NORM_NEG]);;

let ABSOLUTELY_INTEGRABLE_NORM = prove
 (`!f s. f absolutely_integrable_on s
         ==> (\x. lift(norm(f x))) absolutely_integrable_on s`,
  SIMP_TAC[absolutely_integrable_on; NORM_LIFT; REAL_ABS_NORM]);;

let ABSOLUTELY_INTEGRABLE_ABS_1 = prove
 (`!f s. f absolutely_integrable_on s
         ==> (\x. lift(abs(drop(f x)))) absolutely_integrable_on s`,
  REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP; ABSOLUTELY_INTEGRABLE_NORM]);;

let ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL = prove
 (`!f:real^M->real^N s a b.
        f absolutely_integrable_on s /\ interval[a,b] SUBSET s
        ==> f absolutely_integrable_on interval[a,b]`,
  REWRITE_TAC[absolutely_integrable_on] THEN
  MESON_TAC[INTEGRABLE_ON_SUBINTERVAL]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> (\k. integral k f) has_bounded_setvariation_on s`,
  REWRITE_TAC[has_bounded_setvariation_on] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `drop(integral (s:real^M->bool) (\x. lift(norm(f x:real^N))))` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(UNIONS d:real^M->bool) SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; division_of]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (UNIONS d) (\x. lift(norm((f:real^M->real^N) x))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
      EXISTS_TAC `s:real^M->bool` THEN
      EXISTS_TAC `d:(real^M->bool)->bool` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[DIVISION_OF_SUBSET; division_of]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(vsum d (\i. integral i (\x:real^M. lift(norm(f x:real^N)))))` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[DROP_VSUM] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[o_THM] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_MESON_TAC[division_of; SUBSET_TRANS];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIVISION_OF_UNION_SELF]] THEN
    MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    MAP_EVERY EXISTS_TAC [`s:real^M->bool`; `d:(real^M->bool)->bool`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[]]);;

let lemma = prove
 (`!f:A->real^N g s e.
        sum s (\x. norm(f x - g x)) < e
        ==> FINITE s
            ==> abs(sum s (\x. norm(f x)) - sum s (\x. norm(g x))) < e`,
  REPEAT GEN_TAC THEN SIMP_TAC[GSYM SUM_SUB] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN NORM_ARITH_TAC);;

let BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b] /\
        (\k. integral k f) has_bounded_setvariation_on interval[a,b]
        ==> f absolutely_integrable_on interval[a,b]`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_INTERVAL] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[absolutely_integrable_on] THEN
  MP_TAC(ISPEC `IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of interval[a,b] }`
         SUP) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ABBREV_TAC
   `i = sup (IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of interval[a,b] })` THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ELEMENTARY_INTERVAL] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift i` THEN
  REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - e / &2`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i <= i - e / &2)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN
   `!x. ?e. &0 < e /\
            !i. i IN d /\ ~(x IN i) ==> ball(x:real^M,e) INTER i = {}`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN MP_TAC(ISPECL
     [`UNIONS {i:real^M->bool | i IN d /\ ~(x IN i)}`; `x:real^M`]
     SEPARATE_POINT_CLOSED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; IMP_CONJ] THEN
      FIRST_ASSUM(fun t -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
      REWRITE_TAC[CLOSED_INTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    SIMP_TAC[FORALL_IN_UNIONS; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_BALL] THEN
    REWRITE_TAC[IN_ELIM_THM; DE_MORGAN_THM; REAL_NOT_LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `k:real^M->real` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e / &2` o MATCH_MP HENSTOCK_LEMMA) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^M. g(x) INTER ball(x,k x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GAUGE_INTER THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[gauge; CENTRE_IN_BALL; OPEN_BALL];
    ALL_TAC] THEN
  REWRITE_TAC[FINE_INTER] THEN X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ABBREV_TAC
   `p' = {(x:real^M,k:real^M->bool) |
                ?i l. x IN i /\ i IN d /\ (x,l) IN p /\ k = i INTER l}` THEN
  SUBGOAL_THEN `g fine (p':(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "p'" THEN
    MP_TAC(ASSUME `g fine (p:(real^M#(real^M->bool))->bool)`) THEN
    REWRITE_TAC[fine; IN_ELIM_PAIR_THM] THEN
    MESON_TAC[SET_RULE `k SUBSET l ==> (i INTER k) SUBSET l`];
    ALL_TAC] THEN
  SUBGOAL_THEN `p' tagged_division_of interval[a:real^M,b]` ASSUME_TAC THENL
   [REWRITE_TAC[TAGGED_DIVISION_OF] THEN EXPAND_TAC "p'" THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `IMAGE (\(k,(x,l)). x,k INTER l)
              {k,xl | k IN (d:(real^M->bool)->bool) /\
                      xl IN (p:(real^M#(real^M->bool))->bool)}` THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_PRODUCT] THEN
      EXPAND_TAC "p'" THEN REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM; IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`i:real^M->bool`; `l:real^M->bool`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[IN_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `l SUBSET s ==> (k INTER l) SUBSET s`) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `i:real^M->bool` o el 1 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[INTER_INTERVAL] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY X_GEN_TAC
       [`x1:real^M`; `k1:real^M->bool`; `x2:real^M`; `k2:real^M->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `i1:real^M->bool` (X_CHOOSE_THEN `l1:real^M->bool`
          STRIP_ASSUME_TAC)) MP_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `i2:real^M->bool` (X_CHOOSE_THEN `l2:real^M->bool`
          STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `(interior(i1) INTER interior(i2) = {} \/
         interior(l1) INTER interior(l2) = {}) /\
        interior(i1 INTER l1) SUBSET interior(i1) /\
        interior(i2 INTER l2) SUBSET interior(i2) /\
        interior(i1 INTER l1) SUBSET interior(l1) /\
        interior(i2 INTER l2) SUBSET interior(l2)
        ==> interior(i1 INTER l1) INTER interior(i2 INTER l2) = {}`) THEN
      SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`x1:real^M`; `l1:real^M->bool`; `x2:real^M`; `l2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`i1:real^M->bool`; `i2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check(is_neg o concl)) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `i SUBSET s ==> (i INTER k) SUBSET s`) THEN
      ASM_MESON_TAC[division_of];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[MESON[]
     `p /\ q /\ r /\ x = t /\ P x <=> x = t /\ p /\ q /\ r /\ P t`] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(?a b c d. P a b c d) <=> (?d b c a. P a b c d)`] THEN
    REWRITE_TAC[IN_INTER; UNWIND_THM2] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^M->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^M` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o last o CONJUNCTS o
        GEN_REWRITE_RULE I [division_of]) THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `k:real^M->bool`]) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `(\x:real^M. ball (x,k x)) fine p` THEN
    REWRITE_TAC[fine; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p':(real^M#(real^M->bool))->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[tagged_division_of]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  REWRITE_TAC[LAMBDA_PAIR] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  ASM_SIMP_TAC[DROP_VSUM; o_DEF; SUM_SUB; DROP_SUB; ABS_DROP] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; DROP_CMUL; NORM_MUL; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
    `!sni. i - e / &2 < sni /\
           sni' <= i /\ sni <= sni' /\ sf' = sf
              ==> abs(sf' - sni') < e / &2
                  ==> abs(sf - i) < e`) THEN
  EXISTS_TAC `sum d (\k. norm (integral k (f:real^M->real^N)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\k. norm(integral k (f:real^M->real^N))`;
                   `p':(real^M#(real^M->bool))->bool`;
                   `interval[a:real^M,b]`] SUM_OVER_TAGGED_DIVISION_LEMMA) THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIVISION_OF_TAGGED_DIVISION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `p' = {x:real^M,(i INTER l:real^M->bool) |
            (x,l) IN p /\ i IN d /\ ~(i INTER l = {})}`
  (LABEL_TAC "p'") THENL
   [EXPAND_TAC "p'" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    REWRITE_TAC[PAIR_EQ; GSYM CONJ_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `i:real^M->bool` THEN REWRITE_TAC[] THEN
    CONV_TAC(RAND_CONV UNWIND_CONV) THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    X_GEN_TAC `l:real^M->bool` THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `k:real^M->bool = i INTER l` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[IN_INTER; GSYM MEMBER_NOT_EMPTY] THEN
    EQ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^M`; `i:real^M->bool`]) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^M` THEN ASM_REWRITE_TAC[INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `(\x:real^M. ball (x,k x)) fine p` THEN
    REWRITE_TAC[fine; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\y. norm(integral y (f:real^M->real^N))`;
      `p':(real^M#(real^M->bool))->bool`;
      `interval[a:real^M,b]`]
     SUM_OVER_TAGGED_DIVISION_LEMMA) THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {i INTER l | i IN d /\
                 (l IN IMAGE SND (p:(real^M#(real^M->bool))->bool))}
                    (\k. norm(integral k (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_SUPERSET THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        REWRITE_TAC[FORALL_PAIR_THM] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; PAIR_EQ; EXISTS_PAIR_THM] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC
       [`kk:real^M->bool`; `i:real^M->bool`; `l:real^M->bool`] THEN
      ASM_CASES_TAC `kk:real^M->bool = i INTER l` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; UNWIND_THM1] THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x:real^M`)) MP_TAC) THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPECL
       [`x:real^M`; `x:real^M`; `i:real^M->bool`; `l:real^M->bool`]) THEN
      ASM_SIMP_TAC[INTEGRAL_EMPTY; NORM_0]] THEN
    SUBGOAL_THEN
     `{k INTER l | k IN d /\ l IN IMAGE SND (p:(real^M#(real^M->bool))->bool)} =
      IMAGE (\(k,l). k INTER l) {k,l | k IN d /\ l IN IMAGE SND p}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
      REWRITE_TAC[PAIR_EQ] THEN
      CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN MESON_TAC[];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o rand o snd) THEN
    ANTS_TAC THENL
     [ASSUME_TAC(MATCH_MP DIVISION_OF_TAGGED_DIVISION
        (ASSUME `p tagged_division_of interval[a:real^M,b]`)) THEN
      ASM_SIMP_TAC[FINITE_PRODUCT; FINITE_IMAGE] THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC
       [`l1:real^M->bool`; `k1:real^M->bool`;
        `l2:real^M->bool`; `k2:real^M->bool`] THEN
      REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
      SUBGOAL_THEN `interior(l2 INTER k2:real^M->bool) = {}` MP_TAC THENL
       [ALL_TAC;
        MP_TAC(ASSUME `d division_of interval[a:real^M,b]`) THEN
        REWRITE_TAC[division_of] THEN
        DISCH_THEN(MP_TAC o SPEC `l2:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ASSUME
         `(IMAGE SND (p:(real^M#(real^M->bool))->bool))
                division_of interval[a:real^M,b]`) THEN
        REWRITE_TAC[division_of] THEN
        DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[INTER_INTERVAL] THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_EQ_0] THEN
        MATCH_MP_TAC INTEGRAL_NULL THEN
        ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR]] THEN
      MATCH_MP_TAC(SET_RULE
       `(interior(k1) INTER interior(k2) = {} \/
         interior(l1) INTER interior(l2) = {}) /\
        interior(l1 INTER k1) SUBSET interior(k1) /\
        interior(l2 INTER k2) SUBSET interior(k2) /\
        interior(l1 INTER k1) SUBSET interior(l1) /\
        interior(l2 INTER k2) SUBSET interior(l2) /\
        interior(l1 INTER k1) = interior(l2 INTER k2)
        ==> interior(l2 INTER k2) = {}`) THEN
      SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `d division_of interval[a:real^M,b]`) THEN
      REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`l1:real^M->bool`; `l2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME
       `(IMAGE SND (p:(real^M#(real^M->bool))->bool))
              division_of interval[a:real^M,b]`) THEN
      REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`k1:real^M->bool`; `k2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
    ASM_SIMP_TAC[GSYM SUM_SUM_PRODUCT; FINITE_IMAGE] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum { k INTER l |
             l IN IMAGE SND (p:(real^M#(real^M->bool))->bool)}
          (\k. norm(integral k (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO o lhand o snd) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[o_DEF; REAL_LE_REFL]] THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN
      MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `interior(k INTER k2:real^M->bool) = {}` MP_TAC THENL
       [ALL_TAC;
        MP_TAC(MATCH_MP DIVISION_OF_TAGGED_DIVISION
         (ASSUME `p tagged_division_of interval[a:real^M,b]`)) THEN
        MP_TAC(ASSUME `d division_of interval[a:real^M,b]`) THEN
        REWRITE_TAC[division_of] THEN
        DISCH_THEN(MP_TAC o SPEC `k:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[INTER_INTERVAL; GSYM CONTENT_EQ_0_INTERIOR] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[INTER_INTERVAL] THEN
        SIMP_TAC[GSYM CONTENT_EQ_0_INTERIOR; INTEGRAL_NULL; NORM_0]] THEN
      MATCH_MP_TAC(SET_RULE
       `interior(k INTER k2) SUBSET interior(k1 INTER k2) /\
        interior(k1 INTER k2) = {}
        ==> interior(k INTER k2) = {}`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(MATCH_MP DIVISION_OF_TAGGED_DIVISION
         (ASSUME `p tagged_division_of interval[a:real^M,b]`)) THEN
      REWRITE_TAC[division_of] THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      REWRITE_TAC[INTERIOR_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b]` ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    ABBREV_TAC `d' =
        {interval[u,v] INTER l |l|
                l IN IMAGE SND (p:(real^M#(real^M->bool))->bool) /\
                ~(interval[u,v] INTER l = {})}` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum d' (\k. norm (integral k (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SUM_SUPERSET THEN
      EXPAND_TAC "d'" THEN REWRITE_TAC[SUBSET; SET_RULE
       `a IN {f x |x| x IN s /\ ~(f x = b)} <=>
        a IN {f x | x IN s} /\ ~(a = b)`] THEN
      SIMP_TAC[IMP_CONJ; INTEGRAL_EMPTY; NORM_0]] THEN
    SUBGOAL_THEN `d' division_of interval[u:real^M,v]` ASSUME_TAC THENL
     [EXPAND_TAC "d'" THEN MATCH_MP_TAC DIVISION_INTER_1 THEN
      EXISTS_TAC `interval[a:real^M,b]` THEN
      ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(vsum d' (\i. integral i (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
      ASM_MESON_TAC[INTEGRABLE_ON_SUBINTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[division_of];
    ALL_TAC] THEN
  REMOVE_THEN "p'" SUBST_ALL_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x,i INTER l | (x,l) IN p /\ i IN d}
                  (\(x,k:real^M->bool).
                      abs(content k) * norm((f:real^M->real^N) x))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `i:real^M->bool`] THEN
    ASM_CASES_TAC `i:real^M->bool = {}` THEN
    ASM_SIMP_TAC[CONTENT_EMPTY; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
    MATCH_MP_TAC(TAUT `(a <=> b) ==> a /\ ~b ==> c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
    REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x,i INTER l | x,l IN (p:(real^M#(real^M->bool))->bool) /\ i IN d} =
    IMAGE (\((x,l),k). x,k INTER l) {m,k | m IN p /\ k IN d}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    CONV_TAC(REDEPTH_CONV UNWIND_CONV) THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PRODUCT] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`x1:real^M`; `l1:real^M->bool`; `k1:real^M->bool`;
      `x2:real^M`; `l2:real^M->bool`; `k2:real^M->bool`] THEN
    REWRITE_TAC[PAIR_EQ] THEN
    ASM_CASES_TAC `x1:real^M = x2` THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ1_TAC THEN
    REWRITE_TAC[REAL_ABS_ZERO] THEN
    SUBGOAL_THEN `interior(k2 INTER l2:real^M->bool) = {}` MP_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `p tagged_division_of interval[a:real^M,b]`) THEN
      REWRITE_TAC[TAGGED_DIVISION_OF] THEN
      DISCH_THEN(MP_TAC o el 1 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`x2:real^M`; `l2:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[INTER_INTERVAL; CONTENT_EQ_0_INTERIOR]] THEN
    MATCH_MP_TAC(SET_RULE
     `(interior(k1) INTER interior(k2) = {} \/
       interior(l1) INTER interior(l2) = {}) /\
      interior(k1 INTER l1) SUBSET interior(k1) /\
      interior(k2 INTER l2) SUBSET interior(k2) /\
      interior(k1 INTER l1) SUBSET interior(l1) /\
      interior(k2 INTER l2) SUBSET interior(l2) /\
      interior(k1 INTER l1) = interior(k2 INTER l2)
      ==> interior(k2 INTER l2) = {}`) THEN
    SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`k1:real^M->bool`; `k2:real^M->bool`]) THEN
    MP_TAC(ASSUME `p tagged_division_of interval[a:real^M,b]`) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    DISCH_THEN(MP_TAC o SPECL
     [`x2:real^M`; `l1:real^M->bool`; `x2:real^M`; `l2:real^M->bool`]) THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
  ASM_SIMP_TAC[GSYM SUM_SUM_PRODUCT] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
  DISCH_TAC THEN REWRITE_TAC[o_THM; SUM_RMUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
   (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
  THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum d (\k. content(k INTER interval[u:real^M,v]))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[real_abs] THEN
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?w z:real^M. k = interval[w,z]`
      (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    REWRITE_TAC[INTER_INTERVAL; CONTENT_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {k INTER interval[u:real^M,v] | k IN d} content` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_IMAGE_NONZERO THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `interior(k2 INTER interval[u:real^M,v]) = {}` MP_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool` o el 1 o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[INTER_INTERVAL; CONTENT_EQ_0_INTERIOR]] THEN
    MATCH_MP_TAC(SET_RULE
     `interior(k2 INTER i) SUBSET interior(k1 INTER k2) /\
      interior(k1 INTER k2) = {}
      ==> interior(k2 INTER i) = {}`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
    REWRITE_TAC[INTERIOR_INTER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {k INTER interval[u:real^M,v] |k|
                      k IN d /\ ~(k INTER interval[u,v] = {})} content` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; SET_RULE
     `a IN {f x |x| x IN s /\ ~(f x = b)} <=>
      a IN {f x | x IN s} /\ ~(a = b)`] THEN
    SIMP_TAC[IMP_CONJ; CONTENT_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC ADDITIVE_CONTENT_DIVISION THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC DIVISION_INTER_1 THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN ASM_REWRITE_TAC[]);;

let BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N.
        f integrable_on UNIV /\
        (\k. integral k f) has_bounded_setvariation_on (:real^M)
        ==> f absolutely_integrable_on UNIV`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[absolutely_integrable_on] THEN
  MP_TAC(ISPEC `IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of (UNIONS d) }`
         SUP) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  ABBREV_TAC
   `i = sup (IMAGE (\d. sum d (\k. norm(integral k (f:real^M->real^N))))
                      {d | d division_of (UNIONS d) })` THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    EXISTS_TAC `{}:(real^M->bool)->bool` THEN
    REWRITE_TAC[UNIONS_0; DIVISION_OF_TRIVIAL];
    ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[integrable_on] THEN EXISTS_TAC `lift i` THEN
  REWRITE_TAC[HAS_INTEGRAL_ALT; IN_UNIV] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
      (REWRITE_RULE[HAS_BOUNDED_SETVARIATION_ON_INTERVAL]
       BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL)) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_integrable_on]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN EXISTS_TAC `(:real^M)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    EXISTS_TAC `B:real` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIVISION_OF_UNION_SELF];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i - e`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i <= i - e)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `bounded(UNIONS d:real^M->bool)` MP_TAC THENL
   [ASM_MESON_TAC[ELEMENTARY_BOUNDED]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `K + &1` THEN ASM_SIMP_TAC[REAL_LT_ADD; REAL_LT_01] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
  REWRITE_TAC[ABS_DROP; DROP_SUB; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s1. i - e < s1 /\ s1 <= s /\ s < i + e ==> abs(s - i) < e`) THEN
  EXISTS_TAC `sum (d:(real^M->bool)->bool) (\k. norm (integral k
                    (f:real^M->real^N)))` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum d
      (\k. drop(integral k (\x. lift(norm((f:real^M->real^N) x)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LE THEN
      ASM_REWRITE_TAC[absolutely_integrable_on] THEN
      MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral (UNIONS d)
                      (\x. lift(norm((f:real^M->real^N) x))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(MESON[REAL_LE_REFL; LIFT_DROP]
       `lift x = y ==> x <= drop y`) THEN
      ASM_SIMP_TAC[LIFT_SUM; o_DEF; LIFT_DROP] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_BOTTOMUP THEN
      FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]);
      ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(vec 0:real^M,K + &1)` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      ASM_SIMP_TAC[NORM_ARITH `norm(x) <= K ==> dist(vec 0,x) < K + &1`];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN
    EXISTS_TAC `d:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
  REWRITE_TAC[HAS_INTEGRAL_INTEGRAL; has_integral] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
                HENSTOCK_LEMMA) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "+")) THEN
  SUBGOAL_THEN `?p. p tagged_division_of interval[a:real^M,b] /\
                    d1 fine p /\ d2 fine p`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FINE_INTER] THEN MATCH_MP_TAC FINE_DIVISION_EXISTS THEN
    ASM_SIMP_TAC[GAUGE_INTER];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `p:(real^M#(real^M->bool)->bool)`) THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `p:(real^M#(real^M->bool)->bool)`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[tagged_division_of]; ALL_TAC] THEN
  REWRITE_TAC[ABS_DROP; DROP_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR] THEN DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[DROP_VSUM; o_DEF; SUM_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; DROP_CMUL; NORM_MUL; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `sf' = sf /\ si <= i
    ==> abs(sf - si) < e / &2
        ==> abs(sf' - di) < e / &2
            ==> di < i + e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; real_abs] THEN
    ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum p (\(x:real^M,k). norm(integral k f)) =
    sum (IMAGE SND p) (\k. norm(integral k (f:real^M->real^N)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_OVER_TAGGED_DIVISION_LEMMA THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[INTEGRAL_NULL; NORM_0];
    ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC PARTIAL_DIVISION_OF_TAGGED_DIVISION THEN
  EXISTS_TAC `interval[a:real^M,b]` THEN ASM_MESON_TAC[tagged_division_of]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ = prove
 (`!f:real^M->real^N.
        f absolutely_integrable_on (:real^M) <=>
        f integrable_on (:real^M) /\
        (\k. integral k f) has_bounded_setvariation_on (:real^M)`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION;
           BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE;
           ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ = prove
 (`!f:real^M->real^N a b.
        f absolutely_integrable_on interval[a,b] <=>
        f integrable_on interval[a,b] /\
        (\k. integral k f) has_bounded_setvariation_on interval[a,b]`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION;
           BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL;
           ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let ABSOLUTELY_INTEGRABLE_SET_VARIATION = prove
 (`!f:real^M->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> set_variation (interval[a,b]) (\k. integral k f) =
                 drop(integral (interval[a,b]) (\x. lift(norm(f x))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[set_variation] THEN
  MATCH_MP_TAC REAL_SUP_UNIQUE THEN
  REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `d:(real^M->bool)->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `drop(integral s (\x. lift(norm((f:real^M->real^N) x))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\x. lift(norm((f:real^M->real^N) x))`;
                     `d:(real^M->bool)->bool`; `s:real^M->bool`]
        INTEGRAL_COMBINE_DIVISION_TOPDOWN) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
        EXISTS_TAC `interval[a:real^M,b]` THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
      ASM_SIMP_TAC[DROP_VSUM] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[o_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; GSYM absolutely_integrable_on] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN
      ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL; SUBSET_TRANS];
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
      EXISTS_TAC `interval[a:real^M,b]` THEN ASM_MESON_TAC[]];
    X_GEN_TAC `B:real` THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    ABBREV_TAC `e = drop(integral (interval [a,b])
                                  (\x. lift(norm((f:real^M->real^N) x)))) -
                    B` THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2` o MATCH_MP HENSTOCK_LEMMA) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F"))) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [absolutely_integrable_on]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[HAS_INTEGRAL_INTEGRAL; has_integral] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))) THEN
    MP_TAC(ISPECL
     [`\x. (d1:real^M->real^M->bool) x INTER d2 x`;
      `a:real^M`; `b:real^M`]
     FINE_DIVISION_EXISTS) THEN
    ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^M#(real^M->bool)->bool`
        STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "A" (MP_TAC o SPEC  `p:real^M#(real^M->bool)->bool`) THEN
    REMOVE_THEN "F" (MP_TAC o SPEC  `p:real^M#(real^M->bool)->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[tagged_division_of]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x. lift(norm((f:real^M->real^N) x))`;
      `a:real^M`; `b:real^M`; `p:real^M#(real^M->bool)->bool`]
      INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST_ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `abs(sum p (\(x,k). content k * norm((f:real^M->real^N) x)) -
          sum p (\(x,k:real^M->bool). norm(integral k f))) < e / &2`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_LET_TRANS)) THEN
      ASM_SIMP_TAC[GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_ABS_LE THEN
      ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH
       `x = norm u ==> abs(x - norm v) <= norm(u - v:real^N)`) THEN
      REWRITE_TAC[NORM_MUL; real_abs] THEN
      ASM_MESON_TAC[CONTENT_POS_LE; TAGGED_DIVISION_OF];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM NORM_LIFT] THEN
    ASM_SIMP_TAC[LIFT_SUB; LIFT_SUM] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM; o_DEF; LIFT_CMUL; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NORM_ARITH
     `norm(x - y:real^N) < e / &2 /\ norm(x - z) < e / &2
      ==> norm(y - z) < e`)) THEN
    REWRITE_TAC[NORM_1; DROP_SUB] THEN
    DISCH_THEN(MP_TAC o SPEC `B:real` o MATCH_MP
     (REAL_ARITH `!B. abs(x - y) < e ==> y - B = e ==> &0 < x - B`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[DROP_VSUM; REAL_SUB_LT] THEN
    REWRITE_TAC[o_DEF; LAMBDA_PAIR_THM; LIFT_DROP] THEN DISCH_TAC THEN
    EXISTS_TAC `IMAGE SND (p:real^M#(real^M->bool)->bool)` THEN CONJ_TAC THENL
     [EXISTS_TAC `interval[a:real^M,b]` THEN
      ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION; SUBSET_REFL];
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SUM_OVER_TAGGED_DIVISION_LEMMA)) THEN
      DISCH_THEN(fun th ->
       W(MP_TAC o PART_MATCH (rand o rand) th o rand o snd)) THEN
      SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]]);;

let ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else vec 0)
              absolutely_integrable_on (:real^M) <=>
         f absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_RESTRICT_UNIV;
              COND_RAND; NORM_0; LIFT_NUM]);;

let ABSOLUTELY_INTEGRABLE_CONST = prove
 (`!a b c. (\x. c) absolutely_integrable_on interval[a,b]`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_CONST]);;

let ABSOLUTELY_INTEGRABLE_ADD = prove
 (`!f:real^M->real^N g s.
        f absolutely_integrable_on s /\
        g absolutely_integrable_on s
        ==> (\x. f(x) + g(x)) absolutely_integrable_on s`,
  SUBGOAL_THEN
   `!f:real^M->real^N g.
        f absolutely_integrable_on (:real^M) /\
        g absolutely_integrable_on (:real^M)
        ==> (\x. f(x) + g(x)) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LID]] THEN
  REPEAT STRIP_TAC THEN
  EVERY_ASSUM(STRIP_ASSUME_TAC o
   GEN_REWRITE_RULE I [absolutely_integrable_on]) THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD] THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `(:real^M)`]
     ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`]
     ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  DISCH_THEN(X_CHOOSE_TAC `B1:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `B2:real`) THEN EXISTS_TAC `B1 + B2:real` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^M->bool)->bool`)) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= B1 ==> x <= a + B2 ==> x <= B1 + B2`)) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `b <= B2 ==> x <= a + b ==> x <= a + B2`)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
  FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH `x = y + z ==> norm(x) <= norm(y) + norm(z)`) THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let ABSOLUTELY_INTEGRABLE_SUB = prove
 (`!f:real^M->real^N g s.
        f absolutely_integrable_on s /\
        g absolutely_integrable_on s
        ==> (\x. f(x) - g(x)) absolutely_integrable_on s`,
  REWRITE_TAC[VECTOR_SUB] THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_ADD; ABSOLUTELY_INTEGRABLE_NEG]);;

let ABSOLUTELY_INTEGRABLE_LINEAR = prove
 (`!f:real^M->real^N h:real^N->real^P s.
        f absolutely_integrable_on s /\ linear h
        ==> (h o f) absolutely_integrable_on s`,
  SUBGOAL_THEN
   `!f:real^M->real^N h:real^N->real^P.
        f absolutely_integrable_on (:real^M) /\ linear h
        ==> (h o f) absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
     ANTE_RES_THEN MP_TAC th THEN
     ASSUME_TAC(MATCH_MP LINEAR_0 (CONJUNCT2 th))) THEN
    ASM_REWRITE_TAC[o_DEF; COND_RAND]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
  ASM_SIMP_TAC[INTEGRABLE_LINEAR; HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o MATCH_MP
              LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real`) THEN EXISTS_TAC `B * b:real` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * sum d (\k. norm(integral k (f:real^M->real^N)))` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_LE THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(h(integral (interval[a,b]) (f:real^M->real^N)):real^P)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC HAS_INTEGRAL_LINEAR THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let ABSOLUTELY_INTEGRABLE_VSUM = prove
 (`!f:A->real^M->real^N s t.
        FINITE t /\
        (!a. a IN t ==> (f a) absolutely_integrable_on s)
        ==>  (\x. vsum t (\a. f a x)) absolutely_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; ABSOLUTELY_INTEGRABLE_0; IN_INSERT;
           ABSOLUTELY_INTEGRABLE_ADD; ETA_AX]);;

let ABSOLUTELY_INTEGRABLE_ABS = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s
        ==> (\x. (lambda i. abs(f(x)$i)):real^N) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. (lambda i. abs(f(x)$i))):real^M->real^N =
    (\x. vsum (1..dimindex(:N))
        (\i. (((\y. (lambda j. if j = i then drop y else &0)) o
               (\x. lift(norm((lambda j. if j = i then x$i else &0):real^N))) o
               (f:real^M->real^N)) x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:real^M` THEN
    GEN_REWRITE_TAC I [CART_EQ] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VSUM_COMPONENT; o_THM] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; LIFT_DROP] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    REWRITE_TAC[vector_norm; dot] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sqrt(sum (1..dimindex(:N))
                         (\k. if k = i then ((f:real^M->real^N) x)$i pow 2
                              else &0))` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_DELTA; IN_NUMSEG; POW_2_SQRT_ABS]; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POW_2];
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_VSUM THEN
  REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[DROP_ADD; REAL_ADD_LID; DROP_CMUL; REAL_MUL_RZERO]] THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
  SUBGOAL_THEN
    `(\x. lambda j. if j = i then (f x:real^N)$i else &0):real^M->real^N =
     (\x. lambda j. if j = i then x$i else &0) o f`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let ABSOLUTELY_INTEGRABLE_MAX = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f absolutely_integrable_on s /\ g absolutely_integrable_on s
        ==> (\x. (lambda i. max (f(x)$i) (g(x)$i)):real^N)
            absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ABS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o
     MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
           VECTOR_ADD_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let ABSOLUTELY_INTEGRABLE_MAX_1 = prove
 (`!f:real^M->real g:real^M->real s.
        (\x. lift(f x)) absolutely_integrable_on s /\
        (\x. lift(g x)) absolutely_integrable_on s
        ==> (\x. lift(max (f x) (g x))) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (lambda i. max (lift(f x)$i) (lift(g x)$i)):real^1)
                absolutely_integrable_on (s:real^M->bool)`
  MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_MAX]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN SIMP_TAC[LAMBDA_BETA; lift]);;

let ABSOLUTELY_INTEGRABLE_MIN = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f absolutely_integrable_on s /\ g absolutely_integrable_on s
        ==> (\x. (lambda i. min (f(x)$i) (g(x)$i)):real^N)
            absolutely_integrable_on s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SUB) THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ABS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_ADD) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SUB) THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o
     MATCH_MP ABSOLUTELY_INTEGRABLE_CMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN
  SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
           VECTOR_ADD_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let ABSOLUTELY_INTEGRABLE_MIN_1 = prove
 (`!f:real^M->real g:real^M->real s.
        (\x. lift(f x)) absolutely_integrable_on s /\
        (\x. lift(g x)) absolutely_integrable_on s
        ==> (\x. lift(min (f x) (g x))) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (lambda i. min (lift(f x)$i) (lift(g x)$i)):real^1)
                absolutely_integrable_on (s:real^M->bool)`
  MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_MIN]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; CART_EQ] THEN SIMP_TAC[LAMBDA_BETA; lift]);;

let ABSOLUTELY_INTEGRABLE_ABS_EQ = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
          f integrable_on s /\
          (\x. (lambda i. abs(f(x)$i)):real^N) integrable_on s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_ABS;
           ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  SUBGOAL_THEN
   `!f:real^M->real^N.
        f integrable_on (:real^M) /\
        (\x. (lambda i. abs(f(x)$i)):real^N) integrable_on (:real^M)
        ==> f absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV;
                     GSYM INTEGRABLE_RESTRICT_UNIV] THEN
    DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    REWRITE_TAC[CART_EQ] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[LAMBDA_BETA; COND_COMPONENT; VEC_COMPONENT] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ABS_0]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  EXISTS_TAC
   `sum (1..dimindex(:N))
        (\i. integral (:real^M)
              (\x. (lambda j. abs ((f:real^M->real^N) x$j)):real^N)$i)` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. sum (1..dimindex(:N))
      (\i. integral k
              (\x. (lambda j. abs ((f:real^M->real^N) x$j)):real^N)$i))` THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    FIRST_ASSUM(fun t -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION t]) THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (1..dimindex(:N))
             (\i. abs((integral (interval[a,b]) (f:real^M->real^N))$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ --x <= y ==> abs(x) <= y`) THEN
    ASM_SIMP_TAC[GSYM VECTOR_NEG_COMPONENT] THEN
    SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[a,b] /\
        (\x. (lambda i. abs (f x$i)):real^N) integrable_on interval[a,b]`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_NEG] THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_COMPONENT_LE THEN
    ASM_SIMP_TAC[INTEGRABLE_NEG; LAMBDA_BETA] THEN
    ASM_SIMP_TAC[VECTOR_NEG_COMPONENT] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST_ALL_TAC THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(integral (UNIONS d)
              (\x. (lambda j. abs ((f:real^M->real^N) x$j)):real^N))$k` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_COMPONENT] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRAL_SUBSET_COMPONENT_LE THEN
    ASM_SIMP_TAC[LAMBDA_BETA; SUBSET_UNIV; REAL_ABS_POS]] THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
  MAP_EVERY EXISTS_TAC [`(:real^M)`; `d:(real^M->bool)->bool`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV]);;

let NONNEGATIVE_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N)
               ==> &0 <= f(x)$i) /\
        f integrable_on s
        ==> f absolutely_integrable_on s`,
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_ABS_EQ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_EQ THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; real_abs]);;

let ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND = prove
 (`!f:real^M->real^N g s.
        (!x. x IN s ==> norm(f x) <= drop(g x)) /\
        f integrable_on s /\ g integrable_on s
        ==> f absolutely_integrable_on s`,
  SUBGOAL_THEN
   `!f:real^M->real^N g.
        (!x. norm(f x) <= drop(g x)) /\
        f integrable_on (:real^M) /\ g integrable_on (:real^M)
        ==> f absolutely_integrable_on (:real^M)`
  ASSUME_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV; GSYM
                     ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(\x. if x IN s then g x else vec 0):real^M->real^1` THEN
    ASM_REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; NORM_0; DROP_VEC]] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BOUNDED_SETVARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_UNIV] THEN
  EXISTS_TAC `drop(integral(:real^M) g)` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum d (\k. drop(integral k (g:real^M->real^1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (UNIONS d:real^M->bool) g)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= x`) THEN
    ASM_SIMP_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_SUM; o_DEF] THEN
    MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_BOTTOMUP THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; IN_UNIV] THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[NORM_ARITH `norm(x) <= y ==> &0 <= y`]] THEN
    MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    MAP_EVERY EXISTS_TAC [`(:real^M)`; `d:(real^M->bool)->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_BOUND = prove
 (`!f:real^M->real^N g:real^M->real^P s.
        (!x. x IN s ==> norm(f x) <= norm(g x)) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
    [absolutely_integrable_on]) THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `(\x. lift(norm((g:real^M->real^P) x)))`;
    `s:real^M->bool`] ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND) THEN
  ASM_REWRITE_TAC[LIFT_DROP]);;

let ABSOLUTELY_INTEGRABLE_INF_1 = prove
 (`!fs s:real^N->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. lift(fs x i)) absolutely_integrable_on s)
        ==> (\x. lift(inf (IMAGE (fs x) k))) absolutely_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[INF_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN_1 THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let ABSOLUTELY_INTEGRABLE_SUP_1 = prove
 (`!fs s:real^N->bool k:A->bool.
        FINITE k /\ ~(k = {}) /\
        (!i. i IN k ==> (\x. lift(fs x i)) absolutely_integrable_on s)
        ==> (\x. lift(sup (IMAGE (fs x) k))) absolutely_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
  SIMP_TAC[SUP_INSERT_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  ASM_CASES_TAC `k:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[IN_SING; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let ABSOLUTELY_INTEGRABLE_CONTINUOUS = prove
 (`!f:real^M->real^N a b.
        f continuous_on interval[a,b]
        ==> f absolutely_integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  SUBGOAL_THEN `compact(IMAGE (f:real^M->real^N) (interval[a,b]))` MP_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; COMPACT_INTERVAL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^M. lift(B)` THEN
  ASM_SIMP_TAC[INTEGRABLE_CONST; LIFT_DROP; INTEGRABLE_CONTINUOUS]);;

let INTEGRABLE_MIN_CONST_1 = prove
 (`!f s t.
        &0 <= t /\ (!x. x IN s ==> &0 <= f x) /\
        (\x:real^N. lift(f x)) integrable_on s
        ==> (\x. lift(min (f x) t)) integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND THEN
  EXISTS_TAC `\x:real^N. lift(f x)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    MP_TAC(ISPECL
     [`\x:real^N. if x IN s then f x else &0`;
      `(\x. t):real^N->real`;
      `interval[a:real^N,b]`] ABSOLUTELY_INTEGRABLE_MIN_1) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [SIMP_TAC[ABSOLUTELY_INTEGRABLE_CONTINUOUS; CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
      REWRITE_TAC[COND_RAND; LIFT_DROP; LIFT_NUM] THEN
      REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; LIFT_DROP; GSYM drop];
      DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> f(x)$i <= g(x)$i) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\x. (g:real^M->real^N)(x) - (g(x) - f(x))) absolutely_integrable_on s`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    REWRITE_TAC[VECTOR_ARITH `x - (x - y):real^N = y`; ETA_AX]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> f(x)$i <= g(x)$i) /\
        f absolutely_integrable_on s /\ g integrable_on s
        ==> g absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `(\x. (f:real^M->real^N)(x) + (g(x) - f(x))) absolutely_integrable_on s`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ADD THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; VECTOR_SUB_COMPONENT] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    REWRITE_TAC[VECTOR_ARITH `y + (x - y):real^N = x`; ETA_AX]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_DROP_UBOUND = prove
 (`!f:real^M->real^1 g:real^M->real^1 s.
        (!x. x IN s ==> drop(f(x)) <= drop(g(x))) /\
        f integrable_on s /\ g absolutely_integrable_on s
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
    ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND THEN
  EXISTS_TAC `g:real^M->real^1` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_REWRITE_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_DROP_LBOUND = prove
 (`!f:real^M->real^1 g:real^M->real^1 s.
        (!x. x IN s ==> drop(f(x)) <= drop(g(x))) /\
        f absolutely_integrable_on s /\ g integrable_on s
        ==> g absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
    ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND THEN
  EXISTS_TAC `f:real^M->real^1` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_REWRITE_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

(* ------------------------------------------------------------------------- *)
(* Relating vector integrals to integrals of components.                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPONENTWISE = prove
 (`!f:real^M->real^N s y.
        (f has_integral y) s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> ((\x. lift((f x)$i)) has_integral (lift(y$i))) s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o ISPEC `\u:real^N. lift(u$i)` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[LINEAR_LIFT_COMPONENT];
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o BINDER_CONV)
     [GSYM BASIS_EXPANSION] THEN
    MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o ISPEC `\v. drop(v) % (basis i:real^N)` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    SIMP_TAC[o_DEF; LIFT_DROP; LINEAR_VMUL_DROP; LINEAR_ID]]);;

let INTEGRABLE_COMPONENTWISE = prove
 (`!f:real^M->real^N s.
        f integrable_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift((f x)$i)) integrable_on s`,
   REPEAT GEN_TAC THEN REWRITE_TAC[integrable_on] THEN
   GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [HAS_INTEGRAL_COMPONENTWISE] THEN
   REWRITE_TAC[GSYM LAMBDA_SKOLEM; GSYM EXISTS_LIFT]);;

let LIFT_INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N.
        f integrable_on s
        ==> lift((integral s f)$k) = integral s (\x. lift((f x)$k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:N) /\ !z:real^N. z$k = z$j`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL_COMPONENTWISE] THEN
  ASM_SIMP_TAC[]);;

let INTEGRAL_COMPONENT = prove
 (`!f:real^M->real^N.
        f integrable_on s
        ==> (integral s f)$k = drop(integral s (\x. lift((f x)$k)))`,
  SIMP_TAC[GSYM LIFT_INTEGRAL_COMPONENT; LIFT_DROP]);;

let ABSOLUTELY_INTEGRABLE_COMPONENTWISE = prove
 (`!f:real^M->real^N s.
     f absolutely_integrable_on s <=>
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> (\x. lift(f x$i)) absolutely_integrable_on s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[absolutely_integrable_on] THEN
  MATCH_MP_TAC(MESON[]
   `(p <=> !i. a i ==> P i) /\
    (p /\ (!i. a i ==> P i) ==> (q <=> (!i. a i ==> Q i)))
    ==> (p /\ q <=> (!i. a i ==> P i /\ Q i))`) THEN
  CONJ_TAC THENL [REWRITE_TAC[GSYM INTEGRABLE_COMPONENTWISE]; ALL_TAC] THEN
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [SUBGOAL_THEN
     `(\x. lift((f:real^M->real^N) x$i)) absolutely_integrable_on s`
    MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_integrable_on]] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x))` THEN
    ASM_SIMP_TAC[ABS_DROP; LIFT_DROP; COMPONENT_LE_NORM];
    SUBGOAL_THEN
     `(f:real^M->real^N) absolutely_integrable_on s`
    MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_integrable_on]] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
    EXISTS_TAC
     `\x. vsum (1..dimindex(:N))
               (\i. lift(norm(lift((f:real^M->real^N)(x)$i))))` THEN
    ASM_SIMP_TAC[INTEGRABLE_VSUM; IN_NUMSEG; FINITE_NUMSEG] THEN
    SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; LIFT_DROP] THEN
    REWRITE_TAC[NORM_LIFT; NORM_LE_L1]]);;

(* ------------------------------------------------------------------------- *)
(* Dominated convergence.                                                    *)
(* ------------------------------------------------------------------------- *)

let DOMINATED_CONVERGENCE = prove
 (`!f:num->real^M->real^N g h s.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\
        (!k x. x IN s ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`,
  SUBGOAL_THEN
    `!f:num->real^M->real^1 g h s.
        (!k. (f k) integrable_on s) /\ h integrable_on s /\
        (!k x. x IN s ==> norm(f k x) <= drop(h x)) /\
        (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
        ==> g integrable_on s /\
            ((\k. integral s (f k)) --> integral s g) sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!j. 1 <= j /\ j <= dimindex(:N)
          ==> (\x. lift((g x)$j)) integrable_on s /\
              ((\k. integral s (\x. lift (((f:num->real^M->real^N) k x)$j)))
               --> integral s (\x. lift ((g x:real^N)$j))) sequentially`
    STRIP_ASSUME_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
          [INTEGRABLE_COMPONENTWISE]) THEN
        ASM_SIMP_TAC[];
        MAP_EVERY X_GEN_TAC [`i:num`; `x:real^M`] THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm((f:num->real^M->real^N) i x)` THEN
        ASM_SIMP_TAC[NORM_LIFT; COMPONENT_LE_NORM];
        X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [LIM_COMPONENTWISE_LIFT] THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [INTEGRABLE_COMPONENTWISE] THEN ASM_SIMP_TAC[];
        DISCH_TAC THEN  ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
        ASM_SIMP_TAC[LIFT_INTEGRAL_COMPONENT]]]] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `m:num`
   (ISPECL [`\k:num x:real^M. lift(inf {drop(f j x) | j IN m..(m+k)})`;
            `\x:real^M. lift(inf {drop(f j x) | m:num <= j})`;
            `s:real^M->bool`]
           MONOTONE_CONVERGENCE_DECREASING))) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INF_1 THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
      EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];

      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC LOWER_BOUND_FINITE_SET_REAL THEN
      REWRITE_TAC[FINITE_NUMSEG];

      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[dist; ABS_DROP; LIFT_DROP; DROP_SUB] THEN
      MP_TAC(SPEC `{drop((f:num->real^M->real^1) j x) | m <= j}` INF) THEN
      ABBREV_TAC `i = inf {drop((f:num->real^M->real^1) j x) | m <= j}` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
        EXISTS_TAC `--drop(h(x:real^M))` THEN X_GEN_TAC `j:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `x:real^M`]) THEN
        ASM_REWRITE_TAC[ABS_DROP] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i + e:real`)) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i + e <= i)`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN STRIP_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `y < i + e ==> i <= ix /\ ix <= y ==> abs(ix - i) < e`)) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "i" THEN MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
        REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
          REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      W(MP_TAC o C SPEC INF o rand o lhand o snd) THEN ANTS_TAC THENL
       [REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `i:real` THEN GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[bounded] THEN
      EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INF_1 THEN
        REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
        EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_ABS_INF_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD; GSYM ABS_DROP]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `m:num`
   (ISPECL [`\k:num x:real^M. lift(sup {drop(f j x) | j IN m..(m+k)})`;
            `\x:real^M. lift(sup {drop(f j x) | m:num <= j})`;
            `s:real^M->bool`]
           MONOTONE_CONVERGENCE_INCREASING))) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [X_GEN_TAC `m:num` THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUP_1 THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
      EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];

      REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC UPPER_BOUND_FINITE_SET_REAL THEN
      REWRITE_TAC[FINITE_NUMSEG];

      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      REWRITE_TAC[dist; ABS_DROP; LIFT_DROP; DROP_SUB] THEN
      MP_TAC(SPEC `{drop((f:num->real^M->real^1) j x) | m <= j}` SUP) THEN
      ABBREV_TAC `i = sup {drop((f:num->real^M->real^1) j x) | m <= j}` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[IN_ELIM_THM; EXTENSION; NOT_IN_EMPTY] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
        EXISTS_TAC `drop(h(x:real^M))` THEN X_GEN_TAC `j:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `x:real^M`]) THEN
        ASM_REWRITE_TAC[ABS_DROP] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `i - e:real`)) THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(i <= i - e)`] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN STRIP_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `i - e < y ==> ix <= i /\ y <= ix ==> abs(ix - i) < e`)) THEN
      CONJ_TAC THENL
       [EXPAND_TAC "i" THEN MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
        REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
         [MATCH_MP_TAC IMAGE_SUBSET THEN
          REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
          REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
        ALL_TAC] THEN
      W(MP_TAC o C SPEC SUP o rand o rand o snd) THEN ANTS_TAC THENL
       [REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
        REWRITE_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        EXISTS_TAC `i:real` THEN GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
        DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_ARITH_TAC;

      REWRITE_TAC[bounded] THEN
      EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUP_1 THEN
        REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; LE_ADD] THEN
        ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
        EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_ABS_SUP_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
      ASM_SIMP_TAC[NUMSEG_EMPTY; NOT_LT; LE_ADD; GSYM ABS_DROP]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`\k:num x:real^M. lift(inf {drop(f j x) | k <= j})`;
    `g:real^M->real^1`;
    `s:real^M->bool`]
           MONOTONE_CONVERGENCE_INCREASING) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INF_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_LE] THEN
      CONJ_TAC THENL [MESON_TAC[LT_REFL]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `--drop(h(x:real^M))` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> --a <= x`) THEN
      ASM_SIMP_TAC[GSYM ABS_DROP];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
                 MP_TAC(SPEC `e / &2` th)) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
      REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INF_ASCLOSE THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_TRANS; REAL_LT_IMP_LE]] THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      MESON_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
    X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_ABS_INF_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM ABS_DROP; IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
    MESON_TAC[LE_REFL];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "A"))] THEN
  MP_TAC(ISPECL
   [`\k:num x:real^M. lift(sup {drop(f j x) | k <= j})`;
    `g:real^M->real^1`;
    `s:real^M->bool`]
           MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; SET_RULE `{x | x IN s} = s`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; NOT_LE] THEN
      CONJ_TAC THENL [MESON_TAC[LT_REFL]; ALL_TAC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `drop(h(x:real^M))` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
      ASM_SIMP_TAC[GSYM ABS_DROP];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN DISCH_TAC THEN
                 MP_TAC(SPEC `e / &2` th)) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN
      REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
      STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SUP_ASCLOSE THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[LE_TRANS; REAL_LT_IMP_LE]] THEN
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      MESON_TAC[LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    EXISTS_TAC `drop(integral s (h:real^M->real^1))` THEN
    X_GEN_TAC `p:num` THEN MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[ABS_DROP; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_ABS_SUP_LE THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM ABS_DROP; IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
    MESON_TAC[LE_REFL];
    DISCH_THEN(LABEL_TAC "B")] THEN
  ASM_REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "A" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "N1")) THEN
  REMOVE_THEN "B" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "N2")) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REMOVE_THEN "N1" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `N1 + N2 <= n ==> N1:num <= n`]; ALL_TAC] THEN
  REMOVE_THEN "N2" (MP_TAC o SPEC `n:num`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `N1 + N2 <= n ==> N2:num <= n`]; ALL_TAC] THEN
  REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i0 <= i /\ i <= i1
    ==> abs(i1 - g) < e ==> abs(i0 - g) < e ==> abs(i - g) < e`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN
  ASM_REWRITE_TAC[LIFT_DROP] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THENL
   [W(MP_TAC o C SPEC INF o rand o lhand o snd) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
      EXISTS_TAC `--drop(h(x:real^M))` THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> --a <= x`) THEN
      REWRITE_TAC[GSYM ABS_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN REWRITE_TAC[LE_REFL]];
    W(MP_TAC o C SPEC SUP o rand o rand o snd) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; NOT_FORALL_THM] THEN
      CONJ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
      EXISTS_TAC `drop(h(x:real^M))` THEN GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
      REWRITE_TAC[GSYM ABS_DROP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN REWRITE_TAC[LE_REFL]]]);;

let DOMINATED_CONVERGENCE_INTEGRABLE = prove
 (`!f:num->real^M->real^N g h s.
         (!k. f k absolutely_integrable_on s) /\
         h integrable_on s /\
         (!k x. x IN s ==> norm(g x) <= drop(h x)) /\
         (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
         ==> g integrable_on s`,
  let lemma = prove
   (`!f:num->real^N->real^1 g h s.
          (!k. f k absolutely_integrable_on s) /\
          h integrable_on s /\
          (!x. x IN s ==> norm(g x) <= drop(h x)) /\
          (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
          ==> g integrable_on s`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^1) absolutely_integrable_on s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC[DIMINDEX_1; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; IMP_IMP] THEN
      ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n:num x:real^N.
         lift(min (max (--(drop(h x))) (drop(f n x))) (drop(h x)))`;
      `g:real^N->real^1`;
      `h:real^N->real^1`;
      `s:real^N->bool`] DOMINATED_CONVERGENCE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN_1 THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
      ASM_SIMP_TAC[LIFT_NEG; LIFT_DROP; ETA_AX; ABSOLUTELY_INTEGRABLE_NEG];
      MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP; ABS_DROP] THEN
      SUBGOAL_THEN `&0 <= drop((h:real^N->real^1) x)` MP_TAC THENL
       [ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE]; REAL_ARITH_TAC];
      X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      UNDISCH_TAC
       `!x. x IN s ==> ((\n. (f:num->real^N->real^1) n x) --> g x)
                          sequentially` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[tendsto] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `e:real` THEN ASM_CASES_TAC `&0 < e` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[dist; ABS_DROP; DROP_SUB; LIFT_DROP] THEN
      REAL_ARITH_TAC]) in
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ONCE_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_COMPONENTWISE;
                   INTEGRABLE_COMPONENTWISE] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC lemma THEN
  EXISTS_TAC `\i x. lift(((f:num->real^M->real^N) i x)$k)` THEN
  EXISTS_TAC `h:real^M->real^1` THEN ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPONENT_LE_NORM; NORM_LIFT; REAL_LE_TRANS];
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[LIM_COMPONENTWISE_LIFT]) THEN
    RULE_ASSUM_TAC BETA_RULE THEN ASM_SIMP_TAC[]]);;

let DOMINATED_CONVERGENCE_ABSOLUTELY_INTEGRABLE = prove
 (`!f:num->real^M->real^N g h s.
         (!k. f k absolutely_integrable_on s) /\
         h integrable_on s /\
         (!k x. x IN s ==> norm(g x) <= drop(h x)) /\
         (!x. x IN s ==> ((\k. f k x) --> g x) sequentially)
         ==> g absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_INTEGRABLE_BOUND THEN
  EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DOMINATED_CONVERGENCE_INTEGRABLE THEN
  EXISTS_TAC `f:num->real^M->real^N` THEN
  EXISTS_TAC `h:real^M->real^1` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A few more properties of negligible sets.                                 *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_ON_UNIV = prove
 (`!s. negligible s <=> (indicator s has_integral vec 0) (:real^N)`,
  GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[NEGLIGIBLE]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[negligible] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN `indicator s integrable_on interval[a:real^N,b]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real^N)` THEN ASM_MESON_TAC[SUBSET_UNIV; integrable_on];
    ASM_SIMP_TAC[GSYM INTEGRAL_EQ_HAS_INTEGRAL] THEN
    REWRITE_TAC[GSYM DROP_EQ; GSYM REAL_LE_ANTISYM] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
      MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE;
      REWRITE_TAC[DROP_VEC] THEN MATCH_MP_TAC INTEGRAL_DROP_POS] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; DROP_INDICATOR_POS_LE] THEN
    ASM_MESON_TAC[integrable_on]]);;

let NEGLIGIBLE_COUNTABLE_UNIONS = prove
 (`!s:num->real^N->bool.
        (!n. negligible(s n)) ==> negligible(UNIONS {s(n) | n IN (:num)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. indicator(UNIONS {(s:num->real^N->bool)(m) | m <= n})`;
             `indicator(UNIONS {(s:num->real^N->bool)(m) | m IN (:num)})`;
                 `(:real^N)`] MONOTONE_CONVERGENCE_INCREASING) THEN
  SUBGOAL_THEN
   `!n. negligible(UNIONS {(s:num->real^N->bool)(m) | m <= n})`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE; FORALL_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. (indicator (UNIONS {s m | m <= n})) integrable_on (:real^N)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NEGLIGIBLE_ON_UNIV; integrable_on]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n:num. integral (:real^N) (indicator (UNIONS {s m | m <= n})) = vec 0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NEGLIGIBLE_ON_UNIV; INTEGRAL_UNIQUE]; ALL_TAC] THEN
  ASM_SIMP_TAC[NEGLIGIBLE_ON_UNIV; LIM_CONST_EQ;
               TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[INTEGRAL_EQ_HAS_INTEGRAL]] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:num`; `x:real^N`] THEN DISCH_TAC THEN
    REWRITE_TAC[indicator] THEN
    SUBGOAL_THEN
     `x IN UNIONS {(s:num->real^N->bool) m | m <= k}
      ==> x IN UNIONS {s m | m <= SUC k}`
    MP_TAC THENL
     [SPEC_TAC(`x:real^N`,`x:real^N`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      REWRITE_TAC[DROP_VEC; REAL_LE_REFL; REAL_POS]];
    X_GEN_TAC `x:real^N` THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; indicator] THEN
    ASM_CASES_TAC `x IN UNIONS {(s:num->real^N->bool) m | m IN (:num)}` THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [UNIONS_GSPEC]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
        [UNIONS_GSPEC]) THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]];
    REWRITE_TAC[SET_RULE `{c | x | x IN UNIV} = {c}`;
                BOUNDED_INSERT; BOUNDED_EMPTY]]);;

let HAS_INTEGRAL_NEGLIGIBLE_EQ = prove
 (`!f:real^M->real^N s.
        (!x i. x IN s /\ 1 <= i /\ i <= dimindex(:N) ==> &0 <= f(x)$i)
        ==> ((f has_integral vec 0) s <=>
             negligible {x | x IN s /\ ~(f x = vec 0)})`,
  let lemma = prove
   (`!f:real^N->real^1 s.
          (!x. x IN s ==> &0 <= drop(f x)) /\ (f has_integral vec 0) s
          ==> negligible {x | x IN s /\ ~(f x = vec 0)}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
     `UNIONS {{x | x IN s /\ norm((f:real^N->real^1) x) >= &1 / (&n + &1)} |
              n IN (:num)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[NEGLIGIBLE_ON_UNIV; indicator] THEN
      MATCH_MP_TAC HAS_INTEGRAL_STRADDLE_NULL THEN
      EXISTS_TAC `(\x. if x IN s then (&n + &1) % f(x) else vec 0):
                  real^N->real^1` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIV; IN_ELIM_THM; real_ge] THEN
        X_GEN_TAC `x:real^N` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[DROP_VEC; DROP_CMUL; REAL_POS] THENL
         [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
          ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a <= abs x ==> a <= x`) THEN
          ASM_SIMP_TAC[GSYM ABS_DROP];
          COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; REAL_POS; DROP_CMUL] THEN
          ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL; REAL_LE_ADD]];
        REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN
        SUBST1_TAC(VECTOR_ARITH `vec 0:real^1 = (&n + &1) % vec 0`) THEN
        MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[GSYM NORM_POS_LT] THEN ONCE_REWRITE_TAC[REAL_ARCH_INV] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `n:num`
        STRIP_ASSUME_TAC)) THEN
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
      EXISTS_TAC `n - 1` THEN ASM_SIMP_TAC[IN_UNIV; IN_ELIM_THM; real_ge] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_ADD; SUB_ADD; LE_1] THEN
      ASM_SIMP_TAC[real_div; REAL_MUL_LID; REAL_LT_IMP_LE]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN
    EXISTS_TAC `{x | x IN s /\ ~((f:real^M->real^N) x = vec 0)}` THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[]] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `UNIONS {{x | x IN s /\ ~(((f:real^M->real^N) x)$k = &0)} |
                      k IN 1..dimindex(:N)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN MATCH_MP_TAC lemma THEN
    ASM_SIMP_TAC[LIFT_DROP] THEN
    FIRST_X_ASSUM(MP_TAC o ISPEC `\y:real^N. lift(y$k)` o
      MATCH_MP(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_LINEAR)) THEN
    REWRITE_TAC[o_DEF; VEC_COMPONENT; LIFT_NUM] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[linear] THEN
    SIMP_TAC[LIFT_ADD; VECTOR_ADD_COMPONENT; LIFT_CMUL; VECTOR_MUL_COMPONENT];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; CART_EQ; IN_NUMSEG] THEN
    REWRITE_TAC[VEC_COMPONENT; IN_ELIM_THM] THEN MESON_TAC[]]);;

let NEGLIGIBLE_COUNTABLE = prove
 (`!s:real^N->bool. COUNTABLE s ==> negligible s`,
  let lemma = prove
   (`IMAGE f s = UNIONS {{f x} | x IN s}`,
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIONS; IN_SING; IN_ELIM_THM] THEN
    MESON_TAC[IN_SING]) in
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->real^N` SUBST1_TAC o
    MATCH_MP COUNTABLE_AS_IMAGE) THEN
  ONCE_REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  REWRITE_TAC[NEGLIGIBLE_SING]);;

(* ------------------------------------------------------------------------- *)
(* Beppo Levi theorem.                                                       *)
(* ------------------------------------------------------------------------- *)

let BEPPO_LEVI_INCREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`,
  SUBGOAL_THEN
   `!f:num->real^N->real^1 s.
        (!k x. x IN s ==> &0 <= drop(f k x)) /\
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL
     [`\n x:real^N. f(n:num) x - f 0 x:real^1`; `s:real^N->bool`]) THEN
    REWRITE_TAC[] THEN ANTS_TAC THEN REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      MP_TAC(ISPEC
        `\m n:num. drop (f m (x:real^N)) <= drop (f n x)`
        TRANSITIVE_STEPWISE_LE) THEN
      REWRITE_TAC[REAL_LE_TRANS; REAL_LE_REFL] THEN ASM_MESON_TAC[LE_0];
      GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX];
      REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_SUB; REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `x - a <= y - a <=> x <= y`];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      ASM_SIMP_TAC[INTEGRAL_SUB; ETA_AX; bounded] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real`
        (fun th -> EXISTS_TAC `B + norm(integral s (f 0:real^N->real^1))` THEN
                   X_GEN_TAC `k:num` THEN MP_TAC(SPEC `k:num` th))) THEN
      NORM_ARITH_TAC;
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(\x. g x + f 0 x):real^N->real^1` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[LIM_SEQUENTIALLY; dist] THEN
      REWRITE_TAC[VECTOR_ARITH `a - b - c:real^1 = a - (c + b)`]]] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `g = \i n:num x:real^N. lift(min (drop(f n x) / (&i + &1)) (&1))` THEN
  SUBGOAL_THEN
   `!i n. ((g:num->num->real^N->real^1) i n) integrable_on s`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN
    MATCH_MP_TAC INTEGRABLE_MIN_CONST_1 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LE_ADD] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    ASM_SIMP_TAC[LIFT_CMUL; LIFT_DROP; INTEGRABLE_CMUL; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:num k:num x:real^N. x IN s ==> drop(g i k x) <= drop(g i (SUC k) x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> min x a <= min y a`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &n + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num k:num x:real^N. x IN s ==> norm(g i k x:real^1) <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[LIFT_DROP; NORM_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(min x (&1)) <= &1`) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV; REAL_LE_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:num x:real^N. x IN s ==> ?h:real^1. ((\n. g i n x) --> h) sequentially`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\n. drop(g (i:num) (n:num) (x:real^N))`; `&1`]
     CONVERGENT_BOUNDED_MONOTONE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[GSYM ABS_DROP] THEN DISJ1_TAC THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `l:real` (fun th ->
        EXISTS_TAC `lift l` THEN MP_TAC th)) THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop; LIFT_DROP]];
    GEN_REWRITE_TAC (LAND_CONV o REDEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `h:num->real^N->real^1` THEN STRIP_TAC THEN
  MP_TAC(GEN `i:num `(ISPECL
   [`g(i:num):num->real^N->real^1`; `h(i:num):real^N->real^1`;
    `s:real^N->bool`] MONOTONE_CONVERGENCE_INCREASING)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[bounded] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:real` THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC(REAL_ARITH
     `norm a = drop a /\ x <= drop a ==> x <= norm a`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_REAL; GSYM drop; REAL_ABS_REFL] THEN
      MATCH_MP_TAC INTEGRAL_DROP_POS THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= y ==> abs(min x (&1)) <= y`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_DIV] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      REWRITE_TAC[REAL_ARITH `a <= a * (x + &1) <=> &0 <= a * x`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS]];
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  ABBREV_TAC
   `Z =
    {x:real^N | x IN s /\ ~(?l:real^1. ((\k. f k x) --> l) sequentially)}` THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN EXISTS_TAC `Z:real^N->bool` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  CONJ_TAC THENL
   [ALL_TAC; EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM] THEN SET_TAC[]] THEN
  MP_TAC(ISPECL
   [`h:num->real^N->real^1`;
    `(\x. if x IN Z then vec 1 else vec 0):real^N->real^1`;
    `s:real^N->bool`]
        MONOTONE_CONVERGENCE_DECREASING) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!i x:real^N. x IN s ==> drop(h (SUC i) x) <= drop(h i x)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `x:real^N`] THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LE) THEN
    EXISTS_TAC `\n. (g:num->num->real^N->real^1) (SUC i) n x` THEN
    EXISTS_TAC `\n. (g:num->num->real^N->real^1) i n x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> min x a <= min y a`) THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!i. norm(integral s ((h:num->real^N->real^1) i)) <= B / (&i + &1)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\k. integral s ((g:num->num->real^N->real^1) i k)` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `drop(integral s (\x. inv(&i + &1) % (f:num->real^N->real^1) n x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      ASM_SIMP_TAC[INTEGRABLE_CMUL; ETA_AX] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXPAND_TAC "g" THEN
      REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP; DROP_CMUL] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= y ==> abs(min x (&1)) <= y`) THEN
      ASM_SIMP_TAC[REAL_LE_ADD; REAL_POS; REAL_LE_DIV] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_CMUL; ETA_AX; DROP_CMUL] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_DIV2_EQ;
                   REAL_ARITH `&0 < &n + &1`] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
      ASM_REWRITE_TAC[GSYM ABS_DROP]];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `B:real` THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `B / (&i + &1)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      REWRITE_TAC[REAL_ARITH `B <= B * (i + &1) <=> &0 <= i * B`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN Z` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC LIM_EVENTUALLY THEN
      UNDISCH_TAC `(x:real^N) IN Z` THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(GEN `B:real` (ISPECL
        [`\n. drop(f (n:num) (x:real^N))`; `B:real`]
        CONVERGENT_BOUNDED_MONOTONE)) THEN
      REWRITE_TAC[LEFT_FORALL_IMP_THM; LEFT_EXISTS_AND_THM] THEN
      MATCH_MP_TAC(TAUT
       `q /\ ~r /\ (q ==> ~p ==> s)
        ==> (p /\ (q \/ q') ==> r) ==> s`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
        ASM_SIMP_TAC[REAL_LE_REFL; REAL_LE_TRANS] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
        ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
        DISCH_THEN(MP_TAC o SPEC `lift l`) THEN
        REWRITE_TAC[LIM_SEQUENTIALLY] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[DIST_REAL; GSYM drop; DROP_SUB; LIFT_DROP];
        ALL_TAC] THEN
      DISCH_TAC THEN REWRITE_TAC[NOT_FORALL_THM; EVENTUALLY_SEQUENTIALLY] THEN
      REWRITE_TAC[NOT_EXISTS_THM; NOT_FORALL_THM; REAL_NOT_LE] THEN
      DISCH_TAC THEN
      EXISTS_TAC `0` THEN  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `(\n. (g:num->num->real^N->real^1) i n x)` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC LIM_EVENTUALLY THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `&i + &1`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
      REWRITE_TAC[REAL_ARITH `min a b = b <=> b <= a`] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &i + &1`; REAL_MUL_LID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `a < abs N ==> &0 <= N /\ N <= n ==> a <= n`)) THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `~((x:real^N) IN Z)` THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `l:real^1` THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV] THEN
      DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPEC `e / C:real` REAL_ARCH_INV) THEN
      ASM_SIMP_TAC[REAL_LT_DIV] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `N:num` THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN STRIP_TAC THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N) * C` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C / (&i + &1)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC] THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
      EXISTS_TAC `\n. (g:num->num->real^N->real^1) i n x` THEN
      ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
      EXPAND_TAC "g" THEN REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ x <= a ==> abs(min x (&1)) <= a`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_ADD; REAL_POS] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &i + &1`] THEN
      MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
      ASM_REWRITE_TAC[GSYM NORM_LIFT; LIFT_DROP]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(MESON[LIM_UNIQUE; TRIVIAL_LIMIT_SEQUENTIALLY]
     `(f --> vec 0) sequentially /\ (i = vec 0 ==> p)
      ==> (f --> i) sequentially ==> p`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LIM_NULL_COMPARISON THEN
      EXISTS_TAC `\i. B / (&i + &1)` THEN
      ASM_SIMP_TAC[ALWAYS_EVENTUALLY] THEN
      REWRITE_TAC[real_div; LIFT_CMUL] THEN
      SUBST1_TAC(VECTOR_ARITH `vec 0:real^1 = B % vec 0`) THEN
      MATCH_MP_TAC LIM_CMUL THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0] THEN
      X_GEN_TAC `e:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_LIFT; GSYM drop; LIFT_DROP; REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[INTEGRAL_EQ_HAS_INTEGRAL] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) HAS_INTEGRAL_NEGLIGIBLE_EQ o
        lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[DROP_VEC; REAL_POS];
        DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; VEC_EQ; ARITH_EQ] THEN
        EXPAND_TAC "Z" THEN SIMP_TAC[IN_ELIM_THM]]]]);;

let BEPPO_LEVI_DECREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  !x. x IN (s DIFF k) ==> ((\k. f k x) --> g x) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n x. --((f:num->real^N->real^1) n x)`; `s:real^N->bool`]
        BEPPO_LEVI_INCREASING) THEN
  ASM_SIMP_TAC[INTEGRABLE_NEG; DROP_NEG; ETA_AX; REAL_LE_NEG2] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[bounded] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[INTEGRAL_NEG; ETA_AX; NORM_NEG];
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x. --((g:real^N->real^1) x)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV)
      [GSYM VECTOR_NEG_NEG] THEN
    ASM_SIMP_TAC[LIM_NEG_EQ]]);;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f k x) <= drop(f (SUC k) x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BEPPO_LEVI_INCREASING) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(g:real^N->real^1) integrable_on (s DIFF k) /\
    ((\i. integral (s DIFF k) (f i)) --> integral (s DIFF k) g) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC MONOTONE_CONVERGENCE_INCREASING THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl));
    ALL_TAC] THEN
  (SUBGOAL_THEN
    `!f:real^N->real^1. integral (s DIFF k) f = integral s f /\
                        (f integrable_on (s DIFF k) <=> f integrable_on s)`
    (fun th -> SIMP_TAC[th; IN_DIFF]) THEN
   GEN_TAC THEN CONJ_TAC THEN TRY EQ_TAC THEN
   (MATCH_MP_TAC INTEGRABLE_SPIKE_SET ORELSE
    MATCH_MP_TAC INTEGRAL_SPIKE_SET) THEN
   FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
     SET_TAC[]));;

let BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING = prove
 (`!f:num->real^N->real^1 s.
        (!k. (f k) integrable_on s) /\
        (!k x. x IN s ==> drop(f (SUC k) x) <= drop(f k x)) /\
        bounded {integral s (f k) | k IN (:num)}
        ==> ?g k. negligible k /\
                  (!x. x IN (s DIFF k)
                       ==> ((\k. f k x) --> g x) sequentially) /\
                  g integrable_on s /\
                  ((\k. integral s (f k)) --> integral s g) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BEPPO_LEVI_DECREASING) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^N->real^1` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(g:real^N->real^1) integrable_on (s DIFF k) /\
    ((\i. integral (s DIFF k) (f i)) --> integral (s DIFF k) g) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC MONOTONE_CONVERGENCE_DECREASING THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl));
    ALL_TAC] THEN
  (SUBGOAL_THEN
    `!f:real^N->real^1. integral (s DIFF k) f = integral s f /\
                        (f integrable_on (s DIFF k) <=> f integrable_on s)`
    (fun th -> SIMP_TAC[th; IN_DIFF]) THEN
   GEN_TAC THEN CONJ_TAC THEN TRY EQ_TAC THEN
   (MATCH_MP_TAC INTEGRABLE_SPIKE_SET ORELSE
    MATCH_MP_TAC INTEGRAL_SPIKE_SET) THEN
   FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
     SET_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* Fundamental theorem of calculus, starting with strong forms.              *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG = prove
 (`!f:real^1->real^N f' s a b.
        COUNTABLE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  EXISTS_TAC `(\x. if x IN s then vec 0 else f' x):real^1->real^N` THEN
  EXISTS_TAC `s:real^1->bool` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_COUNTABLE; IN_DIFF] THEN
  SUBGOAL_THEN
   `?f t. s = IMAGE (f:num->real^1) t /\
          (!m n. m IN t /\ n IN t /\ f m = f n ==> m = n)`
  MP_TAC THENL
   [ASM_CASES_TAC `FINITE(s:real^1->bool)` THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMSEG]) THEN
      ASM_MESON_TAC[];
      MP_TAC(ISPEC `s:real^1->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN MESON_TAC[IN_UNIV]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; INJECTIVE_ON_LEFT_INVERSE] THEN
    MAP_EVERY X_GEN_TAC [`r:num->real^1`; `t:num->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:real^1->num`)] THEN
  REWRITE_TAC[HAS_INTEGRAL_FACTOR_CONTENT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. ?d. &0 < d /\
            (x IN interval[a,b]
             ==> (x IN IMAGE (r:num->real^1) t
                  ==> !y. norm(y - x) < d /\ y IN interval[a,b]
                          ==> norm(f y - f x)
                              <= e / &2 pow (4 + n x) * norm(b - a)) /\
                 (~(x IN IMAGE r t)
                  ==> !y. norm(y - x) < d /\ y IN interval[a,b]
                          ==> norm(f y - f x - drop(y - x) % f' x:real^N)
                                <= e / &2 * norm(y - x)))`
  MP_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    ASM_CASES_TAC `(x:real^1) IN interval[a,b]` THENL
     [ALL_TAC; EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]] THEN
    ASM_CASES_TAC `x IN IMAGE (r:num->real^1) t` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
       `a <= b ==> a = b \/ a < b`)) THEN
      REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
       [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
        UNDISCH_TAC `(x:real^1) IN interval[a,b]` THEN
        ASM_SIMP_TAC[INTERVAL_SING; IN_SING; VECTOR_SUB_REFL; NORM_0] THEN
        REAL_ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_on]) THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[dist] THEN
        DISCH_THEN(MP_TAC o SPEC
         `e / &2 pow (4 + n(x:real^1)) * norm(b - a:real^1)`) THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; NORM_POS_LT; VECTOR_SUB_EQ;
                     REAL_LT_POW2; GSYM DROP_EQ; REAL_LT_IMP_NE] THEN
        MESON_TAC[REAL_LT_IMP_LE]];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[IN_DIFF; has_vector_derivative;
                      HAS_DERIVATIVE_WITHIN_ALT] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN MESON_TAC[]];
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM; IMP_IMP;
                TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
    X_GEN_TAC `d:real^1->real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "E") (LABEL_TAC "U"))] THEN
  EXISTS_TAC `\x. ball(x:real^1,d(x))` THEN
  ASM_SIMP_TAC[GAUGE_BALL_DEPENDENT] THEN
  X_GEN_TAC `p:(real^1#(real^1->bool))->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[CONTENT_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB; LAMBDA_PAIR_THM] THEN
  SUBGOAL_THEN
   `p:(real^1#(real^1->bool))->bool =
    {(x,k) | (x,k) IN p /\ x IN IMAGE r (t:num->bool)} UNION
    {(x,k) | (x,k) IN p /\ ~(x IN IMAGE r (t:num->bool))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_UNION] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_UNION o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`] THEN
    SIMP_TAC[FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN CONJ_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:(real^1#(real^1->bool))->bool` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(!P. FINITE {(x:real^1,k:real^1->bool) | (x,k) IN p /\ P x k}) /\
    (!P x. FINITE {(x:real^1,k:real^1->bool) |k| (x,k) IN p /\ P x k})`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `p:real^1#(real^1->bool)->bool` THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_GSPEC];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:real^N) <= e / &2 * a /\ norm(y) <= e / &2 * a
    ==> norm(x + y) <= e * a`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `norm(vsum {(x,k) | (x,k) IN p /\ x IN IMAGE (r:num->real^1) t /\
                         ~(content k = &0)}
                (\(x,k). --(f(interval_upperbound k) -
                            (f:real^1->real^N)(interval_lowerbound k))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC VSUM_EQ_SUPERSET THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[VECTOR_ARITH `a % vec 0 - x:real^N = --x`] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      ASM_REWRITE_TAC[CONTENT_EQ_0_1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
      SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1;
               INTERVAL_EQ_EMPTY; REAL_NOT_LE; REAL_NOT_LT] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(VECTOR_ARITH
       `x:real^N = y ==> --(x - y) = vec 0`) THEN
      AP_TERM_TAC THEN ASM_REWRITE_TAC[GSYM DROP_EQ; GSYM REAL_LE_ANTISYM];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum {(x,k:real^1->bool) | (x,k) IN p /\ x IN IMAGE (r:num->real^1) t /\
                                ~(content k = &0)}
          ((\(x,k). e / &2 pow (3 + n x) * norm (b - a:real^1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN
      ASM_REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      MP_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
        (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      SIMP_TAC[CONTENT_EQ_0_1; REAL_NOT_LE; REAL_LT_IMP_LE; IN_INTERVAL_1;
               INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      REPEAT STRIP_TAC THEN
      REMOVE_THEN "E" (MP_TAC o SPEC `x:real^1`) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `interval[u:real^1,v]`]) THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      ASM_REWRITE_TAC[dist; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_SUB] THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      REPEAT(ANTS_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET; INTERVAL_NE_EMPTY_1;
                      REAL_LT_IMP_LE];
        ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`]]) THEN
      REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN NORM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`FST:real^1#(real^1->bool)->real^1`;
      `\(x:real^1,k:real^1->bool). e / &2 pow (3 + n x) * norm (b - a:real^1)`;
      `{(x,k:real^1->bool) | (x,k) IN p /\ x IN IMAGE (r:num->real^1) t /\
                                ~(content k = &0)}`;
      `IMAGE (r:num->real^1) t`
     ] SUM_GROUP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SIMP_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (r:num->real^1) t)
          (\x. sum {(x,k:real^1->bool) |k|
                    (x,k) IN p /\ ~(content k = &0)}
                   (\yk. e / &2 pow (3 + n x) * norm(b - a:real^1)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_EQ_SUPERSET THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST] THEN
    REWRITE_TAC[SUM_RMUL; NORM_1; DROP_SUB; REAL_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[real_abs; REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_SUB_LE; REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `p * e * inv(&2 pow 3) * n = e / &8 * (p * n)`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; SUM_LMUL; REAL_ARITH
     `e / &8 * x <= e * inv(&2) <=> e * x <= e * &4`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (r:num->real^1) t INTER
           IMAGE (FST:real^1#(real^1->bool)->real^1) p)
          (\x. &(CARD {(x,k:real^1->bool) | k |
                      (x,k) IN p /\ ~(content k = &0)}) *
               inv(&2 pow n x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_SUPERSET THEN
      REWRITE_TAC[INTER_SUBSET; IMP_CONJ; FORALL_IN_IMAGE] THEN
      SIMP_TAC[IN_INTER; FUN_IN_IMAGE] THEN
      REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
      DISJ1_TAC THEN AP_TERM_TAC THEN
      MATCH_MP_TAC(MESON[CARD_CLAUSES] `s = {} ==> CARD s = 0`) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (r:num->real^1) t INTER
           IMAGE (FST:real^1#(real^1->bool)->real^1) p)
          (\x. &2 / &2 pow (n x))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER] THEN
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS; REAL_OF_NUM_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `2 = 2 EXP 1`] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM DIMINDEX_1] THEN
      MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_COMMON_TAGS THEN
      ASM_MESON_TAC[tagged_division_of];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; SUM_LMUL; REAL_ARITH `&2 * x <= &4 <=> x <= &2`;
                REAL_INV_POW] THEN
    SUBGOAL_THEN
     `(\x:real^1. inv (&2) pow n x) = (\n. inv(&2) pow n) o n`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN
     `?m. IMAGE (n:real^1->num)
                (IMAGE (r:num->real^1) t INTER
                IMAGE (FST:real^1#(real^1->bool)->real^1) p) SUBSET 0..m`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_NUMSEG; LE_0] THEN
      MATCH_MP_TAC UPPER_BOUND_FINITE_SET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..m) (\n. inv(&2) pow n)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INTER; FINITE_NUMSEG] THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN ASM SET_TAC[];
      REWRITE_TAC[SUM_GP; LT; SUB_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[REAL_ARITH `(&1 - x) / (&1 / &2) <= &2 <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    MP_TAC(ISPECL [`\x:real^1. x`; `p:(real^1#(real^1->bool))->bool`;
                   `a:real^1`; `b:real^1`]
                  ADDITIVE_TAGGED_DIVISION_1) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
    ASM_SIMP_TAC[DROP_VSUM; DROP_SUB] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {(x:real^1,k:real^1->bool) |
           (x,k) IN p /\ ~(x IN IMAGE r (t:num->bool))}
          (\x. e / &2 * (drop o
            (\(x,k). interval_upperbound k - interval_lowerbound k)) x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
      SIMP_TAC[o_DEF] THEN
      REWRITE_TAC[NORM_ARITH `norm(a - (b - c):real^N) = norm(b - c - a)`] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      MP_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
       (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN DISCH_THEN(fun th ->
        ASSUME_TAC th THEN MP_TAC(MATCH_MP REAL_LE_TRANS th)) THEN
      SIMP_TAC[CONTENT_1; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      DISCH_TAC THEN REMOVE_THEN "U" (MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` ASSUME_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET; IN_INTERVAL_1]; ALL_TAC] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `interval[u:real^1,v]`]) THEN
      ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(fun th ->
        MP_TAC(ISPEC `u:real^1` th) THEN MP_TAC(ISPEC `v:real^1` th)) THEN
      ASM_REWRITE_TAC[dist; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_SUB] THEN DISCH_TAC THEN DISCH_TAC THEN
      REPEAT(ANTS_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET; INTERVAL_NE_EMPTY_1;
                      REAL_LT_IMP_LE];
        ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`]]) THEN
      REWRITE_TAC[NORM_1; DROP_SUB] THEN
      ASM_SIMP_TAC[REAL_ARITH `a <= b ==> abs(a - b) = b - a`;
                   REAL_ARITH `b <= a ==> abs(a - b) = a - b`] THEN
      REWRITE_TAC[REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC(NORM_ARITH
       `x - y:real^N = z ==> norm(x) <= c - b
                   ==> norm(y) <= b - a ==> norm(z) <= c - a`) THEN
      VECTOR_ARITH_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[FORALL_PAIR_THM]] THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?u v:real^1. k = interval[u,v] /\ x IN interval[u,v]`
      MP_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
       (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC)) THEN
      REWRITE_TAC[IN_INTERVAL_1; o_THM] THEN
      DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
      SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[DROP_SUB] THEN ASM_REAL_ARITH_TAC]]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG = prove
 (`!f:real^1->real^N f' s a b.
        COUNTABLE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF s
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG THEN
  EXISTS_TAC `(a:real^1) INSERT (b:real^1) INSERT s` THEN
  ASM_REWRITE_TAC[COUNTABLE_INSERT; IN_INTERVAL_1; IN_DIFF] THEN
  REWRITE_TAC[DE_MORGAN_THM; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; IN_DIFF; IN_INSERT] THEN
  ASM_REWRITE_TAC[REAL_LT_LE; DROP_EQ]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS = prove
 (`!f:real^1->real^N f' a b.
        drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG THEN
  EXISTS_TAC `{}:real^1->bool` THEN
  ASM_REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY] THEN
  MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
  REWRITE_TAC[differentiable_on] THEN
  ASM_MESON_TAC[has_vector_derivative; differentiable]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR = prove
 (`!f:real^1->real^N f' a b.
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b)
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `{}:real^1->bool` THEN
  ASM_REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY]);;

let ANTIDERIVATIVE_INTEGRAL_CONTINUOUS = prove
 (`!f:real^1->real^N a b.
     (f continuous_on interval[a,b])
     ==> ?g. !u v. u IN interval[a,b] /\ v IN interval[a,b] /\ drop u <= drop v
                   ==> (f has_integral (g(v) - g(u))) (interval[u,v])`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ANTIDERIVATIVE_CONTINUOUS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^N` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN
  STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `interval[a:real^1,b]` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* This doesn't directly involve integration, but that gives an easy proof.  *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL = prove
 (`!f:real^1->real^N a b k y.
        COUNTABLE k /\ f continuous_on interval[a,b] /\ f a = y /\
        (!x. x IN (interval[a,b] DIFF k)
             ==> (f has_derivative (\h. vec 0)) (at x within interval[a,b]))
        ==> !x. x IN interval[a,b] ==> f x = y`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(ISPEC `(\x. vec 0):real^1->real^N` HAS_INTEGRAL_UNIQUE) THEN
  EXISTS_TAC `interval[a:real^1,x]` THEN
  REWRITE_TAC[HAS_INTEGRAL_0] THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `k:real^1->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,b]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1])) THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1`) THEN ANTS_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN
      SIMP_TAC[IN_DIFF; IN_INTERVAL_1] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      HAS_DERIVATIVE_WITHIN_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `interval(a:real^1,b)`) THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
    REWRITE_TAC[has_vector_derivative; VECTOR_MUL_RZERO] THEN
    MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_OPEN THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SIMP_TAC[OPEN_INTERVAL; IN_INTERVAL_1; IN_DIFF] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Generalize a bit to any convex set.                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX = prove
 (`!f:real^M->real^N s k c y.
      convex s /\ COUNTABLE k /\ f continuous_on s /\ c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_derivative (\h. vec 0)) (at x within s))
      ==> !x. x IN s ==> f x = y`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `z:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^M = y` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`(f:real^M->real^N) o (\t. (&1 - drop t) % x + drop t % y)`;
                 `vec 0:real^1`; `vec 1:real^1`;
                 `{t | ((&1 - drop t) % (x:real^M) + drop t % y) IN k}`;
                 `(f:real^M->real^N) x`]
                HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `vec 1:real^1`) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; REAL_POS; REAL_LE_REFL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_SUB_0; DROP_EQ;
    VECTOR_ARITH `(&1 - t) % x + t % y = (&1 - u) % x + u % y <=>
                  (t - u) % (x - y) = vec 0`];
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID; LIFT_SUB] THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTERVAL_1; GSYM FORALL_DROP] THEN
      REWRITE_TAC[DROP_VEC] THEN ASM_MESON_TAC[CONVEX_ALT]];
    AP_TERM_TAC THEN REWRITE_TAC[DROP_VEC] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\h. vec 0) = ((\h. vec 0):real^M->real^N) o
                               (\t. drop t % (y - x))`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC DIFF_CHAIN_WITHIN THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `t % (y - x) = ((&0 - t) % x) + t % y`] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
    REWRITE_TAC[GSYM DROP_NEG; GSYM DROP_VEC; GSYM DROP_SUB] THEN
    SIMP_TAC[HAS_DERIVATIVE_VMUL_DROP; HAS_DERIVATIVE_ID] THEN
    REWRITE_TAC[DROP_SUB; VECTOR_SUB_RDISTRIB] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; DROP_VEC; HAS_DERIVATIVE_CONST] THEN
    SIMP_TAC[HAS_DERIVATIVE_VMUL_DROP; HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `s:real^M->bool` THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[CONVEX_ALT]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DIFF]) THEN
  SIMP_TAC[IN_ELIM_THM; IN_DIFF] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_INTERVAL_1; GSYM FORALL_DROP; DROP_VEC] THEN
  ASM_MESON_TAC[CONVEX_ALT]);;

(* ------------------------------------------------------------------------- *)
(* Also to any open connected set with finite set of exceptions. Could       *)
(* generalize to locally convex set with limpt-free set of exceptions.       *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONNECTED = prove
 (`!f:real^M->real^N s k c y.
      connected s /\ open s /\ COUNTABLE k /\ f continuous_on s /\
      c IN s /\ f c = y /\
      (!x. x IN (s DIFF k) ==> (f has_derivative (\h. vec 0)) (at x within s))
      ==> !x. x IN s ==> f x = y`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC
   `{x | x IN s /\ (f:real^M->real^N) x IN {y}}`) THEN
  ANTS_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN CONJ_TAC THEN
  ASM_SIMP_TAC[CONTINUOUS_CLOSED_IN_PREIMAGE; CLOSED_SING] THEN
  MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  UNDISCH_TAC `open(s:real^M->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `u:real^M` THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_CONVEX THEN
  MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `u:real^M`] THEN
  ASM_REWRITE_TAC[CONVEX_BALL; IN_DIFF; CENTRE_IN_BALL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[SUBSET] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* Equiintegrability. The definition here only really makes sense for an     *)
(* elementary set. We just use compact intervals in applications below.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("equiintegrable_on",(12,"right"));;

let equiintegrable_on = new_definition
  `fs equiintegrable_on i <=>
        (!f:real^M->real^N. f IN fs ==> f integrable_on i) /\
        (!e. &0 < e
             ==> ?d. gauge d /\
                    !f p. f IN fs /\ p tagged_division_of i /\ d fine p
                        ==> norm(vsum p (\(x,k). content(k) % f(x)) -
                                 integral i f) < e)`;;

let EQUIINTEGRABLE_ON_SING = prove
 (`!f:real^M->real^N a b.
        {f} equiintegrable_on interval[a,b] <=>
        f integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2] THEN
  ASM_CASES_TAC `(f:real^M->real^N) integrable_on interval[a,b]` THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  REWRITE_TAC[has_integral; IMP_IMP]);;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for the interval of integration.                 *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_ON_NULL = prove
 (`!fs:(real^M->real^N)->bool a b.
     content(interval[a,b]) = &0 ==> fs equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_NULL] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP (REWRITE_RULE[IMP_CONJ]
                                           VSUM_CONTENT_NULL) th]) THEN
  ASM_SIMP_TAC[INTEGRAL_NULL; VECTOR_SUB_REFL; NORM_0]);;

let EQUIINTEGRABLE_ON_SPLIT = prove
 (`!fs:(real^M->real^N)->bool k a b c.
      fs equiintegrable_on (interval[a,b] INTER {x | x$k <= c}) /\
      fs equiintegrable_on (interval[a,b] INTER {x | x$k >= c}) /\
      1 <= k /\ k <= dimindex(:M)
      ==> fs equiintegrable_on (interval[a,b])`,
  let lemma1 = prove
   (`(!x k. (x,k) IN {x,f k | P x k} ==> Q x k) <=>
     (!x k. P x k ==> Q x (f k))`,
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
    SET_TAC[]) in
  let lemma2 = prove
   (`!f:B->B s:(A#B)->bool.
      FINITE s ==> FINITE {x,f k | (x,k) IN s /\ P x k}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\(x:A,k:B). x,(f k:B)) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; lemma1; IN_IMAGE] THEN
    REWRITE_TAC[EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]) in
  let lemma3 = prove
   (`!f:real^M->real^N g:(real^M->bool)->(real^M->bool) p.
     FINITE p
     ==> vsum {x,g k |x,k| (x,k) IN p /\ ~(g k = {})}
              (\(x,k). content k % f x) =
         vsum (IMAGE (\(x,k). x,g k) p) (\(x,k). content k % f x)`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE; lemma2] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[FORALL_PAIR_THM; SUBSET; IN_IMAGE; EXISTS_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ; VECTOR_MUL_EQ_0] THEN
    MESON_TAC[CONTENT_EMPTY]) in
  let lemma4 = prove
   (`(\(x,l). content (g l) % f x) =
     (\(x,l). content l % f x) o (\(x,l). x,g l)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `1 <= k /\ k <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[equiintegrable_on] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b ==> c) /\ (a /\ b /\ c ==> a' /\ b' ==> c')
    ==> (a /\ a') /\ (b /\ b') ==> c /\ c'`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN ASM MESON_TAC[HAS_INTEGRAL_SPLIT];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `!f:real^M->real^N.
        f IN fs
        ==> integral (interval[a,b]) f =
                integral (interval [a,b] INTER {x | x$k <= c}) f +
                integral (interval [a,b] INTER {x | x$k >= c}) f`
   (fun th -> SIMP_TAC[th])
  THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_INTEGRAL_SPLIT THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `c:real`] THEN
    ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (MP_TAC o SPEC `e / &2`) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "I1"))) THEN
  EXISTS_TAC `\x. if x$k = c then (d1(x:real^M) INTER d2(x)):real^M->bool
                  else ball(x,abs(x$k - c)) INTER d1(x) INTER d2(x)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[gauge] THEN GEN_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[OPEN_INTER; IN_INTER; OPEN_BALL; IN_BALL] THEN
    ASM_REWRITE_TAC[DIST_REFL; GSYM REAL_ABS_NZ; REAL_SUB_0];
    ALL_TAC] THEN
  X_GEN_TAC `f:real^M->real^N` THEN
  X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
    `(!x:real^M kk. (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})
                    ==> x$k <= c) /\
     (!x:real^M kk. (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})
                    ==> x$k >= c)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `kk:real^M->bool` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; real_ge] THEN DISCH_THEN
     (MP_TAC o MATCH_MP (SET_RULE `k SUBSET (a INTER b) ==> k SUBSET a`)) THEN
    REWRITE_TAC[SUBSET; IN_BALL; dist] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M` MP_TAC) THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs((x - u:real^M)$k)` THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "I2" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k >= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k >= c} = {})}` o
   SPEC `f:real^M->real^N`) THEN
  REMOVE_THEN "I1" (MP_TAC o SPEC
   `{(x:real^M,kk INTER {x:real^M | x$k <= c}) |x,kk|
     (x,kk) IN p /\ ~(kk INTER {x:real^M | x$k <= c} = {})}` o
   SPEC `f:real^M->real^N`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(a /\ b) /\ (a' /\ b' ==> c) ==> (a ==> a') ==> (b ==> b') ==> c`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    REPEAT(MATCH_MP_TAC(TAUT
     `(a ==> (a' /\ a'')) /\ (b ==> (b' /\ d) /\ (b'' /\ e))
      ==> a /\ b ==> ((a' /\ b') /\ d) /\ ((a'' /\ b'') /\ e)`) THEN
      CONJ_TAC) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[lemma1] THEN REWRITE_TAC[IMP_IMP] THENL
     [SIMP_TAC[lemma2];
      REWRITE_TAC[AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `kk:real^M->bool` THEN
      DISCH_THEN(fun th -> CONJ_TAC THEN STRIP_TAC THEN MP_TAC th) THEN
      (ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
        [SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC]) THEN
      (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
      ASM_MESON_TAC[INTERVAL_SPLIT];
      DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
      (REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
       DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
       REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
       DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_SIMP_TAC[] THEN
       ANTS_TAC THENL [ASM_MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
       MATCH_MP_TAC(SET_RULE
        `s SUBSET s' /\ t SUBSET t'
         ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
       CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]);
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> b /\ c) /\ d /\ e
                       ==> (a ==> (b /\ d) /\ (c /\ e))`) THEN
    CONJ_TAC THENL
     [DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[INTER_UNIONS] THEN
      ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS] THEN
      X_GEN_TAC `x:real^M` THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `kk:real^M->bool` THEN
      REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[NOT_IN_EMPTY];
      ALL_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    REWRITE_TAC[fine; lemma1] THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &2 /\ y < e / &2 ==> x + y < e`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP NORM_TRIANGLE_LT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a - i) + (b - j) = c - (i + j) <=> a + b = c:real^N`] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
 MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum p (\(x,l). content (l INTER {x:real^M | x$k <= c}) %
                     (f:real^M->real^N) x) +
    vsum p (\(x,l). content (l INTER {x:real^M | x$k >= c}) %
                     (f:real^M->real^N) x)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[GSYM VSUM_ADD] THEN MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM; GSYM VECTOR_ADD_RDISTRIB] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `l:real^M->bool`] THEN
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `l:real^M->bool`] o
               el 1 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM CONTENT_SPLIT]] THEN
  ASM_SIMP_TAC[lemma3] THEN BINOP_TAC THEN
  (GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [lemma4] THEN
   MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
   REWRITE_TAC[PAIR_EQ] THEN
   ASM_MESON_TAC[TAGGED_DIVISION_SPLIT_LEFT_INJ; VECTOR_MUL_LZERO;
                 TAGGED_DIVISION_SPLIT_RIGHT_INJ]));;

let EQUIINTEGRABLE_DIVISION = prove
 (`!fs:(real^M->real^N)->bool d a b.
        d division_of interval[a,b]
        ==> (fs equiintegrable_on interval[a,b] <=>
             !i. i IN d ==> fs equiintegrable_on i)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC OPERATIVE_DIVISION_AND THEN
  ASM_REWRITE_TAC[operative; NEUTRAL_AND] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[equiintegrable_on; INTEGRABLE_ON_NULL] THEN
    GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `\x:real^M. ball(x,&1)` THEN
    ASM_SIMP_TAC[GAUGE_TRIVIAL; INTEGRAL_NULL; VECTOR_SUB_RZERO] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
     `&0 < e ==> x = vec 0 ==> norm x < e`)) THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ1_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[TAGGED_DIVISION_OF]) THEN
    ASM_MESON_TAC[CONTENT_EQ_0_INTERIOR; SUBSET_INTERIOR;
                  SET_RULE `s = {} <=> s SUBSET {}`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real`; `k:num`] THEN
  STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[EQUIINTEGRABLE_ON_SPLIT]] THEN
  ASM_SIMP_TAC[INTEGRABLE_SPLIT; equiintegrable_on] THEN
  STRIP_TAC THEN CONJ_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  (FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
   MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
   ASM_CASES_TAC `gauge(d:real^M->real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `f:real^M->real^N` THEN
   ASM_CASES_TAC `(f:real^M->real^N) IN fs` THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN
   MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                  `d:real^M->real^M->bool`; `e / &2`]
         HENSTOCK_LEMMA_PART1) THEN ASM_SIMP_TAC[REAL_HALF] THEN
   MATCH_MP_TAC MONO_FORALL THEN
   X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_OF_SUBSET THEN
     RULE_ASSUM_TAC(REWRITE_RULE[tagged_division_of]) THEN
     ASM_MESON_TAC[INTER_SUBSET];
     ALL_TAC] THEN
   MATCH_MP_TAC(NORM_ARITH
    `&0 < e /\ x:real^N = y ==> norm(x) <= e / &2 ==> norm(y) < e`) THEN
   ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN
   W(MP_TAC o PART_MATCH (lhand o rand)
     INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN o rand o rand o snd) THEN
   ASM_SIMP_TAC[GSYM INTERVAL_SPLIT; INTEGRABLE_SPLIT] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
   ASM_SIMP_TAC[GSYM VSUM_SUB] THEN MATCH_MP_TAC VSUM_EQ THEN
   REWRITE_TAC[FORALL_PAIR_THM]));;

(* ------------------------------------------------------------------------- *)
(* Main limit theorem for an equiintegrable sequence.                        *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_LIMIT = prove
 (`!f g:real^M->real^N a b.
        {f n | n IN (:num)} equiintegrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> ((\n. f n x) --> g x) sequentially)
        ==> g integrable_on interval[a,b] /\
            ((\n. integral(interval[a,b]) (f n)) --> integral(interval[a,b]) g)
            sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THEN
  ASM_SIMP_TAC[INTEGRABLE_ON_NULL; INTEGRAL_NULL; LIM_CONST] THEN
  SUBGOAL_THEN `cauchy (\n. integral(interval[a,b]) (f n :real^M->real^N))`
  MP_TAC THENL
   [REWRITE_TAC[cauchy] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
    DISCH_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FINE_DIVISION_EXISTS) THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
    DISCH_THEN(X_CHOOSE_THEN `p:(real^M#(real^M->bool))->bool`
        STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPECL
     [`n:num`; `p:(real^M#(real^M->bool))->bool`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN SUBGOAL_THEN
     `cauchy (\n. vsum p (\(x,k:real^M->bool).
               content k % (f:num->real^M->real^N) n x))`
    MP_TAC THENL
     [MATCH_MP_TAC CONVERGENT_IMP_CAUCHY THEN
      EXISTS_TAC `vsum p (\(x,k:real^M->bool).
          content k % (g:real^M->real^N) x)` THEN
      MATCH_MP_TAC
       (REWRITE_RULE[LAMBDA_PAIR_THM]
        (REWRITE_RULE[FORALL_PAIR_THM]
         (ISPEC `\(x:real^M,k:real^M->bool) (n:num).
                  content k % (f n x:real^N)` LIM_VSUM))) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      MATCH_MP_TAC LIM_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      ASM_SIMP_TAC[SUBSET] THEN ASM_MESON_TAC[];
      REWRITE_TAC[cauchy] THEN DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      ASM_CASES_TAC `N:num <= m /\ N <= n` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(sm - gm:real^N) < e / &3 /\ norm(sn - gn) < e / &3
        ==> dist(sm,sn) < e / &3 ==> dist(gm,gn) < e`) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM CONVERGENT_EQ_CAUCHY] THEN
    DISCH_THEN(X_CHOOSE_TAC `l:real^N`) THEN
    SUBGOAL_THEN `((g:real^M->real^N) has_integral l) (interval[a,b])`
     (fun th -> ASM_MESON_TAC[th; integrable_on; INTEGRAL_UNIQUE]) THEN
    REWRITE_TAC[has_integral] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC; IN_UNIV] THEN
    DISCH_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:(real^M#(real^M->bool))->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n:num. vsum p (\(x,k:real^M->bool). content k % f n x) -
                       integral (interval [a,b]) (f n :real^M->real^N)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[EVENTUALLY_TRUE] THEN
    MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    MATCH_MP_TAC
     (REWRITE_RULE[LAMBDA_PAIR_THM]
      (REWRITE_RULE[FORALL_PAIR_THM]
       (ISPEC `\(x:real^M,k:real^M->bool) (n:num).
                content k % (f n x:real^N)` LIM_VSUM))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    ASM_SIMP_TAC[SUBSET] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for the set of equiintegrable functions.               *)
(* ------------------------------------------------------------------------- *)

let EQUIINTEGRABLE_SUBSET = prove
 (`!fs gs s.
   fs equiintegrable_on s /\ gs SUBSET fs ==> gs equiintegrable_on s`,
  REWRITE_TAC[equiintegrable_on; SUBSET] THEN MESON_TAC[]);;

let EQUIINTEGRABLE_UNION = prove
 (`!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> (fs UNION gs) equiintegrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on; IN_UNION] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:real`)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. (d1:real^M->real^M->bool) x INTER d2 x` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let EQUIINTEGRABLE_EQ = prove
 (`!fs gs:(real^M->real^N)->bool s.
        fs equiintegrable_on s /\
        (!g. g IN gs ==> ?f. f IN fs /\ (!x. x IN s ==> f x = g x))
        ==> gs equiintegrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "*")) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `g:real^M->real^N` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `g:real^M->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f:real^M->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:real^M->real^N`) THEN
    ASM_MESON_TAC[INTEGRABLE_SPIKE; IN_DIFF; NEGLIGIBLE_EMPTY];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC
     [`g:real^M->real^N`;`p:(real^M#(real^M->bool))->bool`] THEN
    STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC `g:real^M->real^N`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `f:real^M->real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`f:real^M->real^N`;`p:(real^M#(real^M->bool))->bool`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[]
     `x:real^N = y /\ a = b ==> norm(x - a) < e ==> norm(y - b) < e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[TAGGED_DIVISION_OF; SUBSET]) THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[INTEGRAL_EQ]]]);;

let EQUIINTEGRABLE_CMUL = prove
 (`!fs:(real^M->real^N)->bool s k.
        fs equiintegrable_on s
        ==> {(\x. c % f x) | abs(c) <= k /\ f IN fs} equiintegrable_on s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[equiintegrable_on; INTEGRABLE_CMUL; FORALL_IN_GSPEC] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM; INTEGRAL_CMUL; IMP_IMP] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / (abs(k) + &1)`) THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_MUL_LZERO;
               REAL_ARITH `&0 < abs(k) + &1`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `f:real^M->real^N`;
                       `p:(real^M#(real^M->bool))->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
   SPECL [`f:real^M->real^N`; `p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x <= c * y ==> x <= y * (c + &1)`) THEN
  REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC(REAL_ARITH
   `!c. x = c * y /\ c *  y <= k * y ==> x <= k * y`) THEN
  EXISTS_TAC `abs c:real` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM NORM_MUL; GSYM VSUM_LMUL; VECTOR_SUB_LDISTRIB] THEN
    REWRITE_TAC[LAMBDA_PAIR_THM; VECTOR_MUL_ASSOC; REAL_MUL_SYM];
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC]);;

let EQUIINTEGRABLE_ADD = prove
 (`!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> {(\x. f x + g x) | f IN fs /\ g IN gs} equiintegrable_on s`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[equiintegrable_on; INTEGRABLE_ADD; FORALL_IN_GSPEC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f"))
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g"))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM; INTEGRAL_ADD; IMP_IMP] THEN
  REMOVE_THEN "g" (MP_TAC o SPEC `e / &2`) THEN
  REMOVE_THEN "f" (MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "f"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real^M->real^M->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g"))) THEN
  EXISTS_TAC `\x. (d1:real^M->real^M->bool) x INTER d2 x` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^M->real^N`;
                       `p:(real^M#(real^M->bool))->bool`] THEN STRIP_TAC THEN
  REMOVE_THEN "g" (MP_TAC o SPECL
   [`g:real^M->real^N`; `p:(real^M#(real^M->bool))->bool`]) THEN
  REMOVE_THEN "f" (MP_TAC o SPECL
   [`f:real^M->real^N`; `p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(NORM_ARITH
   `s + s' = t
    ==> norm(s - i) < e / &2 ==> norm(s' - i') < e / &2
        ==> norm(t - (i + i')) < e`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM_ADD] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM; VECTOR_ADD_LDISTRIB]);;

let EQUIINTEGRABLE_NEG = prove
 (`!fs:(real^M->real^N)->bool s.
        fs equiintegrable_on s
        ==> {(\x. --(f x)) | f IN fs} equiintegrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&1` o MATCH_MP EQUIINTEGRABLE_CMUL) THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `f:real^M->real^N` THEN DISCH_TAC THEN EXISTS_TAC `-- &1` THEN
  EXISTS_TAC `f:real^M->real^N` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN REAL_ARITH_TAC);;

let EQUIINTEGRABLE_SUB = prove
 (`!fs:(real^M->real^N)->bool gs s.
        fs equiintegrable_on s /\ gs equiintegrable_on s
        ==> {(\x. f x - g x) | f IN fs /\ g IN gs} equiintegrable_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP EQUIINTEGRABLE_NEG)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_ADD) THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^M->real^N`; `g:real^M->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `f:real^M->real^N` THEN
  EXISTS_TAC `\x. --((g:real^M->real^N) x)` THEN
  ASM_REWRITE_TAC[VECTOR_SUB] THEN EXISTS_TAC `g:real^M->real^N` THEN
  ASM_REWRITE_TAC[]);;

let EQUIINTEGRABLE_SUM = prove
 (`!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {(\x. vsum t (\i. c i % f i x)) |
               FINITE t /\
               (!i:A. i IN t ==> &0 <= c i /\ (f i) IN fs) /\
               sum t c = &1}
            equiintegrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC; RIGHT_IMP_FORALL_THM] THEN
  STRIP_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [INTEGRABLE_CMUL; INTEGRABLE_VSUM; ETA_AX; INTEGRAL_VSUM] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC
   [`t:A->bool`; `c:A->real`; `f:A->real^M->real^N`;
    `p:(real^M#(real^M->bool))->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!i:A. i IN t
          ==> integral (interval[a,b]) (\x:real^M. c i % f i x:real^N) =
              vsum p (\(x:real^M,k).
                       integral (k:real^M->bool) (\x:real^M. c i % f i x))`
   (fun th -> SIMP_TAC[th])
  THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN
    ASM_SIMP_TAC[INTEGRABLE_CMUL; ETA_AX];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN
   `vsum p (\(x,k:real^M->bool). content k % vsum t (\i. c i % f i x)) =
    vsum t (\i. c i %
                vsum p (\(x,k). content k % (f:A->real^M->real^N) i x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM VSUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o
      rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `sum t (\i:A. c i * e / &2)` THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[SUM_RMUL; ETA_AX; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; GSYM VSUM_SUB] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`(f:A->real^M->real^N) i`; `p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  DISCH_THEN(MP_TAC o SPEC `abs((c:A->real) i)` o
    MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_LMUL)) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS; GSYM NORM_MUL] THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; VECTOR_SUB_LDISTRIB; real_abs] THEN
  REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= a ==> y <= a`) THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
   `integral (interval[a,b]) ((f:A->real^M->real^N) i) =
    vsum p (\(x:real^M,k). integral (k:real^M->bool) (f i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_LMUL; GSYM VSUM_SUB] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_CMUL THEN
  RULE_ASSUM_TAC(REWRITE_RULE[TAGGED_DIVISION_OF]) THEN
  ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL]);;

let EQUIINTEGRABLE_UNIFORM_LIMIT = prove
 (`!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {g | !e. &0 < e
                     ==> ?f. f IN fs /\
                             !x. x IN interval[a,b] ==> norm(g x - f x) < e}
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
  REWRITE_TAC[equiintegrable_on; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_UNIFORM_LIMIT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real^M->real^M->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC
   [`g:real^M->real^N`;`p:(real^M#(real^M->bool))->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  SUBGOAL_THEN `(g:real^M->real^N) integrable_on interval[a,b]`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_UNIFORM_LIMIT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `f:num->real^M->real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN interval[a,b]
        ==> ((\n. f n x) --> (g:real^M->real^N) x) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `k:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `k:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_ARITH `dist(a:real^N,b) = norm(b - a)`] THEN
    MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n + &1)` THEN
    ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->real^M->real^N`; `g:real^M->real^N`;
                 `a:real^M`; `b:real^M`] EQUIINTEGRABLE_LIMIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQUIINTEGRABLE_SUBSET THEN
    EXISTS_TAC `fs:(real^M->real^N)->bool` THEN ASM SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))] THEN
  SUBGOAL_THEN
   `((\n. vsum p (\(x,k:real^M->bool).
                    content k % (f:num->real^M->real^N) n x)) -->
     vsum p (\(x,k). content k % g x)) sequentially`
   (LABEL_TAC "+")
  THENL
   [MATCH_MP_TAC
       (REWRITE_RULE[LAMBDA_PAIR_THM]
        (REWRITE_RULE[FORALL_PAIR_THM]
         (ISPEC `\(x:real^M,k:real^M->bool) (n:num).
                  content k % (f n x:real^N)` LIM_VSUM))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_CMUL THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    ASM_SIMP_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "*")) THEN
  REMOVE_THEN "+" (MP_TAC o REWRITE_RULE[LIM_SEQUENTIALLY]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[dist]] THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "+")) THEN
  SUBGOAL_THEN `?n:num. N1 <= n /\ N2 <= n` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `N1 + N2:num` THEN ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
  REMOVE_THEN "+" (MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(f:num->real^M->real^N) n`;`p:(real^M#(real^M->bool))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let EQUIINTEGRABLE_REFLECT = prove
 (`!fs:(real^M->real^N)->bool a b.
        fs equiintegrable_on interval[a,b]
        ==> {(\x. f(--x)) | f IN fs} equiintegrable_on interval[--b,--a]`,
  let lemma = prove
   (`(!x k. (x,k) IN IMAGE (\(x,k). f x k,g x k) s ==> Q x k) <=>
     (!x k. (x,k) IN s ==> Q (f x k) (g x k))`,
    REWRITE_TAC[IN_IMAGE; PAIR_EQ; EXISTS_PAIR_THM] THEN SET_TAC[]) in
  REPEAT GEN_TAC THEN REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[INTEGRABLE_REFLECT; INTEGRAL_REFLECT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. IMAGE (--) ((d:real^M->real^M->bool) (--x))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    SIMP_TAC[gauge; OPEN_NEGATIONS] THEN DISCH_TAC THEN
    GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_NEG_NEG] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `f:real^M->real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `f:real^M->real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\(x,k). (--x:real^M,IMAGE (--) (k:real^M->bool))) p`) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    REWRITE_TAC[TAGGED_DIVISION_OF] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; lemma] THEN
    REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
        ASM_SIMP_TAC[VECTOR_NEG_NEG; GSYM SUBSET] THEN ASM_MESON_TAC[];
        REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
        REWRITE_TAC[VECTOR_ARITH `x:real^N = --y <=> --x = y`] THEN
        ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
        REWRITE_TAC[UNWIND_THM1] THEN
        SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
        THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
        ASM_MESON_TAC[VECTOR_NEG_NEG]];
      MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`y:real^M`; `l:real^M->bool`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`x:real^M`; `k:real^M->bool`;
        `y:real^M`; `l:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_IMP THEN
      CONJ_TAC THENL [MESON_TAC[PAIR_EQ]; ALL_TAC] THEN
      REWRITE_TAC[INTERIOR_NEGATIONS] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. f(f x) = x)
        ==> s INTER t = {} ==> IMAGE f s INTER IMAGE f t = {}`) THEN
      REWRITE_TAC[VECTOR_NEG_NEG];
      GEN_REWRITE_TAC I [EXTENSION] THEN
      ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      MATCH_MP_TAC(MESON[]
       `!f. (!x. f(f x) = x) /\ (!x. P x <=> Q(f x))
            ==> ((?x. P x) <=> (?x. Q x))`) THEN
      EXISTS_TAC `IMAGE ((--):real^M->real^M)` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_NEG_NEG; IMAGE_ID];
        ALL_TAC] THEN
      X_GEN_TAC `t:real^M->bool` THEN BINOP_TAC THENL
       [REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN
        SUBGOAL_THEN `!k:real^M->bool. IMAGE (--) (IMAGE (--) k) = k`
        MP_TAC THENL
         [REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_NEG_NEG; IMAGE_ID];
          MESON_TAC[]];
        MATCH_MP_TAC(SET_RULE
         `(!x. f(f x) = x) ==> (y IN s <=> f y IN IMAGE f s)`) THEN
        REWRITE_TAC[VECTOR_NEG_NEG]]];
    ANTS_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      REWRITE_TAC[fine; lemma] THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. f(f x) = x) ==> k SUBSET IMAGE f s ==> IMAGE f k SUBSET s`) THEN
      REWRITE_TAC[VECTOR_NEG_NEG];
      ALL_TAC] THEN
    MATCH_MP_TAC(NORM_ARITH
     `x:real^N = y ==> norm(x - i) < e ==> norm(y - i) < e`) THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhs o snd) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC(MESON[]
       `(!x. f(f x) = x)
        ==> !x y. x IN p /\ y IN p /\ f x = f y ==> x = y`) THEN
      REWRITE_TAC[FORALL_PAIR_THM; GSYM IMAGE_o; o_DEF; VECTOR_NEG_NEG;
                  IMAGE_ID];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
      REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
       (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(--):real^M->real^M = (\x. --(&1) % x + vec 0)` SUBST1_TAC
      THENL [REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[CONTENT_IMAGE_AFFINITY_INTERVAL; REAL_ABS_NEG] THEN
      REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_ABS_NUM]]]);;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas about minimizing a "flat" part of a sum over a      *)
(* division, followed by subinterval resictions for equiintegrable family.   *)
(* ------------------------------------------------------------------------- *)

let SUM_CONTENT_AREA_OVER_THIN_DIVISION = prove
 (`!d a b:real^M s i c.
        d division_of s /\ s SUBSET interval[a,b] /\
        1 <= i /\ i <= dimindex(:M) /\ a$i <= c /\ c <= b$i /\
        (!k. k IN d ==> ~(k INTER {x | x$i = c} = {}))
        ==> (b$i - a$i) *
            sum d (\k. content k /
                       (interval_upperbound k$i - interval_lowerbound k$i))
            <= &2 * content(interval[a,b])`,
  let lemma0 = prove
   (`!k:real^M->bool i.
          1 <= i /\ i <= dimindex(:M)
          ==> content k / (interval_upperbound k$i - interval_lowerbound k$i) =
              if content k = &0 then &0
              else product ((1..dimindex(:M)) DELETE i)
                           (\j. interval_upperbound k$j -
                                interval_lowerbound k$j)`,
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
    REWRITE_TAC[content] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[CONTENT_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `1..dimindex(:M) = i INSERT ((1..dimindex(:M)) DELETE i)`
    MP_TAC THENL
     [REWRITE_TAC[SET_RULE `s = x INSERT (s DELETE x) <=> x IN s`] THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [th])] THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES; IN_NUMSEG; FINITE_DELETE; FINITE_NUMSEG;
                 IN_DELETE] THEN
    MATCH_MP_TAC(REAL_FIELD `~(y = &0) ==> (y * x) * inv y = x`) THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~(content(k:real^M->bool) = &0)` THEN
    ASM_REWRITE_TAC[content; PRODUCT_EQ_0_NUMSEG] THEN ASM_MESON_TAC[])
  and lemma1 = prove
   (`!d a b:real^M s i.
          d division_of s /\ s SUBSET interval[a,b] /\
          1 <= i /\ i <= dimindex(:M) /\
          ((!k. k IN d
                ==> ~(content k = &0) /\ ~(k INTER {x | x$i = a$i} = {})) \/
           (!k. k IN d
                ==> ~(content k = &0) /\ ~(k INTER {x | x$i = b$i} = {})))
          ==> (b$i - a$i) *
              sum d (\k. content k /
                         (interval_upperbound k$i - interval_lowerbound k$i))
              <= content(interval[a,b])`,
    REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ABBREV_TAC
     `extend =
      \k:real^M->bool. interval
           [(lambda j. if j = i then (a:real^M)$i
                       else interval_lowerbound k$j):real^M,
            (lambda j. if j = i then (b:real^M)$i
                       else interval_upperbound k$j)]` THEN
    SUBGOAL_THEN `!k. k IN d ==> k SUBSET interval[a:real^M,b]`
    ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!k:real^M->bool. k IN d ==> ~(k = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(!k. k IN d ==> ~((extend:(real^M->bool)->(real^M->bool)) k = {})) /\
      (!k. k IN d ==> extend k SUBSET interval[a,b])`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
      (DISCH_TAC THEN EXPAND_TAC "extend" THEN
       SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b]` MP_TAC THENL
        [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `~(interval[u:real^M,v] = {})` MP_TAC THENL
        [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SIMP_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY; LAMBDA_BETA;
                INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
       MESON_TAC[REAL_LE_TRANS; REAL_LE_REFL]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
              ==> interior((extend:(real^M->bool)->(real^M->bool)) k1) INTER
                  interior(extend k2) = {}`
    ASSUME_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`w:real^M`; `z:real^M`] THEN DISCH_TAC THEN
      DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN DISCH_THEN(MP_TAC o SPECL
       [`interval[u:real^M,v]`; `interval[w:real^M,z]`]) THEN
      ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXPAND_TAC "extend" THEN
      SIMP_TAC[INTERIOR_CLOSED_INTERVAL; IN_INTERVAL; LAMBDA_BETA] THEN
      SUBGOAL_THEN `~(interval[u:real^M,v] = {}) /\
                    ~(interval[w:real^M,z] = {})`
      MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SIMP_TAC[SUBSET_INTERVAL; INTERVAL_NE_EMPTY; LAMBDA_BETA;
               INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND] THEN
      STRIP_TAC THEN DISCH_THEN(X_CHOOSE_THEN `x:real^M` MP_TAC) THEN
      MP_TAC(MESON[]
       `(!P. (!j:num. P j) <=> P i /\ (!j. ~(j = i) ==> P j))`) THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC
       (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
      ASM_SIMP_TAC[IMP_IMP] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN
       (fun th -> MP_TAC(SPEC `interval[u:real^M,v]` th) THEN
                  MP_TAC(SPEC `interval[w:real^M,z]` th))) THEN
      ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL] THEN
      REWRITE_TAC[IMP_CONJ; GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `q:real^M` THEN STRIP_TAC THEN
      X_GEN_TAC `r:real^M` THEN STRIP_TAC THEN
      X_GEN_TAC `s:real^M` THEN STRIP_TAC THEN
      X_GEN_TAC `t:real^M` THEN STRIP_TAC THENL
       [EXISTS_TAC `(lambda j. if j = i then min ((q:real^M)$i) ((s:real^M)$i)
                               else (x:real^M)$j):real^M`;
        EXISTS_TAC `(lambda j. if j = i then max ((q:real^M)$i) ((s:real^M)$i)
                               else (x:real^M)$j):real^M`] THEN
      (SIMP_TAC[AND_FORALL_THM; LAMBDA_BETA] THEN X_GEN_TAC `j:num` THEN
       ASM_CASES_TAC `j:num = i` THEN ASM_SIMP_TAC[] THEN
       UNDISCH_THEN `j:num = i` SUBST_ALL_TAC THEN
       SUBGOAL_THEN `interval[u:real^M,v] SUBSET interval[a,b] /\
                     interval[w:real^M,z] SUBSET interval[a,b]`
       MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SUBGOAL_THEN `~(interval[u:real^M,v] = {}) /\
                     ~(interval[w:real^M,z] = {})`
       MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
       SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL] THEN
       REPEAT STRIP_TAC THEN
       REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC);
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `sum (IMAGE (extend:(real^M->bool)->(real^M->bool)) d) content` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
        STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`k1:real^M->bool`; `k2:real^M->bool`]) THEN
        ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
        EXPAND_TAC "extend" THEN REWRITE_TAC[CONTENT_EQ_0_INTERIOR];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
        MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
        MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN DISCH_TAC THEN
        ASM_CASES_TAC `content(interval[u:real^M,v]) = &0` THENL
         [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; o_THM] THEN
          EXPAND_TAC "extend" THEN REWRITE_TAC[CONTENT_POS_LE];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
        REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
        ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
                     REAL_LT_IMP_LE; real_div; REAL_MUL_ASSOC] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
        SUBGOAL_THEN
         `~((extend:(real^M->bool)->(real^M->bool)) (interval[u,v]) = {})`
        MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "extend" THEN ASM_SIMP_TAC[content; o_THM] THEN
        ASM_SIMP_TAC[INTERVAL_NE_EMPTY; INTERVAL_LOWERBOUND;
                     INTERVAL_UPPERBOUND; REAL_LT_IMP_LE] THEN
        DISCH_THEN(K ALL_TAC) THEN
        SUBGOAL_THEN
         `1..dimindex(:M) = i INSERT ((1..dimindex(:M)) DELETE i)`
        SUBST1_TAC THENL
         [MATCH_MP_TAC(SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) THEN
          ASM_REWRITE_TAC[IN_NUMSEG];
          ALL_TAC] THEN
        SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_DELETE] THEN
        ASM_SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC(REAL_RING
          `x:real = y ==> ab * uv * x = (ab * y) * uv`) THEN
        MATCH_MP_TAC PRODUCT_EQ THEN
        SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA]];
      MATCH_MP_TAC SUBADDITIVE_CONTENT_DIVISION THEN EXISTS_TAC
       `UNIONS (IMAGE (extend:(real^M->bool)->(real^M->bool)) d)` THEN
      ASM_SIMP_TAC[UNIONS_SUBSET; division_of; FINITE_IMAGE] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
      REPEAT CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
      DISCH_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
        EXPAND_TAC "extend" THEN REWRITE_TAC[] THEN MESON_TAC[];
        ASM_MESON_TAC[];
        ASM_SIMP_TAC[]]]) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
   [MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= y ==> x <= &2 * y`) THEN
    REWRITE_TAC[CONTENT_POS_LE; REAL_ENTIRE] THEN DISJ2_TAC THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `k:real^M->bool` THEN
    DISCH_TAC THEN REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
    MATCH_MP_TAC CONTENT_0_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`a:real^M`; `b:real^M`] THEN
    ASM_MESON_TAC[division_of; SUBSET_TRANS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  MP_TAC(ISPECL
   [`{k | k IN {l INTER {x | x$i <= c} | l |
                l IN d /\ ~(l INTER {x:real^M | x$i <= c} = {})} /\
          ~(content k = &0)}`;
    `a:real^M`;
    `(lambda j. if j = i then c else (b:real^M)$j):real^M`;
    `UNIONS {k | k IN {l INTER {x | x$i <= c} | l |
                       l IN d /\ ~(l INTER {x:real^M | x$i <= c} = {})} /\
                 ~(content k = &0)}`;
    `i:num`] lemma1) THEN
  MP_TAC(ISPECL
   [`{k | k IN {l INTER {x | x$i >= c} | l |
                l IN d /\ ~(l INTER {x:real^M | x$i >= c} = {})} /\
          ~(content k = &0)}`;
    `(lambda j. if j = i then c else (a:real^M)$j):real^M`;
    `b:real^M`;
    `UNIONS {k | k IN {l INTER {x | x$i >= c} | l |
                       l IN d /\ ~(l INTER {x:real^M | x$i >= c} = {})} /\
                 ~(content k = &0)}`;
    `i:num`] lemma1) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
   `(p1 /\ p2) /\ (q1 /\ q2 ==> r) ==> (p2 ==> q2) ==> (p1 ==> q1) ==> r`) THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    (REPEAT CONJ_TAC THENL
     [REWRITE_TAC[division_of] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
        MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN
        REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM; SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
          ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]];
        X_GEN_TAC `k:real^M->bool` THEN REPEAT DISCH_TAC THEN
        X_GEN_TAC `l:real^M->bool` THEN REPEAT DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
        DISCH_THEN(MP_TAC o SPECL [`k:real^M->bool`; `l:real^M->bool`] o
          el 2 o CONJUNCTS) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE
         `s SUBSET s' /\ t SUBSET t'
          ==> s' INTER t' = {} ==> s INTER t = {}`) THEN
        CONJ_TAC THEN MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IMP_CONJ] THEN
      X_GEN_TAC `k:real^M->bool` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `k SUBSET interval[a:real^M,b]` MP_TAC THENL
       [ASM_MESON_TAC[division_of; SUBSET_TRANS]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `i INTER h SUBSET j ==> k SUBSET i ==> k INTER h SUBSET j`) THEN
      ASM_SIMP_TAC[INTERVAL_SPLIT; SUBSET_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
      REAL_ARITH_TAC;
      ALL_TAC])
    THENL [DISJ2_TAC; DISJ1_TAC] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; real_ge] THEN ASM SET_TAC[REAL_LE_REFL];
    ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  SUBGOAL_THEN
   `sum {k | k IN
             { l INTER {x | x$i <= c} | l |
               l IN d /\ ~(l INTER {x:real^M | x$i <= c} = {})} /\
             ~(content k = &0)}
        (\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) =
    sum d ((\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) o
           (\k. k INTER {x | x$i <= c})) /\
    sum {k | k IN
             { l INTER {x | x$i >= c} | l |
               l IN d /\ ~(l INTER {x:real^M | x$i >= c} = {})} /\
             ~(content k = &0)}
        (\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) =
    sum d ((\k. content k /
             (interval_upperbound k$i - interval_lowerbound k$i)) o
           (\k. k INTER {x | x$i >= c}))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN
    (W(MP_TAC o PART_MATCH (rand o rand) SUM_IMAGE_NONZERO o rand o snd) THEN
     ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
      [MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `l:real^M->bool`] THEN
       STRIP_TAC THEN
       REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
       (MATCH_MP_TAC DIVISION_SPLIT_LEFT_INJ ORELSE
        MATCH_MP_TAC DIVISION_SPLIT_RIGHT_INJ) THEN ASM_MESON_TAC[];
       DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
       MATCH_MP_TAC SUM_SUPERSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
       GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
        `x IN IMAGE f d /\
         ~(x IN {x | x IN {f y |y| y IN d /\ ~(f y = a)} /\ ~P x})
         ==> (!y. f y = a ==> P(f y)) ==> P x`)) THEN
       SIMP_TAC[CONTENT_EMPTY; real_div; REAL_MUL_LZERO]]);
     ALL_TAC] THEN
  MAP_EVERY (fun (t,tac) ->
    ASM_CASES_TAC t THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_THEN(MP_TAC o tac) THEN
      MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> x <= a ==> y <= b`) THEN
      CONJ_TAC THENL
       [AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
        X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
        PURE_REWRITE_TAC[o_THM] THEN AP_TERM_TAC THEN
        REWRITE_TAC[real_ge; SET_RULE
         `k INTER {x | P x} = k <=> (!x. x IN k ==> P x)`] THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        SUBGOAL_THEN `x IN interval[a:real^M,b]` MP_TAC THENL
         [ASM_MESON_TAC[SUBSET; division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[IN_INTERVAL];
        MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x <= y ==> x <= &2 * y`) THEN
        REWRITE_TAC[CONTENT_POS_LE] THEN MATCH_MP_TAC CONTENT_SUBSET THEN
        SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
        MESON_TAC[REAL_LE_REFL]];
      ALL_TAC])
    [`c = (a:real^M)$i`,CONJUNCT2; `c = (b:real^M)$i`,CONJUNCT1] THEN
  SUBGOAL_THEN `(a:real^M)$i < c /\ c < (b:real^M)$i` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
  REWRITE_TAC[REAL_ARITH `(x * &2) / y = &2 * x / y`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `s <= s1 + s2 /\ c1 = c /\ c2 = c
    ==> s1 <= c1 /\ s2 <= c2 ==> s <= &2 * c`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[lemma0] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `~(interval[u:real^M,v] = {}) /\ interval[u,v] SUBSET interval[a,b]`
    MP_TAC THENL [ASM_MESON_TAC[division_of; SUBSET_TRANS]; ALL_TAC] THEN
    SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL; IMP_CONJ] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ c1 + c2 = c /\
      (~(c1 = &0) ==> x1 = x) /\ (~(c2 = &0) ==> x2 = x)
      ==> (if c = &0 then &0 else x) <=
          (if c1 = &0 then &0 else x1) +
          (if c2 = &0 then &0 else x2)`) THEN
    ASM_SIMP_TAC[GSYM CONTENT_SPLIT] THEN
    ASM_SIMP_TAC[INTERVAL_SPLIT; CONTENT_POS_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN
      ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE; IN_NUMSEG;
                   INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_SUB_LE];
      REWRITE_TAC[CONTENT_EQ_0; REAL_NOT_LE; MESON[]
       `~(?i. P i /\ Q i /\ R i) <=> (!i. P i /\ Q i ==> ~R i)`] THEN
      SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_LT_IMP_LE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
      ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; IN_DELETE;
                   IN_NUMSEG; LAMBDA_BETA]];
    SUBGOAL_THEN
     `~(interval[a,b] = {}) /\
      ~(interval[a:real^M,(lambda j. if j = i then c else b$j)] = {}) /\
      ~(interval[(lambda j. if j = i then c else a$j):real^M,b] = {})`
    MP_TAC THENL
     [SIMP_TAC[INTERVAL_NE_EMPTY; LAMBDA_BETA] THEN
      ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
      ALL_TAC] THEN
    SIMP_TAC[content] THEN
    SIMP_TAC[INTERVAL_NE_EMPTY; INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `1..dimindex(:M) = i INSERT ((1..dimindex(:M)) DELETE i)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG; FINITE_DELETE] THEN
    ASM_SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA] THEN
    CONJ_TAC THEN MATCH_MP_TAC(REAL_FIELD
     `y < x /\ z < w /\ a = b
      ==> ((x - y) * a) / (x - y) = ((w - z) * b) / (w - z)`) THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC[IN_DELETE; IN_NUMSEG; LAMBDA_BETA]]);;

let BOUNDED_EQUIINTEGRAL_OVER_THIN_TAGGED_PARTIAL_DIVISION = prove
 (`!fs f:real^M->real^N a b e.
    fs equiintegrable_on interval[a,b] /\ f IN fs /\
    (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x)) /\
    &0 < e
    ==> ?d. gauge d /\
            !c i p h. c IN interval[a,b] /\ 1 <= i /\ i <= dimindex(:M) /\
                      p tagged_partial_division_of interval[a,b] /\
                      d fine p /\
                      h IN fs /\
                      (!x k. (x,k) IN p ==> ~(k INTER {x | x$i = c$i} = {}))
                      ==> sum p(\(x,k). norm(integral k h)) < e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
   [EXISTS_TAC `\x:real^M. ball(x,&1)` THEN REWRITE_TAC[GAUGE_TRIVIAL] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `&0 < e ==> x = &0 ==> x < e`)) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    GEN_TAC THEN X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?u v:real^M. k = interval[u,v] /\ interval[u,v] SUBSET interval[a,b]`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_EQ_0] THEN MATCH_MP_TAC INTEGRAL_NULL THEN
    ASM_MESON_TAC[CONTENT_0_SUBSET];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. gauge d /\
        !p h. p tagged_partial_division_of interval [a,b] /\
              d fine p /\ (h:real^M->real^N) IN fs
              ==> sum p (\(x,k). norm(content k % h x - integral k h)) <
                  e / &2`
   (X_CHOOSE_THEN `g0:real^M->real^M->bool` STRIP_ASSUME_TAC)
  THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [equiintegrable_on]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC
      `e / &5 / (&(dimindex(:N)) + &1)`)) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &5 /\ &0 < &n + &1`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC
     [`p:(real^M#(real^M->bool))->bool`; `h:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `a:real^M`; `b:real^M`;
           `g:real^M->real^M->bool`; `e / &5 / (&(dimindex(:N)) + &1)`]
        HENSTOCK_LEMMA_PART2) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &5 /\ &0 < &n + &1`] THEN
    DISCH_THEN(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `a < b ==> x <= a ==> x < b`) THEN
    REWRITE_TAC[REAL_ARITH `&2 * d * e / &5 / (d + &1) =
                            (e * &2 / &5 * d) / (d + &1)`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ &0 < e * d ==> e * &2 / &5 * d < e / &2 * (d + &1)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
    ALL_TAC] THEN
  ABBREV_TAC
   `g:real^M->real^M->bool =
       \x. g0(x) INTER
           ball(x,(e / &8 / (norm(f x:real^N) + &1)) *
                  inf(IMAGE (\m. b$m - a$m) (1..dimindex(:M))) /
                  content(interval[a:real^M,b]))` THEN
  SUBGOAL_THEN `gauge(g:real^M->real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC GAUGE_INTER THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL] THEN
    X_GEN_TAC `x:real^M` THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_LT_DIV; NORM_ARITH
     `&0 < &8 /\ &0 < norm(x:real^N) + &1`] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_LT_INF_FINITE o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FINITE_RESTRICT] THEN
      SIMP_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
               GSYM NOT_LE; DIMINDEX_GE_1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_NUMSEG] THEN
      MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[REAL_SUB_LT; IN_NUMSEG; GSYM REAL_ABS_NZ; REAL_SUB_0;
                   IN_ELIM_THM]];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^M->real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`c:real^M`; `i:num`; `p:(real^M#(real^M->bool))->bool`;
    `h:real^M->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `interval[c:real^M,b] SUBSET interval[a,b]`
  ASSUME_TAC THENL
   [UNDISCH_TAC `c IN interval[a:real^M,b]` THEN
    SIMP_TAC[IN_INTERVAL; SUBSET_INTERVAL; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
  MP_TAC(ASSUME `(g:real^M->real^M->bool) fine p`) THEN
  EXPAND_TAC "g" THEN REWRITE_TAC[FINE_INTER] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "F")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
  DISCH_THEN(MP_TAC o SPEC `h:real^M->real^N`) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x - y <= e / &2 ==> y < e / &2 ==> x < e`) THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum p (\(x:real^M,k:real^M->bool). norm(content k % h x:real^N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    REWRITE_TAC[NORM_ARITH `norm y - norm(x - y:real^N) <= norm x`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum p (\(x:real^M,k).
                   e / &4 * (b$i - a$i) / content(interval[a:real^M,b]) *
                   content(k:real^M->bool) /
                   (interval_upperbound k$i - interval_lowerbound k$i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `content(k:real^M->bool) = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO; NORM_0;
                      REAL_MUL_RZERO; REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a * b * content k / d = content k * (a * b) / d`;
                NORM_MUL] THEN
    SUBGOAL_THEN `&0 < content(k:real^M->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTENT_LT_NZ; tagged_partial_division_of]; ALL_TAC] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_LE_LMUL_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `x + &1 <= y ==> x <= y`) THEN
    SUBGOAL_THEN `?u v. k = interval[u:real^M,v]` MP_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`u:real^M`; `v:real^M`] CONTENT_POS_LT_EQ) THEN
    ASM_SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND; REAL_LT_IMP_LE] THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_LE_RDIV_EQ o snd) THEN
    ASM_SIMP_TAC[REAL_SUB_LT] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_ARITH `&0 < norm(x:real^N) + &1`] THEN
    REMOVE_THEN "F" MP_TAC THEN REWRITE_TAC[fine] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `interval[u:real^M,v]`]) THEN
    ASM_REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v:real^M` th) THEN
                         MP_TAC(SPEC `u:real^M` th)) THEN
    ASM_SIMP_TAC[INTERVAL_NE_EMPTY; REAL_LT_IMP_LE; ENDS_IN_INTERVAL] THEN
    REWRITE_TAC[IN_BALL; IMP_IMP] THEN
    MATCH_MP_TAC(NORM_ARITH
     `abs(vi - ui) <= norm(v - u:real^N) /\ &2 * a <= b
      ==> dist(x,u) < a /\ dist(x,v) < a ==> vi - ui <= b`) THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM] THEN
    REWRITE_TAC[REAL_ARITH `&2 * e / &8 / x * y = e / &4 * y / x`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * inv b * inv c:real = (a / c) / b`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x <= e ==> x <= e`) THEN
    REWRITE_TAC[real_div; REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs x <= y`) THEN
      SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY; FINITE_NUMSEG;
               NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1; REAL_LE_INF_FINITE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_NUMSEG] THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; REAL_LE_REFL; REAL_SUB_LE;
                   REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[REAL_LE_REFL];
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= abs(y + &1)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[tagged_partial_division_of; SUBSET]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP TAGGED_PARTIAL_DIVISION_OF_UNION_SELF) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    SUM_OVER_TAGGED_DIVISION_LEMMA)) THEN
  DISCH_THEN(fun th ->
    W(MP_TAC o PART_MATCH (lhs o rand) th o lhand o snd)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [SIMP_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[SUM_LMUL; REAL_ARITH
   `e / &4 * ba / c * s <= e / &2 <=> e * (ba * s) / c <= e * &2`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC SUM_CONTENT_AREA_OVER_THIN_DIVISION THEN
  EXISTS_TAC `UNIONS(IMAGE SND (p:(real^M#(real^M->bool))->bool))` THEN
  EXISTS_TAC `(c:real^M)$i` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN ASM_SIMP_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIVISION_OF_TAGGED_DIVISION THEN
    ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    ASM_MESON_TAC[tagged_partial_division_of];
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM]]);;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i <= c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  let lemma = prove
   (`(!x k. (x,k) IN IMAGE (\(x,k). f x k,g x k) s ==> Q x k) <=>
     (!x k. (x,k) IN s ==> Q (f x k) (g x k))`,
    REWRITE_TAC[IN_IMAGE; PAIR_EQ; EXISTS_PAIR_THM] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THEN
  ASM_SIMP_TAC[EQUIINTEGRABLE_ON_NULL] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
  REWRITE_TAC[equiintegrable_on] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_UNIV; IMP_IMP; GSYM CONJ_ASSOC; RIGHT_IMP_FORALL_THM;
              IN_NUMSEG] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o REWRITE_RULE[equiintegrable_on]) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `x$i <= c <=> x IN {x:real^N | x$i <= c}`] THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_INTER] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN SIMP_TAC[INTERVAL_SPLIT] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN ASM_SIMP_TAC[] THEN
    SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA; REAL_LE_REFL] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`fs:(real^M->real^N)->bool`; `f:real^M->real^N`;
                 `a:real^M`; `b:real^M`; `e / &12`]
        BOUNDED_EQUIINTEGRAL_OVER_THIN_TAGGED_PARTIAL_DIVISION) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &12`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?d. gauge d /\
        !p h. p tagged_partial_division_of interval [a,b] /\
              d fine p /\ (h:real^M->real^N) IN fs
              ==> sum p (\(x,k). norm(content k % h x - integral k h)) <
                  e / &3`
   (X_CHOOSE_THEN `g1:real^M->real^M->bool` STRIP_ASSUME_TAC)
  THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[equiintegrable_on]) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &7 / (&(dimindex(:N)) + &1)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &7 /\ &0 < &n + &1`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:real^M->real^M->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC
     [`p:(real^M#(real^M->bool))->bool`; `h:real^M->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `a:real^M`; `b:real^M`;
           `d:real^M->real^M->bool`; `e / &7 / (&(dimindex(:N)) + &1)`]
        HENSTOCK_LEMMA_PART2) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &7 /\ &0 < &n + &1`] THEN
    DISCH_THEN(MP_TAC o SPEC `p:(real^M#(real^M->bool))->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `a < b ==> x <= a ==> x < b`) THEN
    REWRITE_TAC[REAL_ARITH `&2 * d * e / &7 / (d + &1) =
                            (e * &2 / &7 * d) / (d + &1)`] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ &0 < e * d ==> e * &2 / &7 * d < e / &3 * (d + &1)`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1];
    ALL_TAC] THEN
  EXISTS_TAC `\x. (g0:real^M->real^M->bool) x INTER g1 x` THEN
  ASM_SIMP_TAC[GAUGE_INTER; FINE_INTER] THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `1 <= i` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(MESON[]
   `!P. ((!c. (a:real^M)$i <= c /\ c <= (b:real^M)$i ==> P c) ==> (!c. P c)) /\
        (!c. (a:real^M)$i <= c /\ c <= (b:real^M)$i ==> P c)
        ==> !c. P c`) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [DISCH_THEN(LABEL_TAC "*") THEN
    X_GEN_TAC `c:real` THEN
    ASM_CASES_TAC `(a:real^M)$i <= c /\ c <= (b:real^M)$i` THENL
     [REMOVE_THEN "*" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `(b:real^M)$i`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `h:real^M->real^N` THEN
    MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN STRIP_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `x:real^N = vec 0 /\ y = vec 0 /\ &0 < e ==> norm(x - y) < e`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
        SUBGOAL_THEN `(x:real^M) IN interval[a,b]` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
        REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `integral(interval[a,b]) ((\x. vec 0):real^M->real^N)` THEN
        CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
        MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC(NORM_ARITH
       `x:real^N = y /\ w = z ==> norm(x - w) < e ==> norm(y - z) < e`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:real^M) IN interval[a,b]` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; SUBSET]; ALL_TAC] THEN
        REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC INTEGRAL_EQ THEN REWRITE_TAC[] THEN GEN_TAC THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_INTERVAL] THEN
        DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^N`;
                  `p:(real^M#(real^M->bool))->bool`] THEN STRIP_TAC THEN
  ABBREV_TAC
   `q:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN p /\ ~(k INTER {x | x$i <= c} = {})}` THEN
  MP_TAC(ISPECL
   [`\x. if x$i <= c then (h:real^M->real^N) x else vec 0`;
    `a:real^M`; `b:real^M`; `p:(real^M#(real^M->bool))->bool`]
        INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `FINITE(p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `q SUBSET (p:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(q:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `q tagged_partial_division_of interval[a:real^M,b] /\
                g0 fine q /\ g1 fine q`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_SUBSET; tagged_division_of;
                  FINE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!q. vsum p s = vsum q s /\ norm(vsum q s) < e
                            ==> norm(vsum p s:real^N) < e`) THEN
  EXISTS_TAC `q:(real^M#(real^M->bool))->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[EXTENSION] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[IN_INTER; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[VECTOR_NEG_EQ_0; VECTOR_SUB_LZERO] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `integral k ((\x. vec 0):real^M->real^N)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTEGRAL_0]] THEN
    MATCH_MP_TAC INTEGRAL_EQ THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum q (\(x,k). content k % h x - integral k (h:real^M->real^N)))
        < e / &3`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `sum q
      (\(x,k). norm(content k % h x - integral k (h:real^M->real^N)))` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - y:real^N) <= &2 * e / &3
    ==> norm(x) < e / &3 ==> norm(y) < e`) THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB] THEN ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC
   `r:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN q /\ ~(k SUBSET {x | x$i <= c})}` THEN
  SUBGOAL_THEN `r SUBSET (q:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(r:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `r tagged_partial_division_of interval[a:real^M,b] /\
                g0 fine r /\ g1 fine r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_SUBSET; FINE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `!r. vsum q s = vsum r s /\ norm(vsum r s) <= e
                            ==> norm(vsum q s:real^N) <= e`) THEN
  EXISTS_TAC `r:(real^M#(real^M->bool))->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    EXPAND_TAC "r" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL
     [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `c - i - (c - j):real^N = j - i`] THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  ONCE_REWRITE_TAC[LAMBDA_PAIR_THM] THEN REWRITE_TAC[] THEN
  MAP_EVERY ABBREV_TAC
   [`s:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN r /\ x IN {x | x$i <= c}}`;
    `t:(real^M#(real^M->bool))->bool =
        {(x,k) | (x,k) IN r /\ ~(x IN {x | x$i <= c})}`] THEN
  SUBGOAL_THEN
   `(s:(real^M#(real^M->bool))->bool) SUBSET r /\
    (t:(real^M#(real^M->bool))->bool) SUBSET r`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    SIMP_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(s:(real^M#(real^M->bool))->bool) /\
    FINITE(t:(real^M#(real^M->bool))->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (s:(real^M#(real^M->bool))->bool) t` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    REWRITE_TAC[EXTENSION; DISJOINT; IN_INTER; FORALL_PAIR_THM;
                IN_ELIM_PAIR_THM] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r:(real^M#(real^M->bool))->bool = s UNION t` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum s (\(x:real^M,k). norm
          (integral k (h:real^M->real^N) -
           integral k (\x. if x$i <= c then h x else vec 0))) +
    sum t (\(x:real^M,k). norm
          ((content k % (h:real^M->real^N) x - integral k h) +
           integral k (\x. if x$i <= c then h x else vec 0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
    MAP_EVERY EXPAND_TAC ["s"; "t"] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(NORM_ARITH `a:real^N = --b ==> norm a = norm b`) THEN
      VECTOR_ARITH_TAC;
      AP_TERM_TAC THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `s tagged_partial_division_of interval[a:real^M,b] /\
                t tagged_partial_division_of interval[a:real^M,b] /\
                g0 fine s /\ g1 fine s /\ g0 fine t /\ g1 fine t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_SUBSET; FINE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `(sum s (\(x:real^M,k). norm(integral k (h:real^M->real^N))) +
     sum (IMAGE (\(x,k). (x,k INTER {x | x$i <= c})) s)
         (\(x:real^M,k). norm(integral k (h:real^M->real^N)))) +
    (sum t (\(x:real^M,k). norm(content k % h x - integral k h)) +
     sum t (\(x:real^M,k). norm(integral k (h:real^M->real^N))) +
     sum (IMAGE (\(x,k). (x,k INTER {x | x$i >= c})) t)
         (\(x:real^M,k). norm(integral k (h:real^M->real^N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o
        rand o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC
         [`x:real^M`; `k:real^M->bool`; `y:real^M`; `l:real^M->bool`] THEN
        ASM_CASES_TAC `x:real^M = y` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT STRIP_TAC THEN MP_TAC(ISPECL
         [`s:real^M#(real^M->bool)->bool`;
          `UNIONS(IMAGE SND (s:real^M#(real^M->bool)->bool))`;
          `x:real^M`; `k:real^M->bool`;
          `y:real^M`; `l:real^M->bool`; `i:num`; `c:real`]
         TAGGED_DIVISION_SPLIT_LEFT_INJ) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
        REWRITE_TAC[NORM_EQ_0] THEN
        SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
        THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; INTEGRAL_NULL];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
        ASM_REWRITE_TAC[o_THM; FORALL_PAIR_THM] THEN
        ONCE_REWRITE_TAC[SET_RULE
         `x$i <= c <=> x IN {x:real^M | x$i <= c}`] THEN
        REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
        REWRITE_TAC[IN_ELIM_THM; INTER_COMM] THEN
        REWRITE_TAC[NORM_ARITH `norm(a - b:real^N) <= norm a + norm b`]];
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_NONZERO o
        rand o rand o rand o snd) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC
         [`x:real^M`; `k:real^M->bool`; `y:real^M`; `l:real^M->bool`] THEN
        ASM_CASES_TAC `x:real^M = y` THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
        REPEAT STRIP_TAC THEN MP_TAC(ISPECL
         [`t:real^M#(real^M->bool)->bool`;
          `UNIONS(IMAGE SND (t:real^M#(real^M->bool)->bool))`;
          `x:real^M`; `k:real^M->bool`;
          `y:real^M`; `l:real^M->bool`; `i:num`; `c:real`]
         TAGGED_DIVISION_SPLIT_RIGHT_INJ) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_MESON_TAC[TAGGED_PARTIAL_DIVISION_OF_UNION_SELF]; ALL_TAC] THEN
        REWRITE_TAC[NORM_EQ_0] THEN
        SUBGOAL_THEN `?u v:real^M. l = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
        THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT; INTEGRAL_NULL];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
        ASM_REWRITE_TAC[o_THM; FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
         `i = i1 + i2
          ==> norm(c + i1:real^N) <= norm(c) + norm(i) + norm(i2)`) THEN
        ONCE_REWRITE_TAC[SET_RULE
         `x$i <= c <=> x IN {x:real^M | x$i <= c}`] THEN
        REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
        ONCE_REWRITE_TAC[SET_RULE `{x | P x} INTER s = s INTER {x | P x}`] THEN
        SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
        THENL [ASM_MESON_TAC[tagged_partial_division_of]; ALL_TAC] THEN
        ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MATCH_MP_TAC INTEGRAL_SPLIT THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^M,b]` THEN
        ASM_SIMP_TAC[] THEN ASM_MESON_TAC[tagged_partial_division_of]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^M k. (x,k) IN r ==> ~(k INTER {x:real^M | x$i = c} = {})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MAP_EVERY EXPAND_TAC ["r"; "q"] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; SUBSET; EXTENSION; NOT_FORALL_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY; IN_INTER; NOT_IMP] THEN
    DISCH_TAC THEN MATCH_MP_TAC CONNECTED_IVT_COMPONENT THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_TOTAL]] THEN
    SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
     (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
    MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= e / &6 /\ y <= e / &2 ==> x + y <= &2 * e / &3`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `x < e / &12 /\ y < e / &12 ==> x + y <= e / &6`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(lambda j. if j = i then c else (a:real^M)$j):real^M` THEN
    EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[LAMBDA_BETA; IN_INTERVAL] THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[]];
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        UNDISCH_TAC `s tagged_partial_division_of interval[a:real^M,b]`;
        UNDISCH_TAC `(g0:real^M->real^M->bool) fine s` THEN
        REWRITE_TAC[fine; FORALL_IN_IMAGE; lemma] THEN SET_TAC[];
        REWRITE_TAC[lemma] THEN
        REPEAT GEN_TAC THEN EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
        `~(k INTER t = {}) /\ t SUBSET s ==> ~((k INTER s) INTER t = {})`) THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LE_REFL] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]];
    MATCH_MP_TAC(REAL_ARITH
     `x < e / &3 /\ y < e / &12 /\ z < e / &12 ==> x + y + z <= e / &2`) THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(lambda j. if j = i then c else (a:real^M)$j):real^M` THEN
    EXISTS_TAC `i:num` THEN ASM_SIMP_TAC[LAMBDA_BETA; IN_INTERVAL] THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[]];
      REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
        UNDISCH_TAC `t tagged_partial_division_of interval[a:real^M,b]`;
        UNDISCH_TAC `(g0:real^M->real^M->bool) fine t` THEN
        REWRITE_TAC[fine; FORALL_IN_IMAGE; lemma] THEN SET_TAC[];
        REWRITE_TAC[lemma] THEN
        REPEAT GEN_TAC THEN EXPAND_TAC "t" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        DISCH_TAC THEN MATCH_MP_TAC(SET_RULE
        `~(k INTER t = {}) /\ t SUBSET s ==> ~((k INTER s) INTER t = {})`) THEN
        SIMP_TAC[SUBSET; IN_ELIM_THM; REAL_LE_REFL; real_ge] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]]]] THEN
  REWRITE_TAC[tagged_partial_division_of] THEN
  (MATCH_MP_TAC MONO_AND THEN SIMP_TAC[FINITE_IMAGE] THEN
   MATCH_MP_TAC MONO_AND THEN
   REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_GSPEC] THEN
   REWRITE_TAC[lemma] THEN CONJ_TAC THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
   MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:real^M->bool` THEN
   DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THENL
    [MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
      [SIMP_TAC[real_ge; IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[REAL_LE_TOTAL];
       MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
        [SET_TAC[];
         STRIP_TAC THEN ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]]];
     REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
     MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
     MATCH_MP_TAC MONO_IMP THEN SIMP_TAC[PAIR_EQ; CONTRAPOS_THM] THEN
     MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t'
       ==> s' INTER t' = {} ==> s INTER t = {}`) THEN CONJ_TAC THEN
     MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[INTER_SUBSET]]));;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i >= c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{\x. (f:real^M->real^N) (--x) | f IN fs}`;
    `\x. (f:real^M->real^N)(--x)`;
    `--b:real^M`; `--a:real^M`]
        EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE) THEN
  ASM_SIMP_TAC[EQUIINTEGRABLE_REFLECT] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[GSYM IN_INTERVAL_REFLECT] THEN
    ASM_SIMP_TAC[VECTOR_NEG_NEG] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IN_IMAGE] THEN
    EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_REFLECT) THEN
    REWRITE_TAC[VECTOR_NEG_NEG] THEN MATCH_MP_TAC
     (REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC
     `(\x. if (--x)$i >= c then (h:real^M->real^N)(--x) else vec 0)` THEN
    REWRITE_TAC[VECTOR_NEG_NEG] THEN MAP_EVERY EXISTS_TAC
     [`i:num`; `--c:real`; `\x. (h:real^M->real^N)(--x)`] THEN
    ASM_REWRITE_TAC[IN_UNIV; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `--x >= c <=> x <= --c`] THEN
    EXISTS_TAC `h:real^M->real^N` THEN ASM_REWRITE_TAC[]]);;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LT = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i < c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:(real^M->real^N)->bool`; `f:real^M->real^N`;
                 `a:real^M`; `b:real^M`]
    EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `(fs:(real^M->real^N)->bool) equiintegrable_on interval[a,b]` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_SUB) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `h:real^M->real^N` THEN
  EXISTS_TAC `\x. if x$i >= c then (h:real^M->real^N) x else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; real_ge; GSYM REAL_NOT_LT] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

let EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT = prove
 (`!fs f:real^M->real^N a b.
        fs equiintegrable_on interval[a,b] /\ f IN fs /\
        (!h x. h IN fs /\ x IN interval[a,b] ==> norm(h x) <= norm(f x))
        ==> { (\x. if x$i > c then h x else vec 0) |
              i IN 1..dimindex(:M) /\ c IN (:real) /\ h IN fs }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`fs:(real^M->real^N)->bool`; `f:real^M->real^N`;
                 `a:real^M`; `b:real^M`]
    EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC
   `(fs:(real^M->real^N)->bool) equiintegrable_on interval[a,b]` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_SUB) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
  STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  EXISTS_TAC `h:real^M->real^N` THEN
  EXISTS_TAC `\x. if x$i <= c then (h:real^M->real^N) x else vec 0` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`i:num`; `c:real`; `h:real^M->real^N`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FUN_EQ_THM; real_gt; GSYM REAL_NOT_LE] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC]);;

let EQUIINTEGRABLE_OPEN_INTERVAL_RESTRICTIONS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> { (\x. if x IN interval(c,d) then f x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:M)
        ==> f INSERT
            { (\x. if !i. 1 <= i /\ i <= n ==> c$i < x$i /\ x$i < d$i
                   then (f:real^M->real^N) x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    ASM_REWRITE_TAC[ETA_AX; EQUIINTEGRABLE_ON_SING; SET_RULE
     `f INSERT {f |c,d| c IN UNIV /\ d IN UNIV} = {f}`] THEN
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `SUC n <= dimindex(:M)` THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LT)) THEN
    REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT)) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_SING] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; LEFT_OR_DISTRIB] THEN
      REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM]  THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC;
                  FORALL_AND_THM] THEN
      SIMP_TAC[IN_UNIV] THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE]);
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE
      `s SUBSET t ==> (x INSERT s) SUBSET ({x} UNION t)`) THEN
    REWRITE_TAC[SUBSET; real_gt; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(c:real^M)$(SUC n)` THEN
    MATCH_MP_TAC(MESON[]
     `(?i c k. P i c k /\ Q (g i c k))
      ==> ?h. (h = f \/ ?i c k. P i c k /\ h = g i c k) /\ Q h`) THEN
    EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(d:real^M)$(SUC n)` THEN
    EXISTS_TAC
     `\x. if !i. 1 <= i /\ i <= n ==> (c:real^M)$i < x$i /\ x$i < (d:real^M)$i
          then (f:real^M->real^N) x else vec 0` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM; LE] THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`]];
    DISCH_THEN(MP_TAC o SPEC `dimindex(:M)`) THEN
    REWRITE_TAC[IN_INTERVAL; LE_REFL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    SET_TAC[]]);;

let EQUIINTEGRABLE_CLOSED_INTERVAL_RESTRICTIONS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> { (\x. if x IN interval[c,d] then f x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:M)
        ==> f INSERT
            { (\x. if !i. 1 <= i /\ i <= n ==> c$i <= x$i /\ x$i <= d$i
                   then (f:real^M->real^N) x else vec 0) |
              c IN (:real^M) /\ d IN (:real^M) }
            equiintegrable_on interval[a,b]`
  MP_TAC THENL
   [MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC[ARITH_RULE `~(1 <= i /\ i <= 0)`] THEN
    ASM_REWRITE_TAC[ETA_AX; EQUIINTEGRABLE_ON_SING; SET_RULE
     `f INSERT {f |c,d| c IN UNIV /\ d IN UNIV} = {f}`] THEN
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `SUC n <= dimindex(:M)` THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_LE)) THEN
    REWRITE_TAC[IN_INSERT] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    DISCH_THEN(MP_TAC o SPEC `f:real^M->real^N` o
        MATCH_MP (REWRITE_RULE[IMP_CONJ]
          EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE)) THEN
    ASM_REWRITE_TAC[IN_UNION; IN_SING] THEN ANTS_TAC THENL
     [REWRITE_TAC[TAUT
       `a \/ b ==> c ==> d <=> (a ==> c ==> d) /\ (b ==> c ==> d)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; LEFT_OR_DISTRIB] THEN
      REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
      SIMP_TAC[REAL_LE_REFL; RIGHT_FORALL_IMP_THM]  THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC;
                  FORALL_AND_THM] THEN
      SIMP_TAC[IN_UNIV] THEN
      REPEAT STRIP_TAC THEN
      REPEAT(COND_CASES_TAC THEN
             ASM_SIMP_TAC[NORM_0; REAL_LE_REFL; NORM_POS_LE]);
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE
      `s SUBSET t ==> (x INSERT s) SUBSET ({x} UNION t)`) THEN
    REWRITE_TAC[SUBSET; real_ge; FORALL_IN_GSPEC; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(c:real^M)$(SUC n)` THEN
    MATCH_MP_TAC(MESON[]
     `(?i c k. P i c k /\ Q (g i c k))
      ==> ?h. (h = f \/ ?i c k. P i c k /\ h = g i c k) /\ Q h`) THEN
    EXISTS_TAC `SUC n` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    EXISTS_TAC `(d:real^M)$(SUC n)` THEN
    EXISTS_TAC
     `\x. if !i. 1 <= i /\ i <= n ==> (c:real^M)$i <= x$i /\ x$i <= (d:real^M)$i
          then (f:real^M->real^N) x else vec 0` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM; LE] THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= SUC n`]];
    DISCH_THEN(MP_TAC o SPEC `dimindex(:M)`) THEN
    REWRITE_TAC[IN_INTERVAL; LE_REFL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of the indefinite integral.                                    *)
(* ------------------------------------------------------------------------- *)

let INDEFINITE_INTEGRAL_CONTINUOUS = prove
 (`!f:real^M->real^N a b c d e.
        f integrable_on interval[a,b] /\
        c IN interval[a,b] /\ d IN interval[a,b] /\ &0 < e
        ==> ?k. &0 < k /\
                !c' d'. c' IN interval[a,b] /\
                        d' IN interval[a,b] /\
                        norm(c' - c) <= k /\ norm(d' - d) <= k
                        ==> norm(integral(interval[c',d']) f -
                                 integral(interval[c,d]) f) < e`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(?k. P k /\ Q k) <=> ~(!k. P k ==> ~Q k)`] THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  PURE_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; SKOLEM_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_NOT_LT; GSYM CONJ_ASSOC] THEN
  MAP_EVERY X_GEN_TAC [`u:num->real^M`; `v:num->real^M`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  ABBREV_TAC
   `k:real^M->bool =
    UNIONS (IMAGE (\i. {x | x$i = (c:real^M)$i} UNION {x | x$i = (d:real^M)$i})
                  (1..dimindex(:M)))` THEN
  SUBGOAL_THEN `negligible(k:real^M->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NEGLIGIBLE_UNION; NEGLIGIBLE_STANDARD_HYPERPLANE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num x. if x IN interval[u n,v n] then
                 if x IN k then vec 0 else (f:real^M->real^N) x
               else vec 0`;
    `\x. if x IN interval[c,d] then
            if x IN k then vec 0 else (f:real^M->real^N) x
         else vec 0`;
    `a:real^M`; `b:real^M`] EQUIINTEGRABLE_LIMIT) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x. if x IN k then vec 0 else (f:real^M->real^N) x)
      integrable_on interval[a,b]`
    MP_TAC THENL
     [UNDISCH_TAC `(f:real^M->real^N) integrable_on interval[a,b]` THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
      EQUIINTEGRABLE_CLOSED_INTERVAL_RESTRICTIONS) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN MAP_EVERY EXISTS_TAC
     [`(u:num->real^M) n`; `(v:num->real^M) n`] THEN
    REWRITE_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^M) IN k` THEN
    ASM_REWRITE_TAC[COND_ID; LIM_CONST] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `inf (IMAGE (\i. min (abs((x:real^M)$i - (c:real^M)$i))
                                     (abs((x:real^M)$i - (d:real^M)$i)))
                            (1..dimindex(:M)))` REAL_ARCH_INV) THEN
    SIMP_TAC[REAL_LT_INF_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
             FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_MIN; IN_NUMSEG] THEN
    UNDISCH_TAC `~((x:real^M) IN k)` THEN EXPAND_TAC "k" THEN
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[IN_NUMSEG; SET_RULE
     `~(p /\ x IN (s UNION t)) <=> p ==> ~(x IN s) /\ ~(x IN t)`] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_ARITH `&0 < abs(x - y) <=> ~(x = y)`] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `x IN interval[(u:num->real^M) n,v n] <=> x IN interval[c,d]`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[IN_INTERVAL] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!N n. abs(u - c) <= n /\ abs(v - d) <= n /\
            N < abs(x - c) /\ N < abs(x - d) /\ n <= N
      ==> (u <= x /\ x <= v <=> c <= x /\ x <= d)`) THEN
    MAP_EVERY EXISTS_TAC [`inv(&N)`; `inv(&n + &1)`] THEN
    ASM_SIMP_TAC[] THEN REPEAT (CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM; VECTOR_SUB_COMPONENT];
      ALL_TAC]) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
    SUBGOAL_THEN
     `interval[c:real^M,d] INTER interval[a,b] = interval[c,d] /\
      !n:num. interval[u n,v n] INTER interval[a,b] = interval[u n,v n]`
     (fun th -> SIMP_TAC[th])
    THENL
     [REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
      REWRITE_TAC[SUBSET_INTERVAL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL; REAL_NOT_LT] THEN
    FIRST_ASSUM(fun th -> MP_TAC(SPEC `N:num` th) THEN MATCH_MP_TAC
    (NORM_ARITH `x = a /\ y = b ==> e <= norm(x - y) ==> e <= dist(a,b)`)) THEN
    CONJ_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[IN_DIFF]]);;

let INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
         ==> (\x. integral (interval[a,x]) f) continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[continuous_within] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                 `a:real^M`; `x:real^M`; `e:real`]
        INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[dist]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ENDS_IN_INTERVAL; VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_LE] THEN
  ASM SET_TAC[]);;

let INDEFINITE_INTEGRAL_CONTINUOUS_LEFT = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\x. integral(interval[x,b]) f) continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[continuous_within] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                 `x:real^M`; `b:real^M`; `e:real`]
        INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[dist]] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[ENDS_IN_INTERVAL; VECTOR_SUB_REFL; NORM_0; REAL_LT_IMP_LE] THEN
  ASM SET_TAC[]);;

let INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\y. integral (interval[fstcart y,sndcart y]) f)
            uniformly_continuous_on interval[pastecart a a,pastecart b b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIFORMLY_CONTINUOUS THEN
  REWRITE_TAC[COMPACT_INTERVAL; continuous_on] THEN
  REWRITE_TAC[FORALL_PASTECART; GSYM PASTECART_INTERVAL] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `d:real^M`] THEN STRIP_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `a:real^M`; `b:real^M`; `c:real^M`; `d:real^M`;
    `e:real`] INDEFINITE_INTEGRAL_CONTINUOUS) THEN
  ASM_REWRITE_TAC[dist] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[PASTECART_SUB] THEN
  ASM_MESON_TAC[NORM_LE_PASTECART; REAL_LT_IMP_LE; REAL_LE_TRANS]);;

let INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS_EXPLICIT = prove
 (`!f:real^M->real^N a b e.
        f integrable_on interval[a,b] /\ &0 < e
        ==> ?k. &0 < k /\
                !c d c' d'. c IN interval[a,b] /\ d IN interval[a,b] /\
                            c' IN interval[a,b] /\ d' IN interval[a,b] /\
                            norm (c' - c) <= k /\ norm (d' - d) <= k
                            ==> norm(integral(interval[c',d']) f -
                                     integral(interval[c,d]) f) < e`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
    INDEFINITE_INTEGRAL_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k / &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`c:real^M`; `c':real^M`; `d:real^M`; `d':real^M`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`pastecart (c:real^M) (c':real^M)`;
    `pastecart (d:real^M) (d':real^M)`]) THEN
  REWRITE_TAC[GSYM PASTECART_INTERVAL] THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ASM_REWRITE_TAC[dist; PASTECART_SUB] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[NORM_PASTECART_LE; REAL_LET_TRANS;
    REAL_ARITH `&0 < k /\ x <= k / &3 /\ y <= k / &3 ==> x + y < k`]);;

(* ------------------------------------------------------------------------- *)
(* Second mean value theorem and corollaries.                                *)
(* ------------------------------------------------------------------------- *)

let SECOND_MEAN_VALUE_THEOREM_FULL = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\
        f integrable_on interval [a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (g(a) % integral (interval[a,c]) f +
                  g(b) % integral (interval[c,b]) f)) (interval[a,b])`,
  let lemma1 = prove
   (`!f:real->real s.
      (!x. x IN s ==> &0 <= f x /\ f x <= &1)
      ==> (!n x. x IN s /\ ~(n = 0)
                 ==> abs(f x -
                         sum(1..n) (\k. if &k / &n <= f(x)
                                        then inv(&n) else &0)) < inv(&n))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?m. floor(&n * (f:real->real) x) = &m` CHOOSE_TAC THENL
     [MATCH_MP_TAC FLOOR_POS THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `!k. &k / &n <= (f:real->real) x <=> k <= m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      SIMP_TAC[REAL_LE_FLOOR; INTEGER_CLOSED; REAL_MUL_SYM];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; real_div; REAL_ADD_RDISTRIB] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_MUL_LID; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[REAL_ARITH `y <= &1 /\ &0 < i ==> ~(&1 + i <= y)`;
                 REAL_LT_INV_EQ; REAL_OF_NUM_LT; LE_1; NOT_LE] THEN
    SIMP_TAC[IN_NUMSEG; ARITH_RULE
     `m < n + 1 ==> ((1 <= k /\ k <= n) /\ k <= m <=> 1 <= k /\ k <= m)`] THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM numseg; SUM_CONST_NUMSEG; ADD_SUB] THEN
    MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&n)` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ABS_NUM; REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; LE_1; REAL_SUB_LDISTRIB; GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ] THEN
    MATCH_MP_TAC(REAL_ARITH `f <= x /\ x < f + &1 ==> abs(x - f) < &1`) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[FLOOR]) in
  let lemma2 = prove
   (`!f:real^1->real^N g a b.
          f integrable_on interval[a,b] /\
          (!x y. drop x <= drop y ==> g(x) <= g(y))
          ==> {(\x. if c <= g(x) then f x else vec 0) | c IN (:real)}
              equiintegrable_on interval[a,b]`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM EQUIINTEGRABLE_ON_SING]) THEN
    DISCH_THEN(fun th ->
     MP_TAC(SPEC `f:real^1->real^N` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
       EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GE) th)) THEN
     MP_TAC(SPEC `f:real^1->real^N` (MATCH_MP (REWRITE_RULE[IMP_CONJ]
       EQUIINTEGRABLE_HALFSPACE_RESTRICTIONS_GT) th)) THEN
      MP_TAC th) THEN
    SIMP_TAC[IN_SING; REAL_LE_REFL] THEN
    SUBGOAL_THEN `{(\x. vec 0):real^1->real^N} equiintegrable_on interval[a,b]`
    MP_TAC THENL
     [REWRITE_TAC[EQUIINTEGRABLE_ON_SING; INTEGRABLE_CONST]; ALL_TAC] THEN
    REPEAT(ONCE_REWRITE_TAC[IMP_IMP] THEN
           DISCH_THEN(MP_TAC o MATCH_MP EQUIINTEGRABLE_UNION)) THEN
    REWRITE_TAC[NUMSEG_SING; DIMINDEX_1; IN_SING] THEN
    REWRITE_TAC[SET_RULE `{m i c h | i = 1 /\ c IN (:real) /\ h = f} =
                          {m 1 c f | c IN (:real)}`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN
    X_GEN_TAC `y:real` THEN
    ASM_CASES_TAC `!x. y <= (g:real^1->real) x` THENL
     [ASM_REWRITE_TAC[ETA_AX; IN_UNION; IN_SING]; ALL_TAC] THEN
    ASM_CASES_TAC `!x. ~(y <= (g:real^1->real) x)` THENL
     [ASM_REWRITE_TAC[ETA_AX; IN_UNION; IN_SING]; ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE drop {x | y <= (g:real^1->real) x}` INF) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IMAGE_EQ_EMPTY] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL];
      STRIP_TAC THEN REWRITE_TAC[real_gt; real_ge]] THEN
    REWRITE_TAC[IN_UNION; GSYM DISJ_ASSOC] THEN
    ASM_CASES_TAC `y <= g(lift(inf(IMAGE drop {x | y <= g x})))` THENL
     [REPEAT DISJ2_TAC; REPLICATE_TAC 2 DISJ2_TAC THEN DISJ1_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `inf(IMAGE drop {x | y <= g x})` THEN
    REWRITE_TAC[FUN_EQ_THM] THEN
    MATCH_MP_TAC(MESON[]
     `(!x. P x <=> Q x)
      ==> !x. (if P x then f x else b) = (if Q x then f x else b)`) THEN
    X_GEN_TAC `x:real^1` THEN REWRITE_TAC[GSYM REAL_NOT_LE; GSYM drop] THEN
    ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LT_ANTISYM; REAL_LE_TRANS; LIFT_DROP]) in
  let lemma3 = prove
   (`!f:real^1->real^N g a b.
          f integrable_on interval[a,b] /\
          (!x y. drop x <= drop y ==> g(x) <= g(y))
          ==> {(\x. vsum (1..n)
                     (\k. if &k / &n <= g x then inv(&n) % f(x) else vec 0)) |
               ~(n = 0)}
              equiintegrable_on interval[a,b]`,
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o
     MATCH_MP lemma2) THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (INST_TYPE [`:num`,`:A`] EQUIINTEGRABLE_SUM)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] EQUIINTEGRABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV] THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`1..n`; `\k:num. inv(&n)`;
     `\k x. if &k / &n <= g x then (f:real^1->real^N) x else vec 0`] THEN
    ASM_SIMP_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[FINITE_NUMSEG; COND_RAND; COND_RATOR; VECTOR_MUL_RZERO] THEN
    X_GEN_TAC `k:num` THEN
    REWRITE_TAC[IN_NUMSEG; REAL_LE_INV_EQ; REAL_POS] THEN STRIP_TAC THEN
    EXISTS_TAC `&k / &n` THEN REWRITE_TAC[]) in
  let lemma4 = prove
   (`!f:real^1->real^1 g a b.
          ~(interval[a,b] = {}) /\
          f integrable_on interval[a,b] /\
          (!x y. drop x <= drop y ==> g(x) <= g(y)) /\
          (!x. x IN interval[a,b] ==> &0 <= g x /\ g x <= &1)
          ==> (\x. g(x) % f(x)) integrable_on interval[a,b] /\
              ?c. c IN interval[a,b] /\
                  integral (interval[a,b]) (\x. g(x) % f(x)) =
                  integral (interval[c,b]) f`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?m M. IMAGE (\x. integral (interval[x,b]) (f:real^1->real^1))
                  (interval[a,b]) = interval[m,M]`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM CONNECTED_COMPACT_INTERVAL_1] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE;
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE] THEN
      ASM_SIMP_TAC[INDEFINITE_INTEGRAL_CONTINUOUS_LEFT; CONVEX_CONNECTED;
                   CONVEX_INTERVAL; COMPACT_INTERVAL];
      ALL_TAC] THEN
    MP_TAC(ISPECL[`f:real^1->real^1`; `g:real^1->real`; `a:real^1`; `b:real^1`]
          lemma3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!n. ?c. c IN interval[a,b] /\
              integral (interval[c,b]) (f:real^1->real^1) =
              integral (interval[a,b])
                (\x. vsum (1..n)
                    (\k. if &k / &n <= g x then inv(&n) % f x else vec 0))`
    MP_TAC THENL
     [X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n = 0` THENL
       [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_EQ; INTEGRAL_0] THEN
        EXISTS_TAC `b:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
        SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`f:real^1->real^1`; `g:real^1->real`;
                     `a:real^1`; `b:real^1`] lemma2) THEN
      ASM_REWRITE_TAC[equiintegrable_on; FORALL_IN_GSPEC; IN_UNIV] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
      REWRITE_TAC[MESON[VECTOR_MUL_RZERO]
       `(if p then a % x else vec 0:real^1) =
        a % (if p then x else vec 0)`] THEN
      ASM_SIMP_TAC[VSUM_LMUL; INTEGRAL_CMUL; INTEGRABLE_VSUM; ETA_AX;
                   FINITE_NUMSEG; INTEGRAL_VSUM] THEN
      SUBGOAL_THEN
       `!y:real. ?d:real^1.
          d IN interval[a,b] /\
          integral (interval[a,b]) (\x. if y <= g x then f x else vec 0) =
          integral (interval[d,b]) (f:real^1->real^1)`
      MP_TAC THENL
       [X_GEN_TAC `y:real` THEN
        SUBGOAL_THEN
         `{x | y <= g x} = {} \/
          {x | y <= g x} = (:real^1) \/
          (?a. {x | y <= g x} = {x | a <= drop x}) \/
          (?a. {x | y <= g x} = {x | a < drop x})`
        MP_TAC THENL
         [MATCH_MP_TAC(TAUT `(~a /\ ~b ==> c \/ d) ==> a \/ b \/ c \/ d`) THEN
          DISCH_TAC THEN
          MP_TAC(ISPEC `IMAGE drop {x | y <= (g:real^1->real) x}` INF) THEN
          ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IMAGE_EQ_EMPTY] THEN
          ANTS_TAC THENL
           [FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
            REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
            ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_TOTAL];
            STRIP_TAC] THEN
          ASM_CASES_TAC `y <= g(lift(inf(IMAGE drop {x | y <= g x})))` THENL
           [DISJ1_TAC; DISJ2_TAC] THEN
          REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
          EXISTS_TAC `inf(IMAGE drop {x | y <= g x})` THEN
          REWRITE_TAC[FUN_EQ_THM] THEN
          X_GEN_TAC `x:real^1` THEN
          REWRITE_TAC[GSYM REAL_NOT_LE; GSYM drop] THEN
          ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LT_ANTISYM;
                        REAL_LE_TRANS; LIFT_DROP];
          REWRITE_TAC[EXTENSION; IN_UNIV; NOT_IN_EMPTY; IN_ELIM_THM] THEN
          DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
           [EXISTS_TAC `b:real^1` THEN ASM_REWRITE_TAC[] THEN
            SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL] THEN
            ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTEGRAL_0];
            ALL_TAC] THEN
          DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC MP_TAC) THENL
           [EXISTS_TAC `a:real^1` THEN
            ASM_REWRITE_TAC[ETA_AX; ENDS_IN_INTERVAL];
            ALL_TAC] THEN
          GEN_REWRITE_TAC LAND_CONV [OR_EXISTS_THM] THEN
          REWRITE_TAC[EXISTS_DROP] THEN
          DISCH_THEN(X_CHOOSE_THEN `d:real^1` ASSUME_TAC) THEN
          ASM_CASES_TAC `drop d < drop a` THENL
           [EXISTS_TAC `a:real^1` THEN
            ASM_REWRITE_TAC[ETA_AX; ENDS_IN_INTERVAL] THEN
            MATCH_MP_TAC INTEGRAL_EQ THEN
            REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; NOT_IN_EMPTY] THEN
            GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `~(y <= (g:real^1->real) x)` THEN
            FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          ASM_CASES_TAC `drop b < drop d` THENL
           [EXISTS_TAC `b:real^1` THEN
            SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL] THEN
            ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTEGRAL_0] THEN
            MATCH_MP_TAC INTEGRAL_EQ_0 THEN REWRITE_TAC[IN_INTERVAL_1] THEN
            REPEAT STRIP_TAC THEN
            COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `y <= (g:real^1->real) x` THEN
            FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
            ASM_REAL_ARITH_TAC;
            ALL_TAC] THEN
          EXISTS_TAC `d:real^1` THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1; GSYM REAL_NOT_LT] THEN
          ONCE_REWRITE_TAC[SET_RULE
            `~((g:real^1->real) x < y) <=> x IN {x | ~(g x < y)}`] THEN
          REWRITE_TAC[INTEGRAL_RESTRICT_INTER] THEN
          MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
          MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{d:real^1}` THEN
          REWRITE_TAC[NEGLIGIBLE_SING; REAL_NOT_LT; SUBSET] THEN GEN_TAC THEN
          REWRITE_TAC[SUBSET; IN_UNION; IN_INTER; IN_DIFF; IN_INTERVAL_1;
                      IN_ELIM_THM; IN_SING; GSYM DROP_EQ] THEN
          FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        DISCH_THEN(MP_TAC o GEN `k:num` o SPEC `&k / &n`) THEN
        REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
        X_GEN_TAC `d:num->real^1` THEN STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
         `IMAGE f s = t ==> !y. y IN t ==> ?x. x IN s /\ f x = y`)) THEN
        REWRITE_TAC[GSYM VSUM_LMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[CONVEX_INDEXED]
         (CONJUNCT1(SPEC_ALL CONVEX_INTERVAL))) THEN
        REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_LE_INV_EQ; REAL_POS] THEN
        ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ] THEN ASM SET_TAC[]];
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      X_GEN_TAC `c:num->real^1` THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM)] THEN
    SUBGOAL_THEN `compact(interval[a:real^1,b])` MP_TAC THENL
     [REWRITE_TAC[COMPACT_INTERVAL]; REWRITE_TAC[compact]] THEN
    DISCH_THEN(MP_TAC o SPEC `c:num->real^1`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`d:real^1`; `s:num->num`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`\n:num x. vsum (1..(s n))
                      (\k. if &k / &(s n) <= g x
                           then inv(&(s n)) % (f:real^1->real^1) x
                           else vec 0)`;
      `\x. g x % (f:real^1->real^1) x`; `a:real^1`; `b:real^1`]
     EQUIINTEGRABLE_LIMIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC EQUIINTEGRABLE_SUBSET THEN
        EXISTS_TAC
         `{\x. vsum(1..0) (\k. if &k / &0 <= g x
                               then inv(&0) % (f:real^1->real^1) x else vec 0)}
          UNION
          {\x. vsum (1..n)
                    (\k. if &k / &n <= g x then inv (&n) % f x else vec 0)
           | ~(n = 0)}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC EQUIINTEGRABLE_UNION THEN ASM_REWRITE_TAC[] THEN
          REWRITE_TAC[EQUIINTEGRABLE_ON_SING; VSUM_CLAUSES_NUMSEG;
                      ARITH_EQ] THEN
          REWRITE_TAC[INTEGRABLE_0];
          REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_UNIV; IN_UNION] THEN
          REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
          X_GEN_TAC `n:num` THEN ASM_CASES_TAC `(s:num->num) n = 0` THEN
          ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
          EXISTS_TAC `(s:num->num) n` THEN ASM_REWRITE_TAC[]];
        X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[MESON[VECTOR_MUL_LZERO]
         `(if p then a % x else vec 0) = (if p then a else &0) % x`] THEN
        REWRITE_TAC[VSUM_RMUL] THEN MATCH_MP_TAC LIM_VMUL THEN
        REWRITE_TAC[LIM_SEQUENTIALLY; o_DEF; DIST_LIFT] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(ISPEC `e:real` REAL_ARCH_INV) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
        X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
        DISCH_TAC THEN
        ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
        MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&n)` THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL
           [`(g:real^1->real) o lift`; `IMAGE drop (interval[a,b])`]
            lemma1) THEN
          ASM_REWRITE_TAC[FORALL_IN_IMAGE; o_DEF; LIFT_DROP; IMP_CONJ;
                          RIGHT_FORALL_IMP_THM] THEN
          REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LTE_TRANS THEN
          EXISTS_TAC `inv(&((s:num->num) n))` THEN CONJ_TAC THENL
           [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
            MATCH_MP_TAC REAL_LE_INV2 THEN
            REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT]] THEN
          FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP MONOTONE_BIGGER) THEN
          ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `d:real^1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
      EXISTS_TAC `\n. integral (interval [c((s:num->num) n),b])
                               (f:real^1->real^1)` THEN
      ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
      MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`]
          INDEFINITE_INTEGRAL_CONTINUOUS_LEFT) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN(MP_TAC o SPEC `d:real^1`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONTINUOUS_WITHIN_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `(c:num->real^1) o (s:num->num)`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[o_DEF]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^1->real) a <= g b` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
    ASM_MESON_TAC[INTERVAL_EQ_EMPTY_1; REAL_LET_TOTAL];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `!x. x IN interval[a,b] ==> g(x) % (f:real^1->real^1)(x) = g(a) % f x`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE
       [IN_INTERVAL_1; INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
      ASM_MESON_TAC[REAL_LE_ANTISYM; REAL_LE_TRANS; REAL_LE_TOTAL];
      ALL_TAC] THEN
    EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN
    MATCH_MP_TAC HAS_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. g(a:real^1) % (f:real^1->real^1) x` THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; CONTENT_EQ_0_1; REAL_LE_REFL] THEN
    ASM_SIMP_TAC[INTEGRAL_CMUL; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
    ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`;
    `\x. if drop x < drop a then &0
         else if drop b < drop x then &1
         else (g(x) - g(a)) / (g(b) - g(a))`;
    `a:real^1`; `b:real^1`]
   lemma4) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN
    REPEAT GEN_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL]) THEN
    TRY ASM_REAL_ARITH_TAC THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LE_DIV2_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_SUB_LE;
                    REAL_ARITH `x - a <= y - a <=> x <= y`] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^1->real) b - g a` o
        MATCH_MP HAS_INTEGRAL_CMUL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^1->real)(a)` o
      MATCH_MP HAS_INTEGRAL_CMUL) THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
        INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[IN_INTERVAL_1]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH
   `ga % (i1 + i2) + (gb - ga) % i2:real^N = ga % i1 + gb % i2`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_NOT_LE; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_SUB_LT] THEN
  VECTOR_ARITH_TAC);;

let SECOND_MEAN_VALUE_THEOREM = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\
        f integrable_on interval [a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                 g(a) % integral (interval[a,c]) f +
                 g(b) % integral (interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[]);;

let SECOND_MEAN_VALUE_THEOREM_GEN_FULL = prove
 (`!f:real^1->real^1 g a b u v.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (u % integral (interval[a,c]) f +
                  v % integral (interval[c,b]) f)) (interval[a,b])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real^1 = a` THENL
   [EXISTS_TAC `a:real^1` THEN ASM_REWRITE_TAC[INTERVAL_SING; IN_SING] THEN
    ASM_SIMP_TAC[GSYM INTERVAL_SING; INTEGRAL_NULL; CONTENT_EQ_0_1;
      VECTOR_ADD_LID; REAL_LE_REFL; VECTOR_MUL_RZERO; HAS_INTEGRAL_NULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop a < drop b` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LE; DROP_EQ; REAL_LT_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= v` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_EQ_EMPTY_1; MEMBER_NOT_EMPTY; REAL_NOT_LT;
                  REAL_LE_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`;
    `\x:real^1. if x = a then u else if x = b then v else g x:real`;
    `a:real^1`; `b:real^1`] SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    ASM_CASES_TAC `x:real^1 = a` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[REAL_LE_REFL; INTERVAL_CASES_1]; ALL_TAC] THEN
    ASM_CASES_TAC `y:real^1 = b` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[REAL_LE_REFL; INTERVAL_CASES_1]; ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM DROP_EQ]) THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN MATCH_MP_TAC
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
        HAS_INTEGRAL_SPIKE) THEN
    EXISTS_TAC `{a:real^1,b}` THEN
    SIMP_TAC[NEGLIGIBLE_EMPTY; NEGLIGIBLE_INSERT; IN_DIFF; IN_INSERT;
             NOT_IN_EMPTY; DE_MORGAN_THM]]);;

let SECOND_MEAN_VALUE_THEOREM_GEN = prove
 (`!f:real^1->real^1 g a b u v.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval(a,b) ==> u <= g x /\ g x <= v) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                u % integral (interval[a,c]) f +
                v % integral (interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[]);;

let SECOND_MEAN_VALUE_THEOREM_BONNET_FULL = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\ f integrable_on interval [a,b] /\
        (!x. x IN interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                ((\x. g x % f x) has_integral
                 (g(b) % integral (interval[c,b]) f)) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`; `g:real^1->real`; `a:real^1`; `b:real^1`;
    `&0`; `(g:real^1->real) b`] SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let SECOND_MEAN_VALUE_THEOREM_BONNET = prove
 (`!f:real^1->real^1 g a b.
        ~(interval[a,b] = {}) /\ f integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> &0 <= g x) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g x <= g y)
        ==> ?c. c IN interval [a,b] /\
                integral (interval[a,b]) (\x. g x % f x) =
                g(b) % integral (interval[c,b]) f`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP SECOND_MEAN_VALUE_THEOREM_BONNET_FULL) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^1` THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REWRITE_TAC[]);;

let INTEGRABLE_INCREASING_PRODUCT = prove
 (`!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g(x) <= g(y))
        ==> (\x. g(x) % f(x)) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY] THEN
  ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. lift((f:real^1->real^N) x$i)`;
                 `g:real^1->real`; `a:real^1`; `b:real^1`]
    SECOND_MEAN_VALUE_THEOREM_FULL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_COMPONENTWISE]) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_CMUL; integrable_on] THEN
    MESON_TAC[]]);;

let INTEGRABLE_INCREASING_PRODUCT_UNIV = prove
 (`!f:real^1->real^N g B.
        f integrable_on (:real^1) /\
        (!x y. drop x <= drop y ==> g x <= g y) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x % f x) integrable_on (:real^1)`,
  let lemma = prove
   (`!f:real^1->real^1 g B.
          f integrable_on (:real^1) /\
          (!x y. drop x <= drop y ==> g x <= g y) /\
          (!x. abs(g x) <= B)
           ==> (\x. g x % f x) integrable_on (:real^1)`,
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[INTEGRABLE_ALT_SUBSET] THEN
    REWRITE_TAC[IN_UNIV; ETA_AX] THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
      ASM_SIMP_TAC[];
      DISCH_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / (&8 * abs B + &8)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &8 * abs B + &8`] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(ball(vec 0:real^1,C) = {})` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[BALL_EQ_EMPTY; REAL_NOT_LE]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `c:real^1`; `d:real^1`] THEN
    STRIP_TAC THEN SUBGOAL_THEN
     `~(interval[a:real^1,b] = {}) /\ ~(interval[c:real^1,d] = {})`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL_1]) THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`\x. g x % (f:real^1->real^1) x`;
                   `c:real^1`; `b:real^1`; `a:real^1`] INTEGRAL_COMBINE) THEN
    MP_TAC(ISPECL [`\x. g x % (f:real^1->real^1) x`;
                   `c:real^1`; `d:real^1`; `b:real^1`] INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_NOT_LE; NORM_ARITH
     `norm(ab - ((ca + ab) + bd):real^1) = norm(ca + bd)`] THEN
    MP_TAC(ISPECL[`f:real^1->real^1`; `g:real^1->real`; `c:real^1`; `a:real^1`]
          SECOND_MEAN_VALUE_THEOREM) THEN
    ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL[`f:real^1->real^1`; `g:real^1->real`; `b:real^1`; `d:real^1`]
          SECOND_MEAN_VALUE_THEOREM) THEN
    ASM_SIMP_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^1` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!x y. drop y <= drop a
            ==> norm(integral (interval[x,y]) (f:real^1->real^1))
                < e / (&4 * abs B + &4)`
     (LABEL_TAC "L")
    THENL
     [REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `drop x <= drop y` THENL
       [FIRST_X_ASSUM(fun th ->
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `y:real^1`; `b:real^1`] th) THEN
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `x:real^1`; `b:real^1`] th)) THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`f:real^1->real^1`; `x:real^1`; `b:real^1`; `y:real^1`]
          INTEGRAL_COMBINE) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC(NORM_ARITH
         `&2 * d = e
          ==> norm(ab - (xy + yb)) < d
              ==> norm(ab - yb) < d
                  ==> norm(xy:real^1) < e`) THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN `interval[x:real^1,y] = {}` SUBST1_TAC THENL
         [REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[INTEGRAL_EMPTY; NORM_0] THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x y. drop b <= drop x
            ==> norm(integral (interval[x,y]) (f:real^1->real^1))
                < e / (&4 * abs B + &4)`
     (LABEL_TAC "R")
    THENL
     [REPEAT STRIP_TAC THEN
      ASM_CASES_TAC `drop x <= drop y` THENL
       [FIRST_X_ASSUM(fun th ->
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `a:real^1`; `x:real^1`] th) THEN
         MP_TAC(SPECL[`a:real^1`; `b:real^1`; `a:real^1`; `y:real^1`] th)) THEN
        ASM_REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `y:real^1`; `x:real^1`]
          INTEGRAL_COMBINE) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC(NORM_ARITH
         `&2 * d = e
          ==> norm(ab - (ax + xy)) < d
              ==> norm(ab - ax) < d
                  ==> norm(xy:real^1) < e`) THEN
        CONV_TAC REAL_FIELD;
        SUBGOAL_THEN `interval[x:real^1,y] = {}` SUBST1_TAC THENL
         [REWRITE_TAC[INTERVAL_EQ_EMPTY_1] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[INTEGRAL_EMPTY; NORM_0] THEN
          MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `&4 * B * e / (&4 * abs B + &4)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `(norm a <= e /\ norm b <= e) /\ (norm c <= e /\ norm d <= e)
        ==> norm((a + b) + (c + d):real^1) <= &4 * e`) THEN
      REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REMOVE_THEN "L" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        REMOVE_THEN "R" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH
       `&4 * B * e / y < e <=> e * (&4 * B) / y < e * &1`] THEN
      ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < &4 * abs B + &4`] THEN
      REAL_ARITH_TAC]) in
  GEN_TAC THEN ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_CMUL] THEN
  MATCH_MP_TAC lemma THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[]);;

let INTEGRABLE_INCREASING = prove
 (`!f:real^1->real^N a b.
        (!x y i. x IN interval[a,b] /\ y IN interval[a,b] /\
                 drop x <= drop y /\ 1 <= i /\ i <= dimindex(:N)
                 ==> f(x)$i <= f(y)$i)
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INTEGRABLE_COMPONENTWISE] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_NUM] THEN
  MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
  ASM_SIMP_TAC[INTEGRABLE_CONST]);;

let INTEGRABLE_INCREASING_1 = prove
 (`!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_INCREASING THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

let INTEGRABLE_DECREASING_PRODUCT = prove
 (`!f:real^1->real^N g a b.
        f integrable_on interval[a,b] /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> g(y) <= g(x))
        ==> (\x. g(x) % f(x)) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x % y:real^N = --(--x % y)`] THEN
  MATCH_MP_TAC INTEGRABLE_NEG THEN
  MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2]);;

let INTEGRABLE_DECREASING_PRODUCT_UNIV = prove
 (`!f:real^1->real^N g B.
        f integrable_on (:real^1) /\
        (!x y. drop x <= drop y ==> g y <= g x) /\
        (!x. abs(g x) <= B)
         ==> (\x. g x % f x) integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x % y:real^N = --(--x % y)`] THEN
  MATCH_MP_TAC INTEGRABLE_NEG THEN
  MATCH_MP_TAC INTEGRABLE_INCREASING_PRODUCT_UNIV THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[REAL_LE_NEG2; REAL_ABS_NEG]);;

let INTEGRABLE_DECREASING = prove
 (`!f:real^1->real^N a b.
        (!x y i. x IN interval[a,b] /\ y IN interval[a,b] /\
                 drop x <= drop y /\ 1 <= i /\ i <= dimindex(:N)
                 ==> f(y)$i <= f(x)$i)
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [GSYM VECTOR_NEG_NEG] THEN
  MATCH_MP_TAC INTEGRABLE_NEG THEN MATCH_MP_TAC INTEGRABLE_INCREASING THEN
  ASM_SIMP_TAC[VECTOR_NEG_COMPONENT; REAL_LE_NEG2]);;

let INTEGRABLE_DECREASING_1 = prove
 (`!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> f integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_DECREASING THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  ASM_SIMP_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop]);;

(* ------------------------------------------------------------------------- *)
(* Bounded variation and variation function, for real^1->real^N functions.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_bounded_variation_on",(12,"right"));;

let has_bounded_variation_on = new_definition
 `(f:real^1->real^N) has_bounded_variation_on s <=>
        (\k. f(interval_upperbound k) - f(interval_lowerbound k))
        has_bounded_setvariation_on s`;;

let vector_variation = new_definition
 `vector_variation s (f:real^1->real^N) =
  set_variation s (\k. f(interval_upperbound k) - f(interval_lowerbound k))`;;

let HAS_BOUNDED_VARIATION_ON_EQ = prove
 (`!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x) /\ f has_bounded_variation_on s
        ==> g has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_BOUNDED_SETVARIATION_ON_EQ) THEN
  SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
           GSYM INTERVAL_NE_EMPTY] THEN
  ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET]);;

let VECTOR_VARIATION_EQ = prove
 (`!f g:real^1->real^N s.
        (!x. x IN s ==> f x = g x)
        ==> vector_variation s f = vector_variation s g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  MATCH_MP_TAC SET_VARIATION_EQ THEN
  SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
           GSYM INTERVAL_NE_EMPTY] THEN
  ASM_MESON_TAC[ENDS_IN_INTERVAL; SUBSET]);;

let HAS_BOUNDED_VARIATION_ON_COMPONENTWISE = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s <=>
        !i. 1 <= i /\ i <= dimindex(:N)
            ==> (\x. lift(f x$i)) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_BOUNDED_SETVARIATION_ON_COMPONENTWISE] THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; LIFT_SUB]);;

let VARIATION_EQUAL_LEMMA = prove
 (`!ms ms'.
        (!s. ms'(ms s) = s /\ ms(ms' s) = s) /\
        (!d t. d division_of t
               ==> (IMAGE (IMAGE ms) d) division_of IMAGE ms t /\
                   (IMAGE (IMAGE ms') d) division_of IMAGE ms' t) /\
        (!a b. ~(interval[a,b] = {})
               ==> IMAGE ms' (interval [a,b]) = interval[ms' a,ms' b] \/
                   IMAGE ms' (interval [a,b]) = interval[ms' b,ms' a])
   ==> (!f:real^1->real^N s.
            (\x. f(ms' x)) has_bounded_variation_on (IMAGE ms s) <=>
            f has_bounded_variation_on s) /\
       (!f:real^1->real^N s.
            vector_variation (IMAGE ms s) (\x. f(ms' x)) =
            vector_variation s f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `f:real^1->real^N` THEN
  MP_TAC(ISPECL
   [`\f k. (f:(real^1->bool)->real^N) (IMAGE (ms':real^1->real^1) k)`;
    `IMAGE (ms:real^1->real^1)`;
    `IMAGE (ms':real^1->real^1)`]
  SETVARIATION_EQUAL_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; IMAGE_SUBSET] THEN
    MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [AND_FORALL_THM] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `\k. (f:real^1->real^N) (interval_upperbound k) -
                     f (interval_lowerbound k)` th)) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `s:real^1->bool` THEN
  REWRITE_TAC[has_bounded_setvariation_on; set_variation] THEN
  CONJ_TAC THENL
   [REPLICATE_TAC 3 (AP_TERM_TAC THEN ABS_TAC) THEN
    REWRITE_TAC[TAUT `((p ==> q) <=> (p ==> r)) <=> p ==> (q <=> r)`] THEN
    STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC;
    AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. P x ==> f x = g x) ==> {f x | P x} = {g x | P x}`) THEN
    GEN_TAC THEN STRIP_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
   GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `IMAGE f s = s' ==> ~(s = {}) ==> IMAGE f s = s' /\ ~(s' = {})`)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
  NORM_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ON_SUBSET = prove
 (`!f:real^1->real^N s t.
        f has_bounded_variation_on s /\ t SUBSET s
        ==> f has_bounded_variation_on t`,
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_SUBSET; has_bounded_variation_on]);;

let HAS_BOUNDED_VARIATION_ON_CONST = prove
 (`!s c:real^N. (\x. c) has_bounded_variation_on s`,
  REWRITE_TAC[has_bounded_variation_on; VECTOR_SUB_REFL;
              HAS_BOUNDED_SETVARIATION_ON_0]);;

let VECTOR_VARIATION_CONST = prove
 (`!s c:real^N. vector_variation s (\x. c) = &0`,
  REWRITE_TAC[vector_variation; VECTOR_SUB_REFL; SET_VARIATION_0]);;

let HAS_BOUNDED_VARIATION_ON_CMUL = prove
 (`!f:real^1->real^N c s.
        f has_bounded_variation_on s
        ==> (\x. c % f x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; HAS_BOUNDED_SETVARIATION_ON_CMUL]);;

let HAS_BOUNDED_VARIATION_ON_NEG = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (\x. --f x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[VECTOR_ARITH `--a - --b:real^N = --(a - b)`;
              HAS_BOUNDED_SETVARIATION_ON_NEG]);;

let HAS_BOUNDED_VARIATION_ON_ADD = prove
 (`!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> (\x. f x + g x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[VECTOR_ARITH `(f + g) - (f' + g'):real^N = (f - f') + (g - g')`;
              HAS_BOUNDED_SETVARIATION_ON_ADD]);;

let HAS_BOUNDED_VARIATION_ON_SUB = prove
 (`!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> (\x. f x - g x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[VECTOR_ARITH `(f - g) - (f' - g'):real^N = (f - f') - (g - g')`;
              HAS_BOUNDED_SETVARIATION_ON_SUB]);;

let HAS_BOUNDED_VARIATION_ON_COMPOSE_LINEAR = prove
 (`!f:real^1->real^M g:real^M->real^N s.
        f has_bounded_variation_on s /\ linear g
        ==> (g o f) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  SIMP_TAC[o_THM; GSYM LINEAR_SUB] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_SETVARIATION_ON_COMPOSE_LINEAR) THEN
  REWRITE_TAC[o_DEF]);;

let HAS_BOUNDED_VARIATION_ON_NULL = prove
 (`!f:real^1->real^N s.
        content s = &0 /\ bounded s ==> f has_bounded_variation_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC HAS_BOUNDED_SETVARIATION_ON_NULL THEN
  ASM_SIMP_TAC[INTERVAL_BOUNDS_NULL_1; VECTOR_SUB_REFL]);;

let HAS_BOUNDED_VARIATION_ON_EMPTY = prove
 (`!f:real^1->real^N. f has_bounded_variation_on {}`,
  MESON_TAC[CONTENT_EMPTY; BOUNDED_EMPTY; HAS_BOUNDED_VARIATION_ON_NULL]);;

let HAS_BOUNDED_VARIATION_ON_NORM = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> (\x. lift(norm(f x))) has_bounded_variation_on s`,
  REWRITE_TAC[has_bounded_variation_on; has_bounded_setvariation_on] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC SUM_LE THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; LIFT_DROP; DROP_SUB] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; NORM_ARITH_TAC]);;

let HAS_BOUNDED_VARIATION_ON_MAX = prove
 (`!f g s. f has_bounded_variation_on s /\ g has_bounded_variation_on s
           ==> (\x. lift(max (drop(f x)) (drop(g x))))
               has_bounded_variation_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `max a b = inv(&2) * (a + b + abs(a - b))`] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_DROP; GSYM DROP_SUB] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_CMUL THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NORM THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN ASM_REWRITE_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_MIN = prove
 (`!f g s. f has_bounded_variation_on s /\ g has_bounded_variation_on s
           ==> (\x. lift(min (drop(f x)) (drop(g x))))
               has_bounded_variation_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `min a b = inv(&2) * ((a + b) - abs(a - b))`] THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_ADD; LIFT_DROP; LIFT_SUB; GSYM DROP_SUB] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_CMUL THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
  ASM_SIMP_TAC[HAS_BOUNDED_VARIATION_ON_ADD] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NORM THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN ASM_REWRITE_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s
        ==> bounded { f(d) - f(c) | interval[c,d] SUBSET s /\
                                    ~(interval[c,d] = {})}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   HAS_BOUNDED_SETVARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
  MAP_EVERY X_GEN_TAC [`d:real^1`; `c:real^1`] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`c:real^1`; `d:real^1`] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1]);;

let HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL = prove
 (`!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> bounded(IMAGE f (interval[a,b]))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_SUBINTERVALS) THEN
  REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B + norm((f:real^1->real^N) a)` THEN
  ASM_SIMP_TAC[NORM_ARITH `&0 < B ==> &0 < B + norm(x:real^N)`] THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `a:real^1`]) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; NORM_ARITH_TAC]);;

let HAS_BOUNDED_VARIATION_ON_MUL = prove
 (`!f g:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. drop(f x) % g x) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
    `bounded(IMAGE (f:real^1->real^1) (interval[a,b])) /\
     bounded(IMAGE (g:real^1->real^N) (interval[a,b]))`
  MP_TAC THENL
   [ASM_SIMP_TAC[HAS_BOUNDED_VARIATION_ON_IMP_BOUNDED_ON_INTERVAL];
    REWRITE_TAC[BOUNDED_POS_LT; FORALL_IN_IMAGE]] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC) THEN
  REWRITE_TAC[HAS_BOUNDED_SETVARIATION_ON_INTERVAL;
              has_bounded_variation_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (LABEL_TAC "G")) THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real` (LABEL_TAC "F")) THEN
  EXISTS_TAC `B1 * C2 + B2 * C1:real` THEN
  X_GEN_TAC `d:(real^1->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `B1 * sum d (\k. norm((g:real^1->real^N)(interval_upperbound k) -
                         g(interval_lowerbound k))) +
    B2 * sum d (\k. norm((f:real^1->real^1)(interval_upperbound k) -
                         f(interval_lowerbound k)))` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_SIMP_TAC[REAL_LE_LMUL_EQ]] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
   `f' % g' - f % g:real^N = f' % (g' - g) + (f' - f) % g`] THEN
  MATCH_MP_TAC(NORM_ARITH
    `norm x <= a /\ norm y <= b ==> norm(x + y) <= a + b`) THEN
  REWRITE_TAC[NORM_MUL; NORM_REAL] THEN
  REWRITE_TAC[drop; GSYM NORM_REAL; GSYM VECTOR_SUB_COMPONENT] THEN
  SUBGOAL_THEN `~(interval[u:real^1,v] = {})` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1; GSYM REAL_NOT_LE] THEN
  STRIP_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let VECTOR_VARIATION_POS_LE = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on s ==> &0 <= vector_variation s f`,
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  REWRITE_TAC[SET_VARIATION_POS_LE]);;

let VECTOR_VARIATION_GE_NORM_FUNCTION = prove
 (`!f:real^1->real^N s a b.
        f has_bounded_variation_on s /\
        interval [a,b] SUBSET s /\ ~(interval [a,b] = {})
        ==> norm(f b - f a) <= vector_variation s f`,
  REWRITE_TAC[has_bounded_variation_on] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
  [`\k. (f:real^1->real^N)(interval_upperbound k) - f(interval_lowerbound k)`;
   `s:real^1->bool`; `a:real^1`; `b:real^1`] SET_VARIATION_GE_FUNCTION) THEN
  ASM_REWRITE_TAC[vector_variation] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1]);;

let VECTOR_VARIATION_GE_DROP_FUNCTION = prove
 (`!f s a b.
        f has_bounded_variation_on s /\
        interval [a,b] SUBSET s /\ ~(interval [a,b] = {})
        ==> drop(f b) - drop(f a) <= vector_variation s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((f:real^1->real^1) b - f a)` THEN
  ASM_SIMP_TAC[VECTOR_VARIATION_GE_NORM_FUNCTION] THEN
  REWRITE_TAC[NORM_REAL; DROP_SUB; GSYM drop] THEN REAL_ARITH_TAC);;

let VECTOR_VARIATION_MONOTONE = prove
 (`!f s t. f has_bounded_variation_on s /\ t SUBSET s
           ==> vector_variation t f <= vector_variation s f`,
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  REWRITE_TAC[SET_VARIATION_MONOTONE]);;

let VECTOR_VARIATION_NEG = prove
 (`!f:real^1->real^N s.
        vector_variation s (\x. --(f x)) = vector_variation s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_variation; set_variation] THEN
  REWRITE_TAC[NORM_ARITH `norm(--x - --y:real^N) = norm(x - y)`]);;

let VECTOR_VARIATION_TRIANGLE = prove
 (`!f g:real^1->real^N s.
        f has_bounded_variation_on s /\ g has_bounded_variation_on s
        ==> vector_variation s (\x. f x + g x)
              <= vector_variation s f + vector_variation s g`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SET_VARIATION_TRIANGLE) THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b) - (c + d):real^N = (a - c) + (b - d)`]);;

let OPERATIVE_FUNCTION_ENDPOINT_DIFF = prove
 (`!f:real^1->real^N.
    operative (+) (\k. f (interval_upperbound k) - f (interval_lowerbound k))`,
  GEN_TAC THEN
  SIMP_TAC[operative; INTERVAL_BOUNDS_NULL_1; VECTOR_SUB_REFL] THEN
  REWRITE_TAC[NEUTRAL_VECTOR_ADD; DIMINDEX_1; FORALL_1; GSYM drop] THEN
  REWRITE_TAC[FORALL_DROP] THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`; `c:real^1`] THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THENL
   [ASM_REWRITE_TAC[INTER_EMPTY; INTERVAL_BOUNDS_EMPTY_1] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a,b] INTER {x | drop x <= drop c} = {}` THENL
   [ASM_REWRITE_TAC[INTERVAL_BOUNDS_EMPTY_1; VECTOR_SUB_REFL] THEN
    SUBGOAL_THEN `interval[a,b] INTER {x | drop x >= drop c} = interval[a,b]`
     (fun th -> REWRITE_TAC[th; VECTOR_ADD_LID]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `i INTER s = {} ==> s UNION t = UNIV ==> i INTER t = i`)) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `interval[a,b] INTER {x | drop x >= drop c} = {}` THENL
   [ASM_REWRITE_TAC[INTERVAL_BOUNDS_EMPTY_1; VECTOR_SUB_REFL] THEN
    SUBGOAL_THEN `interval[a,b] INTER {x | drop x <= drop c} = interval[a,b]`
     (fun th -> REWRITE_TAC[th; VECTOR_ADD_RID]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `i INTER s = {} ==> s UNION t = UNIV ==> i INTER t = i`)) THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SIMP_TAC[INTERVAL_SPLIT; drop; DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
  SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1] THEN
  SIMP_TAC[drop; LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN STRIP_TAC THEN
  MATCH_MP_TAC(VECTOR_ARITH
   `fx:real^N = fy ==> fb - fa = fx - fa + fb - fy`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ; drop] THEN
  SIMP_TAC[LAMBDA_BETA; DIMINDEX_1; LE_REFL] THEN ASM_REAL_ARITH_TAC);;

let OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF = prove
 (`!f:real^1->real.
    operative (+) (\k. f (interval_upperbound k) - f (interval_lowerbound k))`,
  GEN_TAC THEN
  MP_TAC(ISPEC `lift o (f:real^1->real)` OPERATIVE_FUNCTION_ENDPOINT_DIFF) THEN
  REWRITE_TAC[operative; NEUTRAL_REAL_ADD; NEUTRAL_VECTOR_ADD] THEN
  REWRITE_TAC[o_THM; GSYM LIFT_SUB; GSYM LIFT_ADD; GSYM LIFT_NUM] THEN
  REWRITE_TAC[LIFT_EQ]);;

let OPERATIVE_LIFTED_VECTOR_VARIATION = prove
 (`!f:real^1->real^N.
        operative (lifted(+))
                  (\i. if f has_bounded_variation_on i
                       then SOME(vector_variation i f) else NONE)`,
  GEN_TAC THEN REWRITE_TAC[has_bounded_variation_on; vector_variation] THEN
  MATCH_MP_TAC OPERATIVE_LIFTED_SETVARIATION THEN
  REWRITE_TAC[OPERATIVE_FUNCTION_ENDPOINT_DIFF]);;

let HAS_BOUNDED_VARIATION_ON_DIVISION = prove
 (`!f:real^1->real^N a b d.
        d division_of interval[a,b]
        ==> ((!k. k IN d ==> f has_bounded_variation_on k) <=>
             f has_bounded_variation_on interval[a,b])`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC HAS_BOUNDED_SETVARIATION_ON_DIVISION THEN
  ASM_REWRITE_TAC[OPERATIVE_FUNCTION_ENDPOINT_DIFF]);;

let VECTOR_VARIATION_ON_DIVISION = prove
 (`!f:real^1->real^N a b d.
        d division_of interval[a,b] /\
        f has_bounded_variation_on interval[a,b]
        ==> sum d (\k. vector_variation k f) =
            vector_variation (interval[a,b]) f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  MATCH_MP_TAC SET_VARIATION_ON_DIVISION THEN
  ASM_REWRITE_TAC[OPERATIVE_FUNCTION_ENDPOINT_DIFF; GSYM
                  has_bounded_variation_on]);;

let HAS_BOUNDED_VARIATION_ON_COMBINE = prove
 (`!f:real^1->real^N a b c.
        drop a <= drop c /\ drop c <= drop b
        ==> (f has_bounded_variation_on interval[a,b] <=>
             f has_bounded_variation_on interval[a,c] /\
             f has_bounded_variation_on interval[c,b])`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `f:real^1->real^N` OPERATIVE_LIFTED_VECTOR_VARIATION) THEN
  REWRITE_TAC[operative; FORALL_1; FORALL_DROP; DIMINDEX_1] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`; `c:real^1`] o
   CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `interval[a,b] INTER {x:real^1 | x$1 <= drop c} = interval[a,c] /\
    interval[a,b] INTER {x:real^1 | x$1 >= drop c} = interval[c,b]`
   (fun th -> REWRITE_TAC[th])
  THENL
   [SIMP_TAC[EXTENSION; IN_INTER; GSYM drop; IN_INTERVAL_1; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[distinctness "option"; lifted])]);;

let VECTOR_VARIATION_COMBINE = prove
 (`!f:real^1->real^N a b c.
        drop a <= drop c /\
        drop c <= drop b /\
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,c]) f +
            vector_variation (interval[c,b]) f =
            vector_variation (interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `f:real^1->real^N` OPERATIVE_LIFTED_VECTOR_VARIATION) THEN
  REWRITE_TAC[operative; FORALL_1; FORALL_DROP; DIMINDEX_1] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`; `c:real^1`] o
   CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN REPEAT(COND_CASES_TAC THENL
    [ALL_TAC;
     ASM_MESON_TAC[HAS_BOUNDED_VARIATION_ON_SUBSET; INTER_SUBSET]]) THEN
  REWRITE_TAC[lifted; injectivity "option"] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_1; LE_REFL] THEN
  BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[EXTENSION; IN_INTERVAL_1; drop; LAMBDA_BETA;
           DIMINDEX_1; LE_REFL] THEN
  REWRITE_TAC[GSYM drop] THEN ASM_REAL_ARITH_TAC);;

let VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE = prove
 (`!f a b c d.
        f has_bounded_variation_on interval[a,b] /\
        interval[c,d] SUBSET interval[a,b] /\ ~(interval[c,d] = {})
        ==> vector_variation (interval[c,d]) f - drop(f d - f c) <=
            vector_variation (interval[a,b]) f - drop(f b - f a)`,
  REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1; REAL_NOT_LT] THEN
  REPEAT STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `drop(f c) - drop(f a) <= vector_variation(interval[a,c]) f /\
    drop(f b) - drop(f d) <= vector_variation(interval[d,b]) f`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_GE_DROP_FUNCTION THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN
    (CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[DROP_SUB] THEN
  MP_TAC(ISPEC `f:real^1->real^1` VECTOR_VARIATION_COMBINE) THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL [`a:real^1`; `b:real^1`; `d:real^1`] th) THEN
    MP_TAC(SPECL [`a:real^1`; `d:real^1`; `c:real^1`] th)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let INCREASING_BOUNDED_VARIATION = prove
 (`!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> f has_bounded_variation_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_EMPTY] THEN
  REWRITE_TAC[has_bounded_variation_on;
              HAS_BOUNDED_SETVARIATION_ON_INTERVAL] THEN
  EXISTS_TAC `drop(f b) - drop(f(a:real^1))` THEN
  MP_TAC(MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
   OPERATIVE_DIVISION) (SPEC `drop o (f:real^1->real^1)`
      OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF)) THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[GSYM sum; MONOIDAL_REAL_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[o_THM; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[u:real^1,v] = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[DROP_SUB; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(y - x) = y - x`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; REWRITE_TAC[SUBSET_INTERVAL_1]] THEN
  ASM_REAL_ARITH_TAC);;

let DECREASING_BOUNDED_VARIATION = prove
 (`!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
         ==> f has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV)
   [GSYM REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM DROP_NEG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INCREASING_BOUNDED_VARIATION) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_ON_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let INCREASING_VECTOR_VARIATION = prove
 (`!f a b.
        ~(interval[a,b] = {}) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> vector_variation (interval[a,b]) f = drop(f b) - drop(f a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_variation] THEN
  REWRITE_TAC[SET_VARIATION_ON_INTERVAL] THEN
  SUBGOAL_THEN
   `{sum d (\k. norm (f (interval_upperbound k) - f (interval_lowerbound k))) |
     d division_of interval[a:real^1,b]} =
    {drop (f b) - drop(f a)}`
   (fun th -> SIMP_TAC[SUP_INSERT_FINITE; FINITE_EMPTY; th]) THEN
  MATCH_MP_TAC(SET_RULE
   `(?x. P x) /\ (!x. P x ==> f x = a) ==> {f x | P x} = {a}`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[DIVISION_OF_SELF]; ALL_TAC] THEN
  MP_TAC(MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c ==> d <=> b ==> a /\ c ==> d`]
   OPERATIVE_DIVISION) (SPEC `drop o (f:real^1->real^1)`
      OPERATIVE_REAL_FUNCTION_ENDPOINT_DIFF)) THEN
   MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[GSYM sum; MONOIDAL_REAL_ADD] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[o_THM; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[u:real^1,v] = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[DROP_SUB; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> abs(y - x) = y - x`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  SUBGOAL_THEN `interval[u:real^1,v] SUBSET interval[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[division_of]; REWRITE_TAC[SUBSET_INTERVAL_1]] THEN
  ASM_REAL_ARITH_TAC);;

let DECREASING_VECTOR_VARIATION = prove
 (`!f a b.
        ~(interval[a,b] = {}) /\
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x))
        ==> vector_variation (interval[a,b]) f = drop(f a) - drop(f b)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC
   (LAND_CONV o RAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV)
   [GSYM REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM DROP_NEG] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INCREASING_VECTOR_VARIATION) THEN
  SIMP_TAC[VECTOR_VARIATION_NEG; DROP_NEG] THEN
  DISCH_TAC THEN REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_TRANSLATION2_EQ,VECTOR_VARIATION_TRANSLATION2 =
 (CONJ_PAIR o prove)
 (`(!a f:real^1->real^N s.
        (\x. f(a + x)) has_bounded_variation_on (IMAGE (\x. --a + x) s) <=>
        f has_bounded_variation_on s) /\
   (!a f:real^1->real^N s.
        vector_variation (IMAGE (\x. --a + x) s) (\x. f(a + x)) =
        vector_variation s f)`,
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `a:real^1` THEN
  MATCH_MP_TAC VARIATION_EQUAL_LEMMA THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIVISION_OF_TRANSLATION; GSYM INTERVAL_TRANSLATION]);;

let HAS_BOUNDED_VARIATION_AFFINITY2_EQ,VECTOR_VARIATION_AFFINITY2 =
 (CONJ_PAIR o prove)
 (`(!m c f:real^1->real^N s.
        (\x. f (m % x + c)) has_bounded_variation_on
        IMAGE (\x. inv m % x + --(inv m % c)) s <=>
        m = &0 \/ f has_bounded_variation_on s) /\
   (!m c f:real^1->real^N s.
        vector_variation (IMAGE (\x. inv m % x + --(inv m % c)) s)
                         (\x. f (m % x + c)) =
        if m = &0 then &0 else vector_variation s f)`,
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `m:real` THEN
  GEN_REWRITE_TAC I [AND_FORALL_THM] THEN X_GEN_TAC `c:real^1` THEN
  ASM_CASES_TAC `m = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; HAS_BOUNDED_VARIATION_ON_CONST] THEN
    REWRITE_TAC[VECTOR_VARIATION_CONST];
    MATCH_MP_TAC VARIATION_EQUAL_LEMMA THEN
    ASM_SIMP_TAC[REWRITE_RULE[FUN_EQ_THM; o_DEF] AFFINITY_INVERSES; I_THM] THEN
    ASM_SIMP_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    ASM_REWRITE_TAC[DIVISION_OF_AFFINITY; REAL_INV_EQ_0] THEN
    MESON_TAC[]]);;

let HAS_BOUNDED_VARIATION_AFFINITY_EQ,VECTOR_VARIATION_AFFINITY =
 (CONJ_PAIR o prove)
 (`(!m c f:real^1->real^N s.
        (\x. f(m % x + c)) has_bounded_variation_on s <=>
        m = &0 \/ f has_bounded_variation_on (IMAGE (\x. m % x + c) s)) /\
   (!m c f:real^1->real^N s.
        vector_variation s (\x. f(m % x + c)) =
        if m = &0 then &0 else vector_variation (IMAGE (\x. m % x + c) s) f)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; HAS_BOUNDED_VARIATION_ON_CONST;
                  VECTOR_VARIATION_CONST] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL[`m:real`; `c:real^1`; `f:real^1->real^N`;
                  `IMAGE (\x:real^1. m % x + c) s`]
          HAS_BOUNDED_VARIATION_AFFINITY2_EQ);
    MP_TAC(ISPECL[`m:real`; `c:real^1`; `f:real^1->real^N`;
                  `IMAGE (\x:real^1. m % x + c) s`]
          VECTOR_VARIATION_AFFINITY2)] THEN
  ASM_SIMP_TAC[AFFINITY_INVERSES; GSYM IMAGE_o; IMAGE_I]);;

let HAS_BOUNDED_VARIATION_TRANSLATION_EQ,VECTOR_VARIATION_TRANSLATION =
 (CONJ_PAIR o prove)
 (`(!a f:real^1->real^N s.
        (\x. f(a + x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on (IMAGE (\x. a + x) s)) /\
   (!a f:real^1->real^N s.
        vector_variation s (\x. f(a + x)) =
        vector_variation (IMAGE (\x. a + x) s) f)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL[`a:real^1`; `f:real^1->real^N`; `IMAGE (\x:real^1. a + x) s`]
          HAS_BOUNDED_VARIATION_TRANSLATION2_EQ);
    MP_TAC(ISPECL[`a:real^1`; `f:real^1->real^N`; `IMAGE (\x:real^1. a + x) s`]
          VECTOR_VARIATION_TRANSLATION2)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[IMAGE_ID; VECTOR_ARITH `--a + a + x:real^N = x`;
              VECTOR_ARITH `a + --a + x:real^N = x`]);;

let HAS_BOUNDED_VARIATION_TRANSLATION_EQ_INTERVAL,
    VECTOR_VARIATION_TRANSLATION_INTERVAL =
 (CONJ_PAIR o prove)
 (`(!a f:real^1->real^N u v.
        (\x. f(a + x)) has_bounded_variation_on interval[u,v] <=>
        f has_bounded_variation_on interval[a+u,a+v]) /\
   (!a f:real^1->real^N u v.
        vector_variation (interval[u,v]) (\x. f(a + x)) =
        vector_variation (interval[a+u,a+v]) f)`,
  REWRITE_TAC[INTERVAL_TRANSLATION; HAS_BOUNDED_VARIATION_TRANSLATION_EQ;
              VECTOR_VARIATION_TRANSLATION]);;

let HAS_BOUNDED_VARIATION_TRANSLATION = prove
 (`!f:real^1->real^N s a.
        f has_bounded_variation_on s
        ==> (\x. f(a + x)) has_bounded_variation_on (IMAGE (\x. --a + x) s)`,
  REWRITE_TAC[HAS_BOUNDED_VARIATION_TRANSLATION2_EQ]);;

let HAS_BOUNDED_VARIATION_REFLECT2_EQ,VECTOR_VARIATION_REFLECT2 =
 (CONJ_PAIR o prove)
 (`(!f:real^1->real^N s.
        (\x. f(--x)) has_bounded_variation_on (IMAGE (--) s) <=>
        f has_bounded_variation_on s) /\
   (!f:real^1->real^N s.
        vector_variation (IMAGE (--) s) (\x. f(--x)) =
        vector_variation s f)`,
  MATCH_MP_TAC VARIATION_EQUAL_LEMMA THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIVISION_OF_REFLECT; REFLECT_INTERVAL]);;

let HAS_BOUNDED_VARIATION_REFLECT_EQ,VECTOR_VARIATION_REFLECT =
 (CONJ_PAIR o prove)
 (`(!f:real^1->real^N s.
        (\x. f(--x)) has_bounded_variation_on s <=>
        f has_bounded_variation_on (IMAGE (--) s)) /\
   (!f:real^1->real^N s.
        vector_variation s (\x. f(--x)) =
        vector_variation (IMAGE (--) s) f)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL[`f:real^1->real^N`; `IMAGE (--) (s:real^1->bool)`]
          HAS_BOUNDED_VARIATION_REFLECT2_EQ);
    MP_TAC(ISPECL[`f:real^1->real^N`; `IMAGE (--) (s:real^1->bool)`]
          VECTOR_VARIATION_REFLECT2)] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
  REWRITE_TAC[IMAGE_ID; VECTOR_NEG_NEG]);;

let HAS_BOUNDED_VARIATION_REFLECT_EQ_INTERVAL,
    VECTOR_VARIATION_REFLECT_INTERVAL =
 (CONJ_PAIR o prove)
 (`(!f:real^1->real^N u v.
        (\x. f(--x)) has_bounded_variation_on interval[u,v] <=>
        f has_bounded_variation_on interval[--v,--u]) /\
   (!f:real^1->real^N u v.
        vector_variation (interval[u,v]) (\x. f(--x)) =
        vector_variation (interval[--v,--u]) f)`,
  REWRITE_TAC[GSYM REFLECT_INTERVAL; HAS_BOUNDED_VARIATION_REFLECT_EQ;
              VECTOR_VARIATION_REFLECT]);;

let HAS_BOUNDED_VARIATION_DARBOUX = prove
 (`!f a b.
     f has_bounded_variation_on interval[a,b] <=>
     ?g h. (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                  ==> drop(g x) <= drop(g y)) /\
           (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
                  ==> drop(h x) <= drop(h y)) /\
           (!x. f x = g x - h x)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`\x:real^1. lift(vector_variation (interval[a,x]) (f:real^1->real^1))`;
      `\x:real^1. lift(vector_variation (interval[a,x]) f) - f x`] THEN
    REWRITE_TAC[VECTOR_ARITH `a - (a - x):real^1 = x`] THEN
    REWRITE_TAC[LIFT_DROP; DROP_SUB] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC VECTOR_VARIATION_MONOTONE;
      MATCH_MP_TAC(REAL_ARITH
       `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
      EXISTS_TAC `drop(f(a:real^1))` THEN
      REWRITE_TAC[GSYM DROP_SUB] THEN
      MATCH_MP_TAC VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE] THEN
    (CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET));
        ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN
      ASM_REAL_ARITH_TAC);
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC INCREASING_BOUNDED_VARIATION THEN
    ASM_REWRITE_TAC[]]);;

let HAS_BOUNDED_VARIATION_DARBOUX_STRICT = prove
 (`!f a b.
     f has_bounded_variation_on interval[a,b] <=>
     ?g h. (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                  ==> drop(g x) < drop(g y)) /\
           (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x < drop y
                  ==> drop(h x) < drop(h y)) /\
           (!x. f x = g x - h x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_BOUNDED_VARIATION_DARBOUX] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^1. g x + x`; `\x:real^1. h x + x`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(a + x) - (b + x):real^1 = a - b`] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[DROP_ADD] THEN
    MATCH_MP_TAC REAL_LET_ADD2 THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    MAP_EVERY EXISTS_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    ASM_REWRITE_TAC[REAL_LE_LT; DROP_EQ] THEN ASM_MESON_TAC[]]);;

let HAS_BOUNDED_VARIATION_COMPOSE_INCREASING = prove
 (`!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        g has_bounded_variation_on interval[f a,f b]
        ==> (g o f) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[HAS_BOUNDED_VARIATION_DARBOUX; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^1->real^1`; `k:real^1->real^1`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(h:real^1->real^1) o (f:real^1->real^1)`;
                        `(k:real^1->real^1) o (f:real^1->real^1)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ON_REFLECT = prove
 (`!f:real^1->real^N s.
        f has_bounded_variation_on IMAGE (--) s
        ==> (\x. f(--x)) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  REWRITE_TAC[has_bounded_setvariation_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`d:(real^1->bool)->bool`; `t:real^1->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`IMAGE (IMAGE (--)) (d:(real^1->bool)->bool)`;
    `IMAGE (--) (t:real^1->bool)`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_REFLECT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM SUBSET] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhand o lhand o snd) THEN
  ANTS_TAC THENL
   [MESON_TAC[VECTOR_ARITH `--x:real^N = --y <=> x = y`; INJECTIVE_IMAGE];
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= d ==> y <= d`) THEN
    MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTERVAL_NE_EMPTY_1; division_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; REFLECT_INTERVAL] THEN
    ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1;
                 DROP_NEG; REAL_LE_NEG2] THEN
    NORM_ARITH_TAC]);;

let HAS_BOUNDED_VARIATION_ON_REFLECT_INTERVAL = prove
 (`!f:real^1->real^N a b.
        f has_bounded_variation_on interval[--b,--a]
        ==> (\x. f(--x)) has_bounded_variation_on interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_REFLECT THEN
  ASM_REWRITE_TAC[REFLECT_INTERVAL]);;

let VECTOR_VARIATION_REFLECT = prove
 (`!f:real^1->real^N s.
        vector_variation s (\x. f(--x)) =
        vector_variation (IMAGE (--) s) f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_variation; set_variation] THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^1->bool)->bool`
   (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE (IMAGE (--)) (d:(real^1->bool)->bool)` THEN
  (CONJ_TAC THENL
    [EXISTS_TAC `IMAGE (--) (t:real^1->bool)` THEN
     ASM_SIMP_TAC[DIVISION_OF_REFLECT] THEN
     ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
     RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_IMAGE]) THEN
     ASM_MESON_TAC[VECTOR_NEG_NEG; IN_IMAGE];
     ALL_TAC]) THEN
  W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o rand o snd) THEN
  (ANTS_TAC THENL
   [MESON_TAC[VECTOR_ARITH `--x:real^N = --y <=> x = y`; INJECTIVE_IMAGE];
    DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC SUM_EQ THEN FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN DISCH_TAC THEN
  (SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERVAL_NE_EMPTY_1; division_of]; ALL_TAC]) THEN
  ASM_REWRITE_TAC[o_THM; REFLECT_INTERVAL] THEN
  ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1;
               DROP_NEG; REAL_LE_NEG2; VECTOR_NEG_NEG] THEN
  NORM_ARITH_TAC);;

let VECTOR_VARIATION_REFLECT_INTERVAL = prove
 (`!f:real^1->real^N a b.
        vector_variation (interval[a,b]) (\x. f(--x)) =
        vector_variation (interval[--b,--a]) f`,
  REWRITE_TAC[VECTOR_VARIATION_REFLECT; REFLECT_INTERVAL]);;

let HAS_BOUNDED_VARIATION_COMPOSE_DECREASING = prove
 (`!f g:real^1->real^N a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        g has_bounded_variation_on interval[f b,f a]
        ==> (g o f) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[VECTOR_NEG_NEG]
    (ISPECL [`f:real^1->real^N`; `--b:real^1`; `--a:real^1`]
        HAS_BOUNDED_VARIATION_ON_REFLECT_INTERVAL))) THEN
  POP_ASSUM MP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o BINDER_CONV o RAND_CONV)
   [GSYM REAL_LE_NEG2] THEN
  REWRITE_TAC[GSYM DROP_NEG; IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_BOUNDED_VARIATION_COMPOSE_INCREASING) THEN
  REWRITE_TAC[o_DEF; VECTOR_NEG_NEG]);;

let HAS_BOUNDED_VARIATION_ON_ID = prove
 (`!a b. (\x. x) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC INCREASING_BOUNDED_VARIATION THEN
  SIMP_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_LINEAR_IMAGE = prove
 (`!f:real^1->real^1 g:real^1->real^N a b.
        linear f /\ g has_bounded_variation_on IMAGE f (interval[a,b])
        ==> (g o f) has_bounded_variation_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LINEAR_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` SUBST_ALL_TAC) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH
   `c = &0 \/ &0 <= c /\ &0 < c \/ ~(&0 <= c) /\ &0 < --c`)
  THENL
   [ASM_REWRITE_TAC[o_DEF; VECTOR_MUL_LZERO; HAS_BOUNDED_VARIATION_ON_CONST];
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_COMPOSE_INCREASING THEN
    REWRITE_TAC[DROP_CMUL];
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_COMPOSE_DECREASING THEN
    REWRITE_TAC[DROP_CMUL] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `c * y <= c * x <=> --c * x <= --c * y`]] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(MESON[]
   `g has_bounded_variation_on s
    ==> s = t ==> g has_bounded_variation_on t`)) THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `c % x:real^N = c % x + vec 0`] THEN
  ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_RID] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_CMUL] THENL
   [ALL_TAC;
   ONCE_REWRITE_TAC[REAL_ARITH `c * y < c * x <=> --c * x < --c * y`]] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN
  ASM_REWRITE_TAC[GSYM INTERVAL_EQ_EMPTY_1]);;

let INCREASING_LEFT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[a,c])`,
  REPEAT STRIP_TAC THEN EXISTS_TAC
   `lift(sup {drop(f x) | x IN interval[a,b] /\ drop x < drop c})` THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[LIM_WITHIN] THEN
  REWRITE_TAC[DIST_REAL; GSYM drop] THEN
  ASM_CASES_TAC `{x | x IN interval[a,b] /\ drop x < drop c} = {}` THENL
   [GEN_TAC THEN DISCH_TAC THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
     `(a ==> ~b) ==> a ==> b ==> c`) THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM; IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `{drop(f x) | x IN interval[a,b] /\ drop x < drop c}` SUP) THEN
  ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN ASM_SIMP_TAC[IMAGE_EQ_EMPTY];
      EXISTS_TAC `drop(f(b:real^1))` THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC];
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[IMAGE_ID] THEN
    ABBREV_TAC `s = sup (IMAGE (\x. drop(f x))
                        {x | x IN interval[a,b] /\ drop x < drop c})` THEN
    REWRITE_TAC[LIFT_DROP] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `s - e:real`)) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> ~(s <= s - e)`; NOT_FORALL_THM] THEN
    REWRITE_TAC[NOT_IMP; REAL_NOT_LE; IN_INTERVAL_1] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `drop c - drop d` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`d:real^1`; `x:real^1`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REAL_ARITH_TAC]);;

let DECREASING_LEFT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[a,c])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. --((f:real^1->real^1) x)`; `a:real^1`; `b:real^1`; `c:real^1`]
        INCREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; DROP_NEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM LIM_NEG_EQ] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN MESON_TAC[]);;

let INCREASING_RIGHT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[c,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. (f:real^1->real^1) (--x)`;
                 `--b:real^1`; `--a:real^1`; `--c:real^1`]
        DECREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[IN_INTERVAL_REFLECT] THEN
  ONCE_REWRITE_TAC[MESON[VECTOR_NEG_NEG]
   `(!x:real^1 y:real^1. P x y) <=> (!x y. P (--x) (--y))`] THEN
  REWRITE_TAC[DROP_NEG; IN_INTERVAL_REFLECT; VECTOR_NEG_NEG] THEN
  ASM_SIMP_TAC[REAL_LE_NEG2] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `l:real^1` THEN REWRITE_TAC[LIM_WITHIN] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [MESON[VECTOR_NEG_NEG] `(!x:real^1. P x) <=> (!x. P (--x))`] THEN
  REWRITE_TAC[IN_INTERVAL_REFLECT; VECTOR_NEG_NEG;
              NORM_ARITH `dist(--x:real^1,--y) = dist(x,y)`]);;

let DECREASING_RIGHT_LIMIT_1 = prove
 (`!f a b c.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f y) <= drop(f x)) /\
        c IN interval[a,b]
       ==> ?l. (f --> l) (at c within interval[c,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. --((f:real^1->real^1) x)`; `a:real^1`; `b:real^1`; `c:real^1`]
        INCREASING_RIGHT_LIMIT_1) THEN
  ASM_REWRITE_TAC[REAL_LE_NEG2; DROP_NEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM LIM_NEG_EQ] THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX] THEN MESON_TAC[]);;

let HAS_BOUNDED_VECTOR_VARIATION_LEFT_LIMIT = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[a,c])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o SPEC `c:real^1` o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ] INCREASING_LEFT_LIMIT_1))) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l2:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `l1:real^1` THEN DISCH_TAC THEN
  EXISTS_TAC `l1 - l2:real^1` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  ASM_SIMP_TAC[LIM_SUB]);;

let HAS_BOUNDED_VECTOR_VARIATION_RIGHT_LIMIT = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ?l. (f --> l) (at c within interval[c,b])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; CONJ_ASSOC] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN DISCH_THEN(CONJUNCTS_THEN
   (MP_TAC o SPEC `c:real^1` o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ] INCREASING_RIGHT_LIMIT_1))) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `l2:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `l1:real^1` THEN DISCH_TAC THEN
  EXISTS_TAC `l1 - l2:real^1` THEN
  GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  ASM_SIMP_TAC[LIM_SUB]);;

let VECTOR_VARIATION_CONTINUOUS_LEFT = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[a,c]) <=>
            f continuous (at c within interval[a,c]))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[continuous_within] THEN
    REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `c:real^1`; `x:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `abs(a - (a + b)) = abs b`] THEN
    REWRITE_TAC[drop; GSYM NORM_REAL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN
    REWRITE_TAC[SUBSET_REFL; INTERVAL_EQ_EMPTY_1] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `c limit_point_of interval[a:real^1,c]` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[CONTINUOUS_WITHIN; LIM; TRIVIAL_LIMIT_WITHIN]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_LEFT_LIMIT_1) THEN
  MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `gc:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `hc:real^1` THEN DISCH_TAC THEN
  ABBREV_TAC `k = gc - (g:real^1->real^1) c` THEN
  SUBGOAL_THEN `hc - (h:real^1->real^1) c = k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `hc' - hc:real^1 = gc' - gc <=> gc' - hc' = gc - hc`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_WITHIN]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
      LIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    ASM_SIMP_TAC[LIM_SUB];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`g':real^1->real^1 = \x. if drop c <= drop x then g(x) + k else g(x)`;
    `h':real^1->real^1 = \x. if drop c <= drop x then h(x) + k else h(x)`] THEN
  SUBGOAL_THEN
   `(!x y. x IN interval[a,c] /\ y IN interval[a,c] /\ drop x <= drop y
           ==> drop(g' x) <= drop(g' y)) /\
    (!x y. x IN interval[a,c] /\ y IN interval[a,c] /\ drop x <= drop y
           ==> drop(h' x) <= drop(h' y))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    (ASM_CASES_TAC `drop c <= drop x` THENL
      [SUBGOAL_THEN `drop c <= drop y` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
       REWRITE_TAC[DROP_ADD; REAL_LE_RADD] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [ALL_TAC;
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC] THEN
     SUBGOAL_THEN `y:real^1 = c` SUBST_ALL_TAC THENL
      [REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
      `gc - g c = k
       ==> b <= drop(g c + (gc - g c)) ==> b <= drop(g c + k)`)) THEN
     REWRITE_TAC[VECTOR_ARITH `a + b - a:real^1 = b`] THEN
     MATCH_MP_TAC(ISPEC `at c within interval[a:real^1,c]`
        LIM_DROP_LBOUND))
    THENL [EXISTS_TAC `g:real^1->real^1`; EXISTS_TAC `h:real^1->real^1`] THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `drop c - drop x` THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g':real^1->real^1) continuous (at c within interval[a,c]) /\
    (h':real^1->real^1) continuous (at c within interval[a,c])`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[CONTINUOUS_WITHIN; REAL_LE_REFL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH
     `g - g':real^1 = k <=> g' + k = g`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] LIM_TRANSFORM)) THEN
    MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[LIM_WITHIN; DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    SIMP_TAC[REAL_ARITH `x <= c /\ &0 < abs(x - c) ==> ~(c <= x)`] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN
  REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`) th) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `d:real^1` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `c:real^1`; `d:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[REAL_ARITH `abs(a - (a + b)) = abs b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < a ==> abs x < a`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_VARIATION_POS_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f:real^1->real^1 = \x. g' x - h' x` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g':real^1->real^1`; `\x. --((h':real^1->real^1) x)`;
    `interval[d:real^1,c]`] VECTOR_VARIATION_TRIANGLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NEG] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,c]` THEN
    ASM_SIMP_TAC[INCREASING_BOUNDED_VARIATION; SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN  ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB] THEN MATCH_MP_TAC(REAL_ARITH
   `y < a / &2 /\ z < a / &2 ==> x <= y + z ==> x < a`) THEN
  REWRITE_TAC[VECTOR_VARIATION_NEG] THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand)
    INCREASING_VECTOR_VARIATION o lhand o snd) THEN
  (ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
     ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; IN_INTERVAL_1; REAL_NOT_LT] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x - y) < e ==> y - x < e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let VECTOR_VARIATION_CONTINUOUS_RIGHT = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[c,b]) <=>
            f continuous (at c within interval[c,b]))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[continuous_within] THEN
    REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
    DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `x:real^1`; `c:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `abs((a + b) - a) = abs b`] THEN
    REWRITE_TAC[drop; GSYM NORM_REAL] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
    MATCH_MP_TAC VECTOR_VARIATION_GE_NORM_FUNCTION THEN
    REWRITE_TAC[SUBSET_REFL; INTERVAL_EQ_EMPTY_1] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
         HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN ASM_CASES_TAC `c limit_point_of interval[c:real^1,b]` THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[CONTINUOUS_WITHIN; LIM; TRIVIAL_LIMIT_WITHIN]] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_RIGHT_LIMIT_1) THEN
  MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`; `c:real^1`]
   INCREASING_RIGHT_LIMIT_1) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `gc:real^1` THEN DISCH_TAC THEN
  X_GEN_TAC `hc:real^1` THEN DISCH_TAC THEN
  ABBREV_TAC `k = gc - (g:real^1->real^1) c` THEN
  SUBGOAL_THEN `hc - (h:real^1->real^1) c = k` ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `hc' - hc:real^1 = gc' - gc <=> gc' - hc' = gc - hc`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTINUOUS_WITHIN]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
      LIM_UNIQUE) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    ASM_SIMP_TAC[LIM_SUB];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`g':real^1->real^1 = \x. if drop x <= drop c then g(x) + k else g(x)`;
    `h':real^1->real^1 = \x. if drop x <= drop c then h(x) + k else h(x)`] THEN
  SUBGOAL_THEN
   `(!x y. x IN interval[c,b] /\ y IN interval[c,b] /\ drop x <= drop y
           ==> drop(g' x) <= drop(g' y)) /\
    (!x y. x IN interval[c,b] /\ y IN interval[c,b] /\ drop x <= drop y
           ==> drop(h' x) <= drop(h' y))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN STRIP_TAC THEN
    (ASM_CASES_TAC `drop y <= drop c` THENL
      [SUBGOAL_THEN `drop x <= drop c` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
       REWRITE_TAC[DROP_ADD; REAL_LE_RADD] THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
      [ALL_TAC;
       FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
       RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC] THEN
     SUBGOAL_THEN `x:real^1 = c` SUBST_ALL_TAC THENL
      [REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
      `gc - g c = k
       ==> drop(g c + (gc - g c)) <= b ==> drop(g c + k) <= b`)) THEN
     REWRITE_TAC[VECTOR_ARITH `a + b - a:real^1 = b`] THEN
     MATCH_MP_TAC(ISPEC `at c within interval[c:real^1,b]`
        LIM_DROP_UBOUND))
    THENL [EXISTS_TAC `g:real^1->real^1`; EXISTS_TAC `h:real^1->real^1`] THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `drop y - drop c` THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REWRITE_TAC[DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(g':real^1->real^1) continuous (at c within interval[c,b]) /\
    (h':real^1->real^1) continuous (at c within interval[c,b])`
  MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[CONTINUOUS_WITHIN; REAL_LE_REFL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH
     `g - g':real^1 = k <=> g' + k = g`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] LIM_TRANSFORM)) THEN
    MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN
    REWRITE_TAC[LIM_WITHIN; DIST_REAL; GSYM drop; IN_INTERVAL_1] THEN
    SIMP_TAC[REAL_ARITH `c <= x /\ &0 < abs(x - c) ==> ~(x <= c)`] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; DROP_VEC; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MESON_TAC[REAL_LT_01];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_within] THEN
  REWRITE_TAC[DIST_LIFT; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
  DISCH_THEN(fun th ->
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    CONJUNCTS_THEN (MP_TAC o SPEC `e / &2`) th) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `d:real^1` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `d:real^1`; `c:real^1`]
        VECTOR_VARIATION_COMBINE) THEN
  ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - a:real = b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < a ==> abs x < a`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VECTOR_VARIATION_POS_LE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `f:real^1->real^1 = \x. g' x - h' x` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g'"; "h'"] THEN REWRITE_TAC[FUN_EQ_THM] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g':real^1->real^1`; `\x. --((h':real^1->real^1) x)`;
    `interval[c:real^1,d]`] VECTOR_VARIATION_TRIANGLE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_NEG] THEN
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `interval[c:real^1,b]` THEN
    ASM_SIMP_TAC[INCREASING_BOUNDED_VARIATION; SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN  ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_SUB] THEN MATCH_MP_TAC(REAL_ARITH
   `y < a / &2 /\ z < a / &2 ==> x <= y + z ==> x < a`) THEN
  REWRITE_TAC[VECTOR_VARIATION_NEG] THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand)
    INCREASING_VECTOR_VARIATION o lhand o snd) THEN
  (ANTS_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
     ASM_REWRITE_TAC[INTERVAL_EQ_EMPTY_1; IN_INTERVAL_1; REAL_NOT_LT] THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
     DISCH_THEN SUBST1_TAC]) THEN
  MATCH_MP_TAC(REAL_ARITH `abs x < e ==> x < e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let VECTOR_VARIATION_CONTINUOUS = prove
 (`!f:real^1->real^1 a b c.
        f has_bounded_variation_on interval[a,b] /\ c IN interval[a,b]
        ==> ((\x. lift(vector_variation(interval[a,x]) f))
             continuous (at c within interval[a,b]) <=>
            f continuous (at c within interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!f:real^1->real^1.
        f continuous (at c within interval[a,b]) <=>
        f continuous (at c within interval[a,c]) /\
        f continuous (at c within interval[c,b])`
   (fun th -> REWRITE_TAC[th] THEN
              ASM_MESON_TAC[VECTOR_VARIATION_CONTINUOUS_LEFT;
                            VECTOR_VARIATION_CONTINUOUS_RIGHT]) THEN
  GEN_TAC THEN REWRITE_TAC[CONTINUOUS_WITHIN] THEN EQ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o GEN_ALL o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] LIM_WITHIN_SUBSET)) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP LIM_UNION) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] LIM_WITHIN_SUBSET)] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_INTERVAL_1] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_DARBOUX_STRONG = prove
 (`!f a b.
     f has_bounded_variation_on interval[a,b]
     ==> ?g h. (!x. f x = g x - h x) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x <= drop y
                      ==> drop(g x) <= drop(g y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x <= drop y
                      ==> drop(h x) <= drop(h y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x < drop y
                      ==> drop(g x) < drop(g y)) /\
               (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\
                      drop x < drop y
                      ==> drop(h x) < drop(h y)) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[a,x])
                    ==> g continuous (at x within interval[a,x]) /\
                        h continuous (at x within interval[a,x])) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[x,b])
                    ==> g continuous (at x within interval[x,b]) /\
                        h continuous (at x within interval[x,b])) /\
               (!x. x IN interval[a,b] /\
                    f continuous (at x within interval[a,b])
                    ==> g continuous (at x within interval[a,b]) /\
                        h continuous (at x within interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^1. x + lift(vector_variation (interval[a,x]) (f:real^1->real^1))`;
    `\x:real^1. x + lift(vector_variation (interval[a,x]) f) - f x`] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + l) - (x + l - f):real^1 = f`] THEN
  REWRITE_TAC[LIFT_DROP; DROP_SUB; DROP_ADD] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MONOTONE;
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
    EXISTS_TAC `drop(f(a:real^1))` THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE;
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MONOTONE;
    MATCH_MP_TAC REAL_LTE_ADD2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x. a - (b - x) <= c - (d - x) ==> a - b <= c - d`) THEN
    EXISTS_TAC `drop(f(a:real^1))` THEN
    REWRITE_TAC[GSYM DROP_SUB] THEN
    MATCH_MP_TAC VECTOR_VARIATION_MINUS_FUNCTION_MONOTONE;
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_LEFT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_LEFT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ADD THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_ID] THEN
    MATCH_MP_TAC CONTINUOUS_SUB THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `x:real^1`]
        VECTOR_VARIATION_CONTINUOUS) THEN
    ASM_REWRITE_TAC[]] THEN
  (CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_BOUNDED_VARIATION_ON_SUBSET));
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1; INTERVAL_EQ_EMPTY_1] THEN
    ASM_REAL_ARITH_TAC));;

let HAS_BOUNDED_VARIATION_COUNTABLE_DISCONTINUITIES = prove
 (`!f:real^1->real^1 a b.
        f has_bounded_variation_on interval[a,b]
        ==> COUNTABLE {x | x IN interval[a,b] /\ ~(f continuous at x)}`,
  SUBGOAL_THEN
   `!f a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> COUNTABLE {x | x IN interval[a,b] /\ ~(f continuous at x)}`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
     GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`] th) THEN
      MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`] th)) THEN
    ASM_REWRITE_TAC[IMP_IMP; GSYM COUNTABLE_UNION] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] COUNTABLE_SUBSET) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(TAUT
     `(p /\ q ==> r) ==> a /\ ~r ==> a /\ ~p \/ a /\ ~q`) THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [GSYM ETA_AX] THEN
    ASM_SIMP_TAC[CONTINUOUS_SUB]] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; COUNTABLE_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_EQ_EMPTY_1; REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[CLOSED_OPEN_INTERVAL_1] THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC
   `a INSERT b INSERT
    {x | x IN interval(a,b) /\ ~((f:real^1->real^1) continuous at x)}` THEN
  CONJ_TAC THENL [REWRITE_TAC[COUNTABLE_INSERT]; SET_TAC[]] THEN
  SUBGOAL_THEN
   `(!c:real^1. c IN interval(a,b) ==> c limit_point_of interval[a,c]) /\
    (!c:real^1. c IN interval(a,b) ==> c limit_point_of interval[c,b])`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[IN_INTERVAL_1; REAL_LE_REFL; LIMPT_OF_CONVEX;
             CONVEX_INTERVAL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM INTERVAL_SING; GSYM SUBSET_ANTISYM_EQ] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`]
        INCREASING_LEFT_LIMIT_1) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^1->real^1` (LABEL_TAC "l")) THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`]
        INCREASING_RIGHT_LIMIT_1) THEN
  ASM_REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^1->real^1` (LABEL_TAC "r")) THEN
  SUBGOAL_THEN
   `!c. c IN interval(a:real^1,b)
        ==> drop(l c) <= drop(f c) /\ drop(f c) <= drop(r c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(ISPEC `at c within interval[a:real^1,c]`
        LIM_DROP_UBOUND);
      MATCH_MP_TAC(ISPEC `at c within interval[c:real^1,b]`
        LIM_DROP_LBOUND)] THEN
    EXISTS_TAC `f:real^1->real^1` THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED;
                 TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01; IN_INTERVAL_1] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!c x. c IN interval(a:real^1,b) /\ x IN interval[a,b] /\ drop x < drop c
           ==> drop(f x) <= drop(l c)) /\
    (!c x. c IN interval(a:real^1,b) /\ x IN interval[a,b] /\ drop c < drop x
           ==> drop(r c) <= drop(f x))`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(ISPEC `at c within interval[a:real^1,c]`
        LIM_DROP_LBOUND);
      MATCH_MP_TAC(ISPEC `at c within interval[c:real^1,b]`
        LIM_DROP_UBOUND)] THEN
    EXISTS_TAC `f:real^1->real^1` THEN
    ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED;
                 TRIVIAL_LIMIT_WITHIN; EVENTUALLY_WITHIN]
    THENL
     [EXISTS_TAC `drop c - drop x`; EXISTS_TAC `drop x - drop c`] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    X_GEN_TAC `y:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_ELIM_THM; DIST_REAL; GSYM drop] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COUNTABLE; ge_c] THEN
  TRANS_TAC CARD_LE_TRANS `rational` THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM ge_c] THEN
  REWRITE_TAC[COUNTABLE_RATIONAL; GSYM COUNTABLE; le_c] THEN
  SUBGOAL_THEN
   `!c. c IN interval(a,b) /\ ~((f:real^1->real^1) continuous at c)
          ==> drop(l(c:real^1)) < drop(r c)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    REWRITE_TAC[DROP_EQ] THEN DISCH_TAC THEN
    SUBGOAL_THEN `l c = (f:real^1->real^1) c /\ r c = f c` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LE_ANTISYM; DROP_EQ]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CONTINUOUS_AT]) THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((f:real^1->real^1) --> f c) (at c within interval(a,b))`
    MP_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[OPEN_INTERVAL; LIM_WITHIN_OPEN]] THEN
    MATCH_MP_TAC LIM_WITHIN_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,c] UNION interval[c,b]` THEN
    REWRITE_TAC[LIM_WITHIN_UNION] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED];
      REWRITE_TAC[SUBSET; IN_UNION; IN_INTERVAL_1] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!c. c IN interval(a,b) /\ ~((f:real^1->real^1) continuous at c)
        ==> ?q. rational q /\ drop(l c) < q /\ q < drop(r c)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `drop(l(c:real^1)) < drop(r c)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(drop(l(c:real^1)) + drop(r c)) / &2`;
                   `(drop(r c) - drop(l(c:real^1))) / &2`]
      RATIONAL_APPROXIMATION) THEN
    ASM_REWRITE_TAC[REAL_HALF; REAL_SUB_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; IN_ELIM_THM; IN_INTERVAL_1] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^1->real` THEN
  SIMP_TAC[IN] THEN DISCH_THEN(LABEL_TAC "*") THEN
  MATCH_MP_TAC(MESON[REAL_LE_TOTAL]
   `(!x y. P x y ==> P y x) /\ (!x y. drop x <= drop y ==> P x y)
    ==> !x y. P x y`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `y:real^1`] THEN
  REWRITE_TAC[REAL_LE_LT; DROP_EQ] THEN
  ASM_CASES_TAC `x:real^1 = y` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q(x:real^1) < q(y)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[REAL_LT_REFL]] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `drop(r(x:real^1))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `drop(l(y:real^1))` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(f(inv(&2) % (x + y):real^1))` THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_ADD] THEN
  ASM_REAL_ARITH_TAC);;

let HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE = prove
 (`!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x)
        ==> (f has_bounded_variation_on interval[a,b] <=>
             (\x. vector_derivative f (at x))
             absolutely_integrable_on interval[a,b])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ] THEN
  REWRITE_TAC[has_bounded_variation_on] THEN
  MATCH_MP_TAC(TAUT `q /\ (p <=> r) ==> (p <=> q /\ r)`) THEN CONJ_TAC THENL
   [ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
    ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
    MP_TAC(ISPECL [`f:real^1->real^N`;
                   `\x. vector_derivative (f:real^1->real^N) (at x)`;
                   `s:real^1->bool`; `a:real^1`; `b:real^1`]
      FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
    ASM_MESON_TAC[VECTOR_DERIVATIVE_WORKS; integrable_on;
                  HAS_VECTOR_DERIVATIVE_AT_WITHIN];
    MATCH_MP_TAC(MESON[HAS_BOUNDED_SETVARIATION_ON_EQ]
     `(!a b. ~(interval[a,b] = {}) /\ interval[a,b] SUBSET s
               ==> f(interval[a,b]) = g(interval[a,b]))
      ==> (f has_bounded_setvariation_on s <=>
           g has_bounded_setvariation_on s)`) THEN
    SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_LOWERBOUND;
             GSYM INTERVAL_NE_EMPTY] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY_1] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^N`;
                   `\x. vector_derivative (f:real^1->real^N) (at x)`;
                   `s:real^1->bool`; `u:real^1`; `v:real^1`]
      FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[INTEGRAL_UNIQUE]] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; IN_DIFF; SUBSET];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      ASM_SIMP_TAC[GSYM VECTOR_DERIVATIVE_WORKS] THEN ASM SET_TAC[]]]);;

let HAS_BOUNDED_VARIATION_INTEGRABLE_NORM_DERIVATIVE = prove
 (`!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x)
        ==> (f has_bounded_variation_on interval[a,b] <=>
             (\x. lift(norm(vector_derivative f (at x))))
             integrable_on interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC th THEN
    REWRITE_TAC[MATCH_MP HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE
                th]) THEN
  REWRITE_TAC[absolutely_integrable_on] THEN
  MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[INTEGRABLE_ON_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
  MP_TAC(ISPECL [`f:real^1->real^N`;
                 `\x. vector_derivative (f:real^1->real^N) (at x)`;
                 `s:real^1->bool`; `a:real^1`; `b:real^1`]
    FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG) THEN
  ASM_MESON_TAC[VECTOR_DERIVATIVE_WORKS; integrable_on;
                HAS_VECTOR_DERIVATIVE_AT_WITHIN]);;

let VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE = prove
 (`!f:real^1->real^N s a b.
        COUNTABLE s /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s ==> f differentiable at x) /\
        f has_bounded_variation_on interval[a,b]
        ==> vector_variation (interval[a,b]) f =
                drop(integral (interval[a,b])
                        (\x. lift(norm(vector_derivative f (at x)))))`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`f:real^1->real^N`; `s:real^1->bool`; `a:real^1`; `b:real^1`]
   HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_SET_VARIATION) THEN
  REWRITE_TAC[vector_variation] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SET_VARIATION_EQ THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
  SIMP_TAC[INTERVAL_NE_EMPTY_1; INTERVAL_LOWERBOUND_1;
           INTERVAL_UPPERBOUND_1] THEN
  STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  ASM_MESON_TAC[VECTOR_DERIVATIVE_WORKS; HAS_VECTOR_DERIVATIVE_AT_WITHIN;
                IN_DIFF; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Baby Fubini theorems for continuous functions. Will be generalized.       *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_PASTECART_CONTINUOUS = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`,
  let lemma1 = prove
   (`!(f:real^(M,N)finite_sum->real^P) a b c d x.
          f continuous_on interval [pastecart a c,pastecart b d] /\
          x IN interval[a,b]
          ==> (\y. (f:real^(M,N)finite_sum->real^P) (pastecart x y))
              integrable_on interval[c,d]`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; CONTINUOUS_ON_CONST;
             CONTINUOUS_ON_ID] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; GSYM PASTECART_INTERVAL;
                 IN_ELIM_PASTECART_THM]) in
  let lemma2 = prove
   (`!(f:real^(M,N)finite_sum->real^P) a b c d.
      f continuous_on interval [pastecart a c,pastecart b d]
      ==> (\x. integral (interval [c,d]) (\y. f (pastecart x y))) integrable_on
          interval [a,b]`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] lemma1)) THEN
    MATCH_MP_TAC INTEGRABLE_CONTINUOUS THEN REWRITE_TAC[continuous_on] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[dist; GSYM INTEGRAL_SUB] THEN
    ASM_CASES_TAC `content(interval[c:real^N,d]) = &0` THENL
     [ASM_SIMP_TAC[INTEGRAL_NULL; NORM_0] THEN MESON_TAC[REAL_LT_01];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COMPACT_UNIFORMLY_CONTINUOUS)) THEN
    REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONTENT_LT_NZ]) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2 / content(interval[c:real^N,d])`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; FORALL_PASTECART] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    REWRITE_TAC[GSYM PASTECART_INTERVAL; dist; IN_ELIM_PASTECART_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x':real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `e / &2 = e / &2 / content(interval[c:real^N,d]) * content(interval[c,d])`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < content(interval[c:real^N,d])` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
      EXISTS_TAC `\y. (f:real^(M,N)finite_sum->real^P) (pastecart x' y) -
                      (f:real^(M,N)finite_sum->real^P) (pastecart x y)` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_HALF; REAL_LT_DIV;
                   GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_SUB; lemma1] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[NORM_PASTECART; PASTECART_SUB; VECTOR_SUB_REFL; NORM_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_SIMP_TAC[REAL_ADD_RID; POW_2_SQRT; NORM_POS_LE]]) in
  let lemma3 = prove
   (`!f:real^(M,N)finite_sum->real^P e s.
      &0 < e /\ f continuous_on s
      ==> operative(/\)
           (\k. !a b c d.
                interval[pastecart a c,pastecart b d] SUBSET k /\
                interval[pastecart a c,pastecart b d] SUBSET s
                ==> norm(integral (interval[pastecart a c,pastecart b d]) f -
                         integral (interval[a,b])
                           (\x. integral (interval[c,d])
                                    (\y. f(pastecart x y))))
                    <= e * content(interval[pastecart a c,pastecart b d]))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[operative; NEUTRAL_AND] THEN
    CONJ_TAC THEN MAP_EVERY X_GEN_TAC
     [`A:real^(M,N)finite_sum`;`B:real^(M,N)finite_sum`] THENL
     [DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real^N`; `d:real^N`] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN
       `content(interval[pastecart (a:real^M) (c:real^N),pastecart b d]) = &0`
       (fun th -> ASSUME_TAC th THEN MP_TAC th)
      THENL [ASM_MESON_TAC[CONTENT_0_SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[CONTENT_PASTECART; REAL_ENTIRE] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[INTEGRAL_NULL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                   VECTOR_SUB_REFL; NORM_0; REAL_LE_REFL; INTEGRAL_0];
      MAP_EVERY X_GEN_TAC [`l:real`; `k:num`] THEN STRIP_TAC THEN EQ_TAC THENL
       [REWRITE_TAC[AND_FORALL_THM] THEN
        REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
        MATCH_MP_TAC(TAUT
         `(P1 ==> P) /\ (P2 ==> P)
          ==> (P ==> Q) ==> (P1 ==> Q) /\ (P2 ==> Q)`) THEN
        SET_TAC[];
        DISCH_TAC]] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`; `c:real^N`; `d:real^N`] THEN
    STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[DIMINDEX_FINITE_SUM]) THEN
    ASM_CASES_TAC `k <= dimindex(:M)` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN2
       (MP_TAC o SPECL
         [`a:real^M`;
          `(lambda i. if i = k then min (b$k) l else (b:real^M)$i):real^M`;
          `c:real^N`; `d:real^N`])
       (MP_TAC o SPECL
         [`(lambda i. if i = k then max (a$k) l else (a:real^M)$i):real^M`;
          `b:real^M`; `c:real^N`; `d:real^N`])) THEN
      ASM_SIMP_TAC[GSYM INTERVAL_SPLIT; GSYM PASTECART_INTERVAL] THEN
      SUBGOAL_THEN
       `!P Q. { pastecart (x:real^M) (y:real^N) |
                x IN interval[a,b] INTER {x | P (x$k)} /\ Q y} =
              {pastecart x y | x IN interval[a,b] /\ Q y} INTER {x | P (x$k)}`
       (fun th -> REWRITE_TAC[th])
      THENL
       [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM;
                    IN_INTER] THEN
        ASM_SIMP_TAC[pastecart; IN_ELIM_THM; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                     ARITH_RULE `i:num <= m ==> i <= m + n`] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[PASTECART_INTERVAL] THEN
      ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER u SUBSET t INTER u`] THEN
      ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER u SUBSET t`] THEN
      MATCH_MP_TAC(NORM_ARITH
       `y = y1 + y2 /\ x = x1 + x2 /\ e = e1 + e2
        ==> norm(y2 - x2:real^N) <= e2 ==> norm(y1 - x1) <= e1
            ==> norm(y - x) <= e`) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SIMP_RULE[GSYM INTERVAL_SPLIT] INTEGRAL_SPLIT) THEN
        ASM_SIMP_TAC[DIMINDEX_FINITE_SUM;
                     ARITH_RULE `i:num <= m ==> i <= m + n`] THEN
        ASM_MESON_TAC[INTEGRABLE_CONTINUOUS; CONTINUOUS_ON_SUBSET];
        MATCH_MP_TAC(SIMP_RULE[GSYM INTERVAL_SPLIT] INTEGRAL_SPLIT) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC lemma2 THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC CONTENT_SPLIT THEN
        ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM]];
      FIRST_X_ASSUM(CONJUNCTS_THEN2
       (MP_TAC o SPECL
         [`a:real^M`; `b:real^M`; `c:real^N`;
          `(lambda i. if i = k - dimindex(:M)
                      then min (d$(k - dimindex(:M))) l
                      else (d:real^N)$i):real^N`])
       (MP_TAC o SPECL
         [`a:real^M`; `b:real^M`;
          `(lambda i. if i = k - dimindex(:M)
                      then max (c$(k - dimindex(:M))) l
                      else (c:real^N)$i):real^N`;
          `d:real^N`])) THEN
      ASM_SIMP_TAC[GSYM INTERVAL_SPLIT; GSYM PASTECART_INTERVAL;
                ARITH_RULE `~(i <= m) ==> 1 <= i - m`;
                ARITH_RULE `~(i <= m) /\ i:num <= m + n ==> i - m <= n`] THEN
      SUBGOAL_THEN
       `!P Q. { pastecart (x:real^M) (y:real^N) |
              P x /\ y IN interval[c,d] INTER {y | Q (y$(k - dimindex(:M)))}} =
              {pastecart x y | P x /\ y IN interval[c,d]} INTER
              {x | Q (x$k)}`
       (fun th -> REWRITE_TAC[th])
      THENL
       [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_ELIM_PASTECART_THM;
                    IN_INTER] THEN
        ASM_SIMP_TAC[pastecart; IN_ELIM_THM; LAMBDA_BETA;
                     DIMINDEX_FINITE_SUM] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[PASTECART_INTERVAL] THEN
      ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER u SUBSET t INTER u`] THEN
      ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER u SUBSET t`] THEN
      MATCH_MP_TAC(NORM_ARITH
       `y = y1 + y2 /\ x = x1 + x2 /\ e = e1 + e2
        ==> norm(y2 - x2:real^N) <= e2 ==> norm(y1 - x1) <= e1
            ==> norm(y - x) <= e`) THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SIMP_RULE[GSYM INTERVAL_SPLIT] INTEGRAL_SPLIT) THEN
        ASM_SIMP_TAC[DIMINDEX_FINITE_SUM;
                     ARITH_RULE `i:num <= m ==> i <= m + n`] THEN
        ASM_MESON_TAC[INTEGRABLE_CONTINUOUS; CONTINUOUS_ON_SUBSET];
        W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_ADD o rand o snd) THEN
        REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_SIMP_TAC[INTERVAL_SPLIT; DIMINDEX_FINITE_SUM;
                 ARITH_RULE `~(i <= m) ==> 1 <= i - m`;
                 ARITH_RULE `~(i <= m) /\ i:num <= m + n ==> i - m <= n`] THEN
          CONJ_TAC THEN MATCH_MP_TAC lemma2 THEN
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
          EXISTS_TAC `s:real^(M,N)finite_sum->bool` THEN
          ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
             MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
          REWRITE_TAC[SUBSET_INTERVAL] THEN DISCH_THEN(K ALL_TAC) THEN
          ASM_SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_FINITE_SUM;
                  ARITH_RULE `~(i <= m) ==> 1 <= i - m`;
                  ARITH_RULE `~(i <= m) /\ i:num <= m + n ==> i - m <= n`] THEN
          REPEAT STRIP_TAC THEN
          REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
          REAL_ARITH_TAC;
          DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_EQ THEN
          X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
          MATCH_MP_TAC(SIMP_RULE[GSYM INTERVAL_SPLIT] INTEGRAL_SPLIT) THEN
          CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
          MATCH_MP_TAC lemma1 THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]];
        REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
        MATCH_MP_TAC CONTENT_SPLIT THEN
        ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM]]]) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `content(interval[pastecart(a:real^M) (c:real^N),pastecart b d]) = &0` THEN
  ASM_SIMP_TAC[INTEGRAL_NULL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONTENT_PASTECART]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ENTIRE; DE_MORGAN_THM]) THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN
    ASM_SIMP_TAC[INTEGRAL_NULL; INTEGRAL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < content(interval[pastecart(a:real^M) (c:real^N),pastecart b d])`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONTENT_LT_NZ; CONTENT_PASTECART; REAL_ENTIRE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MATCH_MP_TAC(MESON[REAL_ARITH
   `~(x = &0) ==> &0 < abs x / &2 /\ ~(abs x <= abs x / &2)`]
   `(!e. &0 < e ==> abs x <= e) ==> x = &0`) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_NORM] THEN
  MP_TAC(ISPECL
   [`f:real^(M,N)finite_sum->real^P`;
    `e / content(interval[pastecart(a:real^M) (c:real^N),pastecart b d])`;
    `interval[pastecart(a:real^M) (c:real^N),pastecart b d]`]
   lemma3) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] OPERATIVE_DIVISION_AND)) THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    COMPACT_UNIFORMLY_CONTINUOUS)) THEN
  REWRITE_TAC[COMPACT_INTERVAL; uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC
    `e / &2 /
     content(interval[pastecart(a:real^M) (c:real^N),pastecart b d])`) THEN
  ASM_SIMP_TAC[dist; REAL_HALF; REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?p. p tagged_division_of
        interval[pastecart(a:real^M) (c:real^N),pastecart b d] /\
        (\x. ball(x,k)) fine p`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINE_DIVISION_EXISTS; GAUGE_BALL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
  `IMAGE SND (p:real^(M,N)finite_sum#(real^(M,N)finite_sum->bool)->bool)`) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`pastecart(a:real^M) (c:real^N)`; `pastecart(b:real^M) (d:real^N)`]) THEN
  ASM_SIMP_TAC[DIVISION_OF_TAGGED_DIVISION] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
  MATCH_MP_TAC(TAUT `(b ==> c) /\ a ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o SPECL
     [`a:real^M`; `b:real^M`; `c:real^N`; `d:real^N`]) THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; SUBSET_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`t:real^(M,N)finite_sum`; `l:real^(M,N)finite_sum->bool`] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`t:real^(M,N)finite_sum`; `l:real^(M,N)finite_sum->bool`] o
     el 1 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^M`; `v:real^M`; `w:real^N`; `z:real^N`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  REWRITE_TAC[SUBSET; IN_BALL; dist] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`u:real^M`; `v:real^M`; `w:real^N`; `z:real^N`;
    `(f:real^(M,N)finite_sum->real^P) t`]
   INTEGRAL_PASTECART_CONST) THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x - x') <= e / &2 /\ norm(y - y') <= e / &2
    ==> x':real^P = y' ==> norm(x - y) <= e`) THEN
  REWRITE_TAC[REAL_ARITH `(e / c * d) / &2 = e / &2 / c * d`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN
    EXISTS_TAC `\y. (f:real^(M,N)finite_sum->real^P) y - f t` THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
      REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_CONST] THEN
      ASM_MESON_TAC[INTEGRABLE_CONTINUOUS; INTEGRABLE_ON_SUBINTERVAL];
      X_GEN_TAC `y:real^(M,N)finite_sum` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC(TAUT `(a /\ b) /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[NORM_SUB; SUBSET]]];
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [CONTENT_PASTECART] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
    MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN EXISTS_TAC
     `\x. integral (interval [w,z]) (\y. f (pastecart x y)) -
           integral (interval [w,z])
                    (\y. (f:real^(M,N)finite_sum->real^P) t)` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[CONTENT_POS_LE] THEN
      ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_IMP_LE];
      MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
      REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_CONST] THEN
      MATCH_MP_TAC lemma2 THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC HAS_INTEGRAL_BOUND THEN EXISTS_TAC
       `\y. (f:real^(M,N)finite_sum->real^P) (pastecart x y) - f t` THEN
      ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_IMP_LE] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HAS_INTEGRAL_SUB THEN
        REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_CONST] THEN
        MATCH_MP_TAC lemma1 THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET];
        X_GEN_TAC `s:real^N` THEN DISCH_TAC THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL
         [ASM SET_TAC[];
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `s SUBSET t ==> x IN s ==> x IN t`)) THEN
          ASM_REWRITE_TAC[GSYM PASTECART_INTERVAL; IN_ELIM_PASTECART_THM];
          RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
          ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
          EXISTS_TAC `l:real^(M,N)finite_sum->bool` THEN
          ASM_REWRITE_TAC[] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
           `s SUBSET t ==> x IN s ==> x IN t`)) THEN
          ASM_REWRITE_TAC[GSYM PASTECART_INTERVAL;
                          IN_ELIM_PASTECART_THM]]]]]);;

let INTEGRAL_SWAP_CONTINUOUS = prove
 (`!f:real^M->real^N->real^P a b c d.
        (\z. f (fstcart z) (sndcart z))
        continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[a,b]) (\x. integral (interval[c,d]) (f x)) =
            integral (interval[c,d])
                     (\y. integral (interval[a,b]) (\x. f x y))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. (f:real^M->real^N->real^P) (fstcart z) (sndcart z)`;
   `a:real^M`; `b:real^M`; `c:real^N`; `d:real^N`]
   INTEGRAL_PASTECART_CONTINUOUS) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; ETA_AX] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`\z. (f:real^M->real^N->real^P) (sndcart z) (fstcart z)`;
   `c:real^N`; `d:real^N`; `a:real^M`; `b:real^M`]
   INTEGRAL_PASTECART_CONTINUOUS) THEN
  ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\z. (f:real^M->real^N->real^P) (sndcart z) (fstcart z)) =
      (\z. (f:real^M->real^N->real^P) (fstcart z) (sndcart z)) o
      (\z. pastecart (sndcart z) (fstcart z))`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF; FSTCART_PASTECART; SNDCART_PASTECART];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_PASTECART; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; LINEAR_SNDCART] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; GSYM PASTECART_INTERVAL] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_PASTECART_THM] THEN
    SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MP_TAC(ISPECL
   [`\z. (f:real^M->real^N->real^P) (fstcart z) (sndcart z)`;
    `\z:real^(N,M)finite_sum. pastecart (sndcart z) (fstcart z)`;
    `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`;
    `&1`;
    `integral (interval[pastecart a c,pastecart b d])
              (\z. (f:real^M->real^N->real^P) (fstcart z) (sndcart z))`;
    `pastecart (a:real^M) (c:real^N)`;
    `pastecart (b:real^M) (d:real^N)`]
  HAS_INTEGRAL_TWIDDLE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_INV_1; REAL_LT_01;
              PASTECART_FST_SND; VECTOR_MUL_LID; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM HAS_INTEGRAL_INTEGRAL; INTEGRABLE_CONTINUOUS] THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              FSTCART_PASTECART; SNDCART_PASTECART;
              GSYM PASTECART_INTERVAL; IN_ELIM_PASTECART_THM] THEN
  REWRITE_TAC[PASTECART_INTERVAL] THEN
  CONV_TAC(ONCE_DEPTH_CONV
   (fun t -> if fst(dest_const(fst(strip_comb
                (snd(dest_exists(snd(dest_exists t))))))) = "SETSPEC"
             then REWR_CONV SWAP_EXISTS_THM t else NO_CONV t)) THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{pastecart (y:real^M) (x:real^N) | p x /\ q y} =
    {pastecart x y | q x /\ p y}`] THEN
  REWRITE_TAC[PASTECART_INTERVAL] THEN
  DISCH_THEN MATCH_MP_TAC  THEN
  SIMP_TAC[CONTINUOUS_PASTECART; LINEAR_CONTINUOUS_AT;
             LINEAR_FSTCART; LINEAR_SNDCART] THEN
  REWRITE_TAC[CONTENT_PASTECART] THEN
  REWRITE_TAC[REAL_MUL_SYM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Rectifiable paths and path length defined using variation.                *)
(* ------------------------------------------------------------------------- *)

let rectifiable_path = new_definition
 `rectifiable_path (g:real^1->real^N) <=>
    path g /\ g has_bounded_variation_on interval[vec 0,vec 1]`;;

let path_length = new_definition
 `path_length (g:real^1->real^N) =
  vector_variation (interval[vec 0,vec 1]) g`;;

let BOUNDED_RECTIFIABLE_PATH_IMAGE = prove
 (`!g:real^1->real^N. rectifiable_path g ==> bounded(path_image g)`,
  SIMP_TAC[rectifiable_path; BOUNDED_PATH_IMAGE]);;

let RECTIFIABLE_PATH_IMP_PATH = prove
 (`!g:real^1->real^N. rectifiable_path g ==> path g`,
  SIMP_TAC[rectifiable_path]);;

let RECTIFIABLE_PATH_LINEPATH = prove
 (`!a b:real^N. rectifiable_path(linepath(a,b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rectifiable_path; PATH_LINEPATH] THEN
  REWRITE_TAC[linepath] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD THEN
  REWRITE_TAC[GSYM DROP_VEC; GSYM DROP_SUB] THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_MUL THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_CONST] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_ID] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_CONST] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_ID]);;

let RECTIFIABLE_PATH_REVERSEPATH = prove
 (`!g:real^1->real^N. rectifiable_path(reversepath g) <=> rectifiable_path g`,
  SUBGOAL_THEN
   `!g:real^1->real^N. rectifiable_path g ==> rectifiable_path(reversepath g)`
   (fun th -> MESON_TAC[th; REVERSEPATH_REVERSEPATH]) THEN
  GEN_TAC THEN REWRITE_TAC[rectifiable_path] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[PATH_REVERSEPATH] THEN
  REWRITE_TAC[reversepath] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_COMPOSE_DECREASING THEN
  ASM_REWRITE_TAC[DROP_SUB; VECTOR_SUB_RZERO; VECTOR_SUB_REFL] THEN
  REAL_ARITH_TAC);;

let PATH_LENGTH_REVERSEPATH = prove
 (`!g:real^1->real^N. path_length(reversepath g) = path_length g`,
  GEN_TAC THEN REWRITE_TAC[path_length; reversepath] THEN
  REWRITE_TAC[VECTOR_SUB; VECTOR_VARIATION_REFLECT] THEN
  REWRITE_TAC[VECTOR_VARIATION_TRANSLATION] THEN
  REWRITE_TAC[REFLECT_INTERVAL; GSYM INTERVAL_TRANSLATION] THEN
  REWRITE_TAC[GSYM VECTOR_SUB; VECTOR_SUB_REFL; VECTOR_SUB_RZERO]);;

let RECTIFIABLE_PATH_SUBPATH = prove
 (`!u v g:real^1->real^N.
        rectifiable_path g /\
        u IN interval[vec 0,vec 1] /\
        v IN interval[vec 0,vec 1]
        ==> rectifiable_path(subpath u v g)`,
  REPEAT GEN_TAC THEN SIMP_TAC[PATH_SUBPATH; rectifiable_path] THEN
  STRIP_TAC THEN REWRITE_TAC[subpath] THEN
  ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
  REWRITE_TAC[HAS_BOUNDED_VARIATION_AFFINITY_EQ; IMAGE_AFFINITY_INTERVAL] THEN
  REWRITE_TAC[UNIT_INTERVAL_NONEMPTY; DROP_SUB; REAL_SUB_LE; REAL_SUB_0] THEN
  DISJ2_TAC THEN COND_CASES_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL; DROP_VEC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  ASM_REAL_ARITH_TAC);;

let RECTIFIABLE_PATH_JOIN = prove
 (`!g1 g2:real^1->real^N.
        pathfinish g1 = pathstart g2
        ==> (rectifiable_path(g1 ++ g2) <=>
             rectifiable_path g1 /\ rectifiable_path g2)`,
  REPEAT GEN_TAC THEN SIMP_TAC[rectifiable_path; PATH_JOIN] THEN
  REWRITE_TAC[pathfinish; pathstart] THEN DISCH_TAC THEN
  ASM_CASES_TAC `path(g1:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `path(g2:real^1->real^N)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`g1 ++ g2:real^1->real^N`; `vec 0:real^1`; `vec 1:real^1`;
                 `lift(&1 / &2)`]
        HAS_BOUNDED_VARIATION_ON_COMBINE) THEN
  REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[joinpaths] THEN BINOP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC
     `(\x. (g1:real^1->real^N)(&2 % x)) has_bounded_variation_on
      interval [vec 0,lift(&1 / &2)]` THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x:real^N = &2 % x + vec 0`];
    EXISTS_TAC
     `(\x. (g2:real^1->real^N)(&2 % x - vec 1)) has_bounded_variation_on
      interval [lift (&1 / &2),vec 1]` THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x - v:real^N = &2 % x + --v`]] THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[HAS_BOUNDED_VARIATION_AFFINITY_EQ] THEN
     REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; INTERVAL_EQ_EMPTY_1] THEN
     REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
     AP_TERM_TAC THEN AP_TERM_TAC THEN
     REWRITE_TAC[CONS_11; PAIR_EQ; GSYM DROP_EQ] THEN
     REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; DROP_VEC; DROP_NEG] THEN
     REAL_ARITH_TAC]) THEN
  MATCH_MP_TAC(MESON[HAS_BOUNDED_VARIATION_ON_EQ]
   `(!x. x IN s ==> f x = g x)
    ==> (f has_bounded_variation_on s <=>
         g has_bounded_variation_on s)`) THEN
  SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN X_GEN_TAC `x:real^1` THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 % x + --vec 1:real^1 = vec 0 /\ &2 % x = vec 1`
    (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[VECTOR_SUB_EQ; GSYM VECTOR_SUB] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC);;

let RECTIFIABLE_PATH_JOIN_IMP = prove
 (`!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2 /\
        pathfinish g1 = pathstart g2
        ==> rectifiable_path(g1 ++ g2)`,
  SIMP_TAC[RECTIFIABLE_PATH_JOIN]);;

let RECTIFIABLE_PATH_JOIN_EQ = prove
 (`!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2
        ==> (rectifiable_path (g1 ++ g2) <=> pathfinish g1 = pathstart g2)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[RECTIFIABLE_PATH_JOIN_IMP] THEN
  DISCH_TAC THEN MATCH_MP_TAC PATH_JOIN_PATH_ENDS THEN
  ASM_SIMP_TAC[RECTIFIABLE_PATH_IMP_PATH]);;

let PATH_LENGTH_JOIN = prove
 (`!g1 g2:real^1->real^N.
        rectifiable_path g1 /\ rectifiable_path g2 /\
        pathfinish g1 = pathstart g2
        ==> path_length(g1 ++ g2) = path_length g1 + path_length g2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[path_length] THEN
  MP_TAC(ISPECL [`g1 ++ g2:real^1->real^N`; `vec 0:real^1`; `vec 1:real^1`;
                 `lift(&1 / &2)`]
        VECTOR_VARIATION_COMBINE) THEN
  REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[rectifiable_path; RECTIFIABLE_PATH_JOIN_IMP];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `vector_variation (interval [vec 0,lift (&1 / &2)])
                     (\x. (g1:real^1->real^N)(&2 % x)) +
    vector_variation (interval [lift (&1 / &2),vec 1])
                     (\x.  (g2:real^1->real^N)(&2 % x - vec 1))` THEN
  CONJ_TAC THENL
   [BINOP_TAC THEN MATCH_MP_TAC VECTOR_VARIATION_EQ THEN
    SIMP_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; joinpaths] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathfinish; pathstart]) THEN
    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 % x - vec 1:real^1 = vec 0 /\ &2 % x = vec 1`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN
    REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[VECTOR_ARITH `&2 % x:real^N = &2 % x + vec 0`] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `(&2 % x + vec 0) - v:real^N = &2 % x + --v`] THEN
    REWRITE_TAC[VECTOR_VARIATION_AFFINITY; IMAGE_AFFINITY_INTERVAL] THEN
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; LIFT_DROP; DROP_VEC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN BINOP_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CONS_11; PAIR_EQ; GSYM DROP_EQ] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP; DROP_VEC; DROP_NEG] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Useful equivalent formulations where the path is differentiable.          *)
(* ------------------------------------------------------------------------- *)

let RECTIFIABLE_PATH_DIFFERENTIABLE = prove
 (`!g:real^1->real^N s.
        COUNTABLE s /\ path g /\
        (!t. t IN interval[vec 0,vec 1] DIFF s ==> g differentiable at t)
        ==> (rectifiable_path g <=>
                (\t. vector_derivative g (at t))
                absolutely_integrable_on interval[vec 0,vec 1])`,
  SIMP_TAC[rectifiable_path] THEN REWRITE_TAC[path] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
    HAS_BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_DERIVATIVE THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[]);;

let PATH_LENGTH_DIFFERENTIABLE = prove
 (`!g:real^1->real^N s.
        COUNTABLE s /\ rectifiable_path g /\
        (!t. t IN interval[vec 0,vec 1] DIFF s ==> g differentiable at t)
        ==> path_length g =
                drop(integral (interval[vec 0,vec 1])
                              (\t. lift(norm(vector_derivative g (at t)))))`,
  REWRITE_TAC[rectifiable_path; path_length; path] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC VECTOR_VARIATION_INTEGRAL_NORM_DERIVATIVE THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[]);;
