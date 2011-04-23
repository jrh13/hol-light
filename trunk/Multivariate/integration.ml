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
 (`!s1 s2:real^N->bool p1 p2 c.
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

let VSUM_OVER_TAGGED_DIVISION_LEMMA = prove
 (`!d:(real^M->bool)->real^N p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = vec 0)
        ==> vsum p (\(x,k). d k) = vsum (IMAGE SND p) d`,
  REWRITE_TAC[CONTENT_EQ_0_INTERIOR] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\(x:real^M,k:real^M->bool). d k:real^N) = d o SND`
  SUBST1_TAC THENL [SIMP_TAC[FUN_EQ_THM; FORALL_PAIR_THM; o_THM]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_IMAGE_NONZERO THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:real^M->bool` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `y:real^M` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k':real^M->bool` THEN
  ASM_CASES_TAC `k':real^M->bool = k` THEN
  ASM_REWRITE_TAC[PAIR_EQ; INTER_ACI] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[]);;

let SUM_OVER_TAGGED_DIVISION_LEMMA = prove
 (`!d:(real^N->bool)->real p i.
        p tagged_division_of i /\
        (!u v. ~(interval[u,v] = {}) /\ content(interval[u,v]) = &0
               ==> d(interval[u,v]) = &0)
        ==> sum p (\(x,k). d k) = sum (IMAGE SND p) d`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
  ASM_SIMP_TAC[LIFT_SUM; FINITE_IMAGE; o_DEF; LAMBDA_PAIR_THM] THEN
  MATCH_MP_TAC VSUM_OVER_TAGGED_DIVISION_LEMMA THEN
  ASM_SIMP_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_MESON_TAC[]);;

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
 (`!s1 s2:real^N->bool p1 p2 c.
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
 (`!f:real^M->real^N g k l s.
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
 (`!f:real^M->real^N g k l s.
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
 (`!f:real^M->real^N g k l s.
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
 (`!f:real^M->real^N g k l s.
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
 (`!d i k1 k2 k c.
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
 (`!d i k1 k2 k c.
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
 (`!r d a b:real^N.
    d division_of interval[a,b]
    ==> sum d content = content(interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  OPERATIVE_DIVISION)
     (CONJ MONOIDAL_REAL_ADD OPERATIVE_CONTENT))) THEN
  REWRITE_TAC[sum]);;

let ADDITIVE_CONTENT_TAGGED_DIVISION = prove
 (`!r d a b:real^N.
    d tagged_division_of interval[a,b]
    ==> sum d (\(x,l). content l) = content(interval[a,b])`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
   (MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                  OPERATIVE_TAGGED_DIVISION)
     (CONJ MONOIDAL_REAL_ADD OPERATIVE_CONTENT))) THEN
  REWRITE_TAC[sum]);;

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
 (`!f:real^M->real^1 g:real^M->real^1 s i.
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
 (`!f:real^M->real^1 g:real^M->real^1 s i.
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
 (`!f:real^M->real^N g s t y.
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
 (`!f:real^M->real^N g s t y.
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
(* Finite case of the spike theorem is quite commonly needed.                *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_SPIKE_FINITE = prove
 (`!f:real^M->real^N g s t y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x) /\
        (f has_integral y) t
        ==> (g has_integral y) t`,
  MESON_TAC[HAS_INTEGRAL_SPIKE; NEGLIGIBLE_FINITE]);;

let HAS_INTEGRAL_SPIKE_FINITE_EQ = prove
 (`!f:real^M->real^N g s a b y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> ((f has_integral y) t <=> (g has_integral y) t)`,
  MESON_TAC[HAS_INTEGRAL_SPIKE_FINITE]);;

let INTEGRABLE_SPIKE_FINITE = prove
 (`!f:real^M->real^N g s a b y.
        FINITE s /\ (!x. x IN (t DIFF s) ==> g x = f x)
        ==> f integrable_on t
            ==> g integrable_on  t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[integrable_on] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MP_TAC(SPEC_ALL HAS_INTEGRAL_SPIKE_FINITE) THEN ASM_REWRITE_TAC[]);;

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
 (`!f:real^M->real^N g a b y.
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
 (`!f:real^M->real^N e a b.
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
(* Fundamental theorem of calculus.                                          *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_CALCULUS = prove
 (`!f:real^1->real^N f' a b.
        drop a <= drop b /\
        (!x. x IN interval[a,b]
             ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  let NORM_LEMMA = prove
   (`z = x - y /\ c = a + b
     ==> norm(x) <= a ==> norm(y) <= b ==> norm(z) <= c`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG] THEN
    ASM_SIMP_TAC[REAL_LE_ADD2]) in
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN_ALT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_INTEGRAL_FACTOR_CONTENT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GAUGE_EXISTENCE_LEMMA] THEN
  REWRITE_TAC[SKOLEM_THM; TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^1->real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN STRIP_TAC THEN
  EXISTS_TAC `\x. ball(x:real^1,d(x))` THEN
  ASM_SIMP_TAC[GAUGE_BALL_DEPENDENT] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[CONTENT_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB; LAMBDA_PAIR_THM] THEN
  MP_TAC(ISPECL [`\x:real^1. x`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  ASM_SIMP_TAC[DROP_VSUM; DROP_SUB] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  ASM_REWRITE_TAC[o_THM; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`x:real^1`; `k:real^1->bool`] o el 1 o
              CONJUNCTS o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LT; INTERVAL_EQ_EMPTY_1; NOT_IN_EMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONTENT_1; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`x:real^1`; `u:real^1`] th) THEN
    MP_TAC(SPECL [`x:real^1`; `v:real^1`] th)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `interval[u:real^1,v]`]) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NORM_SUB] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `u:real^1` th) THEN MP_TAC(SPEC `v:real^1` th)) THEN
  SUBGOAL_THEN `u IN interval[u:real^1,v] /\ v IN interval[u,v]`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC NORM_LEMMA THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; NORM_REAL; GSYM drop; DROP_SUB] THEN
  CONJ_TAC THENL [VECTOR_ARITH_TAC; AP_TERM_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REAL_ARITH_TAC);;

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
 (`!f i:real^N j a b c.
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
(* Combined fundamental theorem of calculus.                                 *)
(* ------------------------------------------------------------------------- *)

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
(* General "twiddling" for interval-to-interval function image.              *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_TWIDDLE = prove
 (`!f:real^M->real^N (g:real^M->real^M) h r i a b.
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
  REPEAT GEN_TAC THEN ASM_CASES_TAC `interval[a:real^M,b] = {}` THEN
  ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_INTEGRAL_EMPTY_EQ; VECTOR_MUL_RZERO] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[has_integral] THEN
  ASM_REWRITE_TAC[has_integral_def; has_integral_compact_interval] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e * r:real`) THEN
  ASM_SIMP_TAC[REAL_LT_MUL] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x y:real^M. (d:real^M->real^M->bool) (g x) (g y)` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    SIMP_TAC[gauge; IN; FORALL_AND_THM] THEN
    STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN
    SUBGOAL_THEN `(\y:real^M. (d:real^M->real^M->bool) (g x) (g y)) =
                  {y | g y IN (d (g x))}` SUBST1_TAC
    THENL [SET_TAC[]; ASM_SIMP_TAC[CONTINUOUS_OPEN_PREIMAGE_UNIV]];
    ALL_TAC] THEN
  X_GEN_TAC `p:real^M#(real^M->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\(x,k). (g:real^M->real^M) x, IMAGE g k) p`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ALL_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      REWRITE_TAC[fine; lemma0] THEN
      STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
      ASM SET_TAC[]] THEN
    SUBGOAL_THEN
     `interval[a,b] = IMAGE ((g:real^M->real^M) o h) (interval[a,b])`
    SUBST1_TAC THENL [SIMP_TAC[o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?u v. IMAGE (h:real^M->real^M) (interval[a,b]) =
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
 (`!a b:real^N m c.
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
(* Stronger form of FCT; quite a tedious proof.                              *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR = prove
 (`!f:real^1->real^N f' a b.
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b)
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  let lemma0 = prove
   (`&0 < e /\
     (!x y. x IN s /\ y IN s ==> x = y) /\
     (!x. x IN s ==> norm(f x) <= e)
     ==> norm(vsum s (f:A->real^N)) <= e`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `s:A->bool = {}` THEN
    ASM_SIMP_TAC[VSUM_CLAUSES; NORM_0; REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    SUBGOAL_THEN `s = {a:A}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[VSUM_SING; IN_SING])
  and lemma1a = prove
   (`interval[u,v] SUBSET interval[a,b]
     ==> a IN interval[u,v]
         ==> u:real^1 = a /\ interval[a,v] SUBSET interval[a,b]`,
    REWRITE_TAC[GSYM DROP_EQ; SUBSET_INTERVAL_1; IN_INTERVAL_1] THEN
    REAL_ARITH_TAC)
  and lemma1b = prove
   (`interval[u,v] SUBSET interval[a,b]
     ==> b IN interval[u,v]
         ==> v:real^1 = b /\ interval[u,b] SUBSET interval[a,b]`,
    REWRITE_TAC[GSYM DROP_EQ; SUBSET_INTERVAL_1; IN_INTERVAL_1] THEN
    REAL_ARITH_TAC)
  and NORM_LEMMA = prove
   (`z = x - y /\ c = a + b
     ==> norm(x) <= a ==> norm(y) <= b ==> norm(z) <= c`,
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN REWRITE_TAC[NORM_NEG] THEN
    ASM_SIMP_TAC[REAL_LE_ADD2]) in
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_AT_ALT] THEN
  REPEAT STRIP_TAC THEN FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP
   (REAL_ARITH `a <= b ==> b = a \/ a < b`))
  THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o GEN_REWRITE_RULE I [DROP_EQ]) THEN
    REWRITE_TAC[VECTOR_SUB_REFL] THEN MATCH_MP_TAC HAS_INTEGRAL_NULL THEN
    REWRITE_TAC[CONTENT_EQ_0_1; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_INTEGRAL_FACTOR_CONTENT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; RIGHT_IMP_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[GAUGE_EXISTENCE_LEMMA] THEN
  REWRITE_TAC[SKOLEM_THM; TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^1->real` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `bounded (IMAGE (f:real^1->real^N) (interval[a,b]))`
  MP_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?da. &0 < da /\
         !c. drop a <= drop c /\
             interval[a,c] SUBSET interval[a,b] /\
             interval[a,c] SUBSET ball(a,da)
             ==> norm(content(interval[a,c]) % (f':real^1->real^N) a -
                      (f c - f a))
                 <= (e * (drop b - drop a)) / &4`
   (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "da")))
  THENL
   [FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^1`) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[continuous_within] THEN
    DISCH_THEN(MP_TAC o SPEC `(e * (drop b - drop a)) / &8`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT;
                 ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?l. &0 < l /\ norm(l % f' a:real^N) <= (e * (drop b - drop a)) / &8`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `(f':real^1->real^N) a = vec 0` THEN
      ASM_SIMP_TAC[VECTOR_MUL_RZERO; NORM_0; REAL_LT_IMP_LE; ARITH;
                  REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      EXISTS_TAC `(e * (drop b - drop a)) / &8 / norm(f' a:real^N)` THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_RZERO; NORM_0; REAL_LT_IMP_LE;
        ARITH; REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT] THEN
      REWRITE_TAC[NORM_MUL] THEN ONCE_REWRITE_TAC[REAL_ABS_DIV] THEN
      ASM_SIMP_TAC[NORM_POS_LT; REAL_ARITH `&0 < x ==> abs x = x`;
                   REAL_LT_IMP_NZ; REAL_DIV_RMUL] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs x <= x`) THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_RZERO; NORM_0; REAL_LT_IMP_LE;
        ARITH; REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT];
      ALL_TAC] THEN
    EXISTS_TAC `min (k:real) l` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[VECTOR_SUB] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / &4 = x / &8 + x / &8`] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[NORM_NEG] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REAL_ARITH
       `x <= e ==> y <= x ==> y <= e`)) THEN
      REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      ASM_CASES_TAC `content(interval[a:real^1,c]) = &0` THEN
      ASM_REWRITE_TAC[REAL_ABS_0; REAL_ABS_POS] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [CONTENT_EQ_0_1]) THEN
      SIMP_TAC[CONTENT_1; REAL_NOT_LE; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `interval[a,c] SUBSET ball (a:real^1,min k l)` THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_BALL; dist; NORM_REAL;
                  GSYM drop; DROP_SUB] THEN
      DISCH_THEN(MP_TAC o SPEC `c:real^1`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL_1]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^1` o
     GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_BALL; dist; NORM_REAL;
                  GSYM drop; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?db. &0 < db /\
         !c. drop c <= drop b /\
             interval[c,b] SUBSET interval[a,b] /\
             interval[c,b] SUBSET ball(b,db)
             ==> norm(content(interval[c,b]) % (f':real^1->real^N) b -
                      (f b - f c))
                 <= (e * (drop b - drop a)) / &4`
   (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "da")))
  THENL
   [FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    DISCH_THEN(MP_TAC o SPEC `b:real^1`) THEN
    ASM_SIMP_TAC[IN_INTERVAL_1; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[continuous_within] THEN
    DISCH_THEN(MP_TAC o SPEC `(e * (drop b - drop a)) / &8`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT;
                 ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?l. &0 < l /\ norm(l % f' b:real^N) <= (e * (drop b - drop a)) / &8`
    STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `(f':real^1->real^N) b = vec 0` THEN
      ASM_SIMP_TAC[VECTOR_MUL_RZERO; NORM_0; REAL_LT_IMP_LE; ARITH;
                  REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      EXISTS_TAC `(e * (drop b - drop a)) / &8 / norm(f' b:real^N)` THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_RZERO; NORM_0; REAL_LT_IMP_LE;
        ARITH; REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT] THEN
      REWRITE_TAC[NORM_MUL] THEN ONCE_REWRITE_TAC[REAL_ABS_DIV] THEN
      ASM_SIMP_TAC[NORM_POS_LT; REAL_ARITH `&0 < x ==> abs x = x`;
                   REAL_LT_IMP_NZ; REAL_DIV_RMUL] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs x <= x`) THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_MUL_RZERO; NORM_0; REAL_LT_IMP_LE;
        ARITH; REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT; REAL_OF_NUM_LT];
      ALL_TAC] THEN
    EXISTS_TAC `min (k:real) l` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[VECTOR_SUB] THEN
    MATCH_MP_TAC NORM_TRIANGLE_LE THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / &4 = x / &8 + x / &8`] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN REWRITE_TAC[NORM_NEG] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REAL_ARITH
       `x <= e ==> y <= x ==> y <= e`)) THEN
      REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      ASM_CASES_TAC `content(interval[c:real^1,b]) = &0` THEN
      ASM_REWRITE_TAC[REAL_ABS_0; REAL_ABS_POS] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [CONTENT_EQ_0_1]) THEN
      SIMP_TAC[CONTENT_1; REAL_NOT_LE; REAL_LT_IMP_LE] THEN
      UNDISCH_TAC `interval[c,b] SUBSET ball (b:real^1,min k l)` THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL_1; IN_BALL; dist; NORM_REAL;
                  GSYM drop; DROP_SUB] THEN
      DISCH_THEN(MP_TAC o SPEC `c:real^1`) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM dist] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL_1]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^1` o
     GEN_REWRITE_RULE I [SUBSET]) THEN
    REWRITE_TAC[IN_INTERVAL_1; IN_BALL; dist; NORM_REAL;
                  GSYM drop; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `\x. ball(x:real^1,if x = a then da
                      else if x = b then db
                      else d x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC GAUGE_BALL_DEPENDENT THEN
    GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[]) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH;
                 CONTENT_POS_LT_1];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[CONTENT_1] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[GSYM VSUM_SUB; LAMBDA_PAIR_THM] THEN
  MP_TAC(ISPECL [`\x:real^1. x`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  ASM_SIMP_TAC[DROP_VSUM; DROP_SUB] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  SUBST1_TAC(SET_RULE
   `p = (p INTER {t:real^1#(real^1->bool) | FST t IN {a,b}}) UNION
        (p DIFF {t:real^1#(real^1->bool) | FST t IN {a,b}})`) THEN
  ASM_SIMP_TAC[VSUM_UNION; SUM_UNION; FINITE_INTER; FINITE_DIFF;
               SET_RULE `DISJOINT (s INTER t) (s DIFF t)`] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LE THEN
  MATCH_MP_TAC(REAL_ARITH
   `n2 <= s2 / &2 /\ n1 - s1 <= s2 / &2 ==> n1 + n2 <= s1 + s2`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC VSUM_NORM_LE THEN
    ASM_SIMP_TAC[FINITE_DIFF; o_THM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN
    SIMP_TAC[IN_DIFF; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`x:real^1`; `k:real^1->bool`] o el 1 o
                CONJUNCTS o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `drop u <= drop v` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_NOT_LT; INTERVAL_EQ_EMPTY_1; NOT_IN_EMPTY];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONTENT_1; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`x:real^1`; `u:real^1`] th) THEN
      MP_TAC(SPECL [`x:real^1`; `v:real^1`] th)) THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `interval[u:real^1,v]`]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [NORM_SUB] THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `u:real^1` th) THEN MP_TAC(SPEC `v:real^1` th)) THEN
    SUBGOAL_THEN `u IN interval[u:real^1,v] /\ v IN interval[u,v]`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL];  ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    ASM_SIMP_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC NORM_LEMMA THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; NORM_REAL; GSYM drop; DROP_SUB] THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN AP_TERM_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= s1 /\ x <= (s1 + s2) / &2 ==> x - s1 <= s2 / &2`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
    ASM_SIMP_TAC[FINITE_INTER; IN_INTER; IN_ELIM_THM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; o_THM] THEN
    FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
      GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `k:real^1->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    SIMP_TAC[DROP_SUB; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_UNION; GSYM SUM_UNION; FINITE_INTER; FINITE_DIFF;
               SET_RULE `DISJOINT (s INTER t) (s DIFF t)`] THEN
  REWRITE_TAC[SET_RULE `(s INTER t) UNION (s DIFF t) = s`] THEN
  MP_TAC(ISPECL [`\x:real^1. x`; `p:(real^1#(real^1->bool))->bool`;
                 `a:real^1`; `b:real^1`]
                ADDITIVE_TAGGED_DIVISION_1) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  ASM_SIMP_TAC[DROP_VSUM; DROP_SUB; SUM_LMUL; ETA_AX] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(MESON[]
   `!t. vsum s f = vsum t f /\ norm(vsum t f) <= e
        ==> norm(vsum s f) <= e`) THEN
  EXISTS_TAC `p INTER {t:real^1#(real^1->bool) |
              FST t IN {a, b} /\ ~(content(SND t) = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `(a /\ b) /\ ~(a /\ b /\ c) <=> a /\ b /\ ~c`] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
      GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
    DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `k:real^1->bool`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONTENT_EQ_0_1]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_TRANS) THEN
    SIMP_TAC[DROP_SUB; INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
    SIMP_TAC[IMP_IMP; REAL_LE_ANTISYM; DROP_EQ] THEN
    DISCH_THEN(K ALL_TAC) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE
   `p INTER {t | FST t IN {a, b} /\ ~(content (SND t) = &0)} =
    {t | t IN p /\ FST t = a /\ ~(content (SND t) = &0)} UNION
    {t | t IN p /\ FST t = b /\ ~(content (SND t) = &0)}`] THEN
  ASM_CASES_TAC `a:real^1 = b` THENL
   [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP TAGGED_DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[VSUM_UNION; FINITE_RESTRICT; SET_RULE
   `~(a = b) ==> DISJOINT {t | t IN p /\ FST t = a /\ Q t}
                          {t | t IN p /\ FST t = b /\ Q t}`] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 = x / &4 + x / &4`] THEN
  MATCH_MP_TAC NORM_TRIANGLE_LE THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN MATCH_MP_TAC lemma0 THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; REAL_SUB_LT;
               REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[IN_ELIM_THM; FORALL_PAIR_THM] THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC
       [`x:real^1`; `k:real^1->bool`; `y:real^1`; `l:real^1->bool`] THEN
      STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
      FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o
        GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`a:real^1`; `k:real^1->bool`; `a:real^1`; `l:real^1->bool`]) THEN
      FIRST_ASSUM(MP_TAC o SPEC `a:real^1` o el 1 o CONJUNCTS o
        GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `k:real^1->bool` th) THEN
        MP_TAC(SPEC `l:real^1->bool` th)) THEN ASM_SIMP_TAC[] THEN
      STRIP_TAC THEN STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
      MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP lemma1a)) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; DISJOINT_INTERVAL_1] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [CONTENT_EQ_0_1])) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `k:real^1->bool`] o
          el 1 o CONJUNCTS) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CONTENT_EQ_0_1; REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1;
                   REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `u:real^1 = a` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM DROP_EQ] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL_1]) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^1`; `interval[a:real^1,v]`]) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC
       [`x:real^1`; `k:real^1->bool`; `y:real^1`; `l:real^1->bool`] THEN
      STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
      FIRST_ASSUM(MP_TAC o el 2 o CONJUNCTS o
        GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      DISCH_THEN(MP_TAC o SPECL
       [`b:real^1`; `k:real^1->bool`; `b:real^1`; `l:real^1->bool`]) THEN
      FIRST_ASSUM(MP_TAC o SPEC `b:real^1` o el 1 o CONJUNCTS o
        GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      ASM_REWRITE_TAC[PAIR_EQ] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `k:real^1->bool` th) THEN
        MP_TAC(SPEC `l:real^1->bool` th)) THEN ASM_SIMP_TAC[] THEN
      STRIP_TAC THEN STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
      MATCH_MP_TAC(TAUT `~q ==> (~p ==> q) ==> p`) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP lemma1b)) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; DISJOINT_INTERVAL_1] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
       [CONTENT_EQ_0_1])) THEN REAL_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^1`; `k:real^1->bool`] o
          el 1 o CONJUNCTS) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[CONTENT_EQ_0_1; REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[INTERVAL_UPPERBOUND_1; INTERVAL_LOWERBOUND_1;
                   REAL_LT_IMP_LE] THEN
      SUBGOAL_THEN `v:real^1 = b` SUBST_ALL_TAC THENL
       [REWRITE_TAC[GSYM DROP_EQ] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL_1]) THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
      DISCH_THEN(MP_TAC o SPECL [`b:real^1`; `interval[u:real^1,b]`]) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]]]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form with finite number of exceptional points.                   *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG = prove
 (`!f:real^1->real^N f' s a b.
        FINITE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval(a,b) DIFF s
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  WF_INDUCT_TAC `CARD(s:real^1->bool)` THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:real^1->bool = {}` THEN
  ASM_REWRITE_TAC[DIFF_EMPTY; FINITE_RULES;
                  FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:real^1`) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (c:real^1)`) THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_SIMP_TAC[CARD_EQ_0] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FINITE_DELETE] THEN
  ASM_CASES_TAC `(c:real^1) IN interval(a,b)` THENL
   [STRIP_TAC THEN
    SUBST1_TAC(VECTOR_ARITH
     `(f:real^1->real^N) b - f a = (f c - f a) + (f b - f c)`) THEN
    MATCH_MP_TAC HAS_INTEGRAL_COMBINE THEN
    EXISTS_TAC `c:real^1` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
       EXISTS_TAC `interval[a:real^1,b]` THEN
       ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
     REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_DIFF]) THEN
     REWRITE_TAC[IN_DIFF; IN_INTERVAL_1; IN_DELETE] THEN
     SIMP_TAC[GSYM DROP_EQ] THEN
     ASM_CASES_TAC `(x:real^1) IN s` THEN ASM_REWRITE_TAC[] THEN
     ASM_REAL_ARITH_TAC;
     DISCH_THEN MATCH_MP_TAC THEN
     ASM_SIMP_TAC[SET_RULE
      `~(c IN s) ==> s DIFF (t DELETE c) = s DIFF t`]]);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_STRONG = prove
 (`!f:real^1->real^N f' s a b.
        FINITE s /\
        drop a <= drop b /\ f continuous_on interval[a,b] /\
        (!x. x IN interval[a,b] DIFF s
             ==> (f has_vector_derivative f'(x)) (at x))
        ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR_STRONG THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
  SIMP_TAC[IN_INTERVAL_1; IN_DIFF] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* This doesn't directly involve integration, but that gives an easy proof.  *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_ZERO_UNIQUE_STRONG_INTERVAL = prove
 (`!f:real^1->real^N a b k y.
        FINITE k /\ f continuous_on interval[a,b] /\ f a = y /\
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
      convex s /\ FINITE k /\ f continuous_on s /\ c IN s /\ f c = y /\
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
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
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
      connected s /\ open s /\ FINITE k /\ f continuous_on s /\
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

let HAS_INTEGRAL_RESTRICT_UNIV = prove
 (`!f:real^M->real^N s i.
        ((\x. if x IN s then f x else vec 0) has_integral i) (:real^M) <=>
         (f has_integral i) s`,
  SIMP_TAC[HAS_INTEGRAL_RESTRICT; SUBSET_UNIV]);;

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

let INTEGRAL_RESTRICT_UNIV = prove
 (`!f s. f integrable_on s
         ==> integral UNIV (\x. if x IN s then f x else vec 0) = integral s f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_SIMP_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL]);;

let INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else vec 0) integrable_on (:real^M) <=>
         f integrable_on s`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_RESTRICT_UNIV]);;

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
  MATCH_MP_TAC INTEGRAL_SPIKE THEN
  EXISTS_TAC `{}:real^M->bool` THEN
  REWRITE_TAC[DIFF_EMPTY; NEGLIGIBLE_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE
   `i SUBSET j ==> !x. x IN i ==> f x = if x IN j then f x else b`) THEN
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
 (`!f:real^M->real^N s p i.
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
    W(MP_TAC o PART_MATCH (rhs o rand) INTEGRAL_RESTRICT_UNIV o
      rand o rand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
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
  W(MP_TAC o PART_MATCH (rhs o rand) INTEGRAL_RESTRICT_UNIV o
    rand o rand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
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
(* Absolute integrability (this is the same as Lebesgue integrability).      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("absolutely_integrable_on",(12,"right"));;

let absolutely_integrable_on = new_definition
 `f absolutely_integrable_on s <=>
        f integrable_on s /\ (\x. lift(norm(f x))) integrable_on s`;;

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

let ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION = prove
 (`!f:real^M->real^N.
        f absolutely_integrable_on (:real^M)
        ==> ?B. !d. d division_of (UNIONS d)
                    ==> sum d (\k. norm(integral k f)) <= B`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `drop(integral (:real^M) (\x. lift(norm(f x:real^N))))` THEN
  X_GEN_TAC `d:(real^M->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (UNIONS d) (\x. lift(norm((f:real^M->real^N) x))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    REWRITE_TAC[SUBSET_UNIV; LIFT_DROP; NORM_POS_LE] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I
     [absolutely_integrable_on]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    MAP_EVERY EXISTS_TAC [`(:real^M)`; `d:(real^M->bool)->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]] THEN
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
    EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_COMBINE_DIVISION_TOPDOWN THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ON_SUBDIVISION THEN
    MAP_EVERY EXISTS_TAC [`(:real^M)`; `d:(real^M->bool)->bool`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV]]);;

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

let BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b] /\
        (?B. !d. d division_of interval[a,b]
                 ==> sum d (\k. norm(integral k f)) <= B)
        ==> f absolutely_integrable_on interval[a,b]`,
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

let BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N.
        f integrable_on UNIV /\
        (?B. !d. d division_of (UNIONS d)
                 ==> sum d (\k. norm(integral k f)) <= B)
        ==> f absolutely_integrable_on UNIV`,
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
       BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE_INTERVAL) THEN
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

let ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV = prove
 (`!f s. (\x. if x IN s then f x else vec 0)
              absolutely_integrable_on (:real^M) <=>
         f absolutely_integrable_on s`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_RESTRICT_UNIV;
              COND_RAND; NORM_0; LIFT_NUM]);;

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
  MATCH_MP_TAC BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD] THEN
  MP_TAC(ISPEC `g:real^M->real^N` ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION) THEN
  MP_TAC(ISPEC `f:real^M->real^N` ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION) THEN
  ASM_REWRITE_TAC[] THEN
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
  MATCH_MP_TAC BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
  ASM_SIMP_TAC[INTEGRABLE_LINEAR] THEN
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

let ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f absolutely_integrable_on s ==> f integrable_on s`,
  SIMP_TAC[absolutely_integrable_on]);;

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
  MATCH_MP_TAC BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[] THEN
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
  MATCH_MP_TAC BOUNDED_VARIATION_ABSOLUTELY_INTEGRABLE THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `drop(integral(:real^M) g)` THEN
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
(* Continuity of indefinite integral wrt. one or both bounds of interval.    *)
(* ------------------------------------------------------------------------- *)

let INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
         ==> (\x. integral (interval[a,x]) f) continuous_on interval[a,b]`,
  let lemma = prove
     (`(\(x,k). f x k) = (\p. f (FST p) (SND p))`,
      REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM])
  and lemma' = prove
   (`(!x y. (x,y) IN IMAGE (\(u,v). f u v,g u v) s ==> P x y) <=>
     (!u v. (u,v) IN s ==> P (f u v) (g u v))`,
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]) in
  let lemma_1 = prove
   (`!f:real^M->real^N a b e.
          f integrable_on interval[a,b] /\ &0 < e
          ==> ?d. &0 < d /\
                  !P c. (?m. 1 <= m /\ m <= dimindex(:M) /\ P m) /\
                        (!i. 1 <= i /\ i <= dimindex(:M) /\ P i
                             ==> a$i <= c$i /\ c$i <= b$i /\ c$i <= a$i + d) /\
                        (!i. 1 <= i /\ i <= dimindex(:M) /\ ~(P i)
                             ==> c$i = b$i)
                        ==> norm(integral(interval[a,c]) f) < e`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THENL
     [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      MAP_EVERY X_GEN_TAC [`P:num->bool`; `c:real^M`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `content(interval[a:real^M,c]) = &0`
       (fun th -> ASM_SIMP_TAC[INTEGRAL_NULL; NORM_0; th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REAL_ARITH
       `x = &0 ==> &0 <= y /\ y <= x ==> y = &0`)) THEN
      REWRITE_TAC[CONTENT_POS_LE] THEN MATCH_MP_TAC CONTENT_SUBSET THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_INTEGRAL) THEN
    REWRITE_TAC[has_integral] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &42`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `g0:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC
     `g:real^M->real^M->bool =
       \x. g0(x) INTER
           ball(x,(e / &41 / (norm(f x:real^N) + &1)) *
                  inf(IMAGE (\m. b$m - a$m) (1..dimindex(:M))) /
                  content(interval[a:real^M,b])) INTER
           (if x = a then UNIV
            else ball(x,inf(IMAGE (\m. abs(x$m - a$m))
                            {m | m IN 1..dimindex(:M) /\ ~(x$m = a$m)})))` THEN
    SUBGOAL_THEN `gauge(g:real^M->real^M->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "g" THEN MATCH_MP_TAC GAUGE_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GAUGE_INTER THEN REWRITE_TAC[gauge] THEN CONJ_TAC THEN
      X_GEN_TAC `x:real^M` THEN TRY COND_CASES_TAC THEN
      ASM_REWRITE_TAC[OPEN_BALL; OPEN_UNIV; IN_UNIV; CENTRE_IN_BALL] THEN
      REPEAT((MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LT_DIV) THEN
             CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH; NORM_ARITH
       `&0 < norm x + &1`] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_LT_INF_FINITE o snd) THEN
      (ANTS_TAC THENL
        [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FINITE_RESTRICT] THEN
         SIMP_TAC[IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
                  GSYM NOT_LE; DIMINDEX_GE_1] THEN
         FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
         REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_NUMSEG] THEN
         MESON_TAC[];
         DISCH_THEN SUBST1_TAC]) THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[REAL_SUB_LT; IN_NUMSEG; GSYM REAL_ABS_NZ; REAL_SUB_0;
                   IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?p. p tagged_division_of interval[a:real^M,b] /\
          g0 fine p /\ g fine p /\
          (!t k. (t,k) IN p ==> &0 < content k)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`g:real^M->real^M->bool`; `a:real^M`; `b:real^M`]
            FINE_DIVISION_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:(real^M#(real^M->bool))->bool`
          STRIP_ASSUME_TAC) THEN
      EXISTS_TAC
       `{(x:real^M,k:real^M->bool) | (x,k) IN p /\ ~(content k = &0)}` THEN
      ASM_SIMP_TAC[TAGGED_DIVISION_OF_NONTRIVIAL] THEN
      MATCH_MP_TAC(TAUT `(b ==> a) /\ b /\ c ==> a /\ b /\ c`) THEN
      REPEAT CONJ_TAC THENL
       [EXPAND_TAC "g" THEN SIMP_TAC[fine; SUBSET_INTER];
        MATCH_MP_TAC FINE_SUBSET THEN
        EXISTS_TAC `p:(real^M#(real^M->bool))->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_PAIR_THM] THEN
        SIMP_TAC[IN_ELIM_PAIR_THM];
        REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        ASM_MESON_TAC[TAGGED_DIVISION_OF; CONTENT_LT_NZ]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m t k y. 1 <= m /\ m <= dimindex(:M) /\ (t,k) IN p /\ y IN k /\
                (y:real^M)$m = (a:real^M)$m
                ==> (t:real^M)$m = a$m`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      UNDISCH_TAC `(g:real^M->real^M->bool) fine p` THEN
      REWRITE_TAC[fine] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:real^M`; `k:real^M->bool`]) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
      REPEAT(DISCH_THEN(MP_TAC o CONJUNCT2)) THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IN_BALL; REAL_NOT_LT; dist] THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `abs((t - y:real^M)$m)` THEN
      ASM_SIMP_TAC[COMPONENT_LE_NORM] THEN
      ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) REAL_INF_LE_FINITE o snd) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FINITE_RESTRICT] THEN
        REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXISTS_IN_IMAGE]] THEN
      EXISTS_TAC `m:num` THEN
      ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG; REAL_LE_REFL];
      ALL_TAC] THEN
    ABBREV_TAC
     `p1 = {(x:real^M,k:real^M->bool) |
              (x,k) IN p /\
              ?m. 1 <= m /\ m <= dimindex(:M) /\ x$m = (a:real^M)$m}` THEN
    SUBGOAL_THEN `FINITE(p1:(real^M#(real^M->bool))->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "p1" THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `p:real^M#(real^M->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF_FINITE]; ALL_TAC] THEN
      SIMP_TAC[SUBSET; IN_ELIM_PAIR_THM; FORALL_PAIR_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(p1:real^M#(real^M->bool)->bool = {})` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o REWRITE_RULE[tagged_division_of]) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN
      ASM_SIMP_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY; REAL_LT_IMP_LE] THEN
      EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
      REWRITE_TAC[NOT_FORALL_THM; LEFT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `t:real^M` THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
      EXISTS_TAC `t:real^M,k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `1` THEN REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `a:real^M`] THEN
      ASM_REWRITE_TAC[DIMINDEX_GE_1; LE_REFL];
      ALL_TAC] THEN
    ABBREV_TAC
     `d = inf (IMAGE (\(m,t:real^M,k).
                  ((interval_upperbound k:real^M)$m - (a:real^M)$m))
                  ((1..dimindex(:M)) CROSS p1))` THEN
    SUBGOAL_THEN
     `&0 < d /\
      !t k m. (t:real^M,k) IN p1 /\ 1 <= m /\ m <= dimindex(:M)
              ==> d <= (interval_upperbound k:real^M)$m - (a:real^M)$m`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `IMAGE (\(m,t:real^M,k).
                  ((interval_upperbound k:real^M)$m - (a:real^M)$m))
                  ((1..dimindex(:M)) CROSS p1)` INF_FINITE) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[IMAGE_EQ_EMPTY; CROSS_EQ_EMPTY; NUMSEG_EMPTY;
          FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1;
          FINITE_IMAGE; FINITE_CROSS];
        ASM_REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
        MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[IN_CROSS; IN_NUMSEG] THEN
        CONJ_TAC THENL [REWRITE_TAC[IN_IMAGE]; MESON_TAC[]] THEN
        REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_PAIR_THM] THEN
        MAP_EVERY X_GEN_TAC [`m:num`; `t:real^M`; `k:real^M->bool`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
        REWRITE_TAC[IN_CROSS; IN_NUMSEG] THEN
        DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
        EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
        SUBGOAL_THEN `k SUBSET interval[a:real^M,b]` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < content(k:real^M->bool)` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
        DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
        SIMP_TAC[CONTENT_POS_LT_EQ; INTERVAL_UPPERBOUND; REAL_LT_IMP_LE;
                 SUBSET_INTERVAL; REAL_SUB_LT] THEN
        ASM_MESON_TAC[REAL_LET_TRANS]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m.  1 <= m /\ m <= dimindex(:M) ==> (a:real^M)$m + d <= (b:real^M)$m`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o
       GEN_REWRITE_RULE I [TAGGED_DIVISION_OF_ALT]) THEN
      DISCH_THEN(MP_TAC o SPEC `a:real^M`) THEN
      REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^M`; `k:real^M->bool`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`t:real^M`; `k:real^M->bool`; `m:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN EXPAND_TAC "p1" THEN
        REWRITE_TAC[IN_ELIM_PAIR_THM] THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `a:real^M`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      SUBGOAL_THEN `~(k = {}) /\ k SUBSET interval[a:real^M,b]` MP_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` MP_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST1_TAC) THEN
      SIMP_TAC[IMP_CONJ; INTERVAL_UPPERBOUND; INTERVAL_NE_EMPTY;
               REAL_LT_IMP_LE; SUBSET_INTERVAL; IN_INTERVAL] THEN
      DISCH_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
      DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `content(interval[a:real^M,c]) = &0` THENL
     [SUBGOAL_THEN `integral(interval[a,c]) (f:real^M->real^N) = vec 0`
      SUBST1_TAC THENL [ASM_MESON_TAC[INTEGRAL_NULL]; ALL_TAC] THEN
      REWRITE_TAC[NORM_0] THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM CONTENT_LT_NZ]) THEN
      DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
      REWRITE_TAC[CONTENT_POS_LT_EQ] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `interval[a:real^M,c] SUBSET interval[a,b]` MP_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL] THEN DISCH_TAC THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_MESON_TAC[REAL_LE_REFL; REAL_LE_TRANS];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
    REWRITE_TAC[SUBSET_INTERVAL] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\(t:real^M,k). (t,k INTER interval[a,c]))
            {(t,k) | (t,k) IN p1 /\
                     !i. 1 <= i /\ i <= dimindex(:M) /\ P i
                         ==> t$i = a$i}
      tagged_division_of interval[a,c]`
    ASSUME_TAC THENL
     [REWRITE_TAC[TAGGED_DIVISION_OF_ALT; tagged_partial_division_of] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                  lemma'; IN_ELIM_PAIR_THM] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
           FINITE_SUBSET)) THEN
        SIMP_TAC[SUBSET; IN_ELIM_PAIR_THM; FORALL_PAIR_THM];
        MAP_EVERY X_GEN_TAC [`t:real^M`; `k:real^M->bool`] THEN
        DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
        EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN DISCH_TAC THEN
        REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF];
          REWRITE_TAC[IN_INTERVAL] THEN X_GEN_TAC `i:num` THEN
          STRIP_TAC THEN
          ASM_CASES_TAC `(P:num->bool) i` THEN ASM_REWRITE_TAC[] THENL
           [ASM_MESON_TAC[REAL_LE_REFL];
            SUBGOAL_THEN `t IN interval[a:real^M,b]` MP_TAC THENL
             [ASM_MESON_TAC[SUBSET; TAGGED_DIVISION_OF]; ALL_TAC] THEN
            SIMP_TAC[IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_REFL]];
          SET_TAC[];
          SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
           (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
          THENL
           [ASM_MESON_TAC[TAGGED_DIVISION_OF];
            REWRITE_TAC[INTER_INTERVAL] THEN MESON_TAC[]]];
        MAP_EVERY X_GEN_TAC [`x1:real^M`; `k1:real^M->bool`] THEN
        EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
        REPEAT DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [ `x2:real^M`; `k2:real^M->bool`] THEN
        DISCH_TAC THEN DISCH_TAC THEN
        ASM_CASES_TAC `x1:real^M = x2 /\ k1:real^M->bool = k2` THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `interior(k1 INTER i) SUBSET interior k1 /\
          interior(k2 INTER i) SUBSET interior k2 /\
          interior(k1) INTER interior(k2) = {}
          ==> interior(k1 INTER i) INTER interior(k2 INTER i) = {}`) THEN
        SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF]) THEN
        DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
        ASM_MESON_TAC[PAIR_EQ];
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN ABBREV_TAC
         `y:real^M = lambda i. if P i then (a:real^M)$i else (x:real^M)$i` THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TAGGED_DIVISION_OF_ALT]) THEN
        DISCH_THEN(MP_TAC o SPEC `y:real^M` o CONJUNCT2) THEN ANTS_TAC THENL
         [REWRITE_TAC[IN_INTERVAL] THEN X_GEN_TAC `i:num` THEN
          EXPAND_TAC "y" THEN SIMP_TAC[LAMBDA_BETA] THEN STRIP_TAC THEN
          UNDISCH_TAC `x IN interval[a:real^M,c]` THEN
          REWRITE_TAC[IN_INTERVAL] THEN
          DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
          COND_CASES_TAC THEN ASM_MESON_TAC[REAL_LT_IMP_LE];
          ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^M` THEN
        DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `k INTER interval[a:real^M,c]` THEN
        REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
        REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
        MAP_EVERY EXISTS_TAC [`t:real^M`; `k:real^M->bool`] THEN
        SUBGOAL_THEN
         `!i. 1 <= i /\ i <= dimindex(:M) /\ P i
              ==> (t:real^M)$i = (a:real^M)$i`
        ASSUME_TAC THENL
         [X_GEN_TAC `j:num` THEN REPEAT DISCH_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `y:real^M`] THEN
          ASM_REWRITE_TAC[] THEN
          EXPAND_TAC "y" THEN ASM_SIMP_TAC[LAMBDA_BETA];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
        MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
         [EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
          ASM_MESON_TAC[];
          DISCH_TAC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[IN_INTER]] THEN
        SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
         (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
        THENL [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
        UNDISCH_TAC `y IN interval[u:real^M,v]` THEN
        REWRITE_TAC[IN_INTERVAL] THEN MATCH_MP_TAC MONO_FORALL THEN
        EXPAND_TAC "y" THEN SIMP_TAC[LAMBDA_BETA] THEN
        X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a:real^M)$i` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `x IN interval[a:real^M,c]` THEN
          REWRITE_TAC[IN_INTERVAL] THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`t:real^M`; `interval[u:real^M,v]`; `i:num`]) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(interval[u:real^M,v] = {})` MP_TAC THENL
         [ASM_MESON_TAC[TAGGED_DIVISION_OF; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
        SIMP_TAC[INTERVAL_UPPERBOUND; INTERVAL_NE_EMPTY] THEN
        DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `x <= a + d ==> d <= v - a ==> x <= v`) THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c:real^M)$i` THEN
        ASM_MESON_TAC[IN_INTERVAL]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`;
                   `g0:real^M->real^M->bool`; `e / &42`]
            HENSTOCK_LEMMA_PART1) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC
     `IMAGE (\(t:real^M,k). (t,k INTER interval[a:real^M,c]))
            {(t,k) | (t,k) IN p1 /\
                     !i. 1 <= i /\ i <= dimindex(:M) /\ P i
                         ==> t$i = a$i}`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC TAGGED_PARTIAL_DIVISION_OF_SUBSET THEN
        EXISTS_TAC `interval[a:real^M,c]` THEN
        RULE_ASSUM_TAC(REWRITE_RULE[tagged_division_of]) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[fine; IN_ELIM_PAIR_THM; lemma'] THEN
        MAP_EVERY X_GEN_TAC [`x:real^M`; `k:real^M->bool`] THEN
        EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE `k SUBSET t ==> k INTER s SUBSET t`) THEN
        UNDISCH_TAC `(g0:real^M->real^M->bool) fine p` THEN
        REWRITE_TAC[fine] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC
     `!i. 1 <= i /\ i <= dimindex (:M) /\ ~P i
          ==> (c:real^M)$i = (b:real^M)$i` THEN
    UNDISCH_TAC
      `!m t k y.
          1 <= m /\ m <= dimindex (:M) /\ t,k IN p /\ y IN k /\
          (y:real^M)$m = (a:real^M)$m
          ==> (t:real^M)$m = a$m` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM CONTRAPOS_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `FINITE {(t:real^M,k:real^M->bool) |
              (t,k) IN p1 /\ !i. 1 <= i /\ i <= dimindex(:M) /\ P i
                                 ==> t$i = (a:real^M)$i}`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP(REWRITE_RULE[IMP_CONJ]
           FINITE_SUBSET)) THEN
      SIMP_TAC[SUBSET; IN_ELIM_PAIR_THM; FORALL_PAIR_THM];
      ALL_TAC] THEN
    REWRITE_TAC[lemma] THEN
    ASM_SIMP_TAC[VSUM_SUB; FINITE_IMAGE] THEN MATCH_MP_TAC(NORM_ARITH
     `i = i' /\ norm b < e / &39
      ==> norm(b - i') <= e / &42 ==> norm(i) < e`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM lemma] THEN
      MATCH_MP_TAC INTEGRAL_COMBINE_TAGGED_DIVISION_TOPDOWN THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `interval[a:real^M,b:real^M]` THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM lemma] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    MATCH_MP_TAC(REAL_ARITH `s < e ==> n <= s ==> n < e`) THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [LAMBDA_PAIR_THM] THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `(e / &41 / content(interval[a:real^M,b]) *
      (b$m - a$m) / ((c:real^M)$m - a$m)) *
      sum (IMAGE (\(x,k). x,k INTER interval [a,c])
                 {(t:real^M,k:real^M->bool) |
              (t,k) IN p1 /\ !i. 1 <= i /\ i <= dimindex(:M) /\ P i
                                 ==> t$i = (a:real^M)$i})
          (\(x:real^M,k:real^M->bool). content k)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`t:real^M`; `k:real^M->bool`] THEN
      EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` MP_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF]; ALL_TAC] THEN
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC) THEN
      REWRITE_TAC[NORM_MUL; INTER_INTERVAL] THEN
      SIMP_TAC[CONTENT_POS_LE; REAL_ARITH `&0 <= x ==> abs x = x`] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[CONTENT_POS_LE] THEN
      MATCH_MP_TAC(REAL_ARITH `x + &1 <= a ==> x <= a`) THEN
      REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      REWRITE_TAC[GSYM real_div] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT; ASSUME `1 <= m`;
       ASSUME `m <= dimindex(:M)`;
       ASSUME `!i. 1 <= i /\ i <= dimindex (:M)
                   ==> (a:real^M)$i < (c:real^M)$i`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; NORM_ARITH `&0 < norm x + &1`] THEN
      REWRITE_TAC[REAL_LE_SUB_RADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(a:real^M)$m + d` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`t:real^M`; `interval[u:real^M,v]`; `m:num`]) THEN
      EXPAND_TAC "p1" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
       `v - a <= x ==> d <= v - a ==> a + d <= x + a`) THEN
      UNDISCH_TAC `(g:real^M->real^M->bool) fine p` THEN REWRITE_TAC[fine] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:real^M`; `interval[u:real^M,v]`]) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "g" THEN REWRITE_TAC[SUBSET_INTER] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      SUBGOAL_THEN `~(interval[u:real^M,v] = {})` MP_TAC THENL
       [ASM_MESON_TAC[TAGGED_DIVISION_OF; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; INTERVAL_UPPERBOUND] THEN DISCH_TAC THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `v:real^M`) THEN
      ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY; IN_BALL] THEN
      MATCH_MP_TAC(REAL_ARITH `abs d <= e /\ y <= x ==> e < y ==> d <= x`) THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
        ASM_MESON_TAC[COMPONENT_LE_NORM; VECTOR_SUB_COMPONENT];
        ALL_TAC] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_INV_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH
       `b1 * e * k * c * n = e * k * n * b1 * c`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
      REWRITE_TAC[CONTENT_POS_LE] THEN
      SIMP_TAC[REAL_INF_LE_FINITE; FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY;
               NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[IN_NUMSEG; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &41 * &1 ==> x < e / &39`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH
      `inv x * a * inv y * z:real = (a * z) * inv x * inv y`] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
    FIRST_ASSUM(fun th ->
      W(MP_TAC o PART_MATCH (lhs o rand)
      (MATCH_MP(REWRITE_RULE[IMP_CONJ] SUM_OVER_TAGGED_DIVISION_LEMMA) th) o
      lhand o snd)) THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
      [MATCH_MP ADDITIVE_CONTENT_DIVISION
        (MATCH_MP DIVISION_OF_TAGGED_DIVISION th)]) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL_CASES; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `1..dimindex(:M) = m INSERT ((1..dimindex(:M)) DELETE m)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `x IN s ==> s = x INSERT (s DELETE x)`) THEN
      ASM_REWRITE_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC(REAL_ARITH
     `(ba * ca) * p1 <= (ba * ca) * p2 ==> ca * p1 * ba <= ba * p2 * ca`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC PRODUCT_LE THEN
    REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; IN_DELETE; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= c /\ c <= b ==> &0 <= c - a /\ c - a <= b - a`) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]) in
  let lemma_2 = prove
   (`!f:real^M->real^N a b c e.
          f integrable_on interval[a,b] /\ c IN interval[a,b] /\ &0 < e
          ==> ?d. &0 < d /\
                  !x. x IN interval[a,b] /\
                      (!i. 1 <= i /\ i <= dimindex(:M) ==> abs(x$i - c$i) <= d)
                      ==> norm(integral(interval[a,x]) f -
                               integral(interval[a,c]) f) < e`,
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; GSYM CONJ_ASSOC] THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`; `c:real^M`]
          INTEGRAL_INTERVALS_DIFF_INCLUSION_EXCLUSION) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN
     `!e. &0 < e
          ==> ?k. &0 < k /\
                  !t. t SUBSET 1..dimindex(:M)
                      ==> !s. s SUBSET 1..dimindex(:M)
                              ==> ~(s = {})
                                  ==>
                  !u v. u IN interval[a,b] /\ v IN interval[a,b] /\
                        (!i. 1 <= i /\ i <= dimindex(:M) ==> u$i <= v$i) /\
                        (!i. 1 <= i /\ i <= dimindex(:M) /\ i IN s
                             ==> u$i = c$i \/ v$i = c$i) /\
                        (!i. 1 <= i /\ i <= dimindex(:M) /\ i IN s
                             ==> (v$i = c$i <=> i IN t)) /\
                        (!i. 1 <= i /\ i <= dimindex(:M) /\ i IN s
                             ==> abs(u$i - v$i) <= k) /\
                        (!i. 1 <= i /\ i <= dimindex(:M) /\ ~(i IN s)
                             ==> u$i = a$i /\ v$i = (c:real^M)$i)
                        ==> norm(integral(interval[u,v]) (f:real^M->real^N))
                            < e`
    ASSUME_TAC THENL
     [ALL_TAC;
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `e / &2 / &2 pow (dimindex(:M))`) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2; REAL_HALF] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `d:real^M` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
      REWRITE_TAC[SET_RULE `{s | ~(s = a) /\ P s} = {s | P s} DELETE a`] THEN
      SIMP_TAC[FINITE_DELETE; FINITE_POWERSET; FINITE_NUMSEG] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD({s | s SUBSET 1..dimindex(:M)} DELETE {})) *
                  e / &2 / &2 pow (dimindex(:M))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_BOUND THEN
        SIMP_TAC[FINITE_DELETE; FINITE_POWERSET; FINITE_NUMSEG] THEN
        X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
        STRIP_TAC THEN REWRITE_TAC[NORM_MUL; REAL_ABS_POW; REAL_ABS_NEG] THEN
        REWRITE_TAC[REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o
          REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
        MAP_EVERY EXISTS_TAC
         [`{i | i IN 1..dimindex(:M) /\ (d:real^M)$i <= (c:real^M)$i}`;
          `s:num->bool`] THEN
        ASM_SIMP_TAC[LAMBDA_BETA; IN_ELIM_THM] THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        SIMP_TAC[IN_INTERVAL; LAMBDA_BETA; IN_ELIM_THM] THEN
        SIMP_TAC[IN_NUMSEG] THEN REPEAT CONJ_TAC THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
        TRY COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
        REWRITE_TAC[REAL_ARITH
         `(c * e) / &2 <= e / &2 * p <=> e * c <= e * p`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        SIMP_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
        SIMP_TAC[CARD_DELETE; FINITE_POWERSET; FINITE_NUMSEG;
                 CARD_POWERSET] THEN
        REWRITE_TAC[CARD_NUMSEG_1] THEN ARITH_TAC]] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC EPSILON_DELTA_MINIMAL THEN
    CONJ_TAC THENL [SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      REPEAT(MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[]) THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC EPSILON_DELTA_MINIMAL THEN
    CONJ_TAC THENL [SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    X_GEN_TAC `s:num->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s:num->bool = {}` THEN ASM_REWRITE_TAC[] THENL
     [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\x:real^M.
          (f:real^M->real^N)
          (lambda i. (if i IN s INTER t then -- &1 else &1) * x$i)`;
      `(lambda i. if i IN s then
                    if i IN t then --((c:real^M)$i) else (c:real^M)$i
                  else (a:real^M)$i):real^M`;
      `(lambda i. if i IN s then
                    if i IN t then --((a:real^M)$i) else (b:real^M)$i
                  else (c:real^M)$i):real^M`;
      `e:real`]
          lemma_1) THEN
    SIMP_TAC[LAMBDA_BETA] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          INTEGRABLE_STRETCH)) THEN
      DISCH_THEN(MP_TAC o ISPEC
       `(\i. if i IN s INTER t then -- &1 else &1):num->real`) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INTEGRABLE_ON_SUBINTERVAL) THEN
      REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN
      COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[SUBSET_INTERVAL; LAMBDA_BETA] THEN
      REWRITE_TAC[REAL_ARITH
       `inv(if p then x else y):real = if p then inv x else inv y`] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL; INTERVAL_NE_EMPTY]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      MAP_EVERY ASM_CASES_TAC [`(i:num) IN s`; `(i:num) IN t`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i:num. i IN s`) THEN
    DISCH_THEN(MP_TAC o SPEC
     `(lambda i. if i IN s then if i IN t then --((u:real^M)$i)
                                else (v:real^M)$i
                 else (c:real^M)$i):real^M`) THEN
    SIMP_TAC[LAMBDA_BETA] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[IN_NUMSEG]; ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^M->real^N) integrable_on interval[u,v]` MP_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `interval[a:real^M,b]` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
      ASM_SIMP_TAC[SUBSET_INTERVAL];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_INTEGRAL_INTEGRAL] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_STRETCH)) THEN
    DISCH_THEN(MP_TAC o ISPEC
       `(\i. if i IN s INTER t then -- &1 else &1):num->real`) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_ARITH `abs(if p then -- &1 else &1) = &1`] THEN
    REWRITE_TAC[PRODUCT_ONE; REAL_INV_1; VECTOR_MUL_LID] THEN
    DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH
     `inv(if p then -- &1 else &1) = if p then -- &1 else &1`] THEN
    REWRITE_TAC[IMAGE_STRETCH_INTERVAL] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[INTERVAL_NE_EMPTY]; ALL_TAC] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[PAIR_EQ; CART_EQ; LAMBDA_BETA; IN_INTER] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; continuous_within] THEN
  X_GEN_TAC `c:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`; `c:real^M`;
                 `e:real`] lemma_2) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^M` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; REAL_LE_TRANS]);;

let INDEFINITE_INTEGRAL_CONTINUOUS_LEFT = prove
 (`!f:real^M->real^N a b.
        f integrable_on interval[a,b]
        ==> (\x. integral(interval[x,b]) f) continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `interval[a:real^M,b] = {}` THENL
   [ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. integral(interval[--b,x]) (\x. (f:real^M->real^N)(--x)))
    continuous_on interval[--b,--a]`
  MP_TAC THENL
   [MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    REWRITE_TAC[VECTOR_ARITH `--x:real^N = --(&1) % x + vec 0`] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`-- &1:real`; `vec 0:real^M`] o
     MATCH_MP (REWRITE_RULE[IMP_CONJ] INTEGRABLE_AFFINITY)) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; VECTOR_NEG_0];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_on] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `--x:real^M`) THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    REWRITE_TAC[IN_INTERVAL] THEN
    SIMP_TAC[REAL_LE_NEG2; VECTOR_NEG_COMPONENT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `--y:real^M`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NORM_ARITH `dist(--y:real^N,--x) = dist(y,x)`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL]) THEN
    REWRITE_TAC[IN_INTERVAL] THEN
    SIMP_TAC[REAL_LE_NEG2; VECTOR_NEG_COMPONENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^M->real^N) integrable_on interval[x,b] /\
    (f:real^M->real^N) integrable_on interval[y,b]`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `interval[a:real^M,b]` THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_INTEGRAL_INTEGRAL] THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o
    SPECL [`-- &1:real`; `vec 0:real^M`] o
    MATCH_MP(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_AFFINITY))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
  SUBGOAL_THEN `~(interval[x:real^M,b] = {}) /\
                ~(interval[y:real^M,b] = {})`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_SIMP_TAC[INTERVAL_NE_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_NEG_0; VECTOR_ADD_RID;
              VECTOR_MUL_LNEG; VECTOR_MUL_LID] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_INV_1; VECTOR_MUL_LID] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE)) THEN
  REWRITE_TAC[]);;

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
  let tac =
    MP_TAC(ISPECL
     [`f:real^M->real^N`; `a:real^M`; `d':real^M`; `c':real^M`]
        INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_LEFT) THEN
    MP_TAC(ISPECL
     [`f:real^M->real^N`; `a:real^M`; `d:real^M`; `c:real^M`]
        INTEGRAL_INTERVALS_INCLUSION_EXCLUSION_LEFT) THEN
    REPEAT(ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL; INTERVAL_NE_EMPTY]) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^M,b]` THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL; REAL_LE_REFL];
        ASM_SIMP_TAC[IN_INTERVAL; REAL_LT_IMP_LE]];
      DISCH_THEN SUBST1_TAC]) THEN
    SIMP_TAC[GSYM VSUM_SUB; FINITE_POWERSET; FINITE_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_NORM o lhand o snd) THEN
    SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ y <= e / &2 ==> x <= y ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
    SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG; GSYM CARD_EQ_0;
             CARD_POWERSET] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ; CARD_NUMSEG_1; GSYM REAL_OF_NUM_POW] THEN
    X_GEN_TAC `s:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
    REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:num->bool`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL; INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN ASM_MESON_TAC[];
      SIMP_TAC[LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(c' - c) <= k /\ abs(d' - d) <= k
        ==> abs((if p then c' else d') - (if p then c else d)) <= k`) THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]] in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\
        !s. s SUBSET 1..dimindex(:M)
            ==> !x. x IN interval[a,b] /\
                    (!i. 1 <= i /\ i <= dimindex(:M)
                         ==> abs(x$i - (if i IN s then c$i else d$i)) <= k)
                    ==> norm(integral (interval [a,x]) f -
                             integral (interval [a,(lambda i. if i IN s
                                                          then (c:real^M)$i
                                                          else (d:real^M)$i)])
                                      (f:real^M->real^N))
                        <= e / &2 / &2 pow dimindex(:M)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EPSILON_DELTA_MINIMAL THEN
    CONJ_TAC THENL [SIMP_TAC[FINITE_POWERSET; FINITE_NUMSEG]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN STRIP_TAC THEN
      REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    X_GEN_TAC `s:num->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `a:real^M`; `b:real^M`]
        INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT) THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; continuous_within] THEN
    DISCH_THEN(MP_TAC o SPEC
     `(lambda i. if i IN s then (c:real^M)$i else (d:real^M)$i):real^M`) THEN
    ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
      ASM_SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2 / &2 pow dimindex(:M)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT; ARITH; dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k / &2 / &(dimindex(:M))` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; ARITH; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1] THEN
    X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < k /\ y <= k / &2 ==> x <= y ==> x < k`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; CARD_NUMSEG_1; LAMBDA_BETA;
                 VECTOR_SUB_COMPONENT; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!i. 1 <= i /\ i <= dimindex(:M) ==> (c:real^M)$i < (d:real^M)$i`
  THENL
   [SUBGOAL_THEN
     `?u. &0 < u /\
          !c' d'. norm(c' - c) <= u /\ norm(d' - d) <= u
                  ==> ~(interval[c':real^M,d'] = {})`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `inf(IMAGE
             (\i. (d:real^M)$i - (c:real^M)$i) (1..dimindex(:M))) / &2` THEN
      REWRITE_TAC[REAL_ARITH `x <= y / &2 <=> &2 * x <= y`] THEN
      SIMP_TAC[REAL_LE_INF_FINITE; FINITE_IMAGE; FINITE_NUMSEG;
               REAL_HALF; REAL_LT_INF_FINITE;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG; REAL_SUB_LT] THEN
      REPEAT GEN_TAC THEN REWRITE_TAC[INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `i:num` THEN DISCH_THEN(fun t -> STRIP_TAC THEN MP_TAC t) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
       `abs(c' - ci) <= nc /\ abs(d' - di) <= nd
        ==> &2 * nc <= di - ci /\ &2 * nd <= di - ci
            ==> c' <= d'`) THEN
      ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM];
      ALL_TAC] THEN
    EXISTS_TAC `min u k` THEN
    ASM_REWRITE_TAC[REAL_LE_MIN; REAL_LT_MIN] THEN
    MAP_EVERY X_GEN_TAC [`c':real^M`; `d':real^M`] THEN STRIP_TAC THEN
    tac;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `!i. 1 <= i /\ i <= dimindex(:M) ==> (c:real^M)$i <= (d:real^M)$i`
  THENL
   [EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`c':real^M`; `d':real^M`] THEN STRIP_TAC THEN
    ASM_CASES_TAC
     `!i. 1 <= i /\ i <= dimindex(:M) ==>  (c':real^M)$i <= (d':real^M)$i`
    THENL
     [tac;
      MATCH_MP_TAC(NORM_ARITH
       `&0 < e /\ x = vec 0 /\ y = vec 0 ==> norm(x - y:real^N) < e`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC INTEGRAL_NULL THEN REWRITE_TAC[CONTENT_EQ_0] THEN
      ASM_MESON_TAC[REAL_LE_TOTAL; REAL_LTE_TOTAL]];
    SUBGOAL_THEN `?j. 1 <= j /\ j <= dimindex(:M) /\
                      (d:real^M)$j < (c:real^M)$j` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_LET_TOTAL]; ALL_TAC] THEN
    EXISTS_TAC `((c:real^M)$j - (d:real^M)$j) / &2` THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; REAL_HALF] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(NORM_ARITH
     `&0 < e /\ x = vec 0 /\ y = vec 0 ==> norm(x - y:real^N) < e`) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC INTEGRAL_NULL THEN REWRITE_TAC[CONTENT_EQ_0] THENL
     [EXISTS_TAC `j:num`; ASM_MESON_TAC[REAL_LE_TOTAL]] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `!c:real^M d:real^M.
        norm(c' - c) <= (c$j - d$j) / &2 /\
        norm(d' - d) <= (c$j - d$j) / &2 /\
        abs(c'$j - c$j) <= norm(c' - c) /\
        abs(d'$j - d$j) <= norm(d' - d)
        ==> d'$j <= c'$j`) THEN
    MAP_EVERY EXISTS_TAC [`c:real^M`; `d:real^M`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; COMPONENT_LE_NORM]]);;

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
