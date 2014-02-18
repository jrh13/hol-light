(* ========================================================================= *)
(* Brunn-Minkowski theorem and related results.                              *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* First, the special case of a box.                                         *)
(* ------------------------------------------------------------------------- *)

let BRUNN_MINKOWSKI_INTERVAL = prove
 (`!a b c d:real^N.
    ~(interval[a,b] = {}) /\ ~(interval[c,d] = {})
    ==> root (dimindex(:N))
             (measure {x + y | x IN interval[a,b] /\ y IN interval[c,d]})
        >= root (dimindex(:N)) (measure(interval[a,b])) +
           root (dimindex(:N)) (measure(interval[c,d]))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUMS_INTERVALS; real_ge] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  ASM_CASES_TAC `measure(interval[a:real^N,b]) = &0` THENL
   [ASM_SIMP_TAC[ROOT_0; DIMINDEX_GE_1; LE_1; REAL_ADD_LID;
                 ROOT_MONO_LE_EQ; MEASURE_POS_LE; MEASURABLE_INTERVAL] THEN
    ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL;
                 VECTOR_ADD_COMPONENT;
                 REAL_ARITH `a <= b /\ c <= d ==> a + c <= b + d`] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SIMP_TAC[MEASURABLE_MEASURE_EQ_0; MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[NEGLIGIBLE_INTERVAL; INTERVAL_NE_EMPTY] THEN STRIP_TAC] THEN
  ASM_CASES_TAC `measure(interval[c:real^N,d]) = &0` THENL
   [ASM_SIMP_TAC[ROOT_0; DIMINDEX_GE_1; LE_1; REAL_ADD_RID;
                 ROOT_MONO_LE_EQ; MEASURE_POS_LE; MEASURABLE_INTERVAL] THEN
    ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL;
                 VECTOR_ADD_COMPONENT;
                 REAL_ARITH `a <= b /\ c <= d ==> a + c <= b + d`] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    SIMP_TAC[MEASURABLE_MEASURE_EQ_0; MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[NEGLIGIBLE_INTERVAL; INTERVAL_NE_EMPTY] THEN STRIP_TAC] THEN
  ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL; VECTOR_ADD_COMPONENT;
               REAL_ARITH `a <= b /\ c <= d ==> a + c <= b + d`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_LE_LDIV_EQ o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ROOT_POS_LT THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; PRODUCT_POS_LT_NUMSEG; IN_NUMSEG;
                 REAL_ARITH `a < b /\ c < d ==> &0 < (b + d) - (a + c)`;
                 DIMINDEX_GE_1; LE_1];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[GSYM REAL_ROOT_DIV] THEN
  REWRITE_TAC[GSYM PRODUCT_DIV_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (1..dimindex(:N))
        (\i. ((b:real^N)$i - (a:real^N)$i) /
             ((b$i + d$i) - (a$i + c$i))) / &(dimindex(:N)) +
    sum (1..dimindex(:N))
        (\i. ((d:real^N)$i - (c:real^N)$i) /
             ((b$i + d$i) - (a$i + c$i))) / &(dimindex(:N))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) REAL_ROOT_LE o snd) THEN
    (ANTS_TAC THENL
      [SIMP_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_EQ; DIMINDEX_GE_1; LE_1;
                REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
       MATCH_MP_TAC SUM_POS_LE_NUMSEG;
       DISCH_THEN SUBST1_TAC THEN  MATCH_MP_TAC AGM THEN
       SIMP_TAC[HAS_SIZE_NUMSEG_1; DIMINDEX_GE_1; LE_1; IN_NUMSEG]]) THEN
     X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
     MATCH_MP_TAC REAL_LE_DIV THEN
     REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
     REWRITE_TAC[real_div; GSYM REAL_ADD_RDISTRIB] THEN
     REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN
     ASM_SIMP_TAC[REAL_FIELD
      `a < b /\ c < d
       ==> (b - a) * inv((b + d) - (a + c)) +
           (d - c) * inv((b + d) - (a + c)) = &1`] THEN
     REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
     ASM_SIMP_TAC[REAL_MUL_RID; REAL_MUL_RINV; REAL_LE_REFL;
                  REAL_OF_NUM_EQ; DIMINDEX_NONZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Now for a finite union of boxes.                                          *)
(* ------------------------------------------------------------------------- *)

let BRUNN_MINKOWSKI_ELEMENTARY = prove
 (`!s t:real^N->bool.
    (s = {} <=> t = {}) /\ (?d. d division_of s) /\ (?d. d division_of t)
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)`,
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`s:real^N->bool`; `t:real^N->bool`;
    `d1:(real^N->bool)->bool`; `d2:(real^N->bool)->bool`] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[NOT_IN_EMPTY; SET_RULE `{f x y |x,y| F} = {}`] THEN
    SIMP_TAC[MEASURE_EMPTY; ROOT_0; DIMINDEX_NONZERO] THEN
    STRIP_TAC THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q /\ r ==> s <=> q /\ p /\ r ==> s`]] THEN
  X_CHOOSE_THEN `n:num` MP_TAC (ISPEC
   `CARD(d1:(real^N->bool)->bool) + CARD(d2:(real^N->bool)->bool)`
   (GSYM EXISTS_REFL)) THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
   [`t:real^N->bool`; `s:real^N->bool`;
    `d2:(real^N->bool)->bool`; `d1:(real^N->bool)->bool`; `n:num`] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[MESON[]
   `(!m. m < n ==> !a b c d. f a b = m /\ stuff a b c d ==> other a b c d) <=>
    (!a b c d. f a b:num < n /\ stuff a b c d ==> other a b c d)`] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(!d d' s s'. P d d' s s' ==> P d' d s' s) /\
    (!d d' s s'. ~(2 <= CARD d) /\ ~(2 <= CARD d') ==> P d d' s s') /\
    (!d d' s s'. negligible s ==>  P d d' s s') /\
    (!d d' s s'. 2 <= CARD d /\ ~(negligible s) /\ ~(negligible s')
                 ==> P d d' s s')
    ==> !d d' s s'.  P d d' s s'`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    CONJ_TAC THENL [REWRITE_TAC[ADD_SYM; CONJ_ACI]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x = y ==> x >= a + b ==> y >= b + a`) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM];
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC `FINITE(d1:(real^N->bool)->bool) /\
                   FINITE(d2:(real^N->bool)->bool)`
    THENL [ALL_TAC; REWRITE_TAC[division_of] THEN ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `~(2 <= n) <=> n = 0 \/ n = 1`] THEN
    ASM_CASES_TAC `d1:(real^N->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_DIVISION_OF] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `d2:(real^N->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[EMPTY_DIVISION_OF] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(d1:(real^N->bool)->bool) HAS_SIZE 1 /\
      (d2:(real^N->bool)->bool) HAS_SIZE 1`
    MP_TAC THENL [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV HAS_SIZE_CONV)) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `u:real^N->bool` SUBST_ALL_TAC)
     (X_CHOOSE_THEN `v:real^N->bool` SUBST_ALL_TAC)) THEN
    STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[division_of; UNIONS_1; IN_SING]) THEN
    REPEAT(FIRST_X_ASSUM
     (CONJUNCTS_THEN2 MP_TAC
       (SUBST_ALL_TAC o SYM o CONJUNCT2) o CONJUNCT2)) THEN
    REWRITE_TAC[FORALL_UNWIND_THM2] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC BRUNN_MINKOWSKI_INTERVAL THEN
    ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `measure(s:real^N->bool) = &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[MEASURE_EQ_0]; ALL_TAC] THEN
    SIMP_TAC[ROOT_0; DIMINDEX_NONZERO; REAL_ADD_LID; real_ge] THEN
    MATCH_MP_TAC ROOT_MONO_LE THEN REWRITE_TAC[DIMINDEX_NONZERO] THEN
    SUBGOAL_THEN `?a:real^N. a IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(IMAGE (\x:real^N. a + x) t)` THEN CONJ_TAC THENL
     [REWRITE_TAC[MEASURE_TRANSLATION; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    REWRITE_TAC[MEASURABLE_TRANSLATION_EQ] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_ELEMENTARY]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
    ASM_MESON_TAC[ELEMENTARY_COMPACT];
    REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC]] THEN
  SUBGOAL_THEN
   `!d1 d2 s t i j k.
        CARD d1 + CARD d2 = n /\
        1 <= k /\ k <= dimindex(:N) /\ ~(i = j) /\
        i IN d1 /\ i SUBSET {x:real^N | x$k <= &0} /\
        j IN d1 /\ j SUBSET {x | x$k >= &0} /\
        ~(negligible i) /\ ~(negligible j) /\
        ~(s = {}) /\ ~(t = {}) /\ ~(negligible s) /\ ~(negligible t) /\
        d1 division_of s /\ d2 division_of t
        ==> root(dimindex (:N)) (measure {x + y | x IN s /\ y IN t}) >=
            root(dimindex (:N)) (measure s) + root(dimindex (:N)) (measure t)`
  MP_TAC THENL
   [ALL_TAC;
    POP_ASSUM(LABEL_TAC "*") THEN DISCH_THEN(LABEL_TAC "+") THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `?i:real^N->bool. i IN d1 /\ interior i = {}` THENL
     [REMOVE_THEN "+" (K ALL_TAC) THEN REMOVE_THEN "*" MP_TAC THEN
      DISCH_THEN(MP_TAC o SPECL
       [`{i:real^N->bool | i IN d1 /\ ~(interior i = {})}`;
        `d2:(real^N->bool)->bool`;
        `UNIONS {i:real^N->bool | i IN d1 /\ ~(interior i = {})}`;
        `t:real^N->bool`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [EXPAND_TAC "n" THEN REWRITE_TAC[LT_ADD_RCANCEL] THEN
          MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
           [ASM SET_TAC[]; ASM_MESON_TAC[DIVISION_OF_FINITE]];
          DISCH_TAC THEN
          SUBGOAL_THEN
           `negligible(UNIONS {i | i IN d1 /\ ~(interior i = {})} UNION
                       UNIONS {i:real^N->bool | i IN d1 /\ interior i = {}})`
          MP_TAC THENL
           [ASM_REWRITE_TAC[UNION_EMPTY] THEN
            MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
             [MATCH_MP_TAC FINITE_RESTRICT THEN
              ASM_MESON_TAC[DIVISION_OF_FINITE];
              REWRITE_TAC[IN_ELIM_THM; IMP_CONJ] THEN
              FIRST_ASSUM(fun th ->
                GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
              REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; NEGLIGIBLE_INTERVAL]];
            REWRITE_TAC[GSYM UNIONS_UNION; SET_RULE
              `{x | x IN s /\ ~Q x} UNION {x | x IN s /\ Q x} = s`] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM_REWRITE_TAC[]];
          MATCH_MP_TAC DIVISION_OF_SUBSET THEN
          EXISTS_TAC `d1:(real^N->bool)->bool` THEN
          CONJ_TAC THENL [ASM_MESON_TAC[division_of]; SET_TAC[]]];
        MATCH_MP_TAC(REAL_ARITH
         `c' <= c /\ a' = a
          ==> c' >= a' + b ==> c >= a + b`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC ROOT_MONO_LE THEN REWRITE_TAC[DIMINDEX_NONZERO] THEN
          MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
            CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ELEMENTARY_COMPACT]] THEN
            MATCH_MP_TAC COMPACT_UNIONS THEN
            RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN
            ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
            ASM_MESON_TAC[COMPACT_INTERVAL];
            MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
            ASM_MESON_TAC[ELEMENTARY_COMPACT];
            MATCH_MP_TAC(SET_RULE
             `s' SUBSET s
              ==> {f x y | x IN s' /\ y IN t} SUBSET
                  {f x y | x IN s /\ y IN t}`) THEN
            SUBGOAL_THEN `s:real^N->bool = UNIONS d1` SUBST1_TAC THENL
             [ASM_MESON_TAC[division_of];
              MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]]];
          AP_TERM_TAC THEN
          MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
          MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
          EXISTS_TAC `UNIONS {i:real^N->bool | i IN d1 /\ interior i = {}}` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN CONJ_TAC THENL
             [MATCH_MP_TAC FINITE_RESTRICT THEN
              ASM_MESON_TAC[DIVISION_OF_FINITE];
              REWRITE_TAC[IN_ELIM_THM; IMP_CONJ] THEN
              FIRST_ASSUM(fun th ->
                GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
              REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; NEGLIGIBLE_INTERVAL]];
            MATCH_MP_TAC(SET_RULE
             `s' UNION s'' = s
              ==> (s' DIFF s) UNION (s DIFF s') SUBSET s''`) THEN
            REWRITE_TAC[GSYM UNIONS_UNION; SET_RULE
              `{x | x IN s /\ ~Q x} UNION {x | x IN s /\ Q x} = s`] THEN
            RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN
            ASM_REWRITE_TAC[]]]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
      REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN DISCH_TAC THEN
      REMOVE_THEN "*" (K ALL_TAC) THEN
      SUBGOAL_THEN
       `?d:(real^N->bool)->bool. d SUBSET d1 /\ d HAS_SIZE 2`
      MP_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP CHOOSE_SUBSET o
          MATCH_MP DIVISION_OF_FINITE) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV HAS_SIZE_CONV)) THEN
      REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:real^N->bool` MP_TAC) THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:real^N->bool` MP_TAC) THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
      REWRITE_TAC[UNWIND_THM2; INSERT_SUBSET; EMPTY_SUBSET] THEN STRIP_TAC THEN
      MP_TAC(ASSUME `d1 division_of (s:real^N->bool)`) THEN
      REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o el 2 o CONJUNCTS) THEN
      DISCH_THEN(MP_TAC o SPECL [`i:real^N->bool`; `j:real^N->bool`]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `?u v w z. i = interval[u:real^N,v] /\ j = interval[w:real^N,z]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[DIVISION_OF]; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM INTERIOR_INTER; INTER_INTERVAL] THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_EQ_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      SIMP_TAC[LAMBDA_BETA; ASSUME `1 <= k`; ASSUME `k <= dimindex(:N)`] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_LE_BETWEEN] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real` MP_TAC) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
       `min v z <= a /\ a <= max u w
        ==> u < v /\ w < z
            ==> u <= a /\ v <= a /\ a <= w /\ a <= z \/
                w <= a /\ z <= a /\ a <= u /\ a <= v`)) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `!i:real^N->bool. i IN d1 ==> ~(interior i = {})` THEN
        DISCH_THEN(fun th -> MP_TAC(ISPEC `interval[u:real^N,v]` th) THEN
                             MP_TAC(ISPEC `interval[w:real^N,z]` th)) THEN
        REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL
         [`IMAGE (IMAGE (\x:real^N. x - a % basis k)) d1`;
          `d2:(real^N->bool)->bool`;
          `IMAGE (\x:real^N. x - a % basis k) s`;
          `t:real^N->bool`])
      THENL
       [DISCH_THEN(MP_TAC o SPECL
         [`IMAGE (\x:real^N. x - a % basis k) i`;
          `IMAGE (\x:real^N. x - a % basis k) j`; `k:num`]);
        DISCH_THEN(MP_TAC o SPECL
         [`IMAGE (\x:real^N. x - a % basis k) j`;
          `IMAGE (\x:real^N. x - a % basis k) i`; `k:num`])] THEN
      (ASM_REWRITE_TAC[] THEN ANTS_TAC THEN REPEAT CONJ_TAC THENL
        [EXPAND_TAC "n" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
         MATCH_MP_TAC CARD_IMAGE_INJ THEN
         CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIVISION_OF_FINITE]] THEN
         MATCH_MP_TAC(MESON[]
          `(!x y. Q x y ==> R x y)
           ==> (!x y. P x /\ P y /\ Q x y ==> R x y)`) THEN
         REWRITE_TAC[INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC;
         MATCH_MP_TAC(SET_RULE
          `(!x y. f x = f y ==> x = y) /\ ~(s = t)
           ==> ~(IMAGE f s = IMAGE f t)`) THEN
         REWRITE_TAC[VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
         ASM_MESON_TAC[];
         MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
         REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
         ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
          BASIS_COMPONENT; REAL_MUL_RID; REAL_LE_SUB_RADD; REAL_ADD_LID] THEN
         REWRITE_TAC[IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_TRANS];
         MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_MESON_TAC[];
         REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; real_ge] THEN
         ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
          BASIS_COMPONENT; REAL_MUL_RID; REAL_LE_SUB_LADD; REAL_ADD_LID] THEN
         REWRITE_TAC[IN_INTERVAL] THEN ASM_MESON_TAC[REAL_LE_TRANS];
         REWRITE_TAC[VECTOR_ARITH `x - a:real^N = --a + x`] THEN
         ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ] THEN
         ASM_MESON_TAC[NEGLIGIBLE_INTERVAL; INTERIOR_CLOSED_INTERVAL];
         REWRITE_TAC[VECTOR_ARITH `x - a:real^N = --a + x`] THEN
         ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ] THEN
         ASM_MESON_TAC[NEGLIGIBLE_INTERVAL; INTERIOR_CLOSED_INTERVAL];
         ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
         REWRITE_TAC[VECTOR_ARITH `x - a:real^N = --a + x`] THEN
         ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ];
         REWRITE_TAC[VECTOR_ARITH `x - a:real^N = --a + x`] THEN
         ASM_REWRITE_TAC[DIVISION_OF_TRANSLATION];
         MATCH_MP_TAC(REAL_ARITH
          `a = a' /\ b = b' ==> a >= b + c ==> a' >= b' + c`) THEN
         REWRITE_TAC[VECTOR_ARITH `x - a:real^N = --a + x`] THEN
         REWRITE_TAC[MEASURE_TRANSLATION] THEN
         REWRITE_TAC[GSYM VECTOR_ADD_ASSOC; SET_RULE
          `{f x y | x IN IMAGE g s /\ y IN t} =
           {f (g x) y | x IN s /\ y IN t}`] THEN
         REWRITE_TAC[SET_RULE
          `{a + x + y:real^N | x IN s /\ y IN t} =
           IMAGE (\z. a + z) {x + y | x IN s /\ y IN t}`] THEN
         REWRITE_TAC[MEASURE_TRANSLATION]])]] THEN
  SUBGOAL_THEN
   `!d1 d2 s t i j k.
        CARD d1 + CARD d2 = n /\
        1 <= k /\ k <= dimindex(:N) /\ ~(i = j) /\
        i IN d1 /\ i SUBSET {x:real^N | x$k <= &0} /\ ~(negligible i) /\
        j IN d1 /\ j SUBSET {x | x$k >= &0} /\ ~(negligible j) /\
        measure(t INTER {x | x$k <= &0}) / measure t =
        measure(s INTER {x | x$k <= &0}) / measure s /\
        measure(t INTER {x | x$k >= &0}) / measure t =
        measure(s INTER {x | x$k >= &0}) / measure s /\
        ~(s = {}) /\ ~(t = {}) /\ ~(negligible s) /\ ~(negligible t) /\
        d1 division_of s /\ d2 division_of t
        ==> root(dimindex (:N)) (measure {x + y | x IN s /\ y IN t}) >=
            root(dimindex (:N)) (measure s) + root(dimindex (:N)) (measure t)`
  MP_TAC THENL
   [ALL_TAC;
    POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < measure(s:real^N->bool) /\ &0 < measure(t:real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_MEASURE_POS_LT; MEASURABLE_ELEMENTARY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?a. measure(t INTER {x:real^N | x$k <= a}) / measure t =
          measure(s INTER {x:real^N | x$k <= &0}) / measure s`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN
       `&0 <= measure(s INTER {x:real^N | x$k <= &0}) / measure s /\
        measure(s INTER {x:real^N | x$k <= &0}) / measure s <= &1`
      MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ; REAL_MUL_LZERO] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MEASURE_POS_LE;
          REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
          REPEAT CONJ_TAC THENL
           [ALL_TAC;
            ASM_MESON_TAC[MEASURABLE_ELEMENTARY];
            SET_TAC[]]] THEN
        MATCH_MP_TAC MEASURABLE_COMPACT THEN
        MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE] THEN
        ASM_MESON_TAC[ELEMENTARY_COMPACT];
        SPEC_TAC(`measure(s INTER {x:real^N | x$k <= &0}) / measure s`,
                 `u:real`)] THEN
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `?b:real. &0 < b /\ !x:real^N. x IN t ==> abs(x$k) <= b`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `bounded(t:real^N->bool)` MP_TAC THENL
         [ASM_MESON_TAC[ELEMENTARY_BOUNDED]; REWRITE_TAC[BOUNDED_POS]] THEN
        MATCH_MP_TAC MONO_EXISTS THEN
        ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `?a. a IN real_interval[--b,b] /\
            measure (t INTER {x:real^N | x$k <= a}) / measure t = u`
       (fun th -> MESON_TAC[th]) THEN
      MATCH_MP_TAC REAL_IVT_INCREASING THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ALL_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `&0 <= u ==> x = &0 ==> x <= u`)) THEN
        REWRITE_TAC[real_div; REAL_ENTIRE] THEN DISJ1_TAC THEN
        MATCH_MP_TAC MEASURE_EQ_0 THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `{x:real^N | x$k = --b}` THEN
        ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
        SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; GSYM REAL_LE_ANTISYM] THEN
        ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> --b <= x`];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `u <= &1 ==> x = &1 ==> u <= x`)) THEN
        ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_MUL_LID] THEN
        AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
        ASM_MESON_TAC[REAL_ARITH `abs x <= b ==> x <= b`]] THEN
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      GEN_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_MEASURE_IN_HALFSPACE_LE THEN
      ASM_MESON_TAC[MEASURABLE_ELEMENTARY];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`d1:(real^N->bool)->bool`;
      `IMAGE (IMAGE (\x:real^N. x - a % basis k)) d2`;
      `s:real^N->bool`;
      `IMAGE (\x:real^N. x - a % basis k) t`;
      `i:real^N->bool`; `j:real^N->bool`; `k:num`]) THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x - a:real^N = --a + x`] THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ; DIVISION_OF_TRANSLATION] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC "n" THEN AP_TERM_TAC THEN
        MATCH_MP_TAC CARD_IMAGE_INJ THEN
        CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[DIVISION_OF_FINITE]] THEN
        MATCH_MP_TAC(MESON[]
         `(!x y. Q x y ==> R x y)
          ==> (!x y. P x /\ P y /\ Q x y ==> R x y)`) THEN
        REWRITE_TAC[INJECTIVE_IMAGE] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `IMAGE (\x. --(a % basis k) + x) t INTER {x:real^N | x$k >= &0} =
        IMAGE (\x. --(a % basis k) + x) (t INTER {x | x$k >= a}) /\
        IMAGE (\x. --(a % basis k) + x) t INTER {x:real^N | x$k <= &0} =
        IMAGE (\x. --(a % basis k) + x) (t INTER {x | x$k <= a})`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `!g. (!x. f(x) IN s' <=> x IN s) /\ (!x. g(f x) = x)
               ==> IMAGE f t INTER s' = IMAGE f (t INTER s)`) THEN
        ASM_SIMP_TAC[IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                     BASIS_COMPONENT; VECTOR_NEG_COMPONENT] THEN
        EXISTS_TAC `\x:real^N. a % basis k + x` THEN
        (CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);
        ALL_TAC] THEN
      REWRITE_TAC[MEASURE_TRANSLATION] THEN MATCH_MP_TAC(REAL_FIELD
       `&0 < s /\ &0 < t /\ t' / t = s' / s  /\ s' + s'' = s /\ t' + t'' = t
        ==> t' / t = s' / s /\ t'' / t = s'' / s`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
      (REPEAT CONJ_TAC THENL
        [MATCH_MP_TAC MEASURABLE_COMPACT THEN
         MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
         REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                     CLOSED_HALFSPACE_COMPONENT_GE] THEN
         ASM_MESON_TAC[ELEMENTARY_COMPACT];
         MATCH_MP_TAC MEASURABLE_COMPACT THEN
         MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
         REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                     CLOSED_HALFSPACE_COMPONENT_GE] THEN
         ASM_MESON_TAC[ELEMENTARY_COMPACT];
         MATCH_MP_TAC(SET_RULE
          `(!x. P x \/ Q x)
           ==> s INTER {x | P x} UNION s INTER {x | Q x} = s`) THEN
         REAL_ARITH_TAC;
         REWRITE_TAC[SET_RULE `(t INTER {x | P x}) INTER (t INTER {x | Q x}) =
                               t INTER {x | P x /\ Q x}`] THEN
         MATCH_MP_TAC(MESON[NEGLIGIBLE_SUBSET; INTER_SUBSET]
          `negligible t ==> negligible(s INTER t)`) THEN
         REWRITE_TAC[REAL_ARITH `x <= a /\ x >= a <=> x = a`] THEN
         ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE]]);
      REWRITE_TAC[MEASURE_TRANSLATION] THEN MATCH_MP_TAC(REAL_ARITH
       `a' = a ==> a' >= b ==> a >= b`) THEN AP_TERM_TAC THEN
      REWRITE_TAC[SET_RULE
       `{f x y | x IN s /\ y IN IMAGE g t} =
        {f x (g y) | x IN s /\ y IN t}`] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `x + a + y:real^N = a + x + y`] THEN
      REWRITE_TAC[SET_RULE
       `{a + x + y:real^N | x IN s /\ y IN t} =
        IMAGE (\z. a + z) {x + y | x IN s /\ y IN t}`] THEN
      REWRITE_TAC[MEASURE_TRANSLATION]]] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
  SUBGOAL_THEN `measurable(s:real^N->bool) /\ measurable(t:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MEASURABLE_ELEMENTARY]; ALL_TAC] THEN
  SUBGOAL_THEN `measurable {x + y:real^N | x IN s /\ y IN t}` ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
    ASM_MESON_TAC[ELEMENTARY_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < measure(s:real^N->bool) /\ &0 < measure(t:real^N->bool)`
  STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[MEASURABLE_MEASURE_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(d1:(real^N->bool)->bool) /\
                FINITE(d2:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[DIVISION_OF_FINITE]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) REAL_LE_ROOT o snd) THEN
  ASM_SIMP_TAC[DIMINDEX_NONZERO; MEASURE_POS_LE; ROOT_POS_LE; REAL_LE_ADD] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `dl = {l INTER {x:real^N | x$k <= &0} |l|
                    l IN d1 DELETE j /\ ~(l INTER {x | x$k <= &0} = {})}` THEN
  ABBREV_TAC `dr = {l INTER {x:real^N | x$k >= &0} |l|
                    l IN d1 DELETE i /\ ~(l INTER {x | x$k >= &0} = {})}` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `measure {x + y:real^N | x IN UNIONS dl /\ y IN (t INTER {x | x$k <= &0})} +
    measure {x + y | x IN UNIONS dr /\ y IN (t INTER {x | x$k >= &0})}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `measure {x + y:real^N | x IN (s INTER {x | x$k <= &0}) /\
                              y IN (t INTER {x | x$k <= &0})} +
      measure {x + y:real^N | x IN (s INTER {x | x$k >= &0}) /\
                              y IN (t INTER {x | x$k >= &0})}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      (MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC COMPACT_UNIONS THEN
          MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
          ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
          ASM_SIMP_TAC[IN_DELETE; FINITE_DELETE; FINITE_IMAGE;
                       FINITE_RESTRICT; IMP_CONJ] THEN
          REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE; IN_DELETE] THEN
          FIRST_ASSUM(fun th ->
            GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
          ASM_SIMP_TAC[INTERVAL_SPLIT; COMPACT_INTERVAL];
          MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
          REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                      CLOSED_HALFSPACE_COMPONENT_GE] THEN
          ASM_MESON_TAC[ELEMENTARY_COMPACT]];
        MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
        CONJ_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                    CLOSED_HALFSPACE_COMPONENT_GE] THEN
        ASM_MESON_TAC[ELEMENTARY_COMPACT];
        MATCH_MP_TAC(SET_RULE
         `s SUBSET s' ==> {x + y:real^N | x IN s /\ y IN t} SUBSET
                         {x + y:real^N | x IN s' /\ y IN t}`) THEN
        MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
        REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        SIMP_TAC[IN_DELETE; IN_INTER; IN_ELIM_THM] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN
        ASM_MESON_TAC[IN_UNIONS]]);
      ALL_TAC] THEN
    SUBGOAL_THEN
     `s = (s INTER {x:real^N | x$k <= &0}) UNION (s INTER {x | x$k >= &0}) /\
      t = (t INTER {x:real^N | x$k <= &0}) UNION (t INTER {x | x$k >= &0})`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
       `(!x. P x \/ Q x)
        ==> s = (s INTER {x | P x}) UNION (s INTER {x | Q x})`) THEN
      REAL_ARITH_TAC;
      DISCH_THEN(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])] THEN
    W(MP_TAC o PART_MATCH (rand o rand)
       MEASURE_NEGLIGIBLE_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [REPEAT(CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
        CONJ_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
        REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                    CLOSED_HALFSPACE_COMPONENT_GE] THEN
        ASM_MESON_TAC[ELEMENTARY_COMPACT];
        ALL_TAC]) THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | x$k = &0}` THEN
      ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN MATCH_MP_TAC(SET_RULE
       `s SUBSET {x | P x} /\ t SUBSET {x | Q x}
        ==> (s INTER t) SUBSET {x | P x /\ Q x}`) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
      SIMP_TAC[IN_INTER; IN_ELIM_THM; REAL_LE_ADD; VECTOR_ADD_COMPONENT;
        real_ge; REAL_ARITH `x <= &0 /\ y <= &0 ==> x + y <= &0`];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
      CONJ_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                  CLOSED_HALFSPACE_COMPONENT_GE] THEN
      ASM_MESON_TAC[ELEMENTARY_COMPACT];
      MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
      CONJ_TAC THEN MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN
      MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
      REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                  CLOSED_HALFSPACE_COMPONENT_GE] THEN
      ASM_MESON_TAC[ELEMENTARY_COMPACT];
      SET_TAC[]]] THEN
  SUBGOAL_THEN
   `&0 < measure(s INTER {x:real^N | x$k <= &0}) /\
    &0 < measure(s INTER {x:real^N | x$k >= &0})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_MEASURE_POS_LT; MEASURABLE_INTER_HALFSPACE_LE;
                 MEASURABLE_INTER_HALFSPACE_GE] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~negligible(i:real^N->bool)`;
      UNDISCH_TAC `~negligible(j:real^N->bool)`] THEN
    REWRITE_TAC[CONTRAPOS_THM] THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      NEGLIGIBLE_SUBSET) THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN
    UNDISCH_TAC `d1 division_of (s:real^N->bool)` THEN
    REWRITE_TAC[division_of] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPECL [`dl:(real^N->bool)->bool`;
                  `{l INTER {x:real^N | x$k <= &0} |l|
                    l IN d2 /\ ~(l INTER {x | x$k <= &0} = {})}`;
                  `UNIONS dl :real^N->bool`;
                   `t INTER {x:real^N | x$k <= &0}`] th) THEN
    MP_TAC(SPECL [`dr:(real^N->bool)->bool`;
                  `{l INTER {x:real^N | x$k >= &0} |l|
                    l IN d2 /\ ~(l INTER {x | x$k >= &0} = {})}`;
                  `UNIONS dr :real^N->bool`;
                   `t INTER {x:real^N | x$k >= &0}`] th)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "n" THEN MATCH_MP_TAC LTE_ADD2 THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC `CARD(d1 DELETE (i:real^N->bool))` THEN CONJ_TAC THENL
         [ALL_TAC; MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE
       `CARD {x | x IN IMAGE f s /\ P x} <= CARD(IMAGE f s) /\
        CARD(IMAGE f s) <= CARD s
        ==> CARD {x | x IN IMAGE f s /\ P x} <= CARD s`) THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      EXISTS_TAC `j INTER {x:real^N | x$k >= &0}` THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; MEMBER_NOT_EMPTY] THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DELETE; GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `j:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE
         `~(s = {}) /\ s SUBSET t ==> ~(s INTER t = {})`) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[division_of]];
      DISCH_TAC THEN
      UNDISCH_TAC `measure (t INTER {x:real^N | x$k >= &0}) / measure t =
                   measure (s INTER {x:real^N | x$k >= &0}) / measure s` THEN
      ASM_SIMP_TAC[MEASURE_EMPTY; REAL_EQ_RDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      REWRITE_TAC[division_of] THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE; IN_DELETE] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_DELETE] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(fun th ->
            GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
        REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]] THEN
        MATCH_MP_TAC(SET_RULE
         `x IN s ==> x SUBSET UNIONS s`) THEN
        ASM SET_TAC[];
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `interior(s) INTER interior(s') = {} /\
          interior(s INTER t) SUBSET interior s /\
          interior(s' INTER t) SUBSET interior s'
          ==> interior(s INTER t) INTER interior(s' INTER t) = {}`) THEN
        SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
        ASM_MESON_TAC[division_of]];
      REWRITE_TAC[division_of] THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE; IN_DELETE] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_DELETE] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(fun th ->
            GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
        REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]] THEN
        MATCH_MP_TAC(SET_RULE
          `s SUBSET t ==> s INTER u SUBSET t INTER u`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM_MESON_TAC[];
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `interior(s) INTER interior(s') = {} /\
          interior(s INTER t) SUBSET interior s /\
          interior(s' INTER t) SUBSET interior s'
          ==> interior(s INTER t) INTER interior(s' INTER t) = {}`) THEN
        SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
        ASM_MESON_TAC[division_of];
        REWRITE_TAC[SET_RULE `{x | x IN s /\ ~(x = a)} = s DELETE a`] THEN
        GEN_REWRITE_TAC LAND_CONV [SET_RULE `s = {} UNION s`] THEN
        REWRITE_TAC[GSYM UNIONS_INSERT] THEN
        REWRITE_TAC[SET_RULE `x INSERT (s DELETE x) = x INSERT s`] THEN
        REWRITE_TAC[UNIONS_INSERT; UNION_EMPTY] THEN
        REWRITE_TAC[GSYM SIMPLE_IMAGE; GSYM INTER_UNIONS] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[division_of]]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "n" THEN MATCH_MP_TAC LTE_ADD2 THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC LET_TRANS THEN
        EXISTS_TAC `CARD(d1 DELETE (j:real^N->bool))` THEN CONJ_TAC THENL
         [ALL_TAC; MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE
       `CARD {x | x IN IMAGE f s /\ P x} <= CARD(IMAGE f s) /\
        CARD(IMAGE f s) <= CARD s
        ==> CARD {x | x IN IMAGE f s /\ P x} <= CARD s`) THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
      MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      EXISTS_TAC `i INTER {x:real^N | x$k <= &0}` THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; MEMBER_NOT_EMPTY] THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DELETE; GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `i:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE
         `~(s = {}) /\ s SUBSET t ==> ~(s INTER t = {})`) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[division_of]];
      DISCH_TAC THEN
      UNDISCH_TAC `measure (t INTER {x:real^N | x$k <= &0}) / measure t =
                   measure (s INTER {x:real^N | x$k <= &0}) / measure s` THEN
      ASM_SIMP_TAC[MEASURE_EMPTY; REAL_EQ_RDIV_EQ] THEN
      REWRITE_TAC[real_div; REAL_MUL_LZERO] THEN
      CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      REWRITE_TAC[division_of] THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE; IN_DELETE] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_DELETE] THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(fun th ->
            GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
        REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]] THEN
        MATCH_MP_TAC(SET_RULE
         `x IN s ==> x SUBSET UNIONS s`) THEN
        ASM SET_TAC[];
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `interior(s) INTER interior(s') = {} /\
          interior(s INTER t) SUBSET interior s /\
          interior(s' INTER t) SUBSET interior s'
          ==> interior(s INTER t) INTER interior(s' INTER t) = {}`) THEN
        SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
        ASM_MESON_TAC[division_of]];
      REWRITE_TAC[division_of] THEN
      MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
      ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                                     {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; FORALL_IN_IMAGE; IN_DELETE] THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_DELETE] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(fun th ->
            GEN_REWRITE_TAC I [MATCH_MP FORALL_IN_DIVISION th]) THEN
        REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ALL_TAC; ASM_SIMP_TAC[INTERVAL_SPLIT] THEN MESON_TAC[]] THEN
        MATCH_MP_TAC(SET_RULE
          `s SUBSET t ==> s INTER u SUBSET t INTER u`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM_MESON_TAC[];
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE
         `interior(s) INTER interior(s') = {} /\
          interior(s INTER t) SUBSET interior s /\
          interior(s' INTER t) SUBSET interior s'
          ==> interior(s INTER t) INTER interior(s' INTER t) = {}`) THEN
        SIMP_TAC[SUBSET_INTERIOR; INTER_SUBSET] THEN
        ASM_MESON_TAC[division_of];
        REWRITE_TAC[SET_RULE `{x | x IN s /\ ~(x = a)} = s DELETE a`] THEN
        GEN_REWRITE_TAC LAND_CONV [SET_RULE `s = {} UNION s`] THEN
        REWRITE_TAC[GSYM UNIONS_INSERT] THEN
        REWRITE_TAC[SET_RULE `x INSERT (s DELETE x) = x INSERT s`] THEN
        REWRITE_TAC[UNIONS_INSERT; UNION_EMPTY] THEN
        REWRITE_TAC[GSYM SIMPLE_IMAGE; GSYM INTER_UNIONS] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN ASM_MESON_TAC[division_of]]];
    ALL_TAC] THEN
  REWRITE_TAC[real_ge; IMP_IMP] THEN
  SUBGOAL_THEN
   `compact(UNIONS dl:real^N->bool) /\ compact(UNIONS dr:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
    ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                               {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_IMAGE; FINITE_DELETE] THEN
    REWRITE_TAC[IMP_CONJ; IN_ELIM_THM; FORALL_IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_LE;
                CLOSED_HALFSPACE_COMPONENT_GE] THEN
    ASM_MESON_TAC[division_of; COMPACT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `measurable(UNIONS dl:real^N->bool) /\
    measurable(UNIONS dr:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MEASURABLE_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
    `measurable { x + y:real^N |
                  x IN UNIONS dl /\ y IN t INTER {x | x$k <= &0}} /\
     measurable { x + y:real^N |
                  x IN UNIONS dr /\ y IN t INTER {x | &0 <= x$k}}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
    MATCH_MP_TAC COMPACT_SUMS THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x <=> x >= &0`;
      CLOSED_HALFSPACE_COMPONENT_LE; CLOSED_HALFSPACE_COMPONENT_GE] THEN
    ASM_MESON_TAC[ELEMENTARY_COMPACT];
    ALL_TAC] THEN
 ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
  [REAL_LE_ROOT; DIMINDEX_NONZERO; REAL_LE_ADD; ROOT_POS_LE;
   MEASURE_POS_LE; MEASURABLE_INTER_HALFSPACE_LE;
   MEASURABLE_INTER_HALFSPACE_GE; REAL_ARITH `&0 <= x <=> x >= &0`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= a' + b' ==> a' <= a /\ b' <= b ==> x <= a + b`) THEN
  SUBGOAL_THEN
   `measure(UNIONS dl :real^N->bool) =
    measure(s INTER {x:real^N | x$k <= &0}) /\
    measure(UNIONS dr :real^N->bool) =
    measure(s INTER {x:real^N | x$k >= &0})`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [MAP_EVERY EXPAND_TAC ["dl"; "dr"] THEN
    ONCE_REWRITE_TAC[SET_RULE `{f x |x| x IN s /\ ~(f x = a)} =
                               {t | t IN IMAGE f s /\ ~(t = a)}`] THEN
    REWRITE_TAC[SET_RULE `{x | x IN s /\ ~(x = a)} = s DELETE a`] THEN
    CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SET_RULE `s = {} UNION s`] THEN
    REWRITE_TAC[GSYM UNIONS_INSERT] THEN
    REWRITE_TAC[SET_RULE `x INSERT (s DELETE x) = x INSERT s`] THEN
    REWRITE_TAC[UNIONS_INSERT; UNION_EMPTY] THEN
    REWRITE_TAC[GSYM SIMPLE_IMAGE; GSYM INTER_UNIONS] THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | x$k = &0}` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
    MATCH_MP_TAC(SET_RULE
     `s SUBSET t /\ t DIFF s SUBSET u
      ==> (s DIFF t UNION t DIFF s) SUBSET u`) THEN
    REWRITE_TAC[SET_RULE `s INTER u DIFF t INTER u = (s DIFF t) INTER u`] THEN
    (SUBGOAL_THEN `s:real^N->bool = UNIONS d1` SUBST1_TAC THENL
      [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
     CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[GSYM REAL_LE_ANTISYM; real_ge; SET_RULE
     `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`]
    THENL
     [MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s INTER u SUBSET u INTER t`);
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s INTER u SUBSET t INTER u`)] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[real_ge]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `root (dimindex (:N)) (measure (s INTER {x:real^N | x$k <= &0})) +
    root (dimindex (:N)) (measure (t INTER {x:real^N | x$k <= &0})) =
    root (dimindex (:N)) (measure (s INTER {x | x$k <= &0})) *
    (&1 + root (dimindex (:N)) (measure (t INTER {x | x$k <= &0})) /
          root (dimindex (:N)) (measure (s INTER {x | x$k <= &0}))) /\
   root (dimindex (:N)) (measure (s INTER {x:real^N | x$k >= &0})) +
    root (dimindex (:N)) (measure (t INTER {x:real^N | x$k >= &0})) =
    root (dimindex (:N)) (measure (s INTER {x | x$k >= &0})) *
    (&1 + root (dimindex (:N)) (measure (t INTER {x | x$k >= &0})) /
          root (dimindex (:N)) (measure (s INTER {x | x$k >= &0})))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(REAL_FIELD `&0 < s ==> s + t = s * (&1 + t / s)`) THEN
    ASM_SIMP_TAC[ROOT_POS_LT; DIMINDEX_NONZERO];
    ALL_TAC] THEN
  ASM_SIMP_TAC[DIMINDEX_NONZERO; GSYM REAL_ROOT_DIV; MEASURE_POS_LE;
    MEASURABLE_INTER_HALFSPACE_LE; MEASURABLE_INTER_HALFSPACE_GE] THEN
  SUBGOAL_THEN
   `measure(t INTER {x:real^N | x$k <= &0}) /
    measure(s INTER {x:real^N | x$k <= &0}) = measure t / measure s /\
    measure(t INTER {x:real^N | x$k >= &0}) /
    measure(s INTER {x:real^N | x$k >= &0}) = measure t / measure s`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MATCH_MP_TAC(REAL_FIELD
     `tn / t = sn / s /\ tp / t = sp / s /\
      &0 < sp /\ &0 < sn /\ &0 < s /\ &0 < t
      ==> tn / sn = t / s /\ tp / sp = t / s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_POW_MUL] THEN
  ASM_SIMP_TAC[REAL_POW_ROOT; DIMINDEX_NONZERO; MEASURE_POS_LE;
           MEASURABLE_INTER_HALFSPACE_LE; MEASURABLE_INTER_HALFSPACE_GE] THEN
  SUBGOAL_THEN
   `measure (s INTER {x | x$k <= &0}) + measure (s INTER {x | x$k >= &0}) =
    root (dimindex(:N)) (measure(s:real^N->bool)) pow (dimindex(:N))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_ROOT; DIMINDEX_NONZERO; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNION_EQ THEN
    ASM_SIMP_TAC[MEASURABLE_INTER_HALFSPACE_LE;
                 MEASURABLE_INTER_HALFSPACE_GE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN s` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | x$k = &0}` THEN
      ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE] THEN
      REWRITE_TAC[GSYM REAL_LE_ANTISYM; real_ge] THEN SET_TAC[]];
    ASM_SIMP_TAC[GSYM REAL_ROOT_MUL; MEASURE_POS_LE; DIMINDEX_NONZERO;
                 REAL_LE_DIV; GSYM REAL_POW_MUL;
                 REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Now for open sets.                                                        *)
(* ------------------------------------------------------------------------- *)

let BRUNN_MINKOWSKI_OPEN = prove
 (`!s t:real^N->bool.
    (s = {} <=> t = {}) /\ bounded s /\ open s /\ bounded t /\ open t
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[SET_RULE `{x + y:real^N | x IN {} /\ y IN {}} = {}`;
               REAL_LE_REFL; MEASURE_EMPTY; ROOT_0; DIMINDEX_NONZERO;
               real_ge; REAL_ADD_LID] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `atreal(&0) within {e | &0 <= e}` REALLIM_UBOUND) THEN
  EXISTS_TAC `\e. root (dimindex(:N)) (measure(s:real^N->bool) - e) +
                  root (dimindex(:N)) (measure(t:real^N->bool) - e)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\e. (measure(s:real^N->bool) - e) rpow (inv(&(dimindex(:N)))) +
          (measure(t:real^N->bool) - e) rpow (inv(&(dimindex(:N))))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
      EXISTS_TAC `min (measure(s:real^N->bool)) (measure(t:real^N->bool))` THEN
      ASM_SIMP_TAC[REAL_LT_MIN; IN_ELIM_THM; REAL_SUB_RZERO;
                   MEASURE_OPEN_POS_LT] THEN
      REPEAT STRIP_TAC THEN BINOP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC REAL_ROOT_RPOW THEN
      REWRITE_TAC[DIMINDEX_NONZERO] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ROOT_RPOW; MEASURE_OPEN_POS_LT; DIMINDEX_NONZERO;
                   REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `measure(s:real^N->bool) = measure s - &0`] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_WITHINREAL] THEN
      REWRITE_TAC[GSYM(REWRITE_CONV [o_DEF]
        `(\x. x rpow y) o (\e. s - e)`)] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_SUB; REAL_CONTINUOUS_WITHIN_ID;
                   REAL_CONTINUOUS_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_RPOW THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
    W(MP_TAC o PART_MATCH (lhand o rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
      rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
    EXISTS_TAC `min (measure(s:real^N->bool)) (measure(t:real^N->bool))` THEN
    ASM_SIMP_TAC[REAL_LT_MIN; IN_ELIM_THM; REAL_SUB_RZERO;
                 MEASURE_OPEN_POS_LT] THEN
    X_GEN_TAC `e:real` THEN REWRITE_TAC[real_abs] THEN
    ASM_CASES_TAC `&0 <= e` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY (fun l -> MP_TAC(ISPECL l OPEN_MEASURABLE_INNER_DIVISION))
    [[`t:real^N->bool`; `e:real`]; [`s:real^N->bool`; `e:real`]] THEN
    ASM_SIMP_TAC[MEASURABLE_OPEN; GSYM REAL_LT_SUB_RADD] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `E:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`UNIONS D:real^N->bool`; `UNIONS E:real^N->bool`]
        BRUNN_MINKOWSKI_ELEMENTARY) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURE_EMPTY; REAL_ARITH `e < s ==> ~(s - e < &0)`];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `s1 <= r1 /\ s2 <= r2 /\ rs <= s
      ==> rs >= r1 + r2 ==> s1 + s2 <= s`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[DIMINDEX_NONZERO; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN
     `measurable {x + y :real^N | x IN UNIONS D /\ y IN UNIONS E}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MEASURABLE_COMPACT THEN MATCH_MP_TAC COMPACT_SUMS THEN
      ASM_MESON_TAC[ELEMENTARY_COMPACT];
      MATCH_MP_TAC MEASURE_SUBSET] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_OPEN THEN
    ASM_SIMP_TAC[BOUNDED_SUMS; OPEN_SUMS]]);;

(* ------------------------------------------------------------------------- *)
(* Now for convex sets.                                                      *)
(* ------------------------------------------------------------------------- *)

let BRUNN_MINKOWSKI_CONVEX = prove
 (`!s t:real^N->bool.
    (s = {} <=> t = {}) /\ bounded s /\ convex s /\ bounded t /\ convex t
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[BRUNN_MINKOWSKI_OPEN; OPEN_EMPTY] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM MEASURE_INTERIOR; NEGLIGIBLE_CONVEX_FRONTIER; real_ge] THEN
  ASM_CASES_TAC `interior s:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[MEASURE_EMPTY; ROOT_0; DIMINDEX_NONZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[DIMINDEX_NONZERO; MEASURE_POS_LE; MEASURABLE_INTERIOR] THEN
    SUBGOAL_THEN `?a:real^N. a IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(IMAGE (\x:real^N. a + x) t)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURE_TRANSLATION; MEASURE_INTERIOR;
                   NEGLIGIBLE_CONVEX_FRONTIER; REAL_LE_REFL];
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_CONVEX;
                   CONVEX_SUMS; BOUNDED_SUMS] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `interior t:real^N->bool = {}` THENL
   [ASM_SIMP_TAC[MEASURE_EMPTY; ROOT_0; DIMINDEX_NONZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[DIMINDEX_NONZERO; MEASURE_POS_LE; MEASURABLE_INTERIOR] THEN
    SUBGOAL_THEN `?a:real^N. a IN t` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(IMAGE (\x:real^N. a + x) s)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURE_TRANSLATION; MEASURE_INTERIOR;
                   NEGLIGIBLE_CONVEX_FRONTIER; REAL_LE_REFL];
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_CONVEX;
                   CONVEX_SUMS; BOUNDED_SUMS] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [VECTOR_ADD_SYM] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
    `root (dimindex (:N))
          (measure {x + y:real^N | x IN interior s /\ y IN interior t})` THEN
  ASM_SIMP_TAC[GSYM real_ge; BRUNN_MINKOWSKI_OPEN; BOUNDED_INTERIOR;
               OPEN_INTERIOR] THEN
  REWRITE_TAC[real_ge] THEN MATCH_MP_TAC ROOT_MONO_LE THEN
  REWRITE_TAC[DIMINDEX_NONZERO] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[DIMINDEX_NONZERO; MEASURE_POS_LE; BOUNDED_SUMS;
     MEASURABLE_CONVEX; BOUNDED_INTERIOR; CONVEX_SUMS; CONVEX_INTERIOR] THEN
  MATCH_MP_TAC(SET_RULE
   `s' SUBSET s /\ t' SUBSET t
    ==> {x + y:real^N | x IN s' /\ y IN t'} SUBSET
        {x + y | x IN s /\ y IN t}`) THEN
  REWRITE_TAC[INTERIOR_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Now for compact sets.                                                     *)
(* ------------------------------------------------------------------------- *)

let INTERS_SUMS_CLOSED_BALL_SEQUENTIAL = prove
 (`!s:real^N->bool.
        closed s
        ==> INTERS {{x + d | x IN s /\ d IN ball(vec 0,inv(&n + &1))} |
                    n IN (:num)} = s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`] SEPARATE_POINT_CLOSED) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^N`; `e:real^N`] THEN
    REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[NORM_ARITH `dist(y + e:real^N,y) = norm e`] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID; REAL_LT_INV_EQ] THEN
    REAL_ARITH_TAC]);;

let MEASURE_SUMS_COMPACT_EPSILON = prove
 (`!s:real^N->bool.
        compact s
        ==> ((\e. measure {x + d | x IN s /\ d IN ball(vec 0,e)})
             ---> measure s)
            (atreal (&0) within {e | &0 <= e})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `\n. {x + d:real^N | x IN s /\ d IN ball(vec 0,inv(&n + &1))}`
   HAS_MEASURE_NESTED_INTERS) THEN
  ASM_SIMP_TAC[INTERS_SUMS_CLOSED_BALL_SEQUENTIAL; COMPACT_IMP_CLOSED] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MEASURABLE_OPEN; BOUNDED_SUMS; OPEN_SUMS;
                 COMPACT_IMP_BOUNDED; BOUNDED_BALL; OPEN_BALL] THEN
    GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `t' SUBSET t
      ==> {x + y:real^N | x IN s /\ y IN t'} SUBSET
          {x + y | x IN s /\ y IN t}`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(REWRITE_RULE[o_DEF] TENDSTO_REAL)] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REALLIM_WITHINREAL] THEN
  STRIP_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `inv(&N + &1)` THEN
  ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `d:real` THEN REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO] THEN
  ASM_CASES_TAC `abs d = d` THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN STRIP_TAC; ASM_REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `m <= m1 /\ m1 <= m2
    ==> abs(m2 - m) < e ==> abs(m1 - m) < e`) THEN
  CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_OPEN; BOUNDED_SUMS; OPEN_SUMS;
               COMPACT_IMP_BOUNDED; BOUNDED_BALL; OPEN_BALL]
  THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_ADD_RID];
    MATCH_MP_TAC(SET_RULE
     `t' SUBSET t
      ==> {x + y:real^N | x IN s /\ y IN t'} SUBSET
          {x + y | x IN s /\ y IN t}`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

let BRUNN_MINKOWSKI_COMPACT = prove
 (`!s t:real^N->bool.
    (s = {} <=> t = {}) /\ compact s /\ compact t
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)`,
  let lemma1 = prove
   (`{ x + y:real^N | x IN {x + d | x IN s /\ d IN ball(vec 0,e)} /\
                      y IN {y + d | y IN t /\ d IN ball(vec 0,e)}} =
     { z + d | z IN {x + y | x IN s /\ y IN t} /\ d IN ball(vec 0,&2 * e) }`,
    MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_BALL_0] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      X_GEN_TAC `k:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `x + y:real^N` THEN EXISTS_TAC `d + k:real^N` THEN
      CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
      ASM_SIMP_TAC[NORM_ARITH
       `norm(d:real^N) < e /\ norm(k) < e ==> norm(d + k) < &2 * e`] THEN
      EXISTS_TAC `x:real^N` THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      X_GEN_TAC `d:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `x + inv(&2) % d:real^N` THEN
      EXISTS_TAC `y + inv(&2) % d:real^N` THEN
      CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^N`; EXISTS_TAC `y:real^N`] THEN
      EXISTS_TAC `inv(&2) % d:real^N` THEN
      ASM_REWRITE_TAC[NORM_MUL] THEN ASM_REAL_ARITH_TAC])
  and lemma2 = prove
   (`(f ---> l) (atreal (&0) within {e | &0 <= e})
     ==> ((\e. f(&2 * e)) ---> l) (atreal (&0) within {e | &0 <= e})`,
    REWRITE_TAC[REALLIM_WITHINREAL] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[BRUNN_MINKOWSKI_OPEN; OPEN_EMPTY; BOUNDED_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
  MATCH_MP_TAC(ISPEC `atreal (&0) within {e | &0 <= e}` REALLIM_LE) THEN
  EXISTS_TAC
   `\e. root (dimindex(:N))
             (measure {x + d:real^N | x IN s /\ d IN ball(vec 0,e)}) +
        root (dimindex(:N))
             (measure {x + d:real^N | x IN t /\ d IN ball(vec 0,e)})` THEN
  EXISTS_TAC
   `\e. root (dimindex(:N))
             (measure { x + y:real^N |
                   x IN {x + d | x IN s /\ d IN ball(vec 0,e)} /\
                   y IN {y + d | y IN t /\ d IN ball(vec 0,e)}})` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [REAL_ROOT_RPOW; DIMINDEX_NONZERO; MEASURE_POS_LE; MEASURABLE_COMPACT;
      MEASURABLE_OPEN; BOUNDED_SUMS; OPEN_SUMS;
      COMPACT_IMP_BOUNDED; BOUNDED_BALL; OPEN_BALL] THEN
    MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REALLIM_RPOW THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    MATCH_MP_TAC MEASURE_SUMS_COMPACT_EPSILON THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[lemma1] THEN MATCH_MP_TAC lemma2 THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 6)
     [REAL_ROOT_RPOW; DIMINDEX_NONZERO; MEASURE_POS_LE; MEASURABLE_COMPACT;
      MEASURABLE_OPEN; BOUNDED_SUMS; OPEN_SUMS; COMPACT_SUMS;
      COMPACT_IMP_BOUNDED; BOUNDED_BALL; OPEN_BALL] THEN
    MATCH_MP_TAC REALLIM_RPOW THEN
    REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    MATCH_MP_TAC MEASURE_SUMS_COMPACT_EPSILON THEN
    ASM_SIMP_TAC[COMPACT_SUMS];
    W(MP_TAC o PART_MATCH (lhand o rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
      rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `e:real` THEN
    REWRITE_TAC[GSYM real_ge] THEN
    MATCH_MP_TAC BRUNN_MINKOWSKI_OPEN THEN
    SIMP_TAC[OPEN_SUMS; OPEN_BALL] THEN
    ASM_SIMP_TAC[BOUNDED_SUMS; BOUNDED_BALL; COMPACT_IMP_BOUNDED] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finally, for an arbitrary measurable set. In this general case, the       *)
(* measurability of the sum-set is needed as an additional hypothesis.       *)
(* ------------------------------------------------------------------------- *)

let BRUNN_MINKOWSKI_MEASURABLE = prove
 (`!s t:real^N->bool.
    (s = {} <=> t = {}) /\ measurable s /\ measurable t /\
    measurable {x + y | x IN s /\ y IN t}
    ==> root (dimindex(:N)) (measure {x + y | x IN s /\ y IN t})
        >= root (dimindex(:N)) (measure s) + root (dimindex(:N)) (measure t)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_SIMP_TAC[BRUNN_MINKOWSKI_OPEN; OPEN_EMPTY; BOUNDED_EMPTY] THEN
  STRIP_TAC THEN REWRITE_TAC[real_ge] THEN
  ASM_CASES_TAC `measure(s:real^N->bool) = &0` THENL
   [ASM_SIMP_TAC[ROOT_0; DIMINDEX_NONZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[DIMINDEX_NONZERO; MEASURE_POS_LE] THEN
    SUBGOAL_THEN `?a:real^N. a IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(IMAGE (\x:real^N. a + x) t)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURE_TRANSLATION; REAL_LE_REFL];
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `measure(t:real^N->bool) = &0` THENL
   [ASM_SIMP_TAC[ROOT_0; DIMINDEX_NONZERO; REAL_ADD_RID] THEN
    MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[DIMINDEX_NONZERO; MEASURE_POS_LE] THEN
    SUBGOAL_THEN `?a:real^N. a IN t` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(IMAGE (\x:real^N. a + x) s)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURE_TRANSLATION; REAL_LE_REFL];
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [VECTOR_ADD_SYM] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < measure(s:real^N->bool) /\
    &0 < measure(t:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_MEASURE_POS_LT; MEASURABLE_MEASURE_EQ_0];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPEC `atreal(&0) within {e | &0 <= e}` REALLIM_UBOUND) THEN
  EXISTS_TAC `\e. root (dimindex(:N)) (measure(s:real^N->bool) - e) +
                  root (dimindex(:N)) (measure(t:real^N->bool) - e)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC
     `\e. (measure(s:real^N->bool) - e) rpow (inv(&(dimindex(:N)))) +
          (measure(t:real^N->bool) - e) rpow (inv(&(dimindex(:N))))` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
      EXISTS_TAC `min (measure(s:real^N->bool)) (measure(t:real^N->bool))` THEN
      ASM_SIMP_TAC[REAL_LT_MIN; IN_ELIM_THM; REAL_SUB_RZERO;
                   MEASURE_OPEN_POS_LT] THEN
      REPEAT STRIP_TAC THEN BINOP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC REAL_ROOT_RPOW THEN
      REWRITE_TAC[DIMINDEX_NONZERO] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ROOT_RPOW; MEASURE_OPEN_POS_LT; DIMINDEX_NONZERO;
                   REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `measure(s:real^N->bool) = measure s - &0`] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_WITHINREAL] THEN
      REWRITE_TAC[GSYM(REWRITE_CONV [o_DEF]
        `(\x. x rpow y) o (\e. s - e)`)] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_SUB; REAL_CONTINUOUS_WITHIN_ID;
                   REAL_CONTINUOUS_CONST] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_RPOW THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]];
    W(MP_TAC o PART_MATCH (lhand o rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
      rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTENSION; IN_SING] THEN
      DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN
    EXISTS_TAC `min (measure(s:real^N->bool)) (measure(t:real^N->bool))` THEN
    ASM_SIMP_TAC[REAL_LT_MIN; IN_ELIM_THM; REAL_SUB_RZERO] THEN
    X_GEN_TAC `e:real` THEN REWRITE_TAC[real_abs] THEN
    ASM_CASES_TAC `&0 <= e` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY (fun l -> MP_TAC(ISPECL l MEASURABLE_INNER_COMPACT))
    [[`t:real^N->bool`; `e:real`]; [`s:real^N->bool`; `e:real`]] THEN
    ASM_SIMP_TAC[MEASURABLE_OPEN; GSYM REAL_LT_SUB_RADD] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s':real^N->bool`; `t':real^N->bool`]
        BRUNN_MINKOWSKI_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURE_EMPTY; REAL_ARITH `e < s ==> ~(s - e < &0)`];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `s1 <= r1 /\ s2 <= r2 /\ rs <= s
      ==> rs >= r1 + r2 ==> s1 + s2 <= s`) THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC ROOT_MONO_LE THEN
    ASM_SIMP_TAC[DIMINDEX_NONZERO; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; COMPACT_SUMS; MEASURABLE_COMPACT] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; COMPACT_SUMS; MEASURABLE_COMPACT] THEN
    ASM SET_TAC[]]);;
