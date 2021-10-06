(* ========================================================================= *)
(* Construction of p-adic numbers.                                           *)
(* ========================================================================= *)

needs "Library/prime.ml";;              (* For the "index" function only *)
needs "Multivariate/metric.ml";;        (* For metric spaces             *)

(* ------------------------------------------------------------------------- *)
(* p-adic norm on the rationals (call it "qnorm" then extend it to "pnorm"). *)
(* ------------------------------------------------------------------------- *)

let [qnorm_def; QNORM_EQ_0; QNORM_ABS] =
  let qnorm_exists = prove
   (`?qnorm.
          (!p m n. prime p /\ ~(m = 0) /\ ~(n = 0)
                   ==> qnorm p (&m / &n) =
                       &p pow (index p n) / &p pow (index p m)) /\
          (!p x. qnorm p x = &0 <=> ~prime p \/ ~rational x \/ x = &0) /\
          (!p x. qnorm p (abs x) = qnorm p x)`,
    SUBGOAL_THEN
     `?padic. !p m n.
          padic p (&m / &n) =
          if ~prime p \/ m = 0 \/ n = 0 then &0
          else &p pow (index p n) / &p pow (index p m)`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
      REWRITE_TAC[FORALL_UNPAIR_THM] THEN
      GEN_REWRITE_TAC BINDER_CONV [GSYM FUN_EQ_THM] THEN
      GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [GSYM o_DEF] THEN
      CONV_TAC (ONCE_DEPTH_CONV SYM_CONV) THEN
      GEN_REWRITE_TAC I [GSYM FUNCTION_FACTORS_LEFT] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`a1:num`; `b1:num`; `a2:num`; `b2:num`] THEN
      ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[real_div] THEN
      MAP_EVERY (fun t ->
        ASM_CASES_TAC t THENL
         [ASM_REWRITE_TAC[] THEN
          ASM_METIS_TAC[REAL_INV_EQ_0; REAL_ENTIRE; REAL_OF_NUM_EQ];
          ALL_TAC]) [`a1 = 0`; `a2 = 0`; `b1 = 0`; `b2 = 0`] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ; REAL_FIELD
       `~(y1 = &0) /\ ~(y2 = &0)
        ==> (x1 * inv y1 = x2 * inv y2 <=> x1 * y2 = x2 * y1)`] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THEN
      REWRITE_TAC[GSYM EXP_ADD] THEN DISCH_THEN(MP_TAC o AP_TERM `index p`) THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[ADD_SYM] INDEX_MUL];
      EXISTS_TAC `\p x. if rational x then (padic:num->real->real) p (abs x)
                        else &0` THEN
      ASM_SIMP_TAC[RATIONAL_ABS_EQ; REAL_ABS_ABS; RATIONAL_CLOSED] THEN
      REWRITE_TAC[MESON[]
       `((if q then y else &0) = &0 <=> ~p \/ ~q \/ x = &0) <=>
        (q ==> (y = &0 <=> ~p \/ x = &0))`] THEN
      REWRITE_TAC[RATIONAL_ALT; LEFT_IMP_EXISTS_THM] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
      MAP_EVERY X_GEN_TAC [`p:num`; `x:real`; `m:num`; `n:num`] THEN
      ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_DIV_EQ_0; REAL_POW_EQ_0] THEN
      ASM_SIMP_TAC[REAL_ABS_ZERO; real_div; REAL_MUL_LZERO; INDEX_EQ_0] THEN
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
      ASM_SIMP_TAC[REAL_OF_NUM_EQ] THEN MATCH_MP_TAC(REAL_ARITH
       `~(a = &0) ==> abs x = a ==> ~(x = &0)`) THEN
      ASM_REWRITE_TAC[REAL_ENTIRE; REAL_INV_EQ_0; REAL_OF_NUM_EQ]]) in
  CONJUNCTS(new_specification ["qnorm"] qnorm_exists);;

let qnorm = prove
 (`!p m n. qnorm p (&m / &n) =
           if ~prime p \/ m = 0 \/ n = 0 then &0
           else &p pow (index p n) / &p pow (index p m)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED; QNORM_EQ_0; REAL_DIV_EQ_0; REAL_OF_NUM_EQ] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN ASM_SIMP_TAC[qnorm_def]);;

let QNORM_NEG = prove
 (`!p x. qnorm p (--x) = qnorm p x`,
  MESON_TAC[QNORM_ABS; REAL_ABS_NEG]);;

let QNORM_0 = prove
 (`!p. qnorm p (&0) = &0`,
  REWRITE_TAC[QNORM_EQ_0]);;

let QNORM_MUL = prove
 (`!p x y. (rational (x * y) ==> rational x /\ rational y)
           ==> qnorm p (x * y) = qnorm p x * qnorm p y`,
  REPEAT GEN_TAC THEN MAP_EVERY
   (fun t -> ASM_CASES_TAC t THENL
   [ALL_TAC; ASM_METIS_TAC[QNORM_EQ_0; REAL_ENTIRE]])
   [`prime p`; `rational x`; `rational y`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM QNORM_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  MAP_EVERY UNDISCH_TAC [`rational y`; `rational x`] THEN
  SIMP_TAC[RATIONAL_ALT; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a1:num`; `b1:num`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a2:num`; `b2:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH
    `a1 / b1 * a2 / b2:real = (a1 * a2) * inv b1 * inv b2`] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL; REAL_OF_NUM_MUL] THEN
  ASM_REWRITE_TAC[qnorm; GSYM real_div; MULT_EQ_0] THEN
  ASM_CASES_TAC `a1 = 0` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `a2 = 0` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  ASM_SIMP_TAC[INDEX_MUL; REAL_POW_ADD] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN CONV_TAC REAL_FIELD);;

let QNORM_1 = prove
 (`!p. qnorm p (&1) = if prime p then &1 else &0`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[QNORM_EQ_0] THEN
  MATCH_MP_TAC(REAL_RING `~(x = &0) /\ x * x = x ==> x = &1`) THEN
  ASM_SIMP_TAC[QNORM_EQ_0; RATIONAL_CLOSED; GSYM QNORM_MUL] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let QNORM_INV = prove
 (`!p x. rational x ==> qnorm p (inv x) = inv(qnorm p x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real = &0` THEN
  ASM_REWRITE_TAC[REAL_INV_0; QNORM_0] THEN ASM_CASES_TAC `prime p` THENL
   [ALL_TAC; ASM_METIS_TAC[QNORM_EQ_0; REAL_INV_0]] THEN
  MATCH_MP_TAC(REAL_FIELD `x * y = &1 ==> x = inv y`) THEN
  ASM_SIMP_TAC[GSYM QNORM_MUL; RATIONAL_CLOSED] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; QNORM_1]);;

let QNORM_POS_LE = prove
 (`!p x. &0 <= qnorm p x`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `(~(x = &0) ==> &0 <= x) ==> &0 <= x`) THEN
  REWRITE_TAC[QNORM_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM QNORM_ABS] THEN
  MAP_EVERY UNDISCH_TAC [`~(x = &0)`; `rational x`] THEN
  SIMP_TAC[RATIONAL_ALT; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_ZERO] THEN
  SIMP_TAC[REAL_DIV_EQ_0; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[qnorm_def; REAL_LE_DIV; REAL_POW_LE; REAL_POS]);;

let QNORM_POS_LT = prove
 (`!p x. &0 < qnorm p x <=> prime p /\ rational x /\ ~(x = &0)`,
  REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
  REWRITE_TAC[QNORM_POS_LE; QNORM_EQ_0] THEN CONV_TAC TAUT);;

let QNORM_ULTRA = prove
 (`!p x y. (rational(x + y) ==> rational x /\ rational y)
           ==> qnorm p (x + y) <= max (qnorm p x) (qnorm p y)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x = &0` THEN
  ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ARITH `y <= max x y`] THEN
  ASM_CASES_TAC `y = &0` THEN
  ASM_REWRITE_TAC[REAL_ADD_RID; REAL_ARITH `x <= max x y`] THEN
  ASM_CASES_TAC `prime p` THENL
   [ALL_TAC; ASM_METIS_TAC[QNORM_EQ_0; REAL_ARITH `x <= max x x`]] THEN
  ASM_CASES_TAC `rational(x + y)` THEN
  ASM_REWRITE_TAC[] THENL
   [REPEAT(POP_ASSUM MP_TAC);
    MATCH_MP_TAC(REAL_ARITH `x = &0 /\ &0 <= y ==> x <= max y z`) THEN
    ASM_REWRITE_TAC[QNORM_POS_LE; QNORM_EQ_0]] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`y:real`; `x:real`] THEN
  MATCH_MP_TAC(MESON[REAL_LE_TOTAL]
   `(!x y. P x y ==> P y x) /\ (!x y. abs y <= abs x ==> P x y)
    ==> (!x y. P x y)`) THEN
  CONJ_TAC THENL
   [MESON_TAC[REAL_ADD_SYM; REAL_ARITH `max a b = max b a`];
    REPEAT STRIP_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(x = &0)`; `~(y = &0)`; `rational y`; `rational x`] THEN
  SIMP_TAC[RATIONAL_ALT; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a1:num`; `b1:num`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`a2:num`; `b2:num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_ZERO] THEN ASM_REWRITE_TAC[REAL_DIV_EQ_0] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ] THEN REPEAT DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM QNORM_ABS] THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP
   (REAL_ARITH `abs y <= abs x ==> abs(x + y) = abs x + abs y \/
                                   abs(x + y) = abs x - abs y`)) THEN
  UNDISCH_TAC `abs y <= abs x` THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b * c:real = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
   `~(b1 = &0) /\ ~(b2 = &0)
    ==> a1 / b1 + a2 / b2 = (a1 * b2 + a2 * b1) / (b1 * b2) /\
        a1 / b1 - a2 / b2 = (a1 * b2 - a2 * b1) / (b1 * b2)`] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
  SIMP_TAC[REAL_OF_NUM_SUB] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[qnorm; MULT_EQ_0; REAL_LE_MAX; ADD_EQ_0] THEN
  TRY COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / b * c:real = (a * c) / b`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1; REAL_POW_LT] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN MATCH_MP_TAC(MESON[REAL_POW_MONO]
   `&1 <= p /\ (u <= v \/ x <= y)
    ==> p pow u <= p pow v \/ p pow x <= p pow y`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_IMP_NZ; LE_1; INDEX_MUL] THEN
  REWRITE_TAC[ARITH_RULE `(b1 + b2) + a1:num <= b1 + c <=> b2 + a1 <= c`] THEN
  REWRITE_TAC[ARITH_RULE `(b1 + b2) + a1:num <= b2 + c <=> b1 + a1 <= c`] THEN
  ASM_SIMP_TAC[GSYM INDEX_MUL] THEN
  REWRITE_TAC[ARITH_RULE `x <= z \/ y <= z <=> MIN x y <= z`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  REWRITE_TAC[INDEX_ADD_MIN] THEN MATCH_MP_TAC INDEX_SUB_MIN THEN
  ASM_ARITH_TAC);;

let QNORM_TRIANGLE = prove
 (`!p x y. (rational(x + y) ==> rational x /\ rational y)
           ==> qnorm p (x + y) <= qnorm p x + qnorm p y`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `p:num` o MATCH_MP QNORM_ULTRA) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> max x y <= x + y`) THEN
  REWRITE_TAC[QNORM_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* p-adic metric on the rationals. To keep theorems cleaner, we default to   *)
(* p = 2 in the case where p is non-prime.                                   *)
(* ------------------------------------------------------------------------- *)

let qadic_metric = new_definition
  `qadic_metric p =
        metric(rational,(\(x,y). qnorm (if prime p then p else 2) (x - y)))`;;

let QADIC_METRIC = prove
 (`(!p. mspace(qadic_metric p) = rational) /\
   (!p x y. mdist(qadic_metric p) (x,y) =
                if prime p then qnorm p (x - y)
                else qnorm 2 (x - y))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `p:num` THEN
  MP_TAC(ISPECL [`rational`;
    `\(x,y). qnorm (if prime p then p else 2) (x - y)`] METRIC) THEN
  ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[qadic_metric] THEN
  REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[is_metric_space] THEN
  ASM_SIMP_TAC[QNORM_POS_LE; QNORM_EQ_0; RATIONAL_CLOSED; REAL_SUB_0;
               PRIME_2; IN] THEN
  (CONJ_TAC THENL [MESON_TAC[QNORM_ABS; REAL_ABS_SUB]; ALL_TAC]) THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `z:real`] THEN STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `x - z:real = (x - y) + (y - z)`) THEN
  ASM_SIMP_TAC[QNORM_TRIANGLE; RATIONAL_CLOSED]);;

let QADIC_ULTRAMETRIC = prove
 (`!p x y z.
        x IN mspace(qadic_metric p) /\
        y IN mspace(qadic_metric p) /\
        z IN mspace(qadic_metric p)
        ==> mdist(qadic_metric p) (x,z) <=
            max (mdist(qadic_metric p) (x,y)) (mdist(qadic_metric p) (y,z))`,
  GEN_TAC THEN ASM_CASES_TAC `prime p` THEN
  ASM_REWRITE_TAC[QADIC_METRIC] THEN REWRITE_TAC[IN] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `z:real`] THEN STRIP_TAC THEN
  SUBST1_TAC(REAL_ARITH `x - z:real = (x - y) + (y - z)`) THEN
  ASM_SIMP_TAC[QNORM_ULTRA; RATIONAL_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Actual padics; make them a whole type ":padic", overlaying the versions   *)
(* for different p's with the same embedding of the rationals (using some    *)
(* arbitrary countably infinite subset that's the same for each value of p). *)
(* ------------------------------------------------------------------------- *)

let padic_tybij =
  let th = prove(`?x:real. T`,REWRITE_TAC[]) in
  REWRITE_RULE[] (new_type_definition "padic" ("mk_padic","dest_padic") th);;

let CARD_EQ_PADIC = prove
 (`(:padic) =_c (:real)`,
  REWRITE_TAC[EQ_C_BIJECTIONS; IN_UNIV] THEN
  MAP_EVERY EXISTS_TAC [`dest_padic`; `mk_padic`] THEN
  MESON_TAC[padic_tybij]);;

let prational =
  let th = prove
   (`?s:padic->bool. s =_c (:num)`,
    REWRITE_TAC[CARD_LE_EQ_SUBSET_UNIV] THEN
    TRANS_TAC CARD_LE_TRANS `(:real)` THEN
    SIMP_TAC[CARD_LT_NUM_REAL; CARD_LT_IMP_LE] THEN
    MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_ACCEPT_TAC CARD_EQ_PADIC) in
  new_specification ["prational"] th;;

let padic_of_rational,rational_of_padic =
  let th = prove
   (`prational =_c rational`,
    TRANS_TAC CARD_EQ_TRANS `(:num)` THEN
    MESON_TAC[CARD_EQ_RATIONAL; CARD_EQ_SYM; prational]) in
  CONJ_PAIR(new_specification ["rational_of_padic"; "padic_of_rational"]
   (REWRITE_RULE[EQ_C_BIJECTIONS; IN_UNIV] th));;

let IMAGE_PADIC_OF_RATIONAL_RATIONAL = prove
 (`IMAGE padic_of_rational rational = prational`,
  MP_TAC padic_of_rational THEN MP_TAC rational_of_padic THEN SET_TAC[]);;

let padic_metric =
  let PADICS_EXIST = prove
   (`!p. ?(m:padic metric).
          mcomplete m /\
          mspace m = (:padic) /\
          mtopology m closure_of prational = (:padic) /\
          mtopology m derived_set_of prational = (:padic) /\
          !x y. rational x /\ rational y
                ==> mdist m (padic_of_rational x,padic_of_rational y) =
                    qnorm (if prime p then p else 2) (x - y)`,
    X_GEN_TAC `p:num` THEN
    MP_TAC(ISPEC `qadic_metric p` METRIC_COMPLETION_EXPLICIT) THEN
    REWRITE_TAC[QADIC_METRIC; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:(real->real)->bool`; `f:real->real->real`] THEN
    ABBREV_TAC `m = funspace rational real_euclidean_metric` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `mtopology (submetric m s) derived_set_of
                (IMAGE f rational):(real->real)->bool = s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [TRANS_TAC SUBSET_TRANS
         `mtopology (submetric m s) derived_set_of s:(real->real)->bool` THEN
        ASM_SIMP_TAC[DERIVED_SET_OF_MONO] THEN
        REWRITE_TAC[DERIVED_SET_SUBSET_GEN; TOPSPACE_MTOPOLOGY] THEN
        MATCH_MP_TAC MCOMPLETE_IMP_CLOSED_IN THEN
        REWRITE_TAC[INTER_SUBSET; SUBMETRIC; SUBMETRIC_SUBMETRIC] THEN
        ASM_SIMP_TAC[SET_RULE
         `s SUBSET m ==> s INTER (s INTER m) INTER s = s`];
        TRANS_TAC SUBSET_TRANS
          `mtopology(submetric m s) closure_of
           (IMAGE (f:real->real->real) rational)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[MTOPOLOGY_SUBMETRIC; CLOSURE_OF_SUBTOPOLOGY] THEN
          ASM_SIMP_TAC[SET_RULE `t SUBSET s ==> s INTER t = t`; SUBSET_REFL];
          ALL_TAC] THEN
        REWRITE_TAC[CLOSURE_OF] THEN MATCH_MP_TAC(SET_RULE
         `u SUBSET v /\ t SUBSET u ==> s INTER (t UNION u) SUBSET v`) THEN
        ASM_SIMP_TAC[DERIVED_SET_OF_MONO] THEN
        REWRITE_TAC[METRIC_DERIVED_SET_OF; SUBSET; FORALL_IN_IMAGE] THEN
        ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
        REWRITE_TAC[EXISTS_IN_IMAGE; IN_ELIM_THM; IN_MBALL; SUBMETRIC] THEN
        X_GEN_TAC `x:real` THEN DISCH_TAC THEN CONJ_TAC THENL
         [ASM SET_TAC[]; X_GEN_TAC `r:real` THEN DISCH_TAC] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN REWRITE_TAC[IN] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[MESON[]
         `(if prime p then qnorm p x else qnorm q x) =
          qnorm (if prime p then p else q) x`]) THEN
        ABBREV_TAC `p' = if prime p then p else 2` THEN
        SUBGOAL_THEN `prime p' /\ 2 <= p'` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[PRIME_2; PRIME_GE_2]; ALL_TAC] THEN
        MP_TAC(ISPECL [`inv(&p')`; `r:real`] REAL_ARCH_POW_INV) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [MATCH_MP_TAC REAL_INV_LT_1 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          ASM_ARITH_TAC;
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
        ABBREV_TAC `y = x + &p' pow n` THEN EXISTS_TAC `y:real` THEN
        MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
        CONJ_TAC THENL [ASM_MESON_TAC[RATIONAL_CLOSED]; DISCH_TAC] THEN
        REWRITE_TAC[INTER; IN_ELIM_THM] THEN ONCE_REWRITE_TAC[TAUT
         `p /\ q /\ r /\ s <=> (q /\ r) /\ (q /\ r ==> p /\ s)`] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
        MP_TAC(ISPEC `m:(real->real)metric` (GSYM MDIST_0)) THEN
        ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
        EXPAND_TAC "y" THEN REWRITE_TAC[REAL_ADD_SUB] THEN
        ONCE_REWRITE_TAC[GSYM QNORM_ABS] THEN
        REWRITE_TAC[REAL_ARITH `abs(x - (x + y)) = abs y`] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `abs x = abs(x / &1)`] THEN
        ASM_REWRITE_TAC[QNORM_ABS; qnorm; REAL_OF_NUM_POW] THEN
        CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
        ASM_SIMP_TAC[INDEX_1; INDEX_EXP; INDEX_REFL; EXP] THEN
        ASM_REWRITE_TAC[ARITH_RULE `p <= 1 <=> ~(2 <= p)`] THEN
        REWRITE_TAC[real_div; MULT_CLAUSES; REAL_MUL_LID] THEN
        ASM_REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_INV_POW] THEN
        REWRITE_TAC[REAL_POW_EQ_0; REAL_INV_EQ_0; REAL_OF_NUM_EQ] THEN
        ASM_SIMP_TAC[PRIME_IMP_NZ]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:(real->real)->bool) =_c (:real)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
       [TRANS_TAC CARD_LE_TRANS `mspace m:(real->real)->bool` THEN
        ASM_SIMP_TAC[CARD_LE_SUBSET] THEN EXPAND_TAC "m" THEN
        TRANS_TAC CARD_LE_TRANS `(:real) ^_c rational` THEN CONJ_TAC THENL
         [REWRITE_TAC[EXP_C; FUNSPACE; REAL_EUCLIDEAN_METRIC] THEN
          MATCH_MP_TAC CARD_LE_SUBSET THEN SET_TAC[];
          SIMP_TAC[CARD_EXP_LE_REAL; CARD_LE_REFL; COUNTABLE_RATIONAL]];
        MATCH_MP_TAC CARD_GE_PERFECT_SET THEN
        EXISTS_TAC `mtopology(submetric m (s:(real->real)->bool))` THEN
        ASM_SIMP_TAC[COMPLETELY_METRIZABLE_SPACE_MTOPOLOGY] THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN CONJ_TAC THENL
         [ALL_TAC; MP_TAC RATIONAL_NUM THEN ASM SET_TAC[]] THEN
        MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [W(MP_TAC o PART_MATCH lhand DERIVED_SET_OF_SUBSET_CLOSURE_OF o
            lhand o snd) THEN
          REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY; MTOPOLOGY_SUBMETRIC] THEN
          ASM SET_TAC[];
          TRANS_TAC SUBSET_TRANS
           `mtopology (submetric m s) derived_set_of
              (IMAGE f rational):(real->real)->bool` THEN
          ASM_SIMP_TAC[DERIVED_SET_OF_MONO; SUBSET_REFL]]];
      ALL_TAC] THEN
    MP_TAC(fst(EQ_IMP_RULE(ISPECL [`f:real->real->real`; `rational`]
        INJECTIVE_ON_LEFT_INVERSE))) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
      ASM_REWRITE_TAC[] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MDIST_REFL o lhand o lhand o
        snd) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      CONV_TAC(LAND_CONV SYM_CONV) THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[QNORM_EQ_0; PRIME_2; RATIONAL_CLOSED] THEN
      REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `f':(real->real)->real`)] THEN
    MP_TAC(ISPECL
     [`padic_of_rational o (f':(real->real)->real)`;
      `(f:real->real->real) o rational_of_padic`;
      `IMAGE (f:real->real->real) rational`; `s:(real->real)->bool`;
      `prational`; `(:padic)`] EQ_C_BIJECTIONS_EXTEND) THEN
    ASM_REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CARD_DIFF_CONG THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
        REPEAT CONJ_TAC THENL
         [TRANS_TAC CARD_EQ_TRANS `(:real)` THEN ASM_REWRITE_TAC[] THEN
          ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[CARD_EQ_PADIC];
          TRANS_TAC CARD_EQ_TRANS `rational` THEN CONJ_TAC THENL
           [MATCH_MP_TAC CARD_EQ_IMAGE THEN ASM SET_TAC[];
            TRANS_TAC CARD_EQ_TRANS `(:num)` THEN
            REWRITE_TAC[CARD_EQ_RATIONAL] THEN
            ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN REWRITE_TAC[prational]];
          DISCH_THEN(K ALL_TAC) THEN TRANS_TAC CARD_LET_TRANS `rational` THEN
          REWRITE_TAC[CARD_LE_IMAGE] THEN
          TRANS_TAC CARD_LET_TRANS `(:num)` THEN
          SIMP_TAC[CARD_EQ_RATIONAL; CARD_EQ_IMP_LE] THEN
          TRANS_TAC CARD_LTE_TRANS `(:real)` THEN
          REWRITE_TAC[CARD_LT_NUM_REAL] THEN
          ASM_MESON_TAC[CARD_EQ_IMP_LE; CARD_EQ_SYM]];
        ASM_SIMP_TAC[FORALL_IN_IMAGE; o_THM] THEN
        MP_TAC rational_of_padic THEN MP_TAC padic_of_rational THEN
        ASM SET_TAC[]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE; IN_UNIV]] THEN
    MAP_EVERY X_GEN_TAC [`g:(real->real)->padic`; `h:padic->(real->real)`] THEN
    ASM_SIMP_TAC[FORALL_AND_THM; o_THM] THEN STRIP_TAC THEN
    ABBREV_TAC `m' = metric(IMAGE (g:(real->real)->padic) s,
                   (\(x,y). mdist m ((h:padic->real->real) x,h y)))` THEN
    EXISTS_TAC `m':padic metric` THEN
    MP_TAC(ISPECL
     [`IMAGE (g:(real->real)->padic) s`;
      `\(x,y). mdist m ((h:padic->real->real) x,h y)`] METRIC) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[is_metric_space; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
      ASM_SIMP_TAC[MDIST_POS_LE; MDIST_0; MDIST_TRIANGLE] THEN
      ASM_MESON_TAC[MDIST_SYM];
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [FUN_EQ_THM] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN STRIP_TAC] THEN
    REWRITE_TAC[IMAGE_o; o_THM] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mcomplete]) THEN
      REWRITE_TAC[CAUCHY_IN_SUBMETRIC; mcomplete; LIMIT_METRIC] THEN
      REWRITE_TAC[SUBMETRIC; cauchy_in] THEN DISCH_THEN(LABEL_TAC "*") THEN
      X_GEN_TAC `x:num->padic` THEN STRIP_TAC THEN FIRST_X_ASSUM
       (MP_TAC o SPEC `(h:padic->real->real) o (x:num->padic)`) THEN
      ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `l:real->real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
      GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `prational = IMAGE (g:(real->real)->padic)
                        (IMAGE (f:real->real->real) rational)`
    SUBST1_TAC THENL
     [MP_TAC rational_of_padic THEN MP_TAC padic_of_rational THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `!x. x IN rational
          ==> g ((f:real->real->real) x) = padic_of_rational x` THEN
    REWRITE_TAC[IN] THEN
    DISCH_THEN(fun th -> SIMP_TAC[GSYM th]) THEN
    REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in `prational` o concl))) THEN
    MATCH_MP_TAC(TAUT `(q ==> p) /\ q /\ r ==> p /\ q /\ r`) THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSURE_OF; TOPSPACE_MTOPOLOGY] THEN ASM SET_TAC[];
      REWRITE_TAC[METRIC_DERIVED_SET_OF] THEN
      ASM_REWRITE_TAC[SET_RULE `{y | y IN IMAGE f s /\ P y} =
          IMAGE f {x | x IN s /\ P(f x)}`] THEN
      SUBGOAL_THEN `(:padic) = IMAGE (g:(real->real)->padic) s`
      SUBST1_TAC THENL [ASM SET_TAC[]; AP_TERM_TAC] THEN
      FIRST_X_ASSUM
       (MP_TAC o GEN_REWRITE_RULE LAND_CONV [METRIC_DERIVED_SET_OF]) THEN
      ASM_REWRITE_TAC[SUBMETRIC; IN_MBALL] THEN
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_MBALL; SUBMETRIC] THEN
      ASM_SIMP_TAC[SET_RULE `s SUBSET m ==> s INTER m = s`] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `k:real->real` THEN
      ASM_CASES_TAC `(k:real->real) IN s` THEN ASM_REWRITE_TAC[] THEN
      AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
      X_GEN_TAC `r:real` THEN ASM_CASES_TAC `&0 < r` THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ABS_TAC THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]) in
  new_specification ["padic_metric"]
   (REWRITE_RULE[SKOLEM_THM] PADICS_EXIST);;

(* ------------------------------------------------------------------------- *)
(* Extract the individual characteristics.                                   *)
(* ------------------------------------------------------------------------- *)

let MSPACE_PADIC_METRIC = prove
 (`!p. mspace(padic_metric p) = (:padic)`,
  REWRITE_TAC[padic_metric]);;

let MCOMPLETE_PADIC_METRIC = prove
 (`!p. mcomplete (padic_metric p)`,
  REWRITE_TAC[padic_metric]);;

let padic_topology = new_definition
 `padic_topology p = mtopology (padic_metric p)`;;

let TOPSPACE_PADIC_TOPOLOGY = prove
 (`!p. topspace(padic_topology p) = (:padic)`,
  REWRITE_TAC[padic_topology; TOPSPACE_MTOPOLOGY; MSPACE_PADIC_METRIC]);;

let HAUSDORFF_SPACE_PADIC_TOPOLOGY = prove
 (`!p. hausdorff_space (padic_topology p)`,
  REWRITE_TAC[padic_topology; HAUSDORFF_SPACE_MTOPOLOGY]);;

let CLOSURE_OF_PRATIONAL = prove
 (`!p. (padic_topology p) closure_of prational = (:padic)`,
  REWRITE_TAC[padic_topology; padic_metric]);;

let DERIVED_SET_OF_PRATIONAL = prove
 (`!p. (padic_topology p) derived_set_of prational = (:padic)`,
  REWRITE_TAC[padic_topology; padic_metric]);;

let pdist = new_definition
 `pdist p = mdist (padic_metric p)`;;

let PDIST_GEN = prove
 (`!p q r. rational q /\ rational r
         ==> pdist p (padic_of_rational q,padic_of_rational r) =
             if prime p then qnorm p (q - r) else qnorm 2 (q - r)`,
  SIMP_TAC[pdist; padic_metric] THEN MESON_TAC[]);;

let PDIST = prove
 (`!p q r. prime p /\ rational q /\ rational r
           ==> pdist p (padic_of_rational q,padic_of_rational r) =
               qnorm p (q - r)`,
  SIMP_TAC[PDIST_GEN]);;

let PDIST_ALT = prove
 (`!p q r. rational q /\ rational r
           ==> pdist p (padic_of_rational q,padic_of_rational r) =
               qnorm (if prime p then p else 2) (q - r)`,
  SIMP_TAC[PDIST_GEN] THEN MESON_TAC[]);;

let PDIST_POS_LE = prove
 (`!p x y. &0 <= pdist p (x,y)`,
  SIMP_TAC[pdist; MDIST_POS_LE; MSPACE_PADIC_METRIC; IN_UNIV]);;

let PDIST_REFL = prove
 (`!p x. pdist p (x,x) = &0`,
  SIMP_TAC[pdist; MDIST_REFL; MSPACE_PADIC_METRIC; IN_UNIV]);;

let PDIST_SYM = prove
 (`!p x y. pdist p (x,y) = pdist p (y,x)`,
  SIMP_TAC[pdist; MDIST_SYM; MSPACE_PADIC_METRIC; IN_UNIV]);;

let PDIST_EQ_0 = prove
 (`!p x y. pdist p (x,y) = &0 <=> x = y`,
  SIMP_TAC[pdist; MDIST_0; MSPACE_PADIC_METRIC; IN_UNIV]);;

let PDIST_TRIANGLE = prove
 (`!p x y z.
        pdist p (x,z) <= pdist p (x,y) + pdist p (y,z)`,
  SIMP_TAC[pdist; MDIST_TRIANGLE; MSPACE_PADIC_METRIC; IN_UNIV]);;

let PDIST_ULTRA = prove
 (`!p x y z.
        pdist p (x,z) <= max (pdist p (x,y)) (pdist p (y,z))`,
  let lemma = prove
   (`!p. (\(x,y,z). &0 <= f x y z) p <=>
         f (FST p) (FST(SND p)) (SND(SND p)) IN {t | &0 <= t}`,
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM]) in
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`prod_topology (padic_topology p)
                   (prod_topology (padic_topology p) (padic_topology p))`;
    `\(x,y,z). pdist p (x,z)
               <= max (pdist p (x,y)) (pdist p (y,z))`;
    `prational CROSS prational CROSS prational`]
    FORALL_IN_CLOSURE_OF) THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; CLOSURE_OF_CROSS] THEN
  REWRITE_TAC[CLOSURE_OF_PRATIONAL; IN_UNIV] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PDIST_GEN] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (rand o rand) QNORM_ULTRA o rand o snd) THEN
    ASM_SIMP_TAC[RATIONAL_CLOSED] THEN MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;

    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN PURE_REWRITE_TAC[lemma] THEN
    MATCH_MP_TAC CLOSED_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `euclideanreal` THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[GSYM REAL_CLOSED_IN; GSYM real_ge;
                  REAL_CLOSED_HALFSPACE_GE]] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_REAL_SUB THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MAX THEN CONJ_TAC) THEN
    PURE_REWRITE_TAC[pdist] THEN MATCH_MP_TAC CONTINUOUS_MAP_MDIST THEN
    REWRITE_TAC[GSYM padic_topology] THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND] THEN TRY CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_MAP_FST_OF ORELSE
           MATCH_MP_TAC CONTINUOUS_MAP_SND_OF) THEN
    MESON_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND]]);;

(* ------------------------------------------------------------------------- *)
(* Extend addition and multiplication operations from the rationals.         *)
(* Also introduce a few natural derived operations.                          *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_PADIC_ADDITION,PADIC_ADD_OF_RATIONAL =
  let lemma = prove
   (`!p x y. cauchy_in (qadic_metric p) x /\ cauchy_in (qadic_metric p) y
           ==> cauchy_in (qadic_metric p) (\n. x n + y n)`,
    GEN_TAC THEN REWRITE_TAC[cauchy_in; QADIC_METRIC] THEN
    ONCE_REWRITE_TAC[GSYM COND_RATOR] THEN REWRITE_TAC[ETA_AX] THEN
    ONCE_REWRITE_TAC[GSYM COND_RAND] THEN
    ABBREV_TAC `p' = if prime p then p else 2` THEN
    SUBGOAL_THEN `prime p'` MP_TAC THENL [ASM_MESON_TAC[PRIME_2]; ALL_TAC] THEN
    SPEC_TAC(`p':num`,`p':num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[IN] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[RATIONAL_CLOSED] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `e:real`)) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `M:num` THEN DISCH_TAC THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN EXISTS_TAC `MAX M N` THEN
    REWRITE_TAC[ARITH_RULE `MAX M N <= n <=> M <= n /\ N <= n`] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ARITH
     `(x + y) - (x' + y'):real = (x - x') + (y - y')`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) QNORM_ULTRA o lhand o snd) THEN
    ASM_SIMP_TAC[RATIONAL_CLOSED] THEN MATCH_MP_TAC(REAL_ARITH
     `a < e /\ b < e ==> x <= max a b ==> x < e`) THEN
    ASM_SIMP_TAC[]) in
  let padic_addition_exists = prove
   (`!p. ?plus.
        continuous_map
         (prod_topology (padic_topology p) (padic_topology p),padic_topology p)
         (\(a,b). plus a b) /\
        !x y. rational x /\ rational y
              ==> plus (padic_of_rational x) (padic_of_rational y) =
                  padic_of_rational (x + y)`,
    GEN_TAC THEN
    MP_TAC(ISPECL
     [`prod_metric (padic_metric p) (padic_metric p)`;
      `padic_metric p`;
      `\(x,y). padic_of_rational
           (rational_of_padic x + rational_of_padic y)`;
      `prational CROSS prational`]
     CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
    REWRITE_TAC[MTOPOLOGY_PROD_METRIC; CLOSURE_OF_CROSS] THEN
    REWRITE_TAC[GSYM padic_topology; CLOSURE_OF_PRATIONAL] THEN
    REWRITE_TAC[CROSS_UNIV; SUBTOPOLOGY_UNIV] THEN
    REWRITE_TAC[MCOMPLETE_PADIC_METRIC; SUBMETRIC_PROD_METRIC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[cauchy_continuous_map; FORALL_PAIR_FUN_THM] THEN
      REWRITE_TAC[CAUCHY_IN_PROD_METRIC; o_DEF; ETA_AX] THEN
      REWRITE_TAC[CAUCHY_IN_SUBMETRIC; TAUT
       `(p /\ p') /\ q /\ q' ==> r <=> p ==> q ==> p' /\ q' ==> r`] THEN
      REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL; IN_IMAGE] THEN
      REWRITE_TAC[SKOLEM_THM; RIGHT_FORALL_IMP_THM; FORALL_AND_THM] THEN
      ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
      REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[IMP_CONJ; FORALL_UNWIND_THM2] THEN
      X_GEN_TAC `x:num->real` THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[FORALL_UNWIND_THM2] THEN
      X_GEN_TAC `y:num->real` THEN DISCH_TAC THEN
      REWRITE_TAC[cauchy_in; MSPACE_PADIC_METRIC; IN_UNIV] THEN
      ASM_SIMP_TAC[rational_of_padic; GSYM pdist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      ASM_SIMP_TAC[PDIST_ALT; RATIONAL_CLOSED] THEN
      MP_TAC(ISPECL [`p:num`; `x:num->real`; `y:num->real`] lemma) THEN
      ASM_REWRITE_TAC[cauchy_in; QADIC_METRIC] THEN
      ASM_CASES_TAC `prime p` THEN ASM_SIMP_TAC[IN; RATIONAL_CLOSED];
      REWRITE_TAC[EXISTS_CURRY; FORALL_PAIR_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `plus:padic->padic->padic` THEN
      REWRITE_TAC[IN_CROSS] THEN
      REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL; FORALL_IN_IMAGE_2] THEN
      SIMP_TAC[rational_of_padic] THEN SIMP_TAC[IN]]) in
  let th = new_specification ["padic_add"]
    (REWRITE_RULE[SKOLEM_THM] padic_addition_exists) in
  CONJ_PAIR(REWRITE_RULE[FORALL_AND_THM] th);;

let CONTINUOUS_MAP_PADIC_MULTIPLICATION,PADIC_MUL_OF_RATIONAL =
  let sublemma = prove
   (`!p x. prime p /\ cauchy_in (qadic_metric p) x
           ==> ?b. &0 < b /\ !n. qnorm p (x n) <= b`,
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP CAUCHY_IN_IMP_MBOUNDED) THEN
    REWRITE_TAC[MBOUNDED_POS; mcball; QADIC_METRIC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `b:real`] THEN
    ASM_REWRITE_TAC[IN_UNIV; IN_ELIM_THM; FORALL_AND_THM] THEN
    REWRITE_TAC[IN] THEN STRIP_TAC THEN EXISTS_TAC `qnorm p c + b` THEN
    ASM_SIMP_TAC[REAL_LET_ADD; QNORM_POS_LE] THEN X_GEN_TAC `n:num` THEN
    SUBST1_TAC(REAL_ARITH `(x:num->real) n = --(c - x n) + c`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) QNORM_TRIANGLE o lhand o snd) THEN
    ASM_SIMP_TAC[RATIONAL_CLOSED; QNORM_NEG] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN REAL_ARITH_TAC) in
  let lemma = prove
   (`!p x y. cauchy_in (qadic_metric p) x /\ cauchy_in (qadic_metric p) y
           ==> cauchy_in (qadic_metric p) (\n. x n * y n)`,
    REPEAT GEN_TAC THEN
    ABBREV_TAC `p' = if prime p then p else 2` THEN
    SUBGOAL_THEN `qadic_metric p = qadic_metric p'` SUBST1_TAC THENL
     [EXPAND_TAC "p'" THEN REWRITE_TAC[qadic_metric] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[PRIME_2];
      SUBGOAL_THEN `prime p'` MP_TAC THENL
       [ASM_MESON_TAC[PRIME_2]; POP_ASSUM_LIST(K ALL_TAC)] THEN
      SPEC_TAC(`p':num`,`p:num`)] THEN
    GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?B. &0 < B /\
          (!n:num. qnorm p (x n) <= B) /\
          (!n:num. qnorm p (y n) <= B)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(SPEC `p:num` sublemma) THEN DISCH_THEN(fun th ->
        MP_TAC(SPEC `y:num->real` th) THEN MP_TAC(SPEC `x:num->real` th)) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `B:real` THEN STRIP_TAC THEN
      X_GEN_TAC `C:real` THEN STRIP_TAC THEN
      EXISTS_TAC `max B C:real` THEN
      ASM_REWRITE_TAC[REAL_LT_MAX; REAL_LE_MAX];
      FIRST_X_ASSUM(CONJUNCTS_THEN MP_TAC)] THEN
    ASM_SIMP_TAC[cauchy_in; QADIC_METRIC; IN; RATIONAL_CLOSED; IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &3 / B`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `M:num`) (X_CHOOSE_TAC `N:num`)) THEN
    EXISTS_TAC `MAX M N` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[ARITH_RULE `MAX M N <= n <=> M <= n /\ N <= n`] THEN
    STRIP_TAC THEN SUBST1_TAC(REAL_ARITH
     `(x:num->real) m * y m - x n * y n =
      x m * (y m - y n) + y n * (x m - x n)`) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) QNORM_TRIANGLE o lhand o snd)  THEN
    ASM_SIMP_TAC[RATIONAL_CLOSED; QNORM_MUL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
    TRANS_TAC REAL_LET_TRANS `B * e / &3 / B + B * e / &3 / B` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[QNORM_POS_LE; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC]) in
  let padic_multiplication_exists = prove
   (`!p. ?plus.
        continuous_map
         (prod_topology (padic_topology p) (padic_topology p),padic_topology p)
         (\(a,b). plus a b) /\
        !x y. rational x /\ rational y
              ==> plus (padic_of_rational x) (padic_of_rational y) =
                  padic_of_rational (x * y)`,
    GEN_TAC THEN
    MP_TAC(ISPECL
     [`prod_metric (padic_metric p) (padic_metric p)`;
      `padic_metric p`;
      `\(x,y). padic_of_rational
           (rational_of_padic x * rational_of_padic y)`;
      `prational CROSS prational`]
     CAUCHY_CONTINUOUS_MAP_EXTENDS_TO_CONTINUOUS_CLOSURE_OF) THEN
    REWRITE_TAC[MTOPOLOGY_PROD_METRIC; CLOSURE_OF_CROSS] THEN
    REWRITE_TAC[GSYM padic_topology; CLOSURE_OF_PRATIONAL] THEN
    REWRITE_TAC[CROSS_UNIV; SUBTOPOLOGY_UNIV] THEN
    REWRITE_TAC[MCOMPLETE_PADIC_METRIC; SUBMETRIC_PROD_METRIC] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[cauchy_continuous_map; FORALL_PAIR_FUN_THM] THEN
      REWRITE_TAC[CAUCHY_IN_PROD_METRIC; o_DEF; ETA_AX] THEN
      REWRITE_TAC[CAUCHY_IN_SUBMETRIC; TAUT
       `(p /\ p') /\ q /\ q' ==> r <=> p ==> q ==> p' /\ q' ==> r`] THEN
      REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL; IN_IMAGE] THEN
      REWRITE_TAC[SKOLEM_THM; RIGHT_FORALL_IMP_THM; FORALL_AND_THM] THEN
      ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
      REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[IMP_CONJ; FORALL_UNWIND_THM2] THEN
      X_GEN_TAC `x:num->real` THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
      REWRITE_TAC[FORALL_UNWIND_THM2] THEN
      X_GEN_TAC `y:num->real` THEN DISCH_TAC THEN
      REWRITE_TAC[cauchy_in; MSPACE_PADIC_METRIC; IN_UNIV] THEN
      ASM_SIMP_TAC[rational_of_padic; GSYM pdist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN]) THEN
      ASM_SIMP_TAC[PDIST_ALT; RATIONAL_CLOSED] THEN
      MP_TAC(ISPECL [`p:num`; `x:num->real`; `y:num->real`] lemma) THEN
      ASM_REWRITE_TAC[cauchy_in; QADIC_METRIC] THEN
      ASM_CASES_TAC `prime p` THEN ASM_SIMP_TAC[IN; RATIONAL_CLOSED];
      REWRITE_TAC[EXISTS_CURRY; FORALL_PAIR_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `plus:padic->padic->padic` THEN
      REWRITE_TAC[IN_CROSS] THEN
      REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL; FORALL_IN_IMAGE_2] THEN
      SIMP_TAC[rational_of_padic] THEN SIMP_TAC[IN]]) in
  let th = new_specification ["padic_mul"]
    (REWRITE_RULE[SKOLEM_THM] padic_multiplication_exists) in
  CONJ_PAIR(REWRITE_RULE[FORALL_AND_THM] th);;

let padic_of_num = new_definition
 `padic_of_num n = padic_of_rational(&n)`;;

let padic_neg = new_definition
 `padic_neg p x = padic_mul p (padic_of_rational(-- &1)) x`;;

let padic_sub = new_definition
 `padic_sub p x y = padic_add p x (padic_neg p y)`;;

let PADIC_NEG_OF_RATIONAL = prove
 (`!p x. rational x
         ==> padic_neg p (padic_of_rational x) =
             padic_of_rational (--x)`,
  SIMP_TAC[padic_neg; PADIC_MUL_OF_RATIONAL; RATIONAL_CLOSED] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]);;

let PADIC_SUB_OF_RATIONAL = prove
 (`!p x y.
         rational x /\ rational y
         ==> padic_sub p (padic_of_rational x) (padic_of_rational y) =
             padic_of_rational (x - y)`,
  SIMP_TAC[padic_sub; PADIC_NEG_OF_RATIONAL; PADIC_ADD_OF_RATIONAL;
           RATIONAL_CLOSED; real_sub]);;

(* ------------------------------------------------------------------------- *)
(* Continuity lemmas.                                                        *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_MAP_PADIC_ADD = prove
 (`!p top f g:A->padic.
      continuous_map (top,padic_topology p) f /\
      continuous_map (top,padic_topology p) g
      ==> continuous_map (top,padic_topology p) (\x. padic_add p (f x) (g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. padic_add p (f x) (g x)) =
    (\(x,y). padic_add p x y) o (\a. (f:A->padic) a,g a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (padic_topology p) (padic_topology p)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PADIC_ADDITION] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let CONTINUOUS_MAP_PADIC_MUL = prove
 (`!p top f g:A->padic.
      continuous_map (top,padic_topology p) f /\
      continuous_map (top,padic_topology p) g
      ==> continuous_map (top,padic_topology p) (\x. padic_mul p (f x) (g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. padic_mul p (f x) (g x)) =
    (\(x,y). padic_mul p x y) o (\a. (f:A->padic) a,g a)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FORALL_PAIR_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
  EXISTS_TAC `prod_topology (padic_topology p) (padic_topology p)` THEN
  REWRITE_TAC[CONTINUOUS_MAP_PADIC_MULTIPLICATION] THEN
  REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let CONTINUOUS_MAP_PADIC_NEG = prove
 (`!p top f:A->padic.
        continuous_map (top,padic_topology p) f
        ==> continuous_map (top,padic_topology p) (\x. padic_neg p (f x))`,
  SIMP_TAC[padic_neg; CONTINUOUS_MAP_PADIC_MUL; CONTINUOUS_MAP_CONST;
           TOPSPACE_PADIC_TOPOLOGY; IN_UNIV]);;

let CONTINUOUS_MAP_PADIC_SUB = prove
 (`!p top f g:A->padic.
      continuous_map (top,padic_topology p) f /\
      continuous_map (top,padic_topology p) g
      ==> continuous_map (top,padic_topology p) (\x. padic_sub p (f x) (g x))`,
  SIMP_TAC[padic_sub; CONTINUOUS_MAP_PADIC_ADD; CONTINUOUS_MAP_PADIC_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Bootstrap some basic field properties by continuity.                      *)
(* ------------------------------------------------------------------------- *)

let FORALL_IN_PADIC_CLOSURE_OF = prove
 (`!p top s f g:A->padic.
        (continuous_map (top,padic_topology p) f /\
         continuous_map (top,padic_topology p) g) /\
        (!x. x IN s ==> f x = g x)
        ==> (!x. x IN top closure_of s ==> f x = g x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_OF_EQ THEN
  EXISTS_TAC `padic_topology p` THEN
  ASM_REWRITE_TAC[HAUSDORFF_SPACE_PADIC_TOPOLOGY]);;

let SIMPLE_PADIC_ARITH_TAC =
  TRY(X_GEN_TAC `p:num`) THEN
  REWRITE_TAC[FORALL_UNPAIR_THM] THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
  REWRITE_TAC[GSYM CROSS_UNIV] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_PRATIONAL] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_CROSS] THEN
  MATCH_MP_TAC FORALL_IN_PADIC_CLOSURE_OF THEN EXISTS_TAC `p:num` THEN
  CONJ_TAC THENL
   [CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC CONTINUOUS_MAP_PADIC_ADD THEN CONJ_TAC) ORELSE
           (MATCH_MP_TAC CONTINUOUS_MAP_PADIC_SUB THEN CONJ_TAC) ORELSE
           (MATCH_MP_TAC CONTINUOUS_MAP_PADIC_MUL THEN CONJ_TAC) ORELSE
           (MATCH_MP_TAC CONTINUOUS_MAP_PADIC_NEG)) THEN
    REPEAT(GEN_REWRITE_TAC I
             [CONTINUOUS_MAP_OF_FST; CONTINUOUS_MAP_OF_SND] THEN
           DISJ2_TAC) THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND;
                CONTINUOUS_MAP_ID; CONTINUOUS_MAP_CONST] THEN
    REWRITE_TAC[TOPSPACE_PADIC_TOPOLOGY; IN_UNIV];
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN; RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
    SIMP_TAC[padic_of_num; PADIC_ADD_OF_RATIONAL; PADIC_SUB_OF_RATIONAL;
      PADIC_NEG_OF_RATIONAL; PADIC_MUL_OF_RATIONAL; RATIONAL_CLOSED] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RING];;

let PADIC_ADD_SYM = prove
 (`!p x y. padic_add p x y = padic_add p y x`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_ADD_ASSOC = prove
 (`!p x y z. padic_add p x (padic_add p y z) =
             padic_add p (padic_add p x y) z`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_ADD_LID = prove
 (`!p x. padic_add p (padic_of_num 0) x = x`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_ADD_LINV = prove
 (`!p x. padic_add p (padic_neg p x) x = padic_of_num 0`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_MUL_SYM = prove
 (`!p x y. padic_mul p x y = padic_mul p y x`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_MUL_ASSOC = prove
 (`!p x y z. padic_mul p x (padic_mul p y z) =
             padic_mul p (padic_mul p x y) z`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_MUL_LID = prove
 (`!p x. padic_mul p (padic_of_num 1) x = x`,
  SIMPLE_PADIC_ARITH_TAC);;

let PADIC_ADD_LDISTRIB = prove
 (`!p x y z. padic_mul p x (padic_add p y z) =
             padic_add p (padic_mul p x y)  (padic_mul p x z)`,
  SIMPLE_PADIC_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Also define the padic norm explicitly. Our connection to qnorm is a bit   *)
(* roundabout because we are using completion machinery that is specifically *)
(* about metric spaces. So we go qnorm -> qdist -> pdist -> pnorm.           *)
(* ------------------------------------------------------------------------- *)

let pnorm = new_definition
 `pnorm p x = pdist p (padic_of_num 0,x)`;;

let PDIST_PNORM = prove
 (`!p x y. pdist p (x,y) = pnorm p (padic_sub p x y)`,
  REWRITE_TAC[pnorm] THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[FORALL_UNPAIR_THM] THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
  REWRITE_TAC[GSYM CROSS_UNIV] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_PRATIONAL] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_CROSS] THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_OF_EQ THEN
  EXISTS_TAC `euclideanreal` THEN
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEANREAL; CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[pdist] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_MDIST_ALT THEN
    REWRITE_TAC[GSYM padic_topology; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_PADIC_TOPOLOGY; IN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_PADIC_SUB THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND];
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; pdist] THEN
    REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL; FORALL_IN_IMAGE_2] THEN
    SIMP_TAC[IN; padic_metric; padic_of_num; RATIONAL_CLOSED;
             PADIC_SUB_OF_RATIONAL] THEN
    REWRITE_TAC[REAL_SUB_LZERO; QNORM_NEG]]);;

let PNORM_0 = prove
 (`!p. pnorm p (padic_of_num 0) = &0`,
  REWRITE_TAC[pnorm; PDIST_REFL]);;

let PNORM_RATIONAL = prove
 (`!p x. rational x
         ==> pnorm p (padic_of_rational x) =
             qnorm (if prime p then p else 2) x`,
  REWRITE_TAC[pnorm; pdist; padic_of_num] THEN
  SIMP_TAC[padic_metric; RATIONAL_CLOSED] THEN
  REWRITE_TAC[REAL_SUB_LZERO; QNORM_NEG]);;

let PNORM_1 = prove
 (`!p. pnorm p (padic_of_num 1) = &1`,
  SIMP_TAC[PNORM_RATIONAL; padic_of_num; RATIONAL_CLOSED] THEN
  REWRITE_TAC[QNORM_1] THEN MESON_TAC[PRIME_2]);;

let PNORM_NEG = prove
 (`!p x. pnorm p (padic_neg p x) = pnorm p x`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [pnorm] THEN REWRITE_TAC[PDIST_PNORM] THEN
  AP_TERM_TAC THEN SPEC_TAC(`x:padic`,`x:padic`) THEN
  SIMPLE_PADIC_ARITH_TAC);;

let PNORM_POS_LE = prove
 (`!p x. &0 <= pnorm p x`,
  REWRITE_TAC[pnorm; PDIST_POS_LE]);;

let PNORM_0 = prove
 (`!p x. pnorm p (padic_of_num 0) = &0`,
  REWRITE_TAC[pnorm; PDIST_REFL]);;

let PNORM_EQ_0 = prove
 (`!p x. pnorm p x = &0 <=> x = padic_of_num 0`,
  REWRITE_TAC[pnorm; PDIST_EQ_0] THEN MESON_TAC[]);;

let PNORM_POS_LT = prove
 (`!p x. &0 < pnorm p x <=> ~(x = padic_of_num 0)`,
  REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
  REWRITE_TAC[PNORM_POS_LE; PNORM_EQ_0]);;

let PNORM_ULTRA = prove
 (`!p x y. pnorm p (padic_add p x y) <= max (pnorm p x) (pnorm p y)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC REAL_LE_TRANS `pnorm p (padic_sub p x (padic_neg p y))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`y:padic`; `x:padic`] THEN
    SIMPLE_PADIC_ARITH_TAC;
    REWRITE_TAC[GSYM PDIST_PNORM] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM PNORM_NEG] THEN
    REWRITE_TAC[pnorm] THEN MP_TAC(ISPECL
     [`p:num`; `x:padic`; `padic_of_num 0`; `padic_neg p y`]
        PDIST_ULTRA) THEN
    REWRITE_TAC[PDIST_SYM]]);;

let PNORM_TRIANGLE = prove
 (`!p x y. pnorm p (padic_add p x y) <= pnorm p x + pnorm p y`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `x <= max y z /\ &0 <= y /\ &0 <= z ==> x <= y + z`) THEN
  REWRITE_TAC[PNORM_ULTRA; PNORM_POS_LE]);;

let PNORM_MUL = prove
 (`!p x y. pnorm p (padic_mul p x y) = pnorm p x * pnorm p y`,
  REWRITE_TAC[pnorm] THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[FORALL_UNPAIR_THM] THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. P x) <=> (!x. x IN UNIV ==> P x)`] THEN
  REWRITE_TAC[GSYM CROSS_UNIV] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_PRATIONAL] THEN
  REWRITE_TAC[GSYM CLOSURE_OF_CROSS] THEN
  MATCH_MP_TAC FORALL_IN_CLOSURE_OF_EQ THEN
  EXISTS_TAC `euclideanreal` THEN
  REWRITE_TAC[HAUSDORFF_SPACE_EUCLIDEANREAL; CONJ_ASSOC] THEN CONJ_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[pdist] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_MAP_REAL_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC CONTINUOUS_MAP_MDIST_ALT THEN
    REWRITE_TAC[CONTINUOUS_MAP_PAIRWISE; o_DEF] THEN
    REWRITE_TAC[GSYM padic_topology; CONTINUOUS_MAP_ID] THEN
    REWRITE_TAC[CONTINUOUS_MAP_CONST; TOPSPACE_PADIC_TOPOLOGY; IN_UNIV] THEN
    TRY(MATCH_MP_TAC CONTINUOUS_MAP_PADIC_MUL) THEN
    REWRITE_TAC[CONTINUOUS_MAP_FST; CONTINUOUS_MAP_SND; ETA_AX];
    REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; pdist] THEN
    REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL; FORALL_IN_IMAGE_2] THEN
    SIMP_TAC[IN; padic_metric; padic_of_num; RATIONAL_CLOSED;
             PADIC_MUL_OF_RATIONAL] THEN
    REWRITE_TAC[REAL_SUB_LZERO; QNORM_NEG] THEN
    SIMP_TAC[QNORM_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* Deduce the existence of multiplicative inverses.                          *)
(* ------------------------------------------------------------------------- *)

let PADIC_ENTIRE = prove
 (`!p x y. padic_mul p x y = padic_of_num 0 <=>
          x = padic_of_num 0 \/ y = padic_of_num 0`,
  REWRITE_TAC[GSYM PNORM_EQ_0; PNORM_MUL; REAL_ENTIRE]);;

let padic_inv = new_definition
 `padic_inv p x = if x = padic_of_num 0 then padic_of_num 0
                  else @y. padic_mul p x y = padic_of_num 1`;;

let PADIC_INV_0 = prove
 (`!p. padic_inv p (padic_of_num 0) = padic_of_num 0`,
  REWRITE_TAC[padic_inv]);;

let PADIC_MUL_RINV = prove
 (`!p x. ~(x = padic_of_num 0)
         ==> padic_mul p x (padic_inv p x) = padic_of_num 1`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[padic_inv] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(ISPECL [`padic_metric p`; `prational`] CLOSURE_OF_SEQUENTIALLY) THEN
  REWRITE_TAC[CLOSURE_OF_PRATIONAL; MSPACE_PADIC_METRIC;
              GSYM padic_topology; INTER_UNIV; IN_UNIV] THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_ELIM_THM] THEN
  REWRITE_TAC[GSYM IMAGE_PADIC_OF_RATIONAL_RATIONAL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:padic`) THEN REWRITE_TAC[IN_IMAGE] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  ONCE_REWRITE_TAC[GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = pnorm p x / &2` THEN
  SUBGOAL_THEN `&0 < e` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN REWRITE_TAC[REAL_HALF; PNORM_POS_LT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `eventually (\n. ~(q n = &0) /\
                    e <= pnorm p (padic_of_rational(q n)))
               sequentially`
  ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIMIT_METRIC] o
      REWRITE_RULE[padic_topology]) THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT
     `(q ==> ~r) /\ (p ==> r) ==> p ==> ~q /\ r`) THEN
    SIMP_TAC[GSYM padic_of_num; PNORM_0] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE; pnorm; pdist] THEN MATCH_MP_TAC(METRIC_ARITH
     `mdist m (z:padic,x) / &2 = e /\ z IN mspace m /\ x IN mspace m
      ==> q IN mspace m /\ mdist m (q,x) < e / &2
          ==> e <= mdist m (z,q)`) THEN
    REWRITE_TAC[MSPACE_PADIC_METRIC; IN_UNIV; GSYM pdist; GSYM pnorm] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `p:num` MCOMPLETE_PADIC_METRIC) THEN REWRITE_TAC[mcomplete] THEN
  DISCH_THEN(MP_TAC o SPEC `padic_of_rational o inv o (q:num->real)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[cauchy_in; MSPACE_PADIC_METRIC; IN_UNIV] THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o
      MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] CONVERGENT_IMP_CAUCHY_IN) o
      REWRITE_RULE[padic_topology]) THEN
    REWRITE_TAC[cauchy_in; MSPACE_PADIC_METRIC; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `(d:real) * e pow 2`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_POW_LT] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVENTUALLY_SEQUENTIALLY]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
    EXISTS_TAC `MAX M N` THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[ARITH_RULE `MAX M N <= n <=> M <= n /\ N <= n`] THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM; GSYM pdist; PDIST_PNORM] THEN
    ASM_SIMP_TAC[PADIC_SUB_OF_RATIONAL; RATIONAL_CLOSED] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = &0) /\ ~(y = &0)
      ==> inv x - inv y = --(x - y) * inv(x) * inv(y)`] THEN
    ASM_SIMP_TAC[GSYM PADIC_MUL_OF_RATIONAL; RATIONAL_CLOSED] THEN
    REWRITE_TAC[PNORM_MUL] THEN
    ASM_SIMP_TAC[PNORM_RATIONAL; RATIONAL_CLOSED; QNORM_INV] THEN
    ASM_SIMP_TAC[GSYM PNORM_RATIONAL] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    SUBGOAL_THEN `!x. e <= x ==> &0 < x` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[GSYM PNORM_RATIONAL; PNORM_NEG; RATIONAL_CLOSED;
                 GSYM PADIC_NEG_OF_RATIONAL] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[GSYM pdist; PDIST_PNORM] THEN
    ASM_SIMP_TAC[PADIC_SUB_OF_RATIONAL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LTE_TRANS) THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_POW_2; REAL_LE_LMUL_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_MUL2; REAL_LT_IMP_LE];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:padic` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIMIT_METRIC_UNIQUE) THEN
    EXISTS_TAC `padic_metric p` THEN
    EXISTS_TAC `(\(x,y). padic_mul p x y) o
           (\n:num. padic_of_rational (q n),padic_of_rational (inv(q n)))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `padic_mul p x y = (\(x,y). padic_mul p x y) (x,y)`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_MAP_LIMIT THEN
      EXISTS_TAC `prod_topology (padic_topology p) (padic_topology p)` THEN
      SIMP_TAC[CONTINUOUS_MAP_PADIC_MULTIPLICATION; GSYM padic_topology] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[o_DEF; GSYM padic_topology]) THEN
      ASM_REWRITE_TAC[LIMIT_PAIRWISE; o_DEF];
      MATCH_MP_TAC LIMIT_EVENTUALLY THEN
      REWRITE_TAC[o_DEF; GSYM padic_topology; TOPSPACE_PADIC_TOPOLOGY] THEN
      ASM_SIMP_TAC[IN_UNIV; PADIC_MUL_OF_RATIONAL; RATIONAL_CLOSED] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        EVENTUALLY_MONO)) THEN
      X_GEN_TAC `n:num` THEN SIMP_TAC[REAL_MUL_RINV; padic_of_num]]]);;

let PADIC_MUL_LINV = prove
 (`!p x. ~(x = padic_of_num 0)
         ==> padic_mul p (padic_inv p x) x = padic_of_num 1`,
  ONCE_REWRITE_TAC[PADIC_MUL_SYM] THEN REWRITE_TAC[PADIC_MUL_RINV]);;

let PNORM_INV = prove
 (`!p x. pnorm p (padic_inv p x) = inv(pnorm p x)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = padic_of_num 0` THEN
  ASM_REWRITE_TAC[REAL_INV_0; PADIC_INV_0; PNORM_0] THEN
  MATCH_MP_TAC(REAL_FIELD `x * y = &1 ==> x = inv y`) THEN
  ASM_SIMP_TAC[GSYM PNORM_MUL; PADIC_MUL_LINV; PNORM_1]);;
