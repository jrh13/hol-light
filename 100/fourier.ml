(* ========================================================================= *)
(* Square integrable functions R->R and basics of Fourier series.            *)
(* ========================================================================= *)

needs "Multivariate/lpspaces.ml";;

(* ------------------------------------------------------------------------- *)
(* Somewhat general lemmas, but perhaps not enough to be installed.          *)
(* ------------------------------------------------------------------------- *)

let SUM_NUMBERS = prove
 (`!n. sum(0..n) (\r. &r) = (&n * (&n + &1)) / &2`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; GSYM REAL_OF_NUM_SUC] THEN
  REAL_ARITH_TAC);;

let REAL_INTEGRABLE_REFLECT_AND_ADD = prove
 (`!f a. f real_integrable_on real_interval[--a,a]
         ==> f real_integrable_on real_interval[&0,a] /\
             (\x. f(--x)) real_integrable_on real_interval[&0,a] /\
             (\x. f x + f(--x)) real_integrable_on real_interval[&0,a]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG; ETA_AX];
    SIMP_TAC[REAL_INTEGRABLE_ADD]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] REAL_INTEGRABLE_SUBINTERVAL)) THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN REAL_ARITH_TAC);;

let REAL_INTEGRAL_REFLECT_AND_ADD = prove
 (`!f a. f real_integrable_on real_interval[--a,a]
         ==> real_integral (real_interval[--a,a]) f =
             real_integral (real_interval[&0,a])
                           (\x. f x + f(--x))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= a` THENL
   [MP_TAC(SPECL [`f:real->real`; `--a:real`; `a:real`; `&0:real`]
        REAL_INTEGRAL_COMBINE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_REFLECT_AND_ADD] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG; ETA_AX; REAL_NEG_0; REAL_ADD_AC];
    ASM_SIMP_TAC[REAL_INTEGRAL_NULL;
                 REAL_ARITH `~(&0 <= a) ==> a <= --a /\ a <= &0`]]);;

(* ------------------------------------------------------------------------- *)
(* Square-integrable real->real functions.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("square_integrable_on",(12,"right"));;

let square_integrable_on = new_definition
 `f square_integrable_on s <=>
     f real_measurable_on s /\ (\x. f(x) pow 2) real_integrable_on s`;;

let SQUARE_INTEGRABLE_IMP_MEASURABLE = prove
 (`!f s. f square_integrable_on s ==> f real_measurable_on s`,
  SIMP_TAC[square_integrable_on]);;

let SQUARE_INTEGRABLE_LSPACE = prove
 (`!f s. f square_integrable_on s <=>
         (lift o f o drop) IN lspace (IMAGE lift s) (&2)`,
  REWRITE_TAC[square_integrable_on; lspace; IN_ELIM_THM] THEN
  REWRITE_TAC[real_measurable_on; REAL_INTEGRABLE_ON; RPOW_POW] THEN
  REWRITE_TAC[o_THM; NORM_REAL; GSYM drop; LIFT_DROP] THEN
  REWRITE_TAC[REAL_POW2_ABS; o_DEF]);;

let SQUARE_INTEGRABLE_0 = prove
 (`!s. (\x. &0) square_integrable_on s`,
  REWRITE_TAC[square_integrable_on; REAL_MEASURABLE_ON_0] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_INTEGRABLE_0]);;

let SQUARE_INTEGRABLE_NEG_EQ = prove
 (`!f s. (\x. --(f x)) square_integrable_on s <=> f square_integrable_on s`,
  REWRITE_TAC[square_integrable_on; REAL_MEASURABLE_ON_NEG_EQ;
               REAL_POW_NEG; ARITH]);;

let SQUARE_INTEGRABLE_NEG = prove
 (`!f s. f square_integrable_on s ==> (\x. --(f x)) square_integrable_on s`,
  REWRITE_TAC[SQUARE_INTEGRABLE_NEG_EQ]);;

let SQUARE_INTEGRABLE_LMUL = prove
 (`!f s c. f square_integrable_on s ==> (\x. c * f(x)) square_integrable_on s`,
  SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_LMUL] THEN
  SIMP_TAC[REAL_POW_MUL; REAL_INTEGRABLE_LMUL]);;

let SQUARE_INTEGRABLE_RMUL = prove
 (`!f s c. f square_integrable_on s ==> (\x. f(x) * c) square_integrable_on s`,
  SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_RMUL] THEN
  SIMP_TAC[REAL_POW_MUL; REAL_INTEGRABLE_RMUL]);;

let SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) * g(x)) absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE] THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_ON_MUL; SQUARE_INTEGRABLE_IMP_MEASURABLE] THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`; `&2`;
                 `lift o f o drop`; `lift o g o drop`]
        LSPACE_INTEGRABLE_PRODUCT) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[o_DEF; NORM_REAL; GSYM drop; LIFT_DROP; REAL_ABS_MUL]);;

let SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) * g(x)) real_integrable_on s`,
  SIMP_TAC[SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_PRODUCT;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;

let SQUARE_INTEGRABLE_ADD = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) + g(x)) square_integrable_on s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_ADD;
               SQUARE_INTEGRABLE_IMP_MEASURABLE] THEN
  SIMP_TAC[REAL_ARITH `(x + y) pow 2 = (x pow 2 + y pow 2) + &2 * x * y`] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               REAL_INTEGRABLE_LMUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[square_integrable_on]) THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_ADD]);;

let SQUARE_INTEGRABLE_SUB = prove
 (`!f g s. f square_integrable_on s /\ g square_integrable_on s
           ==> (\x. f(x) - g(x)) square_integrable_on s`,
  SIMP_TAC[real_sub; SQUARE_INTEGRABLE_ADD; SQUARE_INTEGRABLE_NEG_EQ]);;

let SQUARE_INTEGRABLE_ABS = prove
 (`!f g s. f square_integrable_on s ==> (\x. abs(f x)) square_integrable_on s`,
  SIMP_TAC[square_integrable_on; REAL_MEASURABLE_ON_ABS; REAL_POW2_ABS]);;

let SQUARE_INTEGRABLE_SUM = prove
 (`!f s t. FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s)
           ==> (\x. sum t (\i. f i x)) square_integrable_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SQUARE_INTEGRABLE_0; IN_INSERT; SQUARE_INTEGRABLE_ADD; ETA_AX;
           SUM_CLAUSES]);;

let REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE = prove
 (`!f a b. f real_continuous_on real_interval[a,b]
           ==> f square_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[square_integrable_on] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN ASM_REWRITE_TAC[]]);;

let SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = prove
 (`!f s. f square_integrable_on s /\ real_measurable s
         ==> f absolutely_real_integrable_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  REWRITE_TAC[GSYM LSPACE_1] THEN
  MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `&2` THEN
  ASM_REWRITE_TAC[GSYM REAL_MEASURABLE_MEASURABLE;
                  GSYM SQUARE_INTEGRABLE_LSPACE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let SQUARE_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f s. f square_integrable_on s /\ real_measurable s
         ==> f real_integrable_on s`,
  SIMP_TAC[SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;

(* ------------------------------------------------------------------------- *)
(* The norm and inner product in L2.                                         *)
(* ------------------------------------------------------------------------- *)

let l2product = new_definition
 `l2product s f g = real_integral s (\x. f(x) * g(x))`;;

let l2norm = new_definition
 `l2norm s f = sqrt(l2product s f f)`;;

let L2NORM_LNORM = prove
 (`!f s. f square_integrable_on s
         ==> l2norm s f = lnorm (IMAGE lift s) (&2) (lift o f o drop)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[l2norm; lnorm; l2product] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[square_integrable_on]) THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; REAL_INTEGRAL] THEN
  REWRITE_TAC[NORM_REAL; o_DEF; GSYM drop; LIFT_DROP; RPOW_POW] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(GSYM RPOW_SQRT) THEN
  MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; REAL_LE_POW_2] THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[REAL_INTEGRABLE_ON] o CONJUNCT2) THEN
  REWRITE_TAC[o_DEF]);;

let L2PRODUCT_SYM = prove
 (`!s f g. l2product s f g = l2product s g f`,
  REWRITE_TAC[l2product; REAL_MUL_SYM]);;

let L2PRODUCT_POS_LE = prove
 (`!s f. f square_integrable_on s ==> &0 <= l2product s f f`,
  REWRITE_TAC[square_integrable_on; l2product] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_POS THEN
  REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REWRITE_TAC[GSYM REAL_POW_2]);;

let L2NORM_POW_2 = prove
 (`!s f. f square_integrable_on s ==> (l2norm s f) pow 2 = l2product s f f`,
  SIMP_TAC[l2norm; SQRT_POW_2; L2PRODUCT_POS_LE]);;

let L2NORM_POS_LE = prove
 (`!s f. f square_integrable_on s ==> &0 <= l2norm s f`,
  SIMP_TAC[l2norm; SQRT_POS_LE; L2PRODUCT_POS_LE]);;

let L2NORM_LE = prove
 (`!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f <= l2norm s g <=>
                l2product s f f <= l2product s g g)`,
  SIMP_TAC[SQRT_MONO_LE_EQ; l2norm; SQRT_MONO_LE_EQ; L2PRODUCT_POS_LE]);;

let L2NORM_EQ = prove
 (`!s f g. f square_integrable_on s /\ g square_integrable_on s
           ==> (l2norm s f = l2norm s g <=>
                l2product s f f = l2product s g g)`,
  SIMP_TAC[GSYM REAL_LE_ANTISYM; L2NORM_LE]);;

let SCHWARTZ_INEQUALITY_STRONG = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s (\x. abs(f x)) (\x. abs(g x))
               <= l2norm s f * l2norm s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`; `&2`;
                 `lift o f o drop`; `lift o g o drop`] HOELDER_INEQUALITY) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; GSYM L2NORM_LNORM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  REWRITE_TAC[l2product] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL; SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               SQUARE_INTEGRABLE_ABS] THEN
  REWRITE_TAC[NORM_REAL; o_DEF; GSYM drop; LIFT_DROP; REAL_LE_REFL]);;

let SCHWARTZ_INEQUALITY_ABS = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> abs(l2product s f g) <= l2norm s f * l2norm s g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `l2product s (\x. abs(f x)) (\x. abs(g x))` THEN
  ASM_SIMP_TAC[SCHWARTZ_INEQUALITY_STRONG] THEN REWRITE_TAC[l2product] THEN
  MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT;
               SQUARE_INTEGRABLE_ABS] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_LE_REFL]);;

let SCHWARTZ_INEQUALITY = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2product s f g <= l2norm s f * l2norm s g`,
  MESON_TAC[SCHWARTZ_INEQUALITY_ABS;
            REAL_ARITH `abs x <= a ==> x <= a`]);;

let L2NORM_TRIANGLE = prove
 (`!f g s. f square_integrable_on s /\
           g square_integrable_on s
           ==> l2norm s (\x. f x + g x) <= l2norm s f + l2norm s g`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE lift s`; `&2`;
                 `lift o f o drop`; `lift o g o drop`] LNORM_TRIANGLE) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; L2NORM_LNORM;
               SQUARE_INTEGRABLE_ADD] THEN
  REWRITE_TAC[o_DEF; LIFT_ADD]);;

let L2PRODUCT_LADD = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x + g x) h =
            l2product s f h + l2product s g h`,
  SIMP_TAC[l2product; REAL_ADD_RDISTRIB; REAL_INTEGRAL_ADD;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;

let L2PRODUCT_RADD = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x + h x) =
            l2product s f g + l2product s f h`,
  SIMP_TAC[l2product; REAL_ADD_LDISTRIB; REAL_INTEGRAL_ADD;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;

let L2PRODUCT_LSUB = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s (\x. f x - g x) h =
            l2product s f h - l2product s g h`,
  SIMP_TAC[l2product; REAL_SUB_RDISTRIB; REAL_INTEGRAL_SUB;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;

let L2PRODUCT_RSUB = prove
 (`!s f g h.
        f square_integrable_on s /\
        g square_integrable_on s /\
        h square_integrable_on s
        ==> l2product s f (\x. g x - h x) =
            l2product s f g - l2product s f h`,
  SIMP_TAC[l2product; REAL_SUB_LDISTRIB; REAL_INTEGRAL_SUB;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;

let L2PRODUCT_LZERO = prove
 (`!s f. l2product s (\x. &0) f = &0`,
  REWRITE_TAC[l2product; REAL_MUL_LZERO; REAL_INTEGRAL_0]);;

let L2PRODUCT_RZERO = prove
 (`!s f. l2product s f (\x. &0) = &0`,
  REWRITE_TAC[l2product; REAL_MUL_RZERO; REAL_INTEGRAL_0]);;

let L2PRODUCT_LSUM = prove
 (`!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s (\x. sum t (\i. f i x)) g =
            sum t (\i. l2product s (f i) g)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  ASM_CASES_TAC `g square_integrable_on s` THEN ASM_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[L2PRODUCT_LZERO; SUM_CLAUSES; L2PRODUCT_LADD;
               SQUARE_INTEGRABLE_SUM; ETA_AX; IN_INSERT]);;

let L2PRODUCT_RSUM = prove
 (`!s f g t.
        FINITE t /\ (!i. i IN t ==> (f i) square_integrable_on s) /\
        g square_integrable_on s
        ==> l2product s g (\x. sum t (\i. f i x)) =
            sum t (\i. l2product s g (f i))`,
  ONCE_REWRITE_TAC[L2PRODUCT_SYM] THEN REWRITE_TAC[L2PRODUCT_LSUM]);;

let L2PRODUCT_LMUL = prove
 (`!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s (\x. c * f x) g = c * l2product s f g`,
  SIMP_TAC[l2product; GSYM REAL_MUL_ASSOC; REAL_INTEGRAL_LMUL;
           SQUARE_INTEGRABLE_IMP_INTEGRABLE_PRODUCT]);;

let L2PRODUCT_RMUL = prove
 (`!s c f g.
        f square_integrable_on s /\ g square_integrable_on s
        ==> l2product s f (\x. c * g x) = c * l2product s f g`,
  ONCE_REWRITE_TAC[L2PRODUCT_SYM] THEN SIMP_TAC[L2PRODUCT_LMUL]);;

let L2NORM_LMUL = prove
 (`!f s c. f square_integrable_on s
           ==> l2norm s (\x. c * f(x)) = abs(c) * l2norm s f`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[l2norm; L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_POW_2] THEN
  REWRITE_TAC[SQRT_MUL; POW_2_SQRT_ABS]);;

let L2NORM_RMUL = prove
 (`!f s c. f square_integrable_on s
           ==> l2norm s (\x. f(x) * c) = l2norm s f * abs(c)`,
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[L2NORM_LMUL]);;

let L2NORM_NEG = prove
 (`!f s. f square_integrable_on s ==> l2norm s (\x. --(f x)) = l2norm s f`,
  ONCE_REWRITE_TAC[REAL_ARITH `--x:real = --(&1) * x`] THEN
  SIMP_TAC[L2NORM_LMUL; REAL_ABS_NEG; REAL_ABS_NUM; REAL_MUL_LID]);;

let L2NORM_SUB = prove
 (`!f g s.  f square_integrable_on s /\ g square_integrable_on s
        ==> l2norm s (\x. f x - g x) = l2norm s (\x. g x - f x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_NEG_SUB] THEN
  ASM_SIMP_TAC[L2NORM_NEG; SQUARE_INTEGRABLE_SUB; ETA_AX]);;

let L2_SUMMABLE = prove
 (`!f s t.
     (!i. i IN t ==> (f i) square_integrable_on s) /\
     real_summable t (\i. l2norm s (f i))
     ==> ?g. g square_integrable_on s /\
             ((\n. l2norm s (\x. sum (t INTER (0..n)) (\i. f i x) - g x))
              ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. (lift o f n o drop)`;
                 `&2`; `IMAGE lift s`; `t:num->bool`]
        LSPACE_SUMMABLE) THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
   [UNDISCH_TAC `real_summable t (\i. l2norm s (f i))` THEN
    MATCH_MP_TAC EQ_IMP THEN
    REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `e:real` THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `N:num` THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `n:num` THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[GSYM L2NORM_LNORM; IN_INTER; ETA_AX];
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` MP_TAC) THEN
    SUBGOAL_THEN `g = (lift o (drop o g o lift) o drop)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    ABBREV_TAC `h = drop o g o lift` THEN
    REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
    DISCH_THEN(fun th -> EXISTS_TAC `h:real->real` THEN MP_TAC th) THEN
    ASM_CASES_TAC `h square_integrable_on s` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[o_DEF; GSYM LIFT_SUB; REWRITE_RULE[o_DEF] (GSYM LIFT_SUM);
             FINITE_NUMSEG; FINITE_INTER] THEN
    SUBGOAL_THEN `!f. (\x. lift(f(drop x))) = (lift o f o drop)`
     (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC(GSYM L2NORM_LNORM) THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    ASM_SIMP_TAC[FINITE_INTER; IN_INTER; FINITE_NUMSEG]]);;

let L2_COMPLETE = prove
 (`!f s. (!i. f i square_integrable_on s) /\
         (!e. &0 < e ==> ?N. !m n. m >= N /\ n >= N
                                   ==> l2norm s (\x. f m x - f n x) < e)
         ==> ?g. g square_integrable_on s /\
                 ((\n. l2norm s (\x. f n x - g x)) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n:num. lift o f n o drop`; `&2`; `IMAGE lift s`]
        RIESZ_FISCHER) THEN
  ASM_SIMP_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN ANTS_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` MP_TAC) THEN
    SUBGOAL_THEN `g = (lift o (drop o g o lift) o drop)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_DEF; LIFT_DROP]; ALL_TAC] THEN
    ABBREV_TAC `h = drop o g o lift` THEN
    REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE] THEN
    DISCH_THEN(fun th -> EXISTS_TAC `h:real->real` THEN MP_TAC th) THEN
    ASM_CASES_TAC `h square_integrable_on s` THEN ASM_REWRITE_TAC[]] THEN
  (SUBGOAL_THEN `!f g. (\x. (lift o f o drop) x - (lift o g o drop) x) =
                       (lift o (\y. f y - g y) o drop)`
    (fun th -> REWRITE_TAC[th])
   THENL
    [REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB];
     ASM_SIMP_TAC[GSYM L2NORM_LNORM; SQUARE_INTEGRABLE_SUB; ETA_AX]]) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs(x - &0) = x`; GE;
               L2NORM_POS_LE; SQUARE_INTEGRABLE_SUB; ETA_AX]);;

let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f s e. real_measurable s /\ f square_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g square_integrable_on s /\
                   l2norm s (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&2:real`; `e:real`]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[GSYM SQUARE_INTEGRABLE_LSPACE; REAL_OF_NUM_LE; ARITH;
                  GSYM REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop o g o lift` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; ETA_AX;
                    IMAGE_LIFT_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[SQUARE_INTEGRABLE_LSPACE; o_DEF; LIFT_DROP; ETA_AX];
    DISCH_TAC THEN
    ASM_SIMP_TAC[L2NORM_LNORM; SQUARE_INTEGRABLE_SUB; ETA_AX] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> x = y ==> y < e`)) THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; LIFT_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Orthonormal system of L2 functions and their Fourier coefficients.        *)
(* ------------------------------------------------------------------------- *)

let orthonormal_system = new_definition
 `orthonormal_system s w <=>
        !m n. l2product s (w m) (w n) = if m = n then &1 else &0`;;

let orthonormal_coefficient = new_definition
 `orthonormal_coefficient s w f (n:num) = l2product s (w n) f`;;

let ORTHONORMAL_SYSTEM_L2NORM = prove
 (`!s w. orthonormal_system s w ==> !i. l2norm s (w i) = &1`,
  SIMP_TAC[orthonormal_system; l2norm; SQRT_1]);;

let ORTHONORMAL_PARTIAL_SUM_DIFF = prove
 (`!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> l2norm s (\x. f(x) - sum t (\i. a i * w i x)) pow 2 =
            (l2norm s f) pow 2 + sum t (\i. (a i) pow 2) -
            &2 * sum t (\i. a i * orthonormal_coefficient s w f i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. sum t (\i:num. a i * w i x)) square_integrable_on s`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; ETA_AX; FINITE_NUMSEG;
                 SQUARE_INTEGRABLE_LMUL];
   ALL_TAC] THEN
  ASM_SIMP_TAC[L2NORM_POW_2; SQUARE_INTEGRABLE_SUB; ETA_AX; L2PRODUCT_LSUB] THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB; ETA_AX; L2PRODUCT_RSUB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x' = x /\ b - &2 * x = c ==> a - x - (x' - b) = a + c`) THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[L2PRODUCT_SYM]; ALL_TAC] THEN
  ASM_SIMP_TAC[L2PRODUCT_RSUM; ETA_AX; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_SUM] THEN
  ASM_SIMP_TAC[L2PRODUCT_LSUM; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
  ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  REWRITE_TAC[orthonormal_coefficient; REAL_MUL_RID; GSYM REAL_POW_2] THEN
  REWRITE_TAC[L2PRODUCT_SYM]);;

let ORTHONORMAL_OPTIMAL_PARTIAL_SUM = prove
 (`!s w a f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==>  l2norm s (\x. f(x) -
                           sum t (\i. orthonormal_coefficient s w f i * w i x))
             <= l2norm s (\x. f(x) - sum t (\i. a i * w i x))`,
  REPEAT STRIP_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [L2NORM_LE; SQUARE_INTEGRABLE_SUM; ETA_AX; FINITE_NUMSEG;
    GSYM L2NORM_POW_2; SQUARE_INTEGRABLE_LMUL; SQUARE_INTEGRABLE_SUB] THEN
  ASM_SIMP_TAC[ORTHONORMAL_PARTIAL_SUM_DIFF] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH
   `b pow 2 - &2 * b * b <= a pow 2 - &2 * a * b <=> &0 <= (a - b) pow 2`] THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

let BESSEL_INEQUALITY = prove
 (`!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s /\ FINITE t
        ==> sum t (\i. (orthonormal_coefficient s w f i) pow 2)
             <= l2norm s f pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_PARTIAL_SUM_DIFF) THEN
  DISCH_THEN(MP_TAC o SPEC `orthonormal_coefficient s w f`) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH `a + b - &2 * b = a - b`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= p ==> p = x - y ==> y <= x`) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

let FOURIER_SERIES_SQUARE_SUMMABLE = prove
 (`!s w f t.
        orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
        f square_integrable_on s
        ==> real_summable t (\i. (orthonormal_coefficient s w f i) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[real_summable; real_sums; REALLIM_SEQUENTIALLY] THEN
  MP_TAC(ISPECL
   [`\n. sum(t INTER (0..n)) (\i. (orthonormal_coefficient s w f i) pow 2)`;
    `l2norm s f pow 2`] CONVERGENT_BOUNDED_MONOTONE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`s:real->bool`; `w:num->real->real`;
                `f:real->real`; `t INTER (0..n)`] BESSEL_INEQUALITY) THEN
    ASM_SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= y ==> abs(x) <= y`) THEN
    SIMP_TAC[SUM_POS_LE; FINITE_INTER; FINITE_NUMSEG; REAL_LE_POW_2] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[FINITE_INTER; SUBSET_REFL; FINITE_NUMSEG; REAL_LE_POW_2];
    DISJ1_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[INTER_SUBSET; FINITE_NUMSEG; REAL_LE_POW_2; FINITE_INTER] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> u INTER s SUBSET u INTER t`) THEN
    REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_ARITH_TAC]);;

let ORTHONORMAL_FOURIER_PARTIAL_SUM_DIFF_SQUARED = prove
 (`!s w a f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s /\ FINITE t
    ==> l2norm s (\x. f x -
                      sum t (\i. orthonormal_coefficient s w f i * w i x))
        pow 2 =
        l2norm s f pow 2 - sum t (\i. orthonormal_coefficient s w f i pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_PARTIAL_SUM_DIFF) THEN
  DISCH_THEN(MP_TAC o SPEC `orthonormal_coefficient s w f`) THEN
  REWRITE_TAC[GSYM REAL_POW_2; REAL_ARITH `a + b - &2 * b = a - b`]);;

let FOURIER_SERIES_L2_SUMMABLE = prove
 (`!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            ((\n. l2norm s
                    (\x. sum (t INTER (0..n))
                             (\i. orthonormal_coefficient s w f i * w i x) -
                         g(x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC L2_COMPLETE THEN
  ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; FINITE_INTER; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o
   MATCH_MP FOURIER_SERIES_SQUARE_SUMMABLE) THEN
  REWRITE_TAC[REAL_SUMMABLE; summable; sums; CONVERGENT_EQ_CAUCHY] THEN
  REWRITE_TAC[cauchy; GE] THEN
  DISCH_THEN(MP_TAC o SPEC `(e:real) pow 2`) THEN
  ASM_SIMP_TAC[REAL_POW_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN MATCH_MP_TAC WLOG_LE THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THENL
   [ASM_CASES_TAC `N:num <= m` THEN ASM_CASES_TAC `N:num <= n` THEN
    ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC L2NORM_SUB THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUM; FINITE_INTER; FINITE_NUMSEG;
               SQUARE_INTEGRABLE_LMUL; ETA_AX];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT2_REV THEN EXISTS_TAC `2` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `m:num`]) THEN
  SIMP_TAC[DIST_REAL; GSYM drop; DROP_VSUM; FINITE_INTER; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[o_DEF; LIFT_DROP] THEN
  SUBGOAL_THEN
   `!f. sum (t INTER (0..n)) f - sum (t INTER (0..m)) f =
        sum (t INTER (m+1..n)) f`
   (fun th -> REWRITE_TAC[th])
  THENL
   [X_GEN_TAC `h:num->real` THEN
    REWRITE_TAC[REAL_ARITH `a - b:real = c <=> b + c = a`] THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN
    SIMP_TAC[FINITE_INTER; FINITE_NUMSEG; EXTENSION; IN_INTER; NOT_IN_EMPTY;
             IN_UNION; IN_NUMSEG] THEN
    CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `(i:num) IN t` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  ASM_SIMP_TAC[L2NORM_POW_2; SQUARE_INTEGRABLE_SUM; FINITE_INTER;
               FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RSUM; ETA_AX; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               FINITE_INTER; SQUARE_INTEGRABLE_SUM] THEN
  ASM_SIMP_TAC[L2PRODUCT_LSUM; SQUARE_INTEGRABLE_LMUL; FINITE_NUMSEG;
               FINITE_INTER; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_RMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  ASM_SIMP_TAC[L2PRODUCT_LMUL; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
  ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO; SUM_DELTA] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_POW_2; REAL_ARITH `x <= abs x`]);;

let FOURIER_SERIES_L2_SUMMABLE_STRONG = prove
 (`!s w f t.
    orthonormal_system s w /\ (!i. (w i) square_integrable_on s) /\
    f square_integrable_on s
    ==> ?g. g square_integrable_on s /\
            (!i. i IN t
                 ==> orthonormal_coefficient s w (\x. f x - g x) i = &0) /\
            ((\n. l2norm s
                   (\x. sum (t INTER (0..n))
                            (\i. orthonormal_coefficient s w f i * w i x) -
                        g(x))) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o
    MATCH_MP FOURIER_SERIES_L2_SUMMABLE) THEN
  REWRITE_TAC[orthonormal_coefficient] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[orthonormal_coefficient] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\n. l2product s (w i)
     (\x. (f x - sum (t INTER (0..n)) (\i. l2product s (w i) f * w i x)) +
          (sum (t INTER (0..n)) (\i. l2product s (w i) f * w i x) - g x))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN GEN_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [L2PRODUCT_RADD; SQUARE_INTEGRABLE_SUB;  SQUARE_INTEGRABLE_SUM;
    FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_ADD_LID] THEN
  MATCH_MP_TAC REALLIM_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `i:num` THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[L2PRODUCT_RSUB; SQUARE_INTEGRABLE_SUM; L2PRODUCT_RSUM;
           FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
    ASM_SIMP_TAC[L2PRODUCT_RMUL; ETA_AX] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[orthonormal_system]) THEN
    ASM_SIMP_TAC[COND_RAND; REAL_MUL_RZERO] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; IN_INTER; IN_NUMSEG; LE_0; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_REFL];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REALLIM_NULL_COMPARISON)) THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SCHWARTZ_INEQUALITY_ABS o
        lhand o snd) THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB;  SQUARE_INTEGRABLE_SUM;
      FINITE_INTER; FINITE_NUMSEG; SQUARE_INTEGRABLE_LMUL; ETA_AX] THEN
    ASM_SIMP_TAC[ORTHONORMAL_SYSTEM_L2NORM; REAL_MUL_LID]]);;

(* ------------------------------------------------------------------------- *)
(* Actual trigonometric orthogonality relations.                             *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRABLE_ON_INTERVAL_TAC =
  MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;;

let HAS_REAL_INTEGRAL_SIN_NX = prove
 (`!n. ((\x. sin(&n * x)) has_real_integral &0) (real_interval[--pi,pi])`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0; REAL_MUL_LZERO; SIN_0] THEN
  MP_TAC(ISPECL
   [`\x. --(inv(&n) * cos(&n * x))`; `\x. sin(&n * x)`; `--pi`; `pi`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  SIMP_TAC[REAL_ARITH `&0 <= pi ==> --pi <= pi`; PI_POS_LE] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SIN_NPI; COS_NPI; SIN_NEG; COS_NEG] THEN
  REWRITE_TAC[REAL_SUB_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
  CONV_TAC REAL_FIELD);;

let REAL_INTEGRABLE_SIN_CX = prove
 (`!c. (\x. sin(c * x)) real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN REAL_INTEGRABLE_ON_INTERVAL_TAC);;

let REAL_INTEGRAL_SIN_NX = prove
 (`!n. real_integral (real_interval[--pi,pi]) (\x. sin(&n * x)) = &0`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_SIN_NX]);;

let HAS_REAL_INTEGRAL_COS_NX = prove
 (`!n. ((\x. cos(&n * x)) has_real_integral (if n = 0 then &2 * pi else &0))
       (real_interval[--pi,pi])`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[COS_0; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `&2 * pi = &1 * (pi - --pi)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`\x. inv(&n) * sin(&n * x)`; `\x. cos(&n * x)`; `--pi`; `pi`]
          REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    SIMP_TAC[REAL_ARITH `&0 <= pi ==> --pi <= pi`; PI_POS_LE] THEN
    REWRITE_TAC[REAL_MUL_RNEG; SIN_NPI; COS_NPI; SIN_NEG; COS_NEG] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_NEG_0; REAL_SUB_REFL] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REAL_DIFF_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD]);;

let REAL_INTEGRABLE_COS_CX = prove
 (`!c. (\x. cos(c * x)) real_integrable_on real_interval[--pi,pi]`,
  GEN_TAC THEN REAL_INTEGRABLE_ON_INTERVAL_TAC);;

let REAL_INTEGRAL_COS_NX = prove
 (`!n. real_integral (real_interval[--pi,pi]) (\x. cos(&n * x)) =
       if n = 0 then &2 * pi else &0`,
  GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_COS_NX]);;

let REAL_INTEGRAL_SIN_AND_COS = prove
 (`!m n. real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * cos(&n * x)) =
                (if m = n then if n = 0 then &2 * pi else pi else &0) /\
         real_integral (real_interval[--pi,pi])
           (\x. cos(&m * x) * sin(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * cos(&n * x)) = &0 /\
         real_integral (real_interval[--pi,pi])
           (\x. sin(&m * x) * sin(&n * x)) =
              (if m = n /\ ~(n = 0) then pi else &0)`,
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN
  MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `m:num`] THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_MUL_SIN_COS; REAL_MUL_COS_SIN;
              REAL_MUL_COS_COS; REAL_MUL_SIN_SIN] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
  SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRAL_SUB; real_div;
           REAL_INTEGRABLE_SIN_CX; REAL_INTEGRABLE_COS_CX;
           REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_SUB; REAL_INTEGRABLE_ADD] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[REAL_INTEGRAL_SIN_NX; REAL_INTEGRAL_COS_NX] THEN
  REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_ADD_LID] THEN
  ASM_SIMP_TAC[ARITH_RULE `n:num <= m ==> (m - n = 0 <=> m = n)`] THEN
  REWRITE_TAC[ADD_EQ_0] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ARITH `(a + a) * inv(&2) = a`;
                  REAL_MUL_LZERO] THEN
  REAL_ARITH_TAC);;

let REAL_INTEGRABLE_SIN_AND_COS = prove
 (`!m n a b.
      (\x. cos(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. cos(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * cos(&n * x)) real_integrable_on real_interval[a,b] /\
      (\x. sin(&m * x) * sin(&n * x)) real_integrable_on real_interval[a,b]`,
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THEN
  REAL_INTEGRABLE_ON_INTERVAL_TAC);;

let trigonometric_set_def = new_definition
 `trigonometric_set n =
    if n = 0 then \x. &1 / sqrt(&2 * pi)
    else if ODD n then \x. sin(&(n DIV 2 + 1) * x) / sqrt(pi)
    else \x. cos(&(n DIV 2) * x) / sqrt(pi)`;;

let trigonometric_set = prove
 (`trigonometric_set 0 = (\x. cos(&0 * x) / sqrt(&2 * pi)) /\
   trigonometric_set (2 * n + 1) = (\x. sin(&(n + 1) * x) / sqrt(pi)) /\
   trigonometric_set (2 * n + 2) = (\x. cos(&(n + 1) * x) / sqrt(pi))`,
  REWRITE_TAC[trigonometric_set_def; EVEN_ADD; EVEN_MULT; ARITH; ADD_EQ_0;
              GSYM NOT_EVEN] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 1) DIV 2 = n`] THEN
  REWRITE_TAC[ARITH_RULE `(2 * n + 2) DIV 2 = n + 1`] THEN
  REWRITE_TAC[REAL_MUL_LZERO; COS_0]);;

let TRIGONOMETRIC_SET_EVEN = prove
 (`!k. trigonometric_set(2 * k) =
        if k = 0 then \x. &1 / sqrt(&2 * pi)
        else \x. cos(&k * x) / sqrt pi`,
  INDUCT_TAC THEN
  REWRITE_TAC[ARITH; trigonometric_set; REAL_MUL_LZERO; COS_0] THEN
  REWRITE_TAC[NOT_SUC; ARITH_RULE `2 * SUC k = 2 * k + 2`] THEN
  REWRITE_TAC[trigonometric_set; GSYM ADD1]);;

let ODD_EVEN_INDUCT_LEMMA = prove
 (`(!n:num. P 0) /\ (!n. P(2 * n + 1)) /\ (!n. P(2 * n + 2)) ==> !n. P n`,
  REWRITE_TAC[FORALL_SIMP] THEN STRIP_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(ISPEC `n:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[EVEN_EXISTS; ODD_EXISTS] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[ARITH_RULE
    `SUC(2 * n) = 2 * n + 1 /\ SUC(2 * n + 1) = 2 * n + 2`]);;

let ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET = prove
 (`orthonormal_system (real_interval[--pi,pi]) trigonometric_set`,
  REWRITE_TAC[orthonormal_system; l2product] THEN
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[trigonometric_set] THEN
  REWRITE_TAC[REAL_ARITH `a / k * b / l:real = (inv(k) * inv(l)) * a * b`] THEN
  SIMP_TAC[REAL_INTEGRAL_LMUL; REAL_INTEGRABLE_SIN_AND_COS] THEN
  REWRITE_TAC[REAL_INTEGRAL_SIN_AND_COS] THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_MUL_RZERO] THEN
  ASM_CASES_TAC `m:num = n` THEN
  TRY (COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  TRY (MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_ARITH_TAC) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 = a + b <=> a = 0 /\ b = 0`;
                  EQ_ADD_RCANCEL; EQ_MULT_LCANCEL] THEN
  REWRITE_TAC[ARITH; REAL_MUL_RZERO] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL; GSYM REAL_POW_2] THEN
  SIMP_TAC[SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_MUL_LINV THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let SQUARE_INTEGRABLE_TRIGONOMETRIC_SET = prove
 (`!i. (trigonometric_set i) square_integrable_on real_interval[--pi,pi]`,
  MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REWRITE_TAC[trigonometric_set] THEN
  REWRITE_TAC[real_div] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
  MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
  REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
  GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Weierstrass for trigonometric polynomials.                                *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_TRIG_POLYNOMIAL = prove
 (`!f e. f real_continuous_on real_interval[--pi,pi] /\
         f(--pi) = f pi /\ &0 < e
         ==> ?n a b.
                !x. x IN real_interval[--pi,pi]
                    ==> abs(f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`,
  let lemma1 = prove
   (`!f. f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
         ==> !z. norm z = &1
                 ==> (f o Im o clog) real_continuous
                     at z within {w | norm w = &1}`,
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 <= Re z \/ Re z < &0`) THENL
     [ALL_TAC;
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS] THEN
      MATCH_MP_TAC CONTINUOUS_TRANSFORM_WITHIN THEN
      EXISTS_TAC `Cx o f o (\x. x + pi) o Im o clog o (--)` THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01; IN_ELIM_THM] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w = Cx(&0)` THEN
        ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
        STRIP_TAC THEN ASM_SIMP_TAC[CLOG_NEG; o_THM] THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_II; RE_CX; REAL_SUB_ADD] THEN
        ASM_REWRITE_TAC[REAL_ARITH `(x + pi) + pi = x + &2 * pi`];
        REWRITE_TAC[o_ASSOC] THEN MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
        CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN CONTINUOUS_TAC;
          REWRITE_TAC[GSYM o_ASSOC; GSYM REAL_CONTINUOUS_CONTINUOUS]]]] THEN
    REWRITE_TAC[o_ASSOC] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_WITHIN_COMPOSE THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC CONTINUOUS_WITHIN_CLOG THEN
       REWRITE_TAC[GSYM real] THEN DISCH_TAC THEN
       UNDISCH_TAC `norm(z:complex) = &1` THEN
       ASM_SIMP_TAC[REAL_NORM; RE_NEG; REAL_NEG_GT0] THEN
       ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_COMPOSE THEN
    REWRITE_TAC[REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN] THEN
    TRY(MATCH_MP_TAC REAL_CONTINUOUS_WITHINREAL_COMPOSE THEN
        SIMP_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_CONST;
                 REAL_CONTINUOUS_WITHIN_ID]) THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN]) THEN
    SIMP_TAC[IN_UNIV; WITHINREAL_UNIV]) in
  let lemma2 = prove
   (`!f. f real_continuous_on real_interval[--pi,pi] /\ f(--pi) = f pi
         ==> !z. norm z = &1
                 ==> (f o Im o clog) real_continuous
                     at z within {w | norm w = &1}`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL
     [`f:real->real`; `--pi`; `pi`] REAL_TIETZE_PERIODIC_INTERVAL) THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `g:real->real` lemma1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS] THEN
    MATCH_MP_TAC(REWRITE_RULE
     [TAUT `a /\ b /\ c /\ d ==> e <=> a /\ b /\ c ==> d ==> e`]
      CONTINUOUS_TRANSFORM_WITHIN) THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
    X_GEN_TAC `w:complex` THEN ASM_CASES_TAC `w = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[o_THM] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[IN_REAL_INTERVAL; CLOG_WORKS; REAL_LT_IMP_LE]) in
  REPEAT STRIP_TAC THEN
  (CHOOSE_THEN MP_TAC o prove_inductive_relations_exist)
   `(!c. poly2 (\x. c)) /\
    (!p q. poly2 p /\ poly2 q ==> poly2 (\x. p x + q x)) /\
    (!p q. poly2 p /\ poly2 q ==> poly2 (\x. p x * q x)) /\
    poly2 Re /\ poly2 Im` THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  MP_TAC(ISPECL [`poly2:(complex->real)->bool`; `{z:complex | norm z = &1}`]
        STONE_WEIERSTRASS) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_CLOSED_IMP_COMPACT THEN CONJ_TAC THENL
       [REWRITE_TAC[bounded; IN_ELIM_THM] THEN MESON_TAC[REAL_LE_REFL];
        ONCE_REWRITE_TAC[SET_RULE `{x | p x} = {x | x IN UNIV /\ p x}`] THEN
        REWRITE_TAC[GSYM LIFT_EQ] THEN
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
        REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; GSYM o_DEF; CLOSED_UNIV]];
      MATCH_MP_TAC(MESON[]
       `(!x f. P f ==> R f x) ==> (!f. P f ==> !x. Q x ==> R f x)`) THEN
      GEN_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[REAL_CONTINUOUS_ADD; REAL_CONTINUOUS_MUL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONST;
                  REAL_CONTINUOUS_COMPLEX_COMPONENTS_WITHIN];
      MAP_EVERY X_GEN_TAC [`w:complex`; `z:complex`] THEN
      REWRITE_TAC[IN_ELIM_THM; COMPLEX_EQ; DE_MORGAN_THM] THEN STRIP_TAC THENL
       [EXISTS_TAC `Re` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `Im` THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`(f:real->real) o Im o clog`; `e:real`]) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; lemma2] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `trigpoly =
     \f. ?n a b.
         f = \x. sum(0..n) (\k. a k * sin(&k * x) +  b k * cos(&k * x))` THEN
  SUBGOAL_THEN `!c:real. trigpoly(\x:real. c)` ASSUME_TAC THENL
   [X_GEN_TAC `c:real` THEN EXPAND_TAC "trigpoly" THEN REWRITE_TAC[] THEN
    EXISTS_TAC `0` THEN
    REWRITE_TAC[SUM_SING_NUMSEG; REAL_MUL_LZERO; SIN_0; COS_0] THEN
    MAP_EVERY EXISTS_TAC [`(\n. &0):num->real`; `(\n. c):num->real`] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real->real. trigpoly f /\ trigpoly g ==> trigpoly(\x. f x + g x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "trigpoly" THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`n1:num`; `a1:num->real`; `b1:num->real`;
      `n2:num`; `a2:num->real`; `b2:num->real`] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    MAP_EVERY EXISTS_TAC
     [`MAX n1 n2`;
      `(\n. (if n <= n1 then a1 n else &0) +
             (if n <= n2 then a2 n else &0)):num->real`;
      `(\n. (if n <= n1 then b1 n else &0) +
            (if n <= n2 then b2 n else &0)):num->real`] THEN
    REWRITE_TAC[SUM_ADD_NUMSEG; FUN_EQ_THM; REAL_ADD_RDISTRIB] THEN
    GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a:real = e /\ b = g /\ c = f /\ d = h
      ==> (a + b) + (c + d) = (e + f) + (g + h)`) THEN
    REPEAT CONJ_TAC THEN
    REWRITE_TAC[COND_RATOR; COND_RAND; REAL_MUL_LZERO] THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    MATCH_MP_TAC(MESON[] `s = t ==> sum s f = sum t f`) THEN
    REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f s:num->bool. FINITE s /\ (!i. i IN s ==> trigpoly(f i))
                    ==> trigpoly(\x:real. sum s (\i. f i x))`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    ASM_SIMP_TAC[SUM_CLAUSES; IN_INSERT; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real->real c. trigpoly f ==> trigpoly (\x. c * f x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "trigpoly" THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`; `b:num->real`] THEN
    DISCH_THEN SUBST1_TAC THEN MAP_EVERY EXISTS_TAC
     [`n:num`; `\i. c * (a:num->real) i`; `\i. c * (b:num->real) i`] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB; GSYM SUM_LMUL; GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. trigpoly(\x. sin(&i * x))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "trigpoly" THEN MAP_EVERY EXISTS_TAC
     [`k:num`; `\i:num. if i = k then &1 else &0`; `\i:num. &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; COND_RAND; COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. trigpoly(\x. cos(&i * x))` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN EXPAND_TAC "trigpoly" THEN MAP_EVERY EXISTS_TAC
     [`k:num`; `\i:num. &0`; `\i:num. if i = k then &1 else &0`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; COND_RAND; COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; IN_NUMSEG; LE_0; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. trigpoly(\x. sin(&i * x) * sin(&j * x)) /\
          trigpoly(\x. sin(&i * x) * cos(&j * x)) /\
          trigpoly(\x. cos(&i * x) * sin(&j * x)) /\
          trigpoly(\x. cos(&i * x) * cos(&j * x))`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC WLOG_LE THEN
    CONJ_TAC THENL [REWRITE_TAC[CONJ_ACI; REAL_MUL_AC]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_SIN_SIN; REAL_MUL_SIN_COS; REAL_MUL_COS_SIN;
                REAL_MUL_COS_COS] THEN
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; GSYM REAL_SUB_RDISTRIB] THEN
    SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `x / &2 = inv(&2) * x`;
                REAL_ARITH `x - y:real = x + --(&1) * y`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real->real. trigpoly f /\ trigpoly g ==> trigpoly(\x. f x * g x)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [SYM
         th]) THEN
    REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL STRIP_THM_THEN SUBST1_TAC) THEN
    REWRITE_TAC[REAL_MUL_SUM_NUMSEG] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH
    `(ai * si + bi * ci) * (aj * sj + bj * cj):real =
     ((ai * aj) * (si * sj) + (bi * bj) * (ci * cj)) +
     ((ai * bj) * (si * cj) + (aj * bi) * (ci * sj))`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:complex->real. poly2 f ==> trigpoly(\x.  f(cexp(ii * Cx x)))`
  (MP_TAC o SPEC `g:complex->real`) THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[RE_CEXP; IM_CEXP; RE_MUL_II; IM_CX; IM_MUL_II; RE_CX] THEN
    ONCE_REWRITE_TAC[MESON[REAL_MUL_LID]
     `cos x = cos(&1 * x) /\ sin x = sin(&1 * x)`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "trigpoly" THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`n:num`; `a:num->real`; `b:num->real`] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  X_GEN_TAC `r:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `cexp(ii * Cx r)`) THEN
  REWRITE_TAC[NORM_CEXP_II] THEN MATCH_MP_TAC(REAL_ARITH
   `x = x' ==> abs(x - y) < e ==> abs(x' - y) < e`) THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_CASES_TAC `r = --pi` THENL
   [UNDISCH_THEN `r = --pi` SUBST_ALL_TAC THEN
    REWRITE_TAC[CEXP_EULER; GSYM CX_COS; GSYM CX_SIN] THEN
    REWRITE_TAC[COS_NEG; SIN_NEG; SIN_PI; COS_PI] THEN
    REWRITE_TAC[CX_NEG; COMPLEX_MUL_RZERO; COMPLEX_NEG_0] THEN
    ASM_REWRITE_TAC[CLOG_NEG_1; COMPLEX_ADD_RID; IM_MUL_II; RE_CX];
    ASM_SIMP_TAC[CLOG_CEXP; IM_MUL_II; RE_CX; REAL_LT_LE]]);;

(* ------------------------------------------------------------------------- *)
(* A bit of extra hacking round so that the ends of a function are OK.       *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_TWEAK_ENDS = prove
 (`!a b d e.
        a < b /\ &0 < e
        ==> ?f. f real_continuous_on real_interval[a,b] /\
                f(a) = d /\ f(b) = &0 /\
                l2norm (real_interval[a,b]) f < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. if x <= a + inv(&n + &1)
             then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0)
        real_continuous_on real_interval[a,b]`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `a < a + inv(&n + &1)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `a + inv(&n + &1) <= b` THENL
     [SUBGOAL_THEN
       `real_interval[a,b] = real_interval[a,a + inv(&n + &1)] UNION
                             real_interval[a + inv(&n + &1),b]`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_UNION; IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_CASES THEN
      REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST] THEN
      CONJ_TAC THENL
       [SIMP_TAC[real_div; REAL_CONTINUOUS_ON_MUL; REAL_CONTINUOUS_ON_CONST;
                 REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID];
        X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ASM_CASES_TAC `x:real = a + inv(&n + &1)` THENL
         [ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_MUL_RZERO];
          ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_EQ THEN
      EXISTS_TAC `\x. ((&n + &1) * d) * ((a + inv(&n + &1)) - x)` THEN
      SIMP_TAC[real_div; REAL_CONTINUOUS_ON_MUL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC
   (ISPECL [`\n x. (if x <= a + inv(&n + &1)
                    then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0)
                   pow 2`;
            `\x:real. if x = a then d pow 2 else &0`;
            `\x:real. (d:real) pow 2`;
            `real_interval[a,b]`]
        REAL_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POW];
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_CONST];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_POW] THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_ABS] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
      ONCE_REWRITE_TAC[REAL_ABS_MUL] THEN
      REWRITE_TAC[REAL_ARITH `d * x <= d <=> &0 <= d * (&1 - x)`] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      REWRITE_TAC[REAL_ARITH `&0 <= &1 - x * y <=> y * x <= &1`] THEN
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      ASM_CASES_TAC `x:real = a` THEN ASM_REWRITE_TAC[] THENL
       [ASM_REWRITE_TAC[REAL_LE_ADDR; REAL_LE_INV_EQ;
                        REAL_ARITH `&0 <= &n + &1`] THEN
        REWRITE_TAC[REAL_ADD_SUB] THEN
        SIMP_TAC[REAL_FIELD `&0 < x ==> (x * d) * inv x = d`;
                 REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
        REWRITE_TAC[REALLIM_CONST];
        MATCH_MP_TAC REALLIM_EVENTUALLY THEN
        REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        MP_TAC(ISPEC `x - a:real` REAL_ARCH_INV) THEN
        DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        SUBGOAL_THEN `inv(&n + &1) <= inv(&N)` MP_TAC THENL
         [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC]];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `(e:real) pow 2`) THEN
    ASM_SIMP_TAC[REAL_POW_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
    MP_TAC(ISPEC `b - a:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?n:num. N <= n /\ M <= n` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `M + N:num` THEN ARITH_TAC; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    EXISTS_TAC `\x. if x <= a + inv(&n + &1)
                 then ((&n + &1) * d) * ((a + inv(&n + &1)) - x) else &0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(REAL_ARITH `&0 < &n + &1`) THEN
      SIMP_TAC[REAL_LE_ADDR; REAL_LT_INV_EQ; REAL_LT_IMP_LE] THEN
      CONV_TAC REAL_FIELD;
      SUBGOAL_THEN `inv(&n + &1) < b - a` MP_TAC THENL
        [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&M)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `e = sqrt(e pow 2)` SUBST1_TAC THENL
       [ASM_MESON_TAC[POW_2_SQRT; REAL_LT_IMP_LE]; ALL_TAC] THEN
      REWRITE_TAC[l2norm; l2product] THEN MATCH_MP_TAC SQRT_MONO_LT THEN
      REWRITE_TAC[GSYM REAL_POW_2] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `abs(i - l) < e ==> &0 <= i /\ l = &0 ==> i < e`)) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_POS THEN
        ASM_SIMP_TAC[REAL_INTEGRABLE_CONTINUOUS; REAL_CONTINUOUS_ON_POW] THEN
        REWRITE_TAC[REAL_LE_POW_2];
        MP_TAC(ISPEC `real_interval[a,b]` REAL_INTEGRAL_0) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
        EXISTS_TAC `{a:real}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
        SIMP_TAC[IN_DIFF; IN_SING]]]]);;

let SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS = prove
 (`!f a b e.
        f square_integrable_on real_interval[a,b] /\ a < b /\ &0 < e
        ==> ?g. g real_continuous_on real_interval[a,b] /\
                g b = g a /\
                g square_integrable_on real_interval[a,b] /\
                l2norm (real_interval[a,b]) (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `real_interval[a,b]`; `e / &2`]
        SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_MEASURABLE_REAL_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`a:real`; `b:real`; `(g:real->real) b - g a`; `e / &2`]
        REAL_INTEGRAL_TWEAK_ENDS) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `h square_integrable_on real_interval[a,b]` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE]; ALL_TAC] THEN
  EXISTS_TAC `\x. (g:real->real) x + h x` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    REAL_ARITH_TAC;
    MATCH_MP_TAC SQUARE_INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[REAL_ARITH `f - (g + h):real = (f - g) + --h`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) L2NORM_TRIANGLE o lhand o snd) THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB; SQUARE_INTEGRABLE_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH
     `y < e / &2 /\ z < e / &2 ==> x <= y + z ==> x < e`) THEN
    ASM_SIMP_TAC[L2NORM_NEG]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main approximation result.                                      *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_L2_TRIG_POLYNOMIAL = prove
 (`!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a b.
                l2norm (real_interval[--pi,pi])
                       (\x. f x - sum(0..n) (\k. a k * sin(&k * x) +
                                                 b k * cos(&k * x))) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `e / &2`]
        SQUARE_INTEGRABLE_APPROXIMATE_CONTINUOUS_ENDS) THEN
  ASM_REWRITE_TAC[REAL_HALF; REAL_ARITH `--pi < pi <=> &0 < pi`; PI_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real->real`; `e / &6`] WEIERSTRASS_TRIG_POLYNOMIAL) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MAP_EVERY (fun t -> MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC t)
   [`n:num`; `u:num->real`; `v:num->real`] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  SUBGOAL_THEN
   `!n u v. (\x. sum(0..n) (\k. u k * sin(&k * x) + v k * cos(&k * x)))
            square_integrable_on (real_interval[--pi,pi])`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    GEN_TAC THEN DISCH_TAC THEN REAL_DIFFERENTIABLE_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `l2norm (real_interval[--pi,pi]) (\x. f x - g x) +
              l2norm (real_interval[--pi,pi]) (\x. g x - sum(0..n)
                   (\k. u k * sin(&k * x) + v k * cos(&k * x)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) L2NORM_TRIANGLE o rand o snd) THEN
    REWRITE_TAC[REAL_ARITH `(f - g) + (g - h):real = f - h`] THEN
    ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y <= e / &2 ==> x + y < e`) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[l2norm; l2product; GSYM REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN
  SUBGOAL_THEN
   `(\x. g x - sum(0..n) (\k. u k * sin(&k * x) + v k * cos(&k * x)))
    square_integrable_on (real_interval[--pi,pi])`
  MP_TAC THENL [ASM_SIMP_TAC[SQUARE_INTEGRABLE_SUB]; ALL_TAC] THEN
  REWRITE_TAC[square_integrable_on] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_POS; REAL_LE_POW_2] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral(real_interval[--pi,pi]) (\x. (e / &6) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN X_GEN_TAC `x:real` THEN
    DISCH_TAC THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    MATCH_MP_TAC(REAL_ARITH `abs x < e ==> abs(x) <= abs e`) THEN
    ASM_SIMP_TAC[];
    SIMP_TAC[REAL_INTEGRAL_CONST; REAL_ARITH `--pi <= pi <=> &0 <= pi`;
             PI_POS_LE] THEN
    REWRITE_TAC[real_div; REAL_POW_MUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;

let WEIERSTRASS_L2_TRIGONOMETRIC_SET = prove
 (`!f e. f square_integrable_on real_interval[--pi,pi] /\ &0 < e
         ==> ?n a.
                l2norm (real_interval[--pi,pi])
                       (\x. f x -
                            sum(0..n) (\k. a k * trigonometric_set k x))
                < e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP WEIERSTRASS_L2_TRIG_POLYNOMIAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `a:num->real`; `b:num->real`] THEN
  DISCH_TAC THEN EXISTS_TAC `2 * n + 1` THEN
  SUBST1_TAC(ARITH_RULE `0 = 2 * 0`) THEN
  REWRITE_TAC[SUM_PAIR; SUM_ADD_NUMSEG; trigonometric_set] THEN
  EXISTS_TAC
   `(\k. if k = 0 then sqrt(&2 * pi) * b 0
         else if EVEN k then sqrt pi * b(k DIV 2)
         else if k <= 2 * n then sqrt pi * a((k + 1) DIV 2)
         else &0):num->real` THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y < e`)) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH; ADD_EQ_0; MULT_EQ_0] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_SYM] THEN BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[LE_0; ARITH_RULE `2 * i <= 2 * n <=> i <= n`] THEN
    INDUCT_TAC THENL
     [REWRITE_TAC[trigonometric_set; ARITH; LE_0] THEN
      MATCH_MP_TAC(REAL_FIELD
       `&0 < s ==> (s * b) * c / s = b * c`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[NOT_SUC; ARITH_RULE `2 * (SUC i) = 2 * i + 2`] THEN
      REWRITE_TAC[trigonometric_set;
                  ARITH_RULE `(2 * i + 2) DIV 2 = SUC i`] THEN
      REWRITE_TAC[ADD1] THEN MATCH_MP_TAC(REAL_FIELD
       `&0 < s ==> (s * b) * c / s = b * c`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]];
    REWRITE_TAC[ARITH_RULE `2 * i + 1 = 2 * (i + 1) - 1`] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET)] THEN
    REWRITE_TAC[GSYM ADD1; ARITH; SUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n /\ 2 * SUC n - 1 = 2 * n + 1`] THEN
    REWRITE_TAC[ARITH_RULE `~(2 * n + 1 <= 2 * n)`; REAL_MUL_LZERO] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; REAL_ADD_RID] THEN
    SIMP_TAC[SIN_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_LID; ARITH] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n ==> 2 * i - 1 <= 2 * n`] THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[ARITH_RULE `SUC(2 * SUC i - 1) DIV 2 = SUC i`] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_FIELD
     `&0 < s ==> (s * b) * c / s = b * c`) THEN
    MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[PI_POS]]);;

(* ------------------------------------------------------------------------- *)
(* Convergence w.r.t. L2 norm of trigonometric Fourier series.               *)
(* ------------------------------------------------------------------------- *)

let fourier_coefficient = new_definition
 `fourier_coefficient =
    orthonormal_coefficient (real_interval[--pi,pi]) trigonometric_set`;;

let FOURIER_SERIES_L2 = prove
 (`!f. f square_integrable_on real_interval[--pi,pi]
       ==> ((\n. l2norm (real_interval[--pi,pi])
                        (\x. f(x) - sum(0..n) (\i. fourier_coefficient f i *
                                                   trigonometric_set i x)))
            ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `e:real`]
    WEIERSTRASS_L2_TRIGONOMETRIC_SET) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `a:num->real` THEN DISCH_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  REWRITE_TAC[fourier_coefficient] THEN MP_TAC(ISPECL
   [`real_interval[--pi,pi]`; `trigonometric_set`;
    `(\i. if i <= n then a i else &0):num->real`;
    `f:real->real`; `0..m`]
    ORTHONORMAL_OPTIMAL_PARTIAL_SUM) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET;
                  SQUARE_INTEGRABLE_TRIGONOMETRIC_SET; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ a < e ==> x <= a ==> abs x < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC L2NORM_POS_LE THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SQUARE_INTEGRABLE_LMUL THEN
    REWRITE_TAC[ETA_AX; SQUARE_INTEGRABLE_TRIGONOMETRIC_SET];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y < e`)) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:real` THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ_SUPERSET THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET_NUMSEG; LE_0] THEN
    SIMP_TAC[IN_NUMSEG; REAL_MUL_LZERO; LE_0]]);;

(* ------------------------------------------------------------------------- *)
(* Fourier coefficients go to 0 (weak form of Riemann-Lebesgue).             *)
(* ------------------------------------------------------------------------- *)

let TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real)` THEN
    REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
    MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
    REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; real_div] THEN
    REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; REAL_ABS_DIV] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
             SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
    SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;

let TRIGONOMETRIC_SET_MUL_INTEGRABLE = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. trigonometric_set n x * f x)
             real_integrable_on real_interval[--pi,pi]`,
  SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
           TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE]);;

let ABSOLUTELY_INTEGRABLE_SIN_PRODUCT,ABSOLUTELY_INTEGRABLE_COS_PRODUCT =
 (CONJ_PAIR o prove)
 (`(!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. sin(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi]) /\
   (!f k. f absolutely_real_integrable_on real_interval[--pi,pi]
          ==> (\x. cos(k * x) * f x) absolutely_real_integrable_on
              real_interval[--pi,pi])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  (ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
    [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
     EXISTS_TAC `(:real)` THEN
     REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
     MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
     MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
     REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; real_div] THEN
     REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
     REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
     SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
     REWRITE_TAC[trigonometric_set; COS_BOUND; SIN_BOUND]]));;

let FOURIER_PRODUCTS_INTEGRABLE_STRONG = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`,
  SIMP_TAC[ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
           ABSOLUTELY_INTEGRABLE_COS_PRODUCT;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;

let FOURIER_PRODUCTS_INTEGRABLE = prove
 (`!f. f square_integrable_on real_interval[--pi,pi]
       ==> f real_integrable_on real_interval[--pi,pi] /\
           (!k. (\x. cos(k * x) * f x) real_integrable_on
                real_interval[--pi,pi]) /\
           (!k. (\x. sin(k * x) * f x) real_integrable_on
                real_interval[--pi,pi])`,
  GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC FOURIER_PRODUCTS_INTEGRABLE_STRONG THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_REAL_INTERVAL;
               SQUARE_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE]);;

let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f s e. real_measurable s /\ f absolutely_real_integrable_on s /\ &0 < e
           ==> ?g. g real_continuous_on (:real) /\
                   g absolutely_real_integrable_on s /\
                   real_integral s (\x. abs(f x - g x)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o f o drop`; `IMAGE lift s`; `&1:real`; `e:real`]
          LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[LSPACE_1; GSYM ABSOLUTELY_REAL_INTEGRABLE_ON; REAL_OF_NUM_LE;
                  ARITH; GSYM REAL_MEASURABLE_MEASURABLE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `drop o g o lift` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_CONTINUOUS_ON; o_DEF; LIFT_DROP; ETA_AX;
                    IMAGE_LIFT_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON; o_DEF; LIFT_DROP; ETA_AX];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> x = y ==> y < e`)) THEN
    REWRITE_TAC[lnorm; REAL_INV_1; RPOW_POW; REAL_POW_1] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) REAL_INTEGRAL o rand o snd) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN
       `(\x. f x - (drop o g o lift) x) absolutely_real_integrable_on s`
      MP_TAC THENL [ALL_TAC; SIMP_TAC[absolutely_real_integrable_on]] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB; ETA_AX];
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[o_DEF; NORM_LIFT; LIFT_DROP; NORM_REAL; GSYM drop;
                  DROP_SUB; LIFT_SUB]]]);;

let RIEMANN_LEBESGUE_SQUARE_INTEGRABLE = prove
 (`!s w f.
        orthonormal_system s w /\
        (!i. w i square_integrable_on s) /\
        f square_integrable_on s
        ==> (orthonormal_coefficient s w f ---> &0) sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(:num)` o
    MATCH_MP FOURIER_SERIES_SQUARE_SUMMABLE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_SUMMABLE_IMP_TOZERO) THEN
  SIMP_TAC[IN_UNIV; REALLIM_NULL_POW_EQ; ARITH; ETA_AX]);;

let RIEMANN_LEBESGUE = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> (fourier_coefficient f ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
   [`f:real->real`; `real_interval[--pi,pi]`; `e / &2`]
   ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_MEASURABLE_REAL_INTERVAL;
               LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `g:real->real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`real_interval[--pi,pi]`; `trigonometric_set`; `g:real->real`]
        RIEMANN_LEBESGUE_SQUARE_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[ORTHONORMAL_SYSTEM_TRIGONOMETRIC_SET;
                SQUARE_INTEGRABLE_TRIGONOMETRIC_SET] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_IMP_SQUARE_INTEGRABLE THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `N:num <= n` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &2 ==> abs(y - z) <= x ==> y < e / &2 ==> z < e`)) THEN
  MATCH_MP_TAC(REAL_ARITH `abs(x - y) <= r ==> abs(abs x - abs y) <= r`) THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUB o
    rand o lhand o snd) THEN
  ASM_SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE] THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE];
    SUBGOAL_THEN `(\x. (f:real->real) x - g x) absolutely_real_integrable_on
                  real_interval[--pi,pi]`
    MP_TAC THENL [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB]; ALL_TAC] THEN
    SIMP_TAC[absolutely_real_integrable_on];
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SUB] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
    REWRITE_TAC[trigonometric_set; REAL_ABS_DIV] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
             SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
    SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC]);;

let RIEMANN_LEBESGUE_SIN = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. sin(&n * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * n + 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / sqrt pi * b = inv(sqrt pi) * a * b`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT; PI_POS;
               REAL_ARITH `&0 < x ==> &0 < abs x`; REAL_ABS_DIV] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `d <= e ==> x < d ==> x < e`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1`) THEN
  SIMP_TAC[SQRT_POS_LE; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

let RIEMANN_LEBESGUE_COS = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                                 (\x. cos(&n * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  EXISTS_TAC `N + 1` THEN MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ARITH_TAC; X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC)] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `2 * n + 2`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a / sqrt pi * b = inv(sqrt pi) * a * b`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; SQRT_POS_LT; PI_POS;
               REAL_ARITH `&0 < x ==> &0 < abs x`; REAL_ABS_DIV] THEN
  REWRITE_TAC[ADD1] THEN
  MATCH_MP_TAC(REAL_ARITH `d <= e ==> x < d ==> x < e`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &4 ==> inv(&4) * abs x <= &1`) THEN
  SIMP_TAC[SQRT_POS_LE; PI_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_LSQRT THEN MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

let RIEMANN_LEBESGUE_SIN_HALF = prove
 (`!f. f absolutely_real_integrable_on real_interval[--pi,pi]
       ==> ((\n. real_integral (real_interval[--pi,pi])
                               (\x. sin((&n + &1 / &2) * x) * f x)) ---> &0)
              sequentially`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SIN_ADD; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `(\n. real_integral (real_interval[--pi,pi])
                          (\x. sin(&n * x) * cos(&1 / &2 * x) * f x) +
                   real_integral (real_interval[--pi,pi])
                          (\x. cos(&n * x) * sin(&1 / &2 * x) * f x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REAL_INTEGRAL_ADD;
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC RIEMANN_LEBESGUE_SIN;
      MATCH_MP_TAC RIEMANN_LEBESGUE_COS]] THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
               ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
               ABSOLUTELY_INTEGRABLE_COS_PRODUCT]);;

let FOURIER_SUM_LIMIT_PAIR = prove
 (`!f n t l.
        f absolutely_real_integrable_on real_interval [--pi,pi]
        ==> (((\n. sum(0..2*n) (\k. fourier_coefficient f k *
                                    trigonometric_set k t)) ---> l)
             sequentially <=>
             ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                  trigonometric_set k t)) ---> l)
             sequentially)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP RIEMANN_LEBESGUE) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "1")) THEN
    SUBGOAL_THEN `&0 < e / &2` (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th))
    THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` (LABEL_TAC "2")) THEN
    EXISTS_TAC `N1 + 2 * N2 + 1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    DISJ_CASES_THEN SUBST1_TAC
     (ARITH_RULE `n = 2 * n DIV 2 \/ n = SUC(2 * n DIV 2)`) THEN
    REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0] THENL
     [MATCH_MP_TAC(REAL_ARITH `abs x < e / &2 ==> abs x < e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `abs(x - l) < e / &2 /\ abs y < e / &2 ==> abs((x + y) - l) < e`) THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x * y) <= abs(x) * &1 /\ abs(x) < e ==> abs(x * y) < e`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_ABS_POS] THEN
        SPEC_TAC(`SUC(2 * n DIV 2)`,`r:num`) THEN
        MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
        REWRITE_TAC[ADD1; trigonometric_set; REAL_ABS_DIV] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`;
                 SQRT_POS_LT; REAL_ARITH `&0 < &2 * x <=> &0 < x`; PI_POS] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1` THEN REWRITE_TAC[COS_BOUND; SIN_BOUND] THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= &1 * abs x`) THEN
        SUBST1_TAC(GSYM SQRT_1) THEN MATCH_MP_TAC SQRT_MONO_LE THEN
        MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN DISCH_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Express Fourier sum in terms of the special expansion at the origin.      *)
(* ------------------------------------------------------------------------- *)

let FOURIER_SUM_0 = prove
 (`!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     sum (0..n DIV 2)
         (\k. fourier_coefficient f (2 * k) * trigonometric_set (2 * k) (&0))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (2 * 0..2 * (n DIV 2) + 1)
                 (\k. fourier_coefficient f k * trigonometric_set k (&0))` THEN
  CONJ_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_SUPERSET THEN
    REWRITE_TAC[IN_NUMSEG; SUBSET; LE_0] THEN
    CONJ_TAC THENL [ARITH_TAC; GEN_TAC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `x <= 2 * n DIV 2 + 1 /\ ~(x <= n) ==> x = 2 * n DIV 2 + 1`));
    REWRITE_TAC[SUM_PAIR]] THEN
  REWRITE_TAC[trigonometric_set;  real_div; REAL_MUL_RZERO; SIN_0;
              REAL_MUL_LZERO; REAL_ADD_RID]);;

let FOURIER_SUM_0_EXPLICIT = prove
 (`!f n.
     sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
     (fourier_coefficient f 0 / sqrt(&2) +
      sum (1..n DIV 2) (\k. fourier_coefficient f (2 * k))) / sqrt pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FOURIER_SUM_0] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; real_div;
           REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
  REWRITE_TAC[MULT_CLAUSES; trigonometric_set;
              REAL_MUL_LZERO; COS_0; real_div] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[REAL_MUL_LID; SQRT_MUL; REAL_INV_MUL; GSYM REAL_MUL_ASSOC];
    REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[trigonometric_set; ARITH_RULE `2 * SUC i = 2 * i + 2`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COS_0; real_div; REAL_MUL_LID]]);;

let FOURIER_SUM_0_INTEGRALS = prove
 (`!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum (0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          (real_integral(real_interval[--pi,pi]) f / &2 +
           sum(1..n DIV 2) (\k. real_integral (real_interval[--pi,pi])
                                              (\x. cos(&k * x) * f x))) / pi`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FOURIER_SUM_0_EXPLICIT] THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
  REWRITE_TAC[trigonometric_set] THEN BINOP_TAC THENL
   [REWRITE_TAC[COS_0; REAL_MUL_LZERO; real_div; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
    REWRITE_TAC[REAL_ARITH `((a * b) * c) * d:real = b * a * c * d`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    SIMP_TAC[GSYM SQRT_MUL; REAL_POS; PI_POS_LE; REAL_LE_MUL] THEN
    REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC POW_2_SQRT THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN STRIP_TAC THEN
    REWRITE_TAC[trigonometric_set; ARITH_RULE `2 * SUC i = 2 * i + 2`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COS_0; real_div; REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(i * x) * i:real = x * i * i`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_POW_2] THEN
    MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[PI_POS_LE]]);;

let FOURIER_SUM_0_INTEGRAL = prove
 (`!f n.
      f absolutely_real_integrable_on real_interval[--pi,pi]
      ==> sum(0..n) (\k. fourier_coefficient f k * trigonometric_set k (&0)) =
          real_integral(real_interval[--pi,pi])
           (\x. (&1 / &2 + sum(1..n DIV 2) (\k. cos(&k * x))) * f x) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_0_INTEGRALS] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_SUM; FINITE_NUMSEG;
               FOURIER_PRODUCTS_INTEGRABLE_STRONG; real_div;
               GSYM REAL_INTEGRAL_ADD;
               GSYM REAL_INTEGRAL_RMUL; REAL_INTEGRABLE_RMUL; ETA_AX;
               REAL_INTEGRABLE_SUM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; SUM_RMUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* How Fourier coefficients behave under addition etc.                       *)
(* ------------------------------------------------------------------------- *)

let FOURIER_COEFFICIENT_ADD = prove
 (`!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x + g x) i =
                fourier_coefficient f i + fourier_coefficient g i`,
  SIMP_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE; REAL_ADD_LDISTRIB;
           REAL_INTEGRAL_ADD]);;

let FOURIER_COEFFICIENT_SUB = prove
 (`!f g i. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           g absolutely_real_integrable_on real_interval[--pi,pi]
           ==> fourier_coefficient (\x. f x - g x) i =
                fourier_coefficient f i - fourier_coefficient g i`,
  SIMP_TAC[fourier_coefficient; orthonormal_coefficient; l2product] THEN
  SIMP_TAC[TRIGONOMETRIC_SET_MUL_INTEGRABLE; REAL_SUB_LDISTRIB;
           REAL_INTEGRAL_SUB]);;

let FOURIER_COEFFICIENT_CONST = prove
 (`!c i. fourier_coefficient (\x. c) i =
         if i = 0 then c * sqrt(&2 * pi) else &0`,
  GEN_TAC THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
  REWRITE_TAC[fourier_coefficient; orthonormal_coefficient; l2product;
              trigonometric_set] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `0` HAS_REAL_INTEGRAL_COS_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt(&2 * pi)) * c` o
     MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    MATCH_MP_TAC(REAL_FIELD
     `&0 < s /\ s pow 2 = &2 * pi ==> &2 * pi * inv(s) * c = c * s`) THEN
    SIMP_TAC[SQRT_POW_2; REAL_LT_MUL; REAL_LE_MUL; REAL_POS; REAL_OF_NUM_LT;
             ARITH; SQRT_POS_LT; PI_POS; REAL_LT_IMP_LE];
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `n + 1` HAS_REAL_INTEGRAL_SIN_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt pi) * c` o
      MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_INTEGRAL_UNIQUE];
     X_GEN_TAC `n:num` THEN
    MP_TAC(ISPEC `n + 1` HAS_REAL_INTEGRAL_COS_NX) THEN
    DISCH_THEN(MP_TAC o SPEC `inv(sqrt pi) * c` o
      MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; REAL_MUL_LZERO] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_INTEGRAL_UNIQUE; REAL_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Shifting the origin for integration of periodic functions.                *)
(* ------------------------------------------------------------------------- *)

let REAL_PERIODIC_INTEGER_MULTIPLE = prove
 (`!f:real->real a.
        (!x. f(x + a) = f x) <=> (!x n. integer n ==> f(x + n * a) = f x)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; MESON_TAC[INTEGER_CLOSED; REAL_MUL_LID]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!x n. f(x + &n * a) = (f:real->real) x` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_SUC; REAL_ADD_RDISTRIB;
                    REAL_ADD_ASSOC; REAL_MUL_LID];
    REWRITE_TAC[INTEGER_CASES] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_ARITH `(x + -- &n * a) + &n * a = x`]]);;

let HAS_REAL_INTEGRAL_OFFSET = prove
 (`!f i a b c. (f has_real_integral i) (real_interval[a,b])
                ==> ((\x. f(x + c)) has_real_integral i)
                    (real_interval[a - c,b - c])`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `c:real`] o
   MATCH_MP (REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_AFFINITY)) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ; REAL_MUL_LID; REAL_INV_1] THEN
  REWRITE_TAC[REAL_ABS_1; REAL_MUL_LID; REAL_INV_1] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_REAL_INTERVAL; EXISTS_REFL;
              REAL_ARITH `x - c:real = y <=> x = y + c`] THEN
  REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f(x)) /\
        (f has_real_integral i) (real_interval[a,a+c])
        ==> (f has_real_integral i) (real_interval[b,b+c])`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
    (MP_TAC o SPEC `a - b:real` o MATCH_MP HAS_REAL_INTEGRAL_OFFSET) THEN
  REWRITE_TAC[REAL_ARITH
   `a - (a - b):real = b /\ (a + c) - (a - b) = b + c`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x + a - b:real`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ &0 <= c /\ a + c <= b /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  let tac =
    REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[a,b]` THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[real_integrable_on]; ASM_REAL_ARITH_TAC] in
  REPEAT STRIP_TAC THEN
  CONJUNCTS_THEN SUBST1_TAC
   (REAL_ARITH `a:real = (a + c) - c /\ b = (b + c) - c`) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_OFFSET THEN
  SUBGOAL_THEN
   `((f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[a,a+c]) /\
     (f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b])) /\
    ((f has_real_integral (real_integral(real_interval[a+c,b]) f))
     (real_interval[a+c,b]) /\
     (f has_real_integral (real_integral(real_interval[a,a+c]) f))
     (real_interval[b,b+c]))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN TRY tac THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_LEMMA THEN
    EXISTS_TAC `a:real` THEN ASM_REWRITE_TAC[] THEN tac;
    DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `a /\ b /\ c /\ d ==> e <=>
                  c /\ d ==> a /\ b ==> e`] HAS_REAL_INTEGRAL_COMBINE))) THEN
    REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    ASM_MESON_TAC[HAS_REAL_INTEGRAL_UNIQUE; REAL_ADD_SYM]]);;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\ abs(c) <= b - a /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i)
             (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`\x. (f:real->real)(--x)`; `i:real`;
                   `--b:real`; `--a:real`; `--c:real`]
          HAS_REAL_INTEGRAL_PERIODIC_OFFSET_POS) THEN
    ASM_REWRITE_TAC[REAL_NEG_ADD; HAS_REAL_INTEGRAL_REFLECT] THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    X_GEN_TAC `x:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--x + (a - b):real`) THEN
    REWRITE_TAC[REAL_ARITH `--(--a - --b):real = a - b`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let HAS_REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f i a b c.
        (!x. f(x + (b - a)) = f x) /\
        (f has_real_integral i) (real_interval[a,b])
        ==> ((\x. f(x + c)) has_real_integral i) (real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH `b <= a \/ a < b`) THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_NULL_EQ] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\x. f(x + (b - a) * frac(c / (b - a)))) has_real_integral i)
    (real_interval[a,b])`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET_WEAK THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `a < b /\ (b - a) * f < (b - a) * &1
      ==> abs(b - a) * f <= b - a`) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_LMUL_EQ] THEN
    ASM_REWRITE_TAC[real_abs; FLOOR_FRAC];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_REAL_INTEGRAL_EQ) THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN REWRITE_TAC[FRAC_FLOOR] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `a < b ==> x + (b - a) * (c / (b - a) - f) =
                (x + c) + --f * (b - a)`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[INTEGER_CLOSED; FLOOR]]);;

let REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[real_integrable_on] THEN
  MESON_TAC[HAS_REAL_INTEGRAL_PERIODIC_OFFSET]);;

let ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f absolutely_real_integrable_on real_interval[a,b]
        ==> (\x. f(x + c)) absolutely_real_integrable_on real_interval[a,b]`,
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `f:real->real` (SPEC_ALL REAL_INTEGRABLE_PERIODIC_OFFSET)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let REAL_INTEGRAL_PERIODIC_OFFSET = prove
 (`!f a b c.
        (!x. f(x + (b - a)) = f x) /\
        f real_integrable_on real_interval[a,b]
        ==> real_integral (real_interval[a,b]) (\x. f(x + c)) =
            real_integral (real_interval[a,b]) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL]);;

let FOURIER_OFFSET_TERM = prove
 (`!f n t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
           (!x. f(x + &2 * pi) = f x)
           ==> fourier_coefficient (\x. f(x + t)) (2 * n + 2) *
               trigonometric_set (2 * n + 2) (&0) =
               fourier_coefficient f (2 * n + 1) *
               trigonometric_set (2 * n + 1) t +
               fourier_coefficient f (2 * n + 2) *
               trigonometric_set (2 * n + 2) t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[trigonometric_set; fourier_coefficient;
              orthonormal_coefficient] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC; GSYM REAL_ADD_RDISTRIB] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; COS_0; REAL_MUL_RID] THEN
  REWRITE_TAC[l2product] THEN
  REWRITE_TAC[REAL_ARITH `(a * b) * c:real = b * a * c`] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; GSYM REAL_INTEGRAL_RMUL;
                FOURIER_PRODUCTS_INTEGRABLE_STRONG; GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a * b * c:real = (a * c) * b`] THEN
  REWRITE_TAC[REAL_MUL_SIN_SIN; REAL_MUL_COS_COS] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_ADD o
     rand o rand o snd) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
       EXISTS_TAC `(:real)` THEN
       REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
       MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
       MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
       REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
       SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
       REWRITE_TAC[trigonometric_set; real_div] THEN
       REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
       ASM_REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
       REPEAT STRIP_TAC THEN REWRITE_TAC[real_sub] THEN
       MATCH_MP_TAC(REAL_ARITH
        `abs x <= &1 /\ abs y <= &1 ==> abs((x + y) / &2) <= &1`) THEN
       REWRITE_TAC[SIN_BOUND; COS_BOUND; REAL_ABS_NEG]]);
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   `(cm - cp) / &2 * f + (cm + cp) / &2 * f = cm * f`] THEN
  MP_TAC(ISPECL
   [`\x. cos(&(n + 1) * (x - t)) * f x`;
    `real_integral (real_interval[--pi,pi])
                   (\x. cos(&(n + 1) * (x - t)) * f x)`;
    `--pi`; `pi`; `t:real`] HAS_REAL_INTEGRAL_PERIODIC_OFFSET) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. cos (&(n + 1) * (x - t)) * f x) real_integrable_on
    real_interval[--pi,pi]`
  MP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real)` THEN
      REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_ON_IMP_REAL_CONTINUOUS_ON THEN
      REWRITE_TAC[ETA_AX; IN_UNIV; REAL_DIFFERENTIABLE_ON_DIFFERENTIABLE] THEN
      SPEC_TAC(`n:num`,`n:num`) THEN MATCH_MP_TAC ODD_EVEN_INDUCT_LEMMA THEN
      REWRITE_TAC[trigonometric_set; real_div] THEN
      REPEAT STRIP_TAC THEN REAL_DIFFERENTIABLE_TAC;
      ASM_REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[COS_BOUND]];
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRAL] THEN DISCH_TAC] THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN ANTS_TAC THENL
   [REWRITE_TAC[REAL_ARITH
     `n * ((x + &2 * pi) - t) = (&2 * n) * pi + n * (x - t)`] THEN
    REWRITE_TAC[COS_ADD; SIN_NPI; COS_NPI; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_POW_NEG; REAL_MUL_LZERO; EVEN_MULT; ARITH] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_SUB_RZERO; REAL_MUL_LID];
    REWRITE_TAC[REAL_ARITH `(x + t) - t:real = x`] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = a * c * b`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN ASM_REWRITE_TAC[]]);;

let FOURIER_SUM_OFFSET = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..2*n) (\k. fourier_coefficient (\x. f (x + t)) k *
                             trigonometric_set k (&0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  BINOP_TAC THENL
   [REWRITE_TAC[fourier_coefficient; trigonometric_set; l2product;
                orthonormal_coefficient; REAL_MUL_LZERO; COS_0] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`\x:real. &1 / sqrt(&2 * pi) * f x`;
                  `--pi`; `pi`; `t:real`] REAL_INTEGRAL_PERIODIC_OFFSET) THEN
    ASM_SIMP_TAC[REAL_ARITH `pi - --pi = &2 * pi`; REAL_INTEGRABLE_LMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; SUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
  SUBGOAL_THEN `1..2*n = 2*0+1..(2*(n-1)+1)+1` SUBST1_TAC THENL
   [BINOP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; SUM_PAIR] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `(k + 1) + 1 = k + 2`] THEN
  ASM_SIMP_TAC[GSYM FOURIER_OFFSET_TERM] THEN
  REWRITE_TAC[trigonometric_set; REAL_MUL_RZERO; COS_0; SIN_0] THEN
  REAL_ARITH_TAC);;

let FOURIER_SUM_OFFSET_UNPAIRED = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k *
                             trigonometric_set k t) =
            sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                           trigonometric_set (2 * k) (&0))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(0..n) (\k. fourier_coefficient (\x. f (x + t)) (2 * k) *
                   trigonometric_set (2 * k) (&0) +
                   fourier_coefficient (\x. f (x + t)) (2 * k + 1) *
                   trigonometric_set (2 * k + 1) (&0))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_PAIR] THEN
    REWRITE_TAC[GSYM ADD1; MULT_CLAUSES; SUM_CLAUSES_NUMSEG; LE_0];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_EQ_ADD_LCANCEL_0]] THEN
  REWRITE_TAC[ADD1; trigonometric_set; real_div; REAL_MUL_RZERO] THEN
  REWRITE_TAC[SIN_0; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID]);;

(* ------------------------------------------------------------------------- *)
(* Express partial sums using Dirichlet kernel.                              *)
(* ------------------------------------------------------------------------- *)

let dirichlet_kernel = new_definition
 `dirichlet_kernel n x =
        if x = &0 then &n + &1 / &2
        else sin((&n + &1 / &2) * x) / (&2 * sin(x / &2))`;;

let DIRICHLET_KERNEL_0 = prove
 (`!x. abs(x) < &2 * pi ==> dirichlet_kernel 0 x = &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dirichlet_kernel] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_SYM; REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_FIELD `~(x = &0) ==> inv(&2 * x) * x = inv(&2)`) THEN
  DISCH_TAC THEN SUBGOAL_THEN `~(x * inv(&2) = &0)` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[] THEN MATCH_MP_TAC SIN_EQ_0_PI] THEN
  ASM_REAL_ARITH_TAC);;

let DIRICHLET_KERNEL_NEG = prove
 (`!n x. dirichlet_kernel n (--x) = dirichlet_kernel n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dirichlet_kernel; REAL_NEG_EQ_0] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_LNEG; real_div; SIN_NEG;
                  REAL_INV_NEG; REAL_NEG_NEG]);;

let DIRICHLET_KERNEL_CONTINUOUS_STRONG = prove
 (`!n. (dirichlet_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`,
  let lemma = prove
   (`f real_differentiable (atreal a) /\ f(a) = b
     ==> (f ---> b) (atreal a)`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      MATCH_MP REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL) THEN
    REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN ASM_MESON_TAC[]) in
  SIMP_TAC[REAL_OPEN_REAL_INTERVAL; IN_REAL_INTERVAL;
           REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[dirichlet_kernel] THEN ASM_CASES_TAC `x = &0` THENL
   [ALL_TAC;
    SUBGOAL_THEN
     `(\x. sin((&k + &1 / &2) * x) / (&2 * sin(x / &2)))
      real_continuous atreal x`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_DIV THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [CONJ_TAC THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REWRITE_TAC[NETLIMIT_ATREAL] THEN ASM_REAL_ARITH_TAC];
      ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
      REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `abs x` THEN
      ASM_REAL_ARITH_TAC]] THEN
  ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\x. sin((&k + &1 / &2) * x) / (&2 * sin(x / &2))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[EVENTUALLY_ATREAL; REAL_ARITH
     `&0 < abs(x - &0) <=> ~(x = &0)`] THEN
    EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  MATCH_MP_TAC LHOSPITAL THEN MAP_EVERY EXISTS_TAC
   [`\x. (&k + &1 / &2) * cos((&k + &1 / &2) * x)`;
    `\x. cos(x / &2)`; `&1`] THEN
  REWRITE_TAC[REAL_LT_01; REAL_SUB_RZERO] THEN REPEAT STRIP_TAC THENL
   [REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    REAL_DIFF_TAC THEN REAL_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC COS_POS_PI) THEN
    MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_RZERO; SIN_0] THEN REAL_DIFFERENTIABLE_TAC;
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; real_div; SIN_0] THEN
    REAL_DIFFERENTIABLE_TAC;
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM REAL_DIV_1] THEN
    MATCH_MP_TAC REALLIM_DIV THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC lemma THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO;
                real_div; COS_0; REAL_MUL_RID] THEN
    REAL_DIFFERENTIABLE_TAC]);;

let DIRICHLET_KERNEL_CONTINUOUS = prove
 (`!n. (dirichlet_kernel n) real_continuous_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval(--(&2 * pi),&2 * pi)` THEN
  REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS_STRONG] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. dirichlet_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_CLOSED_REAL_INTERVAL];
    MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[DIRICHLET_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_COMPACT_INTERVAL]]);;

let COSINE_SUM_LEMMA = prove
 (`!n x. (&1 / &2 + sum(1..n) (\k. cos(&k * x))) * sin(x / &2) =
         sin((&n + &1 / &2) * x) / &2`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(ARITH_RULE `n = 0 \/ 1 <= n`) THENL
   [ASM_REWRITE_TAC[REAL_ADD_LID; SUM_CLAUSES_NUMSEG; ARITH] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_ADD_RID; REAL_MUL_SYM];
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM SUM_RMUL] THEN
    REWRITE_TAC[REAL_MUL_COS_SIN; real_div; REAL_SUB_RDISTRIB] THEN
    SUBGOAL_THEN
     `!k x. &k * x + x * inv(&2) = (&(k + 1) * x - x * inv(&2))`
     (fun th -> REWRITE_TAC[th; SUM_DIFFS_ALT])
    THENL [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM real_div] THEN
    REWRITE_TAC[REAL_ARITH `&1 * x - x / &2 = x / &2`] THEN
    REWRITE_TAC[REAL_ARITH `(&n + &1) * x - x / &2 = (&n + &1 / &2) * x`] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN REAL_ARITH_TAC]);;

let DIRICHLET_KERNEL_COSINE_SUM = prove
 (`!n x. ~(x = &0) /\ abs(x) < &2 * pi
         ==> dirichlet_kernel n x = &1 / &2 + sum(1..n) (\k. cos(&k * x))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
  MATCH_MP_TAC(REAL_FIELD
    `~(y = &0) /\ z * y = x / &2 ==> x / (&2 * y) = z`) THEN
  REWRITE_TAC[COSINE_SUM_LEMMA] THEN
  MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN ASM_REAL_ARITH_TAC);;

let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL = prove
 (`!n. (dirichlet_kernel n has_real_integral pi) (real_interval[--pi,pi])`,
  GEN_TAC THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `\x. &1 / &2 + sum(1..n) (\k. cos(&k * x))` THEN
  EXISTS_TAC `{&0}` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
  SIMP_TAC[REAL_ARITH `&0 < pi /\ --pi <= x /\ x <= pi ==> abs(x) < &2 * pi`;
           DIRICHLET_KERNEL_COSINE_SUM; PI_POS] THEN
  SUBGOAL_THEN `pi = pi + sum(1..n) (\k. &0)` MP_TAC THENL
   [REWRITE_TAC[SUM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_ADD THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_ARITH  `pi = (&1 / &2) * (pi - --pi)`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_CONST THEN MP_TAC PI_POS THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `k:num` HAS_REAL_INTEGRAL_COS_NX) THEN ASM_SIMP_TAC[LE_1]]);;

let HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF = prove
 (`!n. (dirichlet_kernel n has_real_integral (pi / &2))
       (real_interval[&0,pi])`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`dirichlet_kernel n`; `--pi`; `pi`; `&0`; `pi`]
        REAL_INTEGRABLE_SUBINTERVAL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MESON_TAC[HAS_REAL_INTEGRAL_DIRICHLET_KERNEL; real_integrable_on];
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRAL] THEN DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [GSYM HAS_REAL_INTEGRAL_REFLECT]) THEN
  REWRITE_TAC[DIRICHLET_KERNEL_NEG; ETA_AX; REAL_NEG_0] THEN DISCH_TAC THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_integrable_on]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`dirichlet_kernel n`;
    `real_integral (real_interval [&0,pi]) (dirichlet_kernel n)`;
    `real_integral (real_interval [&0,pi]) (dirichlet_kernel n)`;
    `--pi`; `pi`; `&0`] HAS_REAL_INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_2] THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  MATCH_MP_TAC(REAL_ARITH `x = pi ==> x = &2 * y ==> y = pi / &2`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]);;

let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) =
            real_integral (real_interval[--pi,pi])
                          (\x. dirichlet_kernel n x * f(x + t)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET_UNPAIRED] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH] THEN
  REWRITE_TAC[trigonometric_set; COS_0; REAL_MUL_LZERO] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `fourier_coefficient (\x. f(x + t)) 0 * &1 / sqrt(&2 * pi) +
    sum (1..n) (\k. fourier_coefficient (\x. f(x + t)) (2 * k) / sqrt pi)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    SIMP_TAC[TRIGONOMETRIC_SET_EVEN; LE_1; REAL_MUL_RZERO; COS_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID;
              fourier_coefficient; orthonormal_coefficient;
              trigonometric_set; l2product] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [GSYM REAL_MUL_ASSOC; GSYM REAL_INTEGRAL_RMUL; GSYM REAL_INTEGRAL_ADD;
    ABSOLUTELY_INTEGRABLE_COS_PRODUCT;
    ABSOLUTELY_INTEGRABLE_SIN_PRODUCT;
    ABSOLUTELY_REAL_INTEGRABLE_LMUL;
    TRIGONOMETRIC_SET_MUL_ABSOLUTELY_INTEGRABLE;
    ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
    GSYM REAL_INTEGRAL_SUM; FINITE_NUMSEG;
    ABSOLUTELY_REAL_INTEGRABLE_RMUL;
    ABSOLUTELY_REAL_INTEGRABLE_SUM;
    ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN EXISTS_TAC `{}:real->bool` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_LZERO; COS_0; REAL_ARITH
   `a * b * c * b:real = (a * c) * b pow 2`] THEN
  SIMP_TAC[REAL_POW_INV; SQRT_POW_2; REAL_LE_MUL; REAL_POS; PI_POS_LE;
           REAL_LE_INV_EQ] THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_ARITH
   `d * f * i = (&1 * f) * inv(&2) * i + y <=> i * f * (d - &1 / &2) = y`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(1..n) (\k. inv pi * f(x + t) * cos(&k * x))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_ARITH `x - &1 / &2 = y <=> x = &1 / &2 + y`] THEN
    ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[dirichlet_kernel] THENL
     [REWRITE_TAC[REAL_MUL_RZERO; COS_0; SUM_CONST_NUMSEG; ADD_SUB] THEN
      REAL_ARITH_TAC;
      MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
      MATCH_MP_TAC(TAUT `a /\ b /\ ~d /\ (~c ==> e)
                         ==> (a /\ b /\ c ==> d) ==> e`) THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      ASM_SIMP_TAC[REAL_FIELD
      `~(y = &0) ==> (x / (&2 * y) = z <=> z * y = x / &2)`] THEN
      REWRITE_TAC[COSINE_SUM_LEMMA]];
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[TRIGONOMETRIC_SET_EVEN; LE_1] THEN
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC(REAL_RING
     `s * s:real = p ==> p * f * c = (c * s) * f * s`) THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN AP_TERM_TAC THEN
    SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; PI_POS_LE]]);;

let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x + t)))
             ---> pi * l) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL] THEN
  SUBGOAL_THEN `l = (l * pi) / pi`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th])
  THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SIMP_TAC[real_div; REALLIM_RMUL_EQ; PI_NZ; REAL_INV_EQ_0] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* A directly deduced sufficient condition for convergence at a point.       *)
(* ------------------------------------------------------------------------- *)

let SIMPLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (\x. (f(x + t) - f(t)) / sin(x / &2))
        absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f(t)) sequentially`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[REALLIM_NULL] THEN
  MP_TAC(ISPECL [`\x. (f:real->real)(x) - f(t)`; `t:real`; `&0`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL) THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
               ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
  MATCH_MP_TAC(TAUT `(a ==> c) /\ b ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FOURIER_COEFFICIENT_SUB; FOURIER_COEFFICIENT_CONST;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REALLIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
    MATCH_MP_TAC(REAL_ARITH
     `s:real = u /\ ft * t = x ==> (f0 - ft) * t + s = (f0 * t + u) - x`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LE_1; ARITH; REAL_SUB_RZERO];
      REWRITE_TAC[trigonometric_set; REAL_MUL_LZERO; COS_0] THEN
      MATCH_MP_TAC(REAL_FIELD `&0 < s ==> (f * s) * &1 / s = f`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN MP_TAC PI_POS THEN REAL_ARITH_TAC];
    MP_TAC(ISPECL [`\x. (f:real->real)(x) - f(t)`; `t:real`; `&0`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL) THEN
    MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
          ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    SUBGOAL_THEN
     `!n. real_integral (real_interval [--pi,pi])
                        (\x. dirichlet_kernel n x * (f(x + t) - f(t))) =
          real_integral (real_interval [--pi,pi])
                        (\x. sin((&n + &1 / &2) * x) *
                             inv(&2) * (f(x + t) - f(t)) / sin(x / &2))`
     (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A more natural sufficient Hoelder condition at a point.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_SIN_X2_ZEROS = prove
 (`{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`,
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_ELIM_THM; SIN_EQ_0; REAL_ARITH
   `y / &2 = n * pi <=> &2 * pi * n = y`] THEN
  REWRITE_TAC[PI_NZ; REAL_RING
   `&2 * pi * m = &2 * pi * n <=> pi = &0 \/ m = n`] THEN
  MESON_TAC[IN]);;

let HOELDER_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f d M a t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ &0 < a /\
        (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t) rpow a)
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLE_FOURIER_CONVERGENCE_PERIODIC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
    `?e. &0 < e /\
         !x. abs(x) < e
             ==> abs((f (x + t) - f t) / sin (x / &2))
                 <= &4 * abs M * abs(x) rpow (a - &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(REAL_DIFF_CONV
     `((\x. sin(x / &2)) has_real_derivative w) (atreal (&0))`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COS_0; REAL_MUL_RID] THEN
    REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL; REALLIM_ATREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `&1 / &4`) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[SIN_0; REAL_SUB_RZERO] THEN DISCH_THEN
     (X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
    EXISTS_TAC `min d e:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    ASM_CASES_TAC `sin(x / &2) = &0` THENL
     [ONCE_REWRITE_TAC[real_div] THEN ASM_REWRITE_TAC[REAL_INV_0] THEN
      REWRITE_TAC[GSYM REAL_ABS_RPOW; GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_SUB_REFL; REAL_ADD_LID;
                      REAL_MUL_LZERO] THEN
      REWRITE_TAC[GSYM REAL_ABS_RPOW; GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (REAL_ARITH
     `abs(x - &1 / &2) < &1 / &4 ==> &1 / &4 <= abs(x)`)) THEN
    SUBGOAL_THEN
     `abs((f(x + t) - f t) / sin (x / &2)) =
      abs(inv(sin(x / &2) / x)) * abs(f(x + t) - f t) / abs(x)`
    SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_INV] THEN
      UNDISCH_TAC `~(x = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_ABS_POS; REAL_LE_DIV] THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ABS_INV] THEN
      SUBST1_TAC(REAL_ARITH `&4 = inv(&1 / &4)`) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; GSYM REAL_ABS_NZ; GSYM REAL_MUL_ASSOC] THEN
      GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM REAL_POW_1] THEN
      ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD; GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC[REAL_ARITH `a - &1 + &1 = a`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `M * abs((x + t) - t) rpow a` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_ARITH `(x + t) - t:real = x`] THEN
        REWRITE_TAC[GSYM REAL_ABS_RPOW] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\x. inv(sin(x / &2)))
                (real_interval[--pi,pi] DIFF real_interval(--e,e)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        DISCH_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN
      SIMP_TAC[REAL_CLOSED_DIFF; REAL_CLOSED_REAL_INTERVAL;
               REAL_OPEN_REAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET_DIFF]];
    SIMP_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real. max (B * abs(f(x + t) - f t))
                           ((&4 * abs M) * abs(x) rpow (a - &1))` THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST];
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[REAL_SIN_X2_ZEROS] THEN
      MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
      MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MAX THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_LMUL;
       ABSOLUTELY_REAL_INTEGRABLE_ABS;
       ABSOLUTELY_REAL_INTEGRABLE_SUB; ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
    MP_TAC(ISPECL
     [`\x. inv(a) * x rpow a`; `\x. x rpow (a - &1)`; `&0`; `pi`]
     REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
    REWRITE_TAC[PI_POS_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_ON_LMUL THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        REAL_DIFF_TAC THEN
        MAP_EVERY UNDISCH_TAC [`&0 < a`; `&0 < x`] THEN CONV_TAC REAL_FIELD];
      DISCH_THEN(ASSUME_TAC o MATCH_MP HAS_REAL_INTEGRAL_INTEGRABLE)] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE THEN
    SIMP_TAC[RPOW_POS_LE; REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[REAL_NEG_LE0; PI_POS_LE] THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
      REWRITE_TAC[REAL_ABS_NEG; REAL_NEG_NEG; REAL_NEG_0];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_INTEGRABLE_EQ)) THEN
    SIMP_TAC[IN_REAL_INTERVAL; real_abs];
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_CASES_TAC `abs(x) < e` THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= b ==> x <= max a b`) THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC];
      MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= max a b`) THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM real_div] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* In particular, a Lipschitz condition at the point.                        *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f d M t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> abs(f x - f t) <= M * abs(x - t))
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HOELDER_FOURIER_CONVERGENCE_PERIODIC THEN
  MAP_EVERY EXISTS_TAC [`d:real`; `M:real`; `&1`] THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* In particular, if left and right derivatives both exist.                  *)
(* ------------------------------------------------------------------------- *)

let BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t within {x | t < x}) /\
         f real_differentiable (atreal t within {x | x < t})
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[real_differentiable; HAS_REAL_DERIVATIVE_WITHINREAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `B1:real` (LABEL_TAC "1"))
   (X_CHOOSE_THEN `B2:real` (LABEL_TAC "2"))) THEN
  MATCH_MP_TAC LIPSCHITZ_FOURIER_CONVERGENCE_PERIODIC THEN
  REMOVE_THEN "1" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  REMOVE_THEN "2" (MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[IN_ELIM_THM; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  MAP_EVERY EXISTS_TAC [`min d1 d2:real`; `abs B1 + abs B2 + &1`] THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC (REAL_ARITH `x = t \/ t < x \/ x < t`)
  THENL
   [ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM; REAL_MUL_RZERO; REAL_LE_REFL];
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_ABS_DIV;
                 REAL_ARITH `t < x ==> &0 < abs(x - t)`] THEN
    REMOVE_THEN "1" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_ABS_DIV;
                 REAL_ARITH `x < t ==> &0 < abs(x - t)`] THEN
    REMOVE_THEN "2" (MP_TAC o SPEC `x:real`) THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* And in particular at points where the function is differentiable.         *)
(* ------------------------------------------------------------------------- *)

let DIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC = prove
 (`!f t. f absolutely_real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f(x)) /\
         f real_differentiable (atreal t)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> f t) sequentially`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC BIDIFFERENTIABLE_FOURIER_CONVERGENCE_PERIODIC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  UNDISCH_TAC `f real_differentiable (atreal t)` THEN
  REWRITE_TAC[real_differentiable] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[HAS_REAL_DERIVATIVE_ATREAL_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Use reflection to halve the region of integration.                        *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED = prove
 (`!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[absolutely_real_integrable_on] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
    REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]]);;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART = prove
 (`!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. dirichlet_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. dirichlet_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP
  ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c) /\ (a /\ b /\ c ==> d /\ e)
    ==> a /\ b /\ c /\ d /\ e`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[--pi,pi]` THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
             ABSOLUTELY_REAL_INTEGRABLE_ADD;
             ABSOLUTELY_REAL_INTEGRABLE_SUB]]);;

let FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF = prove
 (`!f n t.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> sum(0..2*n) (\k. fourier_coefficient f k * trigonometric_set k t) -
            l =
            real_integral (real_interval[&0,pi])
                          (\x. dirichlet_kernel n x *
                               ((f(t + x) + f(t - x)) - &2 * l)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL] THEN
  MATCH_MP_TAC(MATCH_MP (REAL_FIELD
   `&0 < pi ==> x = y + pi * l ==> x / pi - l = y / pi`) PI_POS) THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
               ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[MESON[REAL_ADD_SYM]
   `dirichlet_kernel n x * f(x + t) = dirichlet_kernel n x * f(t + x)`] THEN
  REWRITE_TAC[DIRICHLET_KERNEL_NEG; GSYM real_sub] THEN
  MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF) THEN
  DISCH_THEN(MP_TAC o SPEC `&2 * l` o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
  REWRITE_TAC[REAL_ARITH `pi / &2 * &2 * l = pi * l`] THEN
  DISCH_THEN(SUBST1_TAC o GSYM o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_EQ_SUB_RADD] THEN
  REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(GSYM REAL_INTEGRAL_SUB) THEN
  MP_TAC(GEN `c:real` (ISPECL [`f:real->real`; `n:num`; `pi`; `c:real`]
        ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART)) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; FORALL_AND_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_ADD_LDISTRIB;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;

let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  GEN_REWRITE_TAC LAND_CONV [REALLIM_NULL] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_RMUL_EQ THEN
  MP_TAC PI_POS THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Localization principle: convergence only depends on values "nearby".      *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_LOCALIZATION_INTEGRAL = prove
 (`!d f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ (!x. abs(x) < d ==> f x = g x)
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * g(x)))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x * f(x)) -
        real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x * g(x)) =
        real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x *
                           (if abs(x) < d then &0 else f(x) - g(x)))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 GSYM REAL_INTEGRAL_SUB] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `{}:real->bool` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN AP_TERM_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_ARITH `&0 = x - y <=> x = y`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. real_integral (real_interval[--pi,pi])
                      (\x. dirichlet_kernel n x *
                           (if abs x < d then &0 else f(x) - g(x))) =
        real_integral (real_interval[--pi,pi])
                      (\x. sin((&n + &1 / &2) * x) *
                           inv(&2) *
                           (if abs x < d then &0 else f(x) - g(x)) /
                           sin(x / &2))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
    EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
    REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[dirichlet_kernel] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_AC];
    ALL_TAC] THEN
  MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
  SUBGOAL_THEN `real_bounded (IMAGE (\x. inv(sin(x / &2)))
                (real_interval[--pi,pi] DIFF real_interval(--d,d)))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_DIFF; IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_CONTINUOUS_INV THEN REWRITE_TAC[NETLIMIT_ATREAL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        DISCH_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
        ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_COMPACT_EQ_BOUNDED_CLOSED] THEN
      SIMP_TAC[REAL_CLOSED_DIFF; REAL_CLOSED_REAL_INTERVAL;
               REAL_OPEN_REAL_INTERVAL] THEN
      MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET_DIFF]];
    SIMP_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE; IN_REAL_INTERVAL; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC)] THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real. B * abs(f(x) - g(x))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      ASM_SIMP_TAC[INTEGRABLE_IMP_REAL_MEASURABLE; REAL_MEASURABLE_ON_0;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB] THEN
      SUBGOAL_THEN `{x | abs x < d} = real_interval(--d,d)`
       (fun th -> REWRITE_TAC[th; REAL_LEBESGUE_MEASURABLE_INTERVAL]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      SUBGOAL_THEN `{x | sin(x / &2) = &0} = IMAGE (\n. &2 * pi * n) integer`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
        REWRITE_TAC[IN_ELIM_THM; SIN_EQ_0; REAL_ARITH
         `y / &2 = n * pi <=> &2 * pi * n = y`] THEN
        REWRITE_TAC[PI_NZ; REAL_RING
          `&2 * pi * m = &2 * pi * n <=> pi = &0 \/ m = n`] THEN
        MESON_TAC[IN];
        MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]]];
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LMUL THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ABS;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB];
    X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
    STRIP_TAC THEN COND_CASES_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ONCE_REWRITE_TAC[real_div] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC]]);;

let RIEMANN_LOCALIZATION_INTEGRAL_RANGE = prove
 (`!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[--pi,pi])
                                (\x. dirichlet_kernel n x * f(x)) -
                  real_integral (real_interval[--d,d])
                                (\x. dirichlet_kernel n x * f(x)))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPECL[`d:real`; `f:real->real`;
           `\x. if x IN real_interval[--d,d] then f x else &0`]
     RIEMANN_LOCALIZATION_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV] THEN
      REWRITE_TAC[MESON[] `(if p then if q then x else y else y) =
                           (if p /\ q then x else y)`] THEN
      REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV; GSYM IN_INTER] THEN
      REWRITE_TAC[INTER; IN_REAL_INTERVAL] THEN
      ASM_SIMP_TAC[REAL_ARITH
       `&0 < d /\ d <= pi
        ==> ((--pi <= x /\ x <= pi) /\ --d <= x /\ x <= d <=>
             --d <= x /\ x <= d)`] THEN
      REWRITE_TAC[GSYM real_interval] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL)) THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    REWRITE_TAC[MESON[REAL_MUL_RZERO]
     `a * (if p then b else &0) = if p then a * b else &0`] THEN
    SUBGOAL_THEN `real_interval[--d,d] SUBSET real_interval[--pi,pi]`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL_RESTRICT th])]]);;

let RIEMANN_LOCALIZATION = prove
 (`!t d c f g.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        g absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ (!x. g(x + &2 * pi) = g(x)) /\
        &0 < d /\ (!x. abs(x - t) < d ==> f x = g x)
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> c) sequentially <=>
             ((\n. sum (0..n)
                       (\k. fourier_coefficient g k * trigonometric_set k t))
              ---> c) sequentially)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FOURIER_SUM_LIMIT_DIRICHLET_KERNEL] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC RIEMANN_LOCALIZATION_INTEGRAL THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Localize the earlier integral.                                            *)
(* ------------------------------------------------------------------------- *)

let RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF = prove
 (`!d f.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        &0 < d /\ d <= pi
        ==> ((\n. real_integral (real_interval[&0,pi])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))) -
                  real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x * (f(x) + f(--x))))
             ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN MP_TAC
   (SPECL [`d:real`; `f:real->real`] RIEMANN_LOCALIZATION_INTEGRAL_RANGE) THEN
  MP_TAC(GEN `n:num` (ISPECL [`f:real->real`; `n:num`]
    ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. (\x. dirichlet_kernel n x * f x) absolutely_real_integrable_on
        real_interval[--d,d]`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL) o SPEC `n:num`) THEN
    REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[DIRICHLET_KERNEL_NEG; GSYM REAL_ADD_LDISTRIB]]);;

let FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. dirichlet_kernel n x *
                                     ((f(t + x) + f(t - x)) - &2 * l)))
             ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_HALF] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN
  REWRITE_TAC[REAL_ARITH `(x + y) - &2 * l = (x - l) + (y - l)`] THEN
  MP_TAC(MESON[real_sub] `!x. (f:real->real)(t - x) = f(t + --x)`) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
   MATCH_MP_TAC RIEMANN_LOCALIZATION_INTEGRAL_RANGE_HALF THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`]);;

(* ------------------------------------------------------------------------- *)
(* Make a harmless simplifying tweak to the Dirichlet kernel.                *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND = prove
 (`!f n s. real_integral s (\x. dirichlet_kernel n x * f x) =
           real_integral s (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) *
                                f x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
  EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  SIMP_TAC[IN_DIFF; IN_SING; dirichlet_kernel]);;

let REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND = prove
 (`!f n s. (\x. dirichlet_kernel n x * f x) real_integrable_on s <=>
           (\x. sin((&n + &1 / &2) * x) / (&2 * sin(x / &2)) * f x)
           real_integrable_on s`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC REAL_INTEGRABLE_SPIKE THEN
  EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
  SIMP_TAC[IN_DIFF; IN_SING; dirichlet_kernel]);;

let FOURIER_SUM_LIMIT_SINE_PART = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\ &0 < d /\ d <= pi
        ==> (((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k t))
              ---> l) sequentially <=>
            ((\n. real_integral (real_interval[&0,d])
                                (\x. sin((&n + &1 / &2) * x) *
                                     ((f(t + x) + f(t - x)) - &2 * l) / x))
             ---> &0) sequentially)`,
  let lemma0 = prove
   (`!x. abs(sin(x) - x) <= abs(x) pow 3`,
    GEN_TAC THEN MP_TAC(ISPECL [`0`; `Cx x`] TAYLOR_CSIN) THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM CX_SIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_DIV_1; IM_CX] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; COMPLEX_NORM_CX; REAL_ABS_0] THEN
    REWRITE_TAC[REAL_EXP_0; REAL_MUL_LID] THEN REAL_ARITH_TAC) in
  let lemma1 = prove
   (`!x. ~(x = &0) ==> abs(sin(x) / x - &1) <= x pow 2`,
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs x` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL; GSYM(CONJUNCT2 real_pow)] THEN
    ASM_REWRITE_TAC[GSYM REAL_ABS_NZ; ARITH] THEN
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL; REAL_MUL_RID] THEN
    REWRITE_TAC[lemma0]) in
  let lemma2 = prove
   (`!x. abs(x) <= &1 / &2  ==> abs(x) / &2 <= abs(sin x)`,
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `x:real` lemma0) THEN
    MATCH_MP_TAC(REAL_ARITH
      `&4 * x3 <= abs x ==> abs(s - x) <= x3 ==> abs(x) / &2 <= abs s`) THEN
    REWRITE_TAC[REAL_ARITH
     `&4 * x pow 3 <= x <=> x * x pow 2 <= x * (&1 / &2) pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
    ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!x. ~(x = &0) /\ abs x <= &1 / &2
         ==> abs(inv(sin x) - inv x) <= &2 * abs x`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `abs(sin x)` THEN
    REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ASM_CASES_TAC `sin x = &0` THENL
     [MP_TAC(SPEC `x:real` SIN_EQ_0_PI) THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_SUB_LDISTRIB; REAL_MUL_RINV] THEN
      REWRITE_TAC[REAL_ARITH `abs(&1 - s * inv x) = abs(s / x - &1)`] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(x:real) pow 2` THEN
      ASM_SIMP_TAC[lemma1] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      MP_TAC(ISPEC `x:real` lemma2) THEN ASM_REAL_ARITH_TAC]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t:real`; `l:real`; `d:real`]
        FOURIER_SUM_LIMIT_DIRICHLET_KERNEL_PART) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
        ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN EXISTS_TAC
   `\n. real_integral (real_interval[&0,d])
                      (\x. sin((&n + &1 / &2) * x) *
                           (inv(&2 * sin(x / &2)) - inv x) *
                           ((f(t + x) + f(t - x)) - &2 * l))` THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_INTEGRAL_DIRICHLET_KERNEL_MUL_EXPAND] THEN
    REWRITE_TAC[REAL_ARITH
     `a * (inv y - inv x) * b:real = a / y * b - a / x * b`] THEN
    REWRITE_TAC[REAL_ARITH `sin(y) * (a - b) / x = sin(y) / x * (a - b)`] THEN
    MATCH_MP_TAC REAL_INTEGRAL_SUB THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_INTEGRABLE_DIRICHLET_KERNEL_MUL_EXPAND] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
      [ALL_TAC; REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `\x. dirichlet_kernel n x * (&2 * sin(x / &2)) / x *
                      ((f(t + x) + f(t - x)) - &2 * l)` THEN
      EXISTS_TAC `{&0}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN
        REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL; REAL_MUL_ASSOC] THEN
        STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_REWRITE_TAC[dirichlet_kernel] THEN
        MATCH_MP_TAC(REAL_FIELD
         `~(x = &0) /\ ~(y = &0) ==> a / x = a / (&2 * y) * (&2 * y) / x`) THEN
        MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
        ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                     ABSOLUTELY_REAL_INTEGRABLE_SUB;
                     ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
          REWRITE_TAC[REAL_NEGLIGIBLE_SING; SING_GSPEC] THEN
          CONJ_TAC THEN MATCH_MP_TAC
            REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
          REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
          REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
          REPEAT STRIP_TAC THEN
          MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
          MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
          REAL_DIFFERENTIABLE_TAC;
          ALL_TAC]]] THEN
    SUBGOAL_THEN `real_bounded (IMAGE (\x. &1 + (x / &2) pow 2)
                                      (real_interval[--pi,pi]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[REAL_COMPACT_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      ASM_CASES_TAC `x = &0` THENL
       [ASM_REWRITE_TAC[real_div; REAL_INV_0; REAL_MUL_RID] THEN
        ASM_REAL_ARITH_TAC;
        REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH
         `abs(z - &1) <= y ==> abs(&1 + y) <= B ==> abs(z) <= B`) THEN
        ASM_SIMP_TAC[REAL_FIELD
          `~(x = &0) ==> (&2 * y) / x = y / (x / &2)`] THEN
        MATCH_MP_TAC lemma1 THEN ASM_REAL_ARITH_TAC]];

    SUBGOAL_THEN `real_interval[&0,d] SUBSET real_interval[--pi,pi]`
    MP_TAC THENL
     [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(fun th -> REWRITE_TAC
       [GSYM(MATCH_MP REAL_INTEGRAL_RESTRICT th)])] THEN
    REWRITE_TAC[MESON[REAL_MUL_LZERO; REAL_MUL_RZERO]
     `(if p x then a x * b x * c x else &0) =
      a x * (if p x then b x else &0) * c x`] THEN
    MATCH_MP_TAC RIEMANN_LEBESGUE_SIN_HALF THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_0; SET_RULE `{x | x IN s} = s`;
                  REAL_LEBESGUE_MEASURABLE_INTERVAL] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_SUB THEN CONJ_TAC THEN
      GEN_REWRITE_TAC (LAND_CONV) [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
        MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
        REAL_DIFFERENTIABLE_TAC;
        REWRITE_TAC[REAL_ARITH `&2 * x = &0 <=> x = &0`] THEN
        REWRITE_TAC[REAL_SIN_X2_ZEROS] THEN
        MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN REWRITE_TAC[COUNTABLE_INTEGER]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `real_bounded(IMAGE (\x. inv (&2 * sin (x / &2)) - inv x)
                         (real_interval[--pi,-- &1] UNION
                          real_interval[&1,pi]))`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
      MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
      SIMP_TAC[REAL_COMPACT_INTERVAL; REAL_COMPACT_UNION] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC THEN MP_TAC(ISPEC `x / &2` SIN_EQ_0_PI) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNION]) THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[IN_REAL_INTERVAL; IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `max B (&2)` THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `abs(x) <= &1` THENL
     [ALL_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= B ==> x <= max B C`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC] THEN
    ASM_CASES_TAC `x = &0` THENL
     [ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_INV_0; SIN_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(is - &2 * ix) <= &1 ==> abs(inv(&2) * is - ix) <= max B (&2)`) THEN
    REWRITE_TAC[GSYM real_div] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
     [GSYM REAL_INV_DIV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * abs(x / &2)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC lemma3; ASM_REAL_ARITH_TAC] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Dini's test.                                                              *)
(* ------------------------------------------------------------------------- *)

let FOURIER_DINI_TEST = prove
 (`!f t l d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x) /\
        &0 < d /\
        (\x. abs((f(t + x) + f(t - x)) - &2 * l) / x)
        real_integrable_on real_interval[&0,d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k t))
             ---> l) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `t:real`; `l:real`; `pi`]
                FOURIER_SUM_LIMIT_SINE_PART) THEN
  ASM_REWRITE_TAC[PI_POS; REAL_LE_REFL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT) THEN
  REWRITE_TAC[real_continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `&0`) THEN
  ASM_SIMP_TAC[IN_REAL_INTERVAL; REAL_LE_REFL; REAL_LT_IMP_LE] THEN
  SIMP_TAC[REAL_INTEGRAL_NULL; REAL_LE_REFL] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ABBREV_TAC `dd = min d (min (k / &2) pi)` THEN
  DISCH_THEN(MP_TAC o SPEC `dd:real`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN ANTS_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd /\ dd <= d /\ dd <= pi /\ dd < k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
      ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
    real_interval[&0,dd]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`--pi`; `pi`] THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_SUB;
                   REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0:real`; `d:real`] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE
         [TAUT `p ==> q ==> r <=> q ==> p ==> r`]
                REAL_INTEGRABLE_SPIKE)) THEN
        EXISTS_TAC `{}:real->bool` THEN REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY] THEN
        SIMP_TAC[REAL_ABS_DIV; IN_REAL_INTERVAL; IN_DIFF] THEN
        SIMP_TAC[real_abs];
        REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
    real_interval[dd,pi]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
      MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
      SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
               REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
               REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
               REAL_CLOSED_UNIV];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `inv dd:real` THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[IN_REAL_INTERVAL; REAL_ABS_INV] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD;
                   ABSOLUTELY_REAL_INTEGRABLE_SUB;
                   ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!n. (\x. sin((&n + &1 / &2) * x) *
           ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
         real_interval[&0,dd]) /\
    (!n. (\x. sin((&n + &1 / &2) * x) *
          ((f(t + x) + f(t - x)) - &2 * l) / x) absolutely_real_integrable_on
         real_interval[dd,pi])`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
       REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
       REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
       REPEAT STRIP_TAC THEN
       MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
       MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
       REAL_DIFFERENTIABLE_TAC;
       REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
       EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]]);
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x. if abs x < dd then &0
                    else ((f:real->real)(t + x) - l) / x`
     RIEMANN_LEBESGUE_SIN_HALF) THEN
  SIMP_TAC[REAL_INTEGRAL_REFLECT_AND_ADD;
           ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
           FOURIER_PRODUCTS_INTEGRABLE_STRONG] THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV] THEN
    REWRITE_TAC[MESON[] `(if P x then if Q x then &0 else a x else &0) =
                         (if P x /\ ~Q x then a x else &0)`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[MESON[REAL_MUL_RZERO; REAL_MUL_LZERO]
    `(if P x /\ Q x then a x * b x else &0) =
     (if Q x then a x else &0) * (if P x then b x else &0)`] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_RESTRICT_UNIV;
                 ABSOLUTELY_REAL_INTEGRABLE_SUB;
                 ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_CASES THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_0] THEN CONJ_TAC THENL
       [REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
        REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_COMPL] THEN
        REWRITE_TAC[REAL_ARITH `abs x < d <=> --d < x /\ x < d`] THEN
        REWRITE_TAC[GSYM real_interval; REAL_LEBESGUE_MEASURABLE_INTERVAL];
        GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `inv x = &1 / x`] THEN
        MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN
        SIMP_TAC[REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET;
                 REAL_CLOSED_REAL_INTERVAL; REAL_CONTINUOUS_ON_CONST;
                 REAL_CONTINUOUS_ON_ID; SING_GSPEC; REAL_NEGLIGIBLE_SING;
                 REAL_CLOSED_UNIV]];
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      EXISTS_TAC `inv dd:real` THEN X_GEN_TAC `x:real` THEN
      REWRITE_TAC[REAL_NOT_LT] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_ABS_NUM;
                   REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_MUL_RNEG; SIN_NEG; REAL_MUL_LNEG] THEN
  REWRITE_TAC[GSYM real_sub; GSYM REAL_SUB_LDISTRIB] THEN
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then &0 else a) - (if p then &0 else --b) =
    (if p then &0 else a + b)`] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB] THEN REWRITE_TAC[GSYM real_div] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO]
   `s * (if p then &0 else y) = (if ~p then s * y else &0)`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[]
   `(if p then if q then x else &0 else &0) =
    (if p /\ q then x else &0)`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < dd /\ dd <= pi
    ==> ((&0 <= x /\ x <= pi) /\ ~(abs x < dd) <=>
         dd <= x /\ x <= pi)`] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[REAL_ARITH `(x - l) + (y - l) = (x + y) - &2 * l`] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `real_integral(real_interval[&0,dd]) f +
    real_integral(real_interval[dd,pi]) f =
    real_integral(real_interval[&0,pi]) f /\
    abs(real_integral(real_interval[&0,dd]) f) < e / &2
    ==> abs(real_integral(real_interval[dd,pi]) f - &0) < e / &2
        ==> abs(real_integral(real_interval[&0,pi]) f) < e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `dd:real` THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; REAL_LT_IMP_LE];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `abs x < e / &2 ==> abs y <= x ==> abs y < e / &2`)) THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
      MAP_EVERY EXISTS_TAC [`&0`; `d:real`] THEN
      ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      SIMP_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ARITH
        `&0 <= x ==> abs x = x`] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x * y <= y <=> x * y <= &1 * y`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS; SIN_BOUND]]]);;

(* ------------------------------------------------------------------------- *)
(* Convergence for functions of bounded variation.                           *)
(* ------------------------------------------------------------------------- *)

let REAL_INTEGRAL_SIN_OVER_X_BOUND = prove
 (`!a b c.
       &0 <= a /\ &0 < c
       ==> (\x. sin(c * x) / x) real_integrable_on real_interval[a,b] /\
           abs(real_integral (real_interval[a,b]) (\x. sin(c * x) / x)) <= &4`,
  let lemma0 = prove
   (`!a b. (\x. sin x) real_integrable_on (real_interval[a,b]) /\
           abs(real_integral (real_interval[a,b]) (\x. sin x)) <= &2`,
    REPEAT GEN_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MP_TAC(ISPECL [`\x. --(cos x)`; `\x. sin x`; `a:real`; `b:real`]
        REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        REAL_ARITH_TAC;
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
         `abs x <= &1 /\ abs y <= &1 ==> abs(--y - --x) <= &2`) THEN
        REWRITE_TAC[COS_BOUND]];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS]]) in
  let lemma1 = prove
   (`!a b. &0 < a
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b])
                                 (\x. sin x / x)) <= &4 / a`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MP_TAC(ISPECL [`\x. sin x`; `\x:real. --(inv x)`; `a:real`; `b:real`]
              REAL_SECOND_MEAN_VALUE_THEOREM_FULL) THEN
      ASM_REWRITE_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; lemma0] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_LE_NEG2; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `c:real`
         (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_NEG) THEN
        REWRITE_TAC[REAL_ARITH `--(--(inv y) * x):real = x / y`] THEN
        REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
        MATCH_MP_TAC(REAL_ARITH
         `inv b <= inv a /\ abs x <= inv a * &2 /\ abs y <= inv b * &2
          ==> abs(x + y) <= &4 / a`) THEN
        ASM_SIMP_TAC[REAL_LE_INV2; REAL_ABS_MUL] THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; lemma0] THEN
        ASM_REWRITE_TAC[real_abs; REAL_LE_REFL; REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`!x. &0 <= x ==> sin(x) <= x`,
    REPEAT STRIP_TAC THEN ASM_CASES_TAC `x <= &1` THENL
     [ALL_TAC; ASM_MESON_TAC[SIN_BOUNDS; REAL_LE_TOTAL; REAL_LE_TRANS]] THEN
    MP_TAC(ISPECL [`1`; `Cx x`] TAYLOR_CSIN) THEN
    CONV_TAC(TOP_DEPTH_CONV num_CONV) THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM CX_SIN] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_DIV; GSYM CX_NEG;
                GSYM CX_ADD; GSYM CX_SUB] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; IM_CX; REAL_ABS_0; REAL_EXP_0] THEN
    SIMP_TAC[REAL_POW_1; REAL_DIV_1; real_pow;
             REAL_MUL_LNEG; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH
     `e <= t ==> abs(sin x - (x + --t)) <= e ==> sin x <= x`) THEN
    ASM_REWRITE_TAC[real_abs; REAL_ARITH
     `x pow 5 / &24 <= x pow 3 / &6 <=>
      x pow 3 * x pow 2 <= x pow 3 * &2 pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC) in
  let lemma3 = prove
   (`!x. &0 <= x /\ x <= &2 ==> abs(sin x / x) <= &1`,
    GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
     [ASM_SIMP_TAC[real_div; REAL_MUL_RZERO; REAL_INV_0;
                   REAL_ABS_NUM; REAL_POS];
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID;
                   REAL_ARITH `&0 <= x /\ ~(x = &0) ==> &0 < abs x`] THEN
      MATCH_MP_TAC(REAL_ARITH `s <= x /\ &0 <= s ==> abs s <= abs x`) THEN
      ASM_SIMP_TAC[lemma2] THEN MATCH_MP_TAC SIN_POS_PI_LE THEN
      MP_TAC PI_APPROX_32 THEN ASM_REAL_ARITH_TAC]) in
  let lemma4 = prove
   (`!a b. &0 <= a /\ b <= &2
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b])
                                 (\x. sin x / x)) <= &2`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a <= b` THENL
     [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
        EXISTS_TAC `(\x. &1):real->real` THEN
        REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_MEASURABLE_ON_DIV THEN REPEAT CONJ_TAC THENL
           [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
            GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN REWRITE_TAC[lemma0];
            MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
            REWRITE_TAC[REAL_CONTINUOUS_ON_ID];
            REWRITE_TAC[SING_GSPEC; REAL_NEGLIGIBLE_SING]];
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC lemma3 THEN ASM_REAL_ARITH_TAC];
        DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `real_integral (real_interval [a,b]) (\x. &1)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
          ASM_REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC lemma3 THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN ASM_REAL_ARITH_TAC]];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                   REAL_ABS_NUM; REAL_POS]]) in
  let lemma5 = prove
   (`!a b. &0 <= a
           ==> (\x. sin x / x) real_integrable_on real_interval[a,b] /\
               abs(real_integral (real_interval[a,b]) (\x. sin x / x)) <= &4`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `b <= &2` THENL
     [ASM_MESON_TAC[lemma4; REAL_ARITH `x <= &2 ==> x <= &4`]; ALL_TAC] THEN
    ASM_CASES_TAC `&2 <= a` THENL
     [MP_TAC(SPECL [`a:real`; `b:real`] lemma1) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 <= a ==> &0 < a`] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    MP_TAC(ISPECL [`\x. sin x / x`; `a:real`; `b:real`; `&2`]
          REAL_INTEGRABLE_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[lemma4; REAL_LE_REFL];
        ASM_MESON_TAC[lemma1; REAL_ARITH `&0 < &2`]];
      DISCH_TAC] THEN
    MP_TAC(ISPECL [`\x. sin x / x`; `a:real`; `b:real`; `&2`]
          REAL_INTEGRAL_COMBINE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= &2 /\ abs(y) <= &2 ==> abs(x + y) <= &4`) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[lemma4; REAL_LE_REFL];
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `&2 = &4 / &2`] THEN
      ASM_MESON_TAC[lemma1; REAL_ARITH `&0 < &2`]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a <= b` THENL
   [MP_TAC(ISPECL [`c * a:real`; `c * b:real`] lemma5) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_REAL_INTEGRAL_INTEGRAL] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     HAS_REAL_INTEGRAL_STRETCH)) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_ADD_RID; REAL_SUB_RZERO] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP HAS_REAL_INTEGRAL_LMUL) THEN
    ASM_SIMP_TAC[IMAGE_STRETCH_REAL_INTERVAL; REAL_LE_INV_EQ; REAL_LT_IMP_LE;
      REAL_FIELD `&0 < c ==> inv c * c * a = a`; REAL_INV_MUL; real_div;
      REAL_FIELD `&0 < c ==> c * s * inv c * inv x = s * inv x`;
      REAL_FIELD `&0 < c ==> c * inv c * i = i /\ abs c = c`] THEN
    REWRITE_TAC[GSYM real_div; REAL_INTERVAL_EQ_EMPTY] THEN
    ASM_SIMP_TAC[GSYM REAL_NOT_LE; REAL_LE_LMUL_EQ] THEN
    REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ON_NULL; REAL_INTEGRAL_NULL; REAL_LT_IMP_LE;
                 REAL_ABS_NUM; REAL_POS]]);;

let FOURIER_JORDAN_BOUNDED_VARIATION = prove
 (`!f x d.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        &0 < d /\
        f has_bounded_real_variation_on real_interval[x - d,x + d]
        ==> ((\n. sum (0..n)
                      (\k. fourier_coefficient f k * trigonometric_set k x))
             ---> ((reallim (atreal x within {l | l <= x}) f +
                    reallim (atreal x within {r | r >= x}) f) / &2))
            sequentially`,
  let lemma = prove
   (`!f l d. &0 < d
             ==> ((f ---> l) (atreal (&0) within real_interval[&0,d]) <=>
                  (f ---> l) (atreal (&0) within {x | &0 <= x}))`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_TRANSFORM_WITHINREAL_SET THEN
    REWRITE_TAC[EVENTUALLY_ATREAL] THEN EXISTS_TAC `d:real` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC) in
  MAP_EVERY X_GEN_TAC [`f:real->real`; `t:real`; `d0:real`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `s = (reallim (atreal t within {l | l <= t}) f +
                   reallim (atreal t within {r | r >= t}) f) / &2` THEN
  MP_TAC(SPECL [`f:real->real`; `t:real`; `s:real`; `min d0 pi`]
        FOURIER_SUM_LIMIT_SINE_PART) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; PI_POS; REAL_ARITH `min d0 pi <= pi`] THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `h = \u. ((f:real->real)(t + u) + f(t - u)) - &2 * s` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN ABBREV_TAC `d = min d0 pi` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `h has_bounded_real_variation_on real_interval[&0,d]`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_BOUNDED_REAL_VARIATION_DARBOUX]) THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[HAS_BOUNDED_REAL_VARIATION_DARBOUX] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_REAL_INTERVAL] THEN
    MAP_EVERY X_GEN_TAC [`f1:real->real`; `f2:real->real`] THEN STRIP_TAC THEN
    EXISTS_TAC `\x. ((f1:real->real)(t + x) - f2(t - x)) - s` THEN
    EXISTS_TAC `\x. ((f2:real->real)(t + x) - f1(t - x)) + s` THEN
    ASM_REWRITE_TAC[REAL_ARITH `x - s <= y - s <=> x <= y`; REAL_LE_RADD] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `a <= a' /\ b' <= b ==> a - b <= a' - b'`) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h ---> &0) (atreal(&0) within {x | &0 <= x})`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[REAL_ARITH
     `(f' + f) - &2 * (l + l') / &2 = (f - l) + (f' - l')`] THEN
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `?l. (f ---> l) (atreal t within {l | l <= t})` MP_TAC
      THENL
       [MP_TAC(ISPECL [`f:real->real`; `t - d0:real`; `t + d0:real`; `t:real`]
         HAS_BOUNDED_REAL_VARIATION_LEFT_LIMIT) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `d1:real` (fun th ->
          EXISTS_TAC `min d0 d1` THEN
          CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th)) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        REWRITE_TAC[GSYM reallim] THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
         X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t - x:real` th)) THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
        REAL_ARITH_TAC];
      SUBGOAL_THEN
       `?l. (f ---> l) (atreal t within {r | r >= t})` MP_TAC
      THENL
       [MP_TAC(ISPECL [`f:real->real`; `t - d0:real`; `t + d0:real`; `t:real`]
         HAS_BOUNDED_REAL_VARIATION_RIGHT_LIMIT) THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real` THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN
        ASM_REWRITE_TAC[IN_REAL_INTERVAL; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `d1:real` (fun th ->
          EXISTS_TAC `min d0 d1` THEN
          CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th)) THEN
        ASM_REWRITE_TAC[REAL_LT_MIN] THEN
        MATCH_MP_TAC MONO_FORALL THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(MP_TAC o SELECT_RULE) THEN
        REWRITE_TAC[GSYM reallim] THEN
        REWRITE_TAC[REALLIM_WITHINREAL] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
        ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
         X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t + x:real` th)) THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k < d /\
        !n. (\x. sin ((&n + &1 / &2) * x) * h x / x)
            real_integrable_on real_interval[&0,k] /\
            abs(real_integral (real_interval[&0,k])
                              (\x. sin ((&n + &1 / &2) * x) * h x / x))
              <= e / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `?h1 h2.
         (!x y. x IN real_interval[&0,d] /\ y IN real_interval[&0,d] /\ x <= y
                ==> h1 x <= h1 y) /\
         (!x y. x IN real_interval[&0,d] /\ y IN real_interval[&0,d] /\ x <= y
                ==> h2 x <= h2 y) /\
         (h1 ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (h2 ---> &0) (atreal (&0) within {x | &0 <= x}) /\
         (!x. h x = h1 x - h2 x)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`h:real->real`; `&0`; `d:real`]
          HAS_BOUNDED_REAL_VARIATION_DARBOUX) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`h1:real->real`; `h2:real->real`] THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`h1:real->real`; `&0`; `d:real`; `&0`]
           INCREASING_RIGHT_LIMIT) THEN
      ASM_REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN
      MP_TAC(ISPECL [`h2:real->real`; `&0`; `d:real`; `&0`]
           INCREASING_RIGHT_LIMIT) THEN
      ASM_REWRITE_TAC[ENDS_IN_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
      ASM_SIMP_TAC[REAL_NOT_LT; REAL_LT_IMP_LE] THEN
      DISCH_THEN(X_CHOOSE_TAC `l':real`) THEN
      SUBGOAL_THEN `l':real = l` SUBST_ALL_TAC THENL
       [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
        MATCH_MP_TAC(ISPEC `atreal (&0) within {x | &0 <= x}`
          REALLIM_UNIQUE) THEN
        EXISTS_TAC `h:real->real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [W(MP_TAC o PART_MATCH (lhs o rand) TRIVIAL_LIMIT_WITHIN_REALINTERVAL o
            rand o snd) THEN
          REWRITE_TAC[is_realinterval; IN_ELIM_THM] THEN
          ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
          REWRITE_TAC[EXTENSION; NOT_FORALL_THM; IN_ELIM_THM; IN_SING] THEN
          EXISTS_TAC `&1` THEN REAL_ARITH_TAC;
          GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REALLIM_SUB THEN
          MAP_EVERY UNDISCH_TAC
           [`(h1 ---> l) (atreal(&0) within real_interval[&0,d])`;
            `(h2 ---> l') (atreal(&0) within real_interval[&0,d])`] THEN
          ASM_SIMP_TAC[lemma]];
        EXISTS_TAC `\x. (h1:real->real)(x) - l` THEN
        EXISTS_TAC `\x. (h2:real->real)(x) - l` THEN
        ASM_REWRITE_TAC[REAL_ARITH `x - l <= y - l <=> x <= y`] THEN
        ASM_REWRITE_TAC[GSYM REALLIM_NULL] THEN
        MAP_EVERY UNDISCH_TAC
         [`(h1 ---> l) (atreal(&0) within real_interval[&0,d])`;
          `(h2 ---> l) (atreal(&0) within real_interval[&0,d])`] THEN
        ASM_SIMP_TAC[lemma] THEN REPEAT DISCH_TAC THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?k. &0 < k /\ k < d /\ abs(h1 k) < e / &16 /\ abs(h2 k) < e / &16`
    MP_TAC THENL
     [UNDISCH_TAC `(h2 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
      UNDISCH_TAC `(h1 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &16`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `k1:real` STRIP_ASSUME_TAC)] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &16`) THEN ANTS_TAC THENL
       [ASM_REAL_ARITH_TAC;
        DISCH_THEN(X_CHOOSE_THEN `k2:real` STRIP_ASSUME_TAC)] THEN
      EXISTS_TAC `min d (min k1 k2) / &2` THEN
      REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`\x. sin((&n + &1 / &2) * x) / x`; `h1:real->real`;
                     `&0`; `k:real`; `&0`; `(h1:real->real) k`]
      REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
    ASM_SIMP_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LE_REFL; REAL_ADD_LID;
                 REAL_ARITH `&0 < &n + &1 / &2`; REAL_MUL_LZERO] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          UNDISCH_TAC `(h1 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
          REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
          DISCH_THEN(MP_TAC o SPEC `--((h1:real->real) x)`) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (MP_TAC o SPEC `min d (min x dd) / &2`)) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `h < &0 ==> h' <= h ==> ~(abs h' < --h)`));
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `h * s / x:real = s * h / x`] THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `c1:real` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`\x. sin((&n + &1 / &2) * x) / x`; `h2:real->real`;
                     `&0`; `k:real`; `&0`; `(h2:real->real) k`]
      REAL_SECOND_MEAN_VALUE_THEOREM_GEN_FULL) THEN
    ASM_SIMP_TAC[REAL_INTERVAL_EQ_EMPTY; REAL_NOT_LT; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LE_REFL; REAL_ADD_LID;
                 REAL_ARITH `&0 < &n + &1 / &2`; REAL_MUL_LZERO] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
        REPEAT STRIP_TAC THENL
         [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
          UNDISCH_TAC `(h2 ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
          REWRITE_TAC[REALLIM_WITHINREAL; IN_ELIM_THM; REAL_SUB_RZERO] THEN
          DISCH_THEN(MP_TAC o SPEC `--((h2:real->real) x)`) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          DISCH_THEN(X_CHOOSE_THEN `dd:real` MP_TAC) THEN
          DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
           (MP_TAC o SPEC `min d (min x dd) / &2`)) THEN
          REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `h < &0 ==> h' <= h ==> ~(abs h' < --h)`));
          ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [REAL_ARITH `h * s / x:real = s * h / x`] THEN
      REWRITE_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `c2:real` STRIP_ASSUME_TAC)] THEN
    REWRITE_TAC[REAL_ARITH
     `s * (h - h') / x:real = s * h / x - s * h' / x`] THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_SUB; REAL_INTEGRAL_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= e / &16 * &4 /\ abs(y) <= e / &16 * &4
      ==> abs(x - y) <= e / &2`) THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN
    ASM_SIMP_TAC[REAL_INTEGRAL_SIN_OVER_X_BOUND; REAL_LT_IMP_LE;
                 REAL_ARITH `&0 < &n + &1 / &2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->real`; `--pi`; `pi`; `t:real`]
      ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET) THEN
  ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_ADD_SYM] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [absolutely_real_integrable_on] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [GSYM REAL_INTEGRABLE_REFLECT] THEN
  REWRITE_TAC[GSYM absolutely_real_integrable_on; GSYM real_sub] THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\x. h x / x) absolutely_real_integrable_on real_interval[k,d]`
  ASSUME_TAC THENL
   [REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
      REWRITE_TAC[REAL_CONTINUOUS_WITHIN_ID] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_REAL_INTERVAL]) THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
      EXISTS_TAC `inv k:real` THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "h" THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
      REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `real_interval[--pi,pi]` THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_ADD] THEN
      REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\x. sin((&n + &1 / &2) * x) * h x / x) absolutely_real_integrable_on
        real_interval[k,d]`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
      REWRITE_TAC[REAL_CLOSED_UNIV; REAL_CLOSED_REAL_INTERVAL] THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_ATREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `&1` THEN REWRITE_TAC[SIN_BOUND]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\x. if k <= x /\ x <= d then h x / x else &0`
        RIEMANN_LEBESGUE_SIN_HALF) THEN
  REWRITE_TAC[absolutely_real_integrable_on] THEN
  REWRITE_TAC[MESON[REAL_ABS_NUM]
   `abs(if p then x else &0) = if p then abs x else &0`] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_UNIV; GSYM
                   REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[REAL_MUL_RZERO]
   `(if P then s * (if Q then a else &0) else &0) =
    (if P /\ Q then s * a else &0)`] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REWRITE_TAC[MESON[] `(if P then if Q then x else &0 else &0) =
                       (if P /\ Q then x else &0)`] THEN
  SUBGOAL_THEN `!x. (--pi <= x /\ x <= pi) /\ k <= x /\ x <= d <=>
                    k <= x /\ x <= d`
   (fun th -> REWRITE_TAC[th])
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; REAL_INTEGRAL_RESTRICT_UNIV;
              REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `n:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x + y = z ==> abs(x) <= e / &2 ==> abs(y) < e / &2 ==> abs(z) < e`) THEN
  REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC REAL_INTEGRAL_COMBINE THEN
  REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_INTEGRABLE_COMBINE THEN EXISTS_TAC `k:real` THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  ASM_REAL_ARITH_TAC);;

let FOURIER_JORDAN_BOUNDED_VARIATION_SIMPLE = prove
 (`!f x. f has_bounded_real_variation_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ((\n. sum (0..n)
                       (\k. fourier_coefficient f k * trigonometric_set k x))
              ---> ((reallim (atreal x within {l | l <= x}) f +
                     reallim (atreal x within {r | r >= x}) f) / &2))
             sequentially`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FOURIER_JORDAN_BOUNDED_VARIATION THEN
  EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [HAS_BOUNDED_REAL_VARIATION_DARBOUX]) THEN
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
    CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_INCREASING THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `!n. integer n
          ==> f has_bounded_real_variation_on
              real_interval [(&2 * n - &1) * pi,(&2 * n + &1) * pi]`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o SPEC `&2 * --n * pi` o
       MATCH_MP HAS_BOUNDED_REAL_VARIATION_TRANSLATION) THEN
      REWRITE_TAC[INTEGER_NEG; GSYM REAL_INTERVAL_TRANSLATION] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
       [REAL_PERIODIC_INTEGER_MULTIPLE]) THEN
      DISCH_THEN(MP_TAC o GEN `x:real` o SPECL [`x:real`; `--n:real`]) THEN
      ASM_REWRITE_TAC[REAL_ARITH `x + n * &2 * pi = &2 * n * pi + x`] THEN
      ASM_REWRITE_TAC[INTEGER_NEG] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[CONS_11; PAIR_EQ] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. f has_bounded_real_variation_on
          real_interval[--pi,&(2 * n + 1) * pi]`
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID] THEN
      MP_TAC(ISPECL [`f:real->real`; `--pi`; `&((2 + 2 * n) + 1) * pi`;
                     `&(2 * n + 1) * pi`]
        HAS_BOUNDED_REAL_VARIATION_ON_COMBINE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_ARITH `--pi = --(&1) * pi`] THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_ARITH
         `(&2 * n + &1) * pi = (&2 * (n + &1) - &1) * pi`] THEN
        REWRITE_TAC[REAL_ARITH
         `((&2 + &2 * n) + &1) * pi = (&2 * (n + &1) + &1) * pi`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[INTEGER_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!m n. f has_bounded_real_variation_on
            real_interval[--(&(2 * m + 1)) * pi,&(2 * n + 1) * pi]`
    ASSUME_TAC THENL
     [INDUCT_TAC THEN
      ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; REAL_MUL_LID; REAL_MUL_LNEG] THEN
      X_GEN_TAC `n:num` THEN
      MP_TAC(ISPECL [`f:real->real`; `--(&((2 + 2 * m) + 1) * pi)`;
                     `&(2 * n + 1) * pi`; `--(&(2 * m + 1) * pi)`]
        HAS_BOUNDED_REAL_VARIATION_ON_COMBINE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
        SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS; REAL_OF_NUM_LE] THEN
        REWRITE_TAC[REAL_LE_NEG2; REAL_ARITH `--a <= b <=> &0 <= a + b`] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
        REWRITE_TAC[REAL_ARITH
          `--(&2 * m + &1) = &2 * --(m + &1) + &1`] THEN
        REWRITE_TAC[REAL_ARITH
          `--((&2 + &2 * m) + &1) = &2 * --(m + &1) - &1`] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN SIMP_TAC[INTEGER_CLOSED]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `&2 * pi` REAL_ARCH) THEN
    ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `abs x + &3`) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC HAS_BOUNDED_REAL_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `real_interval[-- &(2 * N + 1) * pi,&(2 * N + 1) * pi]` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Cesaro summability of Fourier series using Fejer kernel.                  *)
(* ------------------------------------------------------------------------- *)

let fejer_kernel = new_definition
  `fejer_kernel n x = if n = 0 then &0
                      else sum(0..n-1) (\r. dirichlet_kernel r x) / &n`;;

let FEJER_KERNEL = prove
 (`fejer_kernel n x =
        if n = 0 then &0
        else if x = &0 then &n / &2
        else sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2)`,
  REWRITE_TAC[fejer_kernel; dirichlet_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[SUM_0] THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG;
                REWRITE_RULE[ETA_AX] SUM_NUMBERS] THEN
    ASM_SIMP_TAC[SUB_ADD; GSYM REAL_OF_NUM_SUB; LE_1; SUB_0] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
     [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_CASES_TAC `sin(x / &2) = &0` THENL
   [ASM_REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; real_div;
                    REAL_INV_0; SUM_0; REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(n = &0) /\ ~(s = &0) /\ &2 * s pow 2 * l = r
    ==> l / n = r / (&2 * n * s pow 2)`) THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_EQ; GSYM SUM_LMUL] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(s = &0) ==> &2 * s pow 2 * a / (&2 * s) = s * a`] THEN
  REWRITE_TAC[REAL_MUL_SIN_SIN] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 - (&n + &1 / &2) * x = --(&n * x)`;
              REAL_ARITH `x / &2 + (&n + &1 / &2) * x = (&n + &1) * x`] THEN
  REWRITE_TAC[real_div; SUM_RMUL; COS_NEG; REAL_OF_NUM_ADD] THEN
  REWRITE_TAC[SUM_DIFFS; LE_0; REAL_MUL_LZERO] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; REAL_SUB_COS] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_RZERO; real_div; REAL_MUL_AC] THEN
  REAL_ARITH_TAC);;

let FEJER_KERNEL_CONTINUOUS_STRONG = prove
 (`!n. (fejer_kernel n) real_continuous_on
       real_interval(--(&2 * pi),&2 * pi)`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[REAL_CONTINUOUS_ON_CONST] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_RMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; DIRICHLET_KERNEL_CONTINUOUS_STRONG]);;

let FEJER_KERNEL_CONTINUOUS = prove
 (`!n. (fejer_kernel n) real_continuous_on real_interval[--pi,pi]`,
  GEN_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `real_interval(--(&2 * pi),&2 * pi)` THEN
  REWRITE_TAC[FEJER_KERNEL_CONTINUOUS_STRONG] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC);;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL = prove
 (`!f n. f absolutely_real_integrable_on real_interval[--pi,pi]
         ==> (\x. fejer_kernel n x * f x)
             absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_IMP_REAL_MEASURABLE_ON_CLOSED_SUBSET THEN
    ASM_REWRITE_TAC[FEJER_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_CLOSED_REAL_INTERVAL];
    MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[FEJER_KERNEL_CONTINUOUS; ETA_AX;
                    REAL_COMPACT_INTERVAL]]);;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED = prove
 (`!f n c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x))
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[--pi,pi] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[absolutely_real_integrable_on] THEN
    ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
    REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
    REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
    ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
    REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST]]);;

let ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART = prove
 (`!f n d c.
        f absolutely_real_integrable_on real_interval [--pi,pi] /\
        (!x. f(x + &2 * pi) = f(x)) /\ d <= pi
        ==> (\x. fejer_kernel n x * f(t + x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * f(t - x))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * c)
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * (f(t + x) + f(t - x)))
            absolutely_real_integrable_on real_interval[&0,d] /\
            (\x. fejer_kernel n x * ((f(t + x) + f(t - x)) - c))
            absolutely_real_integrable_on real_interval[&0,d]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o MATCH_MP
  ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED) ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT
   `(a /\ b /\ c) /\ (a /\ b /\ c ==> d /\ e)
    ==> a /\ b /\ c /\ d /\ e`) THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `real_interval[--pi,pi]` THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN MP_TAC PI_POS THEN
    ASM_REAL_ARITH_TAC;
    SIMP_TAC[REAL_ADD_LDISTRIB; REAL_SUB_LDISTRIB;
             ABSOLUTELY_REAL_INTEGRABLE_ADD;
             ABSOLUTELY_REAL_INTEGRABLE_SUB]]);;

let FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF = prove
 (`!f n t.
     f absolutely_real_integrable_on real_interval[--pi,pi] /\
     (!x. f (x + &2 * pi) = f x) /\
     0 < n
     ==> sum(0..n-1) (\r. sum (0..2*r)
                              (\k. fourier_coefficient f k *
                                   trigonometric_set k t)) / &n - l =
         real_integral (real_interval[&0,pi])
                       (\x. fejer_kernel n x *
                            ((f(t + x) + f(t - x)) - &2 * l)) / pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LE_1; REAL_OF_NUM_EQ; REAL_FIELD
   `~(n = &0) ==> (x / n - l = y <=> x - n * l = n * y)`] THEN
  MP_TAC(ISPECL [`l:real`; `0`; `n - 1`] SUM_CONST_NUMSEG) THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1; SUB_0] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM SUM_SUB_NUMSEG] THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_DIRICHLET_KERNEL_HALF] THEN
  REWRITE_TAC[real_div; SUM_RMUL; REAL_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) REAL_INTEGRAL_SUM o lhand o snd) THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_DIRICHLET_KERNEL_REFLECTED_PART;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
               FINITE_NUMSEG; REAL_LE_REFL] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_LE_REFL;
               ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
               ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC REAL_INTEGRAL_EQ THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[fejer_kernel; LE_1] THEN MATCH_MP_TAC(REAL_FIELD
   `~(n = &0) ==> s * f = n * s / n * f`) THEN
  ASM_SIMP_TAC[LE_1; REAL_OF_NUM_EQ]);;

let FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF = prove
 (`!f t l.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f (x + &2 * pi) = f x)
        ==> (((\n. sum(0..n-1) (\r. sum (0..2*r)
                                        (\k. fourier_coefficient f k *
                                             trigonometric_set k t)) / &n)
               ---> l) sequentially <=>
             ((\n. real_integral (real_interval[&0,pi])
                                 (\x. fejer_kernel n x *
                                      ((f(t + x) + f(t - x)) - &2 * l)))
              ---> &0) sequentially)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM FOURIER_SUM_LIMIT_PAIR] THEN
  GEN_REWRITE_TAC LAND_CONV [REALLIM_NULL] THEN REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(MATCH_MP REALLIM_NULL_RMUL_EQ PI_NZ)] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EQ THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  ASM_SIMP_TAC[FOURIER_SUM_OFFSET_FEJER_KERNEL_HALF; LE_1] THEN
  ASM_SIMP_TAC[PI_POS; REAL_LT_IMP_NZ; REAL_DIV_RMUL; REAL_SUB_REFL]);;

let HAS_REAL_INTEGRAL_FEJER_KERNEL = prove
 (`!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi))
       (real_interval[--pi,pi])`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0] THEN
  SUBGOAL_THEN `pi = sum(0..n-1) (\r. pi) / &n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL
   [ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_ADD; LE_1; SUB_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN
    REWRITE_TAC[FINITE_NUMSEG; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL]]);;

let HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF = prove
 (`!n. (fejer_kernel n has_real_integral (if n = 0 then &0 else pi / &2))
       (real_interval[&0,pi])`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[fejer_kernel] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[HAS_REAL_INTEGRAL_0] THEN
  SUBGOAL_THEN `pi / &2 = sum(0..n-1) (\r. pi / &2) / &n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th])
  THENL
   [ASM_SIMP_TAC[SUM_CONST_NUMSEG; SUB_ADD; LE_1; SUB_0] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM REAL_OF_NUM_EQ]) THEN
    CONV_TAC REAL_FIELD;
    REWRITE_TAC[real_div] THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_RMUL THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[FINITE_NUMSEG; HAS_REAL_INTEGRAL_DIRICHLET_KERNEL_HALF]]);;

let FEJER_KERNEL_POS_LE = prove
 (`!n x. &0 <= fejer_kernel n x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FEJER_KERNEL] THEN
  REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_POS; REAL_LE_DIV]) THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]) THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

let FOURIER_FEJER_CESARO_SUMMABLE = prove
 (`!f x l r.
        f absolutely_real_integrable_on real_interval[--pi,pi] /\
        (!x. f(x + &2 * pi) = f x) /\
        (f ---> l) (atreal x within {x' | x' <= x}) /\
        (f ---> r) (atreal x within {x' | x' >= x})
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> (l + r) / &2)
            sequentially`,
  MAP_EVERY X_GEN_TAC [`f:real->real`; `t:real`; `l:real`; `r:real`] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FOURIER_SUM_LIMIT_FEJER_KERNEL_HALF] THEN
  REWRITE_TAC[REAL_ARITH `&2 * x / &2 = x`] THEN
  ABBREV_TAC `h = \u. ((f:real->real)(t + u) + f(t - u)) - (l + r)` THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
  SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `(h ---> &0) (atreal(&0) within {x | &0 <= x})`
  ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN REWRITE_TAC[REAL_ARITH
     `(f' + f) - (l + l'):real = (f - l) + (f' - l')`] THEN
    MATCH_MP_TAC REALLIM_NULL_ADD THEN CONJ_TAC THENL
     [UNDISCH_TAC `(f ---> l) (atreal t within {x' | x' <= t})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
       X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t - x:real` th)) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `(f ---> r) (atreal t within {x' | x' >= t})` THEN
      REWRITE_TAC[REALLIM_WITHINREAL] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
      ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d1:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th ->
       X_GEN_TAC `x:real` THEN MP_TAC(SPEC `t + x:real` th)) THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?k. &0 < k /\ k < pi /\
        (!x. &0 < x /\ x <= k ==> abs(h x) < e / &2 / pi)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(h ---> &0) (atreal (&0) within {x | &0 <= x})` THEN
    REWRITE_TAC[REALLIM_WITHINREAL] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2 / pi`) THEN
    ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; PI_POS; IN_ELIM_THM; REAL_SUB_RZERO;
                 LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:real` THEN STRIP_TAC THEN EXISTS_TAC `min k pi / &2` THEN
    REPEAT(CONJ_TAC THENL
     [MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\n. real_integral (real_interval[k,pi])
                        (\x. fejer_kernel n x * h x))
     ---> &0) sequentially`
  MP_TAC THENL
   [MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
    EXISTS_TAC
     `\n. real_integral (real_interval[k,pi])
                        (\x. abs(h x) / (&2 * sin(x / &2) pow 2)) / &n` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[REALLIM_1_OVER_N]] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FEJER_KERNEL; LE_1] THEN
    SUBGOAL_THEN
     `(\x. h x / (&2 * sin(x / &2) pow 2))
      absolutely_real_integrable_on real_interval[k,pi]`
    MP_TAC THENL
     [REWRITE_TAC[real_div] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
      REWRITE_TAC[GSYM real_div] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
        MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS;
        MATCH_MP_TAC REAL_COMPACT_IMP_BOUNDED THEN
        MATCH_MP_TAC REAL_COMPACT_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[REAL_COMPACT_INTERVAL];
        EXPAND_TAC "h" THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_SUB THEN
        REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST] THEN
        MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[--pi,pi]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ADD THEN CONJ_TAC THENL
           [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
            ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`];
            REWRITE_TAC[real_sub; absolutely_real_integrable_on] THEN
            ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_REFLECT] THEN
            REWRITE_TAC[GSYM absolutely_real_integrable_on] THEN
            REWRITE_TAC[real_sub; REAL_NEG_NEG] THEN
            ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
            MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_PERIODIC_OFFSET THEN
            ASM_REWRITE_TAC[REAL_ARITH `pi - --pi = &2 * pi`]];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC]] THEN
      (REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
       REWRITE_TAC[IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN
       STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_INV_WITHINREAL THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
         REAL_DIFFERENTIABLE_TAC;
         REWRITE_TAC[REAL_RING `&2 * x pow 2 = &0 <=> x = &0`] THEN
         MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC SIN_POS_PI THEN
         ASM_REAL_ARITH_TAC]);
      DISCH_THEN(fun th -> ASSUME_TAC th THEN
        MP_TAC(MATCH_MP ABSOLUTELY_REAL_INTEGRABLE_ABS th)) THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_DIV; REAL_ABS_NUM; REAL_ABS_POW] THEN
      REWRITE_TAC[REAL_POW2_ABS] THEN DISCH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [real_div] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[GSYM REAL_INV_MUL; REAL_ABS_MUL] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `x <= y <=> x <= &1 * y`] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; ABS_SQUARE_LE_1; SIN_BOUND] THEN
      MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 <= x ==> abs x <= y`) THEN
      REWRITE_TAC[GSYM real_div; REAL_LE_INV_EQ] THEN
      SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_POW_2] THEN
      REWRITE_TAC[REAL_MUL_AC];
      DISCH_TAC] THEN
    MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x.  abs(h x) / (&2 * sin(x / &2) pow 2) * inv(&n)` THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_RMUL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    MATCH_MP_TAC REAL_INTEGRABLE_EQ THEN
    EXISTS_TAC
     `\x. sin(&n / &2 * x) pow 2 / (&2 * &n * sin(x / &2) pow 2) * h(x)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[real_div; REAL_INV_MUL; GSYM REAL_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `s * t * n * i * h:real = n * s * h * (t * i)`] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[GSYM REAL_INV_MUL] THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_REWRITE_TAC[GSYM real_div] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
      MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
      REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_DIFFERENTIABLE_IMP_CONTINUOUS_WITHINREAL THEN
      REAL_DIFFERENTIABLE_TAC;
      REWRITE_TAC[real_bounded; FORALL_IN_IMAGE] THEN EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS; ABS_SQUARE_LE_1; SIN_BOUND]];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `MAX 1 N` THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[ARITH_RULE `MAX a b <= x <=> a <= x /\ b <= x`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x. fejer_kernel n x * h x`; `&0`; `pi`; `k:real`]
        REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN EXPAND_TAC "h" THEN
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs x <= e / &2 ==> x + y = z ==> abs y < e / &2 ==> abs z < e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[&0,k])
                            (\x. fejer_kernel n x * e / &2 / pi)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `real_integral (real_interval [&0,k]) (\x. fejer_kernel n x * h x) =
      real_integral (real_interval [&0,k])
                    (\x. fejer_kernel n x * (if x = &0 then &0 else h x))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
      EXISTS_TAC `{&0}` THEN SIMP_TAC[IN_DIFF; IN_SING] THEN
      REWRITE_TAC[REAL_NEGLIGIBLE_SING];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_ABS_BOUND_INTEGRAL THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] REAL_INTEGRABLE_SPIKE) THEN
      MAP_EVERY EXISTS_TAC [`\x. fejer_kernel n x * h x`; `{&0}`] THEN
      SIMP_TAC[IN_DIFF; IN_SING; REAL_NEGLIGIBLE_SING] THEN
      EXPAND_TAC "h" THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                   REAL_LT_IMP_LE];
      MP_TAC(ISPECL
       [`\x:real. e / &2 / pi`; `n:num`; `k:real`; `&0`]
        ABSOLUTELY_REAL_INTEGRABLE_MUL_FEJER_KERNEL_REFLECTED_PART) THEN
      ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_CONST; REAL_LT_IMP_LE;
                   ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[REAL_ABS_POS; REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      REWRITE_TAC[FEJER_KERNEL_POS_LE] THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_ABS_NUM; REAL_POS;
                   PI_POS_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REAL_ARITH_TAC];
    MP_TAC(SPEC `n:num` HAS_REAL_INTEGRAL_FEJER_KERNEL_HALF) THEN
    ASM_SIMP_TAC[LE_1] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
     `real_integral (real_interval[&0,pi])
                    (\x. fejer_kernel n x * e / &2 / pi)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC REAL_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `real_interval[&0,pi]` THEN CONJ_TAC THENL
         [ASM_MESON_TAC[real_integrable_on];
          REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_INTEGRABLE_RMUL THEN REWRITE_TAC[ETA_AX] THEN
        ASM_MESON_TAC[real_integrable_on];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_REWRITE_TAC[FEJER_KERNEL_POS_LE] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
        MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP HAS_REAL_INTEGRAL_RMUL) THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2 / pi`) THEN
      SIMP_TAC[HAS_REAL_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
      REPEAT STRIP_TAC THEN SIMP_TAC[PI_POS; REAL_FIELD
       `&0 < pi ==> pi / &2 * e / &2 / pi = e / &4`] THEN
      ASM_REAL_ARITH_TAC]]);;

let FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE = prove
 (`!f x l r.
        f real_continuous_on (:real) /\ (!x. f(x + &2 * pi) = f x)
        ==> ((\n. sum(0..n-1) (\m. sum (0..2*m)
                                       (\k. fourier_coefficient f k *
                                            trigonometric_set k x)) / &n)
             ---> f(x))
            sequentially`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [REAL_ARITH `x = (x + x) / &2`] THEN
  MATCH_MP_TAC FOURIER_FEJER_CESARO_SUMMABLE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_CONTINUOUS THEN
    ASM_MESON_TAC[REAL_CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    CONJ_TAC THEN MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_ATREAL] THEN
    ASM_MESON_TAC[REAL_CONTINUOUS_ON_EQ_REAL_CONTINUOUS_AT; REAL_OPEN_UNIV;
                  IN_UNIV]]);;
