(* ========================================================================= *)
(* L_p spaces for functions R^m->R^n based on an arbitrary set.              *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* The space L_p of measurable functions f with |f|^p integrable (on s).     *)
(* ------------------------------------------------------------------------- *)

let lspace = new_definition
 `lspace s p =
   {f:real^M->real^N | f measurable_on s /\
                       (\x. lift(norm(f x) rpow p)) integrable_on s}`;;

let LSPACE_ZERO = prove
 (`!s. lspace s (&0) =
          if measurable s then {f:real^M->real^N | f measurable_on s} else {}`,
  REWRITE_TAC[lspace; RPOW_POW; real_pow; NORM_0; LIFT_NUM] THEN
  GEN_TAC THEN REWRITE_TAC[INTEGRABLE_ON_CONST; VEC_EQ; ARITH_EQ] THEN
  ASM_CASES_TAC `measurable(s:real^M->bool)` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let LSPACE_CONST = prove
 (`!s p c. measurable s ==> (\x. c) IN lspace s p`,
  SIMP_TAC[lspace; IN_ELIM_THM; INTEGRABLE_ON_CONST;
           INTEGRABLE_IMP_MEASURABLE]);;

let LSPACE_0 = prove
 (`!s p. ~(p = &0) ==> (\x. vec 0) IN lspace s p`,
  SIMP_TAC[lspace; IN_ELIM_THM; NORM_0; RPOW_ZERO; LIFT_NUM] THEN
  SIMP_TAC[INTEGRABLE_IMP_MEASURABLE; INTEGRABLE_0]);;

let LSPACE_CMUL = prove
 (`!s p c f:real^M->real^N.
        f IN lspace s p ==> (\x. c % f x) IN lspace s p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  SIMP_TAC[NORM_MUL; RPOW_MUL; NORM_POS_LE; LIFT_CMUL] THEN
  SIMP_TAC[MEASURABLE_ON_CMUL; INTEGRABLE_CMUL]);;

let LSPACE_NEG = prove
 (`!s p f:real^M->real^N. f IN lspace s p ==> (\x. --(f x)) IN lspace s p`,
  REWRITE_TAC[VECTOR_ARITH `--x:real^N = --(&1) % x`; LSPACE_CMUL]);;

let LSPACE_ADD = prove
 (`!s p f g:real^M->real^N.
      &0 <= p /\ f IN lspace s p /\ g IN lspace s p
      ==> (\x. f(x) + g(x)) IN lspace s p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_LE_LT] THEN ASM_CASES_TAC `p = &0` THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LSPACE_ZERO] THEN
    ASM_CASES_TAC `measurable(s:real^M->bool)` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; IN_ELIM_THM; MEASURABLE_ON_ADD];
    ALL_TAC] THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURABLE_ON_ADD] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(&2 rpow p * (norm((f:real^M->real^N) x) rpow p +
                                    norm((g:real^M->real^N) x) rpow p))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\x:real^M. lift(norm(f x + g x:real^N) rpow p)) =
      (lift o (\y. y rpow p) o drop) o (\x. lift(norm(f x + g x)))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_NORM THEN
      MATCH_MP_TAC MEASURABLE_ON_ADD THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[GSYM IMAGE_LIFT_UNIV] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_ON] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_RPOW THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[o_THM; DROP_VEC; RPOW_ZERO; REAL_LT_IMP_NZ] THEN
      REWRITE_TAC[LIFT_NUM]];
    REWRITE_TAC[LIFT_CMUL; LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; LIFT_DROP] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(&0 <= norm(f + g:real^N) rpow p /\ &0 <= norm f /\ &0 <= norm g /\
       norm(f + g) rpow p <= (norm f + norm g) rpow p) /\
      (&0 <= norm f /\ &0 <= norm g ==> (norm f + norm g) rpow p <= e)
      ==> abs(norm(f + g) rpow p) <= e`) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[NORM_POS_LE; RPOW_POS_LE; RPOW_LE2; NORM_TRIANGLE; RPOW_LE2;
                   REAL_LT_IMP_LE];
      SPEC_TAC(`norm((g:real^M->real^N) x)`,`z:real`) THEN
      SPEC_TAC(`norm((f:real^M->real^N) x)`,`w:real`) THEN
      MATCH_MP_TAC REAL_WLOG_LE THEN
      CONJ_TAC THENL [MESON_TAC[REAL_ADD_SYM]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * z) rpow p` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[RPOW_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_ADDL; RPOW_POS_LE; REAL_POS]]]]);;

let LSPACE_SUB = prove
 (`!s p f g:real^M->real^N.
      &0 <= p /\ f IN lspace s p /\ g IN lspace s p
      ==> (\x. f(x) - g(x)) IN lspace s p`,
  SIMP_TAC[VECTOR_SUB; LSPACE_ADD; LSPACE_NEG]);;

let LSPACE_IMP_INTEGRABLE = prove
 (`!s p f. f IN lspace s p ==> (\x. lift(norm(f x) rpow p)) integrable_on s`,
  SIMP_TAC[lspace; IN_ELIM_THM]);;

let LSPACE_NORM = prove
 (`!s p f. f IN lspace s p ==> (\x. lift(norm(f x))) IN lspace s p`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  SIMP_TAC[NORM_LIFT; REAL_ABS_NORM; MEASURABLE_ON_NORM]);;

let LSPACE_VSUM = prove
 (`!s p f:A->real^M->real^N t.
        &0 < p /\ FINITE t /\ (!i. i IN t ==> (f i) IN lspace s p)
        ==> (\x. vsum t (\i. f i x)) IN lspace s p`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; LSPACE_0; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[LSPACE_ADD; REAL_LT_IMP_LE; ETA_AX; IN_INSERT]);;

let LSPACE_MAX = prove
 (`!s p k f:real^M->real^N g:real^M->real^N.
      f IN lspace s p /\ g IN lspace s p /\ &0 < p
      ==> ((\x. lambda i. max (f x$i) (g x$i)):real^M->real^N) IN lspace s p`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MEASURABLE_ON_MAX] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC
   `\x. lift(&(dimindex(:N)) rpow p *
             max (norm((f:real^M->real^N) x) rpow p)
                 (norm((g:real^M->real^N) x) rpow p))` THEN
  ASM_SIMP_TAC[MEASURABLE_ON_LIFT_RPOW; MEASURABLE_ON_NORM;
               MEASURABLE_ON_MAX] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
    CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_MAX_RPOW; NORM_POS_LE; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM RPOW_MUL; NORM_LIFT; REAL_ABS_RPOW; REAL_ABS_NORM] THEN
    REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC RPOW_LE2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    GEN_REWRITE_TAC
      (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC SUM_BOUND THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= y /\ abs(x') <= y' ==> abs(max x x') <= max y y'`) THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM]]);;

let LSPACE_MIN = prove
 (`!s p k f:real^M->real^N g:real^M->real^N.
      f IN lspace s p /\ g IN lspace s p /\ &0 < p
      ==> ((\x. lambda i. min (f x$i) (g x$i)):real^M->real^N) IN lspace s p`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MEASURABLE_ON_MIN] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC
   `\x. lift(&(dimindex(:N)) rpow p *
             max (norm((f:real^M->real^N) x) rpow p)
                 (norm((g:real^M->real^N) x) rpow p))` THEN
  ASM_SIMP_TAC[MEASURABLE_ON_LIFT_RPOW; MEASURABLE_ON_NORM;
               MEASURABLE_ON_MIN] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
    CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[REAL_MAX_RPOW; NORM_POS_LE; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[GSYM RPOW_MUL; NORM_LIFT; REAL_ABS_RPOW; REAL_ABS_NORM] THEN
    REWRITE_TAC[LIFT_DROP] THEN MATCH_MP_TAC RPOW_LE2 THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    GEN_REWRITE_TAC
      (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    MATCH_MP_TAC SUM_BOUND THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= y /\ abs(x') <= y' ==> abs(min x x') <= max y y'`) THEN
    ASM_SIMP_TAC[COMPONENT_LE_NORM]]);;

let LSPACE_BOUNDED_MEASURABLE = prove
 (`!s p f:real^M->real^N g:real^M->real^P.
        &0 < p /\ f measurable_on s /\ g IN lspace s p /\
        (!x. x IN s ==> norm(f x) <= norm(g x))
        ==> f IN lspace s p`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(norm((g:real^M->real^P) x) rpow p)` THEN
  ASM_SIMP_TAC[LSPACE_IMP_INTEGRABLE] THEN
  ASM_SIMP_TAC[MEASURABLE_ON_LIFT_RPOW; MEASURABLE_ON_NORM] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
  REWRITE_TAC[REAL_ABS_RPOW; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[RPOW_LE2; REAL_LT_IMP_LE; NORM_POS_LE]);;

let LSPACE_BOUNDED_MEASURABLE_SIMPLE = prove
 (`!s p f:real^M->real^N.
        &0 < p /\ f measurable_on s /\ measurable s /\ bounded(IMAGE f s)
        ==> f IN lspace s p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:1`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
  MATCH_MP_TAC(MESON[] `(?x. P(\a. lift x)) ==> (?x. P x)`) THEN
  ASM_SIMP_TAC[LSPACE_CONST; NORM_LIFT] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[real_abs; REAL_LT_IMP_LE]);;

let LSPACE_INTEGRABLE_PRODUCT = prove
 (`!s p q f:real^M->real^N g:real^M->real^N.
        &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1 /\
        f IN lspace s p /\ g IN lspace s q
        ==> (\x. lift(norm(f x) * norm(g x))) integrable_on s`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x) rpow p / p) +
                  lift(norm((g:real^M->real^N) x) rpow q / q)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LIFT_CMUL] THEN
    GEN_REWRITE_TAC (LAND_CONV o ABS_CONV o LAND_CONV)
        [GSYM LIFT_DROP] THEN
    MATCH_MP_TAC MEASURABLE_ON_DROP_MUL THEN
    CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INTEGRABLE_ADD THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[LIFT_CMUL] THEN CONJ_TAC THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[NORM_LIFT; REAL_ABS_MUL; REAL_ABS_NORM; LIFT_DROP;
                DROP_ADD] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC YOUNG_INEQUALITY THEN
    ASM_REWRITE_TAC[NORM_POS_LE]]);;

let LSPACE_1 = prove
 (`!f:real^M->real^N s. f IN lspace s (&1) <=> f absolutely_integrable_on s`,
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE; lspace; IN_ELIM_THM] THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let LSPACE_MONO = prove
 (`!f:real^M->real^N s p q.
        f IN lspace s q /\ measurable s /\ &0 < p /\ p <= q
        ==> f IN lspace s p`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(max (&1) (norm((f:real^M->real^N) x) rpow q))` THEN
  ASM_SIMP_TAC[MEASURABLE_ON_LIFT_RPOW; MEASURABLE_ON_NORM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1 THEN
    CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    ASM_SIMP_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; INTEGRABLE_ON_CONST] THEN
    REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop; LIFT_DROP] THEN
    SIMP_TAC[RPOW_POS_LE; NORM_POS_LE; REAL_POS];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ABS_RPOW; REAL_ABS_NORM] THEN
    DISJ_CASES_TAC(ISPECL [`&1`; `norm((f:real^M->real^N) x)`] REAL_LE_TOTAL)
    THENL
     [MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= max z y`) THEN
      MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= max y z`) THEN
      MATCH_MP_TAC RPOW_1_LE THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC]]);;

let LSPACE_INCLUSION = prove
 (`!s p q. measurable s /\ &0 < p /\ p <= q
           ==> (lspace s q :(real^M->real^N)->bool) SUBSET (lspace s p)`,
  REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `q:real` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The corresponding seminorm; Hoelder and Minkowski inequalities.           *)
(* ------------------------------------------------------------------------- *)

let lnorm = new_definition
 `lnorm s p f = drop(integral s (\x. lift(norm(f x) rpow p))) rpow (inv p)`;;

let LNORM_0 = prove
 (`!s p. ~(p = &0) ==> lnorm s p (\x. vec 0) = &0`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[lnorm; NORM_0; RPOW_ZERO] THEN
  ASM_REWRITE_TAC[LIFT_NUM; INTEGRAL_0; DROP_VEC; RPOW_ZERO; REAL_INV_EQ_0]);;

let LNORM_CONST = prove
  (`!s p c:real^N.
      measurable s /\ &0 < p
      ==> lnorm s p (\x:real^M. c) = measure s rpow (inv p) * norm c`,
  SIMP_TAC[lnorm; INTEGRAL_CONST_GEN; DROP_CMUL; LIFT_DROP] THEN
  SIMP_TAC[RPOW_RPOW; NORM_POS_LE; RPOW_MUL] THEN
  SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; RPOW_POW; REAL_POW_1]);;

let LNORM_MONO = prove
 (`!f:real^M->real^N g:real^M->real^P s t p.
        &0 <= p /\ f IN lspace s p /\ g IN lspace s p /\
        negligible t /\ (!x. x IN s DIFF t ==> norm(f x) <= norm(g x))
        ==> lnorm s p f <= lnorm s p g`,
  REWRITE_TAC[lspace; lnorm; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  ASM_SIMP_TAC[INTEGRAL_DROP_POS; LIFT_DROP; RPOW_POS_LE; NORM_POS_LE] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[LIFT_DROP] THEN
  ASM_SIMP_TAC[RPOW_LE2; NORM_POS_LE]);;

let LNORM_NEG = prove
 (`!s p f:real^M->real^N. lnorm s p (\x. --(f x)) = lnorm s p f`,
  REWRITE_TAC[lnorm; NORM_NEG]);;

let LNORM_MUL = prove
 (`!s p f c. f IN lspace s p /\ ~(p = &0)
             ==> lnorm s p (\x. c % f x) = abs(c) * lnorm s p f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnorm; NORM_MUL; RPOW_MUL; LIFT_CMUL] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; LSPACE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[DROP_CMUL; RPOW_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_ABS_POS; REAL_MUL_RINV] THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let LNORM_EQ_0 = prove
 (`!s p f. ~(p = &0) /\ f IN lspace s p
           ==> (lnorm s p f = &0 <=>
                negligible {x | x IN s /\ ~(f x = vec 0)})`,
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[lnorm; RPOW_EQ_0; REAL_INV_EQ_0] THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM; LIFT_DROP] THEN
  ASM_SIMP_TAC[INTEGRAL_EQ_HAS_INTEGRAL] THEN
  SIMP_TAC[HAS_INTEGRAL_NEGLIGIBLE_EQ; lift; LAMBDA_BETA; NORM_POS_LE;
           RPOW_POS_LE] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  SIMP_TAC[IN_ELIM_THM; CART_EQ; LAMBDA_BETA] THEN
  REWRITE_TAC[FORALL_1; DIMINDEX_1; VEC_COMPONENT] THEN
  ASM_REWRITE_TAC[RPOW_EQ_0; NORM_EQ_0; CART_EQ; VEC_COMPONENT]);;

let LNORM_POS_LE = prove
 (`!s p f. f IN lspace s p ==> &0 <= lnorm s p f`,
  SIMP_TAC[lspace; IN_ELIM_THM; lnorm] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RPOW_POS_LE THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
  ASM_SIMP_TAC[LIFT_DROP; NORM_POS_LE; RPOW_POS_LE]);;

let LNORM_NORM = prove
 (`!s p f. lnorm s p (\x. lift(norm(f x))) = lnorm s p f`,
  REWRITE_TAC[lnorm; NORM_LIFT; REAL_ABS_NORM]);;

let LNORM_RPOW = prove
 (`!s p f:real^M->real^N.
        f IN lspace s p /\ ~(p = &0)
        ==> (lnorm s p f) rpow p =
            drop(integral s (\x. lift(norm(f x) rpow p)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lnorm] THEN
  ASM_SIMP_TAC[INTEGRAL_DROP_POS; LIFT_DROP; NORM_POS_LE; RPOW_RPOW;
               LSPACE_IMP_INTEGRABLE; RPOW_POS_LE] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; RPOW_POW; REAL_POW_1]);;

let INTEGRAL_LNORM_RPOW = prove
 (`!s p f:real^M->real^N.
        f IN lspace s p /\ ~(p = &0)
        ==> integral s (\x. lift(norm(f x) rpow p)) =
            lift((lnorm s p f) rpow p)`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; LNORM_RPOW]);;

let HOELDER_INEQUALITY = prove
 (`!s p q f:real^M->real^N g:real^M->real^N.
        &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1 /\
        f IN lspace s p /\ g IN lspace s q
        ==> drop(integral s (\x. lift(norm(f x) * norm(g x))))
              <= lnorm s p f * lnorm s q g`,
  MP_TAC LSPACE_INTEGRABLE_PRODUCT THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= lnorm s p (f:real^M->real^N) /\
                &0 <= lnorm s q (g:real^M->real^N)`
  MP_TAC THENL [ASM_SIMP_TAC[LNORM_POS_LE]; REWRITE_TAC[IMP_CONJ]] THEN
  REPEAT
   (GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
    DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ASSUME_TAC) THENL
     [ASM_SIMP_TAC[LNORM_EQ_0; REAL_LT_IMP_NZ] THEN REPEAT DISCH_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = &0 ==> x <= y`) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; LNORM_POS_LE; GSYM LIFT_EQ; LIFT_DROP] THEN
      ASM_SIMP_TAC[INTEGRAL_EQ_HAS_INTEGRAL; LIFT_NUM] THEN
      SIMP_TAC[HAS_INTEGRAL_NEGLIGIBLE_EQ; lift; LAMBDA_BETA; NORM_POS_LE;
               REAL_LE_MUL] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
      SIMP_TAC[CART_EQ; SUBSET; IN_ELIM_THM; LAMBDA_BETA] THEN
      REWRITE_TAC[DIMINDEX_1; FORALL_1; VEC_COMPONENT] THEN
      REWRITE_TAC[REAL_ENTIRE; CART_EQ; NORM_EQ_0; VEC_COMPONENT] THEN
      MESON_TAC[];
      ALL_TAC]) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_MUL] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
  REWRITE_TAC[GSYM DROP_CMUL] THEN ASM_SIMP_TAC[GSYM INTEGRAL_CMUL] THEN
  REWRITE_TAC[REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral s
   (\x. lift(norm(inv(lnorm s p f) % (f:real^M->real^N) x) rpow p / p +
             norm(inv(lnorm s q g) % (g:real^M->real^N) x) rpow q / q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_SIMP_TAC[LIFT_DROP; INTEGRABLE_CMUL] THEN CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC INTEGRABLE_ADD THEN
      REWRITE_TAC[NORM_MUL; RPOW_MUL] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
      ASM_SIMP_TAC[LSPACE_IMP_INTEGRABLE; INTEGRABLE_CMUL; LIFT_CMUL];
      REWRITE_TAC[DROP_CMUL; LIFT_DROP; NORM_MUL; REAL_ABS_INV] THEN
      ASM_SIMP_TAC[real_abs; LNORM_POS_LE; REAL_LT_IMP_NZ] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
       `(a * b) * (c * d:real) = (a * c) * (b * d)`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC YOUNG_INEQUALITY THEN
      ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; LNORM_POS_LE; REAL_LE_INV_EQ]];
    REWRITE_TAC[LIFT_ADD; NORM_MUL; LIFT_CMUL; RPOW_MUL] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] real_div] THEN
    REWRITE_TAC[LIFT_CMUL; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[INTEGRAL_ADD; INTEGRABLE_CMUL; INTEGRAL_CMUL;
                 LSPACE_IMP_INTEGRABLE; REAL_ABS_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; RPOW_INV] THEN
    ASM_SIMP_TAC[INTEGRAL_LNORM_RPOW; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL; LIFT_DROP] THEN
    ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                 RPOW_POS_LT] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]]);;

let HOELDER_INEQUALITY_FULL = prove
 (`!s p q f:real^M->real^N g:real^M->real^N.
        &0 < p /\ &0 < q /\ inv(p) + inv(q) = &1 /\
        f IN lspace s p /\ g IN lspace s q
        ==> (\x. lift(norm(f x) * norm(g x))) integrable_on s /\
            drop(integral s (\x. lift(norm(f x) * norm(g x))))
              <= lnorm s p f * lnorm s q g`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LSPACE_INTEGRABLE_PRODUCT) THEN
  ASM_SIMP_TAC[HOELDER_INEQUALITY]);;

let LNORM_TRIANGLE = prove
 (`!s p f:real^M->real^N g:real^M->real^N.
        f IN lspace s p /\ g IN lspace s p /\ &1 <= p
        ==> lnorm s p (\x. f x + g x) <= lnorm s p f + lnorm s p g`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `p = &1` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[lnorm;
      MESON[RPOW_POW; REAL_POW_1; REAL_INV_1] `x rpow (inv(&1)) = x`;
      GSYM DROP_ADD; GSYM INTEGRAL_ADD; LSPACE_IMP_INTEGRABLE] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE_MEASURABLE THEN
    ASM_SIMP_TAC[LSPACE_IMP_INTEGRABLE; INTEGRABLE_ADD] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1; LIFT_DROP; DROP_ADD] THEN
    REWRITE_TAC[NORM_POS_LE; NORM_TRIANGLE] THEN
    MATCH_MP_TAC MEASURABLE_ON_NORM THEN MATCH_MP_TAC MEASURABLE_ON_ADD THEN
    RULE_ASSUM_TAC(REWRITE_RULE[lspace; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < p` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lnorm s p (\x. (f:real^M->real^N) x + g x)` MP_TAC THENL
   [ASM_SIMP_TAC[LNORM_POS_LE; LSPACE_ADD; REAL_ARITH `&1 <= p ==> &0 <= p`];
    GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[LNORM_POS_LE; REAL_LE_ADD]] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `lnorm s p (\x. (f:real^M->real^N) x + g x) rpow (p - &1)` THEN
  ASM_SIMP_TAC[RPOW_POS_LT] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_POW_1] THEN
  ASM_SIMP_TAC[GSYM RPOW_POW; GSYM RPOW_ADD] THEN
  ASM_SIMP_TAC[LSPACE_ADD; LNORM_RPOW; REAL_ARITH `p - &1 + &1 = p`;
               REAL_ARITH `&1 <= p ==> &0 <= p /\ ~(p = &0)`] THEN
  CONV_TAC(LAND_CONV(SUBS_CONV[REAL_ARITH `p = &1 + (p - &1)`])) THEN
  ASM_SIMP_TAC[RPOW_ADD_ALT; NORM_POS_LE; REAL_ARITH
   `&1 <= p ==> &1 + p - &1 = &0 ==> p - &1 = &0`] THEN
  REWRITE_TAC[RPOW_POW; REAL_POW_1] THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`; `p:real`; `p / (p - &1)`;
    `\x. lift(norm((g:real^M->real^N) x))`;
    `\x. lift(norm((f:real^M->real^N)(x) + g(x)) rpow (p - &1))`]
        HOELDER_INEQUALITY_FULL) THEN
  MP_TAC(ISPECL
   [`s:real^M->bool`; `p:real`; `p / (p - &1)`;
    `\x. lift(norm((f:real^M->real^N) x))`;
    `\x. lift(norm((f:real^M->real^N)(x) + g(x)) rpow (p - &1))`]
        HOELDER_INEQUALITY_FULL) THEN
  ASM_SIMP_TAC[LSPACE_NORM; REAL_LT_DIV; REAL_SUB_LT;
               REAL_ARITH `&1 < p ==> &0 < p`;
               REAL_FIELD `&1 < p ==> inv(p) + inv(p / (p - &1)) = &1`] THEN
  MATCH_MP_TAC(TAUT
    `p /\ (q ==> r ==> s) ==> (p ==> q) ==> (p ==> r) ==> s`) THEN
  CONJ_TAC THENL
   [SIMP_TAC[lspace; IN_ELIM_THM; NORM_LIFT; REAL_ABS_NORM; REAL_ABS_RPOW;
             RPOW_RPOW; NORM_POS_LE] THEN
    ASM_SIMP_TAC[REAL_FIELD `&1 < p ==> (p - &1) * p / (p - &1) = p`] THEN
    ASM_SIMP_TAC[LSPACE_IMP_INTEGRABLE; LSPACE_ADD;
                 REAL_ARITH `&1 < p ==> &0 <= p`] THEN
    MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `((\x. f x + g x):real^M->real^N) IN lspace s p` MP_TAC THENL
     [ASM_SIMP_TAC[LSPACE_ADD; REAL_ARITH `&1 < p ==> &0 <= p`];
      SIMP_TAC[lspace; IN_ELIM_THM; MEASURABLE_ON_NORM]];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; LNORM_NORM; REAL_ABS_RPOW] THEN
  MATCH_MP_TAC(TAUT
   `(p1 /\ p2 ==> b1 /\ b2 ==> c) ==> p1 /\ b1 ==> p2 /\ b2 ==> c`) THEN
  STRIP_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_ADD2) THEN
  ASM_SIMP_TAC[GSYM DROP_ADD; GSYM INTEGRAL_ADD] THEN
  SUBGOAL_THEN
   `lnorm s (p / (p - &1)) (\x. lift(norm (f x + g x) rpow (p - &1))) =
    lnorm s p (\x. (f:real^M->real^N) x + g x) rpow (p - &1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[lnorm] THEN
    ASM_SIMP_TAC[RPOW_RPOW; INTEGRAL_DROP_POS; LIFT_DROP; NORM_POS_LE;
                 NORM_LIFT; REAL_ABS_NORM; REAL_ABS_RPOW] THEN
    ASM_SIMP_TAC[REAL_FIELD `&1 < p ==> (p - &1) * p / (p - &1) = p`] THEN
    REWRITE_TAC[REAL_INV_DIV] THEN REWRITE_TAC[real_div] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC(GSYM RPOW_RPOW) THEN
    MATCH_MP_TAC INTEGRAL_DROP_POS THEN
    ASM_SIMP_TAC[LIFT_DROP; RPOW_POS_LE; NORM_POS_LE; LSPACE_IMP_INTEGRABLE;
                 LSPACE_ADD; REAL_ARITH `&1 < p ==> &0 <= p`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i2 <= i1 ==> i1 <= f * y + g * y ==> i2 <= y * (f + g)`) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_MEASURABLE THEN
  ASM_SIMP_TAC[INTEGRABLE_ADD] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_MUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC]] THEN
    (SUBGOAL_THEN `((\x. f x + g x):real^M->real^N) IN lspace s p` MP_TAC THENL
      [ASM_SIMP_TAC[LSPACE_ADD; REAL_ARITH `&1 < p ==> &0 <= p`];
       SIMP_TAC[lspace; IN_ELIM_THM; MEASURABLE_ON_NORM]]);
    REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; LIFT_DROP; DROP_ADD] THEN
    SIMP_TAC[NORM_TRIANGLE; REAL_LE_RMUL; NORM_POS_LE; RPOW_POS_LE;
             REAL_LE_MUL]]);;

let VSUM_LNORM = prove
 (`!s p f:A->real^M->real^N t.
        &1 <= p /\ FINITE t /\ (!i. i IN t ==> (f i) IN lspace s p)
        ==> lnorm s p (\x. vsum t (\i. f i x)) <= sum t (\i. lnorm s p (f i))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; LNORM_0; REAL_LE_REFL;
               REAL_ARITH `&1 <= p ==> ~(p = &0)`] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `u:A->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= x + y ==> y <= z ==> a <= x + z`) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
  ASM_SIMP_TAC[ETA_AX; LSPACE_VSUM; REAL_ARITH `&1 <= p ==> &0 < p`]);;

(* ------------------------------------------------------------------------- *)
(* A Hoelder-based bound on integral, theorem 222 in Hardy-Littlewood-Polya  *)
(* ------------------------------------------------------------------------- *)

let HOELDER_BOUND = prove
 (`!(f:real^M->real^N) s p.
        &1 <= p /\ measurable s /\ f IN lspace s p
        ==> f absolutely_integrable_on s /\
            norm(integral s f) rpow p
            <= measure s rpow (p - &1) *
               norm(integral s (\x. lift(norm(f x) rpow p)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `&1 <= p <=> p = &1 \/ &1 < p`] THEN
  ASM_CASES_TAC `p = &1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[LSPACE_1; RPOW_POW; REAL_POW_1; REAL_SUB_REFL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[real_pow; REAL_MUL_LID] THEN
    REWRITE_TAC[NORM_1] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= a ==> x <= abs a`) THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LE THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM LSPACE_1] THEN
    MATCH_MP_TAC LSPACE_MONO THEN EXISTS_TAC `p:real` THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `p / (p - &1)`; `p:real`;
                 `(\x. basis 1):real^M->real^N`; `f:real^M->real^N`]
        HOELDER_INEQUALITY_FULL) THEN
  ASM_SIMP_TAC[LSPACE_CONST; LNORM_CONST; REAL_ARITH `&1 < p ==> &0 < p`] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_DIV; ALL_TAC] THEN
    UNDISCH_TAC `&1 < p` THEN CONV_TAC REAL_FIELD;
    REWRITE_TAC[NORM_BASIS_1; REAL_MUL_RID; REAL_MUL_LID]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `p:real` o MATCH_MP (REWRITE_RULE
   [TAUT `p /\ q /\ r ==> s <=> q ==> p /\ r ==> s`] RPOW_LE2)) THEN
  ASM_SIMP_TAC[RPOW_MUL; RPOW_RPOW; MEASURE_POS_LE;
               LNORM_RPOW; REAL_ARITH `&1 < p ==> &0 <= p /\ ~(p = &0)`;
               REAL_FIELD `&1 < p ==> inv(p / (p - &1)) * p = p - &1`;
               INTEGRAL_DROP_POS; LIFT_DROP; NORM_POS_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a':real <= a /\ b <= b' ==> a <= b ==> a' <= b'`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_ARITH `&1 < p ==> &0 <= p`] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_LE];
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; RPOW_POS_LE] THEN
    REWRITE_TAC[NORM_1; REAL_ABS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness (Riesz-Fischer).                                             *)
(* ------------------------------------------------------------------------- *)

let LSPACE_SUMMABLE_UNIV = prove
 (`!f:num->real^M->real^N p s.
        &1 <= p /\
        (!i. f i IN lspace s p) /\
        real_summable (:num) (\i. lnorm s p (f i))
        ==> ?g. g IN lspace s p /\
                !e. &0 < e  ==> eventually
                                  (\n. lnorm s p (\x. vsum (0..n) (\i. f i x) -
                                                      g(x)) < e)
                                  sequentially`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_SUMS_INFSUM]) THEN
  ABBREV_TAC `M = real_infsum (:num) (\i. lnorm s p (f i:real^M->real^N))` THEN
  DISCH_TAC THEN
  ABBREV_TAC
   `g = \n x:real^M. vsum(0..n) (\i. lift(norm(f i x:real^N)))` THEN
  SUBGOAL_THEN `!n:num. lnorm s p (g n:real^M->real^1) <= M` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_LNORM o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; LSPACE_NORM; ETA_AX] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC[LNORM_NORM] THEN EXPAND_TAC "M" THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SET_RULE `s = UNIV INTER s`] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC REAL_PARTIAL_SUMS_LE_INFSUM THEN
    ASM_SIMP_TAC[LNORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n:num. (g n:real^M->real^1) IN lspace s p` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC LSPACE_VSUM THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[FINITE_NUMSEG]] THEN
    ASM_SIMP_TAC[LSPACE_NORM; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n:num x:real^M. &0 <= drop(g n x)` ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN
    SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; LIFT_DROP] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; NORM_POS_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\i:num x:real^M. lift(drop(g i x) rpow p)`; `s:real^M->bool`]
        BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
  REWRITE_TAC[LIFT_DROP] THEN ANTS_TAC THENL
   [MATCH_MP_TAC(TAUT `b /\ a /\ c ==> a /\ b /\ c`) THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN
      SIMP_TAC[DROP_VSUM; FINITE_NUMSEG] THEN
      MATCH_MP_TAC RPOW_LE2 THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; NORM_POS_LE];
        SIMP_TAC[SUM_CLAUSES_NUMSEG; LE_0; REAL_LE_ADDR] THEN
        REWRITE_TAC[o_DEF; LIFT_DROP; NORM_POS_LE];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!k x. drop((g:num->real^M->real^1) k x) = norm(g k x)`
     (fun th -> REWRITE_TAC[th])
    THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
      ASM_REWRITE_TAC[real_abs];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LSPACE_IMP_INTEGRABLE; ETA_AX] THEN
    REWRITE_TAC[bounded] THEN EXISTS_TAC `M rpow p` THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[INTEGRAL_LNORM_RPOW; ETA_AX;
                 REAL_ARITH `&1 <= p ==> ~(p = &0)`] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_RPOW] THEN
    MATCH_MP_TAC RPOW_LE2 THEN
    ASM_SIMP_TAC[REAL_ARITH `&1 <= p ==> &0 <= p`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= a ==> &0 <= abs x /\ abs x <= a`) THEN
    ASM_SIMP_TAC[LNORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`hp:real^M->real^1`; `k:real^M->bool`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `h:real^M->real^1 = \x. lift(drop(hp x) rpow (inv p))` THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF k ==> ((\i. g i x) --> ((h:real^M->real^1) x)) sequentially`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`lift o (\x. x rpow (inv p)) o drop`;
      `sequentially`; `\i. lift(drop((g:num->real^M->real^1) i x) rpow p)`;
      `(hp:real^M->real^1) x`]
        LIM_CONTINUOUS_FUNCTION) THEN
    ASM_SIMP_TAC[] THEN ANTS_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "h" THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
    ASM_SIMP_TAC[RPOW_RPOW; REAL_MUL_RINV;
                 REAL_ARITH `&1 <= p ==> ~(p = &0)`] THEN
    REWRITE_TAC[RPOW_POW; REAL_POW_1; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF k ==> summable (:num) (\i. (f:num->real^M->real^N) i x)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_LIFT_ABSCONV_IMP_CONV THEN
    REWRITE_TAC[summable] THEN EXISTS_TAC `(h:real^M->real^1) x` THEN
    REWRITE_TAC[sums; INTER_UNIV] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[summable] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `l:real^M->real^N` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n x. x IN s DIFF k
          ==> norm(vsum (0..n) (\i. (f:num->real^M->real^N) i x)) <= drop(h x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LIFT_DROP] THEN
    SIMP_TAC[LIFT_SUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\n. vsum (0..n)
                   (\i. lift(norm((f:num->real^M->real^N) i x)))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[FUN_EQ_THM]) THEN ASM_SIMP_TAC[IN_DIFF];
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `n:num` THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      SIMP_TAC[DROP_VSUM; FINITE_NUMSEG; o_DEF; LIFT_DROP] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[SUBSET; IN_NUMSEG; NORM_POS_LE; FINITE_NUMSEG] THEN
      UNDISCH_TAC `n:num <= m` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF k ==> norm((l:real^M->real^N) x) <= drop(h x)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n. vsum ((:num) INTER (0..n))
                         (\i. (f:num->real^M->real^N) i x)` THEN
    ASM_SIMP_TAC[IN_DIFF; GSYM sums; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM_SIMP_TAC[INTER_UNIV];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[lspace; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
      EXISTS_TAC `\n x. vsum (0..n) (\i. (f:num->real^M->real^N) i x)` THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SET_RULE `0..n = UNIV INTER (0..n)`] THEN
      ASM_REWRITE_TAC[GSYM sums] THEN GEN_TAC THEN
      REWRITE_TAC[INTER_UNIV] THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
      RULE_ASSUM_TAC(REWRITE_RULE[lspace; IN_ELIM_THM]) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG];
      DISCH_TAC] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC
     `\x. if x IN k then lift(norm(l x:real^N) rpow p)
          else (hp:real^M->real^1) x` THEN
    ASM_SIMP_TAC[MEASURABLE_ON_LIFT_RPOW; MEASURABLE_ON_NORM; ETA_AX;
                 REAL_ARITH `&1 <= p ==> &0 < p`] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(hp:real^M->real^1) integrable_on s` THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_SIMP_TAC[IN_DIFF];
      REWRITE_TAC[NORM_LIFT; REAL_ABS_RPOW; REAL_ABS_NORM] THEN
      GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[LIFT_DROP; REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `drop(h(x:real^M)) rpow p` THEN CONJ_TAC THENL
       [MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; IN_DIFF] THEN
        ASM_REAL_ARITH_TAC;
        EXPAND_TAC "h" THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(REAL_ARITH `x = y pow 1 ==> x <= y`) THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `drop(hp(x:real^M)) rpow (inv p * p)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC RPOW_RPOW THEN
          MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
          EXISTS_TAC `\k. lift(drop((g:num->real^M->real^1) k x) rpow p)` THEN
          ASM_SIMP_TAC[IN_DIFF; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
          ASM_SIMP_TAC[LIFT_DROP; RPOW_POS_LE; EVENTUALLY_TRUE];
          ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 <= p ==> ~(p = &0)`] THEN
          REWRITE_TAC[RPOW_POW]]]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN s DIFF k ==> &0 <= drop(h x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN s DIFF k ==> &0 <= drop(hp x)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_LBOUND) THEN
    EXISTS_TAC `\k. lift(drop((g:num->real^M->real^1) k x) rpow p)` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_DROP; RPOW_POS_LE] THEN
    REWRITE_TAC[EVENTUALLY_TRUE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. lift(norm(vsum (0..n) (\i. (f:num->real^M->real^N) i x) - l x)
                    rpow p)`;
    `(\x. vec 0):real^M->real^1`;
    `\x:real^M. &2 rpow p % lift(drop(h x) rpow p)`;
    `s DIFF k:real^M->bool`]
   DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[lnorm; INTEGRAL_0; REAL_INTEGRAL_0; INTEGRABLE_0] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `s:real^M->bool` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
        MATCH_MP_TAC LSPACE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LSPACE_VSUM THEN
        ASM_REWRITE_TAC[FINITE_NUMSEG] THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC INTEGRABLE_CMUL THEN EXPAND_TAC "h" THEN
      REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
      EXISTS_TAC `hp:real^M->real^1` THEN
      EXISTS_TAC `{}:real^M->bool` THEN
      ASM_SIMP_TAC[DIFF_EMPTY; NEGLIGIBLE_EMPTY; RPOW_RPOW] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 <= p ==> ~(p = &0)`] THEN
      REWRITE_TAC[LIFT_DROP; RPOW_POW; REAL_POW_1] THEN
      UNDISCH_TAC `(hp:real^M->real^1) integrable_on s` THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      REWRITE_TAC[DROP_CMUL; GSYM RPOW_MUL; LIFT_DROP] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_REAL; GSYM drop] THEN
      REWRITE_TAC[REAL_ABS_NORM; LIFT_DROP; REAL_ABS_RPOW] THEN
      MATCH_MP_TAC RPOW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) <= a /\ norm(y) <= a ==> norm(x - y) <= &2 * a`) THEN
      ASM_SIMP_TAC[];
      X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
      MATCH_MP_TAC LIM_NULL_RPOW THEN
      CONJ_TAC THENL [REWRITE_TAC[o_DEF]; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[GSYM LIM_NULL_NORM] THEN REWRITE_TAC[GSYM LIM_NULL] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[sums; INTER_UNIV]) THEN
      ASM_SIMP_TAC[]];
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV o ABS_CONV)
     [GSYM LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ; o_DEF] LIM_NULL_RPOW)) THEN
    DISCH_THEN(MP_TAC o SPEC `inv p:real`) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[tendsto; DIST_0; NORM_REAL; GSYM drop; LIFT_DROP] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    SUBGOAL_THEN
     `!f:real^M->real^1. integral (s DIFF k) f = integral s f`
    MP_TAC THENL [ALL_TAC; SIMP_TAC[REAL_ARITH `abs(x) < e ==> x < e`]] THEN
    GEN_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      NEGLIGIBLE_SUBSET)) THEN SET_TAC[]]);;

let LSPACE_SUMMABLE = prove
 (`!f:num->real^M->real^N p s t.
        &1 <= p /\
        (!i. i IN t ==> f i IN lspace s p) /\
        real_summable t (\i. lnorm s p (f i))
        ==> ?g. g IN lspace s p /\
                ((\n. lnorm s p (\x. vsum (t INTER (0..n)) (\i. f i x) - g x))
                 ---> &0) sequentially`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_SUMMABLE_RESTRICT] THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
    [`(\n:num x. if n IN t then f n x else vec 0):num->real^M->real^N`;
     `p:real`; `s:real^M->bool`] LSPACE_SUMMABLE_UNIV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) IN t` THEN
      ASM_SIMP_TAC[LSPACE_0; ETA_AX; REAL_ARITH `&1 <= p ==> ~(p = &0)`];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [real_summable]) THEN
      REWRITE_TAC[real_summable] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[ETA_AX; LNORM_0; REAL_ARITH `&1 <= p ==> ~(p = &0)`]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
    ASM_CASES_TAC `(g:real^M->real^N) IN lspace s p` THEN
    ASM_REWRITE_TAC[tendsto_real] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x = y ==> x < e ==> abs y < e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC LSPACE_SUB THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 <= p ==> &0 <= p`] THEN
      MATCH_MP_TAC LSPACE_VSUM THEN
      ASM_SIMP_TAC[FINITE_NUMSEG; REAL_ARITH `&1 <= p ==> &0 < p`] THEN
      X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(i:num) IN t` THEN
      ASM_SIMP_TAC[ETA_AX; LSPACE_0; REAL_ARITH `&1 <= p ==> ~(p = &0)`];
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[GSYM VSUM_RESTRICT_SET] THEN
      REWRITE_TAC[SET_RULE `s INTER t = {x | x IN t /\ x IN s}`]]]);;

let RIESZ_FISCHER = prove
 (`!f:num->real^M->real^N p s.
        &1 <= p /\ (!n. (f n) IN lspace s p) /\
        (!e. &0 < e
             ==> ?N. !m n. m >= N /\ n >= N
                           ==> lnorm s p (\x. f m x - f n x) < e)
        ==> ?g. g IN lspace s p /\
                !e. &0 < e
                    ==> ?N. !n. n >= N
                                ==> lnorm s p (\x. f n x - g x) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?k:num->num.
        (!n. k n < k (SUC n)) /\
        (!n. lnorm s p ((\x. f (k(SUC n)) x - f (k n) x):real^M->real^N)
             < inv(&2 pow n))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_POW2; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num->num`) THEN
    MP_TAC(prove_recursive_functions_exist num_RECURSION
     `k 0 = N 0 /\
      !n. k(SUC n) = MAX (k n + 1) (MAX (N n) (N(SUC n)))`) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < MAX (n + 1) m`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ARITH_TAC; SPEC_TAC(`n:num`,`n:num`)] THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. f (k(SUC n)) x - (f:num->real^M->real^N) (k n) x`;
    `p:real`; `s:real^M->bool`] LSPACE_SUMMABLE_UNIV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[LSPACE_SUB; ETA_AX; REAL_ARITH `&1 <= p ==> &0 <= p`] THEN
    MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\n. inv(&2) pow n` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_SUMMABLE_GP THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[GSYM REAL_INV_POW] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x < y ==> abs x <= y`) THEN
      ASM_SIMP_TAC[LNORM_POS_LE; LSPACE_SUB; ETA_AX;
                   REAL_ARITH `&1 <= p ==> &0 <= p`]];
    DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
    EXISTS_TAC `\x. (g:real^M->real^N) x + f (k 0:num) x` THEN
    ASM_SIMP_TAC[LSPACE_ADD; ETA_AX; REAL_ARITH `&1 <= p ==> &0 <= p`] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; EVENTUALLY_SEQUENTIALLY] THEN
    REWRITE_TAC[ADD1; VSUM_DIFFS_ALT; LE_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `N1:num` (LABEL_TAC "+")) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
    ASM_REWRITE_TAC[REAL_HALF; GE] THEN
    DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
    EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[ARITH_RULE `MAX N1 N2 <= n <=> N1 <= n /\ N2 <= n`] THEN
    STRIP_TAC THEN REMOVE_THEN "+" (MP_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k(n + 1):num`; `n:num`]) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n + 1` THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; SPEC_TAC(`n + 1`,`m:num`)] THEN
      INDUCT_TAC THEN REWRITE_TAC[LE_0] THEN
      MATCH_MP_TAC(ARITH_RULE
       `m <= k m /\ k m < k(SUC m) ==> SUC m <= k(SUC m)`) THEN
      ASM_REWRITE_TAC[];
      REPEAT DISCH_TAC THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH
       `f n x - (g x + f (k 0) x):real^N =
        (f (k (n + 1)) x - f (k 0) x - g x) +
        --(f (k (n + 1)) x - f n x)`] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
      ASM_SIMP_TAC[LSPACE_SUB; LSPACE_NEG; ETA_AX;
                    REAL_ARITH `&1 <= p ==> &0 <= p`] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x < e / &2 /\ y < e / &2 ==> z <= x + y ==> z < e`) THEN
      ASM_SIMP_TAC[LNORM_NEG; LSPACE_SUB; ETA_AX;
                   REAL_ARITH `&1 <= p ==> &0 <= p`]]]);;

(* ------------------------------------------------------------------------- *)
(* A sort of dominated convergence theorem for L_p spaces.                   *)
(* ------------------------------------------------------------------------- *)

let LSPACE_DOMINATED_CONVERGENCE = prove
 (`!f:num->real^M->real^N g h:real^M->real^N s p k.
        &0 < p /\
        (!n. (f n) IN lspace s p) /\ h IN lspace s p /\
        (!n x. x IN s ==> norm(f n x) <= norm(h x)) /\
        negligible k /\
        (!x. x IN s DIFF k ==> ((\n. f n x) --> g(x)) sequentially)
        ==> g IN lspace s p /\
            ((\n. lnorm s p (\x. f n x - g x)) ---> &0) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n x. lift(norm((f:num->real^M->real^N) n x) rpow p)`;
    `\x. lift(norm((g:real^M->real^N) x) rpow p)`;
    `\x. lift(norm((h:real^M->real^N) x) rpow p)`;
    `s DIFF k:real^M->bool`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE o SPEC `k:num`) THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      FIRST_ASSUM(MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real^M`] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_LIFT; REAL_ABS_RPOW; REAL_ABS_NORM; LIFT_DROP] THEN
      MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o ISPEC
       `(lift o (\x. x rpow p) o  drop) o (lift o (norm:real^N->real))` o
         MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
      ASM_SIMP_TAC[o_THM; DROP_VEC; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM] THEN
      REWRITE_TAC[o_THM; LIFT_DROP] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[lspace; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
      EXISTS_TAC `f:num->real^M->real^N` THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[lspace; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE
       [TAUT `a ==> b ==> c <=> b ==> a ==> c`] INTEGRABLE_SPIKE_SET)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN SET_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN s DIFF k
        ==> norm((g:real^M->real^N) x) <= norm((h:real^M->real^N) x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
    EXISTS_TAC `\n. (f:num->real^M->real^N) n x` THEN
    ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n x. lift(norm((f:num->real^M->real^N) n x - g x) rpow p)`;
    `(\x. vec 0):real^M->real^1`;
    `\x. lift(norm(&2 % (h:real^M->real^N) x) rpow p)`;
    `s DIFF k:real^M->bool`] DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN
      SUBGOAL_THEN `(\x. (f:num->real^M->real^N) k x - g x) IN lspace s p`
      MP_TAC THENL
       [ASM_SIMP_TAC[LSPACE_SUB; REAL_LT_IMP_LE; ETA_AX]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      REWRITE_TAC[NORM_MUL; RPOW_MUL; LIFT_CMUL] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN
      UNDISCH_TAC `(h:real^M->real^N) IN lspace s p` THEN
      DISCH_THEN(MP_TAC o MATCH_MP LSPACE_IMP_INTEGRABLE) THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      MAP_EVERY X_GEN_TAC [`k:num`; `x:real^M`] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_LIFT; REAL_ABS_RPOW; REAL_ABS_NORM; LIFT_DROP] THEN
      MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC(NORM_ARITH
        `norm(x:real^N) <= norm(z) /\ norm(y) <= norm z
         ==> norm(x - y) <= norm(&2 % z:real^N)`) THEN
      ASM_SIMP_TAC[IN_DIFF];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      UNDISCH_TAC
       `!x. x IN s DIFF k
            ==> ((\n. (f:num->real^M->real^N) n x) --> g x) sequentially` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [LIM_NULL] THEN
      DISCH_THEN(MP_TAC o ISPEC
       `(lift o (\x. x rpow p) o  drop) o (lift o (norm:real^N->real))` o
         MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
      ASM_SIMP_TAC[o_THM; DROP_VEC; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM] THEN
      ASM_SIMP_TAC[NORM_0; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_DROP; LIFT_NUM] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_AT_LIFT_NORM] THEN
      GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o CONJUNCT2)] THEN
  REWRITE_TAC[INTEGRAL_0; TENDSTO_REAL; lnorm; o_DEF; LIFT_DROP; LIFT_NUM] THEN
  DISCH_THEN(MP_TAC o ISPEC `lift o (\x. x rpow inv p) o  drop` o
     MATCH_MP(REWRITE_RULE[IMP_CONJ_ALT] LIM_CONTINUOUS_FUNCTION)) THEN
  ASM_SIMP_TAC[o_THM; DROP_VEC; RPOW_ZERO; REAL_LT_IMP_NZ; LIFT_NUM] THEN
  ASM_SIMP_TAC[REAL_INV_EQ_0; REAL_LT_IMP_NZ; LIFT_NUM] THEN ANTS_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM LIFT_DROP] THEN
    REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS_ATREAL] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
  MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Approximation of functions in L_p by bounded ones and continuous ones,    *)
(* and (for bounded domain sets) by purely polynomial ones.                  *)
(* ------------------------------------------------------------------------- *)

let LSPACE_APPROXIMATE_BOUNDED = prove
 (`!f:real^M->real^N s p e.
        &0 < p /\ measurable s /\ f IN lspace s p /\ &0 < e
        ==> ?g. g IN lspace s p /\
                bounded (IMAGE g s) /\
                lnorm s p (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(\n x. (lambda i. max (--(&n)) (min (&n) ((f:real^M->real^N)(x)$i))))
     :num->real^M->real^N`;
    `f:real^M->real^N`;
    `f:real^M->real^N`;
    `s:real^M->bool`; `p:real`; `{}:real^M->bool`]
        LSPACE_DOMINATED_CONVERGENCE) THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  MATCH_MP_TAC(TAUT
   `b /\ c /\ a /\ (a /\ d ==> e)
    ==> (a /\ b /\ c ==> d) ==> e`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
    SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[DIFF_EMPTY] THEN DISCH_TAC THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(ISPEC
      `sup(IMAGE (\i. abs((f:real^M->real^N) x$i)) (1..dimindex(:N)))`
      REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    SIMP_TAC[REAL_SUP_LE_FINITE; FINITE_NUMSEG; NUMSEG_EMPTY;
             NOT_LT; DIMINDEX_GE_1; FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
    SIMP_TAC[FORALL_IN_IMAGE; IN_NUMSEG; CART_EQ; LAMBDA_BETA] THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= n ==> max (--n) (min n x) = x`) THEN
    ASM_MESON_TAC[REAL_OF_NUM_LE; REAL_LE_TRANS];
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL
     [`s:real^M->bool`; `p:real`; `vec n:real^N`] LSPACE_CONST) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:real^M->real^N) IN lspace s p` THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE
     [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] LSPACE_MIN)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL
     [`s:real^M->bool`; `p:real`; `--vec n:real^N`] LSPACE_CONST) THEN
    ASM_REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE
     [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] LSPACE_MAX)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `x = y ==> x IN s ==> y IN s`) THEN
    SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA; VEC_COMPONENT;
             VECTOR_NEG_COMPONENT] THEN REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL; REAL_SUB_RZERO] THEN DISCH_TAC THEN
    EXISTS_TAC
     `(\x. (lambda i. max (-- &n) (min (&n) ((f:real^M->real^N) x$i))))
      :real^M->real^N` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN
      EXISTS_TAC `&(dimindex(:N)) * &n` THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      GEN_REWRITE_TAC
        (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN
      SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; LAMBDA_BETA] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `abs(x) < e ==> x < e`) THEN
      ONCE_REWRITE_TAC[GSYM LNORM_NEG] THEN
      ASM_REWRITE_TAC[VECTOR_NEG_SUB]]]);;

let LSPACE_APPROXIMATE_CONTINUOUS =  prove
 (`!f:real^M->real^N s p e.
        &1 <= p /\ measurable s /\ f IN lspace s p /\ &0 < e
        ==> ?g. g continuous_on (:real^M) /\
                g IN lspace s p /\
                lnorm s p (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP (REAL_ARITH `&1 <= p ==> &0 < p`)) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `p:real`; `e / &2`]
        LSPACE_APPROXIMATE_BOUNDED) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?k g. negligible k /\
          (!n. g n continuous_on (:real^M)) /\
          (!n x. x IN s ==> norm(g n x:real^N) <= norm(B % vec 1:real^N)) /\
          (!x. x IN (s DIFF k)  ==> ((\n. g n x) --> h x) sequentially)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^M->real^N) measurable_on s` MP_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[lspace; IN_ELIM_THM]) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[measurable_on] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(\n x. lambda i. max (--B) (min B (((g n x):real^N)$i))):
                num->real^M->real^N` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      MP_TAC(ISPECL [`(:real^M)`; `(lambda i. B):real^N`]
                CONTINUOUS_ON_CONST) THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MIN) THEN
      MP_TAC(ISPECL [`(:real^M)`; `(lambda i. --B):real^N`]
                CONTINUOUS_ON_CONST) THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MAX) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      SIMP_TAC[LAMBDA_BETA; VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      REAL_ARITH_TAC;
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `ee:real` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(c - a:real^N) <= norm(b - a)
        ==> dist(b,a) < ee ==> dist(c,a) < ee`) THEN
      MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP NORM_BOUND_COMPONENT_LE) THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. ((g:num->real^M->real^N) n) IN lspace s p` ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
    EXISTS_TAC `(\x. B % vec 1):real^M->real^N` THEN
    ASM_SIMP_TAC[LSPACE_CONST] THEN
    ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC(REWRITE_RULE[lebesgue_measurable; indicator]
        MEASURABLE_ON_RESTRICT) THEN
    ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; ETA_AX] THEN
    MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
    ASM_REWRITE_TAC[GSYM MEASURABLE_INTEGRABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g:num->real^M->real^N`; `h:real^M->real^N`;
    `(\x. B % vec 1):real^M->real^N`;
    `s:real^M->bool`; `p:real`; `k:real^M->bool`]
        LSPACE_DOMINATED_CONVERGENCE) THEN
  ASM_SIMP_TAC[LSPACE_CONST] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  EXISTS_TAC `(g:num->real^M->real^N) n` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(\x. f x - (g:num->real^M->real^N) n x) =
    (\x. (f x - h x) + --(g n x - h x))`
  SUBST1_TAC THENL [SIMP_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) LNORM_TRIANGLE o lhand o snd) THEN
  ASM_SIMP_TAC[LSPACE_SUB; ETA_AX; REAL_LT_IMP_LE; LSPACE_NEG] THEN
  MATCH_MP_TAC(REAL_ARITH
   `y < e / &2 /\ z < e / &2 ==> x <= y + z ==> x < e`) THEN
  ASM_SIMP_TAC[LNORM_NEG; REAL_ARITH `abs x < e ==> x < e`]);;

let LSPACE_APPROXIMATE_VECTOR_POLYNOMIAL_FUNCTION = prove
 (`!f:real^M->real^N s p e.
        &1 <= p /\ bounded s /\ measurable s /\ f IN lspace s p /\ &0 < e
        ==> ?g. vector_polynomial_function g /\
                g IN lspace s p /\
                lnorm s p (\x. f x - g x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s:real^M->bool`; `p:real`; `e / &2`]
        LSPACE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_HALF] THEN
  X_GEN_TAC `g:real^M->real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^M->real^N`; `closure s:real^M->bool`;
                 `e / &2 / (measure(s:real^M->bool) rpow (inv p) + &1)`]
        STONE_WEIERSTRASS_VECTOR_POLYNOMIAL_FUNCTION) THEN
  ASM_REWRITE_TAC[REAL_HALF; COMPACT_CLOSURE] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1`) THEN
      ASM_SIMP_TAC[RPOW_POS_LE; MEASURE_POS_LE]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^M->real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC LSPACE_BOUNDED_MEASURABLE_SIMPLE THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
                 MEASURABLE_IMP_LEBESGUE_MEASURABLE;
                 CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (h:real^M->real^N) (closure s)` THEN
    SIMP_TAC[IMAGE_SUBSET; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_VECTOR_POLYNOMIAL_FUNCTION; COMPACT_CLOSURE];
    DISCH_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
   `lnorm s p (\x. (f:real^M->real^N) x - g x) +
    lnorm s p (\x. g x - h x)` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) LNORM_TRIANGLE o rand o snd) THEN
    ASM_SIMP_TAC[LSPACE_SUB; REAL_ARITH `&1 <= p ==> &0 <= p`] THEN
    REWRITE_TAC[VECTOR_ARITH `(f - g) + (g - h):real^N = f - h`];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e / &2 ==> y <= e / &2 ==> x + y < e`))] THEN
  TRANS_TAC REAL_LE_TRANS
   `lnorm (s:real^M->bool) p
          (\x. lift(e / &2 / (measure s rpow inv p + &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^M->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; DIFF_EMPTY] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LSPACE_SUB; LSPACE_CONST; REAL_ARITH `&1 <= p ==> &0 <= p`;
                 NORM_LIFT; REAL_ARITH `x < y ==> x <= abs y`;
                 REWRITE_RULE[SUBSET] CLOSURE_SUBSET];
    ASM_SIMP_TAC[LNORM_CONST; REAL_ARITH `&1 <= p ==> &0 < p`] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_DIV; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[REAL_ARITH
      `&0 < e ==> x * abs e / &2 / y = (x * e / &2) / y`] THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
     [MEASURE_POS_LE; RPOW_POS_LE; REAL_LE_LDIV_EQ;
      REAL_ARITH `abs x = if &0 < x then x else --x`;
      REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    REWRITE_TAC[REAL_ARITH `m * e / &2 <= e / &2 * n <=> e * m <= e * n`] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN REAL_ARITH_TAC]);;
