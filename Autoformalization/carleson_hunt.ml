(* ========================================================================= *)
(* The Carleson-Hunt theorem: for 1 < p, the Fourier series of a             *)
(* 2pi-periodic function in L^p[-pi,pi] converges to it almost everywhere.   *)
(*                                                                           *)
(* This extends Autoformalization/carleson.ml, which proves the case p = 2   *)
(* following Fremlin, Measure Theory vol 2, section 286.  For p >= 2 the     *)
(* result follows at once from the L^2 theorem.  For 1 < p < 2 the proof     *)
(* works with the truncated physical Carleson operator                       *)
(*   T_n f = carleson_Ahat_trunc (fourier f) n                               *)
(* and proceeds as follows.                                                  *)
(*  - A density-capped estimate for the tile model, with logarithmic loss,   *)
(*    for functions dominated by an indicator (after Lacey-Thiele and        *)
(*    Grafakos-Tao-Terwilleger); the near part of the tree energy of an      *)
(*    indicator is controlled by a dyadic Calderon-Zygmund decomposition.    *)
(*  - Transfer of the model estimate to T_n by the averaging argument of     *)
(*    Fremlin 286P-286T, giving restricted weak type (q,q) for every         *)
(*    1 < q <= 2, uniformly in n.                                            *)
(*  - Weak type (p,p) for T_n by a finite dyadic level decomposition.        *)
(*  - The sine-kernel integrals of f are windows of T_n.                     *)
(*  - A Banach-principle argument, with the L^2 theorem applied to the       *)
(*    clamped truncations of f.                                              *)
(* ========================================================================= *)

needs "Autoformalization/carleson.ml";;

prioritize_real();;

(* ========================================================================= *)
(* Preliminaries.                                                            *)
(* ========================================================================= *)

(* The derivative of a Schwartz function is a Schwartz function.             *)
let SCHWARTZ_HAS_DERIV = prove
 (`!(f:real->complex). schwartz f
     ==> ?f'. (!x. ((\z. f(drop z)) has_vector_derivative f' x)
                   (at(lift x))) /\
              schwartz f'`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[schwartz]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->real->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(d:num->real->complex) 1` THEN
  SUBGOAL_THEN `(f:real->complex) = d 0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `x:real`]) THEN REWRITE_TAC[ARITH];
    MATCH_MP_TAC SCHWARTZ_DERIV THEN EXISTS_TAC `(d:num->real->complex) 0` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`0`; `x:real`]) THEN
        REWRITE_TAC[ARITH]]]);;

(* If (\x. lift(f x)) is measurable on s, then so is the complex-valued      *)
(* function (\x. Cx(f x)).                                                   *)
let MEASURABLE_ON_CX = prove
 (`!f:real^M->real s. (\x. lift(f x)) measurable_on s
                      ==> (\x. Cx(f x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [MEASURABLE_ON_COMPONENTWISE] THEN
  X_GEN_TAC `i:num` THEN
  REWRITE_TAC[DIMINDEX_2] THEN STRIP_TAC THEN
    SUBGOAL_THEN `i = 1 \/ i = 2` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_REWRITE_TAC[GSYM RE_DEF; RE_CX];
    ASM_REWRITE_TAC[GSYM IM_DEF; IM_CX; LIFT_NUM; MEASURABLE_ON_0]]);;

(* Absolute integrability passes to Lebesgue measurable subsets.             *)
let ABSINT_ON_LEBMEAS_SUBSET = prove
 (`!h s t. h absolutely_real_integrable_on s /\ t SUBSET s /\
           real_lebesgue_measurable t
           ==> h absolutely_real_integrable_on t`,
  ASM_MESON_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON;
    ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
    REAL_LEBESGUE_MEASURABLE; IMAGE_SUBSET]);;

(* ========================================================================= *)
(* The Plancherel theorem for functions in L^1 cap L^2.                      *)
(* ========================================================================= *)

(* For c in L^1 cap L^2 with fourier c in L^2, ||fourier c||_2 = ||c||_2.    *)
let FOURIER_L1L2_PLANCHEREL = prove
 (`!c:real->complex.
     (\z. c(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. c(drop z)) IN lspace (:real^1) (&2) /\
     (\z. fourier c (drop z)) IN lspace (:real^1) (&2)
     ==> lnorm (:real^1) (&2) (\z. fourier c (drop z)) =
         lnorm (:real^1) (&2) (\z. c(drop z))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FOURIER_L2_REP_NORM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `h:real->complex` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:real->complex`; `h:real->complex`] FOURIER_283O) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SCHWARTZ_ABSINT];
     ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* For every c in L^1 cap L^2, fourier c is in L^2 with the same norm.  The  *)
(* windows c_n = c * 1_[-n,n] have compact support, so fourier c_n is in L^2 *)
(* and ||fourier c_n||_2 = ||c_n||_2 <= ||c||_2 (FOURIER_L1L2_PLANCHEREL).   *)
(* Since c_n -> c in L^1, fourier c_n -> fourier c pointwise, and Fatou      *)
(* gives fourier c in L^2; the norm identity is then FOURIER_L1L2_PLANCHEREL *)
(* for c itself.                                                             *)
(* ------------------------------------------------------------------------- *)

let BALL_DROP = prove
 (`!z:real^1 n. z IN ball(vec 0,&n) <=> abs(drop z) < &n`,
  REWRITE_TAC[IN_BALL; DIST_0; NORM_1]);;

let LNORM1_INTEGRAL = prove
 (`!g:real^1->complex.
     drop(integral (:real^1) (\z. lift(norm(g z)))) = lnorm (:real^1) (&1) g`,
  REWRITE_TAC[lnorm; REAL_INV_1; RPOW_POW; REAL_POW_1]);;

let WINDIFF_DOM = prove
 (`!c:real->complex n z:real^1.
     norm((if abs(drop z) <= &n then (c:real->complex)(drop z)
           else Cx(&0)) - c(drop z))
     <= norm(c(drop z) - (if z IN ball(vec 0,&n)
                          then (c:real->complex)(drop z) else vec 0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BALL_DROP] THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_0; NORM_POS_LE; VECTOR_SUB_RZERO;
    COMPLEX_SUB_LZERO; NORM_NEG] THEN
  ASM_REAL_ARITH_TAC);;

let WINDOW_L2_UNF = prove
 (`!c:real->complex n.
     (\z. c(drop z)) IN lspace (:real^1) (&2)
     ==> (\z. (if abs(drop z) <= &n then (c:real->complex)(drop z)
               else Cx(&0)))
           IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. if abs(drop z) <= &n
                     then (c:real->complex)(drop z) else Cx(&0)) =
                (\z. if abs(drop z) <= &n
                     then (\w. (c:real->complex)(drop w)) z else vec 0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_VEC_0];
    ASM_SIMP_TAC[WINDOW_L2]]);;

let WINDOW_ABSINT_UNF = prove
 (`!c:real->complex n.
     (\z. c(drop z)) IN lspace (:real^1) (&2)
     ==> (\z. (if abs(drop z) <= &n then (c:real->complex)(drop z)
               else Cx(&0)))
           absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CSUPP_L2_ABSINT THEN
    EXISTS_TAC `&n:real` THEN
  ASM_SIMP_TAC[WINDOW_L2_UNF] THEN
  ASM_REAL_ARITH_TAC);;

(* The windowed functions converge to c in L^1 (as a drop-integral of the    *)
(* norm of the difference): the closed-window difference is dominated by the *)
(* ball-truncation difference (WINDIFF_DOM), which tends to 0 by             *)
(* TRUNC_LNORM_LIM at p = 1.                                                 *)
let WINDOW_L1_CONVERGENCE = prove
 (`!c:real->complex.
     (\z. c(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. c(drop z)) IN lspace (:real^1) (&2)
     ==> ((\n. drop(integral (:real^1)
              (\z. lift(norm((if abs(drop z) <= &n
                              then (c:real->complex)(drop z) else Cx(&0)) -
                             c(drop z)))))) ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (c:real->complex)(drop z)) IN lspace (:real^1) (&1)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[LSPACE_1]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\z. (if abs(drop z) <= &n then (c:real->complex)(drop z)
              else Cx(&0)) - c(drop z))
          IN lspace (:real^1) (&1)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[LSPACE_SUB; REAL_POS; LSPACE_1;
     WINDOW_ABSINT_UNF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. (\z. c(drop z) - (if z IN ball(vec 0,&n)
                          then (c:real->complex)(drop z) else vec 0))
          IN lspace (:real^1) (&1)`
   ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC TRUNC_IN_LSPACE THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &1`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
      REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[LNORM1_INTEGRAL] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC
   `\n. lnorm (:real^1) (&1)
        (\z. c(drop z) - (if z IN ball(vec 0,&n)
                          then (c:real->complex)(drop z) else vec 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
     X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `abs(lnorm (:real^1) (&1)
        (\z. (if abs(drop z) <= &n then (c:real->complex)(drop z)
              else Cx(&0)) - c(drop z))) =
      lnorm (:real^1) (&1)
        (\z. (if abs(drop z) <= &n then (c:real->complex)(drop z)
              else Cx(&0)) - c(drop z))`
     SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL; LNORM_POS_LE]; ALL_TAC] THEN
    MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
    ASM_REWRITE_TAC[REAL_POS; NEGLIGIBLE_EMPTY] THEN
    REWRITE_TAC[WINDIFF_DOM];
    MP_TAC(ISPECL [`\z. (c:real->complex)(drop z)`;
      `&1:real`] TRUNC_LNORM_LIM) THEN
    ASM_REWRITE_TAC[REAL_ARITH `&0 < &1`]]);;

(* Plancherel on L^1 cap L^2, by the argument outlined above: if c is in L^1 *)
(* and in L^2, then fourier c is in L^2 and ||fourier c||_2 = ||c||_2.       *)

let FOURIER_L1L2_IN_L2 = prove
 (`!c:real->complex.
     (\z. c(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. c(drop z)) IN lspace (:real^1) (&2)
     ==> (\z. fourier c (drop z)) IN lspace (:real^1) (&2) /\
         lnorm (:real^1) (&2) (\z. fourier c (drop z)) =
         lnorm (:real^1) (&2) (\z. c(drop z))`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `cwin = \n x. if abs x <= &n then (c:real->complex) x
                           else Cx(&0)` THEN
  (* STEP1a: each window in L^2                                              *)
  SUBGOAL_THEN `!n. (\z. (cwin:num->real->complex) n (drop z))
                 IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "cwin" THEN MATCH_MP_TAC WINDOW_L2_UNF THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* STEP1b: each window absolutely integrable                               *)
  SUBGOAL_THEN `!n. (\z. (cwin:num->real->complex) n (drop z))
                 absolutely_integrable_on (:real^1)`
    ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "cwin" THEN MATCH_MP_TAC WINDOW_ABSINT_UNF THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* STEP1c: fourier of each window in L^2                                   *)
  SUBGOAL_THEN `!n. (\z. fourier ((cwin:num->real->complex) n) (drop z))
                 IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `(cwin:num->real->complex) n =
                  (\x. if abs x <= &n
                       then (\w. (c:real->complex)(drop w))(lift x)
                       else Cx(&0))`
    SUBST1_TAC THENL
     [EXPAND_TAC "cwin" THEN REWRITE_TAC[LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC WINDOWED_FOURIER_L2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* STEP2a: Plancherel per window                                           *)
  SUBGOAL_THEN
   `!n. lnorm (:real^1) (&2)
          (\z. fourier ((cwin:num->real->complex) n) (drop z)) =
        lnorm (:real^1) (&2) (\z. (cwin:num->real->complex) n (drop z))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[FOURIER_L1L2_PLANCHEREL]; ALL_TAC] THEN
  (* STEP2b: window L^2-norm <= c L^2-norm                                   *)
  SUBGOAL_THEN
   `!n. lnorm (:real^1) (&2) (\z. (cwin:num->real->complex) n (drop z)) <=
        lnorm (:real^1) (&2) (\z. (c:real->complex)(drop z))`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
    ASM_REWRITE_TAC[REAL_POS; NEGLIGIBLE_EMPTY] THEN
    X_GEN_TAC `z:real^1` THEN EXPAND_TAC "cwin" THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; COMPLEX_NORM_0; NORM_POS_LE];
    ALL_TAC] THEN
  (* STEP3: L^1 convergence of windows to c                                  *)
  SUBGOAL_THEN
   `((\n. drop(integral (:real^1)
       (\z. lift(norm((cwin:num->real->complex) n (drop z) -
                      (c:real->complex)(drop z)))))) ---> &0)
    sequentially`
    ASSUME_TAC THENL
   [EXPAND_TAC "cwin" THEN MATCH_MP_TAC WINDOW_L1_CONVERGENCE THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* STEP4: pointwise fourier convergence                                    *)
  SUBGOAL_THEN
   `!y. ((\n. fourier ((cwin:num->real->complex) n) y) -->
         fourier (c:real->complex) y) sequentially`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[FOURIER_UNIF_LIM_FROM_L1]; ALL_TAC] THEN
  (* STEP5: fourier c in L^2 (Fatou)                                         *)
  SUBGOAL_THEN `(\z. fourier (c:real->complex) (drop z))
                IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC FATOU_L2_LIMIT_MEMBER THEN
    EXISTS_TAC `\k z. fourier ((cwin:num->real->complex) k) (drop z)` THEN
    EXISTS_TAC `lnorm (:real^1) (&2) (\z. (c:real->complex)(drop z))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    MATCH_MP_TAC FOURIER_CONTINUOUS_ON;
    ALL_TAC] THEN
  (* STEP6: norm equality via Plancherel on c itself                         *)
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FOURIER_L1L2_PLANCHEREL THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Carleson theorem for L^p, p >= 2 (a.e. convergence of Fourier series).    *)
(*                                                                           *)
(* For p >= 2 on the finite-measure circle [-pi,pi], L^p is contained in     *)
(* L^2, so a.e. convergence for L^p functions is an immediate corollary of   *)
(* CARLESON_THEOREM (the L^2 case).  The one analytic step is the pointwise  *)
(* bound t^2 <= 1 + t^p (t >= 0, p >= 2), integrated over the finite         *)
(* interval to get square-integrability from L^p-integrability.              *)
(* ========================================================================= *)

(* Pointwise: for t >= 0 and p >= 2, t^2 <= 1 + t rpow p.                    *)
(* (If t <= 1: t^2 <= 1.  If t >= 1: t^2 = t rpow 2 <= t rpow p since p>=2.) *)
let CLP_RPOW_SQ_BOUND = prove
 (`!t p. &0 <= t /\ &2 <= p ==> t pow 2 <= &1 + t rpow p`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `t <= &1` THENL
   [(* t <= 1: t^2 <= 1 <= 1 + t^p *)
    SUBGOAL_THEN `t pow 2 <= &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_1_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= t rpow p` ASSUME_TAC THENL
     [MATCH_MP_TAC RPOW_POS_LE; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `t2 <= tp ==> t2 <= &1 + tp`) THEN
    SUBGOAL_THEN `t pow 2 = t rpow (&2)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM RPOW_POW]; ALL_TAC] THEN
    MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REAL_ARITH_TAC]);;

(* From real-valued L^p on the finite interval [-pi,pi] (p>=2), f is square- *)
(* integrable there.  Uses the pointwise bound + finite measure of [-pi,pi]. *)
let CLP_LP_IMP_SQUARE_INTEGRABLE = prove
 (`!f p. &2 <= p /\
         f real_measurable_on real_interval[--pi,pi] /\
         (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi]
         ==> f square_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[square_integrable_on] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x:real. &1 + abs(f x) rpow p` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_2; REAL_MEASURABLE_ON_MUL];
    ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_CONST];
    ASM_SIMP_TAC[REAL_ABS_POW; CLP_RPOW_SQ_BOUND; REAL_ABS_POS]]);;

(* Carleson for L^p, p >= 2: a.e. convergence of Fourier series.             *)
let CARLESON_THEOREM_LP = prove
 (`!f p. &2 <= p /\
         f real_measurable_on real_interval[--pi,pi] /\
         (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ?s. real_negligible s /\
                 !x. ~(x IN s)
                     ==> ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                              trigonometric_set k x))
                          ---> f x) sequentially`,
  ASM_MESON_TAC[CARLESON_THEOREM; CLP_LP_IMP_SQUARE_INTEGRABLE]);;

(* ========================================================================= *)
(* Smoothness of the wave packets.                                           *)
(*                                                                           *)
(* carleson_phi has a derivative that decays like the Carleson weight cw     *)
(* (CPHI_DERIV_CW), so by the mean-value theorem the difference of two       *)
(* translates keeps the cw decay, with a gain proportional to the            *)
(* displacement (CPHI_DIFF_CW).  With the frequency localisation of the      *)
(* tiles of a tree (TILE_YMID_THROAT) this gives the difference bounds for   *)
(* demodulated packets (PHISIG_DEMOD_DIFF_TILE).                             *)
(* ========================================================================= *)

(* carleson_phi has a derivative psi that decays like the Carleson weight    *)
(* cw: norm(psi u) <= C * cw u (SCHWARTZ_HAS_DERIV gives psi Schwartz, and   *)
(* SCHWARTZ_CW_DOMINATION gives the order-3 cw decay).  With the mean-value  *)
(* theorem this gives the difference bound CPHI_DIFF_CW.                     *)
let CPHI_DERIV_CW = prove
 (`?psi C. (!x. ((\z. carleson_phi(drop z)) has_vector_derivative psi x)
                (at(lift x))) /\
           &0 <= C /\ (!u. norm(psi u) <= C * cw u)`,
  MP_TAC(MATCH_MP SCHWARTZ_HAS_DERIV CARLESON_PHI_SCHWARTZ) THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real->real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(MATCH_MP SCHWARTZ_CW_DOMINATION
    (ASSUME `schwartz(psi:real->real^2)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`psi:real->real^2`; `C:real`] THEN ASM_REWRITE_TAC[]);;

(* tile_ymid (= dyho_mid(k-1)(2nJ), the left-half midpoint) lies in tile_J.  *)
let TILE_YMID_IN_J = prove
 (`!k nI nJ. tile_ymid (k,nI,nJ) IN tile_J (k,nI,nJ)`,
  REPEAT GEN_TAC THEN
    REWRITE_TAC[tile_ymid; tile_J; dyho; dyho_mid; IN_ELIM_THM] THEN
  MP_TAC(ISPEC `k:int` ZPOW2_PRED) THEN
    ABBREV_TAC `m1 = &2 zpow (k - &1)` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < m1` ASSUME_TAC THENL
   [EXPAND_TAC "m1" THEN MATCH_MP_TAC REAL_ZPOW_LT; ALL_TAC] THEN
  ASM_REWRITE_TAC[int_mul_th; int_of_num_th] THEN ASM_REAL_ARITH_TAC);;

(* Two points in the same dyadic interval dyho k n are within 2^k.           *)
let DYHO_TWO_PTS_CLOSE = prove
 (`!k n u v. u IN dyho k n /\ v IN dyho k n ==> abs(u - v) < &2 zpow k`,
  REWRITE_TAC[dyho; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

(* The tree-throat frequency bound, in explicit-triple form.                 *)
let TILE_YMID_TREE_THROAT_TRIPLE = prove
 (`!ks iss js kt it jt.
     tile_le (ks,iss,js) (kt,it,jt)
     ==> abs(tile_ymid (ks,iss,js) - tile_ymid (kt,it,jt)) < &2 zpow ks`,
  REPEAT GEN_TAC THEN REWRITE_TAC[tile_le; tile_J] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`ks:int`;`iss:int`;`js:int`] TILE_YMID_IN_J) THEN
  MP_TAC(ISPECL [`kt:int`;`it:int`;`jt:int`] TILE_YMID_IN_J) THEN
  REWRITE_TAC[tile_J] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `tile_ymid (kt,it,jt) IN dyho ks js` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC DYHO_TWO_PTS_CLOSE THEN
    EXISTS_TAC `js:int` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Comparability of cw under shifts of size at most 1: cw(t + e) <= 8 cw t   *)
(* for |e| <= 1, from the definition of cw and 1 + |t| <= 2 (1 + |t + e|).   *)
(* This bounds the weight at a nearby point, such as the intermediate point  *)
(* of the mean-value theorem, by 8 times the weight at a fixed point.        *)
(* ------------------------------------------------------------------------- *)
let CW_SHIFT_COMPARABLE = prove
 (`!t e:real. abs e <= &1 ==> cw(t + e) <= &8 * cw t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cw] THEN
  SUBGOAL_THEN `&0 < (&1 + abs t) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  SUBGOAL_THEN `&8 * inv((&1 + abs t) pow 3) = inv((&1 + abs t) pow 3 / &8)`
   SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + abs t) pow 3 <= (&2 * (&1 + abs(t + e))) pow 3`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* The demodulated packet.  Multiplying phi_sigma s carleson_phi by the      *)
(* unimodular factor e^(-i btau u) shifts its frequency centre from          *)
(* tile_ymid s to tile_ymid s - btau, i.e. it is a phimst with that relative *)
(* frequency.  On a tree with root tau (btau = tile_ymid tau) the relative   *)
(* frequency tile_ymid s - tile_ymid tau is < 2^(tile_k s)                   *)
(* (TILE_YMID_THROAT).                                                       *)
let PHISIG_DEMOD = prove
 (`!(s:int#int#int) (btau:real) (u:real).
     cexp(--(ii*Cx btau*Cx u)) * phi_sigma s carleson_phi u =
     phimst (&2 zpow (tile_k s)) (tile_xmid s) (tile_ymid s - btau)
            carleson_phi u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[phi_sigma; phimst] THEN
  SUBGOAL_THEN
   `cexp(--(ii*Cx btau*Cx u)) * cexp(ii * Cx(tile_ymid s) * Cx u) =
    cexp(ii * Cx(tile_ymid s - btau) * Cx u)`
   ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_ADD] THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_SUB] THEN CONV_TAC COMPLEX_RING;
    ONCE_REWRITE_TAC[COMPLEX_RING
     `(a:complex) * b * c * d = b * (a * c) * d`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The cw-decaying difference bound for carleson_phi.  On a short segment    *)
(* (|a - b| <= 1) the difference is controlled by the derivative bound       *)
(* (CPHI_DERIV_CW: norm(psi) <= C cw) times |a - b|, with the cw weight      *)
(* evaluated at the endpoint a (VECTOR_DIFFERENTIABLE_BOUND on [a,b], the    *)
(* derivative bound being made uniform on the segment by                     *)
(* CW_SHIFT_COMPARABLE).  The difference thus keeps the cw decay, not merely *)
(* a Lipschitz constant, so that two-bump lattice sums over a slice of a     *)
(* tree stay bounded.                                                        *)
(* ------------------------------------------------------------------------- *)
let CPHI_DIFF_CW = prove
 (`?C. &0 <= C /\
       !a b:real. abs(a - b) <= &1
         ==> norm(carleson_phi a - carleson_phi b) <= C * cw a * abs(a - b)`,
  X_CHOOSE_THEN `psi:real->complex` (X_CHOOSE_THEN `C0:real`
    (CONJUNCTS_THEN2 (LABEL_TAC "deriv")
       (CONJUNCTS_THEN2 (LABEL_TAC "cpos") (LABEL_TAC "cwbd"))))
    CPHI_DERIV_CW THEN
  EXISTS_TAC `&8 * C0` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `lift a IN interval[lift(min a b), lift(max a b)] /\
    lift b IN interval[lift(min a b), lift(max a b)]`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^1. carleson_phi(drop z)`;
    `\z:real^1. (psi:real->complex)(drop z)`;
    `interval[lift(min a b), lift(max a b)]`;
    `&8 * C0 * cw a`] VECTOR_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONVEX_INTERVAL];
      ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_AT_WITHIN; LIFT_DROP];
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN X_GEN_TAC `w:real^1` THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `C0 * cw(drop w)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `&8 * C0 * cw a = C0 * (&8 * cw a)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `drop w = a + (drop w - a)` SUBST1_TAC THENL
        [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CW_SHIFT_COMPARABLE THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPECL [`lift a`; `lift b`]) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT; REAL_MUL_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Small ring identities.                                                    *)
(* ------------------------------------------------------------------------- *)
let MDIFF_RING = prove
 (`!m y yp c:real. m*(y - c) - m*(yp - c) = m*(y - yp)`,
  CONV_TAC REAL_RING);;

let MDISTRIB_RING = prove
 (`!beta y yp:real. beta * y - beta * yp = beta * (y - yp)`,
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The cw-decaying envelope difference at the DILATED argument.  From        *)
(* CPHI_DIFF_CW with a := m(y-c), b := m(yp-c) (so |a-b| = m|y-yp| <= 1 in   *)
(* the coarse regime), the envelope difference gains the m*|y-yp| factor     *)
(* with cw-decay at m(y-c).                                                  *)
(* ------------------------------------------------------------------------- *)
let CPHI_DIFF_MSCALE = prove
 (`?C. &0 <= C /\
       !(m:real) (y:real) (yp:real) (c:real).
          &0 < m /\ m * abs(y - yp) <= &1
          ==> norm(carleson_phi(m*(y - c)) - carleson_phi(m*(yp - c)))
              <= C * cw(m*(y - c)) * (m * abs(y - yp))`,
  X_CHOOSE_THEN `Ce:real` STRIP_ASSUME_TAC CPHI_DIFF_CW THEN
  EXISTS_TAC `Ce:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(m*(y - c) - m*(yp - c)) = m * abs(y - yp)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MDIFF_RING; REAL_ABS_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(INST [`m*(y - c):real`,`a:real`; `m*(yp - c):real`,`b:real`]
    (SPEC_ALL (ASSUME `!a b:real. abs(a - b) <= &1
       ==> norm(carleson_phi a - carleson_phi b) <=
           Ce * cw a * abs(a - b)`))) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN ASM_REWRITE_TAC[REAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* THE PACKET-DIFFERENCE BOUND (heart of the coarse regime).  For the        *)
(* DE-MODULATED wave packet Cx(sqrt m) e^{i beta u} cphi(m(u - c)) with      *)
(* frequency |beta| <= m (the tree throat gives this after de-modulation),   *)
(* the y-difference gains the full m*|y-y'| factor with cw-decay at the      *)
(* midpoint m(y - c), in the coarse regime m|y-y'| <= 1.  Add-subtract the   *)
(* cross term: the ENVELOPE piece (CPHI_DIFF_MSCALE) and the MODULATION      *)
(* piece (CEXP_II_DIFF_BOUND, |cexp diff| <= |beta||y-y'| <= m|y-y'|) both   *)
(* carry the gain; CW_SHIFT_COMPARABLE aligns the y'-bump to the y-bump.     *)
(* ------------------------------------------------------------------------- *)
let PHIMST_DEMOD_DIFF = prove
 (`?Cdiff. &0 <= Cdiff /\
     !(m:real) (beta:real) (c:real) (y:real) (yp:real).
        &0 < m /\ abs beta <= m /\ m * abs(y - yp) <= &1
        ==> norm((Cx(sqrt m) * cexp(ii*Cx beta*Cx y) *
                  carleson_phi(m*(y - c))) -
                 (Cx(sqrt m) * cexp(ii*Cx beta*Cx yp) *
                  carleson_phi(m*(yp - c))))
            <= Cdiff * sqrt m * (m * abs(y - yp)) * cw(m*(y - c))`,
  X_CHOOSE_THEN `Ce:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ce"))
    CPHI_DIFF_MSCALE THEN
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "c1"))
    CARLESON_PHI_CW THEN
  EXISTS_TAC `Ce + &8 * C1` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `mm = sqrt m` THEN
  SUBGOAL_THEN `&0 <= mm` ASSUME_TAC THENL
   [ASM_MESON_TAC[SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= m * abs(y - yp)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cx mm * cexp(ii*Cx beta*Cx y) * carleson_phi(m*(y - c))) -
    (Cx mm * cexp(ii*Cx beta*Cx yp) * carleson_phi(m*(yp - c))) =
    Cx mm * (cexp(ii*Cx beta*Cx y) *
                (carleson_phi(m*(y - c)) - carleson_phi(m*(yp - c)))) +
    Cx mm * ((cexp(ii*Cx beta*Cx y) - cexp(ii*Cx beta*Cx yp)) *
                carleson_phi(m*(yp - c)))`
   SUBST1_TAC THENL [CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(Cx mm * (cexp(ii*Cx beta*Cx y) *
                (carleson_phi(m*(y - c)) - carleson_phi(m*(yp - c))))) +
    norm(Cx mm * ((cexp(ii*Cx beta*Cx y) - cexp(ii*Cx beta*Cx yp)) *
                carleson_phi(m*(yp - c))))` THEN
  CONJ_TAC THENL [REWRITE_TAC[NORM_TRIANGLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Ce + &8 * C1) * mm * (m * abs(y - yp)) * cw(m*(y - c)) =
    (mm * (Ce * cw(m*(y - c)) * (m * abs(y - yp)))) +
    (mm * ((m * abs(y - yp)) * (&8 * C1) * cw(m*(y - c))))`
   SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= mm ==> abs mm = mm`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(cexp(ii*Cx beta*Cx y)) *
                norm(carleson_phi(m*(y - c)) - carleson_phi(m*(yp - c)))` THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM CX_MUL; NORM_CEXP_II; REAL_MUL_LID] THEN
    USE_THEN "ce" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= mm ==> abs mm = mm`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(m * abs(y - yp)) * norm(carleson_phi(m*(yp - c)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
       REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM CX_MUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `abs(beta * y - beta * yp)` THEN
        REWRITE_TAC[CEXP_II_DIFF_BOUND; MDISTRIB_RING; REAL_ABS_MUL] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
        ASM_ARITH_TAC];
      REWRITE_TAC[REAL_ARITH
       `(m * abs(y - yp)) * (&8 * C1) * cw(m*(y - c)) =
        (m * abs(y - yp)) * (&8 * C1 * cw(m*(y - c)))`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `C1 * cw(m*(yp - c))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REWRITE_TAC[REAL_ARITH `&8 * C1 * z = C1 * &8 * z`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `cw(m*(y - c) + (m*(yp - c) - m*(y - c))) <=
                      &8 * cw(m*(y - c))`
         MP_TAC THENL
         [MATCH_MP_TAC CW_SHIFT_COMPARABLE THEN
          REWRITE_TAC[MDIFF_RING; REAL_ABS_MUL] THEN
          ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
          ASM_SIMP_TAC[REAL_ARITH `&0 < m ==> abs m = m`];
          REWRITE_TAC[REAL_SUB_ADD2]]]]]);;

(* ------------------------------------------------------------------------- *)
(* The tree throat in usable tile form: for s <=_r t, the frequency          *)
(* centers are within 2^(tile_k s).  (TILE_YMID_TREE_THROAT_TRIPLE +         *)
(* TILE_LER_IMP_LE, destructuring the triple.)                               *)
(* ------------------------------------------------------------------------- *)
let TILE_YMID_THROAT = prove
 (`!(s:int#int#int) (t:int#int#int).
     tile_ler s t
     ==> abs(tile_ymid s - tile_ymid t) < &2 zpow (tile_k s)`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`ks:int`;`iss:int`;`js:int`;`kt:int`;`it:int`;`jt:int`] THEN
  DISCH_TAC THEN REWRITE_TAC[tile_k] THEN
  MATCH_MP_TAC TILE_YMID_TREE_THROAT_TRIPLE THEN
  MATCH_MP_TAC TILE_LER_IMP_LE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Per-tile DE-MODULATED difference bound in phi_sigma form.  For a tile     *)
(* s <=_r tau the throat forces the relative frequency |tile_ymid s -        *)
(* tile_ymid tau| < 2^(tile_k s), so PHIMST_DEMOD_DIFF applies with beta =   *)
(* tile_ymid s - tile_ymid tau, m = 2^(tile_k s), c = tile_xmid s, giving    *)
(* the coarse-regime packet-difference bound with the 2^k*|y-y'| gain and    *)
(* cw-decay at the spatial midpoint 2^k(y - x_s).                            *)
(* ------------------------------------------------------------------------- *)
let PHISIG_DEMOD_DIFF_TILE = prove
 (`?Cdiff. &0 <= Cdiff /\
     !(s:int#int#int) (tau:int#int#int) (y:real) (yp:real).
        tile_ler s tau /\ (&2 zpow (tile_k s)) * abs(y - yp) <= &1
        ==> norm((cexp(--(ii*Cx(tile_ymid tau)*Cx y)) *
                  phi_sigma s carleson_phi y) -
                 (cexp(--(ii*Cx(tile_ymid tau)*Cx yp)) *
                  phi_sigma s carleson_phi yp))
            <= Cdiff * sqrt(&2 zpow (tile_k s)) *
               ((&2 zpow (tile_k s)) * abs(y - yp)) *
               cw((&2 zpow (tile_k s)) * (y - tile_xmid s))`,
  X_CHOOSE_THEN `Cdiff:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dd"))
    PHIMST_DEMOD_DIFF THEN
  EXISTS_TAC `Cdiff:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[PHISIG_DEMOD; phimst] THEN
  USE_THEN "dd" (MP_TAC o ISPECL
   [`&2 zpow (tile_k s)`; `tile_ymid s - tile_ymid tau`;
    `tile_xmid s`; `y:real`; `yp:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_IMP_LE; TILE_YMID_THROAT];
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The single-tree operator L^2 bound                                        *)
(*   ||T_T f||_2 <= C * ||f||_2,  uniformly in the tree T,                   *)
(* where T_T f = vsum {s in tree} (\s. carleson_ip f s * phi_sigma s         *)
(* carleson_phi).                                                            *)
(*                                                                           *)
(* The frame bound FTILDE_L2_NORM_C (||sum c_s phi_s||_2^2 <= C3 sum         *)
(* |c_s|^2) at c_s = carleson_ip f s gives ||T_T f||_2^2 <= C3 * E, where E  *)
(* = sum_{tree} |<f,phi_s>|^2; CARLESON_BESSEL_IP gives <f,T_T f> = Cx E,    *)
(* and Cauchy-Schwarz gives E <= ||f||_2 ||T_T f||_2; the abstract           *)
(* combination CH_L2_COMBINE then yields ||T_T f||_2 <= C3 ||f||_2.          *)
(* ========================================================================= *)

(* Abstract combine: Ng^2 <= C3 E and E <= Nf Ng (all nonneg) ==> Ng <= C3   *)
(* Nf.                                                                       *)
let CH_L2_COMBINE = prove
 (`!Ng Nf E C3:real.
     &0 <= Ng /\ &0 <= Nf /\ &0 <= E /\ &0 <= C3 /\
     Ng pow 2 <= C3 * E /\ E <= Nf * Ng
     ==> Ng <= C3 * Nf`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `Ng = &0` THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Ng` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Ng pow 2 <= C3 * (Nf * Ng)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_LMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `Ng * Ng <= (C3 * Nf) * Ng` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ]);;

(* The tree frame bound ||T_T f||_2^2 <= C3 * E (FTILDE_L2_NORM_C at c :=    *)
(* carleson_ip f).                                                           *)
let CH_TREE_L2_FRAME = prove
 (`!(f:real->complex) (P:(int#int#int)->bool) tau C3.
     FINITE P /\ &0 <= C3 /\
     (!c Q ta. FINITE Q ==> drop(integral (:real^1)
        (\z. lift(norm(vsum {s | s IN Q /\ tile_ler s ta}
                       (\s. c s * phi_sigma s carleson_phi (drop z))) pow 2)))
        <= C3 * sum {s | s IN Q /\ tile_ler s ta} (\s. norm(c s) pow 2))
     ==> lnorm (:real^1) (&2)
           (\z. vsum {s | s IN P /\ tile_ler s tau}
                     (\s. carleson_ip f s *
                          phi_sigma s carleson_phi (drop z))) pow 2
         <= C3 * sum {s | s IN P /\ tile_ler s tau}
                     (\s. norm(carleson_ip f s) pow 2)`,
  ASM_SIMP_TAC[CARLESON_RECON_L2_C; FINITE_RESTRICT; LNORM2_SQ]);;

(* The bound E <= ||f||_2 ||T_T f||_2.  By the Bessel identity <f,T_T f> =   *)
(* Cx E (CARLESON_BESSEL_IP) and the Cauchy-Schwarz inequality,              *)
(*   E <= |<f,T_T f>| <= ||f||_2 ||T_T f||_2.                                *)
let CH_TREE_BESSEL_CS = prove
 (`!(f:real->complex) (P:(int#int#int)->bool) tau.
     (\z. f(drop z)) IN lspace (:real^1) (&2) /\ FINITE P
     ==> sum {s | s IN P /\ tile_ler s tau} (\s. norm(carleson_ip f s) pow 2)
         <= lnorm (:real^1) (&2) (\z. f(drop z)) *
            lnorm (:real^1) (&2)
              (\z. vsum {s | s IN P /\ tile_ler s tau}
                        (\s. carleson_ip f s *
                             phi_sigma s carleson_phi (drop z)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Tt = {s:int#int#int | s IN P /\ tile_ler s tau}` THEN
  SUBGOAL_THEN `FINITE(Tt:(int#int#int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tt" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:int#int#int. s IN Tt
     ==> (\z:real^1. f(drop z) * cnj(phi_sigma s carleson_phi (drop z)))
         integrable_on (:real^1)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[L2_CNJ_PRODUCT_INTEGRABLE; SCHWARTZ_L2; ETA_AX;
     PHISIG_CARLESON_SCHWARTZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->complex`;
    `Tt:(int#int#int)->bool`] CARLESON_BESSEL_IP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. vsum Tt (\s. carleson_ip (f:real->complex) s *
                      phi_sigma s carleson_phi (drop z)))
    IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARLESON_RECON_L2_C]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. (\w. f(drop w)) z *
         cnj((\z. vsum Tt (\s. carleson_ip (f:real->complex) s *
                               phi_sigma s carleson_phi (drop z))) z))
    integrable_on (:real^1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[L2_CNJ_PRODUCT_INTEGRABLE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(lproduct (:real^1) (\z. f(drop z))
     (\z. vsum Tt (\s. carleson_ip (f:real->complex) s *
                       phi_sigma s carleson_phi (drop z))))` THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[LPRODUCT_CAUCHY_SCHWARZ]]);;

(* The single-tree operator L^2 bound, uniform in the tree.                  *)
let CH_TREE_OPERATOR_L2 = prove
 (`?C. &0 <= C /\
    !(f:real->complex) (P:(int#int#int)->bool) tau.
        (\z. f(drop z)) IN lspace (:real^1) (&2) /\ FINITE P
        ==> lnorm (:real^1) (&2)
              (\z. vsum {s | s IN P /\ tile_ler s tau}
                        (\s. carleson_ip f s *
                             phi_sigma s carleson_phi (drop z)))
            <= C * lnorm (:real^1) (&2) (\z. f(drop z))`,
  X_CHOOSE_THEN `C3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fl"))
    FTILDE_L2_NORM_C THEN
  EXISTS_TAC `C3:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CH_L2_COMBINE THEN
  EXISTS_TAC `sum {s | s IN P /\ tile_ler s tau}
                  (\s. norm(carleson_ip (f:real->complex) s) pow 2)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[LNORM_POS_LE; CARLESON_RECON_L2_C; FINITE_RESTRICT];
    ASM_SIMP_TAC[LNORM_POS_LE];
    ASM_SIMP_TAC[SUM_POS_LE; REAL_LE_POW_2];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[CH_TREE_L2_FRAME];
    ASM_SIMP_TAC[CH_TREE_BESSEL_CS]]);;

(* ========================================================================= *)
(* The exceptional set: Omega_t = {x | forward-maximal(1_Ff)(x) > t} has     *)
(* measure <= |Ff|/t, by the weak type (1,1) bound MAXIMAL_WEAK_TYPE.        *)
(* ========================================================================= *)

(* Indicator of a measurable set: real-integrable on R with integral =       *)
(* measure.                                                                  *)
let CH_INDICATOR_REAL_INTEGRABLE = prove
 (`!Ff. real_measurable Ff
     ==> (\x. if x IN Ff then &1 else &0) real_integrable_on (:real) /\
         real_integral (:real) (\x. if x IN Ff then &1 else &0) =
         real_measure Ff`,
  SIMP_TAC[GSYM REAL_MEASURABLE_REAL_INTEGRABLE;
           REAL_INTEGRAL_REAL_MEASURE_UNIV]);;

(* Weak type (1,1) in the form measure <= integral / t, for any integrable   *)
(* nonnegative g.                                                            *)
let CH_MAXWEAK_MEASURE = prove
 (`!g t. g real_integrable_on (:real) /\ (!x. &0 <= g x) /\ &0 < t
     ==> t * real_measure {x | ?a. x < a /\
                    (a - x) * t < real_integral (real_interval[x,a]) g}
         <= real_integral (:real) g`,
  ASM_MESON_TAC[MAXIMAL_WEAK_TYPE; REAL_LE_TRANS; REAL_INTEGRAL_SUBSET_LE;
    SUBSET_UNIV; MAXIMAL_SUPERLEVEL_INTEGRABLE]);;

(* The exceptional-set bound: t * |Omega_t| <= |Ff|.                         *)
let CH_EXCEPTIONAL_SET = prove
 (`!Ff t. real_measurable Ff /\ &0 < t
     ==> t * real_measure {x | ?a. x < a /\
                    (a - x) * t < real_integral (real_interval[x,a])
                                    (\y. if y IN Ff then &1 else &0)}
         <= real_measure Ff`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `Ff:real->bool` CH_INDICATOR_REAL_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if can (term_match [] `real_integral (:real) gg = m:real`) (concl th)
    then GEN_REWRITE_TAC RAND_CONV [SYM th] else NO_TAC) THEN
  MATCH_MP_TAC CH_MAXWEAK_MEASURE THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The (Cx-valued) indicator of a real_measurable set is in L^2 on the line. *)
let CH_CHI_LSPACE2 = prove
 (`!Ff. real_measurable Ff
     ==> (\z. if drop z IN Ff then Cx(&1) else Cx(&0))
       IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. if drop z IN Ff then Cx(&1) else Cx(&0)) =
                (\z:real^1. if z IN {w | drop w IN Ff} then Cx(&1)
                            else Cx(&0))` SUBST1_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CARLESON_CHI_L2_UNIV THEN
  SUBGOAL_THEN `{w:real^1 | drop w IN Ff} = IMAGE lift Ff` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
     MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_MEASURABLE_MEASURABLE]);;

(* ========================================================================= *)
(* The packet-coefficient bound for indicators                               *)
(*   |carleson_ip 1_F s| <= C1 * 2^{-k/2} * int_F cw_tile_s.                 *)
(* carleson_ip 1_F s is the integral of cnj phi_s over lift F, which         *)
(* INTEGRAL_NORM_BOUND_INTEGRAL bounds by the pointwise packet bound         *)
(* PHISIG_CW (|phi_s| <= C1 2^{-k/2} cw_tile_s).                             *)
(* ========================================================================= *)

(* carleson_ip of an indicator is the (:real^1) integral of the restricted   *)
(* conjugate packet.                                                         *)
let CH_IP_INDICATOR_EQ = prove
 (`!Ff (s:int#int#int).
     carleson_ip (\x. if x IN Ff then Cx(&1) else Cx(&0)) s =
     integral (:real^1)
       (\z. if drop z IN Ff then cnj(phi_sigma s carleson_phi (drop z))
            else vec 0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carleson_ip; lproduct] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]);;

(* The (:real^1) integral of the restricted integrand as an integral over    *)
(* IMAGE lift Ff (INTEGRAL_RESTRICT_UNIV).                                   *)
let CH_IP_INDICATOR_EQ2 = prove
 (`!Ff (s:int#int#int).
     carleson_ip (\x. if x IN Ff then Cx(&1) else Cx(&0)) s =
     integral (IMAGE lift Ff) (\z. cnj(phi_sigma s carleson_phi (drop z)))`,
  REWRITE_TAC[CH_IP_INDICATOR_EQ; GSYM(ISPECL
    [`\z:real^1. cnj(phi_sigma (s:int#int#int) carleson_phi (drop z))`;
     `IMAGE lift (Ff:real->bool)`]
    INTEGRAL_RESTRICT_UNIV); IN_IMAGE_LIFT_DROP]);;

(* The real/lift bridge for c * cw_tile on a measurable set A: the lifted    *)
(* function is integrable, and the drop of its integral is c * real_integral *)
(* A cw_tile.                                                                *)
let CW_LIFT_BRIDGE = prove
 (`!c (s:int#int#int) A. real_measurable A
     ==> (\z:real^1. lift(c * cw_tile s (drop z)))
       integrable_on (IMAGE lift A) /\
         c * real_integral A (\x. cw_tile s x) =
         drop(integral (IMAGE lift A) (\z. lift(c * cw_tile s (drop z))))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\x. cw_tile (s:int#int#int) x)
                 real_integrable_on A` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ETA_AX; CWTILE_INTEGRABLE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z:real^1. lift(c * cw_tile (s:int#int#int) (drop z))) =
    lift o (\x. c * cw_tile s x) o drop`
   ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM REAL_INTEGRABLE_ON] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `c * real_integral A (\x. cw_tile (s:int#int#int) x) =
      real_integral A (\x. c * cw_tile s x)`
     SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_LMUL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRAL THEN
    MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[]]);;

(* the F-restricted conjugate packet is absolutely integrable on lift F      *)
(* (cnj is linear; PHISIG_ABS_INTEGRABLE_MEASURABLE gives the base packet).  *)
let CH_CNJ_PHISIG_ABSINT = prove
 (`!(s:int#int#int) A. real_measurable A
     ==> (\z. cnj(phi_sigma s carleson_phi (drop z)))
       absolutely_integrable_on (IMAGE lift A)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. cnj(phi_sigma (s:int#int#int) carleson_phi (drop z))) =
    cnj o (\z. phi_sigma s carleson_phi (drop z))`
   SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN
  REWRITE_TAC[LINEAR_CNJ] THEN
  MATCH_MP_TAC PHISIG_ABS_INTEGRABLE_MEASURABLE THEN ASM_REWRITE_TAC[]);;

(* drop-of-lift-integral collapse: the vector integral of the lift of        *)
(* c*cw_tile over lift A equals c*real_integral A cw_tile.                   *)
let CH_DROP_INT_EQ = prove
 (`!c (s:int#int#int) A. real_measurable A
     ==> drop(integral (IMAGE lift A)(\z. lift(c * cw_tile s (drop z)))) =
         c * real_integral A (cw_tile s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:int#int#int`; `A:real->bool`] CW_LIFT_BRIDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) then GEN_REWRITE_TAC LAND_CONV [SYM th]
    else failwith "s") THEN
  REWRITE_TAC[ETA_AX]);;

(* The packet-coefficient bound for an indicator.                            *)
let CH_IP_INDICATOR_LE = prove
 (`?C1. &0 <= C1 /\
     !Ff (s:int#int#int). real_measurable Ff
        ==> norm(carleson_ip (\x. if x IN Ff then Cx(&1) else Cx(&0)) s)
            <= C1 * inv(sqrt(&2 zpow (tile_k s))) *
               real_integral Ff (\x. cw_tile s x)`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cw"))
    PHISIG_CW THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`Ff:real->bool`; `s:int#int#int`] THEN DISCH_TAC THEN
  REWRITE_TAC[CH_IP_INDICATOR_EQ2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (IMAGE lift Ff)
                (\z. lift((C1 * inv(sqrt(&2 zpow (tile_k (s:int#int#int))))) *
                          cw_tile s (drop z))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; CH_CNJ_PHISIG_ABSINT];
      ASM_SIMP_TAC[CW_LIFT_BRIDGE];
      ASM_MESON_TAC[COMPLEX_NORM_CNJ; LIFT_DROP; REAL_MUL_ASSOC]];
    ASM_SIMP_TAC[CH_DROP_INT_EQ; ETA_AX; REAL_MUL_ASSOC; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The straddling-average bound for an indicator.  The averages of 1_F are   *)
(* all <= 1, so hl_maximal(1_F) is a genuine supremum, and every straddling  *)
(* average of 1_F over [a,b] (a <= x <= b) is <= hl_maximal(1_F)(x).  This   *)
(* is the hypothesis int_[a,b] f <= M(b-a) of MCM_MAXIMAL_DOMINATION with M  *)
(* = hl_maximal(1_F)(x).                                                     *)
(* ------------------------------------------------------------------------- *)

(* |1_F| = 1_F.                                                              *)
let CH_HL_INDICATOR_ABS_EQ = prove
 (`!(Ff:real->bool) x.
     abs(if x IN Ff then &1 else &0) = (if x IN Ff then &1 else &0)`,
  REAL_ARITH_TAC);;

(* 1_F integrable on any bounded interval (restrict the (:real) integral).   *)
let CH_INDICATOR_INTEGRABLE_INTERVAL = prove
 (`!(Ff:real->bool) a b. real_measurable Ff
     ==> (\x. if x IN Ff then &1 else &0)
       real_integrable_on real_interval[a,b]`,
  ASM_MESON_TAC[REAL_INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV;
    CH_INDICATOR_REAL_INTEGRABLE]);;

(* int_[a,b] 1_F <= b - a  (indicator <= 1).                                 *)
let CH_INDICATOR_INT_LE_LEN = prove
 (`!(Ff:real->bool) a b. real_measurable Ff /\ a <= b
     ==> real_integral (real_interval[a,b]) (\x. if x IN Ff then &1 else &0)
         <= b - a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[a,b]) (\x:real. &1)` THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[CH_INDICATOR_INTEGRABLE_INTERVAL; REAL_INTEGRABLE_CONST] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_INTEGRAL_CONST; REAL_MUL_LID; REAL_LE_REFL]]);;

(* The straddling-average bound.                                             *)
let CH_HL_INDICATOR_STRADDLE = prove
 (`!(Ff:real->bool) a b x. real_measurable Ff /\ a <= x /\ x <= b /\ a < b
     ==> real_integral (real_interval[a,b]) (\t. if t IN Ff then &1 else &0)
         <= hl_maximal (\t. if t IN Ff then &1 else &0) x * (b - a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b])
      (\t. if t IN Ff then &1 else &0) / (b - a)
    <= hl_maximal (\t. if t IN Ff then &1 else &0) x` MP_TAC THENL
   [REWRITE_TAC[hl_maximal] THEN MATCH_MP_TAC REAL_LE_SUP THEN
    EXISTS_TAC `&1` THEN
    EXISTS_TAC `real_integral (real_interval[a,b])
                  (\t. if t IN Ff then &1 else &0) / (b - a)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
       MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN
      ASM_REWRITE_TAC[] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[FUN_EQ_THM] THEN
      REAL_ARITH_TAC;
      ASM_ARITH_TAC;
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < q - p` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN
       `real_integral (real_interval[p,q])
          (\t. abs(if t IN (Ff:real->bool) then &1 else &0)) =
        real_integral (real_interval[p,q]) (\t. if t IN Ff then &1 else &0)`
       SUBST1_TAC THENL
       [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
      MP_TAC(SPECL [`Ff:real->bool`; `p:real`;
        `q:real`] CH_INDICATOR_INT_LE_LEN) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  RULE_ASSUM_TAC(fun th ->
    try REWRITE_RULE[MATCH_MP REAL_LE_LDIV_EQ (ASSUME `&0 < b - a`)] th
    with _ -> th) THEN
  ASM_REWRITE_TAC[]);;

(* cw_tile_s is bounded by 2^k (CW_TILE_POS, CW_LE_1).                       *)
let CW_TILE_BOUNDED = prove
 (`!s:int#int#int. real_bounded (IMAGE (cw_tile s) (:real))`,
  GEN_TAC THEN REWRITE_TAC[real_bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
  EXISTS_TAC `&2 zpow (tile_k (s:int#int#int))` THEN X_GEN_TAC `x:real` THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k (s:int#int#int))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cw_tile (s:int#int#int) x` ASSUME_TAC THENL
   [REWRITE_TAC[CW_TILE_POS]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < c ==> abs c = c`] THEN
  REWRITE_TAC[cw_tile] THEN
  MP_TAC(SPEC `&2 zpow (tile_k (s:int#int#int)) * (x - tile_xmid s)`
    CW_LE_1) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* 1_F absolutely-real-integrable on R (integrable, and abs 1_F = 1_F).      *)
let CH_INDICATOR_ABSINT = prove
 (`!(Ff:real->bool). real_measurable Ff
     ==> (\x. if x IN Ff then &1 else &0)
       absolutely_real_integrable_on (:real)`,
  SIMP_TAC[absolutely_real_integrable_on; CH_HL_INDICATOR_ABS_EQ;
           CH_INDICATOR_REAL_INTEGRABLE]);;

(* The maximal function of the indicator of a measurable set is nonnegative, *)
(* as a supremum of nonnegative averages of |1_F| = 1_F; it is a genuine     *)
(* supremum since 1_F is integrable and bounded by 1 (HL_MAXIMAL_POS).       *)
let CH_HL_INDICATOR_POS = prove
 (`!(Ff:real->bool) x. real_measurable Ff
     ==> &0 <= hl_maximal (\t. if t IN Ff then &1 else &0) x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HL_MAXIMAL_POS THEN
  EXISTS_TAC `&1` THEN
  ASM_SIMP_TAC[CH_HL_INDICATOR_ABS_EQ; CH_INDICATOR_REAL_INTEGRABLE] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Comparability of maximal averages at nearby points.  An averaging         *)
(* interval realising M(1_F)(xmid_s) can be enlarged to contain a point y of *)
(* tile_I s, at a cost of at most a factor 2 in the average; with the        *)
(* trivial bound 1 for small intervals this gives M(1_F)(x) <= max(2 *       *)
(* M(1_F)(x'), 1).  (The naive comparison M(x) <= C * M(x') is false for     *)
(* small averaging intervals.)                                               *)
(* ------------------------------------------------------------------------- *)

(* avg_[c,d] 1_F <= 1 (from int_[c,d] 1_F <= d-c).                           *)
let CH_INDICATOR_AVG_LE_1 = prove
 (`!(Ff:real->bool) c d. real_measurable Ff /\ c < d
     ==> real_integral (real_interval[c,d])
           (\t. abs(if t IN Ff then &1 else &0)) / (d - c) <= &1`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CH_HL_INDICATOR_ABS_EQ; REAL_LE_LDIV_EQ; REAL_SUB_LT;
               REAL_MUL_LID; CH_INDICATOR_INT_LE_LEN; REAL_LT_IMP_LE]);;

(* The tile geometry: every point of tile_I s is within half the cell        *)
(* length, 2^{-k}/2 with k = tile_k s, of the cell midpoint tile_xmid s.     *)
(* For s = (k,nI,nJ) this is DYHO_MEM_BAND, since tile_I s = dyho (--k) nI   *)
(* and tile_xmid s = dyho_mid (--k) nI.                                      *)
let CH_TILE_BAND = prove
 (`!(s:int#int#int) y.
     y IN tile_I s ==> abs(y - tile_xmid s) <= &2 zpow (--(tile_k s)) / &2`,
  REWRITE_TAC[FORALL_PAIR_THM; tile_I; tile_xmid; tile_k] THEN
  MAP_EVERY X_GEN_TAC [`p1:int`; `p1':int`; `y:real`] THEN
    MP_TAC(ISPECL [`--p1:int`; `p1':int`; `y:real`] DYHO_MEM_BAND) THEN
  ASM_REWRITE_TAC[]);;

(* The reflected indicator is the indicator of the reflected set: (\t. 1_Ff  *)
(* t)(--y) = 1_{IMAGE (\z. --z) Ff}(y).  With HL_BWD_REFLECT (bwd f x = fwd  *)
(* (f o neg) (--x)) this reduces the backward maximal function of an         *)
(* indicator to the forward one.                                             *)
let CH_INDICATOR_REFLECT = prove
 (`!(Ff:real->bool) y.
     (if --y IN Ff then &1 else &0) =
     (if y IN IMAGE (\z:real. --z) Ff then &1 else &0)`,
  REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[REAL_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* The two-sided weak type (1,1) bound for an indicator, |{hl_maximal(1_F) > *)
(* tau}| <= 2|F|/tau.  The forward half is CH_EXCEPTIONAL_SET; the backward  *)
(* half follows by reflection (HL_BWD_REFLECT, REFLECT_RMEAS,                *)
(* REFLECT_RMEASURE).                                                        *)
(* ------------------------------------------------------------------------- *)
let IMAGE_NEG_LAMBDA = prove
 (`!s:real->bool. IMAGE (\z:real. --z) s = IMAGE (--) s`,
  GEN_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM]);;

let CH_BWD_INDICATOR_REFLECT = prove
 (`!(Ff:real->bool) x.
     hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x =
     hl_maximal_fwd (\t. if t IN IMAGE (\z:real. --z) Ff then &1 else &0)
                    (--x)`,
  ASM_REWRITE_TAC[HL_BWD_REFLECT; CH_INDICATOR_REFLECT]);;

let CH_FWD_INDICATOR_LEBMEAS = prove
 (`!(Ff:real->bool) tau. real_measurable Ff
     ==> real_lebesgue_measurable
           {x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. if t IN (Ff:real->bool) then &1 else &0`; `&1:real`]
    HL_FWD_MEASURABLE) THEN
  ASM_SIMP_TAC[CH_INDICATOR_REAL_INTEGRABLE] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT; real_gt]);;

let CH_FWD_SUPERLEVEL_MEASURE = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> tau * real_measure
           {x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}
         <= real_measure Ff`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Gt = {x | ?a. x < a /\
              (a - x) * tau < real_integral (real_interval[x,a])
                                (\t. if t IN Ff then &1 else &0)}` THEN
  SUBGOAL_THEN `real_measurable (Gt:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Gt" THEN MATCH_MP_TAC MAXIMAL_SUPERLEVEL_MEASURABLE THEN
    ASM_SIMP_TAC[CH_INDICATOR_REAL_INTEGRABLE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}
                 SUBSET Gt` ASSUME_TAC THENL
   [EXPAND_TAC "Gt" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HL_FWD_SUPERLEVEL_SUB THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measurable
      {x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_MEASURABLE_LEBESGUE_SUBSET;
     CH_FWD_INDICATOR_LEBMEAS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `tau * real_measure (Gt:real->bool)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE; REAL_MEASURE_SUBSET];
    ASM_MESON_TAC[CH_EXCEPTIONAL_SET]]);;

let CH_FWD_SUPERLEVEL_MEAS_SET = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> real_measurable
           {x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_LEBESGUE_SUBSET THEN
  EXISTS_TAC `{x | ?a. x < a /\
      (a - x) * tau < real_integral (real_interval[x,a])
                        (\t. if t IN Ff then &1 else &0)}` THEN
  ASM_SIMP_TAC[CH_FWD_INDICATOR_LEBMEAS] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MAXIMAL_SUPERLEVEL_MEASURABLE THEN
    ASM_SIMP_TAC[CH_INDICATOR_REAL_INTEGRABLE] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; HL_FWD_SUPERLEVEL_SUB]]);;

let CH_BWD_SUPERLEVEL_REFLECT_SET = prove
 (`!(Ff:real->bool) tau.
     {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x} =
     IMAGE (\z:real. --z)
       {y | tau < hl_maximal_fwd
                    (\t. if t IN IMAGE (\z:real. --z) Ff then &1 else &0) y}`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s <=> x IN t) ==> s = t`) THEN
  REWRITE_TAC[CH_BWD_INDICATOR_REFLECT; IN_IMAGE; IN_ELIM_THM] THEN
  ASM_MESON_TAC[REAL_NEG_NEG]);;

let CH_BWD_SUPERLEVEL_MEASURE = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> tau * real_measure
           {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x}
         <= real_measure Ff`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_measurable (IMAGE (\z:real. --z) Ff)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_NEG_LAMBDA; REFLECT_RMEAS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measure
      {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x} =
    real_measure
      {y | tau < hl_maximal_fwd
                   (\t. if t IN IMAGE (\z:real. --z) Ff then &1 else &0) y}`
    SUBST1_TAC THENL
   [REWRITE_TAC[CH_BWD_SUPERLEVEL_REFLECT_SET; IMAGE_NEG_LAMBDA] THEN
     MATCH_MP_TAC REFLECT_RMEASURE THEN
    REWRITE_TAC[GSYM IMAGE_NEG_LAMBDA] THEN
    MATCH_MP_TAC CH_FWD_SUPERLEVEL_MEAS_SET THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure Ff = real_measure (IMAGE (\z:real. --z) Ff)`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[IMAGE_NEG_LAMBDA; REFLECT_RMEASURE]; ALL_TAC] THEN
  MATCH_MP_TAC CH_FWD_SUPERLEVEL_MEASURE THEN ASM_REWRITE_TAC[]);;

(* Arithmetic and inclusion steps for the two-sided bound                    *)
(* CH_HL_MAXIMAL_WEAK11_INDICATOR.                                           *)
let CH_WEAK11_ARITH = prove
 (`!mE mSF mSB mF tau:real.
     &0 < tau /\ mE <= mSF + mSB /\ tau * mSF <= mF /\ tau * mSB <= mF
     ==> mE <= &2 * mF / tau`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mSF <= mF / tau /\ mSB <= mF / tau` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* {tau<hl_maximal(1_F)} SUBSET {tau<fwd(1_F)} UNION {tau<bwd(1_F)}          *)
(* (HL_MAX_LE_MAX).                                                          *)
let CH_HL_SUPERLEVEL_SUBSET = prove
 (`!(Ff:real->bool) tau. real_measurable Ff
     ==> {x | tau < hl_maximal (\t. if t IN Ff then &1 else &0) x} SUBSET
         ({x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x} UNION
          {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN
    MP_TAC(ISPECL [`\t. if t IN (Ff:real->bool) then &1 else &0`; `&1:real`;
    `x:real`] HL_MAX_LE_MAX) THEN
  ASM_SIMP_TAC[CH_HL_INDICATOR_ABS_EQ; CH_INDICATOR_REAL_INTEGRABLE] THEN
  ASM_REAL_ARITH_TAC);;

(* Measurability of the backward superlevel set {tau < bwd(1_F)} = IMAGE     *)
(* (--) {tau < fwd(1_{-F})}, and the two-sided weak type (1,1) bound for an  *)
(* indicator.                                                                *)
let CH_BWD_SUPERLEVEL_MEAS_SET = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> real_measurable
           {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_measurable (IMAGE (\z:real. --z) Ff)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_NEG_LAMBDA; REFLECT_RMEAS]; ALL_TAC] THEN
  REWRITE_TAC[CH_BWD_SUPERLEVEL_REFLECT_SET; IMAGE_NEG_LAMBDA] THEN
  MATCH_MP_TAC REFLECT_RMEAS THEN REWRITE_TAC[GSYM IMAGE_NEG_LAMBDA] THEN
  MATCH_MP_TAC CH_FWD_SUPERLEVEL_MEAS_SET THEN ASM_REWRITE_TAC[]);;

let CH_HL_FWDBWD_UNION_MEAS = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> real_measurable
          ({x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x} UNION
           {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x})`,
  ASM_SIMP_TAC[REAL_MEASURABLE_UNION; CH_FWD_SUPERLEVEL_MEAS_SET;
    CH_BWD_SUPERLEVEL_MEAS_SET]);;

(* {tau<hl_maximal(1_F)} real_measurable: lebesgue-measurable                *)
(* (HL_MAXIMAL_MEASURABLE preimage) + SUBSET the finite union                *)
(* (REAL_MEASURABLE_LEBESGUE_SUBSET).                                        *)
let CH_HL_SUPERLEVEL_MEAS = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> real_measurable
           {x | tau < hl_maximal (\t. if t IN Ff then &1 else &0) x}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_MEASURABLE_LEBESGUE_SUBSET THEN
  EXISTS_TAC
   `{x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x} UNION
    {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x}` THEN
  ASM_SIMP_TAC[CH_HL_FWDBWD_UNION_MEAS; CH_HL_SUPERLEVEL_SUBSET] THEN
  MP_TAC(ISPECL [`\t. if t IN (Ff:real->bool) then &1 else &0`; `&1:real`]
    HL_MAXIMAL_MEASURABLE) THEN
  ASM_SIMP_TAC[CH_HL_INDICATOR_ABS_EQ; CH_INDICATOR_REAL_INTEGRABLE] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT; real_gt]);;

(* THE two-sided HL weak-(1,1) for the indicator: |{hl_maximal(1_F)>tau}| <= *)
(* 2|F|/tau.                                                                 *)
let CH_HL_MAXIMAL_WEAK11_INDICATOR = prove
 (`!(Ff:real->bool) tau. real_measurable Ff /\ &0 < tau
     ==> real_measure {x | tau < hl_maximal (\t. if t IN Ff then &1 else &0) x}
         <= &2 * real_measure Ff / tau`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_measurable
      {x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[CH_FWD_SUPERLEVEL_MEAS_SET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measurable
      {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x}`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[CH_BWD_SUPERLEVEL_MEAS_SET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measurable {x | tau < hl_maximal (\t. if t IN Ff then &1 else &0) x}`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[CH_HL_SUPERLEVEL_MEAS]; ALL_TAC] THEN
  MATCH_MP_TAC CH_WEAK11_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`real_measure
       {x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x}`;
    `real_measure
       {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x}`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `real_measure
        ({x | tau < hl_maximal_fwd (\t. if t IN Ff then &1 else &0) x} UNION
         {x | tau < hl_maximal_bwd (\t. if t IN Ff then &1 else &0) x})` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MEASURE_SUBSET; REAL_MEASURABLE_UNION;
       CH_HL_SUPERLEVEL_SUBSET];
      ASM_SIMP_TAC[REAL_MEASURE_UNION_LE]];
    ASM_SIMP_TAC[CH_FWD_SUPERLEVEL_MEASURE];
    ASM_SIMP_TAC[CH_BWD_SUPERLEVEL_MEASURE]]);;

(* ------------------------------------------------------------------------- *)
(* The tree Bessel inequality: the sum over the tiles of an r-tree of        *)
(* |carleson_ip f s|^2 is at most C times ||f||_2^2.  This is                *)
(* CARLESON_286J_SECOND (the Bessel inequality for the packet inner          *)
(* products) on the tile set {s | s IN P /\ tile_ler s tau}, together with   *)
(* the single-tree operator bound CH_TREE_OPERATOR_L2.                       *)
(* ------------------------------------------------------------------------- *)
let CH_TREE_BESSEL_L2 = prove
 (`?C. &0 <= C /\
    !(f:real->complex) (P:(int#int#int)->bool) tau.
        (\z. f(drop z)) IN lspace (:real^1) (&2) /\ FINITE P
        ==> sum {s | s IN P /\ tile_ler s tau}
                (\s. norm(carleson_ip f s) pow 2)
            <= C * lnorm (:real^1) (&2) (\z. f(drop z)) pow 2`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "op"))
    CH_TREE_OPERATOR_L2 THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`f:real->complex`; `P:(int#int#int)->bool`;
    `tau:int#int#int`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->complex`;
    `{s | s IN P /\ tile_ler s tau}`] CARLESON_286J_SECOND) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm (:real^1) (&2) (\z. f(drop z)) *
              lnorm (:real^1) (&2)
                (\z. vsum {s | s IN P /\ tile_ler s tau}
                          (\s. carleson_ip f s *
                               phi_sigma s carleson_phi (drop z)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z)) *
              (C * lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z)))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL];
    REAL_ARITH_TAC]);;

(* Additivity of the Carleson packet inner product in the function slot:     *)
(* carleson_ip (f + g) s = carleson_ip f s + carleson_ip g s for f, g in L^2 *)
(* (unfold lproduct and use INTEGRAL_ADD with L2_CNJ_PRODUCT_INTEGRABLE).    *)
let CH_IP_ADD = prove
 (`!(f:real->complex) g s.
     (\z. f(drop z)) IN lspace (:real^1) (&2) /\
     (\z. g(drop z)) IN lspace (:real^1) (&2)
     ==> carleson_ip (\x. f x + g x) s = carleson_ip f s + carleson_ip g s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_ip; lproduct] THEN
  SUBGOAL_THEN `(\z. phi_sigma s carleson_phi (drop z))
                IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCHWARTZ_L2; ETA_AX; PHISIG_CARLESON_SCHWARTZ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\z. (f:real->complex)(drop z)`;
                 `\z. phi_sigma s carleson_phi (drop z)`]
                   L2_CNJ_PRODUCT_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^1)`; `\z. (g:real->complex)(drop z)`;
                 `\z. phi_sigma s carleson_phi (drop z)`]
                   L2_CNJ_PRODUCT_INTEGRABLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(\z. ((f:real->complex)(drop z) + g(drop z)) *
         cnj(phi_sigma s carleson_phi (drop z))) =
    (\z. (\z. f(drop z) * cnj(phi_sigma s carleson_phi (drop z))) z +
         (\z. g(drop z) * cnj(phi_sigma s carleson_phi (drop z))) z)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_ADD THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Splitting of the tree energy at a window.  For a window W, 1_Ff = 1_{Ff   *)
(* cap W} + 1_{Ff \ W}, so the tree energy splits into a near part (Ff cap   *)
(* W) and a far part (Ff \ W); the far part is controlled by the decay of    *)
(* the packets.                                                              *)
(* ------------------------------------------------------------------------- *)

(* (a+b)^2 <= 2a^2 + 2b^2, since 2a^2 + 2b^2 - (a+b)^2 = (a-b)^2 >= 0.       *)
let CH_SUMSQ_ARITH = prove
 (`!a b:real. (a + b) pow 2 <= &2 * a pow 2 + &2 * b pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `a - b:real` REAL_LE_POW_2) THEN
  MATCH_MP_TAC(REAL_ARITH `d = c - e ==> &0 <= d ==> e <= c`) THEN
  CONV_TAC REAL_RING);;

(* The indicator of Ff splits as (1_{Ff cap W}) + (1_{Ff \ W}).              *)
let CH_INDICATOR_INTER_DIFF = prove
 (`!(Ff:real->bool) (W:real->bool).
     (\x. if x IN Ff then Cx(&1) else Cx(&0)) =
     (\x. (if x IN (Ff INTER W) then Cx(&1) else Cx(&0)) +
          (if x IN (Ff DIFF W) then Cx(&1) else Cx(&0)))`,
  REWRITE_TAC[FUN_EQ_THM; IN_INTER; IN_DIFF] THEN
  CONV_TAC COMPLEX_RING);;

(* Per-tile packet split at the window (via CH_IP_ADD + CH_CHI_LSPACE2).     *)
let CH_IP_INTER_DIFF = prove
 (`!(Ff:real->bool) (W:real->bool) s.
     real_measurable Ff /\ real_measurable W
     ==> carleson_ip (\x. if x IN Ff then Cx(&1) else Cx(&0)) s =
         carleson_ip (\x. if x IN (Ff INTER W) then Cx(&1) else Cx(&0)) s +
         carleson_ip (\x. if x IN (Ff DIFF W) then Cx(&1) else Cx(&0)) s`,
  ASM_SIMP_TAC[CH_INDICATOR_INTER_DIFF; CH_IP_ADD; CH_CHI_LSPACE2;
    REAL_MEASURABLE_INTER; REAL_MEASURABLE_DIFF]);;

(* The tree-energy sum split: sum |ip(1_Ff)|^2 <= 2 sum |ip(1_{Ff cap W})|^2 *)
(* + 2 sum |ip(1_{Ff \ W})|^2, from CH_IP_INTER_DIFF + CH_SUMSQ_ARITH.       *)
let CH_TREE_SUM_SPLIT = prove
 (`!(Ff:real->bool) (W:real->bool) (P:(int#int#int)->bool) t.
     real_measurable Ff /\ real_measurable W /\ FINITE P
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip (\x. if x IN Ff then Cx(&1)
                                        else Cx(&0)) s) pow 2)
         <= &2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip (\x. if x IN (Ff INTER W) then Cx(&1)
                                        else Cx(&0)) s) pow 2)
          + &2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip (\x. if x IN (Ff DIFF W) then Cx(&1)
                                        else Cx(&0)) s) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {s:int#int#int | s IN P /\ tile_ler s t}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(fun (asl,w) ->
    MP_TAC(ISPECL
     [`\s:int#int#int.
         &2 * norm(carleson_ip (\x. if x IN Ff INTER W then Cx(&1)
                                    else Cx(&0)) s) pow 2`;
      `\s:int#int#int.
         &2 * norm(carleson_ip (\x. if x IN Ff DIFF W then Cx(&1)
                                    else Cx(&0)) s) pow 2`;
      `{s:int#int#int | s IN P /\ tile_ler s t}`] SUM_ADD)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:int#int#int` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CH_IP_INTER_DIFF] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `(norm(carleson_ip (\x. if x IN (Ff INTER W) then Cx(&1) else Cx(&0)) s) +
     norm(carleson_ip (\x. if x IN (Ff DIFF W) then Cx(&1)
                           else Cx(&0)) s)) pow 2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE2; NORM_POS_LE; NORM_TRIANGLE];
    REWRITE_TAC[CH_SUMSQ_ARITH]]);;

(* ------------------------------------------------------------------------- *)
(* Mean-zero pairings.  A mean-zero function b paired against w gains an     *)
(* oscillation factor: <b,w> = <b,w-wc> for every constant wc, so the        *)
(* pairing is bounded by int |b| times the oscillation of w.  This is the    *)
(* mechanism behind the estimate for the bad part in the proof of Lemma 1 of *)
(* Grafakos-Tao-Terwilleger, equation (14):                                  *)
(*   <b_k,phi_s> = <b_k, phi_s - phi_s(c_k)>.                                *)
(* ------------------------------------------------------------------------- *)

(* Mean-zero subtraction: int_J b*cnj(w) = int_J b*cnj(w - wc) when int_J b  *)
(* = 0.                                                                      *)
let CH_MEANZERO_REWRITE = prove
 (`!(b:real^1->complex) (w:real^1->complex) wc J.
     b integrable_on J /\ integral J b = Cx(&0) /\
     (\y. b y * cnj(w y)) integrable_on J
     ==> integral J (\y. b y * cnj(w y)) =
         integral J (\y. b y * cnj(w y - wc))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. (b:real^1->complex) y * cnj(w y - wc)) =
                (\y. b y * cnj(w y) - cnj wc * b y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; CNJ_SUB] THEN
     CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `integral J (\y. (b:real^1->complex) y * cnj(w y) - cnj wc * b y) =
    integral J (\y. b y * cnj(w y)) - integral J (\y. cnj wc * b y)`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_SUB; INTEGRABLE_COMPLEX_LMUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_COMPLEX_LMUL; COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO]);;

(* Mean-zero pairing bound: |int_J b*cnj(w)| <= int_J norm(b)*M when int_J b *)
(* = 0 and norm(w y - wc) <= M y on J (M the pointwise oscillation           *)
(* majorant).                                                                *)
let CH_MEANZERO_PAIR = prove
 (`!(b:real^1->complex) (w:real^1->complex) wc (M:real^1->real^1) J.
     b integrable_on J /\ integral J b = Cx(&0) /\
     (\y. b y * cnj(w y)) integrable_on J /\
     (\y. b y * cnj(w y - wc)) integrable_on J /\
     (\y. lift(norm(b y) * drop(M y))) integrable_on J /\
     (!y. y IN J ==> norm(w y - wc) <= drop(M y))
     ==> norm(integral J (\y. b y * cnj(w y)))
         <= drop(integral J (\y. lift(norm(b y) * drop(M y))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`b:real^1->complex`; `w:real^1->complex`;
    `wc:complex`; `J:real^1->bool`]
    CH_MEANZERO_REWRITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
  REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_SIMP_TAC[]);;

(* cw varies slowly at unit scale: |u-u'| <= 1 ==> cw u' <= 8 cw u.  This    *)
(* moves the cw factor of a packet difference from the point y to the centre *)
(* c of the cube, as needed for sums over the tiles of one scale (sum cw^2 = *)
(* O(1)).                                                                    *)
let CW_SHIFT = prove
 (`!u u'. abs(u - u') <= &1 ==> cw u' <= &8 * cw u`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cw; real_div; REAL_MUL_LID] THEN
  SUBGOAL_THEN `(&1 + abs u) pow 3 <= &8 * (&1 + abs u') pow 3`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `(&1 + abs u) pow 3 <= (&2 * (&1 + abs u')) pow 3`
     MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 + abs u') pow 3 /\ &0 < (&1 + abs u) pow 3`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv((&1 + abs u) pow 3 / &8)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INV_DIV; real_div; REAL_LE_REFL]]);;

(* Monotonicity of products, for CH_PSI_DIFF_CW: if Cd, S, P, cwy and cwc    *)
(* are nonnegative, P <= Q and cwy <= 8 cwc, then                            *)
(*   Cd * S * P * cwy <= (8 Cd) * S * Q * cwc.                               *)
let CWTAIL2 = prove
 (`!Cd S P Q cwy cwc.
     &0 <= Cd /\ &0 <= S /\ &0 <= P /\ P <= Q /\ &0 <= cwy /\
     &0 <= cwc /\ cwy <= &8 * cwc
   ==> Cd * S * P * cwy <= (&8 * Cd) * S * Q * cwc`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&8 * Cd) * S * Q * cwc = Cd * S * (Q * (&8 * cwc))`
    SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]);;

(* The packet difference with the cw localization kept at the centre c of    *)
(* the cube, so that the sum over the tiles of one scale can be taken (sum   *)
(* cw^2 = O(1)); the cw factor is moved to c by CW_SHIFT, and the bound      *)
(* assembled by CWTAIL2.                                                     *)
let CH_PSI_DIFF_CW = prove
 (`?Cdiff. &0 <= Cdiff /\
   !(s:int#int#int) t c w y.
      tile_ler s t /\ &2 zpow tile_k s * w <= &1 /\ abs(y - c) <= w /\ &0 <= w
      ==> norm( (cexp(--(ii * Cx(tile_ymid t) * Cx y)) *
                 phi_sigma s carleson_phi y) -
                (cexp(--(ii * Cx(tile_ymid t) * Cx c)) *
                 phi_sigma s carleson_phi c) )
          <= Cdiff * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * w) *
             cw(&2 zpow tile_k s * (c - tile_xmid s))`,
  X_CHOOSE_THEN `Cd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "d"))
    PHISIG_DEMOD_DIFF_TILE THEN
  EXISTS_TAC `&8 * Cd` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`s:int#int#int`;`t:int#int#int`;`c:real`;`w:real`;`y:real`] THEN
    STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow tile_k s` (LABEL_TAC "pos") THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow tile_k s * abs(y - c) <= &1` (LABEL_TAC "small") THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; REAL_LE_LMUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm( (cexp(--(ii * Cx(tile_ymid t) * Cx y)) *
           phi_sigma s carleson_phi y) -
          (cexp(--(ii * Cx(tile_ymid t) * Cx c)) *
           phi_sigma s carleson_phi c) )
    <= Cd * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * abs(y - c)) *
       cw(&2 zpow tile_k s * (y - tile_xmid s))` (LABEL_TAC "pd") THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `cw(&2 zpow tile_k s * (y - tile_xmid s)) <=
                &8 * cw(&2 zpow tile_k s * (c - tile_xmid s))`
    (LABEL_TAC "cwsh") THENL
   [MATCH_MP_TAC CW_SHIFT THEN
    SUBGOAL_THEN `&2 zpow tile_k s * (c - tile_xmid s) -
                  &2 zpow tile_k s * (y - tile_xmid s) =
                  &2 zpow tile_k s * (c - y)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(&2 zpow tile_k s) = &2 zpow tile_k s` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cd * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * abs(y - c)) *
              cw(&2 zpow tile_k s * (y - tile_xmid s))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CWTAIL2 THEN
  REPEAT CONJ_TAC THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN REWRITE_TAC[CW_POS] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC SQRT_POS_LE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN NO_TAC) THEN
  TRY(MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN NO_TAC) THEN
  (MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC));;

(* The real and imaginary parts of the modulation em(x) = cexp(--(ii y_t x)) *)
(* by the frequency y_t of the tree top:                                     *)
(*   Re(em x) = cos(y_t x),   Im(em x) = -sin(y_t x).                        *)
(* The Calderon-Zygmund decomposition in CH_TREE_NEAR_CZ is applied          *)
(* separately to the real and imaginary parts of em * 1_{F cap W}.           *)
let EM_RE = prove
 (`!yt x. Re(cexp(--(ii * Cx yt * Cx x))) = cos(yt * x)`,
  REWRITE_TAC[RE_CEXP; RE_NEG; IM_NEG; RE_MUL_II; IM_MUL_II; GSYM CX_MUL;
    RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID; COS_NEG]);;

let EM_IM = prove
 (`!yt x. Im(cexp(--(ii * Cx yt * Cx x))) = --sin(yt * x)`,
  REWRITE_TAC[IM_CEXP; RE_NEG; IM_NEG; RE_MUL_II; IM_MUL_II; GSYM CX_MUL;
    RE_CX; IM_CX; REAL_NEG_0; REAL_EXP_0; REAL_MUL_LID; SIN_NEG]);;

(* Continuity and measurability of the modulations cos(yt.) and sin(yt.),   *)
(* the real and imaginary parts of em (up to sign).                          *)
let CH_COS_LIN_CONT = prove
 (`!yt. (\x. cos(yt * x)) real_continuous_on (:real)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\x. cos(yt * x)) = cos o (\x. yt * x)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID];
    REWRITE_TAC[REAL_CONTINUOUS_ON_COS]]);;

let CH_SIN_LIN_CONT = prove
 (`!yt. (\x. sin(yt * x)) real_continuous_on (:real)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(\x. sin(yt * x)) = sin o (\x. yt * x)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_ON_LMUL; REAL_CONTINUOUS_ON_ID];
    REWRITE_TAC[REAL_CONTINUOUS_ON_SIN]]);;

let CH_COS_LIN_MEAS = prove
 (`!yt. (\x. cos(yt * x)) real_measurable_on (:real)`,
  ASM_SIMP_TAC[CONTINUOUS_IMP_REAL_MEASURABLE_ON; CH_COS_LIN_CONT]);;

let CH_SIN_LIN_MEAS = prove
 (`!yt. (\x. sin(yt * x)) real_measurable_on (:real)`,
  ASM_SIMP_TAC[CONTINUOUS_IMP_REAL_MEASURABLE_ON; CH_SIN_LIN_CONT]);;

(* ------------------------------------------------------------------------- *)
(* The density of the window, covariance under modulation, and the L^2 bound *)
(* for the good part.                                                        *)
(* ------------------------------------------------------------------------- *)

(* em(z)*cnj(em(z)) = 1 (unimodularity of the modulation em=cexp(-i yt z)).  *)
let CH_EM_UNIMOD = prove
 (`!yt z.
     cexp(--(ii * Cx yt * Cx z)) * cnj(cexp(--(ii * Cx yt * Cx z))) = Cx(&1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CNJ_CEXP; CNJ_NEG; CNJ_MUL; CNJ_II; CNJ_CX; GSYM CEXP_ADD] THEN
  SUBGOAL_THEN
   `--(ii * Cx yt * Cx z) + --(--ii * Cx yt * Cx z) = Cx(&0)`
   SUBST1_TAC THENL
   [CONV_TAC COMPLEX_RING; REWRITE_TAC[CEXP_0]]);;

(* Cx o (real-L2 fn) is in complex lspace 2.                                 *)
let CH_CXREAL_LSPACE2 = prove
 (`!g:real->real.
     g real_measurable_on (:real) /\ (\x. g x pow 2) real_integrable_on (:real)
     ==> (\z. Cx(g(drop z))) IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lspace; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_CX THEN
    UNDISCH_TAC `g real_measurable_on (:real)` THEN
    REWRITE_TAC[real_measurable_on; IMAGE_LIFT_UNIV; o_DEF];
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    SUBGOAL_THEN `(\z. lift(abs(g(drop z)) rpow &2)) =
                  (\z:real^1. lift(g(drop z) pow 2))` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[RPOW_POW; REAL_POW2_ABS]; ALL_TAC] THEN
    UNDISCH_TAC `(\x. g x pow 2) real_integrable_on (:real)` THEN
    REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV; o_DEF]]);;

(* Modulation by cexp(ii y .) preserves lspace 2 (unimodular multiplier).    *)
let CH_MODULATE_LSPACE2 = prove
 (`!h:real->complex y.
     (\z. h(drop z)) IN lspace (:real^1) (&2)
     ==> (\z. cexp(ii * Cx y * Cx(drop z)) * h(drop z))
       IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[lspace; IN_ELIM_THM]) THEN
  REWRITE_TAC[lspace; IN_ELIM_THM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
      SUBGOAL_THEN `(\z. cexp(ii * Cx y * Cx(drop z))) =
                    cexp o (\z:real^1. ii * Cx y * Cx(drop z))`
        SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
        REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN
      REWRITE_TAC[CONTINUOUS_ON_ID];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `!z:real^1. norm(cexp(ii * Cx y * Cx(drop z))) = &1`
      (fun th -> REWRITE_TAC[COMPLEX_NORM_MUL; th; REAL_MUL_LID]) THENL
     [REWRITE_TAC[GSYM CX_MUL; NORM_CEXP_II]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

(* cnj(em) = cexp(+ii yt .) (conjugate of the modulation).                   *)
let CH_CNJ_EM = prove
 (`!yt x. cnj(cexp(--(ii * Cx yt * Cx x))) = cexp(ii * Cx yt * Cx x)`,
  REPEAT GEN_TAC THEN
    REWRITE_TAC[CNJ_CEXP; CNJ_NEG; CNJ_MUL; CNJ_II; CNJ_CX] THEN
  AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

(* Pointwise em-indicator split: em*1_FW = Cx(cos(yt.)1_FW) + ii             *)
(* Cx(-sin(yt.)1_FW).                                                        *)
let CH_EM_IND_SPLIT = prove
 (`!yt (FW:real->bool) x.
     cexp(--(ii * Cx yt * Cx x)) * (if x IN FW then Cx(&1) else Cx(&0)) =
     Cx(cos(yt * x) * (if x IN FW then &1 else &0)) +
     ii * Cx(--sin(yt * x) * (if x IN FW then &1 else &0))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [COMPLEX_EXPAND] THEN
  REWRITE_TAC[EM_RE; EM_IM] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC[CX_MUL; COMPLEX_ADD_RDISTRIB; COMPLEX_MUL_ASSOC]);;

(* Indicator reconstruction: given the two real CZ splits                    *)
(* cos(yt.)1_FW=gR+bR, -sin(yt.)1_FW=gI+bI, the indicator splits into        *)
(* re-modulated good+bad complex packets: 1_FW = cexp(ii yt.)(Cx gR+ii Cx    *)
(* gI) + cexp(ii yt.)(Cx bR+ii Cx bI).                                       *)
let CH_IND_RECON = prove
 (`!yt (FW:real->bool) gR bR gI bI x.
     cos(yt * x) * (if x IN FW then &1 else &0) = gR x + bR x /\
     --sin(yt * x) * (if x IN FW then &1 else &0) = gI x + bI x
     ==> (if x IN FW then Cx(&1) else Cx(&0)) =
         cexp(ii * Cx yt * Cx x) * (Cx(gR x) + ii * Cx(gI x)) +
         cexp(ii * Cx yt * Cx x) * (Cx(bR x) + ii * Cx(bI x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`yt:real`; `FW:real->bool`; `x:real`] CH_EM_IND_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`yt:real`; `x:real`] CH_EM_UNIMOD) THEN
  REWRITE_TAC[CH_CNJ_EM; CX_ADD] THEN
  CONV_TAC COMPLEX_RING);;

(* Complex good part Cx gR + ii Cx gI in lspace 2 (both real parts L^2).     *)
let CH_CXCPLX_LSPACE2 = prove
 (`!(gR:real->real) (gI:real->real).
     gR real_measurable_on (:real) /\
     (\x. gR x pow 2) real_integrable_on (:real) /\
     gI real_measurable_on (:real) /\
     (\x. gI x pow 2) real_integrable_on (:real)
     ==> (\z. Cx(gR(drop z)) + ii * Cx(gI(drop z))) IN lspace (:real^1) (&2)`,
  ASM_SIMP_TAC[LSPACE_ADD; REAL_POS; CH_CXREAL_LSPACE2; LSPACE_COMPLEX_LMUL]);;

(* Re-modulated complex good packet cexp(ii yt.)(Cx gR + ii Cx gI) in lspace *)
(* 2.                                                                        *)
let CH_GOODPKT_LSPACE2 = prove
 (`!yt (gR:real->real) (gI:real->real).
     gR real_measurable_on (:real) /\
     (\x. gR x pow 2) real_integrable_on (:real) /\
     gI real_measurable_on (:real) /\
     (\x. gI x pow 2) real_integrable_on (:real)
     ==> (\z. cexp(ii * Cx yt * Cx(drop z)) *
              (Cx(gR(drop z)) + ii * Cx(gI(drop z))))
         IN lspace (:real^1) (&2)`,
  ASM_SIMP_TAC[CH_MODULATE_LSPACE2; CH_CXCPLX_LSPACE2]);;

(* Bad packet cexp(ii yt.)(Cx bR + ii Cx bI) in lspace 2: = 1_FW - good_pkt, *)
(* both L^2 (1_FW bounded on the bounded window; good_pkt via                *)
(* CH_GOODPKT_LSPACE2).                                                      *)
let CH_BADPKT_LSPACE2 = prove
 (`!yt (FW:real->bool) gR bR gI bI.
     real_measurable FW /\
     gR real_measurable_on (:real) /\
     (\x. gR x pow 2) real_integrable_on (:real) /\
     gI real_measurable_on (:real) /\
     (\x. gI x pow 2) real_integrable_on (:real) /\
     (!x. cos(yt * x) * (if x IN FW then &1 else &0) = gR x + bR x) /\
     (!x. --sin(yt * x) * (if x IN FW then &1 else &0) = gI x + bI x)
     ==> (\z. cexp(ii * Cx yt * Cx(drop z)) *
              (Cx(bR(drop z)) + ii * Cx(bI(drop z))))
         IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. cexp(ii * Cx yt * Cx(drop z)) *
         (Cx(bR(drop z)) + ii * Cx(bI(drop z)))) =
    (\z. (\w. if drop w IN FW then Cx(&1) else Cx(&0)) z -
         (\w. cexp(ii * Cx yt * Cx(drop w)) *
              (Cx(gR(drop w)) + ii * Cx(gI(drop w)))) z)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN
     MP_TAC(ISPECL [`yt:real`; `FW:real->bool`; `gR:real->real`;
                    `bR:real->real`; `gI:real->real`; `bI:real->real`;
                    `drop z`] CH_IND_RECON) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  MATCH_MP_TAC LSPACE_SUB THEN REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_CHI_LSPACE2];
    ASM_SIMP_TAC[CH_GOODPKT_LSPACE2]]);;

(* THE em-covariance split: carleson_ip(1_FW,s) = good_pkt_ip(s) +           *)
(* bad_pkt_ip(s), good_pkt = cexp(ii yt.)(Cx gR + ii Cx gI), bad_pkt =       *)
(* cexp(ii yt.)(Cx bR+ii Cx bI).                                             *)
let CH_IP_GOODBAD = prove
 (`!yt (FW:real->bool) gR bR gI bI s.
     real_measurable FW /\
     gR real_measurable_on (:real) /\
     (\x. gR x pow 2) real_integrable_on (:real) /\
     gI real_measurable_on (:real) /\
     (\x. gI x pow 2) real_integrable_on (:real) /\
     (!x. cos(yt * x) * (if x IN FW then &1 else &0) = gR x + bR x) /\
     (!x. --sin(yt * x) * (if x IN FW then &1 else &0) = gI x + bI x)
     ==> carleson_ip (\x. if x IN FW then Cx(&1) else Cx(&0)) s =
         carleson_ip (\x. cexp(ii * Cx yt * Cx x) *
                          (Cx(gR x) + ii * Cx(gI x))) s +
         carleson_ip (\x. cexp(ii * Cx yt * Cx x) *
                          (Cx(bR x) + ii * Cx(bI x))) s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `carleson_ip (\x. if x IN FW then Cx(&1) else Cx(&0)) s =
    carleson_ip (\x. cexp(ii * Cx yt * Cx x) * (Cx(gR x) + ii * Cx(gI x)) +
                     cexp(ii * Cx yt * Cx x) * (Cx(bR x) + ii * Cx(bI x))) s`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[CH_IND_RECON]; ALL_TAC] THEN
  MATCH_MP_TAC CH_IP_ADD THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_GOODPKT_LSPACE2];
    MP_TAC(ISPECL [`yt:real`; `FW:real->bool`; `gR:real->real`;
                   `bR:real->real`; `gI:real->real`; `bI:real->real`]
                  CH_BADPKT_LSPACE2) THEN
    ASM_REWRITE_TAC[]]);;

(* norm(Cx a + ii Cx b)^2 = a^2 + b^2.                                       *)
let CH_CXCPLX_NORMSQ = prove
 (`!a b:real. norm(Cx a + ii * Cx b) pow 2 = a pow 2 + b pow 2`,
  REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; RE_CX; IM_CX;
   RE_MUL_II; IM_MUL_II] THEN REAL_ARITH_TAC);;

(* drop(integral (lift(gR^2+gI^2))) = real_integral gR^2 + real_integral     *)
(* gI^2.                                                                     *)
let CH_INT_ADD_SPLIT = prove
 (`!gR gI:real->real.
     (\x. gR x pow 2) real_integrable_on (:real) /\
     (\x. gI x pow 2) real_integrable_on (:real)
     ==> drop(integral (:real^1)
                (\x:real^1. lift(gR(drop x) pow 2 + gI(drop x) pow 2))) =
         real_integral (:real) (\x. gR x pow 2) +
         real_integral (:real) (\x. gI x pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_integral (:real) (\x. gR x pow 2) +
    real_integral (:real) (\x. gI x pow 2) =
    real_integral (:real) (\x. gR x pow 2 + gI x pow 2)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_ADD]; ALL_TAC] THEN
  MP_TAC(MATCH_MP REAL_INTEGRAL (REWRITE_RULE[]
    (MATCH_MP REAL_INTEGRABLE_ADD
      (CONJ (ASSUME `(\x. gR x pow 2) real_integrable_on (:real)`)
            (ASSUME `(\x. gI x pow 2) real_integrable_on (:real)`))))) THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV; o_DEF] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* Full complex good-packet tree-energy: sum_{s<=t}|ip(good_pkt,s)|^2 <=     *)
(* C (int gR^2 + int gI^2).  = CH_TREE_BESSEL_L2 on good_pkt (in L^2 by      *)
(* CH_GOODPKT_LSPACE2) + LNORM2_SQ + norm(em)=1 + norm(Cx gR+ii Cx           *)
(* gI)^2=gR^2+gI^2.                                                          *)
let CH_GOODPKT_ENERGY = prove
 (`?C. &0 <= C /\
    !yt (gR:real->real) (gI:real->real) (P:(int#int#int)->bool) t.
        gR real_measurable_on (:real) /\
        (\x. gR x pow 2) real_integrable_on (:real) /\
        gI real_measurable_on (:real) /\
        (\x. gI x pow 2) real_integrable_on (:real) /\ FINITE P
        ==> sum {s | s IN P /\ tile_ler s t}
                (\s. norm(carleson_ip
                       (\x. cexp(ii * Cx yt * Cx x) *
                            (Cx(gR x) + ii * Cx(gI x))) s) pow 2)
            <= C * (real_integral (:real) (\x. gR x pow 2) +
                    real_integral (:real) (\x. gI x pow 2))`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b"))
    CH_TREE_BESSEL_L2 THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`yt:real`; `gR:real->real`; `gI:real->real`;
                       `P:(int#int#int)->bool`; `t:int#int#int`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. cexp(ii * Cx yt * Cx(drop z)) *
         (Cx(gR(drop z)) + ii * Cx(gI(drop z))))
      IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CH_GOODPKT_LSPACE2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * lnorm (:real^1) (&2)
                (\z. cexp(ii * Cx yt * Cx(drop z)) *
                     (Cx(gR(drop z)) + ii * Cx(gI(drop z)))) pow 2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[LNORM2_SQ] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  SUBGOAL_THEN
   `(\x. lift(norm(cexp(ii * Cx yt * Cx(drop x)) *
                   (Cx(gR(drop x)) + ii * Cx(gI(drop x)))) pow 2)) =
    (\x:real^1. lift(gR(drop x) pow 2 + gI(drop x) pow 2))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    SUBGOAL_THEN `norm(cexp(ii * Cx yt * Cx(drop x))) = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM CX_MUL; NORM_CEXP_II]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_LID; CH_CXCPLX_NORMSQ]; ALL_TAC] THEN
  MATCH_MP_TAC CH_INT_ADD_SPLIT THEN ASM_REWRITE_TAC[]);;

(* Complex 2-term norm-square triangle: norm(a+b)^2 <= 2 norm(a)^2 + 2       *)
(* norm(b)^2.                                                                *)
let CH_NORMSQ_ADD_2 = prove
 (`!a b:complex. norm(a + b) pow 2 <= &2 * norm(a) pow 2 + &2 * norm(b) pow 2`,
  ASM_MESON_TAC[REAL_LE_TRANS; REAL_POW_LE2; NORM_POS_LE;
    NORM_TRIANGLE; CH_SUMSQ_ARITH]);;

(* The splitting of the tree energy into good and bad parts (CH_IP_GOODBAD,  *)
(* CH_NORMSQ_ADD_2): sum |ip(1_FW)|^2 <= 2 sum |ip(good_pkt)|^2 + 2 sum      *)
(* |ip(bad_pkt)|^2.                                                          *)
let CH_TREE_GOODBAD_SPLIT = prove
 (`!yt (FW:real->bool) gR bR gI bI (P:(int#int#int)->bool) t.
     real_measurable FW /\ FINITE P /\
     gR real_measurable_on (:real) /\
     (\x. gR x pow 2) real_integrable_on (:real) /\
     gI real_measurable_on (:real) /\
     (\x. gI x pow 2) real_integrable_on (:real) /\
     (!x. cos(yt * x) * (if x IN FW then &1 else &0) = gR x + bR x) /\
     (!x. --sin(yt * x) * (if x IN FW then &1 else &0) = gI x + bI x)
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip (\x. if x IN FW then Cx(&1)
                                        else Cx(&0)) s) pow 2)
         <= &2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. cexp(ii * Cx yt * Cx x) *
                         (Cx(gR x) + ii * Cx(gI x))) s) pow 2)
          + &2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. cexp(ii * Cx yt * Cx x) *
                         (Cx(bR x) + ii * Cx(bI x))) s) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {s:int#int#int | s IN P /\ tile_ler s t}`
    ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  W(fun (asl,w) ->
    MP_TAC(ISPECL
     [`\s:int#int#int. &2 * norm(carleson_ip
         (\x. cexp(ii * Cx yt * Cx x) * (Cx(gR x) + ii * Cx(gI x))) s) pow 2`;
      `\s:int#int#int. &2 * norm(carleson_ip
         (\x. cexp(ii * Cx yt * Cx x) * (Cx(bR x) + ii * Cx(bI x))) s) pow 2`;
      `{s:int#int#int | s IN P /\ tile_ler s t}`] SUM_ADD)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:int#int#int` THEN
    MP_TAC(ISPECL [`yt:real`; `FW:real->bool`; `gR:real->real`;
                   `bR:real->real`; `gI:real->real`; `bI:real->real`;
                   `s:int#int#int`] CH_IP_GOODBAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CH_NORMSQ_ADD_2]);;

(* Arithmetic: C(a+b) <= 8C tau^2 R from a,b <= 2 tau mFW, mFW <= 2 R tau.   *)
let CH_GOOD2_ARITH = prove
 (`!C a b mFW R tau. &0 <= C /\ &0 <= tau /\ &0 < R /\ &0 <= mFW /\
     a <= &2 * tau * mFW /\ b <= &2 * tau * mFW /\ mFW <= &2 * R * tau
     ==> C * (a + b) <= (&8 * C) * tau pow 2 * R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * tau * mFW <= &2 * tau * (&2 * R * tau)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * (&2 * tau * (&2 * R * tau) + &2 * tau * (&2 * R * tau))` THEN
    CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_LMUL; REAL_LE_ADD2; REAL_LE_TRANS];
    REAL_ARITH_TAC]);;

(* Complex good-packet energy in tau^2 R form: given the CZ bounds int gR^2, *)
(* int gI^2 <= 2 tau mFW and mFW <= 2 R tau, sum|ip(good_pkt)|^2 <= C tau^2  *)
(* R.                                                                        *)
let CH_GOOD_ENERGY_TAU2R = prove
 (`?C. &0 <= C /\
    !yt (gR:real->real) (gI:real->real) (P:(int#int#int)->bool) t mFW R tau.
        gR real_measurable_on (:real) /\
        (\x. gR x pow 2) real_integrable_on (:real) /\
        gI real_measurable_on (:real) /\
        (\x. gI x pow 2) real_integrable_on (:real) /\ FINITE P /\
        &0 <= tau /\ &0 < R /\ &0 <= mFW /\
        real_integral (:real) (\x. gR x pow 2) <= &2 * tau * mFW /\
        real_integral (:real) (\x. gI x pow 2) <= &2 * tau * mFW /\
        mFW <= &2 * R * tau
        ==> sum {s | s IN P /\ tile_ler s t}
                (\s. norm(carleson_ip
                       (\x. cexp(ii * Cx yt * Cx x) *
                            (Cx(gR x) + ii * Cx(gI x))) s) pow 2)
            <= C * tau pow 2 * R`,
  X_CHOOSE_THEN `Cp:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pe"))
    CH_GOODPKT_ENERGY THEN
  EXISTS_TAC `&8 * Cp` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`yt:real`; `gR:real->real`; `gI:real->real`;
     `P:(int#int#int)->bool`; `t:int#int#int`;
     `mFW:real`; `R:real`; `tau:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `Cp * (real_integral (:real) (\x. gR x pow 2) +
                    real_integral (:real) (\x. gI x pow 2))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CH_GOOD2_ARITH THEN MAP_EVERY EXISTS_TAC [`mFW:real`] THEN
  ASM_REWRITE_TAC[]);;

(* The good part in the proof of CH_TREE_NEAR_CZ.  Suppose that the          *)
(* Calderon-Zygmund splittings                                               *)
(*   cos(yt.) 1_FW = gR + bR,   -sin(yt.) 1_FW = gI + bI                     *)
(* satisfy                                                                   *)
(*   int gR^2 <= 2 tau mFW,   int gI^2 <= 2 tau mFW,   mFW <= 2 R tau,       *)
(* and that B bounds the tree energy of the bad packet                       *)
(*   cexp(ii yt.) (Cx bR + ii Cx bI).                                        *)
(* Then the tree energy of 1_FW is at most C tau^2 R + 2 B                   *)
(* (CH_TREE_GOODBAD_SPLIT and CH_GOOD_ENERGY_TAU2R).  This reduces           *)
(* CH_TREE_NEAR_CZ to a bound for the bad part of the form B <= C0 tau^2 R.  *)
let CH_TREE_NEAR_MODULO_BAD = prove
 (`?C. &0 <= C /\
    !yt (FW:real->bool) gR bR gI bI (P:(int#int#int)->bool) t mFW R tau B.
        real_measurable FW /\ FINITE P /\
        gR real_measurable_on (:real) /\
        (\x. gR x pow 2) real_integrable_on (:real) /\
        gI real_measurable_on (:real) /\
        (\x. gI x pow 2) real_integrable_on (:real) /\
        (!x. cos(yt * x) * (if x IN FW then &1 else &0) = gR x + bR x) /\
        (!x. --sin(yt * x) * (if x IN FW then &1 else &0) = gI x + bI x) /\
        &0 <= tau /\ &0 < R /\ &0 <= mFW /\
        real_integral (:real) (\x. gR x pow 2) <= &2 * tau * mFW /\
        real_integral (:real) (\x. gI x pow 2) <= &2 * tau * mFW /\
        mFW <= &2 * R * tau /\
        sum {s | s IN P /\ tile_ler s t}
            (\s. norm(carleson_ip
                   (\x. cexp(ii * Cx yt * Cx x) *
                        (Cx(bR x) + ii * Cx(bI x))) s) pow 2) <= B
        ==> sum {s | s IN P /\ tile_ler s t}
                (\s. norm(carleson_ip (\x. if x IN FW then Cx(&1)
                                           else Cx(&0)) s) pow 2)
            <= C * tau pow 2 * R + &2 * B`,
  X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ge"))
    CH_GOOD_ENERGY_TAU2R THEN
  EXISTS_TAC `&2 * Cg` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`yt:real`; `FW:real->bool`; `gR:real->real`; `bR:real->real`;
     `gI:real->real`; `bI:real->real`; `P:(int#int#int)->bool`;
     `t:int#int#int`; `mFW:real`; `R:real`; `tau:real`; `B:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. cexp(ii * Cx yt * Cx x) *
                         (Cx(gR x) + ii * Cx(gI x))) s) pow 2)
    + &2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. cexp(ii * Cx yt * Cx x) *
                         (Cx(bR x) + ii * Cx(bI x))) s) pow 2)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_TREE_GOODBAD_SPLIT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (Cg * tau pow 2 * R)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "ge" (fun th -> MATCH_MP_TAC (SPECL
        [`yt:real`; `gR:real->real`; `gI:real->real`;
         `P:(int#int#int)->bool`; `t:int#int#int`;
         `mFW:real`; `R:real`; `tau:real`] th)) THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The bad part of the Calderon-Zygmund decomposition: demodulation and      *)
(* per-cube pairing bounds.                                                  *)
(* ------------------------------------------------------------------------- *)

(* Demodulation: carleson_ip(bad_pkt,s) = int B cnj(psi_s), where            *)
(* bad_pkt = cexp(ii yt.)*B, B = Cx bR + ii Cx bI, and                       *)
(* psi_s = cexp(-(ii yt.)) phi_sigma s carleson_phi (the demodulated         *)
(* packet).                                                                  *)
let CH_BADIP_DEMOD = prove
 (`!yt (bR:real->real) (bI:real->real) s.
     carleson_ip (\x. cexp(ii * Cx yt * Cx x) * (Cx(bR x) + ii * Cx(bI x))) s =
     integral (:real^1)
       (\z. (Cx(bR(drop z)) + ii * Cx(bI(drop z))) *
            cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                phi_sigma s carleson_phi (drop z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carleson_ip; lproduct] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN
  REWRITE_TAC[CNJ_MUL] THEN
  MP_TAC(ISPECL [`yt:real`; `drop z`] CH_CNJ_EM) THEN CONV_TAC COMPLEX_RING);;

(* Cx-lift of a real abs-integrable fn is abs-integrable (complex): the      *)
(* linear embedding r |-> Cx r preserves absolute integrability              *)
(* (CXDROP_LINEAR).                                                          *)
let CH_CX_DROP_ABSINT_SET = prove
 (`!(phi:real->real) S. phi absolutely_real_integrable_on S
     ==> (\z. Cx(phi(drop z))) absolutely_integrable_on (IMAGE lift S)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(\z. Cx(phi(drop z))) =
                (\y:real^1. Cx(drop y)) o (lift o phi o drop)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN
  ASM_REWRITE_TAC[CXDROP_LINEAR]);;

let CH_CX_DROP_ABSINT = prove
 (`!(phi:real->real). phi absolutely_real_integrable_on (:real)
     ==> (\z. Cx(phi(drop z))) absolutely_integrable_on (:real^1)`,
  MESON_TAC[CH_CX_DROP_ABSINT_SET; IMAGE_LIFT_UNIV]);;

(* Complex bad part B = Cx bR + ii Cx bI absolutely integrable on UNIV.      *)
let CH_CPLXB_ABSINT = prove
 (`!bR bI:real->real.
     bR absolutely_real_integrable_on (:real) /\
     bI absolutely_real_integrable_on (:real)
     ==> (\z. Cx(bR(drop z)) + ii * Cx(bI(drop z)))
       absolutely_integrable_on (:real^1)`,
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ADD; CH_CX_DROP_ABSINT;
    ABSOLUTELY_INTEGRABLE_COMPLEX_LMUL]);;

(* Product integrability: if B is absolutely integrable and w is bounded and *)
(* measurable, then B * cnj(w) is integrable.                                *)
let CH_B_CNJ_W_INTEGRABLE = prove
 (`!(B:real^1->complex) (w:real^1->complex) (J:real^1->bool) M.
     B absolutely_integrable_on J /\ w measurable_on J /\
     (!y. y IN J ==> norm(w y) <= M)
     ==> (\y. B y * cnj(w y)) integrable_on J`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\y:real^1. lift(M * norm((B:real^1->complex) y))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
      ASM_SIMP_TAC[MEASURABLE_ON_CNJ]];
    ASM_SIMP_TAC[LIFT_CMUL; INTEGRABLE_CMUL;
      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM];
    X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^1`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[NORM_POS_LE]]);;

(* Per-cube pairing bound: for a mean-zero B on a measurable cube J and a    *)
(* bounded measurable packet w with norm(w - wc) <= Md on J,                 *)
(*   |int_J B cnj(w)| <= (int_J norm B) * Md.                                *)
(* It is used with w = psi_s, wc = psi_s(centre of the cube) and Md given by *)
(* CH_PSI_DIFF_CW.                                                           *)
let CH_BAD_CUBE_PAIR = prove
 (`!(B:real^1->complex) (w:real^1->complex) wc (J:real^1->bool) Mb Md.
     measurable J /\
     B absolutely_integrable_on J /\ integral J B = Cx(&0) /\
     w measurable_on J /\ &0 <= Md /\
     (!y. y IN J ==> norm(w y) <= Mb) /\
     (!y. y IN J ==> norm(w y - wc) <= Md)
     ==> norm(integral J (\y. B y * cnj(w y)))
         <= drop(integral J (\y. lift(norm(B y)))) * Md`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^1. lift(norm((B:real^1->complex) y)))
                 integrable_on J` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
     ABSOLUTELY_INTEGRABLE_NORM]; ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^1. (wc:complex)) measurable_on J` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_ON_MEASURABLE_SUBSET; SUBSET_UNIV;
     MEASURABLE_ON_CONST]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^1->complex`; `w:real^1->complex`; `wc:complex`;
                 `\y:real^1. lift Md`; `J:real^1->bool`] CH_MEANZERO_PAIR) THEN
  REWRITE_TAC[LIFT_DROP] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CH_B_CNJ_W_INTEGRABLE];
      MATCH_MP_TAC CH_B_CNJ_W_INTEGRABLE THEN
      MAP_EVERY EXISTS_TAC [`Mb + norm(wc:complex)`] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_ON_SUB];
        X_GEN_TAC `y:real^1` THEN DISCH_TAC THEN
        MATCH_MP_TAC(NORM_ARITH
          `norm(w:complex) <= Mb ==> norm(w - wc) <= Mb + norm wc`) THEN
        ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(\y:real^1. lift(norm((B:real^1->complex) y) * Md)) =
                    (\y. Md % lift(norm(B y)))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
        REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC THEN
          REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRABLE_CMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y:real^1. lift(norm((B:real^1->complex) y) * Md)) =
                (\y. Md % lift(norm(B y)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN AP_TERM_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_CMUL; DROP_CMUL] THEN REAL_ARITH_TAC);;

(* The demodulated packet psi_s = cexp(-(ii yt.)) phi_sigma s carleson_phi   *)
(* is measurable + uniformly bounded -- the two w-side inputs to             *)
(* CH_BAD_CUBE_PAIR.                                                         *)
let CH_PSI_MEAS = prove
 (`!yt (s:int#int#int).
     (\z. cexp(--(ii * Cx yt * Cx(drop z))) *
          phi_sigma s carleson_phi (drop z))
       measurable_on (:real^1)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON THEN
    SUBGOAL_THEN `(\z. cexp(--(ii * Cx yt * Cx(drop z)))) =
                  cexp o (\z:real^1. --(ii * Cx yt * Cx(drop z)))`
      SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      REWRITE_TAC[CONTINUOUS_ON_CEXP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_NEG THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_CX_DROP THEN REWRITE_TAC[CONTINUOUS_ON_ID];
    SUBGOAL_THEN `(\z. phi_sigma s carleson_phi (drop z))
                   IN lspace (:real^1) (&2)`
      MP_TAC THENL
     [ASM_SIMP_TAC[SCHWARTZ_L2; ETA_AX; PHISIG_CARLESON_SCHWARTZ];
      REWRITE_TAC[lspace; IN_ELIM_THM] THEN
        STRIP_TAC]]);;

let CH_PSI_BOUNDED = prove
 (`!yt (s:int#int#int).
     ?Mb. !x. norm(cexp(--(ii * Cx yt * Cx x)) * phi_sigma s carleson_phi x)
              <= Mb`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `phi_sigma s carleson_phi` SCHWARTZ_BOUNDED) THEN
  REWRITE_TAC[PHISIG_CARLESON_SCHWARTZ] THEN
  DISCH_THEN(X_CHOOSE_TAC `Mb:real`) THEN
  EXISTS_TAC `Mb:real` THEN X_GEN_TAC `x:real` THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `norm(cexp(--(ii * Cx yt * Cx x))) = &1` SUBST1_TAC THENL
   [SUBGOAL_THEN `--(ii * Cx yt * Cx x) = ii * Cx(--(yt * x))` SUBST1_TAC THENL
     [REWRITE_TAC[CX_NEG; CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);;

(* The bad-part bound for one cube and one tile (Grafakos-Tao-Terwilleger,   *)
(* equation (14)).  CH_BAD_CUBE_PAIR is applied to the demodulated packet    *)
(*   psi_s = cexp(-(ii y_t .)) phi_sigma s carleson_phi                      *)
(* (y_t = tile_ymid t), with wc = psi_s(c) for a point c (the centre of the  *)
(* cube) and Md the packet-difference bound of CH_PSI_DIFF_CW.  For a        *)
(* mean-zero B on the cube J = IMAGE lift [a,b] whose points are within w of *)
(* c, and a tile s <=_r t with 2^ks w <= 1 (a cube that is small compared    *)
(* with I_s),                                                                *)
(*   |int_J B cnj(psi_s)|                                                    *)
(*      <= (int_J norm B) * Cdiff sqrt(2^ks) (2^ks w) cw(2^ks (c - x_s)).    *)
let CH_BAD_CUBE_TILE = prove
 (`?Cdiff. &0 <= Cdiff /\
    !(B:real^1->complex) (s:int#int#int) t (a:real) b c w.
        measurable (IMAGE lift (real_interval[a,b])) /\
        B absolutely_integrable_on (IMAGE lift (real_interval[a,b])) /\
        integral (IMAGE lift (real_interval[a,b])) B = Cx(&0) /\
        tile_ler s t /\ &2 zpow tile_k s * w <= &1 /\ &0 <= w /\
        (!y. y IN real_interval[a,b] ==> abs(y - c) <= w)
        ==> norm(integral (IMAGE lift (real_interval[a,b]))
                   (\z. B z * cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                                 phi_sigma s carleson_phi (drop z))))
            <= drop(integral (IMAGE lift (real_interval[a,b]))
                             (\z. lift(norm(B z)))) *
               (Cdiff * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * w) *
                cw(&2 zpow tile_k s * (c - tile_xmid s)))`,
  X_CHOOSE_THEN `Cdiff:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pd"))
    CH_PSI_DIFF_CW THEN
  EXISTS_TAC `Cdiff:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`B:real^1->complex`; `s:int#int#int`; `t:int#int#int`; `a:real`;
     `b:real`; `c:real`; `w:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`tile_ymid t`; `s:int#int#int`] CH_PSI_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_TAC `Mb:real`) THEN
  MP_TAC(BETA_RULE(ISPECL
    [`B:real^1->complex`;
     `\z:real^1. cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                 phi_sigma s carleson_phi (drop z)`;
     `cexp(--(ii * Cx(tile_ymid t) * Cx c)) * phi_sigma s carleson_phi c`;
     `IMAGE lift (real_interval[a,b])`; `Mb:real`;
     `Cdiff * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * w) *
      cw(&2 zpow tile_k s * (c - tile_xmid s))`] CH_BAD_CUBE_PAIR)) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MEASURABLE_ON_MEASURABLE_SUBSET THEN
        EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV; CH_PSI_MEAS];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC) THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
          MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_POS]];
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[IN_IMAGE_LIFT_DROP]];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The mass of the tile weight outside a symmetric window around x_s decays  *)
(* quadratically.                                                            *)
(* ------------------------------------------------------------------------- *)

(* Symmetric-window far integral value: over the complement of               *)
(* (x_s - r, x_s + r), cw_tile s integrates to 1/(1+2^{k_s} r)^2             *)
(* (two equal halfline tails, CWTILE_TAIL_COMPLEMENT).                       *)
let CWTILE_FARINT_VALUE = prove
 (`!(s:int#int#int) r. &0 < r
     ==> (cw_tile s has_real_integral
          (&1 / (&1 + &2 zpow (tile_k s) * r) pow 2))
         ({x | x <= tile_xmid s - r} UNION {x | tile_xmid s + r <= x})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:int#int#int`; `tile_xmid s - r`;
    `tile_xmid s + r`] CWTILE_TAIL_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `tile_xmid s - (tile_xmid s - r) = r` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(tile_xmid s + r) - tile_xmid s = r` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 / (&2 * (&1 + &2 zpow (tile_k s) * r) pow 2) +
    &1 / (&2 * (&1 + &2 zpow (tile_k s) * r) pow 2) =
    &1 / (&1 + &2 zpow (tile_k s) * r) pow 2`
   ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* Integrable + value corollary of the far integral.                         *)
let CWTILE_FARINT_INTEGRABLE = prove
 (`!(s:int#int#int) r. &0 < r
     ==> cw_tile s real_integrable_on
         ({x | x <= tile_xmid s - r} UNION {x | tile_xmid s + r <= x}) /\
         real_integral
           ({x | x <= tile_xmid s - r} UNION {x | tile_xmid s + r <= x})
           (cw_tile s) =
         &1 / (&1 + &2 zpow (tile_k s) * r) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:int#int#int`; `r:real`] CWTILE_FARINT_VALUE) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[real_integrable_on; REAL_INTEGRAL_UNIQUE]);;

(* Decay bound: the far integral is <= inv((2^{k_s} r)^2) (drop the +1).     *)
let CWTILE_FARINT_DECAY = prove
 (`!(s:int#int#int) r. &0 < r
     ==> real_integral
           ({x | x <= tile_xmid s - r} UNION {x | tile_xmid s + r <= x})
           (cw_tile s)
         <= inv ((&2 zpow (tile_k s) * r) pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CWTILE_FARINT_INTEGRABLE] THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k s) * r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; GSYM REAL_POW_INV] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

(* Unfolding delta_f and tile_tree: delta_f (1_F) (tile_tree P t) is the sum *)
(* of |carleson_ip 1_F s|^2 over the tiles s IN P with tile_ler s t.         *)
let CH_DELTA_TILE_TREE = prove
 (`!(Ff:real->bool) (P:(int#int#int)->bool) t.
     delta_f (\x. if x IN Ff then Cx(&1) else Cx(&0)) (tile_tree P t) =
     sum {s | s IN P /\ tile_ler s t}
         (\s. norm(carleson_ip (\x. if x IN Ff then Cx(&1)
                                    else Cx(&0)) s) pow 2)`,
  REWRITE_TAC[delta_f; tile_tree]);;

(* ------------------------------------------------------------------------- *)
(* Counting the tiles of one scale in a tree.  First, an integer interval    *)
(*   {n | a <= n /\ n < a + m}                                               *)
(* is finite, with at most m elements.  The tiles s IN P of scale k with     *)
(* tile_ler s t are determined by their spatial index FST(SND s)             *)
(* (TILE_TREE_FST_SND_INJ), and this index ranges over an integer interval   *)
(* with M = 2^(k-k_t) elements (TILE_LE_SUBCELL_ABS).  Hence there are at    *)
(* most M such tiles (CH_TREE_SCALE_CARD); this count is used for the far    *)
(* part of the tree energy.                                                  *)
(* ------------------------------------------------------------------------- *)
let INT_INTERVAL_CARD_LE = prove
 (`!(a:int) (m:num). CARD {n:int | a <= n /\ n < a + &m} <= m`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{n:int | a <= n /\ n < a + &m} =
                IMAGE (\i:num. a + &i) {i | i < m}`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `n:int` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `num_of_int(n - a)` THEN
      MP_TAC(ISPEC `n - a:int` INT_OF_NUM_OF_INT) THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC;
        ASM_ARITH_TAC];
      ASM_ARITH_TAC];
    ASM_MESON_TAC[CARD_IMAGE_LE; FINITE_NUMSEG_LT;
      CARD_NUMSEG_LT]]);;

let TILE_TRIPLE_RECON = prove
 (`!s:int#int#int. (tile_k s, FST(SND s), SND(SND s)) = s`,
  GEN_TAC THEN
  MP_TAC(ISPEC `s:int#int#int` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `bc:int#int`
    SUBST1_TAC)) THEN
  MP_TAC(ISPEC `bc:int#int` PAIR_SURJECTIVE) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:int` (X_CHOOSE_THEN `c:int` SUBST1_TAC)) THEN
  REWRITE_TAC[tile_k]);;

let TILE_LE_SUBCELL_ABS = prove
 (`!(s:int#int#int) (t:int#int#int) M.
     tile_le s t /\ tile_k t <= tile_k s /\
     &2 zpow (tile_k s - tile_k t) = real_of_int M
     ==> FST(SND t) * M <= FST(SND s) /\ FST(SND s) < FST(SND t) * M + M`,
  REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`tile_k(s:int#int#int)`; `tile_k(t:int#int#int)`;
                 `FST(SND(s:int#int#int))`; `SND(SND(s:int#int#int))`;
                 `FST(SND(t:int#int#int))`; `SND(SND(t:int#int#int))`; `M:int`]
         TILE_LE_SUBCELL_INDEX) THEN
  REWRITE_TAC[TILE_TRIPLE_RECON]);;

let CH_TREE_SCALE_CARD = prove
 (`!(P:(int#int#int)->bool) (t:int#int#int) k M.
     FINITE P /\ tile_k t <= k /\ &0 <= M /\
     &2 zpow (k - tile_k t) = real_of_int M
     ==> CARD {s | s IN P /\ tile_ler s t /\ tile_k s = k} <= num_of_int M`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Ak = {s:int#int#int | s IN P /\ tile_ler s t /\ tile_k s = k}` THEN
  SUBGOAL_THEN `!r:int#int#int. r IN Ak ==> tile_k r = k /\ tile_le r t`
    ASSUME_TAC THENL
   [EXPAND_TAC "Ak" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[TILE_LER_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (Ak:(int#int#int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ak" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\s:int#int#int. FST(SND s)) Ak)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:int#int#int`; `v:int#int#int`] THEN
      MP_TAC(ISPECL [`Ak:(int#int#int)->bool`; `k:int`; `t:int#int#int`;
                   `u:int#int#int`; `v:int#int#int`]
                     TILE_TREE_FST_SND_INJ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {n:int | FST(SND(t:int#int#int)) * M <= n /\
                            n < FST(SND t) * M + &(num_of_int M)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `n:int` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:int#int#int`
        (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `tile_k (s:int#int#int) = k /\ tile_le s t`
        STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `&(num_of_int M) = M` SUBST1_TAC THENL
       [ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:int#int#int`; `t:int#int#int`;
        `M:int`] TILE_LE_SUBCELL_ABS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      INT_ARITH_TAC;
      REWRITE_TAC[FINITE_INT_SEG]];
    REWRITE_TAC[INT_INTERVAL_CARD_LE]]);;

(* For a tile s with |x_s - x_t| <= delta, the tile weight cw_tile s at a    *)
(* point x with |x - x_t| >= R > delta is bounded by its value at distance R *)
(* - delta from x_s (CWTILE_DIST_BOUND, since |x - x_s| >= |x - x_t| - |x_s  *)
(* - x_t| >= R - delta).                                                     *)
let CWTILE_ON_ANNULUS = prove
 (`!(s:int#int#int) (xt:real) x R delta.
     abs(tile_xmid s - xt) <= delta /\ delta <= R /\ R <= abs(x - xt)
     ==> cw_tile s x <=
         &2 zpow (tile_k s) * cw(&2 zpow (tile_k s) * (R - delta))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CWTILE_DIST_BOUND THEN
  ASM_REAL_ARITH_TAC);;

(* Integral of cw_tile s over a FAR measurable region G (all points at       *)
(* distance >= R from xt, with x_s within delta of xt): bounded by the       *)
(* annulus-sup value times measure(G).  CWTILE_ON_ANNULUS (sup) +            *)
(* CWTILE_INTEGRAL_LE_MEASURE.                                               *)
let CH_INT_FAR_LE = prove
 (`!(s:int#int#int) (G:real->bool) (xt:real) R delta.
     real_measurable G /\ abs(tile_xmid s - xt) <= delta /\ delta <= R /\
     (!x. x IN G ==> R <= abs(x - xt))
     ==> real_integral G (cw_tile s)
         <= (&2 zpow (tile_k s) * cw(&2 zpow (tile_k s) * (R - delta))) *
            real_measure G`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CWTILE_INTEGRAL_LE_MEASURE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
       MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_POS]];
    ASM_MESON_TAC[CWTILE_ON_ANNULUS]]);;

(* measure(Ff INTER S) = int_S 1_Ff (REAL_INTEGRAL_RESTRICT_INTER).          *)
let CH_MEASURE_INTER_EQ_INT = prove
 (`!(Ff:real->bool) (S:real->bool).
     real_measurable Ff /\ real_measurable S
     ==> real_measure (Ff INTER S) =
         real_integral S (\x. if x IN Ff then &1 else &0)`,
  SIMP_TAC[REAL_INTEGRAL_RESTRICT_INTER; REAL_INTEGRAL_CONST_MEASURABLE;
           REAL_MEASURABLE_INTER; REAL_MUL_LID]);;

(* dyho_mid k n lies in dyho k n (midpoint membership), + the tile-center    *)
(* closeness for the tree order: tile_ler s t ==> |x_s - x_t| < 2^{-k_t}.    *)
(* (x_s, x_t both in tile_I t = dyho(-k_t) n_t of length 2^{-k_t};           *)
(* DYHO_TWO_PTS_CLOSE.)                                                      *)
let DYHO_MID_IN = prove
 (`!(k:int) (n:int). dyho_mid k n IN dyho k n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dyho_mid; dyho; IN_ELIM_THM] THEN
  SUBGOAL_THEN `&0 < &2 zpow k` MP_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CH_TILE_LER_XMID_CLOSE = prove
 (`!(s:int#int#int) (t:int#int#int).
     tile_ler s t
     ==> abs(tile_xmid s - tile_xmid t) < &2 zpow (--(tile_k t))`,
  REWRITE_TAC[FORALL_PAIR_THM; tile_ler; tile_I; tile_xmid; tile_k] THEN
  MAP_EVERY X_GEN_TAC
    [`ks:int`;`nIs:int`;`nJs:int`;`kt:int`;`nIt:int`;`nJt:int`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC DYHO_TWO_PTS_CLOSE THEN
  EXISTS_TAC `nIt:int` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET; DYHO_MID_IN];
    ASM_SIMP_TAC[DYHO_MID_IN]]);;

(* The density cap at a free centre: if G lies in [xt - R, xt + R] and       *)
(* |y - xt| <= R then |Ff INTER G| <= M(1_Ff)(y) * 4R, since G lies in       *)
(* [y - 2R, y + 2R] (CH_HL_INDICATOR_STRADDLE).                              *)
let CH_ANNULUS_DENSITY_CAP = prove
 (`!(Ff:real->bool) (xt:real) (G:real->bool) (y:real) R.
     real_measurable Ff /\ real_measurable G /\ &0 < R /\
     abs(y - xt) <= R /\
     G SUBSET real_interval[xt - R, xt + R]
     ==> real_measure (Ff INTER G)
         <= hl_maximal (\u. if u IN Ff then &1 else &0) y * (&4 * R)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_measure (Ff INTER real_interval[y - &2 * R, y + &2 * R])` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_INTER; REAL_MEASURABLE_REAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `x IN real_interval[xt - R, xt + R]` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[CH_MEASURE_INTER_EQ_INT; REAL_MEASURABLE_REAL_INTERVAL] THEN
    SUBGOAL_THEN `&4 * R = (y + &2 * R) - (y - &2 * R)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CH_HL_INDICATOR_STRADDLE THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The non-straddling density bridge.  The bad part b of the                 *)
(* Calderon-Zygmund decomposition has ||b||_inf ~ 1, so the tree Bessel      *)
(* inequality over all tiles only gives ||b||_2^2 ~ measure(FW) ~ tau R. The *)
(* bound tau^2 R needs the restriction to non-straddling tiles (I_s not      *)
(* contained in Omega), equivalently a per-tile density bound measure(Ff     *)
(* INTER I_s) <~ tau * measure(I_s), which follows from the maximal control  *)
(* at a point y near tile_xmid s with hl_maximal(1_Ff)(y) <= tau.            *)
(* ------------------------------------------------------------------------- *)

(* 2^{-k} <= 2^{1-k}: the tile ball fits in the window of radius 2^{1-k}.    *)
let ZPOW_NEG_LE_ONESUB = prove
 (`!k:int. &2 zpow (--(k:int)) <= &2 zpow (&1 - k)`,
  GEN_TAC THEN
  SUBGOAL_THEN `(&1:int) - k = &1 + --k` SUBST1_TAC THENL
   [INT_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ; REAL_ZPOW_1] THEN
  MP_TAC(ISPEC `--k:int` (SPEC `&2:real` REAL_ZPOW_LT)) THEN REAL_ARITH_TAC);;

(* The spatial interval of a tile lies in the closed 2^{-k_s}-ball around    *)
(* x_s.                                                                      *)
let TILE_I_SUBSET_MID_BALL = prove
 (`!(s:int#int#int).
     tile_I s SUBSET
     real_interval[tile_xmid s - &2 zpow (--(tile_k s)),
                   tile_xmid s + &2 zpow (--(tile_k s))]`,
  MATCH_MP_TAC(MESON[PAIR_SURJECTIVE]
    `(!k nI nJ. P(k,nI,nJ)) ==> (!s:int#int#int. P s)`) THEN
  REWRITE_TAC[tile_I; tile_xmid; tile_k; dyho; dyho_mid; SUBSET;
    IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ASM_REAL_ARITH_TAC);;

(* The density bridge: maximal control at a point within 2^{1-k_s} of the    *)
(* tile gives measure(Ff INTER I_s) <= 4 tau * 2^{1-k_s} = 8 tau *           *)
(* measure(I_s), i.e. Ff has density at most 8 tau on the tile.              *)
let CH_TILE_DENSITY_BRIDGE = prove
 (`!(Ff:real->bool) (s:int#int#int) (y:real).
     real_measurable Ff /\
     abs(y - tile_xmid s) < &2 zpow (&1 - tile_k s)
     ==> real_measure (Ff INTER tile_I s)
         <= hl_maximal (\u. if u IN Ff then &1 else &0) y *
            (&4 * &2 zpow (&1 - tile_k s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`Ff:real->bool`; `tile_xmid s`; `tile_I s`; `y:real`;
      `&2 zpow (&1 - tile_k s)`]
    CH_ANNULUS_DENSITY_CAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[TILE_I_MEASURABLE_TILE] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `real_interval[tile_xmid s - &2 zpow (--(tile_k s)),
                               tile_xmid s + &2 zpow (--(tile_k s))]` THEN
      REWRITE_TAC[TILE_I_SUBSET_MID_BALL; SUBSET; IN_REAL_INTERVAL] THEN
        MP_TAC(ISPEC `tile_k s` ZPOW_NEG_LE_ONESUB) THEN REAL_ARITH_TAC];
    DISCH_THEN ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Geometric domination for the far-tail annular series.  The integral of    *)
(* cw_tile_s over the part of F outside the window W_t is the sum over the   *)
(* annuli A_j (radii 2^j R_0) of the integrals over F cap A_j, and is        *)
(* dominated tile by tile by a geometric series in j: the summand, a tail    *)
(* 2^k cw(2^k R_j) times a density ~ 2^j R_0, decays like 4^{-j}.            *)
(* CW_GEOM_MODEL gives the closed form sum_j cw(a 2^j) 2^j <= 2/a^3, from    *)
(* cw(x) <= 1/x^3 for each term (CW_TERM_POW_BOUND) and the geometric sum    *)
(* sum_j 4^{-j} <= 2 (GEOM_QUARTER_SUM).                                     *)
(* ------------------------------------------------------------------------- *)
let CW_TERM_POW_BOUND = prove
 (`!(a:real) j. &0 < a
     ==> cw (a * &2 pow j) * &2 pow j <= inv(a pow 3) * inv(&4 pow j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow j /\ &4 pow j = &2 pow j * &2 pow j`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[cw; REAL_INV_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv((a * &2 pow j) pow 3) * &2 pow j` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let GEOM_QUARTER_SUM = prove
 (`!n:num. sum (0..n) (\j. inv(&4 pow j)) <= &2`,
  GEN_TAC THEN
  SUBGOAL_THEN `!j:num. inv(&4 pow j) = (inv(&4)) pow j`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_INV_POW]; ALL_TAC] THEN
  MP_TAC(ISPECL [`inv(&4)`; `0`; `n:num`] SUM_GP) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[real_pow] THEN
  SUBGOAL_THEN `&0 <= inv(&4) * inv(&4) pow n` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

let CW_GEOM_MODEL = prove
 (`!(a:real) n. &0 < a
     ==> sum (0..n) (\j. cw (a * &2 pow j) * &2 pow j) <= &2 * inv(a pow 3)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..n) (\j. inv(a pow 3) * inv(&4 pow j))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_LE_NUMSEG; CW_TERM_POW_BOUND];
    REWRITE_TAC[SUM_LMUL] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV; REAL_POW_LE; REAL_LT_IMP_LE];
      REWRITE_TAC[GEOM_QUARTER_SUM]]]);;

(* ------------------------------------------------------------------------- *)
(* Shells: {R <= |x - xt| <= Rout} is the union of two closed intervals,     *)
(* hence measurable.  These are used for the far integral bound              *)
(* CH_FAR_INT_ANNULAR.                                                       *)
(* ------------------------------------------------------------------------- *)
let SHELL_EQ_TWO_INTERVALS = prove
 (`!(xt:real) R Rout. &0 <= R /\ R <= Rout
     ==> {x | R <= abs(x - xt) /\ abs(x - xt) <= Rout} =
         real_interval[xt - Rout, xt - R] UNION
           real_interval[xt + R, xt + Rout]`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  ASM_REAL_ARITH_TAC);;

let SHELL_MEASURABLE = prove
 (`!(xt:real) R Rout. &0 <= R /\ R <= Rout
     ==> real_measurable {x | R <= abs(x - xt) /\ abs(x - xt) <= Rout}`,
  ASM_SIMP_TAC[SHELL_EQ_TWO_INTERVALS; REAL_MEASURABLE_UNION;
    REAL_MEASURABLE_REAL_INTERVAL]);;

(* real_measurable s /\ real_lebesgue_measurable t ==> real_measurable(s     *)
(* INTER t) (via the lift-image bridges + the vector                         *)
(* measurable-inter-lebesgue lemma).                                         *)
let REAL_MEASURABLE_INTER_LEBESGUE = prove
 (`!s t. real_measurable s /\ real_lebesgue_measurable t
         ==> real_measurable (s INTER t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_MEASURABLE_MEASURABLE;
    REAL_LEBESGUE_MEASURABLE] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE lift (s INTER t) = (IMAGE lift s) INTER (IMAGE lift t)`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[IMAGE_INTER_INJ; LIFT_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_MEASURABLE_INTER_LEBESGUE_MEASURABLE THEN
  ASM_REWRITE_TAC[]);;

(* g = 1_F-restricted cw_tile_s integrable on ANY real_lebesgue_measurable   *)
(* set (poss. unbounded, e.g. the far region), since Ff INTER Sc is          *)
(* real_measurable + cw bounded.                                             *)
let CH_FCW_INTEGRABLE_LEBMEAS = prove
 (`!(Ff:real->bool) (s:int#int#int) Sc.
     real_measurable Ff /\ real_lebesgue_measurable Sc
     ==> (\x. if x IN Ff then cw_tile s x else &0) real_integrable_on Sc`,
  ASM_SIMP_TAC[REAL_INTEGRABLE_RESTRICT_INTER; ETA_AX;
    CWTILE_INTEGRABLE_MEASURABLE; REAL_MEASURABLE_INTER_LEBESGUE]);;

(* ---- shell-induction structure for CH_FAR_INT_ANNULAR ----                *)
(* Base: the degenerate shell {R<=|x-xt|<=R} = 2 points, integral 0.         *)
let SHELL_BASE_NULL = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) R.
     real_integral {x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow 0}
                   (\x. if x IN Ff then cw_tile s x else &0) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_pow; REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_NEGLIGIBLE THEN
  EXISTS_TAC `{x:real | R <= abs(x - xt) /\ abs(x - xt) <= R}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{xt - R:real, xt + R}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_INSERT; REAL_NEGLIGIBLE_SING; SUBSET;
      IN_ELIM_THM; IN_INSERT] THEN
    REAL_ARITH_TAC;
    ASM_MESON_TAC[IN_DIFF]]);;

(* Step: S_{SUC N} = S_N UNION A_N (shells nest, boundary negligible).       *)
let SHELL_SUCC_UNION = prove
 (`!(xt:real) R N. &0 < R
     ==> {x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow (SUC N)} =
         {x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow N} UNION
         {x | R * &2 pow N <= abs(x - xt) /\
              abs(x - xt) <= R * &2 pow (SUC N)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &2 pow N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow N <= &2 pow (SUC N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `R <= R * &2 pow N` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `R * &2 pow N <= R * &2 pow (SUC N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  ASM_REAL_ARITH_TAC);;

let SHELL_ANNULUS_DISJOINT = prove
 (`!(xt:real) R N. &0 < R
     ==> real_negligible
          ({x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow N} INTER
           {x | R * &2 pow N <= abs(x - xt) /\
                abs(x - xt) <= R * &2 pow (SUC N)})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{(xt - R * &2 pow N), (xt + R * &2 pow N)}:real->bool` THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_INSERT; REAL_NEGLIGIBLE_SING; SUBSET; IN_INTER;
    IN_ELIM_THM; IN_INSERT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The far integral of the tile weight: the integral over Ff INTER S_N, for  *)
(* the shells S_N, is bounded by induction over N, using the density bound   *)
(* at a free centre on each annulus, by M(y) times a partial sum of a        *)
(* geometric series; summing the series and passing to the limit gives       *)
(* CH_FAR_INT_ANNULAR.                                                       *)
(* ------------------------------------------------------------------------- *)
let CH_INT_FCW_ADD = prove
 (`!(Ff:real->bool) (s:int#int#int) S T.
     real_measurable Ff /\ real_measurable S /\ real_measurable T /\
     real_negligible(S INTER T)
     ==> real_integral (S UNION T) (\x. if x IN Ff then cw_tile s x else &0) =
         real_integral S (\x. if x IN Ff then cw_tile s x else &0) +
         real_integral T (\x. if x IN Ff then cw_tile s x else &0)`,
  ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; HAS_REAL_INTEGRAL_UNION;
    REAL_INTEGRABLE_INTEGRAL; CH_FCW_INTEGRABLE_LEBMEAS;
    REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE]);;

let CH_ANNULUS_STEP_BOUND = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta N.
     real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R /\
     abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R * &2 pow (SUC N)
     ==> real_integral {x | R * &2 pow N <= abs(x - xt) /\
                            abs(x - xt) <= R * &2 pow (SUC N)}
                       (\x. if x IN Ff then cw_tile s x else &0)
         <= hl_maximal (\u. if u IN Ff then &1 else &0) y *
            (&2 zpow (tile_k s) *
             cw(&2 zpow (tile_k s) * (R * &2 pow N - delta))) *
            (&4 * (R * &2 pow (SUC N)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `AN = {x | R * &2 pow N <= abs(x - xt) /\
                        abs(x - xt) <= R * &2 pow (SUC N)}` THEN
  SUBGOAL_THEN `&0 < R * &2 pow N /\ R * &2 pow N <= R * &2 pow (SUC N)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
          [REAL_ARITH_TAC; ARITH_TAC]]]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measurable (AN:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "AN" THEN MATCH_MP_TAC SHELL_MEASURABLE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[ISPEC `cw_tile s` REAL_INTEGRAL_RESTRICT_INTER] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 zpow (tile_k s) *
               cw(&2 zpow (tile_k s) * (R * &2 pow N - delta))) *
              real_measure (Ff INTER AN)` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:int#int#int`; `Ff INTER AN:real->bool`; `xt:real`;
                   `R * &2 pow N`; `delta:real`] CH_INT_FAR_LE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MEASURABLE_INTER];
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `R:real` THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC]];
        X_GEN_TAC `x:real` THEN EXPAND_TAC "AN" THEN
          REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
        STRIP_TAC];
      REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 zpow (tile_k s) *
                 cw(&2 zpow (tile_k s) * (R * &2 pow N - delta))) *
                (hl_maximal (\u. if u IN Ff then &1 else &0) y *
                 (&4 * (R * &2 pow (SUC N))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_IMP_LE THEN
           MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_POS]];
        MP_TAC(ISPECL [`Ff:real->bool`; `xt:real`; `AN:real->bool`;
          `y:real`; `R * &2 pow (SUC N)`]
               CH_ANNULUS_DENSITY_CAP) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC;
            EXPAND_TAC "AN" THEN
              REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
            ASM_REAL_ARITH_TAC];
          DISCH_THEN ACCEPT_TAC]];
      REAL_ARITH_TAC]]);;

let CH_FAR_INT_SHELL_N = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta N.
     real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R / &2 /\
     abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R
     ==> real_integral {x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow N}
                       (\x. if x IN Ff then cw_tile s x else &0)
         <= hl_maximal (\u. if u IN Ff then &1 else &0) y *
            sum {j | j < N}
                (\j. (&2 zpow (tile_k s) *
                      cw(&2 zpow (tile_k s) * (R * &2 pow j - delta))) *
                     (&4 * (R * &2 pow (SUC j))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SPEC_TAC(`N:num`,`N:num`) THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[SHELL_BASE_NULL; SUM_CLAUSES_NUMSEG_LT;
     REAL_MUL_RZERO; REAL_LE_REFL];
    (* step: S_{SUC N} = S_N UNION A_N; additivity + IH + per-annulus step.  *)
    REWRITE_TAC[SUM_CLAUSES_NUMSEG_LT] THEN
    MP_TAC(ISPECL [`xt:real`; `R:real`; `N:num`] SHELL_SUCC_UNION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL
     [`Ff:real->bool`; `s:int#int#int`;
      `{x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow N}`;
      `{x | R * &2 pow N <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow (SUC N)}`]
     CH_INT_FCW_ADD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SHELL_MEASURABLE THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
            MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC]];
        MATCH_MP_TAC SHELL_MEASURABLE THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
              [REAL_ARITH_TAC; ARITH_TAC]]];
        ASM_SIMP_TAC[SHELL_ANNULUS_DISJOINT]];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [FIRST_X_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC CH_ANNULUS_STEP_BOUND THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `R <= R * &2 pow (SUC N)`
          (fun th -> ASM_MESON_TAC[th; REAL_LE_TRANS]) THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
                        MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC]]]]);;

(* ------------------------------------------------------------------------- *)
(* The annular partial sums are bounded by 128/(2^{2ks} R^2), uniformly in N *)
(* (CH_ANNULAR_SUM_GEOM): each term is bounded by CH_ANNULAR_TERM_LE (via    *)
(* the monotonicity of cw and ANTITONE_ARG), and the resulting geometric     *)
(* series by CH_ANNULAR_GEOMTAIL (via CW_GEOM_MODEL and ASG_ARITH).          *)
(* ------------------------------------------------------------------------- *)
let ANTITONE_ARG = prove
 (`!q R delta j. &0 < q /\ &0 < R /\ &0 <= delta /\ delta <= R / &2
     ==> &0 <= (q * R / &2) * &2 pow j /\
         &0 <= q * (R * &2 pow j - delta) /\
         (q * R / &2) * &2 pow j <= q * (R * &2 pow j - delta)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* R/2 <= (R/2)*2^j  (since 2^j>=1, R/2>=0)                                *)
  SUBGOAL_THEN `R / &2 <= R / &2 * &2 pow j` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* (q*R/2)*2^j = q*((R/2)*2^j) and (R/2)*2^j <= R*2^j - delta              *)
  SUBGOAL_THEN `(q * R / &2) * &2 pow j = q * (R / &2 * &2 pow j)`
    SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let ASG_ARITH = prove
 (`!q R:real. &0 < q /\ &0 < R
     ==> (&8 * R * q) * (&2 * inv((q * R / &2) pow 3)) =
         &128 * inv(q pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q = &0) /\ ~(R = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `q:real` REAL_MUL_RINV) THEN
    MP_TAC(SPEC `R:real` REAL_MUL_RINV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv((q * R / &2) pow 3) = &8 * (inv q pow 3 * inv R pow 3)`
    SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; real_div; REAL_INV_MUL;
     REAL_POW_MUL] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_INV_POW] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(&8 * R * q) * &2 * &8 * (inv q pow 3 * inv R pow 3) =
    &128 * (inv q pow 2 * inv R pow 2) * ((R * inv R) * (q * inv q))`
   SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID]);;

let CH_ANNULAR_TERM_LE = prove
 (`!(q:real) R delta j.
     &0 < R /\ &0 <= delta /\ delta <= R / &2 /\ &0 < q
     ==> (q * cw(q * (R * &2 pow j - delta))) * (&4 * (R * &2 pow (SUC j)))
         <= (&8 * R * q) * (cw((q * R / &2) * &2 pow j) * &2 pow j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real`; `R:real`; `delta:real`; `j:num`] ANTITONE_ARG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cw (q * (R * &2 pow j - delta)) <=
                cw ((q * R / &2) * &2 pow j)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC CW_ANTITONE THEN
    MATCH_MP_TAC(REAL_ARITH
      `&0 <= a /\ &0 <= b /\ a <= b ==> abs a <= abs b`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[real_pow] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(q * cw ((q * R / &2) * &2 pow j)) *
              (&4 * (R * (&2 * &2 pow j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
    REAL_ARITH_TAC]);;

let CH_ANNULAR_GEOMTAIL = prove
 (`!(q:real) R N.
     &0 < q /\ &0 < R
     ==> (&8 * R * q) *
         sum {j | j < N} (\j. cw((q * R / &2) * &2 pow j) * &2 pow j)
         <= &128 * inv(q pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &8 * R * q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN
       ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&8 * R * q) *
              sum (0..N) (\j. cw ((q * R / &2) * &2 pow j) * &2 pow j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; FINITE_NUMSEG] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_POS];
        MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC]]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&8 * R * q) * (&2 * inv((q * R / &2) pow 3))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MP_TAC(ISPECL [`q * R / &2`; `N:num`] CW_GEOM_MODEL) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REAL_ARITH_TAC];
        DISCH_THEN ACCEPT_TAC]];
    ASM_SIMP_TAC[REAL_EQ_IMP_LE; ASG_ARITH]]);;

let CH_ANNULAR_SUM_GEOM = prove
 (`!(s:int#int#int) R delta N.
     &0 < R /\ &0 <= delta /\ delta <= R / &2
     ==> sum {j | j < N}
             (\j. (&2 zpow (tile_k s) *
                   cw(&2 zpow (tile_k s) * (R * &2 pow j - delta))) *
                  (&4 * (R * &2 pow (SUC j))))
         <= &128 * inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `q = &2 zpow (tile_k s)` THEN
  SUBGOAL_THEN `&0 < q` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {j | j < N}
        (\j. (&8 * R * q) * (cw((q * R / &2) * &2 pow j) * &2 pow j))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_LE; FINITE_NUMSEG_LT; CH_ANNULAR_TERM_LE];
    ASM_SIMP_TAC[SUM_LMUL; CH_ANNULAR_GEOMTAIL]]);;

(* Uniform-in-N shell bound: combines CH_FAR_INT_SHELL_N (per-N) +           *)
(* CH_ANNULAR_SUM_GEOM (geometric sum) + CH_HL_INDICATOR_POS.  int over      *)
(* shell S_N <= 128 M(y)/(2^{2ks}R^2).                                       *)
let CH_FAR_INT_SHELL_BOUND = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta N.
     real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R / &2 /\
     abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R
     ==> real_integral {x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow N}
                       (\x. if x IN Ff then cw_tile s x else &0)
         <= &128 * hl_maximal (\u. if u IN Ff then &1 else &0) y *
            inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `hl_maximal (\u. if u IN Ff then &1 else &0) y *
              sum {j | j < N}
                  (\j. (&2 zpow (tile_k s) *
                        cw(&2 zpow (tile_k s) * (R * &2 pow j - delta))) *
                       (&4 * (R * &2 pow (SUC j))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_FAR_INT_SHELL_N];
    REWRITE_TAC[REAL_ARITH `&128 * m * a * b = m * (&128 * a * b)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_HL_INDICATOR_POS];
      ASM_SIMP_TAC[CH_ANNULAR_SUM_GEOM]]]);;

(* The far region R <= abs(x - xt) is Lebesgue measurable (the complement of *)
(* an open interval).                                                        *)
let FAR_REGION_MEASURABLE = prove
 (`!(xt:real) R. real_lebesgue_measurable {x | R <= abs(x - xt)}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x | R <= abs(x - xt)} =
                (:real) DIFF {x | abs(x - xt) < R}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_DIFF THEN
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_UNIV] THEN
  SUBGOAL_THEN `{x | abs(x - xt) < R} = real_interval(xt - R, xt + R)`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_INTERVAL]);;

(* The integral over the far region of the shell-cut, F-restricted weight    *)
(* equals the integral over the shell (REAL_INTEGRAL_RESTRICT_INTER).        *)
let CH_FF_SHELL_INT = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) R k.
     real_integral {x | R <= abs(x - xt)}
       (\x. if x IN {x | abs(x - xt) <= R * &2 pow k}
            then (if x IN Ff then cw_tile s x else &0) else &0)
     = real_integral {x | R <= abs(x - xt) /\ abs(x - xt) <= R * &2 pow k}
         (\x. if x IN Ff then cw_tile s x else &0)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_INTEGRAL_RESTRICT_INTER] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* Lemmas for the monotone convergence argument in CH_FAR_INT_ANNULAR, which *)
(* bounds the integral over the whole far region {x | R <= |x - xt|}.        *)
(* Below, ff k denotes the integrand 1_F cw_tile s restricted to the         *)
(* interval |x - xt| <= R 2^k.                                               *)
(*                                                                           *)
(* An Archimedean step: for R > 0, a/R < 2^n ==> a <= R 2^n.                 *)
let FAR_ARCH_ARITH = prove
 (`!(a:real) R n. &0 < R /\ a / R < &2 pow n ==> a <= R * &2 pow n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a < &2 pow n * R` MP_TAC THENL
   [ASM_MESON_TAC[REAL_LT_LDIV_EQ];
    REAL_ARITH_TAC]);;

(* R <= R * 2^k.                                                             *)
let R_LE_RPOW2 = prove
 (`!R k. &0 < R ==> R <= R * &2 pow k`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC]);;

(* ff k (shell-cut F-cw) integrable on far.                                  *)
let CH_FF_INTEGRABLE = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) R k.
     real_measurable Ff /\ &0 < R
     ==> (\x. if x IN {x | abs(x - xt) <= R * &2 pow k}
              then (if x IN Ff then cw_tile s x else &0) else &0)
         real_integrable_on {x | R <= abs(x - xt)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. if x IN {x | abs(x - xt) <= R * &2 pow k}
         then (if x IN Ff then cw_tile s x else &0) else &0) =
    (\x. if x IN (Ff INTER {x | abs(x - xt) <= R * &2 pow k})
         then cw_tile s x else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; IN_INTER] THEN
     ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CH_FCW_INTEGRABLE_LEBMEAS THEN
  REWRITE_TAC[FAR_REGION_MEASURABLE] THEN
  MATCH_MP_TAC REAL_MEASURABLE_INTER THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{x:real | abs(x - xt) <= R * &2 pow k} =
                real_interval[xt - R * &2 pow k, xt + R * &2 pow k]`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL]]);;

(* ff monotone increasing.                                                   *)
let CH_FF_MONO = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) R k x.
     &0 < R
     ==> (if x IN {x | abs(x - xt) <= R * &2 pow k}
          then (if x IN Ff then cw_tile s x else &0) else &0)
         <= (if x IN {x | abs(x - xt) <= R * &2 pow (SUC k)}
             then (if x IN Ff then cw_tile s x else &0) else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `R * &2 pow k <= R * &2 pow (SUC k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; ARITH_TAC]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (if x IN Ff then cw_tile s x else &0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; CW_TILE_POS]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* nonneg of the shell F-cw integral.                                        *)
let CH_FF_SHELL_INT_POS = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) R k.
     real_measurable Ff /\ &0 < R
     ==> &0 <= real_integral {x | R <= abs(x - xt) /\
                                  abs(x - xt) <= R * &2 pow k}
                 (\x. if x IN Ff then cw_tile s x else &0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC CH_FCW_INTEGRABLE_LEBMEAS THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE THEN
      MATCH_MP_TAC SHELL_MEASURABLE THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[R_LE_RPOW2]]];
    ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; CW_TILE_POS]]);;

(* The shell integrals are bounded by 128 M(y)/(2^{2ks}R^2)                  *)
(* (CH_FF_SHELL_INT, CH_FF_SHELL_INT_POS, CH_FAR_INT_SHELL_BOUND).           *)
let CH_FF_INT_BOUNDED = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta.
     real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R / &2 /\
     abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R
     ==> real_bounded
           {real_integral {x | R <= abs(x - xt)}
              (\x. if x IN {x | abs(x - xt) <= R * &2 pow k}
                   then (if x IN Ff then cw_tile s x else &0)
                     else &0) | k IN (:num)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_bounded] THEN
  EXISTS_TAC `&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y *
              inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)` THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[CH_FF_SHELL_INT] THEN
  MP_TAC(ISPECL [`Ff:real->bool`; `s:int#int#int`; `xt:real`; `R:real`;
                 `k:num`] CH_FF_SHELL_INT_POS) THEN
  MP_TAC(ISPECL [`Ff:real->bool`; `s:int#int#int`; `xt:real`; `y:real`;
                 `R:real`; `delta:real`; `k:num`] CH_FAR_INT_SHELL_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `jj:real = real_integral {x | R <= abs(x - xt) /\
                                           abs(x - xt) <= R * &2 pow k}
                     (\x. if x IN Ff then cw_tile s x else &0)` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The per-tile far integral bound                                           *)
(*   int over Ff cap far region of cw_tile_s                                 *)
(*      <= 128 M(1_F)(y) inv(2^(2ks)) inv(R^2),                              *)
(* by monotone convergence (REAL_MONOTONE_CONVERGENCE_INCREASING): the       *)
(* shell-cut integrands increase to the whole far integrand, with the        *)
(* uniform bound CH_FF_INT_BOUNDED.                                          *)
(* ------------------------------------------------------------------------- *)
let CH_FAR_INT_ANNULAR = prove
 (`!(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta.
       real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R / &2 /\
       abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R
       ==> real_integral {x | R <= abs(x - xt)}
                         (\x. if x IN Ff then cw_tile s x else &0)
           <= &128 * hl_maximal (\u. if u IN Ff then &1 else &0) y *
              inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\k:num. \x. if x IN {x | abs(x - xt) <= R * &2 pow k}
                 then (if x IN Ff then cw_tile s x else &0) else &0`;
    `\x. if x IN Ff then cw_tile s x else &0`;
    `{x | R <= abs(x - xt)}`]
    REAL_MONOTONE_CONVERGENCE_INCREASING) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_FF_INTEGRABLE];
      ASM_SIMP_TAC[CH_FF_MONO];
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC REALLIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
        MP_TAC(ISPEC `abs(x - xt) / R` REAL_ARCH_POW2) THEN
      DISCH_THEN(X_CHOOSE_TAC `k0:num`) THEN EXISTS_TAC `k0:num` THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(x - xt) <= R * &2 pow n` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN
         EXISTS_TAC `R * &2 pow k0` THEN CONJ_TAC THENL
         [MATCH_MP_TAC FAR_ARCH_ARITH;
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
              [REAL_ARITH_TAC; ASM_ARITH_TAC]]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CH_FF_INT_BOUNDED]];
    REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`sequentially`;
      `\k:num. real_integral {x | R <= abs(x - xt)}
        (\x. if x IN {x | abs(x - xt) <= R * &2 pow k}
             then (if x IN Ff then cw_tile s x else &0) else &0)`;
      `real_integral {x | R <= abs(x - xt)}
         (\x. if x IN Ff then cw_tile s x else &0)`;
      `&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y *
       inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`] REALLIM_UBOUND) THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[CH_FF_SHELL_INT] THEN
    MP_TAC(ISPECL [`Ff:real->bool`; `s:int#int#int`; `xt:real`; `y:real`;
                   `R:real`; `delta:real`; `k:num`]
      CH_FAR_INT_SHELL_BOUND) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Per-tile far bounds, from CH_FAR_INT_ANNULAR and CH_IP_INDICATOR_LE:      *)
(*  - FAR_TILE_LE: |ip(1_{Ff cap far},s)|                                    *)
(*    <= C M(y) inv(sqrt 2^ks) inv(2^{2ks}) inv(R^2);                        *)
(*  - FAR_TILE_SQ: the corresponding bound for the square.                   *)
(* ------------------------------------------------------------------------- *)
let FAR_TILE_LE = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta.
       real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R / &2 /\
       abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R
       ==> norm(carleson_ip
             (\x. if x IN (Ff INTER {x | R <= abs(x - xt)})
               then Cx(&1) else Cx(&0)) s)
           <= C * hl_maximal (\u. if u IN Ff then &1 else &0) y *
              inv(sqrt(&2 zpow (tile_k s))) *
              inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ip"))
    CH_IP_INDICATOR_LE THEN
  EXISTS_TAC `C1 * &128` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`Ff:real->bool`; `s:int#int#int`; `xt:real`; `y:real`;
     `R:real`; `delta:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `real_measurable (Ff INTER {x | R <= abs(x - xt)})`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_INTER_LEBESGUE;
     FAR_REGION_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(&2 zpow (tile_k s)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  (* int_{Ff cap far} cw <= 128 M(y) inv(2^{2ks}) inv(R^2)                   *)
  SUBGOAL_THEN
   `real_integral (Ff INTER {x | R <= abs(x - xt)}) (\x. cw_tile s x)
    <= &128 * hl_maximal (\u. if u IN Ff then &1 else &0) y *
       inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cw_tile s`; `Ff:real->bool`; `{x | R <= abs(x - xt)}`]
      REAL_INTEGRAL_RESTRICT_INTER) THEN
    REWRITE_TAC[ETA_AX] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`Ff:real->bool`; `s:int#int#int`; `xt:real`;
      `y:real`; `R:real`; `delta:real`]
      CH_FAR_INT_ANNULAR) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * inv(sqrt(&2 zpow (tile_k s))) *
              real_integral (Ff INTER {x | R <= abs(x - xt)})
                            (\x. cw_tile s x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    REWRITE_TAC[REAL_ARITH
     `(C1 * &128) * m * isq * iq * ir = C1 * isq * (&128 * m * iq * ir)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let FAR_TILE_SQ = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (s:int#int#int) (xt:real) (y:real) R delta.
       real_measurable Ff /\ &0 < R /\ &0 <= delta /\ delta <= R / &2 /\
       abs(tile_xmid s - xt) <= delta /\ abs(y - xt) <= R
       ==> norm(carleson_ip
             (\x. if x IN (Ff INTER {x | R <= abs(x - xt)})
                  then Cx(&1) else Cx(&0)) s) pow 2
           <= C * (hl_maximal (\u. if u IN Ff then &1 else &0) y) pow 2 *
              inv(&2 zpow (tile_k s)) *
              inv((&2 zpow (tile_k s)) pow 2) pow 2 * inv(R pow 2) pow 2`,
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "t"))
    FAR_TILE_LE THEN
  EXISTS_TAC `(C0:real) pow 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
   [`Ff:real->bool`; `s:int#int#int`; `xt:real`; `y:real`;
     `R:real`; `delta:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C0 * hl_maximal (\u. if u IN Ff then &1 else &0) y *
               inv(sqrt(&2 zpow (tile_k s))) *
               inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)) pow 2` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_POW_LE2; NORM_POS_LE];
    ASM_SIMP_TAC[REAL_POW_MUL; REAL_POW_INV; SQRT_POW_2; REAL_LT_IMP_LE] THEN
      ASM_REAL_ARITH_TAC]);;

(* Per-scale far energy: sum over scale-k tiles s<=_r t of |ip(1_{Ff cap     *)
(* far_t},s)|^2 <= (count 2^{k-k_t}) x (FAR_TILE_SQ bound at scale k).       *)
(* SUM_BOUND + FAR_TILE_SQ + CH_TREE_SCALE_CARD; delta=2^(-k_t) via          *)
(* CH_TILE_LER_XMID_CLOSE.  far_t = abs(x-xmid t)>=R.                        *)
let FAR_SCALE_SQ = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (P:(int#int#int)->bool) (t:int#int#int) (y:real) R k M.
       real_measurable Ff /\ FINITE P /\ tile_k t <= k /\ &0 <= M /\
       &2 zpow (k - tile_k t) = real_of_int M /\
       &2 zpow (--(tile_k t)) <= R / &2 /\ &0 < R /\ abs(y - tile_xmid t) <= R
       ==> sum {s | s IN P /\ tile_ler s t /\ tile_k s = k}
               (\s. norm(carleson_ip
                      (\x. if x IN (Ff INTER {x | R <= abs(x - tile_xmid t)})
                           then Cx(&1) else Cx(&0)) s) pow 2)
           <= &(num_of_int M) *
              (C * (hl_maximal (\u. if u IN Ff then &1 else &0) y) pow 2 *
               inv(&2 zpow k) * inv((&2 zpow k) pow 2) pow 2 *
               inv(R pow 2) pow 2)`,
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sq"))
    FAR_TILE_SQ THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`; `y:real`;
     `R:real`; `k:int`; `M:int`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `Bk = C0 * (hl_maximal (\u. if u IN Ff then &1 else &0) y) pow 2 *
                   inv(&2 zpow k) * inv((&2 zpow k) pow 2) pow 2 *
                   inv(R pow 2) pow 2` THEN
  SUBGOAL_THEN `&0 <= Bk` ASSUME_TAC THENL
   [EXPAND_TAC "Bk" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_LE_INV_EQ] THEN
    TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC); ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {s:int#int#int | s IN P /\ tile_ler s t /\
                                        tile_k s = k}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {s:int#int#int | s IN P /\ tile_ler s t /\
                                      tile_k s = k}) * Bk` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    X_GEN_TAC `s:int#int#int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "Bk" THEN
    UNDISCH_TAC `tile_k (s:int#int#int) = k` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
    USE_THEN "sq" (fun th -> MATCH_MP_TAC (SPECL
      [`Ff:real->bool`; `s:int#int#int`; `tile_xmid t`; `y:real`; `R:real`;
       `&2 zpow (--(tile_k t))`] th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN
       MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_IMP_LE; CH_TILE_LER_XMID_CLOSE]];
    ASM_SIMP_TAC[REAL_LE_RMUL; REAL_OF_NUM_LE; CH_TREE_SCALE_CARD]]);;

(* ========================================================================= *)
(* The far energy of a whole tree (Grafakos-Tao-Terwilleger, Lemma 1, far    *)
(* side).  The per-scale bound FAR_SCALE_SQ is summed over the scales of the *)
(* tree {s | s IN P /\ tile_ler s t}, reindexed by j = tile_k s - tile_k t,  *)
(* a natural number since a tile of the tree is finer than its top; the sum  *)
(* is dominated by the geometric series                                      *)
(*   sum_j inv(16^j) <= 16/15.                                               *)
(* The factor inv(16^j) = 2^(-4j) comes from the factor 2^(-5k_s) in the     *)
(* bound for each tile times the number 2^(k_s-k_t) of tiles of scale k_s.   *)
(* ========================================================================= *)

(* Summing over the fibres of an index map: let D >= 0, 0 <= q < 1 and       *)
(* g >= 0 on the finite set A.  If for every jj                              *)
(*   sum {a | a IN A /\ nidx a = jj} g <= D * q^jj,                          *)
(* then sum A g <= D / (1 - q).  (Partition A into the fibres of nidx by     *)
(* SUM_IMAGE_GEN; IMAGE nidx A is contained in some 0..N, and SUM_GP sums    *)
(* the geometric series.)                                                    *)
let GEOM_FIBER_SUM_BOUND = prove
 (`!(A:A->bool) (nidx:A->num) (g:A->real) D q.
     FINITE A /\ &0 <= D /\ &0 <= q /\ q < &1 /\
     (!a. a IN A ==> &0 <= g a) /\
     (!jj. sum {a | a IN A /\ nidx a = jj} g <= D * q pow jj)
     ==> sum A g <= D * inv(&1 - q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`nidx:A->num`; `g:A->real`; `A:A->bool`] SUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\x:num. x`; `IMAGE (nidx:A->num) A`]
    UPPER_BOUND_FINITE_SET) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (0..N) (\jj. D * q pow jj)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (nidx:A->num) A) (\jj. D * q pow jj)` THEN
    ASM_SIMP_TAC[SUM_LE; FINITE_IMAGE] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG; LE_0; REAL_LE_MUL;
                 REAL_POW_LE];
    ASM_SIMP_TAC[SUM_LMUL; SUM_GP; CONJUNCT1 LT; REAL_LT_IMP_NE] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[real_div; real_pow] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x * i ==> (&1 - x) * i <= i`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LE_INV_EQ;
                 REAL_ARITH `q < &1 ==> &0 <= &1 - q`]]);;

(* The cancellation for one fibre, used in FAR_SCALE_RHS_EQ with a = 2^(k_t) *)
(* and b = 2^j: for a, b, R > 0,                                             *)
(*   b * (Cc * Mv^2 * inv(ab) * inv((ab)^2)^2 * inv(R^2)^2)                  *)
(*     = (Cc * Mv^2 * inv(a^5) * inv((R^2)^2)) * inv(b^4)                    *)
(* (by ring arithmetic from b * inv b = 1).                                  *)
let FAR_FIBER_ARITH = prove
 (`!a b Cc Mv R.
     &0 < a /\ &0 < b /\ &0 < R
     ==> b * (Cc * Mv pow 2 * inv(a * b) * inv((a * b) pow 2) pow 2 *
              inv(R pow 2) pow 2) =
         (Cc * Mv pow 2 * inv(a pow 5) * inv((R pow 2) pow 2)) * inv(b pow 4)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_INV_MUL; REAL_INV_POW] THEN
  SUBGOAL_THEN `b * inv b = &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RING);;

(* RHS collapse of FAR_SCALE_SQ at scale k = k_t + &j to the geometric form  *)
(* D * inv(16^j), where D = C0*Mv^2*inv((2 zpow k_t)^5)*inv((R^2)^2).        *)
let FAR_SCALE_RHS_EQ = prove
 (`!kt j C0 Mv R.
     &0 < R
     ==> &(2 EXP j) * (C0 * Mv pow 2 * inv(&2 zpow (kt + &j)) *
                       inv((&2 zpow (kt + &j)) pow 2) pow 2 *
                       inv(R pow 2) pow 2) =
         (C0 * Mv pow 2 * inv((&2 zpow kt) pow 5) * inv((R pow 2) pow 2)) *
         inv(&16 pow j)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 zpow (kt + &j) = &2 zpow kt * &2 pow j` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ;
     REAL_ZPOW_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `&(2 EXP j) = &2 pow j` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&16 pow j = (&2 pow j) pow 4` SUBST1_TAC THENL
   [SUBGOAL_THEN `(&16:real) = &2 pow 4` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_POW] THEN AP_TERM_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC FAR_FIBER_ARITH THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC]);;

(* The per-scale far bound FAR_SCALE_SQ at the scale k = k_t + &j for a      *)
(* natural number j (so that M = 2 EXP j), with the right-hand side in the   *)
(* form D * inv(16^j) of FAR_SCALE_RHS_EQ.                                   *)
let FAR_SCALE_SQ_NAT = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (P:(int#int#int)->bool) (t:int#int#int) (y:real) R j.
       real_measurable Ff /\ FINITE P /\
       &2 zpow (--(tile_k t)) <= R / &2 /\ &0 < R /\ abs(y - tile_xmid t) <= R
       ==> sum {s | s IN P /\ tile_ler s t /\ tile_k s = tile_k t + &j}
               (\s. norm(carleson_ip
                      (\x. if x IN (Ff INTER {x | R <= abs(x - tile_xmid t)})
                           then Cx(&1) else Cx(&0)) s) pow 2)
           <= (C * (hl_maximal (\u. if u IN Ff then &1 else &0) y) pow 2 *
               inv((&2 zpow (tile_k t)) pow 5) * inv((R pow 2) pow 2)) *
              inv(&16 pow j)`,
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sc"))
    FAR_SCALE_SQ THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`;
     `y:real`; `R:real`; `j:num`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`tile_k t`; `j:num`; `C0:real`;
                `hl_maximal (\u. if u IN Ff then &1 else &0) y`;
                `R:real`] FAR_SCALE_RHS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  USE_THEN "sc" (MP_TAC o SPECL
    [`Ff:real->bool`; `P:(int#int#int)->bool`;
     `t:int#int#int`; `y:real`; `R:real`;
     `tile_k t + &j`; `&(2 EXP j):int`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [INT_ARITH_TAC;
      ASM_ARITH_TAC;
      REWRITE_TAC[INT_ARITH `(k + &j) - k:int = &j`; REAL_ZPOW_NUM;
        int_of_num_th; REAL_OF_NUM_POW]];
    ALL_TAC] THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM]);;

(* Reindex fiber identity: partitioning the tree by                          *)
(* j(s)=num_of_int(k_s-k_t).                                                 *)
let FAR_TREE_FIBER_EQ = prove
 (`!(P:(int#int#int)->bool) t jj.
     {s | (s IN P /\ tile_ler s t) /\ num_of_int(tile_k s - tile_k t) = jj} =
     {s | s IN P /\ tile_ler s t /\ tile_k s = tile_k t + &jj}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `s:int#int#int` THEN
  ASM_CASES_TAC `(s:int#int#int) IN P` THEN
    ASM_CASES_TAC `tile_ler (s:int#int#int) t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `tile_k t <= tile_k (s:int#int#int)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[TILE_LER_SCALE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= tile_k (s:int#int#int) - tile_k t` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[INT_ARITH `(k + &jj) - k:int = &jj`] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM]]);;

(* GEOM_FIBER_SUM_BOUND with ratio q = 1/16.                                 *)
let FAR_GEOM_REINDEX = prove
 (`!(A:A->bool) (nidx:A->num) (g:A->real) D.
     FINITE A /\ &0 <= D /\
     (!a. a IN A ==> &0 <= g a) /\
     (!jj. sum {a | a IN A /\ nidx a = jj} g <= D * inv(&16 pow jj))
     ==> sum A g <= D * (&16 / &15)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:A->bool`; `nidx:A->num`; `g:A->real`; `D:real`;
                 `inv(&16)`] GEOM_FIBER_SUM_BOUND) THEN
  ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The far energy of a whole tree (Grafakos-Tao-Terwilleger, Lemma 1, far    *)
(* side), for the windows W_t = {abs(x - tile_xmid t) < R}.                  *)
let FAR_TREE_ENERGY = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (P:(int#int#int)->bool) (t:int#int#int) (y:real) R.
       real_measurable Ff /\ FINITE P /\
       &2 zpow (--(tile_k t)) <= R / &2 /\ &0 < R /\ abs(y - tile_xmid t) <= R
       ==> sum {s | s IN P /\ tile_ler s t}
               (\s. norm(carleson_ip
                      (\x. if x IN (Ff INTER {x | R <= abs(x - tile_xmid t)})
                           then Cx(&1) else Cx(&0)) s) pow 2)
           <= (C * (hl_maximal (\u. if u IN Ff then &1 else &0) y) pow 2 *
               inv((&2 zpow (tile_k t)) pow 5) * inv((R pow 2) pow 2)) *
              (&16 / &15)`,
  X_CHOOSE_THEN `C0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nat"))
    FAR_SCALE_SQ_NAT THEN
  EXISTS_TAC `C0:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC
   [`Ff:real->bool`; `P:(int#int#int)->bool`;
     `t:int#int#int`; `y:real`; `R:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{s:int#int#int | s IN P /\ tile_ler s t}`;
    `\s:int#int#int. num_of_int(tile_k s - tile_k t)`;
    `\s:int#int#int. norm(carleson_ip
        (\x. if x IN (Ff INTER {x | R <= abs(x - tile_xmid t)})
             then Cx(&1) else Cx(&0)) s) pow 2`;
    `C0 * (hl_maximal (\u. if u IN Ff then &1 else &0) y) pow 2 *
     inv((&2 zpow (tile_k t)) pow 5) * inv((R pow 2) pow 2)`]
   FAR_GEOM_REINDEX) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
          MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_INV; REAL_LE_POW_2]];
      REWRITE_TAC[REAL_LE_POW_2];
      ASM_SIMP_TAC[IN_ELIM_THM; FAR_TREE_FIBER_EQ]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Windows around tree tops: W_t = {x | abs(x - tile_xmid t) < R} is an open *)
(* interval, and real_measure(Ff INTER S) = int_S 1_Ff                       *)
(* (CH_MEASURE_INTER_EQ_INT).                                                *)
(* ------------------------------------------------------------------------- *)

(* The window {x | abs(x-c)<R} is the open interval (c-R, c+R).              *)
let CH_WINDOW_EQ_INTERVAL = prove
 (`!(c:real) R. {x | abs(x - c) < R} = real_interval(c - R, c + R)`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Window-radius and budget arithmetic for the tree-energy bound of          *)
(* Grafakos-Tao-Terwilleger, Lemma 1.                                        *)
(* ------------------------------------------------------------------------- *)

(* 2^{-k} <= 2^{1-k}/2 (equality): the window-radius side-condition.         *)
let ZPOW_HALF_LE = prove
 (`!k:int. &2 zpow (-- k) <= &2 zpow (&1 - k) / &2`,
  GEN_TAC THEN
  SUBGOAL_THEN `&2 zpow (&1 - k) = &2 * &2 zpow (--k)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&1 - k:int = &1 + (--k)` SUBST1_TAC THENL
     [INT_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    REWRITE_TAC[REAL_ZPOW_1];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* 2^{1-k} = 2 * inv(2^k): the window-radius identity for the budget.        *)
let ZPOW_ONE_SUB = prove
 (`!k:int. &2 zpow (&1 - k) = &2 * inv(&2 zpow k)`,
  GEN_TAC THEN
  SUBGOAL_THEN `&1 - k:int = &1 + (--k)` SUBST1_TAC THENL
    [INT_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[REAL_ZPOW_ADD; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[REAL_ZPOW_1; REAL_ZPOW_NEG]);;

(* Ff DIFF W_t = Ff INTER {x | R <= abs(x - x_t)}, the region of             *)
(* FAR_TREE_ENERGY.                                                          *)
let CH_DIFF_WINDOW_EQ = prove
 (`!(Ff:real->bool) c R.
     Ff DIFF {x | abs(x - c) < R} = Ff INTER {x | R <= abs(x - c)}`,
  REPEAT GEN_TAC THEN
    REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  REAL_ARITH_TAC);;

(* Budget arithmetic: a*(Cg tau^2 (2 inv a) + 2 far) = 2 Cg tau^2 + (2/15)   *)
(* Cf Mv^2.                                                                  *)
let BUDGET_COLLAPSE = prove
 (`!a Cg Cf tau Mv.
     &0 < a
     ==> a * (Cg * tau pow 2 * (&2 * inv a) +
              &2 * ((Cf * Mv pow 2 * inv(a pow 5) *
                     inv(((&2 * inv a) pow 2) pow 2)) * (&16 / &15))) =
         &2 * Cg * tau pow 2 + (&2 / &15) * Cf * Mv pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a * inv a = &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Real and imaginary splitting of the bad coefficients: by CH_BADIP_DEMOD   *)
(* and CH_NORMSQ_ADD_2,                                                      *)
(*   |carleson_ip(bad_pkt,s)|^2                                              *)
(*      <= 2|int bR cnj psi_s|^2 + 2|int (ii bI) cnj psi_s|^2.               *)
(* Each integral on the right involves a single real family (bR on the       *)
(* cosine cubes, bI on the sine cubes), so the tree energy splits into two   *)
(* single-family energies.                                                   *)
(* ------------------------------------------------------------------------- *)
let CH_BADIP_REIM_SPLIT = prove
 (`!yt (bR:real->real) (bI:real->real) s.
     (\z. Cx(bR(drop z)) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (:real^1) /\
     (\z. (ii * Cx(bI(drop z))) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (:real^1)
     ==> norm(carleson_ip (\x. cexp(ii * Cx yt * Cx x) *
                               (Cx(bR x) + ii * Cx(bI x))) s) pow 2
         <= &2 * norm(integral (:real^1)
                  (\z. Cx(bR(drop z)) *
                       cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                           phi_sigma s carleson_phi (drop z)))) pow 2
          + &2 * norm(integral (:real^1)
                  (\z. (ii * Cx(bI(drop z))) *
                       cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                           phi_sigma s carleson_phi (drop z)))) pow 2`,
  ASM_SIMP_TAC[CH_BADIP_DEMOD; COMPLEX_ADD_RDISTRIB;
    INTEGRAL_ADD; CH_NORMSQ_ADD_2]);;

(* ------------------------------------------------------------------------- *)
(* Real per-cube mean zero gives complex per-cube mean zero: if bR is        *)
(* real-integrable on C with real_integral C bR = 0, then the integral of    *)
(* Cx(bR(drop z)) over IMAGE lift C is Cx 0 (CX_DROP_INTEGRAL and            *)
(* REAL_INTEGRAL).                                                           *)
(* ------------------------------------------------------------------------- *)
let CH_CX_MEANZERO_CUBE = prove
 (`!(bR:real->real) C.
     bR real_integrable_on C /\ real_integral C bR = &0
     ==> integral (IMAGE lift C) (\z. Cx(bR(drop z))) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(lift o bR o drop) integrable_on (IMAGE lift C)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRABLE_ON]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CX_DROP_INTEGRAL) THEN
  SUBGOAL_THEN
   `(\x. Cx(drop((lift o bR o drop) x))) = (\z:real^1. Cx(bR(drop z)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[o_THM; LIFT_DROP]; ALL_TAC] THEN
  UNDISCH_TAC `bR real_integrable_on C` THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP REAL_INTEGRAL th)) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[]);;

(* drop(int_(lift C) lift(norm(Cx o bR))) = real_integral C |bR|             *)
(* (COMPLEX_NORM_CX and the REAL_INTEGRAL lift bridge).                      *)
let CH_INT_NORM_CX_EQ = prove
 (`!(bR:real->real) C.
     bR absolutely_real_integrable_on C
     ==> drop(integral (IMAGE lift C) (\z. lift(norm(Cx(bR(drop z)))))) =
         real_integral C (\x. abs(bR x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real^1. lift(norm(Cx(bR(drop z))))) = (\z. lift(abs(bR(drop z))))`
   SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. abs((bR:real->real) x))
                 real_integrable_on C` ASSUME_TAC THENL
   [UNDISCH_TAC `bR absolutely_real_integrable_on C` THEN
    REWRITE_TAC[absolutely_real_integrable_on] THEN SIMP_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> MP_TAC(MATCH_MP REAL_INTEGRAL th)) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[o_DEF]);;

(* Measurability of IMAGE lift (real_interval[a,b]).                         *)
let CH_MEASURABLE_LIFT_INTERVAL = prove
 (`!a b. measurable (IMAGE lift (real_interval[a,b]))`,
  REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; MEASURABLE_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Per-(cube, tile) bound for a real family: if bR has mean zero and is      *)
(* absolutely integrable on real_interval[a,b] with real_integral |bR| <= K, *)
(* then the demodulated pairing satisfies                                    *)
(*   |int_(lift[a,b]) (Cx o bR) cnj psi_s|                                   *)
(*      <= K * (Cdiff sqrt(2^ks) (2^ks w) cw(2^ks(cc - x_s))).               *)
(* This is CH_BAD_CUBE_TILE at B = Cx o bR.                                  *)
(* ------------------------------------------------------------------------- *)
let CH_CUBE_TILE_REAL = prove
 (`?Cdiff. &0 <= Cdiff /\
    !(bR:real->real) (s:int#int#int) t (a:real) b cc w K.
        bR absolutely_real_integrable_on (real_interval[a,b]) /\
        real_integral (real_interval[a,b]) bR = &0 /\
        real_integral (real_interval[a,b]) (\x. abs(bR x)) <= K /\
        tile_ler s t /\ &2 zpow tile_k s * w <= &1 /\ &0 <= w /\ &0 <= K /\
        (!y. y IN real_interval[a,b] ==> abs(y - cc) <= w)
        ==> norm(integral (IMAGE lift (real_interval[a,b]))
                   (\z. Cx(bR(drop z)) *
                        cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z))))
            <= K * (Cdiff * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * w) *
                    cw(&2 zpow tile_k s * (cc - tile_xmid s)))`,
  X_CHOOSE_THEN `Cdiff:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bct"))
    CH_BAD_CUBE_TILE THEN
  EXISTS_TAC `Cdiff:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`bR:real->real`; `s:int#int#int`; `t:int#int#int`; `a:real`; `b:real`;
     `cc:real`; `w:real`; `K:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `drop(integral (IMAGE lift (real_interval[a,b]))
                  (\z. lift(norm(Cx(bR(drop z)))))) *
    (Cdiff * sqrt(&2 zpow tile_k s) * (&2 zpow tile_k s * w) *
     cw(&2 zpow tile_k s * (cc - tile_xmid s)))` THEN
  CONJ_TAC THENL
   [USE_THEN "bct" (fun th -> MP_TAC(BETA_RULE(SPECL
      [`\z:real^1. Cx(bR(drop z))`; `s:int#int#int`; `t:int#int#int`;
       `a:real`; `b:real`; `cc:real`; `w:real`] th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CH_MEASURABLE_LIFT_INTERVAL] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[CH_CX_DROP_ABSINT_SET];
        MATCH_MP_TAC CH_CX_MEANZERO_CUBE THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC
         `bR absolutely_real_integrable_on (real_interval[a,b])` THEN
        REWRITE_TAC[absolutely_real_integrable_on] THEN SIMP_TAC[]];
      REWRITE_TAC[]];
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_INT_NORM_CX_EQ];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
        CONJ_TAC) THEN ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_IMP_LE THEN
          MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_POS]]]]);;

(* CH_CUBE_TILE_REAL at the centre and half-width of the cube itself: for    *)
(* [a,b] with cc = (a+b)/2 and w = (b-a)/2 the geometric condition holds     *)
(* automatically and the tile condition becomes 2^ks * (b-a)/2 <= 1, i.e.    *)
(* the cube is small (|c| <= 2^{1-ks}); this is the case in which the packet *)
(* difference bound CH_PSI_DIFF_CW applies.  The bound is in terms of |c| =  *)
(* b - a.                                                                    *)
let CH_CUBE_TILE_REAL_IVL = prove
 (`?Cdiff. &0 <= Cdiff /\
    !(bR:real->real) (s:int#int#int) t (a:real) b K.
        bR absolutely_real_integrable_on (real_interval[a,b]) /\
        real_integral (real_interval[a,b]) bR = &0 /\
        real_integral (real_interval[a,b]) (\x. abs(bR x)) <= K /\
        tile_ler s t /\ a <= b /\ &2 zpow tile_k s * ((b - a) / &2) <= &1 /\
        &0 <= K
        ==> norm(integral (IMAGE lift (real_interval[a,b]))
                   (\z. Cx(bR(drop z)) *
                        cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z))))
            <= K * (Cdiff * sqrt(&2 zpow tile_k s) *
                    (&2 zpow tile_k s * ((b - a) / &2)) *
                    cw(&2 zpow tile_k s * ((a + b) / &2 - tile_xmid s)))`,
  X_CHOOSE_THEN `Cdiff:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ctr"))
    CH_CUBE_TILE_REAL THEN
  EXISTS_TAC `Cdiff:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`bR:real->real`; `s:int#int#int`; `t:int#int#int`;
      `a:real`; `b:real`; `K:real`] THEN
  STRIP_TAC THEN
  USE_THEN "ctr" (fun th -> MATCH_MP_TAC (SPECL
    [`bR:real->real`; `s:int#int#int`; `t:int#int#int`; `a:real`; `b:real`;
     `(a + b) / &2`; `(b - a) / &2`; `K:real`] th)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]);;

(* Scale-explicit pointwise bound for the demodulated packet psi_s =         *)
(* cexp(-ii yt.) phi_sigma s carleson_phi:                                   *)
(*   norm(psi_s x) <= C1 inv(sqrt 2^ks) cw_tile s x,                         *)
(* which is PHISIG_CW since the modulation is unimodular.  For large cubes,  *)
(* where the mean-zero gain is not available, it gives the size bound        *)
(* |int_{J_k} b cnj psi_s| <= (int_{J_k} |b|) * (cw tail weight).            *)
let CH_PSI_CW = prove
 (`?C1. &0 <= C1 /\ !yt (s:int#int#int) x.
     norm(cexp(--(ii * Cx yt * Cx x)) * phi_sigma s carleson_phi x)
     <= C1 * inv(sqrt(&2 zpow (tile_k s))) * cw_tile s x`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pcw"))
    PHISIG_CW THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`yt:real`; `s:int#int#int`; `x:real`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `norm(cexp(--(ii * Cx yt * Cx x))) = &1` SUBST1_TAC THENL
   [SUBGOAL_THEN `--(ii * Cx yt * Cx x) = ii * Cx(--(yt * x))` SUBST1_TAC THENL
     [REWRITE_TAC[CX_NEG; CX_MUL] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    REWRITE_TAC[NORM_CEXP_II]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_LID] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Removing repetitions from an enumeration e:num->set without changing the  *)
(* union: e2 n = if (?m. m < n /\ e m = e n) then {} else e n keeps only the *)
(* first index hitting each set, so the family becomes pairwise disjoint or  *)
(* empty, as INTEGRAL_COUNTABLE_UNIONS requires.                             *)
(* ------------------------------------------------------------------------- *)
let DEDUP_UNIONS = prove
 (`!(e:num->A->bool).
     UNIONS {(if (?m. m < n /\ e m = e n) then ({}:A->bool)
              else e n) | n IN (:num)} =
     UNIONS {e n | n IN (:num)}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
  EQ_TAC THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool`
       (CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:num` ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `x IN (e:num->A->bool) n` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?k. x IN (e:num->A->bool) k /\ (!m. m < k ==> ~(x IN e m))`
      STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM num_WOP] THEN
       EXISTS_TAC `n:num` THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `(e:num->A->bool) k` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* From the countable-union limit to a bound: if the partial sums of the     *)
(* norms of the integrals over the pieces are uniformly bounded, sum_{i<=N}  *)
(* norm(int_{s i} f) <= B for all N, then                                    *)
(*   norm(int_(UNIONS {s n}) f) <= B                                         *)
(* (LIM_NORM_UBOUND and VSUM_NORM_LE).  This lets the per-cube bounds        *)
(* control the pairing with the bad part on the whole of Om.                 *)
(* ------------------------------------------------------------------------- *)
let CH_BADPAIR_SERIES_BOUND = prove
 (`!(f:real^M->real^N) s B.
     (!n. f integrable_on (s n)) /\
     pairwise (\i j. negligible (s i INTER s j)) (:num) /\
     f absolutely_integrable_on (UNIONS {s n | n IN (:num)}) /\
     (!N. sum (0..N) (\i. norm(integral (s i) f)) <= B)
     ==> norm(integral (UNIONS {s n | n IN (:num)}) f) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\N. vsum(0..N) (\i. integral (s i) (f:real^M->real^N))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGRAL_COUNTABLE_UNIONS];
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (0..N) (\i. norm(integral (s i) (f:real^M->real^N)))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[VSUM_NORM_LE; FINITE_NUMSEG; REAL_LE_REFL];
      ASM_REWRITE_TAC[]]]);;

(* Removing repetitions does not increase the norms of the integrals over    *)
(* the pieces: the piece with index i becomes either e i itself or the empty *)
(* set, whose integral is 0.  Hence a bound on norm(integral (e i) f) for    *)
(* every i also holds for the family without repetitions.                    *)
let DEDUP_INT_NORM_LE = prove
 (`!(f:real^M->real^N) (e:num->real^M->bool) i.
     norm(integral (if (?m. m < i /\ e m = e i) then ({}:real^M->bool)
                    else e i) f)
     <= norm(integral (e i) f)`,
  ASM_MESON_TAC[REAL_LE_REFL; INTEGRAL_EMPTY; NORM_0; NORM_POS_LE]);;

(* Algebra for squaring the per-cube bound: for 0 <= sc,                     *)
(*   (K * (C * sqrt sc * m * w))^2 = (C^2 * sc) * (K^2 * (m * w)^2).         *)
let CUBE_SQ_ALG = prove
 (`!K C sc m w. &0 <= sc
     ==> (K * (C * sqrt sc * m * w)) pow 2 =
         (C pow 2 * sc) * (K pow 2 * (m * w) pow 2)`,
  ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The per-tile squared bound, from CH_CUBE_TILE_REAL_IVL and CUBE_SQ_ALG:   *)
(*   |int_{J_k} (Cx bR) cnj psi_s|^2                                         *)
(*      <= (Cd2 * 2^ks) * (K^2 * (2^ks((b-a)/2) * cw(2^ks((a+b)/2 -          *)
(*        x_s)))^2).                                                         *)
(* ------------------------------------------------------------------------- *)
let CH_CUBE_TILE_SQ = prove
 (`?Cd2. &0 <= Cd2 /\
    !(bR:real->real) (s:int#int#int) t (a:real) b K.
        bR absolutely_real_integrable_on (real_interval[a,b]) /\
        real_integral (real_interval[a,b]) bR = &0 /\
        real_integral (real_interval[a,b]) (\x. abs(bR x)) <= K /\
        tile_ler s t /\ a <= b /\ &2 zpow tile_k s * ((b - a) / &2) <= &1 /\
        &0 <= K
        ==> norm(integral (IMAGE lift (real_interval[a,b]))
                   (\z. Cx(bR(drop z)) *
                        cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2
            <= (Cd2 * &2 zpow tile_k s) *
               (K pow 2 * ((&2 zpow tile_k s * ((b - a) / &2)) *
                           cw(&2 zpow tile_k s *
                              ((a + b) / &2 - tile_xmid s))) pow 2)`,
  X_CHOOSE_THEN `Cdiff:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "iv"))
    CH_CUBE_TILE_REAL_IVL THEN
  EXISTS_TAC `(Cdiff:real) pow 2` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`bR:real->real`; `s:int#int#int`; `t:int#int#int`;
      `a:real`; `b:real`; `K:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(K * (Cdiff * sqrt(&2 zpow tile_k s) *
                    (&2 zpow tile_k s * ((b - a) / &2)) *
                    cw(&2 zpow tile_k s *
                       ((a + b) / &2 - tile_xmid s)))) pow 2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE2; NORM_POS_LE];
    MP_TAC(ISPECL
      [`K:real`; `Cdiff:real`; `&2 zpow tile_k s`;
       `&2 zpow tile_k s * ((b - a) / &2)`;
       `cw(&2 zpow tile_k s * ((a + b) / &2 - tile_xmid s))`] CUBE_SQ_ALG) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Sums over a single scale of a tree.  TILE_XMID_SCALE_S: tile_xmid s *     *)
(* 2^{tile_k s} = FST(SND s) + 1/2, i.e. x_s = (nI + 1/2) 2^{-k}.  Since the *)
(* centres x_s of the tiles of one scale are 2^{-k}-separated (distinct      *)
(* spatial indices), sums of cw over them reduce to sums over integer        *)
(* shifts.                                                                   *)
(* ------------------------------------------------------------------------- *)
let TILE_XMID_SCALE_S = prove
 (`!s:int#int#int. tile_xmid s * &2 zpow (tile_k s) =
    real_of_int(FST(SND s)) + &1 / &2`,
  REWRITE_TAC[FORALL_PAIR_THM; tile_xmid; tile_k; dyho_mid] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  SUBGOAL_THEN `&2 zpow (--p1) * &2 zpow p1 = &1` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_ZPOW_ADD_2; INT_ADD_LINV; REAL_ZPOW_0]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Decaying tail sums of cw.  The terms at offset at least m >= 1 have sum   *)
(* at most 1/(2(1+(m-1))^2) = 1/(2m^2), which decays in m.  The bounds       *)
(* follow from CW_SUM_BOUND, sum_{k=m..n} cw(k+1/2) <= 1/(2(1+m)^2):         *)
(*   CW_NUMSEG_TAIL0_SUM: sum_{i=0..P} cw((i+m)-1/2) <= 1/(2(1+(m-1))^2)     *)
(*   CW_NUMSEG_MN_TAIL:   sum_{j=m..N} cw(j-1/2)     <= 1/(2(1+(m-1))^2)     *)
(*   CW_ONESIDE_TAIL:     sum_{j in J} cw(r-j)       <= 1/(2(1+(m-1))^2)     *)
(*                        for finite J with j >= m on J and abs r <= 1/2.    *)
(* The last two are the decaying analogues of CW_NUMSEG_HALF_SUM and         *)
(* CW_ONESIDE_SUM, which are their cases m = 1.                              *)
(* ------------------------------------------------------------------------- *)
let CW_NUMSEG_TAIL0_SUM = prove
 (`!P m:num. 1 <= m
     ==> sum (0..P) (\i. cw(&(i+m) - &1 / &2)) <=
         &1 / (&2 * (&1 + &(m-1)) pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (m - 1..P + m - 1) (\k:num. cw(&k + &1 / &2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MP_TAC(ISPECL [`m - 1:num`; `\k:num. cw(&k + &1 / &2)`; `0`;
      `P:num`] SUM_OFFSET) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `i:num` THEN
      DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `i + m - 1 = (i + m) - 1` SUBST1_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= i + m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[CW_SUM_BOUND]]);;

let CW_NUMSEG_MN_TAIL = prove
 (`!N m:num. 1 <= m
     ==> sum (m..N) (\j. cw(&j - &1 / &2)) <= &1 / (&2 * (&1 + &(m-1)) pow 2)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `N < m:num` THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; REWRITE_TAC[REAL_LE_POW_2]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `\j:num. cw(&j - &1 / &2)`; `0`;
    `N - m:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `N - m + m = N:num` SUBST1_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`N - m:num`;
    `m:num`] CW_NUMSEG_TAIL0_SUM) THEN ASM_REWRITE_TAC[]);;

let CW_ONESIDE_TAIL = prove
 (`!r (J:num->bool) m. abs r <= &1 / &2 /\ 1 <= m /\ FINITE J
    /\ (!j. j IN J ==> m <= j)
     ==> sum J (\j. cw(r - &j)) <= &1 / (&2 * (&1 + &(m-1)) pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum J (\j. cw(&j - &1 / &2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN SUBGOAL_THEN `1 <= j`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
       ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CW_SHIFT_BND];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\j:num. j`; `J:num->bool`] UPPER_BOUND_FINITE_SET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (m..N) (\j. cw(&j - &1 / &2))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_SUBSET_SIMPLE; FINITE_NUMSEG; SUBSET;
     IN_NUMSEG; REAL_LT_IMP_LE; CW_POS];
    ASM_SIMP_TAC[CW_NUMSEG_MN_TAIL]]);;

(* CW_ONESIDE_TAIL_R: the right-shift (cw(r + &j)) analogue of              *)
(* CW_ONESIDE_TAIL, for the LEFT side (n < M) of the two-sided integer tail, *)
(* by the evenness of cw.                                                    *)
let CW_ONESIDE_TAIL_R = prove
 (`!r (J:num->bool) m. abs r <= &1 / &2 /\ 1 <= m /\ FINITE J
    /\ (!j. j IN J ==> m <= j)
     ==> sum J (\j. cw(r + &j)) <= &1 / (&2 * (&1 + &(m-1)) pow 2)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CW_EVEN] THEN
  REWRITE_TAC[REAL_ARITH `--(r + j) = --r - j`] THEN
  MATCH_MP_TAC CW_ONESIDE_TAIL THEN ASM_REWRITE_TAC[REAL_ABS_NEG]);;

(* The two-sided decaying integer-shift sum: for a finite set S of integers  *)
(* n with offset num_of_int(abs(n - M)) >= m from the integer M nearest to y *)
(* (abs(y - M) <= 1/2),                                                      *)
(*   sum_{n in S} cw(y - real_of_int n) <= 2 / (2(1+(m-1))^2).               *)
(* This is the decaying analogue of CW_INTEGER_SHIFT_SUM; the proof splits S *)
(* at M (SUM_INT_TRICHOTOMY) and reindexes each side (CW_ONESIDE_TAIL_R,     *)
(* CW_ONESIDE_TAIL).                                                         *)
let CW_INTEGER_SHIFT_TAIL = prove
 (`!(S:int->bool) y M m.
      FINITE S /\ 1 <= m /\ abs(y - real_of_int M) <= &1 / &2 /\
      (!n. n IN S ==> m <= num_of_int(abs(n - M)))
      ==> sum S (\n. cw(y - real_of_int n)) <=
          &2 / (&2 * (&1 + &(m-1)) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:int->bool`; `\n:int. cw(y - real_of_int n)`;
    `M:int`] SUM_INT_TRICHOTOMY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `{n:int | n IN S /\ n = M} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `n:int` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:int`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INT_SUB_REFL; INT_ABS_NUM; NUM_OF_INT_OF_NUM] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES; REAL_ADD_LID] THEN
  SUBGOAL_THEN
   `&2 / (&2 * (&1 + &(m - 1)) pow 2) =
    &1 / (&2 * (&1 + &(m - 1)) pow 2) + &1 / (&2 * (&1 + &(m - 1)) pow 2)`
   SUBST1_TAC THENL [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `sum {n:int | n IN S /\ n < M} (\n. cw(y - real_of_int n)) =
      sum (IMAGE (\n:int. num_of_int(M - n)) {n | n IN S /\ n < M})
          (\j. cw((y - real_of_int M) + &j))`
     SUBST1_TAC THENL
     [MP_TAC(ISPECL [`\n:int. num_of_int(M - n)`;
                     `\j:num. cw((y - real_of_int M) + &j)`;
                     `{n:int | n IN S /\ n < M}`] SUM_IMAGE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
         MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN
           MP_TAC(ISPEC `M - a:int` INT_OF_NUM_OF_INT) THEN
           MP_TAC(ISPEC `M - b:int` INT_OF_NUM_OF_INT) THEN
           REPEAT DISCH_TAC THEN
        SUBGOAL_THEN `M - a:int = M - b` MP_TAC THENL
         [ASM_ARITH_TAC;
          INT_ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:int` THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN `&(num_of_int(M - n)) =
                       real_of_int(M - n)` SUBST1_TAC THENL
         [MATCH_MP_TAC ROI_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[int_sub_th] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CW_ONESIDE_TAIL_R THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `n:int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:int`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs(n - M:int) = M - n` SUBST1_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[]];
    SUBGOAL_THEN
     `sum {n:int | n IN S /\ M < n} (\n. cw(y - real_of_int n)) =
      sum (IMAGE (\n:int. num_of_int(n - M)) {n | n IN S /\ M < n})
          (\j. cw((y - real_of_int M) - &j))`
     SUBST1_TAC THENL
     [MP_TAC(ISPECL [`\n:int. num_of_int(n - M)`;
                     `\j:num. cw((y - real_of_int M) - &j)`;
                     `{n:int | n IN S /\ M < n}`] SUM_IMAGE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN
         MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN
           MP_TAC(ISPEC `a - M:int` INT_OF_NUM_OF_INT) THEN
           MP_TAC(ISPEC `b - M:int` INT_OF_NUM_OF_INT) THEN
           REPEAT DISCH_TAC THEN
        SUBGOAL_THEN `a - M:int = b - M` MP_TAC THENL
         [ASM_ARITH_TAC;
          INT_ARITH_TAC];
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:int` THEN
          REWRITE_TAC[IN_ELIM_THM] THEN
        STRIP_TAC THEN AP_TERM_TAC THEN
        SUBGOAL_THEN `&(num_of_int(n - M)) =
                       real_of_int(n - M)` SUBST1_TAC THENL
         [MATCH_MP_TAC ROI_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[int_sub_th] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CW_ONESIDE_TAIL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_RESTRICT];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `n:int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:int`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `abs(n - M:int) = n - M` SUBST1_TAC THENL
       [ASM_INT_ARITH_TAC; ALL_TAC] THEN REWRITE_TAC[]]]);;

(* (a+b+c)^2 <= 3(a^2+b^2+c^2) (CH_SUMSQ3_ARITH) and its sum over tiles      *)
(* (CH_NEAR_TREE_SPLIT3), for combining the near, far and large cases of the *)
(* per-tile sums over cubes.                                                 *)
let CH_SUMSQ3_ARITH = prove
 (`!a b c:real. (a + b + c) pow 2 <= &3 * (a pow 2 + b pow 2 + c pow 2)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= (a-b) pow 2 + (a-c) pow 2 + (b-c) pow 2 /\
                           &3*(a pow 2+b pow 2+c pow 2) - (a+b+c) pow 2 =
                           (a-b) pow 2 + (a-c) pow 2 + (b-c) pow 2
                           ==> (a+b+c) pow 2 <=
                               &3*(a pow 2+b pow 2+c pow 2)`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2];
    CONV_TAC REAL_RING]);;

let CH_NEAR_TREE_SPLIT3 = prove
 (`!(Tt:(int#int#int)->bool) (a:(int#int#int)->real)
    (b:(int#int#int)->real) (c:(int#int#int)->real).
    FINITE Tt
    ==> sum Tt (\s. (a s + b s + c s) pow 2)
        <= &3 * sum Tt (\s. (a s) pow 2)
         + &3 * sum Tt (\s. (b s) pow 2)
         + &3 * sum Tt (\s. (c s) pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Tt (\s:int#int#int. &3 * ((a s) pow 2 + (b s) pow 2 +
                                            (c s) pow 2))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_LE; CH_SUMSQ3_ARITH];
    ASM_SIMP_TAC[SUM_LMUL; SUM_ADD] THEN ASM_REAL_ARITH_TAC]);;

(* Support of the complex bad packet Bc = Cx bR + ii Cx bI: if bR and bI     *)
(* both vanish off Om, then Bc(drop z) = Cx 0 off IMAGE lift Om, so the      *)
(* pairing integral over the whole line equals the integral over IMAGE lift  *)
(* Om.                                                                       *)

let CH_INT_SUPPORT_OM_CPLX = prove
 (`!(bR:real->real) (bI:real->real) (w:real^1->complex) (Om:real->bool).
     (!x. ~(x IN Om) ==> bR x = &0) /\ (!x. ~(x IN Om) ==> bI x = &0)
     ==> integral (:real^1)
           (\z. (Cx(bR(drop z)) + ii * Cx(bI(drop z))) * w z) =
         integral (IMAGE lift Om)
           (\z. (Cx(bR(drop z)) + ii * Cx(bI(drop z))) * w z)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN
  REWRITE_TAC[IN_IMAGE] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  (* off Om: bR(drop z)=bI(drop z)=0, so the packet factor = Cx 0 + ii*Cx 0  *)
  (* = 0.                                                                    *)
  SUBGOAL_THEN `bR(drop z) = &0 /\ bI(drop z) = &0` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LIFT_DROP];
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID;
      COMPLEX_VEC_0; COMPLEX_MUL_LZERO]]);;

(* The bad-pairing integrand f_s = (Cx bR + ii Cx bI) * cnj(psi_s) is        *)
(* absolutely integrable on (:real^1), where psi_s = cexp(--(ii yt .))       *)
(* phi_sigma s carleson_phi: it is the product of an absolutely integrable   *)
(* function (CH_CPLXB_ABSINT) and a bounded measurable one (CH_PSI_BOUNDED,  *)
(* CH_PSI_MEAS).                                                             *)

let CH_BADPAIR_ABSINT_UNIV = prove
 (`!yt (bR:real->real) (bI:real->real) (s:int#int#int).
     bR absolutely_real_integrable_on (:real) /\
     bI absolutely_real_integrable_on (:real)
     ==> (\z. (Cx(bR(drop z)) + ii * Cx(bI(drop z))) *
              cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                  phi_sigma s carleson_phi (drop z)))
         absolutely_integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`bR:real->real`; `bI:real->real`] CH_CPLXB_ABSINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "bc") THEN
  MP_TAC(ISPECL [`yt:real`; `s:int#int#int`] CH_PSI_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_THEN `Mb:real` (LABEL_TAC "mb")) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC
   `\z:real^1. lift(Mb * norm((Cx(bR(drop z)) + ii * Cx(bI(drop z)))))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
      ASM_SIMP_TAC[MEASURABLE_ON_CNJ; CH_PSI_MEAS]];
    ASM_SIMP_TAC[LIFT_CMUL; INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_NORM;
      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_POS_LE];
      ASM_MESON_TAC[COMPLEX_NORM_MUL]]]);;

(* Monotonicity of tree energies: if norm(ip s) <= g s for each tile, then   *)
(* sum_s norm(ip s)^2 <= sum_s (g s)^2.                                      *)
let CH_TREE_ENERGY_MONO = prove
 (`!(Tt:(int#int#int)->bool)
    (ip:(int#int#int)->complex) (g:(int#int#int)->real).
     FINITE Tt /\ (!s. s IN Tt ==> &0 <= g s) /\
     (!s. s IN Tt ==> norm(ip s) <= g s)
     ==> sum Tt (\s. norm(ip s) pow 2) <= sum Tt (\s. (g s) pow 2)`,
  ASM_SIMP_TAC[SUM_LE; REAL_POW_LE2; NORM_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Combination of the near, far and large cases for each tile: the partition *)
(* of the sum over cubes (CH_QSUM_TRICHOT, CH_QSUM_TRICHOT_TREE) and the     *)
(* bound sum_s (sum_Q A_sk)^2 <= 3(En + Ef + El) (CH_TREE_ENERGY_3CASE).     *)
(* ------------------------------------------------------------------------- *)

(* per-tile trichotomy partition of sum_{k in Q} A.                          *)
let CH_QSUM_TRICHOT = prove
 (`!(Q:num->bool) (A:num->real) (nb:num->bool) (fr:num->bool) (lg:num->bool).
     FINITE Q /\
     (!k. k IN Q ==> (nb k \/ fr k \/ lg k)) /\
     (!k. k IN Q ==> ~(nb k /\ fr k) /\ ~(nb k /\ lg k) /\ ~(fr k /\ lg k))
     ==> sum Q A = sum {k | k IN Q /\ nb k} A + sum {k | k IN Q /\ fr k} A
                   + sum {k | k IN Q /\ lg k} A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE {k:num | k IN Q /\ nb k} /\ FINITE {k:num | k IN Q /\ fr k} /\
    FINITE {k:num | k IN Q /\ lg k}` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->real`; `{k:num | k IN Q /\ fr k}`;
                 `{k:num | k IN Q /\ lg k}`] SUM_UNION) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
     NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  MP_TAC(ISPECL [`A:num->real`; `{k:num | k IN Q /\ nb k}`;
                 `{k:num | k IN Q /\ fr k} UNION {k:num | k IN Q /\ lg k}`]
                SUM_UNION) THEN
  ASM_SIMP_TAC[FINITE_UNION] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNION;
     IN_ELIM_THM; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[]);;

(* the tree-level trichotomy rewrite: sum_s (sum_Q A_sk)^2 = sum_s           *)
(* (near+far+large)^2.                                                       *)
let CH_QSUM_TRICHOT_TREE = prove
 (`!(Tt:(int#int#int)->bool) (Q:num->bool) (A:(int#int#int)->num->real)
    (nb:(int#int#int)->num->bool) (fr:(int#int#int)->num->bool)
    (lg:(int#int#int)->num->bool).
     FINITE Tt /\ FINITE Q /\
     (!s k. k IN Q ==> (nb s k \/ fr s k \/ lg s k)) /\
     (!s k. k IN Q ==> ~(nb s k /\ fr s k) /\ ~(nb s k /\ lg s k) /\
                       ~(fr s k /\ lg s k))
     ==> sum Tt (\s. (sum Q (\k. A s k)) pow 2) =
         sum Tt (\s. (sum {k | k IN Q /\ nb s k} (\k. A s k) +
                      sum {k | k IN Q /\ fr s k} (\k. A s k) +
                      sum {k | k IN Q /\ lg s k} (\k. A s k)) pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `s0:int#int#int` THEN
    MP_TAC(ISPECL [`Q:num->bool`; `\k:num. (A:(int#int#int)->num->real) s0 k`;
                 `(nb:(int#int#int)->num->bool) s0`;
                 `(fr:(int#int#int)->num->bool) s0`;
                 `(lg:(int#int#int)->num->bool) s0`] CH_QSUM_TRICHOT) THEN
  ASM_SIMP_TAC[]);;

(* whole cube-sum tree-energy <= 3(En+Ef+El), from the three per-case        *)
(* sub-energies.                                                             *)
let CH_TREE_ENERGY_3CASE = prove
 (`!(Tt:(int#int#int)->bool) (Q:num->bool) (A:(int#int#int)->num->real)
    (nb:(int#int#int)->num->bool) (fr:(int#int#int)->num->bool)
    (lg:(int#int#int)->num->bool)
    (En:real) (Ef:real) (El:real).
     FINITE Tt /\ FINITE Q /\
     (!s k. k IN Q ==> (nb s k \/ fr s k \/ lg s k)) /\
     (!s k. k IN Q ==> ~(nb s k /\ fr s k) /\ ~(nb s k /\ lg s k) /\
                       ~(fr s k /\ lg s k)) /\
     sum Tt (\s. (sum {k | k IN Q /\ nb s k} (\k. A s k)) pow 2) <= En /\
     sum Tt (\s. (sum {k | k IN Q /\ fr s k} (\k. A s k)) pow 2) <= Ef /\
     sum Tt (\s. (sum {k | k IN Q /\ lg s k} (\k. A s k)) pow 2) <= El
     ==> sum Tt (\s. (sum Q (\k. A s k)) pow 2) <=
         &3 * En + &3 * Ef + &3 * El`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tt:(int#int#int)->bool`; `Q:num->bool`;
                 `A:(int#int#int)->num->real`;
                 `nb:(int#int#int)->num->bool`; `fr:(int#int#int)->num->bool`;
                 `lg:(int#int#int)->num->bool`] CH_QSUM_TRICHOT_TREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&3 * sum Tt (\s:int#int#int.
                   (sum {k:num | k IN Q /\ nb s k}
                        (\k. (A:(int#int#int)->num->real) s k)) pow 2) +
    &3 * sum Tt (\s:int#int#int.
                   (sum {k:num | k IN Q /\ fr s k}
                        (\k. (A:(int#int#int)->num->real) s k)) pow 2) +
    &3 * sum Tt (\s:int#int#int.
                   (sum {k:num | k IN Q /\ lg s k}
                        (\k. (A:(int#int#int)->num->real) s k)) pow 2)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_NEAR_TREE_SPLIT3];
    MATCH_MP_TAC(REAL_ARITH
     `a <= En /\ b <= Ef /\ c <= El
      ==> &3 * a + &3 * b + &3 * c <= &3 * En + &3 * Ef + &3 * El`) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* From a uniform bound for the truncated energies to the limit energy: if   *)
(* Tt is finite, for each tile s the truncated sums over cubes g N s tend to *)
(* L s as N -> oo, and sum Tt (\s. (g N s) pow 2) <= M for all N, then sum   *)
(* Tt (\s. (L s) pow 2) <= M (REALLIM_SUM, REALLIM_POW, REALLIM_LE).         *)
(* ------------------------------------------------------------------------- *)

let CH_TREE_ENERGY_LIMIT = prove
 (`!(Tt:(int#int#int)->bool) (g:num->(int#int#int)->real)
    (L:(int#int#int)->real) (M:real).
     FINITE Tt /\
     (!s. s IN Tt ==> ((\N. g N s) ---> L s) sequentially) /\
     (!N. sum Tt (\s. (g N s) pow 2) <= M)
     ==> sum Tt (\s. (L s) pow 2) <= M`,
  REPEAT STRIP_TAC THEN
  (* REALLIM_LE, with the two sequences given explicitly.                    *)
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\N:num. sum Tt (\s:int#int#int. (g N s) pow 2)`; `\N:num. (M:real)`] THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; REALLIM_CONST] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REALLIM_SUM; REALLIM_POW];
    ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY]]);;

(* The energy from a per-tile bound: if norm(int_UNIV Cx(b) cnj psi_s) <= gg *)
(* s with gg >= 0 for each tile and sum_s (gg s)^2 <= D, then Ef[b] = sum_s  *)
(* norm(int_UNIV ...)^2 <= D (CH_TREE_ENERGY_MONO).                          *)
let CH_EF_FROM_PERTILE = prove
 (`!(P:(int#int#int)->bool) t (b:real->real) yt
    (gg:(int#int#int)->real) (D:real).
     FINITE {s | s IN P /\ tile_ler s t} /\
     (!s. s IN {s | s IN P /\ tile_ler s t} ==> &0 <= gg s) /\
     (!s. s IN {s | s IN P /\ tile_ler s t}
          ==> norm(integral (:real^1) (\z. Cx(b(drop z)) *
                cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                    phi_sigma s carleson_phi (drop z)))) <= gg s) /\
     sum {s | s IN P /\ tile_ler s t} (\s. (gg s) pow 2) <= D
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(integral (:real^1) (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2) <= D`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {s | s IN P /\ tile_ler s t} (\s. (gg s) pow 2)` THEN
    CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_TREE_ENERGY_MONO];
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The tree energy of the bad part of the Calderon-Zygmund decomposition,    *)
(* after Grafakos-Tao-Terwilleger: per-cube pairings of the bad pieces with  *)
(* the packets, the weighted Cauchy-Schwarz inequality, and separate         *)
(* estimates for small cubes (|J_k| <= 2|I_s|) and large cubes.              *)
(* ========================================================================= *)

(* Raw per-cube pairing bound, without a mean-zero condition (for large      *)
(* cubes):                                                                   *)
(*   norm(int_{IMAGE lift Jc} Cx b(drop.) cnj w) <= P * int_{Jc} |b| cw_tile *)
(*     s,                                                                    *)
(* given the packet bound norm(w z) <= P cw_tile s (drop z).  Unlike         *)
(* CH_CUBE_TILE_REAL this needs neither int b = 0 nor a bound on the size of *)
(* the cube: it is INTEGRAL_NORM_BOUND_INTEGRAL with the pointwise bound |b| *)
(* * |w| <= |b| P cw_tile.  The integrability of the pairing is a            *)
(* hypothesis.                                                               *)
let CH_CUBE_TILE_CW_RAW = prove
 (`!(b:real->real) (w:real^1->complex) (s:int#int#int) (Jc:real->bool)
   (P:real).
     (\z. Cx(b(drop z)) * cnj(w z)) integrable_on (IMAGE lift Jc) /\
     &0 <= P /\
     (!z. z IN (IMAGE lift Jc) ==> norm(w z) <= P * cw_tile s (drop z)) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on Jc
     ==> norm(integral (IMAGE lift Jc) (\z. Cx(b(drop z)) * cnj(w z)))
         <= P * real_integral Jc (\x. abs(b x) * cw_tile s x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (IMAGE lift Jc)
                 (\z. lift(P * (abs(b(drop z)) * cw_tile s (drop z)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      SUBGOAL_THEN
        `(\z. lift (P * (abs(b(drop z)) * cw_tile s (drop z)))) =
         lift o (\x. P * (abs(b x) * cw_tile s x)) o drop`
        SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_INTEGRABLE_ON] THEN
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
      REWRITE_TAC[LIFT_DROP; COMPLEX_NORM_MUL;
        COMPLEX_NORM_CNJ; COMPLEX_NORM_CX] THEN
      ONCE_REWRITE_TAC[REAL_ARITH
        `P * abs(bb:real) * c = abs bb * (P * c)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[]];
    SUBGOAL_THEN
      `(\z. lift (P * (abs(b(drop z)) * cw_tile s (drop z)))) =
       lift o (\x. P * (abs(b x) * cw_tile s x)) o drop`
      SUBST1_TAC THENL
      [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. P * (abs(b x) * cw_tile s x))
                   real_integrable_on Jc` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_INTEGRABLE_LMUL; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL; REAL_INTEGRAL_LMUL] THEN
    REWRITE_TAC[REAL_LE_REFL]]);;

(* Per-tile pairing with the packet factor 2^{-ks/2} extracted (CH_PSI_CW in *)
(* CH_CUBE_TILE_CW_RAW): A_sk <= C1 inv(sqrt 2^ks) int |b| cw.               *)
let CH_LARGE_PERTILE_ASK = prove
 (`!(b:real->real) (s:int#int#int) (Jc:real->bool) (yt:real) (C1:real).
     &0 <= C1 /\
     (!x. norm(cexp(--(ii * Cx yt * Cx x)) * phi_sigma s carleson_phi x)
          <= C1 * inv(sqrt(&2 zpow tile_k s)) * cw_tile s x) /\
     (\z. Cx(b(drop z)) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (IMAGE lift Jc) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on Jc
     ==> norm(integral (IMAGE lift Jc)
               (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z))))
         <= (C1 * inv(sqrt(&2 zpow tile_k s))) *
            real_integral Jc (\x. abs(b x) * cw_tile s x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`b:real->real`;
    `\z:real^1. cexp(--(ii * Cx yt * Cx(drop z))) *
                phi_sigma s carleson_phi (drop z)`;
    `s:int#int#int`; `Jc:real->bool`; `C1 * inv(sqrt(&2 zpow tile_k s))`]
   CH_CUBE_TILE_CW_RAW) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[REAL_MUL_ASSOC]];
    DISCH_THEN ACCEPT_TAC]);;

(* The far region {R <= |x - tile_xmid s|} as a union, in the form used by   *)
(* CWTILE_FARINT_INTEGRABLE and CWTILE_FARINT_DECAY.                         *)
let CH_FAR_REGION_EQ = prove
 (`!(s:int#int#int) R.
     {x | R <= abs(x - tile_xmid s)} =
     {x | x <= tile_xmid s - R} UNION {x | tile_xmid s + R <= x}`,
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

(* The Om part of the mass over the far region:                              *)
(*   int_{far} 1_Om cw_tile <= inv((2^ks)^2) inv(R^2),                       *)
(* since 1_Om cw_tile <= cw_tile and the integral of cw_tile over the far    *)
(* region is bounded by CWTILE_FARINT_DECAY.                                 *)
let CH_OM_FAR_INT = prove
 (`!(Om:real->bool) (s:int#int#int) R.
     &0 < R /\ real_measurable Om
     ==> real_integral {x | R <= abs(x - tile_xmid s)}
                       (\x. if x IN Om then cw_tile s x else &0)
         <= inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral {x | R <= abs(x - tile_xmid s)} (cw_tile s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_FCW_INTEGRABLE_LEBMEAS; FAR_REGION_MEASURABLE];
      ASM_SIMP_TAC[CWTILE_FARINT_INTEGRABLE; CH_FAR_REGION_EQ];
      ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; CW_TILE_POS]];
    ASM_MESON_TAC[CH_FAR_REGION_EQ; CWTILE_FARINT_DECAY;
      REAL_INV_MUL; REAL_POW_MUL]]);;

(* The mass of the bad part over the far region (equation (15) of            *)
(* Grafakos-Tao-Terwilleger): for |y - tile_xmid s| <= R,                    *)
(*   int_{far} |b| cw_tile                                                   *)
(*      <= (128 M(1_Ff)(y) + tau) inv((2^ks)^2) inv(R^2).                    *)
(* Since |b| <= 1_Ff + tau 1_Om, the left side is at most                    *)
(*   int_{far} 1_Ff cw_tile + tau int_{far} 1_Om cw_tile;                    *)
(* the first term is bounded by CH_FAR_INT_ANNULAR (centred at tile_xmid s,  *)
(* with delta = 0) and the second by CH_OM_FAR_INT.  The integrability of    *)
(* the function |b| cw_tile on the far region is a hypothesis.               *)
let CH_B_FAR_MASS = prove
 (`!(b:real->real) (Ff:real->bool) (Om:real->bool)
    (s:int#int#int) (y:real) (tau:real) R.
     real_measurable Ff /\ real_measurable Om /\ &0 < R /\ &0 <= tau /\
     abs(y - tile_xmid s) <= R /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on
       {x | R <= abs(x - tile_xmid s)}
     ==> real_integral {x | R <= abs(x - tile_xmid s)}
       (\x. abs(b x) * cw_tile s x)
         <= (&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau) *
            inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_integral {x | R <= abs(x - tile_xmid s)}
      (\x. if x IN Ff then cw_tile s x else &0) +
    tau * real_integral {x | R <= abs(x - tile_xmid s)}
            (\x. if x IN Om then cw_tile s x else &0)` THEN
  CONJ_TAC THENL
   [(* pointwise |b| cw <= (1_Ff + tau 1_Om) cw, integrate *)
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral {x | R <= abs(x - tile_xmid s)}
                  (\x. (if x IN Ff then cw_tile s x else &0) +
                       tau * (if x IN Om then cw_tile s x else &0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; CH_FCW_INTEGRABLE_LEBMEAS;
          FAR_REGION_MEASURABLE; REAL_INTEGRABLE_LMUL];
        X_GEN_TAC `x:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `((if x IN Ff then &1 else &0) +
                     tau * (if x IN Om then &1 else &0)) * cw_tile s x` THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LT_IMP_LE; CW_TILE_POS];
          REAL_ARITH_TAC]];
      ASM_SIMP_TAC[REAL_EQ_IMP_LE; CH_FCW_INTEGRABLE_LEBMEAS;
        FAR_REGION_MEASURABLE; REAL_INTEGRAL_ADD;
        REAL_INTEGRABLE_LMUL; REAL_INTEGRAL_LMUL]];
    (* now bound each piece: F via CH_FAR_INT_ANNULAR, Om via CH_OM_FAR_INT  *)
    REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`Ff:real->bool`; `s:int#int#int`; `tile_xmid s`;
        `y:real`; `R:real`; `&0:real`]
        CH_FAR_INT_ANNULAR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
         ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_ASSOC];
      ASM_SIMP_TAC[REAL_LE_LMUL; CH_OM_FAR_INT]]]);;

(* CH_B_CUBE_MASS: per-cube weighted mass.  For a cube Jc SUBSET the far     *)
(* region {R <= |x - tile_xmid s|} (i.e. Jc at distance >= R from the tile   *)
(* center) and |b| <= 1_Ff + tau 1_Om:                                       *)
(*   int_Jc |b| cw_tile <= (128 M(1_Ff)(y) + tau) inv((2^ks)^2) inv(R^2).    *)
(* = int_Jc |b| cw <= int_{far} |b| cw (subset + nonneg integrand) <=        *)
(* CH_B_FAR_MASS.                                                            *)
let CH_B_CUBE_MASS = prove
 (`!(b:real->real) (Ff:real->bool) (Om:real->bool) (s:int#int#int) (y:real)
    (tau:real) R (Jc:real->bool).
     real_measurable Ff /\ real_measurable Om /\ &0 < R /\ &0 <= tau /\
     abs(y - tile_xmid s) <= R /\
     Jc SUBSET {x | R <= abs(x - tile_xmid s)} /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on
       {x | R <= abs(x - tile_xmid s)}
     ==> real_integral Jc (\x. abs(b x) * cw_tile s x)
         <= (&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau) *
            inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral {x | R <= abs(x - tile_xmid s)}
                (\x. abs(b x) * cw_tile s x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_SUBSET_LE; REAL_LE_MUL; REAL_ABS_POS;
     REAL_LT_IMP_LE; CW_TILE_POS];
    MP_TAC(ISPECL [`b:real->real`; `Ff:real->bool`;
                   `Om:real->bool`; `s:int#int#int`;
                   `y:real`; `tau:real`; `R:real`] CH_B_FAR_MASS) THEN
    ASM_REWRITE_TAC[]]);;

(* The per-cube form of equation (15) of Grafakos-Tao-Terwilleger for the    *)
(* bad part: for a cube Jc far from the tile, that is                        *)
(*   Jc SUBSET {R <= |x - tile_xmid s|},                                     *)
(* we have                                                                   *)
(*   norm(carleson_ip (b 1_Jc) s)                                            *)
(*      <= C1 inv(sqrt 2^ks) (128 M(1_Ff)(y)+tau) inv(2^ks)^2 inv(R^2)       *)
(* (CH_LARGE_PERTILE_ASK for the cube, and CH_B_CUBE_MASS).                  *)
let CH_B_CUBE_IP = prove
 (`?C1. &0 <= C1 /\
    !(b:real->real) (Ff:real->bool) (Om:real->bool) (s:int#int#int)
      (yt:real) (y:real) (tau:real) R (Jc:real->bool).
     real_measurable Ff /\ real_measurable Om /\ &0 < R /\ &0 <= tau /\
     abs(y - tile_xmid s) <= R /\
     Jc SUBSET {x | R <= abs(x - tile_xmid s)} /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (\z. Cx(b(drop z)) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (IMAGE lift Jc) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on
       {x | R <= abs(x - tile_xmid s)}
     ==> norm(integral (IMAGE lift Jc)
               (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z))))
         <= (C1 * inv(sqrt(&2 zpow tile_k s))) *
            ((&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau) *
             inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2))`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "psicw"))
    CH_PSI_CW THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C1 * inv(sqrt(&2 zpow tile_k s))) *
              real_integral Jc (\x. abs(b x) * cw_tile s x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_LARGE_PERTILE_ASK];
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`b:real->real`; `Ff:real->bool`;
                     `Om:real->bool`; `s:int#int#int`;
                     `y:real`; `tau:real`; `R:real`;
                     `Jc:real->bool`] CH_B_CUBE_MASS) THEN
      ASM_REWRITE_TAC[]]]);;

(* Division-free SOS identity (REAL_RING): W(W a^2 - 2 wa a S + Q wa^2) =    *)
(* (Wa - wa S)^2 + wa^2(QW - S^2).                                           *)
let WCS_ID = prove
 (`!a wa S Q W:real.
     W * (W * a pow 2 - &2 * wa * a * S + Q * wa pow 2) =
     (W * a - wa * S) pow 2 + wa pow 2 * (Q * W - S pow 2)`,
  CONV_TAC REAL_RING);;

(* The quadratic-in-a nonnegativity: W a^2 - 2 wa a S + Q wa^2 >= 0 given    *)
(* QW>=S^2, W>=0.                                                            *)
let WCS_QUAD = prove
 (`!a wa S Q W:real.
     &0 <= W /\ &0 <= Q /\ S pow 2 <= Q * W
     ==> &0 <= W * a pow 2 - &2 * wa * a * S + Q * wa pow 2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `W = &0` THENL
   [UNDISCH_TAC `S pow 2 <= Q * W` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `S = &0` SUBST1_TAC THENL
     [SUBGOAL_THEN `S pow 2 = &0` MP_TAC THENL
       [MP_TAC(SPEC `S:real` REAL_LE_POW_2) THEN
         ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[REAL_POW_EQ_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO;
      REAL_SUB_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    SUBGOAL_THEN `&0 < W` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real`; `wa:real`; `S:real`;
      `Q:real`; `W:real`] WCS_ID) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= W * (W * a pow 2 - &2 * wa * a * S + Q * wa pow 2)`
      MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`W:real`; `&0:real`;
                   `W * a pow 2 - &2 * wa * a * S + Q * wa pow 2`]
                     REAL_LE_LCANCEL_IMP) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO]]);;

(* WCS_STEP: the per-step inequality for the weighted-CS induction.          *)
let WCS_STEP = prove
 (`!a wa S Q W:real.
     &0 < wa /\ &0 <= W /\ &0 <= Q /\ S pow 2 <= Q * W
     ==> (a + S) pow 2 <= (a pow 2 / wa + Q) * (wa + W)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real`; `wa:real`; `S:real`;
    `Q:real`; `W:real`] WCS_QUAD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* (a^2/wa+Q)(wa+W) - (a+S)^2 = (1/wa)(W a^2 - 2 wa a S + Q wa^2) + (QW -  *)
  (* S^2)                                                                    *)
  SUBGOAL_THEN
    `(a pow 2 / wa + Q) * (wa + W) - (a + S) pow 2 =
     inv wa * (W * a pow 2 - &2 * wa * a * S + Q * wa pow 2) +
     (Q * W - S pow 2)`
    (fun th -> MP_TAC th) THENL
   [MP_TAC(ISPEC `wa:real` REAL_MUL_LINV) THEN ANTS_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (a pow 2 / wa + Q) * (wa + W) - (a + S) pow 2`
    MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* WCS_SUM: the weighted Cauchy-Schwarz inequality for finite sums (cf.      *)
(* Grafakos-Tao-Terwilleger, equation (19)):                                 *)
(*   (sum s a)^2 <= (sum s (\k. a k pow 2 / w k)) * (sum s w)                *)
(* for w k > 0 on the finite set s.  The proof is by induction               *)
(* (FINITE_INDUCT_STRONG), the step being WCS_STEP with                      *)
(*   S = sum s a,   Q = sum s (\k. a k pow 2 / w k),   W = sum s w.          *)
let WCS_SUM = prove
 (`!(a:A->real) w s.
     FINITE s /\ (!k. k IN s ==> &0 < w k)
     ==> (sum s a) pow 2 <= (sum s (\k. a k pow 2 / w k)) * (sum s w)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      ASSUME_TAC ASSUME_TAC)) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (w:A->real) x` ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `!k:A. k IN s ==> &0 < w k` ASSUME_TAC THENL
     [ASM_SIMP_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sum s (w:A->real)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[SUM_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= sum s (\k. (a:A->real) k pow 2 / w k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUM_POS_LE; REAL_LE_DIV; REAL_LE_POW_2;
       REAL_LT_IMP_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `(sum s (a:A->real)) pow 2 <=
                  (sum s (\k. a k pow 2 / w k)) * (sum s w)`
     ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES] THEN
    MP_TAC(ISPECL [`(a:A->real) x`; `(w:A->real) x`; `sum s (a:A->real)`;
                   `sum s (\k. (a:A->real) k pow 2 / w k)`;
                   `sum s (w:A->real)`] WCS_STEP) THEN
    ASM_REWRITE_TAC[]]);;

(* CH_WCS_ENERGY_ABSTRACT: the tree energy by the weighted Cauchy-Schwarz    *)
(* inequality (cf. Grafakos-Tao-Terwilleger, (18)-(19)).  For each tile s,   *)
(* WCS_SUM over the cubes {k | k IN Q /\ P s k} gives                        *)
(*   (sum_k A s k)^2 <= (sum_k (A s k)^2 / w s k) * (sum_k w s k)            *)
(*                    = FA_s * FB_s.                                         *)
(* If FB_s <= WB for every tile and sum_s FA_s <= FA, then                   *)
(*   sum_s (sum_k A s k)^2 <= WB * sum_s FA_s <= WB * FA.                    *)
(* This is better than the Minkowski inequality, which leads to the sum      *)
(* sum_k C sqrt|J_k|; that sum can be arbitrarily large when there are many  *)
(* small cubes.                                                              *)
let CH_WCS_ENERGY_ABSTRACT = prove
 (`!(Q:num->bool) (Tt:(int#int#int)->bool) (A:(int#int#int)->num->real)
    (w:(int#int#int)->num->real)
    (P:(int#int#int)->num->bool) (WB:real) (FA:real).
     FINITE Q /\ FINITE Tt /\ &0 <= WB /\
     (!s k. &0 <= A s k) /\
     (!s k. s IN Tt /\ k IN Q /\ P s k ==> &0 < w s k) /\
     (!s. s IN Tt ==> sum {k | k IN Q /\ P s k} (\k. w s k) <= WB) /\
     sum Tt (\s. sum {k | k IN Q /\ P s k} (\k. (A s k) pow 2 / w s k)) <= FA
     ==> sum Tt (\s. (sum {k | k IN Q /\ P s k} (\k. A s k)) pow 2)
         <= WB * FA`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Tt (\s. WB * sum {k | k IN Q /\ P s k}
                (\k. (A:(int#int#int)->num->real) s k pow 2 / w s k))` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[SUM_LMUL; REAL_LE_LMUL]] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {k | k IN Q /\ P s k}
                (\k. (A:(int#int#int)->num->real) s k pow 2 / w s k) *
              sum {k | k IN Q /\ P (s:int#int#int) k} (\k. w s k)` THEN
  ASM_SIMP_TAC[WCS_SUM; FINITE_RESTRICT; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; REAL_LE_DIV; REAL_LE_POW_2;
    REAL_LT_IMP_LE]);;

(* The first factor of CH_WCS_ENERGY_ABSTRACT summed over the tiles, by      *)
(* exchange of summation (SUM_SUM_RESTRICT): if V s k >= 0, for each cube k  *)
(* in Q the sum of V s k over the tiles s in Tt with P s k is at most D k,   *)
(* and sum_k D k <= M, then                                                  *)
(*   sum_{s in Tt} sum_{k in Q, P s k} V s k <= M.                           *)
(* It is used with V s k = (A s k)^2 / w s k.                                *)
let FA_TOTAL_ABSTRACT = prove
 (`!(Tt:(int#int#int)->bool) (Q:num->bool) (V:(int#int#int)->num->real)
    (P:(int#int#int)->num->bool) (D:num->real) (M:real).
     FINITE Tt /\ FINITE Q /\
     (!s k. &0 <= V s k) /\
     (!k. k IN Q ==> sum {s | s IN Tt /\ P s k} (\s. V s k) <= D k) /\
     sum Q D <= M
     ==> sum Tt (\s. sum {k | k IN Q /\ P s k} (\k. V s k)) <= M`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum Tt (\s. sum {k | k IN Q /\ P s k}
                    (\k. (V:(int#int#int)->num->real) s k)) =
    sum Q (\k. sum {s | s IN Tt /\ P s k} (\s. V s k))`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_SUM_RESTRICT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum Q (D:num->real)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[]);;

(* int_{[a,b]} inv((u-xs)^2) du = inv(a-xs) - inv(b-xs) for xs < a <= b,     *)
(* with antiderivative \u. --inv(u-xs).                                      *)
let INV_SQ_INTEGRAL_SHIFT = prove
 (`!xs a b:real. xs < a /\ a <= b
     ==> ((\u. inv((u - xs) pow 2)) has_real_integral
          (inv(a - xs) - inv(b - xs)))
         (real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\u:real. --inv(u - xs)`;
    `\u:real. inv((u - xs) pow 2)`; `a:real`; `b:real`]
                REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x - xs = &0)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_REAL_INTERVAL]) THEN
       ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_DIFF_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REAL_ARITH_TAC]);;

(* Enclosing-interval integral bound: int_{[xs+h,B]} du/(u-xs)^2 = inv h -   *)
(* inv(B-xs) <= inv h (INV_SQ_INTEGRAL_SHIFT).                               *)
let FB_ENCL_INT = prove
 (`!xs h B:real. &0 < h /\ xs + h <= B
     ==> real_integral (real_interval[xs + h, B]) (\u. inv((u - xs) pow 2))
         <= inv h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`xs:real`; `xs + h:real`; `B:real`] INV_SQ_INTEGRAL_SHIFT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
  REWRITE_TAC[REAL_ARITH `((xs:real) + h) - xs = h`] THEN
  MATCH_MP_TAC(REAL_ARITH
    `&0 <= inv(B - xs) ==> inv h - inv(B - xs) <= inv h`) THEN
  MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC);;

(* INVSQ_INTEGRABLE: inv((u-xs)^2) is integrable on [a,b] when xs<a          *)
(* (continuous away from xs).                                                *)
let INVSQ_INTEGRABLE = prove
 (`!xs a b:real. xs < a ==> (\u. inv((u - xs) pow 2))
                            real_integrable_on real_interval[a,b]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
  MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_CONTINUOUS_ON_POW; REAL_CONTINUOUS_ON_SUB;
     REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST];
    X_GEN_TAC `u:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < y ==> ~(y = &0)`) THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC]);;

(* NONDEG_NOT_NEG: a nondegenerate interval [a,b] (a<b) is NOT               *)
(* real_negligible.                                                          *)
let NONDEG_NOT_NEG = prove
 (`!a b:real. a < b ==> ~(real_negligible(real_interval[a,b]))`,
  ASM_SIMP_TAC[REAL_NEGLIGIBLE_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY] THEN
    ASM_REAL_ARITH_TAC);;

(* FB_JC_INJ: the cube-map k |-> [cl k, cr k] is injective on Q, from strict *)
(* width + disjointness (two equal cubes would make their negligible         *)
(* intersection = a nondegenerate interval).                                 *)
let FB_JC_INJ = prove
 (`!(Q:num->bool) (cl:num->real) (cr:num->real).
     (!k. k IN Q ==> cl k < cr k) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[cl i, cr i] INTER
                                real_interval[cl j, cr j]))
     ==> (!i j. i IN Q /\ j IN Q /\
                (\k. real_interval[(cl:num->real) k, cr k]) i =
                (\k. real_interval[cl k, cr k]) j
                ==> i = j)`,
  ASM_MESON_TAC[INTER_IDEMPOT; NONDEG_NOT_NEG]);;

(* Near and far splitting of an integral at a ball: for g integrable on the  *)
(* closed ball [c-R,c+R] and on the open exterior {R < |x - c|}, the         *)
(* integral over the whole line is the sum (HAS_REAL_INTEGRAL_UNION).        *)
let CH_INT_SPLIT_BALL = prove
 (`!(g:real->real) (c:real) (R:real).
     g real_integrable_on real_interval[c - R, c + R] /\
     g real_integrable_on {x | R < abs(x - c)}
     ==> real_integral (:real) g =
         real_integral (real_interval[c - R, c + R]) g +
         real_integral {x | R < abs(x - c)} g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN
   `(:real) = real_interval[c - R, c + R] UNION {x | R < abs(x - c)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIV; IN_ELIM_THM;
     IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_UNION THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL];
    ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL];
    SUBGOAL_THEN `real_interval[c - R, c + R] INTER {x | R < abs(x - c)} = {}`
      SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM;
       IN_REAL_INTERVAL; NOT_IN_EMPTY] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY]]);;

(* Arithmetic for the constants in CH_CW_DENSITY_FREE_POINT.  The window has *)
(* radius R = 2 zpow(&1 - ks) = 2 * 2^{-ks}; the near part gives 2^ks * (M * *)
(* 4 * R) = 8M and the far part 128 * M * inv((2^ks)^2) * inv(R^2) = 32M,    *)
(* both via 2^ks * 2^{1-ks} = 2.                                             *)

(* Key cancellation: 2^n * 2^{1-n} = 2  (via REAL_ZPOW_ADD: n + (1-n) = 1).  *)
let ZPOW_KS_CANCEL_2 = prove
 (`!n:int. &2 zpow n * &2 zpow (&1 - n) = &2`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`&2:real`; `n:int`; `(&1 - n):int`] REAL_ZPOW_ADD) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INT_ARITH `n + (&1 - n):int = &1`; REAL_ZPOW_1]);;

(* Near constant collapse: 2^n * (M*4*2^{1-n}) = 8M.                         *)
let NEAR_CONST_COLLAPSE = prove
 (`!n:int M. &2 zpow n * (M * &4 * &2 zpow (&1 - n)) = &8 * M`,
  REPEAT GEN_TAC THEN
    MP_TAC(ISPEC `n:int` ZPOW_KS_CANCEL_2) THEN CONV_TAC REAL_RING);;

(* Far constant collapse: 128*M*inv((2^n)^2)*inv((2^{1-n})^2) = 32M.         *)
(* REAL_FIELD (nonzero powers).                                              *)
let FAR_CONST_COLLAPSE = prove
 (`!n:int M.
     &128 * M * inv((&2 zpow n) pow 2) * inv((&2 zpow (&1 - n)) pow 2) =
     &32 * M`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPEC `n:int` ZPOW_KS_CANCEL_2) THEN
  CONV_TAC REAL_FIELD);;

let INDICATOR_MUL_COND = prove
 (`!(Ff:real->bool) g x.
     (if x IN Ff then &1 else &0) * g x = (if x IN Ff then g x else &0)`,
  REAL_ARITH_TAC);;

(* The open far region {x | R < dist(x,c)} is Lebesgue measurable (the       *)
(* complement of a closed interval).                                         *)
let OPEN_FAR_REGION_MEASURABLE = prove
 (`!(c:real) R. real_lebesgue_measurable {x | R < abs(x - c)}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{x | R < abs(x - c)} =
                (:real) DIFF real_interval[c - R, c + R]` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM;
     IN_REAL_INTERVAL] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_DIFF THEN
  REWRITE_TAC[REAL_LEBESGUE_MEASURABLE_UNIV;
    REAL_LEBESGUE_MEASURABLE_INTERVAL]);;

(* The product 1_Ff * cw_tile is absolutely real-integrable on R, since      *)
(* cw_tile is continuous and bounded and the indicator is absolutely         *)
(* integrable.                                                               *)
let CH_INDCW_INTEGRABLE = prove
 (`!Ff (s:int#int#int).
     real_measurable Ff
     ==> (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
       absolutely_real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_IMP_REAL_MEASURABLE_ON; ETA_AX; CWTILE_CONTINUOUS];
    REWRITE_TAC[ETA_AX; CW_TILE_BOUNDED];
    ASM_SIMP_TAC[CH_INDICATOR_ABSINT]]);;

(* Near part: over the closed ball [xt - R, xt + R] the cw_tile-weighted     *)
(* mass of Ff is at most 2^ks * (M(1_Ff)(y) 4R) (cw_tile <= 2^ks by          *)
(* CWTILE_LE_MUJ, and the density bound CH_ANNULUS_DENSITY_CAP).             *)
let CH_NEAR_CW_DENS = prove
 (`!Ff (s:int#int#int) y R.
     real_measurable Ff /\ &0 < R /\ abs(y - tile_xmid s) <= R
     ==> real_integral (real_interval[tile_xmid s - R, tile_xmid s + R])
           (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
         <= &2 zpow (tile_k s) *
            (hl_maximal (\u. if u IN Ff then &1 else &0) y * &4 * R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
    `(\x. (if x IN Ff then &1 else &0) * cw_tile s x) real_integrable_on
     real_interval[tile_xmid s - R, tile_xmid s + R] /\
     (\x. if x IN Ff then &1 else &0) real_integrable_on
     real_interval[tile_xmid s - R, tile_xmid s + R]`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV;
     ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; CH_INDCW_INTEGRABLE;
     CH_INDICATOR_ABSINT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[tile_xmid s - R, tile_xmid s + R])
                (\x. &2 zpow (tile_k s) * (if x IN Ff then &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL];
      REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
        COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_MUL_RID;
        REAL_MUL_RZERO; REAL_LE_REFL; CWTILE_LE_MUJ]];
    SUBGOAL_THEN
      `real_integral (real_interval[tile_xmid s - R, tile_xmid s + R])
         (\x. &2 zpow (tile_k s) * (if x IN Ff then &1 else &0)) =
       &2 zpow (tile_k s) *
       real_integral (real_interval[tile_xmid s - R, tile_xmid s + R])
         (\x. if x IN Ff then &1 else &0)`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_LMUL]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; GSYM CH_MEASURE_INTER_EQ_INT;
      REAL_MEASURABLE_REAL_INTERVAL] THEN
    MP_TAC(ISPECL [`Ff:real->bool`; `tile_xmid s`;
                   `real_interval[tile_xmid s - R, tile_xmid s + R]`;
                   `y:real`; `R:real`]
           CH_ANNULUS_DENSITY_CAP) THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_REAL_INTERVAL; SUBSET_REFL]]);;

(* 1_Ff cw_tile is integrable on the open far region.                        *)
let CH_INDCW_INT_FAR = prove
 (`!Ff (s:int#int#int) (c:real) R.
     real_measurable Ff
     ==> (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
       real_integrable_on {x | R < abs(x - c)}`,
  ASM_SIMP_TAC[INDICATOR_MUL_COND; CH_FCW_INTEGRABLE_LEBMEAS;
    OPEN_FAR_REGION_MEASURABLE]);;

(* CH_CW_DENSITY_FREE_POINT: the weighted density at a free point y,         *)
(*   int_R 1_Ff cw_tile s <= 40 M(1_Ff)(y),                                  *)
(* for |y - tile_xmid s| <= R = 2 zpow(1 - ks) = 2 * 2^{-ks}, by splitting   *)
(* at the ball (CH_INT_SPLIT_BALL) into the near part (CH_NEAR_CW_DENS) and  *)
(* the far part (CH_FAR_INT_ANNULAR).                                        *)
let CH_CW_DENSITY_FREE_POINT = prove
 (`!Ff (s:int#int#int) y.
     real_measurable Ff /\ abs(y - tile_xmid s) <= &2 zpow (&1 - tile_k s)
     ==> real_integral (:real) (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
         <= &40 * hl_maximal (\u. if u IN Ff then &1 else &0) y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow (&1 - tile_k s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* split int_R = int over closed ball [c+-R] + int over open far set,  c = *)
  (* tile_xmid s, R = 2^{1-ks}                                               *)
  MP_TAC(ISPECL [`\x. (if x IN Ff then &1 else &0) * cw_tile s x`;
                 `tile_xmid s`; `&2 zpow (&1 - tile_k s)`]
                   CH_INT_SPLIT_BALL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV;
       ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; CH_INDCW_INTEGRABLE];
      ASM_SIMP_TAC[CH_INDCW_INT_FAR]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&8 * hl_maximal (\u. if u IN Ff then &1 else &0) y +
              &32 * hl_maximal (\u. if u IN Ff then &1 else &0) y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CH_NEAR_CW_DENS; NEAR_CONST_COLLAPSE];
      (* the far part: the open far region lies in the closed one, and the   *)
      (* integrand is nonnegative                                            *)
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `real_integral {x | &2 zpow (&1 - tile_k s) <= abs(x - tile_xmid s)}
                      (\x. if x IN Ff then cw_tile s x else &0)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INDICATOR_MUL_COND] THEN
        MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
          ASM_SIMP_TAC[CH_FCW_INTEGRABLE_LEBMEAS; OPEN_FAR_REGION_MEASURABLE];
          ASM_SIMP_TAC[CH_FCW_INTEGRABLE_LEBMEAS; FAR_REGION_MEASURABLE];
          ASM_MESON_TAC[REAL_LE_REFL; REAL_LT_IMP_LE; CW_TILE_POS]];
        MP_TAC(ISPECL [`Ff:real->bool`; `s:int#int#int`; `tile_xmid s`;
                       `y:real`; `&2 zpow (&1 - tile_k s)`; `&0:real`]
                      CH_FAR_INT_ANNULAR) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[FAR_CONST_COLLAPSE]]];
    REAL_ARITH_TAC]);;

(* Density bound for the bad part: int_R (abs b) cw_tile <= 40 M(1_Ff)(y) +  *)
(* tau, for the window radius 2 zpow(1 - tile_k s), the Ff part being        *)
(* bounded by CH_CW_DENSITY_FREE_POINT.                                      *)
let CH_LARGE_DENS2 = prove
 (`!(b:real->real) (Ff:real->bool) (Om:real->bool)
    (s:int#int#int) (y:real) (tau:real).
     real_measurable Ff /\ real_measurable Om /\
     abs(y - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\ &0 <= tau /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
     (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
       real_integrable_on (:real) /\
     (\x. (if x IN Om then &1 else &0) * cw_tile s x)
       real_integrable_on (:real)
     ==> real_integral (:real) (\x. abs(b x) * cw_tile s x)
         <= &40 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (:real)
                (\x. (if x IN Ff then &1 else &0) * cw_tile s x) +
              tau * real_integral (:real)
                      (\x. (if x IN Om then &1 else &0) * cw_tile s x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; GSYM REAL_INTEGRAL_ADD;
     REAL_INTEGRABLE_LMUL] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_LMUL] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((if x IN Ff then &1 else &0) +
                 tau * (if x IN Om then &1 else &0)) * cw_tile s x` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LT_IMP_LE; CW_TILE_POS];
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_CW_DENSITY_FREE_POINT];
      GEN_REWRITE_TAC (RAND_CONV) [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `real_integral (:real) (cw_tile s)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL
         [MESON_TAC[CW_TILE_FULL; HAS_REAL_INTEGRAL_INTEGRABLE];
          ASM_MESON_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_LE_REFL;
            REAL_LT_IMP_LE; CW_TILE_POS]];
        ASM_MESON_TAC[REAL_LE_REFL; REAL_INTEGRAL_UNIQUE; CW_TILE_FULL]]]]);;

(* (C1 * inv(sqrt(2^ks)))^2 = C1^2 * inv(2 zpow(tile_k s)).                  *)
let ASK_SQ_ARITH = prove
 (`!(C1:real) (s:int#int#int).
     (C1 * inv(sqrt(&2 zpow (tile_k s)))) pow 2 =
     C1 pow 2 * inv(&2 zpow (tile_k s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_MUL] THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_INV] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SQRT_POW_2 THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC);;

(* The per-tile squared bound.  The hypotheses are the packet bound (from    *)
(* CH_PSI_CW), the integrability of the pairing on lift Jc, the              *)
(* integrability of (abs b) cw on Jc, the density bound intJc <= 41 tau, and *)
(* C1 >= 0, tau >= 0.                                                        *)
let CH_LARGE_ASK_SQ = prove
 (`!(b:real->real) (s:int#int#int) (Jc:real->bool)
    (yt:real) (C1:real) (tau:real).
     &0 <= C1 /\ &0 <= tau /\
     (!x. norm(cexp(--(ii * Cx yt * Cx x)) * phi_sigma s carleson_phi x)
          <= C1 * inv(sqrt(&2 zpow tile_k s)) * cw_tile s x) /\
     (\z. Cx(b(drop z)) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (IMAGE lift Jc) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
     real_integral Jc (\x. abs(b x) * cw_tile s x) <= &41 * tau
     ==> norm(integral (IMAGE lift Jc)
               (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2
         <= (&41 * C1) pow 2 * tau pow 2 * inv(&2 zpow (tile_k s))`,
  REPEAT STRIP_TAC THEN
  (* A_sk <= (C1 inv(sqrt 2^ks)) * intJc (CH_LARGE_PERTILE_ASK)              *)
  MP_TAC(ISPECL [`b:real->real`; `s:int#int#int`;
    `Jc:real->bool`; `yt:real`; `C1:real`]
    CH_LARGE_PERTILE_ASK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* square-monotone: A_sk >= 0, A_sk <= RHS0 => A_sk^2 <= RHS0^2            *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((C1 * inv(sqrt(&2 zpow tile_k s))) * (&41 * tau)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(C1 * inv(sqrt(&2 zpow tile_k s))) *
                real_integral Jc (\x. abs(b x) * cw_tile s x)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC SQRT_POS_LE THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[ASK_SQ_ARITH; REAL_POW_MUL] THEN ASM_REAL_ARITH_TAC]);;

(* Reindexing from integer exponents to natural-number scale offsets: for a  *)
(* tile s with Kstar <= tile_k s,                                            *)
(*   inv(&2 zpow(tile_k s))                                                  *)
(*      = inv(&2 zpow Kstar) * inv(&2 pow(num_of_int(tile_k s - Kstar))).    *)
(* Thus the bound A_sk^2 <= (41 C1)^2 tau^2 inv(&2 zpow(tile_k s)) of        *)
(* CH_LARGE_PERTILE_SQ becomes A_sk^2 <= Bc_k * inv(2^nidx), with Bc_k = (41 *)
(* C1)^2 tau^2 inv(&2 zpow Kstar) and nidx = num_of_int(tile_k s - Kstar).   *)
let ZPOW_TILE_NIDX = prove
 (`!(k:int) (Kstar:int).
     Kstar <= k
     ==> inv(&2 zpow k) =
         inv(&2 zpow Kstar) * inv(&2 pow (num_of_int(k - Kstar)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&0:int) <= k - Kstar` ASSUME_TAC THENL
    [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `k:int = Kstar + &(num_of_int(k - Kstar))` ASSUME_TAC THENL
   [SUBGOAL_THEN `&(num_of_int(k - Kstar)):int = k - Kstar` SUBST1_TAC THENL
     [ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; INT_ARITH_TAC]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
    [ASSUME `k:int = Kstar + &(num_of_int(k - Kstar))`] THEN
  SUBGOAL_THEN `&2 zpow (Kstar + &(num_of_int(k - Kstar))) =
                &2 zpow Kstar * &2 zpow (&(num_of_int(k - Kstar)))`
    SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_ADD THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ZPOW_NUM; REAL_INV_MUL]);;

(* The squared per-tile bound for large cubes, A_sk^2 <= (41 C1)^2 tau^2     *)
(* inv(2^ks): CH_LARGE_ASK_SQ with the density bound int_Jc |b| cw <= int_R  *)
(* |b| cw <= 40 M(1_Ff)(ys) + tau <= 41 tau (CH_LARGE_DENS2 and M <= tau).   *)
let CH_LARGE_PERTILE_SQ = prove
 (`?C1. &0 <= C1 /\
    !(b:real->real) (Ff:real->bool) (Om:real->bool)
      (s:int#int#int) (yt:real) (ys:real) (tau:real) (Jc:real->bool).
     real_measurable Ff /\ real_measurable Om /\ &0 <= tau /\
     abs(ys - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
     hl_maximal (\u. if u IN Ff then &1 else &0) ys <= tau /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (\z. Cx(b(drop z)) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (IMAGE lift Jc) /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
     (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
     (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
       real_integrable_on (:real) /\
     (\x. (if x IN Om then &1 else &0) * cw_tile s x)
       real_integrable_on (:real) /\
     Jc SUBSET (:real)
     ==> norm(integral (IMAGE lift Jc)
               (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2
         <= (&41 * C1) pow 2 * tau pow 2 * inv(&2 zpow (tile_k s))`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pcw"))
    CH_PSI_CW THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CH_LARGE_ASK_SQ THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (:real) (\x. abs(b x) * cw_tile s x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_SUBSET_LE; REAL_LE_MUL; REAL_ABS_POS;
     REAL_LT_IMP_LE; CW_TILE_POS];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&40 * hl_maximal (\u. if u IN Ff then &1 else &0) ys + tau` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`b:real->real`; `Ff:real->bool`;
                     `Om:real->bool`; `s:int#int#int`;
                     `ys:real`; `tau:real`] CH_LARGE_DENS2) THEN
      ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC]]);;

let NIDX_EQ = prove
 (`!a b:int. !jj:num. b <= a ==> (num_of_int(a - b) = jj <=> a = b + &jj)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&(num_of_int(a - b:int)) = a - b` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_SUB_LE]; ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* The ratio-4 version of FAR_GEOM_REINDEX: for the far tree sum of a single *)
(* cube the per-scale bound decays like inv(4^j) rather than inv(16^j).      *)
let FAR_GEOM_REINDEX_Q = prove
 (`!(A:A->bool) (nidx:A->num) (g:A->real) D.
     FINITE A /\ &0 <= D /\
     (!a. a IN A ==> &0 <= g a) /\
     (!jj. sum {a | a IN A /\ nidx a = jj} g <= D * inv(&4 pow jj))
     ==> sum A g <= D * &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `D * inv(&1 - inv(&4))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC GEOM_FIBER_SUM_BOUND THEN EXISTS_TAC `nidx:A->num` THEN
    ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let ZPOW_STRICT_HALF = prove
 (`!Kc tk:int. Kc < tk ==> &2 * &2 zpow(--tk) <= inv(&2 zpow Kc)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * &2 zpow(--tk) = &2 zpow(&1 - tk)` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`&2:real`; `&1:int`; `--tk:int`] REAL_ZPOW_ADD) THEN
    REWRITE_TAC[REAL_ZPOW_1;
      INT_ARITH `&1 + --tk:int = &1 - tk`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ZPOW_NEG] THEN
    MATCH_MP_TAC ZPOW2_MONOE THEN ASM_INT_ARITH_TAC);;

let DYHO_SUBSET_CLOSED = prove
 (`!k n. dyho k n SUBSET real_interval[real_of_int n * &2 zpow k,
                                       (real_of_int n + &1) * &2 zpow k]`,
  REWRITE_TAC[dyho; SUBSET; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC);;

(* If the cube lies outside the open window of the tile, i.e. bb <= xmid -   *)
(* Is/2 \/ xmid + Is/2 <= aa (touching the boundary of the window is         *)
(* allowed), then Is/2 <= dd and cube SUBSET {dd <= |x - xmid|}.             *)
(* Disjointness of half-open dyadic cells gives exactly this condition, so   *)
(* cubes adjacent to the tile are covered (e.g. tile [0,1) and cube [-2,0),  *)
(* whose closures share the point 0).                                        *)
let CUBE_OUTSIDE_DD_SEP = prove
 (`!(xmid:real) (aa:real) (bb:real) (Is:real).
     &0 < Is /\ aa < bb /\
     (bb <= xmid - Is / &2 \/ xmid + Is / &2 <= aa)
     ==> Is / &2 <= (if xmid < aa then aa - xmid else xmid - bb) /\
         real_interval[aa,bb]
         SUBSET {x | (if xmid < aa then aa - xmid else xmid - bb) <=
                     abs(x - xmid)}`,
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC);;

(* Disjointness of dyadic cells: distinct dyadic cells that are not nested   *)
(* are disjoint; disjoint dyadic cells are separated at the level of their   *)
(* endpoints; and a dyadic cell disjoint from a tile dyho (--tk) nI lies     *)
(* outside the open window of the tile.                                      *)
let DYHO_DISJOINT = prove
 (`!k n k' n'. ~(dyho k n SUBSET dyho k' n') /\ ~(dyho k' n' SUBSET dyho k n)
               ==> DISJOINT (dyho k n) (dyho k' n')`,
  ASM_MESON_TAC[DYHO_TRICHOTOMY]);;

let DYHO_DISJOINT_ENDPOINTS = prove
 (`!kJ nJ kI nI.
     &0 < &2 zpow kJ /\ &0 < &2 zpow kI /\ DISJOINT (dyho kJ nJ) (dyho kI nI)
     ==> (real_of_int nJ + &1) * &2 zpow kJ <= real_of_int nI * &2 zpow kI \/
         (real_of_int nI + &1) * &2 zpow kI <= real_of_int nJ * &2 zpow kJ`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dyho; DISJOINT; EXTENSION; IN_INTER;
    IN_ELIM_THM; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN
  ABBREV_TAC `aJ = real_of_int nJ * &2 zpow kJ` THEN
  ABBREV_TAC `aI = real_of_int nI * &2 zpow kI` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max aJ aI`) THEN ASM_REAL_ARITH_TAC);;

let DYHO_MID_ENDPOINTS = prove
 (`!k n. dyho_mid k n - (&2 zpow k) / &2 = real_of_int n * &2 zpow k /\
         dyho_mid k n + (&2 zpow k) / &2 = (real_of_int n + &1) * &2 zpow k`,
  REWRITE_TAC[dyho_mid] THEN REAL_ARITH_TAC);;

let DYHO_TILE_OUTSIDE = prove
 (`!(kJ:int) (nJ:int) (tk:int) (nI:int).
     DISJOINT (dyho kJ nJ) (dyho (--tk) nI)
     ==> (real_of_int nJ + &1) * &2 zpow kJ <=
           dyho_mid (--tk) nI - (&2 zpow (--tk)) / &2 \/
         dyho_mid (--tk) nI + (&2 zpow (--tk)) / &2 <=
           real_of_int nJ * &2 zpow kJ`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`kJ:int`; `nJ:int`; `--tk:int`;
    `nI:int`] DYHO_DISJOINT_ENDPOINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[DYHO_MID_ENDPOINTS]);;

(* The bad pieces of the dyadic Calderon-Zygmund decomposition: for an       *)
(* interval [a,b] with a < b and integrable f, bJ = (f - avg_J f) * 1_J has  *)
(* mean zero and int_J abs(bJ) <= 2 int_J abs(f).  With the stopping density *)
(* int_J abs(f) <= 2 tau meas(J) these are the properties of the bad pieces  *)
(* needed later.                                                             *)

let REALDIV_SELF_CANCEL = prove
 (`!i d:real. ~(d = &0) ==> i - i / d * d = &0`,
  CONV_TAC REAL_FIELD);;

let CZ_BADPIECE_MEANZERO = prove
 (`!f a b. a < b /\ f real_integrable_on real_interval[a,b]
     ==> real_integral (real_interval[a,b])
           (\x. f x - real_integral (real_interval[a,b]) f / (b - a)) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b - a /\ a <= b` STRIP_ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_SUB; REAL_INTEGRABLE_CONST;
    REAL_INTEGRAL_CONST] THEN
  MATCH_MP_TAC REALDIV_SELF_CANCEL THEN ASM_REAL_ARITH_TAC);;

let CZ_BADPIECE_L1 = prove
 (`!f a b. a < b /\ f real_integrable_on real_interval[a,b] /\
           (\x. abs(f x)) real_integrable_on real_interval[a,b]
     ==> real_integral (real_interval[a,b])
           (\x. abs(f x - real_integral (real_interval[a,b]) f / (b - a)))
         <= &2 * real_integral (real_interval[a,b]) (\x. abs(f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b - a /\ a <= b` STRIP_ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `f absolutely_real_integrable_on real_interval[a,b]`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[absolutely_real_integrable_on]; ALL_TAC] THEN
  ABBREV_TAC `c = real_integral (real_interval[a,b]) f / (b - a)` THEN
  SUBGOAL_THEN `(\x. f x - c) absolutely_real_integrable_on real_interval[a,b]`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
     ABSOLUTELY_REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[a,b]) (\x. abs(f x) + abs c)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
       ABSOLUTELY_REAL_INTEGRABLE_ABS];
      MATCH_MP_TAC REAL_INTEGRABLE_ADD;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL_ADD; REAL_INTEGRABLE_CONST;
    REAL_INTEGRAL_CONST] THEN
  EXPAND_TAC "c" THEN REWRITE_TAC[REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < b - a ==> abs(b - a) = b - a`] THEN
  SUBGOAL_THEN `abs(real_integral (real_interval[a,b]) f) / (b - a) * (b - a) =
                abs(real_integral (real_interval[a,b]) f)` SUBST1_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `&0 < d ==> x / d * d = x`) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(i) <= j ==> j + abs i <= &2 * j`) THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_LE THEN ASM_REWRITE_TAC[]);;

(* Well-foundedness of the maximal-cube selection.  The stopping condition   *)
(* is avg_Q abs f > tau, i.e. tau * meas(Q) < int_Q abs f, where meas(dyho k *)
(* n) = 2 zpow k.                                                            *)
(*  - ABS_INTEGRAL_DYHO_LE_UNIV: the integral over a dyadic cell is at most  *)
(*    the integral over the whole line.                                      *)
(*  - CZ_STOPSCALE_BOUND: the stopping scales are bounded above, since       *)
(*    tau * 2^k < int_Q abs f <= int abs f; so a largest stopping scale      *)
(*    exists.                                                                *)

let ABS_INTEGRAL_DYHO_LE_UNIV = prove
 (`!f k n. (\x. abs(f x)) real_integrable_on (:real)
     ==> real_integral (dyho k n) (\x. abs(f x)) <=
         real_integral (:real) (\x. abs(f x))`,
  ASM_MESON_TAC[NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE; REAL_ABS_POS;
    REAL_INTEGRAL_SUBSET_LE; SUBSET_UNIV;
    ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; ABSINT_ON_LEBMEAS_SUBSET;
    REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE; DYHO_MEASURABLE]);;

let CZ_STOPSCALE_BOUND = prove
 (`!f tau. (\x. abs(f x)) real_integrable_on (:real) /\ &0 < tau
     ==> ?K:int. !k n.
           tau * &2 zpow k < real_integral (dyho k n) (\x. abs(f x))
           ==> k <= K`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `N = real_integral (:real) (\x. abs(f x))` THEN
  MP_TAC(SPEC `(N:real) / tau` REAL_ARCH_POW2) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  EXISTS_TAC `&m :int` THEN
  MAP_EVERY X_GEN_TAC [`k:int`; `n:int`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 zpow k < &2 zpow (&m)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `(N:real) / tau` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `tau * &2 zpow k < N` MP_TAC THENL
       [ASM_MESON_TAC[REAL_LTE_TRANS; ABS_INTEGRAL_DYHO_LE_UNIV]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_ZPOW_POW; REAL_LT_IMP_LE]]; ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH `~(&m:int < k) ==> k <= &m`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 zpow (&m) <= &2 zpow k` MP_TAC THENL
   [MATCH_MP_TAC ZPOW2_MONOE THEN ASM_INT_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Per-cube density from maximality: if the parent dyho (k+1) (n div 2) does *)
(* not stop (int_parent abs f <= tau * 2^{k+1}), then int_Q abs f <= 2 tau * *)
(* 2^k = 2 tau meas Q, since Q SUBSET parent (DYHO_PARENT).  With            *)
(* CZ_BADPIECE_L1 this gives int_Q abs(bQ) <= 4 tau meas Q.                  *)
let ABS_INTEGRAL_SUBSET_MONO = prove
 (`!f s t. (\x. abs(f x)) real_integrable_on (:real) /\ s SUBSET t /\
           real_measurable s /\ real_measurable t
     ==> real_integral s (\x. abs(f x)) <= real_integral t (\x. abs(f x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. abs(f x)) absolutely_real_integrable_on (:real)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE;
     REAL_ABS_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSINT_ON_LEBMEAS_SUBSET THEN EXISTS_TAC `(:real)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  MATCH_MP_TAC REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE THEN
    ASM_REWRITE_TAC[]);;

let CZ_MAXCUBE_DENSITY = prove
 (`!f tau k n.
     (\x. abs(f x)) real_integrable_on (:real) /\ &0 < tau /\
     real_integral (dyho (k + &1) (n div &2)) (\x. abs(f x))
       <= tau * &2 zpow (k + &1)
     ==> real_integral (dyho k n) (\x. abs(f x)) <= &2 * tau * &2 zpow k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (dyho (k + &1) (n div &2)) (\x. abs(f x))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[ABS_INTEGRAL_SUBSET_MONO; DYHO_PARENT; DYHO_MEASURABLE];
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `tau * &2 zpow (k + &1)` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 zpow (k + &1) = &2 * &2 zpow k` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`&2:real`; `k:int`; `&1:int`] REAL_ZPOW_ADD) THEN
      REWRITE_TAC[REAL_ZPOW_1] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* Per-point MAXIMAL dyadic-cube selection: for x in the dyadic stopping set *)
(* (some scale-k cell of x has avg>tau), there is a GREATEST stopping scale  *)
(* kmax(x).  Its cell is the maximal CZ cube at x; its PARENT (scale kmax+1) *)
(* does NOT stop (by maximality), so CZ_MAXCUBE_DENSITY gives the density    *)
(* bound.                                                                    *)
let CZ_MAXCUBE_SELECT = prove
 (`!f tau x.
     (\x. abs(f x)) real_integrable_on (:real) /\ &0 < tau /\
     (?k. tau * &2 zpow k <
          real_integral (dyho k (@q. x IN dyho k q)) (\x. abs(f x)))
     ==> ?kmax. tau * &2 zpow kmax
                 < real_integral (dyho kmax (@q. x IN dyho kmax q))
                                 (\x. abs(f x)) /\
                (!k. tau * &2 zpow k
                       < real_integral (dyho k (@q. x IN dyho k q))
                                       (\x. abs(f x))
                     ==> k <= kmax)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `tau:real`] CZ_STOPSCALE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `K:int`) THEN
  MP_TAC(ISPECL
   [`\k:int. tau * &2 zpow k < real_integral (dyho k (@q. x IN dyho k q))
      (\x. abs(f x))`; `K:int`]
   INT_HAS_MAX) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Disjointness of SELECTED (maximal) dyadic cubes, over an abstract `stops` *)
(* predicate.  A cube is selected if it stops AND no strictly-coarser cube   *)
(* containing it stops.  Two distinct selected cubes are DISJOINT: by        *)
(* DYHO_TRICHOTOMY they nest or are disjoint; if dyho k1 n1 SUBSET dyho k2   *)
(* n2 with k1<k2 then dyho k2 n2 is a strictly-coarser stopping container -> *)
(* contradicts (k1,n1) selected; at equal scale SUBSET forces equality       *)
(* (DYHO_SAMESCALE_SUBSET_EQ) -> contra distinctness.  Instantiate `stops k  *)
(* n := tau * &2 zpow k < real_integral (dyho k n) (\x. abs(f x))` for the   *)
(* CZ decomposition.                                                         *)
let CZ_SELECTED_DISJOINT = prove
 (`!stops k1 n1 k2 n2.
     (stops k1 n1 /\
      (!k n. k1 < k /\ dyho k1 n1 SUBSET dyho k n ==> ~stops k n)) /\
     (stops k2 n2 /\
      (!k n. k2 < k /\ dyho k2 n2 SUBSET dyho k n ==> ~stops k n)) /\
     ~(dyho k1 n1 = dyho k2 n2)
     ==> DISJOINT (dyho k1 n1) (dyho k2 n2)`,
  REPEAT GEN_TAC THEN
    MP_TAC(ISPECL [`k1:int`; `n1:int`; `k2:int`; `n2:int`]
      DYHO_TRICHOTOMY) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_CASES_TAC `k1:int < k2` THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `k1:int = k2` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`k1:int`;`n1:int`;`k2:int`;`n2:int`]
         DYHO_SUBSET_SCALE) THEN
        ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[DYHO_SAMESCALE_SUBSET_EQ]];
    ASM_CASES_TAC `k2:int < k1` THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `k2:int = k1` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`k2:int`;`n2:int`;`k1:int`;`n1:int`]
         DYHO_SUBSET_SCALE) THEN
        ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
      ASM_MESON_TAC[DYHO_SAMESCALE_SUBSET_EQ]];
    ASM_REWRITE_TAC[]]);;

(* Endpoint identities for the enumerated cubes: for scale k and index n the *)
(* cube real_interval[aa,bb] with aa = n 2^k and bb = (n+1) 2^k has aa < bb  *)
(* and width 2^k, and with Kc = --k the scale conditions 2 zpow Kc * (width  *)
(* / 2) = 1/2 <= 1 and inv(2 zpow Kc) = width hold.                          *)

let CZ_CUBE_AABB_LT = prove
 (`!k n:int. real_of_int n * &2 zpow k < (real_of_int n + &1) * &2 zpow k`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow k` MP_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Right-side sum of integrals over disjoint cubes: for cubes [cl k, cr k]   *)
(* in [xs + h, B], sum int_{[cl k, cr k]} inv((u-xs)^2) <= inv h             *)
(* (SUM_COVER_INTEGRAL_LE and FB_ENCL_INT).                                  *)
let TFULL = prove
 (`!(Q:A->bool) (cl:A->real) (cr:A->real) (xs:real) (h:real) (B:real).
     FINITE Q /\ &0 < h /\ xs + h <= B /\
     (!k. k IN Q ==> xs + h <= cl k /\ cl k < cr k /\ cr k <= B) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[cl i, cr i] INTER
                                real_interval[cl j, cr j]))
     ==> sum Q (\k. real_integral (real_interval[cl k, cr k])
                                  (\u. inv((u - xs) pow 2))) <= inv h`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[xs + h,B])
                (\u. inv((u - xs) pow 2))` THEN
  ASM_SIMP_TAC[FB_ENCL_INT] THEN MATCH_MP_TAC SUM_COVER_INTEGRAL_LE THEN
  ASM_SIMP_TAC[REAL_LE_INV; REAL_LE_POW_2; INVSQ_INTEGRABLE;
    REAL_ARITH `&0 < h ==> xs < xs + h`] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTER_IDEMPOT; NONDEG_NOT_NEG]; ALL_TAC] THEN
  X_GEN_TAC `k:A` THEN DISCH_TAC THEN
  SUBGOAL_THEN `xs + h <= (cl:A->real) k /\ cl k < cr k /\ cr k <= B`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN STRIP_TAC THEN
  CONJ_TAC THENL [MATCH_MP_TAC INVSQ_INTEGRABLE; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The squared per-tile far bound in the form Is^5/d^4 (from CH_B_CUBE_IP),  *)
(* with the algebra SQALG:                                                   *)
(*   ((C1 inv(sqrt z))(Mp inv(z^2) inv(R^2)))^2 = C1^2 Mp^2 inv(z^5)         *)
(*     inv(R^4).                                                             *)
let SQALG = prove
 (`!C1 Mp z R sqz:real.
        &0 < z /\ &0 < R /\ sqz pow 2 = z /\ &0 < sqz
        ==> ((C1 * inv(sqz)) * (Mp * inv(z pow 2) * inv(R pow 2))) pow 2
            = C1 pow 2 * Mp pow 2 * inv(z pow 5) * inv(R pow 4)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD);;

let CH_B_CUBE_IP_SQ_FORM = prove
 (`?C. &0 <= C /\
        !(b:real->real) (Ff:real->bool) (Om:real->bool) (s:int#int#int)
          (yt:real) (y:real) (tau:real) (R:real) (Jc:real->bool).
         real_measurable Ff /\ real_measurable Om /\ &0 < R /\ &0 <= tau /\
         abs(y - tile_xmid s) <= R /\
         Jc SUBSET {x | R <= abs(x - tile_xmid s)} /\
         (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                          tau * (if x IN Om then &1 else &0)) /\
         (\z. Cx(b(drop z)) *
              cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                  phi_sigma s carleson_phi (drop z)))
           integrable_on (IMAGE lift Jc) /\
         (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
         (\x. abs(b x) * cw_tile s x) real_integrable_on
           {x | R <= abs(x - tile_xmid s)}
         ==> norm(integral (IMAGE lift Jc)
                   (\z. Cx(b(drop z)) *
                        cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2
             <= C * (&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y +
                     tau) pow 2 *
                inv((&2 zpow (tile_k s)) pow 5) * inv(R pow 4)`,
      X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ip"))
        CH_B_CUBE_IP THEN
      EXISTS_TAC `(C1:real) pow 2` THEN CONJ_TAC THENL
        [REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `((C1 * inv(sqrt(&2 zpow tile_k s))) *
         ((&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau) *
          inv((&2 zpow (tile_k s)) pow 2) * inv(R pow 2))) pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        USE_THEN "ip" (fun th -> MATCH_MP_TAC(SPECL
          [`b:real->real`;`Ff:real->bool`;`Om:real->bool`;
           `s:int#int#int`;`yt:real`;`y:real`;
           `tau:real`;`R:real`;`Jc:real->bool`] th)) THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `&0 < &2 zpow (tile_k s)` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(SPECL
         [`C1:real`;
          `&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau`;
          `&2 zpow (tile_k s)`; `R:real`; `sqrt(&2 zpow tile_k s)`]
         SQALG) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
            ASM_SIMP_TAC[SQRT_POS_LT]];
          REAL_ARITH_TAC]]);;

(* Tile geometry for the sums over positions.                                *)

(* EF_CLOSED_NEGL: two closed intervals with b1 <= a2 (disjoint interiors)   *)
(* meet in at most {a2} = negligible.                                        *)
let EF_CLOSED_NEGL = prove
 (`!a1 b1 a2 b2:real. b1 <= a2
     ==> real_negligible(real_interval[a1,b1] INTER real_interval[a2,b2])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{a2:real}` THEN REWRITE_TAC[REAL_NEGLIGIBLE_SING; SUBSET;
    IN_INTER; IN_REAL_INTERVAL; IN_SING] THEN
  ASM_REAL_ARITH_TAC);;

(* EF_ABS_INT_GE1: a nonzero integer has real-absolute-value >= 1 (int->real *)
(* bridge).                                                                  *)
let EF_ABS_INT_GE1 = prove
 (`!n:int. ~(n = &0) ==> &1 <= abs(real_of_int n)`,
  ASM_ARITH_TAC);;

(* EF_XMID_SEP: distinct same-scale tiles have centers >= Is apart (Is = 2   *)
(* zpow(-tile_k)).                                                           *)
let EF_XMID_SEP = prove
 (`!(s1:int#int#int) (s2:int#int#int).
     tile_k s1 = tile_k s2 /\ ~(FST(SND s1) = FST(SND s2))
     ==> &2 zpow(--(tile_k s1)) <= abs(tile_xmid s1 - tile_xmid s2)`,
  REWRITE_TAC[FORALL_PAIR_THM; tile_k; tile_xmid; dyho_mid] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `z = &2 zpow(--p1'')` THEN
  SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL
   [EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(real_of_int p1' + &1 / &2) * z - (real_of_int p1''' + &1 / &2) * z =
    (real_of_int p1' - real_of_int p1''') * z`
   SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs z = z` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
  REWRITE_TAC[GSYM int_sub_th] THEN MATCH_MP_TAC EF_ABS_INT_GE1 THEN
  ASM_REWRITE_TAC[INT_SUB_0]);;

(* EF_TILE_CELLS_NEGL2: for distinct tiles of the same scale the cells [xmid *)
(* - Is/2, xmid - Is/2 + Is] (Is = 2 zpow(-k)) have negligible intersection. *)
let EF_TILE_CELLS_NEGL2 = prove
 (`!(i:int#int#int) (j:int#int#int) (k:int) (Is:real).
     Is = &2 zpow(--k) /\ tile_k i = k /\ tile_k j = k /\
     ~(FST(SND i) = FST(SND j))
     ==> real_negligible(real_interval[tile_xmid i - Is / &2,
                                       tile_xmid i - Is / &2 + Is] INTER
                         real_interval[tile_xmid j - Is / &2,
                                       tile_xmid j - Is / &2 + Is])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`i:int#int#int`; `j:int#int#int`] EF_XMID_SEP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  DISJ_CASES_TAC (REAL_ARITH
    `tile_xmid(i:int#int#int) <= tile_xmid(j:int#int#int) \/
     tile_xmid j <= tile_xmid i`) THENL
   [MATCH_MP_TAC EF_CLOSED_NEGL THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[INTER_COMM] THEN
      MATCH_MP_TAC EF_CLOSED_NEGL THEN ASM_REAL_ARITH_TAC]);;

(* EF_DENSITY_SQ: for 0 <= M <= tau,                                         *)
(*   (128 M + tau)^2 <= (129 tau)^2 = 16641 tau^2.                           *)
let EF_DENSITY_SQ = prove
 (`!M tau. &0 <= M /\ &0 <= tau /\ M <= tau
     ==> (&128 * M + tau) pow 2 <= &16641 * tau pow 2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&129 * tau) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* CH_EF_FA_TOTAL_COND: FA_TOTAL_ABSTRACT for the summand                    *)
(*   V s k = (A s k)^2 / w s k.                                              *)
(* This summand is nonnegative whenever w s k >= 0 (also when w s k = 0, as  *)
(* x / 0 = 0), so only 0 <= w is needed, not 0 < w.                          *)
let CH_EF_FA_TOTAL_COND = prove
 (`!(Q:num->bool) (Tt:(int#int#int)->bool) (A:(int#int#int)->num->real)
    (w:(int#int#int)->num->real)
    (P:(int#int#int)->num->bool) (D:num->real) (FA:real).
     FINITE Q /\ FINITE Tt /\ (!s k. &0 <= w s k) /\
     (!k. k IN Q ==> sum {s | s IN Tt /\ P s k} (\s. (A s k) pow 2 / w s k)
                     <= D k) /\
     sum Q D <= FA
     ==> sum Tt (\s. sum {k | k IN Q /\ P s k} (\k. (A s k) pow 2 / w s k))
         <= FA`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FA_TOTAL_ABSTRACT THEN EXISTS_TAC `D:num->real` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:int#int#int`; `k:num`] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_SIMP_TAC[]);;

(* CH_EF_ASSEMBLE_COND: the weighted Cauchy-Schwarz assembly with            *)
(* conditional positivity of the weights: the weight need only be > 0 for    *)
(* s IN Tt, k IN Q and P s k, and >= 0 everywhere, which is what a geometric *)
(* weight (bb-aa)/Is (Is/dd)^2 provides (dd > 0 only on the far region, and  *)
(* for the large cubes only on the tree, where cube and tile are separated). *)
let CH_EF_ASSEMBLE_COND = prove
 (`!(Q:num->bool) (Tt:(int#int#int)->bool) (A:(int#int#int)->num->real)
    (w:(int#int#int)->num->real) (P:(int#int#int)->num->bool)
    (D:num->real) (WB:real) (FA:real).
     FINITE Q /\ FINITE Tt /\ &0 <= WB /\
     (!s k. &0 <= A s k) /\ (!s k. &0 <= w s k) /\
     (!s k. s IN Tt /\ k IN Q /\ P s k ==> &0 < w s k) /\
     (!s. s IN Tt ==> sum {k | k IN Q /\ P s k} (\k. w s k) <= WB) /\
     (!k. k IN Q ==> sum {s | s IN Tt /\ P s k} (\s. (A s k) pow 2 / w s k)
                     <= D k) /\
     sum Q D <= FA
     ==> sum Tt (\s. (sum {k | k IN Q /\ P s k} (\k. A s k)) pow 2)
         <= WB * FA`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:num->bool`; `Tt:(int#int#int)->bool`;
                 `A:(int#int#int)->num->real`; `w:(int#int#int)->num->real`;
                 `P:(int#int#int)->num->bool`; `WB:real`; `FA:real`]
    CH_WCS_ENERGY_ABSTRACT) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(ISPECL [`Q:num->bool`; `Tt:(int#int#int)->bool`;
                 `A:(int#int#int)->num->real`; `w:(int#int#int)->num->real`;
                 `P:(int#int#int)->num->bool`; `D:num->real`; `FA:real`]
    CH_EF_FA_TOTAL_COND) THEN ASM_REWRITE_TAC[]);;

(* The per-tile squared bound for large cubes, keeping the distance: with R  *)
(* the distance from the tile to the near edge of the cube,                  *)
(*   norm(int_Jc)^2 <= C tau^2 inv((2 zpow tk)^5) inv(R^4),  C = 16641 Cb.   *)
(* This has the same shape Is^5/d^4 as the far bound but holds for wide      *)
(* cubes as well.                                                            *)
let EST15_TILE_SQ_DIST = prove
 (`?C. &0 <= C /\
    !(b:real->real) (Ff:real->bool) (Om:real->bool) (s:int#int#int)
      (yt:real) (y:real) (tau:real) (R:real) (Jc:real->bool).
        real_measurable Ff /\ real_measurable Om /\ &0 < R /\ &0 <= tau /\
        abs(y - tile_xmid s) <= R /\
        Jc SUBSET {x | R <= abs(x - tile_xmid s)} /\
        &0 <= hl_maximal (\u. if u IN Ff then &1 else &0) y /\
        hl_maximal (\u. if u IN Ff then &1 else &0) y <= tau /\
        (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                         tau * (if x IN Om then &1 else &0)) /\
        (\z. Cx(b(drop z)) *
             cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                 phi_sigma s carleson_phi (drop z)))
          integrable_on (IMAGE lift Jc) /\
        (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
        (\x. abs(b x) * cw_tile s x) real_integrable_on
          {x | R <= abs(x - tile_xmid s)}
        ==> norm(integral (IMAGE lift Jc)
                   (\z. Cx(b(drop z)) *
                        cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2
            <= C * tau pow 2 * inv((&2 zpow (tile_k s)) pow 5) * inv(R pow 4)`,
  X_CHOOSE_THEN `Cb:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ipsq"))
    CH_B_CUBE_IP_SQ_FORM THEN
  EXISTS_TAC `&16641 * Cb` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `Cb * (&128 * hl_maximal (\u. if u IN Ff then &1 else &0) y + tau) pow 2 *
    inv((&2 zpow (tile_k s)) pow 5) * inv(R pow 4)` THEN
  CONJ_TAC THENL
   [USE_THEN "ipsq" (fun th -> MATCH_MP_TAC(SPECL
      [`b:real->real`; `Ff:real->bool`; `Om:real->bool`;
       `s:int#int#int`; `yt:real`; `y:real`;
       `tau:real`; `R:real`; `Jc:real->bool`] th)) THEN ASM_REWRITE_TAC[];
    (* (128M+tau)^2<=16641 tau^2, then rearrange constants                   *)
    SUBGOAL_THEN `&0 <= inv((&2 zpow (tile_k s)) pow 5) * inv(R pow 4)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
       REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_POW_LE THEN
      TRY(MATCH_MP_TAC REAL_LT_IMP_LE THEN
        MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC) THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH
      `Cb * A * iv <= (&16641 * Cb) * tau pow 2 * iv <=>
       (Cb * iv) * A <= (Cb * iv) * &16641 * tau pow 2`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
    MATCH_MP_TAC EF_DENSITY_SQ THEN ASM_REWRITE_TAC[]]);;

(* Factor B for large cubes.  The weight is (Is/dd)^2, without a width       *)
(* factor.  Each cube satisfies the telescoping domination (Is/dd)^2 <=      *)
(* (5/2) Is (inv dd - inv(dd+w)); summed over disjoint wide cubes on one     *)
(* side, the right-hand side telescopes to at most (5/2) Is inv(Is/2) = 5.   *)

let INV_DIFF_ID = prove
 (`!d w:real. ~(d = &0) /\ ~(d + w = &0)
              ==> inv d - inv(d + w) = w / (d * (d + w))`,
  CONV_TAC REAL_FIELD);;

(* EST15_FB_PERCUBE_R: per-cube domination (right side).  d = near-edge dist *)
(* (>=Is/2), w = width (>=2Is).                                              *)
let EST15_FB_PERCUBE_R = prove
 (`!Is d w:real. &0 < Is /\ Is / &2 <= d /\ &2 * Is <= w
     ==> (Is / d) pow 2 <= (&5 / &2) * Is * (inv d - inv(d + w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < d /\ &0 < w /\ &0 < d + w` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(d + w = &0)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[INV_DIFF_ID] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  SUBGOAL_THEN
   `(&5 / &2 * Is * (w / (d * (d + w)))) * d pow 2 =
    (&5 / &2 * Is * w * d) / (d + w)`
   SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= Is * d * (w / &2 - Is) + Is * w * (&2 * d - Is)`
    MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* EST15_FB_PERCUBE_INT: per-cube domination in integral form (Is/(cl-xs))^2 *)
(* <= (5/2)Is int_{J_k} invsq. Combines EST15_FB_PERCUBE_R +                 *)
(* INV_SQ_INTEGRAL_SHIFT (int_{[cl,cr]} inv((u-xs)^2) =                      *)
(* inv(cl-xs)-inv(cr-xs)).                                                   *)
let EST15_FB_PERCUBE_INT = prove
 (`!Is xs cl cr:real.
     &0 < Is /\ xs + Is / &2 <= cl /\ cl < cr /\ &2 * Is <= cr - cl
     ==> (Is / (cl - xs)) pow 2 <=
         (&5 / &2) * Is * real_integral (real_interval[cl,cr])
                                        (\u. inv((u - xs) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_integral (real_interval[cl,cr]) (\u. inv((u - xs) pow 2)) =
    inv(cl - xs) - inv(cr - xs)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
     MATCH_MP_TAC INV_SQ_INTEGRAL_SHIFT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`Is:real`; `cl - xs:real`;
    `cr - cl:real`] EST15_FB_PERCUBE_R) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* Summing per-cell bounds: if g k <= c Is f k for k in Q, where c >= 0 and  *)
(* sum f <= inv(Is/2), then sum g <= d for every d >= 2 c.                   *)
let EST15_SUM_HALF_INV_BOUND = prove
 (`!(Q:A->bool) (g:A->real) (f:A->real) c d Is.
     FINITE Q /\ &0 < Is /\ &0 <= c /\ &2 * c <= d /\
     (!k. k IN Q ==> g k <= c * Is * f k) /\ sum Q f <= inv(Is / &2)
     ==> sum Q g <= d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Q (\k. c * Is * (f:A->real) k)` THEN
  ASM_SIMP_TAC[SUM_LE; SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * Is * inv(Is / &2)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE; REAL_INV_DIV; REAL_DIV_LMUL;
    REAL_LT_IMP_NZ] THEN
  ASM_REAL_ARITH_TAC);;

(* Right-side factor B for large cubes: for disjoint wide cubes [cl k, cr k] *)
(* to the right of xs (cl k >= xs + Is/2, cr k - cl k >= 2 Is), sum (Is/(cl  *)
(* k - xs))^2 <= 5 (EST15_FB_PERCUBE_INT and TFULL).                         *)
let EST15_FB_SUM_R = prove
 (`!(Q:A->bool) (cl:A->real) (cr:A->real) (xs:real) (Is:real) (B:real).
     FINITE Q /\ &0 < Is /\ xs + Is / &2 <= B /\
     (!k. k IN Q ==> xs + Is / &2 <= cl k /\ cl k < cr k /\ cr k <= B /\
                     &2 * Is <= cr k - cl k) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[cl i, cr i] INTER
                                real_interval[cl j, cr j]))
     ==> sum Q (\k. (Is / (cl k - xs)) pow 2) <= &5`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EST15_SUM_HALF_INV_BOUND THEN
  MAP_EVERY EXISTS_TAC
   [`\k. real_integral (real_interval[(cl:A->real) k, cr k])
           (\u. inv((u - xs) pow 2))`; `&5 / &2`; `Is:real`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[EST15_FB_PERCUBE_INT] THEN
  MATCH_MP_TAC TFULL THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[REAL_HALF]);;

(* The cubes to the left of xs are handled by reflection: the intersection   *)
(* of two closed intervals is negligible iff it has empty interior, which is *)
(* invariant under x |-> --x.                                                *)
let REAL_NEGLIGIBLE_INTER_REAL_INTERVAL = prove
 (`!a b c d. real_negligible(real_interval[a,b] INTER real_interval[c,d]) <=>
             min b d <= max a c`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `real_interval[a,b] INTER real_interval[c,d] =
                real_interval[max a c,min b d]` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_REAL_INTERVAL] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_NEGLIGIBLE_REAL_INTERVAL; REAL_INTERVAL_EQ_EMPTY]]);;

(* Left-side factor B for large cubes: EST15_FB_SUM_R for the reflected      *)
(* cubes [--cr k, --cl k] and the point --xs.                                *)
let EST15_FB_SUM_L = prove
 (`!(Q:A->bool) (cl:A->real) (cr:A->real) (xs:real) (Is:real) (A:real).
     FINITE Q /\ &0 < Is /\ A <= xs - Is / &2 /\
     (!k. k IN Q ==> A <= cl k /\ cl k < cr k /\ cr k <= xs - Is / &2 /\
                     &2 * Is <= cr k - cl k) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[cl i, cr i] INTER
                                real_interval[cl j, cr j]))
     ==> sum Q (\k. (Is / (xs - cr k)) pow 2) <= &5`,
  REWRITE_TAC[REAL_NEGLIGIBLE_INTER_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:A->bool`; `\k. --((cr:A->real) k)`;
                 `\k. --((cl:A->real) k)`; `--xs:real`; `Is:real`; `--A:real`]
         EST15_FB_SUM_R) THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_INTER_REAL_INTERVAL;
              REAL_ARITH `--c - --x:real = x - c`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:A) IN Q`)) THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `j:A`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The cube-condition converters EST15_RCONV and EST15_LCONV, and            *)
(* EST15_FACTORB_PERTILE: the two-sided per-tile factor B for large cubes,   *)
(* with weight (Is/dd)^2 and constant 10, splitting the cubes into those to  *)
(* the right of xs (EST15_FB_SUM_R) and those to the left (EST15_FB_SUM_L).  *)
let EST15_RCONV = prove
 (`!aa bb xs Is Bd:real.
     aa < bb /\ bb <= Bd /\ &2 * Is <= bb - aa /\
     (xs + Is / &2 <= aa \/ bb <= xs - Is / &2) /\ xs < aa /\ &0 < Is
     ==> xs + Is / &2 <= aa /\ aa < bb /\ bb <= Bd /\ &2 * Is <= bb - aa`,
  REAL_ARITH_TAC);;

let EST15_LCONV = prove
 (`!aa bb xs Is Ad:real.
     aa < bb /\ Ad <= aa /\ &2 * Is <= bb - aa /\
     (xs + Is / &2 <= aa \/ bb <= xs - Is / &2) /\ ~(xs < aa) /\ &0 < Is
     ==> Ad <= aa /\ aa < bb /\ bb <= xs - Is / &2 /\ &2 * Is <= bb - aa`,
  REAL_ARITH_TAC);;

let EST15_FACTORB_PERTILE = prove
 (`!(Qf:num->bool) (aa:num->real) (bb:num->real) (xs:real)
    (Is:real) (Ad:real) (Bd:real).
     FINITE Qf /\ &0 < Is /\ Ad <= xs - Is / &2 /\ xs + Is / &2 <= Bd /\
     (!k. k IN Qf ==> aa k < bb k /\ Ad <= aa k /\ bb k <= Bd /\
                      &2 * Is <= bb k - aa k /\
                      (xs + Is / &2 <= aa k \/ bb k <= xs - Is / &2)) /\
     (!i j. i IN Qf /\ j IN Qf /\ ~(i = j)
            ==> real_negligible (real_interval[aa i, bb i] INTER
                                 real_interval[aa j, bb j]))
     ==> sum Qf (\k. (Is / (if xs < aa k then aa k - xs
                            else xs - bb k)) pow 2) <= &10`,
  MAP_EVERY X_GEN_TAC
    [`Qf:num->bool`;`aa:num->real`;`bb:num->real`;`xs:real`;`Is:real`;
    `Ad:real`;`Bd:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "cube") (LABEL_TAC "disj")))))) THEN
  SUBGOAL_THEN `Qf = {k:num | k IN Qf /\ xs < aa k} UNION
                     {k:num | k IN Qf /\ ~(xs < aa k)}`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
     MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {k:num | k IN Qf /\ xs < aa k} /\
    FINITE {k:num | k IN Qf /\ ~(xs < aa k)} /\
    DISJOINT {k:num | k IN Qf /\ xs < aa k} {k:num | k IN Qf /\ ~(xs < aa k)}`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
     NOT_IN_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&5 + &5` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`{k:num | k IN Qf /\ xs < aa k}`;
                     `aa:num->real`; `bb:num->real`;
                     `xs:real`; `Is:real`; `Bd:real`] EST15_FB_SUM_R) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
          SUBGOAL_THEN
           `(aa:num->real) k < bb k /\ bb k <= (Bd:real) /\
            &2 * (Is:real) <= bb k - aa k /\
            (xs + Is / &2 <= aa k \/ bb k <= xs - Is / &2) /\
            xs < aa k /\ &0 < Is`
           (fun th -> MATCH_ACCEPT_TAC (MATCH_MP EST15_RCONV th)) THEN
          USE_THEN "cube" (fun th -> MP_TAC(MATCH_MP th
            (ASSUME `(k:num) IN Qf`))) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[IN_ELIM_THM]];
        REWRITE_TAC[]];
      MP_TAC(ISPECL [`{k:num | k IN Qf /\ ~(xs < aa k)}`;
                     `aa:num->real`; `bb:num->real`;
                     `xs:real`; `Is:real`; `Ad:real`] EST15_FB_SUM_L) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
          SUBGOAL_THEN
           `(aa:num->real) k < bb k /\ (Ad:real) <= aa k /\
            &2 * (Is:real) <= bb k - aa k /\
            (xs + Is / &2 <= aa k \/ bb k <= xs - Is / &2) /\
            ~(xs < aa k) /\ &0 < Is`
           (fun th -> MATCH_ACCEPT_TAC (MATCH_MP EST15_LCONV th)) THEN
          USE_THEN "cube" (fun th -> MP_TAC(MATCH_MP th
            (ASSUME `(k:num) IN Qf`))) THEN
          STRIP_TAC THEN ASM_REWRITE_TAC[];
          ASM_SIMP_TAC[IN_ELIM_THM]];
        REWRITE_TAC[]]];
    REAL_ARITH_TAC]);;

(* EST15_FA_REINDEX: GEOM_FIBER_SUM_BOUND with ratio q = 1/2.                *)
let EST15_FA_REINDEX = prove
 (`!(A:A->bool) (nidx:A->num) (g:A->real) D.
     FINITE A /\ &0 <= D /\
     (!a. a IN A ==> &0 <= g a) /\
     (!jj. sum {a | a IN A /\ nidx a = jj} g <= D * inv(&2 pow jj))
     ==> sum A g <= D * &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:A->bool`; `nidx:A->num`; `g:A->real`; `D:real`;
                 `inv(&2)`] GEOM_FIBER_SUM_BOUND) THEN
  ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Factor A for large cubes: sums over tile cells in all positions.  The     *)
(* large class tile_k s > Kc k includes the tiles adjacent to the cube (dd = *)
(* Is/2).  These telescoping sums bound sum inv(dd^2) over disjoint tile     *)
(* cells of width Is with near-edge distance dd >= Is/2 by 6/Is^2 on each    *)
(* side.                                                                     *)

(* EST15_TILE_PERCUBE_R: the per-tile telescoping bound (right side, all     *)
(* positions, adjacent tiles included).  With D >= Is/2 the distance from    *)
(* the centre to the cube edge,                                              *)
(*   (Is/D)^2 <= 3 Is (inv D - inv(D + Is)),                                 *)
(* which holds since 1 + Is/D <= 3.                                          *)
let EST15_TILE_PERCUBE_R = prove
 (`!Is D:real. &0 < Is /\ Is / &2 <= D
     ==> (Is / D) pow 2 <= &3 * Is * (inv D - inv(D + Is))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < D /\ &0 < D + Is` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(D = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(D + Is = &0)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[INV_DIFF_ID] THEN
  REWRITE_TAC[REAL_POW_DIV] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
  SUBGOAL_THEN
   `(&3 * Is * (Is / (D * (D + Is)))) * D pow 2 =
    (&3 * Is * Is * D) / (D + Is)`
   SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= Is * Is * (&2 * D - Is)` MP_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* EST15_TILE_PERCUBE_INT: right per-tile integral form (comparison point    *)
(* xs, cell [cl,cr] width Is).                                               *)
let EST15_TILE_PERCUBE_INT = prove
 (`!Is xs cl cr:real. &0 < Is /\ xs + Is / &2 <= cl /\ cl < cr /\ cr - cl = Is
     ==> (Is / (cl - xs)) pow 2 <=
         &3 * Is * real_integral (real_interval[cl,cr])
                                 (\u. inv((u - xs) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_integral (real_interval[cl,cr]) (\u. inv((u - xs) pow 2)) =
    inv(cl - xs) - inv(cr - xs)` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
     MATCH_MP_TAC INV_SQ_INTEGRAL_SHIFT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cr:real) - xs = (cl - xs) + Is` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`Is:real`; `cl - xs:real`] EST15_TILE_PERCUBE_R) THEN
  ASM_SIMP_TAC[REAL_ARITH `Is / &2 <= cl - xs <=> xs + Is / &2 <= cl`]);;

(* EST15_TILE_POSSUM_R: the sum over positions to the right of xs, adjacent  *)
(* cells included.  If the cells [cl k, cr k] of width Is have pairwise      *)
(* negligible intersections and satisfy xs + Is/2 <= cl k, then              *)
(*   sum_k (Is/(cl k - xs))^2 <= 6.                                          *)
(* Each term is bounded by EST15_TILE_PERCUBE_INT, and the sum of the        *)
(* integrals of inv((u - xs)^2) over the cells by TFULL.                     *)
let EST15_TILE_POSSUM_R = prove
 (`!(Q:A->bool) (cl:A->real) (cr:A->real) (xs:real) (Is:real) (B:real).
     FINITE Q /\ &0 < Is /\ xs + Is / &2 <= B /\
     (!k. k IN Q ==> xs + Is / &2 <= cl k /\ cl k < cr k /\ cr k <=
       B /\ cr k - cl k = Is) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[cl i, cr i] INTER
                                real_interval[cl j, cr j]))
     ==> sum Q (\k. (Is / (cl k - xs)) pow 2) <= &6`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EST15_SUM_HALF_INV_BOUND THEN
  MAP_EVERY EXISTS_TAC
   [`\k. real_integral (real_interval[(cl:A->real) k, cr k])
           (\u. inv((u - xs) pow 2))`; `&3`; `Is:real`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[EST15_TILE_PERCUBE_INT] THEN
  MATCH_MP_TAC TFULL THEN EXISTS_TAC `B:real` THEN ASM_SIMP_TAC[REAL_HALF]);;

(* The same bound for the cells to the left of xs, with near edge cr, by     *)
(* reflection (EST15_TILE_POSSUM_R for the cells [--cr k, --cl k]).          *)
let EST15_TILE_POSSUM_L = prove
 (`!(Q:A->bool) (cl:A->real) (cr:A->real) (xs:real) (Is:real) (A:real).
     FINITE Q /\ &0 < Is /\ A <= xs - Is / &2 /\
     (!k. k IN Q ==> A <= cl k /\ cl k < cr k /\ cr k <= xs - Is / &2 /\
                     cr k - cl k = Is) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[cl i, cr i] INTER
                                real_interval[cl j, cr j]))
     ==> sum Q (\k. (Is / (xs - cr k)) pow 2) <= &6`,
  REWRITE_TAC[REAL_NEGLIGIBLE_INTER_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Q:A->bool`; `\k. --((cr:A->real) k)`;
                 `\k. --((cl:A->real) k)`; `--xs:real`; `Is:real`; `--A:real`]
         EST15_TILE_POSSUM_R) THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_INTER_REAL_INTERVAL;
              REAL_ARITH `--c - --x:real = x - c`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `k:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:A) IN Q`)) THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `j:A`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* Tiles of one scale k below u: the cells [xmid - Is/2, xmid + Is/2]        *)
(* (Is = 2 zpow --k) have pairwise negligible intersections.                 *)
let EST15_TILE_CELLS_AP = prove
 (`!(A:(int#int#int)->bool) (k:int) (u:int#int#int).
     (!s. s IN A ==> tile_k s = k /\ tile_le s u)
     ==> !i j. i IN A /\ j IN A /\ ~(i = j)
               ==> real_negligible
                    (real_interval[tile_xmid i - &2 zpow --k / &2,
                                   tile_xmid i - &2 zpow --k / &2 +
                                   &2 zpow --k] INTER
                     real_interval[tile_xmid j - &2 zpow --k / &2,
                                   tile_xmid j - &2 zpow --k / &2 +
                                   &2 zpow --k])`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EF_TILE_CELLS_NEGL2 THEN
  EXISTS_TAC `k:int` THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`A:(int#int#int)->bool`; `k:int`; `u:int#int#int`;
                 `i:int#int#int`; `j:int#int#int`] TILE_TREE_FST_SND_INJ) THEN
  ASM_REWRITE_TAC[]);;

(* Per-scale tile bounds for tiles in all positions.                         *)
let EST15_TILE_PERSCALE_R_AP = prove
 (`!(A:(int#int#int)->bool) (k:int) (u:int#int#int)
    (bb:real) (Bd:real).
     FINITE A /\ &0 < &2 zpow(--k) /\ bb + &2 zpow(--k) / &2 <= Bd /\
     (!s. s IN A ==> tile_k s = k /\ tile_le s u) /\
     (!s. s IN A ==> bb <= tile_xmid s - &2 zpow(--k) / &2 /\
                     tile_xmid s + &2 zpow(--k) / &2 <= Bd)
     ==> sum A (\s. inv((tile_xmid s - bb) pow 2)) <=
         &6 * inv(&2 zpow(--k) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:(int#int#int)->bool`; `k:int`; `u:int#int#int`]
    EST15_TILE_CELLS_AP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ABBREV_TAC `Is = &2 zpow(--k)` THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM real_div; GSYM REAL_POW_DIV] THEN
  MP_TAC(ISPECL
   [`A:(int#int#int)->bool`; `\s:int#int#int. tile_xmid s - Is / &2`;
    `\s:int#int#int. tile_xmid s - Is / &2 + Is`; `bb - Is / &2`; `Is:real`;
    `Bd:real`]
   EST15_TILE_POSSUM_R) THEN
  REWRITE_TAC[REAL_ARITH `(x - i / &2) - (b - i / &2) = x - b`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
  SUBGOAL_THEN `bb <= tile_xmid s - Is / &2 /\ tile_xmid s + Is / &2 <= Bd`
    MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC]);;

(* EST15_TILE_PERSCALE_L_AP: the per-scale tile bound on the left, for tiles *)
(* in all positions.  For the tiles s in A of scale k that lie to the left   *)
(* of the cube (tile_xmid s + Is/2 <= aa, which allows adjacency) and are    *)
(* bounded below by Ad,                                                      *)
(*   sum_A inv((aa - tile_xmid s)^2) <= 6/Is^2,                              *)
(* where Is = 2 zpow (--k) is the width of the tiles; this is                *)
(* EST15_TILE_POSSUM_L at the cells [xmid - Is/2, xmid - Is/2 + Is] with     *)
(* xs = aa + Is/2.                                                           *)
let EST15_TILE_PERSCALE_L_AP = prove
 (`!(A:(int#int#int)->bool) (k:int) (u:int#int#int)
    (aa:real) (Ad:real).
     FINITE A /\ &0 < &2 zpow(--k) /\ Ad <= aa - &2 zpow(--k) / &2 /\
     (!s. s IN A ==> tile_k s = k /\ tile_le s u) /\
     (!s. s IN A ==> Ad <= tile_xmid s - &2 zpow(--k) / &2 /\
                     tile_xmid s + &2 zpow(--k) / &2 <= aa)
     ==> sum A (\s. inv((aa - tile_xmid s) pow 2)) <=
         &6 * inv(&2 zpow(--k) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`A:(int#int#int)->bool`; `k:int`; `u:int#int#int`]
    EST15_TILE_CELLS_AP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ABBREV_TAC `Is = &2 zpow(--k)` THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM real_div; GSYM REAL_POW_DIV] THEN
  MP_TAC(ISPECL
   [`A:(int#int#int)->bool`; `\s:int#int#int. tile_xmid s - Is / &2`;
    `\s:int#int#int. tile_xmid s - Is / &2 + Is`; `aa + Is / &2`; `Is:real`;
    `Ad:real`]
   EST15_TILE_POSSUM_L) THEN
  REWRITE_TAC[REAL_ARITH `(a + i / &2) - (x - i / &2 + i) = a - x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
  SUBGOAL_THEN `Ad <= tile_xmid s - Is / &2 /\ tile_xmid s + Is / &2 <= aa`
    MP_TAC THENL [ASM_SIMP_TAC[]; ASM_REAL_ARITH_TAC]);;

(* The sum over the tiles of scale k disjoint from the cube of inv(dd^2) is  *)
(* at most 12/Is^2.                                                          *)

let EST15_POSSUM_BOTH = prove
 (`!(A:(int#int#int)->bool) (k:int) (u:int#int#int) (aa:real) (bb:real)
    (Ad:real) (Bd:real).
     FINITE A /\ &0 < &2 zpow(--k) /\
     Ad <= aa - &2 zpow(--k) / &2 /\ bb + &2 zpow(--k) / &2 <= Bd /\
     (!s. s IN A ==> tile_k s = k /\ tile_le s u) /\
     (!s. s IN A
          ==> (tile_xmid s < aa /\ Ad <= tile_xmid s - &2 zpow(--k) / &2 /\
               tile_xmid s + &2 zpow(--k) / &2 <= aa) \/
              (~(tile_xmid s < aa) /\ bb <= tile_xmid s - &2 zpow(--k) / &2 /\
               tile_xmid s + &2 zpow(--k) / &2 <= Bd))
     ==> sum A (\s. inv((if tile_xmid s < aa then aa - tile_xmid s
                         else tile_xmid s - bb) pow 2))
         <= &12 * inv((&2 zpow(--k)) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `A = {s | s IN A /\ tile_xmid s < aa} UNION
                    {s | s IN A /\ ~(tile_xmid s < aa)}`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
     MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {s:int#int#int | s IN A /\ tile_xmid s < aa} /\
    FINITE {s:int#int#int | s IN A /\ ~(tile_xmid s < aa)} /\
    DISJOINT {s:int#int#int | s IN A /\ tile_xmid s < aa}
             {s:int#int#int | s IN A /\ ~(tile_xmid s < aa)}`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT; DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
     NOT_IN_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&6 * inv((&2 zpow(--k)) pow 2) +
              &6 * inv((&2 zpow(--k)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`{s:int#int#int | s IN A /\ tile_xmid s < aa}`;
                     `k:int`; `u:int#int#int`; `aa:real`; `Ad:real`]
             EST15_TILE_PERSCALE_L_AP) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      REPEAT(FIRST
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[] THEN NO_TAC;
        (X_GEN_TAC `s:int#int#int` THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
         ASM_MESON_TAC[]);
        (X_GEN_TAC `s:int#int#int` THEN
          REWRITE_TAC[] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `s:int#int#int` o check(fun th ->
           is_forall(concl th) &&
           (let b = snd(strip_forall(concl th)) in
            is_imp b && is_disj(snd(dest_imp b))))) THEN
         ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[])]);
      MP_TAC(ISPECL [`{s:int#int#int | s IN A /\ ~(tile_xmid s < aa)}`;
                     `k:int`; `u:int#int#int`; `bb:real`; `Bd:real`]
             EST15_TILE_PERSCALE_R_AP) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      REPEAT(FIRST
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[] THEN NO_TAC;
        (X_GEN_TAC `s:int#int#int` THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
         ASM_MESON_TAC[]);
        (X_GEN_TAC `s:int#int#int` THEN
          REWRITE_TAC[] THEN STRIP_TAC THEN
         FIRST_X_ASSUM(MP_TAC o SPEC `s:int#int#int` o check(fun th ->
           is_forall(concl th) &&
           (let b = snd(strip_forall(concl th)) in
            is_imp b && is_disj(snd(dest_imp b))))) THEN
         ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[])])];
    REAL_ARITH_TAC]);;

(* CRUDE_ARITH: N (p dd)^2 <= 16 K inv(p^3) inv(dd^2), from N <= K inv p,    *)
(* dd<2/p (=> (p dd)^2<4).                                                   *)
let CRUDE_ARITH = prove
 (`!N K p dd:real.
     &0 < p /\ &0 < dd /\ &0 <= K /\ &0 <= N /\ N <= K * inv p /\
     dd < &2 * inv p
     ==> N * (p * dd) pow 2 <= &16 * K * inv(p pow 3) * inv(dd pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= p * dd /\ p * dd < &2` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `dd < &2 * inv p` THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(K * inv p) * (p * dd) pow 2` THEN
  ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LE_POW_2] THEN
  SUBGOAL_THEN
   `(K * inv p) * (p * dd) pow 2 =
    (K * (p * dd) pow 4) * (inv(p pow 3) * inv(dd pow 2)) /\
    &16 * K * inv(p pow 3) * inv(dd pow 2) =
    (K * &16) * (inv(p pow 3) * inv(dd pow 2))`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [UNDISCH_TAC `&0 < p` THEN UNDISCH_TAC `&0 < dd` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_POW_LE; REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`4`; `p * dd`; `&2`] REAL_POW_LE2) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let INVW_ID = prove
 (`!p dd:real. &0 < p /\ &0 < dd ==> inv((inv p / dd) pow 2) = (p * dd) pow 2`,
  REWRITE_TAC[REAL_POW_DIV; REAL_POW_INV; REAL_INV_DIV] THEN
  REWRITE_TAC[real_div; REAL_INV_INV] THEN REAL_ARITH_TAC);;

let COEFF_LE = prove
 (`!K tau ip idd Cd:real.
     &0 <= Cd /\ &0 <= tau pow 2 * ip * idd
     ==> &16 * (K pow 2 * tau pow 2) * ip * idd
         <= (Cd + &16 * K pow 2) * tau pow 2 * ip * idd`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&16 * (K pow 2 * tau pow 2) * ip * idd =
      (&16 * K pow 2) * (tau pow 2 * ip * idd) /\
    (Cd + &16 * K pow 2) * tau pow 2 * ip * idd =
      (Cd + &16 * K pow 2) * (tau pow 2 * ip * idd)`
   (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* DE_ID and DENS_ARITH: the arithmetic for the case dd >= 2 inv p of        *)
(* EST15_TILE_SQ_UNI, where the distance bound EST15_TILE_SQ_DIST is used:   *)
(*   N <= Cd tau^2 inv(p^5) inv(dd^4)                                        *)
(*   ==> N (p dd)^2 <= Cd tau^2 inv(p^3) inv(dd^2).                          *)
let DE_ID = prove
 (`!Cd tau p dd:real. ~(p = &0) /\ ~(dd = &0)
     ==> (Cd * tau pow 2 * inv(p pow 5) * inv(dd pow 4)) * (p * dd) pow 2
         = Cd * tau pow 2 * inv(p pow 3) * inv(dd pow 2)`,
  CONV_TAC REAL_FIELD);;

let DENS_ARITH = prove
 (`!N Cd tau p dd:real.
     &0 < p /\ &0 < dd /\ &0 <= N /\
     N <= Cd * tau pow 2 * inv(p pow 5) * inv(dd pow 4)
     ==> N * (p * dd) pow 2 <= Cd * tau pow 2 * inv(p pow 3) * inv(dd pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((Cd:real) * tau pow 2 * inv(p pow 5) * inv(dd pow 4)) *
              (p * dd) pow 2` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LE_POW_2];
    MP_TAC(SPECL [`Cd:real`; `tau:real`; `p:real`; `dd:real`] DE_ID) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

let EST15_TILE_SQ_UNI = prove
 (`?C. &0 <= C /\
    !(b:real->real) (Ff:real->bool) (Om:real->bool) (s:int#int#int)
      (yt:real) (ys:real) (tau:real) (dd:real) (Jc:real->bool).
        real_measurable Ff /\ real_measurable Om /\ &0 <= tau /\
        &2 zpow (--(tile_k s)) / &2 <= dd /\
        abs(ys - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
        &0 <= hl_maximal (\u. if u IN Ff then &1 else &0) ys /\
        hl_maximal (\u. if u IN Ff then &1 else &0) ys <= tau /\
        (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                         tau * (if x IN Om then &1 else &0)) /\
        Jc SUBSET {x | dd <= abs(x - tile_xmid s)} /\
        (\z. Cx(b(drop z)) *
             cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                 phi_sigma s carleson_phi (drop z)))
          integrable_on (IMAGE lift Jc) /\
        (\x. abs(b x) * cw_tile s x) real_integrable_on Jc /\
        (\x. abs(b x) * cw_tile s x) real_integrable_on
          {x | dd <= abs(x - tile_xmid s)} /\
        (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
        (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
          real_integrable_on (:real) /\
        (\x. (if x IN Om then &1 else &0) * cw_tile s x)
          real_integrable_on (:real)
        ==> norm(integral (IMAGE lift Jc)
                   (\z. Cx(b(drop z)) *
                        cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2
            / ((inv(&2 zpow (tile_k s)) / dd) pow 2)
            <= C * tau pow 2 * inv((&2 zpow (tile_k s)) pow 3) *
               inv(dd pow 2)`,
  X_CHOOSE_THEN `Cd:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dens"))
    EST15_TILE_SQ_DIST THEN
  X_CHOOSE_THEN `Cc:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "crude"))
    CH_LARGE_PERTILE_SQ THEN
  EXISTS_TAC `Cd + &16 * (&41 * Cc) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ZPOW_ONE_SUB; REAL_ZPOW_NEG]) THEN
    ABBREV_TAC `p = &2 zpow (tile_k(s:int#int#int))` THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < dd` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < inv p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check(fun th -> concl th = `inv p / &2 <= dd`)) THEN
      REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `N = norm(integral (IMAGE lift Jc)
                   (\z. Cx(b(drop z)) *
                        cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2` THEN
  SUBGOAL_THEN `&0 <= N` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  (* clear the division: goal N/w <= RHS  <=>  N <= RHS*w                    *)
  ONCE_REWRITE_TAC[REAL_ARITH `a / w <= r <=> a * inv w <= r`] THEN
  ASM_SIMP_TAC[INVW_ID] THEN
  (* now goal: N * (p*dd)^2 <= (Cd+16(41Cc)^2) tau^2 inv(p^3) inv(dd^2)      *)
  ASM_CASES_TAC `dd < &2 * inv p` THENL
   [(* CRUDE: N <= (41Cc)^2 tau^2 inv p *)
    SUBGOAL_THEN `N <= ((&41 * Cc) pow 2 * tau pow 2) * inv p` MP_TAC THENL
     [EXPAND_TAC "N" THEN
      SUBGOAL_THEN `inv p = inv(&2 zpow (tile_k(s:int#int#int)))`
        SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= a * b * c ==> x <= (a * b) * c`) THEN
      USE_THEN "crude" (fun th -> MATCH_MP_TAC(SPECL
        [`b:real->real`; `Ff:real->bool`; `Om:real->bool`;
         `s:int#int#int`; `yt:real`; `ys:real`;
         `tau:real`; `Jc:real->bool`] th)) THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&41 * Cc) pow 2 * tau pow 2` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&16 * ((&41 * Cc) pow 2 * tau pow 2) * inv(p pow 3) *
                inv(dd pow 2)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CRUDE_ARITH];
      (* 16 (41Cc)^2 tau^2 inv(p^3) inv(dd^2) <= (Cd+16(41Cc)^2) tau^2       *)
      (* inv(p^3) inv(dd^2)                                                  *)
      MATCH_MP_TAC COEFF_LE THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC]];
    (* DENSITY: dd >= 2 inv p, use EST15_TILE_SQ_DIST with R := dd           *)
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
    SUBGOAL_THEN `N <= Cd * tau pow 2 * inv(p pow 5) * inv(dd pow 4)`
      MP_TAC THENL
     [EXPAND_TAC "N" THEN EXPAND_TAC "p" THEN
      USE_THEN "dens" (fun th -> MATCH_MP_TAC(SPECL
        [`b:real->real`; `Ff:real->bool`; `Om:real->bool`;
         `s:int#int#int`; `yt:real`; `ys:real`;
         `tau:real`; `dd:real`; `Jc:real->bool`] th)) THEN
      ASM_REWRITE_TAC[] THEN
      (* |ys - xmid| <= dd, from |ys - xmid| <= 2 inv p <= dd                *)
      FIRST_X_ASSUM(MP_TAC o check(fun th -> concl th =
        `abs(ys - tile_xmid s) <= &2 * inv p`)) THEN
      FIRST_X_ASSUM(MP_TAC o check(fun th -> concl th =
        `&2 * inv p <= dd`)) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Cd:real) * tau pow 2 * inv(p pow 3) * inv(dd pow 2)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[DENS_ARITH];
      (* Cd tau^2 inv(p^3) inv(dd^2) <= (Cd+16(41Cc)^2) tau^2 inv(p^3)       *)
      (* inv(dd^2)                                                           *)
      SUBGOAL_THEN `&0 <= tau pow 2 * inv(p pow 3) * inv(dd pow 2)`
        ASSUME_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_LE_INV_EQ] THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= e ==> Cd <= Cd + e`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC]]);;

(* EST15_FA_PERSCALE_B: the per-scale bound for factor A, with a parameter B *)
(* for the bound on the sum over positions (B = 12 in                        *)
(* EST15_FA_PERSCALE_TILE).  If sum dsq <= B p^2 and                         *)
(*   0 <= q s <= (Cc tau^2 inv(p^3)) dsq s     for s in Fs,                  *)
(* then sum q <= B Cc tau^2 inv p.  FA_AC is a ring identity used in the     *)
(* proof.                                                                    *)
let FA_AC = prove
 (`!Cc tau u v B pp:real.
     (Cc * tau pow 2 * u * v) * B * pp = B * Cc * tau pow 2 * u * (pp * v)`,
  CONV_TAC REAL_RING);;

let EST15_FA_PERSCALE_B = prove
 (`!(Fs:(int#int#int)->bool) (q:(int#int#int)->real) (dsq:(int#int#int)->real)
    (p:real) (Cc:real) (tau:real) (B:real).
     FINITE Fs /\ &0 < p /\ &0 <= Cc /\ &0 <= B /\
     (!s. s IN Fs ==> &0 <= q s /\
                      q s <= (Cc * tau pow 2 * inv(p pow 3)) * dsq s) /\
     sum Fs dsq <= B * p pow 2
     ==> sum Fs q <= B * Cc * tau pow 2 * inv p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Fs (\s:int#int#int.
                ((Cc:real) * tau pow 2 * inv(p pow 3)) * dsq s)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_LE];
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `((Cc:real) * tau pow 2 * inv(p pow 3)) * (B * p pow 2)` THEN
      CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      REWRITE_TAC[REAL_LE_INV_EQ] THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `~(p = &0)` ASSUME_TAC THENL
        [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(p:real) pow 3 = p * p pow 2` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_INV_MUL] THEN
      SUBGOAL_THEN `~(p pow 2 = &0)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_POW_NZ; ALL_TAC] THEN
      REWRITE_TAC[FA_AC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV] THEN REAL_ARITH_TAC]]);;

(* EST15_FA_PERSCALE_TILE: factor A at one scale k.  If for each tile s      *)
(*   0 <= q s <= (Cu tau^2 inv((2 zpow k)^3)) inv(dd^2),                     *)
(* where dd is the distance from tile_xmid s to the cube [aa,bb], then       *)
(*   sum q <= 12 Cu tau^2 inv(2 zpow k),                                     *)
(* since the sum over positions of inv(dd^2) is at most 12 (2 zpow k)^2      *)
(* (EST15_POSSUM_BOTH); this is EST15_FA_PERSCALE_B with B = 12.             *)
let EST15_FA_PERSCALE_TILE = prove
 (`!(Fs:(int#int#int)->bool) (q:(int#int#int)->real) (k:int) (u:int#int#int)
    (aa:real) (bb:real) (Ad:real) (Bd:real) (Cu:real) (tau:real).
     FINITE Fs /\ &0 <= Cu /\ &0 < &2 zpow(--k) /\
     Ad <= aa - &2 zpow(--k) / &2 /\ bb + &2 zpow(--k) / &2 <= Bd /\
     (!s. s IN Fs ==> tile_k s = k /\ tile_le s u) /\
     (!s. s IN Fs
          ==> (tile_xmid s < aa /\ Ad <= tile_xmid s - &2 zpow(--k) / &2 /\
               tile_xmid s + &2 zpow(--k) / &2 <= aa) \/
              (~(tile_xmid s < aa) /\ bb <= tile_xmid s - &2 zpow(--k) / &2 /\
               tile_xmid s + &2 zpow(--k) / &2 <= Bd)) /\
     (!s. s IN Fs
          ==> &0 <= q s /\
              q s <= (Cu * tau pow 2 * inv((&2 zpow k) pow 3)) *
                     inv((if tile_xmid s < aa then aa - tile_xmid s
                          else tile_xmid s - bb) pow 2))
     ==> sum Fs q <= &12 * Cu * tau pow 2 * inv(&2 zpow k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Fs (\s. inv((if tile_xmid s < aa then aa - tile_xmid s
                     else tile_xmid s - bb) pow 2))
    <= &12 * (&2 zpow k) pow 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Fs:(int#int#int)->bool`; `k:int`; `u:int#int#int`;
                   `aa:real`; `bb:real`; `Ad:real`; `Bd:real`]
           EST15_POSSUM_BOTH) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ZPOW_NEG; REAL_INV_POW; REAL_INV_INV]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`Fs:(int#int#int)->bool`; `q:(int#int#int)->real`;
    `\s:int#int#int. inv((if tile_xmid s < aa then aa - tile_xmid s
                          else tile_xmid s - bb) pow 2)`;
    `&2 zpow k`; `Cu:real`; `tau:real`; `&12`] EST15_FA_PERSCALE_B) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* per-cube factor A total: fiber-reindex the per-scale bound over scales    *)
let FA_AC2 = prove
 (`!Cu tau a b:real.
     &12 * Cu * tau pow 2 * (a * b) = (&12 * Cu * tau pow 2 * a) * b`,
  CONV_TAC REAL_RING);;

let EST15_FA_PERCUBE = prove
 (`!(Tt:(int#int#int)->bool) (q:(int#int#int)->real) (Kc:int) (u:int#int#int)
    (aa:real) (bb:real) (Ad:real) (Bd:real) (Cu:real) (tau:real).
     FINITE Tt /\ &0 <= Cu /\
     (!s. s IN Tt ==> Kc <= tile_k s /\ tile_le s u) /\
     (!s. s IN Tt ==> Ad <= aa - &2 zpow(--(tile_k s)) / &2 /\
                      bb + &2 zpow(--(tile_k s)) / &2 <= Bd) /\
     (!s. s IN Tt
          ==> (tile_xmid s < aa /\
               Ad <= tile_xmid s - &2 zpow(--(tile_k s)) / &2 /\
               tile_xmid s + &2 zpow(--(tile_k s)) / &2 <= aa) \/
              (~(tile_xmid s < aa) /\
               bb <= tile_xmid s - &2 zpow(--(tile_k s)) / &2 /\
               tile_xmid s + &2 zpow(--(tile_k s)) / &2 <= Bd)) /\
     (!s. s IN Tt
          ==> &0 <= q s /\
              q s <= (Cu * tau pow 2 * inv((&2 zpow (tile_k s)) pow 3)) *
                     inv((if tile_xmid s < aa then aa - tile_xmid s
                          else tile_xmid s - bb) pow 2))
     ==> sum Tt q <= (&12 * Cu * tau pow 2 * inv(&2 zpow Kc)) * &2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "tkm") (CONJUNCTS_THEN2 (LABEL_TAC "sca")
      (CONJUNCTS_THEN2 (LABEL_TAC "pos") (LABEL_TAC "quo")))))) THEN
  MATCH_MP_TAC EST15_FA_REINDEX THEN
  EXISTS_TAC `\s:int#int#int. num_of_int(tile_k s - Kc)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &12 * Cu * tau pow 2 * inv(&2 zpow Kc)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_LE_INV_EQ] THEN
    TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `jj:num` THEN
  ASM_CASES_TAC
   `{s:int#int#int | s IN Tt /\ num_of_int(tile_k s - Kc) = jj} = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `s0:int#int#int` o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  SUBGOAL_THEN `(s0:int#int#int) IN Tt /\ tile_k s0 = Kc + &jj`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[NIDX_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `Ad <= aa - &2 zpow(--(Kc + &jj)) / &2 /\
                bb + &2 zpow(--(Kc + &jj)) / &2 <= Bd`
   STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{s:int#int#int | s IN Tt /\ num_of_int(tile_k s - Kc) = jj}`;
     `q:(int#int#int)->real`;
    `Kc + &jj:int`; `u:int#int#int`; `aa:real`; `bb:real`;
      `Ad:real`; `Bd:real`;
    `Cu:real`; `tau:real`] EST15_FA_PERSCALE_TILE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(FIRST
     [(MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[] THEN NO_TAC);
      (FIRST_ASSUM ACCEPT_TAC);
      (ASM_REWRITE_TAC[] THEN NO_TAC);
      (MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC);
      (X_GEN_TAC `s:int#int#int` THEN REWRITE_TAC[IN_ELIM_THM] THEN
       DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "nid")) THEN
       SUBGOAL_THEN `tile_k(s:int#int#int) = Kc + &jj`
         (fun th -> ASSUME_TAC th THEN REWRITE_TAC[SYM th]) THENL
        [MP_TAC(ISPECL [`tile_k(s:int#int#int)`;
          `Kc:int`; `jj:num`] NIDX_EQ) THEN
         (ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
         USE_THEN "nid" (fun th -> REWRITE_TAC[]); ALL_TAC] THEN
       ASM_SIMP_TAC[] THEN ASM_MESON_TAC[])]);
    MP_TAC(ISPECL [`Kc + &jj:int`; `Kc:int`] ZPOW_TILE_NIDX) THEN
    REWRITE_TAC[INT_ARITH `(Kc + &jj) - Kc:int = &jj`; NUM_OF_INT_OF_NUM] THEN
    ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[FA_AC2]]);;

let POS_DISJUNCT = prove
 (`!(xmid:real) (aa:real) (bb:real) (Is:real) (Ad:real) (Bd:real).
     &0 < Is /\ aa < bb /\ Ad <= xmid - Is / &2 /\ xmid + Is / &2 <= Bd /\
     (bb <= xmid - Is / &2 \/ xmid + Is / &2 <= aa)
     ==> (xmid < aa /\ Ad <= xmid - Is / &2 /\ xmid + Is / &2 <= aa) \/
         (~(xmid < aa) /\ bb <= xmid - Is / &2 /\ xmid + Is / &2 <= Bd)`,
  ASM_REAL_ARITH_TAC);;

let EST15_BRANCH_FA = prove
 (`?Cu. &0 <= Cu /\
    !(P:(int#int#int)->bool) (t:int#int#int) (b:real->real)
      (Ff:real->bool) (Om:real->bool)
     (ypt:int#int#int->real) (aa:real) (bb:real) (Kc:int)
       (u:int#int#int) (tau:real)
     (Ad:real) (Bd:real).
     FINITE P /\ &0 <= tau /\ real_measurable Ff /\
     real_measurable Om /\ aa < bb /\
     (!s. s IN P ==> tile_le s u) /\
     (!s. s IN P /\ Kc < tile_k s
          ==> Kc <= tile_k s /\
              Ad <= tile_xmid s - &2 zpow(--(tile_k s)) / &2 /\
              tile_xmid s + &2 zpow(--(tile_k s)) / &2 <= Bd /\
              Ad <= aa - &2 zpow(--(tile_k s)) / &2 /\
              bb + &2 zpow(--(tile_k s)) / &2 <= Bd) /\
     (!s. s IN P ==> abs(ypt s - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
                     &0 <= hl_maximal (\uu. if uu IN Ff then &1 else &0)
                                      (ypt s) /\
                     hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s)
                     <= tau) /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (!s. s IN P /\ Kc < tile_k s
          ==> (bb <= tile_xmid s - &2 zpow(--(tile_k s)) / &2 \/
               tile_xmid s + &2 zpow(--(tile_k s)) / &2 <= aa)) /\
     (!s. s IN P
          ==> (\z. Cx(b(drop z)) *
                   cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                       phi_sigma s carleson_phi (drop z)))
              integrable_on (IMAGE lift (real_interval[aa,bb])) /\
              (\x. abs(b x) * cw_tile s x) real_integrable_on
                (real_interval[aa,bb]) /\
              (\x. abs(b x) * cw_tile s x) real_integrable_on
                {x | (if tile_xmid s < aa then aa - tile_xmid s
                      else tile_xmid s - bb) <= abs(x - tile_xmid s)} /\
              (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
              (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
                real_integrable_on (:real) /\
              (\x. (if x IN Om then &1 else &0) * cw_tile s x)
                real_integrable_on (:real))
     ==> sum {s | s IN P /\ Kc < tile_k s}
             (\s. norm(integral (IMAGE lift (real_interval[aa,bb]))
                    (\z. Cx(b(drop z)) *
                         cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                             phi_sigma s carleson_phi (drop z)))) pow 2 /
                  ((inv(&2 zpow (tile_k s)) /
                    (if tile_xmid s < aa then aa - tile_xmid s
                     else tile_xmid s - bb)) pow 2))
         <= (&12 * Cu * tau pow 2 * inv(&2 zpow Kc)) * &2`,
  X_CHOOSE_THEN `Cu:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uni"))
    EST15_TILE_SQ_UNI THEN
  EXISTS_TAC `Cu:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EST15_FA_PERCUBE THEN
  MAP_EVERY EXISTS_TAC [`u:int#int#int`; `aa:real`; `bb:real`; `Ad:real`;
    `Bd:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!s:int#int#int. s IN P ==> &0 < &2 zpow(--(tile_k s))`
   (LABEL_TAC "ispos") THENL
   [X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    ASM_SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[IN_ELIM_THM];
    ASM_SIMP_TAC[POS_DISJUNCT; IN_ELIM_THM];
    (* per-tile quotient via EST15_TILE_SQ_UNI                               *)
    X_GEN_TAC `s:int#int#int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_POW_2]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    USE_THEN "uni" (fun th -> MATCH_MP_TAC(SPECL
      [`b:real->real`; `Ff:real->bool`; `Om:real->bool`;
       `s:int#int#int`; `tile_ymid t`;
       `(ypt:int#int#int->real) s`; `tau:real`;
       `if tile_xmid s < aa then aa - tile_xmid s else tile_xmid s - bb`;
       `real_interval[aa,bb]`] th)) THEN
    MP_TAC(ISPECL [`tile_xmid(s:int#int#int)`; `aa:real`; `bb:real`;
                   `&2 zpow(--(tile_k(s:int#int#int)))`]
                     CUBE_OUTSIDE_DD_SEP) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* EST15_BRANCH_FB: factor B for large cubes, in the form used in            *)
(* CH_EST15_LARGE (from EST15_FACTORB_PERTILE).  Suppose that the tile       *)
(* interval of s and the cubes [aa k, bb k] lie in [Ad,Bd], that the cubes   *)
(* have pairwise negligible intersections, and that each cube lies outside   *)
(* the tile interval and has width at least inv(2 zpow (Kc k)), where Kc k   *)
(* is less than tile_k s.  Then                                              *)
(*   sum_k (inv(2 zpow tk) / dd_k)^2 <= 10,                                  *)
(* where dd_k is the distance from tile_xmid s to the k-th cube.             *)
let EST15_BRANCH_FB = prove
 (`!(Qf:num->bool) (aa:num->real) (bb:num->real) (Kc:num->int)
    (s:int#int#int) (Ad:real) (Bd:real).
     FINITE Qf /\
     Ad <= tile_xmid s - &2 zpow(--(tile_k s)) / &2 /\
     tile_xmid s + &2 zpow(--(tile_k s)) / &2 <= Bd /\
     (!k. k IN Qf ==> aa k < bb k /\ Ad <= aa k /\ bb k <= Bd /\
                      inv(&2 zpow (Kc k)) <= bb k - aa k /\ Kc k < tile_k s /\
                      (bb k <= tile_xmid s - &2 zpow(--(tile_k s)) / &2 \/
                       tile_xmid s + &2 zpow(--(tile_k s)) / &2 <= aa k)) /\
     (!i j. i IN Qf /\ j IN Qf /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j]))
     ==> sum Qf (\k. (inv(&2 zpow (tile_k s)) /
                      (if tile_xmid s < aa k then aa k - tile_xmid s
                       else tile_xmid s - bb k)) pow 2) <= &10`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow(--(tile_k(s:int#int#int)))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`Qf:num->bool`; `aa:num->real`; `bb:num->real`;
                 `tile_xmid(s:int#int#int)`;
                 `&2 zpow(--(tile_k(s:int#int#int)))`; `Ad:real`;
                 `Bd:real`] EST15_FACTORB_PERTILE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; ZPOW_STRICT_HALF];
    REWRITE_TAC[REAL_ZPOW_NEG]]);;

(* EST15_DK_SUM: the sum over the cubes of the per-cube bounds D_k for       *)
(* factor A of large cubes.  If inv(2 zpow (Kc k)) <= bb k - aa k for each   *)
(* cube and sum_Q (bb - aa) <= 2R, then                                      *)
(*   sum_Q (24 Cu tau^2 inv(2 zpow (Kc k))) * 2 <= (24 Cu 2) tau^2 (2R),     *)
(* since sum_Q inv(2 zpow (Kc k)) <= sum_Q (bb - aa) <= 2R.                  *)
let EST15_DK_SUM = prove
 (`!(Q:num->bool) (aa:num->real) (bb:num->real) (Kc:num->int)
    (Cu:real) (tau:real) (R:real).
     FINITE Q /\ &0 <= Cu /\ &0 <= tau /\
     (!k. k IN Q ==> inv(&2 zpow (Kc k)) <= bb k - aa k) /\
     sum Q (\k. bb k - aa k) <= &2 * R
     ==> sum Q (\k. (&24 * Cu * tau pow 2 * inv(&2 zpow (Kc k))) * &2)
         <= (&24 * Cu * &2) * tau pow 2 * (&2 * R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum Q (\k. (&24 * Cu * tau pow 2 * inv(&2 zpow ((Kc:num->int) k))) * &2)
    = (&24 * Cu * &2 * tau pow 2) * sum Q (\k. inv(&2 zpow (Kc k)))`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum Q (\k. inv(&2 zpow ((Kc:num->int) k)))
                 <= &2 * R` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum Q (\k. (bb:num->real) k - aa k)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LE];
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &24 * Cu * &2 * tau pow 2` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
     ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&24 * Cu * &2 * tau pow 2) * (&2 * R)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL];
    REAL_ARITH_TAC]);;

(* The tree energy of the large cubes:                                       *)
(*   sum_{s in tree} (sum_{k: Kc k < tile_k s} |<b_k, phi_s>|)^2 <= Cd2      *)
(*     tau^2 R,                                                              *)
(* by the weighted Cauchy-Schwarz bound CH_EF_ASSEMBLE_COND with weight      *)
(* (inv(2 zpow tk)/dd)^2, factor A from EST15_BRANCH_FA and factor B from    *)
(* EST15_BRANCH_FB.  The positivity of the weights needs the separation of   *)
(* cube and tile, which holds only for the tiles of the tree.                *)
let CH_EST15_LARGE = prove
 (`?Cd2. &0 <= Cd2 /\
    !(P:(int#int#int)->bool) (t:int#int#int) (Q:num->bool) (b:real->real)
     (Ff:real->bool) (Om:real->bool) (ypt:int#int#int->real)
     (aa:num->real) (bb:num->real) (Kc:num->int) (tau:real) (R:real)
     (Ad:real) (Bd:real).
     FINITE P /\ FINITE Q /\ &0 <= tau /\ &0 < R /\ real_measurable
       Ff /\ real_measurable Om /\
     (!s. s IN P ==> tile_ler s t) /\
     (!s. s IN P ==> Ad <= tile_xmid s - &2 zpow (--(tile_k s)) / &2 /\
                     tile_xmid s + &2 zpow (--(tile_k s)) / &2 <= Bd) /\
     (!s. s IN P ==> abs(ypt s - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
                     &0 <= hl_maximal (\uu. if uu IN Ff then &1 else &0)
                                      (ypt s) /\
                     hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s)
                     <= tau) /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     (!k. k IN Q ==> aa k < bb k /\ Ad <= aa k /\ bb k <= Bd /\
                     inv(&2 zpow (Kc k)) <= bb k - aa k) /\
     (!s k. k IN Q
            ==> (\z. Cx(b(drop z)) *
                     cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                         phi_sigma s carleson_phi (drop z)))
                integrable_on (IMAGE lift (real_interval[aa k, bb k])) /\
                (\x. abs(b x) * cw_tile s x) real_integrable_on
                  (real_interval[aa k, bb k]) /\
                (\x. abs(b x) * cw_tile s x) real_integrable_on
                  {x | (if tile_xmid s < aa k then aa k - tile_xmid s
                        else tile_xmid s - bb k) <= abs(x - tile_xmid s)} /\
                (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
                (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
                  real_integrable_on (:real) /\
                (\x. (if x IN Om then &1 else &0) * cw_tile s x)
                  real_integrable_on (:real)) /\
     (!s k. s IN P /\ k IN Q /\ Kc k < tile_k s
            ==> (bb k <= tile_xmid s - &2 zpow (--(tile_k s)) / &2 \/
                 tile_xmid s + &2 zpow (--(tile_k s)) / &2 <= aa k)) /\
     (!s k. s IN P /\ k IN Q /\ Kc k < tile_k s
            ==> Ad <= aa k - &2 zpow (--(tile_k s)) / &2 /\
                bb k + &2 zpow (--(tile_k s)) / &2 <= Bd) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j])) /\
     sum Q (\k. bb k - aa k) <= &2 * R
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. (sum {k | k IN Q /\ Kc k < tile_k s}
                    (\k. norm(integral (IMAGE lift (real_interval[aa k, bb k]))
                      (\z. Cx(b(drop z)) *
                           cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                               phi_sigma s carleson_phi (drop z)))))) pow 2)
         <= Cd2 * tau pow 2 * R`,
  X_CHOOSE_THEN `Cu:real` STRIP_ASSUME_TAC EST15_BRANCH_FA THEN
  EXISTS_TAC `&10 * (&24 * Cu * &2) * &2` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`Q:num->bool`; `{s | s IN P /\ tile_ler s t}`;
    `\(s:int#int#int) (k:num). norm(integral
        (IMAGE lift (real_interval[(aa:num->real) k, (bb:num->real) k]))
        (\z. Cx((b:real->real)(drop z)) *
             cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                 phi_sigma s carleson_phi (drop z))))`;
    `\(s:int#int#int) (k:num). (inv(&2 zpow (tile_k s)) /
        (if tile_xmid s < (aa:num->real) k then aa k - tile_xmid s
         else tile_xmid s - bb k)) pow 2`;
    `\(s:int#int#int) (k:num). (Kc:num->int) k < tile_k s`;
    `\k:num. (&24 * Cu * tau pow 2 * inv(&2 zpow ((Kc:num->int) k))) * &2`;
    `&10`; `(&24 * Cu * &2) * tau pow 2 * (&2 * R)`]
      CH_EF_ASSEMBLE_COND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT; NORM_POS_LE; REAL_LE_POW_2; REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [(* the weights are positive on the tree: cube and tile are separated *)
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
      SIMP_TAC[REAL_LT_INV; REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH] THEN
      MP_TAC(ISPECL [`tile_xmid(s:int#int#int)`; `(aa:num->real) k`;
        `(bb:num->real) k`; `&2 zpow(--(tile_k(s:int#int#int)))`]
        CUBE_OUTSIDE_DD_SEP) THEN
      MP_TAC(ISPECL [`&2`; `--(tile_k(s:int#int#int))`] REAL_ZPOW_LT) THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH] THEN REPEAT STRIP_TAC THEN
      ASM_REAL_ARITH_TAC;
      (* factor B: EST15_BRANCH_FB on the cubes below the tile *)
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC EST15_BRANCH_FB THEN
      MAP_EVERY EXISTS_TAC [`Kc:num->int`; `Ad:real`; `Bd:real`] THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      (* factor A: EST15_BRANCH_FA for the cube k *)
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= c /\ x <= (&12 * c) * &2 ==> x <= (&24 * c) * &2`) THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LE_INV_EQ;
                     REAL_ZPOW_LE; REAL_POS];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o SPECL
       [`{s | s IN P /\ tile_ler s t}`; `t:int#int#int`; `b:real->real`;
        `Ff:real->bool`; `Om:real->bool`; `ypt:int#int#int->real`;
        `(aa:num->real) k`; `(bb:num->real) k`; `(Kc:num->int) k`;
        `t:int#int#int`; `tau:real`; `Ad:real`; `Bd:real`]) THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; TILE_LER_IMP_LE;
                   INT_LT_IMP_LE] THEN
      ASM_MESON_TAC[];
      (* the sum of the bounds D k: EST15_DK_SUM *)
      MATCH_MP_TAC EST15_DK_SUM THEN
      MAP_EVERY EXISTS_TAC [`aa:num->real`; `bb:num->real`] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    CONV_TAC REAL_RING]);;

(* The per-tile squared amplitude for small cubes (cf.                       *)
(* Grafakos-Tao-Terwilleger, equation (14)), from CH_CUBE_TILE_SQ and        *)
(* int_{[a,b]} |bR| <= 2 tau (b-a): if 2^tk (b-a)/2 <= 1 then                *)
(*   norm(int_sk)^2 <= C tau^2 (2 zpow tk s) *                               *)
(*                     ((b-a)^2 * ((2 zpow tk s (b-a)/2) cw(...))^2),        *)
(* where cw(x) = 1/(1+|x|)^3 gives the decay in the distance.                *)
let EST14_TILE_SQ = prove
 (`?C. &0 <= C /\
    !(bR:real->real) (s:int#int#int) t (a:real) b (tau:real).
        bR absolutely_real_integrable_on (real_interval[a,b]) /\
        real_integral (real_interval[a,b]) bR = &0 /\
        real_integral (real_interval[a,b]) (\x. abs(bR x))
          <= &2 * tau * (b - a) /\
        &0 <= tau /\ tile_ler s t /\ a <= b /\
        &2 zpow tile_k s * ((b - a) / &2) <= &1
        ==> norm(integral (IMAGE lift (real_interval[a,b]))
                   (\z. Cx(bR(drop z)) *
                        cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2
            <= C * tau pow 2 * (&2 zpow tile_k s) *
               ((b - a) pow 2 *
                ((&2 zpow tile_k s * (b - a) / &2) *
                 cw(&2 zpow tile_k s * ((a + b) / &2 - tile_xmid s))) pow 2)`,
  X_CHOOSE_THEN `Cd2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cts"))
    CH_CUBE_TILE_SQ THEN
  EXISTS_TAC `&4 * Cd2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`bR:real->real`; `s:int#int#int`; `t:int#int#int`;
    `a:real`; `b:real`; `tau:real`] THEN
  STRIP_TAC THEN
  USE_THEN "cts" (fun th -> MP_TAC(SPECL
    [`bR:real->real`; `s:int#int#int`; `t:int#int#int`; `a:real`; `b:real`;
     `&2 * tau * (b - a)`] th)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SUBGOAL_THEN `&0 <= b - a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL]];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Factor B for small cubes (|J_k| <= 2|I_s|): sum_k |J_k| * peak_k <= 8,    *)
(* where peak_k = 2^tk cw(2^tk((aa+bb)/2 - xs)) is the cw factor of the      *)
(* per-tile amplitude.  Each cube has |J_k| peak_k <= 8 int_{J_k} cw_tile s, *)
(* since cw varies slowly over a small cube, and for disjoint cubes sum_k    *)
(* int_{J_k} cw_tile s <= int_R cw_tile s = 1.                               *)
(* ------------------------------------------------------------------------- *)

(* INV_MONO_C : monotone inverse with a multiplicative slack constant.       *)
let INV_MONO_C = prove
 (`!A B c:real. &0 < A /\ &0 < B /\ &0 < c /\ B <= c * A
    ==> &1 / A <= c * (&1 / B)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `c * (&1 / B) = (c * &1) / B` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(c * &1) / B * A = (c * A) / B` SUBST1_TAC THENL
   [REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

(* CW_CLOSE1 : args within 1 give cw a <= 8 cw b (the small-cube-diameter    *)
(* threshold, const 8=2^3).                                                  *)
let CW_CLOSE1 = prove
 (`!a b:real. abs(a - b) <= &1 ==> cw a <= &8 * cw b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cw] THEN
  MATCH_MP_TAC INV_MONO_C THEN
  SUBGOAL_THEN `&0 < &1 + abs a /\ &0 < &1 + abs b` STRIP_ASSUME_TAC THENL
   [REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT];
    ASM_MESON_TAC[REAL_POW_LT];
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * (&1 + abs a)) pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC]]);;

let CW_TILE_INTEGRABLE_UNIV = prove
 (`!(s:int#int#int). cw_tile s real_integrable_on (:real)`,
  ASM_MESON_TAC[HAS_REAL_INTEGRAL_INTEGRABLE; CW_TILE_FULL]);;

let CW_TILE_INT_UNIV = prove
 (`!(s:int#int#int). real_integral (:real) (cw_tile s) = &1`,
  ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; CW_TILE_FULL]);;

(* CW_TILE_SMALL_PTW: for x in a small cube [aa,bb], i.e. p (bb-aa)/2 <= 1   *)
(* with p = 2 zpow tk s, the peak value satisfies                            *)
(*   p cw(p (cc - xs)) <= 8 cw_tile s x,                                     *)
(* where cc = (aa+bb)/2 and xs = tile_xmid s.  Since                         *)
(*   |p (cc - xs) - p (x - xs)| = p |cc - x| <= p (bb-aa)/2 <= 1,            *)
(* this follows from CW_CLOSE1.                                              *)
let CW_TILE_SMALL_PTW = prove
 (`!(s:int#int#int) (aa:real) (bb:real) (x:real).
     &2 zpow (tile_k s) * ((bb - aa) / &2) <= &1 /\ aa <= x /\ x <= bb
     ==> &2 zpow (tile_k s) *
           cw(&2 zpow (tile_k s) * ((aa + bb) / &2 - tile_xmid s))
         <= &8 * cw_tile s x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cw_tile] THEN
  ABBREV_TAC `p = &2 zpow (tile_k(s:int#int#int))` THEN
  SUBGOAL_THEN `&0 < p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&8 * p * c = p * &8 * c`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CW_CLOSE1 THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs p = p` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `p * ((bb - aa) / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* CW_TILE_SMALL_CUBE_INT: |J_k| * peak <= 8 * int_{[aa,bb]} cw_tile s,      *)
(* integrating the ptw bound.                                                *)
let CW_TILE_SMALL_CUBE_INT = prove
 (`!(s:int#int#int) (aa:real) (bb:real).
     aa <= bb /\ &2 zpow (tile_k s) * ((bb - aa) / &2) <= &1
     ==> (bb - aa) * (&2 zpow (tile_k s) *
                      cw(&2 zpow (tile_k s) * ((aa + bb) / &2 - tile_xmid s)))
         <= &8 * real_integral (real_interval[aa,bb]) (cw_tile s)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `peak = &2 zpow (tile_k(s:int#int#int)) *
           cw(&2 zpow (tile_k s) * ((aa + bb) / &2 - tile_xmid s))` THEN
  SUBGOAL_THEN `(bb - aa) * peak =
                real_integral (real_interval[aa,bb]) (\x. peak)`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&8 * real_integral (real_interval[aa,bb]) (cw_tile s) =
    real_integral (real_interval[aa,bb]) (\x. &8 * cw_tile s x)`
   SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
    REWRITE_TAC[CWTILE_INTEGRABLE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_CONST];
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; ETA_AX; CWTILE_INTEGRABLE];
    ASM_MESON_TAC[IN_REAL_INTERVAL; CW_TILE_SMALL_PTW]]);;

(* CW_TILE_DISJ_CUBE_SUM: sum over disjoint cubes of int_{J_k} cw_tile s <=  *)
(* 1 (= int_R cw_tile s).                                                    *)
let CW_TILE_DISJ_CUBE_SUM = prove
 (`!(s:int#int#int) (Q:num->bool) (aa:num->real) (bb:num->real).
     FINITE Q /\ (!k. k IN Q ==> aa k < bb k) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j]))
     ==> sum Q (\k. real_integral (real_interval[aa k, bb k]) (cw_tile s))
         <= &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fin")
    (CONJUNCTS_THEN2 (LABEL_TAC "cube") (LABEL_TAC "disj"))) THEN
  SUBGOAL_THEN
   `sum Q (\k. real_integral (real_interval[(aa:num->real) k, bb k])
                             (cw_tile s)) =
    sum (IMAGE (\k. real_interval[(aa:num->real) k, bb k]) Q)
        (\J. real_integral J (cw_tile s))`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\k. real_interval[(aa:num->real) k, bb k]`;
                   `\J:real->bool. real_integral J (cw_tile s)`;
                   `Q:num->bool`] SUM_IMAGE) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FB_JC_INJ THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(cw_tile s has_real_integral
     (sum (IMAGE (\k. real_interval[(aa:num->real) k, bb k]) Q)
          (\J:real->bool. real_integral J (cw_tile s))))
    (UNIONS (IMAGE (\k. real_interval[(aa:num->real) k, bb k]) Q))`
   (LABEL_TAC "hri") THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIONS THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE];
      ASM_MESON_TAC[IN_IMAGE; REAL_INTEGRABLE_INTEGRAL; CWTILE_INTEGRABLE];
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum (IMAGE (\k. real_interval[(aa:num->real) k, bb k]) Q)
        (\J:real->bool. real_integral J (cw_tile s)) =
    real_integral
      (UNIONS (IMAGE (\k. real_interval[(aa:num->real) k, bb k]) Q))
      (cw_tile s)`
   SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (:real) (cw_tile s)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRAL_SUBSET_LE; SUBSET_UNIV;
     HAS_REAL_INTEGRAL_INTEGRABLE; CW_TILE_INTEGRABLE_UNIV;
     REAL_LT_IMP_LE; CW_TILE_POS];
    REWRITE_TAC[CW_TILE_INT_UNIV; REAL_LE_REFL]]);;

(* The per-tile factor B for small cubes: for disjoint cubes with            *)
(* 2^tk(bb-aa)/2 <= 1, sum_k (bb-aa) * peak_k <= 8, where peak_k = 2^tk      *)
(* cw(2^tk((aa+bb)/2 - xs)).                                                 *)
let EST14_FACTORB = prove
 (`!(s:int#int#int) (Q:num->bool) (aa:num->real) (bb:num->real).
     FINITE Q /\ (!k. k IN Q ==> aa k < bb k) /\
     (!k. k IN Q ==> &2 zpow (tile_k s) * ((bb k - aa k) / &2) <= &1) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j]))
     ==> sum Q (\k. (bb k - aa k) *
                    (&2 zpow (tile_k s) *
                     cw(&2 zpow (tile_k s) *
                        ((aa k + bb k) / &2 - tile_xmid s)))) <= &8`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fin")
    (CONJUNCTS_THEN2 (LABEL_TAC "cube")
    (CONJUNCTS_THEN2 (LABEL_TAC "small") (LABEL_TAC "disj")))) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Q (\k. &8 * real_integral (real_interval[(aa:num->real) k, bb k])
                                  (cw_tile s))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CW_TILE_SMALL_CUBE_INT THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&8 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        ASM_SIMP_TAC[CW_TILE_DISJ_CUBE_SUM]];
      REAL_ARITH_TAC]]);;

(* EST14_FACTORB_ABS: EST14_FACTORB with abs(bb-aa) in the summand (= plain  *)
(* on Q where aa<bb; SUM_EQ).                                                *)
let EST14_FACTORB_ABS = prove
 (`!(s:int#int#int) (Q:num->bool) (aa:num->real) (bb:num->real).
     FINITE Q /\ (!k. k IN Q ==> aa k < bb k) /\
     (!k. k IN Q ==> &2 zpow (tile_k s) * ((bb k - aa k) / &2) <= &1) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j]))
     ==> sum Q (\k. abs(bb k - aa k) *
                    (&2 zpow (tile_k s) *
                     cw(&2 zpow (tile_k s) *
                        ((aa k + bb k) / &2 - tile_xmid s)))) <= &8`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum Q (\k. abs(bb k - aa k) *
               (&2 zpow (tile_k s) *
                cw(&2 zpow (tile_k s) *
                   (((aa:num->real) k + bb k) / &2 - tile_xmid s)))) =
    sum Q (\k. (bb k - aa k) *
               (&2 zpow (tile_k s) *
                cw(&2 zpow (tile_k s) *
                   (((aa:num->real) k + bb k) / &2 - tile_xmid s))))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
     DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `aa(k:num) < bb k` MP_TAC THENL
      [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC EST14_FACTORB THEN ASM_REWRITE_TAC[]);;

(* CW_INTEGER_FULL_SUM: if |y - M| <= 1/2, the sum of cw(y - n) over any     *)
(* finite set of integers n is at most 3: the term n = M is at most 1, and   *)
(* each of the two tails n < M and n > M is at most 1 (CW_INTEGER_SHIFT_TAIL *)
(* with m = 1).                                                              *)
let CW_INTEGER_FULL_SUM = prove
 (`!(S:int->bool) y M.
      FINITE S /\ abs(y - real_of_int M) <= &1 / &2
      ==> sum S (\n. cw(y - real_of_int n)) <= &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:int->bool`; `\n:int. cw(y - real_of_int n)`;
    `M:int`] SUM_INT_TRICHOTOMY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
    `l <= &1 /\ c <= &1 /\ r <= &1 ==> l + c + r <= &3`) THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`{n:int | n IN S /\ n < M}`; `y:real`; `M:int`;
     `1`] CW_INTEGER_SHIFT_TAIL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT];
        X_GEN_TAC `n:int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        SUBGOAL_THEN `abs(n - M:int) = M - n` SUBST1_TAC THENL
          [ASM_INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
        SUBGOAL_THEN `&(num_of_int(M - n:int)) = M - n` SUBST1_TAC THENL
         [MATCH_MP_TAC INT_OF_NUM_OF_INT; ALL_TAC] THEN
        ASM_INT_ARITH_TAC];
      CONV_TAC(NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)];
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum {M:int} (\n:int. cw(y - real_of_int n))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_SUBSET_SIMPLE; FINITE_SING; SUBSET; IN_ELIM_THM;
       IN_SING; REAL_LT_IMP_LE; CW_POS];
      REWRITE_TAC[SUM_SING; CW_LE_1]];
    MP_TAC(ISPECL [`{n:int | n IN S /\ M < n}`; `y:real`; `M:int`;
      `1`] CW_INTEGER_SHIFT_TAIL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT];
        X_GEN_TAC `n:int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        SUBGOAL_THEN `abs(n - M:int) = n - M` SUBST1_TAC THENL
          [ASM_INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
        SUBGOAL_THEN `&(num_of_int(n - M:int)) = n - M` SUBST1_TAC THENL
         [MATCH_MP_TAC INT_OF_NUM_OF_INT; ALL_TAC] THEN
        ASM_INT_ARITH_TAC];
      CONV_TAC(NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV)]]);;

(* The full sum over positions of cw at one scale of a tree is at most 3     *)
(* (TILE_XMID_SCALE_S and SUM_IMAGE, using the injectivity of FST(SND s)).   *)
let CW_TREE_SCALE_FULL = prove
 (`!(A:(int#int#int)->bool) (k:int) (c:real) (u:int#int#int) (M:int).
     FINITE A /\ abs((&2 zpow k * c - &1 / &2) - real_of_int M) <= &1 / &2 /\
     (!s. s IN A ==> tile_k s = k /\ tile_le s u)
     ==> sum A (\s. cw(&2 zpow k * (c - tile_xmid s))) <= &3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum A (\s:int#int#int. cw(&2 zpow k * (c - tile_xmid s))) =
    sum A (\s:int#int#int. cw((&2 zpow k * c - &1 / &2) -
      real_of_int(FST(SND s))))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `tile_k (s:int#int#int) = k` ASSUME_TAC THENL
      [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `s:int#int#int` TILE_XMID_SCALE_S) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:int#int#int. FST(SND s)`;
                 `\n:int. cw((&2 zpow k * c - &1 / &2) - real_of_int n)`;
                 `A:(int#int#int)->bool`] SUM_IMAGE) THEN
  REWRITE_TAC[o_DEF] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:int#int#int`; `q:int#int#int`] THEN
     MP_TAC(ISPECL [`A:(int#int#int)->bool`; `k:int`; `u:int#int#int`;
                   `p:int#int#int`; `q:int#int#int`]
                     TILE_TREE_FST_SND_INJ) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th])] THEN
  MATCH_MP_TAC CW_INTEGER_FULL_SUM THEN
  EXISTS_TAC `M:int` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]);;

(* ZPOW_FIBER_SQ: (2 zpow(ktop - &jj))^2 = (2 zpow ktop)^2 * inv(4^jj).      *)
(* Scale-square factoring.                                                   *)
let ZPOW_FIBER_SQ = prove
 (`!ktop:int jj:num.
     (&2 zpow (ktop - &jj)) pow 2 = (&2 zpow ktop) pow 2 * inv(&4 pow jj)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `~(&2:real = &0)` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ZPOW_SUB] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_ZPOW_POW] THEN
  SUBGOAL_THEN `(&2 pow jj) pow 2 = &4 pow jj` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    REWRITE_TAC[real_div]]);;

(* EST14_FA_FIBER: the bound 3 KK (2 zpow ktop)^2 inv(4^jj) for the sum of   *)
(* the quotients of the weighted Cauchy-Schwarz bound over one fiber, the    *)
(* tiles with tile_k s = ktop - jj.  On the fiber                            *)
(*   (2 zpow tile_k s)^2 = (2 zpow ktop)^2 inv(4^jj)                         *)
(* (ZPOW_FIBER_SQ); this factor is pulled out, and CW_TREE_SCALE_FULL bounds *)
(* the sum of the cw terms by 3.                                             *)
let EST14_FA_FIBER = prove
 (`!(Tt:(int#int#int)->bool) (u:int#int#int) (ktop:int) (cc:real)
    (KK:real) (jj:num) (Mj:int).
     FINITE Tt /\ &0 <= KK /\
     (!s. s IN Tt ==> tile_k s <= ktop /\ tile_le s u) /\
     abs((&2 zpow (ktop - &jj) * cc - &1 / &2) - real_of_int Mj) <= &1 / &2
     ==> sum {s | s IN Tt /\ num_of_int(ktop - tile_k s) = jj}
             (\s. KK * (&2 zpow (tile_k s)) pow 2 *
                  cw(&2 zpow (tile_k s) * (cc - tile_xmid s)))
         <= (&3 * KK * (&2 zpow ktop) pow 2) * inv(&4 pow jj)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum {s | s IN Tt /\ num_of_int(ktop - tile_k s) = jj}
        (\s:int#int#int. KK * (&2 zpow (tile_k s)) pow 2 *
                         cw(&2 zpow (tile_k s) * (cc - tile_xmid s))) =
    sum {s | s IN Tt /\ num_of_int(ktop - tile_k s) = jj}
        (\s:int#int#int. (KK * (&2 zpow ktop) pow 2 * inv(&4 pow jj)) *
                         cw(&2 zpow (ktop - &jj) * (cc - tile_xmid s)))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:int#int#int` THEN
     REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
       SUBGOAL_THEN `tile_k(s:int#int#int) = ktop - &jj` SUBST1_TAC THENL
     [SUBGOAL_THEN `&(num_of_int(ktop - tile_k(s:int#int#int))) =
                     ktop - tile_k s` MP_TAC THENL
       [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
         SUBGOAL_THEN `tile_k(s:int#int#int) <= ktop` MP_TAC THENL
         [ASM_SIMP_TAC[]; INT_ARITH_TAC];
        ASM_ARITH_TAC];
      ALL_TAC] THEN REWRITE_TAC[ZPOW_FIBER_SQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(&3 * KK * z) * i = (KK * z * i) * &3`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2; REAL_LE_INV_EQ] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN REAL_ARITH_TAC;
    MP_TAC(ISPECL
     [`{s | s IN Tt /\ num_of_int(ktop - tile_k s) = jj}`;
      `ktop - &jj:int`; `cc:real`; `u:int#int#int`;
        `Mj:int`] CW_TREE_SCALE_FULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT];
        X_GEN_TAC `s:int#int#int` THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        CONJ_TAC THENL
         [SUBGOAL_THEN `&(num_of_int(ktop - tile_k(s:int#int#int))) =
                         ktop - tile_k s` MP_TAC THENL
           [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
             SUBGOAL_THEN `tile_k(s:int#int#int) <= ktop` MP_TAC THENL
             [ASM_SIMP_TAC[]; INT_ARITH_TAC];
            ASM_ARITH_TAC];
          ASM_SIMP_TAC[]]];
      DISCH_THEN ACCEPT_TAC]]);;

(* EST14_MOF_EXISTS: the per-fiber M-alignment function always exists        *)
(* (nearest integer, INTEGER_ROUND).                                         *)
let EST14_MOF_EXISTS = prove
 (`!Kc:int cc:real. ?Mof:num->int.
     !jj. abs((&2 zpow (Kc - &jj) * cc - &1 / &2) -
       real_of_int(Mof jj)) <= &1 / &2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `jj:num` THEN
  MP_TAC(ISPEC `&2 zpow (Kc - &jj) * cc - &1 / &2` INTEGER_ROUND) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `int_of_real n` THEN
  SUBGOAL_THEN `real_of_int(int_of_real n) = n` SUBST1_TAC THENL
   [ASM_MESON_TAC[int_rep]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* EST14_FA_PERCUBE: the per-cube total of factor A for small cubes.  The    *)
(* sum over all tiles s of the tree (of scale at most ktop) of               *)
(*   KK (2 zpow tk)^2 cw(2 zpow tk (cc - tile_xmid s))                       *)
(* is at most 6 KK (2 zpow ktop)^2.  This follows from FAR_GEOM_REINDEX_Q    *)
(* over the fibers jj = num_of_int(ktop - tile_k s): each fiber contributes  *)
(* at most 3 KK (2 zpow ktop)^2 inv(4^jj) (EST14_FA_FIBER), and the          *)
(* geometric sum with ratio 1/4 gives the factor 2.                          *)
let EST14_FA_PERCUBE = prove
 (`!(Tt:(int#int#int)->bool) (u:int#int#int) (ktop:int) (cc:real) (KK:real).
     FINITE Tt /\ &0 <= KK /\
     (!s. s IN Tt ==> tile_k s <= ktop /\ tile_le s u)
     ==> sum Tt (\s. KK * (&2 zpow (tile_k s)) pow 2 *
                     cw(&2 zpow (tile_k s) * (cc - tile_xmid s)))
         <= &6 * KK * (&2 zpow ktop) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ktop:int`; `cc:real`] EST14_MOF_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_TAC `Mof:num->int`) THEN
  MP_TAC(ISPECL
   [`Tt:(int#int#int)->bool`;
    `\s:int#int#int. num_of_int(ktop - tile_k s)`;
    `\s:int#int#int. KK * (&2 zpow (tile_k s)) pow 2 *
                     cw(&2 zpow (tile_k s) * (cc - tile_xmid s))`;
    `&3 * KK * (&2 zpow ktop) pow 2`] FAR_GEOM_REINDEX_Q) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2; REAL_LT_IMP_LE; CW_POS];
      ASM_MESON_TAC[EST14_FA_FIBER]];
    REAL_ARITH_TAC]);;

(* EST14_QUOT: the quotient A^2/w of the weighted Cauchy-Schwarz bound for   *)
(* small cubes.  If w = wd p cwv and                                         *)
(*   A^2 <= C tau^2 p (wd^2 (p wd/2 cwv)^2)                                  *)
(* (the form of the per-tile bound EST14_TILE_SQ), then                      *)
(*   A^2/w <= (C/4 tau^2 wd^3) p^2 cwv,                                      *)
(* the summand of EST14_FA_PERCUBE with KK = C/4 tau^2 wd^3.                 *)
let EST14_QUOT = prove
 (`!A2 p wd cwv C tau.
     &0 < p /\ &0 < wd /\ &0 < cwv /\ &0 <= C /\ &0 <= A2 /\
     A2 <= C * tau pow 2 * p * (wd pow 2 * (p * wd / &2 * cwv) pow 2)
     ==> A2 / (wd * p * cwv)
         <= (C / &4 * tau pow 2 * wd pow 3) * p pow 2 * cwv`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < wd * p * cwv` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C * tau pow 2 * p * (wd pow 2 * (p * wd / &2 * cwv) pow 2)` THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_FIELD);;

(* SMALL_FROM_SCALECUT: the scale condition tile_k s <= Kc implies the       *)
(* smallness condition                                                       *)
(*   2 zpow (tile_k s) (wd/2) <= 1,                                          *)
(* given the bound 2 zpow Kc (wd/2) <= 1 for the cube (ZPOW2_MONOE).         *)
let SMALL_FROM_SCALECUT = prove
 (`!ts Kc:int. !wd:real. ts <= Kc /\ &2 zpow Kc * (wd / &2) <= &1 /\ &0 <= wd
     ==> &2 zpow ts * (wd / &2) <= &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 zpow Kc * (wd / &2)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[ZPOW2_MONOE];
    ASM_REAL_ARITH_TAC]);;

(* EST14_FA_PERCUBE_CAP: EST14_FA_PERCUBE (with ktop = Kc) together with the *)
(* bound 2 zpow Kc (wd/2) <= 1 for the cube gives the per-cube bound         *)
(*   D_k = 6 Cc tau^2 wd,                                                    *)
(* linear in wd: (2 zpow Kc)^2 wd^2 <= 4 turns the factor wd^3 into wd.      *)
let EST14_FA_PERCUBE_CAP = prove
 (`!(Tt:(int#int#int)->bool) (u:int#int#int) (Kc:int) (cc:real) (Cc:real)
    (tau:real) (wd:real).
     FINITE Tt /\ &0 <= Cc /\ &0 < wd /\
     &2 zpow Kc * (wd / &2) <= &1 /\
     (!s. s IN Tt ==> tile_k s <= Kc /\ tile_le s u)
     ==> sum Tt (\s. (Cc / &4 * tau pow 2 * wd pow 3) *
                     (&2 zpow (tile_k s)) pow 2 *
                     cw(&2 zpow (tile_k s) * (cc - tile_xmid s)))
         <= &6 * Cc * tau pow 2 * wd`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tt:(int#int#int)->bool`; `u:int#int#int`; `Kc:int`;
                 `cc:real`; `Cc / &4 * tau pow 2 * wd pow 3`]
         EST14_FA_PERCUBE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= c ==> x <= a ==> x <= c`) THEN
  SUBGOAL_THEN `&0 < &2 zpow Kc` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 zpow Kc) pow 2 * wd pow 2 <= &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `(&2 zpow Kc) pow 2 * wd pow 2 = (&2 zpow Kc * wd) pow 2`
     SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2:real) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&6 * (Cc / &4 * tau pow 2 * wd pow 3) * (&2 zpow Kc) pow 2 =
    (&6 / &4 * Cc * tau pow 2 * wd) * ((&2 zpow Kc) pow 2 * wd pow 2)`
   SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&6 / &4 * Cc * tau pow 2 * wd) * &4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_FIELD]);;

(* EST14_W_NONNEG and EST14_W_POS: the weight                                *)
(*   abs(bb-aa) 2^tk cw(2^tk((aa+bb)/2 - xs))                                *)
(* of the weighted Cauchy-Schwarz bound for small cubes is nonnegative, and  *)
(* positive if aa < bb.                                                      *)
let EST14_W_NONNEG = prove
 (`!(s:int#int#int) (aa:real) (bb:real).
     &0 <= abs(bb - aa) * (&2 zpow (tile_k s)) *
           cw(&2 zpow (tile_k s) * ((aa + bb) / &2 - tile_xmid s))`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
     MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_POS]]);;

let EST14_W_POS = prove
 (`!(s:int#int#int) (aa:real) (bb:real).
     aa < bb
     ==> &0 < abs(bb - aa) * (&2 zpow (tile_k s)) *
              cw(&2 zpow (tile_k s) * ((aa + bb) / &2 - tile_xmid s))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; REWRITE_TAC[CW_POS]]);;

(* The per-cube factor A hypothesis of CH_EST14_SMALL, from the per-tile     *)
(* bound on A^2: EST14_QUOT bounds A^2/w by the quotient, and                *)
(* EST14_FA_PERCUBE_CAP sums it.                                             *)
let EST14_FACTORA_PERCUBE = prove
 (`!(Tt:(int#int#int)->bool) (t:int#int#int) (u:int#int#int) (b:real->real)
    (aa:real) (bb:real) (Kc:int) (tau:real) (C:real).
     &0 <= C /\ &0 <= tau /\ aa < bb /\ FINITE Tt /\
     &2 zpow Kc * ((bb - aa) / &2) <= &1 /\
     (!s. s IN Tt ==> tile_ler s t /\ tile_k s <= Kc /\ tile_le s u) /\
     (!s. s IN Tt
          ==> norm(integral (IMAGE lift (real_interval[aa,bb]))
                     (\z. Cx(b(drop z)) *
                          cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                              phi_sigma s carleson_phi (drop z)))) pow 2
              <= C * tau pow 2 * (&2 zpow tile_k s) *
                 ((bb - aa) pow 2 *
                  ((&2 zpow tile_k s * (bb - aa) / &2) *
                   cw(&2 zpow tile_k s *
                      ((aa + bb) / &2 - tile_xmid s))) pow 2))
     ==> sum Tt
             (\s. norm(integral (IMAGE lift (real_interval[aa, bb]))
                    (\z. Cx(b(drop z)) *
                         cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                             phi_sigma s carleson_phi (drop z)))) pow 2 /
                  (abs(bb - aa) * (&2 zpow (tile_k s)) *
                   cw(&2 zpow (tile_k s) * ((aa + bb) / &2 - tile_xmid s))))
         <= &6 * C * tau pow 2 * (bb - aa)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Tt (\s:int#int#int. (C / &4 * tau pow 2 * (bb - aa) pow 3) *
                            (&2 zpow (tile_k s)) pow 2 *
                            cw(&2 zpow (tile_k s) *
                               ((aa + bb) / &2 - tile_xmid s)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs(bb - aa) = bb - aa` SUBST1_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC EST14_QUOT THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CW_POS];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_LE_POW_2];
      FIRST_X_ASSUM(MP_TAC o SPEC `s:int#int#int` o
        check(fun th -> let c = concl th in is_forall c &&
              (can (find_term (fun u -> u = `phi_sigma`)) c))) THEN
      ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC EST14_FA_PERCUBE_CAP THEN
    MAP_EVERY EXISTS_TAC [`u:int#int#int`; `Kc:int`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

(* The per-cube factor A bound in exactly the form of the hypothesis of      *)
(* CH_EF_ASSEMBLE_COND used in CH_EST14_SMALL (from EST14_FACTORA_PERCUBE).  *)
let EST14_FA_PERCUBE_ASSEMBLE = prove
 (`!(P:(int#int#int)->bool) (t:int#int#int) (Q:num->bool) (b:real->real)
    (aa:num->real) (bb:num->real) (Kc:num->int) (tau:real) (C:real) (k:num).
     &0 <= C /\ &0 <= tau /\ FINITE P /\ k IN Q /\
     (!k. k IN Q ==> aa k < bb k) /\
     (!k. k IN Q ==> &2 zpow (Kc k) * ((bb k - aa k) / &2) <= &1) /\
     (!(bR:real->real) (s:int#int#int) tt (a:real) bd (ta:real).
        bR absolutely_real_integrable_on (real_interval[a,bd]) /\
        real_integral (real_interval[a,bd]) bR = &0 /\
        real_integral (real_interval[a,bd]) (\x. abs(bR x)) <=
          &2 * ta * (bd - a) /\
        &0 <= ta /\ tile_ler s tt /\ a <= bd /\
        &2 zpow tile_k s * ((bd - a) / &2) <= &1
        ==> norm(integral (IMAGE lift (real_interval[a,bd]))
                   (\z. Cx(bR(drop z)) *
                        cnj(cexp(--(ii * Cx(tile_ymid tt) * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z)))) pow 2
            <= C * ta pow 2 * (&2 zpow tile_k s) *
               ((bd - a) pow 2 *
                ((&2 zpow tile_k s * (bd - a) / &2) *
                 cw(&2 zpow tile_k s *
                    ((a + bd) / &2 - tile_xmid s))) pow 2)) /\
     (!k. k IN Q
          ==> b absolutely_real_integrable_on (real_interval[aa k, bb k]) /\
              real_integral (real_interval[aa k, bb k]) b = &0 /\
              real_integral (real_interval[aa k, bb k]) (\x. abs(b x)) <=
                &2 * tau * (bb k - aa k))
     ==> sum {s | s IN {s | s IN P /\ tile_ler s t} /\ tile_k s <= Kc k}
             (\s. norm(integral (IMAGE lift (real_interval[aa k, bb k]))
                    (\z. Cx(b(drop z)) *
                         cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                             phi_sigma s carleson_phi (drop z)))) pow 2 /
                  (abs(bb k - aa k) * (&2 zpow (tile_k s)) *
                   cw(&2 zpow (tile_k s) *
                      ((aa k + bb k) / &2 - tile_xmid s))))
         <= &6 * C * tau pow 2 * (bb k - aa k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EST14_FACTORA_PERCUBE THEN
  MAP_EVERY EXISTS_TAC [`t:int#int#int`; `(Kc:num->int) k`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[FINITE_RESTRICT];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[IN_ELIM_THM; TILE_LER_IMP_LE];
    X_GEN_TAC `s:int#int#int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL [`b:real->real`; `s:int#int#int`;
                                   `t:int#int#int`; `(aa:num->real) k`;
                                   `(bb:num->real) k`; `tau:real`] o
      check(fun th -> is_forall(concl th) &&
            (can (find_term (fun u -> u = `phi_sigma`)) (concl th)))) THEN
    DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_MESON_TAC[SMALL_FROM_SCALECUT; REAL_SUB_LE; REAL_LT_IMP_LE]]]);;

(* The tree energy of the small cubes (|J_k| <= 2|I_s|, i.e. tile_k s <= Kc  *)
(* k):                                                                       *)
(*   sum_{s in tree} (sum_{k: tile_k s <= Kc k} |<b_k,phi_s>|)^2             *)
(*      <= 96 C tau^2 R,                                                     *)
(* by the weighted Cauchy-Schwarz bound CH_EF_ASSEMBLE_COND with A =         *)
(* norm(int_sk) and weight w_sk = abs(bb-aa) 2^tk cw(2^tk((aa+bb)/2 -        *)
(* xmid)).  Factor B is EST14_FACTORB_ABS and factor A is                    *)
(* EST14_FA_PERCUBE_ASSEMBLE (D_k = 6 C tau^2 |J_k|: a sum over positions at *)
(* each scale and a geometric sum over scales), with sum_k D_k <= 12 C tau^2 *)
(* R; C is the constant of EST14_TILE_SQ.                                    *)
let CH_EST14_SMALL = prove
 (`?Cd2. &0 <= Cd2 /\
    !(P:(int#int#int)->bool) (t:int#int#int) (Q:num->bool) (b:real->real)
     (aa:num->real) (bb:num->real) (Kc:num->int) (tau:real) (R:real).
     FINITE P /\ FINITE Q /\ &0 <= tau /\ &0 < R /\
     (!s. s IN P ==> tile_ler s t) /\
     (!k. k IN Q ==> aa k < bb k) /\
     (!k. k IN Q
          ==> b absolutely_real_integrable_on (real_interval[aa k, bb k]) /\
              real_integral (real_interval[aa k, bb k]) b = &0 /\
              real_integral (real_interval[aa k, bb k]) (\x. abs(b x)) <=
                &2 * tau * (bb k - aa k)) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j])) /\
     (!k. k IN Q ==> &2 zpow (Kc k) * ((bb k - aa k) / &2) <= &1) /\
     sum Q (\k. bb k - aa k) <= &2 * R
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. (sum {k | k IN Q /\ tile_k s <= Kc k}
                    (\k. norm(integral (IMAGE lift (real_interval[aa k, bb k]))
                         (\z. Cx(b(drop z)) *
                              cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                                  phi_sigma s carleson_phi (drop z)))))) pow 2)
         <= Cd2 * tau pow 2 * R`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e14"))
    EST14_TILE_SQ THEN
  EXISTS_TAC `&96 * C` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`Q:num->bool`; `{s | s IN P /\ tile_ler s t}`;
    `\(s:int#int#int) (k:num). norm(integral
        (IMAGE lift (real_interval[(aa:num->real) k, bb k]))
        (\z. Cx((b:real->real)(drop z)) *
             cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                 phi_sigma s carleson_phi (drop z))))`;
    `\(s:int#int#int) (k:num). abs(bb k - aa k) * (&2 zpow (tile_k s)) *
        cw(&2 zpow (tile_k s) * ((aa k + bb k) / &2 - tile_xmid s))`;
    `\(s:int#int#int) (k:num). tile_k s <= (Kc:num->int) k`;
    `\k:num. &6 * C * tau pow 2 * (bb k - aa k)`;
    `&8`; `&12 * C * tau pow 2 * R`] CH_EF_ASSEMBLE_COND) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[FINITE_RESTRICT];
      REAL_ARITH_TAC;
      (* 0<=A *) REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[EST14_W_NONNEG];
      ASM_SIMP_TAC[EST14_W_POS];
      (* factor B                                                            *)
      X_GEN_TAC `s:int#int#int` THEN
        STRIP_TAC THEN
      MATCH_MP_TAC EST14_FACTORB_ABS THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT];
        ASM_SIMP_TAC[IN_ELIM_THM];
        X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC SMALL_FROM_SCALECUT THEN EXISTS_TAC `(Kc:num->int) k` THEN
        REPEAT CONJ_TAC THENL
         [ASM_SIMP_TAC[]; ASM_SIMP_TAC[];
           ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE]];
        ASM_SIMP_TAC[IN_ELIM_THM]];
      (* factor A                                                            *)
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`P:(int#int#int)->bool`; `t:int#int#int`;
                       `Q:num->bool`; `b:real->real`;
                       `aa:num->real`; `bb:num->real`; `Kc:num->int`;
                       `tau:real`; `C:real`; `k:num`]
                      EST14_FA_PERCUBE_ASSEMBLE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[];
        DISCH_THEN ACCEPT_TAC];
      SUBGOAL_THEN
       `sum Q (\k. &6 * C * tau pow 2 * (bb k - aa k)) =
        (&6 * C * tau pow 2) * sum Q (\k:num. bb k - aa k)`
       SUBST1_TAC THENL
       [ASM_SIMP_TAC[SUM_LMUL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&6 * C * tau pow 2) * (&2 * R)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
      REAL_ARITH_TAC]);;

(* CH_TREE_ENERGY_2CASE: a two-case split of the tree energy, used for the   *)
(* bad part (as in Grafakos-Tao-Terwilleger) with the small cubes, where     *)
(* |J_k| <= 2|I_s|, and the large cubes.  If the energies of the cubes with  *)
(* sm s k and of those with ~sm s k are at most Es and El, then              *)
(*   sum_s (sum_Q A s k)^2 <= 3 Es + 3 El                                    *)
(* (CH_TREE_ENERGY_3CASE with an empty third case).                          *)
let CH_TREE_ENERGY_2CASE = prove
 (`!(Tt:(int#int#int)->bool) (Q:num->bool) (A:(int#int#int)->num->real)
    (sm:(int#int#int)->num->bool) (Es:real) (El:real).
     FINITE Tt /\ FINITE Q /\
     sum Tt (\s. (sum {k | k IN Q /\ sm s k} (\k. A s k)) pow 2) <= Es /\
     sum Tt (\s. (sum {k | k IN Q /\ ~sm s k} (\k. A s k)) pow 2) <= El
     ==> sum Tt (\s. (sum Q (\k. A s k)) pow 2) <= &3 * Es + &3 * El`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Tt:(int#int#int)->bool`; `Q:num->bool`;
                 `A:(int#int#int)->num->real`; `sm:(int#int#int)->num->bool`;
                 `\(s:int#int#int) (k:num). ~sm s k`;
                 `\(s:int#int#int) (k:num). F`; `Es:real`; `El:real`;
                 `&0`] CH_TREE_ENERGY_3CASE) THEN
  ASM_REWRITE_TAC[REAL_ARITH
    `&3 * Es + &3 * El + &3 * &0 = &3 * Es + &3 * El`] THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [CONV_TAC TAUT;
    CONV_TAC TAUT;
    SUBGOAL_THEN `{k | F} = ({}:num->bool)` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES;
      REAL_ARITH `&0 pow 2 = &0`; SUM_0; REAL_LE_REFL]]);;

(* The tree energy of the bad part: combining the small cubes (tile_k s <=   *)
(* Kc k, CH_EST14_SMALL) and the large cubes (Kc k < tile_k s,               *)
(* CH_EST15_LARGE) by CH_TREE_ENERGY_2CASE gives                             *)
(*   sum_s (sum_Q A s k)^2 <= C tau^2 R                                      *)
(* with C = 3 Cs + 3 Cl, where A s k = norm(integral (IMAGE lift J_k) ...).  *)
let CH_CZ_TREE_ENERGY = prove
 (`?C. &0 <= C /\
    !(P:(int#int#int)->bool) (t:int#int#int) (Q:num->bool) (b:real->real)
     (Ff:real->bool) (Om:real->bool) (ypt:int#int#int->real)
     (aa:num->real) (bb:num->real) (Kc:num->int) (tau:real) (R:real)
     (Ad:real) (Bd:real).
     FINITE P /\ FINITE Q /\ &0 <= tau /\ &0 < R /\ real_measurable
       Ff /\ real_measurable Om /\
     (!s. s IN P ==> tile_ler s t) /\
     (!s. s IN P ==> Ad <= tile_xmid s - &2 zpow (--(tile_k s)) / &2 /\
                     tile_xmid s + &2 zpow (--(tile_k s)) / &2 <= Bd) /\
     (!s. s IN P ==> abs(ypt s - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
                     &0 <= hl_maximal (\uu. if uu IN Ff
                       then &1 else &0) (ypt s) /\
                     hl_maximal (\uu. if uu IN Ff then &1
                       else &0) (ypt s) <= tau) /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) + tau * (if x
       IN Om then &1 else &0)) /\
     (!k. k IN Q ==> aa k < bb k /\ Ad <= aa k /\ bb k <= Bd /\ inv(&2 zpow
       (Kc k)) <= bb k - aa k) /\
     (!k. k IN Q
          ==> b absolutely_real_integrable_on (real_interval[aa k, bb k]) /\
              real_integral (real_interval[aa k, bb k]) b = &0 /\
              real_integral (real_interval[aa k, bb k]) (\x. abs(b x)) <=
                &2 * tau * (bb k - aa k)) /\
     (!s k. k IN Q
          ==> (\z. Cx(b(drop z)) *
                   cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                       phi_sigma s carleson_phi (drop z)))
              integrable_on (IMAGE lift (real_interval[aa k, bb k])) /\
              (\x. abs(b x) * cw_tile s x) real_integrable_on
                (real_interval[aa k, bb k]) /\
              (\x. abs(b x) * cw_tile s x) real_integrable_on
                {x | (if tile_xmid s < aa k then aa k - tile_xmid s
                      else tile_xmid s - bb k)
                     <= abs(x - tile_xmid s)} /\
              (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
              (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
                real_integrable_on (:real) /\
              (\x. (if x IN Om then &1 else &0) * cw_tile s x)
                real_integrable_on (:real)) /\
     (!s k. s IN P /\ k IN Q /\ Kc k < tile_k s
            ==> (bb k <= tile_xmid s - &2 zpow (--(tile_k s)) / &2 \/
                 tile_xmid s + &2 zpow (--(tile_k s)) / &2 <= aa k)) /\
     (!s k. s IN P /\ k IN Q /\ Kc k < tile_k s
            ==> Kc k <= tile_k s /\ Ad <= aa k - &2 zpow (--(tile_k s)) / &2 /\
                bb k + &2 zpow (--(tile_k s)) / &2 <= Bd) /\
     (!i j. i IN Q /\ j IN Q /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j])) /\
     (!k. k IN Q ==> &2 zpow (Kc k) * ((bb k - aa k) / &2) <= &1) /\
     sum Q (\k. bb k - aa k) <= &2 * R
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. (sum Q
                    (\k. norm(integral (IMAGE lift (real_interval[aa k, bb k]))
                         (\z. Cx(b(drop z)) *
                              cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                                  phi_sigma s carleson_phi (drop z)))))) pow 2)
         <= C * tau pow 2 * R`,
  X_CHOOSE_THEN `Cs:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "small"))
    CH_EST14_SMALL THEN
  X_CHOOSE_THEN `Cl:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "large"))
    CH_EST15_LARGE THEN
  EXISTS_TAC `&3 * Cs + &3 * Cl` THEN
  CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{s | s IN P /\ tile_ler s t}`; `Q:num->bool`;
    `\(s:int#int#int) (k:num). norm(integral
        (IMAGE lift (real_interval[(aa:num->real) k, bb k]))
        (\z. Cx((b:real->real)(drop z)) *
             cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                 phi_sigma s carleson_phi (drop z))))`;
    `\(s:int#int#int) (k:num). tile_k s <= (Kc:num->int) k`;
    `(Cs:real) * tau pow 2 * R`;
    `(Cl:real) * tau pow 2 * R`] CH_TREE_ENERGY_2CASE) THEN
  REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      (* LARGE: ~sm s k = ~(tile_k s <= Kc k) = Kc k < tile_k s via          *)
      (* INT_NOT_LE                                                          *)
      REWRITE_TAC[INT_NOT_LE] THEN
      USE_THEN "large" (fun th -> MATCH_MP_TAC(SPECL
        [`P:(int#int#int)->bool`; `t:int#int#int`;
         `Q:num->bool`; `b:real->real`;
         `Ff:real->bool`; `Om:real->bool`; `ypt:int#int#int->real`;
         `aa:num->real`; `bb:num->real`; `Kc:num->int`; `tau:real`; `R:real`;
         `Ad:real`; `Bd:real`] th)) THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`s:int#int#int`;`k:num`] o
        check(fun th -> is_forall(concl th) &&
          free_in `(aa:num->real)` (concl th) &&
          can(find_term(fun u->is_const u && fst(dest_const u)="int_le"))
             (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    MATCH_MP_TAC(REAL_ARITH
      `&3 * a + &3 * c = D ==> x <= &3 * (a) + &3 * (c) ==> x <= D`) THEN
    REAL_ARITH_TAC]);;

(* Pointwise bounds for the bad parts of the modulated indicators cos(yt.)   *)
(* 1_Ff and sin(yt.) 1_Ff: |b x| <= 1_Ff x + tau 1_Om x.                     *)

(* Convergence of the per-tile partial sums: if A s k >= 0 and the partial   *)
(* squares are uniformly bounded, sum Tt (\s. (sum(0..N) A s k)^2) <= M for  *)
(* all N, then for each tile s in Tt there is a limit L s with sum(0..N) A s *)
(* k --> L s and every partial sum <= L s.  For fixed s0 the partial sums    *)
(* are increasing and bounded by sqrt M, hence convergent                    *)
(* (CONVERGENT_BOUNDED_INCREASING).                                          *)

(* Per-tile partial sums are monotone increasing (nonneg terms).             *)
let CH_PARTIAL_INCREASING = prove
 (`!(A:num->real) m n. (!k. &0 <= A k) /\ m <= n
     ==> sum(0..m) A <= sum(0..n) A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_DIFF; IN_NUMSEG] THEN
  ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;

(* A single-tile partial-square bound: for s0 in Tt, every partial sum <=    *)
(* sqrt M.                                                                   *)
let CH_PARTIAL_SQRT_BOUND = prove
 (`!(Tt:(int#int#int)->bool) (A:(int#int#int)->num->real) (s0:int#int#int) M N.
     FINITE Tt /\ s0 IN Tt /\ (!s k. &0 <= A s k) /\
     sum Tt (\s. (sum(0..N)(\k. A s k)) pow 2) <= M
     ==> sum(0..N)(\k. A s0 k) <= sqrt M`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RSQRT THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Tt (\s. (sum(0..N)(\k. (A:(int#int#int)->num->real) s k)) pow 2)` THEN
  MP_TAC(ISPECL
   [`\s. (sum(0..N)(\k. (A:(int#int#int)->num->real) s k)) pow 2`;
    `sum Tt (\s. (sum(0..N)(\k. (A:(int#int#int)->num->real) s k)) pow 2)`;
    `Tt:(int#int#int)->bool`] SUM_POS_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_POW_2];
    ASM_SIMP_TAC[]]);;

(* Existence of the per-tile limits L, with the partial sums tending to L    *)
(* and every partial sum <= L.                                               *)
let CH_UNIFORM_ENERGY_CONVERGES = prove
 (`!(Tt:(int#int#int)->bool) (A:(int#int#int)->num->real) (M:real).
     FINITE Tt /\ (!s k. &0 <= A s k) /\
     (!N. sum Tt (\s. (sum(0..N)(\k. A s k)) pow 2) <= M)
     ==> ?L. (!s. s IN Tt
                  ==> ((\N. sum(0..N)(\k. A s k)) ---> L s) sequentially) /\
             (!s N. s IN Tt ==> sum(0..N)(\k. A s k) <= L s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?L. !s:int#int#int. s IN Tt
        ==> ((\N. sum(0..N)(\k. A s k)) ---> L s) sequentially /\
            (!N. sum(0..N)(\k. A s k) <= L s)`
   MP_TAC THENL
   [ALL_TAC;
    MESON_TAC[]] THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `s0:int#int#int` THEN DISCH_TAC THEN
  (* the per-tile partial-sum sequence converges                             *)
  MP_TAC(ISPECL [`\N. sum(0..N)(\k. (A:(int#int#int)->num->real) s0 k)`;
                 `sqrt M`] CONVERGENT_BOUNDED_INCREASING) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_PARTIAL_INCREASING];
      X_GEN_TAC `N:num` THEN
      SUBGOAL_THEN `&0 <= sum(0..N)(\k:num. A (s0:int#int#int) k)`
        ASSUME_TAC THENL
       [ASM_SIMP_TAC[SUM_POS_LE_NUMSEG]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= b ==> abs x <= b`) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CH_PARTIAL_SQRT_BOUND THEN
      EXISTS_TAC `Tt:(int#int#int)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(X_CHOOSE_TAC `l:real`) THEN EXISTS_TAC `l:real` THEN
  ASM_REWRITE_TAC[] THEN
  (* every partial sum <= l : partials increasing, l is the limit            *)
  X_GEN_TAC `N:num` THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_LE) THEN
  MAP_EVERY EXISTS_TAC
   [`\M:num. sum(0..N)(\k. (A:(int#int#int)->num->real) s0 k)`;
    `\M:num. sum(0..M)(\k. (A:(int#int#int)->num->real) s0 k)`] THEN
  ASM_REWRITE_TAC[REALLIM_CONST; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CH_PARTIAL_INCREASING THEN ASM_REWRITE_TAC[]);;

(* From a uniform bound on the energies truncated in the cubes (sum_s        *)
(* (sum_{k<=N} A s k)^2 <= M for every N), the convergence of the partial    *)
(* sums over cubes to L s, and the per-tile bound norm(int_UNIV Cx b cnj     *)
(* psi_s) <= L s, to the bound sum_s norm(int_UNIV ...)^2 <= M               *)
(* (CH_TREE_ENERGY_LIMIT and CH_EF_FROM_PERTILE).                            *)

let CH_EF_UNIFORM_TO_LIMIT = prove
 (`!(P:(int#int#int)->bool) t (b:real->real) yt (A:(int#int#int)->num->real)
    (L:(int#int#int)->real) (M:real).
     FINITE {s | s IN P /\ tile_ler s t} /\
     (!s k. &0 <= A s k) /\
     (!s. s IN {s | s IN P /\ tile_ler s t}
          ==> ((\N. sum (0..N) (\k. A s k)) ---> L s) sequentially) /\
     (!s. s IN {s | s IN P /\ tile_ler s t}
          ==> norm(integral (:real^1) (\z. Cx(b(drop z)) *
                cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                    phi_sigma s carleson_phi (drop z))))
              <= L s) /\
     (!N. sum {s | s IN P /\ tile_ler s t}
              (\s. (sum (0..N) (\k. A s k)) pow 2) <= M)
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(integral (:real^1) (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2) <= M`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CH_EF_FROM_PERTILE THEN
  MAP_EVERY EXISTS_TAC [`L:(int#int#int)->real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; NORM_POS_LE];
    (* sum L^2 <= M via CH_TREE_ENERGY_LIMIT                                 *)
    MATCH_MP_TAC(ISPECL
     [`{s | s IN P /\ tile_ler s t}`;
      `\(N:num) (s:int#int#int). sum (0..N) (\k. A s k)`;
      `L:(int#int#int)->real`; `M:real`] CH_TREE_ENERGY_LIMIT) THEN
    ASM_REWRITE_TAC[]]);;

(* The factor ii drops out of the imaginary bad pairing: norm(integral (ii * *)
(* Cx(bI(drop z)) * cnj psi_s)) = norm(integral (Cx(bI(drop z)) * cnj        *)
(* psi_s)) (INTEGRAL_COMPLEX_LMUL, COMPLEX_NORM_MUL, COMPLEX_NORM_II).       *)

let CH_BADIP_II_NORM = prove
 (`!yt (bI:real->real) (s:int#int#int).
     (\z. Cx(bI(drop z)) *
          cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
              phi_sigma s carleson_phi (drop z)))
       integrable_on (:real^1)
     ==> norm(integral (:real^1)
            (\z. (ii * Cx(bI(drop z))) *
                 cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                     phi_sigma s carleson_phi (drop z))))
         = norm(integral (:real^1)
            (\z. Cx(bI(drop z)) *
                 cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                     phi_sigma s carleson_phi (drop z))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `integral (:real^1)
      (\z. (ii * Cx(bI(drop z))) *
           cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
               phi_sigma s carleson_phi (drop z))) =
    ii * integral (:real^1)
      (\z. Cx(bI(drop z)) *
           cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
               phi_sigma s carleson_phi (drop z)))`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL
     [`\z:real^1. Cx(bI(drop z)) *
                  cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                      phi_sigma s carleson_phi (drop z))`;
      `(:real^1)`; `ii`] INTEGRAL_COMPLEX_LMUL) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_II; REAL_MUL_LID]);;

(* The tree sum of CH_BADIP_REIM_SPLIT: the bad-cube energy                  *)
(*   B = sum_{s in P, tile_ler s t}                                          *)
(*         norm(carleson_ip(cexp(ii yt.)(Cx bR+ii Cx bI),s))^2               *)
(* splits into the two single-family energies, B <= 2 * Ef[bR] + 2 *         *)
(* Ef[biI], where Ef[bR] = sum_s norm(int_UNIV Cx bR cnj psi_s)^2 and        *)
(* Ef[biI] = sum_s norm(int_UNIV (ii Cx bI) cnj psi_s)^2.                    *)

let CH_BADENERGY_REIM_SPLIT = prove
 (`!yt (bR:real->real) (bI:real->real) (P:(int#int#int)->bool) (t:int#int#int).
     FINITE P /\
     (!s. s IN P /\ tile_ler s t
          ==> (\z. Cx(bR(drop z)) *
                   cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                       phi_sigma s carleson_phi (drop z)))
                integrable_on (:real^1) /\
              (\z. (ii * Cx(bI(drop z))) *
                   cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                       phi_sigma s carleson_phi (drop z)))
                integrable_on (:real^1))
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. cexp(ii * Cx yt * Cx x) *
                         (Cx(bR x) + ii * Cx(bI x))) s) pow 2)
         <= &2 * sum {s | s IN P /\ tile_ler s t}
                   (\s. norm(integral (:real^1)
                          (\z. Cx(bR(drop z)) *
                               cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                                   phi_sigma s carleson_phi (drop z)))) pow 2)
          + &2 * sum {s | s IN P /\ tile_ler s t}
                   (\s. norm(integral (:real^1)
                          (\z. (ii * Cx(bI(drop z))) *
                               cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                                   phi_sigma s carleson_phi (drop z))))
                        pow 2)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {s | s IN P /\ tile_ler s t}
      (\s. &2 * norm(integral (:real^1)
                 (\z. Cx(bR(drop z)) *
                      cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                          phi_sigma s carleson_phi (drop z)))) pow 2
         + &2 * norm(integral (:real^1)
                 (\z. (ii * Cx(bI(drop z))) *
                      cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                          phi_sigma s carleson_phi (drop z)))) pow 2)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_BADIP_REIM_SPLIT; SUM_LE; FINITE_RESTRICT; IN_ELIM_THM];
    ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; FINITE_RESTRICT; REAL_LE_REFL]]);;

(* Integrability of the single-family pairings Cx bR cnj psi and (ii Cx bI)  *)
(* cnj psi (from CH_B_CNJ_W_INTEGRABLE), and the arithmetic that combines    *)
(* the energy bounds Ef[bR], Ef[bI] <= Cf tau^2 R of the two real families   *)
(* into the bound (Cmod + 8 Cf) tau^2 R for the near-tree energy             *)
(* (CH_BADENERGY_REIM_SPLIT, CH_BADIP_II_NORM, CH_TREE_NEAR_MODULO_BAD).     *)

let CH_BADPAIR_R_INTEGRABLE = prove
 (`!yt (bR:real->real) (s:int#int#int).
     bR absolutely_real_integrable_on (:real)
     ==> (\z. Cx(bR(drop z)) *
              cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                  phi_sigma s carleson_phi (drop z)))
           integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`yt:real`; `s:int#int#int`] CH_PSI_BOUNDED) THEN
  DISCH_THEN(X_CHOOSE_TAC `Mb:real`) THEN
  MATCH_MP_TAC CH_B_CNJ_W_INTEGRABLE THEN
  EXISTS_TAC `Mb:real` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_CX_DROP_ABSINT];
    REWRITE_TAC[CH_PSI_MEAS];
    ASM_REWRITE_TAC[]]);;

let CH_BADPAIR_iI_INTEGRABLE = prove
 (`!yt (bI:real->real) (s:int#int#int).
     bI absolutely_real_integrable_on (:real)
     ==> (\z. (ii * Cx(bI(drop z))) *
              cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                  phi_sigma s carleson_phi (drop z)))
           integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC INTEGRABLE_COMPLEX_LMUL THEN
  ASM_SIMP_TAC[CH_BADPAIR_R_INTEGRABLE]);;

let CH_BADENERGY_ARITH = prove
 (`!Cmod Cf A B W. &0 <= Cf /\ A <= Cf * W /\ B <= Cf * W /\ &0 <= W
     ==> Cmod * W + &2 * (&2 * A + &2 * B) <= (Cmod + &8 * Cf) * W`,
  REAL_ARITH_TAC);;

(* UNIONS_COND_EMPTY: dropping the empty members of the conditional family   *)
(* {if P n then g n else {}} leaves UNIONS {g n | P n}.                      *)

let UNIONS_COND_EMPTY = prove
 (`!(g:num->real^1->bool) P.
     UNIONS {(if P n then g n else {}) | n IN (:num)} =
     UNIONS {g n | n | P n}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^1` THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Versions of the enumeration bounds for families with pairwise negligible  *)
(* intersections instead of disjoint ones: closed dyadic cubes may share     *)
(* endpoints, so the Calderon-Zygmund decomposition only provides negligible *)
(* intersections (CZ_CLOSED_CUBE_NEGLIGIBLE_INTER).                          *)
(* ------------------------------------------------------------------------- *)

(* DEDUP_PAIRWISE_NEG: replacing the repeated members of a family by {}      *)
(* preserves pairwise negligible intersections: {} INTER x = {} is           *)
(* negligible, and the members kept at two distinct indices are distinct     *)
(* sets, so their intersection is negligible by hypothesis.                  *)
let DEDUP_PAIRWISE_NEG = prove
 (`!e:num->real^N->bool.
     (!i j. ~(e i = e j) ==> negligible (e i INTER e j))
     ==> pairwise
          (\i j. negligible
                   ((if (?m. m < i /\ e m = e i) then {} else e i) INTER
                    (if (?m. m < j /\ e m = e j) then {} else e j)))
          (:num)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pairwise] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
  COND_CASES_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY] THEN
  SUBGOAL_THEN `i:num < j \/ j < i` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* The enumeration pairing bound for a family with pairwise negligible       *)
(* intersections.                                                            *)
let CH_ENUM_PAIRING_BOUND_NEG = prove
 (`!(f:real^M->real^N) (e:num->real^M->bool) B.
     (!i j. ~(e i = e j) ==> negligible (e i INTER e j)) /\
     (!n. f integrable_on (e n)) /\
     f absolutely_integrable_on (UNIONS {e n | n IN (:num)}) /\
     (!N. sum (0..N) (\i. norm(integral (e i) f)) <= B)
     ==> norm(integral (UNIONS {e n | n IN (:num)}) f) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`f:real^M->real^N`;
     `\n. if (?m. m < n /\ (e:num->real^M->bool) m = e n)
          then ({}:real^M->bool) else e n`;
     `B:real`] CH_BADPAIR_SERIES_BOUND) THEN
  BETA_TAC THEN
  SUBGOAL_THEN `UNIONS {(if (?m. m < n /\ (e:num->real^M->bool) m = e n)
                         then ({}:real^M->bool) else e n) | n IN (:num)} =
                UNIONS {(e:num->real^M->bool) n | n IN (:num)}`
    SUBST1_TAC THENL [REWRITE_TAC[DEDUP_UNIONS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_ON_EMPTY];
    ASM_SIMP_TAC[DEDUP_PAIRWISE_NEG];
    X_GEN_TAC `N:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= B ==> a <= B`) THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[DEDUP_INT_NORM_LE]]);;

(* The bound for the bad pairing over an enumerated family with pairwise     *)
(* negligible intersections (general yt).                                    *)
let CH_BADIP_ENUM_BOUND_NEG = prove
 (`!(yt:real) (bR:real->real) (bI:real->real)
    (Om:real->bool) (e:num->real^1->bool)
    (s:int#int#int) (B:real).
     bR absolutely_real_integrable_on (:real) /\
     bI absolutely_real_integrable_on (:real) /\
     (!x. ~(x IN Om) ==> bR x = &0) /\ (!x. ~(x IN Om) ==> bI x = &0) /\
     IMAGE lift Om = UNIONS {e n | n IN (:num)} /\
     lebesgue_measurable (IMAGE lift Om) /\
     (!n. lebesgue_measurable (e n)) /\
     (!i j. ~(e i = e j) ==> negligible (e i INTER e j)) /\
     (!n. e n SUBSET IMAGE lift Om) /\
     (!N. sum (0..N)
            (\i. norm(integral (e i)
                   (\z. (Cx(bR(drop z)) + ii * Cx(bI(drop z))) *
                        cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                            phi_sigma s carleson_phi (drop z))))) <= B)
     ==> norm(carleson_ip
                (\x. cexp(ii * Cx yt * Cx x) *
                     (Cx(bR x) + ii * Cx(bI x))) s) <= B`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[CH_BADIP_DEMOD] THEN
  MP_TAC(ISPECL
   [`bR:real->real`; `bI:real->real`;
    `\z:real^1. cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                    phi_sigma s carleson_phi (drop z))`;
    `Om:real->bool`] CH_INT_SUPPORT_OM_CPLX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`yt:real`; `bR:real->real`; `bI:real->real`; `s:int#int#int`]
    CH_BADPAIR_ABSINT_UNIV) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "fabs") THEN
  MATCH_MP_TAC CH_ENUM_PAIRING_BOUND_NEG THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
     ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET; SUBSET_UNIV];
    ONCE_REWRITE_TAC[GSYM(ASSUME
      `IMAGE lift Om = UNIONS {e n | n IN (:num)}`)] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^1)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]]);;

(* The energy bound from uniform per-tile bounds, for an enumerated family   *)
(* with pairwise negligible intersections.                                   *)
let CH_EF_FROM_UNIFORM_NEG = prove
 (`!(P:(int#int#int)->bool) t (b:real->real) yt
    (Om:real->bool) (e:num->real^1->bool)
    (M:real).
     FINITE {s | s IN P /\ tile_ler s t} /\
     b absolutely_real_integrable_on (:real) /\
     (!x. ~(x IN Om) ==> b x = &0) /\
     IMAGE lift Om = UNIONS {e n | n IN (:num)} /\
     lebesgue_measurable (IMAGE lift Om) /\
     (!n. lebesgue_measurable (e n)) /\
     (!i j. ~(e i = e j) ==> negligible (e i INTER e j)) /\
     (!n. e n SUBSET IMAGE lift Om) /\
     (!N. sum {s | s IN P /\ tile_ler s t}
            (\s. (sum (0..N)
                   (\k. norm(integral (e k)
                          (\z. Cx(b(drop z)) *
                               cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                                   phi_sigma s carleson_phi (drop z))))))
                 pow 2) <= M)
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(integral (:real^1) (\z. Cx(b(drop z)) *
                    cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2) <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{s | s IN P /\ tile_ler s t}`;
    `\(s:int#int#int) (k:num). norm(integral (e k)
             (\z. Cx(b(drop z)) *
                  cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                      phi_sigma s carleson_phi (drop z))))`;
    `M:real`] CH_UNIFORM_ENERGY_CONVERGES) THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(int#int#int)->real`
   (CONJUNCTS_THEN2 (LABEL_TAC "conv") (LABEL_TAC "ple"))) THEN
  MATCH_MP_TAC CH_EF_UNIFORM_TO_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`\(s:int#int#int) (k:num). norm(integral (e k)
             (\z. Cx(b(drop z)) *
                  cnj(cexp(--(ii * Cx yt * Cx(drop z))) *
                      phi_sigma s carleson_phi (drop z))))`;
    `L:(int#int#int)->real`] THEN
  ASM_REWRITE_TAC[NORM_POS_LE] THEN
  X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`yt:real`; `b:real->real`; `\x:real. &0`;
    `Om:real->bool`; `e:num->real^1->bool`;
    `s:int#int#int`; `(L:(int#int#int)->real) s`] CH_BADIP_ENUM_BOUND_NEG) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_0;
     COMPLEX_MUL_RZERO; COMPLEX_ADD_RID];
    ASM_REWRITE_TAC[CH_BADIP_DEMOD; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]]);;

(* Distinct members of a conditional family {if P n then g n else {}} have   *)
(* negligible intersection if the members g n do (real^1).                   *)
let DISJOINT_COND_EMPTY_NEG = prove
 (`!(g:num->real^1->bool) P.
     (!a b. P a /\ P b /\ ~(g a = g b) ==> negligible (g a INTER g b))
     ==> !i j. ~((if P i then g i else {}) = (if P j then g j else {}))
               ==> negligible ((if P i then g i else {}) INTER
                               (if P j then g j else {}))`,
  ASM_MESON_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY]);;

(* CH_CZ_BOX_EXISTS supplies a bounding box for a finite set of tiles and    *)
(* cubes.  CH_CZ_EF_ENERGY_NEG is the bound for the bad-part energy for a    *)
(* cube family whose lifted images have pairwise negligible intersections    *)
(* (adjacent closed cubes share an endpoint,                                 *)
(* CZ_CLOSED_CUBE_NEGLIGIBLE_INTER), via CH_EF_FROM_UNIFORM_NEG and          *)
(* DISJOINT_COND_EMPTY_NEG.                                                  *)
let CH_CZ_BOX_EXISTS = prove
 (`!(P:(int#int#int)->bool) (Q:num->bool) (aa:num->real) (bb:num->real)
    (xmid:(int#int#int)->real) (tk:(int#int#int)->int).
     FINITE P /\ FINITE Q
     ==> ?Ad Bd.
           (!s. s IN P ==> Ad <= xmid s - &2 zpow (--(tk s)) / &2 /\
                           xmid s + &2 zpow (--(tk s)) / &2 <= Bd) /\
           (!k. k IN Q ==> Ad <= aa k /\ bb k <= Bd) /\
           (!s k. s IN P /\ k IN Q
                  ==> Ad <= aa k - &2 zpow (--(tk s)) / &2 /\
                      bb k + &2 zpow (--(tk s)) / &2 <= Bd)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\s:int#int#int. xmid s - &2 zpow (--(tk s)) / &2`;
                 `P:(int#int#int)->bool`] LOWER_BOUND_FINITE_SET_REAL) THEN
  MP_TAC(ISPECL [`\s:int#int#int. xmid s + &2 zpow (--(tk s)) / &2`;
                 `P:(int#int#int)->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  MP_TAC(ISPECL [`\s:int#int#int. abs(&2 zpow (--(tk s)) / &2)`;
                 `P:(int#int#int)->bool`] UPPER_BOUND_FINITE_SET_REAL) THEN
  MP_TAC(ISPECL [`aa:num->real`; `Q:num->bool`]
    LOWER_BOUND_FINITE_SET_REAL) THEN
  MP_TAC(ISPECL [`bb:num->real`; `Q:num->bool`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `ch:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `cl:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `ah:real`) THEN
  DISCH_THEN(X_CHOOSE_TAC `al:real`) THEN
  MAP_EVERY EXISTS_TAC [`min al (cl - abs m)`; `max ah (ch + abs m)`] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `s:int#int#int`)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num`)) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CH_CZ_EF_ENERGY_NEG = prove
 (`?C. &0 <= C /\
    !(P:(int#int#int)->bool) (t:int#int#int) (b:real->real)
     (Ff:real->bool) (Om:real->bool) (ypt:int#int#int->real) (aa:num->real)
     (bb:num->real) (Kc:num->int) (sel:num->bool) (tau:real) (R:real).
     FINITE P /\ &0 < tau /\ &0 < R /\
     real_measurable Ff /\ real_measurable Om /\
     b absolutely_real_integrable_on (:real) /\
     (!x. ~(x IN Om) ==> b x = &0) /\
     (!s. s IN P ==> tile_ler s t) /\
     (!s. s IN P ==> abs(ypt s - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
                     &0 <= hl_maximal (\uu. if uu IN Ff then &1 else &0)
                                      (ypt s) /\
                     hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s)
                       <= tau) /\
     (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                      tau * (if x IN Om then &1 else &0)) /\
     IMAGE lift Om =
     UNIONS {IMAGE lift (real_interval[aa n, bb n]) | n | sel n} /\
     (!i j. sel i /\ sel j /\
            ~(IMAGE lift (real_interval[aa i, bb i]) =
              IMAGE lift (real_interval[aa j, bb j]))
            ==> negligible (IMAGE lift (real_interval[aa i, bb i]) INTER
                            IMAGE lift (real_interval[aa j, bb j]))) /\
     (!k. sel k ==> aa k < bb k /\ inv(&2 zpow (Kc k)) <= bb k - aa k) /\
     (!k. sel k
          ==> b absolutely_real_integrable_on (real_interval[aa k, bb k]) /\
              real_integral (real_interval[aa k, bb k]) b = &0 /\
              real_integral (real_interval[aa k, bb k]) (\x. abs(b x)) <=
                &2 * tau * (bb k - aa k)) /\
     (!s k. sel k
            ==> (\z. Cx(b(drop z)) *
                     cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                         phi_sigma s carleson_phi (drop z)))
                integrable_on (IMAGE lift (real_interval[aa k, bb k])) /\
                (\x. abs(b x) * cw_tile s x) real_integrable_on
                  (real_interval[aa k, bb k]) /\
                (\x. abs(b x) * cw_tile s x) real_integrable_on
                  {x | (if tile_xmid s < aa k then aa k - tile_xmid s
                        else tile_xmid s - bb k)
                       <= abs(x - tile_xmid s)} /\
                (\x. abs(b x) * cw_tile s x) real_integrable_on (:real) /\
                (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
                  real_integrable_on (:real) /\
                (\x. (if x IN Om then &1 else &0) * cw_tile s x)
                  real_integrable_on (:real)) /\
     (!s k. s IN P /\ sel k /\ Kc k < tile_k s
            ==> (bb k <= tile_xmid s - &2 zpow (--(tile_k s)) / &2 \/
                 tile_xmid s + &2 zpow (--(tile_k s)) / &2 <= aa k)) /\
     (!s k. s IN P /\ sel k /\ Kc k < tile_k s ==> Kc k <= tile_k s) /\
     (!i j. sel i /\ sel j /\ ~(i = j)
            ==> real_negligible(real_interval[aa i, bb i] INTER
                                real_interval[aa j, bb j])) /\
     (!k. sel k ==> &2 zpow (Kc k) * ((bb k - aa k) / &2) <= &1) /\
     (!N. sum {n | n IN 0..N /\ sel n} (\k. bb k - aa k) <= &2 * R)
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(integral (:real^1)
                    (\z. Cx(b(drop z)) *
                         cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                             phi_sigma s carleson_phi (drop z)))) pow 2)
         <= C * tau pow 2 * R`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cz"))
    CH_CZ_TREE_ENERGY THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CH_EF_FROM_UNIFORM_NEG THEN
  MAP_EVERY EXISTS_TAC
   [`Om:real->bool`;
    `\n:num. if sel n then IMAGE lift (real_interval[(aa:num->real) n, bb n])
             else {}`] THEN
  REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[UNIONS_COND_EMPTY];
    MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
      ASM_REWRITE_TAC[GSYM REAL_MEASURABLE_MEASURABLE];
    GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_EMPTY; IMAGE_LIFT_REAL_INTERVAL] THEN
      MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
        REWRITE_TAC[MEASURABLE_INTERVAL];
    MATCH_MP_TAC DISJOINT_COND_EMPTY_NEG THEN FIRST_X_ASSUM MATCH_ACCEPT_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN
      MATCH_MP_TAC (SET_RULE
        `(?m:num. sel m /\ e = f m)
         ==> e SUBSET UNIONS {f m | m | sel m}`) THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `N:num` THEN
      SUBGOAL_THEN
       `sum {s | s IN P /\ tile_ler s t}
            (\s. (sum (0..N)
                   (\k. norm(integral
                      (if sel k
                       then IMAGE lift (real_interval[(aa:num->real) k, bb k])
                       else {})
                      (\z. Cx(b(drop z)) *
                           cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                               phi_sigma s carleson_phi (drop z)))))) pow 2) =
        sum {s | s IN P /\ tile_ler s t}
            (\s. (sum {k | k IN 0..N /\ sel k}
                   (\k. norm(integral
                      (IMAGE lift (real_interval[(aa:num->real) k, bb k]))
                      (\z. Cx(b(drop z)) *
                           cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                               phi_sigma s carleson_phi (drop z)))))) pow 2)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
        X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
        ASM_REWRITE_TAC[INTEGRAL_EMPTY; NORM_0];
        ALL_TAC] THEN
      (* the box Ad, Bd for the tiles of P and the cubes {k IN 0..N /\ sel *)
      (* k} (CH_CZ_BOX_EXISTS), then CH_CZ_TREE_ENERGY                       *)
      SUBGOAL_THEN `FINITE {k | k IN 0..N /\ sel k}` ASSUME_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
      MP_TAC(ISPECL [`P:(int#int#int)->bool`; `{k | k IN 0..N /\ sel k}`;
                     `aa:num->real`; `bb:num->real`; `tile_xmid`; `tile_k`]
             CH_CZ_BOX_EXISTS) THEN
      ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `Ad:real` (X_CHOOSE_THEN `Bd:real`
          STRIP_ASSUME_TAC)) THEN
        USE_THEN "cz" (fun th -> MATCH_MP_TAC(SPECL
          [`P:(int#int#int)->bool`; `t:int#int#int`;
           `{k | k IN 0..N /\ sel k}`; `b:real->real`;
           `Ff:real->bool`; `Om:real->bool`; `ypt:int#int#int->real`;
           `aa:num->real`; `bb:num->real`; `Kc:num->int`; `tau:real`; `R:real`;
           `Ad:real`; `Bd:real`] th)) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
        REPEAT(FIRST[GEN_TAC; DISCH_TAC]) THEN
        TRY(ASM_REAL_ARITH_TAC) THEN
        TRY(REPEAT CONJ_TAC THEN
            ASM_SIMP_TAC[IN_ELIM_THM] THEN NO_TAC) THEN
        (* the remaining per-(s,k) and per-k facts are instances of          *)
        (* hypotheses                                                        *)
        TRY(FIRST_X_ASSUM(fun th ->
              if is_forall(concl th) && not(free_in `Ad:real` (concl th))
              then (fun g -> (MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]) g)
              else failwith "skip"))]);;

(* ========================================================================= *)
(* The dyadic Calderon-Zygmund decomposition CH_CZ_PRODUCER: maximal         *)
(* stopping cubes, their density, the good and bad parts, and the comparison *)
(* of the stopping set with the superlevel set of the maximal function.      *)
(* ========================================================================= *)

(* Every point of the dyadic stopping set lies in a maximal stopping cube.   *)
(* Here stops k n means tau * 2^k < int_{dyho k n} abs(h).  For x in some    *)
(* stopping cell, CZ_MAXCUBE_SELECT gives the greatest stopping scale kmax;  *)
(* the cell of x at that scale stops, and no strictly coarser dyadic cell    *)
(* containing it stops.                                                      *)
let CZ_POINT_MAXCELL = prove
 (`!h tau x.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau /\
     (?k. tau * &2 zpow k <
          real_integral (dyho k (@q. x IN dyho k q)) (\x. abs(h x)))
     ==> ?k n. x IN dyho k n /\
               tau * &2 zpow k < real_integral (dyho k n) (\x. abs(h x)) /\
               (!k' n'. k < k' /\ dyho k n SUBSET dyho k' n'
                        ==> ~(tau * &2 zpow k' <
                              real_integral (dyho k' n') (\x. abs(h x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real->real`; `tau:real`; `x:real`] CZ_MAXCUBE_SELECT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kmax:int`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gr"))) THEN
  MAP_EVERY EXISTS_TAC [`kmax:int`; `(@q. x IN dyho kmax q):int`] THEN
  SUBGOAL_THEN `x IN dyho kmax (@q. x IN dyho kmax q)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DYHO_COVERS_POINT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`k':int`; `n':int`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `x IN dyho k' n'` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dyho k' n' = dyho k' (@q. x IN dyho k' q)` SUBST1_TAC THENL
   [ASM_MESON_TAC[DYHO_POINT_UNIQUE];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `k':int <= kmax` MP_TAC THENL
   [ASM_SIMP_TAC[]; ASM_ARITH_TAC]);;

(* The dyadic stopping set Om is the union of the maximal stopping cubes     *)
(* (stopping cells dyho k n contained in no strictly coarser stopping cell). *)
let CZ_OM_EQ_UNION_MAXCELLS = prove
 (`!h tau.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau
     ==> {x | ?k. tau * &2 zpow k <
                  real_integral (dyho k (@q. x IN dyho k q)) (\x. abs(h x))} =
         UNIONS { dyho k n | k,n |
                  tau * &2 zpow k < real_integral (dyho k n) (\x. abs(h x)) /\
                  (!k' n'. k < k' /\ dyho k n SUBSET dyho k' n'
                           ==> ~(tau * &2 zpow k' <
                                 real_integral (dyho k' n')
                                               (\x. abs(h x)))) }`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_ELIM_THM; UNIONS_GSPEC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real->real`; `tau:real`; `x:real`] CZ_POINT_MAXCELL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:int`
      (X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`k:int`; `n:int`] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[DYHO_POINT_UNIQUE]]);;

(* A maximal stopping cube dyho k n satisfies int_{dyho k n} |h| <= 2 tau    *)
(* 2^k, i.e. avg_J |h| <= 2 tau: its parent dyho (k+1) (n div 2) is a        *)
(* strictly coarser cell (DYHO_PARENT), which by maximality does not stop    *)
(* (CZ_MAXCUBE_DENSITY).                                                     *)
let CZ_MAXCELL_DENSITY = prove
 (`!h tau k n.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau /\
     tau * &2 zpow k < real_integral (dyho k n) (\x. abs(h x)) /\
     (!k' n'. k < k' /\ dyho k n SUBSET dyho k' n'
              ==> ~(tau * &2 zpow k' <
                    real_integral (dyho k' n') (\x. abs(h x))))
     ==> real_integral (dyho k n) (\x. abs(h x)) <= &2 * tau * &2 zpow k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CZ_MAXCUBE_DENSITY THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k + &1:int`; `n div &2:int`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [INT_ARITH_TAC; REWRITE_TAC[DYHO_PARENT]];
    REWRITE_TAC[REAL_NOT_LT]]);;

(* The comparison with centred intervals, used to show that |h(x)| <= tau    *)
(* almost everywhere off Om.  A dyadic cell dyho k n containing x lies in    *)
(* the centred interval [x - 2^k, x + 2^k] of twice its length, so avg_cell  *)
(* |h - h(x)| <= 2 * avg_{[x-L,x+L]} |h - h(x)|, and the centred averages    *)
(* tend to 0 almost everywhere (ABSOLUTELY_INTEGRABLE_LEBESGUE_POINTS).      *)
let DYHO_IN_CENTERED = prove
 (`!k n x. x IN dyho k n
           ==> dyho k n SUBSET real_interval[x - &2 zpow k, x + &2 zpow k]`,
  REWRITE_TAC[dyho; IN_ELIM_THM; SUBSET; IN_REAL_INTERVAL] THEN
  ASM_REAL_ARITH_TAC);;

let REAL_LEBESGUE_AVERAGE = prove
 (`!(h:real->real).
     (!a b. h absolutely_real_integrable_on real_interval[a,b])
     ==> ?k. real_negligible k /\
             !x. ~(x IN k)
                 ==> ((\r. inv(&2 * r) *
                           real_integral (real_interval[x - r, x + r])
                                         (\y. abs(h y - h x)))
                      ---> &0) (atreal (&0) within {t | &0 < t})`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `lift o h o drop`
    LEBESGUE_DENSITY_THEOREM_INTEGRAL_NORM_CBALL) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[IMAGE_LIFT_REAL_INTERVAL; LIFT_DROP;
     ABSOLUTELY_REAL_INTEGRABLE_ON];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kv:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `IMAGE drop kv` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[real_negligible; GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift x`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LIFT_DROP; IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[LIM_WITHIN; REALLIM_WITHINREAL; DIST_0; IN_ELIM_THM] THEN
  DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `lift r`) THEN
  REWRITE_TAC[LIFT_DROP; NORM_LIFT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `measure (cball (lift x,r)) = &2 * r` ASSUME_TAC THENL
   [REWRITE_TAC[BALL_1; MEASURE_INTERVAL_1; DROP_SUB; DROP_ADD; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `integral (cball(lift x, r))
             (\y. lift(norm((lift o h o drop) y - (lift o h o drop)(lift x))))
    = lift(real_integral (real_interval[x - r, x + r]) (\y. abs(h y - h x)))`
   ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(\y. lift(norm((lift o h o drop) y - (lift o h o drop)(lift x))))
      = lift o (\y. abs(h y - h x)) o drop`
     SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP; GSYM LIFT_SUB; NORM_LIFT];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `cball(lift x, r) = IMAGE lift(real_interval[x - r, x + r])`
     SUBST1_TAC THENL
     [REWRITE_TAC[BALL_1; IMAGE_LIFT_REAL_INTERVAL; GSYM LIFT_SUB;
                  GSYM LIFT_ADD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(\y. abs(h y - h x)) real_integrable_on real_interval[x - r, x + r]`
     ASSUME_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
       ABSOLUTELY_REAL_INTEGRABLE_ABS; ABSOLUTELY_REAL_INTEGRABLE_SUB;
       ABSOLUTELY_REAL_INTEGRABLE_CONST];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[MATCH_MP REAL_INTEGRAL th]) THEN
    REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LIFT_CMUL; NORM_LIFT; REAL_SUB_RZERO]);;

(* The average of abs(g) over a dyadic cell containing x is at most twice    *)
(* the average over the centred interval [x-2^k, x+2^k] (DYHO_IN_CENTERED;   *)
(* the measures are 2^k and 2 * 2^k).                                        *)
let DYHO_AVG_LE_CENTERED = prove
 (`!(g:real->real) k n x.
     x IN dyho k n /\
     (\y. abs(g y)) real_integrable_on (dyho k n) /\
     (\y. abs(g y)) real_integrable_on
       (real_interval[x - &2 zpow k, x + &2 zpow k])
     ==> real_integral (dyho k n) (\y. abs(g y)) / &2 zpow k
         <= &2 * (real_integral (real_interval[x - &2 zpow k, x + &2 zpow k])
                                (\y. abs(g y)) / (&2 * &2 zpow k))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * real_integral (real_interval [x - &2 zpow k,x + &2 zpow k])
         (\y. abs (g y)) / (&2 * &2 zpow k)
    = real_integral (real_interval [x - &2 zpow k,x + &2 zpow k])
      (\y. abs (g y)) / &2 zpow k`
   SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_SUBSET_LE; DYHO_IN_CENTERED; REAL_ABS_POS];
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* An enumeration of int#int by num, used to index the maximal dyadic cubes  *)
(* (scale k, index n): an injective and surjective pair:num->int#int         *)
(* (INTINT_ENUM), with aa m = real_of_int(SND(pair m)) * 2 zpow (FST(pair    *)
(* m)) and so on.                                                            *)
let INTINT_COUNTABLE = prove
 (`COUNTABLE (:int#int)`,
  SIMP_TAC[COUNTABLE_CROSS; INT_COUNTABLE; GSYM CROSS_UNIV]);;

let INTINT_INFINITE = prove
 (`INFINITE (:int#int)`,
  REWRITE_TAC[INFINITE] THEN DISCH_TAC THEN
  MP_TAC int_INFINITE THEN REWRITE_TAC[INFINITE] THEN
  SUBGOAL_THEN `(:int) = IMAGE FST (:int#int)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `i:int` THEN EXISTS_TAC `(i,&0:int):int#int` THEN REWRITE_TAC[];
    ASM_SIMP_TAC[FINITE_IMAGE]]);;

let INTINT_ENUM = prove
 (`?pair:num->int#int. (!m n. pair m = pair n ==> m = n)
    /\ (!kn. ?m. pair m = kn)`,
  MP_TAC(ISPEC `(:int#int)` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
  REWRITE_TAC[INTINT_COUNTABLE; INTINT_INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `pair:num->int#int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `pair:num->int#int` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `kn:int#int` THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `\s. (kn:int#int) IN s`) THEN
  REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Off the dyadic stopping set, |h(x)| <= tau almost everywhere.             *)
(* CZ_H_LE_TAU_OFF_OM: at a Lebesgue point x lying in no stopping dyadic     *)
(* cell (every dyadic cell dyho k n containing x has average of |h| at most  *)
(* tau) we have |h(x)| <= tau; the proof lets the scale 2 zpow k tend to 0   *)
(* (REAL_ARCH_POW2).                                                         *)
(* ========================================================================= *)

(* --- Integrability of h on a dyadic cell (subset of a closed interval).    *)

let PERSCALE_ABSINT = prove
 (`!(h:real->real) k n.
     (!a b. h absolutely_real_integrable_on real_interval[a,b])
     ==> h absolutely_real_integrable_on (dyho k n)`,
  ASM_MESON_TAC[ABSINT_ON_LEBMEAS_SUBSET; DYHO_SUBSET_CLOSED;
    REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE; DYHO_MEASURABLE]);;

(* --- Constant integral / integrability over a dyadic cell (measure 2^k).   *)

let DYHO_INTEGRAL_CONST = prove
 (`!k n c. real_integral (dyho k n) (\y. c) = c * &2 zpow k`,
  SIMP_TAC[REAL_INTEGRAL_CONST_MEASURABLE; DYHO_MEASURABLE; DYHO_MEASURE]);;

let DYHO_INTEGRABLE_CONST = prove
 (`!k n c. (\y. c) real_integrable_on (dyho k n)`,
  SIMP_TAC[REAL_INTEGRABLE_ON_CONST_MEASURABLE; DYHO_MEASURABLE]);;

(* --- h - constant is absolutely integrable on every closed interval.       *)

let SUB_CONST_ABSINT_IVL = prove
 (`!(h:real->real) c a b.
     (!a b. h absolutely_real_integrable_on real_interval[a,b])
     ==> (\y. h y - c) absolutely_real_integrable_on real_interval[a,b]`,
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
    ABSOLUTELY_REAL_INTEGRABLE_CONST]);;

let CENTERED_ABSINT = prove
 (`!(h:real->real) x r.
     (!a b. h absolutely_real_integrable_on real_interval[a,b])
     ==> (\y. abs(h y - h x)) real_integrable_on real_interval[x - r, x + r]`,
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
    ABSOLUTELY_REAL_INTEGRABLE_ABS; SUB_CONST_ABSINT_IVL]);;

(* --- Per-scale integral inequality: |h(x)| * measure(cell) is bounded by   *)
(* the mass of |h| plus the mass of |h - h(x)| over the cell.                *)

let PERSCALE_INEQ = prove
 (`!(h:real->real) k n x.
     (!a b. h absolutely_real_integrable_on real_interval[a,b])
     ==> abs(h x) * &2 zpow k <=
         real_integral (dyho k n) (\y. abs(h y)) +
         real_integral (dyho k n) (\y. abs(h y - h x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y. abs(h y)) real_integrable_on (dyho k n)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
     ABSOLUTELY_REAL_INTEGRABLE_ABS; PERSCALE_ABSINT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\y. abs(h y - h x)) real_integrable_on
                 (dyho k n)` ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ABS THEN
    MATCH_MP_TAC PERSCALE_ABSINT THEN
    ASM_SIMP_TAC[SUB_CONST_ABSINT_IVL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV)
    [GSYM(SPECL [`k:int`; `n:int`; `abs(h(x:real))`] DYHO_INTEGRAL_CONST)] THEN
  MP_TAC(ISPECL [`\y:real. abs(h y)`; `\y:real. abs(h y - h x)`; `dyho k n`]
    REAL_INTEGRAL_ADD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; DYHO_INTEGRABLE_CONST] THEN
  REAL_ARITH_TAC);;

(* --- Centered-average domination for g = h - h(x) (DYHO_AVG_LE_CENTERED)   *)

let DYHO_AVG_CENTERED_HX = prove
 (`!(h:real->real) x k nk.
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     x IN dyho k nk
     ==> real_integral (dyho k nk) (\y. abs(h y - h x)) / &2 zpow k <=
         &2 * real_integral (real_interval[x - &2 zpow k, x + &2 zpow k])
                (\y. abs(h y - h x)) / (&2 * &2 zpow k)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DYHO_AVG_LE_CENTERED THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ABS THEN
    MATCH_MP_TAC PERSCALE_ABSINT THEN
    ASM_SIMP_TAC[SUB_CONST_ABSINT_IVL];
    ASM_SIMP_TAC[CENTERED_ABSINT]]);;

let TWO_C_DIV = prove
 (`!C Z:real. &2 * C / (&2 * Z) = &2 * (inv(&2 * Z) * C)`,
  REAL_ARITH_TAC);;

let PERSCALE_ARITH = prove
 (`!hx Z A B C tau:real.
     &0 < Z /\
     hx * Z <= A + B /\
     A <= tau * Z /\
     B / Z <= &2 * C / (&2 * Z)
     ==> hx <= tau + &2 * (inv(&2 * Z) * C)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `hx <= (A + B) / Z` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `A / Z <= tau` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[TWO_C_DIV]) THEN
  REAL_ARITH_TAC);;

(* --- Per-scale key bound: at the (unique) cell of scale k containing x,    *)
(* |h(x)| <= tau + 2 * (centered average of |h - h(x)| at radius 2^k).       *)

let PERSCALE_KEY = prove
 (`!(h:real->real) tau x k.
     &0 < tau /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     (!k n. x IN dyho k n
            ==> real_integral (dyho k n) (\y. abs(h y)) <= tau * &2 zpow k)
     ==> abs(h x) <= tau + &2 * (inv(&2 * &2 zpow k) *
           real_integral (real_interval[x - &2 zpow k, x + &2 zpow k])
             (\y. abs(h y - h x)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `nk = @q. x IN dyho k q` THEN
  SUBGOAL_THEN `x IN dyho k nk` ASSUME_TAC THENL
   [ASM_MESON_TAC[DYHO_COVERS_POINT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC PERSCALE_ARITH THEN
  EXISTS_TAC `real_integral (dyho k nk) (\y. abs(h y))` THEN
  EXISTS_TAC `real_integral (dyho k nk) (\y. abs(h y - h x))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[PERSCALE_INEQ];
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[DYHO_AVG_CENTERED_HX]]);;

(* --- Scale selection: for any d > 0 there is a dyadic scale k with         *)
(* 0 < 2^k < d (take k = --n via REAL_ARCH_POW2).                            *)

let SCALE_SELECT = prove
 (`!d:real. &0 < d ==> ?k. &0 < &2 zpow k /\ &2 zpow k < d`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_TAC `n:num` (SPEC `inv d:real` REAL_ARCH_POW2) THEN
  EXISTS_TAC `--(&n):int` THEN
  SUBGOAL_THEN `&2 zpow (--(&n)) = inv(&2 pow n)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ZPOW_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2 pow n) < inv(inv d)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV2; REAL_LT_INV];
    ASM_SIMP_TAC[REAL_INV_INV]]);;

(* --- Main theorem.                                                         *)

let CZ_H_LE_TAU_OFF_OM = prove
 (`!(h:real->real) tau x.
     &0 < tau /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     ((\r. inv(&2 * r) * real_integral (real_interval[x - r, x + r])
                                       (\y. abs(h y - h x))) ---> &0)
        (atreal (&0) within {t | &0 < t}) /\
     (!k n. x IN dyho k n
            ==> real_integral (dyho k n) (\y. abs(h y)) <= tau * &2 zpow k)
     ==> abs(h x) <= tau`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARLESON_REAL_LE_EPSILON THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_WITHINREAL]) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `k:int` STRIP_ASSUME_TAC
    (MATCH_MP SCALE_SELECT (ASSUME `&0 < d`)) THEN
  MP_TAC(SPECL [`h:real->real`; `tau:real`; `x:real`; `k:int`]
    PERSCALE_KEY) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&2 zpow k`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

(* Dyadic stopping implies a large maximal function: if x lies in a stopping *)
(* dyadic cell (average of |h| greater than tau) and |h| <= 1, then          *)
(* hl_maximal h x > tau, since the closed cell [n2^k, (n+1)2^k] (which       *)
(* differs from dyho k n by an endpoint, REAL_INTEGRAL_SPIKE_SET) is an      *)
(* interval containing x with average greater than tau.  Hence Om SUBSET     *)
(* {hl_maximal h > tau}, and a tile containing a point y with                *)
(* hl_maximal(1_Ff) y <= tau is not contained in Om.                         *)
let CZ_STOP_IMP_MAXIMAL = prove
 (`!h tau k n x.
     x IN dyho k n /\ &0 < tau /\
     (!t. abs(h t) <= &1) /\
     (\t. abs(h t)) real_integrable_on (:real) /\
     tau * &2 zpow k < real_integral (dyho k n) (\t. abs(h t))
     ==> tau < hl_maximal h x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hl_maximal] THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (dyho k n) (\t. abs(h t)) =
    real_integral (real_interval[real_of_int n * &2 zpow k,
                                 (real_of_int n + &1) * &2 zpow k])
                  (\t. abs(h t))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET THEN
     MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{(real_of_int n + &1) * &2 zpow k}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_SING; dyho; SUBSET;
      IN_UNION; IN_DIFF; IN_ELIM_THM;
      IN_REAL_INTERVAL; IN_SING] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `real_integral (dyho k n) (\t. abs(h t)) / &2 zpow k` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_SUP THEN
  MAP_EVERY EXISTS_TAC
   [`&1`; `real_integral (dyho k n) (\t. abs(h t)) / &2 zpow k`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`real_of_int n * &2 zpow k`;
                          `(real_of_int n + &1) * &2 zpow k`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x IN dyho k n` THEN
      REWRITE_TAC[dyho; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ASM_ARITH_TAC;
    REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a:real <= b` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (real_interval[a,b]) (\t. &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
      REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[REAL_INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV];
        ASM_REWRITE_TAC[]];
      ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN ASM_REAL_ARITH_TAC]]);;

(* Density of the bad piece on a selected cube: on the closed cube [n2^k,    *)
(* (n+1)2^k] the bad piece bpiece = h - avg_J h satisfies int_J |bpiece| <=  *)
(* 4 tau 2^k = 4 tau |J| (CZ_BADPIECE_L1 and CZ_MAXCELL_DENSITY); its mean   *)
(* is zero by CZ_BADPIECE_MEANZERO.                                          *)
let CZ_CUBE_BPIECE_DENSITY = prove
 (`!h tau k n.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau /\
     h real_integrable_on (real_interval[real_of_int n * &2 zpow k,
                                         (real_of_int n + &1) * &2 zpow k]) /\
     (\x. abs(h x)) real_integrable_on
       (real_interval[real_of_int n * &2 zpow k,
                      (real_of_int n + &1) * &2 zpow k]) /\
     tau * &2 zpow k < real_integral (dyho k n) (\y. abs(h y)) /\
     (!k' n'. k < k' /\ dyho k n SUBSET dyho k' n'
              ==> ~(tau * &2 zpow k' <
                    real_integral (dyho k' n') (\y. abs(h y))))
     ==> real_integral (real_interval[real_of_int n * &2 zpow k,
                                      (real_of_int n + &1) * &2 zpow k])
           (\x. abs(h x - real_integral
                            (real_interval[real_of_int n * &2 zpow k,
                              (real_of_int n + &1) * &2 zpow k]) h /
                          ((real_of_int n + &1) * &2 zpow k -
                           real_of_int n * &2 zpow k)))
         <= &4 * tau * &2 zpow k`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * real_integral (real_interval[real_of_int n * &2 zpow k,
               (real_of_int n + &1) * &2 zpow k]) (\x. abs(h x))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CZ_BADPIECE_L1; CZ_CUBE_AABB_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[real_of_int n * &2 zpow k,
                                 (real_of_int n + &1) * &2 zpow k])
                  (\x. abs(h x))
    = real_integral (dyho k n) (\x. abs(h x))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET THEN
    MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{(real_of_int n + &1) * &2 zpow k}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_SING; dyho; SUBSET;
      IN_UNION; IN_DIFF; IN_ELIM_THM;
      IN_REAL_INTERVAL; IN_SING] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
    `i <= &2 * tau * &2 zpow k ==> &2 * i <= &4 * tau * &2 zpow k`) THEN
  MATCH_MP_TAC CZ_MAXCELL_DENSITY THEN ASM_REWRITE_TAC[]);;

(* If Om is the union UNIONS {real_interval[aa n,bb n] | sel n} of the       *)
(* closed cubes, then IMAGE lift Om = UNIONS {IMAGE lift (real_interval[aa   *)
(* n,bb n]) | sel n}.                                                        *)
let COVER_LIFT_DISTRIB = prove
 (`!(aa:num->real) bb sel.
     IMAGE lift (UNIONS {real_interval[aa n, bb n] | n | sel n}) =
     UNIONS {IMAGE lift (real_interval[aa n, bb n]) | n | sel n}`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_IMAGE; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The closed cubes of disjoint half-open dyadic cells have negligible       *)
(* intersection: they meet in at most a shared endpoint                      *)
(* (DYHO_DISJOINT_ENDPOINTS).                                                *)
let CZ_CLOSED_CUBE_NEGLIGIBLE_INTER = prove
 (`!k1 n1 k2 n2.
     DISJOINT (dyho k1 n1) (dyho k2 n2)
     ==> real_negligible
           (real_interval[real_of_int n1 * &2 zpow k1,
                          (real_of_int n1 + &1) * &2 zpow k1] INTER
            real_interval[real_of_int n2 * &2 zpow k2,
                          (real_of_int n2 + &1) * &2 zpow k2])`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k1:int`;`n1:int`;`k2:int`;`n2:int`]
    DYHO_DISJOINT_ENDPOINTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THENL
   [EXISTS_TAC `{(real_of_int n1 + &1) * &2 zpow k1}`;
    EXISTS_TAC `{real_of_int n1 * &2 zpow k1}`] THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_SING; SUBSET; IN_INTER;
    IN_REAL_INTERVAL; IN_SING] THEN
  ASM_REAL_ARITH_TAC);;

(* The L^2 bound for the good part from an almost-everywhere pointwise       *)
(* bound: if g^2 and abs g are integrable and g^2 <= c * abs(g) outside a    *)
(* negligible set (c >= 0), then int g^2 <= c * int |g|.  For the good part  *)
(* c = 2 tau, giving int g^2 <= 2 tau int |g| <= 2 tau mFW.                  *)
let GOOD_L2_FROM_AE = prove
 (`!(g:real->real) c e.
     (\x. g x pow 2) real_integrable_on (:real) /\
     (\x. abs(g x)) real_integrable_on (:real) /\
     real_negligible e /\ &0 <= c /\
     (!x. ~(x IN e) ==> g x pow 2 <= c * abs(g x))
     ==> real_integral (:real) (\x. g x pow 2) <=
         c * real_integral (:real) (\x. abs(g x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `c * real_integral (:real) (\x. abs(g x)) =
    real_integral (:real) (\x. c * abs(g x))`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_LMUL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE_AE THEN
  EXISTS_TAC `e:real->bool` THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; IN_DIFF]);;

(* Separation of large cubes from non-straddling tiles.                      *)
(*  - CZ_CUBE_TILE_DISJOINT_LARGE: a cube dyho kJ nJ in Om that is wider     *)
(*    than the tile (--tile_k s < kJ) is disjoint from tile_I s if the tile  *)
(*    is not contained in Om (DYHO_DISJOINT: dyadic cells that are not       *)
(*    nested are disjoint).                                                  *)
(*  - CZ_CUBE_TILE_SEP: if dyho kJ nJ and tile_I s are disjoint, then        *)
(*    (nJ+1)2^kJ <= tile_xmid s - 2^{-tk}/2 or                               *)
(*    tile_xmid s + 2^{-tk}/2 <= nJ 2^kJ (DYHO_TILE_OUTSIDE).                *)
let CZ_CUBE_TILE_DISJOINT_LARGE = prove
 (`!(s:int#int#int) kJ nJ Om.
     dyho kJ nJ SUBSET Om /\ ~(tile_I s SUBSET Om) /\ --(tile_k s) < kJ
     ==> DISJOINT (dyho kJ nJ) (tile_I s)`,
  MATCH_MP_TAC(MESON[PAIR_SURJECTIVE]
    `(!k nI nJ2. P(k,nI,nJ2)) ==> (!s:int#int#int. P s)`) THEN
  MAP_EVERY X_GEN_TAC [`tk:int`; `nI:int`; `nJ2:int`] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[tile_I; tile_k] THEN STRIP_TAC THEN
  MATCH_MP_TAC DYHO_DISJOINT THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`kJ:int`;`nJ:int`;`--tk:int`;`nI:int`]
      DYHO_SUBSET_SCALE) THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ASM_MESON_TAC[SUBSET_TRANS]]);;

let CZ_CUBE_TILE_SEP = prove
 (`!(s:int#int#int) kJ nJ.
     DISJOINT (dyho kJ nJ) (tile_I s)
     ==> ((real_of_int nJ + &1) * &2 zpow kJ <=
            tile_xmid s - &2 zpow(--(tile_k s)) / &2 \/
          tile_xmid s + &2 zpow(--(tile_k s)) / &2 <=
            real_of_int nJ * &2 zpow kJ)`,
  MATCH_MP_TAC(MESON[PAIR_SURJECTIVE]
    `(!k nI nJ2. P(k,nI,nJ2)) ==> (!s:int#int#int. P s)`) THEN
  MAP_EVERY X_GEN_TAC [`tk:int`; `nI:int`; `nJ2:int`] THEN
  X_GEN_TAC `kJ:int` THEN X_GEN_TAC `nJ:int` THEN
  REWRITE_TAC[tile_I; tile_xmid; tile_k] THEN
    MP_TAC(ISPECL [`kJ:int`;`nJ:int`;`tk:int`;`nI:int`] DYHO_TILE_OUTSIDE) THEN
  ASM_REWRITE_TAC[]);;

let CZ_CUBE_WIDTH_LE_INT = prove
 (`!h tau k n.
     &0 < tau /\ tau * &2 zpow k < real_integral (dyho k n) (\y. abs(h y))
     ==> &2 zpow k <= inv(tau) * real_integral (dyho k n) (\y. abs(h y))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(tau) * (tau * &2 zpow k)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
     REAL_MUL_LID; REAL_LE_REFL];
    ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE]]);;

(* A finite set S of pairwise disjoint dyadic stopping cubes (each c = dyho  *)
(* (kf c) (nf c) with tau * 2^{kf c} < int_c |h|) has total measure at most  *)
(* inv(tau) * int_UNIV |h|.                                                  *)

let CZ_FINITE_CUBES_MEASURE_LE = prove
 (`!(h:real->real) tau S kf nf.
     &0 < tau /\ FINITE S /\ (\y. abs(h y)) real_integrable_on (:real) /\
     (!c. c IN S ==> c = dyho (kf c) (nf c) /\
                     tau * &2 zpow (kf c) < real_integral c (\y. abs(h y))) /\
     (!c1 c2. c1 IN S /\ c2 IN S /\ ~(c1 = c2) ==> DISJOINT c1 c2)
     ==> sum S (\c. real_measure c) <=
         inv(tau) * real_integral (:real) (\y. abs(h y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* abs h absolutely integrable on UNIV (nonneg + integrable)               *)
  SUBGOAL_THEN `(\y. abs((h:real->real) y))
                 absolutely_real_integrable_on (:real)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[NONNEGATIVE_ABSOLUTELY_REAL_INTEGRABLE; REAL_ABS_POS];
    ALL_TAC] THEN
  (* per-cell integrability of abs h                                         *)
  SUBGOAL_THEN
   `!c. c IN S ==> (\y. abs((h:real->real) y)) real_integrable_on c`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
     ABSINT_ON_LEBMEAS_SUBSET; SUBSET_UNIV;
     REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE; DYHO_MEASURABLE];
    ALL_TAC] THEN
  (* STEP 0: transitivity through the middle sum                             *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum S (\c. inv(tau) * real_integral c (\y. abs((h:real->real) y)))` THEN
  CONJ_TAC THENL
   [(* STEP 1: measure c <= inv tau * int_c |h| termwise *)
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:real->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `c = dyho (kf(c:real->bool)) (nf c) /\
      tau * &2 zpow (kf(c:real->bool)) <
      real_integral c (\y. abs((h:real->real) y))`
     STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    (* rewrite real_measure c = 2 zpow (kf c)                                *)
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [ASSUME `c = dyho (kf(c:real->bool)) (nf c)`] THEN
    REWRITE_TAC[DYHO_MEASURE] THEN
    (* apply CZ_CUBE_WIDTH_LE_INT as a fresh subgoal instance                *)
    SUBGOAL_THEN
     `&2 zpow (kf(c:real->bool)) <=
      inv tau * real_integral (dyho (kf c) (nf c)) (\y. abs((h:real->real) y))`
     MP_TAC THENL
     [ASM_MESON_TAC[CZ_CUBE_WIDTH_LE_INT];
      ASM_MESON_TAC[]];
    (* STEP 2: pull out inv tau, union monotonicity                          *)
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `sum S (\c. real_integral c (\y. abs((h:real->real) y))) =
      real_integral (UNIONS S) (\y. abs(h y))`
     SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_DISJOINT_UNIONS];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; REAL_ABS_POS] THEN
    (* abs h integrable on UNIONS S                                          *)
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSINT_ON_LEBMEAS_SUBSET THEN
    EXISTS_TAC `(:real)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE THEN
    MATCH_MP_TAC REAL_MEASURABLE_UNIONS THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `c:real->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `c = dyho (kf(c:real->bool)) (nf c)`
     (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[DYHO_MEASURABLE]]]);;

(* ========================================================================= *)
(* Comparison of the dyadic stopping set with the superlevel set of the      *)
(* maximal function.                                                         *)
(*  - HL_MAXIMAL_MONO: if |g| <= |f| pointwise, |f| <= 1 and f is locally    *)
(*    integrable, then hl_maximal g x <= hl_maximal f x.                     *)
(*  - INDICATOR_ABS_INTEGRABLE: for real_measurable Ff, (\t. abs(1_Ff t)) is *)
(*    integrable on every bounded interval.                                  *)
(*  - CZ_OM_SUBSET_MAXFN: for |h| <= 1_Ff, the dyadic stopping set of h is   *)
(*    contained in Omega = {x | tau < hl_maximal 1_Ff x}                     *)
(*    (CZ_STOP_IMP_MAXIMAL and HL_MAXIMAL_MONO).  So a tile not contained in *)
(*    Omega is not contained in the stopping set.                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Monotonicity of the maximal function under |g| <= |f| <= 1.               *)
(* ------------------------------------------------------------------------- *)

let HL_MAXIMAL_MONO = prove
 (`!f g x.
     (!t. abs(g t) <= abs(f t)) /\ (!t. abs(f t) <= &1) /\
     (!a b. (\t. abs(f t)) real_integrable_on real_interval[a,b]) /\
     (!a b. (\t. abs(g t)) real_integrable_on real_interval[a,b])
     ==> hl_maximal g x <= hl_maximal f x`,
  REWRITE_TAC[hl_maximal] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`real_integral (real_interval [x - &1,x + &1]) (\t. abs (g t)) /
       ((x + &1) - (x - &1))`; `x - &1`; `x + &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_integral (real_interval [a,b]) (\t. abs (f t)) / (b - a)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_LE];
      SIMP_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_SUP THEN
    MAP_EVERY EXISTS_TAC
     [`&1:real`;
      `real_integral (real_interval [a,b]) (\t. abs (f t)) / (b - a)`] THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`c:real`; `d:real`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < d - c` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `real_integral (real_interval [c,d]) (\t. &1)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_INTEGRAL_LE; REAL_INTEGRABLE_CONST];
        SUBGOAL_THEN `c <= d` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The absolute value of the indicator of a real-measurable set is           *)
(* integrable on every bounded interval.                                     *)
(* ------------------------------------------------------------------------- *)

let INDICATOR_ABS_INTEGRABLE = prove
 (`!Ff a b. real_measurable Ff
     ==> (\t. abs (if t IN Ff then &1 else &0)) real_integrable_on
         real_interval[a,b]`,
  SIMP_TAC[CH_HL_INDICATOR_ABS_EQ; CH_INDICATOR_INTEGRABLE_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* If |h| <= 1_Ff, the dyadic stopping set of h is contained in the          *)
(* superlevel set {x | tau < hl_maximal 1_Ff x} of the maximal function of   *)
(* the indicator of Ff.                                                      *)
(* ------------------------------------------------------------------------- *)

let CZ_OM_SUBSET_MAXFN = prove
 (`!h Ff tau.
     &0 < tau /\ real_measurable Ff /\
     (!t. abs(h t) <= (if t IN Ff then &1 else &0)) /\
     (\t. abs(h t)) real_integrable_on (:real) /\
     (!a b. (\t. abs(h t)) real_integrable_on real_interval[a,b])
     ==> {x | ?k. tau * &2 zpow k <
                  real_integral (dyho k (@q. x IN dyho k q)) (\y. abs(h y))}
         SUBSET {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x}`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `hl_maximal h x` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CZ_STOP_IMP_MAXIMAL THEN
    MAP_EVERY EXISTS_TAC [`k:int`; `(@q. x IN dyho k q):int`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[DYHO_COVERS_POINT];
      GEN_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                              (let b = snd(dest_forall(concl th)) in
                               is_binary "real_le" b)
                            then MP_TAC(SPEC `t:real` th) else NO_TAC) THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC HL_MAXIMAL_MONO THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN
      FIRST_ASSUM(fun th -> if is_forall(concl th) &&
                              (let b = snd(dest_forall(concl th)) in
                               is_binary "real_le" b)
                            then MP_TAC(SPEC `t:real` th) else NO_TAC) THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[INDICATOR_ABS_INTEGRABLE];
      ASM_REWRITE_TAC[]]]);;

let CZ_PARTIAL_WIDTH_SUM = prove
 (`!(h:real->real) lam (sel:num->bool) (kk:num->int) (nn:num->int)
     (aa:num->real) (bb:num->real).
     &0 < lam /\ (\y. abs(h y)) real_integrable_on (:real) /\
     (!k. sel k
          ==> aa k = real_of_int(nn k) * &2 zpow (kk k) /\
              bb k = (real_of_int(nn k) + &1) * &2 zpow (kk k) /\
              lam * &2 zpow (kk k) <
                real_integral (dyho (kk k) (nn k)) (\y. abs(h y))) /\
     (!i j. sel i /\ sel j /\ ~(i = j)
            ==> DISJOINT (dyho (kk i) (nn i)) (dyho (kk j) (nn j)))
     ==> !N. sum {k | k IN 0..N /\ sel k} (\k. bb k - aa k) <=
             inv lam * real_integral (:real) (\y. abs(h y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  ABBREV_TAC `Q = {k | k IN 0..N /\ (sel:num->bool) k}` THEN
  SUBGOAL_THEN `FINITE (Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `!k:num. k IN Q ==> (sel:num->bool) k` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `cube = \k:num. dyho ((kk:num->int) k) (nn k)` THEN
  SUBGOAL_THEN `!i j:num. i IN Q /\ j IN Q /\
                 (cube:num->real->bool) i = cube j ==> i = j`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `i:num = j` THEN FIRST_X_ASSUM(MP_TAC o
      check(fun t -> is_forall(concl t) &&
                     free_in `DISJOINT:(real->bool)->(real->bool)->bool`
                       (concl t))) THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(cube:num->real->bool) i = cube j` THEN EXPAND_TAC "cube" THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[DISJOINT; INTER_IDEMPOT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `real_of_int((nn:num->int) j) * &2 zpow (kk j)` THEN
    REWRITE_TAC[DYHO_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Q (\k. (bb:num->real) k - aa k) =
    sum (IMAGE (cube:num->real->bool) Q) (\c. real_measure c)`
    SUBST1_TAC THENL
   [MP_TAC(ISPECL [`cube:num->real->bool`;
                   `\c:real->bool. real_measure c`; `Q:num->bool`]
                  SUM_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[o_THM] THEN
    EXPAND_TAC "cube" THEN REWRITE_TAC[DYHO_MEASURE] THEN
    ASM_SIMP_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
    [`h:real->real`; `lam:real`; `IMAGE (cube:num->real->bool) Q`;
     `\c:real->bool. (kk:num->int)((@k. k IN Q /\ cube k = c))`;
     `\c:real->bool. (nn:num->int)((@k. k IN Q /\ cube k = c))`]
    CZ_FINITE_CUBES_MEASURE_LE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o
        check(fun t -> is_forall(concl t) &&
                       free_in `DISJOINT:(real->bool)->(real->bool)->bool`
                         (concl t))) THEN
      EXPAND_TAC "cube" THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((cube:num->real->bool) i = cube j)` THEN
      ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* The union of the selected closed cubes real_interval[aa n, bb n] (sel n)  *)
(* is measurable if the sums of the widths over the selected indices in 0..n *)
(* are bounded uniformly in n (REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG).     *)
let CZ_OM_MEASURABLE = prove
 (`!(aa:num->real) (bb:num->real) (sel:num->bool) B.
     (!k. sel k ==> aa k <= bb k) /\
     (!n. sum {k | k IN 0..n /\ sel k} (\k. bb k - aa k) <= B)
     ==> real_measurable (UNIONS {real_interval[aa n, bb n] | n | sel n})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS {real_interval[(aa:num->real) n, bb n] | n | (sel:num->bool) n} =
    UNIONS {(\k. if sel k then real_interval[aa k, bb k]
                 else {}) n | n IN (:num)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real` THEN EQ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[NOT_IN_EMPTY]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `B:real` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_MEASURABLE_REAL_INTERVAL; REAL_MEASURABLE_EMPTY];
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {k | k IN 0..n /\ (sel:num->bool) k}
                    (\k. (bb:num->real) k - aa k)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    (* measure(UNIONS {s k | k<=n}) <= sum widths                            *)
    SUBGOAL_THEN
     `UNIONS {(\k. if (sel:num->bool) k
                   then real_interval[(aa:num->real) k, bb k]
                   else {}) k | k <= n}
      = UNIONS (IMAGE (\k. real_interval[aa k, bb k])
                      {k | k IN 0..n /\ sel k})`
     SUBST1_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; UNIONS_IMAGE; EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
      EQ_TAC THENL
       [ASM_MESON_TAC[NOT_IN_EMPTY];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum {k | k IN 0..n /\ (sel:num->bool) k} (\k. (bb:num->real) k - aa k) =
      sum {k | k IN 0..n /\ (sel:num->bool) k}
          (\k. real_measure(real_interval[(aa:num->real) k, bb k]))`
     SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `k:num` THEN
       REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[REAL_MEASURE_REAL_INTERVAL] THEN
      SUBGOAL_THEN `(aa:num->real) k <= bb k` MP_TAC THENL
       [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_MEASURE_UNIONS_LE_IMAGE THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL]]);;

(* The density of the bad piece on a maximal stopping cube for the stopping  *)
(* level lam = tau/2: on the closed cube J = [nn 2^kk, (nn+1) 2^kk],         *)
(*   int_J |h - avg_J h| <= 2 tau |J|                                        *)
(* (CZ_CUBE_BPIECE_DENSITY, with 4 lam = 2 tau).                             *)
let CZ_MAXCUBE_BADPIECE_L1 = prove
 (`!h tau lam kk nn.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < lam /\ &2 * lam = tau /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     lam * &2 zpow kk < real_integral (dyho kk nn) (\y. abs(h y)) /\
     (!k' n'. kk < k' /\ dyho kk nn SUBSET dyho k' n'
              ==> ~(lam * &2 zpow k' <
                    real_integral (dyho k' n') (\y. abs(h y))))
     ==> real_integral
           (real_interval[real_of_int nn * &2 zpow kk,
             (real_of_int nn + &1) * &2 zpow kk])
           (\x. abs(h x - real_integral
                          (real_interval[real_of_int nn * &2 zpow kk,
                            (real_of_int nn + &1) * &2 zpow kk]) h /
                        ((real_of_int nn + &1) * &2 zpow kk -
                          real_of_int nn * &2 zpow kk)))
         <= &2 * tau *
            ((real_of_int nn + &1) * &2 zpow kk -
             real_of_int nn * &2 zpow kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&4 * lam * &2 zpow kk` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CZ_CUBE_BPIECE_DENSITY;
     ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
     ABSOLUTELY_REAL_INTEGRABLE_ABS];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check(fun t -> is_eq(concl t) && rand(concl t) = `tau:real`)) THEN
    REAL_ARITH_TAC]);;

(* Scalar arithmetic for CH_CZ_PRODUCER.  CZ_SCALE_ARITH: with inv(2^Kc) =   *)
(* width, 2^Kc * (width/2) = (2^Kc * inv 2^Kc)/2 = 1/2 <= 1.                 *)
let CZ_SCALE_ARITH = prove
 (`!z w:real. &0 < z /\ inv z = w ==> z * (w / &2) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[real_div] THEN
  SUBGOAL_THEN `z * inv z * inv(&2) = (z * inv z) * inv(&2)`
   (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `z * inv z = &1` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* CZ_WIDTH_SUM_ARITH: from S <= inv lam * int |h| with lam = tau, int |h|   *)
(* <= mFW and 0 < tau, we get S <= &2 * inv tau * mFW.                       *)
let CZ_WIDTH_SUM_ARITH = prove
 (`!s q tau mFW:real.
     s <= inv tau * q /\ q <= mFW /\ &0 < tau /\ &0 <= mFW
     ==> s <= &2 * inv tau * mFW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv tau * q:real` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv tau * mFW:real` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv tau = &1 * inv tau`
      (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]]);;

(* Variants of REAL_INTEGRABLE_SPIKE and REAL_INTEGRAL_SPIKE: functions that *)
(* agree outside a negligible set have the same integrability and the same   *)
(* integral.                                                                 *)
let SPIKE_INTEG = prove
 (`!g t. (?f s. real_negligible s /\ (!x. x IN t DIFF s ==> g x = f x) /\
                f real_integrable_on t)
         ==> g real_integrable_on t`,
  ASM_MESON_TAC[REAL_INTEGRABLE_SPIKE]);;

let SPIKE_INTEGRAL_EQ = prove
 (`!g f s t. real_negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
             ==> real_integral t g = real_integral t f`,
  ASM_MESON_TAC[REAL_INTEGRAL_SPIKE]);;

(* ------------------------------------------------------------------------- *)
(* The bad piece on one dyadic cell real_interval[a,b]: if bfun equals h     *)
(* minus its average over the cell outside a negligible set e, then bfun is  *)
(* absolutely integrable, has integral 0, and int |bfun| <= C whenever int   *)
(* |h - avg| <= C (SPIKE_INTEG, SPIKE_INTEGRAL_EQ, CZ_BADPIECE_MEANZERO).    *)
(* ------------------------------------------------------------------------- *)

let CZ_BAD_CUBE_PROPERTIES = prove
 (`!(bfun:real->real) (h:real->real) (a:real) (b:real) (e:real->bool) (C:real).
     a < b /\ real_negligible e /\
     h absolutely_real_integrable_on real_interval[a,b] /\
     (!x. x IN real_interval[a,b] DIFF e
          ==> bfun x = h x - real_integral (real_interval[a,b]) h / (b - a)) /\
     real_integral (real_interval[a,b])
       (\x. abs(h x - real_integral (real_interval[a,b]) h / (b - a))) <= C
     ==> bfun absolutely_real_integrable_on (real_interval[a,b]) /\
         real_integral (real_interval[a,b]) bfun = &0 /\
         real_integral (real_interval[a,b]) (\x. abs(bfun x)) <= C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `avg = real_integral (real_interval[a,b]) (h:real->real) / (b - a)` THEN
  SUBGOAL_THEN `(\x. (h:real->real) x - avg)
                 absolutely_real_integrable_on real_interval[a,b]`
   (LABEL_TAC "hmavg") THENL
   [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB;
     ABSOLUTELY_REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `bfun absolutely_real_integrable_on
                 (real_interval[a,b])` ASSUME_TAC THENL
   [REWRITE_TAC[absolutely_real_integrable_on] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SPIKE_INTEG THEN
      MAP_EVERY EXISTS_TAC [`\x. (h:real->real) x - avg`; `e:real->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
        USE_THEN "hmavg" ACCEPT_TAC;
      MATCH_MP_TAC SPIKE_INTEG THEN
      MAP_EVERY EXISTS_TAC [`\x. abs((h:real->real) x - avg)`;
                            `e:real->bool`] THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
          ABSOLUTELY_REAL_INTEGRABLE_ABS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[a,b]) bfun =
    real_integral (real_interval[a,b]) (\x. (h:real->real) x - avg) /\
    real_integral (real_interval[a,b]) (\x. abs(bfun x)) =
    real_integral (real_interval[a,b]) (\x. abs((h:real->real) x - avg))`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SPIKE_INTEGRAL_EQ THEN
     EXISTS_TAC `e:real->bool` THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "avg" THEN
  MATCH_MP_TAC CZ_BADPIECE_MEANZERO THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    ASM_REWRITE_TAC[]);;

(* A finite sum of real-measurable functions is real-measurable (by          *)
(* induction on the finite index set, as for MEASURABLE_ON_VSUM).            *)
let REAL_MEASURABLE_ON_SUM = prove
 (`!f:A->real->real t.
        FINITE t /\ (!i. i IN t ==> (f i) real_measurable_on (:real))
        ==> (\x. sum t (\i. f i x)) real_measurable_on (:real)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; FORALL_IN_INSERT] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MEASURABLE_ON_CONST];
    ASM_SIMP_TAC[REAL_MEASURABLE_ON_ADD; ETA_AX]]);;

(* A measurable h, modified to h - c_m on pairwise disjoint measurable cells *)
(* (cell m) for the selected indices m and to 0 off all cells, is measurable *)
(* on UNIV: it is the pointwise limit of the finite partial sums over 0..N   *)
(* of the restricted step functions, which are eventually constant at each x *)
(* since at most one cell contains x.                                        *)
let CZ_STEP_MEASURABLE = prove
 (`!(h:real->real) (cell:num->real->bool) (c:num->real)
    (sel:num->bool) (bfun:real->real).
     h real_measurable_on (:real) /\
     (!m. real_lebesgue_measurable (cell m)) /\
     (!i j. sel i /\ sel j /\ ~(i = j) ==> DISJOINT (cell i) (cell j)) /\
     (!m x. sel m /\ x IN cell m ==> bfun x = h x - c m) /\
     (!x. (!m. sel m ==> ~(x IN cell m)) ==> bfun x = &0)
     ==> bfun real_measurable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_ON_LIMIT THEN
  MAP_EVERY EXISTS_TAC
   [`\N x. sum {m | m IN 0..N /\ sel m}
              (\m. if x IN cell m then (h:real->real) x - c m else &0)`;
    `{}:real->bool`] THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_EMPTY; DIFF_EMPTY; IN_UNIV] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_ON_SUM; FINITE_RESTRICT; FINITE_NUMSEG;
     REAL_MEASURABLE_ON_RESTRICT; REAL_MEASURABLE_ON_SUB;
     REAL_MEASURABLE_ON_CONST];
    (* pointwise convergence, everywhere                                     *)
    X_GEN_TAC `x:real` THEN
      ASM_CASES_TAC `?m:num. sel m /\ (x:real) IN cell m` THENL
     [(* CASE A: x lies in the (unique) selected cell m0 *)
      FIRST_X_ASSUM(X_CHOOSE_THEN `m0:num` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC REALLIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `m0:num` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `sum {m | m IN 0..N /\ sel m}
            (\m. if (x:real) IN cell m then h x - c m else &0) =
        sum {m | m IN 0..N /\ sel m}
            (\m. if m = m0 then (h:real->real) x - c m0 else &0)`
       SUBST1_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
         REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        ASM_CASES_TAC `m:num = m0` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `DISJOINT ((cell:num->real->bool) m) (cell m0)`
          MP_TAC THENL
         [ASM_SIMP_TAC[];
          ASM_MESON_TAC[DISJOINT; IN_INTER; NOT_IN_EMPTY]];
        ALL_TAC] THEN
      SUBGOAL_THEN `m0 IN {m | m IN 0..N /\ sel m}` ASSUME_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; LE_0];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SUM_DELTA] THEN
      CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      (* CASE B: x lies in no selected cell => bfun x = 0 and every partial  *)
      (* sum is 0                                                            *)
      MATCH_MP_TAC REALLIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      EXISTS_TAC `0` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `!m:num. sel m ==> ~((x:real) IN cell m)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[SUM_EQ_0];
        ASM_SIMP_TAC[]]]]);;

(* Dominating functions for b and g: |b x| <= |h x| + tau*1_Om x everywhere, *)
(* and likewise for |g x| = |h x - b x|; the dominator is integrable since   *)
(* |h| is and Om has finite measure.                                         *)

(* |b x| and |g x| = |h x - b x| are at most |h x| + tau 1_Om x: off Omset  *)
(* b = 0, and on Omset b = h - c, g = c with |c| <= 2 lam = tau.             *)
let CZ_BG_DOMINATED = prove
 (`!(bfun:real->real) (h:real->real) (Omset:real->bool) (Om:real->bool)
     (lam:real) (tau:real) (x:real).
     &2 * lam = tau /\ &0 <= lam /\
     Omset SUBSET Om /\
     (!y. ~(y IN Omset) ==> bfun y = &0) /\
     (!y. y IN Omset ==> ?c. bfun y = h y - c /\ abs c <= &2 * lam)
     ==> abs(bfun x) <= abs(h x) + tau * (if x IN Om then &1 else &0) /\
         abs(h x - bfun x) <= abs(h x) + tau * (if x IN Om then &1 else &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real) IN Omset` THENL
   [SUBGOAL_THEN `(x:real) IN Om` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o
      check(fun t -> is_forall(concl t) && can (find_term
        is_exists) (concl t))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* tau*1_Om is integrable on UNIV when Om is measurable (finite measure).    *)
let CZ_TAU_IND_OM_INTEGRABLE = prove
 (`!(Om:real->bool) tau.
     real_measurable Om
     ==> (\x. tau * (if x IN Om then &1 else &0)) real_integrable_on (:real)`,
  ASM_REWRITE_TAC[REAL_INTEGRABLE_LMUL; REAL_MEASURABLE_REAL_INTEGRABLE]);;

(* The good part g = h - b has g^2 integrable: from the pointwise bound |g   *)
(* x| <= D x = |h x| + tau * 1_Om x, with D integrable and D <= 1 + tau (as  *)
(* |h| <= 1), we get g^2 <= (1 + tau) * D.                                   *)
let CZ_G2_INTEGRABLE = prove
 (`!(g:real->real) (h:real->real) (D:real->real) tau.
     g real_measurable_on (:real) /\
     D real_integrable_on (:real) /\ &0 <= tau /\
     (!x. abs(h x) <= &1) /\
     (!x. abs(g x) <= D x) /\
     (!x. D x <= &1 + tau)
     ==> (\x. g x pow 2) real_integrable_on (:real)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. (&1 + tau) * (D:real->real) x` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_2; REAL_MEASURABLE_ON_MUL];
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL];
    ASM_MESON_TAC[REAL_ABS_POW; REAL_POW_2; REAL_LE_MUL2;
      REAL_ABS_POS; REAL_LE_TRANS]]);;

(* Integrability of the pairings of b with the packets and weights (from the *)
(* absolute integrability of b, the boundedness of cw_tile,                  *)
(* CH_INDCW_INTEGRABLE and CH_BADPAIR_ABSINT_UNIV).                          *)

(* |b| * cw_tile s is absolutely integrable on UNIV, since cw_tile s is      *)
(* measurable and bounded.                                                   *)
let CZ_BCW_ABSINT = prove
 (`!(b:real->real) (s:int#int#int).
     b absolutely_real_integrable_on (:real)
     ==> (\x. abs(b x) * cw_tile s x) absolutely_real_integrable_on (:real)`,
  ASM_SIMP_TAC[REAL_MUL_SYM;
    ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT;
    INTEGRABLE_IMP_REAL_MEASURABLE; ETA_AX; CW_TILE_INTEGRABLE_UNIV;
    CW_TILE_BOUNDED; ABSOLUTELY_REAL_INTEGRABLE_ABS]);;

(* |b| cw_tile s is real-integrable on any real_lebesgue_measurable set (an  *)
(* interval, a tail, UNIV): by REAL_INTEGRABLE_RESTRICT_UNIV, as a           *)
(* measurable function dominated by the integrable function |b| cw_tile s    *)
(* itself.                                                                   *)
let CZ_BCW_INTEGRABLE_ON = prove
 (`!(b:real->real) (s:int#int#int) (u:real->bool).
     b absolutely_real_integrable_on (:real) /\ real_lebesgue_measurable u
     ==> (\x. abs(b x) * cw_tile s x) real_integrable_on u`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. abs((b:real->real) x) * cw_tile s x` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_RESTRICT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_IMP_REAL_MEASURABLE THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC CZ_BCW_ABSINT THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE; CZ_BCW_ABSINT];
    X_GEN_TAC `x:real` THEN
      SUBGOAL_THEN `&0 <= abs((b:real->real) x) * cw_tile s x` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      MP_TAC(ISPECL [`s:int#int#int`; `x:real`] CW_TILE_POS) THEN
      REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* the complex packet integrable on a lift-interval.                         *)
let CZ_PACKET_INTEGRABLE = prove
 (`!(b:real->real) (t:int#int#int) (s:int#int#int) (a0:real) (b0:real).
     b absolutely_real_integrable_on (:real)
     ==> (\z. Cx(b(drop z)) *
              cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                  phi_sigma s carleson_phi (drop z)))
         integrable_on (IMAGE lift (real_interval[a0, b0]))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `(:real^1)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`tile_ymid t`; `b:real->real`;
                   `\x:real. &0`; `s:int#int#int`]
      CH_BADPAIR_ABSINT_UNIV) THEN
    ASM_REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_0] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_LEBESGUE_MEASURABLE;
      REAL_LEBESGUE_MEASURABLE_INTERVAL]]);;

(* Cube-tile separation for the stopping set Omset.  Suppose that Omset is   *)
(* contained in G = {x | tau < hl_maximal 1_Ff x}, that the tile s is not    *)
(* contained in G, and that the cube dyho kk nn SUBSET Omset is wider than   *)
(* the tile (--tile_k s < kk).  Then the cube is disjoint from the tile      *)
(* (CZ_CUBE_TILE_DISJOINT_LARGE with Om := Omset) and hence lies on one side *)
(* of it (CZ_CUBE_TILE_SEP).                                                 *)
let CZ_CUBE_TILE_SEP_OMSET = prove
 (`!(Omset:real->bool) (Ff:real->bool) (s:int#int#int)
    (kk:int) (nn:int) (tau:real).
     Omset SUBSET {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x} /\
     ~(tile_I s SUBSET
       {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x}) /\
     dyho kk nn SUBSET Omset /\
     --tile_k s < kk
     ==> (real_of_int nn + &1) * &2 zpow kk <=
           tile_xmid s - &2 zpow (--tile_k s) / &2 \/
         tile_xmid s + &2 zpow (--tile_k s) / &2 <=
           real_of_int nn * &2 zpow kk`,
  ASM_MESON_TAC[CZ_CUBE_TILE_SEP; CZ_CUBE_TILE_DISJOINT_LARGE;
    SUBSET_TRANS]);;

(* The stopping set at level lam is contained in {lam < M(1_Ff)}: the form   *)
(* of CZ_OM_SUBSET_MAXFN for the stopping set Omset used in CH_CZ_PRODUCER,  *)
(* with absolute integrability of h on bounded intervals as hypothesis.      *)
let CZ_OMSET_SUB_MAXFN = prove
 (`!(h:real->real) (Ff:real->bool) (lam:real).
     &0 < lam /\ real_measurable Ff /\
     (!x. abs(h x) <= (if x IN Ff then &1 else &0)) /\
     (\x. abs(h x)) real_integrable_on (:real) /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b])
     ==> {x | ?k. lam * &2 zpow k <
                  real_integral (dyho k (@q. x IN dyho k q)) (\y. abs(h y))}
         SUBSET {x | lam < hl_maximal (\u. if u IN Ff then &1 else &0) x}`,
  ASM_SIMP_TAC[CZ_OM_SUBSET_MAXFN; ABSOLUTELY_REAL_INTEGRABLE_ABS;
    ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE]);;

(* |g x| <= &2 * tau for almost all x, where g = h - bfun and the stopping   *)
(* level is tau.  On Omset, g = c with |c| <= &2 * tau; off Omset, g = h,    *)
(* and every dyadic cell containing x has average of |h| at most tau, so |h  *)
(* x| <= tau at every Lebesgue point (CZ_H_LE_TAU_OFF_OM,                    *)
(* REAL_LEBESGUE_AVERAGE).                                                   *)
let CZ_G_LE_2TAU_AE = prove
 (`!(h:real->real) (bfun:real->real) (Omset:real->bool) (tau:real).
     &0 < tau /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     (!x. ~(x IN Omset) ==> bfun x = &0) /\
     (!x. x IN Omset ==> ?c. bfun x = h x - c /\ abs c <= &2 * tau) /\
     (!x. ~(x IN Omset)
          ==> (!k n. x IN dyho k n
                     ==> real_integral (dyho k n) (\y. abs(h y)) <=
                         tau * &2 zpow k))
     ==> ?e. real_negligible e /\
             (!x. ~(x IN e) ==> abs(h x - bfun x) <= &2 * tau)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real->real` REAL_LEBESGUE_AVERAGE) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:real->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(x:real) IN Omset` THENL
   [(* on Omset: g = c, |c| <= 2 tau *)
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o
      check(fun t -> is_forall(concl t) &&
                     can (find_term is_exists) (concl t) &&
                     free_in `bfun:real->real` (concl t))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[REAL_ARITH `!a c:real. a - (a - c) = c`];
    (* off Omset: g = h, |h x| <= tau <= 2 tau via CZ_H_LE_TAU_OFF_OM        *)
    SUBGOAL_THEN `(bfun:real->real) x = &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `tau:real` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(ISPECL [`h:real->real`; `tau:real`; `x:real`]
      CZ_H_LE_TAU_OFF_OM) THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_MESON_TAC[]]]);;

(* ========================================================================= *)
(* The good part of the decomposition is an L^1 contraction:                 *)
(*   CZ_GOOD_L1_LE:  int_UNIV |g| <= int_UNIV |h|                            *)
(* where g equals h off a countable disjoint family of measurable cells      *)
(* {cell m | sel m} and equals the cell average c m on each selected cell (c *)
(* m * measure(cell m) = int_cell h).  The per-cell bound |int_cell h| <=    *)
(* int_cell |h| (CZ_GOOD_PERCELL), summed over the finite partial unions     *)
(* Om_N = UNIONS {cell m | m <= N /\ sel m} (CZ_GOOD_FINITE_L1), gives       *)
(* int_UNIV (|g| on Om_N, |h| off Om_N) <= int_UNIV |h|                      *)
(* (CZ_GOOD_PARTIAL_L1); then dominated convergence as N -> oo               *)
(* (CZ_GOOD_POINTWISE, REAL_DOMINATED_CONVERGENCE).                          *)
(* ========================================================================= *)

let CZ_GOOD_PERCELL = prove
 (`!(h:real->real) (g:real->real) (s:real->bool) (cc:real).
     real_measurable s /\
     h absolutely_real_integrable_on s /\
     (!x. x IN s ==> g x = cc) /\
     cc * real_measure s = real_integral s h
     ==> ((\x. abs(g x)) has_real_integral (abs cc * real_measure s)) s /\
         abs cc * real_measure s <= real_integral s (\x. abs(h x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `(\x. abs cc):real->real` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_CONST_MEASURABLE; REAL_INTEGRABLE_INTEGRAL;
                 REAL_INTEGRABLE_ON_CONST_MEASURABLE];
    ASM_MESON_TAC[REAL_ABS_MUL; REAL_ABS_REFL; REAL_MEASURE_POS_LE;
      ABSOLUTELY_REAL_INTEGRABLE_LE]]);;

(* Summing the per-cell bounds over a finite family of disjoint cells        *)
(* (HAS_REAL_INTEGRAL_UNIONS).                                               *)
let CZ_GOOD_FINITE_L1 = prove
 (`!Q. FINITE Q
     ==> !(h:real->real) (g:real->real) (cell:num->real->bool) (c:num->real).
           (!m. m IN Q ==> real_measurable (cell m)) /\
           (!i j. i IN Q /\ j IN Q /\ ~(i = j) ==>
             DISJOINT (cell i) (cell j)) /\
           (!m. m IN Q ==> h absolutely_real_integrable_on (cell m)) /\
           (!m x. m IN Q /\ x IN cell m ==> g x = c m) /\
           (!m. m IN Q ==> c m * real_measure(cell m) =
             real_integral (cell m) h)
           ==> ?ig ih. ((\x. abs(g x)) has_real_integral ig)
                         (UNIONS {cell m | m IN Q}) /\
                       ((\x. abs(h x)) has_real_integral ih)
                         (UNIONS {cell m | m IN Q}) /\
                       ig <= ih`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m IN Q
        ==> ((\x. abs((g:real->real) x)) has_real_integral
             (abs((c:num->real) m) * real_measure((cell:num->real->bool) m)))
            (cell m) /\
            abs(c m) * real_measure(cell m) <=
            real_integral (cell m) (\x. abs((h:real->real) x)) /\
            ((\x. abs(h x)) has_real_integral
             real_integral (cell m) (\x. abs(h x))) (cell m)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real->real) absolutely_real_integrable_on
                  (cell:num->real->bool) m` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real->real`; `g:real->real`; `(cell:num->real->bool) m`;
                   `(c:num->real) m`] CZ_GOOD_PERCELL) THEN
    ASM_SIMP_TAC[REAL_INTEGRABLE_INTEGRAL;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE;
                 ABSOLUTELY_REAL_INTEGRABLE_ABS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i j. i IN IMAGE (cell:num->real->bool) Q /\ j IN IMAGE cell Q /\
          ~(i = j) ==> real_negligible(i INTER j)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(cell:num->real->bool) x INTER cell x' = {}`
     (fun th -> REWRITE_TAC[th; REAL_NEGLIGIBLE_EMPTY]) THEN
    ASM_MESON_TAC[DISJOINT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`sum (IMAGE (cell:num->real->bool) Q) (\C. real_integral C
       (\x. abs((g:real->real) x)))`;
    `sum (IMAGE (cell:num->real->bool) Q) (\C. real_integral C
       (\x. abs((h:real->real) x)))`] THEN
  REWRITE_TAC[SIMPLE_IMAGE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[REAL_INTEGRABLE_INTEGRAL; real_integrable_on];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE];
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE]]);;

let CZ_GOOD_PARTIAL_L1 = prove
 (`!(h:real->real) (g:real->real) (cell:num->real->bool)
    (c:num->real) (sel:num->bool) N.
      (\x. abs(h x)) real_integrable_on (:real) /\
      (!m. real_measurable (cell m)) /\
      (!i j. sel i /\ sel j /\ ~(i=j) ==> DISJOINT (cell i) (cell j)) /\
      (!m. sel m ==> h absolutely_real_integrable_on cell m) /\
      (!m x. sel m /\ x IN cell m ==> g x = c m) /\
      (!m. sel m ==> c m * real_measure(cell m) = real_integral (cell m) h)
      ==> (\x. if x IN UNIONS {cell m | m IN 0..N /\ sel m}
               then abs(g x) else abs(h x)) real_integrable_on (:real) /\
          real_integral (:real)
            (\x. if x IN UNIONS {cell m | m IN 0..N /\ sel m}
                 then abs(g x) else abs(h x))
          <= real_integral (:real) (\x. abs(h x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Q = {m:num | m IN 0..N /\ sel m}` THEN
  SUBGOAL_THEN `UNIONS {(cell:num->real->bool) m | m IN 0..N /\ sel m} =
                UNIONS {cell m | m IN Q}` SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:num. m IN Q ==> sel m` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPEC `Q:num->bool` CZ_GOOD_FINITE_L1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`h:real->real`; `g:real->real`;
                            `cell:num->real->bool`; `c:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ig:real`
    (X_CHOOSE_THEN `ih:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `((\x. if x IN UNIONS {(cell:num->real->bool) m | m IN Q}
          then abs((g:real->real) x) - abs(h x) else &0)
     has_real_integral (ig - ih)) (:real)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV;
     HAS_REAL_INTEGRAL_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\x. abs((h:real->real) x) +
          (if x IN UNIONS {(cell:num->real->bool) m | m IN Q}
           then abs(g x) - abs(h x) else &0)) has_real_integral
     (real_integral (:real) (\x. abs(h x)) + (ig - ih))) (:real)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[HAS_REAL_INTEGRAL_ADD; REAL_INTEGRABLE_INTEGRAL];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. if x IN UNIONS {(cell:num->real->bool) m | m IN Q}
         then abs((g:real->real) x) else abs(h x)) =
    (\x. abs(h x) + (if x IN UNIONS {cell m | m IN Q}
                     then abs(g x) - abs(h x) else &0))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[real_integrable_on] THEN EXISTS_TAC
      `real_integral (:real) (\x. abs((h:real->real) x)) + (ig - ih)` THEN
    ASM_REWRITE_TAC[];
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    ASM_REAL_ARITH_TAC]);;

let CZ_UNIONS_NUMSEG_MEM = prove
 (`!(cell:num->real->bool) sel x k.
     x IN UNIONS {cell m | m IN 0..k /\ sel m} <=>
     ?m. m <= k /\ sel m /\ x IN cell m`,
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN MESON_TAC[]);;

let CZ_GOOD_POINTWISE = prove
 (`!(h:real->real) (g:real->real) (cell:num->real->bool) (sel:num->bool)
     (c:num->real) x.
      (!m y. sel m /\ y IN cell m ==> g y = c m) /\
      (!y. (!m. sel m ==> ~(y IN cell m)) ==> g y = h y)
      ==> ((\k. if x IN UNIONS {cell m | m IN 0..k /\ sel m}
                then abs(g x) else abs(h x)) ---> abs(g x)) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC REALLIM_EVENTUALLY THEN
  ASM_CASES_TAC `?m:num. sel m /\ (x:real) IN cell m` THENL
   [ASM_MESON_TAC[EVENTUALLY_SEQUENTIALLY; CZ_UNIONS_NUMSEG_MEM];
    ASM_MESON_TAC[ALWAYS_EVENTUALLY]]);;

let CZ_GOOD_L1_LE = prove
 (`!(h:real->real) (g:real->real) (cell:num->real->bool)
    (c:num->real) (sel:num->bool).
      (\x. abs(h x)) real_integrable_on (:real) /\
      (\x. abs(g x)) real_integrable_on (:real) /\
      (!m. real_measurable (cell m)) /\
      (!i j. sel i /\ sel j /\ ~(i=j) ==> DISJOINT (cell i) (cell j)) /\
      (!m. sel m ==> h absolutely_real_integrable_on cell m) /\
      (!m x. sel m /\ x IN cell m ==> g x = c m) /\
      (!m. sel m ==> c m * real_measure(cell m) = real_integral (cell m) h) /\
      (!x. (!m. sel m ==> ~(x IN cell m)) ==> g x = h x)
      ==> real_integral (:real) (\x. abs(g x)) <=
        real_integral (:real) (\x. abs(h x))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `fN = \n:num. \x:real. if x IN UNIONS {cell m | m IN 0..n /\ sel m}
                          then abs((g:real->real) x) else abs(h x)` THEN
  MP_TAC(ISPECL
   [`fN:num->real->real`; `\x:real. abs((g:real->real) x)`;
    `\x:real. abs((g:real->real) x) + abs(h x)`; `(:real)`]
   REAL_DOMINATED_CONVERGENCE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [(* fN k integrable *)
      X_GEN_TAC `k:num` THEN EXPAND_TAC "fN" THEN
      MP_TAC(ISPECL [`h:real->real`; `g:real->real`; `cell:num->real->bool`;
                     `c:num->real`; `sel:num->bool`; `k:num`]
             CZ_GOOD_PARTIAL_L1) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ASM_SIMP_TAC[REAL_INTEGRABLE_ADD];
      EXPAND_TAC "fN" THEN REAL_ARITH_TAC;
      (* pointwise convergence                                               *)
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN EXPAND_TAC "fN" THEN
        MATCH_MP_TAC(ISPECL [`h:real->real`; `g:real->real`;
                             `cell:num->real->bool`; `sel:num->bool`;
                             `c:num->real`; `x:real`] CZ_GOOD_POINTWISE) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL
   [`sequentially`;
    `\k:num. real_integral (:real) ((fN:num->real->real) k)`;
    `real_integral (:real) (\x. abs((g:real->real) x))`;
    `real_integral (:real) (\x. abs((h:real->real) x))`] REALLIM_UBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `k:num` THEN
  EXPAND_TAC "fN" THEN
  MP_TAC(ISPECL [`h:real->real`; `g:real->real`; `cell:num->real->bool`;
                 `c:num->real`; `sel:num->bool`; `k:num`]
         CZ_GOOD_PARTIAL_L1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;

(* int_UNIV g^2 <= 2 * tau * mFW, from the integrability of g^2 and |g|, the *)
(* bound |g x| <= 2 * tau off a negligible set, int |g| <= mFW and 0 <= tau  *)
(* (GOOD_L2_FROM_AE with c = 2 * tau).                                       *)
let CZ_GOOD_L2_BOUND = prove
 (`!(g:real->real) (mFW:real) (tau:real) (e:real->bool).
     (\x. g x pow 2) real_integrable_on (:real) /\
     (\x. abs(g x)) real_integrable_on (:real) /\
     real_negligible e /\ &0 <= tau /\ &0 <= mFW /\
     (!x. ~(x IN e) ==> abs(g x) <= &2 * tau) /\
     real_integral (:real) (\x. abs(g x)) <= mFW
     ==> real_integral (:real) (\x. g x pow 2) <= &2 * tau * mFW`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&2 * tau) * real_integral (:real) (\x. abs(g x))` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real->real`; `&2 * tau`; `e:real->bool`]
      GOOD_L2_FROM_AE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    (* g x pow 2 <= (2 tau) * abs(g x), from |g x| <= 2 tau                  *)
    REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `abs((g:real->real) x) <= &2 * tau` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(SPEC `(g:real->real) x`
      (REAL_ARITH `!y. y * y = abs y * abs y`)) THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* Averages off the stopping set: if                                         *)
(*   Omset = {x | ?k. lam*2^k < int_{dyho k (@q. x IN dyho k q)} |h|},       *)
(* then for x not in Omset every dyadic cell dyho k n containing x satisfies *)
(* int_{dyho k n} |h| <= lam*2^k (dyadic cells of the same scale with a      *)
(* common point coincide, DYHO_POINT_UNIQUE).                                *)
let CZ_OFF_OMSET_AVG = prove
 (`!(h:real->real) (Omset:real->bool) (lam:real).
     {x | ?k. lam * &2 zpow k <
              real_integral (dyho k (@q. x IN dyho k q)) (\y. abs(h y))}
                = Omset
     ==> (!x. ~(x IN Omset)
              ==> (!k n. x IN dyho k n
                         ==> real_integral (dyho k n) (\y. abs(h y)) <=
                             lam * &2 zpow k))`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM; REAL_NOT_LT] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `dyho k (@q. (x:real) IN dyho k q) = dyho k n`
    (fun th -> SUBST1_TAC(SYM th)) THENL
   [ASM_MESON_TAC[DYHO_POINT_UNIQUE];
    ASM_REWRITE_TAC[]]);;

(* The maximal stopping cells of the dyadic Calderon-Zygmund decomposition   *)
(* at height tau.  A dyadic cell dyho k n stops if                           *)
(* tau * 2^k < int_{dyho k n} |h|, and it is maximal if no strictly coarser  *)
(* dyadic cell containing it stops.  The maximal stopping cells can be       *)
(* enumerated injectively as dyho (kk m) (nn m), m with sel m; distinct ones *)
(* are disjoint, and their union is the stopping set                         *)
(*   {x | ?k. tau * 2^k < int_{dyho k (@q. x IN dyho k q)} |h|}.             *)
let CZ_MAXCELL_ENUMERATION = prove
 (`!(h:real->real) tau.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau
     ==> ?(kk:num->int) (nn:num->int) (sel:num->bool).
           (!m. sel m
                ==> tau * &2 zpow (kk m) <
                    real_integral (dyho (kk m) (nn m)) (\y. abs(h y)) /\
                    (!k' n'. kk m < k' /\ dyho (kk m) (nn m) SUBSET dyho k' n'
                             ==> ~(tau * &2 zpow k' <
                                   real_integral (dyho k' n')
                                                 (\y. abs(h y))))) /\
           (!i j. sel i /\ sel j /\ ~(i = j)
                  ==> DISJOINT (dyho (kk i) (nn i)) (dyho (kk j) (nn j))) /\
           {x | ?k. tau * &2 zpow k <
                    real_integral (dyho k (@q. x IN dyho k q))
                                  (\y. abs(h y))} =
           UNIONS {dyho (kk m) (nn m) | m | sel m}`,
  REPEAT STRIP_TAC THEN MP_TAC INTINT_ENUM THEN
  REWRITE_TAC[EXISTS_PAIR_FUN_THM; PAIR_EQ; FORALL_PAIR_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kk:num->int` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `nn:num->int` THEN STRIP_TAC THEN
  EXISTS_TAC
   `\m. tau * &2 zpow ((kk:num->int) m) <
        real_integral (dyho (kk m) (nn m)) (\y. abs((h:real->real) y)) /\
        (!k' n'. kk m < k' /\ dyho (kk m) (nn m) SUBSET dyho k' n'
                 ==> ~(tau * &2 zpow k' <
                       real_integral (dyho k' n') (\y. abs(h y))))` THEN
  MP_TAC(ISPECL [`h:real->real`; `tau:real`] CZ_OM_EQ_UNION_MAXCELLS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(BETA_RULE(ISPEC `\k n. tau * &2 zpow k <
      real_integral (dyho k n) (\y. abs((h:real->real) y))`
      CZ_SELECTED_DISJOINT)) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[DYHO_INJ];
    REWRITE_TAC[UNIONS_GSPEC; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:int`
      (X_CHOOSE_THEN `n:int` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?m. (kk:num->int) m = k /\ (nn:num->int) m = n`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]);;

(* The average of h over a maximal stopping cell is at most 2 tau in         *)
(* absolute value (by the density bound CZ_MAXCELL_DENSITY).                 *)
let CZ_MAXCELL_AVG_BOUND = prove
 (`!(h:real->real) tau k n.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     tau * &2 zpow k < real_integral (dyho k n) (\y. abs(h y)) /\
     (!k' n'. k < k' /\ dyho k n SUBSET dyho k' n'
              ==> ~(tau * &2 zpow k' <
                    real_integral (dyho k' n') (\y. abs(h y))))
     ==> abs(real_integral (dyho k n) h / &2 zpow k) <= &2 * tau`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs x = x`;
               REAL_LE_LDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (dyho k n) (\y. abs((h:real->real) y))` THEN
  ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_LE; PERSCALE_ABSINT] THEN
  MP_TAC(ISPECL [`h:real->real`; `tau:real`; `k:int`; `n:int`]
    CZ_MAXCELL_DENSITY) THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]);;

(* The closed cubes [aa m,bb m] of a family of disjoint stopping cells       *)
(* dyho (kk m) (nn m), m with sel m.  Each cube contains its cell and has    *)
(* length 2^(kk m), which gives the scale conditions for Kc m = --kk m;      *)
(* distinct cubes meet in a null set, their union is measurable, and their   *)
(* total length is at most 2 mFW / tau when int |h| <= mFW.                  *)
let CZ_SELECTED_CLOSED_CUBES = prove
 (`!(h:real->real) tau mFW (kk:num->int) (nn:num->int) (sel:num->bool) aa bb.
     (!m. aa m = real_of_int(nn m) * &2 zpow (kk m) /\
          bb m = (real_of_int(nn m) + &1) * &2 zpow (kk m)) /\
     &0 < tau /\ (\y. abs(h y)) real_integrable_on (:real) /\
     real_integral (:real) (\y. abs(h y)) <= mFW /\ &0 <= mFW /\
     (!m. sel m ==> tau * &2 zpow (kk m) <
                    real_integral (dyho (kk m) (nn m)) (\y. abs(h y))) /\
     (!i j. sel i /\ sel j /\ ~(i = j)
            ==> DISJOINT (dyho (kk i) (nn i)) (dyho (kk j) (nn j)))
     ==> (!m. dyho (kk m) (nn m) SUBSET real_interval[aa m,bb m]) /\
         real_measurable (UNIONS {real_interval[aa n,bb n] | n | sel n}) /\
         (!k. aa k < bb k /\ inv(&2 zpow --(kk k)) <= bb k - aa k) /\
         (!k. &2 zpow --(kk k) * (bb k - aa k) / &2 <= &1) /\
         (!i j. sel i /\ sel j /\ ~(i = j)
                ==> real_negligible(real_interval[aa i,bb i] INTER
                                    real_interval[aa j,bb j])) /\
         (!N. sum {n | n IN 0..N /\ sel n} (\k. bb k - aa k)
              <= &2 * inv tau * mFW)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!N. sum {n | n IN 0..N /\ sel n} (\k. (bb:num->real) k - aa k)
        <= inv tau * real_integral (:real) (\y. abs((h:real->real) y))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC CZ_PARTIAL_WIDTH_SUM THEN
    MAP_EVERY EXISTS_TAC [`kk:num->int`; `nn:num->int`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. (aa:num->real) m < bb m /\
        inv(&2 zpow --((kk:num->int) m)) = bb m - aa m`
   ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CZ_CUBE_AABB_LT; REAL_ZPOW_NEG; REAL_INV_INV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[DYHO_SUBSET_CLOSED];
    MATCH_MP_TAC CZ_OM_MEASURABLE THEN
    EXISTS_TAC `inv tau * real_integral (:real) (\y. abs((h:real->real) y))`
    THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LE_REFL];
    GEN_TAC THEN MATCH_MP_TAC CZ_SCALE_ARITH THEN
    ASM_SIMP_TAC[REAL_ZPOW_LT; REAL_OF_NUM_LT; ARITH];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CZ_CLOSED_CUBE_NEGLIGIBLE_INTER THEN ASM_SIMP_TAC[];
    GEN_TAC THEN MATCH_MP_TAC CZ_WIDTH_SUM_ARITH THEN
    EXISTS_TAC `real_integral (:real) (\y. abs((h:real->real) y))` THEN
    ASM_REWRITE_TAC[]]);;

(* Given pairwise disjoint cells cell m (for the m with sel m) and constants *)
(* c m, there is a function equal to h - c m on each cell and to 0 off all   *)
(* the cells.                                                                *)
let DISJOINT_CELLS_STEP_FUNCTION = prove
 (`!(cell:num->real->bool) (c:num->real) (sel:num->bool) (h:real->real).
     (!i j. sel i /\ sel j /\ ~(i = j) ==> DISJOINT (cell i) (cell j))
     ==> ?bfun. (!m x. sel m /\ x IN cell m ==> bfun x = h x - c m) /\
                (!x. (!m. sel m ==> ~(x IN cell m)) ==> bfun x = &0)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\x. if ?m. (sel:num->bool) m /\ x IN (cell:num->real->bool) m
                  then (h:real->real) x - (c:num->real)
                                          (@m. sel m /\ x IN cell m)
                  else &0` THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o SELECT_RULE) THEN
    ASM_MESON_TAC[IN_DISJOINT];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* The bad part on one cube.  If bfun = h - (average of h on dyho k n) on a  *)
(* maximal stopping cell dyho k n, then on its closure [a,b] the function    *)
(* bfun is absolutely integrable, has integral 0 and has L^1 norm at most    *)
(* 2 (2 tau) (b - a).                                                        *)
let CZ_BAD_PART_ON_MAXCUBE = prove
 (`!(h:real->real) bfun tau k n a b.
     (\x. abs(h x)) real_integrable_on (:real) /\ &0 < tau /\
     (!a b. h absolutely_real_integrable_on real_interval[a,b]) /\
     tau * &2 zpow k < real_integral (dyho k n) (\y. abs(h y)) /\
     (!k' n'. k < k' /\ dyho k n SUBSET dyho k' n'
              ==> ~(tau * &2 zpow k' <
                    real_integral (dyho k' n') (\y. abs(h y)))) /\
     (!x. x IN dyho k n
          ==> bfun x = h x - real_integral (dyho k n) h / &2 zpow k) /\
     a = real_of_int n * &2 zpow k /\ b = (real_of_int n + &1) * &2 zpow k
     ==> bfun absolutely_real_integrable_on real_interval[a,b] /\
         real_integral (real_interval[a,b]) bfun = &0 /\
         real_integral (real_interval[a,b]) (\x. abs(bfun x))
           <= &2 * (&2 * tau) * (b - a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CZ_BAD_CUBE_PROPERTIES THEN
  MAP_EVERY EXISTS_TAC [`h:real->real`; `{b:real}`] THEN
  ASM_REWRITE_TAC[REAL_NEGLIGIBLE_SING; CZ_CUBE_AABB_LT] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CZ_MAXCUBE_BADPIECE_L1 THEN EXISTS_TAC `tau:real` THEN
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `real_integral (dyho k n) (h:real->real) =
    real_integral (real_interval[real_of_int n * &2 zpow k,
                                 (real_of_int n + &1) * &2 zpow k]) h`
   (SUBST_ALL_TAC o SYM) THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SPIKE_SET THEN
    MATCH_MP_TAC REAL_NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{(real_of_int n + &1) * &2 zpow k}` THEN
    REWRITE_TAC[REAL_NEGLIGIBLE_SING; dyho; SUBSET; IN_UNION; IN_DIFF;
                IN_ELIM_THM; IN_REAL_INTERVAL; IN_SING] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(x + &1) * y - x * y = y`] THEN
  REWRITE_TAC[IN_DIFF; IN_SING; IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[dyho; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC);;

(* The global estimates of a Calderon-Zygmund decomposition h = g + b.  The  *)
(* cells cell m (m with sel m) are disjoint, measurable and contained in the *)
(* measurable set Om, the constants c m satisfy |c m| <= 2 tau and           *)
(* c m * measure(cell m) = int_{cell m} h, b = h - c m on cell m and b = 0   *)
(* off the cells.  If |h| <= 1_Ff, int |h| <= mFW, and every dyadic cell     *)
(* containing a point outside the cells has average of |h| at most tau, then *)
(* g = h - b is measurable with g^2 integrable and int g^2 <= 2 tau mFW, and *)
(* b is absolutely integrable, vanishes off Om and |b| <= 1_Ff + 2 tau 1_Om. *)
let CZ_GOOD_BAD_ESTIMATES = prove
 (`!(h:real->real) bfun Ff Om (cell:num->real->bool) (c:num->real)
    (sel:num->bool) tau mFW.
     &0 < tau /\ &0 <= mFW /\ h real_measurable_on (:real) /\
     (\x. abs(h x)) real_integrable_on (:real) /\
     real_integral (:real) (\x. abs(h x)) <= mFW /\
     (!x. abs(h x) <= (if x IN Ff then &1 else &0)) /\ real_measurable Om /\
     (!m. real_measurable (cell m)) /\
     (!i j. sel i /\ sel j /\ ~(i = j) ==> DISJOINT (cell i) (cell j)) /\
     (!m. sel m ==> cell m SUBSET Om /\ abs(c m) <= &2 * tau /\
                    c m * real_measure (cell m) = real_integral (cell m) h) /\
     (!x. ~(x IN UNIONS {cell m | m | sel m})
          ==> !k n. x IN dyho k n
                    ==> real_integral (dyho k n) (\y. abs(h y))
                          <= tau * &2 zpow k) /\
     (!m x. sel m /\ x IN cell m ==> bfun x = h x - c m) /\
     (!x. (!m. sel m ==> ~(x IN cell m)) ==> bfun x = &0)
     ==> (\x. h x - bfun x) real_measurable_on (:real) /\
         (\x. (h x - bfun x) pow 2) real_integrable_on (:real) /\
         bfun absolutely_real_integrable_on (:real) /\
         (!x. ~(x IN Om) ==> bfun x = &0) /\
         (!x. abs(bfun x) <= (if x IN Ff then &1 else &0) +
                             (&2 * tau) * (if x IN Om then &1 else &0)) /\
         real_integral (:real) (\x. (h x - bfun x) pow 2) <= &2 * tau * mFW`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Omset = UNIONS {(cell:num->real->bool) m | m | sel m}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `Omset SUBSET Om /\ (!x. ~(x IN Omset) ==> (bfun:real->real) x = &0) /\
    (!x. x IN Omset
         ==> ?d. bfun x = (h:real->real) x - d /\ abs d <= &2 * tau)`
   STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Omset" THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real->real) absolutely_real_integrable_on (:real)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC
      REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x. abs((h:real->real) x)` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bfun:real->real) real_measurable_on (:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC CZ_STEP_MEASURABLE THEN
    MAP_EVERY EXISTS_TAC [`h:real->real`; `cell:num->real->bool`;
                          `c:num->real`; `sel:num->bool`] THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. abs((bfun:real->real) x) <=
        abs((h:real->real) x) + (&2 * tau) * (if x IN Om then &1 else &0) /\
        abs(h x - bfun x) <=
        abs(h x) + (&2 * tau) * (if x IN Om then &1 else &0)`
   ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CZ_BG_DOMINATED THEN
    MAP_EVERY EXISTS_TAC [`Omset:real->bool`; `tau:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. abs((h:real->real) x) + (&2 * tau) * (if x IN Om then &1 else &0))
    real_integrable_on (:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_ADD THEN
    ASM_SIMP_TAC[CZ_TAU_IND_OM_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(bfun:real->real) absolutely_real_integrable_on (:real)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC
      REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC
     `\x. abs((h:real->real) x) + (&2 * tau) * (if x IN Om then &1 else &0)`
    THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (h:real->real) x - bfun x) real_measurable_on (:real) /\
                (\x. abs(h x - bfun x)) real_integrable_on (:real)`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_ON_SUB] THEN
    MP_TAC(ISPECL [`h:real->real`; `bfun:real->real`; `(:real)`]
      ABSOLUTELY_REAL_INTEGRABLE_SUB) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[absolutely_real_integrable_on];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. abs((h:real->real) x) <= &1 /\
        abs(h x) + (&2 * tau) * (if x IN Om then &1 else &0) <= &1 + &2 * tau`
   ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o
      check (free_in `Ff:real->bool` o concl)) THEN
    COND_CASES_TAC THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. ((h:real->real) x - bfun x) pow 2) real_integrable_on (:real)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC(BETA_RULE(ISPECL
     [`\x. (h:real->real) x - bfun x`; `h:real->real`;
      `\x. abs((h:real->real) x) + (&2 * tau) * (if x IN Om then &1 else &0)`;
      `&2 * tau`] CZ_G2_INTEGRABLE)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (:real) (\x. abs((h:real->real) x - bfun x)) <= mFW`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (:real) (\x. abs((h:real->real) x))` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(BETA_RULE(ISPECL
     [`h:real->real`; `\x. (h:real->real) x - bfun x`;
      `cell:num->real->bool`; `c:num->real`; `sel:num->bool`]
     CZ_GOOD_L1_LE)) THEN
    ASM_SIMP_TAC[REAL_SUB_SUB2; REAL_SUB_RZERO] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC ABSINT_ON_LEBMEAS_SUBSET THEN
    EXISTS_TAC `(:real)` THEN
    ASM_SIMP_TAC[SUBSET_UNIV; REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `bfun:real->real`; `Omset:real->bool`;
                 `tau:real`] CZ_G_LE_2TAU_AE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV];
    DISCH_THEN(X_CHOOSE_THEN `e:real->bool` STRIP_ASSUME_TAC)] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[REAL_ARITH `a <= h + t /\ h <= f ==> a <= f + t`];
    MATCH_MP_TAC(BETA_RULE(ISPECL
     [`\x. (h:real->real) x - bfun x`; `mFW:real`; `tau:real`;
      `e:real->bool`] CZ_GOOD_L2_BOUND)) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* The dyadic Calderon-Zygmund decomposition at height tau of h with         *)
(* |h| <= 1_Ff.  The cubes are the closures of the maximal stopping cells    *)
(* (CZ_MAXCELL_ENUMERATION, CZ_SELECTED_CLOSED_CUBES), b is h minus its      *)
(* average on each cube and 0 elsewhere, and g = h - b                       *)
(* (CZ_GOOD_BAD_ESTIMATES, CZ_BAD_PART_ON_MAXCUBE).  The cubes of scale      *)
(* larger than a tile of P are separated from it, since no tile of P lies in *)
(* the superlevel set of the maximal function of 1_Ff, which contains the    *)
(* stopping set (CZ_OMSET_SUB_MAXFN, CZ_CUBE_TILE_SEP_OMSET).                *)
let CH_CZ_PRODUCER = prove
 (`!(P:(int#int#int)->bool) (t:int#int#int) (h:real->real) (Ff:real->bool)
    (ypt:int#int#int->real) (tau:real) (R:real) (mFW:real).
     FINITE P /\ &0 < tau /\ &0 < R /\ real_measurable Ff /\
     (!x. abs(h x) <= (if x IN Ff then &1 else &0)) /\
     h real_measurable_on (:real) /\
     (\x. abs(h x)) real_integrable_on (:real) /\
     real_integral (:real) (\x. abs(h x)) <= mFW /\ &0 <= mFW /\
     (!s. s IN P
          ==> ~(tile_I s SUBSET
                {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x}))
     ==> ?(g:real->real) (b:real->real) (Om:real->bool)
          (aa:num->real) (bb:num->real) (Kc:num->int) (sel:num->bool).
           (!x. h x = g x + b x) /\
           g real_measurable_on (:real) /\
           (\x. g x pow 2) real_integrable_on (:real) /\
           b absolutely_real_integrable_on (:real) /\
           real_measurable Om /\
           (!x. ~(x IN Om) ==> b x = &0) /\
           (!x. abs(b x) <= (if x IN Ff then &1 else &0) +
                            (&2 * tau) * (if x IN Om then &1 else &0)) /\
           real_integral (:real) (\x. g x pow 2) <= &2 * tau * mFW /\
           IMAGE lift Om =
           UNIONS {IMAGE lift (real_interval[aa n, bb n]) | n | sel n} /\
           (!i j. sel i /\ sel j /\
                  ~(IMAGE lift (real_interval[aa i, bb i]) =
                    IMAGE lift (real_interval[aa j, bb j]))
                  ==> negligible (IMAGE lift (real_interval[aa i, bb i]) INTER
                                  IMAGE lift (real_interval[aa j, bb j]))) /\
           (!k. sel k
                ==> aa k < bb k /\ inv(&2 zpow (Kc k)) <= bb k - aa k) /\
           (!k. sel k
                ==> b absolutely_real_integrable_on
                      (real_interval[aa k, bb k]) /\
                    real_integral (real_interval[aa k, bb k]) b = &0 /\
                    real_integral (real_interval[aa k, bb k]) (\x. abs(b x))
                      <= &2 * (&2 * tau) * (bb k - aa k)) /\
           (!s k. sel k
                  ==> (\z. Cx(b(drop z)) *
                           cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                               phi_sigma s carleson_phi (drop z)))
                      integrable_on (IMAGE lift (real_interval[aa k, bb k])) /\
                      (\x. abs(b x) * cw_tile s x) real_integrable_on
                        (real_interval[aa k, bb k]) /\
                      (\x. abs(b x) * cw_tile s x) real_integrable_on
                        {x | (if tile_xmid s < aa k then aa k - tile_xmid s
                              else tile_xmid s - bb k)
                             <= abs(x - tile_xmid s)} /\
                      (\x. abs(b x) * cw_tile s x) real_integrable_on
                        (:real) /\
                      (\x. (if x IN Ff then &1 else &0) * cw_tile s x)
                        real_integrable_on (:real) /\
                      (\x. (if x IN Om then &1 else &0) * cw_tile s x)
                        real_integrable_on (:real)) /\
           (!s k. s IN P /\ sel k /\ Kc k < tile_k s
                  ==> (bb k <= tile_xmid s - &2 zpow (--(tile_k s)) / &2 \/
                       tile_xmid s + &2 zpow (--(tile_k s)) / &2 <= aa k)) /\
           (!s k. s IN P /\ sel k /\ Kc k < tile_k s ==> Kc k <= tile_k s) /\
           (!i j. sel i /\ sel j /\ ~(i = j)
                  ==> real_negligible(real_interval[aa i, bb i] INTER
                                      real_interval[aa j, bb j])) /\
           (!k. sel k ==> &2 zpow (Kc k) * ((bb k - aa k) / &2) <= &1) /\
           (!N. sum {n | n IN 0..N /\ sel n} (\k. bb k - aa k)
             <= &2 * inv(tau) * mFW)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b. (h:real->real)
                 absolutely_real_integrable_on real_interval[a,b]`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `(:real)` THEN REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC
      REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\x. abs((h:real->real) x)` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  (* the maximal stopping cells, the bad part and the closed cubes *)
  MP_TAC(ISPECL [`h:real->real`; `tau:real`] CZ_MAXCELL_ENUMERATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num->int` (X_CHOOSE_THEN `nn:num->int`
    (X_CHOOSE_THEN `sel:num->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL
   [`\m. dyho ((kk:num->int) m) (nn m)`;
    `\m. real_integral (dyho ((kk:num->int) m) (nn m)) h / &2 zpow (kk m)`;
    `sel:num->bool`; `h:real->real`] DISJOINT_CELLS_STEP_FUNCTION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bfun:real->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?aa bb:num->real.
      !m. real_of_int((nn:num->int) m) * &2 zpow (kk m) = aa m /\
          (real_of_int(nn m) + &1) * &2 zpow (kk m) = bb m`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->real`; `tau:real`; `mFW:real`; `kk:num->int`;
                 `nn:num->int`; `sel:num->bool`; `aa:num->real`;
                 `bb:num->real`] CZ_SELECTED_CLOSED_CUBES) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x. (h:real->real) x - bfun x`; `bfun:real->real`;
    `UNIONS {real_interval[(aa:num->real) n,bb n] | n | sel n}`;
    `aa:num->real`; `bb:num->real`; `\m. --((kk:num->int) m)`;
    `sel:num->bool`] THEN
  REWRITE_TAC[REAL_SUB_ADD] THEN
  (* the estimates for the good and the bad part *)
  MP_TAC(ISPECL
   [`h:real->real`; `bfun:real->real`; `Ff:real->bool`;
    `UNIONS {real_interval[(aa:num->real) n,bb n] | n | sel n}`;
    `\m. dyho ((kk:num->int) m) (nn m)`;
    `\m. real_integral (dyho ((kk:num->int) m) (nn m)) h / &2 zpow (kk m)`;
    `sel:num->bool`; `tau:real`; `mFW:real`] CZ_GOOD_BAD_ESTIMATES) THEN
  ASM_REWRITE_TAC[DYHO_MEASURABLE] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(sel:num->bool) m`))
      THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MATCH_MP_TAC CZ_MAXCELL_AVG_BOUND THEN ASM_REWRITE_TAC[];
        SIMP_TAC[DYHO_MEASURE; REAL_DIV_RMUL; REAL_ZPOW_EQ_0;
                 REAL_OF_NUM_EQ; ARITH_EQ]];
      MATCH_MP_TAC CZ_OFF_OMSET_AVG THEN ASM_REWRITE_TAC[]];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[COVER_LIFT_DISTRIB] THEN REPEAT CONJ_TAC THENL
   [(* the lifted cubes *)
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    ASM_CASES_TAC `i:num = j` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM IMAGE_INTER_INJ; LIFT_EQ; GSYM real_negligible];
    (* the bad part on each cube *)
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(sel:num->bool) k`)) THEN
    MATCH_MP_TAC CZ_BAD_PART_ON_MAXCUBE THEN
    MAP_EVERY EXISTS_TAC [`h:real->real`; `(kk:num->int) k`;
                          `(nn:num->int) k`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    (* integrability against the tile weights *)
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[CZ_PACKET_INTEGRABLE; CZ_BCW_INTEGRABLE_ON;
                 REAL_LEBESGUE_MEASURABLE_INTERVAL; FAR_REGION_MEASURABLE;
                 REAL_LEBESGUE_MEASURABLE_UNIV; CH_INDCW_INTEGRABLE;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
    (* separation of the large cubes from the tiles of P *)
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real->real`; `Ff:real->bool`; `tau:real`]
      CZ_OMSET_SUB_MAXFN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`UNIONS {dyho ((kk:num->int) m) (nn m) | m | sel m}`;
                   `Ff:real->bool`; `s:int#int#int`; `(kk:num->int) k`;
                   `(nn:num->int) k`; `tau:real`] CZ_CUBE_TILE_SEP_OMSET) THEN
    ASM_SIMP_TAC[INT_ARITH `--a < b ==> --b < a:int`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    SIMP_TAC[INT_LT_IMP_LE]]);;

(* ========================================================================= *)
(* The near-tree energy bound CH_TREE_NEAR_CZ.  For the two modulated        *)
(* indicators cos(yt.) 1_FW and -sin(yt.) 1_FW, with FW =                    *)
(* Ff INTER ball(c,R), CH_CZ_PRODUCER gives the Calderon-Zygmund             *)
(* decomposition into good and bad parts.  Each bad-part tree energy is      *)
(* bounded by NEAR_CZ_H_EF_CF (that is, CH_CZ_EF_ENERGY_NEG) at level 2 tau  *)
(* and radius 4R (as |FW| <= 4R tau), and CH_TREE_NEAR_MODULO_BAD with the   *)
(* splitting into real and imaginary parts gives the bound C tau^2 R with    *)
(* C = 4 (Cmod + 32 Cf), where Cmod and Cf are the constants of these two    *)
(* lemmas.  The density points ypt s near the tiles s are chosen by the      *)
(* non-straddling hypothesis.                                                *)
(* ========================================================================= *)

(* The measure of the window: for FW = Ff INTER ball(c,R) with abs(y - c) <  *)
(* R and hl_maximal(1_Ff) y <= tau, measure FW <= 4 R tau, since the ball    *)
(* lies in [y - 2R, y + 2R] (AVG_LE_HL_MAXIMAL).                             *)

let CH_FW_MEASURE_LE = prove
 (`!(Ff:real->bool) (c:real) (R:real) (y:real) (tau:real).
     real_measurable Ff /\ &0 < R /\ abs(y - c) < R /\
     hl_maximal (\u. if u IN Ff then &1 else &0) y <= tau
     ==> real_measure (Ff INTER {x | abs(x - c) < R}) <= &4 * R * tau`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | abs(x - c) < R} = real_interval(c - R, c + R)`
    SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_measure (Ff INTER real_interval[y - &2 * R, y + &2 * R])` THEN
  CONJ_TAC THENL
   [(* measure(Ff INTER ball) <= measure(Ff INTER [y-2R,y+2R]) *)
    MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_INTER; REAL_MEASURABLE_REAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_REAL_INTERVAL] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    (* measure(Ff INTER [y-2R,y+2R]) = int_{[y-2R,y+2R]} 1_Ff <= M*(4R) <=   *)
    (* tau*(4R)                                                              *)
    ASM_SIMP_TAC[CH_MEASURE_INTER_EQ_INT; REAL_MEASURABLE_REAL_INTERVAL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hl_maximal (\u. if u IN Ff then &1 else &0) y * (&4 * R)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&4 * R = (y + &2 * R) - (y - &2 * R)` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC CH_HL_INDICATOR_STRADDLE THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `tau * (&4 * R)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN
         ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]]);;

(* per-tile density witness from the non-straddling hypothesis +             *)
(* CH_TILE_BAND                                                              *)
let NEAR_CZ_YPT_PERTILE = prove
 (`!Ff s tau. real_measurable Ff /\
     ~(tile_I s SUBSET
       {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x})
     ==> ?p. abs(p - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
             &0 <= hl_maximal (\u. if u IN Ff then &1 else &0) p /\
             hl_maximal (\u. if u IN Ff then &1 else &0) p <= tau`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET; IN_ELIM_THM; NOT_FORALL_THM;
    NOT_IMP; REAL_NOT_LT]) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real` THEN ASM_SIMP_TAC[CH_HL_INDICATOR_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 zpow (--tile_k s) / &2` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_TILE_BAND];
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 zpow (--tile_k s)` THEN CONJ_TAC THENL
     [SIMP_TAC[REAL_ZPOW_LE; REAL_POS; REAL_ARITH `&0 <= a ==> a / &2 <= a`];
      MATCH_MP_TAC ZPOW2_MONOE THEN INT_ARITH_TAC]]);;

(* window FW = Ff INTER ball(c,R) is negligible when hl_maximal(1_Ff) y = 0  *)
(* (tau = 0 case)                                                            *)
let NEAR_CZ_FW_NEGLIGIBLE = prove
 (`!Ff c R y. real_measurable Ff /\ &0 < R /\ abs(y - c) < R /\
     hl_maximal (\u. if u IN Ff then &1 else &0) y <= &0
     ==> real_negligible (Ff INTER {x | abs(x - c) < R})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_measurable (Ff INTER {x | abs(x - c) < R})`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_INTER; CH_WINDOW_EQ_INTERVAL;
     REAL_MEASURABLE_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Ff INTER {x | abs(x - c) < R}) = &0`
    ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Ff:real->bool`; `c:real`; `R:real`; `y:real`;
                   `&0:real`] CH_FW_MEASURE_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= m ==> m <= &4 * R * &0 ==> m = &0`) THEN
    ASM_SIMP_TAC[REAL_MEASURE_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_REAL_MEASURE_0] THEN
  SUBGOAL_THEN `real_measure (Ff INTER {x | abs(x - c) < R}) = &0`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV) [SYM th]) THEN
  ASM_REWRITE_TAC[GSYM HAS_REAL_MEASURE_MEASURE]);;

(* carleson_ip of a negligible-support indicator is 0                        *)
let NEAR_CZ_CARLESON_IP_NULL = prove
 (`!FW s. real_negligible FW
          ==> carleson_ip (\x. if x IN FW then Cx(&1) else Cx(&0)) s = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_ip; lproduct] THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  SUBGOAL_THEN `Cx(&0) = vec 0` SUBST1_TAC THENL
    [REWRITE_TAC[COMPLEX_VEC_0]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_INTEGRAL_NEGLIGIBLE THEN EXISTS_TAC `IMAGE lift FW` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[real_negligible]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
    X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((drop z) IN FW)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO]);;

(* int |h| <= measure FW  when |h| <= 1_FW                                   *)
let NEAR_CZ_INT_ABS_LE_MEASURE = prove
 (`!h FW. real_measurable FW /\ (\x. abs(h x)) real_integrable_on (:real) /\
     (!x. abs(h x) <= (if x IN FW then &1 else &0))
     ==> real_integral (:real) (\x. abs(h x)) <= real_measure FW`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `real_measure FW = real_integral (:real) (\x. if x IN FW then &1 else &0)`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_RESTRICT_UNIV; REAL_MEASURE_REAL_INTEGRAL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  MATCH_MP_TAC REAL_INTEGRABLE_ON_CONST_MEASURABLE THEN ASM_REWRITE_TAC[]);;

(* 1_(Ff INTER S) <= 1_Ff                                                    *)
let NEAR_CZ_IND_INTER_LE = prove
 (`!Ff S x. (if x IN ((Ff:A->bool) INTER S) then &1 else &0) <=
            (if x IN Ff then &1 else &0)`,
  REWRITE_TAC[IN_INTER] THEN
  REAL_ARITH_TAC);;

(* idempotence of the tree tile-set restriction                              *)
let NEAR_CZ_TILESET_IDEM = prove
 (`!P t. {s:int#int#int | s IN {s | s IN P /\ tile_ler s t} /\ tile_ler s t} =
         {s | s IN P /\ tile_ler s t}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* A window indicator modulated by a measurable u with |u| <= 1 (used with  *)
(* u = cos(yt.) and u = --sin(yt.)): bound, measurability, integrability,    *)
(* and integral <= measure.                                                  *)
let NEAR_CZ_H_FACTS = prove
 (`!Ff c R (u:real->real).
     real_measurable Ff /\ &0 < R /\
     u real_measurable_on (:real) /\ (!x. abs(u x) <= &1)
     ==> (!x. abs(u x * (if x IN (Ff INTER {x | abs(x - c) < R})
                         then &1 else &0))
              <= (if x IN Ff then &1 else &0)) /\
         (\x. u x * (if x IN (Ff INTER {x | abs(x - c) < R})
                     then &1 else &0)) real_measurable_on (:real) /\
         (\x. abs(u x * (if x IN (Ff INTER {x | abs(x - c) < R})
                         then &1 else &0))) real_integrable_on (:real) /\
         real_integral (:real)
           (\x. abs(u x * (if x IN (Ff INTER {x | abs(x - c) < R})
                           then &1 else &0)))
           <= real_measure (Ff INTER {x | abs(x - c) < R})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `FW = Ff INTER {x:real | abs(x - c) < R}` THEN
  SUBGOAL_THEN `real_measurable(FW:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "FW" THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_INTER; CH_WINDOW_EQ_INTERVAL;
                 REAL_MEASURABLE_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. abs((u:real->real) x * (if x IN FW then &1 else &0)) <=
        (if x IN FW then &1 else &0)`
  ASSUME_TAC THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. (u:real->real) x * (if x IN FW then &1 else &0))
    absolutely_real_integrable_on (:real)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
    ASM_SIMP_TAC[CH_INDICATOR_ABSINT; REAL_BOUNDED_POS; FORALL_IN_IMAGE] THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; NEAR_CZ_IND_INTER_LE];
    ASM_SIMP_TAC[INTEGRABLE_IMP_REAL_MEASURABLE;
                 ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[absolutely_real_integrable_on]) THEN
    STRIP_TAC;
    MATCH_MP_TAC NEAR_CZ_INT_ABS_LE_MEASURE THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[absolutely_real_integrable_on]) THEN
    STRIP_TAC]);;

(* The bad-part tree energy of a modulated indicator h: CH_CZ_PRODUCER       *)
(* applied to h, with the energy bounded by C (2 tau)^2 R through            *)
(* CH_CZ_EF_ENERGY_NEG.                                                      *)
let NEAR_CZ_H_EF_CF = prove
 (`?C. &0 <= C /\
       !Ff (P:(int#int#int)->bool) (t:int#int#int) tau R
        (ypt:int#int#int->real) (h:real->real) mFW.
         real_measurable Ff /\ FINITE {s | s IN P /\ tile_ler s t} /\
         &0 < tau /\ &0 < R /\
         (!x. abs(h x) <= (if x IN Ff then &1 else &0)) /\
         h real_measurable_on (:real) /\
         (\x. abs(h x)) real_integrable_on (:real) /\
         real_integral (:real) (\x. abs(h x)) <= mFW /\
         &0 <= mFW /\ mFW <= R * tau /\
         (!s. s IN {s | s IN P /\ tile_ler s t}
              ==> abs(ypt s - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
                  &0 <= hl_maximal (\uu. if uu IN Ff then &1 else &0)
                                   (ypt s) /\
                  hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s)
                  <= tau) /\
         (!s. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x}))
         ==> ?g b. (!x. h x = g x + b x) /\
                   g real_measurable_on (:real) /\
                   (\x. g x pow 2) real_integrable_on (:real) /\
                   b absolutely_real_integrable_on (:real) /\
                   real_integral (:real) (\x. g x pow 2) <= &2 * tau * mFW /\
                   sum {s | s IN P /\ tile_ler s t}
                       (\s. norm(integral (:real^1)
                              (\z. Cx(b(drop z)) *
                                   cnj(cexp(--(ii * Cx(tile_ymid t) *
                                               Cx(drop z))) *
                                       phi_sigma s carleson_phi (drop z))))
                            pow 2)
                   <= C * (&2 * tau) pow 2 * R`,
  X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)
    CH_CZ_EF_ENERGY_NEG THEN
  EXISTS_TAC `Cf:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{s:int#int#int | s IN P /\ tile_ler s t}`; `t:int#int#int`;
    `h:real->real`;
    `Ff:real->bool`; `ypt:int#int#int->real`; `tau:real`; `R:real`;
    `mFW:real`] CH_CZ_PRODUCER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real` (X_CHOOSE_THEN `bb0:real->real`
   (X_CHOOSE_THEN `Om:real->bool` (X_CHOOSE_THEN `aa:num->real`
    (X_CHOOSE_THEN `bb:num->real` (X_CHOOSE_THEN `Kc:num->int`
     (X_CHOOSE_THEN `sel:num->bool` STRIP_ASSUME_TAC))))))) THEN
  MAP_EVERY EXISTS_TAC [`g:real->real`; `bb0:real->real`] THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM NEAR_CZ_TILESET_IDEM] THEN
  FIRST_X_ASSUM(fun efp ->
    if free_in `Cf:real` (concl efp) && is_forall(concl efp)
    then MATCH_MP_TAC(SPECL
      [`{s:int#int#int | s IN P /\ tile_ler s t}`;
       `t:int#int#int`; `bb0:real->real`;
       `Ff:real->bool`; `Om:real->bool`; `ypt:int#int#int->real`;
       `aa:num->real`; `bb:num->real`; `Kc:num->int`; `sel:num->bool`;
       `&2 * tau:real`; `R:real`] efp)
    else failwith "not efp") THEN
  (* CH_CZ_EF_ENERGY_NEG at &2 * tau, using M(1_Ff)(ypt s) <= tau <= &2 *    *)
  (* tau                                                                     *)
  SUBGOAL_THEN
   `!s. s IN {s:int#int#int | s IN P /\ tile_ler s t}
        ==> abs((ypt:int#int#int->real) s - tile_xmid s) <=
              &2 zpow (&1 - tile_k s) /\
            &0 <= hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s) /\
            hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s) <= &2 * tau`
   ASSUME_TAC THENL
   [X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th ->
      if is_forall(concl th) && free_in `ypt:int#int#int->real` (concl th) &&
         free_in `hl_maximal` (concl th) && not(free_in `&2 * tau` (concl th))
      then MP_TAC(SPEC `s:int#int#int` th) else failwith "not ypt") THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THEN
  REPEAT(FIRST [GEN_TAC; DISCH_TAC]) THEN
    TRY(ASM_REWRITE_TAC[IN_ELIM_THM] THEN NO_TAC) THEN
  (* the positivity &0 < &2 * tau, then the width-sum bound sum widths <= &2 *)
  (* * R from mFW <= R * tau                                                 *)
  TRY(ASM_REAL_ARITH_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * inv(tau:real) * mFW:real` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(fun th -> MATCH_ACCEPT_TAC(SPEC `N:num` th)) ORELSE
    FIRST_ASSUM(fun th -> ACCEPT_TAC(SPEC `N:num` th));
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * inv(tau:real) * (R * tau)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_SIMP_TAC[REAL_FIELD
                     `&0 < tau ==> &2 * inv(tau) * (R * tau) = &2 * R`;
                   REAL_LE_REFL]]]);;

let CH_TREE_NEAR_CZ = prove
 (`?C. &0 <= C /\
   !Ff (P:(int#int#int)->bool) t c R y tau.
     real_measurable Ff /\ FINITE P /\ &0 <= tau /\ &0 < R /\ abs(y - c) < R /\
     hl_maximal (\u. if u IN Ff then &1 else &0) y <= tau /\
     (!s. s IN P /\ tile_ler s t
          ==> real_measure (Ff INTER tile_I s) <=
              tau * &4 * &2 zpow (&1 - tile_k s)) /\
     (!s. s IN P /\ tile_ler s t
          ==> ~(tile_I s SUBSET
                {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x}))
     ==> sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip (\x. if x IN Ff INTER {x | abs(x - c) < R}
                                        then Cx(&1) else Cx(&0)) s) pow 2)
         <= C * tau pow 2 * R`,
  X_CHOOSE_THEN `Cmod:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mod"))
    CH_TREE_NEAR_MODULO_BAD THEN
  X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ef"))
    NEAR_CZ_H_EF_CF THEN
  EXISTS_TAC `&4 * (Cmod + &32 * Cf)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Ff:real->bool`; `P:(int#int#int)->bool`;
                       `t:int#int#int`; `c:real`; `R:real`; `y:real`;
                       `tau:real`] THEN
  STRIP_TAC THEN
  (* ---- tau = 0 edge case ----                                             *)
  ASM_CASES_TAC `tau = &0` THENL
   [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {s | s IN P /\ tile_ler s t} (\s:int#int#int. &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
       SUBGOAL_THEN `real_negligible (Ff INTER {x | abs(x - c) < R})`
         MP_TAC THENL
       [MATCH_MP_TAC NEAR_CZ_FW_NEGLIGIBLE THEN EXISTS_TAC `y:real` THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN(fun th ->
          REWRITE_TAC[MATCH_MP NEAR_CZ_CARLESON_IP_NULL th]) THEN
        REWRITE_TAC[COMPLEX_NORM_0] THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      REWRITE_TAC[SUM_0; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* ---- the tree tile set is finite ----                                   *)
  SUBGOAL_THEN `FINITE {s:int#int#int | s IN P /\ tile_ler s t}`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  (* ypt by choice from the non-straddling hypothesis                        *)
  SUBGOAL_THEN
   `?ypt. !s. s IN {s | s IN P /\ tile_ler s t}
          ==> abs(ypt s - tile_xmid s) <= &2 zpow (&1 - tile_k s) /\
              &0 <= hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s) /\
              hl_maximal (\uu. if uu IN Ff then &1 else &0) (ypt s) <= tau`
   (X_CHOOSE_THEN `ypt:int#int#int->real` (LABEL_TAC "ypt")) THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN
    X_GEN_TAC `s:int#int#int` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `s IN P /\ tile_ler s t` THENL
     [ASM_SIMP_TAC[NEAR_CZ_YPT_PERTILE];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* ---- shared FW facts ----                                               *)
  SUBGOAL_THEN `real_measurable (Ff INTER {x | abs(x - c) < R})`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_INTER; CH_WINDOW_EQ_INTERVAL;
     REAL_MEASURABLE_REAL_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Ff INTER {x | abs(x - c) < R}) <= &4 * R * tau`
    ASSUME_TAC THENL
   [MATCH_MP_TAC CH_FW_MEASURE_LE THEN EXISTS_TAC `y:real` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (Ff INTER {x | abs(x - c) < R})`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Ff INTER {x | abs(x - c) < R}) <= (&4 * R) * tau`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * R * tau` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &4 * R * tau` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measure (Ff INTER {x | abs(x - c) < R}) <= &2 * (&4 * R) * tau`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&4 * R * tau` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* ---- the cos part, at energy radius &4 * R ----                         *)
  USE_THEN "ef" (MP_TAC o ISPECL
   [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`; `tau:real`;
    `&4 * R`; `ypt:int#int#int->real`;
    `\x. cos(tile_ymid t * x) *
         (if x IN (Ff INTER {x | abs(x - c) < R}) then &1 else &0)`;
    `real_measure (Ff INTER {x | abs(x - c) < R})`]) THEN
  ANTS_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`Ff:real->bool`; `c:real`; `R:real`;
                             `\x. cos(tile_ymid t * x)`] NEAR_CZ_H_FACTS)) THEN
    ASM_REWRITE_TAC[COS_BOUND; CH_COS_LIN_MEAS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gR:real->real`
    (X_CHOOSE_THEN `bR:real->real` STRIP_ASSUME_TAC)) THEN
  (* ---- the -sin part, at the same energy radius ----                      *)
  USE_THEN "ef" (MP_TAC o ISPECL
   [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`; `tau:real`;
    `&4 * R`; `ypt:int#int#int->real`;
    `\x. --sin(tile_ymid t * x) *
         (if x IN (Ff INTER {x | abs(x - c) < R}) then &1 else &0)`;
    `real_measure (Ff INTER {x | abs(x - c) < R})`]) THEN
  ANTS_TAC THENL
   [MP_TAC(BETA_RULE(ISPECL [`Ff:real->bool`; `c:real`; `R:real`;
                             `\x. --sin(tile_ymid t * x)`]
                            NEAR_CZ_H_FACTS)) THEN
    ASM_SIMP_TAC[REAL_ABS_NEG; SIN_BOUND; REAL_MEASURABLE_ON_NEG;
                 CH_SIN_LIN_MEAS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gI:real->real`
    (X_CHOOSE_THEN `bI:real->real` STRIP_ASSUME_TAC)) THEN
  (* the reduction to the bad-part energies, with radius &4 * R              *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `Cmod * tau pow 2 * (&4 * R) +
    &2 * sum {s | s IN P /\ tile_ler s t}
           (\s. norm(carleson_ip
                  (\x. cexp(ii * Cx(tile_ymid t) * Cx x) *
                       (Cx(bR x) + ii * Cx(bI x))) s) pow 2)` THEN
  CONJ_TAC THENL
   [USE_THEN "mod" (fun th -> MATCH_MP_TAC(SPECL
      [`tile_ymid t`; `Ff INTER {x | abs(x - c) < R}`; `gR:real->real`;
       `bR:real->real`; `gI:real->real`;
       `bI:real->real`; `P:(int#int#int)->bool`; `t:int#int#int`;
       `real_measure(Ff INTER {x | abs(x - c) < R})`;
       `&4 * R`; `tau:real`;
       `sum {s | s IN P /\ tile_ler s t}
          (\s. norm(carleson_ip
                 (\x. cexp(ii * Cx(tile_ymid t) * Cx x) *
                      (Cx(bR x) + ii * Cx(bI x))) s) pow 2)`] th)) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(ONCE_DEPTH_CONV BETA_CONV))) THEN
    REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `Cmod * tau pow 2 * (&4 * R) +
    &2 * (&2 * sum {s | s IN P /\ tile_ler s t}
                (\s. norm(integral (:real^1)
                       (\z. Cx(bR(drop z)) *
                            cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                                phi_sigma s carleson_phi (drop z)))) pow 2)
        + &2 * sum {s | s IN P /\ tile_ler s t}
                (\s. norm(integral (:real^1)
                       (\z. (ii * Cx(bI(drop z))) *
                            cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                                phi_sigma s carleson_phi (drop z))))
                     pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LADD_IMP THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CH_BADENERGY_REIM_SPLIT THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `s:int#int#int` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_BADPAIR_R_INTEGRABLE];
      MATCH_MP_TAC CH_BADPAIR_iI_INTEGRABLE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {s | s IN P /\ tile_ler s t}
        (\s. norm(integral (:real^1)
               (\z. (ii * Cx(bI(drop z))) *
                    cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2) =
    sum {s | s IN P /\ tile_ler s t}
        (\s. norm(integral (:real^1)
               (\z. Cx(bI(drop z)) *
                    cnj(cexp(--(ii * Cx(tile_ymid t) * Cx(drop z))) *
                        phi_sigma s carleson_phi (drop z)))) pow 2)`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[CH_BADIP_II_NORM;
     CH_BADPAIR_R_INTEGRABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(&4 * (Cmod + &32 * Cf)) * tau pow 2 * R =
                (Cmod + &8 * (&4 * Cf)) * (tau pow 2 * (&4 * R))`
   SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CH_BADENERGY_ARITH THEN
  (* the side conditions: &0 <= &4 Cf; the energy bounds for bR and bI by    *)
  (* (&4 Cf) tau^2 (&4 R), from NEAR_CZ_H_EF_CF since (&2 tau) pow 2 = &4    *)
  (* tau^2; and &0 <= tau^2 (&4 R)                                           *)
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(fun th -> if free_in `bR:real->real` (concl th) &&
        can (find_term (fun t -> is_binary "real_le" t)) (concl th)
          && not(is_forall(concl th))
        then MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `b = a ==> x <= b ==> x <= a`) THEN
    CONV_TAC REAL_RING;
    FIRST_X_ASSUM(fun th -> if free_in `bI:real->real` (concl th) &&
        can (find_term (fun t -> is_binary "real_le" t)) (concl th)
          && not(is_forall(concl th))
        then MP_TAC th else NO_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `b = a ==> x <= b ==> x <= a`) THEN
    CONV_TAC REAL_RING;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE];
      ASM_REAL_ARITH_TAC]]);;

(* The tree energy of an indicator modulo the far part: the near part is     *)
(* bounded by CH_TREE_NEAR_CZ, and the far part (Ff DIFF the window) enters  *)
(* through its energy B.                                                     *)
let CH_TREE_ENERGY_MODULO_FAR = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (P:(int#int#int)->bool) t c R y tau B.
        real_measurable Ff /\ FINITE P /\ &0 <= tau /\ &0 < R /\
        abs(y - c) < R /\
        hl_maximal (\u. if u IN Ff then &1 else &0) y <= tau /\
        (!s. s IN P /\ tile_ler s t
             ==> real_measure (Ff INTER tile_I s)
                 <= tau * (&4 * &2 zpow (&1 - tile_k s))) /\
        (!s. s IN P /\ tile_ler s t
             ==> ~(tile_I s SUBSET
                   {x | tau <
                        hl_maximal (\u. if u IN Ff then &1 else &0) x})) /\
        sum {s | s IN P /\ tile_ler s t}
            (\s. norm(carleson_ip
                   (\x. if x IN (Ff DIFF {x | abs(x - c) < R}) then Cx(&1)
                        else Cx(&0)) s) pow 2) <= B
        ==> sum {s | s IN P /\ tile_ler s t}
                (\s. norm(carleson_ip
                       (\x. if x IN Ff then Cx(&1) else Cx(&0)) s) pow 2)
            <= C * tau pow 2 * R + &2 * B`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near"))
    CH_TREE_NEAR_CZ THEN
  EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC
    [`Ff:real->bool`; `P:(int#int#int)->bool`;
     `t:int#int#int`; `c:real`; `R:real`;
     `y:real`; `tau:real`; `B:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. if x IN (Ff INTER {x | abs(x - c) < R})
                         then Cx(&1) else Cx(&0)) s) pow 2)
    + &2 * sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. if x IN (Ff DIFF {x | abs(x - c) < R})
                         then Cx(&1) else Cx(&0)) s) pow 2)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CH_TREE_SUM_SPLIT; CH_WINDOW_EQ_INTERVAL;
     REAL_MEASURABLE_REAL_INTERVAL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (C * tau pow 2 * R)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      USE_THEN "near" (fun th -> MATCH_MP_TAC
        (SPECL [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`;
                `c:real`; `R:real`; `y:real`; `tau:real`] th)) THEN
      ASM_REWRITE_TAC[];
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The tree energy of an indicator (Grafakos-Tao-Terwilleger, Lemma 1), in   *)
(* the form where the density points ypt t are only required for the tiles t *)
(* with nonempty trees.                                                      *)
(* ========================================================================= *)

(* An empty tree has delta_f = 0.                                            *)
let DELTA_EMPTY_TREE = prove
 (`!(f:real->complex) (P:(int#int#int)->bool) (t:int#int#int).
     tile_tree P t = {} ==> delta_f f (tile_tree P t) = &0`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[delta_f; SUM_CLAUSES]);;

let CH_GTT_LEMMA1_SCOPED = prove
 (`?C. &0 <= C /\
    !(Ff:real->bool) (P:(int#int#int)->bool) (ypt:int#int#int->real) tau.
       real_measurable Ff /\ FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN Ff then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau < hl_maximal (\u. if u IN Ff then &1 else &0) x}))
       ==> energy_f (\x. if x IN Ff then Cx(&1) else Cx(&0)) P <= C * tau`,
  X_CHOOSE_THEN `Cg:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "glue"))
    CH_TREE_ENERGY_MODULO_FAR THEN
  X_CHOOSE_THEN `Cf:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "far"))
    FAR_TREE_ENERGY THEN
  ABBREV_TAC `D = &2 * Cg + (&2 / &15) * Cf` THEN
  SUBGOAL_THEN `&0 <= D` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `sqrt D` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SQRT_POS_LE]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Ff:real->bool`; `P:(int#int#int)->bool`;
                       `ypt:int#int#int->real`; `tau:real`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC ENERGY_THRESHOLD THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
  X_GEN_TAC `t:int#int#int` THEN
  ASM_CASES_TAC `tile_tree P (t:int#int#int) = {}` THENL
   [ASM_SIMP_TAC[DELTA_EMPTY_TREE; REAL_MUL_RZERO; REAL_LE_POW_2];
     ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(ypt(t:int#int#int) - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
    hl_maximal (\u. if u IN Ff then &1 else &0) (ypt t) <= tau`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:int#int#int. s IN P /\ tile_ler s t
      ==> real_measure (Ff INTER tile_I s) <=
          tau * (&4 * &2 zpow (&1 - tile_k s))`
   (LABEL_TAC "densh") THENL
   [X_GEN_TAC `s:int#int#int` THEN STRIP_TAC THEN
    SUBGOAL_THEN
      `abs(ypt(s:int#int#int) - tile_xmid s) < &2 zpow (&1 - tile_k s) /\
       hl_maximal (\u. if u IN Ff then &1 else &0) (ypt s) <= tau`
      STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:int#int#int` o
        check (fun th -> is_forall(concl th) &&
                         (let b = snd(dest_forall(concl th)) in
                          is_imp b && is_conj(snd(dest_imp b))))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `s:int#int#int` THEN
        ASM_REWRITE_TAC[tile_tree; IN_ELIM_THM; TILE_LER_REFL];
        ASM_REWRITE_TAC[]]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hl_maximal (\u. if u IN Ff then &1 else &0) (ypt s) *
                (&4 * &2 zpow (&1 - tile_k s))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CH_TILE_DENSITY_BRIDGE];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[CH_DELTA_TILE_TREE] THEN
  SUBGOAL_THEN `(sqrt D * tau) pow 2 = D * tau pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 zpow (tile_k t) *
    (Cg * tau pow 2 * (&2 zpow (&1 - tile_k t)) +
     &2 * ((Cf * (hl_maximal (\u. if u IN Ff then &1 else &0) (ypt t)) pow 2 *
            inv((&2 zpow (tile_k t)) pow 5) *
            inv(((&2 zpow (&1 - tile_k t)) pow 2) pow 2)) * (&16 / &15)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "glue" (fun th -> MATCH_MP_TAC (SPECL
      [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`;
       `tile_xmid t`;
       `&2 zpow (&1 - tile_k t)`; `ypt(t:int#int#int):real`; `tau:real`;
       `(Cf * (hl_maximal (\u. if u IN Ff then &1 else &0) (ypt t)) pow 2 *
         inv((&2 zpow (tile_k t)) pow 5) *
         inv(((&2 zpow (&1 - tile_k t)) pow 2) pow 2)) *
        (&16 / &15)`] th)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CH_DIFF_WINDOW_EQ] THEN
      USE_THEN "far" (MP_TAC o SPECL
       [`Ff:real->bool`; `P:(int#int#int)->bool`; `t:int#int#int`;
        `ypt(t:int#int#int):real`;
        `&2 zpow (&1 - tile_k t)`]) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[ZPOW_HALF_LE] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN ACCEPT_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `a = &2 zpow (tile_k t)` THEN
  ABBREV_TAC `Mv = hl_maximal (\u. if u IN Ff then &1 else &0)
               (ypt(t:int#int#int))` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Mv` ASSUME_TAC THENL
   [EXPAND_TAC "Mv" THEN MATCH_MP_TAC CH_HL_INDICATOR_POS THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow (&1 - tile_k t) = &2 * inv a` ASSUME_TAC THENL
   [REWRITE_TAC[ZPOW_ONE_SUB]; ALL_TAC] THEN
  ASM_SIMP_TAC[BUDGET_COLLAPSE] THEN
  EXPAND_TAC "D" THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * Cg * tau pow 2 + (&2 / &15) * Cf * tau pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_POW_2] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[]];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The capped descent for the tile model.  Fremlin 286M (M286_STEPS,         *)
(* CARLESON_286M_FINITE) runs the coupled energy and mass stopping-time      *)
(* descent at a cost of C7 (C5 + C6) min(level, 1/level) per step.  When the *)
(* energy of the whole tile set is bounded a priori by e0 (as for            *)
(* non-straddling tiles, where e0 ~ |G|/|E| by CH_GTT_LEMMA1_SCOPED), each   *)
(* step costs only C7 (C5 + C6) min(e0, level), and the total is C (C5 + C6) *)
(* e0 (N + 2) whenever (1/2)^N <= e0.  With C5 ~ |E'| (the mass budget) and  *)
(* C6 ~ |G| (the energy budget) this is the bound |G| (1 + log(|E|/|G|)) of  *)
(* the small regime; the logarithm cannot be avoided (without it one would   *)
(* have restricted weak type (1,1)).                                         *)
(* ========================================================================= *)

let SUM_MIN_CAP_STEP = prove
 (`!e0 N M. &0 <= e0 /\
     sum {n | n < M} (\n. min e0 (inv(&2) pow n)) <=
       (if M <= N then &M * e0
        else &N * e0 + &2 * inv(&2) pow N - &2 * inv(&2) pow M)
     ==> sum {n | n < SUC M} (\n. min e0 (inv(&2) pow n)) <=
         (if SUC M <= N then &(SUC M) * e0
          else &N * e0 + &2 * inv(&2) pow N - &2 * inv(&2) pow (SUC M))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{n | n < SUC M} = M INSERT {n | n < M}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
     ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  SUBGOAL_THEN `inv(&2) pow SUC M = inv(&2) pow M / &2` SUBST1_TAC THENL
   [REWRITE_TAC[real_pow] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  ABBREV_TAC `S = sum {n | n < M} (\n. min e0 (inv(&2) pow n))` THEN
  ABBREV_TAC `q = inv(&2) pow M` THEN
  ABBREV_TAC `r = inv(&2) pow N` THEN
  ASM_CASES_TAC `M:num < N` THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(SUC M <= N)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `M:num = N` THENL
   [SUBGOAL_THEN `(r:real) = q` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((M:num) <= N)` ASSUME_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SUM_MIN_CAP_GEOM_STRONG = prove
 (`!e0 N M. &0 <= e0
     ==> sum {n | n < M} (\n. min e0 (inv(&2) pow n)) <=
         (if M <= N then &M * e0
          else &N * e0 + &2 * inv(&2) pow N - &2 * inv(&2) pow M)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[CONJUNCT1 LT; EMPTY_GSPEC; SUM_CLAUSES;
     LE_0] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_MIN_CAP_STEP]]);;

let SUM_MIN_CAP_GEOM = prove
 (`!e0 N M. &0 <= e0 /\ inv(&2) pow N <= e0
     ==> sum {n | n < M} (\n. min e0 (inv(&2) pow n)) <= e0 * (&N + &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e0:real`; `N:num`; `M:num`] SUM_MIN_CAP_GEOM_STRONG) THEN
  ABBREV_TAC `S = sum {n | n < M} (\n. min e0 (inv(&2) pow n))` THEN
  SUBGOAL_THEN `&0 <= inv(&2) pow M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `&M <= &N` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `&M * e0 <= &N * e0` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* 286M with an a priori energy cap e0 <= 1: if (1/2)^N <= e0 the sum over   *)
(* P is at most C (C5 + C6) e0 (N + 2).  The instance k = 0 of               *)
(* CARLESON_286M_FINITE_GEN, with the capped geometric partial sums bounded  *)
(* by SUM_MIN_CAP_GEOM.                                                      *)
let CARLESON_286M_CAP = prove
 (`?C. &0 <= C /\
   !(f:real->complex) E h (P:(int#int#int)->bool) C5 C6 e0 N.
      carleson_mass_budget f E h C5 /\ carleson_energy_budget f C6 /\
      &0 <= C5 /\ &0 <= C6 /\ FINITE P /\
      (!t. cw_tile t real_integrable_on {x | x IN E /\ h x IN tile_J t}) /\
      real_lebesgue_measurable E /\ h real_measurable_on (:real) /\
      energy_f f P <= e0 /\ e0 <= &1 /\ inv(&2) pow N <= e0
      ==> sum P (\s. norm(carleson_ip f s *
                integral (IMAGE lift {x | x IN E /\ h x IN tile_Jr s})
                     (\z. phi_sigma s carleson_phi (drop z))))
          <= C * (C5 + C6) * e0 * (&N + &2)`,
  X_CHOOSE_THEN `C7:real` STRIP_ASSUME_TAC CARLESON_286M_FINITE_GEN THEN
  EXISTS_TAC `C7:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `e0:real`; `\n. min e0 (inv(&2) pow n)`] THEN
  SUBGOAL_THEN `&0 <= e0` ASSUME_TAC THENL
   [ASM_MESON_TAC[ENERGY_F_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_MIN_CAP_GEOM; real_pow; REAL_MUL_LID] THEN
  REPEAT STRIP_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[MASS_LE_1; SQRT_1; SQRT_MONO_LE];
    REAL_ARITH_TAC]);;

(* mass budget with the first-power |E| constant (CARLESON_286J without mu E *)
(* <= 1)                                                                     *)
let CARLESON_286J_GEN = prove
 (`!(f:real->complex) E h.
     real_lebesgue_measurable E /\ real_measurable E /\
     h real_measurable_on (:real)
     ==> carleson_mass_budget f E h (&2 pow 12 * real_measure E)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[carleson_mass_budget] THEN
  MAP_EVERY X_GEN_TAC [`P:(int#int#int)->bool`; `gam:real`] THEN STRIP_TAC THEN
  EXISTS_TAC `carleson_jR E h (gam pow 2 / &4) P` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CARLESON_JR_FINITE];
    ASM_SIMP_TAC[CARLESON_JR_BUDGET];
    ASM_SIMP_TAC[CARLESON_JMASS_BOUND]]);;

let CARLESON_IP_CMUL_L2 = prove
 (`!(f:real->complex) (c:complex) s.
     (\z. f(drop z)) IN lspace (:real^1) (&2)
     ==> carleson_ip (\x. c * f x) s = c * carleson_ip f s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_ip] THEN
  MP_TAC(ISPECL [`(:real^1)`; `\z:real^1. (f:real->complex)(drop z)`;
                 `\z:real^1. phi_sigma s carleson_phi (drop z)`;
                 `c:complex`] LPRODUCT_LMUL) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC L2_CNJ_PRODUCT_INTEGRABLE THEN
    ASM_REWRITE_TAC[PHISIG_IN_LSPACE2]);;

let ENERGY_F_COEFF_LE = prove
 (`!(f:real->complex) (g:real->complex) (P:(int#int#int)->bool) a.
     FINITE P /\ &0 <= a /\
     (!s. s IN P ==> norm(carleson_ip g s) <= a * norm(carleson_ip f s))
     ==> energy_f g P <= a * energy_f f P`,
  REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ENERGY_THRESHOLD THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[REAL_LE_MUL; ENERGY_F_POS]; ALL_TAC] THEN
  X_GEN_TAC `t:int#int#int` THEN REWRITE_TAC[delta_f; tile_tree] THEN
  ABBREV_TAC `Sf = sum {s | s IN P /\ tile_ler s t}
                       (\s. norm(carleson_ip (f:real->complex) s) pow 2)` THEN
  SUBGOAL_THEN `&0 <= Sf` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUM_POS_LE; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k t)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum {s | s IN P /\ tile_ler s t}
                    (\s. norm(carleson_ip (g:real->complex) s) pow 2)
                <= a pow 2 * Sf` ASSUME_TAC THENL
   [EXPAND_TAC "Sf" THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
     MATCH_MP_TAC SUM_LE THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:(int#int#int)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `s:int#int#int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[NORM_POS_LE] THEN
      FIRST_X_ASSUM MATCH_MP_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real->complex`; `P:(int#int#int)->bool`; `t:int#int#int`]
    ENERGY_TERM_LE_SELF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&2 zpow (tile_k t) * Sf <= energy_f (f:real->complex) P pow 2`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_LE2;
     REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 zpow (tile_k t) * (a pow 2 * Sf)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  SUBGOAL_THEN `&2 zpow (tile_k t) * (a pow 2 * Sf) =
                a pow 2 * (&2 zpow (tile_k t) * Sf)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let CARLESON_IP_ZERO_LNORM = prove
 (`!(f:real->complex) s.
     (\z. f(drop z)) IN lspace (:real^1) (&2) /\
     lnorm (:real^1) (&2) (\z. f(drop z)) = &0
     ==> carleson_ip f s = Cx(&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
    REWRITE_TAC[NORM_POS_LE; carleson_ip] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z)) *
    lnorm (:real^1) (&2) (\z. phi_sigma s carleson_phi (drop z))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[LPRODUCT_CAUCHY_SCHWARZ; PHISIG_IN_LSPACE2;
     L2_CNJ_PRODUCT_INTEGRABLE];
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_REFL]]);;

let CARLESON_ENERGY_BUDGET_L2 = prove
 (`?C6. &0 <= C6 /\
    !f. (\z. f(drop z)) IN lspace (:real^1) (&2)
        ==> carleson_energy_budget f
              (C6 * lnorm (:real^1) (&2) (\z. f(drop z)) pow 2)`,
  X_CHOOSE_THEN `C6:real` STRIP_ASSUME_TAC CARLESON_286K THEN
  EXISTS_TAC `C6:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `f:real->complex` THEN DISCH_TAC THEN
  ABBREV_TAC `L = lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z))` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [ASM_MESON_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[carleson_energy_budget] THEN
  MAP_EVERY X_GEN_TAC [`P:(int#int#int)->bool`; `gam:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `L = &0` THENL
   [EXISTS_TAC `{}:(int#int#int)->bool` THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; SUM_CLAUSES] THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH_EQ; REAL_MUL_RZERO; REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&0 * energy_f (f:real->complex) (P DIFF tile_upset {})` THEN
      CONJ_TAC THENL
     [ASM_SIMP_TAC[ENERGY_F_COEFF_LE; FINITE_DIFF; REAL_LE_REFL;
       REAL_MUL_LZERO; NORM_LE_0; COMPLEX_VEC_0; CARLESON_IP_ZERO_LNORM];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `g = \x. Cx(inv L) * (f:real->complex) x` THEN
  SUBGOAL_THEN `(\z. (g:real->complex)(drop z)) IN lspace (:real^1) (&2) /\
                lnorm (:real^1) (&2) (\z. g(drop z)) <= &1`
                  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[GSYM COMPLEX_CMUL] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[LSPACE_CMUL];
      MP_TAC(ISPECL [`(:real^1)`; `&2`; `\z. (f:real->complex)(drop z)`;
                     `inv L`] LNORM_MUL) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `abs(inv L) * L = &1`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < L ==> abs L = L`] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. norm(carleson_ip (g:real->complex) s) =
                    inv L * norm(carleson_ip (f:real->complex) s)`
    ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN ASM_SIMP_TAC[CARLESON_IP_CMUL_L2] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < L ==> abs L = L`];
      ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:real->complex`) THEN
    ASM_REWRITE_TAC[carleson_energy_budget] THEN
  DISCH_THEN(MP_TAC o SPECL [`P:(int#int#int)->bool`; `gam / L`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv L * energy_f (f:real->complex) P` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ENERGY_F_COEFF_LE; REAL_LE_INV_EQ; REAL_LE_REFL];
      REWRITE_TAC[real_div] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:(int#int#int)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `R1:(int#int#int)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
   [SUBGOAL_THEN `gam pow 2 * sum R1 (\t. &2 zpow --tile_k t) =
                  ((gam / L) pow 2 * sum R1 (\t. &2 zpow --tile_k t)) *
                    L pow 2` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `L * energy_f (g:real->complex) (P DIFF tile_upset R1)` THEN
      CONJ_TAC THENL
     [MATCH_MP_TAC ENERGY_F_COEFF_LE THEN
       ASM_SIMP_TAC[FINITE_DIFF; REAL_MUL_ASSOC; REAL_MUL_RINV] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `L * ((gam / L) / &2)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_LMUL];
        SUBGOAL_THEN `L * ((gam / L) / &2) = gam / &2` SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < L` THEN CONV_TAC REAL_FIELD; REAL_ARITH_TAC]]]]);;

(* the capped forest bound with concrete budgets: (2^12 |E| + C6 ||f||_2^2)  *)
(* e0 (N+2)                                                                  *)
let CARLESON_TILESUM_CAP = prove
 (`?C C6. &0 <= C /\ &0 <= C6 /\
     !(f:real->complex) E h (P:(int#int#int)->bool) e0 N.
        (\z. f(drop z)) IN lspace (:real^1) (&2) /\
        real_lebesgue_measurable E /\ real_measurable E /\
        h real_measurable_on (:real) /\
        FINITE P /\
        (!t. cw_tile t real_integrable_on {x | x IN E /\ h x IN tile_J t}) /\
        energy_f f P <= e0 /\ e0 <= &1 /\ inv(&2) pow N <= e0
        ==> sum P (\s. norm(carleson_ip f s *
                  integral (IMAGE lift {x | x IN E /\ h x IN tile_Jr s})
                       (\z. phi_sigma s carleson_phi (drop z))))
            <= C * (&2 pow 12 * real_measure E +
                    C6 * lnorm (:real^1) (&2) (\z. f(drop z)) pow 2) *
               e0 * (&N + &2)`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC CARLESON_286M_CAP THEN
  X_CHOOSE_THEN `C6:real` STRIP_ASSUME_TAC CARLESON_ENERGY_BUDGET_L2 THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `C6:real`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`f:real->complex`; `E:real->bool`; `h:real->real`; `P:(int#int#int)->bool`;
    `&2 pow 12 * real_measure E`;
    `C6 * lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z)) pow 2`;
    `e0:real`; `N:num`] o
   check(fun th -> is_forall(concl th) &&
     can (find_term (fun t -> t = `carleson_mass_budget`)) (concl th))) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CARLESON_286J_GEN];
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_MEASURE_POS_LE]];
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_POW_2]]);;

(* ========================================================================= *)
(* The energy of functions dominated by an indicator.  CH_GTT_LEMMA1_SCOPED, *)
(* proved for indicators 1_F, extends to every f with |f| <= 1_G by a        *)
(* discretized layer cake:                                                   *)
(*   u_N = (1/N) sum_{m=1..N} 1_{G_m},   G_m = {x | m < N u x} SUBSET G,     *)
(* with |u - u_N| <= 1/N and |avg a|^2 <= avg |a|^2 (finite convexity).  So  *)
(* each tree carries at most (C tau)^2 for u_N, then for u (letting N ->     *)
(* oo), and then for complex f via the four nonnegative parts.               *)
(* ========================================================================= *)

let RF_IND_INT_MEASURE = prove
 (`!G a b. real_measurable G
     ==> real_integral (real_interval[a,b])
                       (\t. abs(if t IN G then &1 else &0)) =
         real_measure (G INTER real_interval[a,b])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\t. abs(if t IN G then &1 else &0)) =
                (\t. if t IN G then (\x:real. &1) t else &0)`
    SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_INTEGRAL_RESTRICT_INTER] THEN
  MATCH_MP_TAC REAL_INTEGRAL_REAL_MEASURE THEN
  MATCH_MP_TAC REAL_MEASURABLE_INTER THEN
    ASM_REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL]);;

let HL_MAXIMAL_IND_SUBSET_LE = prove
 (`!G' G x. real_measurable G /\ real_measurable G' /\ G' SUBSET G
     ==> hl_maximal (\t. if t IN G' then &1 else &0) x <=
         hl_maximal (\t. if t IN G then &1 else &0) x`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [hl_maximal] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `real_integral (real_interval[x - &1,x + &1])
         (\t. abs(if t IN G' then &1 else &0)) / ((x + &1) - (x - &1))` THEN
    MAP_EVERY EXISTS_TAC [`x - &1`; `x + &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_integral (real_interval[a,b]) (\t. abs(if t IN G then &1 else &0)) /
    (b - a)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < b - a` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; RF_IND_INT_MEASURE] THEN
    MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_MEASURABLE_INTER) THEN
    ASM_REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL] THEN ASM SET_TAC[];
    MATCH_MP_TAC AVG_LE_HL_MAXIMAL THEN
      EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
      MATCH_MP_TAC CH_INDICATOR_AVG_LE_1 THEN ASM_REWRITE_TAC[]]);;

let ENERGY_IND_SUBSET_CAP = prove
 (`?C. &0 <= C /\
    !(G:real->bool) G' (P:(int#int#int)->bool) (ypt:int#int#int->real) tau.
       real_measurable G /\ real_measurable G' /\ G' SUBSET G /\
       FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN G then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau <
                         hl_maximal (\u. if u IN G then &1 else &0) x}))
       ==> energy_f (\x. if x IN G' then Cx(&1) else Cx(&0)) P <= C * tau`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC CH_GTT_LEMMA1_SCOPED THEN
  EXISTS_TAC `C:real` THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`G':real->bool`; `P:(int#int#int)->bool`;
                                 `ypt:int#int#int->real`; `tau:real`] o
    check(fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `energy_f`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; HL_MAXIMAL_IND_SUBSET_LE];
    MAP_EVERY X_GEN_TAC [`s:int#int#int`; `t:int#int#int`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:int#int#int`; `t:int#int#int`] o
      check(fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `tile_I`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> ~b`) THEN DISCH_TAC THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `hl_maximal (\u. if u IN G' then &1 else &0) y` THEN
      CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      ASM_SIMP_TAC[HL_MAXIMAL_IND_SUBSET_LE]]]);;

(* counting: all of 1..N lie below r when N < r                              *)
let SUM_IND_LT_ALL = prove
 (`!N r. &N < r ==> sum (1..N) (\m. if &m < r then &1 else &0) = &N`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum (1..N) (\m. if &m < r then &1 else &0) =
                sum (1..N) (\m. &1)` SUBST1_TAC THENL
   [ASM_MESON_TAC[SUM_EQ_NUMSEG; REAL_LET_TRANS; REAL_OF_NUM_LE];
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB; REAL_MUL_RID]]);;

(* counting: for 0 <= r <= N, r - 1 <= #{m in 1..N | m < r} <= r             *)
let COUNT_LT_BOUNDS = prove
 (`!N r. &0 <= r /\ r <= &N
     ==> r - &1 <= sum (1..N) (\m. if &m < r then &1 else &0) /\
         sum (1..N) (\m. if &m < r then &1 else &0) <= r`,
  INDUCT_TAC THENL
   [REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC N`] THEN
  SUBGOAL_THEN `~(&(SUC N) < r)`
    (fun th -> REWRITE_TAC[th; REAL_ADD_RID]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `r <= &N` THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&N < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_IND_LT_ALL] THEN
  UNDISCH_TAC `r <= &(SUC N)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN ASM_REAL_ARITH_TAC);;

(* the level sets G_m = {x | m < N u x} of 0 <= u <= 1_G are measurable      *)
(* subsets of G                                                              *)
let LEVELSET_SUBSET_MEAS = prove
 (`!(u:real->real) G N m.
     real_measurable G /\ u real_measurable_on (:real) /\ 1 <= m /\
     (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0))
     ==> real_measurable {x | &m < &N * u x} /\ {x | &m < &N * u x} SUBSET G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x | &m < &N * u x} SUBSET (G:real->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real` THEN
     DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `u (x:real) = &0` SUBST_ALL_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&m < &N * &0` THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_NOT_LT; REAL_POS];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_MEASURABLE_LEBESGUE_SUBSET THEN
  EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{x | &m < &N * u x} = {x | (\x. &N * (u:real->real) x) x > &m}`
   SUBST1_TAC THENL
   [REWRITE_TAC[real_gt]; ALL_TAC] THEN
  MP_TAC(ISPEC `\x. &N * (u:real->real) x`
    REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT) THEN
  SUBGOAL_THEN `(\x. &N * (u:real->real) x) real_measurable_on (:real)`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_ON_LMUL]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&m`) THEN REWRITE_TAC[]);;

(* pointwise discretization error                                            *)
let LAYER_DISC_BOUND = prove
 (`!N v. 1 <= N /\ &0 <= v /\ v <= &1
     ==> abs(v - inv(&N) * sum (1..N) (\m. if &m < &N * v then &1 else &0))
         <= inv(&N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `&N * v`] COUNT_LT_BOUNDS) THEN ANTS_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
                    MATCH_MP_TAC REAL_LE_LMUL THEN
                      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `S = sum (1..N) (\m. if &m < &N * v then &1 else &0)` THEN
    STRIP_TAC THEN
  SUBGOAL_THEN `v - inv(&N) * S = inv(&N) * (&N * v - S)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `abs(inv(&N)) = inv(&N)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* the discretized function as a complex average of level-set indicators     *)
let CX_DISC_EQ = prove
 (`!(u:real->real) N x.
     Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1 else &0)) =
     Cx(inv(&N)) * vsum (1..N) (\m. if x IN {y | &m < &N * u y}
                                    then Cx(&1) else Cx(&0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CX_MUL; IN_ELIM_THM] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM VSUM_CX_NUMSEG] THEN MATCH_MP_TAC VSUM_EQ THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let CARLESON_IP_DISC = prove
 (`!(u:real->real) G N s.
     real_measurable G /\ u real_measurable_on (:real) /\
     (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0))
     ==> carleson_ip (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                       else &0))) s =
         Cx(inv(&N)) *
         vsum (1..N) (\m. carleson_ip (\x. if x IN {y | &m < &N * u y}
                                           then Cx(&1) else Cx(&0)) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CX_DISC_EQ] THEN
  SUBGOAL_THEN
   `!m. m IN 1..N ==> real_measurable {y | &m < &N * (u:real->real) y}`
   ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_NUMSEG; LEVELSET_SUBSET_MEAS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. vsum (1..N) (\m. if drop z IN {y | &m < &N * (u:real->real) y}
                          then Cx(&1) else Cx(&0)))
    IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^1)`; `&2`;
       `\m:num. \z:real^1. if drop z IN {y | &m < &N * (u:real->real) y}
                           then Cx(&1) else Cx(&0)`;
       `1..N`] LSPACE_VSUM) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[CH_CHI_LSPACE2] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. vsum (1..N) (\m. if x IN {y | &m < &N * (u:real->real) y}
                          then Cx(&1) else Cx(&0))`;
    `Cx(inv(&N))`; `s:int#int#int`] CARLESON_IP_CMUL_L2) THEN
  REWRITE_TAC[carleson_ip] THEN
  MP_TAC(ISPECL
   [`(:real^1)`;
    `\m:num. \z:real^1. if drop z IN {y | &m < &N * (u:real->real) y}
                        then Cx(&1) else Cx(&0)`;
    `\z:real^1. phi_sigma s carleson_phi (drop z)`; `1..N`] LPRODUCT_LSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[L2_CNJ_PRODUCT_INTEGRABLE; PHISIG_IN_LSPACE2; CH_CHI_LSPACE2];
    ASM_SIMP_TAC[]]);;

(* finite convexity: |avg a|^2 <= avg |a|^2                                  *)
let NORM_AVG_SQ_LE = prove
 (`!(a:num->complex) N. 1 <= N
     ==> norm(Cx(inv(&N)) * vsum (1..N) a) pow 2 <=
         inv(&N) * sum (1..N) (\m. norm(a m) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_INV;
    REAL_ABS_NUM; REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&N) pow 2 * sum (1..N) (\m. norm((a:num->complex) m)) pow 2`
    THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC VSUM_NORM; ALL_TAC] THEN
  MP_TAC(ISPECL [`1..N`; `\m. norm((a:num->complex) m)`; `\m:num. &1`]
    SUM_CAUCHY_SCHWARZ) THEN
  REWRITE_TAC[FINITE_NUMSEG; REAL_MUL_RID; REAL_POW_ONE;
    SUM_CONST_NUMSEG; ADD_SUB] THEN
  DISCH_TAC THEN
  ABBREV_TAC `B = sum (1..N) (\m. norm((a:num->complex) m) pow 2)` THEN
  SUBGOAL_THEN `inv(&N) * B = inv(&N) pow 2 * (B * &N)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]);;

let TREE_DISC_BOUND = prove
 (`?C. &0 <= C /\
    !(u:real->real) G N (P:(int#int#int)->bool) (ypt:int#int#int->real) tau t.
       real_measurable G /\ u real_measurable_on (:real) /\
       (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0)) /\ 1 <= N /\
       FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN G then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau <
                         hl_maximal (\u. if u IN G then &1 else &0) x}))
       ==> &2 zpow (tile_k t) *
           sum {s | s IN P /\ tile_ler s t}
             (\s. norm(carleson_ip
                    (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                      else &0))) s) pow 2)
           <= (C * tau) pow 2`,
  X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC ENERGY_IND_SUBSET_CAP THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ts = {s | s IN P /\ tile_ler s (t:int#int#int)}` THEN
  SUBGOAL_THEN `FINITE (Ts:(int#int#int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `P:(int#int#int)->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k (t:int#int#int))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* per-level-set tree bound                                                *)
  SUBGOAL_THEN
   `!m. m IN 1..N
        ==> &2 zpow (tile_k (t:int#int#int)) *
            sum Ts (\s. norm(carleson_ip
                          (\x. if x IN {y | &m < &N * (u:real->real) y}
                               then Cx(&1) else Cx(&0)) s) pow 2)
            <= (C * tau) pow 2`
   ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`u:real->real`; `G:real->bool`; `N:num`; `m:num`]
      LEVELSET_SUBSET_MEAS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `Gm = {y | &m < &N * (u:real->real) y}` THEN
    MP_TAC(ISPECL [`\x. if x IN (Gm:real->bool) then Cx(&1) else Cx(&0)`;
                   `P:(int#int#int)->bool`;
                   `t:int#int#int`] ENERGY_TERM_LE_SELF) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `energy_f (\x. if x IN (Gm:real->bool) then Cx(&1)
                                else Cx(&0)) P <= C * tau`
      ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) &&
        can (find_term (fun tm -> tm = `energy_f`)) (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`G:real->bool`; `ypt:int#int#int->real`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `S = sum Ts (\s. norm(carleson_ip
                                  (\x. if x IN (Gm:real->bool)
                                       then Cx(&1) else Cx(&0)) s) pow 2)` THEN
    SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN MATCH_MP_TAC SUM_POS_LE THEN
       REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
    SUBGOAL_THEN `&2 zpow (tile_k (t:int#int#int)) * S =
                  (sqrt(&2 zpow (tile_k t)) * sqrt S) pow 2`
      SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
       MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[REAL_LE_TRANS]];
    ALL_TAC] THEN
  (* convexity + sum swap                                                    *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `&2 zpow (tile_k (t:int#int#int)) *
    sum Ts (\s. inv(&N) * sum (1..N) (\m. norm(carleson_ip
                  (\x. if x IN {y | &m < &N * (u:real->real) y}
                       then Cx(&1) else Cx(&0)) s) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`u:real->real`; `G:real->bool`; `N:num`; `s:int#int#int`]
      CARLESON_IP_DISC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC NORM_AVG_SQ_LE;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(BETA_RULE(ISPECL
   [`\(s:int#int#int) (m:num). norm(carleson_ip
        (\x. if x IN {y | &m < &N * (u:real->real) y}
             then Cx(&1) else Cx(&0)) s) pow 2`;
    `Ts:(int#int#int)->bool`; `1..N`] SUM_SWAP)) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `&2 zpow (tile_k (t:int#int#int)) * inv(&N) *
      sum (1..N) (\m. sum Ts (\s. norm(carleson_ip
                                (\x. if x IN {y | &m < &N * (u:real->real) y}
                                     then Cx(&1) else Cx(&0)) s) pow 2)) =
    inv(&N) * sum (1..N) (\m. &2 zpow (tile_k t) *
      sum Ts (\s. norm(carleson_ip (\x. if x IN {y | &m < &N * u y}
                                        then Cx(&1) else Cx(&0)) s) pow 2))`
   SUBST1_TAC THENL [REWRITE_TAC[SUM_LMUL; REAL_MUL_AC]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv(&N) * sum (1..N) (\m:num. (C * tau) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
    SUBGOAL_THEN `inv(&N) * &N * (C * tau) pow 2 = (C * tau) pow 2`
      (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `&0 < &N` THEN CONV_TAC REAL_FIELD]);;

(* Cauchy-Schwarz for the tile coefficient                                   *)
let CARLESON_IP_CS = prove
 (`!(f:real->complex) s. (\z. f(drop z)) IN lspace (:real^1) (&2)
     ==> norm(carleson_ip f s) <=
         lnorm (:real^1) (&2) (\z. f(drop z)) *
         lnorm (:real^1) (&2) (\z. phi_sigma s carleson_phi (drop z))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_ip] THEN
  MATCH_MP_TAC LPRODUCT_CAUCHY_SCHWARZ THEN
    ASM_REWRITE_TAC[PHISIG_IN_LSPACE2] THEN
  MATCH_MP_TAC L2_CNJ_PRODUCT_INTEGRABLE THEN
    ASM_REWRITE_TAC[PHISIG_IN_LSPACE2]);;

let CX_REAL_MEASURABLE_ON = prove
 (`!u:real->real. u real_measurable_on (:real)
     ==> (\z:real^1. Cx(u(drop z))) measurable_on (:real^1)`,
  REWRITE_TAC[real_measurable_on; IMAGE_LIFT_UNIV; o_DEF] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CX THEN
  ASM_REWRITE_TAC[]);;

(* domination by an indicator gives L^2                                      *)
let DOM_IND_LSPACE2 = prove
 (`!(w:real^1->complex) G. real_measurable G /\ w measurable_on (:real^1) /\
     (!z. norm(w z) <= (if drop z IN G then &1 else &0))
     ==> w IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:2`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
  EXISTS_TAC `\z. if drop z IN G then Cx(&1) else Cx(&0)` THEN
  ASM_SIMP_TAC[CH_CHI_LSPACE2] THEN CONJ_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real^1`) THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM]);;

let CX_U_LSPACE = prove
 (`!(u:real->real) G.
     real_measurable G /\ u real_measurable_on (:real) /\
     (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0))
     ==> (\z. Cx(u(drop z))) IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DOM_IND_LSPACE2 THEN
    EXISTS_TAC `G:real->bool` THEN
  ASM_SIMP_TAC[CX_REAL_MEASURABLE_ON] THEN X_GEN_TAC `z:real^1` THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop z`) THEN REAL_ARITH_TAC);;

let UN_LSPACE = prove
 (`!(u:real->real) G N.
     real_measurable G /\ u real_measurable_on (:real) /\
     (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0))
     ==> (\z. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u(drop z) then &1
                                           else &0)))
         IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CX_DISC_EQ] THEN
  MATCH_MP_TAC LSPACE_COMPLEX_LMUL THEN
  MP_TAC(ISPECL [`(:real^1)`; `&2`;
       `\m:num. \z:real^1. if drop z IN {y | &m < &N * (u:real->real) y}
                           then Cx(&1) else Cx(&0)`;
       `1..N`] LSPACE_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC CH_CHI_LSPACE2 THEN
    MP_TAC(SPECL [`u:real->real`; `G:real->bool`; `N:num`; `m:num`]
      LEVELSET_SUBSET_MEAS) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;

let IP_U_BOUND = prove
 (`!(u:real->real) G s.
     real_measurable G /\ u real_measurable_on (:real) /\
     (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0))
     ==> norm(carleson_ip (\x. Cx(u x)) s)
         <= lnorm (:real^1) (&2) (\z. if drop z IN G then Cx(&1) else Cx(&0)) *
            lnorm (:real^1) (&2) (\z. phi_sigma s carleson_phi (drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`u:real->real`; `G:real->bool`] CX_U_LSPACE) THEN
    DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lnorm (:real^1) (&2) (\z. Cx(u(drop z))) *
    lnorm (:real^1) (&2) (\z. phi_sigma s carleson_phi (drop z))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARLESON_IP_CS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[LNORM_POS_LE; PHISIG_IN_LSPACE2] THEN
  MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
  ASM_SIMP_TAC[CH_CHI_LSPACE2; NEGLIGIBLE_EMPTY] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^1` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop z`) THEN COND_CASES_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC);;

(* the discretization error on a tile coefficient is O(1/N)                  *)
let IP_DISC_ERR = prove
 (`!(u:real->real) G N s.
     real_measurable G /\ u real_measurable_on (:real) /\
     (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0)) /\ 1 <= N
     ==> norm(carleson_ip (\x. Cx(u x)) s -
              carleson_ip
                (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                  else &0))) s)
         <= inv(&N) * lnorm (:real^1) (&2) (\z. if drop z IN G then Cx(&1)
                                                else Cx(&0)) *
            lnorm (:real^1) (&2) (\z. phi_sigma s carleson_phi (drop z))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`u:real->real`; `G:real->bool`] CX_U_LSPACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:real->real`; `G:real->bool`; `N:num`] UN_LSPACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[carleson_ip] THEN
  MP_TAC(ISPECL [`\z. Cx(u(drop z))`;
                 `\z. Cx(inv(&N) *
                         sum (1..N) (\m. if &m < &N * (u:real->real)(drop z)
                                         then &1 else &0))`;
                 `\z. phi_sigma s carleson_phi (drop z)`;
                 `(:real^1)`] LPRODUCT_LSUB) THEN
  ASM_REWRITE_TAC[PHISIG_IN_LSPACE2] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `dd = \z. Cx(u(drop z)) -
                       Cx(inv(&N) *
                          sum (1..N) (\m. if &m < &N * (u:real->real)(drop z)
                                          then &1 else &0))` THEN
  SUBGOAL_THEN `(dd:real^1->complex) IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [EXPAND_TAC "dd" THEN MATCH_MP_TAC LSPACE_SUB THEN
     ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `lnorm (:real^1) (&2) (dd:real^1->complex) *
    lnorm (:real^1) (&2) (\z. phi_sigma s carleson_phi (drop z))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[LPRODUCT_CAUCHY_SCHWARZ; PHISIG_IN_LSPACE2;
     L2_CNJ_PRODUCT_INTEGRABLE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  SIMP_TAC[LNORM_POS_LE; PHISIG_IN_LSPACE2] THEN
  MP_TAC(ISPECL [`(:real^1)`; `&2`;
    `\z. if drop z IN G then Cx(&1) else Cx(&0)`; `inv(&N)`] LNORM_MUL) THEN
  ASM_SIMP_TAC[CH_CHI_LSPACE2] THEN ANTS_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs(inv(&N)) = inv(&N)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NUM]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
  ASM_SIMP_TAC[LSPACE_CMUL; CH_CHI_LSPACE2; NEGLIGIBLE_EMPTY] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `z:real^1` THEN EXPAND_TAC "dd" THEN
  REWRITE_TAC[GSYM CX_SUB; NORM_MUL; REAL_ABS_INV] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `drop z` o check(fun th -> is_forall(concl th) &&
     can (find_term (fun tm -> tm = `(u:real->real)`)) (concl th) &&
     not (can (find_term (fun tm -> tm = `dd:real^1->complex`))
              (concl th)))) THEN
  COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM;
    REAL_MUL_RID] THENL
   [ASM_SIMP_TAC[LAYER_DISC_BOUND]; ALL_TAC] THEN
  STRIP_TAC THEN SUBGOAL_THEN `u(drop z) = &0` SUBST1_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RZERO] THEN
  SUBGOAL_THEN `!m. ~(&m < &0)` (fun th -> REWRITE_TAC[th]) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_0; REAL_MUL_RZERO; REAL_SUB_REFL; REAL_ABS_0;
    REAL_LE_REFL]);;

(* squares under a perturbation: b <= a + e, b <= K  ==>  b^2 <= a^2 + 2 e K *)
let SQ_PERTURB = prove
 (`!a b e K. &0 <= a /\ &0 <= b /\ b <= a + e /\ b <= K /\ &0 <= e
     ==> b pow 2 <= a pow 2 + &2 * e * K`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b <= a` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a pow 2` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE2]; ALL_TAC] THEN
    REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `(b - a) * (b + a) <= e * (&2 * K)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* x <= a + c/N for all N >= 1  ==>  x <= a                                  *)
let REAL_LE_ADD_INV_N = prove
 (`!x a. (?c. !N. 1 <= N ==> x <= a + c * inv(&N)) ==> x <= a`,
  REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  ASM_CASES_TAC `c <= &0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
     REWRITE_TAC[LE_REFL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `(x - a) / c` REAL_ARCH_INV) THEN
  SUBGOAL_THEN `&0 < (x - a) / c` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ANTS_TAC THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * inv(&n) < x - a` MP_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN
     EXISTS_TAC `c * ((x - a) / c)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_LMUL];
      SUBGOAL_THEN `c * ((x - a) / c) = x - a` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* the tree bound for real 0 <= u <= 1_G (limit of the discretization)       *)
let TREE_U_BOUND = prove
 (`?C. &0 <= C /\
    !(u:real->real) G (P:(int#int#int)->bool) (ypt:int#int#int->real) tau t.
       real_measurable G /\ u real_measurable_on (:real) /\
       (!x. &0 <= u x /\ u x <= (if x IN G then &1 else &0)) /\
       FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN G then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau <
                         hl_maximal (\u. if u IN G then &1 else &0) x}))
       ==> &2 zpow (tile_k t) *
           sum {s | s IN P /\ tile_ler s t}
               (\s. norm(carleson_ip (\x. Cx(u x)) s) pow 2)
           <= (C * tau) pow 2`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "disc"))
    TREE_DISC_BOUND THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `Ts = {s | s IN P /\ tile_ler s (t:int#int#int)}` THEN
  SUBGOAL_THEN `FINITE (Ts:(int#int#int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ts" THEN MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `P:(int#int#int)->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k (t:int#int#int))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = \s. lnorm (:real^1) (&2)
                        (\z. if drop z IN G then Cx(&1) else Cx(&0)) *
                      lnorm (:real^1) (&2)
                        (\z. phi_sigma s carleson_phi (drop z))` THEN
  SUBGOAL_THEN `!s. &0 <= (K:(int#int#int)->real) s` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "K" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[LNORM_POS_LE; PHISIG_IN_LSPACE2; CH_CHI_LSPACE2];
      ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD_INV_N THEN
  EXISTS_TAC `&2 zpow (tile_k (t:int#int#int)) * &2 *
              sum Ts (\s. (K:(int#int#int)->real) s pow 2)` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  (* per-tile perturbation                                                   *)
  SUBGOAL_THEN
   `!s. s IN Ts ==> norm(carleson_ip (\x. Cx(u x)) s) pow 2 <=
       norm(carleson_ip
              (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                else &0))) s) pow 2 +
       inv(&N) * &2 * (K:(int#int#int)->real) s pow 2`
   ASSUME_TAC THENL
   [X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `inv(&N) * &2 * (K:(int#int#int)->real) s pow 2 =
                   &2 * (inv(&N) * K s) * K s`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SQ_PERTURB THEN
      REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(x - y:complex) <= e ==> norm x <= norm y + e`) THEN
      EXPAND_TAC "K" THEN MATCH_MP_TAC IP_DISC_ERR THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "K" THEN MATCH_MP_TAC IP_U_BOUND THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  (* sum it                                                                  *)
  SUBGOAL_THEN
   `sum Ts (\s. norm(carleson_ip (\x. Cx(u x)) s) pow 2) <=
    sum Ts (\s. norm(carleson_ip
                  (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                    else &0))) s) pow 2) +
    inv(&N) * &2 * sum Ts (\s. (K:(int#int#int)->real) s pow 2)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum Ts (\s. norm(carleson_ip
                    (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                      else &0))) s) pow 2 +
                  inv(&N) * &2 * (K:(int#int#int)->real) s pow 2)` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LE];
      ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; REAL_LE_REFL]];
    ALL_TAC] THEN
  (* the discretized tree bound                                              *)
  USE_THEN "disc" (MP_TAC o SPECL
    [`u:real->real`; `G:real->bool`; `N:num`; `P:(int#int#int)->bool`;
     `ypt:int#int#int->real`; `tau:real`; `t:int#int#int`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[ASSUME
    `{s | s IN P /\ tile_ler s (t:int#int#int)} = Ts`]) THEN
  ABBREV_TAC `A = sum Ts (\s. norm(carleson_ip
                  (\x. Cx(inv(&N) * sum (1..N) (\m. if &m < &N * u x then &1
                                                    else &0))) s) pow 2)` THEN
  ABBREV_TAC `B = sum Ts (\s. (K:(int#int#int)->real) s pow 2)` THEN
  ABBREV_TAC `Z = &2 zpow (tile_k (t:int#int#int))` THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `Z * (A + inv(&N) * &2 * B)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `Z * A <= (C * tau) pow 2` THEN REAL_ARITH_TAC);;

(* linearity of the tile coefficient (subtraction)                           *)
let IP_SUB_L2 = prove
 (`!(f:real->complex) (g:real->complex) s.
     (\z. f(drop z)) IN lspace (:real^1) (&2) /\
     (\z. g(drop z)) IN lspace (:real^1) (&2)
     ==> carleson_ip f s - carleson_ip g s = carleson_ip (\x. f x - g x) s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_ip] THEN
  MP_TAC(BETA_RULE(ISPECL [`\z:real^1. (f:real->complex)(drop z)`;
                           `\z:real^1. (g:real->complex)(drop z)`;
                           `\z:real^1. phi_sigma s carleson_phi (drop z)`;
                           `(:real^1)`] LPRODUCT_LSUB)) THEN
  ASM_REWRITE_TAC[PHISIG_IN_LSPACE2]);;

let NORM_SUB_SQ_LE = prove
 (`!a b:complex. norm(a - b) pow 2 <= &2 * norm a pow 2 + &2 * norm b pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(a:complex) + norm(b:complex)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
     CONV_TAC NORM_ARITH;
    MP_TAC(SPEC `norm(a:complex) - norm(b:complex)` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC]);;

let NORM_ADD_II_SQ_LE = prove
 (`!a b:complex.
     norm(a + ii * b) pow 2 <= &2 * norm a pow 2 + &2 * norm b pow 2`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(norm(a:complex) + norm(b:complex)) pow 2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(a:complex) + norm(ii * b)` THEN
    REWRITE_TAC[NORM_TRIANGLE; COMPLEX_NORM_MUL; COMPLEX_NORM_II;
      REAL_MUL_LID; REAL_LE_REFL];
    MP_TAC(SPEC `norm(a:complex) - norm(b:complex)` REAL_LE_POW_2) THEN
      REAL_ARITH_TAC]);;

(* the tree sum of a pointwise-dominated sequence                            *)
let TREE_PAIR_BOUND = prove
 (`!(Ts:(int#int#int)->bool) Z (x:int#int#int->complex)
    (y:int#int#int->complex) (z:int#int#int->complex) A.
     FINITE Ts /\ &0 <= Z /\
     (!s. s IN Ts ==> norm(x s) pow 2 <= &2 * norm(y s) pow 2 +
                                         &2 * norm(z s) pow 2) /\
     Z * sum Ts (\s. norm(y s) pow 2) <= A pow 2 /\
     Z * sum Ts (\s. norm(z s) pow 2) <= A pow 2
     ==> Z * sum Ts (\s. norm(x s) pow 2) <= (&2 * A) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `Z * (&2 * sum Ts (\s. norm((y:int#int#int->complex) s) pow 2) +
         &2 * sum Ts (\s. norm((z:int#int#int->complex) s) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
     ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* positive and negative parts of a dominated real function                  *)
let POSNEG_PART_DOM = prove
 (`!(v:real->real) G.
     v real_measurable_on (:real) /\
     (!x. abs(v x) <= (if x IN G then &1 else &0))
     ==> (\x. max (v x) (&0)) real_measurable_on (:real) /\
         (!x. &0 <= max (v x) (&0) /\
              max (v x) (&0) <= (if x IN G then &1 else &0)) /\
         (\x. max (--(v x)) (&0)) real_measurable_on (:real) /\
         (!x. &0 <= max (--(v x)) (&0) /\
              max (--(v x)) (&0) <= (if x IN G then &1 else &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_ON_MAX; REAL_MEASURABLE_ON_CONST];
    X_GEN_TAC `x:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_MEASURABLE_ON_MAX;
      REAL_MEASURABLE_ON_CONST; REAL_MEASURABLE_ON_NEG];
    X_GEN_TAC `x:real` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN REAL_ARITH_TAC]);;

(* the tree bound for a signed real function dominated by 1_G                *)
let TREE_SIGNED_BOUND = prove
 (`?C. &0 <= C /\
    !(v:real->real) G (P:(int#int#int)->bool) (ypt:int#int#int->real) tau t.
       real_measurable G /\ v real_measurable_on (:real) /\
       (!x. abs(v x) <= (if x IN G then &1 else &0)) /\
       FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN G then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau < hl_maximal (\u. if u IN G then &1 else &0) x}))
       ==> &2 zpow (tile_k t) *
           sum {s | s IN P /\ tile_ler s t}
               (\s. norm(carleson_ip (\x. Cx(v x)) s) pow 2)
           <= (C * tau) pow 2`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ub"))
    TREE_U_BOUND THEN
  EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`v:real->real`; `G:real->bool`] POSNEG_PART_DOM) THEN
    ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC TREE_PAIR_BOUND THEN
  MAP_EVERY EXISTS_TAC
   [`\s. carleson_ip (\x. Cx(max ((v:real->real) x) (&0))) s`;
    `\s. carleson_ip (\x. Cx(max (--((v:real->real) x)) (&0))) s`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:(int#int#int)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
    X_GEN_TAC `s:int#int#int` THEN
      MP_TAC(BETA_RULE(ISPECL [`\x. Cx(max ((v:real->real) x) (&0))`;
                               `\x. Cx(max (--((v:real->real) x)) (&0))`;
                               `s:int#int#int`] IP_SUB_L2)) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CX_U_LSPACE THEN
      EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(\x. Cx(max ((v:real->real) x) (&0)) -
                       Cx(max (--(v x)) (&0))) = (\x. Cx(v x))`
      SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; GSYM CX_SUB; CX_INJ] THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[NORM_SUB_SQ_LE];
    USE_THEN "ub" (MATCH_MP_TAC o BETA_RULE o SPECL
      [`\x. max ((v:real->real) x) (&0)`; `G:real->bool`;
       `P:(int#int#int)->bool`; `ypt:int#int#int->real`;
       `tau:real`; `t:int#int#int`]) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "ub" (MATCH_MP_TAC o BETA_RULE o SPECL
      [`\x. max (--((v:real->real) x)) (&0)`; `G:real->bool`;
       `P:(int#int#int)->bool`; `ypt:int#int#int->real`;
       `tau:real`; `t:int#int#int`]) THEN
    ASM_REWRITE_TAC[]]);;

let RE_IM_REAL_MEASURABLE = prove
 (`!f:real->complex. (\z. f(drop z)) measurable_on (:real^1)
     ==> (\x. Re(f x)) real_measurable_on (:real) /\
         (\x. Im(f x)) real_measurable_on (:real)`,
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o GEN_REWRITE_RULE I [MEASURABLE_ON_COMPONENTWISE]) THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; real_measurable_on; o_DEF;
    IMAGE_LIFT_UNIV; RE_DEF; IM_DEF]);;

let CX_DOM_LSPACE = prove
 (`!(v:real->real) G.
     real_measurable G /\ v real_measurable_on (:real) /\
     (!x. abs(v x) <= (if x IN G then &1 else &0))
     ==> (\z. Cx(v(drop z))) IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DOM_IND_LSPACE2 THEN
    EXISTS_TAC `G:real->bool` THEN
  ASM_SIMP_TAC[CX_REAL_MEASURABLE_ON; COMPLEX_NORM_CX]);;

(* the tree bound for complex f with |f| <= 1_G                              *)
let TREE_COMPLEX_BOUND = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G (P:(int#int#int)->bool) (ypt:int#int#int->real) tau t.
       real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
       (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
       FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN G then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau < hl_maximal (\u. if u IN G then &1 else &0) x}))
       ==> &2 zpow (tile_k t) *
           sum {s | s IN P /\ tile_ler s t} (\s. norm(carleson_ip f s) pow 2)
           <= (C * tau) pow 2`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sb"))
    TREE_SIGNED_BOUND THEN
  EXISTS_TAC `&2 * C` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `f:real->complex` RE_IM_REAL_MEASURABLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!x. abs(Re((f:real->complex) x)) <=
                     (if x IN G then &1 else &0)) /\
                (!x. abs(Im((f:real->complex) x)) <=
                     (if x IN G then &1 else &0))`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM FORALL_AND_THM] THEN X_GEN_TAC `x:real` THEN
    MP_TAC(SPEC `(f:real->complex) x` COMPLEX_NORM_GE_RE_IM) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `norm:complex->real`)) (concl th))) THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC TREE_PAIR_BOUND THEN
  MAP_EVERY EXISTS_TAC
   [`\s. carleson_ip (\x. Cx(Re((f:real->complex) x))) s`;
    `\s. carleson_ip (\x. Cx(Im((f:real->complex) x))) s`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `P:(int#int#int)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
    X_GEN_TAC `s:int#int#int` THEN
      SUBGOAL_THEN `carleson_ip f s =
                    carleson_ip (\x. Cx(Re((f:real->complex) x))) s +
                    ii * carleson_ip (\x. Cx(Im(f x))) s` SUBST1_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL [`\x. Re((f:real->complex) x)`;
       `G:real->bool`] CX_DOM_LSPACE)) THEN
      DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL [`\x. Im((f:real->complex) x)`;
        `G:real->bool`] CX_DOM_LSPACE)) THEN
      DISCH_TAC THEN
      MP_TAC(BETA_RULE(ISPECL [`\x. Cx(Im((f:real->complex) x))`; `ii`;
        `s:int#int#int`] CARLESON_IP_CMUL)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[L2_CNJ_PRODUCT_INTEGRABLE;
         PHISIG_IN_LSPACE2]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(BETA_RULE(ISPECL [`\x. Cx(Re((f:real->complex) x))`;
                               `\x. ii * Cx(Im((f:real->complex) x))`;
                               `s:int#int#int`] CH_IP_ADD)) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LSPACE_COMPLEX_LMUL]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN MATCH_ACCEPT_TAC COMPLEX_EXPAND;
      REWRITE_TAC[NORM_ADD_II_SQ_LE]];
    USE_THEN "sb" (MATCH_MP_TAC o BETA_RULE o SPECL
      [`\x. Re((f:real->complex) x)`; `G:real->bool`;
       `P:(int#int#int)->bool`; `ypt:int#int#int->real`;
       `tau:real`; `t:int#int#int`]) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "sb" (MATCH_MP_TAC o BETA_RULE o SPECL
      [`\x. Im((f:real->complex) x)`; `G:real->bool`;
       `P:(int#int#int)->bool`; `ypt:int#int#int->real`;
       `tau:real`; `t:int#int#int`]) THEN
    ASM_REWRITE_TAC[]]);;

(* The energy of any f with |f| <= 1_G over a non-straddling tile set P      *)
(* satisfying the density condition.                                         *)
let ENERGY_DOM_IND_CAP = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G (P:(int#int#int)->bool) (ypt:int#int#int->real) tau.
       real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
       (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
       FINITE P /\ &0 <= tau /\ tau <= &1 /\
       (!t. ~(tile_tree P t = {})
            ==> abs(ypt t - tile_xmid t) < &2 zpow (&1 - tile_k t) /\
                hl_maximal (\u. if u IN G then &1 else &0) (ypt t) <= tau) /\
       (!s t. s IN P /\ tile_ler s t
              ==> ~(tile_I s SUBSET
                    {x | tau < hl_maximal (\u. if u IN G then &1 else &0) x}))
       ==> energy_f f P <= C * tau`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cb"))
    TREE_COMPLEX_BOUND THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ENERGY_THRESHOLD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  X_GEN_TAC `t:int#int#int` THEN REWRITE_TAC[delta_f; tile_tree] THEN
  USE_THEN "cb" (MATCH_MP_TAC o SPECL
    [`f:real->complex`; `G:real->bool`; `P:(int#int#int)->bool`;
     `ypt:int#int#int->real`; `tau:real`; `t:int#int#int`]) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Straddling tiles: tile_I s SUBSET Omega, where Omega = {tau < M(1_G)} and *)
(* Ep is disjoint from Omega.  Here only decay is used: with n the dyadic    *)
(* depth of tile_I s in Omega,                                               *)
(*   |<f,phi_s>| <~ n tau 2^{-k/2},                                          *)
(*   sum_nJ |int_{Ep cap g^-1 Jr} phi_s| <~ 2^{-k/2} n^{-5},                 *)
(* the first from the density at a good point within n|I|, the second since  *)
(* Ep is far from the centre; and the depth sum satisfies                    *)
(*   sum_I |I| n(I)^{-4} <~ |Omega| <~ |G| / tau.                            *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The cw kernel at an ARBITRARY centre c and scale a (cw_tile is the case   *)
(* a = 2^k, c = tile_xmid s):  x |-> a cw(a (x - c)).  bump <= maximal holds *)
(* at any centre:  int_F a cw(a(. - c)) <= M(1_F)(c).                        *)
(* ------------------------------------------------------------------------- *)

let CWG_POS = prove
 (`!a c x. &0 < a ==> &0 < a * cw(a * (x - c))`,
  ASM_SIMP_TAC[REAL_LT_MUL; CW_POS]);;

let CWG_MCM = prove
 (`!a c. &0 < a ==>
     (!x y. x <= y /\ y <= c ==> a * cw(a * (x - c)) <= a * cw(a * (y - c))) /\
     (!x y. c <= x /\ x <= y ==> a * cw(a * (y - c)) <= a * cw(a * (x - c))) /\
     (!x. c <= x /\ x <= c ==> a * cw(a * (x - c)) = a * cw(a * (c - c)))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
     MATCH_MP_TAC CW_ANTITONE THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC CW_ANTITONE THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `x:real = c` (fun th -> REWRITE_TAC[th]) THEN
      ASM_REAL_ARITH_TAC]);;

let CWG_CONTINUOUS = prove
 (`!a c. (\x. a * cw(a * (x - c))) real_continuous_on (:real)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(\x. a * cw(a * (x - c))) =
                (\x. a * cw(a * x + --(a * c)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
     AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`\x:real. a:real`;
    `\x. cw(a * x + --(a * c))`; `(:real)`]
     REAL_CONTINUOUS_ON_MUL)) THEN
  REWRITE_TAC[REAL_CONTINUOUS_ON_CONST; CW_SHIFT_CONTINUOUS]);;

let CWG_FULL = prove
 (`!a c. &0 < a
     ==> ((\x. a * cw(a * (x - c))) has_real_integral (&1)) (:real)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. a * cw(a * (x - c))) =
                (\x. a * cw(a * x + --(a * c)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
     AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(a:real) = a` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 = a * inv(a) * &1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  MP_TAC(ISPECL [`cw`; `&1`; `a:real`;
    `--(a * c)`] CARLESON_HAS_REAL_INTEGRAL_AFFINITY_UNIV) THEN
  ASM_SIMP_TAC[CW_FULL; REAL_LT_IMP_NZ]);;

let CWG_BOUNDED = prove
 (`!a c. &0 < a ==> real_bounded (IMAGE (\x. a * cw(a * (x - c))) (:real))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_bounded; FORALL_IN_IMAGE;
    IN_UNIV] THEN
  EXISTS_TAC `a:real` THEN X_GEN_TAC `x:real` THEN
  MP_TAC(SPECL [`a:real`; `c:real`; `x:real`] CWG_POS) THEN
    DISCH_TAC THEN ASM_SIMP_TAC[REAL_ARITH `&0 < y ==> abs y = y`] THEN
  MP_TAC(SPEC `a * (x - c)` CW_LE_1) THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_RID] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let CWG_SUPERLEVEL_BOUNDED = prove
 (`!a c u. &0 < a /\ &0 < u ==> real_bounded {x | u <= a * cw(a * (x - c))}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_BOUNDED_SUBSET THEN
  EXISTS_TAC `real_interval[c - inv u, c + inv u]` THEN
  REWRITE_TAC[REAL_BOUNDED_REAL_INTERVAL; SUBSET;
    IN_ELIM_THM; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `u / a <= cw(a * (x - c))` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_SYM]; ALL_TAC] THEN
  ABBREV_TAC `w = a * (x - c)` THEN
  REWRITE_TAC[cw; REAL_ARITH `&1 / y = inv y`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + abs w) pow 3 <= a / u` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_INV_INV; REAL_INV_DIV; REAL_LE_INV2;
     REAL_LT_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + abs w <= a / u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 + abs w) pow 3` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL [REAL_ARITH_TAC; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(x - c) <= inv u` MP_TAC THENL
   [SUBGOAL_THEN `a * abs(x - c) <= a * inv u` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]; ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* bump <= maximal at an arbitrary centre                                    *)
let CWG_INT_F_LE_MAXIMAL = prove
 (`!(Ff:real->bool) a c. real_measurable Ff /\ &0 < a
     ==> real_integral Ff (\x. a * cw(a * (x - c)))
         <= hl_maximal (\t. if t IN Ff then &1 else &0) c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN (Ff:real->bool) then &1 else &0`;
    `\x. a * cw(a * (x - c))`; `c:real`; `c:real`;
    `hl_maximal (\t. if t IN (Ff:real->bool) then &1 else &0) c`]
   MCM_MAXIMAL_DOMINATION) THEN
  MP_TAC(SPECL [`a:real`; `c:real`] CWG_MCM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CH_INDICATOR_ABSINT;
       ABSOLUTELY_REAL_INTEGRABLE_REAL_MEASURABLE];
      ASM_SIMP_TAC[CH_INDICATOR_ABSINT];
      REAL_ARITH_TAC;
      GEN_TAC THEN MP_TAC(SPECL [`a:real`; `c:real`; `x:real`] CWG_POS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[CWG_CONTINUOUS];
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_IMP_INTEGRABLE THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      MATCH_MP_TAC ABSOLUTELY_REAL_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[CONTINUOUS_IMP_REAL_MEASURABLE_ON; CWG_CONTINUOUS];
        ASM_SIMP_TAC[CWG_BOUNDED];
        ASM_SIMP_TAC[CH_INDICATOR_ABSINT]];
      ASM_MESON_TAC[HAS_REAL_INTEGRAL_INTEGRABLE; CWG_FULL];
      ASM_SIMP_TAC[CWG_SUPERLEVEL_BOUNDED];
      MAP_EVERY X_GEN_TAC [`aa:real`; `bb:real`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `aa:real = bb` THENL
       [ASM_SIMP_TAC[REAL_SUB_REFL; REAL_MUL_RZERO;
         REAL_INTEGRAL_NULL; REAL_LE_REFL];
        MATCH_MP_TAC CH_HL_INDICATOR_STRADDLE THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (:real) (\x. a * cw(a * (x - c))) = &1`
    SUBST1_TAC THENL
   [ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; CWG_FULL]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `(\x. (if x IN (Ff:real->bool) then &1 else &0) * a * cw(a * (x - c))) =
    (\x. if x IN Ff then (\x. a * cw(a * (x - c))) x else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV]]);;

(* |<f,phi_s>| <= C1 2^{-k/2} int_G w_s  for |f| <= 1_G  (generalizes        *)
(* CH_IP_INDICATOR_LE)                                                       *)
let CH_IP_DOM_LE = prove
 (`?C1. &0 <= C1 /\
     !(f:real->complex) G (s:int#int#int).
        real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
        (!x. norm(f x) <= (if x IN G then &1 else &0))
        ==> norm(carleson_ip f s)
            <= C1 * inv(sqrt(&2 zpow (tile_k s))) *
              real_integral G (\x. cw_tile s x)`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cw"))
    PHISIG_CW THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`f:real->complex`; `G:real->bool`;
    `s:int#int#int`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (f:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DOM_IND_LSPACE2 THEN EXISTS_TAC `G:real->bool` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `hh = \z. (f:real->complex)(drop z) *
                       cnj(phi_sigma s carleson_phi (drop z))` THEN
  SUBGOAL_THEN `(hh:real^1->complex) integrable_on (:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "hh" THEN MATCH_MP_TAC L2_CNJ_PRODUCT_INTEGRABLE THEN
     ASM_REWRITE_TAC[PHISIG_IN_LSPACE2];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. if z IN IMAGE lift G then (hh:real^1->complex) z
                     else vec 0) = hh`
    (fun th -> MP_TAC(ISPECL [`hh:real^1->complex`; `IMAGE lift G`]
                   INTEGRAL_RESTRICT_UNIV) THEN
               MP_TAC(ISPECL [`hh:real^1->complex`; `IMAGE lift G`]
                   INTEGRABLE_RESTRICT_UNIV) THEN
               REWRITE_TAC[th]) THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN
    REWRITE_TAC[IN_IMAGE_LIFT_DROP] THEN
      COND_CASES_TAC THEN EXPAND_TAC "hh" THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop z` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `norm:complex->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[NORM_LE_0] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `carleson_ip f s = integral (IMAGE lift G) (hh:real^1->complex)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[carleson_ip; lproduct]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (IMAGE lift G)
                (\z. lift((C1 * inv(sqrt(&2 zpow (tile_k (s:int#int#int))))) *
                          cw_tile s (drop z))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[CW_LIFT_BRIDGE];
      X_GEN_TAC `z:real^1` THEN
        REWRITE_TAC[IN_IMAGE_LIFT_DROP] THEN DISCH_TAC THEN
      EXPAND_TAC "hh" THEN
        REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; LIFT_DROP] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop z` o check(fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> tm = `norm:complex->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "cw" (MP_TAC o SPECL [`s:int#int#int`; `drop(z:real^1)`]) THEN
      DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * norm(phi_sigma s carleson_phi (drop z))` THEN
        CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE];
        ASM_REAL_ARITH_TAC]];
    ASM_SIMP_TAC[CH_DROP_INT_EQ; ETA_AX; REAL_MUL_ASSOC; REAL_LE_REFL]]);;

let CWG_SCALE_COMPARE = prove
 (`!b n x y c. &0 < b /\ &1 <= n /\ abs(y - c) <= n * inv b
     ==> &1 + abs((b / n) * (x - y)) <= &2 * (&1 + abs(b * (x - c)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < b / n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  SUBGOAL_THEN `b / n * abs(x - y) <=
                b / n * abs(x - c) + b / n * abs(y - c)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `b / n * abs(x - c) <= b * abs(x - c)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= n ==> &0 < n`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `b / n * abs(y - c) <= &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `b / n * (n * inv b)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE];
      SUBGOAL_THEN `b / n * (n * inv b) = &1`
        (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
      SUBGOAL_THEN `~(n = &0) /\ ~(b = &0)` MP_TAC THENL
        [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b * abs(x - c)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let CW_TILE_LE_CWG = prove
 (`!(s:int#int#int) y n x.
     &1 <= n /\ abs(y - tile_xmid s) <= n * inv(&2 zpow (tile_k s))
     ==> cw_tile s x <= &8 * n * ((&2 zpow (tile_k s) / n) *
                                  cw((&2 zpow (tile_k s) / n) * (x - y)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `b = &2 zpow (tile_k (s:int#int#int))` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `n:real`; `x:real`; `y:real`;
    `tile_xmid (s:int#int#int)`]
    CWG_SCALE_COMPARE) THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[cw_tile] THEN
  SUBGOAL_THEN `&8 * n * (b / n) * cw((b / n) * (x - y)) =
                b * (&8 * cw((b / n) * (x - y)))` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(n = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REWRITE_TAC[cw; REAL_ARITH `&1 / y = inv y`] THEN
  ABBREV_TAC `U = &1 + abs(b * (x - tile_xmid (s:int#int#int)))` THEN
  ABBREV_TAC `V = &1 + abs((b / n) * (x - y))` THEN
  SUBGOAL_THEN `V pow 3 <= &8 * U pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `(&2 * U) pow 3` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < U pow 3 /\ &0 < V pow 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&8 * inv(V pow 3) = inv(V pow 3 / &8)` SUBST1_TAC THENL
   [CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

let CWG_INTEGRABLE_MEASURABLE = prove
 (`!a c Sc. real_measurable Sc /\ &0 < a
     ==> (\x. a * cw(a * (x - c))) real_integrable_on Sc`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. a):real->real` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_MEASURABLE_ON_MEASURABLE_SUBSET; SUBSET_UNIV;
     CONTINUOUS_IMP_REAL_MEASURABLE_ON; CWG_CONTINUOUS];
    ASM_SIMP_TAC[REAL_INTEGRABLE_ON_CONST_MEASURABLE];
    X_GEN_TAC `x:real` THEN
      MP_TAC(SPECL [`a:real`; `c:real`; `x:real`] CWG_POS) THEN
    MP_TAC(SPEC `a * (x - c)` CW_LE_1) THEN
      REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < y ==> abs y = y`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]]);;

(* the straddling-tile coefficient bound from a good point y near the tile   *)
let IP_DENSITY_POINT = prove
 (`?C. &0 <= C /\
     !(f:real->complex) G (s:int#int#int) y n tau.
        real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
        (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
        &1 <= n /\ abs(y - tile_xmid s) <= n * inv(&2 zpow (tile_k s)) /\
        hl_maximal (\t. if t IN G then &1 else &0) y <= tau
        ==> norm(carleson_ip f s)
            <= C * n * tau * inv(sqrt(&2 zpow (tile_k s)))`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ip"))
    CH_IP_DOM_LE THEN
  EXISTS_TAC `&8 * C1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow (tile_k (s:int#int#int))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `a = &2 zpow (tile_k (s:int#int#int)) / n` THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN MATCH_MP_TAC REAL_LT_DIV THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `real_integral G (\x. cw_tile s x) <= (&8 * n) * tau`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral G (\x. (&8 * n) * (a * cw(a * (x - y))))` THEN
      CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[ETA_AX; CWTILE_INTEGRABLE_MEASURABLE];
        MATCH_MP_TAC REAL_INTEGRABLE_LMUL;
        ASM_MESON_TAC[REAL_MUL_ASSOC; CW_TILE_LE_CWG]];
      ALL_TAC] THEN
    MP_TAC(BETA_RULE(ISPECL [`\x. a * cw(a * (x - y))`; `&8 * n`;
      `G:real->bool`] REAL_INTEGRAL_LMUL)) THEN
    ASM_SIMP_TAC[CWG_INTEGRABLE_MEASURABLE] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `hl_maximal (\t. if t IN G then &1 else &0) y` THEN
      ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CWG_INT_F_LE_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C1 * inv(sqrt(&2 zpow (tile_k s))) *
              real_integral G (\x. cw_tile s x)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= inv(sqrt(&2 zpow (tile_k (s:int#int#int))))`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV; SQRT_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `q = inv(sqrt(&2 zpow (tile_k (s:int#int#int))))` THEN
  ABBREV_TAC `I0 = real_integral G (\x. cw_tile (s:int#int#int) x)` THEN
  SUBGOAL_THEN `(&8 * C1) * n * tau * q = (C1 * q) * ((&8 * n) * tau)`
    SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(C1 * q) * I0` THEN
    CONJ_TAC THENL
   [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* Window decay for straddling tiles: Ep stays at distance >= r from the     *)
(* tile centre, so int_Ep |phi_s| <~ 2^{-k/2} (1 + 2^k r)^{-5}.              *)
(* ------------------------------------------------------------------------- *)

let SELREGION_MEAS = prove
 (`!(Ep:real->bool) (g:real->real) (s:int#int#int).
     real_measurable Ep /\ g real_measurable_on (:real)
     ==> real_measurable {x | x IN Ep /\ g x IN tile_Jr s}`,
  REWRITE_TAC[FORALL_PAIR_THM; tile_Jr] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_MEASURABLE_LEBESGUE_SUBSET THEN
    EXISTS_TAC `Ep:real->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  SUBGOAL_THEN `{x | x IN Ep /\
                     (g:real->real) x IN dyho (p1 - &1) (&2 * p2 + &1)} =
                Ep INTER {x | g x IN dyho (p1 - &1) (&2 * p2 + &1)}`
    SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_INTER THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE;
    H_PREIMAGE_DYHO_LEBESGUE]);;

(* norm of a window integral <= integral of the modulus                      *)
let PHISIG_WINDOW_NORM_LE = prove
 (`!(s:int#int#int) R. real_lebesgue_measurable R
     ==> (\x. norm(phi_sigma s carleson_phi x)) real_integrable_on R /\
         norm(integral (IMAGE lift R) (\z. phi_sigma s carleson_phi (drop z)))
         <= real_integral R (\x. norm(phi_sigma s carleson_phi x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:int#int#int`; `R:real->bool`] PHISIG_ABSINT_LEBESGUE) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(\z. lift(norm(phi_sigma s carleson_phi (drop z))))
                 integrable_on (IMAGE lift R)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
     ABSOLUTELY_INTEGRABLE_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. norm(phi_sigma s carleson_phi x)) real_integrable_on R`
    ASSUME_TAC THENL
   [REWRITE_TAC[REAL_INTEGRABLE_ON; o_DEF]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_INTEGRAL] THEN REWRITE_TAC[o_DEF] THEN
  MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
    LIFT_DROP; REAL_LE_REFL]);;

(* int_Ep w_s <= (1 + 2^k r)^{-2} when Ep keeps distance r from the centre   *)
let CWTILE_INT_FAR_LE = prove
 (`!(s:int#int#int) r Ep.
     &0 <= r /\ real_measurable Ep /\
     (!x. x IN Ep ==> r <= abs(x - tile_xmid s))
     ==> real_integral Ep (cw_tile s)
         <= inv((&1 + &2 zpow (tile_k s) * r) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x. &0 <= cw_tile (s:int#int#int) x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; CW_TILE_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `r = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_POW_ONE;
     REAL_INV_1] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `real_integral (:real) (cw_tile s)` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_INTEGRAL_SUBSET_LE; SUBSET_UNIV;
       CWTILE_INTEGRABLE_MEASURABLE;
       HAS_REAL_INTEGRAL_INTEGRABLE; CW_TILE_FULL];
      ASM_MESON_TAC[REAL_EQ_IMP_LE; REAL_INTEGRAL_UNIQUE; CW_TILE_FULL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`s:int#int#int`; `r:real`] CWTILE_FARINT_VALUE) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral ({x | x <= tile_xmid s - r} UNION
                             {x | tile_xmid s + r <= x}) (cw_tile s)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_SUBSET_LE THEN
     ASM_SIMP_TAC[CWTILE_INTEGRABLE_MEASURABLE] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
       X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check(fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> tm = `abs:real->real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[real_integrable_on]];
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INTEGRAL_UNIQUE) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_LE_REFL]]);;

(* int_Ep w_s^2 <= 2^k (1 + 2^k r)^{-5}                                      *)
let CWTILE_SQ_INT_FAR_LE = prove
 (`!(s:int#int#int) r Ep.
     &0 <= r /\ real_measurable Ep /\
     (!x. x IN Ep ==> r <= abs(x - tile_xmid s))
     ==> (\x. cw_tile s x pow 2) real_integrable_on Ep /\
         real_integral Ep (\x. cw_tile s x pow 2)
         <= &2 zpow (tile_k s) * inv((&1 + &2 zpow (tile_k s) * r) pow 5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `b = &2 zpow (tile_k (s:int#int#int))` THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN MATCH_MP_TAC REAL_ZPOW_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `K3 = b * inv((&1 + b * r) pow 3)` THEN
  SUBGOAL_THEN `&0 < &1 + b * r` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 < &1 + y`) THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. x IN Ep ==> cw_tile (s:int#int#int) x <= K3`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[cw_tile] THEN EXPAND_TAC "K3" THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `inv((&1 + b * r) pow 3) = cw(b * r)` SUBST1_TAC THENL
     [REWRITE_TAC[cw; real_div; REAL_MUL_LID; REAL_ABS_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b = b`;
        REAL_ARITH `&0 <= r ==> abs r = r`];
      ALL_TAC] THEN
    MATCH_MP_TAC CW_ANTITONE THEN REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < b ==> abs b = b`;
      REAL_ARITH `&0 <= r ==> abs r = r`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. cw_tile (s:int#int#int) x pow 2) real_integrable_on Ep`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `(\x. b * cw_tile (s:int#int#int) x)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real)` THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_REAL_MEASURABLE_ON THEN
      MATCH_MP_TAC REAL_CONTINUOUS_ON_POW THEN
        REWRITE_TAC[ETA_AX; CWTILE_CONTINUOUS];
      ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; ETA_AX; CWTILE_INTEGRABLE_MEASURABLE];
      X_GEN_TAC `x:real` THEN
        MP_TAC(SPECL [`s:int#int#int`; `x:real`] CW_TILE_POS) THEN
      MP_TAC(SPECL [`s:int#int#int`; `x:real`] CWTILE_BOUNDS) THEN
        ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW; REAL_POW_2] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < y ==> abs y = y`] THEN
      MATCH_MP_TAC REAL_LE_RMUL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral Ep (\x. K3 * cw_tile (s:int#int#int) x)` THEN
    CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_LMUL THEN REWRITE_TAC[ETA_AX];
      ASM_SIMP_TAC[REAL_POW_2; REAL_LE_RMUL; REAL_LT_IMP_LE;
        CW_TILE_POS]]; ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`cw_tile (s:int#int#int)`; `K3:real`;
    `Ep:real->bool`] REAL_INTEGRAL_LMUL)) THEN
  ASM_SIMP_TAC[CWTILE_INTEGRABLE_MEASURABLE] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`s:int#int#int`; `r:real`;
    `Ep:real->bool`] CWTILE_INT_FAR_LE) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K3 * inv((&1 + b * r) pow 2)` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_LMUL; REAL_LE_MUL; REAL_LT_IMP_LE;
     REAL_LE_INV; REAL_POW_LE];
    EXPAND_TAC "K3" THEN
    SUBGOAL_THEN `~(&1 + b * r = &0)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_FIELD
      `~(q = &0) ==> (b * inv(q pow 3)) * inv(q pow 2) = b * inv(q pow 5)`;
             REAL_LE_REFL]]);;

(* sum over nJ of the selector-restricted integrand <= the integrand         *)
let SUM_SELECTOR_LE = prove
 (`!(NJ:int->bool) (g:real->real) k nI (Fw:real->real) x.
     FINITE NJ /\ &0 <= Fw x
     ==> sum NJ (\nJ. if g x IN tile_Jr (k,nI,nJ) then Fw x else &0) <= Fw x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ASM_CASES_TAC `?nJ0. nJ0 IN NJ /\
                       (g:real->real) x IN tile_Jr (k,nI,nJ0)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `nJ0:int` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{nJ | nJ IN NJ /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}
                   = {nJ0}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
       X_GEN_TAC `nJ:int` THEN EQ_TAC THENL
       [ASM_MESON_TAC[CARLESON_THETA_SINGLE_NJ];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[SUM_SING; REAL_LE_REFL]];
    SUBGOAL_THEN `{nJ | nJ IN NJ /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}
                   = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
       ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUM_CLAUSES]]);;

(* the window bound for all straddling tiles sharing (k,nI): disjoint        *)
(* selectors                                                                 *)
let WINDOW_GROUP_FAR = prove
 (`?C. &0 <= C /\
    !(Ep:real->bool) (g:real->real) (k:int) (nI:int) (NJ:int->bool) r.
       real_measurable Ep /\ g real_measurable_on (:real) /\
       FINITE NJ /\ &0 <= r /\
       (!x. x IN Ep ==> r <= abs(x - tile_xmid(k,nI,&0)))
       ==> sum NJ
            (\nJ. norm(integral
                         (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr (k,nI,nJ)})
                         (\z. phi_sigma (k,nI,nJ) carleson_phi (drop z))))
           <= C * inv(sqrt(&2 zpow k)) * inv((&1 + &2 zpow k * r) pow 5)`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sq"))
    PHISIG_CW_SQ THEN
  EXISTS_TAC `C1:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `s0 = (k:int,nI:int,&0:int)` THEN
  SUBGOAL_THEN `!nJ. cw_tile (k,nI,nJ) = cw_tile (s0:int#int#int)`
    ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN
     REWRITE_TAC[FUN_EQ_THM; cw_tile; tile_k; tile_xmid];
    ALL_TAC] THEN
  SUBGOAL_THEN `tile_k (s0:int#int#int) = k /\
                tile_xmid s0 = tile_xmid (k,nI,&0)`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "s0" THEN
      REWRITE_TAC[tile_k]; ALL_TAC] THEN
  ABBREV_TAC `q = inv(sqrt(&2 zpow k))` THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_INV; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `W = \x. cw_tile (s0:int#int#int) x pow 2` THEN
  SUBGOAL_THEN `!nJ. real_measurable
                      {x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[SELREGION_MEAS]; ALL_TAC] THEN
  SUBGOAL_THEN `!nJ. (W:real->real) real_integrable_on
                     {x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}`
    ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(SPECL [`s0:int#int#int`; `r:real`;
      `{x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}`]
      CWTILE_SQ_INT_FAR_LE) THEN
    ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  (* step 1-2: each window <= C1 q^3 int_{R_nJ} W                            *)
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum NJ (\nJ. (C1 * q pow 3) *
       real_integral {x | x IN Ep /\
                          (g:real->real) x IN tile_Jr (k,nI,nJ)} W)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `nJ:int` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`(k:int,nI:int,nJ:int)`;
      `{x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}`]
      PHISIG_WINDOW_NORM_LE) THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE] THEN
      STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral
                  {x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}
                  (\x. norm(phi_sigma (k,nI,nJ) carleson_phi x))` THEN
    MP_TAC(BETA_RULE(ISPECL [`W:real->real`; `C1 * q pow 3`;
       `{x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)}`]
         REAL_INTEGRAL_LMUL)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL]; ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      EXPAND_TAC "W" THEN EXPAND_TAC "q" THEN
    USE_THEN "sq" (MP_TAC o SPECL [`(k:int,nI:int,nJ:int)`; `x:real`]) THEN
    REWRITE_TAC[tile_k] THEN
    SUBGOAL_THEN `cw_tile (k,nI,nJ) = cw_tile (s0:int#int#int)`
      SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  (* step 3: disjoint selectors                                              *)
  SUBGOAL_THEN `sum NJ (\nJ. real_integral {x | x IN Ep /\
                               (g:real->real) x IN tile_Jr (k,nI,nJ)} W)
                <= real_integral Ep W` ASSUME_TAC THENL
   [SUBGOAL_THEN `!nJ. real_integral {x | x IN Ep /\
                         (g:real->real) x IN tile_Jr (k,nI,nJ)} W =
                       real_integral Ep (\x. if g x IN tile_Jr (k,nI,nJ)
                                             then W x else &0)`
      (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `{x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)} =
                    {x | g x IN tile_Jr (k,nI,nJ)} INTER Ep` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_INTEGRAL_RESTRICT_INTER; IN_ELIM_THM];
        ALL_TAC] THEN
    SUBGOAL_THEN `!nJ. (\x. if (g:real->real) x IN tile_Jr (k,nI,nJ)
                            then W x else &0)
                       real_integrable_on Ep` ASSUME_TAC THENL
     [GEN_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `nJ:int` o check(fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> tm = `real_integrable_on`)) (concl th))) THEN
      SUBGOAL_THEN `{x | x IN Ep /\ (g:real->real) x IN tile_Jr (k,nI,nJ)} =
                    {x | g x IN tile_Jr (k,nI,nJ)} INTER Ep` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_INTEGRABLE_RESTRICT_INTER;
        IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\nJ x. if (g:real->real) x IN tile_Jr (k,nI,nJ) then
                     (W:real->real) x else &0`;
                   `Ep:real->bool`; `NJ:int->bool`] REAL_INTEGRAL_SUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_SUM;
      EXPAND_TAC "W";
      ASM_MESON_TAC[SUM_SELECTOR_LE; REAL_LE_POW_2]]; ALL_TAC] THEN
  (* step 4                                                                  *)
  MP_TAC(SPECL [`s0:int#int#int`; `r:real`;
    `Ep:real->bool`] CWTILE_SQ_INT_FAR_LE) THEN
  ASM_SIMP_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= C1 * q pow 3` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(C1 * q pow 3) * (&2 zpow k * inv((&1 + &2 zpow k * r) pow 5))`
    THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_LMUL; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 * &2 zpow k = &1` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(C1 * q pow 3) * (&2 zpow k * inv((&1 + &2 zpow k * r) pow 5)) =
    (C1 * q * inv((&1 + &2 zpow k * r) pow 5)) * (q pow 2 * &2 zpow k)`
  SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_MUL_RID; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* The dyadic depth sum: sum_{I in S} |I| w_I <~ |Omega| when w_I decays     *)
(* like (1 + m)^{-4} in the largest m with [c_I - m|I|, c_I + m|I|] SUBSET   *)
(* Omega.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* a sub-cell at gap >= m from both ends of its ancestor keeps its m-ball    *)
(* inside                                                                    *)
let DYHO_DEPTH_GAP = prove
 (`!a b M nI n0 (m:num).
     a <= b /\ &2 zpow (b - a) = real_of_int M /\
     &m <= real_of_int(nI - n0 * M) /\
     &m <= real_of_int((n0 * M + M - &1) - nI)
     ==> real_interval[dyho_mid a nI - &m * &2 zpow a,
                       dyho_mid a nI + &m * &2 zpow a]
         SUBSET dyho b n0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 zpow b = real_of_int M * &2 zpow a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM REAL_ZPOW_ADD_2] THEN
    AP_TERM_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow a` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; dyho; dyho_mid; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN UNDISCH_TAC `&m <= real_of_int(nI - n0 * M)` THEN
  UNDISCH_TAC `&m <= real_of_int((n0 * M + M - &1) - nI)` THEN
  REWRITE_TAC[int_sub_th; int_add_th; int_mul_th; int_of_num_th] THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `L = &2 zpow a` THEN
  ABBREV_TAC `rn = real_of_int nI` THEN ABBREV_TAC `r0 = real_of_int n0` THEN
  ABBREV_TAC `rM = real_of_int M` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `(rn + &1 / &2) * L - &m * L` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r0 * rM) * L <= (rn + &1 / &2 - &m) * L` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
       ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(rn + &1 / &2) * L + &m * L` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(rn + &1 / &2 + &m) * L < (r0 + &1) * (rM * L)` MP_TAC THENL
     [REWRITE_TAC[REAL_MUL_ASSOC] THEN
       MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* the quartic depth weight is dominated by the two one-sided cw weights     *)
let QUARTIC_MIN_LE_CW = prove
 (`!p q. &0 <= p /\ &0 <= q ==> inv((&1 + min p q) pow 4) <= cw p + cw q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `inv((&1 + min p q) pow 4) <= cw(min p q)` ASSUME_TAC THENL
   [REWRITE_TAC[cw; REAL_ARITH `&1 / y = inv y`] THEN
    SUBGOAL_THEN `abs(min p q) = min p q` SUBST1_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT;
      MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC; ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPEC `p:real` CW_POS) THEN MP_TAC(SPEC `q:real` CW_POS) THEN
  ASM_REAL_ARITH_TAC);;

let DEPTH_ELEMENT_BOUND = prove
 (`!(Om:real->bool) (wv:real) k0 n0 k nI M.
     dyho (--k0) n0 SUBSET Om /\ k0 <= k /\
     &2 zpow (--k0 - --k) = real_of_int M /\
     dyho (--k) nI SUBSET dyho (--k0) n0 /\
     (!m:num. real_interval[dyho_mid (--k) nI - &m * &2 zpow (--k),
                            dyho_mid (--k) nI + &m * &2 zpow (--k)] SUBSET Om
              ==> wv <= inv((&1 + &m) pow 4))
     ==> wv <= cw(real_of_int(n0 * M) - real_of_int nI) +
               cw(real_of_int(n0 * M + M - &1) - real_of_int nI)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--k:int`; `--k0:int`; `M:int`; `n0:int`;
    `nI:int`] DYHO_SUBCELL_IFF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p = (nI:int) - n0 * M` THEN
  ABBREV_TAC `q = ((n0:int) * M + M - &1) - nI` THEN
  SUBGOAL_THEN `&0 <= (p:int) /\ &0 <= (q:int)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= min p q:int` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int(min p q)) = real_of_int(min p q)` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP INT_OF_NUM_OF_INT th)]) THEN
    REWRITE_TAC[int_of_num_th]; ALL_TAC] THEN
  SUBGOAL_THEN `wv <= inv((&1 + real_of_int(min p q)) pow 4)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `dyho (--k0) n0` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC DYHO_DEPTH_GAP THEN
      EXISTS_TAC `M:int` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_ARITH_TAC;
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv((&1 + real_of_int(min p q)) pow 4)` THEN
    ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[int_min_th] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `cw(real_of_int p) + cw(real_of_int q)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC QUARTIC_MIN_LE_CW THEN
    UNDISCH_TAC `&0 <= p:int` THEN UNDISCH_TAC `&0 <= q:int` THEN
    REWRITE_TAC[int_le; int_of_num_th] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THENL
   [EXPAND_TAC "p" THEN REWRITE_TAC[int_sub_th] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM CW_EVEN] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
    EXPAND_TAC "q" THEN REWRITE_TAC[int_sub_th]]);;

(* one scale of the depth sum inside a fixed dyadic ancestor J = dyho(-k0)   *)
(* n0                                                                        *)
let DEPTH_SCALE_SUM = prove
 (`!(Om:real->bool) (S:int#int->bool) (w:int#int->real) k0 n0 k.
     FINITE S /\ dyho (--k0) n0 SUBSET Om /\
     (!kn. kn IN S ==> &0 <= w kn) /\
     (!kn (m:num). kn IN S /\
          real_interval[dyho_mid (--(FST kn)) (SND kn) -
                          &m * &2 zpow (--(FST kn)),
                        dyho_mid (--(FST kn)) (SND kn) +
                          &m * &2 zpow (--(FST kn))] SUBSET Om
          ==> w kn <= inv((&1 + &m) pow 4))
     ==> sum {kn | kn IN S /\
                   dyho (--(FST kn)) (SND kn) SUBSET dyho (--k0) n0 /\
                   FST kn = k}
             (\kn. &2 zpow (--(FST kn)) * w kn)
         <= &4 * inv(&2 zpow k)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Tk = {kn:int#int | kn IN S /\
                     dyho (--(FST kn)) (SND kn) SUBSET dyho (--k0) n0 /\
                     FST kn = k}` THEN
  SUBGOAL_THEN `FINITE (Tk:int#int->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Tk" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `Tk:int#int->bool = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `k0 <= k:int` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    EXPAND_TAC "Tk" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `kn:int#int` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DYHO_SUBSET_SCALE) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `--k0 - --k:int` DYADIC_SCALE_INT) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!kn. kn IN Tk ==>
      &2 zpow (--(FST kn)) * w kn <=
      inv(&2 zpow k) * (cw(real_of_int(n0 * M) - real_of_int(SND kn)) +
                        cw(real_of_int(n0 * M + M - &1) -
                           real_of_int(SND kn)))`
   ASSUME_TAC THENL
   [X_GEN_TAC `kn:int#int` THEN DISCH_TAC THEN
    UNDISCH_TAC `(kn:int#int) IN Tk` THEN EXPAND_TAC "Tk" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&2 zpow (--(FST(kn:int#int))) = inv(&2 zpow k)`
      SUBST1_TAC THENL
     [ASM_REWRITE_TAC[REAL_ZPOW_NEG]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]; ALL_TAC] THEN
    MATCH_MP_TAC DEPTH_ELEMENT_BOUND THEN
    MAP_EVERY EXISTS_TAC [`Om:real->bool`; `k0:int`; `k:int`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) &&
      can (find_term (fun tm -> tm = `real_interval`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Tk (\kn:int#int. inv(&2 zpow k) *
                 (cw(real_of_int(n0 * M) - real_of_int(SND kn)) +
                  cw(real_of_int(n0 * M + M - &1) -
                     real_of_int(SND kn))))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_LE; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN ASM_SIMP_TAC[SUM_ADD] THEN
  SUBGOAL_THEN `!y. sum Tk (\kn:int#int. cw(y - real_of_int(SND kn))) <= &2`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`SND:int#int->int`; `\n:int. cw(y - real_of_int n)`;
      `Tk:int#int->bool`] SUM_IMAGE) THEN
    ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`a:int#int`; `b:int#int`] THEN EXPAND_TAC "Tk" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CW_INTEGER_SHIFT_SUM THEN
      ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= &2 /\ b <= &2 ==> a + b <= &4`) THEN
    ASM_REWRITE_TAC[]);;

(* Maximal members of finite families of sets (used for the maximal dyadic   *)
(* cells in DYADIC_DEPTH_SUM).  For s IN Fam and a proper superset t of s,   *)
(* the members of Fam containing t form a proper subset of the members       *)
(* containing s.                                                             *)
let HB_CANDSET_PSUBSET = prove
 (`!Fam (s:A->bool) s'. s IN Fam /\ s SUBSET s' /\ ~(s' = s)
     ==> {N | N IN Fam /\ s' SUBSET N} PSUBSET {N | N IN Fam /\ s SUBSET N}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `N:A->bool` THEN
     REWRITE_TAC[IN_ELIM_THM; GSYM SUBSET] THEN
       STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `s':A->bool` THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* Every member of a finite family lies below a SUBSET-maximal member.       *)
(* Strong induction on CARD {N in Fam | s SUBSET N}: if s is not itself      *)
(* maximal, some s1 strictly above it has a strictly smaller candidate set   *)
(* (HB_CANDSET_PSUBSET), so recurse on s1 and transit SUBSET.                *)
let HB_MAXIMAL_MEMBER = prove
 (`!Fam:(A->bool)->bool. FINITE Fam
     ==> !s. s IN Fam ==> ?M. M IN Fam /\ s SUBSET M /\
                            (!N. N IN Fam /\ M SUBSET N ==> N = M)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n s:A->bool. CARD {N | N IN Fam /\ s SUBSET N} = n /\ s IN Fam
       ==> ?M. M IN Fam /\ s SUBSET M /\
               (!N. N IN Fam /\ M SUBSET N ==> N = M)`
   (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:A->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `!N. N IN Fam /\ (s:A->bool) SUBSET N ==> N = s` THENL
   [ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `{N | N IN Fam /\ (s':A->bool) SUBSET N} PSUBSET
    {N | N IN Fam /\ (s:A->bool) SUBSET N}`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[HB_CANDSET_PSUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `CARD {N | N IN Fam /\ (s':A->bool) SUBSET N}`) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "n" THEN MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

(* all scales inside a fixed dyadic ancestor J = dyho(-k0) n0                *)
let DEPTH_J_SUM = prove
 (`!(Om:real->bool) (S:int#int->bool) (w:int#int->real) k0 n0.
     FINITE S /\ dyho (--k0) n0 SUBSET Om /\
     (!kn. kn IN S ==> &0 <= w kn) /\
     (!kn (m:num). kn IN S /\
          real_interval[dyho_mid (--(FST kn)) (SND kn) -
                          &m * &2 zpow (--(FST kn)),
                        dyho_mid (--(FST kn)) (SND kn) +
                          &m * &2 zpow (--(FST kn))] SUBSET Om
          ==> w kn <= inv((&1 + &m) pow 4))
     ==> sum {kn | kn IN S /\ dyho (--(FST kn)) (SND kn) SUBSET dyho (--k0) n0}
             (\kn. &2 zpow (--(FST kn)) * w kn)
         <= &8 * inv(&2 zpow k0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{kn:int#int | kn IN S /\
                    dyho (--(FST kn)) (SND kn) SUBSET dyho (--k0) n0}`;
                 `FST:int#int->int`;
                 `\kn:int#int. &2 zpow (--(FST kn)) * w kn`; `k0:int`; `&4`]
     ABSTRACT_SCALE_GEOM_SUM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT];
      REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `kn:int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP DYHO_SUBSET_SCALE) THEN INT_ARITH_TAC;
      X_GEN_TAC `k:int` THEN
      SUBGOAL_THEN
       `{a | a IN {kn:int#int | kn IN S /\
                   dyho (--(FST kn)) (SND kn) SUBSET dyho (--k0) n0} /\
             FST a = k} =
        {kn | kn IN S /\ dyho (--(FST kn)) (SND kn) SUBSET dyho (--k0) n0 /\
              FST kn = k}`
       SUBST1_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
      MATCH_MP_TAC DEPTH_SCALE_SUM THEN
        EXISTS_TAC `Om:real->bool` THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(ACCEPT_TAC o MATCH_MP (REAL_ARITH
      `(a:real) <= &2 * &4 * x ==> a <= &8 * x`))]);;

(* the dyadic depth sum over an arbitrary finite family of dyadic cells in   *)
(* Omega                                                                     *)
let DYADIC_DEPTH_SUM = prove
 (`!(Om:real->bool) (S:int#int->bool) (w:int#int->real).
     real_measurable Om /\ FINITE S /\
     (!kn. kn IN S ==> dyho (--(FST kn)) (SND kn) SUBSET Om) /\
     (!kn. kn IN S ==> &0 <= w kn) /\
     (!kn (m:num). kn IN S /\
          real_interval[dyho_mid (--(FST kn)) (SND kn) -
                          &m * &2 zpow (--(FST kn)),
                        dyho_mid (--(FST kn)) (SND kn) +
                          &m * &2 zpow (--(FST kn))] SUBSET Om
          ==> w kn <= inv((&1 + &m) pow 4))
     ==> sum S (\kn. &2 zpow (--(FST kn)) * w kn) <= &8 * real_measure Om`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Fam = IMAGE (\kn:int#int. dyho (--(FST kn)) (SND kn)) S` THEN
  SUBGOAL_THEN `FINITE (Fam:(real->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real->bool. a IN Fam /\ b IN Fam
                                 ==> a SUBSET b \/ b SUBSET a \/ DISJOINT a b`
    ASSUME_TAC THENL
   [EXPAND_TAC "Fam" THEN
     REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE;
       DYHO_TRICHOTOMY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?mx:int#int->real->bool. !kn. kn IN S ==>
       mx kn IN Fam /\ dyho (--(FST kn)) (SND kn) SUBSET mx kn /\
       (!N. N IN Fam /\ mx kn SUBSET N ==> N = mx kn)`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
     X_GEN_TAC `kn:int#int` THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `Fam:(real->bool)->bool` HB_MAXIMAL_MEMBER) THEN
      ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "Fam" THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `kn:int#int` THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Mx = IMAGE (mx:int#int->real->bool) S` THEN
  SUBGOAL_THEN `FINITE (Mx:(real->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  (* each maximal cell is a dyadic cell of S inside Omega                    *)
  SUBGOAL_THEN `!J. J IN Mx ==> ?kn0:int#int. kn0 IN S /\
                                              J = dyho (--(FST kn0)) (SND kn0)`
    ASSUME_TAC THENL
   [EXPAND_TAC "Mx" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
     X_GEN_TAC `kn:int#int` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(mx:int#int->real->bool) kn IN Fam` MP_TAC THENL
      [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Fam" THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  (* group by the maximal ancestor                                           *)
  MP_TAC(ISPECL [`mx:int#int->real->bool`;
                 `\kn:int#int. &2 zpow (--(FST kn)) * w kn`;
                 `S:int#int->bool`; `Mx:(real->bool)->bool`] SUM_GROUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Mx (\J:real->bool. &8 * real_measure J)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `J:real->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `J:real->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `kn0:int#int` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {kn | kn IN S /\ dyho (--(FST kn)) (SND kn) SUBSET
                                     dyho (--(FST(kn0:int#int))) (SND kn0)}
                    (\kn:int#int. &2 zpow (--(FST kn)) * w kn)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[FINITE_RESTRICT];
        MATCH_MP_TAC(SET_RULE `(!x:A. x IN s /\ Q x ==> P x)
                               ==> {x | x IN s /\ Q x} SUBSET
                                 {x | x IN s /\ P x}`) THEN
        X_GEN_TAC `kn:int#int` THEN STRIP_TAC THEN
        SUBGOAL_THEN `dyho (--(FST(kn:int#int))) (SND kn) SUBSET mx kn`
          MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
          X_GEN_TAC `kn:int#int` THEN STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_ZPOW_LE THEN REAL_ARITH_TAC; ASM_MESON_TAC[]]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`Om:real->bool`; `S:int#int->bool`; `w:int#int->real`;
                  `FST(kn0:int#int)`; `SND(kn0:int#int)`] DEPTH_J_SUM) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[DYHO_MEASURE; REAL_ZPOW_NEG]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!J:real->bool. J IN Mx ==> real_measurable J` ASSUME_TAC THENL
   [ASM_MESON_TAC[DYHO_MEASURABLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`real_measure:(real->bool)->real`; `Mx:(real->bool)->bool`]
    REAL_MEASURE_DISJOINT_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GSYM HAS_REAL_MEASURE_MEASURE] THEN
    MAP_EVERY X_GEN_TAC [`J1:real->bool`; `J2:real->bool`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(J1:real->bool) IN Mx` THEN
      UNDISCH_TAC `(J2:real->bool) IN Mx` THEN
    EXPAND_TAC "Mx" THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_MEASURE_SUBSET THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_UNIONS; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[]);;

(* the dyadic depth of a point of a finite-measure set                       *)
let DEPTH_EXISTS = prove
 (`!(Om:real->bool) c L. real_measurable Om /\ &0 < L /\ c IN Om
     ==> ?n:num. 1 <= n /\
           ~(real_interval[c - &n * L, c + &n * L] SUBSET Om) /\
           real_interval[c - (&n - &1) * L, c + (&n - &1) * L] SUBSET Om /\
           (!m:num. real_interval[c - &m * L, c + &m * L] SUBSET Om
                    ==> m < n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n:num. ~(real_interval[c - &n * L, c + &n * L] SUBSET Om)`
    MP_TAC THENL
   [MP_TAC(SPEC `real_measure(Om:real->bool) / (&2 * L) + &1`
     REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN
      DISCH_TAC THEN
    MP_TAC(ISPECL [`real_interval[c - &n * L, c + &n * L]`;
      `Om:real->bool`] REAL_MEASURE_SUBSET) THEN
    ASM_REWRITE_TAC[REAL_MEASURABLE_REAL_INTERVAL;
      REAL_MEASURE_REAL_INTERVAL] THEN
    SUBGOAL_THEN `real_measure(Om:real->bool) < &2 * L * &n` MP_TAC THENL
     [SUBGOAL_THEN `real_measure(Om:real->bool) / (&2 * L) < &n` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ;
        REAL_ARITH `&0 < L ==> &0 < &2 * L`] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(real_interval[c - &0 * L, c + &0 * L]
                  SUBSET (Om:real->bool))` THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO;
      REAL_ADD_RID; REAL_INTERVAL_SING] THEN
    ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
      [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`];
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(real_interval[c - &n * L, c + &n * L]
                  SUBSET (Om:real->bool))` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `real_interval[c - &m * L, c + &m * L]` THEN
      ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN
      SUBGOAL_THEN `&n * L <= &m * L` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RMUL; REAL_OF_NUM_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

(* one (k,nI) group of straddling tiles: density point at distance <= n|I|,  *)
(* Ep at distance >= (n-1)|I| from the centre.  Total <~ tau |I| n^{-4}.     *)
let STRADDLE_GROUP_BOUND = prove
 (`?C. &0 <= C /\
   !(f:real->complex) G Ep (g:real->real)
     (Qk:(int#int#int)->bool) k nI tau (n:num).
     real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
     (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
     real_measurable Ep /\ g real_measurable_on (:real) /\ FINITE Qk /\
     (!s. s IN Qk ==> FST s = k /\ FST(SND s) = nI) /\ 1 <= n /\
     (?y. abs(y - dyho_mid (--k) nI) <= &n * &2 zpow (--k) /\
          hl_maximal (\t. if t IN G then &1 else &0) y <= tau) /\
     (!x. x IN Ep ==> (&n - &1) * &2 zpow (--k) <= abs(x - dyho_mid (--k) nI))
     ==> sum Qk (\s. norm(carleson_ip f s *
                     integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                              (\z. phi_sigma s carleson_phi (drop z))))
         <= C * tau * inv(&2 zpow k) * inv(&n pow 4)`,
  X_CHOOSE_THEN `CA:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ca"))
    IP_DENSITY_POINT THEN
  X_CHOOSE_THEN `CW:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cw"))
    WINDOW_GROUP_FAR THEN
  EXISTS_TAC `CA * CW` THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 zpow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 zpow (--k) = inv(&2 zpow k)` (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [REWRITE_TAC[REAL_ZPOW_NEG]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL
    [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  ABBREV_TAC `q = inv(sqrt(&2 zpow k))` THEN
  SUBGOAL_THEN `&0 <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_INV; SQRT_POS_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* tau >= 0 from the density point                                         *)
  SUBGOAL_THEN `&0 <= tau` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; CH_HL_INDICATOR_POS]; ALL_TAC] THEN
  (* coefficient bound on the group                                          *)
  SUBGOAL_THEN `!s. s IN Qk ==> norm(carleson_ip f s) <= CA * &n * tau * q`
    ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN
     MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a:int,b:int,c:int)` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `FST:int#int#int->int`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    EXPAND_TAC "q" THEN
    USE_THEN "ca" (MATCH_MP_TAC o REWRITE_RULE[tile_k; tile_xmid] o
      SPECL [`f:real->complex`; `G:real->bool`; `(k:int,nI:int,c:int)`;
        `y:real`; `&n`; `tau:real`]) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum Qk (\s:int#int#int. (CA * &n * tau * q) *
                 norm(integral (IMAGE lift {x | x IN Ep /\
                                                (g:real->real) x IN tile_Jr s})
                               (\z. phi_sigma s carleson_phi (drop z))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_LE; COMPLEX_NORM_MUL; REAL_LE_RMUL;
     NORM_POS_LE]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  (* reindex the window sum by nJ                                            *)
  SUBGOAL_THEN
   `sum Qk (\s:int#int#int.
             norm(integral
                    (IMAGE lift {x | x IN Ep /\ (g:real->real) x IN tile_Jr s})
                    (\z. phi_sigma s carleson_phi (drop z)))) =
    sum (IMAGE (\s:int#int#int. SND(SND s)) Qk)
        (\nJ. norm(integral (IMAGE lift {x | x IN Ep /\
                                             g x IN tile_Jr (k,nI,nJ)})
                            (\z. phi_sigma (k,nI,nJ) carleson_phi (drop z))))`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\s:int#int#int. SND(SND s)`;
      `\nJ. norm(integral (IMAGE lift {x | x IN Ep /\
                                        (g:real->real) x IN tile_Jr (k,nI,nJ)})
                          (\z. phi_sigma (k,nI,nJ) carleson_phi (drop z)))`;
      `Qk:(int#int#int)->bool`] SUM_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`a1:int`; `b1:int`; `c1:int`;
        `a2:int`; `b2:int`; `c2:int`] THEN
      STRIP_TAC THEN
      FIRST_ASSUM(fun th0 ->
        let th = check(fun th -> is_forall(concl th) &&
          can (find_term (fun tm -> tm = `FST:int#int#int->int`))
              (concl th)) th0 in
        MP_TAC(MATCH_MP th (ASSUME `(a1:int,b1:int,c1:int) IN Qk`)) THEN
        MP_TAC(MATCH_MP th (ASSUME `(a2:int,b2:int,c2:int) IN Qk`))) THEN
      UNDISCH_TAC `c1:int = c2` THEN
      REWRITE_TAC[PAIR_EQ] THEN INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a:int,b:int,c:int)` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `FST:int#int#int->int`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  (* the window bound                                                        *)
  USE_THEN "cw" (MP_TAC o SPECL
    [`Ep:real->bool`; `g:real->real`; `k:int`; `nI:int`;
     `IMAGE (\s:int#int#int. SND(SND s)) Qk`;
     `(&n - &1) * inv(&2 zpow k)`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]];
      ASM_REWRITE_TAC[tile_xmid]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &2 zpow k * (&n - &1) * inv(&2 zpow k) = &n`
    SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < &2 zpow k` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= CA * &n * tau * q` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(CA * &n * tau * q) * (CW * q * inv(&n pow 5))` THEN
    CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `q pow 2 = inv(&2 zpow k)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[REAL_POW_INV] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(&n = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  FIRST_X_ASSUM(fun th ->
    if is_eq(concl th) && concl th = `q pow 2 = inv(&2 zpow k)` then
     SUBST1_TAC(SYM th) else NO_TAC) THEN
  UNDISCH_TAC `~(&n = &0)` THEN CONV_TAC REAL_FIELD);;

(* The straddling part of the model tile sum is <~ |G|, without logarithm.   *)
let STRADDLE_TILESUM_BOUND = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G Ep (g:real->real) (Q:(int#int#int)->bool) tau.
      real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      real_measurable Ep /\ g real_measurable_on (:real) /\
      FINITE Q /\ &0 < tau /\
      (!x. x IN Ep ==> hl_maximal (\t. if t IN G then &1 else &0) x <= tau) /\
      (!s. s IN Q ==> tile_I s SUBSET
                      {x | tau < hl_maximal (\t. if t IN G then &1 else &0) x})
      ==> sum Q (\s. norm(carleson_ip f s *
                       integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                                (\z. phi_sigma s carleson_phi (drop z))))
          <= C * real_measure G`,
  X_CHOOSE_THEN `CS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "grp"))
    STRADDLE_GROUP_BOUND THEN
  EXISTS_TAC `&16 * CS` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC
   `Om = {x | tau < hl_maximal (\t. if t IN G then &1 else &0) x}` THEN
  SUBGOAL_THEN `real_measurable (Om:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN MATCH_MP_TAC CH_HL_SUPERLEVEL_MEAS THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Om:real->bool) <= &2 * real_measure G / tau`
    ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN
     MATCH_MP_TAC CH_HL_MAXIMAL_WEAK11_INDICATOR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real. x IN Ep ==> ~(x IN (Om:real->bool))` ASSUME_TAC THENL
   [EXPAND_TAC "Om" THEN
     REWRITE_TAC[IN_ELIM_THM; REAL_NOT_LT] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `kp = \s:int#int#int. (FST s, FST(SND s))` THEN
  ABBREV_TAC `S = IMAGE (kp:int#int#int->int#int) Q` THEN
  SUBGOAL_THEN `FINITE (S:int#int->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_SIMP_TAC[FINITE_IMAGE]; ALL_TAC] THEN
  SUBGOAL_THEN `!kn. kn IN S
                     ==> dyho (--(FST kn)) (SND kn) SUBSET (Om:real->bool)`
    ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN EXPAND_TAC "kp" THEN
     REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`; `c:int`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(a:int,b:int,c:int)` o check(fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> tm = `tile_I`)) (concl th))) THEN
    ASM_REWRITE_TAC[tile_I]; ALL_TAC] THEN
  (* the depth of each spatial cell                                          *)
  SUBGOAL_THEN
   `?nfun:int#int->num. !kn. kn IN S ==>
      1 <= nfun kn /\
      ~(real_interval[dyho_mid (--(FST kn)) (SND kn) -
                        &(nfun kn) * &2 zpow (--(FST kn)),
                      dyho_mid (--(FST kn)) (SND kn) +
                        &(nfun kn) * &2 zpow (--(FST kn))] SUBSET Om) /\
      real_interval[dyho_mid (--(FST kn)) (SND kn) -
                      (&(nfun kn) - &1) * &2 zpow (--(FST kn)),
                    dyho_mid (--(FST kn)) (SND kn) +
                      (&(nfun kn) - &1) * &2 zpow (--(FST kn))]
        SUBSET Om /\
      (!m:num. real_interval[dyho_mid (--(FST kn)) (SND kn) -
                               &m * &2 zpow (--(FST kn)),
                             dyho_mid (--(FST kn)) (SND kn) +
                               &m * &2 zpow (--(FST kn))] SUBSET Om
               ==> m < nfun kn)`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
     X_GEN_TAC `kn:int#int` THEN
    DISCH_TAC THEN MATCH_MP_TAC DEPTH_EXISTS THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_ZPOW_LT THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `kn:int#int` o check(fun th ->
        is_forall(concl th) &&
        can (find_term (fun tm -> tm = `dyho`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[DYHO_MID_IN]]; ALL_TAC] THEN
  (* group the tiles by spatial cell                                         *)
  MP_TAC(ISPECL [`kp:int#int#int->int#int`;
                 `\s:int#int#int. norm(carleson_ip f s *
                       integral (IMAGE lift {x | x IN Ep /\
                                              (g:real->real) x IN tile_Jr s})
                                (\z. phi_sigma s carleson_phi (drop z)))`;
                 `Q:(int#int#int)->bool`; `S:int#int->bool`] SUM_GROUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum S (\kn:int#int. CS * tau * (&2 zpow (--(FST kn)) *
                                              inv(&(nfun kn) pow 4)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `kn:int#int` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kn:int#int` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `nfun:int#int->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    (* a good point y                                                        *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET] o check(fun th ->
      is_neg(concl th) &&
      can (find_term (fun tm -> tm = `real_interval`)) (concl th))) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; IN_REAL_INTERVAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&2 zpow (--(FST(kn:int#int))) * inv(&(nfun kn) pow 4) =
                  inv(&2 zpow (FST kn)) * inv(&(nfun kn) pow 4)`
      SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ZPOW_NEG]; ALL_TAC] THEN
    USE_THEN "grp" (MATCH_MP_TAC o SPECL
      [`f:real->complex`; `G:real->bool`; `Ep:real->bool`; `g:real->real`;
       `{s:int#int#int | s IN Q /\ kp s = (kn:int#int)}`;
       `FST(kn:int#int)`; `SND(kn:int#int)`;
       `tau:real`; `(nfun:int#int->num) kn`]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT];
      REWRITE_TAC[IN_ELIM_THM] THEN
        X_GEN_TAC `s:int#int#int` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN EXPAND_TAC "kp";
      EXISTS_TAC `y:real` THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `~((y:real) IN Om)` MP_TAC THENL
          [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "Om" THEN REWRITE_TAC[IN_ELIM_THM; REAL_NOT_LT]];
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `~(x IN real_interval[dyho_mid (--(FST(kn:int#int))) (SND kn) -
                               (&(nfun kn) - &1) * &2 zpow (--(FST kn)),
                             dyho_mid (--(FST kn)) (SND kn) +
                               (&(nfun kn) - &1) * &2 zpow (--(FST kn))])`
        MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(ISPECL [`Om:real->bool`; `S:int#int->bool`;
    `\kn:int#int. inv(&(nfun kn) pow 4)`]
    DYADIC_DEPTH_SUM) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_INV; REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`kn:int#int`; `m:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `kn:int#int` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `nfun:int#int->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `m < (nfun:int#int->num) kn` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `CS * tau * &8 * (&2 * real_measure (G:real->bool) / tau)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&8 * real_measure(Om:real->bool)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < tau` THEN CONV_TAC REAL_FIELD]);;

(* ========================================================================= *)
(* The restricted-type bound for the tile model, MODEL_TILESUM_BOUND: for    *)
(* |f| <= 1_G and Ep in E avoiding {M 1_G > 4|G|/|E|}, every finite tile set *)
(* Q and every measurable selector g,                                        *)
(*   sum_Q |<f,phi_s>| |int_{Ep cap g^-1 Jr_s} phi_s| <= C |G| (N + 2)       *)
(* whenever 2^{-N} <= |G|/|E|.  It combines the bound for the straddling     *)
(* tiles (STRADDLE_TILESUM_BOUND), the energy of the non-straddling tiles    *)
(* (NONSTRADDLE_ENERGY) and the capped descent (CARLESON_TILESUM_CAP), after *)
(* normalizing f by K = max(C1,1).                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Auxiliary lemmas.                                                         *)
(* ------------------------------------------------------------------------- *)

let HL_IND_LE_1 = prove
 (`!(G:real->bool) x. real_measurable G
     ==> hl_maximal (\t. if t IN G then &1 else &0) x <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[hl_maximal] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `real_integral (real_interval[x - &1,x + &1])
         (\t. abs(if t IN G then &1 else &0)) / ((x + &1) - (x - &1))` THEN
    MAP_EVERY EXISTS_TAC [`x - &1`; `x + &1`] THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[FORALL_IN_GSPEC; CH_INDICATOR_AVG_LE_1]]);;

let IND_LNORM_SQ = prove
 (`!(G:real->bool). real_measurable G
     ==> lnorm (:real^1) (&2)
               (\z. if drop z IN G then Cx(&1) else Cx(&0)) pow 2 =
         real_measure G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\z:real^1. if drop z IN G then Cx(&1) else Cx(&0)`
    LNORM2_SQ) THEN
  ASM_SIMP_TAC[CH_CHI_LSPACE2] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(\x:real^1. lift(norm(if drop x IN G then Cx(&1)
                                      else Cx(&0)) pow 2)) =
                lift o (\t. if t IN G then &1 else &0) o drop` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_POW_2;
      REAL_MUL_LZERO; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(SPEC `G:real->bool` CH_INDICATOR_REAL_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRAL) THEN
  REWRITE_TAC[IMAGE_LIFT_UNIV] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC);;

let DOM_LNORM_SQ_LE = prove
 (`!(f:real->complex) G.
     real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
     (!x. norm(f x) <= (if x IN G then &1 else &0))
     ==> lnorm (:real^1) (&2) (\z. f(drop z)) pow 2 <= real_measure G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `G:real->bool` IND_LNORM_SQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC LNORM_POS_LE THEN MATCH_MP_TAC DOM_IND_LSPACE2 THEN
    EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
  ASM_SIMP_TAC[CH_CHI_LSPACE2; NEGLIGIBLE_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC DOM_IND_LSPACE2 THEN
      EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `z:real^1` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop z` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `norm:complex->real`)) (concl th))) THEN
    COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC]);;

let SELREGION_J_INTEGRABLE = prove
 (`!(Ep:real->bool) (g:real->real) (t:int#int#int).
     real_measurable Ep /\ g real_measurable_on (:real)
     ==> cw_tile t real_integrable_on {x | x IN Ep /\ g x IN tile_J t}`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[FORALL_PAIR_THM; tile_J] THEN
  MAP_EVERY X_GEN_TAC [`k:int`; `nI:int`; `nJ:int`] THEN STRIP_TAC THEN
  MATCH_MP_TAC CWTILE_INTEGRABLE_MEASURABLE THEN
  MATCH_MP_TAC REAL_MEASURABLE_LEBESGUE_SUBSET THEN
    EXISTS_TAC `Ep:real->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  SUBGOAL_THEN `{x | x IN Ep /\ (g:real->real) x IN dyho k nJ} =
                Ep INTER {x | g x IN dyho k nJ}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_INTER THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE;
    H_PREIMAGE_DYHO_LEBESGUE]);;

(* points of a non-straddling tile with small maximal function               *)
let NONSTRADDLE_GOOD_POINT = prove
 (`!(G:real->bool) (s:int#int#int) tau.
     real_measurable G /\
     ~(tile_I s SUBSET
       {x | tau < hl_maximal (\t. if t IN G then &1 else &0) x})
     ==> ?y. y IN tile_I s /\
             hl_maximal (\t. if t IN G then &1 else &0) y <= min tau (&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[SUBSET; IN_ELIM_THM;
    NOT_FORALL_THM; NOT_IMP]) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[REAL_LE_MIN] THEN
  ASM_SIMP_TAC[HL_IND_LE_1] THEN ASM_REAL_ARITH_TAC);;

(* A point of tile_I t lies within 2^(1 - k_t) of the centre tile_xmid t     *)
(* (TILE_I_BAND_TILE).                                                       *)
let TILE_I_MID_DIST = prove
 (`!(t:int#int#int) y.
     y IN tile_I t ==> abs(y - tile_xmid t) < &2 zpow (&1 - tile_k t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `&2 zpow (--(tile_k t) - &1)` THEN
  ASM_SIMP_TAC[TILE_I_BAND_TILE] THEN
  MATCH_MP_TAC ZPOW2_MONOE_LT THEN INT_ARITH_TAC);;

(* ENERGY_DOM_IND_CAP for a non-straddling tile family, with the points ypt  *)
(* chosen in the tops of the trees.                                          *)
let NONSTRADDLE_ENERGY = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G (P:(int#int#int)->bool) tau.
      real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      FINITE P /\ &0 <= tau /\
      (!s. s IN P
           ==> ~(tile_I s SUBSET
                 {x | tau < hl_maximal (\t. if t IN G then &1 else &0) x}))
      ==> energy_f f P <= C * min tau (&1)`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "en"))
    ENERGY_DOM_IND_CAP THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `t1 = min tau (&1)` THEN
  ABBREV_TAC `ypt = \t:int#int#int. @y. y IN tile_I t /\
                     hl_maximal (\u. if u IN G then &1 else &0) y <= t1` THEN
  USE_THEN "en" (MATCH_MP_TAC o SPECL
    [`f:real->complex`; `G:real->bool`; `P:(int#int#int)->bool`;
     `ypt:int#int#int->real`; `t1:real`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    X_GEN_TAC `t:int#int#int` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; tile_tree; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:int#int#int` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?y. y IN tile_I t /\
                      hl_maximal (\u. if u IN G then &1 else &0) y <= t1`
      MP_TAC THENL
     [MP_TAC(SPECL [`G:real->bool`; `s:int#int#int`;
       `tau:real`] NONSTRADDLE_GOOD_POINT) THEN
      UNDISCH_TAC `tile_ler s (t:int#int#int)` THEN
        REWRITE_TAC[tile_ler] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN
    SUBGOAL_THEN `(@y. y IN tile_I t /\
                       hl_maximal (\u. if u IN G then &1 else &0) y <= t1) =
                  (ypt:int#int#int->real) t` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC TILE_I_MID_DIST THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:int#int#int`; `t:int#int#int`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`G:real->bool`; `s:int#int#int`;
      `tau:real`] NONSTRADDLE_GOOD_POINT) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real`) THEN
    ASM_REWRITE_TAC[REAL_NOT_LT]]);;

let ABS_INV_POS = prove
 (`!K. &0 < K ==> abs(inv K) = inv K`,
  SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < K ==> abs K = K`]);;

(* The non-straddling part: the energy bound and the capped descent, after   *)
(* normalizing f by K.                                                       *)
let NONSTRADDLE_TILESUM = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G E Ep (g:real->real)
      (P:(int#int#int)->bool) tau (N:num).
      real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      real_measurable E /\ real_measurable Ep /\ Ep SUBSET E /\
      g real_measurable_on (:real) /\ FINITE P /\ &0 <= tau /\
      real_measure E * tau <= &4 * real_measure G /\
      inv(&2) pow N <= tau /\
      (!s. s IN P
           ==> ~(tile_I s SUBSET
                 {x | tau < hl_maximal (\t. if t IN G then &1 else &0) x}))
      ==> sum P (\s. norm(carleson_ip f s *
                       integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                                (\z. phi_sigma s carleson_phi (drop z))))
          <= C * real_measure G * (&N + &2)`,
  X_CHOOSE_THEN `C1:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "en"))
    NONSTRADDLE_ENERGY THEN
  MP_TAC CARLESON_TILESUM_CAP THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `C6:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "cap"))))) THEN
  ABBREV_TAC `K = max C1 (&1)` THEN
  SUBGOAL_THEN `&1 <= K /\ C1 <= K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `K * C * (&2 pow 14 + C6)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (f:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DOM_IND_LSPACE2 THEN EXISTS_TAC `G:real->bool` THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t1 = min tau (&1)` THEN
  SUBGOAL_THEN `&0 <= t1 /\ t1 <= &1 /\ t1 <= tau` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `f1 = \x. Cx(inv K) * (f:real->complex) x` THEN
  SUBGOAL_THEN `(\z. (f1:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN MATCH_MP_TAC LSPACE_COMPLEX_LMUL THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. carleson_ip f1 s = Cx(inv K) * carleson_ip f s`
    ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f1" THEN
     MATCH_MP_TAC CARLESON_IP_CMUL_L2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* energy of the normalized function                                       *)
  SUBGOAL_THEN `energy_f f1 P <= t1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `inv K * energy_f f P` THEN CONJ_TAC THENL
     [MATCH_MP_TAC ENERGY_F_COEFF_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      ASM_SIMP_TAC[ABS_INV_POS; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv K * (C1 * t1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "t1" THEN
      USE_THEN "en" (MATCH_MP_TAC o SPECL [`f:real->complex`; `G:real->bool`;
                                           `P:(int#int#int)->bool`;
                                           `tau:real`]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID]; ALL_TAC] THEN
  (* the capped descent for f1                                               *)
  USE_THEN "cap" (MP_TAC o SPECL
    [`f1:real->complex`; `Ep:real->bool`; `g:real->real`;
     `P:(int#int#int)->bool`; `t1:real`; `N:num`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE;
     SELREGION_J_INTEGRABLE] THEN
    EXPAND_TAC "t1" THEN ASM_REWRITE_TAC[REAL_LE_MIN] THEN
    MATCH_MP_TAC REAL_POW_1_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  (* undo the normalization                                                  *)
  SUBGOAL_THEN
   `sum P (\s. norm(carleson_ip f s *
                    integral (IMAGE lift {x | x IN Ep /\
                                              (g:real->real) x IN tile_Jr s})
                             (\z. phi_sigma s carleson_phi (drop z)))) =
    K * sum P (\s. norm(carleson_ip f1 s *
                    integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                             (\z. phi_sigma s carleson_phi (drop z))))`
   SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM SUM_LMUL; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[ABS_INV_POS] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    SUBGOAL_THEN `K * inv K = &1`
      (fun th -> REWRITE_TAC[th; REAL_MUL_LID]) THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* bound the budget                                                        *)
  SUBGOAL_THEN `lnorm (:real^1) (&2) (\z. (f1:real->complex)(drop z)) pow 2
                <= real_measure G` ASSUME_TAC THENL
   [MATCH_MP_TAC DOM_LNORM_SQ_LE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "f1" THEN MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN
        ASM_REWRITE_TAC[MEASURABLE_ON_CONST];
      X_GEN_TAC `x:real` THEN EXPAND_TAC "f1" THEN
        REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      ASM_SIMP_TAC[ABS_INV_POS] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 * norm((f:real->complex) x)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; REAL_INV_LE_1];
        ASM_REWRITE_TAC[REAL_MUL_LID]]]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Ep:real->bool) <= real_measure (E:real->bool)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (Ep:real->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC
   `L2 = lnorm (:real^1) (&2) (\z. (f1:real->complex)(drop z)) pow 2` THEN
  ABBREV_TAC `S1 = sum P (\s. norm(carleson_ip f1 s *
                    integral (IMAGE lift {x | x IN Ep /\
                                              (g:real->real) x IN tile_Jr s})
                             (\z. phi_sigma s carleson_phi (drop z))))` THEN
  SUBGOAL_THEN `(&2 pow 12 * real_measure (Ep:real->bool) + C6 * L2) * t1 <=
                (&2 pow 14 + C6) * real_measure (G:real->bool)`
    ASSUME_TAC THENL
   [SUBGOAL_THEN `real_measure (Ep:real->bool) * t1 <=
                  &4 * real_measure (G:real->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `real_measure (E:real->bool) * tau` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `L2 * t1 <= real_measure (G:real->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L2 * &1` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
         ASM_REWRITE_TAC[] THEN EXPAND_TAC "L2" THEN
        REWRITE_TAC[REAL_LE_POW_2];
        ASM_REWRITE_TAC[REAL_MUL_RID]]; ALL_TAC] THEN
    SUBGOAL_THEN `C6 * L2 * t1 <= C6 * real_measure (G:real->bool)`
      MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `real_measure (Ep:real->bool) * t1 <=
                 &4 * real_measure (G:real->bool)` THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N + &2` ASSUME_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `K * C * ((&2 pow 12 * real_measure (Ep:real->bool) + C6 * L2) *
                       t1) * (&N + &2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o
      check(fun th -> can (find_term (fun tm -> tm = `S1:real`)) (concl th) &&
        not(is_eq(concl th)))); ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* The restricted-type bound for the tile model, for |f| <= 1_G and Ep       *)
(* avoiding {M 1_G > 4|G|/|E|}:                                              *)
(*   sum_Q |<f,phi_s>||int_{Ep cap g^-1 Jr_s} phi_s| <= C |G| (N+2)          *)
(* whenever 2^{-N} <= |G|/|E|.                                               *)
let MODEL_TILESUM_BOUND = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G E Ep (g:real->real) (Q:(int#int#int)->bool) (N:num).
      real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      &0 < real_measure G /\ real_measurable E /\ &0 < real_measure E /\
      real_measurable Ep /\ Ep SUBSET E /\
      (!x. x IN Ep ==> hl_maximal (\t. if t IN G then &1 else &0) x
                       <= &4 * real_measure G / real_measure E) /\
      g real_measurable_on (:real) /\ FINITE Q /\
      inv(&2) pow N <= real_measure G / real_measure E
      ==> sum Q (\s. norm(carleson_ip f s *
                       integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                                (\z. phi_sigma s carleson_phi (drop z))))
          <= C * real_measure G * (&N + &2)`,
  X_CHOOSE_THEN `CS:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st"))
    STRADDLE_TILESUM_BOUND THEN
  X_CHOOSE_THEN `CN:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ns"))
    NONSTRADDLE_TILESUM THEN
  EXISTS_TAC `CS + CN` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tau = &4 * real_measure (G:real->bool) /
                         real_measure (E:real->bool)` THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_LT_DIV]]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (E:real->bool) * tau =
                &4 * real_measure (G:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN
     UNDISCH_TAC `&0 < real_measure (E:real->bool)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&2) pow N <= tau` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `Om = {x | tau < hl_maximal (\t. if t IN G then &1 else &0) x}` THEN
  ABBREV_TAC `F0 = \s:int#int#int. norm(carleson_ip f s *
                       integral (IMAGE lift {x | x IN Ep /\
                                              (g:real->real) x IN tile_Jr s})
                                (\z. phi_sigma s carleson_phi (drop z)))` THEN
  MP_TAC(ISPECL [`Q:(int#int#int)->bool`;
                 `\s:int#int#int. tile_I s SUBSET (Om:real->bool)`;
                 `F0:(int#int#int)->real`;
                 `F0:(int#int#int)->real`] SUM_CASES) THEN
  ASM_REWRITE_TAC[COND_ID; ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `sum {s | s IN Q /\ tile_I s SUBSET (Om:real->bool)} F0
                <= CS * real_measure (G:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN
    USE_THEN "st" (MATCH_MP_TAC o SPECL
      [`f:real->complex`; `G:real->bool`; `Ep:real->bool`; `g:real->real`;
       `{s:int#int#int | s IN Q /\ tile_I s SUBSET (Om:real->bool)}`;
       `tau:real`]) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum {s | s IN Q /\ ~(tile_I s SUBSET (Om:real->bool))} F0
                <= CN * real_measure (G:real->bool) * (&N + &2)`
    ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN
    USE_THEN "ns" (MATCH_MP_TAC o SPECL
      [`f:real->complex`; `G:real->bool`; `E:real->bool`; `Ep:real->bool`;
       `g:real->real`;
       `{s:int#int#int | s IN Q /\ ~(tile_I s SUBSET (Om:real->bool))}`;
       `tau:real`; `N:num`]) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; REAL_LT_IMP_LE; REAL_LE_REFL] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:int#int#int` THEN STRIP_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (G:real->bool)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `CS * real_measure (G:real->bool)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Transfer of the model bound MODEL_TILESUM_BOUND to the physical Carleson  *)
(* operator T f = carleson_Ahat (fourier f).                                 *)
(*  - A_FROM_TILESUM: int_FF A h <= 4B from a uniform bound B on the tile    *)
(*    sums (the argument of 286P with an abstract bound).                    *)
(*  - AAVG_INT_F_BOUND_GEN, ATILDE_INT_F_BOUND_GEN: the averaging of         *)
(*    286Q-286S with an abstract bound M.                                    *)
(*  - AHAT_FROM_AMD_BOUND, T_SCHWARTZ_FROM_AMD: 286T and Fourier inversion.  *)
(*  - AMD_FROM_TILESUM, TILESUM_L2_BOUND (the homogeneous form of 286N) and  *)
(*    TILESUM_PERTURB.                                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* From a uniform tile-sum bound to the bound for the operator A, for one    *)
(* pair (h, FF): the argument of 286P with an abstract bound B.              *)
(* ------------------------------------------------------------------------- *)

let IMAGE_LIFT_DROP_SET = prove
 (`!s:real^1->bool. IMAGE lift (IMAGE drop s) = s`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_DROP; IMAGE_ID]);;

let SELREGION_LIFT_EQ = prove
 (`!(F':real^1->bool) (g:real->real) J.
     F' INTER {x:real^1 | g(drop x) IN J} =
     IMAGE lift {x | x IN IMAGE drop F' /\ g x IN J}`,
  REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
  ASM_MESON_TAC[LIFT_DROP]);;

(* the selected-window integral is bounded by any uniform bound on its tile  *)
(* sums                                                                      *)
let WSEL_FROM_TILESUM = prove
 (`!(h:real->complex) u n FF F' B.
     schwartz h /\ real_measurable FF /\ measurable F' /\
     F' SUBSET (IMAGE lift FF) /\
     (!(g:real->real) Q. g real_measurable_on (:real) /\ FINITE Q
          ==> sum Q (\s. norm(carleson_ip h s *
                 integral (IMAGE lift {x | x IN IMAGE drop F' /\
                                           g x IN tile_Jr s})
                          (\z. phi_sigma s carleson_phi (drop z)))) <= B)
     ==> norm(integral F' (\x:real^1. carleson_wsel h u n (drop x))) <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real->complex`; `u:num->real`; `n:num`;
    `FF:real->bool`; `F':real^1->bool`]
    CARLESON_WSEL_TILE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN
    `Qenum:num->(int#int#int)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
   `\(m:num). vsum (Qenum m)
          (\s. carleson_ip (h:real->complex) s *
               integral
                 (F' INTER {x:real^1 | (u(cargmax (\i:num. carleson_v h (u i))
                                                  n (drop x))) IN tile_Jr s})
                 (\z. phi_sigma s carleson_phi (drop z)))` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum ((Qenum:num->(int#int#int)->bool) m)
               (\s. norm(carleson_ip (h:real->complex) s *
       integral (F' INTER {x:real^1 | (u(cargmax (\i:num. carleson_v h (u i))
                                                 n (drop x))) IN tile_Jr s})
         (\z. phi_sigma s carleson_phi (drop z))))` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[VSUM_NORM]; ALL_TAC] THEN
  REWRITE_TAC[SELREGION_LIFT_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) &&
    can (find_term (fun tm -> tm = `carleson_ip`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* 286P with an abstract per-(h,FF) tile bound                               *)
let A_FROM_TILESUM = prove
 (`!(h:real->complex) FF B.
     schwartz h /\ real_measurable FF /\
     (!(Ep:real->bool) (g:real->real) Q.
          real_measurable Ep /\ Ep SUBSET FF /\
          g real_measurable_on (:real) /\ FINITE Q
          ==> sum Q (\s. norm(carleson_ip h s *
                 integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                          (\z. phi_sigma s carleson_phi (drop z)))) <= B)
     ==> real_integral FF (carleson_A h) <= &4 * B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CARLESON_256MB_A THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:num->real` THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ETA_AX; CARLESON_V_ABSINT];
    ASM_MESON_TAC[CARLESON_V_UNIF_BOUND];
    X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`h:real->complex`; `u:num->real`; `n:num`;
      `FF:real->bool`] CARLESON_FINITEMAX_246K) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `F':real^1->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * norm(integral F'
                            (\x:real^1. carleson_wsel h u n (drop x)))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC WSEL_FROM_TILESUM THEN
      EXISTS_TAC `FF:real->bool` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`g:real->real`;
      `Q:(int#int#int)->bool`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_MEASURABLE_MEASURABLE; IMAGE_LIFT_DROP_SET];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^1) IN IMAGE lift FF` MP_TAC THENL
        [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]]]);;

(* ------------------------------------------------------------------------- *)
(* The averaging of 286Q-286T with an abstract bound for each (alpha, beta). *)
(* ------------------------------------------------------------------------- *)

let AAVG_INT_F_BOUND_GEN = prove
 (`!(h:real->complex) FF n M.
     schwartz h /\ real_measurable FF /\ ~(n = 0) /\ &0 <= M /\
     (!a b. &1 <= a /\ a <= &2 /\ &0 <= b /\ b <= &n
            ==> real_integral FF (\x. carleson_amd h a b x) <= M)
   ==> real_integral FF (\x. carleson_Aavg h n x) <= M * log(&2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[carleson_Aavg] THEN
  SUBGOAL_THEN
   `real_integral FF (\x. inv(&n) * carleson_Sinner h n x) =
    inv(&n) * real_integral FF (\x. carleson_Sinner h n x)`
   SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_LMUL; SINNER_INTEGRABLE_F];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real->complex`; `FF:real->bool`; `n:num`] SIDE_A) THEN
    ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[SIDE_A_KFF] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&n) * (M * log(&2) * &n)` THEN CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `inv(&n) * (M * log(&2) * &n) = M * log(&2)` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&n = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
     REWRITE_TAC[REAL_LE_REFL]] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_INV; REAL_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`M:real`; `n:num`] DOM_BOX_INTEGRAL) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; KFF_ABSINT];
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; DOM_BOX_ABSINT];
    X_GEN_TAC `ab:real^(1,1)finite_sum` THEN REWRITE_TAC[IN_UNIV] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; LIFT_DROP] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[]]]);;

let AAVG_INT_F_ALLN_GEN = prove
 (`!(h:real->complex) FF n M.
     schwartz h /\ real_measurable FF /\ &0 <= M /\
     (!a b. &1 <= a /\ a <= &2 /\ &0 <= b
            ==> real_integral FF (\x. carleson_amd h a b x) <= M)
   ==> real_integral FF (\x. carleson_Aavg h n x) <= M * log(&2)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[carleson_Aavg; REAL_INV_0; REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_INTEGRAL_0] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[AAVG_INT_F_BOUND_GEN]]);;

(* 286S with an abstract bound: Atilde h is integrable on FF and int_FF      *)
(* Atilde h <= M log 2                                                       *)
let ATILDE_INT_F_BOUND_GEN = prove
 (`!(h:real->complex) FF M.
     schwartz h /\ real_measurable FF /\ &0 <= M /\
     (!a b. &1 <= a /\ a <= &2 /\ &0 <= b
            ==> real_integral FF (\x. carleson_amd h a b x) <= M)
   ==> (\x. carleson_Atilde h x) real_integrable_on FF /\
       real_integral FF (\x. carleson_Atilde h x) <= M * log(&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`carleson_Aavg (h:real->complex)`; `FF:real->bool`;
    `M * log(&2)`] REAL_FATOU_LIMINF) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM ETA_AX] THEN
      MATCH_MP_TAC AAVG_ABSINT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[AAVG_NONNEG];
      GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
      MATCH_MP_TAC AAVG_INT_F_ALLN_GEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real->real`
    (X_CHOOSE_THEN `k:real->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x. x IN FF DIFF k
                    ==> g x = carleson_Atilde (h:real->complex) x`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    REWRITE_TAC[carleson_Atilde] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC REALLIM_OF_CONVERGENT THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`g:real->real`;
                   `\x. carleson_Atilde (h:real->complex) x`; `k:real->bool`;
                   `FF:real->bool`] REAL_INTEGRABLE_SPIKE) THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `real_integral FF g` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_INTEGRAL_SPIKE THEN
       EXISTS_TAC `k:real->bool` THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* 286T with an abstract bound on the reflected averages                     *)
let AHAT_FROM_AMD_BOUND = prove
 (`!(h:real->complex) FF M.
     schwartz h /\ real_measurable FF /\ &0 <= M /\
     (!a b. &1 <= a /\ a <= &2 /\ &0 <= b
        ==> real_integral (IMAGE (--) FF)
                          (\x. carleson_amd (\x. fourier h (--x)) a b x) <= M)
     ==> real_integral FF (carleson_Ahat h)
         <= inv(pi * carleson_thetatilde (&1) (&0)) * M * log(&2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. fourier (h:real->complex) (--x)`;
    `IMAGE (--) (FF:real->bool)`; `M:real`]
    ATILDE_INT_F_BOUND_GEN) THEN
  ASM_SIMP_TAC[SCHWARTZ_HCHECK; REFLECT_RMEAS] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= inv(pi * carleson_thetatilde (&1) (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
    MP_TAC PI_POS THEN MP_TAC CARLESON_THETATILDE_1_0_POS THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\y. carleson_Atilde (\x. fourier (h:real->complex) (--x))
                                     (--y)) real_integrable_on FF`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_INTEGRABLE_REFLECT_GEN]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_integral FF (\y. inv(pi * carleson_thetatilde (&1)(&0)) *
                          carleson_Atilde (\x. fourier (h:real->complex) (--x))
                                          (--y))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_LE; CARLESON_AHAT_SCHWARTZ_INTEGRABLE;
     REAL_INTEGRABLE_LMUL; AHAT_LE_ATILDE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y. carleson_Atilde (\x. fourier (h:real->complex) (--x))
                                      (--y)`;
                 `inv(pi * carleson_thetatilde (&1)(&0))`;
                 `FF:real->bool`] REAL_INTEGRAL_LMUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `real_integral FF (\y. carleson_Atilde (\x. fourier (h:real->complex) (--x))
                                          (--y)) =
    real_integral (IMAGE (--) FF)
      (\y. carleson_Atilde (\x. fourier (h:real->complex) (--x)) y)`
   SUBST1_TAC THENL
   [REWRITE_TAC[real_integral; HAS_REAL_INTEGRAL_REFLECT_GEN]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]);;

(* the physical Carleson operator T psi = Ahat(fourier psi) at a Schwartz    *)
(* psi                                                                       *)
let T_SCHWARTZ_FROM_AMD = prove
 (`!(psi:real->complex) FF M.
     schwartz psi /\ real_measurable FF /\ &0 <= M /\
     (!a b. &1 <= a /\ a <= &2 /\ &0 <= b
        ==> real_integral (IMAGE (--) FF) (\x. carleson_amd psi a b x) <= M)
     ==> real_integral FF (carleson_Ahat (fourier psi))
         <= inv(pi * carleson_thetatilde (&1) (&0)) * M * log(&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AHAT_FROM_AMD_BOUND THEN
  ASM_SIMP_TAC[SCHWARTZ_FOURIER] THEN
  SUBGOAL_THEN `(\x. fourier (fourier (psi:real->complex)) (--x)) = psi`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; DOUBLE_TRANSFORM];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The bound for A at one modulated dilate, and the L^2 perturbation of tile *)
(* sums (the homogeneous form of 286N for general f in L^2).                 *)
(* ------------------------------------------------------------------------- *)

let AMD_FROM_TILESUM = prove
 (`!(psi:real->complex) a b GG B.
     schwartz psi /\ &0 < a /\ real_measurable GG /\
     (!(Ep:real->bool) (g:real->real) Q.
          real_measurable Ep /\ Ep SUBSET IMAGE (\x. inv a * x) GG /\
          g real_measurable_on (:real) /\ FINITE Q
          ==> sum Q (\s. norm(carleson_ip (carleson_modulate b
                                             (carleson_dilate a psi)) s *
                 integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                          (\z. phi_sigma s carleson_phi (drop z)))) <= B)
     ==> real_integral GG (\x. carleson_amd psi a b x) <= a * (&4 * B)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AMD_INT_F_SUBST] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC A_FROM_TILESUM THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CARLESON_SCHWARTZ_MODDIL; REAL_LT_IMP_NZ];
    ASM_SIMP_TAC[REAL_MEASURABLE_SCALING]]);;

(* integrals over negligible windows vanish                                  *)
let TILESUM_NEGLIGIBLE_REGION = prove
 (`!(f:real->complex) (FF:real->bool) (g:real->real) P.
     real_measurable FF /\ real_measure FF = &0
     ==> sum P (\s. norm(carleson_ip f s *
                 integral (IMAGE lift {x | x IN FF /\ g x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z)))) = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_0 THEN
    X_GEN_TAC `s:int#int#int` THEN
  SUBGOAL_THEN `negligible (IMAGE lift {x | x IN FF /\
                                            (g:real->real) x IN tile_Jr s})`
    ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
     EXISTS_TAC `IMAGE lift (FF:real->bool)` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    SUBGOAL_THEN `real_negligible (FF:real->bool)` MP_TAC THENL
     [ASM_MESON_TAC[HAS_REAL_MEASURE_0; HAS_REAL_MEASURE_MEASURE];
      REWRITE_TAC[real_negligible]]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_ON_NEGLIGIBLE; COMPLEX_VEC_0; COMPLEX_MUL_RZERO;
    COMPLEX_NORM_CX; REAL_ABS_NUM]);;

(* homogeneous 286N: the tile sum is O(||f||_2 sqrt|FF|) for every L2 f      *)
let TILESUM_L2_BOUND = prove
 (`?C9. &0 <= C9 /\
     !(g:real->real) FF (f:real->complex) P.
        (\z. f(drop z)) IN lspace (:real^1) (&2) /\
        g real_measurable_on (:real) /\ real_measurable FF /\ FINITE P
        ==> sum P (\s. norm(carleson_ip f s *
                 integral (IMAGE lift {x | x IN FF /\ g x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z))))
            <= C9 * lnorm (:real^1) (&2) (\z. f(drop z))
              * sqrt(real_measure FF)`,
  X_CHOOSE_THEN `C9:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "n"))
    CARLESON_286N THEN
  EXISTS_TAC `C9:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `L = lnorm (:real^1) (&2) (\z. (f:real->complex)(drop z))` THEN
  SUBGOAL_THEN `&0 <= L` ASSUME_TAC THENL
   [ASM_MESON_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (FF:real->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_POS_LE]; ALL_TAC] THEN
  ASM_CASES_TAC `real_measure (FF:real->bool) = &0` THENL
   [ASM_SIMP_TAC[TILESUM_NEGLIGIBLE_REGION; SQRT_0; REAL_MUL_RZERO;
     REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < real_measure (FF:real->bool)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `L = &0` THENL
   [SUBGOAL_THEN `!s. carleson_ip (f:real->complex) s = Cx(&0)`
     ASSUME_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &0 ==> x = &0`) THEN
      REWRITE_TAC[NORM_POS_LE] THEN
      MP_TAC(ISPECL [`f:real->complex`;
        `s:int#int#int`] CARLESON_IP_CS); ALL_TAC] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_NORM_CX;
                    REAL_ABS_NUM; SUM_0; REAL_MUL_LZERO;
                    REAL_MUL_RZERO; REAL_LE_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < L` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `f1 = \x. Cx(inv L) * (f:real->complex) x` THEN
  SUBGOAL_THEN `(\z. (f1:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN MATCH_MP_TAC LSPACE_COMPLEX_LMUL THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lnorm (:real^1) (&2) (\z. (f1:real->complex)(drop z)) = &1`
    ASSUME_TAC THENL
   [EXPAND_TAC "f1" THEN REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
    MP_TAC(ISPECL [`(:real^1)`; `&2`; `\z. (f:real->complex)(drop z)`;
      `inv L`] LNORM_MUL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[ABS_INV_POS; REAL_MUL_LINV]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. carleson_ip (f:real->complex) s = Cx L * carleson_ip f1 s`
    ASSUME_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPECL [`f:real->complex`; `Cx(inv L)`;
      `s:int#int#int`] CARLESON_IP_CMUL_L2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; COMPLEX_MUL_LID]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s. norm((Cx L * carleson_ip f1 s) *
             integral (IMAGE lift {x | x IN FF /\
                                       (g:real->real) x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z))) =
        L * norm(carleson_ip f1 s *
             integral (IMAGE lift {x | x IN FF /\ g x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z)))`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < L ==> abs L = L`;
      REAL_MUL_ASSOC]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  SUBGOAL_THEN `C9 * L * sqrt(real_measure (FF:real->bool)) =
                L * (C9 * sqrt(real_measure FF))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_REFL; SELREGION_J_INTEGRABLE]);;

(* tile sums are L2-Lipschitz in f                                           *)
let TILESUM_PERTURB = prove
 (`?C9. &0 <= C9 /\
     !(g:real->real) FF (f:real->complex) (h:real->complex) P.
        (\z. f(drop z)) IN lspace (:real^1) (&2) /\
        (\z. h(drop z)) IN lspace (:real^1) (&2) /\
        g real_measurable_on (:real) /\ real_measurable FF /\ FINITE P
        ==> sum P (\s. norm(carleson_ip h s *
                 integral (IMAGE lift {x | x IN FF /\ g x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z))))
            <= sum P (\s. norm(carleson_ip f s *
                 integral (IMAGE lift {x | x IN FF /\ g x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z)))) +
               C9 * lnorm (:real^1) (&2) (\z. h(drop z) - f(drop z))
                 * sqrt(real_measure FF)`,
  X_CHOOSE_THEN `C9:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "l2"))
    TILESUM_L2_BOUND THEN
  EXISTS_TAC `C9:real` THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (h:real->complex)(drop z) - f(drop z))
                IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LSPACE_SUB THEN ASM_REWRITE_TAC[] THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "l2" (MP_TAC o BETA_RULE o SPECL
    [`g:real->real`; `FF:real->bool`; `\x. (h:real->complex) x - f x`;
     `P:(int#int#int)->bool`]) THEN
  DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum P (\s. norm(carleson_ip (f:real->complex) s *
                 integral (IMAGE lift {x | x IN FF /\
                                           (g:real->real) x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z))) +
                       norm(carleson_ip (\x. (h:real->complex) x - f x) s *
                 integral (IMAGE lift {x | x IN FF /\ g x IN tile_Jr s})
                      (\z. phi_sigma s carleson_phi (drop z))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
     X_GEN_TAC `s:int#int#int` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`h:real->complex`; `f:real->complex`;
      `s:int#int#int`] IP_SUB_L2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[COMPLEX_SUB_RDISTRIB] THEN
    MATCH_ACCEPT_TAC(NORM_ARITH
      `!a b:complex. norm(a) <= norm(b) + norm(a - b)`);
    ASM_SIMP_TAC[SUM_ADD; REAL_LE_LADD]]);;

(* ------------------------------------------------------------------------- *)
(* Dilation covariance of the maximal function of an indicator, and the      *)
(* modulated dilated indicator.                                              *)
(* ------------------------------------------------------------------------- *)

let DILATE_INTER_INTERVAL = prove
 (`!(G:real->bool) a c d. &0 < a
     ==> IMAGE (\x. inv a * x) G INTER real_interval[c,d] =
         IMAGE (\x. inv a * x) (G INTER real_interval[a * c,a * d])`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE; IN_REAL_INTERVAL] THEN
  X_GEN_TAC `y:real` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC)
                               STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `z = a * y` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
       REAL_MUL_LID]; ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [EXISTS_TAC `z:real`; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `c = inv a * (a * c)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
         REAL_MUL_LID]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE];
      SUBGOAL_THEN `d = inv a * (a * d)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
         REAL_MUL_LID]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_INV; REAL_LT_IMP_LE]]]);;

(* M(1_{G/a})(x) <= M(1_G)(a x)                                              *)
let HL_MAXIMAL_DILATE_LE = prove
 (`!(G:real->bool) a x. real_measurable G /\ &0 < a
     ==> hl_maximal (\t. if t IN IMAGE (\x. inv a * x) G then &1 else &0) x
         <= hl_maximal (\t. if t IN G then &1 else &0) (a * x)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [hl_maximal] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `real_integral (real_interval[x - &1,x + &1])
         (\t. abs(if t IN IMAGE (\x. inv a * x) G then &1 else &0)) /
           ((x + &1) - (x - &1))` THEN
    MAP_EVERY EXISTS_TAC [`x - &1`; `x + &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `d:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_measurable (IMAGE (\x. inv a * x) (G:real->bool))`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_SCALING; ALL_TAC] THEN
  ASM_SIMP_TAC[RF_IND_INT_MEASURE; DILATE_INTER_INTERVAL] THEN
  SUBGOAL_THEN `real_measurable ((G:real->bool) INTER
                                 real_interval[a * c,a * d])` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_INTER;
     REAL_MEASURABLE_REAL_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MEASURE_SCALING; ABS_INV_POS] THEN
  SUBGOAL_THEN `(inv a * real_measure ((G:real->bool) INTER
                                       real_interval[a * c,a * d])) / (d - c) =
                real_integral (real_interval[a * c,a * d])
                              (\t. abs(if t IN G then &1 else &0)) /
                (a * d - a * c)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RF_IND_INT_MEASURE] THEN
    SUBGOAL_THEN `a * d - a * c = a * (d - c)` SUBST1_TAC THENL
      [REAL_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC AVG_LE_HL_MAXIMAL THEN EXISTS_TAC `&1` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE];
    ASM_MESON_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE];
    ASM_SIMP_TAC[REAL_LT_LMUL];
    ASM_SIMP_TAC[CH_INDICATOR_AVG_LE_1]]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary lemmas: linearity of the modulated dilate, Fourier transforms   *)
(* of L^1 and L^2 functions, the area formula AREA_FROM_INTEGRAL, and the    *)
(* absorption of logarithms by powers (LOGPOW_ABSORB, RATIO_FROM_PROD).      *)
(* ------------------------------------------------------------------------- *)

(* the modulated dilate is linear in the function slot                       *)
let MODDIL_SUB = prove
 (`!(f:real->complex) g a b x.
     carleson_modulate b (carleson_dilate a f) x -
     carleson_modulate b (carleson_dilate a g) x =
     carleson_modulate b (carleson_dilate a (\x. f x - g x)) x`,
  REWRITE_TAC[carleson_modulate; carleson_dilate] THEN CONV_TAC COMPLEX_RING);;

let FOURIER_SUB_L1 = prove
 (`!(f:real->complex) g y.
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> fourier (\x. f x - g x) y = fourier f y - fourier g y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x. cexp(--(ii * Cx y * Cx(drop x))) * (f:real->complex)(drop x))
    integrable_on (:real^1)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; MODULATION_ABSINT_ANY;
     LEBESGUE_MEASURABLE_UNIV]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. cexp(--(ii * Cx y * Cx(drop x))) * (g:real->complex)(drop x))
    integrable_on (:real^1)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; MODULATION_ABSINT_ANY;
     LEBESGUE_MEASURABLE_UNIV]; ALL_TAC] THEN
  REWRITE_TAC[fourier] THEN
  SUBGOAL_THEN
   `(\x. cexp(--(ii * Cx y * Cx(drop x))) *
     ((f:real->complex)(drop x) - g(drop x))) =
    (\x. cexp(--(ii * Cx y * Cx(drop x))) * f(drop x) -
         cexp(--(ii * Cx y * Cx(drop x))) * g(drop x))`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_SUB] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let AREA_FROM_INTEGRAL = prove
 (`!mu m I C. &0 < mu /\ &0 <= m /\ mu * m <= I /\ I <= C * sqrt m /\ &0 <= C
     ==> m <= C pow 2 / mu pow 2`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
  ASM_CASES_TAC `m = &0` THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt m` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt m pow 2 = m` ASSUME_TAC THENL
    [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `mu * sqrt m <= C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN
     EXISTS_TAC `sqrt m` THEN
       SUBGOAL_THEN `(mu * sqrt m) * sqrt m = mu * m` SUBST1_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
       [SYM th]); ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(mu * sqrt m) pow 2 <= C pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC);;

(* a logarithmic loss is absorbed by any power > 1                           *)
let LOGPOW_ABSORB = prove
 (`!q. &1 < q
       ==> ?D. &0 < D /\
               !A r (N:num). &0 < A /\ &1 <= r /\ &2 pow N <= &2 * r /\
                             r <= A * (&N + &2)
                             ==> r <= D * A rpow q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = &1 - inv q` THEN
  SUBGOAL_THEN `&0 < inv q /\ inv q < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
                    ASM_SIMP_TAC[REAL_INV_LT_1]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e /\ e < &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < e * log(&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MUL]; ALL_TAC] THEN
  ABBREV_TAC `c = &3 + inv(e * log(&2))` THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN MATCH_MP_TAC(REAL_ARITH `&0 < y ==> &0 < &3 + y`) THEN
    MATCH_MP_TAC REAL_LT_INV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `c rpow q` THEN CONJ_TAC THENL
    [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= r rpow e` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_LE_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* N <= 1 + log r / log 2                                                  *)
  SUBGOAL_THEN `&N * log(&2) <= log(&2) + log r` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&2 pow N) <= log(&2 * r)` MP_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LT; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POW; LOG_MUL; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  (* log r <= r^e / e                                                        *)
  SUBGOAL_THEN `e * log r <= r rpow e` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM LOG_RPOW] THEN
    MP_TAC(SPEC `r rpow e - &1` LOG_LE) THEN ANTS_TAC THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  (* N + 2 <= c r^e                                                          *)
  SUBGOAL_THEN `&N + &2 <= c * r rpow e` ASSUME_TAC THENL
   [ABBREV_TAC `L2 = log(&2)` THEN ABBREV_TAC `R = r rpow e` THEN
     ABBREV_TAC `lr = log r` THEN
    SUBGOAL_THEN `e * (&N * L2) <= e * (L2 + lr)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&3 * (e * L2) <= &3 * (e * L2) * R` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
       REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
        [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&N + &2) * (e * L2) <= (&3 * (e * L2) + &1) * R`
      ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "c" THEN
    SUBGOAL_THEN `(&3 + inv(e * L2)) * R =
                  ((&3 * (e * L2) + &1) * R) / (e * L2)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < e * L2` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  (* r <= A c r^e, hence r^{1/q} <= A c                                      *)
  SUBGOAL_THEN `r <= (A * c) * r rpow e` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS; REAL_MUL_ASSOC; REAL_LE_LMUL;
     REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `r = r rpow e * r rpow (inv q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[REAL_ARITH `(&1 - x) + x = &1`; RPOW_POW;
      REAL_POW_1]; ALL_TAC] THEN
  SUBGOAL_THEN `r rpow (inv q) <= A * c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
     EXISTS_TAC `r rpow e` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r = (r rpow (inv q)) rpow q` SUBST1_TAC THENL
   [ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
    SUBGOAL_THEN `inv q * q = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN
       ASM_REAL_ARITH_TAC; REWRITE_TAC[RPOW_POW; REAL_POW_1]]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(A * c) rpow q` THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[RPOW_MUL] THEN REAL_ARITH_TAC]);;

(* A ratio bound used in the restricted case.                                *)
let RATIO_FROM_PROD = prove
 (`!CR mu m f CR1 a.
     &0 < mu /\ &0 < f /\ mu * m <= CR * f * a /\ CR <= CR1 /\ &0 <= a
     ==> m / f <= (CR1 / mu) * a`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(CR1 / mu) * a = ((CR1 * f * a) / mu) / f` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(mu = &0) /\ ~(f = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `CR * f * a` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Weak type (p,p) of the truncated operator for 1 < p < 2.                  *)
(*  - Weak type (2,2) of the truncated operator at a general L^2 symbol.     *)
(*  - Restricted weak type for functions dominated by an indicator,          *)
(*    |f| <= 1_F (the model bound already allows such f): T_DOM_RWT_Q0,      *)
(*    |{T_n f > mu}| <= D |F| mu^(-q0) for 1 < q0 <= 2.                      *)
(*  - The structure of T_n: sublinear, homogeneous and measurable.           *)
(*  - Weak type (p,p) by a finite dyadic level decomposition.                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Weak type (2,2) for the truncated operator at a general L^2 symbol.       *)
(* ------------------------------------------------------------------------- *)

let AHAT_TRUNC_WEAK22 = prove
 (`?C2. &0 <= C2 /\
    !(H:real->complex) n mu.
      (\z. H(drop z)) IN lspace (:real^1) (&2) /\ &0 <= n /\ &0 < mu
      ==> real_measurable {y | mu < carleson_Ahat_trunc H n y} /\
          real_measure {y | mu < carleson_Ahat_trunc H n y}
          <= C2 * lnorm (:real^1) (&2) (\z. H(drop z)) pow 2 / mu pow 2`,
  X_CHOOSE_THEN `C10:real` STRIP_ASSUME_TAC CARLESON_286T_SCHWARTZ THEN
  EXISTS_TAC `C10 pow 2` THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `Lh = lnorm (:real^1) (&2) (\z. (H:real->complex)(drop z))` THEN
  SUBGOAL_THEN `&0 <= Lh` ASSUME_TAC THENL
   [ASM_MESON_TAC[LNORM_POS_LE]; ALL_TAC] THEN
  ABBREV_TAC `L = {y | mu < carleson_Ahat_trunc H n y}` THEN
  SUBGOAL_THEN `real_lebesgue_measurable (L:real->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`H:real->complex`;
     `n:real`] CARLESON_AHAT_TRUNC_MEASURABLE) THEN
    ASM_REWRITE_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT] THEN
    DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN EXPAND_TAC "L" THEN
      REWRITE_TAC[real_gt]; ALL_TAC] THEN
  ABBREV_TAC `sM = \M:num. L INTER real_interval[--(&M),&M]` THEN
  SUBGOAL_THEN `!M:num. real_measurable ((sM:num->real->bool) M)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_MEASURABLE_LEBESGUE_SUBSET;
     REAL_MEASURABLE_REAL_INTERVAL; INTER_SUBSET;
     REAL_LEBESGUE_MEASURABLE_INTER;
     REAL_LEBESGUE_MEASURABLE_INTERVAL]; ALL_TAC] THEN
  (* the per-window bound                                                    *)
  SUBGOAL_THEN `!M:num. real_measure ((sM:num->real->bool) M)
                        <= C10 pow 2 * Lh pow 2 / mu pow 2` ASSUME_TAC THENL
   [X_GEN_TAC `M:num` THEN ABBREV_TAC `S = (sM:num->real->bool) M` THEN
    SUBGOAL_THEN `real_measurable (S:real->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `S SUBSET (L:real->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[INTER_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= real_measure (S:real->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_MEASURE_POS_LE; ALL_TAC] THEN
    MP_TAC(ISPECL [`H:real->complex`; `S:real->bool`; `n:real`; `C10:real`]
      CARLESON_286T_TRUNC_GENERAL_FF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `mu * real_measure (S:real->bool) <=
                  real_integral S (\y. carleson_Ahat_trunc H n y)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `real_integral S (\y:real. mu)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_INTEGRAL_CONST_MEASURABLE] THEN
         REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_INTEGRABLE_ON_CONST_MEASURABLE];
        ASM_SIMP_TAC[CARLESON_AHAT_TRUNC_INTEGRABLE_GEN];
        X_GEN_TAC `y:real` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(y:real) IN L` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN
          REAL_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `C10 pow 2 * Lh pow 2 / mu pow 2 =
                  (C10 * Lh) pow 2 / mu pow 2` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC AREA_FROM_INTEGRAL THEN
    EXISTS_TAC `real_integral S (\y. carleson_Ahat_trunc H n y)` THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* nested union                                                            *)
  MP_TAC(ISPECL [`sM:num->real->bool`; `C10 pow 2 * Lh pow 2 / mu pow 2`]
    HAS_REAL_MEASURE_NESTED_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN EXPAND_TAC "sM" THEN
     MATCH_MP_TAC(SET_RULE `s SUBSET t ==> L INTER s SUBSET L INTER t`) THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; GSYM REAL_OF_NUM_SUC] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {(sM:num->real->bool) M | M IN (:num)} = L`
    SUBST1_TAC THENL
   [EXPAND_TAC "sM" THEN
     REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNIV; IN_INTER] THEN
    X_GEN_TAC `y:real` THEN EQ_TAC THENL
     [ASM_MESON_TAC[];
      DISCH_TAC THEN MP_TAC(SPEC `abs y` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
      EXISTS_TAC `L INTER real_interval[--(&M),&M]` THEN CONJ_TAC THENL
       [EXISTS_TAC `M:num`; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INTER; IN_REAL_INTERVAL] THEN
        ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\M:num. real_measure ((sM:num->real->bool) M)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY]);;

(* ------------------------------------------------------------------------- *)
(* Functions dominated by an indicator, |f| <= 1_G.                          *)
(* ------------------------------------------------------------------------- *)

let DOM_L1L2 = prove
 (`!(f:real->complex) G.
     real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
     (!x. norm(f x) <= (if x IN G then &1 else &0))
     ==> (\z. f(drop z)) IN lspace (:real^1) (&2) /\
         (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
         lnorm (:real^1) (&2) (\z. f(drop z)) pow 2 <= real_measure G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (f:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC DOM_IND_LSPACE2 THEN EXISTS_TAC `G:real->bool`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC
     MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `lift o (\t. if t IN G then &1 else &0) o drop` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IMAGE_LIFT_UNIV; REAL_INTEGRABLE_ON;
       CH_INDICATOR_REAL_INTEGRABLE];
      ASM_REWRITE_TAC[o_THM; LIFT_DROP]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `lnorm (:real^1) (&2)
                      (\z. if drop z IN G then Cx(&1) else Cx(&0)) pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[LNORM_POS_LE] THEN
      MATCH_MP_TAC LNORM_MONO THEN EXISTS_TAC `{}:real^1->bool` THEN
      ASM_SIMP_TAC[CH_CHI_LSPACE2; NEGLIGIBLE_EMPTY; DIFF_EMPTY; IN_UNIV] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      X_GEN_TAC `z:real^1` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `drop z` o check (is_forall o concl)) THEN
      COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
      ASM_SIMP_TAC[IND_LNORM_SQ; REAL_LE_REFL]]]);;

let MODDIL_GEN_DOM = prove
 (`!(f:real->complex) (G:real->bool) a b x.
     &0 < a /\ (!x. norm(f x) <= (if x IN G then &1 else &0))
     ==> norm(carleson_modulate b (carleson_dilate a f) x)
         <= (if x IN IMAGE (\x. inv a * x) G then &1 else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_modulate; carleson_dilate;
    GSYM CX_MUL; COMPLEX_NORM_MUL; NORM_CEXP_II; REAL_MUL_LID] THEN
  SUBGOAL_THEN `a * x IN G <=> x IN IMAGE (\x. inv a * x) (G:real->bool)`
    (fun th -> REWRITE_TAC[GSYM th]) THENL
   [REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `a * x` THEN
       ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_LID];
      DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; REAL_MUL_LID]];
    ASM_REWRITE_TAC[]]);;

let MODDIL_GEN_MEASURABLE = prove
 (`!(f:real->complex) a b. (\z. f(drop z)) measurable_on (:real^1) /\ &0 < a
     ==> (\z. carleson_modulate b (carleson_dilate a f) (drop z))
       measurable_on (:real^1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[carleson_modulate; carleson_dilate] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON;
     COMPLEX_MUL_ASSOC; CEXP_LINEAR_CONTINUOUS];
    MP_TAC(ISPECL [`\z. (f:real->complex)(drop z)`; `a:real`; `vec 0:real^1`]
      MEASURABLE_ON_DILATE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; VECTOR_ADD_RID; DROP_CMUL]]);;

let MODDIL_GEN_LSPACE = prove
 (`!(f:real->complex) G a b.
     real_measurable G /\ (\z. f(drop z)) measurable_on (:real^1) /\
     (!x. norm(f x) <= (if x IN G then &1 else &0)) /\ &0 < a
     ==> (\z. carleson_modulate b (carleson_dilate a f) (drop z))
       IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DOM_IND_LSPACE2 THEN
  EXISTS_TAC `IMAGE (\x. inv a * x) (G:real->bool)` THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_SCALING;
    MODDIL_GEN_MEASURABLE; MODDIL_GEN_DOM]);;

(* weak (2,2) at a dominated function                                        *)
let T_DOM_LEVEL_WEAK22 = prove
 (`?C2. &0 <= C2 /\
    !(f:real->complex) (Fs:real->bool) n mu.
      real_measurable Fs /\ (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN Fs then &1 else &0)) /\ &0 <= n /\ &0 < mu
      ==> real_measurable {y | mu < carleson_Ahat_trunc (fourier f) n y} /\
          real_measure {y | mu < carleson_Ahat_trunc (fourier f) n y}
          <= C2 * real_measure Fs / mu pow 2`,
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w2"))
    AHAT_TRUNC_WEAK22 THEN
  EXISTS_TAC `C2:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `Fs:real->bool`] DOM_L1L2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `f:real->complex` FOURIER_L1L2_IN_L2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "w2" (MP_TAC o SPECL [`fourier (f:real->complex)`;
    `n:real`; `mu:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C2 * lnorm (:real^1) (&2)
                         (\z. fourier (f:real->complex) (drop z)) pow 2 /
                   mu pow 2` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]);;

(* ------------------------------------------------------------------------- *)
(* The restricted bound for |f| <= 1_G.                                      *)
(* ------------------------------------------------------------------------- *)

let TILESUM_MODDIL_GEN = prove
 (`?C. &0 <= C /\
    !(f:real->complex) (psi:real->complex) G E E1 a b (N:num) (Ep:real->bool)
      (g:real->real) (Q:(int#int#int)->bool).
      schwartz psi /\ real_measurable G /\ &0 < real_measure G /\
      (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      real_measurable E /\ &0 < real_measure E /\
      E1 SUBSET E /\
      (!y. y IN E1 ==> hl_maximal (\t. if t IN G then &1 else &0) (--y)
                       <= &4 * real_measure G / real_measure E) /\
      &1 <= a /\ a <= &2 /\ inv(&2) pow N <= real_measure G / real_measure E /\
      real_measurable Ep /\ Ep SUBSET IMAGE (\x. inv a * x) (IMAGE (--) E1) /\
      g real_measurable_on (:real) /\ FINITE Q
      ==> sum Q (\s. norm(carleson_ip (carleson_modulate b
                                         (carleson_dilate a psi)) s *
                 integral (IMAGE lift {x | x IN Ep /\ g x IN tile_Jr s})
                          (\z. phi_sigma s carleson_phi (drop z))))
          <= C * (real_measure G * (&N + &2) +
                  lnorm (:real^1) (&2) (\z. psi(drop z) - f(drop z)) *
                  sqrt(real_measure E))`,
  X_CHOOSE_THEN `CB:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "b4"))
    MODEL_TILESUM_BOUND THEN
  X_CHOOSE_THEN `C9:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pt"))
    TILESUM_PERTURB THEN
  EXISTS_TAC `CB + C9` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `G:real->bool`] DOM_L1L2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `fab = carleson_modulate b (carleson_dilate a (f:real->complex))` THEN
  ABBREV_TAC `Ga = IMAGE (\x. inv a * x) (G:real->bool)` THEN
  ABBREV_TAC `Ea = IMAGE (\x. inv a * x) (IMAGE (--) (E:real->bool))` THEN
  SUBGOAL_THEN `real_measurable (Ga:real->bool) /\
                real_measurable (Ea:real->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ga" THEN EXPAND_TAC "Ea" THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_SCALING; REFLECT_RMEAS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measure (Ga:real->bool) = inv a * real_measure (G:real->bool) /\
    real_measure (Ea:real->bool) = inv a * real_measure (E:real->bool)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ga" THEN EXPAND_TAC "Ea" THEN
    ASM_SIMP_TAC[REAL_MEASURE_SCALING; REFLECT_RMEAS; ABS_INV_POS;
      REFLECT_RMEASURE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv a /\ inv a <= &1` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_LE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Ga:real->bool) / real_measure (Ea:real->bool) =
                real_measure (G:real->bool) / real_measure (E:real->bool)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(a = &0) /\ ~(real_measure (E:real->bool) = &0)`
      MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_IMP_NZ]; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  SUBGOAL_THEN `Ep SUBSET (Ea:real->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
     EXISTS_TAC `IMAGE (\x. inv a * x) (IMAGE (--) (E1:real->bool))` THEN
    ASM SET_TAC[]; ALL_TAC] THEN
  (* the perturbation                                                        *)
  SUBGOAL_THEN `(\z. (fab:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [EXPAND_TAC "fab" THEN MATCH_MP_TAC MODDIL_GEN_LSPACE THEN
     EXISTS_TAC `G:real->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. carleson_modulate b
                       (carleson_dilate a (psi:real->complex)) (drop z))
                IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SCHWARTZ_L2; ETA_AX; CARLESON_SCHWARTZ_MODDIL;
     REAL_LT_IMP_NZ]; ALL_TAC] THEN
  USE_THEN "pt" (MP_TAC o SPECL
    [`g:real->real`; `Ep:real->bool`; `fab:real->complex`;
     `carleson_modulate b (carleson_dilate a (psi:real->complex))`;
     `Q:(int#int#int)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  (* the model bound for fab                                                 *)
  SUBGOAL_THEN
   `sum Q (\s. norm(carleson_ip fab s *
                 integral (IMAGE lift {x | x IN Ep /\
                                           (g:real->real) x IN tile_Jr s})
                          (\z. phi_sigma s carleson_phi (drop z))))
    <= CB * real_measure (Ga:real->bool) * (&N + &2)` ASSUME_TAC THENL
   [USE_THEN "b4" (MATCH_MP_TAC o SPECL
     [`fab:real->complex`; `Ga:real->bool`; `Ea:real->bool`; `Ep:real->bool`;
      `g:real->real`; `Q:(int#int#int)->bool`; `N:num`]) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "fab" THEN
       MATCH_MP_TAC MODDIL_GEN_MEASURABLE THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real` THEN EXPAND_TAC "fab" THEN EXPAND_TAC "Ga" THEN
      MATCH_MP_TAC MODDIL_GEN_DOM THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `hl_maximal (\t. if t IN G then &1 else &0) (a * x)` THEN
        CONJ_TAC THENL
       [ASM_MESON_TAC[HL_MAXIMAL_DILATE_LE]; ALL_TAC] THEN
      SUBGOAL_THEN
       `(x:real) IN IMAGE (\x. inv a * x) (IMAGE (--) (E1:real->bool))`
      MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a * inv a * --y = --y` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
         REAL_MUL_LID]; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  (* the norm of the difference                                              *)
  SUBGOAL_THEN
   `lnorm (:real^1) (&2)
          (\z. carleson_modulate b (carleson_dilate a (psi:real->complex))
                                 (drop z) -
               (fab:real->complex)(drop z))
    <= lnorm (:real^1) (&2) (\z. psi(drop z) - f(drop z))`
   ASSUME_TAC THENL
   [EXPAND_TAC "fab" THEN REWRITE_TAC[MODDIL_SUB] THEN
    SUBGOAL_THEN `(\z. (\x. (psi:real->complex) x - f x) (drop z))
                  IN lspace (:real^1) (&2)` ASSUME_TAC THENL
     [REWRITE_TAC[] THEN MATCH_MP_TAC LSPACE_SUB THEN
       ASM_SIMP_TAC[SCHWARTZ_L2] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`\x. (psi:real->complex) x - f x`; `a:real`; `b:real`]
      MODDIL_LNORM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_INV_LE_1; SQRT_1; SQRT_MONO_LE];
      ASM_MESON_TAC[LNORM_POS_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Ep:real->bool) <= real_measure (E:real->bool)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `real_measure (Ea:real->bool)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MEASURE_SUBSET];
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `Lp = lnorm (:real^1) (&2)
                         (\z. (psi:real->complex)(drop z) - f(drop z))` THEN
  ABBREV_TAC
   `Ld = lnorm (:real^1) (&2)
           (\z. carleson_modulate b (carleson_dilate a (psi:real->complex))
                                  (drop z) -
                (fab:real->complex)(drop z))` THEN
  SUBGOAL_THEN `&0 <= Ld` ASSUME_TAC THENL
   [EXPAND_TAC "Ld" THEN MATCH_MP_TAC LNORM_POS_LE THEN
     MATCH_MP_TAC LSPACE_SUB THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (Ep:real->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `C9 * Ld * sqrt(real_measure (Ep:real->bool)) <=
                C9 * Lp * sqrt(real_measure (E:real->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_MUL2; SQRT_POS_LE;
     SQRT_MONO_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `CB * real_measure (Ga:real->bool) * (&N + &2) <=
                CB * real_measure (G:real->bool) * (&N + &2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Lp` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (G:real->bool) * (&N + &2) /\
                &0 <= Lp * sqrt(real_measure (E:real->bool))`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
     ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C9 * real_measure (G:real->bool) * (&N + &2) /\
                &0 <= CB * Lp * sqrt(real_measure (E:real->bool))`
    STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    `!a b c:real. a <= b ==> b <= c ==> a <= c`) o
    check(fun th -> not(is_forall(concl th)) &&
                    can (find_term (fun tm -> tm = `C9:real`)) (concl th) &&
                    can (find_term (fun tm -> is_const tm &&
                                              fst(dest_const tm) = "sum"))
                        (concl th))) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
    `!a a' b c:real. a <= a' ==> a' + b <= c ==> a + b <= c`) o
    check(fun th -> not(is_forall(concl th)) &&
                    can (find_term (fun tm -> tm = `CB:real`)) (concl th) &&
                    can (find_term (fun tm -> is_const tm &&
                                              fst(dest_const tm) = "sum"))
                        (concl th))) THEN
  UNDISCH_TAC `C9 * Ld * sqrt(real_measure (Ep:real->bool)) <=
               C9 * Lp * sqrt(real_measure (E:real->bool))` THEN
  UNDISCH_TAC `CB * real_measure (Ga:real->bool) * (&N + &2) <=
               CB * real_measure (G:real->bool) * (&N + &2)` THEN
  UNDISCH_TAC `&0 <= C9 * real_measure (G:real->bool) * (&N + &2)` THEN
  UNDISCH_TAC `&0 <= CB * Lp * sqrt(real_measure (E:real->bool))` THEN
  REAL_ARITH_TAC);;

let HUNT_T_SCHWARTZ_GEN = prove
 (`?C. &0 <= C /\
    !(f:real->complex) (psi:real->complex) G E E1 (N:num).
      schwartz psi /\ real_measurable G /\ &0 < real_measure G /\
      (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      real_measurable E /\ &0 < real_measure E /\
      real_measurable E1 /\ E1 SUBSET E /\
      (!y. y IN E1 ==> hl_maximal (\t. if t IN G then &1 else &0) (--y)
                       <= &4 * real_measure G / real_measure E) /\
      inv(&2) pow N <= real_measure G / real_measure E
      ==> real_integral E1 (carleson_Ahat (fourier psi))
          <= C * (real_measure G * (&N + &2) +
                  lnorm (:real^1) (&2) (\z. psi(drop z) - f(drop z)) *
                  sqrt(real_measure E))`,
  X_CHOOSE_THEN `CT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tm"))
    TILESUM_MODDIL_GEN THEN
  EXISTS_TAC `inv(pi * carleson_thetatilde (&1) (&0)) *
               (&8 * CT) * log(&2)` THEN
  SUBGOAL_THEN `&0 <= inv(pi * carleson_thetatilde (&1) (&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_LE_MUL THEN
    MP_TAC PI_POS THEN MP_TAC CARLESON_THETATILDE_1_0_POS THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `G:real->bool`] DOM_L1L2) THEN
    STRIP_TAC THEN
  ABBREV_TAC `Lp = lnorm (:real^1) (&2)
                         (\z. (psi:real->complex)(drop z) - f(drop z))` THEN
  SUBGOAL_THEN `&0 <= Lp` ASSUME_TAC THENL
   [EXPAND_TAC "Lp" THEN MATCH_MP_TAC LNORM_POS_LE THEN
     MATCH_MP_TAC LSPACE_SUB THEN
    ASM_SIMP_TAC[SCHWARTZ_L2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `B0 = CT * (real_measure (G:real->bool) * (&N + &2) +
                         Lp * sqrt(real_measure (E:real->bool)))` THEN
  SUBGOAL_THEN `&0 <= B0` ASSUME_TAC THENL
   [EXPAND_TAC "B0" THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_LT_IMP_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(pi * carleson_thetatilde (&1) (&0)) *
              (&2 * (&4 * B0)) * log(&2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC T_SCHWARTZ_FROM_AMD THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `a * (&4 * B0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC AMD_FROM_TILESUM THEN
      ASM_SIMP_TAC[REFLECT_RMEAS; REAL_ARITH `&1 <= a ==> &0 < a`] THEN
      MAP_EVERY X_GEN_TAC [`Ep:real->bool`; `g:real->real`;
        `Q:(int#int#int)->bool`] THEN STRIP_TAC THEN
      EXPAND_TAC "B0" THEN EXPAND_TAC "Lp" THEN
      USE_THEN "tm" (MATCH_MP_TAC o SPECL
        [`f:real->complex`; `psi:real->complex`; `G:real->bool`;
         `E:real->bool`; `E1:real->bool`; `a:real`; `b:real`; `N:num`;
         `Ep:real->bool`; `g:real->real`; `Q:(int#int#int)->bool`]) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXPAND_TAC "B0" THEN REAL_ARITH_TAC);;

let HUNT_T_DOM_TRUNC = prove
 (`?C. &0 <= C /\
    !(f:real->complex) G E E1 (N:num) n.
      real_measurable G /\ &0 < real_measure G /\
      (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN G then &1 else &0)) /\
      real_measurable E /\ &0 < real_measure E /\
      real_measurable E1 /\ E1 SUBSET E /\
      (!y. y IN E1 ==> hl_maximal (\t. if t IN G then &1 else &0) (--y)
                       <= &4 * real_measure G / real_measure E) /\
      inv(&2) pow N <= real_measure G / real_measure E /\ &0 <= n
      ==> real_integral E1
            (\y. carleson_Ahat_trunc (fourier f) n y)
          <= C * real_measure G * (&N + &2)`,
  X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ts"))
    HUNT_T_SCHWARTZ_GEN THEN
  EXISTS_TAC `C:real` THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `G:real->bool`] DOM_L1L2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\z. fourier (f:real->complex) (drop z))
                IN lspace (:real^1) (&2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FOURIER_L1L2_IN_L2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (E1:real->bool) /\
                &0 <= real_measure (E:real->bool) /\
                &0 <= real_measure (G:real->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC CARLESON_REAL_LE_EPSILON THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `K = &1 + C * sqrt(real_measure (E:real->bool)) +
                  inv(sqrt(&2 * pi)) * sqrt(&2 * n) *
                    real_measure (E1:real->bool)` THEN
  SUBGOAL_THEN
   `&0 <= inv(sqrt(&2 * pi)) * sqrt(&2 * n) * real_measure (E1:real->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SQRT_POS_LE THEN
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * sqrt(real_measure (E:real->bool))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; SQRT_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `\z. (f:real->complex)(drop z)`
    LSPACE_APPROXIMATE_SCHWARTZ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / K`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `psi:real->complex` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `del = lnorm (:real^1) (&2)
                          (\z. (f:real->complex)(drop z) - psi(drop z))` THEN
  SUBGOAL_THEN `&0 <= del` ASSUME_TAC THENL
   [EXPAND_TAC "del" THEN MATCH_MP_TAC LNORM_POS_LE THEN
     MATCH_MP_TAC LSPACE_SUB THEN
    ASM_SIMP_TAC[SCHWARTZ_L2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* step 1: density step in the truncated operator                          *)
  MP_TAC(ISPECL [`fourier (f:real->complex)`; `fourier (psi:real->complex)`;
    `E1:real->bool`; `n:real`]
    CARLESON_TRUNC_DENSITY_STEP_FF) THEN
  ASM_SIMP_TAC[SCHWARTZ_FOURIER] THEN
  SUBGOAL_THEN `lnorm (:real^1) (&2) (\z. fourier (f:real->complex) (drop z) -
                                          fourier psi (drop z)) = del`
    SUBST1_TAC THENL
   [EXPAND_TAC "del" THEN
    SUBGOAL_THEN `(\z. fourier (f:real->complex) (drop z) -
                       fourier psi (drop z)) =
                  (\z. fourier (\x. f x - psi x) (drop z))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[FOURIER_SUB_L1; SCHWARTZ_ABSINT]; ALL_TAC] THEN
    MP_TAC(ISPEC `\x. (f:real->complex) x - psi x` FOURIER_L1L2_IN_L2) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_SUB; SCHWARTZ_ABSINT];
        MATCH_MP_TAC LSPACE_SUB THEN
          ASM_SIMP_TAC[SCHWARTZ_L2] THEN REAL_ARITH_TAC];
      SIMP_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "s1") THEN
  (* step 2: truncated <= full for Schwartz, then the Schwartz bound         *)
  SUBGOAL_THEN
   `real_integral E1
                  (\y. carleson_Ahat_trunc (fourier (psi:real->complex)) n y)
    <= real_integral E1 (carleson_Ahat (fourier psi))` (LABEL_TAC "s2") THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_LE; CARLESON_AHAT_TRUNC_INTEGRABLE_GEN;
     SCHWARTZ_FOURIER_L2; CARLESON_AHAT_SCHWARTZ_INTEGRABLE; SCHWARTZ_FOURIER;
     CARLESON_AHAT_TRUNC_SCHWARTZ_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral E1 (carleson_Ahat (fourier (psi:real->complex)))
    <= C * (real_measure (G:real->bool) * (&N + &2) +
            del * sqrt(real_measure (E:real->bool)))`
   (LABEL_TAC "s3") THENL
   [EXPAND_TAC "del" THEN ONCE_REWRITE_TAC[LNORM_SUB_SYM] THEN
    USE_THEN "ts" (MP_TAC o SPECL [`f:real->complex`; `psi:real->complex`;
                                   `G:real->bool`; `E:real->bool`;
                                   `E1:real->bool`; `N:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[]; ALL_TAC] THEN
  (* step 3: arithmetic                                                      *)
  SUBGOAL_THEN `del * K <= e` ASSUME_TAC THENL
   [SUBGOAL_THEN `del <= e / K` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ]; ALL_TAC] THEN
  UNDISCH_TAC `del * K <= e` THEN EXPAND_TAC "K" THEN
  REMOVE_THEN "s1" MP_TAC THEN REMOVE_THEN "s2" MP_TAC THEN
    REMOVE_THEN "s3" MP_TAC THEN
  UNDISCH_TAC `&0 <= del` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Restricted weak type (q0,q0) for |f| <= 1_F.                              *)
(* ------------------------------------------------------------------------- *)

let T_DOM_LEVEL_RESTRICTED = prove
 (`?C. &0 <= C /\
    !(f:real->complex) (Fs:real->bool) n mu (N:num).
      real_measurable Fs /\ &0 < real_measure Fs /\
      (\z. f(drop z)) measurable_on (:real^1) /\
      (!x. norm(f x) <= (if x IN Fs then &1 else &0)) /\
      &0 <= n /\ &0 < mu /\
      &0 < real_measure {y | mu < carleson_Ahat_trunc (fourier f) n y} /\
      inv(&2) pow N <=
        real_measure Fs /
        real_measure {y | mu < carleson_Ahat_trunc (fourier f) n y}
      ==> mu * real_measure {y | mu < carleson_Ahat_trunc (fourier f) n y}
          <= C * real_measure Fs * (&N + &2)`,
  X_CHOOSE_THEN `CT:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ti"))
    HUNT_T_DOM_TRUNC THEN
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w2"))
    T_DOM_LEVEL_WEAK22 THEN
  EXISTS_TAC `&2 * CT` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `Fs:real->bool`] DOM_L1L2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `f:real->complex` FOURIER_L1L2_IN_L2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = {y | mu < carleson_Ahat_trunc (fourier f) n y}` THEN
  SUBGOAL_THEN `real_measurable (L:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    USE_THEN "w2" (MP_TAC o SPECL [`f:real->complex`; `Fs:real->bool`;
      `n:real`; `mu:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]; ALL_TAC] THEN
  ABBREV_TAC `tau = &4 * real_measure (Fs:real->bool) /
                         real_measure (L:real->bool)` THEN
  SUBGOAL_THEN `&0 < tau` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN
       ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  ABBREV_TAC
   `Om = {x | tau < hl_maximal (\t. if t IN Fs then &1 else &0) x}` THEN
  SUBGOAL_THEN `real_measurable (Om:real->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CH_HL_SUPERLEVEL_MEAS]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (Om:real->bool) <=
                real_measure (L:real->bool) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `&2 * real_measure (Fs:real->bool) / tau` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CH_HL_MAXIMAL_WEAK11_INDICATOR];
      EXPAND_TAC "tau" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `~(real_measure (Fs:real->bool) = &0) /\
                    ~(real_measure (L:real->bool) = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]; ALL_TAC] THEN
  ABBREV_TAC `E1 = L DIFF IMAGE (--) (Om:real->bool)` THEN
  SUBGOAL_THEN `real_measurable (E1:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "E1" THEN MATCH_MP_TAC REAL_MEASURABLE_DIFF THEN
    ASM_SIMP_TAC[REFLECT_RMEAS]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measure (L:real->bool) / &2 <=
                real_measure (E1:real->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `real_measure (L:real->bool) <= real_measure (E1:real->bool) +
                   real_measure (IMAGE (--) (Om:real->bool))`
      MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `real_measure ((E1:real->bool) UNION
                                IMAGE (--) (Om:real->bool))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_MEASURE_SUBSET THEN
        ASM_SIMP_TAC[REAL_MEASURABLE_UNION; REFLECT_RMEAS] THEN
          EXPAND_TAC "E1" THEN SET_TAC[];
        ASM_SIMP_TAC[REAL_MEASURE_UNION_LE; REFLECT_RMEAS]]; ALL_TAC] THEN
    ASM_SIMP_TAC[REFLECT_RMEASURE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the restricted bound on E1                                              *)
  SUBGOAL_THEN `real_integral E1 (\y. carleson_Ahat_trunc (fourier f) n y)
                <= CT * real_measure (Fs:real->bool) * (&N + &2)`
    ASSUME_TAC THENL
   [USE_THEN "ti" (MATCH_MP_TAC o SPECL [`f:real->complex`; `Fs:real->bool`;
     `L:real->bool`; `E1:real->bool`; `N:num`; `n:real`]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [EXPAND_TAC "E1" THEN SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `y:real` THEN EXPAND_TAC "E1" THEN
    REWRITE_TAC[IN_DIFF; IN_IMAGE; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `--y:real`) THEN EXPAND_TAC "Om" THEN
    REWRITE_TAC[REAL_NEG_NEG; IN_ELIM_THM; REAL_NOT_LT];
    ALL_TAC] THEN
  (* the lower bound on E1                                                   *)
  SUBGOAL_THEN `mu * real_measure (E1:real->bool) <=
                real_integral E1 (\y. carleson_Ahat_trunc (fourier f) n y)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `real_integral E1 (\y:real. mu)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_CONST_MEASURABLE] THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_INTEGRAL_LE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRABLE_ON_CONST_MEASURABLE];
      ASM_SIMP_TAC[CARLESON_AHAT_TRUNC_INTEGRABLE_GEN];
      X_GEN_TAC `y:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real) IN L` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "L" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `mu * real_measure (L:real->bool) / &2 <=
                mu * real_measure (E1:real->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
  UNDISCH_TAC `mu * real_measure (E1:real->bool) <=
               real_integral E1 (\y. carleson_Ahat_trunc (fourier f) n y)` THEN
  UNDISCH_TAC `real_integral E1 (\y. carleson_Ahat_trunc (fourier f) n y)
                <= CT * real_measure (Fs:real->bool) * (&N + &2)` THEN
  REAL_ARITH_TAC);;

let T_DOM_RWT_Q0 = prove
 (`!q0. &1 < q0 /\ q0 <= &2
        ==> ?D. &0 <= D /\
                !(f:real->complex) (Fs:real->bool) n mu.
                  real_measurable Fs /\
                  (\z. f(drop z)) measurable_on (:real^1) /\
                  (!x. norm(f x) <= (if x IN Fs then &1 else &0)) /\
                  &0 <= n /\ &0 < mu
                  ==> real_measure
                        {y | mu < carleson_Ahat_trunc (fourier f) n y}
                      <= D * real_measure Fs * inv(mu rpow q0)`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w2"))
    T_DOM_LEVEL_WEAK22 THEN
  X_CHOOSE_THEN `CR:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rs"))
    T_DOM_LEVEL_RESTRICTED THEN
  MP_TAC(SPEC `q0:real` LOGPOW_ABSORB) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lp"))) THEN
  ABBREV_TAC `CR1 = CR + &1` THEN
  SUBGOAL_THEN `&0 < CR1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `C2 + &1 + D0 * CR1 rpow q0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + &1 + b`) THEN
     ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; RPOW_POS_LE]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `L = {y | mu < carleson_Ahat_trunc (fourier f) n y}` THEN
  USE_THEN "w2" (MP_TAC o SPECL [`f:real->complex`; `Fs:real->bool`;
    `n:real`; `mu:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= real_measure (Fs:real->bool) /\
                &0 <= real_measure (L:real->bool)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu rpow q0` ASSUME_TAC THENL
    [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= D0 * CR1 rpow q0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; RPOW_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= real_measure (Fs:real->bool) * inv(mu rpow q0)`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  (* case mu >= 1: weak (2,2)                                                *)
  ASM_CASES_TAC `&1 <= mu` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `C2 * real_measure (Fs:real->bool) / mu pow 2` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `C2 * real_measure (Fs:real->bool) * inv(mu rpow q0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN
       MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM RPOW_POW] THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [ALL_TAC; MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= inv(mu rpow q0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `q0:real` RPOW_ONE)] THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* case |L| <= |F|                                                         *)
  ASM_CASES_TAC `real_measure (L:real->bool) <=
                  real_measure (Fs:real->bool)` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `real_measure (Fs:real->bool) * inv(mu rpow q0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC `real_measure (Fs:real->bool) * &1` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LMUL]];
      SUBGOAL_THEN `&0 <= C2 * real_measure (Fs:real->bool) *
                          inv(mu rpow q0) /\
                    &0 <= (D0 * CR1 rpow q0) * real_measure (Fs:real->bool) *
                          inv(mu rpow q0)` MP_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the restricted case: |L| > |F| > 0                                      *)
  SUBGOAL_THEN `&0 < real_measure (Fs:real->bool)` ASSUME_TAC THENL
   [ASM_CASES_TAC `real_measure (Fs:real->bool) = &0` THENL
     [UNDISCH_TAC `real_measure (L:real->bool) <=
                   C2 * real_measure (Fs:real->bool) / mu pow 2` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < real_measure (L:real->bool)` ASSUME_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `r = real_measure (L:real->bool) /
                  real_measure (Fs:real->bool)` THEN
  SUBGOAL_THEN `&1 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?N:num. inv(&2) pow N <= real_measure (Fs:real->bool) /
                                         real_measure (L:real->bool)`
    MP_TAC THENL
   [MP_TAC(SPECL [`inv(&2)`;
     `real_measure (Fs:real->bool) / real_measure (L:real->bool)`]
     REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV] THEN ASM_REAL_ARITH_TAC;
      MESON_TAC[REAL_LT_IMP_LE]]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `real_measure (Fs:real->bool) / real_measure (L:real->bool)
                 = inv r` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_INV_DIV]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow N <= &2 * r` ASSUME_TAC THENL
   [ASM_CASES_TAC `N = 0` THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N - 1` o check(fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `inv(&2)`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE; GSYM REAL_INV_POW] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 pow (N - 1) < r` MP_TAC THENL
     [MP_TAC(SPECL [`inv r`; `inv(&2 pow (N - 1))`] REAL_LT_INV2) THEN
      ASM_REWRITE_TAC[REAL_INV_INV] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&2 pow N = &2 * &2 pow (N - 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN
       ASM_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
  (* the restricted level bound                                              *)
  USE_THEN "rs" (MP_TAC o SPECL [`f:real->complex`; `Fs:real->bool`; `n:real`;
    `mu:real`; `N:num`]) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `inv(&2) pow N <= real_measure (Fs:real->bool) /
                                  real_measure (L:real->bool)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r <= (CR1 / mu) * (&N + &2)` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    MP_TAC(SPECL [`CR:real`; `mu:real`; `real_measure (L:real->bool)`;
                  `real_measure (Fs:real->bool)`;
                  `CR1:real`; `&N + &2`] RATIO_FROM_PROD) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "CR1" THEN REAL_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  USE_THEN "lp" (MP_TAC o SPECL [`CR1 / mu`; `r:real`; `N:num`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[real_div; RPOW_MUL; RPOW_INV] THEN DISCH_TAC THEN
  SUBGOAL_THEN `real_measure (L:real->bool) =
                r * real_measure (Fs:real->bool)` SUBST1_TAC THENL
   [EXPAND_TAC "r" THEN
     UNDISCH_TAC `&0 < real_measure (Fs:real->bool)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(D0 * CR1 rpow q0 * inv(mu rpow q0)) *
              real_measure (Fs:real->bool)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RMUL]; ALL_TAC] THEN
  SUBGOAL_THEN `(D0 * CR1 rpow q0 * inv(mu rpow q0)) *
                 real_measure (Fs:real->bool) =
                (D0 * CR1 rpow q0) * (real_measure Fs * inv(mu rpow q0))`
    SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Structure of the truncated operator: it is sublinear and homogeneous,     *)
(* depends only on the symbol on [-n,n], and is measurable for L^1           *)
(* functions.                                                                *)
(* ------------------------------------------------------------------------- *)

let TRUNC_WINDOWS_NONEMPTY = prove
 (`!(g:real->real->real) n. &0 <= n
     ==> ~({g a b | a,b | --n <= a /\ a <= b /\ b <= n} = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`(g:real->real->real) (--n) (--n)`;
    `--n:real`; `--n:real`] THEN
  ASM_REAL_ARITH_TAC);;

let TRUNC_WINDOW_INTEGRABLE = prove
 (`!(Ff:real->complex) n y a b.
     --n <= a /\ a <= b /\ b <= n /\
     (\z. Ff(drop z)) absolutely_integrable_on
       (IMAGE lift (real_interval[--n,n]))
     ==> (\x. cexp(--(ii * Cx y * Cx(drop x))) * Ff(drop x)) integrable_on
         (IMAGE lift (real_interval[a,b]))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (Ff:real->complex)(drop z)) absolutely_integrable_on
                (IMAGE lift (real_interval[a,b]))` ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
    EXISTS_TAC `IMAGE lift (real_interval[--n,n])` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; SUBSET_INTERVAL_1; LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC FOURIER_MODULATION_ABSINT_ON THEN
  ASM_REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; MEASURABLE_INTERVAL]);;

let AHAT_TRUNC_ADD_LE = prove
 (`!(Ff:real->complex) Gg n y.
     &0 <= n /\
     (\z. Ff(drop z)) absolutely_integrable_on
       (IMAGE lift (real_interval[--n,n])) /\
     (\z. Gg(drop z)) absolutely_integrable_on
       (IMAGE lift (real_interval[--n,n]))
     ==> carleson_Ahat_trunc (\x. Ff x + Gg x) n y
         <= carleson_Ahat_trunc Ff n y + carleson_Ahat_trunc Gg n y`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [carleson_Ahat_trunc] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[TRUNC_WINDOWS_NONEMPTY]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(sqrt(&2 * pi)) * norm(integral
                 (IMAGE lift (real_interval[a,b]))
                 (\x. cexp(--(ii * Cx y * Cx(drop x))) *
                   (Ff:real->complex)(drop x))) +
              inv(sqrt(&2 * pi)) * norm(integral
                 (IMAGE lift (real_interval[a,b]))
                 (\x. cexp(--(ii * Cx y * Cx(drop x))) *
                   (Gg:real->complex)(drop x)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
       MP_TAC PI_POS THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `integral (IMAGE lift (real_interval[a,b]))
        (\x. cexp(--(ii * Cx y * Cx(drop x))) *
          ((Ff:real->complex)(drop x) + Gg(drop x))) =
      integral (IMAGE lift (real_interval[a,b]))
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * Ff(drop x)) +
      integral (IMAGE lift (real_interval[a,b]))
        (\x. cexp(--(ii * Cx y * Cx(drop x))) * Gg(drop x))`
     SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN
       MATCH_MP_TAC INTEGRAL_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC TRUNC_WINDOW_INTEGRABLE THEN
        EXISTS_TAC `n:real` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_TRIANGLE];
    ASM_SIMP_TAC[REAL_LE_ADD2; CARLESON_TRUNC_WINDOW_LE_SUP]]);;

let AHAT_TRUNC_CMUL_LE = prove
 (`!(Ff:real->complex) c n y.
     &0 <= n /\
     (\z. Ff(drop z)) absolutely_integrable_on
       (IMAGE lift (real_interval[--n,n]))
     ==> carleson_Ahat_trunc (\x. c * Ff x) n y
         <= norm c * carleson_Ahat_trunc Ff n y`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [carleson_Ahat_trunc] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[TRUNC_WINDOWS_NONEMPTY]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `integral (IMAGE lift (real_interval[a,b]))
      (\x. cexp(--(ii * Cx y * Cx(drop x))) * c * (Ff:real->complex)(drop x)) =
    c * integral (IMAGE lift (real_interval[a,b]))
          (\x. cexp(--(ii * Cx y * Cx(drop x))) * Ff(drop x))`
   SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(\x. cexp(--(ii * Cx y * Cx(drop x))) * c * (Ff:real->complex)(drop x)) =
      (\x. c * (cexp(--(ii * Cx y * Cx(drop x))) *
                Ff(drop x)))` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRAL_COMPLEX_LMUL THEN
    MATCH_MP_TAC TRUNC_WINDOW_INTEGRABLE THEN
      EXISTS_TAC `n:real` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(c:complex) * (inv(sqrt(&2 * pi)) *
                norm(integral (IMAGE lift (real_interval[a,b]))
                  (\x. cexp(--(ii * Cx y * Cx(drop x))) *
                    (Ff:real->complex)(drop x))))` THEN
  CONJ_TAC THENL
   [REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LMUL; NORM_POS_LE; CARLESON_TRUNC_WINDOW_LE_SUP]]);;

(* the truncated operator only sees its symbol on [-n,n]                     *)
let AHAT_TRUNC_RESTRICT = prove
 (`!(Ff:real->complex) n y.
     carleson_Ahat_trunc Ff n y =
     carleson_Ahat_trunc
       (\x. if x IN real_interval[--n,n] then Ff x else Cx(&0)) n y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[carleson_Ahat_trunc] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:real` THEN
  SUBGOAL_THEN
   `!a b. --n <= a /\ a <= b /\ b <= n
          ==> integral (IMAGE lift (real_interval[a,b]))
                (\x. cexp(--(ii * Cx y * Cx(drop x))) *
                  (Ff:real->complex)(drop x)) =
              integral (IMAGE lift (real_interval[a,b]))
                (\x. cexp(--(ii * Cx y * Cx(drop x))) *
                     (if drop x IN real_interval[--n,n] then
                       Ff(drop x) else Cx(&0)))`
   ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    REWRITE_TAC[FORALL_IN_IMAGE; LIFT_DROP; IN_REAL_INTERVAL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `a:real`
    (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `b:real`] THEN ASM_SIMP_TAC[]);;

let FOURIER_RESTRICT_LSPACE = prove
 (`!(f:real->complex) n.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z. if drop z IN real_interval[--n,n] then fourier f (drop z)
              else Cx(&0))
         IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `K:real` o MATCH_MP FOURIER_BOUND_UNIFORM) THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:P`] LSPACE_BOUNDED_MEASURABLE) THEN
  EXISTS_TAC `\z. Cx(abs K + &1) * (if drop z IN real_interval[--n,n]
                                    then Cx(&1) else Cx(&0))` THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MATCH_MP_TAC MEASURABLE_ON_CASES THEN
      REWRITE_TAC[MEASURABLE_ON_CONST] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `{x:real^1 | drop x IN real_interval[--n,n]} =
                     interval[lift(--n),lift n]`
        SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTERVAL_1; IN_REAL_INTERVAL;
         LIFT_DROP]; ALL_TAC] THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL];
      ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; FOURIER_CONTINUOUS_ON]];
    ASM_SIMP_TAC[LSPACE_COMPLEX_LMUL; CH_CHI_LSPACE2;
      REAL_MEASURABLE_REAL_INTERVAL];
    X_GEN_TAC `z:real^1` THEN BETA_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop z`) THEN REAL_ARITH_TAC]);;

let T_TRUNC_MEASURABLE_L1 = prove
 (`!(f:real->complex) n.
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\ &0 <= n
     ==> (\y. carleson_Ahat_trunc (fourier f) n y) real_measurable_on (:real)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[AHAT_TRUNC_RESTRICT] THEN
  MATCH_MP_TAC CARLESON_AHAT_TRUNC_MEASURABLE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FOURIER_RESTRICT_LSPACE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* T_n f := carleson_Ahat_trunc (fourier f) n for f in L^1: sublinear (for   *)
(* finite sums), homogeneous and measurable.                                 *)
(* ------------------------------------------------------------------------- *)

let FOURIER_LOCAL_ABSINT = prove
 (`!(f:real->complex) n.
     (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> (\z. fourier f (drop z)) absolutely_integrable_on
         (IMAGE lift (real_interval[--n,n]))`,
  ASM_MESON_TAC[IMAGE_LIFT_REAL_INTERVAL; ABSOLUTELY_INTEGRABLE_CONTINUOUS;
    CONTINUOUS_ON_SUBSET; SUBSET_UNIV; FOURIER_CONTINUOUS_ON]);;

let T_ADD_LE = prove
 (`!(f:real->complex) g n y.
     &0 <= n /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\z. g(drop z)) absolutely_integrable_on (:real^1)
     ==> carleson_Ahat_trunc (fourier (\x. f x + g x)) n y
         <= carleson_Ahat_trunc (fourier f) n y +
           carleson_Ahat_trunc (fourier g) n y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `fourier (\x. (f:real->complex) x + g x) =
                (\y. fourier f y + fourier g y)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; FOURIER_ADD; MODINT]; ALL_TAC] THEN
  MATCH_MP_TAC AHAT_TRUNC_ADD_LE THEN ASM_SIMP_TAC[FOURIER_LOCAL_ABSINT]);;

let T_CMUL_LE = prove
 (`!(f:real->complex) c n y.
     &0 <= n /\ (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> carleson_Ahat_trunc (fourier (\x. c * f x)) n y
         <= norm c * carleson_Ahat_trunc (fourier f) n y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `fourier (\x. c * (f:real->complex) x) = (\y. c * fourier f y)`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[FUN_EQ_THM; FOURIER_LMUL; MODINT]; ALL_TAC] THEN
  MATCH_MP_TAC AHAT_TRUNC_CMUL_LE THEN ASM_SIMP_TAC[FOURIER_LOCAL_ABSINT]);;

let T_VSUM_LE = prove
 (`!(g:num->real->complex) n y J.
     &0 <= n /\ (!j. (\z. g j (drop z)) absolutely_integrable_on (:real^1))
     ==> carleson_Ahat_trunc (fourier (\x. vsum(0..J) (\j. g j x))) n y
         <= sum(0..J) (\j. carleson_Ahat_trunc (fourier (g j)) n y)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[VSUM_SING_NUMSEG; SUM_SING_NUMSEG; ETA_AX;
     REAL_LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `carleson_Ahat_trunc
      (fourier (\x. vsum(0..J) (\j. (g:num->real->complex) j x))) n y +
    carleson_Ahat_trunc (fourier (g (SUC J))) n y` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[T_ADD_LE; ABSOLUTELY_INTEGRABLE_VSUM; FINITE_NUMSEG];
    ASM_SIMP_TAC[REAL_LE_RADD]]);;

let T_LEVEL_LMEAS = prove
 (`!(f:real->complex) n mu.
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\ &0 <= n
     ==> real_lebesgue_measurable
           {y | mu < carleson_Ahat_trunc (fourier f) n y}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`f:real->complex`; `n:real`] T_TRUNC_MEASURABLE_L1) THEN
  ASM_REWRITE_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT] THEN
  DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN REWRITE_TAC[real_gt]);;

(* ------------------------------------------------------------------------- *)
(* Combinatorics of the dyadic level decomposition.                          *)
(* ------------------------------------------------------------------------- *)

(* superlevel set of a dominated sum, by a finite union bound                *)
let LEVEL_UNION_BOUND = prove
 (`!(Sf:real->real) (S0:real->real) (S:num->real->real) (c:num->real) lam J.
     &0 < lam /\ sum(0..J) c <= &1 / &2 /\
     (!y. Sf y <= S0 y + sum(0..J) (\j. S j y)) /\
     real_measurable {y | lam < Sf y} /\
     real_measurable {y | lam / &2 < S0 y} /\
     (!j. j IN 0..J ==> real_measurable {y | c j * lam < S j y})
     ==> real_measure {y | lam < Sf y}
         <= real_measure {y | lam / &2 < S0 y} +
            sum(0..J) (\j. real_measure {y | c j * lam < S j y})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `real_measure ({y | lam / &2 < S0 y} UNION
                  UNIONS (IMAGE (\j. {y | c j * lam < (S:num->real->real) j y})
                                (0..J)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_MEASURE_SUBSET THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MEASURABLE_UNION; REAL_MEASURABLE_UNIONS; FINITE_IMAGE;
       FINITE_NUMSEG; FORALL_IN_IMAGE];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `lam / &2 < (S0:real->real) y` THEN
      ASM_CASES_TAC `?j. j IN 0..J /\ c j * lam < (S:num->real->real) j y` THEN
      ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM;
      REAL_NOT_LT; IN_NUMSEG]) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `sum(0..J) (\j. (S:num->real->real) j y) <=
                  sum(0..J) (\j. c j * lam)` MP_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_RMUL] THEN
    SUBGOAL_THEN `sum(0..J) c * lam <= &1 / &2 * lam` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RMUL; REAL_LT_IMP_LE]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `Sf:real->real`)) (concl th))) THEN
    UNDISCH_TAC `~(lam / &2 < (S0:real->real) y)` THEN
      UNDISCH_TAC `lam < (Sf:real->real) y` THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_measure {y | lam / &2 < S0 y} +
                real_measure
                 (UNIONS (IMAGE (\j. {y | c j * lam < (S:num->real->real) j y})
                                (0..J)))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_MEASURE_UNION_LE; REAL_MEASURABLE_UNIONS; FINITE_IMAGE;
       FINITE_NUMSEG; FORALL_IN_IMAGE];
      ASM_SIMP_TAC[REAL_LE_LADD;
        REAL_MEASURE_UNIONS_LE_IMAGE; FINITE_NUMSEG]]]);;

let LEVEL_EXISTS = prove
 (`!lam t J. &0 < lam /\ lam < t /\ t <= &2 pow (J + 1) * lam
     ==> ?k. k <= J /\ &2 pow k * lam < t /\ t <= &2 pow (k + 1) * lam`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. t <= &2 pow (k + 1) * lam` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[NOT_LT];
    ASM_CASES_TAC `k = 0` THENL
     [ASM_REWRITE_TAC[real_pow; REAL_MUL_LID]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 + 1 = k` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC]);;

let LEVEL_UNIQUE = prove
 (`!lam t j k. &0 < lam /\ &2 pow j * lam < t /\ t <= &2 pow (j + 1) * lam /\
               &2 pow k * lam < t /\ t <= &2 pow (k + 1) * lam ==> j = k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!a b. a < b ==> &2 pow (a + 1) * lam <= &2 pow b * lam`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONJ_TAC THENL
      [REAL_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LE_ANTISYM; GSYM NOT_LT] THEN CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `j:num`]) THEN
     ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `k:num`]) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let LEVEL_IFF = prove
 (`!lam t k. &0 < lam /\ &2 pow k * lam < t /\ t <= &2 pow (k + 1) * lam
     ==> !j. (&2 pow j * lam < t /\ t <= &2 pow (j + 1) * lam) <=> j = k`,
  ASM_MESON_TAC[LEVEL_UNIQUE]);;

let LEVEL_LOW = prove
 (`!lam t j. &0 < lam /\ t <= lam ==> ~(&2 pow j * lam < t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lam <= &2 pow j * lam` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
     MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* the level pieces of a value v add up to its high part                     *)
let LEVEL_VSUM = prove
 (`!lam t (v:complex) J. &0 < lam /\ t <= &2 pow (J + 1) * lam
     ==> vsum(0..J) (\j. if &2 pow j * lam < t /\ t <= &2 pow (j + 1) * lam
                         then v else Cx(&0)) =
         (if lam < t then v else Cx(&0))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MP_TAC(SPECL [`lam:real`; `t:real`; `J:num`] LEVEL_EXISTS) THEN
     ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`lam:real`; `t:real`; `k:num`] LEVEL_IFF) THEN
      ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG;
      LE_0];
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    X_GEN_TAC `j:num` THEN
      MP_TAC(SPECL [`lam:real`; `t:real`; `j:num`] LEVEL_LOW) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* a weighted sum over the levels sees at most one level                     *)
let LEVEL_SUM_LE = prove
 (`!lam t (w:num->real) W J. &0 < lam /\ &0 <= W /\
     (!j. &2 pow j * lam < t /\ t <= &2 pow (j + 1) * lam ==> w j <= W)
     ==> sum(0..J) (\j. if &2 pow j * lam < t /\ t <= &2 pow (j + 1) * lam
                        then w j else &0) <= W`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `?k. &2 pow k * lam < t /\ t <= &2 pow (k + 1) * lam` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`lam:real`; `t:real`; `k:num`] LEVEL_IFF) THEN
      ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `sum(0..J) (\j. if j = k then (w:num->real) j else &0) =
                  sum(0..J) (\j. if j = k then w k else &0)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_DELTA] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[SUM_EQ_0_NUMSEG]]);;

(* ------------------------------------------------------------------------- *)
(* Measure-theoretic pieces of the level decomposition.                      *)
(* ------------------------------------------------------------------------- *)

let NORM_RMEAS = prove
 (`!(f:real->complex). (\z. f(drop z)) measurable_on (:real^1)
     ==> (\x. norm(f x)) real_measurable_on (:real)`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC[real_measurable_on; IMAGE_LIFT_UNIV; o_DEF] THEN
  MATCH_MP_TAC MEASURABLE_ON_NORM THEN ASM_REWRITE_TAC[]);;

let SUPERLEVEL_RMEAS = prove
 (`!(phi:real->real) a b p.
     &0 < a /\ &0 < p /\ (!x. &0 <= phi x) /\ phi real_measurable_on (:real) /\
     (\x. phi x rpow p) real_integrable_on (:real)
     ==> real_measurable {x | a < phi x /\ phi x <= b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MEASURABLE_REAL_INTEGRABLE] THEN
  MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x:real. inv(a rpow p) * phi x rpow p` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM real_lebesgue_measurable] THEN
    SUBGOAL_THEN `{x | a < phi x /\ phi x <= b} =
                  {x | (phi:real->real) x > a} INTER {x | phi x <= b}`
      SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LEBESGUE_MEASURABLE_INTER THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT];
      ASM_MESON_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LE]];
    ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL];
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN COND_CASES_TAC THENL
     [REWRITE_TAC[REAL_ABS_NUM] THEN
      SUBGOAL_THEN `&0 < a rpow p` ASSUME_TAC THENL
        [MATCH_MP_TAC RPOW_POS_LT; ALL_TAC] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
        MATCH_MP_TAC RPOW_LE2 THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN
         MATCH_MP_TAC RPOW_POS_LE THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[RPOW_POS_LE]]]]);;

let INDICATOR_CONST_INTEGRAL = prove
 (`!(P:real->bool) w. real_measurable {x | P x}
     ==> (\x. if P x then w else &0) real_integrable_on (:real) /\
         real_integral (:real) (\x. if P x then w else &0) =
         w * real_measure {x | P x}`,
  REPEAT GEN_TAC THEN
    SUBGOAL_THEN `(\x. if P x then w else &0) =
                  (\x. if x IN {x | P x} then (\x:real. w) x else &0)`
    SUBST1_TAC THENL [REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[REAL_INTEGRAL_RESTRICT_UNIV; REAL_INTEGRABLE_RESTRICT_UNIV] THEN
  ASM_SIMP_TAC[REAL_INTEGRABLE_ON_CONST_MEASURABLE;
    REAL_INTEGRAL_CONST_MEASURABLE]);;

(* Chebyshev over the dyadic levels                                          *)
let LEVEL_CHEB = prove
 (`!(phi:real->real) lam p J.
     &0 < lam /\ &0 < p /\ (!x. &0 <= phi x) /\
     phi real_measurable_on (:real) /\
     (\x. phi x rpow p) real_integrable_on (:real)
     ==> sum(0..J) (\j. real_measure {x | &2 pow j * lam < phi x /\
                                          phi x <= &2 pow (j + 1) * lam} *
                        (&2 pow j * lam) rpow p)
         <= real_integral (:real) (\x. phi x rpow p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. real_measurable {x | &2 pow j * lam < phi x /\
                                         phi x <= &2 pow (j + 1) * lam}`
    ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SUPERLEVEL_RMEAS THEN
     EXISTS_TAC `p:real` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (:real)
                (\x. sum(0..J) (\j. if &2 pow j * lam < phi x /\
                                       phi x <= &2 pow (j + 1) * lam
                                    then (&2 pow j * lam) rpow p
                                    else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN
     `real_integral (:real)
        (\x. sum(0..J) (\j. if &2 pow j * lam < phi x /\
                               phi x <= &2 pow (j + 1) * lam
                            then (&2 pow j * lam) rpow p else &0)) =
      sum(0..J) (\j. real_integral (:real)
        (\x. if &2 pow j * lam < phi x /\ phi x <= &2 pow (j + 1) * lam
             then (&2 pow j * lam) rpow p else &0))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_SUM; FINITE_NUMSEG; INDICATOR_CONST_INTEGRAL];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN
      MP_TAC(ISPECL [`\x. &2 pow j * lam < (phi:real->real) x /\
                          phi x <= &2 pow (j + 1) * lam`;
                     `(&2 pow j * lam) rpow p`] INDICATOR_CONST_INTEGRAL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_SYM];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN
    ASM_REWRITE_TAC[IN_UNIV] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_SUM; FINITE_NUMSEG; INDICATOR_CONST_INTEGRAL];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN MATCH_MP_TAC LEVEL_SUM_LE THEN
    ASM_SIMP_TAC[RPOW_POS_LE] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC RPOW_LE2 THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The pieces: measurability of the cut-offs, the low part (by weak type     *)
(* (2,2)), the scaled restricted bound, and the geometric weights.           *)
(* ------------------------------------------------------------------------- *)

let CASES_MEAS = prove
 (`!(f:real->complex) (P:real->bool).
     (\z. f(drop z)) measurable_on (:real^1) /\
     real_lebesgue_measurable {x | P x}
     ==> (\z. if P(drop z) then f(drop z) else Cx(&0)) measurable_on
       (:real^1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CASES THEN
  ASM_REWRITE_TAC[MEASURABLE_ON_CONST] THEN
  SUBGOAL_THEN `{z:real^1 | P(drop z)} = IMAGE lift {x | P x}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
     ASM_MESON_TAC[LIFT_DROP]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_LEBESGUE_MEASURABLE]);;

let L1_BOUNDED_IMP_L2 = prove
 (`!(h:real^1->complex) B.
     h measurable_on (:real^1) /\ h absolutely_integrable_on (:real^1) /\
     (!z. norm(h z) <= B)
     ==> h IN lspace (:real^1) (&2)`,
  REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[lspace; IN_ELIM_THM] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\z. lift(abs B * norm((h:real^1->complex) z))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_LIFT_RPOW THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_ON_NORM]; REAL_ARITH_TAC];
    ASM_SIMP_TAC[LIFT_CMUL; INTEGRABLE_CMUL;
      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_NORM];
    X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_LIFT; LIFT_DROP] THEN
    SUBGOAL_THEN `abs(norm((h:real^1->complex) z) rpow &2) =
                  norm(h z) * norm(h z)` SUBST1_TAC THENL
     [REWRITE_TAC[RPOW_POW; REAL_POW_2; REAL_ABS_MUL;
       REAL_ABS_NORM]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^1`) THEN REAL_ARITH_TAC]);;

let LOW_SQ_LE = prove
 (`!u lam p. &0 <= u /\ u <= lam /\ &0 < lam /\ &1 <= p /\ p <= &2
     ==> u pow 2 <= lam rpow (&2 - p) * u rpow p`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u = &0` THENL
   [ASM_SIMP_TAC[RPOW_ZERO] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u pow 2 = u rpow (&2 - p) * u rpow p` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
     REWRITE_TAC[REAL_ARITH `(&2 - p) + p = &2`; RPOW_POW]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[RPOW_POS_LE] THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC);;

let LOW_ARITH = prove
 (`!C2 L Mq a b lam. &0 <= C2 /\ &0 < a /\ &0 < b /\ &0 < lam /\
                     a * b = lam pow 2 /\ L <= a * Mq
     ==> C2 * L / (lam / &2) pow 2 <= (&4 * C2) * Mq / b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C2 * L / (lam / &2) pow 2 = (&4 * C2) * L / (a * b)`
    SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(a * Mq) / (a * b)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_MUL];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(a = &0) /\ ~(b = &0)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]]);;

let LOW_PART_BOUND = prove
 (`?C2. &0 <= C2 /\
    !(f:real->complex) p n lam.
      &1 <= p /\ p <= &2 /\ (\z. f(drop z)) measurable_on (:real^1) /\
      (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
      (\x. norm(f x) rpow p) real_integrable_on (:real) /\ &0 <= n /\ &0 < lam
      ==> real_measurable {y | lam / &2 < carleson_Ahat_trunc
                                  (fourier (\x. if norm(f x) <= lam
                                                then f x else Cx(&0))) n y} /\
          real_measure {y | lam / &2 < carleson_Ahat_trunc
                                  (fourier (\x. if norm(f x) <= lam
                                                then f x else Cx(&0))) n y}
          <= C2 * real_integral (:real) (\x. norm(f x) rpow p) / lam rpow p`,
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w2"))
    AHAT_TRUNC_WEAK22 THEN
  EXISTS_TAC `&4 * C2` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `fl = \x. if norm((f:real->complex) x) <= lam
                       then f x else Cx(&0)` THEN
  SUBGOAL_THEN `(\z. (fl:real->complex)(drop z)) measurable_on (:real^1)`
    ASSUME_TAC THENL
   [EXPAND_TAC "fl" THEN MP_TAC(ISPECL [`f:real->complex`;
      `\x. norm((f:real->complex) x) <= lam`] CASES_MEAS) THEN
    MP_TAC(SPEC `f:real->complex` NORM_RMEAS) THEN
    ASM_REWRITE_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LE] THEN
      SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm((fl:real->complex) x) <= norm((f:real->complex) x) /\
                    norm(fl x) <= lam` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "fl" THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (fl:real->complex)(drop z)) absolutely_integrable_on
                 (:real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC
     MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\z. lift(norm((f:real->complex)(drop z)))` THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (fl:real->complex)(drop z)) IN lspace (:real^1) (&2)`
    ASSUME_TAC THENL
   [ASM_MESON_TAC[L1_BOUNDED_IMP_L2]; ALL_TAC] THEN
  MP_TAC(ISPEC `fl:real->complex` FOURIER_L1L2_IN_L2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "w2" (MP_TAC o SPECL [`fourier (fl:real->complex)`;
    `n:real`; `lam / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  (* the L^2 mass of the low part                                            *)
  SUBGOAL_THEN `(\x. norm((fl:real->complex) x) pow 2) real_integrable_on
                 (:real)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `(\z. (fl:real->complex)(drop z)) IN lspace (:real^1) (&2)` THEN
    ASM_REWRITE_TAC[lspace; IN_ELIM_THM; RPOW_POW; REAL_INTEGRABLE_ON;
      IMAGE_LIFT_UNIV; o_DEF]; ALL_TAC] THEN
  SUBGOAL_THEN `lnorm (:real^1) (&2) (\z. (fl:real->complex)(drop z)) pow 2 =
                real_integral (:real) (\x. norm((fl:real->complex) x) pow 2)`
    ASSUME_TAC THENL
   [MP_TAC(ISPEC `\z. (fl:real->complex)(drop z)` LNORM2_SQ) THEN
     ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP REAL_INTEGRAL) THEN
    REWRITE_TAC[IMAGE_LIFT_UNIV; o_DEF] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `real_integral (:real) (\x. norm((fl:real->complex) x) pow 2) <=
                lam rpow (&2 - p) *
                  real_integral (:real) (\x. norm((f:real->complex) x) rpow p)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `real_integral (:real)
                  (\x. lam rpow (&2 - p) *
                       norm((f:real->complex) x) rpow p)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRAL_LE THEN
       ASM_SIMP_TAC[REAL_INTEGRABLE_LMUL; IN_UNIV] THEN
      X_GEN_TAC `x:real` THEN EXPAND_TAC "fl" THEN
        COND_CASES_TAC THENL
       [ASM_SIMP_TAC[LOW_SQ_LE; NORM_POS_LE];
        REWRITE_TAC[COMPLEX_NORM_0] THEN
          CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN
          ASM_SIMP_TAC[RPOW_POS_LE; NORM_POS_LE; REAL_LT_IMP_LE]];
      ASM_SIMP_TAC[REAL_EQ_IMP_LE; REAL_INTEGRAL_LMUL]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C2 * lnorm (:real^1) (&2)
                         (\z. fourier (fl:real->complex) (drop z)) pow 2 /
                   (lam / &2) pow 2` THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LOW_ARITH THEN EXISTS_TAC `lam rpow (&2 - p)` THEN
  ASM_SIMP_TAC[RPOW_POS_LT; GSYM RPOW_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(&2 - p) + p = &2`; RPOW_POW]);;

(* scaled restricted bound: |g| <= A 1_F                                     *)
let T_DOM_RWT_SCALED = prove
 (`!q0. &1 < q0 /\ q0 <= &2
        ==> ?D. &0 <= D /\
                !(g:real->complex) (Fs:real->bool) A n mu.
                  real_measurable Fs /\
                  (\z. g(drop z)) measurable_on (:real^1) /\
                  (!x. norm(g x) <= A * (if x IN Fs then &1 else &0)) /\
                  &0 < A /\ &0 <= n /\ &0 < mu
                  ==> real_measurable
                        {y | mu < carleson_Ahat_trunc (fourier g) n y} /\
                      real_measure
                        {y | mu < carleson_Ahat_trunc (fourier g) n y}
                      <= D * real_measure Fs * inv((mu / A) rpow q0)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `q0:real` T_DOM_RWT_Q0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rw"))) THEN
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w2"))
    T_DOM_LEVEL_WEAK22 THEN
  EXISTS_TAC `D:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `u = \x. Cx(inv A) * (g:real->complex) x` THEN
  SUBGOAL_THEN `(\z. (u:real->complex)(drop z)) measurable_on (:real^1)`
    ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC MEASURABLE_ON_COMPLEX_MUL THEN
    ASM_REWRITE_TAC[MEASURABLE_ON_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm((u:real->complex) x) <= (if x IN Fs then &1 else &0)`
    ASSUME_TAC THENL
   [X_GEN_TAC `x:real` THEN EXPAND_TAC "u" THEN
     REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `A:real`)) (concl th))) THEN
    ASM_SIMP_TAC[REAL_ABS_INV;
      REAL_ARITH `&0 < A ==> abs A = A`] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. Cx A * (u:real->complex) x) = g` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
     REWRITE_TAC[FUN_EQ_THM; COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; COMPLEX_MUL_LID]; ALL_TAC] THEN
  MP_TAC(SPECL [`u:real->complex`; `Fs:real->bool`] DOM_L1L2) THEN
    STRIP_TAC THEN
  SUBGOAL_THEN `(\z. (g:real->complex)(drop z)) absolutely_integrable_on
                 (:real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC
     MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `\z:real^1. lift(A * (if drop z IN Fs then &1 else &0))` THEN
      ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC INTEGRABLE_CMUL THEN
      SUBGOAL_THEN `(\z:real^1. lift(if drop z IN Fs then &1 else &0)) =
                    lift o (\t. if t IN Fs then &1 else &0) o drop`
        SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      REWRITE_TAC[GSYM IMAGE_LIFT_UNIV; GSYM REAL_INTEGRABLE_ON] THEN
      ASM_SIMP_TAC[CH_INDICATOR_REAL_INTEGRABLE];
      ASM_REWRITE_TAC[LIFT_DROP]]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. carleson_Ahat_trunc (fourier g) n y <=
                    A * carleson_Ahat_trunc (fourier u) n y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real` THEN
    MP_TAC(SPECL [`u:real->complex`; `Cx A`; `n:real`; `y:real`]
      T_CMUL_LE) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < A ==> abs A = A`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu / A` ASSUME_TAC THENL
    [ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  USE_THEN "w2" (MP_TAC o SPECL [`u:real->complex`; `Fs:real->bool`;
    `n:real`; `mu / A`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{y | mu < carleson_Ahat_trunc (fourier g) n y} SUBSET
                {y | mu / A < carleson_Ahat_trunc (fourier u) n y}`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
     ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun tm -> tm = `A:real`)) (concl th) &&
      can (find_term (fun tm -> is_const tm &&
                                fst(dest_const tm) = "carleson_Ahat_trunc"))
          (concl th))) THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measurable {y | mu < carleson_Ahat_trunc (fourier g) n y}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_LEBESGUE_SUBSET THEN
    EXISTS_TAC `{y | mu / A < carleson_Ahat_trunc (fourier u) n y}` THEN
      ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC T_LEVEL_LMEAS; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_measure {y | mu / A < carleson_Ahat_trunc (fourier u) n y}`
    THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURE_SUBSET];
    ASM_SIMP_TAC[]]);;

let POW_RPOW_COMM = prove
 (`!x q j. &0 < x ==> (x pow j) rpow q = (x rpow q) pow j`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RPOW_POW] THEN
  ASM_SIMP_TAC[RPOW_RPOW; REAL_LT_IMP_LE] THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC);;

(* the geometric weights of the level decomposition                          *)
let GEOM_WEIGHTS = prove
 (`!p q0. &1 < q0 /\ q0 < p
     ==> ?s kap. &0 < s /\ &0 < kap /\
                 (!J. sum(0..J) (\j. &2 pow (j + 1) * kap * s pow j)
                      <= &1 / &2) /\
                 (!j. inv((kap * s pow j) rpow q0) =
                      inv(kap rpow q0) * (&2 pow j) rpow p)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = &2 rpow (--(p / q0))` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC RPOW_POS_LT THEN
     REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * s < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `s < &2 rpow (--(&1))` MP_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC RPOW_MONO_LT THEN
      REWRITE_TAC[REAL_LT_NEG2] THEN
      SUBGOAL_THEN `&0 < q0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[RPOW_NEG; RPOW_POW] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `s:real` THEN EXISTS_TAC `(&1 - &2 * s) / &4` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    GEN_TAC THEN
    SUBGOAL_THEN `!j. &2 pow (j + 1) * ((&1 - &2 * s) / &4) * s pow j =
                      ((&1 - &2 * s) / &2) * (&2 * s) pow j`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[REAL_POW_ADD; REAL_POW_MUL] THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SUM_LMUL; SUM_GP] THEN
    SUBGOAL_THEN `~(&2 * s = &1)` (fun th -> REWRITE_TAC[th]) THENL
      [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LT; CONJUNCT1 real_pow] THEN
    ABBREV_TAC `t = (&2 * s) pow (SUC J)` THEN
    SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN MATCH_MP_TAC REAL_POW_LE THEN
       ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - &2 * s) / &2 * (&1 - t) / (&1 - &2 * s) =
                  (&1 - t) / &2` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&1 - &2 * s = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ASM_REAL_ARITH_TAC];
    ASM_SIMP_TAC[RPOW_MUL; POW_RPOW_COMM;
      REAL_ARITH `&0 < &2`] THEN
    SUBGOAL_THEN `s rpow q0 = inv(&2 rpow p)` SUBST1_TAC THENL
     [EXPAND_TAC "s" THEN SIMP_TAC[RPOW_RPOW; REAL_POS] THEN
      SUBGOAL_THEN `--(p / q0) * q0 = --p` SUBST1_TAC THENL
       [UNDISCH_TAC `&1 < q0` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      REWRITE_TAC[RPOW_NEG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_INV; REAL_INV_MUL; REAL_INV_INV]]);;

(* ------------------------------------------------------------------------- *)
(* Helpers for the interpolation.                                            *)
(* ------------------------------------------------------------------------- *)

let T_DECOMP_LE = prove
 (`!(f:real->complex) fl (g:num->real->complex) J n y.
     &0 <= n /\
     (\z. fl(drop z)) absolutely_integrable_on (:real^1) /\
     (!j. (\z. g j (drop z)) absolutely_integrable_on (:real^1)) /\
     (!x. f x = fl x + vsum(0..J) (\j. g j x))
     ==> carleson_Ahat_trunc (fourier f) n y
         <= carleson_Ahat_trunc (fourier fl) n y +
            sum(0..J) (\j. carleson_Ahat_trunc (fourier (g j)) n y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `f = (\x. (fl:real->complex) x +
                         (\x. vsum(0..J) (\j. (g:num->real->complex) j x)) x)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `carleson_Ahat_trunc (fourier fl) n y +
    carleson_Ahat_trunc
      (fourier (\x. vsum(0..J) (\j. (g:num->real->complex) j x))) n y` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[T_ADD_LE; ABSOLUTELY_INTEGRABLE_VSUM; FINITE_NUMSEG];
    ASM_SIMP_TAC[REAL_LE_LADD; T_VSUM_LE]]);;

let DECOMP_POINTWISE = prove
 (`!lam t (v:complex) J. &0 < lam /\ t <= &2 pow (J + 1) * lam
     ==> v = (if t <= lam then v else Cx(&0)) +
             vsum(0..J) (\j. if &2 pow j * lam < t /\ t <= &2 pow (j + 1) * lam
                             then v else Cx(&0))`,
  ASM_SIMP_TAC[LEVEL_VSUM] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  CONV_TAC COMPLEX_RING);;

let HIGH_SUM_BOUND = prove
 (`!D kap s q0 p lam (m:num->real) Mq J.
     &0 <= D /\ &0 < kap /\ &0 < lam /\ &0 < p /\ (!j. &0 <= m j) /\
     (!j. inv((kap * s pow j) rpow q0) =
          inv(kap rpow q0) * (&2 pow j) rpow p) /\
     sum(0..J) (\j. m j * (&2 pow j * lam) rpow p) <= Mq
     ==> sum(0..J) (\j. D * m j * inv((kap * s pow j) rpow q0))
         <= D * inv(kap rpow q0) * Mq / lam rpow p`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < lam rpow p` ASSUME_TAC THENL
    [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < kap rpow q0` ASSUME_TAC THENL
    [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. D * (m:num->real) j * inv(kap rpow q0) * (&2 pow j) rpow p =
        (D * inv(kap rpow q0) * inv(lam rpow p)) *
        (m j * (&2 pow j * lam) rpow p)`
    (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[RPOW_MUL] THEN
    SUBGOAL_THEN `~(lam rpow p = &0)` MP_TAC THENL
      [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]; ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_INV_EQ;
    REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Weak type (p,p) for the truncated operator, 1 < p < 2, for bounded f.     *)
(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)
(* Weak type (p,p) for the truncated operator, 1 < p < 2, for bounded f.     *)
(* ------------------------------------------------------------------------- *)

(* Cutting f off outside a Lebesgue measurable set {x | P x} preserves       *)
(* measurability and absolute integrability (domination by norm f).          *)
let CASES_MEAS_ABSINT = prove
 (`!(f:real->complex) P.
     (\z. f(drop z)) measurable_on (:real^1) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     real_lebesgue_measurable {x | P x}
     ==> (\z. if P(drop z) then f(drop z) else Cx(&0)) measurable_on
         (:real^1) /\
         (\z. if P(drop z) then f(drop z) else Cx(&0))
         absolutely_integrable_on (:real^1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[CASES_MEAS] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\z. lift(norm((f:real->complex)(drop z)))` THEN
  ASM_SIMP_TAC[CASES_MEAS; LIFT_DROP; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
    ABSOLUTELY_INTEGRABLE_NORM] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_LE_REFL; COMPLEX_NORM_0; NORM_POS_LE]);;

(* Proof: with |f| <= M <= 2^(J+1) lam, split f = fl + sum_{j<=J} gj into    *)
(* the part fl where |f| <= lam and the pieces gj of f on the level sets Fj  *)
(* = {2^j lam < |f| <= 2^(j+1) lam}; bound fl by LOW_PART_BOUND and each gj  *)
(* by T_DOM_RWT_SCALED at the geometric levels of GEOM_WEIGHTS, sum with     *)
(* LEVEL_CHEB, and combine by LEVEL_UNION_BOUND.                             *)
let T_WEAK_PP_BOUNDED = prove
 (`!p. &1 < p /\ p < &2
       ==> ?C. &0 <= C /\
               !(f:real->complex) M n lam.
                 (\z. f(drop z)) measurable_on (:real^1) /\
                 (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
                 (!x. norm(f x) <= M) /\
                 (\x. norm(f x) rpow p) real_integrable_on (:real) /\
                 &0 <= n /\ &0 < lam
                 ==> real_measurable
                       {y | lam < carleson_Ahat_trunc (fourier f) n y} /\
                     real_measure
                       {y | lam < carleson_Ahat_trunc (fourier f) n y}
                     <= C * real_integral (:real) (\x. norm(f x) rpow p) /
                            lam rpow p`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `q0 = (&1 + p) / &2` THEN
  SUBGOAL_THEN `&0 < p /\ &1 < q0 /\ q0 < p /\ q0 <= &2` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `q0:real`] GEOM_WEIGHTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real`
    (X_CHOOSE_THEN `kap:real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `q0:real` T_DOM_RWT_SCALED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rw"))) THEN
  X_CHOOSE_THEN `C2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lo"))
    LOW_PART_BOUND THEN
  X_CHOOSE_THEN `CW:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "w2"))
    AHAT_TRUNC_WEAK22 THEN
  EXISTS_TAC `C2 + D * inv(kap rpow q0)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; RPOW_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?J. M <= &2 pow (J + 1) * lam` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `M / (&2 * lam)` REAL_ARCH_POW2) THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < lam ==> &0 < &2 * lam`;
      GSYM ADD1; real_pow] THEN
    MESON_TAC[REAL_ARITH `M < a * &2 * lam ==> M <= (&2 * a) * lam`];
    ALL_TAC] THEN
  ABBREV_TAC
   `I0 = real_integral (:real) (\x. norm((f:real->complex) x) rpow p)` THEN
  ABBREV_TAC `fl = \x. if norm((f:real->complex) x) <= lam
                       then f x else Cx(&0)` THEN
  ABBREV_TAC `Fj = \j:num. {x | &2 pow j * lam < norm((f:real->complex) x) /\
                                norm(f x) <= &2 pow (j + 1) * lam}` THEN
  ABBREV_TAC `gj = \j:num x. if x IN (Fj:num->real->bool) j
                             then (f:real->complex) x else Cx(&0)` THEN
  (* the level sets and the pieces                                           *)
  SUBGOAL_THEN `!j. real_measurable ((Fj:num->real->bool) j)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Fj" THEN MATCH_MP_TAC SUPERLEVEL_RMEAS THEN
    EXISTS_TAC `p:real` THEN
    ASM_SIMP_TAC[NORM_POS_LE; NORM_RMEAS; REAL_LT_MUL; REAL_POW_LT;
      REAL_ARITH `&0 < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (fl:real->complex)(drop z)) absolutely_integrable_on
                  (:real^1) /\
                !j. (\z. (gj:num->real->complex) j (drop z)) measurable_on
                      (:real^1) /\
                    (\z. gj j (drop z)) absolutely_integrable_on (:real^1)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "fl" THEN EXPAND_TAC "gj" THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f:real->complex`;
        `\x. norm((f:real->complex) x) <= lam`] CASES_MEAS_ABSINT) THEN
      MP_TAC(SPEC `f:real->complex` NORM_RMEAS) THEN
      ASM_SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LE];
      GEN_TAC THEN MP_TAC(ISPECL [`f:real->complex`;
        `\x. x IN (Fj:num->real->bool) j`] CASES_MEAS_ABSINT) THEN
      ASM_SIMP_TAC[IN_GSPEC; REAL_MEASURABLE_IMP_REAL_LEBESGUE_MEASURABLE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j x. norm((gj:num->real->complex) j x) <=
                      (&2 pow (j + 1) * lam) *
                      (if x IN (Fj:num->real->bool) j then &1 else &0)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "gj" THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; COMPLEX_NORM_0;
      REAL_LE_REFL] THEN
    UNDISCH_TAC `x IN (Fj:num->real->bool) j` THEN EXPAND_TAC "Fj" THEN
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  (* measurability of the superlevel set, as f is in L^2                     *)
  SUBGOAL_THEN
   `real_measurable {y | lam < carleson_Ahat_trunc (fourier f) n y}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\z. (f:real->complex)(drop z)) IN lspace (:real^1) (&2)`
      ASSUME_TAC THENL
     [MATCH_MP_TAC L1_BOUNDED_IMP_L2 THEN EXISTS_TAC `M:real` THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `f:real->complex` FOURIER_L1L2_IN_L2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "w2" (MP_TAC o SPECL [`fourier (f:real->complex)`;
        `n:real`; `lam:real`]) THEN ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[]] THEN
  (* the low part                                                            *)
  USE_THEN "lo" (MP_TAC o SPECL [`f:real->complex`; `p:real`;
    `n:real`; `lam:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the level pieces                                                        *)
  SUBGOAL_THEN
   `!j. real_measurable {y | (&2 pow (j + 1) * kap * s pow j) * lam <
                             carleson_Ahat_trunc
                               (fourier ((gj:num->real->complex) j)) n y} /\
        real_measure {y | (&2 pow (j + 1) * kap * s pow j) * lam <
                          carleson_Ahat_trunc (fourier (gj j)) n y}
        <= D * real_measure ((Fj:num->real->bool) j) *
          inv((kap * s pow j) rpow q0)`
   ASSUME_TAC THENL
   [GEN_TAC THEN
    USE_THEN "rw" (MP_TAC o SPECL [`(gj:num->real->complex) j`;
      `(Fj:num->real->bool) j`; `&2 pow (j + 1) * lam`; `n:real`;
      `(&2 pow (j + 1) * kap * s pow j) * lam`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&0 < &2`];
      ALL_TAC] THEN
    SIMP_TAC[ASSUME `&0 < lam`; REAL_POW_LT; REAL_ARITH `&0 < &2`; REAL_FIELD
      `&0 < a /\ &0 < lam ==> ((a * b) * lam) / (a * lam) = b`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..J) (\j. real_measure {y | (&2 pow (j + 1) * kap * s pow j) * lam <
                                     carleson_Ahat_trunc (fourier
                                       ((gj:num->real->complex) j)) n y})
    <= D * inv(kap rpow q0) * I0 / lam rpow p` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..J) (\j. D * real_measure ((Fj:num->real->bool) j) *
                               inv((kap * s pow j) rpow q0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN REWRITE_TAC[] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HIGH_SUM_BOUND THEN ASM_SIMP_TAC[REAL_MEASURE_POS_LE] THEN
    EXPAND_TAC "Fj" THEN EXPAND_TAC "I0" THEN
    MP_TAC(ISPECL [`\x. norm((f:real->complex) x)`; `lam:real`; `p:real`;
      `J:num`] LEVEL_CHEB) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[NORM_POS_LE; NORM_RMEAS]; ALL_TAC] THEN
  (* the decomposition and the union bound                                   *)
  MP_TAC(ISPECL [`\y. carleson_Ahat_trunc (fourier f) n y`;
                 `\y. carleson_Ahat_trunc (fourier fl) n y`;
                 `\j y. carleson_Ahat_trunc
                          (fourier ((gj:num->real->complex) j)) n y`;
                 `\j. &2 pow (j + 1) * kap * s pow j`; `lam:real`;
                 `J:num`] LEVEL_UNION_BOUND) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN MATCH_MP_TAC T_DECOMP_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN
    EXPAND_TAC "fl" THEN EXPAND_TAC "gj" THEN EXPAND_TAC "Fj" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC DECOMP_POINTWISE THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M:real` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC(REAL_ARITH `b <= C2 * I0 / l /\ c <= D * k * I0 / l
      ==> a <= b + c ==> a <= (C2 + D * k) * I0 / l`) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Weak type (p,p) for all f in L^1 cap L^p, by truncation and the L^1       *)
(* continuity of the truncated operator.                                     *)
(* ------------------------------------------------------------------------- *)

let T_L1_BOUND = prove
 (`!(f:real->complex) n y.
     &0 <= n /\ (\z. f(drop z)) absolutely_integrable_on (:real^1)
     ==> carleson_Ahat_trunc (fourier f) n y
         <= inv(sqrt(&2 * pi)) * (&2 * n) *
            (&1 / sqrt(&2 * pi) *
             drop(integral (:real^1) (\x. lift(norm(f(drop x))))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Kb = &1 / sqrt(&2 * pi) *
                   drop(integral (:real^1)
                          (\x. lift(norm((f:real->complex)(drop x)))))` THEN
  SUBGOAL_THEN `!w. norm(fourier (f:real->complex) w) <= Kb` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "Kb" THEN MATCH_MP_TAC FOURIER_BOUND THEN
    ASM_SIMP_TAC[MODINT] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(sqrt(&2 * pi)) *
              drop(integral
                    (IMAGE lift (real_interval[--n,n]))
                    (\x. lift(norm(fourier (f:real->complex) (drop x)))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARLESON_AHAT_TRUNC_FINITE;
     FOURIER_LOCAL_ABSINT]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC SQRT_POS_LE THEN
     MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `drop(integral (IMAGE lift (real_interval[--n,n]))
                            (\x:real^1. lift Kb))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_DROP_LE THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
       ABSOLUTELY_INTEGRABLE_NORM; FOURIER_LOCAL_ABSINT];
      REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; INTEGRABLE_CONST];
      ASM_REWRITE_TAC[LIFT_DROP]];
    REWRITE_TAC[IMAGE_LIFT_REAL_INTERVAL; INTEGRAL_CONST] THEN
    SUBGOAL_THEN `drop(lift(--n)) <= drop(lift n)` ASSUME_TAC THENL
     [REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CONTENT_1; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC]);;

let TAIL_POINT_BOUND = prove
 (`!t M p. &0 < M /\ M < t /\ &1 < p ==> t <= M rpow (&1 - p) * t rpow p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t = t rpow (&1 - p) * t rpow p` (fun th ->
    GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [ASM_SIMP_TAC[GSYM RPOW_ADD] THEN
     REWRITE_TAC[REAL_ARITH `(&1 - p) + p = &1`; RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[RPOW_POS_LE; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&1 - p = --(p - &1)` SUBST1_TAC THENL
    [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[RPOW_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[RPOW_POS_LT] THEN
    MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC);;

(* The part of f above a large height M is negligible for the truncated      *)
(* operator: above M, |f| <= M^(1-p) |f|^p (TAIL_POINT_BOUND), so the L^1    *)
(* mass of that part is at most M^(1-p) int |f|^p, and T_L1_BOUND applies.   *)
let T_TAIL_SMALL = prove
 (`!(f:real->complex) p n lam.
     &1 < p /\ (\z. f(drop z)) measurable_on (:real^1) /\
     (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
     (\x. norm(f x) rpow p) real_integrable_on (:real) /\ &0 <= n /\ &0 < lam
     ==> ?M. &0 < M /\
             (\z. if M < norm(f(drop z)) then f(drop z) else Cx(&0))
             absolutely_integrable_on (:real^1) /\
             !y. carleson_Ahat_trunc
                   (fourier (\x. if M < norm(f x) then f x else Cx(&0))) n y
                 < lam`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `I0 = real_integral (:real) (\x. norm((f:real->complex) x) rpow p)` THEN
  ABBREV_TAC `Kn = inv(sqrt(&2 * pi)) * (&2 * n) * &1 / sqrt(&2 * pi)` THEN
  SUBGOAL_THEN `&0 <= Kn /\ &0 <= I0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kn" THEN EXPAND_TAC "I0" THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_DIV; SQRT_POS_LE; REAL_LE_MUL;
        PI_POS_LE; REAL_POS];
      ASM_SIMP_TAC[REAL_INTEGRAL_POS; RPOW_POS_LE; NORM_POS_LE]];
    ALL_TAC] THEN
  (* a height M with Kn * M^(1-p) * I0 < lam                                 *)
  SUBGOAL_THEN `?M. &0 < M /\ Kn * M rpow (&1 - p) * I0 < lam`
    (X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC) THENL
   [MP_TAC(SPECL [`&2 rpow (&1 - p)`; `lam / (Kn * I0 + &1)`]
      REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_MUL; REAL_LT_RDIV_EQ;
      REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `&2` RPOW_0)] THEN
      MATCH_MP_TAC RPOW_MONO_LT THEN ASM_REAL_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `k:num`)] THEN
    EXISTS_TAC `&2 pow k` THEN
    ASM_SIMP_TAC[REAL_POW_LT; POW_RPOW_COMM; REAL_ARITH `&0 < &2`] THEN
    SUBGOAL_THEN `&0 <= (&2 rpow (&1 - p)) pow k /\ &0 <= Kn * I0` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_LE; RPOW_POS_LE; REAL_POS; REAL_LE_MUL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `M:real` THEN
  MP_TAC(ISPECL [`f:real->complex`; `\x. M < norm((f:real->complex) x)`]
    CASES_MEAS_ABSINT) THEN
  MP_TAC(SPEC `f:real->complex` NORM_RMEAS) THEN
  ASM_SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT; real_gt] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `Kn * M rpow (&1 - p) * I0` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x. if M < norm((f:real->complex) x) then f x else Cx(&0)`;
    `n:real`; `y:real`] T_L1_BOUND) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
    `(b * c * d) * L <= x ==> a <= b * c * (d * L) ==> a <= x`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  (* the L^1 mass of the tail                                                *)
  SUBGOAL_THEN `M rpow (&1 - p) * I0 =
                drop(integral (:real^1)
                       (\x. lift(M rpow (&1 - p) *
                                 norm((f:real->complex)(drop x)) rpow p)))`
    SUBST1_TAC THENL
   [EXPAND_TAC "I0" THEN
    ASM_SIMP_TAC[GSYM REAL_INTEGRAL_LMUL; REAL_INTEGRAL; REAL_INTEGRABLE_LMUL;
      IMAGE_LIFT_UNIV; o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC INTEGRAL_DROP_LE_MEASURABLE THEN
  ASM_SIMP_TAC[MEASURABLE_ON_NORM; LIFT_DROP; IN_UNIV] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\x. norm((f:real->complex) x) rpow p`; `M rpow (&1 - p)`;
      `(:real)`] REAL_INTEGRABLE_LMUL) THEN
    ASM_REWRITE_TAC[REAL_INTEGRABLE_ON; IMAGE_LIFT_UNIV; o_DEF];
    GEN_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[NORM_POS_LE; COMPLEX_NORM_0; TAIL_POINT_BOUND; REAL_LE_MUL;
      RPOW_POS_LE; REAL_LT_IMP_LE]]);;

(* Weak type (p,p) for f in L^1 cap L^p: split f into the bounded part hM    *)
(* where |f| <= M and the part above M, which contributes less than lam/2 by *)
(* T_TAIL_SMALL; then T_WEAK_PP_BOUNDED at level lam/2 applies to hM.        *)
let T_WEAK_PP_L1 = prove
 (`!p. &1 < p /\ p < &2
       ==> ?C. &0 <= C /\
               !(f:real->complex) n lam.
                 (\z. f(drop z)) measurable_on (:real^1) /\
                 (\z. f(drop z)) absolutely_integrable_on (:real^1) /\
                 (\x. norm(f x) rpow p) real_integrable_on (:real) /\
                 &0 <= n /\ &0 < lam
                 ==> real_measurable
                       {y | lam < carleson_Ahat_trunc (fourier f) n y} /\
                     real_measure
                       {y | lam < carleson_Ahat_trunc (fourier f) n y}
                     <= C * real_integral (:real) (\x. norm(f x) rpow p) /
                            lam rpow p`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:real` T_WEAK_PP_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd"))) THEN
  EXISTS_TAC `C0 * &2 rpow p` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_MUL; RPOW_POS_LE; REAL_POS]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* a height M above which f contributes less than lam / 2                  *)
  MP_TAC(SPECL [`f:real->complex`; `p:real`; `n:real`; `lam / &2`]
    T_TAIL_SMALL) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tail")))) THEN
  ABBREV_TAC `hM = \x. if norm((f:real->complex) x) <= M
                       then f x else Cx(&0)` THEN
  (* the bounded part hM                                                     *)
  SUBGOAL_THEN `(\z. (hM:real->complex)(drop z)) measurable_on (:real^1) /\
                (\z. hM(drop z)) absolutely_integrable_on (:real^1)`
    STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "hM" THEN
    MP_TAC(ISPECL [`f:real->complex`;
      `\x. norm((f:real->complex) x) <= M`] CASES_MEAS_ABSINT) THEN
    MP_TAC(SPEC `f:real->complex` NORM_RMEAS) THEN
    ASM_SIMP_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. norm((hM:real->complex) x) <= norm((f:real->complex) x) /\
                    norm(hM x) <= M`
    ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "hM" THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; COMPLEX_NORM_0; NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. &0 <= norm((hM:real->complex) x) rpow p /\
                    norm(hM x) rpow p <= norm((f:real->complex) x) rpow p`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LE; RPOW_LE2; NORM_POS_LE;
      REAL_ARITH `&1 < p ==> &0 <= p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x. norm((hM:real->complex) x) rpow p) real_integrable_on
                  (:real)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x. norm((f:real->complex) x) rpow p` THEN
    ASM_SIMP_TAC[real_abs; REAL_MEASURABLE_ON_RPOW; NORM_RMEAS;
      REAL_ARITH `&1 < p ==> &0 < p`];
    ALL_TAC] THEN
  USE_THEN "bd" (MP_TAC o SPECL [`hM:real->complex`; `M:real`;
    `n:real`; `lam / &2`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_HALF]; STRIP_TAC] THEN
  (* the inclusion of superlevel sets: f is hM plus the part above M         *)
  SUBGOAL_THEN `{y | lam < carleson_Ahat_trunc (fourier f) n y} SUBSET
                {y | lam / &2 < carleson_Ahat_trunc (fourier hM) n y}`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
    MP_TAC(ISPECL [`hM:real->complex`;
      `\x. if M < norm((f:real->complex) x) then f x else Cx(&0)`;
      `n:real`; `y:real`] T_ADD_LE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(\x. (hM:real->complex) x +
                       (if M < norm((f:real->complex) x) then f x
                        else Cx(&0))) = f` SUBST1_TAC THENL
     [EXPAND_TAC "hM" THEN REWRITE_TAC[FUN_EQ_THM; GSYM REAL_NOT_LE] THEN
      GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[COMPLEX_ADD_LID; COMPLEX_ADD_RID];
      USE_THEN "tail" (MP_TAC o SPEC `y:real`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_measurable {y | lam < carleson_Ahat_trunc (fourier f) n y}`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_MEASURABLE_LEBESGUE_SUBSET; T_LEVEL_LMEAS];
     ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_measure
                {y | lam / &2 < carleson_Ahat_trunc (fourier hM) n y}` THEN
  ASM_SIMP_TAC[REAL_MEASURE_SUBSET] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `C0 * real_integral (:real)
                                 (\x. norm((hM:real->complex) x) rpow p) /
                   (lam / &2) rpow p` THEN
  ASM_REWRITE_TAC[RPOW_DIV] THEN
  SUBGOAL_THEN `&0 < lam rpow p /\ &0 < &2 rpow p` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RPOW_POS_LT; REAL_ARITH `&0 < &2`]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD
    `&0 < a /\ &0 < b ==> c * x / (a / b) = (c * b) * x / a`] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LE_DIV2_EQ; REAL_LE_MUL; REAL_LT_IMP_LE;
    REAL_INTEGRAL_LE; IN_UNIV]);;

(* ========================================================================= *)
(* The sine-kernel integrals are windows of the truncated operator:          *)
(*   inv(pi) int_[-pi,pi] sin(a(x-t))/(x-t) f t dt                           *)
(*      = (1/sqrt 2pi) int_[-a,a] e^{ix xi} fhat1(xi) dxi,                   *)
(* where f1 is the extension of f by zero; hence |S_a f(x)| <= T_n f1 (-x)   *)
(* for 0 < a <= n.                                                           *)
(* ========================================================================= *)

let F1_ABSINT = prove
 (`!(f:real->real). f absolutely_real_integrable_on real_interval[--pi,pi]
     ==> (\z:real^1. if drop z IN real_interval[--pi,pi] then Cx(f(drop z))
                     else Cx(&0))
         absolutely_integrable_on (:real^1)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  SUBGOAL_THEN
   `(\z:real^1. if drop z IN real_interval[--pi,pi] then Cx(f(drop z))
                else vec 0) =
    (\z. if z IN IMAGE lift (real_interval[--pi,pi])
         then (\w. Cx(f(drop w))) z else vec 0)`
   SUBST1_TAC THENL
   [REWRITE_TAC[IN_IMAGE_LIFT_DROP]; ALL_TAC] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  UNDISCH_TAC `(f:real->real) absolutely_real_integrable_on
                real_interval[--pi,pi]` THEN
  REWRITE_TAC[ABSOLUTELY_REAL_INTEGRABLE_ON] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(\w:real^1. Cx(f(drop w))) =
                (\v:real^1. Cx(drop v)) o (lift o f o drop)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_LINEAR THEN
    ASM_REWRITE_TAC[CXDROP_LINEAR]);;

let F1_SINC_INTEGRABLE = prove
 (`!(f:real->real) a x.
     &0 < a /\ f absolutely_real_integrable_on real_interval[--pi,pi]
     ==> (\z. (if drop z IN real_interval[--pi,pi] then Cx(f(drop z))
               else Cx(&0)) *
              Cx(sin(a * (x - drop z)) / (x - drop z)))
                integrable_on (:real^1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z:real^1. (if drop z IN real_interval[--pi,pi] then Cx(f(drop z))
                 else Cx(&0)) *
                Cx(sin(a * (x - drop z)) / (x - drop z))) =
    (\z. if z IN IMAGE lift (real_interval[--pi,pi])
         then (\w. Cx(f(drop w) * (sin(a * (x - drop w)) / (x - drop w)))) z
         else vec 0)`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
     REWRITE_TAC[IN_IMAGE_LIFT_DROP] THEN
    COND_CASES_TAC THEN
      REWRITE_TAC[GSYM CX_MUL; COMPLEX_VEC_0; COMPLEX_MUL_LZERO]; ALL_TAC] THEN
  REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV] THEN
  MP_TAC(ISPECL [`\t. (f:real->real) t * sin(a * (x - t)) / (x - t)`;
    `real_interval[--pi,pi]`]
    INTEGRABLE_CX_DROP_COMPOSE) THEN
  ASM_SIMP_TAC[SINC_KERNEL_TIMES_F_INTEGRABLE]);;

let F1_HAX_INTEGRAL = prove
 (`!(f:real->real) a x.
     &0 < a /\ f absolutely_real_integrable_on real_interval[--pi,pi]
     ==> integral (:real^1)
           (\z. (if drop z IN real_interval[--pi,pi] then Cx(f(drop z))
                 else Cx(&0)) *
                fourier (\y. if abs y <= a then cexp(ii * Cx x * Cx y)
                             else Cx(&0)) (drop z)) =
         Cx(inv(sqrt(&2 * pi))) * Cx(&2) *
         Cx(real_integral (real_interval[--pi,pi])
                          (\t. f t * sin(a * (x - t)) / (x - t)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `integral (:real^1)
     (\z. Cx(inv(sqrt(&2 * pi))) * Cx(&2) *
          ((if drop z IN real_interval[--pi,pi] then
            Cx(f(drop z)) else Cx(&0)) *
           Cx(sin(a * (x - drop z)) / (x - drop z))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_SPIKE THEN EXISTS_TAC `{lift x}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING; IN_DIFF; IN_SING] THEN
    X_GEN_TAC `z:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x - drop z = &0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_SUB_0; LIFT_DROP]; ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `x:real`; `drop z`] CARLESON_HAX_FT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\z. (if drop z IN real_interval[--pi,pi] then Cx(f(drop z))
                      else Cx(&0)) *
                     Cx(sin(a * (x - drop z)) / (x - drop z))) integrable_on
                       (:real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC F1_SINC_INTEGRABLE; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRAL_COMPLEX_LMUL; INTEGRABLE_COMPLEX_LMUL;
    SINC_F1_INTEGRAL_COLLAPSE; SINC_KERNEL_TIMES_F_INTEGRABLE]);;

let SINE_WINDOW_IDENTITY = prove
 (`!(f:real->real) a x.
     &0 < a /\ f absolutely_real_integrable_on real_interval[--pi,pi]
     ==> integral (IMAGE lift (real_interval[--a,a]))
           (\z. cexp(--(ii * Cx(--x) * Cx(drop z))) *
                fourier (\t. if t IN real_interval[--pi,pi] then Cx(f t)
                             else Cx(&0)) (drop z)) =
         Cx(inv(sqrt(&2 * pi))) * Cx(&2) *
         Cx(real_integral (real_interval[--pi,pi])
                          (\t. f t * sin(a * (x - t)) / (x - t)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f1 = \t. if t IN real_interval[--pi,pi]
                       then Cx((f:real->real) t) else Cx(&0)` THEN
  SUBGOAL_THEN
   `integral (IMAGE lift (real_interval[--a,a]))
      (\z. cexp(--(ii * Cx(--x) * Cx(drop z))) *
           fourier (f1:real->complex) (drop z)) =
    integral (:real^1)
      (\z. fourier f1 (drop z) *
           (\y. if abs y <= a then cexp(ii * Cx x * Cx y)
                else Cx(&0)) (drop z))`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\z. cexp(--(ii * Cx(--x) * Cx(drop z))) *
                        fourier (f1:real->complex) (drop z)`;
                   `IMAGE lift (real_interval[--a,a])`]
                     INTEGRAL_RESTRICT_UNIV) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:real^1` THEN
    REWRITE_TAC[IN_IMAGE_LIFT_DROP; IN_REAL_INTERVAL;
      REAL_ARITH `--a <= t /\ t <= a <=> abs t <= a`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
    SUBGOAL_THEN `--(ii * Cx(--x) * Cx(drop z)) = ii * Cx x * Cx(drop z)`
      SUBST1_TAC THENL
     [REWRITE_TAC[]; ALL_TAC] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f1:real->complex`;
    `\y. if abs y <= a then cexp(ii * Cx x * Cx y) else Cx(&0)`]
    FOURIER_283O) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "f1" THEN MATCH_MP_TAC F1_ABSINT THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[HAX_ABSINT]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  EXPAND_TAC "f1" THEN MATCH_MP_TAC F1_HAX_INTEGRAL THEN ASM_REWRITE_TAC[]);;

let INV_SQRT2PI_SQ = prove
 (`inv(sqrt(&2 * pi)) * inv(sqrt(&2 * pi)) * &2 = inv pi`,
  SUBGOAL_THEN `sqrt(&2 * pi) * sqrt(&2 * pi) = &2 * pi` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_2] THEN MATCH_MP_TAC SQRT_POW_2 THEN
     MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC PI_POS THEN
  UNDISCH_TAC `sqrt(&2 * pi) * sqrt(&2 * pi) = &2 * pi` THEN
  CONV_TAC REAL_FIELD);;

(* |S_a f(x)| <= T_n f1 (-x)                                                 *)
let SINC_LE_T = prove
 (`!(f:real->real) a n x.
     &0 < a /\ a <= n /\ f absolutely_real_integrable_on real_interval[--pi,pi]
     ==> abs(inv(pi) * real_integral (real_interval[--pi,pi])
                                     (\t. sin(a * (x - t)) / (x - t) * f t))
         <= carleson_Ahat_trunc
              (fourier (\t. if t IN real_interval[--pi,pi] then Cx(f t)
                            else Cx(&0))) n (--x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(sqrt(&2 * pi)) *
              norm(integral (IMAGE lift (real_interval[--a,a]))
                (\z. cexp(--(ii * Cx(--x) * Cx(drop z))) *
                     fourier (\t. if t IN real_interval[--pi,pi] then Cx(f t)
                                  else Cx(&0)) (drop z)))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SINE_WINDOW_IDENTITY] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    SUBGOAL_THEN `real_integral (real_interval[--pi,pi])
                    (\t. sin(a * (x - t)) / (x - t) * f t) =
                  real_integral (real_interval[--pi,pi])
                    (\t. f t * sin(a * (x - t)) / (x - t))`
      SUBST1_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
       REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(inv(sqrt(&2 * pi))) = inv(sqrt(&2 * pi))`
      SUBST1_TAC THENL
     [REWRITE_TAC[REAL_ABS_REFL; REAL_LE_INV_EQ] THEN
       MATCH_MP_TAC SQRT_POS_LE THEN
      MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    SUBGOAL_THEN `abs(inv pi) = inv(sqrt(&2 * pi)) * inv(sqrt(&2 * pi)) * &2`
      SUBST1_TAC THENL
     [REWRITE_TAC[INV_SQRT2PI_SQ; REAL_ABS_REFL; REAL_LE_INV_EQ] THEN
      MP_TAC PI_POS; ALL_TAC] THEN
    REAL_ARITH_TAC;
    MATCH_MP_TAC CARLESON_TRUNC_WINDOW_LE_SUP THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[FOURIER_LOCAL_ABSINT; F1_ABSINT]]]);;

(* ------------------------------------------------------------------------- *)
(* L^p on [-pi,pi]: clamped truncations, tails, extensions by zero, and the  *)
(* exceptional-set bound for the sine-kernel maximal function.               *)
(* ------------------------------------------------------------------------- *)

let RPOW_ONE_EXP = prove
 (`!x. x rpow &1 = x`,
  REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let LP_IMP_ABSINT = prove
 (`!(f:real->real) p.
     &1 <= p /\ f real_measurable_on real_interval[--pi,pi] /\
     (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi]
     ==> f absolutely_real_integrable_on real_interval[--pi,pi]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC
    REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x. &1 + abs((f:real->real) x) rpow p` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRABLE_ADD; REAL_INTEGRABLE_CONST];
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      ASM_CASES_TAC `abs((f:real->real) x) <= &1` THENL
     [MP_TAC(SPECL [`abs((f:real->real) x)`; `p:real`] RPOW_POS_LE) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= &1 + y`) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM RPOW_ONE_EXP] THEN
        MATCH_MP_TAC RPOW_MONO_LE THEN
      ASM_REAL_ARITH_TAC]]);;

let RMEAS_CONST_INTERVAL = prove
 (`!c a b. (\x:real. c) real_measurable_on real_interval[a,b]`,
  ASM_MESON_TAC[REAL_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET; SUBSET_UNIV;
    REAL_MEASURABLE_ON_CONST; REAL_LEBESGUE_MEASURABLE_INTERVAL]);;

let CLAMP_PROPS = prove
 (`!(f:real->real) p k.
     &1 <= p /\ f real_measurable_on real_interval[--pi,pi] /\
     (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi]
     ==> (\x. max (--(&k)) (min (&k) (f x))) square_integrable_on
           real_interval[--pi,pi] /\
         (\x. max (--(&k)) (min (&k) (f x))) absolutely_real_integrable_on
           real_interval[--pi,pi] /\
         (\x. f x - max (--(&k)) (min (&k) (f x))) real_measurable_on
           real_interval[--pi,pi] /\
         (\x. f x - max (--(&k)) (min (&k) (f x)))
           absolutely_real_integrable_on real_interval[--pi,pi] /\
         (\x. abs(f x - max (--(&k)) (min (&k) (f x))) rpow p)
           real_integrable_on real_interval[--pi,pi]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(\x. max (--(&k)) (min (&k) ((f:real->real) x)))
                 real_measurable_on real_interval[--pi,pi]`
    ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_ON_MAX; RMEAS_CONST_INTERVAL;
     REAL_MEASURABLE_ON_MIN]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. abs(max (--(&k)) (min (&k) ((f:real->real) x))) <= &k /\
                    abs(f x - max (--(&k)) (min (&k) (f x))) <=
                      abs(f x)` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real->real) absolutely_real_integrable_on
                 real_interval[--pi,pi]` ASSUME_TAC THENL
   [ASM_MESON_TAC[LP_IMP_ABSINT]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. max (--(&k)) (min (&k) ((f:real->real) x)))
                 absolutely_real_integrable_on
                real_interval[--pi,pi]` ASSUME_TAC THENL
   [ASM_MESON_TAC
      [REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE;
       REAL_INTEGRABLE_CONST]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. (f:real->real) x - max (--(&k)) (min (&k) (f x)))
                real_measurable_on real_interval[--pi,pi]` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MEASURABLE_ON_SUB; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[square_integrable_on] THEN
    MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x:real. &k pow 2` THEN
      REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_2; REAL_MEASURABLE_ON_MUL];
      ASM_SIMP_TAC[REAL_ABS_POW; REAL_POW_LE2; REAL_ABS_POS]];
    ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB];
    MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x. abs((f:real->real) x) rpow p` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_MEASURABLE_ON_RPOW THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_MEASURABLE_ON_ABS]; ASM_REAL_ARITH_TAC];
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `abs(abs((f:real->real) x - max (--(&k)) (min (&k) (f x))) rpow p) =
        abs(f x - max (--(&k)) (min (&k) (f x))) rpow p` SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_ABS_REFL; RPOW_POS_LE; REAL_ABS_POS];
        ALL_TAC] THEN
      MATCH_MP_TAC RPOW_LE2 THEN
        ASM_REAL_ARITH_TAC]]);;

let TAIL_LP_TO_ZERO = prove
 (`!(f:real->real) p.
     &1 <= p /\ f real_measurable_on real_interval[--pi,pi] /\
     (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi]
     ==> ((\k. real_integral (real_interval[--pi,pi])
                 (\x. abs(f x - max (--(&k)) (min (&k) (f x))) rpow p))
          ---> &0) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k:num x. abs((f:real->real) x -
                                max (--(&k)) (min (&k) (f x))) rpow p`;
                 `\x:real. &0`; `\x. abs((f:real->real) x) rpow p`;
                 `real_interval[--pi,pi]`]
    REAL_DOMINATED_CONVERGENCE) THEN
  REWRITE_TAC[REAL_INTEGRAL_0] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CLAMP_PROPS];
    MAP_EVERY X_GEN_TAC [`k:num`; `x:real`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `abs(abs((f:real->real) x - max (--(&k)) (min (&k) (f x))) rpow p) =
      abs(f x - max (--(&k)) (min (&k) (f x))) rpow p` SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_REFL; RPOW_POS_LE; REAL_ABS_POS];
      ALL_TAC] THEN
    MATCH_MP_TAC RPOW_LE2 THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN MATCH_MP_TAC REALLIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    MP_TAC(SPEC `abs((f:real->real) x)` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `N:num` THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real->real) x - max (--(&k)) (min (&k) (f x)) = &0`
      SUBST1_TAC THENL
     [SUBGOAL_THEN `&N <= &k` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; RPOW_ZERO] THEN
    ASM_REAL_ARITH_TAC]);;

let ZERO_EXT_PROPS = prove
 (`!(h:real->real) p.
     &0 < p /\ h absolutely_real_integrable_on real_interval[--pi,pi] /\
     (\x. abs(h x) rpow p) real_integrable_on real_interval[--pi,pi]
     ==> (\z. (\t. if t IN real_interval[--pi,pi] then Cx(h t)
                   else Cx(&0)) (drop z))
           measurable_on (:real^1) /\
         (\z. (\t. if t IN real_interval[--pi,pi] then Cx(h t)
                   else Cx(&0)) (drop z))
           absolutely_integrable_on (:real^1) /\
         (\x. norm((\t. if t IN real_interval[--pi,pi] then Cx(h t)
                        else Cx(&0)) x) rpow p)
           real_integrable_on (:real) /\
         real_integral (:real)
           (\x. norm((\t. if t IN real_interval[--pi,pi] then Cx(h t)
                          else Cx(&0)) x) rpow p) =
         real_integral (real_interval[--pi,pi]) (\x. abs(h x) rpow p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\z:real^1. if drop z IN real_interval[--pi,pi]
                            then Cx(h(drop z)) else Cx(&0))
                absolutely_integrable_on (:real^1)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[F1_ABSINT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE]; ALL_TAC] THEN
  SUBGOAL_THEN `(\x. norm(if x IN real_interval[--pi,pi]
                          then Cx((h:real->real) x) else Cx(&0)) rpow p) =
                (\x. if x IN real_interval[--pi,pi] then abs(h x) rpow p
                     else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; RPOW_ZERO] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_INTEGRABLE_RESTRICT_UNIV;
    REAL_INTEGRAL_RESTRICT_UNIV]);;

let CHEB_RPOW = prove
 (`!(phi:real->real) t p.
     &0 < t /\ &0 < p /\ (!x. &0 <= phi x) /\ phi real_measurable_on (:real) /\
     (\x. phi x rpow p) real_integrable_on (:real)
     ==> real_measurable {x | t < phi x} /\
         real_measure {x | t < phi x}
         <= real_integral (:real) (\x. phi x rpow p) / t rpow p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t rpow p` ASSUME_TAC THENL
    [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `real_measurable {x | t < (phi:real->real) x}` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MEASURABLE_REAL_INTEGRABLE] THEN
    MATCH_MP_TAC REAL_MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x:real. inv(t rpow p) * phi x rpow p` THEN
      REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM real_lebesgue_measurable] THEN
      UNDISCH_TAC `(phi:real->real) real_measurable_on (:real)` THEN
      REWRITE_TAC[REAL_MEASURABLE_ON_PREIMAGE_HALFSPACE_GT;
        real_gt];
      MATCH_MP_TAC REAL_INTEGRABLE_LMUL;
      X_GEN_TAC `x:real` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_ELIM_THM] THEN COND_CASES_TAC THENL
       [REWRITE_TAC[REAL_ABS_NUM] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
         REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
          MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_ABS_NUM; REAL_LE_MUL; REAL_LE_INV_EQ;
          REAL_LT_IMP_LE; RPOW_POS_LE]]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MP_TAC(ISPECL [`\x. t < (phi:real->real) x`;
    `t rpow p`] INDICATOR_CONST_INTEGRAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN ASM_REWRITE_TAC[IN_UNIV] THEN
  X_GEN_TAC `x:real` THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC RPOW_LE2 THEN ASM_REAL_ARITH_TAC;
     ASM_SIMP_TAC[RPOW_POS_LE]]);;

(* ------------------------------------------------------------------------- *)
(* The exceptional set of the sine-kernel maximal function.                  *)
(* ------------------------------------------------------------------------- *)

let MAXIMAL_SET_BOUND = prove
 (`!p. &1 < p /\ p < &2
       ==> ?C. &0 <= C /\
               !(G:real->complex) mu.
                 (\z. G(drop z)) measurable_on (:real^1) /\
                 (\z. G(drop z)) absolutely_integrable_on (:real^1) /\
                 (\x. norm(G x) rpow p) real_integrable_on (:real) /\ &0 < mu
                 ==> real_measurable {x | ?n. mu < carleson_Ahat_trunc
                                                     (fourier G) (&n) (--x)} /\
                     real_measure {x | ?n. mu < carleson_Ahat_trunc
                                                  (fourier G) (&n) (--x)}
                     <= C * real_integral (:real) (\x. norm(G x) rpow p) /
                            mu rpow p`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:real` T_WEAK_PP_L1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wp"))) THEN
  EXISTS_TAC `C:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = C * real_integral (:real)
                                    (\x. norm((G:real->complex) x) rpow p) /
                      mu rpow p` THEN
  ABBREV_TAC `A = \n:num. {y | mu < carleson_Ahat_trunc
                                      (fourier (G:real->complex)) (&n) y}` THEN
  SUBGOAL_THEN `{x | ?n. mu < carleson_Ahat_trunc
                                (fourier (G:real->complex)) (&n) (--x)} =
                IMAGE (--) (UNIONS {(A:num->real->bool) n | n IN (:num)})`
    SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_UNIONS; IN_UNIV] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `--x:real` THEN
       REWRITE_TAC[REAL_NEG_NEG] THEN
      EXISTS_TAC `{y | mu < carleson_Ahat_trunc
                              (fourier (G:real->complex)) (&n) y}` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[IN_ELIM_THM]];
      DISCH_THEN(X_CHOOSE_THEN `y:real`
        (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_TAC `n:num`) MP_TAC)) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; REAL_NEG_NEG] THEN DISCH_TAC THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. real_measurable ((A:num->real->bool) n) /\
                    real_measure (A n) <= B` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_POS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->real->bool`;
    `B:real`] HAS_REAL_MEASURE_NESTED_UNIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN EXPAND_TAC "A" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `y:real` THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> mu < a ==> mu < b`) THEN
    MATCH_MP_TAC CARLESON_AHAT_TRUNC_MONO THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ARITH_TAC;
      ASM_SIMP_TAC[FOURIER_LOCAL_ABSINT]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REFLECT_RMEAS; REFLECT_RMEASURE] THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\n:num. real_measure ((A:num->real->bool) n)` THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY]);;

let ZERO_EXT_PROPS_EQ = prove
 (`!(h:real->real) p (H:real->complex).
     &0 < p /\ h absolutely_real_integrable_on real_interval[--pi,pi] /\
     (\x. abs(h x) rpow p) real_integrable_on real_interval[--pi,pi] /\
     (!t. H t = if t IN real_interval[--pi,pi] then Cx(h t) else Cx(&0))
     ==> (\z. H(drop z)) measurable_on (:real^1) /\
         (\z. H(drop z)) absolutely_integrable_on (:real^1) /\
         (\x. norm(H x) rpow p) real_integrable_on (:real) /\
         real_integral (:real) (\x. norm(H x) rpow p) =
         real_integral (real_interval[--pi,pi]) (\x. abs(h x) rpow p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `H = (\t. if t IN real_interval[--pi,pi]
                         then Cx((h:real->real) t) else Cx(&0))`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC ZERO_EXT_PROPS THEN ASM_REWRITE_TAC[]);;

let BAD_SET_BOUND = prove
 (`!p. &1 < p /\ p < &2
       ==> ?C. &0 <= C /\
               !(h:real->real) mu.
                 h absolutely_real_integrable_on real_interval[--pi,pi] /\
                 (\x. abs(h x) rpow p) real_integrable_on
                   real_interval[--pi,pi] /\ &0 < mu
                 ==> ?U. real_measurable U /\
                         real_measure U <= C *
                           real_integral (real_interval[--pi,pi])
                                         (\x. abs(h x) rpow p) / mu rpow p /\
                         !x. x IN real_interval[--pi,pi] /\ ~(x IN U)
                             ==> abs(h x) <= mu /\
                                 !a. &0 < a
                                     ==> abs(inv(pi) *
                                             real_integral
                                              (real_interval[--pi,pi])
                                              (\t. sin(a * (x - t)) /
                                                   (x - t) * h t)) <= mu`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:real` MAXIMAL_SET_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mx"))) THEN
  EXISTS_TAC `C + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `H = \t. if t IN real_interval[--pi,pi]
                      then Cx((h:real->real) t) else Cx(&0)` THEN
  MP_TAC(SPECL [`h:real->real`; `p:real`;
    `H:real->complex`] ZERO_EXT_PROPS_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "H" THEN REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  USE_THEN "mx" (MP_TAC o SPECL [`H:real->complex`; `mu:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. norm((H:real->complex) x)`; `mu:real`;
    `p:real`] CHEB_RPOW) THEN
  REWRITE_TAC[NORM_POS_LE] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[NORM_RMEAS] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{x | ?n. mu < carleson_Ahat_trunc
                              (fourier (H:real->complex)) (&n) (--x)} UNION
              {x | mu < norm((H:real->complex) x)}` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_MEASURABLE_UNION];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `real_measure {x | ?n. mu < carleson_Ahat_trunc
                                   (fourier (H:real->complex)) (&n) (--x)} +
      real_measure {x | mu < norm((H:real->complex) x)}` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[REAL_MEASURE_UNION_LE]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; real_div;
      REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN
      RULE_ASSUM_TAC(REWRITE_RULE[real_div]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM; IN_ELIM_THM;
    NOT_EXISTS_THM; REAL_NOT_LT] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[COMPLEX_NORM_CX]; ALL_TAC] THEN
  X_GEN_TAC `a:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `a:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `carleson_Ahat_trunc (fourier (H:real->complex)) (&N) (--x)` THEN
    ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "H" THEN MATCH_MP_TAC SINC_LE_T THEN ASM_REWRITE_TAC[]);;

let SA_SPLIT = prove
 (`!(f:real->real) g a x.
     &0 < a /\ f absolutely_real_integrable_on real_interval[--pi,pi] /\
     g absolutely_real_integrable_on real_interval[--pi,pi]
     ==> inv(pi) * real_integral (real_interval[--pi,pi])
                     (\t. sin(a * (x - t)) / (x - t) * f t) =
         inv(pi) * real_integral (real_interval[--pi,pi])
                     (\t. sin(a * (x - t)) / (x - t) * g t) +
         inv(pi) * real_integral (real_interval[--pi,pi])
                     (\t. sin(a * (x - t)) / (x - t) * (f t - g t))`,
  REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `!u:real->real.
                  u absolutely_real_integrable_on real_interval[--pi,pi]
                  ==> (\t. sin(a * (x - t)) / (x - t) * u t)
                      real_integrable_on real_interval[--pi,pi]`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`u:real->real`; `a:real`; `x:real`]
      SINC_KERNEL_TIMES_F_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(\t. (f:real->real) t - g t)
                 absolutely_real_integrable_on real_interval[--pi,pi]`
    ASSUME_TAC THENL
      [ASM_SIMP_TAC[ABSOLUTELY_REAL_INTEGRABLE_SUB]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\t. sin(a * (x - t)) / (x - t) * (g:real->real) t`;
                 `\t. sin(a * (x - t)) / (x - t) * ((f:real->real) t - g t)`;
                 `real_interval[--pi,pi]`] REAL_INTEGRAL_ADD) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Banach principle: for each m, the set of points where the sine-kernel *)
(* integrals do not eventually stay within 1/(m+1) of f is negligible.       *)
(* ------------------------------------------------------------------------- *)

let SMALL_TAIL_ARITH = prove
 (`!C ep e M. &0 <= C /\ &0 <= ep /\ &0 < M /\ &0 < e /\ ep < e * M / (C + &1)
              ==> C * ep / M < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `C * ep / M = (C * ep) / M` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 < C + &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ep * (C + &1) < e * M` ASSUME_TAC THENL
   [UNDISCH_TAC `ep < e * M / (C + &1)` THEN
    SUBGOAL_THEN `e * M / (C + &1) = (e * M) / (C + &1)` SUBST1_TAC THENL
     [REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BAD_M_NEGLIGIBLE = prove
 (`!p C (f:real->real) (gk:num->real->real)
    (hk:num->real->real) (sk:num->real->bool) m.
     &1 < p /\ p < &2 /\ &0 <= C /\
     (!h mu. h absolutely_real_integrable_on real_interval[--pi,pi] /\
             (\x. abs(h x) rpow p) real_integrable_on
               real_interval[--pi,pi] /\ &0 < mu
             ==> ?U. real_measurable U /\
                     real_measure U <= C *
                       real_integral (real_interval[--pi,pi])
                                     (\x. abs(h x) rpow p) / mu rpow p /\
                     !x. x IN real_interval[--pi,pi] /\ ~(x IN U)
                         ==> abs(h x) <= mu /\
                             !a. &0 < a
                                 ==> abs(inv(pi) *
                                   real_integral (real_interval[--pi,pi])
                                           (\t. sin(a * (x - t)) /
                                             (x - t) * h t)) <= mu) /\
     f absolutely_real_integrable_on real_interval[--pi,pi] /\
     (!k. gk k absolutely_real_integrable_on real_interval[--pi,pi] /\
          hk k absolutely_real_integrable_on real_interval[--pi,pi] /\
          (\x. abs(hk k x) rpow p) real_integrable_on real_interval[--pi,pi] /\
          (!x. f x - gk k x = hk k x)) /\
     ((\k. real_integral (real_interval[--pi,pi]) (\x. abs(hk k x) rpow p))
      ---> &0) sequentially /\
     (!k x. --pi < x /\ x < pi /\ ~(x IN sk k)
            ==> ((\a. inv(pi) * real_integral (real_interval[--pi,pi])
                        (\t. sin(a * (x - t)) / (x - t) * gk k t))
                          ---> gk k x) at_posinfinity)
     ==> real_negligible
           {x | --pi < x /\ x < pi /\ ~(x IN UNIONS {sk k | k IN (:num)}) /\
                !A. ?a. A <= a /\
                        inv(&m + &1) <= abs(inv(pi) *
                          real_integral (real_interval[--pi,pi])
                                              (\t. sin(a * (x - t))
                                                / (x - t) * f t) - f x)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "bs") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "dec")
    (CONJUNCTS_THEN2 (LABEL_TAC "tl") (LABEL_TAC "l2")))))))) THEN
  ABBREV_TAC `mu = inv(&m + &1) / &4` THEN
  SUBGOAL_THEN `&0 < inv(&m + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < mu rpow p` ASSUME_TAC THENL
    [ASM_SIMP_TAC[RPOW_POS_LT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_NEGLIGIBLE_OUTER] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN
  (* a truncation level k with small tail                                    *)
  SUBGOAL_THEN `?k. C * real_integral (real_interval[--pi,pi])
                          (\x. abs((hk:num->real->real) k x) rpow p) /
                        mu rpow p < e` STRIP_ASSUME_TAC THENL
   [USE_THEN "tl" (MP_TAC o REWRITE_RULE[REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `e * mu rpow p / (C + &1)`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
      REWRITE_TAC[LE_REFL] THEN
    DISCH_TAC THEN EXISTS_TAC `N:num` THEN
    MATCH_MP_TAC SMALL_TAIL_ARITH THEN
      SUBGOAL_THEN `&0 <= real_integral (real_interval[--pi,pi])
                            (\x. abs((hk:num->real->real) N x) rpow p)`
      ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_INTEGRAL_POS; RPOW_POS_LE; REAL_ABS_POS]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the exceptional set for the tail h_k                                    *)
  USE_THEN "dec" (MP_TAC o SPEC `k:num`) THEN STRIP_TAC THEN
  USE_THEN "bs" (MP_TAC o SPECL [`(hk:num->real->real) k`; `mu:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `U:real->bool` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[REAL_LET_TRANS]] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun tm -> tm = `U:real->bool`)) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sh")) THEN
  SUBGOAL_THEN `~((x:real) IN (sk:num->real->bool) k)` ASSUME_TAC THENL
   [UNDISCH_TAC
     `~((x:real) IN UNIONS {(sk:num->real->bool) k | k IN (:num)})` THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "l2" (MP_TAC o SPECL [`k:num`; `x:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
    DISCH_THEN(MP_TAC o SPEC `mu:real`) THEN
  ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` (LABEL_TAC "cv")) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `max b (&1)` o check (fun th ->
    is_forall(concl th) &&
    can (find_term (fun tm -> tm = `inv(&m + &1)`)) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THEN
  USE_THEN "cv" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
    [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  USE_THEN "sh" (MP_TAC o SPEC `a:real`) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`f:real->real`; `(gk:num->real->real) k`;
    `a:real`; `x:real`] SA_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real` o check (fun th ->
    is_forall(concl th) &&
    is_eq(snd(strip_forall(concl th))) &&
    can (find_term (fun tm -> tm = `(hk:num->real->real) k`)) (concl th))) THEN
  ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Almost-everywhere convergence of the sine-kernel integrals for f in L^p,  *)
(* 1 < p < 2, and the Carleson-Hunt theorem.                                 *)
(* ========================================================================= *)

let SINC_AE_LP = prove
 (`!(f:real->real) p.
     &1 < p /\ p < &2 /\
     f real_measurable_on real_interval[--pi,pi] /\
     (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi] /\
     (!x. f(x + &2 * pi) = f x)
     ==> ?s. real_negligible s /\
             !x. --pi < x /\ x < pi /\ ~(x IN s)
                 ==> ((\a. inv(pi) * real_integral (real_interval[--pi,pi])
                              (\t. sin(a * (x - t)) / (x - t) * f t))
                                ---> f x) at_posinfinity`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `p:real` BAD_SET_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bs"))) THEN
  SUBGOAL_THEN `(f:real->real) absolutely_real_integrable_on
                 real_interval[--pi,pi]` ASSUME_TAC THENL
   [ASM_MESON_TAC[LP_IMP_ABSINT; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ABBREV_TAC `gk = \k:num x. max (--(&k)) (min (&k) ((f:real->real) x))` THEN
  ABBREV_TAC
   `hk = \k:num x. (f:real->real) x - max (--(&k)) (min (&k) (f x))` THEN
  SUBGOAL_THEN
   `!k. (gk:num->real->real) k square_integrable_on real_interval[--pi,pi] /\
        gk k absolutely_real_integrable_on real_interval[--pi,pi] /\
        (hk:num->real->real) k absolutely_real_integrable_on
          real_interval[--pi,pi] /\
        (\x. abs(hk k x) rpow p) real_integrable_on real_interval[--pi,pi] /\
        (!x. gk k (x + &2 * pi) = gk k x) /\
        (!x. f x - gk k x = hk k x)` ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "gk" THEN EXPAND_TAC "hk" THEN
     MP_TAC(SPECL [`f:real->real`; `p:real`; `k:num`] CLAMP_PROPS) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?sk:num->real->bool. !k. real_negligible (sk k) /\
       !x. --pi < x /\ x < pi /\ ~(x IN sk k)
           ==> ((\a. inv(pi) * real_integral (real_interval[--pi,pi])
                      (\t. sin(a * (x - t)) / (x - t) *
                        (gk:num->real->real) k t)) ---> gk k x)
               at_posinfinity`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN GEN_TAC THEN
     MATCH_MP_TAC CARLESON_286U_SINC THEN
    ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
  SUBGOAL_THEN `((\k. real_integral (real_interval[--pi,pi])
                        (\x. abs((hk:num->real->real) k x) rpow p))
                 ---> &0) sequentially` ASSUME_TAC THENL
   [EXPAND_TAC "hk" THEN MATCH_MP_TAC TAIL_LP_TO_ZERO THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  EXISTS_TAC `UNIONS {(sk:num->real->bool) k | k IN (:num)} UNION
              UNIONS {{x | --pi < x /\ x < pi /\
                           ~(x IN UNIONS {sk k | k IN (:num)}) /\
                           !A. ?a. A <= a /\
                                   inv(&m + &1) <=
                                   abs(inv(pi) *
                                       real_integral (real_interval[--pi,pi])
                                        (\t. sin(a * (x - t)) / (x - t) *
                                             f t) - f x)} |
                      m IN (:num)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_NEGLIGIBLE_UNION THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_NEGLIGIBLE_COUNTABLE_UNIONS THENL
     [ASM_REWRITE_TAC[];
      X_GEN_TAC `m:num` THEN
      MP_TAC(SPECL [`p:real`; `C:real`; `f:real->real`; `gk:num->real->real`;
                    `hk:num->real->real`; `sk:num->real->bool`; `m:num`]
        BAD_M_NEGLIGIBLE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN
    REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_GSPEC; IN_ELIM_THM;
    IN_UNIV; NOT_EXISTS_THM]) THEN
  REWRITE_TAC[REALLIM_AT_POSINFINITY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N - 1` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun tm -> is_const tm &&
                              fst(dest_const tm) = "real_integral"))
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(N - 1) + &1 = &N` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `A:real`) THEN EXISTS_TAC `A:real` THEN
  X_GEN_TAC `a:real` THEN FIRST_X_ASSUM(MP_TAC o SPEC `a:real`) THEN
    ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The Carleson-Hunt theorem for 1 < p < 2: the Fourier series of a          *)
(* 2pi-periodic function in L^p[-pi,pi] converges to it almost everywhere.   *)
(* (For p >= 2 this follows from the L^2 theorem, since L^p is contained in  *)
(* L^2 on the circle.)                                                       *)
(* ========================================================================= *)

let CARLESON_HUNT_THEOREM = prove
 (`!f p. &1 < p /\ p < &2 /\
         f real_measurable_on real_interval[--pi,pi] /\
         (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ?s. real_negligible s /\
                 !x. ~(x IN s)
                     ==> ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                              trigonometric_set k x))
                          ---> f x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CARLESON_286V_FROM_CONTINUOUS_SINC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LP_IMP_ABSINT; REAL_LT_IMP_LE];
    MATCH_MP_TAC SINC_AE_LP THEN EXISTS_TAC `p:real` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The Carleson-Hunt theorem for all p > 1: the case p < 2 is                *)
(* CARLESON_HUNT_THEOREM and the case p >= 2 is CARLESON_THEOREM_LP.         *)
(* ========================================================================= *)

let CARLESON_HUNT_THEOREM_ALL_P = prove
 (`!f p. &1 < p /\
         f real_measurable_on real_interval[--pi,pi] /\
         (\x. abs(f x) rpow p) real_integrable_on real_interval[--pi,pi] /\
         (!x. f(x + &2 * pi) = f x)
         ==> ?s. real_negligible s /\
                 !x. ~(x IN s)
                     ==> ((\n. sum(0..n) (\k. fourier_coefficient f k *
                                              trigonometric_set k x))
                          ---> f x) sequentially`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `p < &2` THENL
   [ASM_MESON_TAC[CARLESON_HUNT_THEOREM];
    MATCH_MP_TAC CARLESON_THEOREM_LP THEN
      EXISTS_TAC `p:real` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;
