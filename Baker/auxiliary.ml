(* ========================================================================= *)
(* The auxiliary function of Baker in single-variable form.                  *)
(*                                                                           *)
(* Purpose: the auxiliary function of Baker (Transcendental Number Theory,   *)
(* Ch. 3) as a function of one variable: for a multi-index                   *)
(* m = (m 0, ..., m (n-1)),                                                  *)
(*   F_m(z) = sum_lambda p(lambda) D^(m 0) G_lambda(z)                       *)
(*                 prod_{r=1}^{n-1} (gamma_r lg_r)^(m r)                     *)
(*                 cexp(z sum_{r=1}^{n-1} gamma_r lg_r),                     *)
(* lambda = (a,b,mu), a < h, b <= L, mu r <= L (1 <= r <= n),                *)
(* gamma_r = mu r + mu n beta r,                                             *)
(* G_lambda(w) = B_{a,b}(w) cexp(mu n beta 0 w)                              *)
(* with the basis polynomials B_{a,b} = feldman_basis h a b. Here beta r is  *)
(* -beta_r/beta_n of Baker and lg r is log alpha_r (r < n); the number       *)
(* beta 0 + sum_{r<n} beta r lg r approximates log alpha_n.                  *)
(*                                                                           *)
(* Proved: the derivative relation D F_m = sum_{i<n} F_{m+e_i}; the explicit *)
(* form of the terms and the upper bound (Baker Lemma 5, first part); the    *)
(* algebraic counterpart baker_alg (the true logarithm lg n in the exponent  *)
(* and no factor prod_r lg_r^(m r)), whose values at integers and rationals  *)
(* are algebraic, and the bound for its difference with F_m in terms of      *)
(* delta = beta 0 + sum_{r<n} beta r lg r - lg n.                            *)
(*                                                                           *)
(* Main results: baker_index, baker_aux, baker_alg (definitions; also        *)
(*   baker_gamma, baker_term, baker_omega, baker_algterm);                   *)
(*   BAKER_AUX_HAS_DERIVATIVE, BAKER_AUX_HOLOMORPHIC, BAKER_AUX_DERIVATIVE,  *)
(*   BAKER_AUX_BOUND, BAKER_AUX_ALG_APPROX; NORM_CEXP_LE,                    *)
(*   NORM_CEXP_SUB_1_LE.                                                     *)
(*                                                                           *)
(* Uses: Baker/algebraic.ml (CPRODUCT_DELETE), sets.ml                       *)
(*   (FINITE_CARTESIAN_PRODUCT_FINITE), Baker/delta.ml (feldman_basis and    *)
(*   its derivative bounds); CEXP_LIPSCHITZ_BOUNDED of                       *)
(*   Multivariate/transcendentals.ml.                                        *)
(* ========================================================================= *)

needs "Baker/intpoly.ml";;
needs "Baker/delta.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Definitions.                                                              *)
(* ------------------------------------------------------------------------- *)

let baker_index = new_definition
 `baker_index h L n =
    {a:num | a < h} CROSS
    ((0..L) CROSS cartesian_product (1..n) (\r:num. 0..L))`;;

let baker_gamma = new_definition
 `baker_gamma n (beta:num->complex) (mu:num->num) r =
    Cx(&(mu r)) + Cx(&(mu n)) * beta r`;;

let baker_term = new_definition
 `baker_term n h (p:num#num#(num->num)->real) beta (lg:num->complex)
             (m:num->num) (a,b,mu) z =
    Cx(p(a,b,mu)) *
    higher_complex_derivative (m 0)
      (\w. feldman_basis h a b w * cexp((Cx(&(mu n)) * beta 0) * w)) z *
    cproduct(1..n-1) (\r. (baker_gamma n beta mu r * lg r) pow (m r)) *
    cexp(z * vsum(1..n-1) (\r. baker_gamma n beta mu r * lg r))`;;

let baker_aux = new_definition
 `baker_aux n h L p beta lg m z =
    vsum (baker_index h L n) (\x. baker_term n h p beta lg m x z)`;;

let baker_omega = new_definition
 `baker_omega n (beta:num->complex) (lg:num->complex) (mu:num->num) =
    Cx(&(mu n)) * beta 0 + vsum(1..n-1) (\r. baker_gamma n beta mu r * lg r)`;;

let FINITE_BAKER_INDEX = prove
 (`!h L n. FINITE(baker_index h L n)`,
  REWRITE_TAC[baker_index] THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FINITE_NUMSEG_LT;
           FINITE_CARTESIAN_PRODUCT_FINITE]);;
let CPRODUCT_POW_INCREMENT = prove
 (`!s (x:num->complex) m i.
        FINITE s /\ i IN s
        ==> cproduct s (\r. x r pow (if r = i then m r + 1 else m r)) =
            x i * cproduct s (\r. x r pow (m r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. (x:num->complex) r pow (if r = i then m r + 1 else m r)`;
                 `s:num->bool`; `i:num`] CPRODUCT_DELETE) THEN
  MP_TAC(ISPECL [`\r. (x:num->complex) r pow (m r)`;
                 `s:num->bool`; `i:num`] CPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[GSYM ADD1; complex_pow; GSYM COMPLEX_MUL_ASSOC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE]);;

let HOLOMORPHIC_ON_BAKER_G = prove
 (`!h a b c s. (\w. feldman_basis h a b w * cexp(c * w)) holomorphic_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
  REWRITE_TAC[ETA_AX; HOLOMORPHIC_ON_FELDMAN_BASIS] THEN
  SUBGOAL_THEN `(\w. cexp(c * w)) = cexp o (\w. c * w)` SUBST1_TAC THENL
   [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN THEN EXISTS_TAC `(:complex)` THEN
  SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID;
           HOLOMORPHIC_ON_CEXP; IN_UNIV]);;

let BAKER_TERM_HAS_DERIVATIVE = prove
 (`!n h p beta lg m a b mu z.
        ((\z. baker_term n h p beta lg m (a,b,mu) z) has_complex_derivative
         (baker_term n h p beta lg (\r. if r = 0 then m r + 1 else m r)
                     (a,b,mu) z +
          vsum(1..n-1) (\i. baker_term n h p beta lg
                              (\r. if r = i then m r + 1 else m r)
                              (a,b,mu) z)))
        (at z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[baker_term] THEN
  ABBREV_TAC `G = \w. feldman_basis h a b w *
                      cexp((Cx(&((mu:num->num) n)) * beta 0) * w)` THEN
  ABBREV_TAC `P = cproduct(1..n-1)
                   (\r. (baker_gamma n beta mu r * (lg:num->complex) r) pow
                        ((m:num->num) r))` THEN
  ABBREV_TAC `s = vsum(1..n-1)
                   (\r. baker_gamma n beta mu r * (lg:num->complex) r)` THEN
  SUBGOAL_THEN
   `cproduct(1..n-1) (\r. (baker_gamma n beta mu r * lg r) pow
                          (if r = 0 then m r + 1 else m r)) = P`
  SUBST1_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC CPRODUCT_EQ THEN
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= r ==> ~(r = 0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN 1..n-1
        ==> cproduct(1..n-1) (\r. (baker_gamma n beta mu r * lg r) pow
                                  (if r = i then m r + 1 else m r)) =
            (baker_gamma n beta mu i * lg i) * P`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC CPRODUCT_POW_INCREMENT THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..n-1)
     (\i. Cx((p:num#num#(num->num)->real)(a,b,mu)) *
          higher_complex_derivative (if 0 = i then m 0 + 1 else m 0) G z *
          cproduct(1..n-1) (\r. (baker_gamma n beta mu r * lg r) pow
                                (if r = i then m r + 1 else m r)) *
          cexp(z * s)) =
    Cx(p(a,b,mu)) * higher_complex_derivative (m 0) G z * (s * P) *
    cexp(z * s)`
  SUBST1_TAC THENL
   [TRANS_TAC EQ_TRANS
     `vsum(1..n-1) (\i. Cx((p:num#num#(num->num)->real)(a,b,mu)) *
                        higher_complex_derivative (m 0) G z *
                        ((baker_gamma n beta mu i * lg i) * P) *
                        cexp(z * s))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(0 = i)` (fun th -> REWRITE_TAC[th]) THENL
       [UNDISCH_TAC `i IN 1..n-1` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC;
      SIMP_TAC[VSUM_COMPLEX_LMUL; VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `(:complex)`; `z:complex`;
                 `(m:num->num) 0`]
         HAS_COMPLEX_DERIVATIVE_HIGHER_COMPLEX_DERIVATIVE) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "G" THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV; HOLOMORPHIC_ON_BAKER_G];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\z. P * cexp(z * s)) has_complex_derivative (P * (s * cexp(z * s))))
    (at z)`
  ASSUME_TAC THENL
   [COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_AT o
    CONJ (ASSUME `(higher_complex_derivative (m 0) G has_complex_derivative
                   higher_complex_derivative (m 0 + 1) G z) (at z)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx((p:num#num#(num->num)->real)(a,b,mu))` o
             MATCH_MP HAS_COMPLEX_DERIVATIVE_LMUL_AT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The derivative relation D F_m = sum_{i<n} F_{m+e_i}.                      *)
(* ------------------------------------------------------------------------- *)

let BAKER_AUX_HAS_DERIVATIVE = prove
 (`!n h L p beta lg m z.
        1 <= n
        ==> (baker_aux n h L p beta lg m has_complex_derivative
             vsum(0..n-1) (\i. baker_aux n h L p beta lg
                                 (\r. if r = i then m r + 1 else m r) z))
            (at z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `baker_aux n h L p beta lg m =
    \z. vsum (baker_index h L n) (\x. baker_term n h p beta lg m x z)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; baker_aux]; ALL_TAC] THEN
  REWRITE_TAC[baker_aux] THEN
  MP_TAC(ISPECL
   [`\i x. baker_term n h p beta lg (\r. if r = i then m r + 1 else m r) x z`;
    `0..n-1`; `baker_index h L n`] VSUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_BAKER_INDEX] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_BAKER_INDEX; FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `0 <= n - 1`
   (fun th -> REWRITE_TAC[MATCH_MP VSUM_CLAUSES_LEFT th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; BAKER_TERM_HAS_DERIVATIVE]);;

let BAKER_AUX_HOLOMORPHIC = prove
 (`!n h L p beta lg m s.
        1 <= n ==> baker_aux n h L p beta lg m holomorphic_on s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[holomorphic_on] THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  EXISTS_TAC
   `vsum(0..n-1) (\i. baker_aux n h L p beta lg
                        (\r. if r = i then m r + 1 else m r) z)` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
  ASM_SIMP_TAC[BAKER_AUX_HAS_DERIVATIVE]);;

let BAKER_AUX_DERIVATIVE = prove
 (`!n h L p beta lg m.
        1 <= n
        ==> complex_derivative (baker_aux n h L p beta lg m) =
            \z. vsum(0..n-1) (\i. baker_aux n h L p beta lg
                                    (\r. if r = i then m r + 1 else m r) z)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC[BAKER_AUX_HAS_DERIVATIVE]);;

(* ------------------------------------------------------------------------- *)
(* Explicit form of the terms and the upper bound (Baker Lemma 5, first      *)
(* part): |F_m(z)| <= #index P 2^((L+2)(N+h)) (m0 + L|b0|)^m0 ...            *)
(* exp(N L Omega) for |z| + 1 <= N.                                          *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_CEXP_LINEAR = prove
 (`!c k. higher_complex_derivative k (\w. cexp(c * w)) =
         \w. c pow k * cexp(c * w)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[higher_complex_derivative; complex_pow; COMPLEX_MUL_LID;
                  ETA_AX] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let FACT_LE_POW = prove
 (`!j m. j <= m ==> FACT j <= m EXP j`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; EXP; LE_REFL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
   [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let SUM_BINOM_FACT_POW_LE = prove
 (`!m x. &0 <= x
         ==> sum(0..m) (\j. &(binom(m,j)) * &(FACT j) * x pow (m - j)) <=
             (&m + x) pow m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_BINOMIAL_THEOREM] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; FACT_LE_POW]);;

let BAKER_TERM_EXPLICIT = prove
 (`!n h p beta lg m a b mu z.
        baker_term n h p beta lg m (a,b,mu) z =
        Cx(p(a,b,mu)) *
        vsum(0..m 0) (\j. Cx(&(binom(m 0,j))) *
                          higher_complex_derivative j (feldman_basis h a b) z *
                          (Cx(&(mu n)) * beta 0) pow (m 0 - j)) *
        cproduct(1..n-1) (\r. (baker_gamma n beta mu r * lg r) pow (m r)) *
        cexp(z * baker_omega n beta lg mu)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[baker_term; baker_omega] THEN
  MP_TAC(ISPECL [`feldman_basis h a b`;
                 `\w. cexp((Cx(&((mu:num->num) n)) * beta 0) * w)`;
                 `(:complex)`; `(m:num->num) 0`; `z:complex`]
         HIGHER_COMPLEX_DERIVATIVE_MUL) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV; HOLOMORPHIC_ON_FELDMAN_BASIS] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `(\w. cexp((Cx(&((mu:num->num) n)) * beta 0) * w)) =
      cexp o (\w. (Cx(&(mu n)) * beta 0) * w)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE_GEN THEN EXISTS_TAC `(:complex)` THEN
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_ID;
             HOLOMORPHIC_ON_CEXP; IN_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_CEXP_LINEAR] THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB; CEXP_ADD] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let BAKER_DPART_BOUND = prove
 (`!h L a b m z N c X.
        a < h /\ b <= L /\ norm z + &1 <= &N /\ norm c <= X
        ==> norm(vsum(0..m) (\j. Cx(&(binom(m,j))) *
                                 higher_complex_derivative j
                                   (feldman_basis h a b) z *
                                 c pow (m - j))) <=
            &2 pow ((L + 2) * (N + h)) * (&m + X) pow m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(0..m) (\j. &(binom(m,j)) * (&(FACT j) * &2 pow ((L + 2) * (N + h))) *
                   X pow (m - j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM;
                COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_POW_LE2] THEN
    MP_TAC(ISPECL [`h:num`; `a:num`; `b:num`; `j:num`; `z:complex`; `N:num`]
           FELDMAN_BASIS_DERIV_BOUND) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow ((N + a) + (b + 1) * (N + h)) * &(FACT j)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THENL
     [ARITH_TAC;
      MATCH_MP_TAC(ARITH_RULE
       `a < h /\ (b + 1) * (N + h) <= (L + 1) * (N + h)
        ==> (N + a) + (b + 1) * (N + h) <= (L + 2) * (N + h)`) THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    REWRITE_TAC[REAL_ARITH `b * (f * t) * x = t * b * f * x:real`] THEN
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_POS; SUM_BINOM_FACT_POW_LE]]);;

let BAKER_GAMMA_BOUND = prove
 (`!n beta mu r L.
        mu r <= L /\ mu n <= L
        ==> norm(baker_gamma n beta mu r) <= &L * (&1 + norm(beta r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_gamma] THEN
  W(MP_TAC o PART_MATCH lhand NORM_TRIANGLE o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH
   `x <= l /\ y <= l * b ==> n <= x + y ==> n <= l * (&1 + b)`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_LE_RMUL; NORM_POS_LE]);;

let BAKER_OMEGA_SPLIT = prove
 (`!n beta lg mu.
        1 <= n
        ==> baker_omega n beta lg mu =
            vsum(1..n) (\r. Cx(&(mu r)) * lg r) +
            Cx(&(mu n)) * (beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_omega; baker_gamma] THEN
  SUBGOAL_THEN `0 < n /\ 1 <= n` (fun th ->
    REWRITE_TAC[MATCH_MP VSUM_CLAUSES_RIGHT th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_ADD_RDISTRIB] THEN
  SIMP_TAC[VSUM_ADD; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN CONV_TAC COMPLEX_RING);;

let BAKER_OMEGA_BOUND_DELTA = prove
 (`!n beta lg mu L.
        (!r. r IN 1..n ==> mu r <= L) /\ 1 <= n
        ==> norm(baker_omega n beta lg mu) <=
            &L * (sum(1..n) (\r. norm(lg r)) +
                  norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[BAKER_OMEGA_SPLIT] THEN
  SUBGOAL_THEN `(mu:num->num) n <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:complex) <= a /\ norm(y:complex) <= b ==> norm(x + y) <= a + b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_OF_NUM_LE; NORM_POS_LE];
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_OF_NUM_LE; NORM_POS_LE]]);;

let NORM_CEXP_LE = prove
 (`!z. norm(cexp z) <= exp(norm z)`,
  GEN_TAC THEN REWRITE_TAC[NORM_CEXP; REAL_EXP_MONO_LE] THEN
  MP_TAC(SPEC `z:complex` COMPLEX_NORM_GE_RE_IM) THEN REAL_ARITH_TAC);;

let BAKER_TERM_BOUND = prove
 (`!n h L p beta lg m a b mu z N P.
        1 <= n /\ a < h /\ b <= L /\ (!r. r IN 1..n ==> mu r <= L) /\
        abs(p(a,b,mu)) <= P /\ norm z + &1 <= &N
        ==> norm(baker_term n h p beta lg m (a,b,mu) z) <=
            P * &2 pow ((L + 2) * (N + h)) *
            (&(m 0) + &L * norm(beta 0)) pow (m 0) *
            product(1..n-1)
              (\r. (&L * (&1 + norm(beta r)) * norm(lg r)) pow (m r)) *
            exp(&N * &L *
                (sum(1..n) (\r. norm(lg r)) +
                 norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[BAKER_TERM_EXPLICIT] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `(mu:num->num) n <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BAKER_DPART_BOUND THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_LE_RMUL; NORM_POS_LE];
      ALL_TAC] THEN
    SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_POW; COMPLEX_NORM_MUL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN
      SIMP_TAC[REAL_LE_MUL; NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC BAKER_GAMMA_BOUND THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `exp(norm(z * baker_omega n beta lg mu))` THEN
  REWRITE_TAC[NORM_CEXP_LE; REAL_EXP_MONO_LE; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC BAKER_OMEGA_BOUND_DELTA THEN ASM_REWRITE_TAC[]);;

let BAKER_AUX_BOUND = prove
 (`!n h L p beta lg m z N P.
        1 <= n /\ (!x. x IN baker_index h L n ==> abs(p x) <= P) /\
        norm z + &1 <= &N
        ==> norm(baker_aux n h L p beta lg m z) <=
            &(CARD(baker_index h L n)) *
            (P * &2 pow ((L + 2) * (N + h)) *
             (&(m 0) + &L * norm(beta 0)) pow (m 0) *
             product(1..n-1)
               (\r. (&L * (&1 + norm(beta r)) * norm(lg r)) pow (m r)) *
             exp(&N * &L *
                 (sum(1..n) (\r. norm(lg r)) +
                  norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_aux] THEN
  MATCH_MP_TAC VSUM_NORM_BOUND THEN REWRITE_TAC[FINITE_BAKER_INDEX] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  MATCH_MP_TAC BAKER_TERM_BOUND THEN ASM_SIMP_TAC[] THEN
  UNDISCH_TAC `(a,b,mu) IN baker_index h L n` THEN
  REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
              cartesian_product; EXTENSIONAL] THEN
  SIMP_TAC[IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The algebraic counterpart: replace beta 0 + sum_{r<n} beta r lg r by the  *)
(* true logarithm lg n in the exponent, and drop the factor prod lg_r^(m r). *)
(* At integers (and at rationals l/k) its value is an algebraic number;      *)
(* BAKER_AUX_ALG_APPROX bounds the difference in terms of                    *)
(* delta = beta 0 + sum_{r<n} beta r lg r - lg n.                            *)
(* ------------------------------------------------------------------------- *)

let baker_algterm = new_definition
 `baker_algterm n h (p:num#num#(num->num)->real) beta (lg:num->complex)
                (m:num->num) (a,b,mu) z =
    Cx(p(a,b,mu)) *
    vsum(0..m 0) (\j. Cx(&(binom(m 0,j))) *
                      higher_complex_derivative j (feldman_basis h a b) z *
                      (Cx(&(mu n)) * beta 0) pow (m 0 - j)) *
    cproduct(1..n-1) (\r. baker_gamma n beta mu r pow (m r)) *
    cexp(z * vsum(1..n) (\r. Cx(&(mu r)) * lg r))`;;

let baker_alg = new_definition
 `baker_alg n h L p beta lg m z =
    vsum (baker_index h L n) (\x. baker_algterm n h p beta lg m x z)`;;

let NORM_CEXP_SUB_1_LE = prove
 (`!z. norm(cexp z - Cx(&1)) <= norm z * exp(norm z)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`norm(z:complex)`; `z:complex`; `Cx(&0)`]
         CEXP_LIPSCHITZ_BOUNDED) THEN
  REWRITE_TAC[CEXP_0; COMPLEX_SUB_RZERO; COMPLEX_NORM_0; NORM_POS_LE;
              REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let BAKER_TERM_ALGTERM = prove
 (`!n h p beta lg m a b mu z.
        1 <= n
        ==> baker_term n h p beta lg m (a,b,mu) z =
            cproduct(1..n-1) (\r. lg r pow (m r)) *
            baker_algterm n h p beta lg m (a,b,mu) z *
            cexp(z * Cx(&(mu n)) *
                 (beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[BAKER_TERM_EXPLICIT; baker_algterm; BAKER_OMEGA_SPLIT] THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB; CEXP_ADD; COMPLEX_POW_MUL] THEN
  SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let BAKER_ALGTERM_BOUND = prove
 (`!n h L p beta lg m a b mu z N P.
        1 <= n /\ a < h /\ b <= L /\ (!r. r IN 1..n ==> mu r <= L) /\
        abs(p(a,b,mu)) <= P /\ norm z + &1 <= &N
        ==> norm(baker_algterm n h p beta lg m (a,b,mu) z) <=
            P * &2 pow ((L + 2) * (N + h)) *
            (&(m 0) + &L * norm(beta 0)) pow (m 0) *
            product(1..n-1) (\r. (&L * (&1 + norm(beta r))) pow (m r)) *
            exp(&N * &L * sum(1..n) (\r. norm(lg r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_algterm] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `(mu:num->num) n <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BAKER_DPART_BOUND THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LE; REAL_LE_RMUL; NORM_POS_LE];
      ALL_TAC] THEN
    SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_POW] THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC BAKER_GAMMA_BOUND THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `exp(norm(z * vsum(1..n) (\r. Cx(&((mu:num->num) r)) * lg r)))` THEN
  REWRITE_TAC[NORM_CEXP_LE; REAL_EXP_MONO_LE; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_OF_NUM_LE; NORM_POS_LE]);;

let BAKER_AUX_ALG_APPROX = prove
 (`!n h L p beta lg m z N P.
        1 <= n /\ (!x. x IN baker_index h L n ==> abs(p x) <= P) /\
        norm z + &1 <= &N
        ==> norm(baker_aux n h L p beta lg m z -
                 cproduct(1..n-1) (\r. lg r pow (m r)) *
                 baker_alg n h L p beta lg m z) <=
            &(CARD(baker_index h L n)) *
            (P * &2 pow ((L + 2) * (N + h)) *
             (&(m 0) + &L * norm(beta 0)) pow (m 0) *
             product(1..n-1)
               (\r. (&L * (&1 + norm(beta r)) * norm(lg r)) pow (m r)) *
             exp(&N * &L * sum(1..n) (\r. norm(lg r)))) *
            (&N * &L *
             norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) *
             exp(&N * &L *
                 norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_aux; baker_alg] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_BAKER_INDEX] THEN
  MATCH_MP_TAC VSUM_NORM_BOUND THEN REWRITE_TAC[FINITE_BAKER_INDEX] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `a < h /\ b <= L /\ (!r. r IN 1..n ==> (mu:num->num) r <= L)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a,b,mu) IN baker_index h L n` THEN
    REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
                cartesian_product; EXTENSIONAL] THEN
    SIMP_TAC[IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[BAKER_TERM_ALGTERM] THEN
  ABBREV_TAC `d = (beta:num->complex) 0 + vsum(1..n-1) (\r. beta r * lg r) -
                  (lg:num->complex) n` THEN
  REWRITE_TAC[COMPLEX_RING
   `l * a * e - l * a:complex = (l * a) * (e - Cx(&1))`] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_LE_MUL; NORM_POS_LE] THEN
  CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `norm(cproduct(1..n-1) (\r. (lg:num->complex) r pow (m r))) *
      (P * &2 pow ((L + 2) * (N + h)) *
       (&(m 0) + &L * norm((beta:num->complex) 0)) pow (m 0) *
       product(1..n-1) (\r. (&L * (&1 + norm(beta r))) pow (m r)) *
       exp(&N * &L * sum(1..n) (\r. norm(lg r))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      MATCH_MP_TAC BAKER_ALGTERM_BOUND THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN
       `norm(cproduct(1..n-1) (\r. (lg:num->complex) r pow (m r))) =
        product(1..n-1) (\r. norm(lg r) pow (m r))`
      SUBST1_TAC THENL
       [SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG; COMPLEX_NORM_POW]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      REWRITE_TAC[REAL_POW_MUL; PRODUCT_MUL_NUMSEG] THEN
      REWRITE_TAC[REAL_MUL_AC]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `norm(z * Cx(&((mu:num->num) n)) * d) *
    exp(norm(z * Cx(&(mu n)) * d))` THEN
  REWRITE_TAC[NORM_CEXP_SUB_1_LE] THEN
  SUBGOAL_THEN `norm(z * Cx(&((mu:num->num) n)) * d) <= &N * &L * norm d`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[NORM_POS_LE; REAL_POS; REAL_LE_MUL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE; REAL_OF_NUM_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC; NORM_POS_LE; REAL_EXP_POS_LE;
                  REAL_EXP_MONO_LE]);;
