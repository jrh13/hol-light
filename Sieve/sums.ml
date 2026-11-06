(* ========================================================================= *)
(* Partial summation in integral form, and some integral bounds.             *)
(*                                                                           *)
(* ABEL_SUMMATION is the exact formula                                       *)
(*                                                                           *)
(*  sum_{y<n<=x} a(n) f(n) = (A(x)-A(y)) f(x) - int_y^x (A(t)-A(y)) f'(t) dt *)
(*                                                                           *)
(* proved by writing f(n) = f(x) - int_n^x f' and exchanging the finite sum  *)
(* with the integral.  ABEL_SUMMATION_ASYMPTOTIC compares a sum with the     *)
(* integral int_y^x M'(t) f(t) dt when the partial sums of a(n) are within C *)
(* of M(t) - M(y) and f is monotone.                                         *)
(* ========================================================================= *)

needs "Sieve/base.ml";;
needs "Multivariate/realanalysis.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Two general facts about real integrals.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_REAL_INTEGRAL_ABS_BOUND = prove
 (`!f g s i j.
        (f has_real_integral i) s /\ (g has_real_integral j) s /\
        (!x. x IN s ==> abs(f x) <= g x)
        ==> abs i <= j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real->real`; `g:real->real`; `s:real->bool`]
         REAL_INTEGRAL_ABS_BOUND_INTEGRAL) THEN
  ASM_MESON_TAC[REAL_INTEGRAL_UNIQUE; real_integrable_on]);;

let HAS_REAL_INTEGRAL_ABS_SIGNED = prove
 (`!f s i.
        (f has_real_integral i) s /\
        ((!x. x IN s ==> &0 <= f x) \/ (!x. x IN s ==> f x <= &0))
        ==> ((\x. abs(f x)) has_real_integral abs i) s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC) THENL
   [SUBGOAL_THEN `&0 <= i` ASSUME_TAC THENL
     [ASM_MESON_TAC[HAS_REAL_INTEGRAL_POS]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= i ==> abs i = i`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC `f:real->real` THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= u ==> abs u = u`];
    SUBGOAL_THEN `((\x. --(f x)) has_real_integral --i) s` ASSUME_TAC THENL
     [ASM_SIMP_TAC[HAS_REAL_INTEGRAL_NEG]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= --i` ASSUME_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_POS THEN
      EXISTS_TAC `\x. --((f:real->real) x)` THEN EXISTS_TAC `s:real->bool` THEN
      ASM_SIMP_TAC[REAL_ARITH `u <= &0 ==> &0 <= --u`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= --i ==> abs i = --i`] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\x. --((f:real->real) x)` THEN
    ASM_SIMP_TAC[REAL_ARITH `u <= &0 ==> abs u = --u`]]);;

(* ------------------------------------------------------------------------- *)
(* Abel summation.                                                           *)
(* ------------------------------------------------------------------------- *)

let ABEL_SUMMATION = prove
 (`!a f f' x y.
        y <= x /\
        (!t. t IN real_interval[y,x]
             ==> (f has_real_derivative f' t)
                 (atreal t within real_interval[y,x]))
        ==> ((\t. sum {n | y < &n /\ &n <= t} a * f' t) has_real_integral
             (sum {n | y < &n /\ &n <= x} a * f x -
              sum {n | y < &n /\ &n <= x} (\n. a n * f(&n))))
            (real_interval[y,x])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {n | y < &n /\ &n <= x}` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\t. sum {n | y < &n /\ &n <= x}
            (\n. a n * (if t IN real_interval[&n,x] then f' t else &0))` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {n | y < &n /\ &n <= x} a * f x -
    sum {n | y < &n /\ &n <= x} (\n. a n * f(&n)) =
    sum {n | y < &n /\ &n <= x} (\n. a n * (f x - f(&n)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_RMUL; GSYM SUM_SUB; REAL_SUB_LDISTRIB]; ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_SUM THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
  ASM_SIMP_TAC[HAS_REAL_INTEGRAL_RESTRICT; SUBSET_REAL_INTERVAL;
               REAL_LT_IMP_LE; REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_WITHIN_SUBSET THEN
  EXISTS_TAC `real_interval[y,x]` THEN
  REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN
  CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
  REAL_ARITH_TAC);;

let ABEL_SUMMATION_ASYMPTOTIC = prove
 (`!a f f' M m C x y.
        y <= x /\
        (!t. t IN real_interval[y,x]
             ==> (f has_real_derivative f' t)
                 (atreal t within real_interval[y,x])) /\
        ((!t. t IN real_interval[y,x] ==> &0 <= f' t) \/
         (!t. t IN real_interval[y,x] ==> f' t <= &0)) /\
        (!t. t IN real_interval[y,x]
             ==> (M has_real_derivative m t)
                 (atreal t within real_interval[y,x])) /\
        m real_continuous_on real_interval[y,x] /\
        (!t. t IN real_interval[y,x]
             ==> abs(sum {n | y < &n /\ &n <= t} a - (M t - M y)) <= C)
        ==> abs(sum {n | y < &n /\ &n <= x} (\n. a n * f(&n)) -
                real_integral (real_interval[y,x]) (\t. m t * f t))
            <= C * (abs(f x) + abs(f x - f y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  DISCH_TAC THEN DISCH_THEN(LABEL_TAC "fd") THEN
  DISCH_THEN(LABEL_TAC "sg") THEN DISCH_THEN(LABEL_TAC "Md") THEN
  DISCH_THEN(LABEL_TAC "mc") THEN DISCH_THEN(LABEL_TAC "bd") THEN
  MP_TAC(ISPECL [`a:num->real`; `f:real->real`; `f':real->real`;
                 `x:real`; `y:real`] ABEL_SUMMATION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `((\t. (M t - M y) * f' t + m t * f t) has_real_integral
     (M x - M y) * f x) (real_interval[y,x])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`\t. (M t - M y) * (f:real->real) t`;
      `\t. (M t - M y) * f' t + m t * (f:real->real) t`;
      `y:real`; `x:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`M:real->real`; `(m:real->real) t`;
                   `(\t:real. (M:real->real) y)`;
                   `&0`; `atreal t within real_interval[y,x]`]
           HAS_REAL_DERIVATIVE_SUB) THEN
    ASM_SIMP_TAC[HAS_REAL_DERIVATIVE_CONST; REAL_SUB_RZERO] THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`\t. (M:real->real) t - M y`; `(m:real->real) t`;
                   `f:real->real`; `(f':real->real) t`; `t:real`;
                   `real_interval[y,x]`] HAS_REAL_DERIVATIVE_MUL_WITHIN) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\t. m t * f t) has_real_integral
     real_integral (real_interval[y,x]) (\t. m t * f t)) (real_interval[y,x])`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM HAS_REAL_INTEGRAL_INTEGRAL] THEN
    MATCH_MP_TAC REAL_INTEGRABLE_CONTINUOUS THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_IMP_CONTINUOUS_WITHINREAL THEN
    EXISTS_TAC `(f':real->real) t` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `J = (sum {n | y < &n /\ &n <= x} a * f x -
                   sum {n | y < &n /\ &n <= x} (\n. a n * f(&n))) -
                  ((M x - M y) * f x -
                   real_integral (real_interval[y,x]) (\t. m t * f t))` THEN
  SUBGOAL_THEN
   `((\t. (sum {n | y < &n /\ &n <= t} a - (M t - M y)) * f' t)
     has_real_integral J) (real_interval[y,x])`
  ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\t. sum {n | y < &n /\ &n <= t} a * f' t -
                    (((M t - M y) * f' t + m t * f t) - m t * f t)` THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_RDISTRIB] THEN
      REWRITE_TAC[REAL_ARITH `s - ((p - q + e) - e) = s - (p - q:real)`];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs J <= C * abs((f:real->real) x - f y)` ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_ABS_BOUND THEN
    EXISTS_TAC `\t. (sum {n | y < &n /\ &n <= t} a - (M t - M y)) * f' t` THEN
    EXISTS_TAC `\t. C * abs((f':real->real) t)` THEN
    EXISTS_TAC `real_interval[y,x]` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HAS_REAL_INTEGRAL_LMUL THEN
      MATCH_MP_TAC HAS_REAL_INTEGRAL_ABS_SIGNED THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s i a p fx j c u v.
        ((a * fx - s) - (p * fx - i) = j) /\
        abs((a - p) * fx) <= c * u /\ abs j <= c * v
        ==> abs(s - i) <= c * (u + v)`) THEN
  MAP_EVERY EXISTS_TAC
   [`sum {n | y < &n /\ &n <= x} a`; `(M:real->real) x - M y`;
    `(f:real->real) x`; `J:real`] THEN
  ASM_REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  USE_THEN "bd" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* A function whose increments beyond x are bounded by d(x), where d takes   *)
(* arbitrarily small values, has a limit l with |E(x) - l| <= d(x).          *)
(* ------------------------------------------------------------------------- *)

let CAUCHY_RATE_LIMIT = prove
 (`!E:real->real d a.
        (!x y. a <= x /\ x <= y ==> abs(E y - E x) <= d x) /\
        (!e. &0 < e ==> ?x. a <= x /\ d x < e)
        ==> ?l. !x. a <= x ==> abs(E x - l) <= d x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(LABEL_TAC "small") THEN
  SUBGOAL_THEN `?l. ((\n. E(a + &n)) ---> l) sequentially`
  (X_CHOOSE_TAC `l:real`) THENL
   [REWRITE_TAC[TENDSTO_REAL] THEN REWRITE_TAC[GSYM EXISTS_LIFT] THEN
    REWRITE_TAC[CONVERGENT_EQ_CAUCHY; cauchy; o_THM; DIST_LIFT] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    USE_THEN "small" (MP_TAC o SPEC `e / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `x - a:real` REAL_ARCH_SIMPLE) THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REWRITE_TAC[GE; GSYM REAL_OF_NUM_LE] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`x:real`; `a + &m`] th) THEN
      MP_TAC(SPECL [`x:real`; `a + &n`] th)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `l:real` THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
  MP_TAC(SPEC `x - a:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  SUBGOAL_THEN
   `eventually (\n. abs((E:real->real)(a + &n) - E x) <= (d:real->real) x)
               sequentially`
  (LABEL_TAC "ev") THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sequentially`; `\n. (E:real->real)(a + &n)`; `l:real`;
                 `(E:real->real) x + (d:real->real) x`] REALLIM_UBOUND) THEN
  MP_TAC(ISPECL [`sequentially`; `\n. (E:real->real)(a + &n)`; `l:real`;
                 `(E:real->real) x - (d:real->real) x`] REALLIM_LBOUND) THEN
  ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REPEAT(ANTS_TAC THENL
   [USE_THEN "ev" MP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    REAL_ARITH_TAC;
    DISCH_TAC]) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Partial summation against a monotone weight, with only an upper bound on  *)
(* the tail sums (Nathanson's Lemma 9.8, without Stieltjes integrals): for   *)
(* points p in [w,z), weights c(p) >= 0, Phi increasing, continuous, >= 0,   *)
(* and tail sums  sum_{p >= u} c(p) <= B(u)  with B' <= 0 and B(z) >= 0:     *)
(*                                                                           *)
(*   sum_p c(p) Phi(p) <= B(z) Phi(z) - int_w^z B'(u) Phi(u) du.             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* [N] Lemma 9.8 in cumulative form: points x(p) in [s,S] with weights       *)
(* c(p) >= 0 whose cumulative sums are bounded by an affine function         *)
(* B0 + b (t - s), against a decreasing psi >= 0.  This is the form used     *)
(* for the linear sieve, in the variable t = log D / log p, and needs no     *)
(* change of variables in the integral.                                      *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_DIV_DENOM = prove
 (`!a b c. &0 < c /\ &0 < a /\ &0 < b ==> (c / a <= c / b <=> b <= a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN ASM_MESON_TAC[REAL_LT_INV2];
    ASM_MESON_TAC[REAL_LE_INV2]]);;

let REAL_LT_DIV_DENOM = prove
 (`!a b c. &0 < c /\ &0 < a /\ &0 < b ==> (c / a < c / b <=> b < a)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ASM_SIMP_TAC[REAL_LE_DIV_DENOM]);;

let REAL_INTEGRAL_UPPER_MONO_POS = prove
 (`!f a b c.
        (!x. a <= x /\ x <= c ==> &0 <= f x) /\
        f real_integrable_on real_interval[a,c] /\ b <= c
        ==> real_integral (real_interval[a,b]) f <=
            real_integral (real_interval[a,c]) f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= real_integral (real_interval[a,c]) f` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN ASM_SIMP_TAC[IN_REAL_INTERVAL];
    ALL_TAC] THEN
  ASM_CASES_TAC `b <= a` THEN ASM_SIMP_TAC[REAL_INTEGRAL_NULL] THEN
  MP_TAC(ISPECL [`f:real->real`; `a:real`; `c:real`; `b:real`]
         REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
  MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `c:real`] THEN
    ASM_REWRITE_TAC[SUBSET_REAL_INTERVAL] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC]);;

let REAL_INTEGRAL_DECREASING_LOWER = prove
 (`!(psi:real->real) s S u v.
        (!x y. s <= x /\ x <= y /\ y <= S ==> psi y <= psi x) /\
        s <= u /\ u <= v /\ v <= S
        ==> (v - u) * psi v <= real_integral (real_interval[u,v]) psi`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `real_integral (real_interval[u,v]) (\x:real. psi v)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_INTEGRAL_CONST] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_INTEGRAL_LE THEN REWRITE_TAC[REAL_INTEGRABLE_CONST] THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC;
    REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let REAL_INTEGRABLE_DECREASING_SUB = prove
 (`!(psi:real->real) s S u v.
        (!x y. s <= x /\ x <= y /\ y <= S ==> psi y <= psi x) /\
        s <= u /\ v <= S
        ==> psi real_integrable_on real_interval[u,v]`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_INTEGRABLE_DECREASING THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

let FINITE_MAX_IMAGE = prove
 (`!(f:A->real) s. FINITE s /\ ~(s = {})
                   ==> ?m. m IN s /\ !p. p IN s ==> f p <= f m`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `IMAGE (f:A->real) s` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let SUM_CUMULATIVE_DECREASING_LEMMA = prove
 (`!(psi:real->real) (x:A->real) (c:A->real) s S B0 b P m.
        (!u v. s <= u /\ u <= v /\ v <= S ==> psi v <= psi u) /\
        (!u. s <= u /\ u <= S ==> &0 <= psi u) /\
        &0 <= B0 /\ &0 <= b /\
        FINITE P /\ (!p. p IN P ==> s <= x p /\ x p <= S) /\
        (!p. p IN P ==> &0 <= c p) /\
        (!p. p IN P
             ==> sum {q | q IN P /\ x q <= x p} c <= B0 + b * (x p - s)) /\
        m IN P /\ (!p. p IN P ==> x p <= x m)
        ==> sum P (\p. c p * psi(x p)) <=
            (sum P c - (B0 + b * (x m - s))) * psi(x m) + B0 * psi s +
            b * real_integral (real_interval[s,x m]) psi`,
  MAP_EVERY X_GEN_TAC [`psi:real->real`; `x:A->real`; `c:A->real`;
                       `s:real`; `S:real`; `B0:real`; `b:real`] THEN
  X_GEN_TAC `P:A->bool` THEN WF_INDUCT_TAC `CARD(P:A->bool)` THEN
  X_GEN_TAC `m:A` THEN STRIP_TAC THEN
  ABBREV_TAC `Q = (P:A->bool) DELETE m` THEN
  POP_ASSUM(LABEL_TAC "Qdef") THEN
  SUBGOAL_THEN `FINITE(Q:A->bool) /\ (!p:A. p IN Q ==> p IN P) /\
                (!p:A. p IN P /\ ~(p = m) ==> p IN Q)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "Qdef" (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum P (\p. (c:A->real) p * psi((x:A->real) p)) =
    c m * psi(x m) + sum Q (\p. c p * psi(x p)) /\
    sum P c = c m + sum Q c`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [USE_THEN "Qdef" (SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[SUM_DELETE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= (x:A->real) m /\ x m <= S` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (psi:real->real)(x(m:A))` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `B0 * (psi:real->real)(x(m:A)) <= B0 * psi s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `Q:A->bool = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES] THEN
    MP_TAC(ISPECL [`psi:real->real`; `s:real`; `S:real`; `s:real`;
                   `(x:A->real) m`] REAL_INTEGRAL_DECREASING_LOWER) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `b * ((x:A->real) m - s) * psi(x m) <=
      b * real_integral (real_interval[s,x m]) psi`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:A->real`; `Q:A->bool`] FINITE_MAX_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(m2:A) IN P /\ s <= (x:A->real) m2 /\ x m2 <= x m`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Q:A->bool` o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [USE_THEN "Qdef" (SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[CARD_DELETE] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m2:A`) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `p:A` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {q | q IN P /\ (x:A->real) q <= x p} (c:A->real)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_DIFF; IN_ELIM_THM; SUBSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sum Q (c:A->real) <= B0 + b * ((x:A->real) m2 - s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {q | q IN P /\ (x:A->real) q <= x m2} (c:A->real)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_DIFF; IN_ELIM_THM; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sum Q (c:A->real) - (B0 + b * ((x:A->real) m2 - s))) * psi(x m2) <=
    (sum Q c - (B0 + b * (x m2 - s))) * psi(x m)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `a * p <= a * q <=> &0 <= --a * (p - q)`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_SUB_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real->real`; `s:real`; `S:real`; `(x:A->real) m2`;
                 `(x:A->real) m`] REAL_INTEGRAL_DECREASING_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `b * ((x:A->real) m - x m2) * psi(x m) <=
    b * real_integral (real_interval[x m2,x m]) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real->real`; `s:real`; `(x:A->real) m`;
                 `(x:A->real) m2`] REAL_INTEGRAL_COMBINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_DECREASING_SUB THEN
    MAP_EVERY EXISTS_TAC [`s:real`; `S:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `I1 = real_integral (real_interval[s,(x:A->real) m2]) psi` THEN
  ABBREV_TAC `I2 = real_integral (real_interval[(x:A->real) m2,x m]) psi` THEN
  ABBREV_TAC `SQ = sum Q (\p. (c:A->real) p * psi((x:A->real) p))` THEN
  ABBREV_TAC `CQ = sum Q (c:A->real)` THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN ASM_REAL_ARITH_TAC);;

let SUM_CUMULATIVE_DECREASING_BOUND = prove
 (`!(psi:real->real) (x:A->real) (c:A->real) s S B0 b P.
        s <= S /\
        (!u v. s <= u /\ u <= v /\ v <= S ==> psi v <= psi u) /\
        (!u. s <= u /\ u <= S ==> &0 <= psi u) /\
        &0 <= B0 /\ &0 <= b /\
        FINITE P /\ (!p. p IN P ==> s <= x p /\ x p <= S) /\
        (!p. p IN P ==> &0 <= c p) /\
        (!p. p IN P
             ==> sum {q | q IN P /\ x q <= x p} c <= B0 + b * (x p - s))
        ==> sum P (\p. c p * psi(x p)) <=
            B0 * psi s + b * real_integral (real_interval[s,S]) psi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= real_integral (real_interval[s,S]) (psi:real->real)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING_SUB THEN
      MAP_EVERY EXISTS_TAC [`s:real`; `S:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (psi:real->real) s` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `P:A->bool = {}` THENL
   [ASM_REWRITE_TAC[SUM_CLAUSES] THEN MATCH_MP_TAC REAL_LE_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`x:A->real`; `P:A->bool`] FINITE_MAX_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:A` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`psi:real->real`; `x:A->real`; `c:A->real`; `s:real`;
                 `S:real`; `B0:real`; `b:real`; `P:A->bool`; `m:A`]
         SUM_CUMULATIVE_DECREASING_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s <= (x:A->real) m /\ x m <= S` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sum P (c:A->real) <= B0 + b * ((x:A->real) m - s)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum {q | q IN P /\ (x:A->real) q <= x m} (c:A->real)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(sum P (c:A->real) - (B0 + b * ((x:A->real) m - s))) * psi(x m) <= &0`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= --a * b`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `b * real_integral (real_interval[s,(x:A->real) m]) psi <=
    b * real_integral (real_interval[s,S]) psi`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`psi:real->real`; `s:real`; `S:real`;
                   `(x:A->real) m`] REAL_INTEGRAL_COMBINE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INTEGRABLE_DECREASING_SUB THEN
      MAP_EVERY EXISTS_TAC [`s:real`; `S:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
    MATCH_MP_TAC REAL_INTEGRAL_POS THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_INTEGRABLE_DECREASING_SUB THEN
      MAP_EVERY EXISTS_TAC [`s:real`; `S:real`] THEN
      ASM_REWRITE_TAC[REAL_LE_REFL];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
