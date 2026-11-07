(* ========================================================================= *)
(* The limit formula at s = 1 for a general positive definite binary         *)
(* quadratic form and a general modulus k = k1 k2.                           *)
(*                                                                           *)
(* Purpose: for a form F = (a, b, c) with a > 0 and |D| = 4 a c - b^2 > 0, a *)
(* product k = k1 k2 of two distinct odd primes coprime to a and to |D|, and *)
(* any sum S of the series of the slices S_y(1) = qform_slice k a b c (&1) y *)
(* over y >= 1 (the sums over all integers x of chi_k(F(x,y)) / F(x,y)),     *)
(* abs S <= (4 pi / sqrt|D|) qform_kernel(eta) with eta =                    *)
(* exp(-pi sqrt|D| / (a k)) (QFORM_SLICE_BOUND), without any class number    *)
(* hypothesis. CLASSNO_SLICE_BOUND of Baker/classno_product.ml (the          *)
(* principal form of discriminant -d, k = 21, 33, for the class number one   *)
(* problem) is the special case; the general form covers the forms and       *)
(* moduli of the class number two problem (Baker, Transcendental Number      *)
(* Theory, Ch. 5, sec. 5).                                                   *)
(*                                                                           *)
(* Method: grouping x by residues m modulo k and the Poisson kernel          *)
(* identity: F(m + k n, y) = a k^2 ((n + t)^2 + w^2) with                    *)
(* t = (m + b y/(2a))/k, w = y sqrt|D| / (2 a k), so S_y(1) is a finite sum  *)
(* of Poisson kernels (QFORM_LIMIT_SLICE_EVAL) and differs from its main     *)
(* term 2 pi / (k y sqrt|D|) times the sum over m < k of chi_k(F(m,y)) by    *)
(* (4 pi / (y sqrt|D|)) q (1 + q) / (1 - q)^2, q = eta^y                     *)
(* (QFORM_LIMIT_SLICE_APPROX, CLASSNO_LIMIT_KERNEL_BOUND). The Ramanujan     *)
(* identity QFORM_LIMIT_RAMANUJAN: the sum over m < k of chi_k(F(m,y)) is    *)
(* chi_k(a) c_k(y), c_k(y) the Ramanujan sum, by completing the square       *)
(* 4 a F(m,y) = (2 a m + b y)^2 + |D| y^2 (QFORM_LIMIT_FORM_QCHAR), the      *)
(* substitution u = 2 a m + b y (a permutation of the residues modulo k),    *)
(* the Chinese remainder theorem (QFORM_LIMIT_PRODUCT_SUM) and, for each     *)
(* prime t dividing k, the sum over u < t of ((u^2 + N) | t), which is t - 1 *)
(* if t divides N and -1 otherwise (QFORM_LIMIT_PRIME_SUM: the number of     *)
(* square roots of w modulo t is 1 + (w | t), QFORM_LIMIT_SQRT_COUNT, and    *)
(* the pairs (u,v) with v^2 = u^2 + N are counted by s = v - u). The mean of *)
(* c_k(y)/y vanishes along the partial sums up to k N                        *)
(* (CLASSNO_LIMIT_MEAN_ZERO) and the errors of the slices are summed         *)
(* (QFORM_LIMIT_ASSEMBLY).                                                   *)
(*                                                                           *)
(* Main results: QFORM_SLICE_BOUND, QFORM_LIMIT_RAMANUJAN;                   *)
(* QFORM_LIMIT_SQRT_COUNT, QFORM_LIMIT_PRIME_SUM, QFORM_LIMIT_PRODUCT_SUM,   *)
(* QFORM_LIMIT_FORM_QCHAR, QFORM_LIMIT_POS, QFORM_LIMIT_POISSON,             *)
(* QFORM_LIMIT_SLICE_EVAL, QFORM_LIMIT_SLICE_ERROR, QFORM_LIMIT_ASSEMBLY;    *)
(* helper names CN_LIMIT_*.                                                  *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (qform), Baker/classno_chardefs.ml (qchar,    *)
(* qform_term, qform_slice, qform_kernel, QFORM_TERM_1),                     *)
(* Baker/classno_limit.ml (CLASSNO_LIMIT_KERNEL_BOUND,                       *)
(* CLASSNO_LIMIT_SUM_BLOCKS, CLASSNO_LIMIT_SUM_MOD_PERMUTE,                  *)
(* CLASSNO_LIMIT_LE_MULT, CLASSNO_LIMIT_MEAN_ZERO, CLASSNO_LIMIT_GEOM_TERM,  *)
(* CLASSNO_LIMIT_GP_BOUND), Baker/classno_poisson.ml (POISSON_KERNEL_SUM),   *)
(* Baker/classno_series.ml (CLASSNO_SERIES_QCHAR_BOUND,                      *)
(* CLASSNO_SERIES_REALLIM_SUBSEQ), Baker/classno_gauss.ml                    *)
(* (CLASSNO_GAUSS_CRT_VSUM); Library/jacobi.ml (JACOBI_PRIME, JACOBI_CONG,   *)
(* JACOBI_LMUL, JACOBI_RMUL, JACOBI_SQUARED), Library/primitive.ml           *)
(* (COUNT_ROOTS_MODULO_PRIMITIVE_GEN, PRIMITIVE_ROOT_MODULO_PRIME,           *)
(* EULER_CRITERION), Library/pocklington.ml (CONG_EXP, PHI_PRIME),           *)
(* Library/prime.ml (PRIME_COPRIME_LT, DISTINCT_PRIME_COPRIME).              *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files, 100/dirichlet.ml before *)
(* Multivariate/gamma.ml), so that the file also loads alone.                *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Multivariate/gamma.ml";;
needs "Baker/classno_poisson.ml";;
needs "Baker/classno_limit.ml";;
needs "Baker/classno_gauss.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The form: completing the square and positivity.                           *)
(* ------------------------------------------------------------------------- *)

let QFORM_LIMIT_4A = prove
 (`!a b c x y. &4 * a * qform a b c x y =
               (&2 * a * x + b * y) pow 2 + (&4 * a * c - b pow 2) * y pow 2`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_LIMIT_POS = prove
 (`!a b c x y. &0 < a /\ &0 < &4 * a * c - b pow 2
               ==> &0 <= qform a b c x y /\
                   (~(y = &0) ==> &0 < qform a b c x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_LIMIT_4A) THEN
  SPEC_TAC(`qform a b c x y`, `q:int`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&0:int) <= (&2 * a * x + b * y) pow 2 /\
                (&0:int) <= (&4 * a * c - b pow 2) * y pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_LE_POW_2] THEN MATCH_MP_TAC INT_LE_MUL THEN
    ASM_SIMP_TAC[INT_LT_IMP_LE; INT_LE_POW_2];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`&0:int`; `q:int`; `&4 * a:int`] INT_LE_LMUL_EQ) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_INT_ARITH_TAC;
    DISCH_TAC THEN
    SUBGOAL_THEN `(&0:int) < (&4 * a * c - b pow 2) * y pow 2` ASSUME_TAC
    THENL
     [MATCH_MP_TAC INT_LT_MUL THEN ASM_REWRITE_TAC[INT_POW_2; INT_LT_SQUARE];
      ALL_TAC] THEN
    MP_TAC(SPECL [`&0:int`; `q:int`; `&4 * a:int`] INT_LT_LMUL_EQ) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The sums of ((u^2 + N) | t) over u < t for an odd prime t.                *)
(* ------------------------------------------------------------------------- *)

(* The number of square roots of w modulo an odd prime t is 1 + (w | t);     *)
(* for t not dividing w the roots of x^2 = w modulo t are counted with a     *)
(* primitive root (COUNT_ROOTS_MODULO_PRIMITIVE_GEN: 2 or 0 by the Euler     *)
(* criterion).                                                               *)

let QFORM_LIMIT_SQRT_COUNT = prove
 (`!t w. prime t /\ ~(t = 2)
         ==> sum(0..t - 1) (\v. if (v EXP 2 == w) (mod t) then &1 else &0) =
             &1 + qchar t w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `3 <= t /\ ODD t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; PRIME_ODD;
                  ARITH_RULE `2 <= t /\ ~(t = 2) ==> 3 <= t`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_0; qchar; JACOBI_PRIME;
               ARITH_RULE `3 <= t ==> (v <= t - 1 <=> v < t)`] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{v | v < t /\ (v EXP 2 == w) (mod t)} = {0}` SUBST1_TAC
    THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `v:num` THEN
      ASM_SIMP_TAC[NUMBER_RULE
       `(t:num) divides w ==> ((x == w) (mod t) <=> t divides x)`;
       PRIME_DIVEXP_EQ; ARITH_EQ] THEN
      ASM_MESON_TAC[DIVIDES_LE; DIVIDES_0; NOT_LT; LT_NZ;
                    ARITH_RULE `3 <= t ==> 0 < t`];
      REWRITE_TAC[CARD_SING; int_of_num_th] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `w:num`; `2`] COUNT_ROOTS_MODULO_PRIMITIVE_GEN) THEN
  ASM_SIMP_TAC[PHI_PRIME; PRIME_COPRIME_EQ; ARITH_EQ; PRIME_IMP_NZ] THEN
  SUBGOAL_THEN `gcd(2,t - 1) = 2` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[GSYM DIVIDES_GCD_LEFT; DIVIDES_2; EVEN_SUB; GSYM NOT_ODD;
                    ARITH];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PRIMITIVE_ROOT_MODULO_PRIME]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP HAS_SIZE_CARD) THEN
  ASM_SIMP_TAC[EULER_CRITERION] THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_of_num_th; int_neg_th] THEN
  REAL_ARITH_TAC);;

let QFORM_LIMIT_SUM_NONZERO = prove
 (`!n. 1 <= n ==> sum(0..n - 1) (\s. if s = 0 then &0 else &1) = &n - &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. (if s = 0 then &0 else &1) = &1 - (if s = 0 then &1 else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG; SUM_DELTA; IN_NUMSEG; LE_0] THEN
  ASM_SIMP_TAC[SUB_ADD; SUB_0] THEN REAL_ARITH_TAC);;

(* The sum over u < t of ((u^2 + N) | t): t - 1 if t divides N, else -1      *)
(* (the pairs (u,v) with v^2 = u^2 + N are counted by s = v - u: for         *)
(* s <> 0 there is exactly one u with 2 s u + s^2 = N modulo t).             *)

let QFORM_LIMIT_PRIME_SUM = prove
 (`!t N. prime t /\ ~(t = 2)
         ==> sum(0..t - 1) (\u. qchar t (u EXP 2 + N)) =
             if t divides N then &t - &1 else --(&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `3 <= t` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(t = 2)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s <= t - 1 ==> (coprime(s,t) <=> ~(s = 0))` ASSUME_TAC
  THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN ASM_CASES_TAC `s = 0` THEN
    ASM_REWRITE_TAC[COPRIME_0] THENL
     [UNDISCH_TAC `3 <= t` THEN ARITH_TAC;
      MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(s = 0)`; `s <= t - 1`; `3 <= t`] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= t` ASSUME_TAC THENL
   [UNDISCH_TAC `3 <= t` THEN ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [TRANS_TAC EQ_TRANS `sum(0..t - 1) (\s. if s = 0 then &0 else &1)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[QFORM_LIMIT_SUM_NONZERO]] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
    REWRITE_TAC[qchar] THEN
    SUBGOAL_THEN `jacobi(u EXP 2 + N,t) = jacobi(u EXP 2,t)` SUBST1_TAC THENL
     [MATCH_MP_TAC JACOBI_CONG THEN UNDISCH_TAC `t divides N` THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[JACOBI_SQUARED] THEN ASM_SIMP_TAC[] THEN
    ASM_CASES_TAC `u = 0` THEN ASM_REWRITE_TAC[int_of_num_th];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. sum(0..t - 1) (\v. if (v EXP 2 == w) (mod t) then &1 else &0) =
        &1 + qchar t w`
  ASSUME_TAC THENL [ASM_SIMP_TAC[QFORM_LIMIT_SQRT_COUNT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. qchar t (u EXP 2 + N) =
        sum(0..t - 1) (\s. if (((s + u) MOD t) EXP 2 == u EXP 2 + N) (mod t)
                           then &1 else &0) - &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `u:num` THEN
    MP_TAC(ISPECL [`\v. if (v EXP 2 == u EXP 2 + N) (mod t) then &1 else &0`;
                   `t:num`; `1`; `u:num`] CLASSNO_LIMIT_SUM_MOD_PERMUTE) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; COPRIME_1] THEN
    DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; SUM_CONST_NUMSEG] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SUM_SWAP_NUMSEG] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s. s <= t - 1
        ==> sum(0..t - 1)
             (\u. if (((s + u) MOD t) EXP 2 == u EXP 2 + N) (mod t)
                  then &1 else &0) =
            if s = 0 then &0 else &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `u:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN
      REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
      UNDISCH_TAC `~(t divides N)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(u MOD t == u) (mod t)` MP_TAC THENL
       [REWRITE_TAC[CONG_LMOD; CONG_REFL]; ALL_TAC] THEN
      UNDISCH_TAC `((u MOD t) EXP 2 == u EXP 2 + N) (mod t)` THEN
      SPEC_TAC(`u MOD t`, `a:num`) THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!u. (((s + u) MOD t) EXP 2 == u EXP 2 + N) (mod t) <=>
          (((2 * s) * u + s EXP 2) MOD t == N) (mod t)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN
       `((s + u) MOD t == s + u) (mod t) /\
        (((2 * s) * u + s EXP 2) MOD t == (2 * s) * u + s EXP 2) (mod t)`
      MP_TAC THENL [REWRITE_TAC[CONG_LMOD; CONG_REFL]; ALL_TAC] THEN
      SPEC_TAC(`(s + u) MOD t`, `a:num`) THEN
      SPEC_TAC(`((2 * s) * u + s EXP 2) MOD t`, `b:num`) THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`\z. if (z == N) (mod t) then &1 else &0`; `t:num`;
                   `2 * s`; `s EXP 2`] CLASSNO_LIMIT_SUM_MOD_PERMUTE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[COPRIME_LMUL; COPRIME_2] THEN CONJ_TAC THENL
       [MP_TAC(SPEC `t:num` PRIME_ODD) THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[]];
      DISCH_THEN SUBST1_TAC] THEN
    TRANS_TAC EQ_TRANS `sum(0..t - 1) (\z. if z = N MOD t then &1 else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `z:num` THEN STRIP_TAC THEN
      REWRITE_TAC[CONG] THEN
      SUBGOAL_THEN `z MOD t = z` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOD_LT THEN
      MAP_EVERY UNDISCH_TAC [`z <= t - 1`; `3 <= t`] THEN ARITH_TAC;
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0] THEN
      SUBGOAL_THEN `N MOD t <= t - 1` (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC(SPECL [`N:num`; `t:num`] MOD_LT_EQ) THEN
      UNDISCH_TAC `3 <= t` THEN ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `sum(0..t - 1) (\s. if s = 0 then &0 else &1) - &((t - 1 + 1) - 0) * &1` THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[QFORM_LIMIT_SUM_NONZERO; SUB_ADD; SUB_0] THEN
      REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Chinese remainder theorem for k = k1 k2.                              *)
(* ------------------------------------------------------------------------- *)

(* A real version of CLASSNO_GAUSS_CRT_VSUM.                                 *)

let QFORM_LIMIT_CRT_SUM = prove
 (`!f:num->real m1 m2.
        coprime(m1,m2) /\ ~(m1 = 0) /\ ~(m2 = 0) /\
        (!a. f(a + m1 * m2) = f a)
        ==> sum(0..m1 * m2 - 1) f =
            sum(0..m1 - 1)
                (\a1. sum(0..m2 - 1) (\a2. f(a1 * m2 + a2 * m1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`lift o (f:num->real)`; `m1:num`; `m2:num`]
    CLASSNO_GAUSS_CRT_VSUM) THEN
  ASM_REWRITE_TAC[o_THM] THEN
  DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; LIFT_DROP; ETA_AX]);;

let QFORM_LIMIT_QCHAR_CONG = prove
 (`!t x x' N. (x == x') (mod t)
              ==> qchar t (x EXP 2 + N) = qchar t (x' EXP 2 + N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qchar] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC JACOBI_CONG THEN MATCH_MP_TAC CONG_ADD THEN
  REWRITE_TAC[CONG_REFL] THEN MATCH_MP_TAC CONG_EXP THEN ASM_REWRITE_TAC[]);;

let QFORM_LIMIT_PRODUCT_SUM = prove
 (`!k k1 k2 N.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k
     ==> sum(0..k - 1) (\u. qchar k (u EXP 2 + N)) =
         (if k1 divides N then &k1 - &1 else --(&1)) *
         (if k2 divides N then &k2 - &1 else --(&1))`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `k = k1 * k2` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `ODD k1 /\ ODD k2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ODD(k1 * k2)` THEN REWRITE_TAC[ODD_MULT]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k1 = 0) /\ ~(k1 = 2) /\ ~(k2 = 0) /\ ~(k2 = 2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `ODD k1`; UNDISCH_TAC `ODD k1`;
      UNDISCH_TAC `ODD k2`; UNDISCH_TAC `ODD k2`] THEN
    ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(k1,k2)` ASSUME_TAC THENL
   [MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. qchar (k1 * k2) n = qchar k1 n * qchar k2 n`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[qchar; JACOBI_RMUL; int_mul_th]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. qchar k1 (u EXP 2 + N) * qchar k2 (u EXP 2 + N)`;
                 `k1:num`; `k2:num`] QFORM_LIMIT_CRT_SUM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN BINOP_TAC THEN MATCH_MP_TAC QFORM_LIMIT_QCHAR_CONG THEN
    CONV_TAC NUMBER_RULE;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!a1 a2. qchar k1 ((a1 * k2 + a2 * k1) EXP 2 + N) =
            qchar k1 ((a1 * k2) EXP 2 + N) /\
            qchar k2 ((a1 * k2 + a2 * k1) EXP 2 + N) =
            qchar k2 ((a2 * k1) EXP 2 + N)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC QFORM_LIMIT_QCHAR_CONG THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN
  SUBGOAL_THEN
   `!t r. prime t /\ ~(t = 2) /\ coprime(r,t)
          ==> sum(0..t - 1) (\a. qchar t ((a * r) EXP 2 + N)) =
              if t divides N then &t - &1 else --(&1)`
  (fun th -> BINOP_TAC THEN MATCH_MP_TAC th THEN
             ASM_MESON_TAC[COPRIME_SYM]) THEN
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `sum(0..t - 1) (\a. (\u. qchar t (u EXP 2 + N)) ((r * a + 0) MOD t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC QFORM_LIMIT_QCHAR_CONG THEN REWRITE_TAC[CONG_RMOD] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u. qchar t (u EXP 2 + N)`; `t:num`; `r:num`; `0`]
    CLASSNO_LIMIT_SUM_MOD_PERMUTE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `t:num` PRIME_GE_2) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[QFORM_LIMIT_PRIME_SUM]);;

(* ------------------------------------------------------------------------- *)
(* The Ramanujan identity for a general form: completing the square,         *)
(* 4 a F(m,y) = (2 a m + b y)^2 + |D| y^2, and u = 2 a m + b y modulo k.     *)
(* ------------------------------------------------------------------------- *)

let QFORM_LIMIT_DIVIDES_TRANSFER = prove
 (`!t k d y. prime t /\ t divides k /\ coprime(k,d)
             ==> (t divides (d * y EXP 2) <=> t divides y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(t divides d)` ASSUME_TAC THENL
   [DISCH_TAC THEN SUBGOAL_THEN `t = 1` MP_TAC THENL
     [REWRITE_TAC[GSYM DIVIDES_ONE] THEN
      MAP_EVERY UNDISCH_TAC
       [`coprime(k:num,d)`; `t divides k`; `t divides d`] THEN
      CONV_TAC NUMBER_RULE;
      ASM_MESON_TAC[PRIME_1]];
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; PRIME_DIVEXP_EQ; ARITH_EQ]]);;

let QFORM_LIMIT_FORM_QCHAR = prove
 (`!k a b c m y.
     ODD k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ coprime(k,num_of_int a)
     ==> qchar k (num_of_int(qform a b c (&m) (&y))) =
         qchar k (num_of_int a) *
         qchar k ((((2 * num_of_int a) * m + num_of_int(b rem &k) * y) MOD k)
                  EXP 2 + num_of_int(&4 * a * c - b pow 2) * y EXP 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ODD k` THEN ASM_REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `&m:int`; `&y:int`]
    QFORM_LIMIT_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[qchar; GSYM int_mul_th] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `jacobi((((2 * num_of_int a) * m + num_of_int(b rem &k) * y) MOD k)
           EXP 2 + num_of_int(&4 * a * c - b pow 2) * y EXP 2,k) =
    jacobi(4 * num_of_int a * num_of_int(qform a b c (&m) (&y)),k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC JACOBI_CONG THEN
    REWRITE_TAC[num_congruent; GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL;
                GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_REM] THEN
    SUBGOAL_THEN
     `&(num_of_int a) = a /\
      &(num_of_int(qform a b c (&m) (&y))) = qform a b c (&m) (&y) /\
      &(num_of_int(&4 * a * c - b pow 2)) = &4 * a * c - b pow 2 /\
      &(num_of_int(b rem &k)) = b rem &k`
    (fun th -> REWRITE_TAC[th]) THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
      ASM_SIMP_TAC[INT_LT_IMP_LE; INT_REM_POS; INT_OF_NUM_EQ];
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `&m:int`; `&y:int`]
      QFORM_LIMIT_4A) THEN
    SUBGOAL_THEN
     `(((&2 * a) * &m + b rem &k * &y) rem &k ==
       (&2 * a) * &m + b rem &k * &y) (mod &k) /\
      (b rem &k == b) (mod &k)`
    MP_TAC THENL [REWRITE_TAC[INT_CONG_LREM; INT_CONG_REFL]; ALL_TAC] THEN
    SPEC_TAC(`((&2 * a) * &m + b rem &k * &y) rem &k`, `u:int`) THEN
    SPEC_TAC(`b rem &k`, `bk:int`) THEN
    SPEC_TAC(`qform a b c (&m) (&y)`, `q:int`) THEN
    CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[JACOBI_LMUL] THEN
  SUBGOAL_THEN `jacobi(4,k) = &1 /\
                jacobi(num_of_int a,k) * jacobi(num_of_int a,k) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM JACOBI_LMUL; ARITH_RULE `4 = 2 EXP 2`; GSYM EXP_2;
                JACOBI_SQUARED] THEN
    ASM_REWRITE_TAC[COPRIME_2] THEN ASM_MESON_TAC[COPRIME_SYM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_MUL_LID] THEN
  UNDISCH_TAC `jacobi(num_of_int a,k) * jacobi(num_of_int a,k) = &1` THEN
  SPEC_TAC(`jacobi(num_of_int a,k)`, `ja:int`) THEN
  SPEC_TAC(`jacobi(num_of_int(qform a b c (&m) (&y)),k)`, `jq:int`) THEN
  CONV_TAC INT_RING);;

let QFORM_LIMIT_RAMANUJAN = prove
 (`!k k1 k2 a b c y.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k /\
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\
     coprime(k,num_of_int a) /\ coprime(k,num_of_int(&4 * a * c - b pow 2))
     ==> sum(0..k - 1) (\m. qchar k (num_of_int(qform a b c (&m) (&y)))) =
         qchar k (num_of_int a) *
         (&1 - &k1 * (if k1 divides y then &1 else &0) -
          &k2 * (if k2 divides y then &1 else &0) +
          &k * (if k divides y then &1 else &0))`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `k = k1 * k2` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN `1 <= k1 * k2` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(k = 0) ==> 1 <= k`) THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `ODD(k1 * k2)` THEN REWRITE_TAC[th]) THEN
    REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  MP_TAC(GEN `m:num` (SPECL [`k1 * k2`; `a:int`; `b:int`; `c:int`; `m:num`;
                             `y:num`] QFORM_LIMIT_FORM_QCHAR)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th; SUM_LMUL]) THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL
   [`\u. qchar (k1 * k2)
          (u EXP 2 + num_of_int(&4 * a * c - b pow 2) * y EXP 2)`;
    `k1 * k2`; `2 * num_of_int a`; `num_of_int(b rem &(k1 * k2)) * y`]
   CLASSNO_LIMIT_SUM_MOD_PERMUTE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COPRIME_LMUL; COPRIME_2] THEN ASM_MESON_TAC[COPRIME_SYM];
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`k1 * k2`; `k1:num`; `k2:num`;
                `num_of_int(&4 * a * c - b pow 2) * y EXP 2`]
    QFORM_LIMIT_PRODUCT_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `coprime(k1,k2)` ASSUME_TAC THENL
   [MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(k1 divides num_of_int(&4 * a * c - b pow 2) * y EXP 2 <=>
     k1 divides y) /\
    (k2 divides num_of_int(&4 * a * c - b pow 2) * y EXP 2 <=>
     k2 divides y) /\
    (k1 * k2 divides y <=> k1 divides y /\ k2 divides y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC QFORM_LIMIT_DIVIDES_TRANSFER THEN EXISTS_TAC `k1 * k2` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE;
      MATCH_MP_TAC QFORM_LIMIT_DIVIDES_TRANSFER THEN EXISTS_TAC `k1 * k2` THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE;
      UNDISCH_TAC `coprime(k1,k2)` THEN CONV_TAC NUMBER_RULE];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ASM_CASES_TAC `k1 divides y` THEN ASM_CASES_TAC `k2 divides y` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The slices of a general form in Poisson form,                             *)
(* F(x,y) = a k^2 ((x/k + b y/(2 a k))^2 + (y sqrt|D| / (2 a k))^2).         *)
(* ------------------------------------------------------------------------- *)

let QFORM_LIMIT_REAL_POS = prove
 (`!a b c. &0 < a /\ &0 < &4 * a * c - b pow 2
           ==> &0 < real_of_int a /\
               &0 < real_of_int(&4 * a * c - b pow 2) /\
               &0 < sqrt(real_of_int(&4 * a * c - b pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < real_of_int a /\ &0 < real_of_int(&4 * a * c - b pow 2)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM int_of_num_th; GSYM int_lt]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LT]);;

let QFORM_LIMIT_POISSON = prove
 (`!k a b c x y.
     ~(k = 0) /\ &0 < a /\ &0 < &4 * a * c - b pow 2
     ==> real_of_int(qform a b c x (&y)) =
         real_of_int a * &k pow 2 *
         ((real_of_int x / &k +
           real_of_int b * &y / (&2 * real_of_int a * &k)) pow 2 +
          (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
           (&2 * real_of_int a * &k)) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `sqrt(real_of_int(&4 * a * c - b pow 2)) pow 2 =
                real_of_int(&4 * a * c - b pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_DIV; REAL_POW_MUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(&k:real = &0)` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  UNDISCH_TAC `&0 < real_of_int a` THEN
  REWRITE_TAC[qform; int_add_th; int_mul_th; int_pow_th; int_sub_th;
              int_of_num_th] THEN
  CONV_TAC REAL_FIELD);;

let QFORM_LIMIT_TERM_BOUND = prove
 (`!k a b c x y.
     &0 < qform a b c x y
     ==> abs(qform_term k a b c (&1) x y) <= inv(real_of_int(qform a b c x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[QFORM_TERM_1; real_div; REAL_ABS_MUL] THEN
  SUBGOAL_THEN `&0 < real_of_int(qform a b c x y)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM int_of_num_th; GSYM int_lt]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_SIMP_TAC[CLASSNO_SERIES_QCHAR_BOUND; REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let QFORM_LIMIT_QCHAR_PERIODIC = prove
 (`!k a b c x x' y.
     (x == x') (mod &k) /\ &0 <= qform a b c x y /\ &0 <= qform a b c x' y
     ==> qchar k (num_of_int(qform a b c x y)) =
         qchar k (num_of_int(qform a b c x' y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qchar] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC JACOBI_CONG THEN REWRITE_TAC[num_congruent] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN REWRITE_TAC[qform] THEN
  UNDISCH_TAC `(x:int == x') (mod &k)` THEN CONV_TAC INTEGER_RULE);;

(* The slices converge (comparison with the Poisson series for k = 1).       *)

let QFORM_LIMIT_SLICE_SUMMABLE = prove
 (`!k a b c y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y
     ==> real_summable (from 0)
          (\n. qform_term k a b c (&1) (&n) (&y) +
               qform_term k a b c (&1) (--(&n) - &1) (&y))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC
   `\n. inv(real_of_int a) *
        (inv((&n + real_of_int b * &y / (&2 * real_of_int a)) pow 2 +
             (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
              (&2 * real_of_int a)) pow 2) +
         inv((real_of_int b * &y / (&2 * real_of_int a) - (&n + &1)) pow 2 +
             (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
              (&2 * real_of_int a)) pow 2))` THEN
  SUBGOAL_THEN `~(&y:int = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= y` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN REWRITE_TAC[real_summable] THEN
    EXISTS_TAC
     `pi / (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
            (&2 * real_of_int a)) *
      (exp(&2 * pi * (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                      (&2 * real_of_int a))) -
       exp(--(&2 * pi * (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                         (&2 * real_of_int a))))) /
      (exp(&2 * pi * (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                      (&2 * real_of_int a))) +
       exp(--(&2 * pi * (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                         (&2 * real_of_int a)))) -
       &2 * cos(&2 * pi * (real_of_int b * &y / (&2 * real_of_int a))))` THEN
    MATCH_MP_TAC POISSON_KERNEL_SUM THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= y` THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&0 < real_of_int a` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs a <= c /\ abs b <= e ==> abs(a + b) <= c + e`) THEN
  MP_TAC(SPECL [`1`; `a:int`; `b:int`; `c:int`] QFORM_LIMIT_POISSON) THEN
  ASM_REWRITE_TAC[ARITH_EQ; REAL_POW_ONE; REAL_DIV_1; REAL_MUL_LID;
                  REAL_MUL_RID] THEN
  DISCH_TAC THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) QFORM_LIMIT_TERM_BOUND o lhand o snd)
    THEN
  ASM_SIMP_TAC[QFORM_LIMIT_POS] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_neg_th; REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_ARITH `--n - &1 + t = t - (n + &1)`]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of a slice: residues modulo k and the Poisson kernel.          *)
(* ------------------------------------------------------------------------- *)

(* The terms x = k j + m and x = m - k (j + 1) of a slice in Poisson form,   *)
(* t = (m + b y/(2a))/k, w = y sqrt|D| / (2 a k); the partial sums up to     *)
(* k (N + 1).                                                                *)

let QFORM_LIMIT_TERM_PAIR = prove
 (`!k a b c y m j.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y /\ m <= k - 1
     ==> qform_term k a b c (&1) (&(k * j + m)) (&y) +
         qform_term k a b c (&1) (--(&(k * j + ((k - 1) - m))) - &1) (&y) =
         qchar k (num_of_int(qform a b c (&m) (&y))) /
         (real_of_int a * &k pow 2) *
         (inv((&j + (&m + real_of_int b * &y / (&2 * real_of_int a)) / &k)
              pow 2 +
              (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
               (&2 * real_of_int a * &k)) pow 2) +
          inv(((&m + real_of_int b * &y / (&2 * real_of_int a)) / &k -
               (&j + &1)) pow 2 +
              (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
               (&2 * real_of_int a * &k)) pow 2))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `--(&(k * j + ((k - 1) - m))) - &1:int = &m - &k * (&j + &1)`
  SUBST1_TAC THENL
   [MP_TAC(ARITH_RULE `1 <= k /\ m <= k - 1
                       ==> (k * j + ((k - 1) - m)) + m + 1 = k * (j + 1)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `int_of_num`) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(&y:int = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= y` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `qchar k (num_of_int(qform a b c (&(k * j + m)) (&y))) =
    qchar k (num_of_int(qform a b c (&m) (&y))) /\
    qchar k (num_of_int(qform a b c (&m - &k * (&j + &1)) (&y))) =
    qchar k (num_of_int(qform a b c (&m) (&y)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC QFORM_LIMIT_QCHAR_PERIODIC THEN
    ASM_SIMP_TAC[QFORM_LIMIT_POS] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[QFORM_TERM_1] THEN
  ASM_SIMP_TAC[QFORM_LIMIT_POISSON] THEN
  REWRITE_TAC[int_of_num_th; int_sub_th; int_mul_th; int_add_th] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `~(&k:real = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(real_of_int a = &0)` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < real_of_int a` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(&k:real = &0) /\ ~(ra = &0)
    ==> (&k * &j + &m) / &k + rb * &y / (&2 * ra * &k) =
        &j + (&m + rb * &y / (&2 * ra)) / &k /\
        (&m - &k * (&j + &1)) / &k + rb * &y / (&2 * ra * &k) =
        (&m + rb * &y / (&2 * ra)) / &k - (&j + &1)`] THEN
  SPEC_TAC(`qchar k (num_of_int(qform a b c (&m) (&y)))`, `z:real`) THEN
  SPEC_TAC(`&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
            (&2 * real_of_int a * &k)`, `w:real`) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
  REAL_ARITH_TAC);;

let QFORM_LIMIT_SLICE_PARTIAL = prove
 (`!k a b c y N.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y
     ==> sum(0..k * N + (k - 1))
          (\n. qform_term k a b c (&1) (&n) (&y) +
               qform_term k a b c (&1) (--(&n) - &1) (&y)) =
         sum(0..k - 1)
          (\m. qchar k (num_of_int(qform a b c (&m) (&y))) /
               (real_of_int a * &k pow 2) *
               sum(0..N)
                (\j. inv((&j + (&m + real_of_int b * &y /
                                     (&2 * real_of_int a)) / &k) pow 2 +
                         (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                          (&2 * real_of_int a * &k)) pow 2) +
                     inv(((&m + real_of_int b * &y / (&2 * real_of_int a)) /
                          &k - (&j + &1)) pow 2 +
                         (&y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                          (&2 * real_of_int a * &k)) pow 2)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN ASM_SIMP_TAC[CLASSNO_LIMIT_SUM_BLOCKS] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SUM_REFLECT] THEN
  REWRITE_TAC[LT; SUB_0] THEN
  REWRITE_TAC[GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC QFORM_LIMIT_TERM_PAIR THEN
  ASM_REWRITE_TAC[]);;

(* The slice as a finite sum of Poisson kernels.                             *)

let QFORM_LIMIT_SLICE_EVAL = prove
 (`!k a b c y w.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y /\
     w = &y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
         (&2 * real_of_int a * &k)
     ==> qform_slice k a b c (&1) y =
         sum(0..k - 1)
          (\m. qchar k (num_of_int(qform a b c (&m) (&y))) /
               (real_of_int a * &k pow 2) *
               (pi / w * (exp(&2 * pi * w) - exp(--(&2 * pi * w))) /
                         (exp(&2 * pi * w) + exp(--(&2 * pi * w)) -
                          &2 * cos(&2 * pi *
                                   ((&m + real_of_int b * &y /
                                          (&2 * real_of_int a)) / &k)))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `y:num`]
    QFORM_LIMIT_SLICE_SUMMABLE) THEN
  ASM_REWRITE_TAC[GSYM REAL_SUMS_INFSUM; GSYM qform_slice] THEN
  REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC
   `\N. sum(0..k * N + (k - 1))
         (\n. qform_term k a b c (&1) (&n) (&y) +
              qform_term k a b c (&1) (--(&n) - &1) (&y))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`\n. sum(0..n) (\n. qform_term k a b c (&1) (&n) (&y) +
                          qform_term k a b c (&1) (--(&n) - &1) (&y))`;
      `qform_slice k a b c (&1) y`; `\N. k * N + (k - 1)`]
     CLASSNO_SERIES_REALLIM_SUBSEQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    GEN_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `n <= k * n ==> n <= k * n + (k - 1)`) THEN
    ASM_SIMP_TAC[CLASSNO_LIMIT_LE_MULT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[QFORM_LIMIT_SLICE_PARTIAL] THEN
  MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN
  MP_TAC(SPECL [`(&m + real_of_int b * &y / (&2 * real_of_int a)) / &k`;
                `w:real`] POISSON_KERNEL_SUM) THEN
  REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= y` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
  UNDISCH_TAC `1 <= k` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A slice is its main term up to an exponentially small error.              *)
(* ------------------------------------------------------------------------- *)

let QFORM_LIMIT_SLICE_APPROX = prove
 (`!k a b c y.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y
     ==> abs(qform_slice k a b c (&1) y -
             (&2 * pi) /
             (&k * &y * sqrt(real_of_int(&4 * a * c - b pow 2))) *
             sum(0..k - 1) (\m. qchar k (num_of_int(qform a b c (&m) (&y)))))
         <= (&4 * pi) / (&y * sqrt(real_of_int(&4 * a * c - b pow 2))) *
            (exp(--(pi * &y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                    (real_of_int a * &k))) *
             (&1 + exp(--(pi * &y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                          (real_of_int a * &k))))) /
            (&1 - exp(--(pi * &y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                         (real_of_int a * &k)))) pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `w = &y * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                  (&2 * real_of_int a * &k)` THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `y:num`; `w:real`]
    QFORM_LIMIT_SLICE_EVAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `sd = sqrt(real_of_int(&4 * a * c - b pow 2))` THEN
  ABBREV_TAC `ra = real_of_int a` THEN
  SUBGOAL_THEN `&0 < &k /\ &0 < &y` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= k`; `1 <= y`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < w` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pi * &y * sd / (ra * &k) = &2 * pi * w` SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &k`; `&0 < ra`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * pi) / (&k * &y * sd) = pi / w / (ra * &k pow 2)`
  SUBST1_TAC THENL
   [EXPAND_TAC "w" THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &k`; `&0 < &y`; `&0 < sd`; `&0 < ra`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(GEN `t:real` (SPECL [`t:real`; `w:real`]
    CLASSNO_LIMIT_KERNEL_BOUND)) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = exp(--(&2 * pi * w))` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  SUBGOAL_THEN `&0 < inv(ra * &k pow 2)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..k - 1) (\m. inv(ra * &k pow 2) *
                 (pi / w * (&2 * q * (&1 + q)) / (&1 - q) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH
     `z / kk * g - p / kk * z = (z * inv kk) * (g - p)`] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[CLASSNO_SERIES_QCHAR_BOUND; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG] THEN
  ASM_SIMP_TAC[SUB_0; SUB_ADD] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  EXPAND_TAC "w" THEN
  SUBGOAL_THEN `~(&1 - q = &0)` MP_TAC THENL
   [EXPAND_TAC "q" THEN
    MATCH_MP_TAC(REAL_ARITH `x < &1 ==> ~(&1 - x = &0)`) THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT; REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[PI_POS];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < &k`; `&0 < &y`; `&0 < sd`; `&0 < ra`] THEN
  CONV_TAC REAL_FIELD);;

(* The error of a slice is at most                                           *)
(* (4 pi / sqrt|D|) (1 + eta) / (1 - eta)^2 eta^y.                           *)

let QFORM_LIMIT_SLICE_ERROR = prove
 (`!k a b c y cm.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y /\
     sum(0..k - 1) (\m. qchar k (num_of_int(qform a b c (&m) (&y)))) = cm
     ==> abs(qform_slice k a b c (&1) y -
             (&2 * pi) / (&k * sqrt(real_of_int(&4 * a * c - b pow 2))) *
             cm / &y)
         <= (&4 * pi) / sqrt(real_of_int(&4 * a * c - b pow 2)) *
            (&1 + exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                         (real_of_int a * &k)))) /
            (&1 - exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                         (real_of_int a * &k)))) pow 2 *
            exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                   (real_of_int a * &k))) pow y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `y:num`]
    QFORM_LIMIT_SLICE_APPROX) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `sd = sqrt(real_of_int(&4 * a * c - b pow 2))` THEN
  ABBREV_TAC `ra = real_of_int a` THEN
  SUBGOAL_THEN `&0 < &k /\ &1 <= &y` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= k`; `1 <= y`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 * pi) / (&k * &y * sd) * cm =
                (&2 * pi) / (&k * sd) * cm / &y`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < &k`; `&1 <= &y`; `&0 < sd`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  SUBGOAL_THEN `exp(--(pi * &y * sd / (ra * &k))) =
                exp(--(pi * sd / (ra * &k))) pow y`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_EXP_N] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eta = exp(--(pi * sd / (ra * &k)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT; REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 * pi) / (&y * sd) *
    (eta pow y * (&1 + eta pow y)) / (&1 - eta pow y) pow 2 =
    (&4 * pi) / sd *
    ((eta pow y * (&1 + eta pow y)) / (&1 - eta pow y) pow 2 / &y)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= &y`; `&0 < sd`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN MP_TAC PI_POS THEN
    UNDISCH_TAC `&0 < sd` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CLASSNO_LIMIT_GEOM_TERM THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
  MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  UNDISCH_TAC `1 <= y` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Summing the errors over the slices; the bound of the limit formula.       *)
(* ------------------------------------------------------------------------- *)

(* Assembly for k = p q: the main terms cancel along the partial sums up to  *)
(* k N, the errors sum to at most (4 pi / sqrt|D|) qform_kernel(eta).        *)

let QFORM_LIMIT_ASSEMBLY = prove
 (`!k p q a b c S.
     k = p * q /\ 1 <= p /\ 1 <= q /\
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\
     (!y. sum(0..k - 1) (\m. qchar k (num_of_int(qform a b c (&m) (&y)))) =
          qchar k (num_of_int a) *
          (&1 - &p * (if p divides y then &1 else &0) -
           &q * (if q divides y then &1 else &0) +
           &k * (if k divides y then &1 else &0))) /\
     (qform_slice k a b c (&1) real_sums S) (from 1)
     ==> abs S <=
         &4 * pi / sqrt(real_of_int(&4 * a * c - b pow 2)) *
         qform_kernel(exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                          (real_of_int a * &k))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p`; `1 <= q`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `p:num`; `q:num`] CLASSNO_LIMIT_MEAN_ZERO) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `k = p * q`)) THEN
  ABBREV_TAC `chi = qchar k (num_of_int a)` THEN
  SUBGOAL_THEN
   `((\N. sum(1..k * N)
           (\y. (chi * (&1 - &p * (if p divides y then &1 else &0) -
                        &q * (if q divides y then &1 else &0) +
                        &k * (if k divides y then &1 else &0))) / &y))
     ---> &0) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
    SUBGOAL_THEN `&0 = chi * &0`
     (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_LIMIT_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!N. abs(sum(1..k * N) (qform_slice k a b c (&1)) -
            (&2 * pi) / (&k * sqrt(real_of_int(&4 * a * c - b pow 2))) *
            sum(1..k * N)
             (\y. (chi * (&1 - &p * (if p divides y then &1 else &0) -
                          &q * (if q divides y then &1 else &0) +
                          &k * (if k divides y then &1 else &0))) / &y))
        <= (&4 * pi) / sqrt(real_of_int(&4 * a * c - b pow 2)) *
           (&1 + exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                        (real_of_int a * &k)))) /
           (&1 - exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                        (real_of_int a * &k)))) pow 2 *
           sum(1..k * N)
            (\y. exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                        (real_of_int a * &k))) pow y)`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
    MATCH_MP_TAC SUM_ABS_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `y:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC QFORM_LIMIT_SLICE_ERROR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sd = sqrt(real_of_int(&4 * a * c - b pow 2))` THEN
  ABBREV_TAC `ra = real_of_int a` THEN
  SUBGOAL_THEN
   `((\N. sum(1..k * N) (qform_slice k a b c (&1)) -
          (&2 * pi) / (&k * sd) *
          sum(1..k * N)
           (\y. (chi * (&1 - &p * (if p divides y then &1 else &0) -
                        &q * (if q divides y then &1 else &0) +
                        &k * (if k divides y then &1 else &0))) / &y))
     ---> S) sequentially`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `S = S - (&2 * pi) / (&k * sd) * &0`
     (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUB THEN CONJ_TAC THENL
     [UNDISCH_TAC `(qform_slice k a b c (&1) real_sums S) (from 1)` THEN
      REWRITE_TAC[real_sums; FROM_INTER_NUMSEG] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\n. sum(1..n) (qform_slice k a b c (&1))`; `S:real`;
                     `\N. k * N`] CLASSNO_SERIES_REALLIM_SUBSEQ) THEN
      ASM_SIMP_TAC[CLASSNO_LIMIT_LE_MULT];
      MATCH_MP_TAC REALLIM_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `eta = exp(--(pi * sd / (ra * &k)))` THEN
  SUBGOAL_THEN `&0 < eta /\ eta < &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    ONCE_REWRITE_TAC[GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT; REAL_NEG_LT0] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4 * pi) / sd * (&1 + eta) / (&1 - eta) pow 2 *
              eta / (&1 - eta)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC
     `\N. abs(sum(1..k * N) (qform_slice k a b c (&1)) -
              (&2 * pi) / (&k * sd) *
              sum(1..k * N)
               (\y. (chi * (&1 - &p * (if p divides y then &1 else &0) -
                            &q * (if q divides y then &1 else &0) +
                            &k * (if k divides y then &1 else &0))) / &y))` THEN
    ASM_SIMP_TAC[REALLIM_ABS; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `(a:real) <= b ==> b <= c ==> a <= c`) o SPEC `N:num`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN MP_TAC PI_POS THEN
      UNDISCH_TAC `&0 < sd` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
        REWRITE_TAC[REAL_LE_POW_2]];
      MATCH_MP_TAC CLASSNO_LIMIT_GP_BOUND THEN
      MAP_EVERY UNDISCH_TAC [`&0 < eta`; `eta < &1`] THEN REAL_ARITH_TAC];
    REWRITE_TAC[qform_kernel] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `~(&1 - eta = &0)` MP_TAC THENL
     [UNDISCH_TAC `eta < &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&0 < sd` THEN CONV_TAC REAL_FIELD]);;

(* The main result: the bound for the sum of the slices.                     *)

let QFORM_SLICE_BOUND = prove
 (`!k k1 k2 a b c S.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k /\
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\
     coprime(k,num_of_int a) /\ coprime(k,num_of_int(&4 * a * c - b pow 2)) /\
     (qform_slice k a b c (&1) real_sums S) (from 1)
     ==> abs S <=
         &4 * pi / sqrt(real_of_int(&4 * a * c - b pow 2)) *
         qform_kernel(exp(--(pi * sqrt(real_of_int(&4 * a * c - b pow 2)) /
                          (real_of_int a * &k))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC QFORM_LIMIT_ASSEMBLY THEN
  MAP_EVERY EXISTS_TAC [`k1:num`; `k2:num`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC(ARITH_RULE `2 <= p ==> 1 <= p`) THEN
    MATCH_MP_TAC PRIME_GE_2 THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(ARITH_RULE `2 <= p ==> 1 <= p`) THEN
    MATCH_MP_TAC PRIME_GE_2 THEN FIRST_ASSUM ACCEPT_TAC;
    GEN_TAC THEN MATCH_MP_TAC QFORM_LIMIT_RAMANUJAN THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
