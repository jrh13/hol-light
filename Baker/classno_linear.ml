(* ========================================================================= *)
(* The linear form in log eps_21 and log eps_33 attached to an imaginary     *)
(* quadratic field of class number one.                                      *)
(*                                                                           *)
(* Purpose: for d prime, d = 3 mod 8, d > 10^4 and form_classno(-d) = 1      *)
(* there are integers b1, b2 >= 1 with b1 <= 391 sqrt d, b2 <= 160 sqrt d,   *)
(* b2 l2 <> b1 l1 and abs(b2 l2 - b1 l1) <= 8800 exp(-pi sqrt(d) / 33),      *)
(* where l1 = log eps and l2 = log eps1, eps = (5 + sqrt 21) / 2,            *)
(* eps1 = 23 + 4 sqrt 33 (CLASSNO_LINEAR_FORM): the linear form in two       *)
(* logarithms of Baker, Transcendental Number Theory, Ch. 5, sec. 4 (Baker   *)
(* and Wustholz, Logarithmic Forms and Diophantine Geometry, sec. 3.1).      *)
(*                                                                           *)
(* Method: for k = 21, 33 the product formula CLASSNO_PRODUCT_LIMIT and the  *)
(* slice bound CLASSNO_SLICE_BOUND give                                      *)
(* abs L(1, chi_k) abs L(1, chi_kd) = abs(zeta_k(2) + S_k),                  *)
(* abs S_k <= E_k(d), with E_k(d) = (4 pi / sqrt d) g(eta_k),                *)
(* g(x) = x (1 + x) / (1 - x)^3, eta_k = exp(-pi sqrt(d) / k). The class     *)
(* number formulas abs L(1, chi_21) = 2 l1 / sqrt 21,                        *)
(* abs L(1, chi_33) = 2 l2 / sqrt 33 (CLASSNO_L1_REAL) and                   *)
(* abs L(1, chi_q) = pi T / ((2 - chi_q(2)) sqrt q) for q = k d              *)
(* (CLASSNO_L1_ODD; T, the absolute value of the sum of chi_q(a) over        *)
(* a <= (q - 1)/2, is a natural number), with chi_21d(2) = 1 and             *)
(* chi_33d(2) = -1, give 2 pi l1 T21 = 21 sqrt(d) abs(zeta_21(2) + S_21) and *)
(* 2 pi l2 T33 = 99 sqrt(d) abs(zeta_33(2) + S_33). By the Euler factors     *)
(* zeta_21(2) = (384/441) zeta(2) and zeta_33(2) = (960/1089) zeta(2), and   *)
(* 105 * 21 * 384/441 = 22 * 99 * 960/1089 = 1920, the main terms cancel in  *)
(* Lam = 22 T33 l2 - 105 T21 l1, so                                          *)
(* abs Lam <= 4410 g(eta_21) + 4356 g(eta_33) <= 8800 eta_33, while          *)
(* 1 <= zeta(2) <= 2 gives T21, T33 >= 1 and the bounds for b1 = 105 T21,    *)
(* b2 = 22 T33. Lam <> 0 since eps^u = eps1^v (u, v >= 1) would give         *)
(* a + b sqrt 21 = c + w sqrt 33 with rational a, b, c, w and b, w > 0.      *)
(* Since T = (2 - chi_q(2)) h(-q), this is three times the form              *)
(* 35 h log eps - 22 h1 log eps1 of Baker; the class numbers h(-21 d),       *)
(* h(-33 d) themselves are not used.                                         *)
(*                                                                           *)
(* Main results: CLASSNO_LINEAR_FORM; library style                          *)
(* CLASSNO_LINEAR_ZETA_SUMS, CLASSNO_LINEAR_ZETA_PRIME_MUL (the Euler factor *)
(* of a prime p not dividing m: zeta_pm(2) = (1 - 1/p^2) zeta_m(2)); helper  *)
(* names CLASSNO_LINEAR_*.                                                   *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (form_classno), Baker/classno_chardefs.ml     *)
(* (qchar, zeta_coprime), Baker/classno_product.ml (CLASSNO_PRODUCT_LIMIT,   *)
(* CLASSNO_SLICE_BOUND), Baker/classno_gauss.ml (CLASSNO_L1_ODD),            *)
(* Baker/classno_cyclo.ml (CLASSNO_L1_REAL, CLASSNO_CYCLO_SQUAREFREE),       *)
(* Baker/classno_nf.ml (CLASSNO_NF_SQRT_INDEPENDENT,                         *)
(* CLASSNO_NF_IRRATIONAL_SQRT), Baker/classno_cf.ml                          *)
(* (CLASSNO_CF_LOG_EPS21_BOUNDS, CLASSNO_CF_LOG_EPS33_BOUNDS);               *)
(* Library/jacobi.ml (JACOBI_OF_2_CASES, JACOBI_RMUL),                       *)
(* Multivariate/realanalysis.ml (REAL_INFSUM_ZETA_BOUNDS).                   *)
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
needs "Baker/classno_product.ml";;
needs "Baker/classno_cyclo.ml";;
needs "Baker/classno_nf.ml";;
needs "Baker/classno_cf.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. zeta_k(2): the defining series, the Euler factor of a prime, bounds    *)
(*    and the two values for k = 21, 33.                                     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LINEAR_ZETA_SUMS = prove
 (`!k. ((\n. if coprime(n,k) then inv(&n pow 2) else &0) real_sums
        zeta_coprime k) (from 1)`,
  GEN_TAC THEN REWRITE_TAC[zeta_coprime; REAL_SUMS_INFSUM] THEN
  MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n:num. inv(&n pow 2):real` THEN
  SIMP_TAC[REAL_SUMMABLE_ZETA_INTEGER; LE_REFL] THEN
  EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_0; REAL_LE_INV_EQ; REAL_LE_POW_2; REAL_ABS_INV;
              REAL_ABS_POW; REAL_ABS_NUM; REAL_LE_REFL]);;

(* The Euler factor: removing the multiples of a prime p not dividing m.     *)

let CLASSNO_LINEAR_ZETA_PRIME_MUL = prove
 (`!p m. prime p /\ coprime(p,m)
         ==> zeta_coprime(p * m) = (&1 - inv(&p pow 2)) * zeta_coprime m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  ABBREV_TAC `f = \n. if coprime(n,m) then inv(&n pow 2) else (&0:real)` THEN
  SUBGOAL_THEN `((f:num->real) real_sums zeta_coprime m) (from 1)`
  ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[CLASSNO_LINEAR_ZETA_SUMS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. &0 <= (f:num->real) n /\ f n <= inv(&n pow 2)`
  ASSUME_TAC THENL
   [GEN_TAC THEN EXPAND_TAC "f" THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ; REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((f:num->real) real_sums (inv(&p pow 2) * zeta_coprime m))
    (IMAGE (\n. p * n) (from 1))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lift o (f:num->real)`; `from 1`; `\n:num. p * n`;
                   `lift(inv(&p pow 2) * zeta_coprime m)`]
                  SERIES_INJECTIVE_IMAGE) THEN
    REWRITE_TAC[GSYM REAL_SUMS; GSYM o_ASSOC] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[o_DEF; NORM_LIFT] THEN
        REWRITE_TAC[GSYM(REWRITE_RULE[o_DEF] REAL_SUMMABLE)] THEN
        MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
        EXISTS_TAC `\n:num. inv(&n pow 2):real` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_SUMMABLE_POS_SUBSET THEN
          EXISTS_TAC `from 1` THEN
          SIMP_TAC[REAL_SUMMABLE_ZETA_INTEGER; LE_REFL; REAL_LE_INV_EQ;
                   REAL_LE_POW_2; SUBSET; FORALL_IN_IMAGE; IN_FROM] THEN
          ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0];
          EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN
          DISCH_THEN(K ALL_TAC) THEN
          FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN REAL_ARITH_TAC];
        REWRITE_TAC[] THEN ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN
        MESON_TAC[]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC REAL_SUMS_EQ THEN
      EXISTS_TAC `\n:num. inv(&p pow 2) * (f:num->real) n` THEN
      ASM_SIMP_TAC[REAL_SERIES_LMUL] THEN X_GEN_TAC `n:num` THEN
      DISCH_THEN(K ALL_TAC) THEN EXPAND_TAC "f" THEN
      REWRITE_TAC[o_THM; COPRIME_LMUL] THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_RZERO; GSYM REAL_OF_NUM_MUL; REAL_POW_MUL;
                  REAL_INV_MUL]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [zeta_coprime] THEN
  MATCH_MP_TAC REAL_INFSUM_UNIQUE THEN
  ONCE_REWRITE_TAC[GSYM REAL_SERIES_RESTRICT] THEN
  MP_TAC(ISPECL
   [`\n. if n IN from 1 then (f:num->real) n else &0`; `zeta_coprime m`;
    `\n. if n IN IMAGE (\n. p * n) (from 1) then (f:num->real) n else &0`;
    `inv(&p pow 2) * zeta_coprime m`; `(:num)`] REAL_SERIES_SUB) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_SERIES_RESTRICT]; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `(z:real) - i * z = (&1 - i) * z`] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_SUMS_EQ) THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[IN_FROM; IN_IMAGE] THEN
  ASM_CASES_TAC `1 <= n` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?x. n = p * x /\ 1 <= x)`
     (fun th -> REWRITE_TAC[th; REAL_SUB_REFL]) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `x:num` THEN
    SUBGOAL_THEN `n = 0` SUBST1_TAC THENL
     [UNDISCH_TAC `~(1 <= n)` THEN ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[MULT_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC] THEN
  SUBGOAL_THEN `(?x. n = p * x /\ 1 <= x) <=> p divides n` SUBST1_TAC THENL
   [REWRITE_TAC[divides] THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN EXISTS_TAC `x:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x = 0` THENL
     [UNDISCH_TAC `1 <= n` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
      ARITH_TAC;
      UNDISCH_TAC `~(x = 0)` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `coprime(n,p) <=> ~(p divides n)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  EXPAND_TAC "f" THEN ASM_REWRITE_TAC[COPRIME_RMUL] THEN
  ASM_CASES_TAC `p divides n` THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_SUB_RZERO]);;

(* 1 <= zeta(2) <= 2: the bounds 1 / (s - 1) <= zeta(s) <= s / (s - 1) of   *)
(* ANT/dedekind_zeta.ml at s = 2.                                            *)

let CLASSNO_LINEAR_ZETA_1_BOUNDS = prove
 (`&1 <= zeta_coprime 1 /\ zeta_coprime 1 <= &2`,
  MP_TAC(SPEC `&2:real` REAL_INFSUM_ZETA_BOUNDS) THEN
  REWRITE_TAC[zeta_coprime; COPRIME_1; RPOW_POW] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]);;

(* The values for k = 21 = 3 * 7 and k = 33 = 3 * 11.                        *)

let CLASSNO_LINEAR_ZETA_21_33 = prove
 (`zeta_coprime 21 = &384 / &441 * zeta_coprime 1 /\
   zeta_coprime 33 = &960 / &1089 * zeta_coprime 1`,
  MP_TAC(SPECL [`3`; `7`] CLASSNO_LINEAR_ZETA_PRIME_MUL) THEN
  MP_TAC(SPECL [`7`; `1`] CLASSNO_LINEAR_ZETA_PRIME_MUL) THEN
  MP_TAC(SPECL [`3`; `11`] CLASSNO_LINEAR_ZETA_PRIME_MUL) THEN
  MP_TAC(SPECL [`11`; `1`] CLASSNO_LINEAR_ZETA_PRIME_MUL) THEN
  CONV_TAC(ONCE_DEPTH_CONV PRIME_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV COPRIME_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. Arithmetic of the characters: squarefree moduli, values at 2.          *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LINEAR_QCHAR_2 = prove
 (`!d. d MOD 8 = 3 ==> qchar (21 * d) 2 = &1 /\ qchar (33 * d) 2 = --(&1)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `jacobi(2,d) = --(&1)` ASSUME_TAC THENL
   [REWRITE_TAC[JACOBI_OF_2_CASES; CONG] THEN
    SUBGOAL_THEN `~EVEN d` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[EVEN_MOD] THEN
      MP_TAC(SPECL [`d:num`; `2`; `4`] MOD_MOD) THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      CONV_TAC NUM_REDUCE_CONV;
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[qchar; JACOBI_RMUL] THEN
  REWRITE_TAC[JACOBI_OF_2_CASES; CONG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  REWRITE_TAC[int_neg_th; int_of_num_th]);;

(* ------------------------------------------------------------------------- *)
(* 3. The product formula in absolute value: |L(1,chi_k)| |L(1,chi_kd)| =    *)
(*    |zeta_k(2) + S| with the slice sum S bounded by E_k(d), and the        *)
(*    class number formulas for k = 21, 33.                                  *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LINEAR_MOD_8_4 = prove
 (`!d. d MOD 8 = 3 ==> d MOD 4 = 3`,
  GEN_TAC THEN MP_TAC(SPECL [`d:num`; `4`; `2`] MOD_MOD) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV);;

let CLASSNO_LINEAR_NORMS = prove
 (`!k d. (k = 21 \/ k = 33) /\ prime d /\ d MOD 4 = 3 /\ k < d /\
         form_classno (--(&d)) = 1
         ==> ?S t. abs S <= &4 * pi / sqrt(&d) *
                            exp(--(pi * sqrt(&d) / &k)) *
                            (&1 + exp(--(pi * sqrt(&d) / &k))) /
                            (&1 - exp(--(pi * sqrt(&d) / &k))) pow 3 /\
                   norm(Lfunction (\n. Cx(qchar k n))) *
                   pi * &t / ((&2 - qchar (k * d) 2) * sqrt(&(k * d))) =
                   abs(zeta_coprime k + S)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `coprime(k,d)` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k = 21 \/ k = 33` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `squarefree(k * d) /\ (k * d) MOD 4 = 3` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k = 21 \/ k = 33` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CLASSNO_CYCLO_SQUAREFREE] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `d:num`] CLASSNO_PRODUCT_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`k:num`; `d:num`; `S:real`] CLASSNO_SLICE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `k * d` CLASSNO_L1_ODD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `integer(sum(1..(k * d - 1) DIV 2) (\a. qchar (k * d) a))`
  MP_TAC THENL
   [MATCH_MP_TAC INTEGER_SUM THEN REWRITE_TAC[qchar; INTEGER_REAL_OF_INT];
    ALL_TAC] THEN
  REWRITE_TAC[integer] THEN DISCH_THEN(X_CHOOSE_TAC `t:num`) THEN
  MAP_EVERY EXISTS_TAC [`S:real`; `t:num`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(zeta_coprime k + S) =
    norm(Lfunction (\n. Cx(qchar k n))) *
    norm(Lfunction (\n. Cx(qchar (k * d) n)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_NORM_MUL] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX];
    ASM_REWRITE_TAC[]]);;

let CLASSNO_LINEAR_IDENTITY_21 = prove
 (`!d. prime d /\ d MOD 8 = 3 /\ 21 < d /\ form_classno (--(&d)) = 1
       ==> ?S t. abs S <= &4 * pi / sqrt(&d) *
                          exp(--(pi * sqrt(&d) / &21)) *
                          (&1 + exp(--(pi * sqrt(&d) / &21))) /
                          (&1 - exp(--(pi * sqrt(&d) / &21))) pow 3 /\
                 &2 * pi * log((&5 + sqrt(&21)) / &2) * &t =
                 &21 * sqrt(&d) * abs(zeta_coprime 21 + S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`21`; `d:num`] CLASSNO_LINEAR_NORMS) THEN
  ASM_SIMP_TAC[CLASSNO_LINEAR_MOD_8_4] THEN
  ASM_SIMP_TAC[CLASSNO_LINEAR_QCHAR_2; CLASSNO_L1_REAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[SQRT_MUL; REAL_POS] THEN
  MP_TAC(SPEC `&21:real` SQRT_POW_2) THEN
  MP_TAC(SPEC `&21:real` SQRT_POS_LT) THEN
  MP_TAC(SPEC `&d:real` SQRT_POS_LT) THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_LT; ARITH] THEN
  ANTS_TAC THENL [UNDISCH_TAC `21 < d` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD);;

let CLASSNO_LINEAR_IDENTITY_33 = prove
 (`!d. prime d /\ d MOD 8 = 3 /\ 33 < d /\ form_classno (--(&d)) = 1
       ==> ?S t. abs S <= &4 * pi / sqrt(&d) *
                          exp(--(pi * sqrt(&d) / &33)) *
                          (&1 + exp(--(pi * sqrt(&d) / &33))) /
                          (&1 - exp(--(pi * sqrt(&d) / &33))) pow 3 /\
                 &2 * pi * log(&23 + &4 * sqrt(&33)) * &t =
                 &99 * sqrt(&d) * abs(zeta_coprime 33 + S)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`33`; `d:num`] CLASSNO_LINEAR_NORMS) THEN
  ASM_SIMP_TAC[CLASSNO_LINEAR_MOD_8_4] THEN
  ASM_SIMP_TAC[CLASSNO_LINEAR_QCHAR_2; CLASSNO_L1_REAL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `S:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  SIMP_TAC[SQRT_MUL; REAL_POS] THEN
  MP_TAC(SPEC `&33:real` SQRT_POW_2) THEN
  MP_TAC(SPEC `&33:real` SQRT_POS_LT) THEN
  MP_TAC(SPEC `&d:real` SQRT_POS_LT) THEN
  REWRITE_TAC[REAL_POS; REAL_OF_NUM_LT; ARITH] THEN
  ANTS_TAC THENL [UNDISCH_TAC `33 < d` THEN ARITH_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* 4. Numerics: sqrt d >= 100, pi, eta_k = exp(-pi sqrt(d) / k) <= 1/2000,   *)
(*    g(eta) = eta (1 + eta) / (1 - eta)^3 <= 1.003 eta, and the arithmetic  *)
(*    core (positivity, coefficient bounds, the cancellation of the main     *)
(*    terms 105 * 21 * 384 / 441 = 22 * 99 * 960 / 1089 = 1920).             *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LINEAR_SQRT_D = prove
 (`!d. 10000 < d ==> &100 <= sqrt(&d)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `10000 < d` THEN ARITH_TAC);;

let CLASSNO_LINEAR_PI_BOUNDS = prove
 (`&31415 / &10000 <= pi /\ pi <= &31416 / &10000`,
  MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC);;

let CLASSNO_LINEAR_ETA = prove
 (`!s. &100 <= s
       ==> &0 <= exp(--(pi * s / &21)) /\
           exp(--(pi * s / &21)) <= exp(--(pi * s / &33)) /\
           exp(--(pi * s / &33)) <= inv(&2000)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&314 / &100 * &100 <= pi * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN MP_TAC PI_APPROX_32 THEN
    UNDISCH_TAC `&100 <= (s:real)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE];
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    UNDISCH_TAC `&314 / &100 * &100 <= pi * s` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_EXP_NEG] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&9)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `exp(&9) = exp(&1) pow 9` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_N; REAL_MUL_RID]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2718 / &1000:real) pow 9` THEN CONJ_TAC THENL
       [CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC REAL_POW_LE2 THEN MP_TAC E_APPROX_32 THEN
        REAL_ARITH_TAC];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      UNDISCH_TAC `&314 / &100 * &100 <= pi * s` THEN REAL_ARITH_TAC]]);;

let CLASSNO_LINEAR_G_BOUND = prove
 (`!x. &0 <= x /\ x <= inv(&2000)
       ==> &0 <= x * (&1 + x) / (&1 - x) pow 3 /\
           x * (&1 + x) / (&1 - x) pow 3 <= &1003 / &1000 * x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&1 - x:real) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `(x:real) <= inv(&2000)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `&0 <= (x:real)` THEN REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `(a:real) * y <= a * c ==> a * y <= c * a`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&0 <= x pow 2 * (&3 - x:real)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      UNDISCH_TAC `(x:real) <= inv(&2000)` THEN REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC [`&0 <= (x:real)`; `(x:real) <= inv(&2000)`] THEN
      REAL_ARITH_TAC]]);;

let CLASSNO_LINEAR_E_MUL = prove
 (`!s p g S. &0 < s /\ abs S <= &4 * p / s * g ==> s * abs S <= &4 * p * g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&4 * p * g = s * (&4 * p / s * g:real)` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < (s:real)` THEN CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ]]);;

(* The arithmetic core. Here p = pi, s = sqrt d, l1 = log eps,               *)
(* l2 = log eps1, z = zeta(2), S1, S2 the slice sums, g1, g2 the values      *)
(* g(eta_21), g(eta_33), e1, e2 the values eta_21, eta_33, and t1, t2 the    *)
(* two character sums T21, T33.                                              *)

let CLASSNO_LINEAR_ARITH = prove
 (`!p s l1 l2 z S1 S2 g1 g2 e1 e2 t1 t2.
     &31415 / &10000 <= (p:real) /\ p <= &31416 / &10000 /\ &100 <= s /\
     &15667 / &10000 <= l1 /\ &38281 / &10000 <= l2 /\
     &1 <= z /\ z <= &2 /\
     s * abs S1 <= &4 * p * g1 /\ s * abs S2 <= &4 * p * g2 /\
     &0 <= g1 /\ g1 <= &1003 / &1000 * e1 /\
     &0 <= g2 /\ g2 <= &1003 / &1000 * e2 /\
     &0 <= e1 /\ e1 <= e2 /\ e2 <= inv(&2000) /\
     &2 * p * l1 * t1 = &21 * s * abs(&384 / &441 * z + S1) /\
     &2 * p * l2 * t2 = &99 * s * abs(&960 / &1089 * z + S2)
     ==> &0 < t1 /\ &0 < t2 /\
         &105 * t1 <= &391 * s /\ &22 * t2 <= &160 * s /\
         abs(&22 * t2 * l2 - &105 * t1 * l1) <= &8800 * e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(S1:real) <= &1 / &10000 /\ abs(S2:real) <= &1 / &10000`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`&100:real`; `s:real`; `abs(S1:real)`] REAL_LE_RMUL) THEN
      MP_TAC(SPECL [`p:real`; `&31416 / &10000:real`; `g1:real`]
        REAL_LE_RMUL) THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      MAP_EVERY UNDISCH_TAC
       [`s * abs S1 <= &4 * p * (g1:real)`; `g1 <= &1003 / &1000 * (e1:real)`;
        `e1 <= (e2:real)`; `(e2:real) <= inv(&2000)`] THEN
      REAL_ARITH_TAC;
      MP_TAC(SPECL [`&100:real`; `s:real`; `abs(S2:real)`] REAL_LE_RMUL) THEN
      MP_TAC(SPECL [`p:real`; `&31416 / &10000:real`; `g2:real`]
        REAL_LE_RMUL) THEN
      ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      MAP_EVERY UNDISCH_TAC
       [`s * abs S2 <= &4 * p * (g2:real)`; `g2 <= &1003 / &1000 * (e2:real)`;
        `(e2:real) <= inv(&2000)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &384 / &441 * z + (S1:real) /\ &0 < &960 / &1089 * z + (S2:real)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&1 <= (z:real)`; `abs(S1:real) <= &1 / &10000`;
      `abs(S2:real) <= &1 / &10000`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * p * l1 * t1 = &21 * s * (&384 / &441 * z + (S1:real)) /\
    &2 * p * l2 * t2 = &99 * s * (&960 / &1089 * z + (S2:real))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_ARITH `&0 < (x:real) ==> abs x = x`]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&31415 / &10000 * &15667 / &10000 <= p * (l1:real) /\
    &31415 / &10000 * &38281 / &10000 <= p * (l2:real)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < &2 * p * (l1:real) /\ &0 < &2 * p * (l2:real) /\ &0 < &2 * (p:real)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`&31415 / &10000 * &15667 / &10000 <= p * (l1:real)`;
      `&31415 / &10000 * &38281 / &10000 <= p * (l2:real)`;
      `&31415 / &10000 <= (p:real)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < s * (&384 / &441 * z + (S1:real)) /\
    &0 < s * (&960 / &1089 * z + (S2:real))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&100 <= (s:real)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`&0:real`; `t1:real`; `&2 * p * (l1:real)`]
      REAL_LT_LMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC
     [`&2 * p * l1 * t1 = &21 * s * (&384 / &441 * z + (S1:real))`;
      `&0 < s * (&384 / &441 * z + (S1:real))`] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`&0:real`; `t2:real`; `&2 * p * (l2:real)`]
      REAL_LT_LMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY UNDISCH_TAC
     [`&2 * p * l2 * t2 = &99 * s * (&960 / &1089 * z + (S2:real))`;
      `&0 < s * (&960 / &1089 * z + (S2:real))`] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`&105 * (t1:real)`; `&391 * (s:real)`; `&2 * p * (l1:real)`]
      REAL_LE_LMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`s:real`; `&2205 * (&384 / &441 * z + (S1:real))`;
                  `&782 * (p * (l1:real))`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `&100 <= (s:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real) <= &2`; `abs(S1:real) <= &1 / &10000`;
        `&31415 / &10000 * &15667 / &10000 <= p * (l1:real)`] THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC
       `&2 * p * l1 * t1 = &21 * s * (&384 / &441 * z + (S1:real))` THEN
      REAL_ARITH_TAC];
    MP_TAC(SPECL [`&22 * (t2:real)`; `&160 * (s:real)`; `&2 * p * (l2:real)`]
      REAL_LE_LMUL_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPECL [`s:real`; `&2178 * (&960 / &1089 * z + (S2:real))`;
                  `&320 * (p * (l2:real))`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `&100 <= (s:real)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(z:real) <= &2`; `abs(S2:real) <= &1 / &10000`;
        `&31415 / &10000 * &38281 / &10000 <= p * (l2:real)`] THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC
       `&2 * p * l2 * t2 = &99 * s * (&960 / &1089 * z + (S2:real))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&2 * (&2178 * g2 + &2205 * (g1:real))` THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY UNDISCH_TAC
     [`g1 <= &1003 / &1000 * (e1:real)`; `g2 <= &1003 / &1000 * (e2:real)`;
      `&0 <= (e1:real)`; `e1 <= (e2:real)`] THEN
    REAL_ARITH_TAC] THEN
  SUBGOAL_THEN `!x. s * x <= s * abs x /\ s * --x <= (s:real) * abs x`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    UNDISCH_TAC `&100 <= (s:real)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&22 * t2 * l2 - &105 * t1 * l1 <= &2 * (&2178 * g2 + &2205 * g1) /\
    --(&22 * t2 * l2 - &105 * t1 * l1) <=
    &2 * (&2178 * g2 + &2205 * (g1:real))`
  MP_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP REAL_LE_LMUL_EQ
    (ASSUME `&0 < &2 * (p:real)`))] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `S1:real` th) THEN
                          MP_TAC(SPEC `S2:real` th)) THEN
  MAP_EVERY UNDISCH_TAC
   [`&2 * p * l1 * t1 = &21 * s * (&384 / &441 * z + (S1:real))`;
    `&2 * p * l2 * t2 = &99 * s * (&960 / &1089 * z + (S2:real))`;
    `s * abs S1 <= &4 * p * (g1:real)`;
    `s * abs S2 <= &4 * p * (g2:real)`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 5. The linear form does not vanish: eps^u = eps1^v with u, v >= 1 would   *)
(*    give a + b sqrt 21 = c + w sqrt 33 with rational a, b, c, w and        *)
(*    b, w > 0, against the independence of 1, sqrt 21, sqrt 33, sqrt 693.   *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LINEAR_EPS21_POW = prove
 (`!n. ?a b. rational a /\ rational b /\ &0 < a /\ &0 < b /\
             ((&5 + sqrt(&21)) / &2) pow (n + 1) = a + b * sqrt(&21)`,
  INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&5 / &2:real`; `&1 / &2:real`] THEN
    SIMP_TAC[RATIONAL_DIV; RATIONAL_NUM; ADD_CLAUSES; REAL_POW_1] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`(&5 * a + &21 * b) / &2:real`; `(a + &5 * b) / &2:real`] THEN
    ASM_SIMP_TAC[RATIONAL_DIV; RATIONAL_ADD; RATIONAL_MUL; RATIONAL_NUM] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < (a:real)`; `&0 < (b:real)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < (a:real)`; `&0 < (b:real)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; real_pow] THEN
    MP_TAC(SPEC `&21:real` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING]);;

let CLASSNO_LINEAR_EPS33_POW = prove
 (`!n. ?a b. rational a /\ rational b /\ &0 < a /\ &0 < b /\
             (&23 + &4 * sqrt(&33)) pow (n + 1) = a + b * sqrt(&33)`,
  INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&23:real`; `&4:real`] THEN
    REWRITE_TAC[RATIONAL_NUM; ADD_CLAUSES; REAL_POW_1] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`&23 * a + &132 * b:real`; `&4 * a + &23 * b:real`] THEN
    ASM_SIMP_TAC[RATIONAL_ADD; RATIONAL_MUL; RATIONAL_NUM] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < (a:real)`; `&0 < (b:real)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&0 < (a:real)`; `&0 < (b:real)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; real_pow] THEN
    MP_TAC(SPEC `&33:real` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING]);;

let CLASSNO_LINEAR_LOGS_INDEPENDENT = prove
 (`!u v. 1 <= u /\ 1 <= v
         ==> ~(&v * log(&23 + &4 * sqrt(&33)) =
               &u * log((&5 + sqrt(&21)) / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&5 + sqrt(&21)) / &2 /\ &0 < &23 + &4 * sqrt(&33)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&21:real` SQRT_POS_LE) THEN
    MP_TAC(SPEC `&33:real` SQRT_POS_LE) THEN
    REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&23 + &4 * sqrt(&33)) pow v = ((&5 + sqrt(&21)) / &2) pow u`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `exp` o check (is_eq o concl)) THEN
    ASM_SIMP_TAC[REAL_EXP_N; EXP_LOG];
    ALL_TAC] THEN
  MP_TAC(SPEC `u - 1` CLASSNO_LINEAR_EPS21_POW) THEN
  MP_TAC(SPEC `v - 1` CLASSNO_LINEAR_EPS33_POW) THEN
  ASM_SIMP_TAC[SUB_ADD] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `w:real`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&21:real`; `&33:real`; `a - c:real`; `b:real`; `--w:real`;
                `&0:real`]
    CLASSNO_NF_SQRT_INDEPENDENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RATIONAL_NUM; REAL_POS; REAL_OF_NUM_MUL] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[RATIONAL_SUB; RATIONAL_NEG;
      MATCH_MP CLASSNO_NF_IRRATIONAL_SQRT
       (ARITH_RULE `4 EXP 2 < 21 /\ 21 < (4 + 1) EXP 2`);
      MATCH_MP CLASSNO_NF_IRRATIONAL_SQRT
       (ARITH_RULE `5 EXP 2 < 33 /\ 33 < (5 + 1) EXP 2`);
      MATCH_MP CLASSNO_NF_IRRATIONAL_SQRT
       (ARITH_RULE `26 EXP 2 < 693 /\ 693 < (26 + 1) EXP 2`)] THEN
    UNDISCH_TAC `c + w * sqrt(&33) = a + b * sqrt(&21)` THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `&0 < (b:real)` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 6. The linear form b2 log eps1 - b1 log eps with b1 = 105 T21 and         *)
(*    b2 = 22 T33. Since T = (2 - chi_q(2)) h(-q), this is three times the   *)
(*    form 35 h log eps - 22 h1 log eps1 of Baker (TNT, ch. 5); the class    *)
(*    numbers h(-21 d), h(-33 d) themselves are not used.                    *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LINEAR_LOG_BOUNDS = prove
 (`&15667 / &10000 <= log((&5 + sqrt(&21)) / &2) /\
   &38281 / &10000 <= log(&23 + &4 * sqrt(&33))`,
  MP_TAC CLASSNO_CF_LOG_EPS21_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_EPS33_BOUNDS THEN REAL_ARITH_TAC);;

let CLASSNO_LINEAR_FORM = prove
 (`!d. prime d /\ d MOD 8 = 3 /\ 10000 < d /\ form_classno (--(&d)) = 1
      ==> ?b1 b2. 1 <= b1 /\ 1 <= b2 /\
                  &b1 <= &391 * sqrt(&d) /\ &b2 <= &160 * sqrt(&d) /\
                  ~(&b2 * log(&23 + &4 * sqrt(&33)) =
                    &b1 * log((&5 + sqrt(&21)) / &2)) /\
                  abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                      &b1 * log((&5 + sqrt(&21)) / &2))
                  <= &8800 * exp(--(pi * sqrt(&d) / &33))`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `21 < d /\ 33 < d` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `10000 < d` THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `d:num` CLASSNO_LINEAR_IDENTITY_21) THEN
  MP_TAC(SPEC `d:num` CLASSNO_LINEAR_IDENTITY_33) THEN
  ASM_REWRITE_TAC[CLASSNO_LINEAR_ZETA_21_33] THEN
  DISCH_THEN(X_CHOOSE_THEN `S2:real` (X_CHOOSE_THEN `t2:num`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `S1:real` (X_CHOOSE_THEN `t1:num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `&100 <= sqrt(&d)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_LINEAR_SQRT_D THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `sqrt(&d)` CLASSNO_LINEAR_ETA) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e1 = exp(--(pi * sqrt(&d) / &21))` THEN
  ABBREV_TAC `e2 = exp(--(pi * sqrt(&d) / &33))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(e1:real) <= inv(&2000)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`e1 <= (e2:real)`; `(e2:real) <= inv(&2000)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `e1:real` CLASSNO_LINEAR_G_BOUND) THEN
  MP_TAC(SPEC `e2:real` CLASSNO_LINEAR_G_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (e2:real)` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= (e1:real)`; `e1 <= (e2:real)`] THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&d) * abs S1 <= &4 * pi * (e1 * (&1 + e1) / (&1 - e1) pow 3) /\
    sqrt(&d) * abs S2 <= &4 * pi * (e2 * (&1 + e2) / (&1 - e2) pow 3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLASSNO_LINEAR_E_MUL THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&100 <= sqrt(&d)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`pi`; `sqrt(&d)`; `log((&5 + sqrt(&21)) / &2)`;
    `log(&23 + &4 * sqrt(&33))`; `zeta_coprime 1`; `S1:real`; `S2:real`;
    `(e1:real) * (&1 + e1) / (&1 - e1) pow 3`;
    `(e2:real) * (&1 + e2) / (&1 - e2) pow 3`;
    `e1:real`; `e2:real`; `&t1:real`; `&t2:real`] CLASSNO_LINEAR_ARITH) THEN
  ASM_REWRITE_TAC[CLASSNO_LINEAR_PI_BOUNDS; CLASSNO_LINEAR_LOG_BOUNDS;
                  CLASSNO_LINEAR_ZETA_1_BOUNDS] THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`105 * t1`; `22 * t2`] THEN
  SUBGOAL_THEN `1 <= 105 * t1 /\ 1 <= 22 * t2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`0 < t1`; `0 < t2`] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CLASSNO_LINEAR_LOGS_INDEPENDENT] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_MUL_ASSOC] THEN
  ASM_REWRITE_TAC[]);;
