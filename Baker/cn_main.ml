(* ========================================================================= *)
(* Class number two: only finitely many imaginary quadratic fields have      *)
(* class number two (Baker 1971, Stark 1971).                                *)
(*                                                                           *)
(* Purpose: Baker, Transcendental Number Theory, Ch. 5, sec. 5: there are    *)
(* only finitely many squarefree d with form_classno (qdisc d) = 2, i.e.     *)
(* with exactly two reduced primitive forms of the discriminant of           *)
(* Q(sqrt(-d)) (CLASS_NUMBER_TWO_FINITE); the odd discriminants -d,          *)
(* d = 3 mod 4, give CLASS_NUMBER_TWO_FINITE_ODD.                            *)
(*                                                                           *)
(* Method: CN_FORMS_TWO_CASES leaves d = p q (p = 1, q = 3 mod 4 primes,     *)
(* d = 3 mod 8 or d = 15), d prime = 1 mod 4, and d = 2 p. In each case a    *)
(* linear form in logarithms is exponentially small in a power of d, and a   *)
(* Baker type lower bound excludes large d:                                  *)
(*  - q^4 <= d: CN_LINEAR_SMALL with k = 21 (k = 33 if q = 7, k = 77 if      *)
(*    q = 3) gives b log xi_k - y pi with y = r sqrt d, r rational, of size  *)
(*    at most 384 k s exp(-pi s / k), s = d^(1/4) (CN_MAIN_SMALL_ERROR);     *)
(*    BAKER_FELDMAN with the fixed logarithms log xi_k and i pi and the      *)
(*    coefficient i y, a root of n X^2 + m (n y^2 = m), gives B^-C with      *)
(*    B = 40 k^2 N^2 d^3 (CN_MAIN_FELDMAN_TWO, CN_MAIN_SMALL_HEIGHTS), and   *)
(*    exp beats a power (CN_MAIN_FELDMAN_NUMERIC): CN_MAIN_SMALL_BOUND;      *)
(*  - the discriminants -4d: the same with CN_LINEAR_EVEN, k = 21 and        *)
(*    s = sqrt d (CN_MAIN_EVEN_BOUND);                                       *)
(*  - q^4 > d (so p < q^3 and q > 7 for d > 2401): CN_LINEAR_MAIN gives      *)
(*    abs(b1 log eps + b2 log xi - (128/7) pi sqrt d) <= 8800 eta,           *)
(*    eta = exp(-pi sqrt(d) / 21), xi = cyclo_unit (21 p), a root of         *)
(*    X^2 - t X + 1 (CN_CYCLO_UNIT_QUADRATIC) with abs t <= exp M,           *)
(*    M = 1 + sqrt(21 p) (log(21 p) + 3) (CLASSNO_L1_EVEN, CN_L1_BOUND,      *)
(*    CN_MAIN_LOG_CYCLO_BOUND, CN_MAIN_TRACE_BOUND).                         *)
(*    BAKER_SHARPENING_ALGEBRAIC_COEFFS with n = 3, the numbers -1, eps =    *)
(*    (5 + sqrt 21) / 2, xi, g0 = 5, A = exp M and the coefficients          *)
(*    (128/7) i sqrt d (a root of 49 X^2 + 16384 d), b1, b2 of height        *)
(*    B = 16384 d^2 gives exp(-C 5^K M log(B M)) (CN_MAIN_SA_INSTANCE); with *)
(*    M <= 46 sqrt(p) log q and log(B M) <= 31 log q this forces             *)
(*    sqrt q <= c (log q)^2 (CN_MAIN_LARGE_NUMERIC, LOG_POLY_BOUND), so q    *)
(*    and d < q^4 are bounded (CN_MAIN_LARGE_BOUND).                         *)
(* The linear forms never vanish: if exp x and c <> 0 are algebraic then     *)
(* x <> c pi (Gelfond-Schneider, CN_MAIN_EXP_PI_NONZERO), applied to         *)
(* x = b log xi_k and x = b1 log eps + b2 log xi (integer powers of          *)
(* algebraic numbers, CN_MAIN_ALGEBRAIC_EXP_INT_LOG).                        *)
(*                                                                           *)
(* Main results: CLASS_NUMBER_TWO_FINITE, CLASS_NUMBER_TWO_FINITE_ODD; the   *)
(* bounds CN_MAIN_ODD_BOUND, CN_MAIN_ALL_BOUND, CN_MAIN_SMALL_BOUND,         *)
(* CN_MAIN_EVEN_BOUND, CN_MAIN_LARGE_BOUND; helper names CN_MAIN_*.          *)
(*                                                                           *)
(* Uses: Baker/cn_defs.ml (cyclo_unit), Baker/classno_chardefs.ml            *)
(* (qform_kernel), Baker/cn_forms.ml (CN_FORMS_TWO_CASES),                   *)
(* Baker/cn_linear.ml (CN_LINEAR_MAIN, CN_LINEAR_SMALL, CN_LINEAR_EVEN),     *)
(* Baker/cn_cyclo.ml (CN_CYCLO_UNIT_QUADRATIC, CN_L1_BOUND),                 *)
(* Baker/sharpc_main.ml (BAKER_SHARPENING_ALGEBRAIC_COEFFS),                 *)
(* Baker/theorem.ml (BAKER_FELDMAN), Baker/apps.ml (GELFOND_SCHNEIDER),      *)
(* Baker/bridge.ml (ALGEBRAIC_NUMBER_EXPLICIT and the closure rules),        *)
(* Baker/apps_examples.ml (ALGEBRAIC_NUMBER_CX_RATIONAL),                    *)
(* Baker/classno_gauss.ml (CLASSNO_L1_EVEN, QCHAR_NONPRINCIPAL,              *)
(* CLASSNO_GAUSS_ODD_MOD4), Baker/classno_series.ml (QCHAR_DIRICHLET,        *)
(* CLASSNO_SERIES_QCHAR_BOUND), Baker/classno_main.ml (CLASSNO_MAIN_INV_EXP, *)
(* CLASSNO_MAIN_EXP_DOMINATES, CLASSNO_MAIN_EXP_COMPARE), Baker/lemmas.ml    *)
(* (LOG_POLY_BOUND, LOG_NUM_GE_1, REAL_LE_1_MUL, VSUM_DEGREE_1_ROOT),        *)
(* Baker/twolog.ml (LOG_LE_SUB_1), Baker/thue.ml (THUE_VSUM_SMALL);          *)
(* Library/pocklington.ml (squarefree, SQUAREFREE_MUL, PRIME_CONV).          *)
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
needs "Baker/apps_examples.ml";;
needs "Baker/sharpc_main.ml";;
needs "Baker/thue.ml";;
needs "Baker/classno_main.ml";;
needs "Baker/cn_linear.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. Analytic tools: the kernel qform_kernel near 0 and the numerics of the *)
(*    Baker-Feldman cases (exp beats a power).                               *)
(* ------------------------------------------------------------------------- *)

(* qform_kernel x <= 16 x for 0 <= x <= 1/2 ((1 - x)^3 >= 1/8).              *)

let CN_MAIN_KERNEL_LE = prove
 (`!x. &0 <= x /\ x <= &1 / &2 ==> qform_kernel x <= &16 * x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qform_kernel] THEN
  SUBGOAL_THEN `(&1 / &2) pow 3 <= (&1 - x) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&1 - x) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x * y <= x * &16 ==> x * y <= &16 * x`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  UNDISCH_TAC `(&1 / &2) pow 3 <= (&1 - x) pow 3` THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let CN_MAIN_EXP_NEG_LE_HALF = prove
 (`!y. &1 <= y ==> exp(--y) <= &1 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_NEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN MP_TAC(SPEC `y:real` REAL_EXP_LE_X) THEN
    ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let CN_MAIN_KERNEL_EXP = prove
 (`!y. &1 <= y ==> qform_kernel(exp(--y)) <= &16 * exp(--y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CN_MAIN_KERNEL_LE THEN
  ASM_SIMP_TAC[REAL_EXP_POS_LE; CN_MAIN_EXP_NEG_LE_HALF]);;

(* A Baker-Feldman lower bound inv(B^C) with B <= a0 s^j against an upper    *)
(* bound a1 s exp(-c s): s is bounded (exp beats a power).                   *)

let CN_MAIN_FELDMAN_NUMERIC = prove
 (`!c a0 a1 j C.
     &0 < c
     ==> ?S. !s B lam. &1 <= s /\ &2 <= B /\ B <= a0 * s pow j /\
                       inv(B pow C) <= lam /\ lam <= a1 * s * exp(--(c * s))
                       ==> s <= S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `(a1:real) * a0 pow C`; `j * C + 1`]
    CLASSNO_MAIN_EXP_DOMINATES) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `S:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:real`; `B:real`; `lam:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < B pow C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exp(c * s) <= (a1 * s) * B pow C` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_MAIN_INV_EXP THEN EXISTS_TAC `lam:real` THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= a1 * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    SUBGOAL_THEN `&0 * B pow C < (a1 * s) * B pow C` MP_TAC THENL
     [MP_TAC(SPEC `c * s:real` REAL_EXP_POS_LT) THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(a1 * s) * B pow C` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(a1 * s) * (a0 * s pow j) pow C` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW; REAL_POW_ADD; REAL_POW_1] THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Algebraic numbers and the non-vanishing of the linear forms            *)
(*    (Gelfond-Schneider: exp(c pi) is transcendental for algebraic c <> 0). *)
(* ------------------------------------------------------------------------- *)

(* Gelfond-Schneider: exp(c pi) = (-1)^(-i c) is transcendental for          *)
(* algebraic c <> 0, so x <> c pi whenever exp x is algebraic.               *)

let CN_MAIN_EXP_PI_NONZERO = prove
 (`!x c. algebraic_number(Cx(exp x)) /\ algebraic_number(Cx c) /\ ~(c = &0)
         ==> ~(x = c * pi)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`ii * Cx pi`; `--(ii * Cx c)`] GELFOND_SCHNEIDER) THEN
  REWRITE_TAC[CEXP_II_PI] THEN
  MATCH_MP_TAC(TAUT `(a /\ b /\ c /\ d) /\ e ==> ~(a /\ b /\ c /\ d ==> ~e)`)
  THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC algebraic_number_neg THEN
    REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM];
    REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ; PI_NZ];
    MATCH_MP_TAC algebraic_number_neg THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN
    ASM_REWRITE_TAC[algebraic_number_ii];
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `r:real` THEN
    DISCH_THEN(MP_TAC o AP_TERM `Im` o CONJUNCT2) THEN
    REWRITE_TAC[IM_NEG; IM_MUL_II; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `--(ii * Cx c) * ii * Cx pi = Cx(c * pi)` SUBST1_TAC THENL
     [REWRITE_TAC[CX_MUL] THEN MP_TAC COMPLEX_POW_II_2 THEN
      CONV_TAC COMPLEX_RING;
      ASM_REWRITE_TAC[GSYM CX_EXP]]]);;

(* exp(b log x) = x^b is algebraic for algebraic x > 0 and integer b.        *)

let CN_MAIN_ALGEBRAIC_EXP_INT_LOG = prove
 (`!x b. &0 < x /\ algebraic_number(Cx x) /\ integer b
         ==> algebraic_number(Cx(exp(b * log x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[REAL_EXP_N] THEN
    ASM_SIMP_TAC[EXP_LOG; CX_POW; ALGEBRAIC_NUMBER_POW];
    REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG; REAL_EXP_N] THEN
    ASM_SIMP_TAC[EXP_LOG; CX_INV; CX_POW; ALGEBRAIC_NUMBER_POW;
                 ALGEBRAIC_NUMBER_INV]]);;

let CN_MAIN_QUADRATIC_ALGEBRAIC = prove
 (`!x t. integer t /\ x pow 2 - t * x + &1 = &0 ==> algebraic_number(Cx x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALGEBRAIC_NUMBER_EXPLICIT] THEN
  MAP_EVERY EXISTS_TAC [`2`; `\i. if i = 1 then --t else &1`] THEN
  REWRITE_TAC[THUE_VSUM_SMALL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  ASM_REAL_ARITH_TAC);;

let CN_MAIN_ALGEBRAIC_EPS = prove
 (`algebraic_number(Cx((&5 + sqrt(&21)) / &2))`,
  REWRITE_TAC[CX_DIV; CX_ADD] THEN
  SIMP_TAC[ALGEBRAIC_NUMBER_DIV; ALGEBRAIC_NUMBER_ADD;
           ALGEBRAIC_NUMBER_CX_NUM; ALGEBRAIC_NUMBER_CX_SQRT]);;

let CN_MAIN_ALGEBRAIC_SQRT_MUL = prove
 (`!r n. rational r ==> algebraic_number(Cx(r * sqrt(&n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CX_MUL] THEN
  MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN
  ASM_SIMP_TAC[ALGEBRAIC_NUMBER_CX_RATIONAL; ALGEBRAIC_NUMBER_CX_SQRT]);;

(* ------------------------------------------------------------------------- *)
(* 3. The height of the cyclotomic unit: abs(log xi_m) <= sqrt m (log m + 3) *)
(*    (CLASSNO_L1_EVEN and CN_L1_BOUND), and the trace of xi.                *)
(* ------------------------------------------------------------------------- *)

(* abs(log xi_m) = sqrt m abs(L(1,chi_m)) <= sqrt m (log m + 3) for          *)
(* squarefree m = 1 mod 4 (CLASSNO_L1_EVEN, CN_L1_BOUND).                    *)

let CN_MAIN_LOG_CYCLO_BOUND = prove
 (`!m. squarefree m /\ m MOD 4 = 1 /\ 1 < m
       ==> abs(log(cyclo_unit m)) <= sqrt(&m) * (log(&m) + &3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD m` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPEC `m:num` CLASSNO_L1_EVEN) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `\n. Cx(qchar m n)`] CN_L1_BOUND) THEN
  ASM_SIMP_TAC[QCHAR_DIRICHLET; QCHAR_NONPRINCIPAL;
               ARITH_RULE `1 < m ==> 1 <= m`] THEN
  REWRITE_TAC[cyclo_unit; LOG_EXP; REAL_ABS_NEG] THEN
  SUBGOAL_THEN `&0 < sqrt(&m)` ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `L = norm(Lfunction (\n. Cx(qchar m n)))` THEN
  ABBREV_TAC
   `S = abs(sum(1..m - 1) (\a. qchar m a * log(sin(pi * &a / &m))))` THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `S / sqrt(&m) <= log(&m) + &3` THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC);;

(* The trace t = xi + 1/xi of a root of X^2 - t X + 1 is at most exp(1 +     *)
(* abs(log xi)).                                                             *)

let CN_MAIN_TRACE_BOUND = prove
 (`!xi t L. &0 < xi /\ xi pow 2 - t * xi + &1 = &0 /\ abs(log xi) <= L
            ==> abs t <= exp(&1 + L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = xi + inv xi` SUBST1_TAC THENL
   [SUBGOAL_THEN `~(xi = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `xi pow 2 - t * xi + &1 = &0` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `exp(log xi) <= exp L /\ exp(--(log xi)) <= exp L` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_EXP_NEG] THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_EXP_ADD] THEN
  SUBGOAL_THEN `&2 <= exp(&1)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < inv xi` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INV]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * exp L <= exp(&1) * exp L` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Crude polynomial bound for the coefficient bounds of Baker/cn_linear.ml.  *)

let CN_MAIN_SQRT_LOG_LE = prove
 (`!x. &1 <= x ==> sqrt x * (log x + &3) <= &3 * x pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sqrt x <= x` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log x /\ log x <= x - &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_LE_SUB_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `x * (&3 * x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC SQRT_POS_LE) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. BAKER_FELDMAN for the two fixed logarithms log z and i pi with the     *)
(*    coefficients b (integer) and i y (y^2 rational, y <> 0).               *)
(* ------------------------------------------------------------------------- *)

let CN_MAIN_SQUARE_ALGEBRAIC = prove
 (`!y m n. integer m /\ integer n /\ ~(n = &0) /\ n * y pow 2 = m
           ==> algebraic_number(Cx y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALGEBRAIC_NUMBER_EXPLICIT] THEN
  MAP_EVERY EXISTS_TAC
   [`2`; `\i. if i = 0 then --m else if i = 2 then n else &0`] THEN
  REWRITE_TAC[THUE_VSUM_SMALL] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  ASM_REAL_ARITH_TAC);;

(* BAKER_FELDMAN with n = 2, lg 1 = log z, lg 2 = i pi, beta 0 = 0, beta 1 = *)
(* b, beta 2 = i y with n y^2 = m: inv(B^C) <= abs(b log z - y pi) (non-     *)
(* vanishing by CN_MAIN_EXP_PI_NONZERO).                                     *)

let CN_MAIN_FELDMAN_TWO = prove
 (`!z. &0 < z /\ algebraic_number(Cx z)
       ==> ?C. !B b y m n.
             &2 <= B /\ integer b /\ integer m /\ integer n /\
             ~(m = &0) /\ ~(n = &0) /\
             abs b <= B /\ abs m <= B /\ abs n <= B /\ n * y pow 2 = m
             ==> inv(B pow C) <= abs(b * log z - y * pi)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `\r. if r = 1 then Cx(log z) else ii * Cx pi`; `2`]
    BAKER_FELDMAN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[GSYM CX_EXP; EXP_LOG; CEXP_II_PI] THEN
    MATCH_MP_TAC algebraic_number_neg THEN
    REWRITE_TAC[ALGEBRAIC_NUMBER_CX_NUM];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`B:real`; `b:real`; `y:real`; `m:real`; `n:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`B:real`;
    `\j. if j = 0 then Cx(&0) else if j = 1 then Cx b else Cx y * ii`;
    `\j. if j = 2 then 2 else 1`;
    `\j i. if j = 0 then (if i = 1 then &1 else &0)
           else if j = 1 then (if i = 0 then --b else if i = 1 then &1 else &0)
           else (if i = 0 then m else if i = 2 then n else &0)`]) THEN
  REWRITE_TAC[VSUM_2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `Cx(&0) + Cx b * Cx(log z) + (Cx y * ii) * ii * Cx pi =
    Cx(b * log z - y * pi)`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_SUB; CX_MUL] THEN MP_TAC COMPLEX_POW_II_2 THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN
  MATCH_MP_TAC(TAUT `p ==> (p ==> q) ==> q`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `~(x = y * pi) ==> ~(x - y * pi = &0)`) THEN
    MATCH_MP_TAC CN_MAIN_EXP_PI_NONZERO THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CN_MAIN_ALGEBRAIC_EXP_INT_LOG THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CN_MAIN_SQUARE_ALGEBRAIC THEN
      MAP_EVERY EXISTS_TAC [`m:real`; `n:real`] THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `n * y pow 2 = m` THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC]] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `j = 0 \/ j = 1 \/ j = 2`
   (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
   [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
     ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC;
     ALL_TAC]) THEN
  ASM_REWRITE_TAC[THUE_VSUM_SMALL; VSUM_DEGREE_1_ROOT] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
  TRY(UNDISCH_TAC `n * y pow 2 = m` THEN DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[CX_MUL; CX_POW; complex_pow; COMPLEX_POW_1] THEN
  MP_TAC COMPLEX_POW_II_2 THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* 5. BAKER_SHARPENING_ALGEBRAIC_COEFFS for the main linear form: n = 3,     *)
(*    degree bound 2, al = -1, eps = (5 + sqrt 21) / 2, xi (a root of        *)
(*    X^2 - t X + 1), g0 = 5, A = exp M, coefficients (128/7) i sqrt d       *)
(*    (root of 49 X^2 + 16384 d), b1, b2.                                    *)
(* ------------------------------------------------------------------------- *)

(* The instance of BAKER_SHARPENING_ALGEBRAIC_COEFFS for the main linear     *)
(* form b1 log eps + b2 log xi - (128/7) pi sqrt d (non-vanishing by         *)
(* CN_MAIN_EXP_PI_NONZERO with x = b1 log eps + b2 log xi).                  *)

let CN_MAIN_SA_INSTANCE = prove
 (`?C K. !b1 b2 t xi d M B.
     integer b1 /\ integer b2 /\ integer t /\ &0 < xi /\
     xi pow 2 - t * xi + &1 = &0 /\ 1 <= d /\
     abs t <= exp M /\ &1 <= M /\
     &16384 * &d <= B /\ abs b1 <= B /\ abs b2 <= B
     ==> exp(--(C * &5 pow K * M * log(B * M))) <=
         abs(b1 * log((&5 + sqrt(&21)) / &2) + b2 * log xi -
             &128 / &7 * pi * sqrt(&d))`,
  MP_TAC(SPECL [`3`; `2`] BAKER_SHARPENING_ALGEBRAIC_COEFFS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `C:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:num` THEN
  DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`b1:real`; `b2:real`; `t:real`; `xi:real`; `d:num`;
                       `M:real`; `B:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. if r = 1 then --Cx(&1)
         else if r = 2 then Cx((&5 + sqrt(&21)) / &2) else Cx xi`;
    `\r j. if r = 1 then (if j = 0 \/ j = 1 then &1 else &0)
           else if r = 2
           then (if j = 0 \/ j = 2 then &1 else if j = 1 then -- &5 else &0)
           else (if j = 0 \/ j = 2 then &1 else if j = 1 then --t else &0)`;
    `\r. if r = 1 then 1 else 2`;
    `\r. if r = 1 then Cx(&128 / &7 * sqrt(&d)) * ii
         else if r = 2 then Cx b1 else Cx b2`;
    `\r j. if r = 1
           then (if j = 0 then &16384 * &d else if j = 2 then &49 else &0)
           else if r = 2 then (if j = 0 then --b1 else if j = 1 then &1 else &0)
           else (if j = 0 then --b2 else if j = 1 then &1 else &0)`;
    `\r. if r = 1 then 2 else 1`;
    `exp M`; `B:real`; `&5`]) THEN
  REWRITE_TAC[VSUM_3; LOG_EXP] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < (&5 + sqrt(&21)) / &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `&21` SQRT_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cx(&128 / &7 * sqrt(&d)) * ii) * clog(--Cx(&1)) +
    Cx b1 * clog(Cx((&5 + sqrt(&21)) / &2)) + Cx b2 * clog(Cx xi) =
    Cx(b1 * log((&5 + sqrt(&21)) / &2) + b2 * log xi -
       &128 / &7 * pi * sqrt(&d))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[CLOG_NEG_1; GSYM CX_LOG] THEN
    REWRITE_TAC[CX_ADD; CX_SUB; CX_MUL] THEN MP_TAC COMPLEX_POW_II_2 THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN
  MATCH_MP_TAC(TAUT `p ==> (p ==> q) ==> q`) THEN
  SUBGOAL_THEN `&1 <= &d` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&6 <= exp(&5)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&5` REAL_EXP_LE_X) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= exp M` ASSUME_TAC THENL
   [MP_TAC(SPEC `M:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC;
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_NUMSEG] THEN GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `r = 1 \/ r = 2 \/ r = 3`
     (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THENL
    [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NEG_EQ_0; CX_INJ] THEN REAL_ARITH_TAC;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
      REAL_ARITH_TAC;
      REWRITE_TAC[THUE_VSUM_SMALL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[complex_pow; COMPLEX_POW_1] THEN CONV_TAC COMPLEX_RING;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REWRITE_TAC[THUE_VSUM_SMALL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      SUBGOAL_THEN `Cx(&49) * Cx(&128 / &7) pow 2 = Cx(&16384)` MP_TAC THENL
       [REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; CX_INJ] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SUBGOAL_THEN `Cx(sqrt(&d)) pow 2 = Cx(&d)` MP_TAC THENL
       [REWRITE_TAC[GSYM CX_POW; CX_INJ] THEN SIMP_TAC[SQRT_POW_2; REAL_POS];
        ALL_TAC] THEN
      MP_TAC COMPLEX_POW_II_2 THEN REWRITE_TAC[CX_MUL] THEN
      CONV_TAC COMPLEX_RING];
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN SIMP_TAC[INTEGER_CLOSED];
      REAL_ARITH_TAC;
      REWRITE_TAC[THUE_VSUM_SMALL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
      MP_TAC(SPEC `&21` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_FIELD;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REWRITE_TAC[VSUM_DEGREE_1_ROOT]];
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
      REAL_ARITH_TAC;
      REWRITE_TAC[THUE_VSUM_SMALL] THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ABS_NEG] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REWRITE_TAC[VSUM_DEGREE_1_ROOT]]];
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `r = 1 \/ r = 2` (DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_ARITH_TAC; ALL_TAC; ALL_TAC] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NEG] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH
     `~(a + b = (&128 / &7 * s) * pi) ==> ~(a + b - &128 / &7 * pi * s = &0)`)
    THEN MATCH_MP_TAC CN_MAIN_EXP_PI_NONZERO THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_ADD; CX_MUL] THEN
      MATCH_MP_TAC ALGEBRAIC_NUMBER_MUL THEN
      CONJ_TAC THEN MATCH_MP_TAC CN_MAIN_ALGEBRAIC_EXP_INT_LOG THEN
      ASM_REWRITE_TAC[CN_MAIN_ALGEBRAIC_EPS] THEN
      MATCH_MP_TAC CN_MAIN_QUADRATIC_ALGEBRAIC THEN EXISTS_TAC `t:real` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CN_MAIN_ALGEBRAIC_SQRT_MUL THEN
      SIMP_TAC[RATIONAL_CLOSED];
      MATCH_MP_TAC(REAL_ARITH `&0 < s ==> ~(&128 / &7 * s = &0)`) THEN
      MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* 6. The main case q^4 > d: numerics of the three-logarithm bound.          *)
(* ------------------------------------------------------------------------- *)

let CN_MAIN_MOD4_GE = prove
 (`!p. prime p /\ p MOD 4 = 1 ==> 5 <= p`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`p:num`; `4`] DIVISION) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  SUBGOAL_THEN `~(p = 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  ABBREV_TAC `k = p DIV 4` THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CN_MAIN_NUM_POW_BOUNDS = prove
 (`!p q. 3 <= q /\ p < q EXP 3 ==> 21 * p <= q EXP 6 /\ p <= q EXP 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `27 <= q EXP 3 /\ q EXP 3 <= q EXP 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`3`; `q:num`; `3`] EXP_MONO_LE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `q EXP 6 = q EXP 3 * q EXP 3` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC);;

let CN_MAIN_SQRT_GE_1 = prove
 (`!p. 1 <= p ==> &1 <= sqrt(&p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_OF_NUM_LE]);;

(* log A = M = 1 + sqrt(21 p) (log(21 p) + 3) <= 46 sqrt(p) log q when p <   *)
(* q^3, q >= 3.                                                              *)

let CN_MAIN_LOG_A_BOUND = prove
 (`!p q. 1 <= p /\ 3 <= q /\ p < q EXP 3
         ==> &1 + sqrt(&(21 * p)) * (log(&(21 * p)) + &3) <=
             &46 * sqrt(&p) * log(&q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CN_MAIN_NUM_POW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&q) /\ &1 <= sqrt(&p)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_1; CN_MAIN_SQRT_GE_1]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&(21 * p)) <= &5 * sqrt(&p)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; SQRT_MUL] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&(21 * p)) /\ log(&(21 * p)) <= &6 * log(&q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&q pow 6)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LOG_POW THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + (&5 * sqrt(&p)) * (&9 * log(&q))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&1 <= sqrt(&p) * log(&q)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; REAL_ARITH_TAC]]);;

(* The final numerics of the main case: with M <= 46 sqrt(p) log q and B <=  *)
(* 16384 q^8, pi sqrt(p q) / 21 <= c M log(B M) + 8800 forces q <= c (log    *)
(* q)^4, so q is bounded (LOG_POLY_BOUND).                                   *)

let CN_MAIN_LARGE_NUMERIC = prove
 (`!c. &0 <= c
       ==> ?Q. !p q M B.
             1 <= p /\ 3 <= q /\ p < q EXP 3 /\
             &1 <= M /\ M <= &46 * sqrt(&p) * log(&q) /\
             &1 <= B /\ B <= &16384 * &q pow 8 /\
             pi * sqrt(&(p * q)) / &21 <= c * M * log(B * M) + &8800
             ==> &q <= Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(&7 * (&1426 * c + &8800)) pow 2`; `4`] LOG_POLY_BOUND) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `Q:real` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`; `M:real`; `B:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CN_MAIN_NUM_POW_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&q) /\ &1 <= sqrt(&p) /\ &3 <= &q`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_NUM_GE_1; CN_MAIN_SQRT_GE_1; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&p) <= &q pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LSQRT THEN REWRITE_TAC[REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; LE_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&q) <= &q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LOG_LT_X THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `M <= &46 * &q pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&46 * sqrt(&p) * log(&q)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&q pow 3 = &q pow 2 * &q` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &q pow 11 /\ &2 pow 20 <= &q pow 20 /\ &0 <= &q pow 8`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_POW_LE2) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= B * M /\ B * M <= &q pow 31` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&16384 * &q pow 8) * (&46 * &q pow 3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&16384 * &q pow 8) * (&46 * &q pow 3) =
                  &753664 * &q pow 11 /\
                  &q pow 31 = &q pow 20 * &q pow 11`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [REAL_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow 20` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(B * M) /\ log(B * M) <= &31 * log(&q)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&q pow 31)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC LOG_POW THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c * M * log(B * M) <= c * (&46 * sqrt(&p) * log(&q)) * (&31 * log(&q))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&(p * q)) = sqrt(&p) * sqrt(&q)` SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; SQRT_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= sqrt(&p) * log(&q) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(&p) * (pi * sqrt(&q)) <=
    sqrt(&p) * (&21 * (&1426 * c + &8800) * log(&q) pow 2)`
  MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&p)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&3 * sqrt(&q) <= pi * sqrt(&q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
    MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&q) <= &7 * (&1426 * c + &8800) * log(&q) pow 2`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&q) pow 2` THEN
  CONJ_TAC THENL [SIMP_TAC[SQRT_POW_2; REAL_POS; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&7 * (&1426 * c + &8800) * log(&q) pow 2) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 7. The arithmetic data of the moduli k = 21, 33, 77 and the main case     *)
(*    bound (CN_LINEAR_MAIN, CN_CYCLO_UNIT_QUADRATIC, SA).                   *)
(* ------------------------------------------------------------------------- *)

let CN_MAIN_NOT_PRIME_MUL = prove
 (`!m n. 1 < m /\ 1 < n ==> ~prime(m * n)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num` o CONJUNCT2 o REWRITE_RULE[prime]) THEN
  SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN
  SUBGOAL_THEN `m * 2 <= m * n` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let CN_MAIN_K_FACTS = prove
 (`prime 3 /\ prime 7 /\ prime 11 /\ ~prime 21 /\ ~prime 33 /\ ~prime 77 /\
   squarefree 21 /\ squarefree 33 /\ squarefree 77`,
  SUBGOAL_THEN `prime 3 /\ prime 7 /\ prime 11` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC PRIME_CONV; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC(RAND_CONV PRIME_CONV) THEN REWRITE_TAC[];
    CONV_TAC(RAND_CONV PRIME_CONV) THEN REWRITE_TAC[];
    CONV_TAC(RAND_CONV PRIME_CONV) THEN REWRITE_TAC[];
    SUBST1_TAC(ARITH_RULE `21 = 3 * 7`);
    SUBST1_TAC(ARITH_RULE `33 = 3 * 11`);
    SUBST1_TAC(ARITH_RULE `77 = 7 * 11`)] THEN
  ASM_SIMP_TAC[SQUAREFREE_MUL; PRIME_IMP_SQUAREFREE] THEN
  CONV_TAC COPRIME_CONV);;

let CN_MAIN_COPRIME_21_PRIME = prove
 (`!p. prime p /\ ~(p = 3) /\ ~(p = 7) ==> coprime(21,p)`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(ARITH_RULE `21 = 3 * 7`) THEN
  REWRITE_TAC[COPRIME_LMUL] THEN CONJ_TAC THEN
  MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN
  ASM_REWRITE_TAC[CN_MAIN_K_FACTS]);;

let CN_MAIN_CYCLO_TRACE = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q /\ ~prime q
       ==> ?t. integer t /\ cyclo_unit q pow 2 - t * cyclo_unit q + &1 = &0`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CN_CYCLO_UNIT_QUADRATIC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let CN_MAIN_CYCLO_ALGEBRAIC = prove
 (`!q. squarefree q /\ q MOD 4 = 1 /\ 1 < q /\ ~prime q
       ==> algebraic_number(Cx(cyclo_unit q))`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CN_MAIN_CYCLO_TRACE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC CN_MAIN_QUADRATIC_ALGEBRAIC THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[]);;

(* The main case q^4 > d: CN_LINEAR_MAIN, the cyclotomic unit xi_21p and     *)
(* BAKER_SHARPENING_ALGEBRAIC_COEFFS bound d.                                *)

let CN_MAIN_LARGE_BOUND = prove
 (`?D. !p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
             (p * q) MOD 8 = 3 /\ coprime(21,p * q) /\
             form_classno (--(&(p * q))) = 2 /\ p * q < q EXP 4
             ==> p * q <= D`,
  X_CHOOSE_THEN `C:real` (X_CHOOSE_THEN `K:num` (LABEL_TAC "sa"))
    CN_MAIN_SA_INSTANCE THEN
  MP_TAC(SPEC `abs C * &5 pow K` CN_MAIN_LARGE_NUMERIC) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Q:real` (LABEL_TAC "num")) THEN
  X_CHOOSE_TAC `N:num` (SPEC `max (Q pow 4) (&10000)` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `N:num` THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `10000 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `p * q <= 10000` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3 <= q /\ 5 <= p` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`q:num`; `4`] MOD_LE) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CN_MAIN_MOD4_GE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `p < q EXP 3` ASSUME_TAC THENL
   [UNDISCH_TAC `p * q < q EXP 4` THEN
    SUBGOAL_THEN `q EXP 4 = q EXP 3 * q` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `4 = 3 + 1`; EXP_ADD; EXP_1]; ALL_TAC] THEN
    SIMP_TAC[LT_MULT_RCANCEL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `q:num`] CN_LINEAR_MAIN) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b1:real`; `b2:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `squarefree(21 * p) /\ (21 * p) MOD 4 = 1 /\ 1 < 21 * p /\ ~prime(21 * p)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SQUAREFREE_MUL; CN_MAIN_K_FACTS] THEN
      ASM_SIMP_TAC[PRIME_IMP_SQUAREFREE] THEN
      UNDISCH_TAC `coprime(21,p * q)` THEN SIMP_TAC[COPRIME_RMUL];
      ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV;
      UNDISCH_TAC `5 <= p` THEN ARITH_TAC;
      MATCH_MP_TAC CN_MAIN_NOT_PRIME_MUL THEN UNDISCH_TAC `5 <= p` THEN
      ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `21 * p` CN_MAIN_CYCLO_TRACE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `21 * p` CN_MAIN_LOG_CYCLO_BOUND) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < cyclo_unit(21 * p)` ASSUME_TAC THENL
   [REWRITE_TAC[cyclo_unit; REAL_EXP_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `M = &1 + sqrt(&(21 * p)) * (log(&(21 * p)) + &3)` THEN
  SUBGOAL_THEN `abs t <= exp M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC CN_MAIN_TRACE_BOUND THEN
    EXISTS_TAC `cyclo_unit(21 * p)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M /\ M <= &46 * sqrt(&p) * log(&q)` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "M" THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &3`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      UNDISCH_TAC `5 <= p` THEN ARITH_TAC;
      MATCH_MP_TAC CN_MAIN_LOG_A_BOUND THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `5 <= p` THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `B = &16384 * &(p * q) pow 2` THEN
  SUBGOAL_THEN
   `&q <= &(p * q) /\ &1 <= &(p * q) /\ &(p * q) <= &q pow 4`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_POW] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * q <= p * q ==> q <= p * q`) THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      UNDISCH_TAC `5 <= p` THEN ARITH_TAC;
      UNDISCH_TAC `~(p * q <= 10000)` THEN ARITH_TAC;
      UNDISCH_TAC `p * q < q EXP 4` THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(p * q) <= &(p * q) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN UNDISCH_TAC `&1 <= &(p * q)` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&16384 * &(p * q) <= B /\ abs b1 <= B /\ abs b2 <= B /\ &1 <= B /\
    B <= &16384 * &q pow 8`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&(p * q) <= &(p * q) pow 2` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * sqrt(&(21 * p * q)) * (log(&(21 * p * q)) + &3)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&(21 * p * q)` CN_MAIN_SQRT_LOG_LE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `~(p * q <= 10000)` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&(21 * p * q) = &21 * &(p * q)` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_MUL]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`&1 <= &(p * q)`; `&(p * q) <= &(p * q) pow 2`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(&(21 * q)) * (log(&(21 * q)) + &3)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `&(21 * q)` CN_MAIN_SQRT_LOG_LE) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `3 <= q` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&(21 * q) = &21 * &q` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_MUL]; ALL_TAC] THEN
      SUBGOAL_THEN `&q pow 2 <= &(p * q) pow 2` MP_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`&1 <= &(p * q)`; `&(p * q) <= &(p * q) pow 2`] THEN
      REAL_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`&1 <= &(p * q)`; `&(p * q) <= &(p * q) pow 2`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&q pow 8 = (&q pow 4) pow 2` SUBST1_TAC THENL
       [REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "sa" (MP_TAC o SPECL
   [`b1:real`; `b2:real`; `t:real`; `cyclo_unit(21 * p)`; `p * q`;
    `M:real`; `B:real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `~(p * q <= 10000)` THEN ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `pi * sqrt(&(p * q)) / &21 <= C * &5 pow K * M * log(B * M) + &8800`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_MAIN_EXP_COMPARE THEN
    EXISTS_TAC `abs(b1 * log((&5 + sqrt(&21)) / &2) +
                    b2 * log(cyclo_unit(21 * p)) -
                    &128 / &7 * pi * sqrt(&(p * q)))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&504 * qform_kernel(exp(--(pi * sqrt(&(p * q)) / &21)))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `pi * sqrt(&(p * q)) / &21` CN_MAIN_KERNEL_EXP) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `&100 <= sqrt(&(p * q))` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_RSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `~(p * q <= 10000)` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `pi * &100 <= pi * sqrt(&(p * q))` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[PI_POS_LE] THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `--(pi * sqrt(&(p * q)) / &21)` REAL_EXP_POS_LE) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(B * M)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_LE_1_MUL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `C * &5 pow K * M * log(B * M) <= (abs C * &5 pow K) * M * log(B * M)`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [UNDISCH_TAC `&1 <= M` THEN REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q <= Q` ASSUME_TAC THENL
   [REMOVE_THEN "num" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `M:real`; `B:real`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `5 <= p` THEN ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `!a b c:real. a <= b + &8800 /\ b <= c ==> a <= c + &8800`) THEN
      EXISTS_TAC `C * &5 pow K * M * log(B * M)` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(p * q) <= &N` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q pow 4` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&q pow 4` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `max (Q pow 4) (&10000) <= &N` THEN REAL_ARITH_TAC];
    REWRITE_TAC[REAL_OF_NUM_LE]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The error terms and the heights of the two-logarithm cases (small q    *)
(*    and the discriminants -4d).                                            *)
(* ------------------------------------------------------------------------- *)

let CN_MAIN_KERNEL_EXP_MONO = prove
 (`!y z. &1 <= z /\ z <= y ==> qform_kernel(exp(--y)) <= &16 * exp(--z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&16 * exp(--y)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CN_MAIN_KERNEL_EXP THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `&16 * x <= &16 * y <=> x <= y`] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]);;

(* The error term of CN_LINEAR_SMALL for q <= s = d^(1/4), k <= s.           *)

let CN_MAIN_SMALL_ERROR = prove
 (`!k q u s x.
     &1 <= &k /\ &1 <= &q /\ (u = &1 \/ u = &3) /\ &q <= s /\ &k <= s /\
     x = s pow 2
     ==> &4 * u * &q * &k *
         (qform_kernel(exp(--(pi * x / &k))) +
          qform_kernel(exp(--(pi * x / (&q * &k))))) <=
         &384 * &k * s * exp(--(pi / &k * s))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 <= u /\ u <= &3` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < pi / &k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= pi / &k * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pi / &k * &k` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `pi / &k * &k = pi` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
        MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) <= x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `s * &1 <= s * s ==> s <= s * s`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) <= x / &q` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `x:real = s pow 2` THEN DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN
   `pi / &k * s <= pi * x / &k /\ pi / &k * s <= pi * x / (&q * &k)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `pi * x / &k = pi / &k * x /\ pi * x / (&q * &k) = pi / &k * x / &q`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [SUBGOAL_THEN `~(&q = &0) /\ ~(&k = &0)` MP_TAC THENL
       [CONJ_TAC THEN ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `qform_kernel(exp(--(pi * x / &k))) <= &16 * exp(--(pi / &k * s)) /\
    qform_kernel(exp(--(pi * x / (&q * &k)))) <= &16 * exp(--(pi / &k * s))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CN_MAIN_KERNEL_EXP_MONO THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `E = exp(--(pi / &k * s))` THEN
  SUBGOAL_THEN `&0 <= E` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= u * &q /\ u * &q <= &3 * s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(u * &q) * (&k * (qform_kernel(exp(--(pi * x / &k))) +
                      qform_kernel(exp(--(pi * x / (&q * &k)))))) <=
    (u * &q) * (&k * (&32 * E))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u * &q) * (&k * (&32 * E)) <= (&3 * s) * (&k * (&32 * E))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The error term of CN_LINEAR_EVEN for k <= s = sqrt d.                     *)

let CN_MAIN_EVEN_ERROR = prove
 (`!k s. &1 <= &k /\ &k <= s
         ==> &8 * &k * (qform_kernel(exp(--(&2 * pi * s / &k))) +
                        qform_kernel(exp(--(pi * s / &k)))) <=
             &256 * &k * s * exp(--(pi / &k * s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < pi / &k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= pi / &k * s` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `pi / &k * &k` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `pi / &k * &k = pi` SUBST1_TAC THENL
       [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
        MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `pi * s / &k = pi / &k * s /\
                &2 * pi * s / &k = &2 * (pi / &k * s)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `y = pi / &k * s` THEN
  SUBGOAL_THEN `qform_kernel(exp(--(&2 * y))) <= &16 * exp(--y) /\
                qform_kernel(exp(--y)) <= &16 * exp(--y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CN_MAIN_KERNEL_EXP_MONO THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= exp(--y)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&k * (qform_kernel(exp(--(&2 * y))) + qform_kernel(exp(--y))) <=
    &k * (&32 * exp(--y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 * (&k * exp(--y)) <= s * (&k * exp(--y))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Heights for BAKER_FELDMAN in the small case: B = 40 k^2 N^2 d^3 bounds b, *)
(* m = u^2 (q + chi)^2 N^2 d and n = 36 k^2.                                 *)

let CN_MAIN_SMALL_HEIGHTS = prove
 (`!k N q d u c b.
     1 <= k /\ 1 <= N /\ 3 <= q /\ q <= d /\ (u = &1 \/ u = &3) /\
     abs c <= &1 /\
     abs b <= &q * sqrt(&(k * d)) * (log(&(k * d)) + &3)
     ==> &2 <= &40 * &k pow 2 * &N pow 2 * &d pow 3 /\
         abs b <= &40 * &k pow 2 * &N pow 2 * &d pow 3 /\
         abs(u pow 2 * (&q + c) pow 2 * &N pow 2 * &d) <=
         &40 * &k pow 2 * &N pow 2 * &d pow 3 /\
         abs(&36 * &k pow 2) <= &40 * &k pow 2 * &N pow 2 * &d pow 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= &k /\ &1 <= &N /\ &3 <= &q /\ &q <= &d`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= &k pow 2 /\ &1 <= &N pow 2 /\ &1 <= &d pow 3 /\
    &1 <= &N pow 2 * &d pow 3 /\ &1 <= &k pow 2 * &d pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = &k pow 2 * &N pow 2 * &d pow 3` THEN
  SUBGOAL_THEN
   `&N pow 2 * &d pow 3 <= P /\ &k pow 2 * &d pow 3 <= P /\ &k pow 2 <= P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 * x <= y * x ==> x <= y * x`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `(a * c) * &1 <= (a * c) * b ==> a * c <= a * b * c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * y ==> x <= x * y`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `&(k * d)` CN_MAIN_SQRT_LOG_LE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= sqrt(&(k * d)) * (log(&(k * d)) + &3)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &3`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&q * sqrt(&(k * d)) * (log(&(k * d)) + &3) <=
      &d * &3 * &(k * d) pow 2`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&(k * d) pow 2 = &k pow 2 * &d pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `&0 <= &q + c /\ &q + c <= &2 * &d` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `u pow 2 <= &9` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `u pow 2 * (&q + c) pow 2 <= &9 * (&2 * &d) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(u pow 2 * (&q + c) pow 2) * (&N pow 2 * &d) <=
      (&9 * (&2 * &d) pow 2) * (&N pow 2 * &d)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (u pow 2 * (&q + c) pow 2) * (&N pow 2 * &d)` MP_TAC
    THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* Heights in the even case: B = 100 k^2 N^2 d^2 bounds b, m = (2 + chi)^2   *)
(* N^2 d and n = 9 k^2.                                                      *)

let CN_MAIN_EVEN_HEIGHTS = prove
 (`!k N d c b.
     1 <= k /\ 1 <= N /\ 1 <= d /\ abs c <= &1 /\
     abs b <= &2 * sqrt(&(k * d)) * (log(&(4 * k * d)) + &3)
     ==> &2 <= &100 * &k pow 2 * &N pow 2 * &d pow 2 /\
         abs b <= &100 * &k pow 2 * &N pow 2 * &d pow 2 /\
         abs((&2 + c) pow 2 * &N pow 2 * &d) <=
         &100 * &k pow 2 * &N pow 2 * &d pow 2 /\
         abs(&9 * &k pow 2) <= &100 * &k pow 2 * &N pow 2 * &d pow 2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= &k /\ &1 <= &N /\ &1 <= &d` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= &k pow 2 /\ &1 <= &N pow 2 /\ &1 <= &d pow 2 /\ &d <= &d pow 2 /\
    &1 <= &N pow 2 * &d pow 2 /\ &1 <= &k pow 2 * &d pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * x ==> x <= x * x`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = &k pow 2 * &N pow 2 * &d pow 2` THEN
  SUBGOAL_THEN
   `&N pow 2 * &d <= P /\ &k pow 2 * &d pow 2 <= P /\ &k pow 2 <= P`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N pow 2 * &d pow 2` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `&1 * x <= y * x ==> x <= y * x`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
       `(a * c) * &1 <= (a * c) * b ==> a * c <= a * b * c`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x * &1 <= x * y ==> x <= x * y`) THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `&(4 * k * d)` CN_MAIN_SQRT_LOG_LE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
      MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `sqrt(&(k * d)) * (log(&(4 * k * d)) + &3) <=
      sqrt(&(4 * k * d)) * (log(&(4 * k * d)) + &3)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SQRT_MONO_LE THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ARITH_TAC;
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &3`) THEN
        MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        UNDISCH_TAC `1 <= k` THEN UNDISCH_TAC `1 <= d` THEN
        REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP LE_MULT2) THEN
        ARITH_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC
     `sqrt(&(4 * k * d)) * (log(&(4 * k * d)) + &3) <=
      &3 * &(4 * k * d) pow 2` THEN
    SUBGOAL_THEN `&(4 * k * d) pow 2 = &16 * &k pow 2 * &d pow 2`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_POW_MUL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `(&2 + c) pow 2 <= &3 pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 + c) pow 2 * (&N pow 2 * &d) <= &3 pow 2 * (&N pow 2 * &d)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (&2 + c) pow 2 * (&N pow 2 * &d)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_LE_POW_2];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2; REAL_POS]];
      ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 9. The two-logarithm cases: small q (CN_LINEAR_SMALL, any k = k1 k2) and  *)
(*    the discriminants -4d (CN_LINEAR_EVEN), with BAKER_FELDMAN.            *)
(* ------------------------------------------------------------------------- *)

let CN_MAIN_QCHAR_INTEGER = prove
 (`!k n. integer(qchar k n)`,
  REWRITE_TAC[qchar; INTEGER_REAL_OF_INT]);;

let CN_MAIN_N_POS = prove
 (`!k1 k2. prime k1 /\ prime k2 ==> 1 <= (k1 EXP 2 - 1) * (k2 EXP 2 - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `4 <= k1 EXP 2 /\ 4 <= k2 EXP 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXP_2] THEN CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `2 * 2 <= n * n ==> 4 <= n * n`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * 1 <= a * b ==> 1 <= a * b`) THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC);;

let CN_MAIN_ROOT4 = prove
 (`!d. &0 <= sqrt(sqrt(&d)) /\ sqrt(sqrt(&d)) pow 2 = sqrt(&d) /\
       sqrt(sqrt(&d)) pow 4 = &d`,
  GEN_TAC THEN
  SUBGOAL_THEN `&0 <= sqrt(&d)` ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LE; REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(sqrt(&d)) pow 2 = sqrt(&d)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SQRT_POW_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_POS_LE] THEN
  SUBGOAL_THEN `4 = 2 * 2` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_POW_POW] THEN SIMP_TAC[SQRT_POW_2; REAL_POS]);;

(* The small case q^4 <= d for one modulus k = k1 k2 (k = 21, 33, 77):       *)
(* CN_LINEAR_SMALL and BAKER_FELDMAN bound d.                                *)

let CN_MAIN_SMALL_BOUND = prove
 (`!k k1 k2.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     algebraic_number(Cx(cyclo_unit k))
     ==> ?D. !p q. prime p /\ prime q /\ p MOD 4 = 1 /\ q MOD 4 = 3 /\
                   coprime(k,p * q) /\ form_classno (--(&(p * q))) = 2 /\
                   q EXP 4 <= p * q
                   ==> p * q <= D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cyclo_unit k` ASSUME_TAC THENL
   [REWRITE_TAC[cyclo_unit; REAL_EXP_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `cyclo_unit k` CN_MAIN_FELDMAN_TWO) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num` (LABEL_TAC "feld")) THEN
  SUBGOAL_THEN `1 <= k /\ 1 <= (k1 EXP 2 - 1) * (k2 EXP 2 - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `1 * 1 <= a * b ==> 1 <= a * b`) THEN
      MATCH_MP_TAC LE_MULT2 THEN
      MP_TAC(SPEC `k1:num` PRIME_GE_2) THEN
      MP_TAC(SPEC `k2:num` PRIME_GE_2) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC CN_MAIN_N_POS THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `N = (k1 EXP 2 - 1) * (k2 EXP 2 - 1)` THEN
  SUBGOAL_THEN `&1 <= &k` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`pi / &k`; `&40 * &k pow 2 * &N pow 2`; `&384 * &k`; `12`;
                `C:num`] CN_MAIN_FELDMAN_NUMERIC) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real` (LABEL_TAC "num")) THEN
  X_CHOOSE_TAC `D:num` (SPEC `max (S pow 4) (&k pow 4)` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `D:num` THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPEC `p * q` CN_MAIN_ROOT4) THEN
  ABBREV_TAC `s = sqrt(sqrt(&(p * q)))` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&D < s pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x y z:real. x < y /\ z = y ==> x < z`) THEN
    EXISTS_TAC `&(p * q)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow 4 <= s pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!x y z:real. x <= y /\ z = y ==> x <= z`) THEN
    EXISTS_TAC `&(p * q)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&k <= s /\ &q <= s /\ &1 <= s` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(a /\ b) /\ (a ==> c) ==> a /\ b /\ c`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `4` THEN
    REWRITE_TAC[ARITH_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `p:num`; `q:num`]
    CN_LINEAR_SMALL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(k1 EXP 2 - 1) * (k2 EXP 2 - 1) = N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (X_CHOOSE_THEN `u:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  SUBGOAL_THEN `integer u /\ &0 < u` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(qchar k q) <= &1 /\ &3 <= &q /\ &1 <= &N /\ &1 <= &(p * q) /\
    3 <= q /\ q <= p * q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `3 <= q /\ 1 <= p` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(SPECL [`q:num`; `4`] MOD_LE) THEN
        UNDISCH_TAC `q MOD 4 = 3` THEN ARITH_TAC;
        MP_TAC(SPEC `p:num` PRIME_GE_2) THEN
        UNDISCH_TAC `prime p` THEN SIMP_TAC[] THEN ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `q <= p * q` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * q <= p * q ==> q <= p * q`) THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CLASSNO_SERIES_QCHAR_BOUND; REAL_OF_NUM_LE] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= N`; `3 <= q`; `q <= p * q`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `q:num`; `p * q`; `u:real`; `qchar k q`;
                `b:real`] CN_MAIN_SMALL_HEIGHTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  REMOVE_THEN "feld" (MP_TAC o SPECL
   [`&40 * &k pow 2 * &N pow 2 * &(p * q) pow 3`; `b:real`;
    `u * (&q + qchar k q) * &N / (&6 * &k) * sqrt(&(p * q))`;
    `u pow 2 * (&q + qchar k q) pow 2 * &N pow 2 * &(p * q)`;
    `&36 * &k pow 2`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REPEAT((MATCH_MP_TAC INTEGER_MUL ORELSE MATCH_MP_TAC INTEGER_POW ORELSE
              MATCH_MP_TAC INTEGER_ADD) THEN TRY CONJ_TAC) THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED; CN_MAIN_QCHAR_INTEGER];
      SIMP_TAC[INTEGER_CLOSED];
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LT) THEN
      MAP_EVERY UNDISCH_TAC
       [`&0 < u`; `abs(qchar k q) <= &1`; `&3 <= &q`; `&1 <= &N`;
        `&1 <= &(p * q)`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&1 <= &k` THEN
      REAL_ARITH_TAC;
      MP_TAC(SPEC `&(p * q)` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
      SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
       [UNDISCH_TAC `&1 <= &k` THEN REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `abs(b * log(cyclo_unit k) -
        (u * (&q + qchar k q) * &N / (&6 * &k) * sqrt(&(p * q))) * pi) <=
    &384 * &k * s * exp(--(pi / &k * s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&4 * u * &q * &k *
      (qform_kernel(exp(--(pi * sqrt(&(p * q)) / &k))) +
       qform_kernel(exp(--(pi * sqrt(&(p * q)) / (&q * &k)))))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `qform_kernel` (concl
       th)))
      THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CN_MAIN_SMALL_ERROR THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      TRY(CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `&3 <= &q` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) <= S` ASSUME_TAC THENL
   [REMOVE_THEN "num" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&40 * &k pow 2 * &N pow 2 * &(p * q) pow 3`;
      `abs(b * log(cyclo_unit k) -
           (u * (&q + qchar k q) * &N / (&6 * &k) * sqrt(&(p * q))) * pi)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [SUBGOAL_THEN `&(p * q) pow 3 = s pow 12` SUBST1_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check
         (fun th -> concl th = `s pow 4 = &(p * q)`)) THEN
        REWRITE_TAC[REAL_POW_POW] THEN CONV_TAC NUM_REDUCE_CONV;
        REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `&384` (concl th))) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) pow 4 <= S pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&(p * q) <= &D` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`max (S pow 4) (&k pow 4) <= &D`; `(s:real) pow 4 <= S pow 4`;
      `(s:real) pow 4 = &(p * q)`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `D < p * q` THEN ARITH_TAC]);;

(* The discriminants -4d (d prime = 1 mod 4 or d = 2 p) for one modulus k =  *)
(* k1 k2 (used with k = 21): CN_LINEAR_EVEN and BAKER_FELDMAN.               *)

let CN_MAIN_EVEN_BOUND = prove
 (`!k k1 k2.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ k MOD 4 = 1 /\
     algebraic_number(Cx(cyclo_unit k))
     ==> ?D. !d. (prime d /\ d MOD 4 = 1 \/
                  (?p. prime p /\ ODD p /\ d = 2 * p)) /\
                 coprime(k,d) /\ form_classno (--(&4 * &d)) = 2
                 ==> d <= D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < cyclo_unit k` ASSUME_TAC THENL
   [REWRITE_TAC[cyclo_unit; REAL_EXP_POS_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `cyclo_unit k` CN_MAIN_FELDMAN_TWO) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num` (LABEL_TAC "feld")) THEN
  SUBGOAL_THEN `1 <= k /\ 1 <= (k1 EXP 2 - 1) * (k2 EXP 2 - 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `k = k1 * k2` THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `1 * 1 <= a * b ==> 1 <= a * b`) THEN
      MATCH_MP_TAC LE_MULT2 THEN
      MP_TAC(SPEC `k1:num` PRIME_GE_2) THEN
      MP_TAC(SPEC `k2:num` PRIME_GE_2) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      MATCH_MP_TAC CN_MAIN_N_POS THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `N = (k1 EXP 2 - 1) * (k2 EXP 2 - 1)` THEN
  SUBGOAL_THEN `&1 <= &k /\ &1 <= &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`pi / &k`; `&100 * &k pow 2 * &N pow 2`; `&256 * &k`; `4`;
                `C:num`] CN_MAIN_FELDMAN_NUMERIC) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[PI_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real` (LABEL_TAC "num")) THEN
  X_CHOOSE_TAC `D:num` (SPEC `max (S pow 2) (&k pow 2)` REAL_ARCH_SIMPLE) THEN
  EXISTS_TAC `D:num` THEN X_GEN_TAC `d:num` THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= sqrt(&d) /\ sqrt(&d) pow 2 = &d /\ &D < sqrt(&d) pow 2 /\
    1 <= d /\ &1 <= &d`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_POS; REAL_OF_NUM_LT;
             REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `D < d` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&k <= sqrt(&d) /\ &1 <= sqrt(&d)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL
     [ALL_TAC; UNDISCH_TAC `&1 <= &k` THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[ARITH_EQ] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`max (S pow 2) (&k pow 2) <= &D`; `&D < sqrt(&d) pow 2`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `d:num`] CN_LINEAR_EVEN) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(k1 EXP 2 - 1) * (k2 EXP 2 - 1) = N`] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `abs(qchar k 2) <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[CLASSNO_SERIES_QCHAR_BOUND]; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `d:num`; `qchar k 2`; `b:real`]
    CN_MAIN_EVEN_HEIGHTS) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  REMOVE_THEN "feld" (MP_TAC o SPECL
   [`&100 * &k pow 2 * &N pow 2 * &d pow 2`; `b:real`;
    `(&2 + qchar k 2) * &N / (&3 * &k) * sqrt(&d)`;
    `(&2 + qchar k 2) pow 2 * &N pow 2 * &d`;
    `&9 * &k pow 2`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [REPEAT((MATCH_MP_TAC INTEGER_MUL ORELSE MATCH_MP_TAC INTEGER_POW ORELSE
              MATCH_MP_TAC INTEGER_ADD) THEN TRY CONJ_TAC) THEN
      REWRITE_TAC[INTEGER_CLOSED; CN_MAIN_QCHAR_INTEGER];
      SIMP_TAC[INTEGER_CLOSED];
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LT) THEN
      MAP_EVERY UNDISCH_TAC
       [`abs(qchar k 2) <= &1`; `&1 <= &N`; `&1 <= &d`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_MUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&1 <= &k` THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
       [UNDISCH_TAC `&1 <= &k` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `sqrt(&d) pow 2 = &d` THEN CONV_TAC REAL_FIELD];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `abs(b * log(cyclo_unit k) -
        ((&2 + qchar k 2) * &N / (&3 * &k) * sqrt(&d)) * pi) <=
    &256 * &k * sqrt(&d) * exp(--(pi / &k * sqrt(&d)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&8 * &k * (qform_kernel(exp(--(&2 * pi * sqrt(&d) / &k))) +
                 qform_kernel(exp(--(pi * sqrt(&d) / &k))))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `qform_kernel` (concl
       th)))
      THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CN_MAIN_EVEN_ERROR THEN CONJ_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&d) <= S` ASSUME_TAC THENL
   [REMOVE_THEN "num" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&100 * &k pow 2 * &N pow 2 * &d pow 2`;
      `abs(b * log(cyclo_unit k) -
           ((&2 + qchar k 2) * &N / (&3 * &k) * sqrt(&d)) * pi)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [SUBGOAL_THEN `&d pow 2 = sqrt(&d) pow 4` SUBST1_TAC THENL
       [REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
        SIMP_TAC[SQRT_POW_2; REAL_POS];
        REAL_ARITH_TAC];
      FIRST_X_ASSUM(MP_TAC o check (fun th -> free_in `&256` (concl th))) THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sqrt(&d) pow 2 <= S pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&d <= &D` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`max (S pow 2) (&k pow 2) <= &D`; `sqrt(&d) pow 2 <= S pow 2`;
      `sqrt(&d) pow 2 = &d`] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `D < d` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 10. The headline theorems: the moduli 21, 33, 77, the case analysis of    *)
(*     CN_FORMS_TWO_CASES and the finiteness.                                *)
(* ------------------------------------------------------------------------- *)

let CN_MAIN_K_DATA = prove
 (`(21 = 3 * 7 /\ prime 3 /\ prime 7 /\ ~(3 = 7) /\ 21 MOD 4 = 1 /\
    algebraic_number(Cx(cyclo_unit 21))) /\
   (33 = 3 * 11 /\ prime 3 /\ prime 11 /\ ~(3 = 11) /\ 33 MOD 4 = 1 /\
    algebraic_number(Cx(cyclo_unit 33))) /\
   (77 = 7 * 11 /\ prime 7 /\ prime 11 /\ ~(7 = 11) /\ 77 MOD 4 = 1 /\
    algebraic_number(Cx(cyclo_unit 77)))`,
  REWRITE_TAC[CN_MAIN_K_FACTS] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CN_MAIN_CYCLO_ALGEBRAIC THEN
  REWRITE_TAC[CN_MAIN_K_FACTS] THEN CONV_TAC NUM_REDUCE_CONV);;

let CN_MAIN_MOD4_NE = prove
 (`!p. p MOD 4 = 1 ==> ~(p = 3) /\ ~(p = 7) /\ ~(p = 11)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CN_MAIN_COPRIME_K = prove
 (`!k1 k2 p q. prime k1 /\ prime k2 /\ prime p /\ prime q /\
               ~(p = k1) /\ ~(p = k2) /\ ~(q = k1) /\ ~(q = k2)
               ==> coprime(k1 * k2,p * q)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COPRIME_LMUL; COPRIME_RMUL] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC DISTINCT_PRIME_COPRIME THEN
  ASM_MESON_TAC[]);;

(* The discriminants -d: CN_FORMS_TWO_CASES, k = 21, 33 or 77 for q^4 <= d,  *)
(* the main case otherwise.                                                  *)

let CN_MAIN_ODD_BOUND = prove
 (`?D. !d. squarefree d /\ d MOD 4 = 3 /\ form_classno (--(&d)) = 2
           ==> d <= D`,
  MP_TAC CN_MAIN_K_DATA THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o MATCH_MP CN_MAIN_SMALL_BOUND)
    (CONJUNCTS_THEN2 (MP_TAC o MATCH_MP CN_MAIN_SMALL_BOUND)
                     (MP_TAC o MATCH_MP CN_MAIN_SMALL_BOUND))) THEN
  DISCH_THEN(X_CHOOSE_THEN `D77:num` (LABEL_TAC "s77")) THEN
  DISCH_THEN(X_CHOOSE_THEN `D33:num` (LABEL_TAC "s33")) THEN
  DISCH_THEN(X_CHOOSE_THEN `D21:num` (LABEL_TAC "s21")) THEN
  X_CHOOSE_THEN `DL:num` (LABEL_TAC "large") CN_MAIN_LARGE_BOUND THEN
  EXISTS_TAC `D21 + D33 + D77 + DL + 2401` THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:num` CN_FORMS_TWO_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[qdisc]; ALL_TAC] THEN
  STRIP_TAC THENL
   [ALL_TAC;
    ASM_ARITH_TAC;
    UNDISCH_TAC `d MOD 4 = 3` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MP_TAC(SPEC `d:num` CLASSNO_GAUSS_ODD_MOD4) THEN
    ASM_REWRITE_TAC[ODD_MULT; ARITH]] THEN
  UNDISCH_TAC `d = p * q` THEN DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPEC `p:num` CN_MAIN_MOD4_NE) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `q EXP 4 <= p * q` THENL
   [ASM_CASES_TAC `q = 3` THENL
     [REMOVE_THEN "s77" (MP_TAC o SPECL [`p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `77 = 7 * 11`) THEN
      MATCH_MP_TAC CN_MAIN_COPRIME_K THEN
      ASM_REWRITE_TAC[CN_MAIN_K_FACTS] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    ASM_CASES_TAC `q = 7` THENL
     [REMOVE_THEN "s33" (MP_TAC o SPECL [`p:num`; `q:num`]) THEN
      ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(ARITH_RULE `33 = 3 * 11`) THEN
      MATCH_MP_TAC CN_MAIN_COPRIME_K THEN
      ASM_REWRITE_TAC[CN_MAIN_K_FACTS] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REMOVE_THEN "s21" (MP_TAC o SPECL [`p:num`; `q:num`]) THEN
    ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(ARITH_RULE `21 = 3 * 7`) THEN
    MATCH_MP_TAC CN_MAIN_COPRIME_K THEN ASM_REWRITE_TAC[CN_MAIN_K_FACTS];
    ALL_TAC] THEN
  ASM_CASES_TAC `p * q <= 2401` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(q = 3) /\ ~(q = 7)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(q <= 7)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `q EXP 4 <= 7 EXP 4` MP_TAC THENL
       [ASM_REWRITE_TAC[EXP_MONO_LE]; ALL_TAC] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "large" (MP_TAC o SPECL [`p:num`; `q:num`]) THEN
  ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  SUBST1_TAC(ARITH_RULE `21 = 3 * 7`) THEN
  MATCH_MP_TAC CN_MAIN_COPRIME_K THEN ASM_REWRITE_TAC[CN_MAIN_K_FACTS]);;

let CLASS_NUMBER_TWO_FINITE_ODD = prove
 (`FINITE {d | squarefree d /\ d MOD 4 = 3 /\ form_classno (--(&d)) = 2}`,
  X_CHOOSE_TAC `D:num` CN_MAIN_ODD_BOUND THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d:num | d <= D}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* All squarefree d: the odd bound for d = p q, the even bound with k = 21   *)
(* for d prime = 1 mod 4 and d = 2 p (d > 14 is coprime to 21).              *)

let CN_MAIN_ALL_BOUND = prove
 (`?D. !d. squarefree d /\ form_classno (qdisc d) = 2 ==> d <= D`,
  X_CHOOSE_THEN `DO:num` (LABEL_TAC "odd") CN_MAIN_ODD_BOUND THEN
  MP_TAC(MATCH_MP CN_MAIN_EVEN_BOUND (CONJUNCT1 CN_MAIN_K_DATA)) THEN
  DISCH_THEN(X_CHOOSE_THEN `DE:num` (LABEL_TAC "even")) THEN
  EXISTS_TAC `DO + DE + 14` THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN
  MP_TAC(SPEC `d:num` CN_FORMS_TWO_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 MP_TAC ASSUME_TAC) THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `d MOD 4 = 3` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    REMOVE_THEN "odd" (MP_TAC o SPEC `d:num`) THEN
    ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN
    UNDISCH_TAC `form_classno (qdisc d) = 2` THEN
    ASM_REWRITE_TAC[qdisc];
    ALL_TAC] THEN
  ASM_CASES_TAC `d <= 14` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(d MOD 4 = 3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
      check (is_disj o concl)) THENL
     [ASM_REWRITE_TAC[] THEN ARITH_TAC;
      DISCH_TAC THEN MP_TAC(SPEC `d:num` CLASSNO_GAUSS_ODD_MOD4) THEN
      ASM_REWRITE_TAC[ODD_MULT; ARITH]];
    ALL_TAC] THEN
  REMOVE_THEN "even" (MP_TAC o SPEC `d:num`) THEN
  ANTS_TAC THENL [ALL_TAC; ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
      check (is_disj o concl)) THENL
     [MATCH_MP_TAC CN_MAIN_COPRIME_21_PRIME THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ASM_REWRITE_TAC[COPRIME_RMUL] THEN CONJ_TAC THENL
       [CONV_TAC COPRIME_CONV;
        MATCH_MP_TAC CN_MAIN_COPRIME_21_PRIME THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC]];
    UNDISCH_TAC `form_classno (qdisc d) = 2` THEN
    ASM_REWRITE_TAC[qdisc]]);;

let CLASS_NUMBER_TWO_FINITE = prove
 (`FINITE {d | squarefree d /\ form_classno (qdisc d) = 2}`,
  X_CHOOSE_TAC `D:num` CN_MAIN_ALL_BOUND THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d:num | d <= D}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LE; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;
