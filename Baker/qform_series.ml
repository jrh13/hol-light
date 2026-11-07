(* ========================================================================= *)
(* The lattice series of a positive definite binary quadratic form twisted   *)
(* by a real character: the Dirichlet series for s > 1 and the sum of the    *)
(* slices as s -> 1+ (the general form layer of the class number one and two *)
(* problems).                                                                *)
(*                                                                           *)
(* Purpose: for a positive definite form F = (a,b,c) (a > 0,                 *)
(* D = 4 a c - b^2 > 0, F(x,y) = qform a b c x y) and chi_k = qchar k, the   *)
(* lattice sum of chi_k(F) / F^s over the integer pairs (x,y) <> (0,0) is    *)
(* regrouped in two ways. QFORM_DIRICHLET_SERIES (any k, s > 1): the         *)
(* Dirichlet series of the representation numbers r_F = qform_rep a b c, the *)
(* sum over l >= 1 of chi_k(l) r_F(l) / l^s, is 2 chi_k(a) a^-s zeta_k(2 s)  *)
(* (the row y = 0) plus 2 times the sum over y >= 1 of the slices            *)
(* S_y(s) = qform_slice k a b c s y (the rows y and -y agree by              *)
(* (x,y) -> (-x,-y)). QFORM_SLICE_SERIES_CONTINUOUS (k = k1 k2 a product of  *)
(* two distinct odd primes, prime to a and to D): the series of the slices   *)
(* converges for s >= 1 and its sum is continuous at s = 1 from the right.   *)
(* The limit tools CNP_* for the products of L-series at s = 1               *)
(* (QFORM_SERIES_SLICE_LIMIT, QFORM_SERIES_QCHAR_LIMIT,                      *)
(* QFORM_SERIES_ZETA_LIMIT, QFORM_SERIES_LIMIT_EQ,                           *)
(* QFORM_SERIES_SUMS_COMBINE) are used by the product identities of          *)
(* the class number one problem (Baker/classno_product.ml) and of the class  *)
(* number two problem (Baker/cn_products.ml).                                *)
(*                                                                           *)
(* Method: (1) absolute convergence without a representation formula:        *)
(* 4 a F >= y^2 and 4 c F >= x^2 give (|x| + 1) (|y| + 1) <=                 *)
(* 8 (a + c) F(x,y) off (0,0), so the box sums of F^-s are at most           *)
(* (8 (a + c))^s (2 zeta(s))^2 and the series of r_F(l) / l^s converges      *)
(* (QFORM_SERIES_WS_SUMMABLE). Counting lattice points in boxes of size B N, *)
(* B = 4 (a + c), and the limits of the rows give the regrouping             *)
(* (QFORM_SERIES_ROWS_TENDS, QFORM_SERIES_ROWS_SYM). (2) For y >= 1 the      *)
(* slice is scaled by (4 a)^-s: its terms are chi_k(F) / (4 a F)^s with      *)
(* 4 a F = (2 a x + b y)^2 + D y^2 >= y^2, which gives bounds uniform in     *)
(* s >= 1. The residue classes x = m + k n and UNIMODAL_SHIFT with spacing   *)
(* 2 a k (QFORM_SERIES_SLICE_DECOMP) give                                    *)
(* (4 a)^-s S_y(s) = c(y) Psi_y(s) + O(k / y^2), where c(y), the sum over m  *)
(* < k of chi_k(F(m,y)), is chi_k(a) c_k(y) by the Ramanujan identity        *)
(* QFORM_LIMIT_RAMANUJAN, periodic of mean zero, and Psi_y(s) <= 8 / y       *)
(* decreases in y. The Dirichlet test gives the block bound (32 k^2 + 4 k) / *)
(* m uniform in s >= 1 (QFORM_SERIES_TSUM_BLOCK), hence the continuity of    *)
(* the scaled sum; the factor (4 a)^s is continuous.                         *)
(*                                                                           *)
(* Main results: QFORM_DIRICHLET_SERIES, QFORM_SLICE_SERIES_CONTINUOUS,      *)
(* QFORM_SERIES_SLICE_LIMIT; QFORM_SERIES_WS_SUMMABLE,                       *)
(* QFORM_SERIES_SLICE_DECOMP, QFORM_SERIES_TSUM_BLOCK,                       *)
(* QFORM_SERIES_LIMIT_EQ, QFORM_SERIES_LSERIES_LIMIT,                        *)
(* QFORM_SERIES_QCHAR_LIMIT, QFORM_SERIES_ZETA_LIMIT,                        *)
(* QFORM_SERIES_SUMS_COMBINE; helper names CNS_*, CNP_*.                     *)
(*                                                                           *)
(* Uses: Baker/classno_defs.ml (qform, qform_rep), Baker/classno_chardefs.ml *)
(* (qchar, zeta_coprime, qform_term, qform_slice), Baker/qform_limit.ml      *)
(* (QFORM_LIMIT_RAMANUJAN, QFORM_LIMIT_4A), Baker/classno_series.ml          *)
(* (QCHAR_DIRICHLET, CLASSNO_SERIES_BLOCK_TAIL, _UNIFORM_CONTINUOUS,         *)
(* _BOX_SUM, _BOX_NEG, _BOX_LIMIT, _BOX_MONO, _PAIRED_BLOCKS,                *)
(* _PERIODIC_BOUND, _DIRICHLET_BOUND, _KERNEL_*, _PSI_*, _QCHAR_BOUND,       *)
(* _QCHAR_CONG, _QCHAR_LMUL, _SUM_BLOCKS, _SUM_DELTA_SWAP, _ZETA_CONTINUOUS, *)
(* _ZETA_EQ, _RPOW_TERM_CONTINUOUS, _INV_SQUARE_BLOCK, _INV_SQUARE_BLOCK1,   *)
(* _REALLIM_SUBSEQ, _ABS_MUL_LE, _NONTRIVIAL, _LFUNCTION_REAL,               *)
(* _WITHIN_LIMIT), Baker/classno_series_lib.ml (UNIMODAL_SHIFT,              *)
(* LSERIES_RIGHT_CONTINUOUS), Baker/classno_rep.ml                           *)
(* (CLASSNO_REP_ABS_LE_POW2); Library/jacobi.ml (JACOBI_SQUARED),            *)
(* 100/dirichlet.ml (dirichlet_character, chi_0, Lfunction),                 *)
(* Multivariate/realanalysis.ml (REAL_SUMMABLE_ZETA,                         *)
(* REAL_SUMMABLE_POS_PARTIAL_BOUND).                                         *)
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
needs "ANT/frobenius_density.ml";;
needs "Baker/classno_rep.ml";;
needs "Baker/qform_limit.ml";;

prioritize_real();;
prioritize_num();;

(* The helper lemmas are parsed with real arithmetic as the default; the     *)
(* three main results are parsed after prioritize_num, the project default.  *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Arithmetic of a positive definite form F = (a,b,c), D = 4 a c - b^2:      *)
(* lower bounds, symmetry, congruences.                                      *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_FORM_C_POS = prove
 (`!a b c:int. &0 < a /\ &0 < &4 * a * c - b pow 2 ==> &0 < c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0:int <= a * --c` MP_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `b:int` INT_LE_POW_2) THEN
  UNDISCH_TAC `&0:int < &4 * a * c - b pow 2` THEN INT_ARITH_TAC);;

let QFORM_SERIES_FORM_4C = prove
 (`!a b c x y:int.
     &4 * c * qform a b c x y =
     (&2 * c * y + b * x) pow 2 + (&4 * a * c - b pow 2) * x pow 2`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_SERIES_FORM_LOWER = prove
 (`!a b c x y:int.
     &0 < a /\ &0 < &4 * a * c - b pow 2
     ==> &0 <= qform a b c x y /\
         y pow 2 <= &4 * a * qform a b c x y /\
         x pow 2 <= &4 * c * qform a b c x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0:int <= (&4 * a * c - b pow 2 - &1) * y pow 2 /\
    &0:int <= (&4 * a * c - b pow 2 - &1) * x pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_LE_POW_2] THEN
    UNDISCH_TAC `&0:int < &4 * a * c - b pow 2` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_LIMIT_4A) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_4C) THEN
  MP_TAC(SPEC `&2 * a * x + b * y:int` INT_LE_POW_2) THEN
  MP_TAC(SPEC `&2 * c * y + b * x:int` INT_LE_POW_2) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `y pow 2 <= &4 * a * qform a b c x y /\
                x pow 2 <= &4 * c * qform a b c x y`
  STRIP_ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `&0:int <= a * qform a b c x y` MP_TAC THENL
   [MP_TAC(SPEC `y:int` INT_LE_POW_2) THEN
    UNDISCH_TAC `y pow 2 <= &4 * a * qform a b c x y` THEN INT_ARITH_TAC;
    ASM_SIMP_TAC[INT_LE_MUL_EQ]]);;

let QFORM_SERIES_FORM_POS = prove
 (`!a b c x y:int.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ ~(x = &0 /\ y = &0)
     ==> &1 <= qform a b c x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1:int <= x pow 2 + y pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:int` CLASSNO_REP_ABS_LE_POW2) THEN
    MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN
    MP_TAC(SPEC `x:int` INT_LE_POW_2) THEN
    MP_TAC(SPEC `y:int` INT_LE_POW_2) THEN
    UNDISCH_TAC `~(x:int = &0 /\ y:int = &0)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0:int < (a + c) * qform a b c x y` MP_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0:int < a + c` (fun th -> SIMP_TAC[INT_LT_MUL_EQ; th]) THENL
   [ASM_INT_ARITH_TAC; INT_ARITH_TAC]);;

let QFORM_SERIES_FORM_NEG = prove
 (`!a b c x y:int. qform a b c (--x) (--y) = qform a b c x y`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_SERIES_FORM_NEG2 = prove
 (`!a b c x y:int. qform a b c x (--y) = qform a b c (--x) y`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_SERIES_FORM_CONG = prove
 (`(!a b c x y t k.
      (qform a b c (x + &k * t) y == qform a b c x y) (mod &k)) /\
   (!a b c x y t k.
      (qform a b c x (y + &k * t) == qform a b c x y) (mod &k))`,
  REWRITE_TAC[qform] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN
  CONV_TAC INTEGER_RULE);;

let QFORM_SERIES_FORM_ROW0 = prove
 (`!a b c x:int. qform a b c x (&0) = a * x pow 2`,
  REWRITE_TAC[qform] THEN INT_ARITH_TAC);;

let QFORM_SERIES_FORM_REAL_POS = prove
 (`!a b c:int.
     &0 < a /\ &0 < &4 * a * c - b pow 2
     ==> &1 <= real_of_int a /\ &1 <= real_of_int c /\
         &1 <= real_of_int(&4 * a * c - b pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM int_of_num_th; GSYM int_le] THEN ASM_INT_ARITH_TAC);;

let QFORM_SERIES_FORM_REAL_4A = prove
 (`!a b c x y:int.
     &4 * real_of_int a * real_of_int(qform a b c x y) =
     ((&2 * real_of_int a) * real_of_int x + real_of_int b * real_of_int y)
     pow 2 + real_of_int(&4 * a * c - b pow 2) * real_of_int y pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_LIMIT_4A) THEN
  DISCH_THEN(MP_TAC o AP_TERM `real_of_int`) THEN
  REWRITE_TAC[int_add_th; int_mul_th; int_pow_th; int_sub_th;
              int_of_num_th] THEN
  REAL_ARITH_TAC);;

let QFORM_SERIES_FORM_ROW_LOWER = prove
 (`!a b c x y:int.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ ~(y = &0)
     ==> &1 <= real_of_int(qform a b c x y) /\
         real_of_int x pow 2 + &1 <=
         &8 * real_of_int c * real_of_int(qform a b c x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_POS) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0:int <= c * (qform a b c x y - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1:int <= qform a b c x y /\
    x pow 2 + &1 <= &8 * c * qform a b c x y`
  MP_TAC THENL
   [ASM_INT_ARITH_TAC;
    REWRITE_TAC[int_le; int_add_th; int_mul_th; int_pow_th; int_of_num_th]]);;

let QFORM_SERIES_FORM_NUM_REAL = prove
 (`!a b c x y:int.
     &0 < a /\ &0 < &4 * a * c - b pow 2
     ==> &(num_of_int(qform a b c x y)) = real_of_int(qform a b c x y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM int_of_num_th] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  ASM_SIMP_TAC[]);;

let QFORM_SERIES_FORM_BOX = prove
 (`!a b c x y:int N B.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &4 * (a + c) <= &B /\
     qform a b c x y <= &N
     ==> abs x <= &(B * N) /\ abs y <= &(B * N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `a * qform a b c x y <= a * &N /\ c * qform a b c x y <= c * &N /\
    (&4 * (a + c)) * &N <= &B * &N`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
      MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
      MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[INT_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0:int <= a * &N /\ &0:int <= c * &N` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_POS] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:int` CLASSNO_REP_ABS_LE_POW2) THEN
  MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN ASM_INT_ARITH_TAC);;

let QFORM_SERIES_FORM_PROD_BOUND = prove
 (`!a b c x y:int.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ ~(x = &0 /\ y = &0)
     ==> (abs x + &1) * (abs y + &1) <= (&8 * (a + c)) * qform a b c x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_POS) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0:int <= (a + c - &1) * qform a b c x y` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `abs x - abs y:int` INT_LE_POW_2) THEN
  MP_TAC(SPEC `x:int` CLASSNO_REP_ABS_LE_POW2) THEN
  MP_TAC(SPEC `y:int` CLASSNO_REP_ABS_LE_POW2) THEN
  MP_TAC(SPEC `x:int` INT_POW2_ABS) THEN MP_TAC(SPEC `y:int` INT_POW2_ABS) THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The rows y <> 0 as functions of s >= 1: the terms are at most             *)
(* 8 c / (x^2 + 1), uniformly in s; summability, box limits, continuity in   *)
(* s, symmetry.                                                              *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_TERM_BOUND = prove
 (`!k a b c s x y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 <= s /\ ~(y = &0)
     ==> abs(qform_term k a b c s x y) <=
         (&8 * real_of_int c) * inv(real_of_int x pow 2 + &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_ROW_LOWER) THEN
  ASM_REWRITE_TAC[qform_term] THEN
  SPEC_TAC(`real_of_int(qform a b c x y)`,`ff:real`) THEN
  GEN_TAC THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ff <= ff rpow s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1`; `s:real`; `ff:real`] RPOW_MONO_LE) THEN
    ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < ff` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_DIV] THEN
  SUBGOAL_THEN `abs(ff rpow s) = ff rpow s` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(ff)` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_ABS_POS; CLASSNO_SERIES_QCHAR_BOUND] THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&8 * real_of_int c) * inv(real_of_int x pow 2 + &1) =
    inv((real_of_int x pow 2 + &1) / (&8 * real_of_int c))`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_INV_DIV; real_div]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `&0 < &8 * real_of_int c` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `real_of_int x` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let QFORM_SERIES_PAIRED_BLOCK_BOUND = prove
 (`!h:int->real M m N.
     (!x. abs(h x) <= M * inv(real_of_int x pow 2 + &1))
     ==> abs(sum(m..N) (\n. h(&n) + h(--(&n) - &1))) <=
         (&6 * M) / (&m + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&0:int`) THEN
    REWRITE_TAC[int_of_num_th] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..N) (\n. (&3 * M) * inv((&n + &1) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..N) (\n. abs((h:int->real)(&n) + h(--(&n) - &1)))` THEN
    REWRITE_TAC[SUM_ABS_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN BETA_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `&n:int`) THEN
    FIRST_ASSUM(MP_TAC o SPEC `--(&n) - &1:int`) THEN
    REWRITE_TAC[int_sub_th; int_neg_th; int_of_num_th] THEN
    REWRITE_TAC[REAL_ARITH `(--x - &1) pow 2 = (x + &1) pow 2`] THEN
    SUBGOAL_THEN
     `M * inv(&n pow 2 + &1) <= M * (&2 * inv((&n + &1) pow 2)) /\
      M * inv((&n + &1) pow 2 + &1) <= M * inv((&n + &1) pow 2)`
    MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `&2 * inv((&n + &1) pow 2) = inv((&n + &1) pow 2 / &2)`
        SUBST1_TAC THENL
         [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x / &2`) THEN
          MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
          REWRITE_TAC[REAL_POW_2] THEN
          MP_TAC(SPEC `&n - &1` REAL_LE_SQUARE) THEN REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; REAL_ARITH_TAC]];
      REAL_ARITH_TAC];
    REWRITE_TAC[SUM_LMUL] THEN
    MP_TAC(SPECL [`m:num`; `N:num`] CLASSNO_SERIES_INV_SQUARE_BLOCK1) THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&3 * M) * &2 / (&m + &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]]);;

let QFORM_SERIES_ROW_BLOCK = prove
 (`!k a b c s y m N.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 <= s /\ ~(y = &0)
     ==> abs(sum(m..N) (\n. qform_term k a b c s (&n) y +
                            qform_term k a b c s (--(&n) - &1) y)) <=
         (&6 * (&8 * real_of_int c)) / (&m + &1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x. qform_term k a b c s x y`; `&8 * real_of_int c`;
                 `m:num`; `N:num`] QFORM_SERIES_PAIRED_BLOCK_BOUND) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC QFORM_SERIES_TERM_BOUND THEN ASM_REWRITE_TAC[]);;

let QFORM_SERIES_ROW_SUMMABLE = prove
 (`!k a b c s y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 <= s /\ ~(y = &0)
     ==> real_summable (from 0)
          (\n. qform_term k a b c s (&n) y +
               qform_term k a b c s (--(&n) - &1) y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n. qform_term k a b c s (&n) y + qform_term k a b c s (--(&n) - &1) y`;
    `\m. (&6 * (&8 * real_of_int c)) / (&m + &1)`; `0`]
   CLASSNO_SERIES_BLOCK_TAIL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
      REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
      REPEAT STRIP_TAC THEN BETA_TAC THEN
        MATCH_MP_TAC QFORM_SERIES_ROW_BLOCK THEN
      ASM_REWRITE_TAC[]];
    SIMP_TAC[]]);;

let QFORM_SERIES_ROW_LIMIT = prove
 (`!k a b c s y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 <= s /\ ~(y = &0)
     ==> ((\X. sum {x:int | --(&X) <= x /\ x <= &X}
                (\x. qform_term k a b c s x y)) --->
          real_infsum (from 0)
           (\n. qform_term k a b c s (&n) y +
                qform_term k a b c s (--(&n) - &1) y)) sequentially`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. qform_term k a b c s x y`;
    `real_infsum (from 0)
      (\n. qform_term k a b c s (&n) y +
           qform_term k a b c s (--(&n) - &1) y)`]
   CLASSNO_SERIES_BOX_LIMIT) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_SUMS_INFSUM] THEN
    MATCH_MP_TAC QFORM_SERIES_ROW_SUMMABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REALLIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. (&8 * real_of_int c) * inv(&n + &1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `0` THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&8 * real_of_int c) *
                inv(real_of_int(--(&n) - &1) pow 2 + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC QFORM_SERIES_TERM_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[int_sub_th; int_neg_th; int_of_num_th] THEN
    REWRITE_TAC[REAL_ARITH `(--x - &1) pow 2 = (x + &1) * (x + &1)`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ &0 <= x * x ==> x + &1 <= (x + &1) * (x + &1) + &1`) THEN
    REWRITE_TAC[REAL_LE_SQUARE; REAL_POS];
    MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[REALLIM_1_OVER_N_OFFSET]]);;

let QFORM_SERIES_ROW_CONTINUOUS = prove
 (`!k a b c y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ ~(y = &0)
     ==> (\s. real_infsum (from 0)
               (\n. qform_term k a b c s (&n) y +
                    qform_term k a b c s (--(&n) - &1) y))
         real_continuous (atreal (&1) within {s | &1 <= s})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\s n. qform_term k a b c s (&n) y + qform_term k a b c s (--(&n) - &1) y`;
    `\m. (&6 * (&8 * real_of_int c)) / (&m + &1)`; `{s:real | &1 <= s}`;
    `&1`; `0`]
   CLASSNO_SERIES_UNIFORM_CONTINUOUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[REALLIM_1_OVER_N_OFFSET];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC QFORM_SERIES_ROW_BLOCK THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    REWRITE_TAC[qform_term] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CLASSNO_SERIES_RPOW_TERM_CONTINUOUS THEN
    MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN
    ASM_SIMP_TAC[QFORM_SERIES_FORM_ROW_LOWER]]);;

let QFORM_SERIES_PS_NEG = prove
 (`!k a b c s y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 <= s /\ ~(y = &0)
     ==> real_infsum (from 0)
          (\n. qform_term k a b c s (&n) (--y) +
               qform_term k a b c s (--(&n) - &1) (--y)) =
         real_infsum (from 0)
          (\n. qform_term k a b c s (&n) y +
               qform_term k a b c s (--(&n) - &1) y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
  EXISTS_TAC `\X. sum {x:int | --(&X) <= x /\ x <= &X}
                   (\x. qform_term k a b c s x y)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC QFORM_SERIES_ROW_LIMIT THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `s:real`; `--y:int`]
    QFORM_SERIES_ROW_LIMIT) THEN
  ASM_REWRITE_TAC[INT_NEG_EQ_0] THEN
  SUBGOAL_THEN
   `!x. qform_term k a b c s x (--y) = qform_term k a b c s (--x) y`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[qform_term; QFORM_SERIES_FORM_NEG2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x. qform_term k a b c s x y`] CLASSNO_SERIES_BOX_NEG) THEN
  REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* The row y = 0: 2 chi_k(a) a^-s zeta_k(2 s).                               *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_TERM_ZERO = prove
 (`!k a b c s. &0 < s ==> qform_term k a b c s (&0) (&0) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qform_term; QFORM_SERIES_FORM_ROW0] THEN
  REWRITE_TAC[INT_ARITH `a * &0 pow 2 = &0:int`; int_of_num_th] THEN
  ASM_SIMP_TAC[RPOW_ZERO; REAL_LT_IMP_NZ; real_div; REAL_INV_0;
               REAL_MUL_RZERO]);;

let QFORM_SERIES_ROW0_TERM = prove
 (`!k a b c s n.
     &0 < a
     ==> qform_term k a b c s (&n) (&0) =
         qchar k (num_of_int a) / real_of_int a rpow s *
         (if coprime(n,k) then inv((&n pow 2) rpow s) else &0) /\
         qform_term k a b c s (--(&n)) (&0) =
         qchar k (num_of_int a) / real_of_int a rpow s *
         (if coprime(n,k) then inv((&n pow 2) rpow s) else &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?A. a:int = &A` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `num_of_int a` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_SIMP_TAC[INT_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[qform_term; QFORM_SERIES_FORM_ROW0; INT_ARITH `(--x:int) pow 2 =
    x pow 2`;
              INT_OF_NUM_POW; INT_OF_NUM_MUL; NUM_OF_INT_OF_NUM;
              int_of_num_th] THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_LMUL; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_POW; RPOW_MUL] THEN
  REWRITE_TAC[qchar; JACOBI_SQUARED] THEN
  COND_CASES_TAC THEN REWRITE_TAC[int_of_num_th] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; REAL_MUL_RID; REAL_MUL_RZERO;
              REAL_MUL_LZERO] THEN
  REAL_ARITH_TAC);;

let QFORM_SERIES_ROW0_LIMIT = prove
 (`!k a b c s.
     &0 < a /\ &1 <= s
     ==> ((\X. sum {x:int | --(&X) <= x /\ x <= &X}
                (\x. qform_term k a b c s x (&0))) --->
          &2 * qchar k (num_of_int a) / real_of_int a rpow s *
          real_infsum (from 1)
           (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0))
         sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLASSNO_SERIES_BOX_SUM] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[QFORM_SERIES_TERM_ZERO] THEN
    ASM_SIMP_TAC[QFORM_SERIES_ROW0_TERM] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_ARITH `x + x = &2 * x`; SUM_LMUL] THEN
  MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_LMUL THEN
  REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
  MP_TAC(SPEC `k:num` CLASSNO_SERIES_ZETA_CONTINUOUS) THEN
  DISCH_THEN(MP_TAC o SPEC `s:real` o CONJUNCT1) THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Counting lattice points by the value of F in boxes of size B N,           *)
(* B >= 4 (a + c).                                                           *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_COUNT_BOX = prove
 (`!a b c l B X Y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &4 * (a + c) <= &B /\
     B * l <= X /\ B * l <= Y
     ==> sum {x:int | --(&X) <= x /\ x <= &X}
          (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                (\y. if num_of_int(qform a b c x y) = l then &1 else &0)) =
         &(qform_rep a b c l)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_INT_SEG] THEN
  REWRITE_TAC[LAMBDA_PAIR; GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_PRODUCT_DEPENDENT;
           FINITE_INT_SEG; REAL_MUL_RID] THEN
  REWRITE_TAC[qform_rep; REAL_OF_NUM_EQ] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM;
              FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `num_of_int(qform a b c x y) = l <=> qform a b c x y = &l`
  SUBST1_TAC THENL
   [EQ_TAC THENL
     [DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[INT_OF_NUM_OF_INT];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM]];
    ALL_TAC] THEN
  EQ_TAC THENL [SIMP_TAC[]; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`; `l:num`;
                `B:num`] QFORM_SERIES_FORM_BOX) THEN
  ASM_REWRITE_TAC[INT_LE_REFL] THEN
  SUBGOAL_THEN `&(B * l):int <= &X /\ &(B * l):int <= &Y` MP_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; INT_ARITH_TAC]);;

let QFORM_SERIES_LATTICE_COUNT = prove
 (`!a b c h N B X Y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &4 * (a + c) <= &B /\
     h 0 = &0 /\ B * N <= X /\ B * N <= Y
     ==> sum {x:int | --(&X) <= x /\ x <= &X}
          (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                (\y. if num_of_int(qform a b c x y) <= N
                     then h(num_of_int(qform a b c x y)) else &0)) =
         sum(1..N) (\l. &(qform_rep a b c l) * h l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{x:int | --(&X) <= x /\ x <= &X}`;
                 `{y:int | --(&Y) <= y /\ y <= &Y}`;
                 `\x y. num_of_int(qform a b c x y)`; `h:num->real`; `N:num`]
    CLASSNO_SERIES_SUM_DELTA_SWAP) THEN
  REWRITE_TAC[FINITE_INT_SEG] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `l:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[REAL_MUL_SYM] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC QFORM_SERIES_COUNT_BOX THEN EXISTS_TAC `B:num` THEN
    ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `B * l <= B * N:num` MP_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
  UNDISCH_TAC `B * N <= X:num` THEN UNDISCH_TAC `B * N <= Y:num` THEN
  ARITH_TAC);;

let QFORM_SERIES_LATTICE_TAIL = prove
 (`!a b c h H N B X Y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &4 * (a + c) <= &B /\
     h 0 = &0 /\ H 0 = &0 /\ (!l. abs(h l) <= H l) /\
     B * N <= X /\ B * N <= Y
     ==> ?M. N <= M /\
             abs(sum {x:int | --(&X) <= x /\ x <= &X}
                  (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                        (\y. h(num_of_int(qform a b c x y)))) -
                 sum(1..N) (\l. &(qform_rep a b c l) * h l))
             <= sum(1..M) (\l. &(qform_rep a b c l) * H l) -
                sum(1..N) (\l. &(qform_rep a b c l) * H l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= B` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:int#int. num_of_int(qform a b c (FST p) (SND p))`;
                 `{x:int | --(&X) <= x /\ x <= &X} CROSS
                  {y:int | --(&Y) <= y /\ y <= &Y}`]
    UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[FINITE_CROSS_EQ; FINITE_INT_SEG; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_TAC `m0:num`) THEN EXISTS_TAC `m0 + N + X + Y:num` THEN
  REWRITE_TAC[ARITH_RULE `N <= m0 + N + X + Y:num`] THEN
  SUBGOAL_THEN `!l. &0 <= (H:num->real) l` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  ABBREV_TAC `M = m0 + N + X + Y:num` THEN
  SUBGOAL_THEN `N <= M:num` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `X <= B * M /\ Y <= B * M /\ B * N <= B * M:num`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `M <= B * M:num` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `M = 1 * M:num`] THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL];
      ALL_TAC] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN EXPAND_TAC "M" THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `h:num->real`; `N:num`;
                `B:num`; `X:num`; `Y:num`] QFORM_SERIES_LATTICE_COUNT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `H:num->real`; `N:num`;
                `B:num`; `B * M:num`; `B *
                  M:num`] QFORM_SERIES_LATTICE_COUNT) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `H:num->real`; `M:num`;
                `B:num`; `B * M:num`; `B *
                  M:num`] QFORM_SERIES_LATTICE_COUNT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  SIMP_TAC[GSYM SUM_SUB; FINITE_INT_SEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {x:int | --(&X) <= x /\ x <= &X}
     (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
       (\y. (if num_of_int(qform a b c x y) <= M
             then (H:num->real)(num_of_int(qform a b c x y)) else &0) -
            (if num_of_int(qform a b c x y) <= N
             then H(num_of_int(qform a b c x y)) else &0)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CLASSNO_SERIES_BOX_MONO THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN BETA_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_LE_REFL; REAL_SUB_RZERO] THEN
    UNDISCH_TAC `N <= M:num` THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {x:int | --(&X) <= x /\ x <= &X}
     (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
       (\y. abs((h:num->real)(num_of_int(qform a b c x y)) -
                (if num_of_int(qform a b c x y) <= N
                 then h(num_of_int(qform a b c x y)) else &0))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {x:int | --(&X) <= x /\ x <= &X}
       (\x. abs(sum {y:int | --(&Y) <= y /\ y <= &Y}
         (\y. (h:num->real)(num_of_int(qform a b c x y)) -
              (if num_of_int(qform a b c x y) <= N
               then h(num_of_int(qform a b c x y)) else &0))))` THEN
    SIMP_TAC[SUM_ABS; FINITE_INT_SEG] THEN
    MATCH_MP_TAC SUM_LE THEN SIMP_TAC[SUM_ABS; FINITE_INT_SEG];
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
    X_GEN_TAC `x:int` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
    X_GEN_TAC `y:int` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:int`; `y:int`] o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `m0:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `num_of_int(qform a b c x y) <= M` ASSUME_TAC THENL
     [EXPAND_TAC "M" THEN UNDISCH_TAC `num_of_int(qform a b c x y) <= m0` THEN
      ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_LE_REFL; REAL_SUB_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Absolute convergence for s > 1: the box sums of F^-s are bounded by       *)
(* (8 (a + c))^s (2 zeta(s))^2.                                              *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_INV_RPOW_BOUND = prove
 (`!a b c x y:int s.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &0 < s
     ==> inv(real_of_int(qform a b c x y) rpow s) <=
         (&8 * (real_of_int a + real_of_int c)) rpow s *
         inv((abs(real_of_int x) + &1) rpow s) *
         inv((abs(real_of_int y) + &1) rpow s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `K = &8 * (real_of_int a + real_of_int c)` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs(real_of_int x) + &1 /\ &0 < abs(real_of_int y) + &1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MP_TAC(SPEC `real_of_int x` REAL_ABS_POS) THEN
    MP_TAC(SPEC `real_of_int y` REAL_ABS_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `K rpow s * inv((abs(real_of_int x) + &1) rpow s) *
    inv((abs(real_of_int y) + &1) rpow s) =
    inv((((abs(real_of_int x) + &1) * (abs(real_of_int y) + &1)) / K)
        rpow s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[RPOW_DIV; RPOW_MUL; REAL_INV_DIV; REAL_INV_MUL; real_div;
                REAL_INV_INV] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x:int = &0 /\ y:int = &0` THENL
   [SUBGOAL_THEN `qform a b c x y = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST1_TAC) THEN REWRITE_TAC[qform] THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[int_of_num_th; RPOW_ZERO; REAL_LT_IMP_NZ; REAL_INV_0] THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= x + &1`) THEN
      REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_PROD_BOUND) THEN
  ASM_REWRITE_TAC[int_le; int_mul_th; int_add_th; int_abs_th;
                  int_of_num_th] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  MATCH_MP_TAC RPOW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_DIV; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  ASM_REAL_ARITH_TAC);;

let QFORM_SERIES_BOX_INV_SUM = prove
 (`!s X. &1 < s
         ==> sum {x:int | --(&X) <= x /\ x <= &X}
              (\x. inv((abs(real_of_int x) + &1) rpow s)) <=
             &2 * real_infsum (from 1) (\n. inv(&n rpow s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(1..X + 1) (\n. inv(&n rpow s)) <=
    real_infsum (from 1) (\n. inv(&n rpow s))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`\n. inv(&n rpow s)`; `from 1`; `X + 1`]
      REAL_PARTIAL_SUMS_LE_INFSUM) THEN
    REWRITE_TAC[FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[REAL_SUMMABLE_ZETA] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; ARITH_RULE `1 <= X + 1`] THEN
  REWRITE_TAC[SUM_OFFSET; RPOW_ONE; REAL_INV_1] THEN
  REWRITE_TAC[CLASSNO_SERIES_BOX_SUM; int_of_num_th; int_neg_th;
              REAL_ABS_NUM; REAL_ABS_NEG; REAL_ADD_LID; RPOW_ONE;
              REAL_INV_1; GSYM REAL_OF_NUM_ADD; SUM_ADD_NUMSEG] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s z:real. &1 + s <= z ==> &1 + s + s <= &2 * z`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let QFORM_SERIES_BOX_INV_BOUND = prove
 (`!a b c s X Y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 < s
     ==> sum {x:int | --(&X) <= x /\ x <= &X}
          (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                (\y. inv(real_of_int(qform a b c x y) rpow s))) <=
         (&8 * (real_of_int a + real_of_int c)) rpow s *
         (&2 * real_infsum (from 1) (\n. inv(&n rpow s))) pow 2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {x:int | --(&X) <= x /\ x <= &X}
     (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
       (\y. (&8 * (real_of_int a + real_of_int c)) rpow s *
            inv((abs(real_of_int x) + &1) rpow s) *
            inv((abs(real_of_int y) + &1) rpow s)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
    REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC QFORM_SERIES_INV_RPOW_BOUND THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LE THEN
    MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[QFORM_SERIES_BOX_INV_SUM] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[FINITE_INT_SEG; REAL_LE_INV_EQ] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC RPOW_POS_LE THEN
  MP_TAC(SPEC `real_of_int x` REAL_ABS_POS) THEN REAL_ARITH_TAC);;

let QFORM_SERIES_WS_SUMMABLE = prove
 (`!a b c s.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 < s
     ==> real_summable (from 1)
          (\l. &(qform_rep a b c l) * inv(&l rpow s))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[REAL_SUMMABLE_POS_PARTIAL_BOUND]
   `!f:num->real p B. (!n. p <= n ==> &0 <= f n) /\ (!n. sum(p..n) f <= B)
                      ==> real_summable (from p) f`) THEN
  EXISTS_TAC
   `(&8 * (real_of_int a + real_of_int c)) rpow s *
    (&2 * real_infsum (from 1) (\n. inv(&n rpow s))) pow 2` THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN MATCH_MP_TAC RPOW_POS_LE THEN
    REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN
  SUBGOAL_THEN `~(s = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `B = num_of_int(&4 * (a + c))` THEN
  SUBGOAL_THEN `&4 * (a + c) <= &B:int` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `&0:int <= &4 * (a + c)` (fun th ->
      SIMP_TAC[th; INT_OF_NUM_OF_INT; INT_LE_REFL]) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `\l:num. inv(&l rpow s)`;
                `N:num`; `B:num`; `B * N:num`; `B * N:num`]
    QFORM_SERIES_LATTICE_COUNT) THEN
  ASM_REWRITE_TAC[LE_REFL; RPOW_ZERO; REAL_INV_0] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {x:int | --(&(B * N)) <= x /\ x <= &(B * N)}
     (\x. sum {y:int | --(&(B * N)) <= y /\ y <= &(B * N)}
       (\y. inv(real_of_int(qform a b c x y) rpow s)))` THEN
  ASM_SIMP_TAC[QFORM_SERIES_BOX_INV_BOUND] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
  X_GEN_TAC `x:int` THEN DISCH_TAC THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
  X_GEN_TAC `y:int` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `x:int`; `y:int`]
    QFORM_SERIES_FORM_LOWER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[QFORM_SERIES_FORM_NUM_REAL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC RPOW_POS_LE THEN
  ASM_REWRITE_TAC[GSYM int_of_num_th; GSYM int_le]);;

let QFORM_SERIES_LS_SUMMABLE = prove
 (`!k a b c s.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 < s
     ==> real_summable (from 1)
          (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\l. &(qform_rep a b c l) * inv(&l rpow s)` THEN
  ASM_SIMP_TAC[QFORM_SERIES_WS_SUMMABLE] THEN EXISTS_TAC `0` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; real_div] THEN
  MATCH_MP_TAC CLASSNO_SERIES_ABS_MUL_LE THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_BOUND; REAL_LE_INV_EQ] THEN
  MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* The Dirichlet series for s > 1 regrouped by rows.                         *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_TERM_EQ = prove
 (`!k a b c s x y.
     &0 < a /\ &0 < &4 * a * c - b pow 2
     ==> qform_term k a b c s x y =
         qchar k (num_of_int(qform a b c x y)) /
         &(num_of_int(qform a b c x y)) rpow s`,
  SIMP_TAC[qform_term; QFORM_SERIES_FORM_NUM_REAL]);;

let QFORM_SERIES_BOX_BOUND = prove
 (`!k a b c s N B X Y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &4 * (a + c) <= &B /\ &1 < s /\
     B * N <= X /\ B * N <= Y
     ==> abs(sum {x:int | --(&X) <= x /\ x <= &X}
              (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                    (\y. qform_term k a b c s x y)) -
             sum(1..N) (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s)))
         <= real_infsum (from 1)
             (\l. &(qform_rep a b c l) * inv(&l rpow s)) -
            sum(1..N) (\l. &(qform_rep a b c l) * inv(&l rpow s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[QFORM_SERIES_TERM_EQ] THEN
  MP_TAC(ISPECL [`a:int`; `b:int`; `c:int`; `\l. qchar k l / &l rpow s`;
                 `\l. inv(&l rpow s)`; `N:num`; `B:num`; `X:num`; `Y:num`]
    QFORM_SERIES_LATTICE_TAIL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[RPOW_ZERO; real_div; REAL_INV_0; REAL_MUL_RZERO] THEN
    GEN_TAC THEN MATCH_MP_TAC CLASSNO_SERIES_ABS_MUL_LE THEN
    REWRITE_TAC[CLASSNO_SERIES_QCHAR_BOUND; REAL_LE_INV_EQ] THEN
    MATCH_MP_TAC RPOW_POS_LE THEN REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c x:real. x <= a - c /\ a <= b ==> x <= b - c`) THEN
  EXISTS_TAC `sum(1..M) (\l. &(qform_rep a b c l) * inv(&l rpow s))` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\l. &(qform_rep a b c l) * inv(&l rpow s)`; `from 1`;
                 `M:num`] REAL_PARTIAL_SUMS_LE_INFSUM) THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[QFORM_SERIES_WS_SUMMABLE] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN MATCH_MP_TAC RPOW_POS_LE THEN
  REWRITE_TAC[REAL_POS]);;

let QFORM_SERIES_ROWS_TENDS = prove
 (`!k a b c s.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 < s
     ==> ((\Y. sum {y:int | --(&Y) <= y /\ y <= &Y}
                (\y. if y = &0
                     then &2 * qchar k (num_of_int a) / real_of_int a rpow s *
                          real_infsum (from 1)
                           (\n. if coprime(n,k) then inv((&n pow 2) rpow s)
                                else &0)
                     else real_infsum (from 0)
                           (\n. qform_term k a b c s (&n) y +
                                qform_term k a b c s (--(&n) - &1) y))) --->
          real_infsum (from 1)
           (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_C_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `B = num_of_int(&4 * (a + c))` THEN
  SUBGOAL_THEN `&4 * (a + c) <= &B:int` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `&0:int <= &4 * (a + c)` (fun th ->
      SIMP_TAC[th; INT_OF_NUM_OF_INT; INT_LE_REFL]) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `SS = \y:int. if y = &0
                 then &2 * qchar k (num_of_int a) / real_of_int a rpow s *
                      real_infsum (from 1)
                       (\n. if coprime(n,k) then inv((&n pow 2) rpow s)
                            else &0)
                 else real_infsum (from 0)
                       (\n. qform_term k a b c s (&n) y +
                            qform_term k a b c s (--(&n) - &1) y)` THEN
  SUBGOAL_THEN
   `!Y. ((\X. sum {x:int | --(&X) <= x /\ x <= &X}
               (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                     (\y. qform_term k a b c s x y))) --->
         sum {y:int | --(&Y) <= y /\ y <= &Y} (SS:int->real)) sequentially`
  (LABEL_TAC "S3") THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `!X. sum {x:int | --(&X) <= x /\ x <= &X}
           (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                 (\y. qform_term k a b c s x y)) =
          sum {y:int | --(&Y) <= y /\ y <= &Y}
           (\y. sum {x:int | --(&X) <= x /\ x <= &X}
                 (\x. qform_term k a b c s x y))`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      MP_TAC(ISPECL [`\x:int y:int. qform_term k a b c s x y`;
                     `{x:int | --(&X) <= x /\ x <= &X}`;
                     `{y:int | --(&Y) <= y /\ y <= &Y}`] SUM_SWAP) THEN
      REWRITE_TAC[FINITE_INT_SEG] THEN DISCH_THEN ACCEPT_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_INT_SEG] THEN
    X_GEN_TAC `y:int` THEN DISCH_TAC THEN EXPAND_TAC "SS" THEN
    ASM_CASES_TAC `y:int = &0` THEN ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC QFORM_SERIES_ROW0_LIMIT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC QFORM_SERIES_ROW_LIMIT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = real_infsum (from 1) (\l. &(qform_rep a b c l) * inv(&l rpow s))` THEN
  ABBREV_TAC
   `WS = \N. sum(1..N) (\l. &(qform_rep a b c l) * inv(&l rpow s))` THEN
  ABBREV_TAC
   `LS = \N. sum(1..N)
              (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))` THEN
  SUBGOAL_THEN
   `!N Y. B * N <= Y
          ==> abs(sum {y:int | --(&Y) <= y /\ y <= &Y} (SS:int->real) -
                  (LS:num->real) N) <= W - (WS:num->real) N`
  (LABEL_TAC "S4") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
    EXISTS_TAC
     `\X. abs(sum {x:int | --(&X) <= x /\ x <= &X}
                (\x. sum {y:int | --(&Y) <= y /\ y <= &Y}
                      (\y. qform_term k a b c s x y)) -
              (LS:num->real) N)` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REALLIM_ABS THEN MATCH_MP_TAC REALLIM_SUB THEN
      REWRITE_TAC[REALLIM_CONST] THEN USE_THEN "S3" MATCH_ACCEPT_TAC;
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `B * N:num` THEN
      X_GEN_TAC `X:num` THEN DISCH_TAC THEN BETA_TAC THEN
      MAP_EVERY EXPAND_TAC ["LS"; "WS"; "W"] THEN
      MATCH_MP_TAC QFORM_SERIES_BOX_BOUND THEN EXISTS_TAC `B:num` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_summable (from 1)
     (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC QFORM_SERIES_LS_SUMMABLE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((LS:num->real) --->
     real_infsum (from 1)
      (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))) sequentially /\
    ((WS:num->real) ---> W) sequentially`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["LS"; "WS"; "W"] THEN
    REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
    ASM_SIMP_TAC[QFORM_SERIES_WS_SUMMABLE];
    ALL_TAC] THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `((LS:num->real) --->
     real_infsum (from 1)
      (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))) sequentially` THEN
  UNDISCH_TAC `((WS:num->real) ---> W) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `B * (N1 + N2):num` THEN X_GEN_TAC `Y:num` THEN DISCH_TAC THEN
  USE_THEN "S4" (MP_TAC o SPECL [`N1 + N2:num`; `Y:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N1 + N2:num`) THEN
  REWRITE_TAC[ARITH_RULE `N1 <= N1 + N2:num /\ N2 <= N1 + N2`] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!a w b c sg e:real.
      abs(a - w) < e / &2 ==> abs(b - c) < e / &2 ==>
      abs(sg - b) <= w - a ==> abs(sg - c) < e`));;

let QFORM_SERIES_ROWS_SYM = prove
 (`!k a b c s Y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 <= s
     ==> sum {y:int | --(&Y) <= y /\ y <= &Y}
          (\y. if y = &0
               then &2 * qchar k (num_of_int a) / real_of_int a rpow s *
                    real_infsum (from 1)
                     (\n. if coprime(n,k) then inv((&n pow 2) rpow s)
                          else &0)
               else real_infsum (from 0)
                     (\n. qform_term k a b c s (&n) y +
                          qform_term k a b c s (--(&n) - &1) y)) =
         &2 * qchar k (num_of_int a) / real_of_int a rpow s *
         real_infsum (from 1)
          (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) +
         &2 * sum(1..Y) (qform_slice k a b c s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLASSNO_SERIES_BOX_SUM] THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&j:int = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN UNDISCH_TAC `1 <= j` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_NEG_EQ_0; qform_slice] THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `s:real`; `&j:int`]
    QFORM_SERIES_PS_NEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!x:real. x + x = &2 * x`));;

(* ------------------------------------------------------------------------- *)
(* A slice h(x) = chi(x) ((lam x + be)^2 + D)^-s with chi periodic modulo k, *)
(* as (sum of chi over a period) times Psi plus an error <= 2 k D^-s:        *)
(* residue classes and UNIMODAL_SHIFT with spacing lam k.                    *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_SLICE_CLASS = prove
 (`!h:int->real chi:int->real D s k lam be m n.
     (!x t. chi(x + &k * t) = chi x) /\
     (!x. h x = chi x * inv(((lam * real_of_int x + be) pow 2 + D) rpow s))
     ==> h(&m + &k * &n) + h(&m - &k * (&n + &1)) =
         chi(&m) *
         (inv((((lam * &m + be) + (lam * &k) * &n) pow 2 + D) rpow s) +
          inv((((lam * &m + be) - (lam * &k) * (&n + &1)) pow 2 + D) rpow s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(chi:int->real)(&m - &k * (&n + &1)) = chi(&m)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `&m - &k * (&n + &1):int = &m + &k * --(&n + &1)`
      SUBST1_TAC THENL
     [INT_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[int_add_th; int_sub_th; int_mul_th; int_of_num_th] THEN
  REWRITE_TAC[REAL_ARITH
   `lam * (m + k * n) + be:real = (lam * m + be) + (lam * k) * n`;
              REAL_ARITH
   `lam * (m - k * (n + &1)) + be:real =
    (lam * m + be) - (lam * k) * (n + &1)`] THEN
  REAL_ARITH_TAC);;

let QFORM_SERIES_SLICE_PARTIAL = prove
 (`!h:int->real chi:int->real D s k lam be.
     1 <= k /\
     (!x t. chi(x + &k * t) = chi x) /\
     (!x. h x = chi x * inv(((lam * real_of_int x + be) pow 2 + D) rpow s))
     ==> !N. sum(0..k * (N + 1) - 1) (\j. h(&j) + h(--(&j) - &1)) =
         sum(0..k - 1)
          (\m. chi(&m) *
               sum(0..N)
                (\n. inv((((lam * &m + be) + (lam * &k) * &n) pow 2 + D)
                         rpow s) +
                     inv((((lam * &m + be) - (lam * &k) * (&n + &1)) pow 2 +
                          D) rpow s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SIMP_TAC[CLASSNO_SERIES_PAIRED_BLOCKS; ASSUME `1 <= k`] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  BETA_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC QFORM_SERIES_SLICE_CLASS THEN
  ASM_REWRITE_TAC[]);;

let QFORM_SERIES_SLICE_DECOMP = prove
 (`!h:int->real chi:int->real D s k lam be.
     1 <= k /\ &1 <= lam /\ &1 <= D /\ &1 <= s /\
     (!x t. chi(x + &k * t) = chi x) /\
     (!x. abs(chi x) <= &1) /\
     (!x. h x = chi x * inv(((lam * real_of_int x + be) pow 2 + D) rpow s))
     ==> real_summable (from 0) (\n. h(&n) + h(--(&n) - &1)) /\
         abs(real_infsum (from 0) (\n. h(&n) + h(--(&n) - &1)) -
             sum(0..k - 1) (\m. chi(&m)) *
             real_infsum (from 0)
              (\n. inv((((lam * &k) * &n) pow 2 + D) rpow s) +
                   inv((((lam * &k) * (&n + &1)) pow 2 + D) rpow s)))
         <= &2 * &k * inv(D rpow s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < D /\ &1 <= &k /\ &1 <= lam * &k` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_summable (from 0) (\n. (h:int->real)(&n) + h(--(&n) - &1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
    EXISTS_TAC `\n. inv(((be + lam * &n) pow 2 + D) rpow s) +
                    inv(((be - lam * (&n + &1)) pow 2 + D) rpow s)` THEN
    ASM_SIMP_TAC[CLASSNO_SERIES_KERNEL_SUMMABLE] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[int_sub_th; int_neg_th; int_of_num_th] THEN
    REWRITE_TAC[REAL_ARITH `lam * &n + be:real = be + lam * &n`;
                REAL_ARITH `lam * (--(&n) - &1) + be:real =
                            be - lam * (&n + &1)`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(a:real) <= x /\ abs(b) <= y ==> abs(a + b) <= x + y`) THEN
    CONJ_TAC THEN MATCH_MP_TAC CLASSNO_SERIES_ABS_MUL_LE THEN
    ASM_SIMP_TAC[CLASSNO_SERIES_KERNEL_POS];
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]] THEN
  ABBREV_TAC
   `U = \m. real_infsum (from 0)
             (\n. inv((((lam * &m + be) + (lam * &k) * &n) pow 2 + D) rpow s) +
                  inv((((lam * &m + be) - (lam * &k) * (&n + &1)) pow 2 + D)
                      rpow s))` THEN
  ABBREV_TAC
   `Psi = real_infsum (from 0)
           (\n. inv((((lam * &k) * &n) pow 2 + D) rpow s) +
                inv((((lam * &k) * (&n + &1)) pow 2 + D) rpow s))` THEN
  SUBGOAL_THEN
   `real_infsum (from 0) (\n. (h:int->real)(&n) + h(--(&n) - &1)) =
    sum(0..k - 1) (\m. (chi:int->real)(&m) * (U:num->real) m)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UNIQUE) THEN
    EXISTS_TAC `\N. sum(0..k * (N + 1) - 1)
                       (\j. (h:int->real)(&j) + h(--(&j) - &1))` THEN
    REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`\M. sum(0..M) (\j. (h:int->real)(&j) + h(--(&j) - &1))`;
        `real_infsum (from 0) (\n. (h:int->real)(&n) + h(--(&n) - &1))`;
        `\N. k * (N + 1) - 1`] CLASSNO_SERIES_REALLIM_SUBSEQ) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
        FIRST_ASSUM ACCEPT_TAC;
        X_GEN_TAC `n:num` THEN
        MP_TAC(SPECL [`1`; `k:num`; `n + 1`] LE_MULT_RCANCEL) THEN
        ASM_REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:int->real`; `chi:int->real`; `D:real`;
      `s:real`; `k:num`; `lam:real`; `be:real`] QFORM_SERIES_SLICE_PARTIAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REALLIM_SUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((\N. sum(0..N)
             (\n. inv((((lam * &m + be) + (lam * &k) * &n) pow 2 + D) rpow s) +
                  inv((((lam * &m + be) - (lam * &k) * (&n + &1)) pow 2 + D)
                      rpow s))) --->
       (U:num->real) m) sequentially`
    (fun th -> MP_TAC(ISPEC `(chi:int->real)(&m)` (MATCH_MP REALLIM_LMUL th)))
    THENL
     [EXPAND_TAC "U" THEN
      REWRITE_TAC[GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM] THEN
      MATCH_MP_TAC CLASSNO_SERIES_KERNEL_SUMMABLE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RMUL; GSYM SUM_SUB_NUMSEG; GSYM REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(0..k - 1)) * &2 * inv(D rpow s)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[CARD_NUMSEG; SUB_0] THEN
    ASM_SIMP_TAC[SUB_ADD] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_ABS_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  MP_TAC(ISPECL [`\t. inv((t pow 2 + D) rpow s)`; `&0`; `lam * &k`;
                 `lam * &m + be`; `&0`] UNIMODAL_SHIFT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[CLASSNO_SERIES_KERNEL_POS; CLASSNO_SERIES_KERNEL_SUMMABLE] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC CLASSNO_SERIES_KERNEL_MONO THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    (CONJ_TAC THENL [UNDISCH_TAC `&1 <= s` THEN REAL_ARITH_TAC; ALL_TAC]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "U" THEN EXPAND_TAC "Psi" THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_SUB_LZERO; REAL_POW_NEG; ARITH] THEN
  REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* The scaled slices (4 a)^-s S_y(s), y >= 1: c(y) Psi_y(s) + O(k / y^2).    *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_TERM_SCALE = prove
 (`!k a b c s x y.
     inv((&4 * real_of_int a) rpow s) * qform_term k a b c s x y =
     qchar k (num_of_int(qform a b c x y)) *
     inv((((&2 * real_of_int a) * real_of_int x +
           real_of_int b * real_of_int y) pow 2 +
          real_of_int(&4 * a * c - b pow 2) * real_of_int y pow 2) rpow s)`,
  REPEAT GEN_TAC THEN
    REWRITE_TAC[qform_term; GSYM QFORM_SERIES_FORM_REAL_4A] THEN
  REWRITE_TAC[RPOW_MUL; real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC);;

let QFORM_SERIES_SLICE_SPLIT = prove
 (`!k a b c s y.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y /\ &1 <= s
     ==> abs(inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y -
             sum(0..k - 1) (\m. qchar k (num_of_int(qform a b c (&m) (&y)))) *
             real_infsum (from 0)
              (\n. inv(((((&2 * real_of_int a) * &k) * &n) pow 2 +
                         real_of_int(&4 * a * c - b pow 2) * &y pow 2) rpow s) +
                   inv(((((&2 * real_of_int a) * &k) * (&n + &1)) pow 2 +
                         real_of_int(&4 * a * c - b pow 2) * &y pow 2) rpow s)))
         <= &2 * &k * inv(&y pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&y:int = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &y pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&y pow 2 <= real_of_int(&4 * a * c - b pow 2) * &y pow 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (d - &1) * y ==> y <= d * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y =
    real_infsum (from 0)
     (\n. inv((&4 * real_of_int a) rpow s) * qform_term k a b c s (&n) (&y) +
          inv((&4 * real_of_int a) rpow s) *
          qform_term k a b c s (--(&n) - &1) (&y))`
  SUBST1_TAC THENL
   [REWRITE_TAC[qform_slice; GSYM REAL_ADD_LDISTRIB] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INFSUM_LMUL THEN
    MATCH_MP_TAC QFORM_SERIES_ROW_SUMMABLE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. inv((&4 * real_of_int a) rpow s) * qform_term k a b c s x (&y)`;
    `\x. qchar k (num_of_int(qform a b c x (&y)))`;
    `real_of_int(&4 * a * c - b pow 2) * &y pow 2`; `s:real`; `k:num`;
    `&2 * real_of_int a`; `real_of_int b * &y`] QFORM_SERIES_SLICE_DECOMP) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLASSNO_SERIES_QCHAR_BOUND; QFORM_SERIES_TERM_SCALE;
                    int_of_num_th] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[REAL_LE_TRANS];
      REPEAT GEN_TAC THEN MATCH_MP_TAC CLASSNO_SERIES_QCHAR_CONG THEN
      ASM_SIMP_TAC[QFORM_SERIES_FORM_LOWER; QFORM_SERIES_FORM_CONG]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(real_of_int(&4 * a * c - b pow 2) * &y pow 2)` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`real_of_int(&4 * a * c - b pow 2) * &y pow 2`; `s:real`;
                  `&0`] CLASSNO_SERIES_KERNEL_LE_INV) THEN
    REWRITE_TAC[REAL_POW_ZERO; ARITH; REAL_ADD_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[REAL_LE_TRANS];
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The class sums c(y) = sum over m < k of chi_k(F(m,y)) = chi_k(a) c_k(y)   *)
(* (QFORM_LIMIT_RAMANUJAN): periodic modulo k with mean zero, block sums at  *)
(* most 2 k^2.                                                               *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_CLASS_PERIODIC = prove
 (`!k a b c y.
     &0 < a /\ &0 < &4 * a * c - b pow 2
     ==> sum(0..k - 1)
          (\m. qchar k (num_of_int(qform a b c (&m) (&(y + k))))) =
         sum(0..k - 1) (\m. qchar k (num_of_int(qform a b c (&m) (&y))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN BETA_TAC THEN
  MATCH_MP_TAC CLASSNO_SERIES_QCHAR_CONG THEN
  ASM_SIMP_TAC[QFORM_SERIES_FORM_LOWER] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`; `&m:int`; `&y:int`; `&1:int`;
                `k:num`] (CONJUNCT2 QFORM_SERIES_FORM_CONG)) THEN
  REWRITE_TAC[INT_MUL_RID]);;

let QFORM_SERIES_CLASS_BOUND = prove
 (`!k a b c y.
     1 <= k
     ==> abs(sum(0..k - 1)
              (\m. qchar k (num_of_int(qform a b c (&m) (&y))))) <= &k`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(0..k - 1)) * &1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_BOUND THEN
    REWRITE_TAC[FINITE_NUMSEG; CLASSNO_SERIES_QCHAR_BOUND];
    REWRITE_TAC[CARD_NUMSEG; SUB_0; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[SUB_ADD; REAL_LE_REFL]]);;

let QFORM_SERIES_COUNT_DIVIDES = prove
 (`!q r. 1 <= q /\ 1 <= r
         ==> sum(0..q * r - 1) (\y. if q divides y then &1 else &0) = &r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q * r - 1 = ((r - 1) + 1) * q - 1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUB_ADD] THEN REWRITE_TAC[MULT_SYM]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLASSNO_SERIES_SUM_BLOCKS] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0..q - 1) (\a. if a = 0 then &r else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `!i. (q divides (a + i * q) <=> a = 0)`
    (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `q divides (a + i * q) <=> q divides a` SUBST1_TAC THENL
       [CONV_TAC NUMBER_RULE; ALL_TAC] THEN
      EQ_TAC THENL
       [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIVIDES_0]];
      ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[SUM_0; SUM_CONST_NUMSEG] THEN
    ASM_SIMP_TAC[SUB_ADD; SUB_0; REAL_MUL_RID; REAL_MUL_RZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0]]);;

let QFORM_SERIES_RAMANUJAN_MEAN = prove
 (`!k k1 k2.
     k = k1 * k2 /\ 1 <= k1 /\ 1 <= k2
     ==> sum(0..k - 1)
          (\y. &1 - &k1 * (if k1 divides y then &1 else &0) -
               &k2 * (if k2 divides y then &1 else &0) +
               &k * (if k divides y then &1 else &0)) = &0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_SUB_NUMSEG; SUM_LMUL] THEN
  SUBGOAL_THEN
   `sum(0..k - 1) (\y. if k1 divides y then &1 else &0) = &k2 /\
    sum(0..k - 1) (\y. if k2 divides y then &1 else &0) = &k1 /\
    sum(0..k - 1) (\y. if k divides y then &1 else &0) = &1 /\
    sum(0..k - 1) (\y. &1) = &k`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 1 * 1`] THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[QFORM_SERIES_COUNT_DIVIDES];
      SUBGOAL_THEN `k - 1 = k2 * k1 - 1` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[MULT_SYM]; ASM_SIMP_TAC[QFORM_SERIES_COUNT_DIVIDES]];
      SUBGOAL_THEN `k - 1 = k * 1 - 1` SUBST1_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES];
        MATCH_MP_TAC QFORM_SERIES_COUNT_DIVIDES THEN ASM_REWRITE_TAC[LE_REFL]];
      REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[SUB_ADD]];
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC]);;

let QFORM_SERIES_K_POS = prove
 (`!k k1 k2. k = k1 * k2 /\ prime k1 /\ prime k2
             ==> 1 <= k1 /\ 1 <= k2 /\ 1 <= k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `k1:num` PRIME_GE_2) THEN MP_TAC(SPEC `k2:num` PRIME_GE_2) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
  ARITH_TAC);;

let QFORM_SERIES_CLASS_BLOCK = prove
 (`!k k1 k2 a b c.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k /\
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\
     coprime(k,num_of_int a) /\ coprime(k,num_of_int(&4 * a * c - b pow 2))
     ==> !m n. abs(sum(m..n)
                    (\y. sum(0..k - 1)
                          (\x. qchar k (num_of_int(qform a b c (&x) (&y))))))
               <= &2 * &k * &k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_K_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC CLASSNO_SERIES_PERIODIC_BOUND THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC QFORM_SERIES_CLASS_PERIODIC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC;
    GEN_TAC THEN BETA_TAC THEN MATCH_MP_TAC QFORM_SERIES_CLASS_BOUND THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN
   `!y. sum(0..k - 1) (\x. qchar k (num_of_int(qform a b c (&x) (&y)))) =
        qchar k (num_of_int a) *
        (&1 - &k1 * (if k1 divides y then &1 else &0) -
         &k2 * (if k2 divides y then &1 else &0) +
         &k * (if k divides y then &1 else &0))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC QFORM_LIMIT_RAMANUJAN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_RAMANUJAN_MEAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* The block bound of the scaled y-series, uniform in s >= 1, and the        *)
(* continuity of the scaled slices.                                          *)
(* ------------------------------------------------------------------------- *)

let QFORM_SERIES_TSUM_BLOCK = prove
 (`!k a b c.
     1 <= k /\ &0 < a /\ &0 < &4 * a * c - b pow 2 /\
     (!m n. abs(sum(m..n)
                 (\y. sum(0..k - 1)
                       (\x. qchar k (num_of_int(qform a b c (&x) (&y))))))
            <= &2 * &k * &k)
     ==> !s m n.
           &1 <= s /\ 1 <= m
           ==> abs(sum(m..n)
                    (\y. inv((&4 * real_of_int a) rpow s) *
                         qform_slice k a b c s y))
               <= (&32 * &k * &k + &4 * &k) / &m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cblk")))) THEN
  MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `cc = \y. sum(0..k - 1)
                      (\x. qchar k (num_of_int(qform a b c (&x) (&y))))` THEN
  ABBREV_TAC `P = \y. real_infsum (from 0)
       (\n. inv(((((&2 * real_of_int a) * &k) * &n) pow 2 +
                 real_of_int(&4 * a * c - b pow 2) * &y pow 2) rpow s) +
            inv(((((&2 * real_of_int a) * &k) * (&n + &1)) pow 2 +
                 real_of_int(&4 * a * c - b pow 2) * &y pow 2) rpow s))` THEN
  ABBREV_TAC `S = \y. inv((&4 * real_of_int a) rpow s) *
                      qform_slice k a b c s y` THEN
  SUBGOAL_THEN
   `!y. 1 <= y ==> abs((S:num->real) y - (cc:num->real) y * (P:num->real) y)
                   <= &2 * &k * inv(&y pow 2)`
  (LABEL_TAC "split") THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["S"; "cc"; "P"] THEN
    MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `s:real`; `y:num`]
      QFORM_SERIES_SLICE_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&2 * real_of_int a) * &k` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. 1 <= y ==> &0 <= (P:num->real) y /\ P(y + 1) <= P y /\ P y <= &8 / &y`
  (LABEL_TAC "psi") THENL
   [X_GEN_TAC `y:num` THEN DISCH_TAC THEN EXPAND_TAC "P" THEN
    SUBGOAL_THEN
     `&y pow 2 <= real_of_int(&4 * a * c - b pow 2) * &y pow 2 /\
      &1 <= &y pow 2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= (d - &1) * y ==> y <= d * y`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= real_of_int(&4 * a * c - b pow 2) * &y pow 2`
    ASSUME_TAC THENL [ASM_MESON_TAC[REAL_LE_TRANS]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLASSNO_SERIES_PSI_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLASSNO_SERIES_PSI_MONO THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      ARITH_TAC;
      MATCH_MP_TAC CLASSNO_SERIES_PSI_BOUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "psi" (fun th ->
    LABEL_TAC "psi0" (GEN `y:num` (DISCH `1 <= y` (CONJUNCT1
      (MP (SPEC `y:num` th) (ASSUME `1 <= y`))))) THEN
    LABEL_TAC "psi1" (GEN `y:num` (DISCH `1 <= y` (CONJUNCT1 (CONJUNCT2
      (MP (SPEC `y:num` th) (ASSUME `1 <= y`)))))) THEN
    LABEL_TAC "psi2" (GEN `y:num` (DISCH `1 <= y` (CONJUNCT2 (CONJUNCT2
      (MP (SPEC `y:num` th) (ASSUME `1 <= y`))))))) THEN
  SUBGOAL_THEN
   `sum(m..n) (S:num->real) =
    sum(m..n) (\y. (cc:num->real) y * (P:num->real) y) +
    sum(m..n) (\y. S y - cc y * P y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD_NUMSEG] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(a) <= x /\ abs(b) <= y ==> abs(a + b) <= x + y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 * (&2 * &k * &k) * (P:num->real) m` THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`cc:num->real`; `P:num->real`; `&2 * &k * &k`; `1`]
        CLASSNO_SERIES_DIRICHLET_BOUND) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
          UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
          ARITH_TAC;
          REPEAT STRIP_TAC THEN USE_THEN "cblk" (fun th -> REWRITE_TAC[th]);
          X_GEN_TAC `y:num` THEN DISCH_TAC THEN
          USE_THEN "psi0" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
          X_GEN_TAC `y:num` THEN DISCH_TAC THEN
          USE_THEN "psi1" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
        DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&4 * &k * &k) * (&8 * inv(&m))` THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&2 * (&2 * &k * &k) * (P:num->real) m =
                      (&4 * &k * &k) * P m` SUBST1_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
          REWRITE_TAC[GSYM real_div] THEN USE_THEN "psi2" MATCH_MP_TAC THEN
          FIRST_ASSUM ACCEPT_TAC];
        REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..n) (\y. &2 * &k * inv(&y pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(m..n) (\y. abs((S:num->real) y - (cc:num->real) y *
                                    (P:num->real) y))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `y:num` THEN STRIP_TAC THEN BETA_TAC THEN
      USE_THEN "split" MATCH_MP_TAC THEN
      UNDISCH_TAC `1 <= m` THEN UNDISCH_TAC `m <= y:num` THEN ARITH_TAC;
      REWRITE_TAC[SUM_LMUL] THEN
      MP_TAC(SPECL [`m:num`; `n:num`] CLASSNO_SERIES_INV_SQUARE_BLOCK) THEN
      ASM_REWRITE_TAC[real_div] THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&2 * &k * (&2 * inv(&m))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
        REAL_ARITH_TAC]]]);;

let QFORM_SERIES_SCALED_CONTINUOUS = prove
 (`!k a b c y.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ 1 <= y
     ==> (\s. inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y)
         real_continuous (atreal (&1) within {s | &1 <= s})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &4 * real_of_int a` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_INV_ATREAL THEN
    ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RPOW_RIGHT; RPOW_POS_LT; REAL_LT_IMP_NZ];
    REWRITE_TAC[qform_slice] THEN MATCH_MP_TAC QFORM_SERIES_ROW_CONTINUOUS THEN
    ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main results, parsed after prioritize_num.                            *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let QFORM_DIRICHLET_SERIES = prove
 (`!k a b c s.
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\ &1 < s
     ==> ((\l. qchar k l * &(qform_rep a b c l) / &l rpow s) real_sums
          (&2 * qchar k (num_of_int a) / real_of_int a rpow s *
           real_infsum (from 1)
            (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0) +
           &2 * real_infsum (from 1) (qform_slice k a b c s))) (from 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= s:real` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`; `s:real`]
    QFORM_SERIES_ROWS_TENDS) THEN
  ASM_SIMP_TAC[QFORM_SERIES_ROWS_SYM] THEN
  ABBREV_TAC
   `Z0 = &2 * qchar k (num_of_int a) / real_of_int a rpow s *
         real_infsum (from 1)
          (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0)` THEN
  ABBREV_TAC
   `L = real_infsum (from 1)
         (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(qform_slice k a b c s real_sums (inv(&2) * (L - Z0))) (from 1)`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SERIES_FROM] THEN
    SUBGOAL_THEN
     `((\Y. inv(&2) * ((Z0 + &2 * sum(1..Y) (qform_slice k a b c s)) - Z0))
       ---> inv(&2) * (L - Z0)) sequentially`
    MP_TAC THENL
     [MATCH_MP_TAC REALLIM_LMUL THEN MATCH_MP_TAC REALLIM_SUB THEN
      ASM_REWRITE_TAC[REALLIM_CONST];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `inv(&2) * ((z + &2 * t) - z) = t:real`] THEN
    DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP REAL_INFSUM_UNIQUE) THEN
  SUBGOAL_THEN `Z0 + &2 * inv(&2) * (L - Z0) = L:real` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "L" THEN
  SUBGOAL_THEN
   `(\l. qchar k l * &(qform_rep a b c l) / &l rpow s) =
    (\l. &(qform_rep a b c l) * (qchar k l / &l rpow s))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_SUMS_INFSUM] THEN MATCH_MP_TAC QFORM_SERIES_LS_SUMMABLE THEN
  ASM_REWRITE_TAC[]);;

let QFORM_SLICE_SERIES_CONTINUOUS = prove
 (`!k k1 k2 a b c.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k /\
     &0 < a /\ &0 < &4 * a * c - b pow 2 /\
     coprime(k,num_of_int a) /\ coprime(k,num_of_int(&4 * a * c - b pow 2))
     ==> (!s. &1 <= s ==> real_summable (from 1) (qform_slice k a b c s)) /\
         (\s. real_infsum (from 1) (qform_slice k a b c s))
         real_continuous (atreal (&1) within {s | &1 <= s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `a:int`; `b:int`; `c:int`]
    QFORM_SERIES_CLASS_BLOCK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`] QFORM_SERIES_K_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `k = k1 * k2:num` THEN DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(SPECL [`k:num`; `a:int`; `b:int`; `c:int`] QFORM_SERIES_TSUM_BLOCK)
    THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(LABEL_TAC "blk")] THEN
  SUBGOAL_THEN `((\m. (&32 * &k * &k + &4 * &k) / &m) ---> &0) sequentially`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[REALLIM_1_OVER_N];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &4 * real_of_int a` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:int`; `b:int`; `c:int`] QFORM_SERIES_FORM_REAL_POS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. &1 <= s
        ==> real_summable (from 1)
             (\y. inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y)`
  (LABEL_TAC "ssum") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\y. inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y`;
      `\m. (&32 * &k * &k + &4 * &k) / &m`; `1`]
     CLASSNO_SERIES_BLOCK_TAIL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "blk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. qform_slice k a b c s =
        (\y. (&4 * real_of_int a) rpow s *
             (inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y))`
  (LABEL_TAC "eq") THENL
   [GEN_TAC THEN REWRITE_TAC[FUN_EQ_THM; REAL_MUL_ASSOC] THEN GEN_TAC THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; RPOW_POS_LT; REAL_LT_IMP_NZ; REAL_MUL_LID];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    USE_THEN "eq" (fun th -> ONCE_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_SUMMABLE_LMUL THEN USE_THEN "ssum" MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_TRANSFORM_WITHINREAL THEN
  EXISTS_TAC
   `\s. (&4 * real_of_int a) rpow s *
        real_infsum (from 1)
         (\y. inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y)` THEN
  EXISTS_TAC `&1:real` THEN
  REWRITE_TAC[REAL_LT_01; IN_ELIM_THM; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    USE_THEN "eq" (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_INFSUM_LMUL THEN
    USE_THEN "ssum" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    MATCH_MP_TAC REAL_CONTINUOUS_AT_RPOW_RIGHT THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s y. inv((&4 * real_of_int a) rpow s) * qform_slice k a b c s y`;
    `\m. (&32 * &k * &k + &4 * &k) / &m`; `{s:real | &1 <= s}`; `&1:real`;
    `1`]
   CLASSNO_SERIES_UNIFORM_CONTINUOUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "blk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC QFORM_SERIES_SCALED_CONTINUOUS THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tools for the products of L-series at s = 1: combining the sums of        *)
(* series, the uniqueness of the limits s -> 1+, the limits of the L-series  *)
(* of real non-principal characters, of zeta_k(2s), of a^-s and of the sums  *)
(* of the slices.                                                            *)
(* ------------------------------------------------------------------------- *)

(* If lam w = u + v termwise, the sums of the series satisfy the same        *)
(* relation.                                                                 *)
let QFORM_SERIES_SUMS_COMBINE = prove
 (`!u v w a b c lam (s:num->bool).
     (u real_sums a) s ==> (v real_sums b) s ==> (w real_sums c) s ==>
     (!l. l IN s ==> lam * w l = u l + v l)
     ==> lam * c = a + b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_UNIQUE THEN
  EXISTS_TAC `\l. (u:num->real) l + v l` THEN EXISTS_TAC `s:num->bool` THEN
  ASM_SIMP_TAC[REAL_SERIES_ADD] THEN
  MATCH_MP_TAC REAL_SUMS_EQ THEN EXISTS_TAC `\l. lam * (w:num->real) l` THEN
  ASM_SIMP_TAC[REAL_SERIES_LMUL]);;

let QFORM_SERIES_QCHAR_BOUNDED = prove
 (`!m. ?B. !n. abs(qchar m n) <= B`,
  GEN_TAC THEN EXISTS_TAC `&1` THEN REWRITE_TAC[CLASSNO_SERIES_QCHAR_BOUND]);;

let QFORM_SERIES_LIMIT_EQ = prove
 (`!X Y x y.
     (!s. &1 < s ==> X s = Y s) /\
     (X ---> x) (atreal (&1) within {s | &1 < s}) /\
     (Y ---> y) (atreal (&1) within {s | &1 < s})
     ==> x = y`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `atreal (&1) within {s | &1 < s}` REALLIM_UNIQUE) THEN
  EXISTS_TAC `X:real->real` THEN
  ASM_REWRITE_TAC[CLASSNO_SERIES_NONTRIVIAL] THEN
  MATCH_MP_TAC REALLIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `Y:real->real` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EVENTUALLY_WITHINREAL; IN_ELIM_THM] THEN
  EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN ASM_MESON_TAC[]);;

let QFORM_SERIES_LSERIES_LIMIT = prove
 (`!M f. dirichlet_character M (\n. Cx(f n)) /\
         ~((\n. Cx(f n)) = chi_0 M)
         ==> ?L. Lfunction (\n. Cx(f n)) = Cx L /\
                 ((\s. real_infsum (from 1) (\n. f n / &n rpow s)) ---> L)
                 (atreal (&1) within {s | &1 < s})`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `Re(Lfunction (\n. Cx((f:num->real) n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CLASSNO_SERIES_LFUNCTION_REAL THEN EXISTS_TAC `M:num` THEN
    ASM_REWRITE_TAC[REAL_CX];
    MP_TAC(ISPECL [`M:num`; `\n. Cx((f:num->real) n)`]
      LSERIES_RIGHT_CONTINUOUS) THEN
    ASM_REWRITE_TAC[REAL_CX; RE_CX]]);;

let QFORM_SERIES_QCHAR_LIMIT = prove
 (`!m. ODD m /\ ~((\n. Cx(qchar m n)) = chi_0 m)
       ==> ?L. Lfunction (\n. Cx(qchar m n)) = Cx L /\
               ((\s. real_infsum (from 1) (\n. qchar m n / &n rpow s)) ---> L)
               (atreal (&1) within {s | &1 < s})`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC QFORM_SERIES_LSERIES_LIMIT THEN
  EXISTS_TAC `m:num` THEN ASM_SIMP_TAC[QCHAR_DIRICHLET]);;

let QFORM_SERIES_ZETA_LIMIT = prove
 (`!k. ((\s. real_infsum (from 1)
              (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0)) --->
        zeta_coprime k) (atreal (&1) within {s | &1 < s})`,
  GEN_TAC THEN MP_TAC(SPEC `k:num` CLASSNO_SERIES_ZETA_CONTINUOUS) THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLASSNO_SERIES_WITHIN_LIMIT o CONJUNCT2) THEN
  REWRITE_TAC[GSYM CLASSNO_SERIES_ZETA_EQ] THEN DISCH_THEN ACCEPT_TAC);;

let QFORM_SERIES_RPOW_LIMIT = prove
 (`!a x. &0 < a
         ==> ((\s. x / a rpow s) ---> x / a) (atreal (&1) within {s | &1 < s})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
  MATCH_MP_TAC REALLIM_DIV THEN REWRITE_TAC[REALLIM_CONST] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`a:real`; `&1`] REAL_CONTINUOUS_AT_RPOW_RIGHT) THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_ATREAL; RPOW_POW; REAL_POW_1];
    ASM_REAL_ARITH_TAC]);;

let QFORM_SERIES_SLICE_LIMIT = prove
 (`!k k1 k2.
     k = k1 * k2 /\ prime k1 /\ prime k2 /\ ~(k1 = k2) /\ ODD k
     ==> !a b c.
           &0 < a /\ &0 < &4 * a * c - b pow 2 /\
           coprime(k,num_of_int a) /\
           coprime(k,num_of_int(&4 * a * c - b pow 2))
           ==> (qform_slice k a b c (&1) real_sums
                real_infsum (from 1) (qform_slice k a b c (&1))) (from 1) /\
               ((\s. real_infsum (from 1) (qform_slice k a b c s)) --->
                real_infsum (from 1) (qform_slice k a b c (&1)))
               (atreal (&1) within {s | &1 < s})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`; `k1:num`; `k2:num`; `a:int`; `b:int`; `c:int`]
    QFORM_SLICE_SERIES_CONTINUOUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `&1`)
    (MP_TAC o MATCH_MP CLASSNO_SERIES_WITHIN_LIMIT)) THEN
  REWRITE_TAC[REAL_LE_REFL; REAL_SUMS_INFSUM] THEN SIMP_TAC[]);;

(* Leave the project default.                                                *)

prioritize_num();;
