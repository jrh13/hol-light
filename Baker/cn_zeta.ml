(* ========================================================================= *)
(* zeta(2) = pi^2 / 6.                                                       *)
(*                                                                           *)
(* Purpose: zeta_coprime 1, the sum of 1 / n^2 over n >= 1, is pi^2 / 6      *)
(* (CN_ZETA_2; the series form CN_ZETA_2_SUMS). The class number two problem *)
(* uses the value: with one modulus k the main term zeta_k(2) sqrt(d) / pi   *)
(* of the linear forms must be a rational multiple of pi sqrt(d) (in the     *)
(* class number one problem, zeta(2) / pi cancels between the moduli 21 and  *)
(* 33). Combined with CLASSNO_LINEAR_ZETA_PRIME_MUL and                      *)
(* CLASSNO_LINEAR_ZETA_21_33 it gives zeta_k(2) for squarefree k.            *)
(*                                                                           *)
(* Method: the Poisson kernel identity at t = 0 gives, for c > 0,            *)
(*   sum_(n >= 1) 1 / (n^2 + c^2) = (pi c coth(pi c) - 1) / (2 c^2)          *)
(* (CNZ_POISSON_ZERO; coth(pi c) = (E + 1) / (E - 1) with E = exp(2 pi c)).  *)
(* Two explicit estimates for 0 < c <= 1 / (4 pi) follow: termwise,          *)
(* 0 <= zeta(2) - sum 1 / (n^2 + c^2) <= c^2 zeta(2) (CNZ_ZETA_APPROX), and  *)
(* from the Taylor bound of order 4 for exp (TAYLOR_CEXP, CNZ_EXP_TAYLOR4)   *)
(* abs((y/2) coth(y/2) - 1 - y^2 / 12) <= y^4 / 6 for 0 < y <= 1/2           *)
(* (CNZ_COTH_EXPANSION, at y = 2 pi c). Hence                                *)
(* abs(zeta(2) - pi^2 / 6) <= (2 + 2 pi^4) c^2 for all small c > 0, and the  *)
(* two numbers are equal (CNZ_ZERO_FROM_BOUND). No limits, power series or   *)
(* product expansions are needed beyond POISSON_KERNEL_SUM_SYM.              *)
(*                                                                           *)
(* Main results: CN_ZETA_2, CN_ZETA_2_SUMS; CNZ_POISSON_ZERO (the sum of     *)
(* 1 / (n^2 + c^2)), CNZ_COTH_EXPANSION, CNZ_EXP_TAYLOR4; helper names       *)
(* CNZ_*.                                                                    *)
(*                                                                           *)
(* Uses: Baker/classno_chardefs.ml (zeta_coprime), Baker/classno_poisson.ml  *)
(* (POISSON_KERNEL_SUM_SYM), Baker/classno_linear.ml                         *)
(* (CLASSNO_LINEAR_ZETA_SUMS, CLASSNO_LINEAR_ZETA_1_BOUNDS);                 *)
(* Multivariate/transcendentals.ml (TAYLOR_CEXP, REAL_EXP_BOUND_LEMMA,       *)
(* REAL_EXP_LE_X), Multivariate/realanalysis.ml (REAL_SERIES_LE,             *)
(* REAL_SERIES_POS).                                                         *)
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
needs "Baker/classno_linear.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. The exponential near 0: a Taylor bound of order 4, and the expansion   *)
(*    (y/2) (exp y + 1) / (exp y - 1) = 1 + y^2/12 + O(y^4).                 *)
(* ------------------------------------------------------------------------- *)

let CNZ_EXP_TAYLOR4 = prove
 (`!y. &0 <= y /\ y <= inv(&2)
       ==> abs(exp y - (&1 + y + y pow 2 / &2 + y pow 3 / &6 +
                        y pow 4 / &24)) <= y pow 5 / &12`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`4`; `Cx y`] TAYLOR_CEXP) THEN
  REWRITE_TAC[RE_CX; COMPLEX_NORM_CX; GSYM CX_EXP; GSYM CX_POW;
              GSYM CX_DIV] THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[GSYM CX_ADD; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[CONJUNCT1 real_pow; REAL_POW_1; REAL_DIV_1] THEN
  SUBGOAL_THEN `abs y = y` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `y:real` REAL_EXP_BOUND_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `exp y * y pow 5 / &24 <= y pow 5 / &12` MP_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `x * (z / &24) <= &2 * (z / &24) ==> x * z / &24 <= z / &12`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
      REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* With E = exp y = P4(y) + r, P4 the Taylor polynomial of order 4, the      *)
(* numerator of the difference is E (6 y - 12 - y^2) + 6 y + 12 + y^2        *)
(* = y^5/12 - y^6/24 + r (6 y - 12 - y^2).                                   *)

let CNZ_COTH_EXPANSION = prove
 (`!y. &0 < y /\ y <= inv(&2)
       ==> abs((y / &2 * (exp y + &1) / (exp y - &1) - &1) - y pow 2 / &12)
           <= y pow 4 / &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `y:real` CNZ_EXP_TAYLOR4) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `y:real` REAL_EXP_LE_X) THEN
  SPEC_TAC(`exp y`,`E:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < E - &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(y / &2 * (E + &1) / (E - &1) - &1) - y pow 2 / &12 =
    (y pow 5 / &12 - y pow 6 / &24 +
     (E - (&1 + y + y pow 2 / &2 + y pow 3 / &6 + y pow 4 / &24)) *
     (&6 * y - &12 - y pow 2)) / (&12 * (E - &1))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < E - &1` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ARITH `&0 < x ==> abs(&12 * x) = &12 * x`;
               REAL_LE_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < &12 * x`] THEN
  SUBGOAL_THEN `&0 <= y pow 2 /\ y pow 2 <= y` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN REWRITE_TAC[REAL_POW_2] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= y pow 4 /\ &0 <= y pow 5 /\ &0 <= y pow 6`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `y pow 6 <= y pow 5` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `6 = SUC 5`; real_pow] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `y pow 5 <= y pow 4 * (E - &1)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 = SUC 4`; real_pow] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((E - (&1 + y + y pow 2 / &2 + y pow 3 / &6 + y pow 4 / &24)) *
        (&6 * y - &12 - y pow 2)) <= y pow 5 / &12 * &12`
  MP_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 2. The Poisson kernel identity at t = 0, and the comparison with          *)
(*    zeta(2) = zeta_coprime 1.                                              *)
(* ------------------------------------------------------------------------- *)

(* The sum of 1 / (n^2 + c^2) over n >= 1 is                                 *)
(* (pi c coth(pi c) - 1) / (2 c^2).                                          *)

let CNZ_POISSON_ZERO = prove
 (`!c. &0 < c
       ==> ((\m. inv(&m pow 2 + c pow 2)) real_sums
            ((pi / c * (exp(&2 * pi * c) + &1) / (exp(&2 * pi * c) - &1) -
              inv(c pow 2)) / &2)) (from 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&0`; `c:real`] POISSON_KERNEL_SUM_SYM) THEN
  ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_ADD_RID; REAL_MUL_RZERO; COS_0;
                  REAL_EXP_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_LID] THEN
  SUBGOAL_THEN `&1 < exp(&2 * pi * c)` MP_TAC THENL
   [MATCH_MP_TAC REAL_EXP_LT_1 THEN MATCH_MP_TAC REAL_LT_MUL THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC REAL_LT_MUL THEN
    ASM_REWRITE_TAC[PI_POS];
    ALL_TAC] THEN
  SPEC_TAC(`exp(&2 * pi * c)`,`E:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o MATCH_MP REAL_SERIES_LMUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN BETA_TAC THEN REAL_ARITH_TAC;
    MAP_EVERY UNDISCH_TAC [`&1 < E`; `&0 < c`] THEN CONV_TAC REAL_FIELD]);;

(* 0 <= 1/a - 1/(a + b) <= b/a for a >= 1, b >= 0.                           *)

let CNZ_INV_SUB_BOUNDS = prove
 (`!a b. &1 <= a /\ &0 <= b
         ==> &0 <= inv a - inv(a + b) /\ inv a - inv(a + b) <= b * inv a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inv a - inv(a + b) = (b * inv a) * inv(a + b)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 <= b`; `&1 <= a`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b * inv a /\ &0 <= inv(a + b) /\ inv(a + b) <= &1`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]]);;

let CNZ_ZETA_SUMS_1 = prove
 (`((\n. inv(&n pow 2)) real_sums zeta_coprime 1) (from 1)`,
  MP_TAC(SPEC `1` CLASSNO_LINEAR_ZETA_SUMS) THEN REWRITE_TAC[COPRIME_1]);;

let CNZ_ZETA_APPROX = prove
 (`!c S. ((\m. inv(&m pow 2 + c pow 2)) real_sums S) (from 1)
         ==> S <= zeta_coprime 1 /\
             zeta_coprime 1 - S <= c pow 2 * zeta_coprime 1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\n. inv(&n pow 2)`; `zeta_coprime 1`;
                 `\m. inv(&m pow 2 + c pow 2)`; `S:real`; `from 1`]
                REAL_SERIES_SUB) THEN
  ASM_REWRITE_TAC[CNZ_ZETA_SUMS_1] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n IN from 1
        ==> &0 <= inv(&n pow 2) - inv(&n pow 2 + c pow 2) /\
            inv(&n pow 2) - inv(&n pow 2 + c pow 2) <=
            c pow 2 * inv(&n pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_FROM] THEN DISCH_TAC THEN
    MATCH_MP_TAC CNZ_INV_SUB_BOUNDS THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN MATCH_MP_TAC REAL_SERIES_POS THEN
    MAP_EVERY EXISTS_TAC
     [`\n. inv(&n pow 2) - inv(&n pow 2 + c pow 2)`; `from 1`] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_SERIES_LE THEN
    MAP_EVERY EXISTS_TAC
     [`\n. inv(&n pow 2) - inv(&n pow 2 + c pow 2)`;
      `\n. c pow 2 * inv(&n pow 2)`; `from 1`] THEN
    ASM_SIMP_TAC[REAL_SERIES_LMUL; CNZ_ZETA_SUMS_1]]);;

(* ------------------------------------------------------------------------- *)
(* 3. zeta(2) = pi^2 / 6.                                                    *)
(* ------------------------------------------------------------------------- *)

(* A real number bounded by K c^2 for all small c > 0 is 0.                  *)

let CNZ_ZERO_FROM_BOUND = prove
 (`!x K c0. &0 < c0 /\
            (!c. &0 < c /\ c <= c0 ==> abs(x:real) <= K * c pow 2)
            ==> x = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x = &0` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `k = abs K + &1` THEN
  SUBGOAL_THEN `&0 < k /\ K <= k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs x / (&2 * k)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `c = min c0 (min (&1) (abs x / (&2 * k)))` THEN
  SUBGOAL_THEN `&0 < c /\ c <= c0 /\ c <= &1 /\ c <= abs x / (&2 * k)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `y <= abs x / &2 /\ ~(x = &0) ==> ~(abs x <= y)`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(k:real) * c` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(k:real) * c pow 2` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_POW_2] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(k:real) * abs(x:real) / (&2 * k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < k` THEN
      CONV_TAC REAL_FIELD]]);;

(* For 0 < c <= 1 / (4 pi), with S the sum of 1 / (n^2 + c^2) and            *)
(* D = coth(pi c): 0 <= zeta(2) - S <= c^2 zeta(2) <= 2 c^2 and              *)
(* abs(S - pi^2 / 6) <= (4/3) pi^4 c^2.                                      *)

let CN_ZETA_2 = prove
 (`zeta_coprime 1 = pi pow 2 / &6`,
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC CNZ_ZERO_FROM_BOUND THEN
  MAP_EVERY EXISTS_TAC [`&2 + &2 * pi pow 4`; `inv(&4 * pi)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `c:real` THEN STRIP_TAC THEN
  MP_TAC(SPEC `&2 * pi * c` CNZ_COTH_EXPANSION) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[PI_POS];
      SUBGOAL_THEN `&2 * pi * inv(&4 * pi) = inv(&2)` (SUBST1_TAC o SYM)
      THENL [MP_TAC PI_POS THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MP_TAC PI_POS THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPEC `c:real` CNZ_POISSON_ZERO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP CNZ_ZETA_APPROX) THEN
  MP_TAC CLASSNO_LINEAR_ZETA_1_BOUNDS THEN
  SPEC_TAC(`(exp(&2 * pi * c) + &1) / (exp(&2 * pi * c) - &1)`,`D:real`) THEN
  SPEC_TAC(`zeta_coprime 1`,`z:real`) THEN REPEAT GEN_TAC THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `(pi / c * D - inv(c pow 2)) / &2 - pi pow 2 / &6 =
    (((&2 * pi * c) / &2 * D - &1) - (&2 * pi * c) pow 2 / &12) /
    (&2 * c pow 2)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < c` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 * c pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((pi / c * D - inv(c pow 2)) / &2 - pi pow 2 / &6) <=
    (&4 / &3 * pi pow 4) * c pow 2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * pi * c) pow 4 / &6` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c pow 2 /\ &0 <= pi pow 4 * c pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_POW_LE THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c pow 2 * z <= c pow 2 * &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* The series form.                                                          *)

let CN_ZETA_2_SUMS = prove
 (`((\n. inv(&n pow 2)) real_sums (pi pow 2 / &6)) (from 1)`,
  REWRITE_TAC[GSYM CN_ZETA_2; CNZ_ZETA_SUMS_1]);;
