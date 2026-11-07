(* ========================================================================= *)
(* The class number formula in absolute value for the odd characters of      *)
(* even modulus, chi = (-4 k d / .).                                         *)
(*                                                                           *)
(* Purpose: kchar4 d (Baker/cn_defs.ml) is a Dirichlet character modulo 4 d  *)
(* for d = 1 or 2 mod 4 (KCHAR4_DIRICHLET). For k d squarefree, k = 1 mod 4, *)
(* d = 1 or 2 mod 4 and k d > 1 the character chi = qchar k . kchar4 d       *)
(* modulo M = 4 k d satisfies abs L(1,chi) = pi abs t / (2 sqrt(k d)) with   *)
(* the integer t = sum of chi(a) over 0 < a < k d (CN_L1_KCHAR4; t is the    *)
(* class number h(-4 k d) up to sign, which is never needed). The case       *)
(* k d = 1 (D = -4, four units) is excluded: L(1, chi_(-4)) = pi / 4.        *)
(*                                                                           *)
(* Method: kchar4 d is completely multiplicative for every d (CN_KCHAR4_MUL, *)
(* by JACOBI_RMUL), its zeros come from JACOBI_EQ_0 and the period 4 d from  *)
(* Jacobi reciprocity                                                        *)
(* (jacobi(a,n + 4 a) = jacobi(a,n) for odd a, n) and the period 8 of        *)
(* jacobi(2,.). The splitting kchar4 d = c . qchar e (CNC2_KCHAR4_SPLIT),    *)
(* e the odd part of d and c one of chi_(-4) = kchar4 1, chi_(-8) = kchar4 2 *)
(* or chi_8 = kchar4 1 . kchar4 2 of modulus 2 h (h = 2, 4) with             *)
(* c(a + h) = -c(a), gives the Gauss sum property of kchar4 d                *)
(* (CN_KCHAR4_GAUSS_PROPERTY): for c the sums at even n vanish by the half   *)
(* shift and the odd n are coprime to 2 h (CLASSNO_GAUSS_PROPERTY_COPRIME),  *)
(* qchar e has it by CLASSNO_GAUSS_PROPERTY_REAL, and                        *)
(* CLASSNO_GAUSS_PROPERTY_MUL combines them, then once more with qchar k.    *)
(* The odd-character formula of any modulus M, abs L(1,chi) =                *)
(* pi abs S / M^(3/2) with S the sum of a chi(a) over 0 < a < M              *)
(* (CLASSNO_GAUSS_LFUNCTION_ODD_NORM of Baker/classno_gauss.ml), and         *)
(* chi(a + M/2) = -chi(a), chi(M/2 - a) = chi(a), chi(k d) = 0, which give   *)
(* S = -M t (CNC2_MOMENT_HALF), prove CN_L1_KCHAR4 (CNC2_L1_FOUR).           *)
(*                                                                           *)
(* Main results: KCHAR4_DIRICHLET, CN_L1_KCHAR4; CN_KCHAR4_MUL, CN_KCHAR4_1, *)
(* CN_KCHAR4_2, CN_KCHAR4_PRIME_DIVIDES, CN_KCHAR4_ODD_PRIME (for every d),  *)
(* CN_KCHAR4_GAUSS_PROPERTY, CN_KCHAR4_HALF, CN_KCHAR4_MINUS1,               *)
(* CN_INTEGER_KCHAR4, CN_DIRICHLET_CHARACTER_PRODUCT (the product of         *)
(* Dirichlet characters to two moduli); helper names CNC2_*.                 *)
(*                                                                           *)
(* Uses: Baker/cn_defs.ml (kchar4), Baker/classno_chardefs.ml (qchar),       *)
(* Baker/classno_series.ml (QCHAR_DIRICHLET, CLASSNO_SERIES_QCHAR_RMUL),     *)
(* Baker/classno_gauss.ml (CLASSNO_GAUSS_LFUNCTION_ODD_NORM,                 *)
(* CLASSNO_GAUSS_PROPERTY_COPRIME, CLASSNO_GAUSS_PROPERTY_MUL,               *)
(* CLASSNO_GAUSS_PROPERTY_REAL, CLASSNO_GAUSS_QCHAR_NONPRINCIPAL,            *)
(* CLASSNO_GAUSS_QCHAR_MINUS1, CLASSNO_GAUSS_CHAR_REFLECT,                   *)
(* CLASSNO_GAUSS_VSUM_HALVES, CLASSNO_GAUSS_PERIODIC_MOD,                    *)
(* CLASSNO_GAUSS_CEXP_INTEGER, CLASSNO_GAUSS_ODD_MOD4), Baker/classno_rep.ml *)
(* (CLASSNO_REP_INT_SQUARE);                                                 *)
(* Library/jacobi.ml (JACOBI_RECIPROCITY, JACOBI_OF_2, JACOBI_OF_2_CASES,    *)
(* JACOBI_MINUS1, JACOBI_PRIME, JACOBI_1, JACOBI_RMUL, JACOBI_LMUL,          *)
(* JACOBI_CONG, JACOBI_EQ_0); Library/pocklington.ml (SQUAREFREE_MUL,        *)
(* SQUAREFREE_DIVISOR); 100/dirichlet.ml (dirichlet_character, Lfunction).   *)
(*                                                                           *)
(* The library files come first, in the order of Baker/make.ml               *)
(* (Library/jacobi.ml before the Multivariate files), so that the file also  *)
(* loads alone.                                                              *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "100/transcendence.ml";;
needs "Examples/mangoldt.ml";;
needs "100/dirichlet.ml";;
needs "Baker/classno_rep.ml";;
needs "Baker/classno_gauss.ml";;
needs "Baker/cn_defs.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Signs (-1)^((n - 1) DIV 2) on odd numbers, Jacobi reciprocity without     *)
(* the coprimality condition, and the periodicity of jacobi(d,n) in n.       *)
(* ------------------------------------------------------------------------- *)

let CNC2_HALF_ADD4 = prove
 (`!n x. ODD n ==> ((n + 4 * x) - 1) DIV 2 = (n - 1) DIV 2 + 2 * x`,
  REWRITE_TAC[ODD_EXISTS] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(SUC(2 * m) + 4 * x) - 1 = 2 * (m + 2 * x)`;
              ARITH_RULE `SUC(2 * m) - 1 = 2 * m`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let CNC2_NEG1_POW = prove
 (`!n. (--(&1):real) pow n = if EVEN n then &1 else -- &1`,
  REWRITE_TAC[REAL_POW_NEG; REAL_POW_ONE]);;

let CNC2_INT_NEG1_POW = prove
 (`!n. (--(&1):int) pow n = if EVEN n then &1 else -- &1`,
  REWRITE_TAC[INT_POW_NEG; INT_POW_ONE]);;

let CNC2_COPRIME_POW2 = prove
 (`!n. (coprime(n,4) <=> ODD n) /\ (coprime(n,8) <=> ODD n)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `2`; `2`] COPRIME_REXP) THEN
  MP_TAC(SPECL [`n:num`; `2`; `3`] COPRIME_REXP) THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[COPRIME_2]);;

let CNC2_COPRIME_4 = prove
 (`!n d. coprime(n,4 * d) <=> ODD n /\ coprime(n,d)`,
  REWRITE_TAC[COPRIME_RMUL; CNC2_COPRIME_POW2]);;

let CNC2_MOD4_2 = prove
 (`!d. d MOD 4 = 2 ==> ?e. d = 2 * e /\ ODD e`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  EXISTS_TAC `2 * (d DIV 4) + 1` THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN ASM_ARITH_TAC);;

let CNC2_JACOBI_RECIP = prove
 (`!a n. ODD a /\ ODD n
         ==> jacobi(a,n) =
             (--(&1):int) pow ((n - 1) DIV 2 * (a - 1) DIV 2) * jacobi(n,a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `a:num`] JACOBI_RECIPROCITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `jacobi(n,a) = &0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[JACOBI_EQ_0]; INT_ARITH_TAC]);;

let CNC2_JACOBI_SHIFT = prove
 (`!a n. ODD a /\ ODD n ==> jacobi(a,n + 4 * a) = jacobi(a,n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD(n + 4 * a)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `n:num`] CNC2_JACOBI_RECIP) THEN
  MP_TAC(SPECL [`a:num`; `n + 4 * a`] CNC2_JACOBI_RECIP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBGOAL_THEN `jacobi(n + 4 * a,a) = jacobi(n,a)` SUBST1_TAC THENL
   [MATCH_MP_TAC JACOBI_CONG THEN CONV_TAC NUMBER_RULE; ALL_TAC] THEN
  ASM_SIMP_TAC[CNC2_HALF_ADD4] THEN
  REWRITE_TAC[CNC2_INT_NEG1_POW; EVEN_MULT; EVEN_ADD; ARITH_EVEN]);;

let CNC2_JACOBI_2_SHIFT8 = prove
 (`!n j. jacobi(2,n + 8 * j) = jacobi(2,n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[JACOBI_OF_2_CASES] THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[NUMBER_RULE
   `!n j r m. (n + m * j == r) (mod m) <=> (n == r) (mod m)`]);;

let CNC2_JACOBI_PERIOD = prove
 (`!d n. (d MOD 4 = 1 \/ d MOD 4 = 2) /\ ODD n
         ==> jacobi(d,n + 4 * d) = jacobi(d,n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  STRIP_TAC THENL
   [MATCH_MP_TAC CNC2_JACOBI_SHIFT THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC o
    MATCH_MP CNC2_MOD4_2) THEN
  ASM_REWRITE_TAC[JACOBI_LMUL] THEN
  REWRITE_TAC[ARITH_RULE `n + 4 * 2 * e = n + 8 * e`; CNC2_JACOBI_2_SHIFT8] THEN
  AP_TERM_TAC THEN
  SUBST1_TAC(ARITH_RULE `n + 8 * e = (n + 4 * e) + 4 * e`) THEN
  SUBGOAL_THEN `ODD(n + 4 * e)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]; ALL_TAC] THEN
  ASM_SIMP_TAC[CNC2_JACOBI_SHIFT]);;

(* ------------------------------------------------------------------------- *)
(* The values of kchar4 d at 1, 2 and the primes, and its complete           *)
(* multiplicativity, for every d.                                            *)
(* ------------------------------------------------------------------------- *)

let CN_KCHAR4_2 = prove
 (`!d. kchar4 d 2 = &0`,
  REWRITE_TAC[kchar4; ARITH]);;

let CN_KCHAR4_1 = prove
 (`!d. kchar4 d 1 = &1`,
  REWRITE_TAC[kchar4; ARITH; JACOBI_1; int_of_num_th] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[real_pow; REAL_MUL_LID]);;

let CN_KCHAR4_PRIME_DIVIDES = prove
 (`!d r. prime r /\ r divides d ==> kchar4 d r = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[kchar4] THEN
  ASM_SIMP_TAC[JACOBI_PRIME; int_of_num_th; REAL_MUL_RZERO; COND_ID]);;

let CN_KCHAR4_ODD_PRIME = prove
 (`!d r. prime r /\ ~(r = 2) /\ ~(r divides d)
         ==> kchar4 d r =
             if ?s:int. &r divides s pow 2 + &d then &1 else -- &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD r` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_ODD]; ALL_TAC] THEN
  ASM_REWRITE_TAC[kchar4; GSYM NOT_ODD] THEN
  SUBGOAL_THEN `--(&1) pow ((r - 1) DIV 2) = real_of_int(jacobi(r - 1,r))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[JACOBI_MINUS1] THEN
    REWRITE_TAC[int_pow_th; int_neg_th; int_of_num_th];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM int_mul_th; GSYM JACOBI_LMUL] THEN
  ASM_SIMP_TAC[JACOBI_PRIME] THEN
  SUBGOAL_THEN `~(r divides (r - 1) * d)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[PRIME_DIVPROD_EQ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CLASSNO_REP_INT_SQUARE] THEN
  SUBGOAL_THEN
   `!x. (x EXP 2 == (r - 1) * d) (mod r) <=> r divides x EXP 2 + d`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(SPECL [`x EXP 2`; `r - 1`; `d:num`]
     (NUMBER_RULE `!x s d:num. (x == s * d) (mod (s + 1)) <=>
                               (s + 1) divides x + d`)) THEN
    SUBGOAL_THEN `r - 1 + 1 = r` SUBST1_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      REWRITE_TAC[]];
    COND_CASES_TAC THEN REWRITE_TAC[int_of_num_th; int_neg_th]]);;

let CN_KCHAR4_MUL = prove
 (`!d m n. kchar4 d (m * n) = kchar4 d m * kchar4 d n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kchar4; EVEN_MULT] THEN
  ASM_CASES_TAC `EVEN m` THEN ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  REWRITE_TAC[JACOBI_RMUL; int_mul_th] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_EVEN; ODD_EXISTS; ADD1]) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `b:num` SUBST1_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `(2 * a + 1) * (2 * b + 1) = 2 * (2 * a * b + a + b) + 1`
  SUBST1_TAC THENL [CONV_TAC NUM_RING; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB] THEN SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  SUBGOAL_THEN `--(&1) pow (2 * a * b) = &1` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_NEG; EVEN_MULT; ARITH; REAL_POW_ONE]; ALL_TAC] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* kchar4 d is a Dirichlet character modulo 4 d (d = 1 or 2 mod 4).          *)
(* ------------------------------------------------------------------------- *)

let KCHAR4_DIRICHLET = prove
 (`!d. d MOD 4 = 1 \/ d MOD 4 = 2
       ==> dirichlet_character (4 * d) (\n. Cx(kchar4 d n))`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[dirichlet_character; GSYM CX_MUL; CX_INJ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN REWRITE_TAC[kchar4] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EVEN]) THEN
    ASM_SIMP_TAC[CNC2_JACOBI_PERIOD; CNC2_HALF_ADD4] THEN
    REWRITE_TAC[REAL_POW_ADD] THEN
    REWRITE_TAC[CNC2_NEG1_POW; EVEN_MULT; ARITH_EVEN; REAL_MUL_RID];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[kchar4; CNC2_COPRIME_4] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NOT_EVEN] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    REWRITE_TAC[GSYM JACOBI_EQ_0; int_eq; int_of_num_th] THEN
    REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0; REAL_NEG_EQ_0; REAL_OF_NUM_EQ;
                ARITH_EQ];
    REWRITE_TAC[CN_KCHAR4_MUL]]);;

(* ------------------------------------------------------------------------- *)
(* The characters of 2-power modulus: kchar4 1 = chi_(-4) modulo 4,          *)
(* kchar4 2 = chi_(-8) and chi_8 = kchar4 1 * kchar4 2 modulo 8; each        *)
(* changes sign under the shift by half the modulus.                         *)
(* ------------------------------------------------------------------------- *)

let CNC2_PERIODIC_HALF = prove
 (`!f:num->real m h.
        ~(m = 0) /\ (!n. f(n + m) = f n) /\
        (!r. r < m ==> f((r + h) MOD m) = --(f r))
        ==> !a. f(a + h) = --(f a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. Cx((f:num->real) n)`; `m:num`]
    CLASSNO_GAUSS_PERIODIC_MOD) THEN
  ASM_REWRITE_TAC[CX_INJ] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN
  SUBGOAL_THEN `(a + h) MOD m = (a MOD m + h) MOD m` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_ADD THEN
    REWRITE_TAC[CONG_REFL] THEN ONCE_REWRITE_TAC[CONG_SYM] THEN
    REWRITE_TAC[CONG_MOD];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[MOD_LT_EQ]]);;

let CNC2_KCHAR4_EVAL_TAC =
  REWRITE_TAC[kchar4; JACOBI_1; JACOBI_OF_2] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[int_pow_th; int_neg_th; int_of_num_th] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV;;

let CNC2_KCHAR4_VALUES = prove
 (`kchar4 1 3 = -- &1 /\ kchar4 2 7 = -- &1 /\ kchar4 1 7 = -- &1`,
  CNC2_KCHAR4_EVAL_TAC);;

let CNC2_KCHAR4_1_HALF = prove
 (`!a. kchar4 1 (a + 2) = --(kchar4 1 a)`,
  MATCH_MP_TAC CNC2_PERIODIC_HALF THEN EXISTS_TAC `4` THEN
  MP_TAC(SPEC `1` KCHAR4_DIRICHLET) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[dirichlet_character; CX_INJ] THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CNC2_KCHAR4_EVAL_TAC);;

let CNC2_KCHAR4_2_HALF = prove
 (`!a. kchar4 2 (a + 4) = --(kchar4 2 a)`,
  MATCH_MP_TAC CNC2_PERIODIC_HALF THEN EXISTS_TAC `8` THEN
  MP_TAC(SPEC `2` KCHAR4_DIRICHLET) THEN CONV_TAC NUM_REDUCE_CONV THEN
  SIMP_TAC[dirichlet_character; CX_INJ] THEN DISCH_THEN(K ALL_TAC) THEN
  CONV_TAC EXPAND_CASES_CONV THEN CNC2_KCHAR4_EVAL_TAC);;

let CNC2_KCHAR4_1_MOD8 = prove
 (`dirichlet_character 8 (\n. Cx(kchar4 1 n))`,
  MP_TAC(SPEC `1` KCHAR4_DIRICHLET) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[dirichlet_character; CNC2_COPRIME_POW2] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
  SUBST1_TAC(ARITH_RULE `n + 8 = (n + 4) + 4`) THEN ASM_REWRITE_TAC[]);;

let CNC2_CHI8_DIRICHLET = prove
 (`dirichlet_character 8 (\n. Cx(kchar4 1 n * kchar4 2 n))`,
  MP_TAC(ISPECL [`8`; `\n. Cx(kchar4 1 n)`; `\n. Cx(kchar4 2 n)`]
    DIRICHLET_CHARACTER_GROUPMUL) THEN
  REWRITE_TAC[CNC2_KCHAR4_1_MOD8; CX_MUL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPEC `2` KCHAR4_DIRICHLET) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[]);;

let CNC2_CHI8_HALF = prove
 (`!a. kchar4 1 (a + 4) * kchar4 2 (a + 4) = --(kchar4 1 a * kchar4 2 a)`,
  GEN_TAC THEN REWRITE_TAC[CNC2_KCHAR4_2_HALF] THEN
  REWRITE_TAC[ARITH_RULE `a + 4 = (a + 2) + 2`; CNC2_KCHAR4_1_HALF] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Reciprocity for e = 1 and e = 3 mod 4, and the splitting of kchar4 d into *)
(* a character of 2-power modulus 2 h and qchar e, e the odd part of d.      *)
(* ------------------------------------------------------------------------- *)

let CNC2_MOD4_HALF = prove
 (`!e. (e MOD 4 = 1 ==> (e - 1) DIV 2 = 2 * (e DIV 4)) /\
       (e MOD 4 = 3 ==> (e - 1) DIV 2 = 2 * (e DIV 4) + 1)`,
  GEN_TAC THEN CONJ_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `0` THEN MP_TAC(SPECL [`e:num`; `4`] DIVISION) THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN ARITH_TAC);;

let CNC2_ODD_MOD4 = prove
 (`!e. ODD e ==> e MOD 4 = 1 \/ e MOD 4 = 3`,
  GEN_TAC THEN MP_TAC(SPECL [`e:num`; `4`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> GEN_REWRITE_TAC
    (LAND_CONV o RAND_CONV) [th]) MP_TAC) THEN
  SPEC_TAC(`e MOD 4`,`r:num`) THEN CONV_TAC EXPAND_CASES_CONV THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH]);;

let CNC2_JACOBI_RECIP_1 = prove
 (`!e n. e MOD 4 = 1 /\ ODD n ==> jacobi(e,n) = jacobi(n,e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD e` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`e:num`; `n:num`] CNC2_JACOBI_RECIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CNC2_MOD4_HALF] THEN
  REWRITE_TAC[CNC2_INT_NEG1_POW; EVEN_MULT; ARITH_EVEN; INT_MUL_LID]);;

let CNC2_JACOBI_RECIP_3 = prove
 (`!e n. e MOD 4 = 3 /\ ODD n
         ==> jacobi(e,n) = (--(&1):int) pow ((n - 1) DIV 2) * jacobi(n,e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `ODD e` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`e:num`; `n:num`] CNC2_JACOBI_RECIP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CNC2_MOD4_HALF] THEN
  REWRITE_TAC[CNC2_INT_NEG1_POW; EVEN_MULT; EVEN_ADD; ARITH_EVEN]);;

let CNC2_KCHAR4_SPLIT = prove
 (`!d. d MOD 4 = 1 \/ d MOD 4 = 2
       ==> ?h e c. (h = 2 \/ h = 4) /\ ODD e /\ e divides d /\
                   2 * d = h * e /\
                   dirichlet_character (2 * h) (\n. Cx(c n)) /\
                   (!a. c(a + h) = --(c a)) /\
                   c(2 * h - 1) * qchar e (e - 1) = -- &1 /\
                   (!n. kchar4 d n = c n * qchar e n)`,
  GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `ODD d` ASSUME_TAC THENL
     [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`2`; `d:num`; `kchar4 1`] THEN
    ASM_SIMP_TAC[DIVIDES_REFL; CLASSNO_GAUSS_QCHAR_MINUS1;
                 CNC2_KCHAR4_1_HALF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CNC2_KCHAR4_VALUES] THEN
    CONJ_TAC THENL
     [MP_TAC(SPEC `1` KCHAR4_DIRICHLET) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ETA_AX];
      ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[kchar4; qchar; JACOBI_1] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EVEN]) THEN
    MP_TAC(SPECL [`d:num`; `n:num`] CNC2_JACOBI_RECIP_1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[int_of_num_th] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `e:num` STRIP_ASSUME_TAC o
    MATCH_MP CNC2_MOD4_2) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `!n. ODD n
                    ==> kchar4 (2 * e) n =
                        kchar4 2 n * real_of_int(jacobi(e,n))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[kchar4; JACOBI_LMUL; int_mul_th] THEN
    ASM_REWRITE_TAC[GSYM NOT_ODD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP CNC2_ODD_MOD4) THENL
   [MAP_EVERY EXISTS_TAC [`4`; `e:num`; `kchar4 2`] THEN
    ASM_SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1; CNC2_KCHAR4_2_HALF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CNC2_KCHAR4_VALUES] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUMBER_RULE;
      ARITH_TAC;
      MP_TAC(SPEC `2` KCHAR4_DIRICHLET) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ETA_AX];
      REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN ASM_CASES_TAC `EVEN n` THENL
       [ASM_REWRITE_TAC[kchar4; REAL_MUL_LZERO]; ALL_TAC] THEN
      FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EVEN]) THEN
      MP_TAC(SPECL [`e:num`; `n:num`] CNC2_JACOBI_RECIP_1) THEN
      ASM_SIMP_TAC[qchar]];
    MAP_EVERY EXISTS_TAC [`4`; `e:num`; `\n. kchar4 1 n * kchar4 2 n`] THEN
    ASM_SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1; CNC2_CHI8_HALF] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CNC2_KCHAR4_VALUES] THEN
    REPEAT CONJ_TAC THENL
     [CONV_TAC NUMBER_RULE;
      ARITH_TAC;
      REWRITE_TAC[CNC2_CHI8_DIRICHLET];
      REAL_ARITH_TAC;
      X_GEN_TAC `n:num` THEN ASM_CASES_TAC `EVEN n` THENL
       [ASM_REWRITE_TAC[kchar4; REAL_MUL_LZERO]; ALL_TAC] THEN
      FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EVEN]) THEN
      ASM_SIMP_TAC[CNC2_JACOBI_RECIP_3; qchar] THEN
      ASM_REWRITE_TAC[kchar4; GSYM NOT_ODD; JACOBI_1] THEN
      REWRITE_TAC[int_mul_th; int_pow_th; int_neg_th; int_of_num_th] THEN
      CONV_TAC REAL_RING]]);;

(* ------------------------------------------------------------------------- *)
(* Consequences of the splitting: the shift by 2 d, the value at 4 d - 1.    *)
(* ------------------------------------------------------------------------- *)

let CNC2_PERIODIC_GEN_REAL = prove
 (`!m f j a. dirichlet_character m (\n. Cx(f n)) ==> f(a + j * m) = f a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:num`; `\n. Cx((f:num->real) n)`; `j:num`; `a:num`]
    DIRICHLET_CHARACTER_PERIODIC_GEN) THEN
  ASM_REWRITE_TAC[CX_INJ] THEN REWRITE_TAC[ADD_SYM]);;

let CNC2_QCHAR_PERIODIC = prove
 (`!e a j. qchar e (a + j * e) = qchar e a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qchar] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC JACOBI_CONG THEN CONV_TAC NUMBER_RULE);;

let CNC2_CHAR_MINUS1 = prove
 (`!m f j. dirichlet_character m (\n. Cx(f n)) /\ 1 <= j /\ 1 <= m
           ==> f(j * m - 1) = f(m - 1)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `1 <= j` THEN
  REWRITE_TAC[LE_EXISTS] THEN DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST1_TAC) THEN
  SUBGOAL_THEN `(1 + i) * m - 1 = (m - 1) + i * m` SUBST1_TAC THENL
   [UNDISCH_TAC `1 <= m` THEN ARITH_TAC;
    ASM_MESON_TAC[CNC2_PERIODIC_GEN_REAL]]);;

let CN_KCHAR4_HALF = prove
 (`!d a. d MOD 4 = 1 \/ d MOD 4 = 2
         ==> kchar4 d (a + 2 * d) = --(kchar4 d a)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:num` CNC2_KCHAR4_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `e:num`; `c:num->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[CNC2_QCHAR_PERIODIC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  SUBGOAL_THEN `a + h * SUC(2 * j) = (a + h) + j * 2 * h` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CNC2_PERIODIC_GEN_REAL] THEN REAL_ARITH_TAC);;

let CN_KCHAR4_MINUS1 = prove
 (`!d. d MOD 4 = 1 \/ d MOD 4 = 2 ==> kchar4 d (4 * d - 1) = -- &1`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `d:num` CNC2_KCHAR4_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `e:num`; `c:num->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= e /\ 1 <= 2 * h` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ODD e` THEN UNDISCH_TAC `h = 2 \/ h = 4` THEN
    REWRITE_TAC[ODD_EXISTS] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:num->real)(4 * d - 1) = c(2 * h - 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `4 * d = e * 2 * h` SUBST1_TAC THENL
     [UNDISCH_TAC `2 * d = h * e` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CNC2_CHAR_MINUS1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `qchar e (4 * d - 1) = qchar e (e - 1)` SUBST1_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `4 * d = (2 * h) * e` SUBST1_TAC THENL
   [UNDISCH_TAC `2 * d = h * e` THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CNC2_CHAR_MINUS1 THEN ASM_SIMP_TAC[QCHAR_DIRICHLET]);;

(* ------------------------------------------------------------------------- *)
(* The Gauss sum property of a real character of modulus 2 h that changes    *)
(* sign under the shift by h (the sums at even n vanish), and of kchar4 d.   *)
(* ------------------------------------------------------------------------- *)

let CNC2_VSUM_SPLIT_HALF = prove
 (`!g:num->real^N h.
        1 <= h ==> vsum(0..2 * h - 1) g = vsum(0..h - 1) (\a. g a + g(a + h))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 * h - 1 = (h - 1) + h` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[VSUM_ADD_SPLIT; LE_0; VSUM_ADD; FINITE_NUMSEG] THEN
  AP_TERM_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= h ==> h - 1 + 1 = h`] THEN
  SIMP_TAC[VSUM_OFFSET_0; ARITH_RULE `h <= h - 1 + h`;
           ARITH_RULE `(h - 1 + h) - h = h - 1`]);;

let CNC2_SUM_SPLIT_HALF = prove
 (`!g h. 1 <= h ==> sum(0..2 * h - 1) g = sum(0..h - 1) (\a. g a + g(a + h))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\a. Cx((g:num->real) a)`; `h:num`] CNC2_VSUM_SPLIT_HALF) THEN
  ASM_REWRITE_TAC[GSYM CX_ADD; VSUM_CX; CX_INJ]);;

let CNC2_GAUSS_HALF_ZERO = prove
 (`!h f n. 1 <= h /\ (!a. f(a + h) = --(f a)) /\ EVEN n
           ==> vsum(0..2 * h - 1)
                 (\a. Cx(f a) * cexp(ii * Cx(&2 * pi * &a * &n / &(2 * h)))) =
               Cx(&0)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` SUBST1_TAC o
    REWRITE_RULE[EVEN_EXISTS]) THEN
  ASM_SIMP_TAC[CNC2_VSUM_SPLIT_HALF] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  X_GEN_TAC `a:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[CX_NEG] THEN
  SUBGOAL_THEN
   `&2 * pi * &(a + h) * &(2 * k) / &(2 * h) =
    &2 * pi * (&a * &(2 * k) / &(2 * h) + &k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `~(&h:real = &0)` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SIMP_TAC[CLASSNO_GAUSS_CEXP_INTEGER; INTEGER_CLOSED] THEN
  REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING);;

let CNC2_GAUSS_PROPERTY_HALF = prove
 (`!h f. 1 <= h /\ dirichlet_character (2 * h) (\n. Cx(f n)) /\
         (!a. f(a + h) = --(f a)) /\ (!n. ODD n ==> coprime(n,2 * h))
         ==> !n. vsum(0..2 * h - 1)
                   (\a. Cx(f a) *
                        cexp(ii * Cx(&2 * pi * &a * &n / &(2 * h)))) =
                 Cx(f n) *
                 vsum(0..2 * h - 1)
                   (\a. Cx(f a) *
                        cexp(ii * Cx(&2 * pi * &a * &1 / &(2 * h))))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `coprime(n,2 * h)` THENL
   [MP_TAC(ISPECL [`2 * h`; `\n. Cx((f:num->real) n)`; `n:num`]
      CLASSNO_GAUSS_PROPERTY_COPRIME) THEN
    ASM_REWRITE_TAC[CNJ_CX] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:num->real) n = &0` SUBST1_TAC THENL
   [MP_TAC(ISPECL [`2 * h`; `\n. Cx((f:num->real) n)`; `n:num`]
      DIRICHLET_CHARACTER_EQ_0) THEN
    ASM_REWRITE_TAC[CX_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO] THEN MATCH_MP_TAC CNC2_GAUSS_HALF_ZERO THEN
  ASM_REWRITE_TAC[GSYM NOT_ODD] THEN ASM_MESON_TAC[]);;

let CN_KCHAR4_GAUSS_PROPERTY = prove
 (`!d. squarefree d /\ (d MOD 4 = 1 \/ d MOD 4 = 2)
       ==> ?gs. !n. vsum(0..4 * d - 1)
                      (\a. Cx(kchar4 d a) *
                           cexp(ii * Cx(&2 * pi * &a * &n / &(4 * d)))) =
                    Cx(kchar4 d n) * gs`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPEC `d:num` CNC2_KCHAR4_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:num`; `e:num`; `c:num->real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN
   `1 <= h /\ (!n. ODD n ==> coprime(n,2 * h)) /\ coprime(2 * h,e) /\
    ~(e = 0) /\ (2 * h) * e = 4 * d`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `2 * d = h * e` THEN UNDISCH_TAC `h = 2 \/ h = 4` THEN
    UNDISCH_TAC `ODD e` THEN DISCH_TAC THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN DISCH_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CNC2_COPRIME_POW2;
                ONCE_REWRITE_RULE[COPRIME_SYM] CNC2_COPRIME_POW2] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_MESON_TAC[ODD]; ASM_ARITH_TAC]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `c:num->real`] CNC2_GAUSS_PROPERTY_HALF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `g1 = vsum(0..2 * h - 1)
           (\a. Cx((c:num->real) a) *
                cexp(ii * Cx(&2 * pi * &a * &1 / &(2 * h))))` THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `qchar` CLASSNO_GAUSS_PROPERTY_REAL) THEN ANTS_TAC THENL
   [SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_QCHAR_NONPRINCIPAL;
             CLASSNO_SERIES_QCHAR_RMUL];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `e:num`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SQUAREFREE_DIVISOR]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g2:complex`) THEN
  MP_TAC(ISPECL
   [`2 * h`; `e:num`; `\n. Cx(kchar4 d n)`; `\n. Cx((c:num->real) n)`;
    `\n. Cx(qchar e n)`; `g1:complex`; `g2:complex`]
    CLASSNO_GAUSS_PROPERTY_MUL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[QCHAR_DIRICHLET; GSYM CX_MUL; CX_INJ] THEN ASM_ARITH_TAC;
    SUBST1_TAC(ASSUME `(2 * h) * e = 4 * d`) THEN REWRITE_TAC[] THEN
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Modulus 4 m with f(a + 2 m) = -f(a): the first moment is -4 m times the   *)
(* sum of f(a) over 0 < a < m, so abs L(1,f) = pi abs(t) / (2 sqrt m).       *)
(* ------------------------------------------------------------------------- *)

let CNC2_SUM_HALVES = prove
 (`!f h. sum(1..2 * h) f = sum(1..h) (\b. f b + f((2 * h + 1) - b))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\a. Cx((f:num->real) a)`; `h:num`]
    CLASSNO_GAUSS_VSUM_HALVES) THEN
  REWRITE_TAC[GSYM CX_ADD; VSUM_CX; CX_INJ]);;

let CNC2_MOMENT_HALF = prove
 (`!m f. 1 <= m /\ f 0 = &0 /\ f m = &0 /\
         (!a. f(a + 2 * m) = --(f a)) /\
         (!a. 1 <= a /\ a <= 4 * m ==> f(4 * m - a) = --(f a))
         ==> sum(1..4 * m - 1) (\a. &a * f a) =
             --(&(4 * m)) * sum(1..m - 1) f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:num->real)(2 * m) = &0` ASSUME_TAC THENL
   [MP_TAC(SPEC `0` (ASSUME `!a. (f:num->real)(a + 2 * m) = --(f a)`)) THEN
    REWRITE_TAC[ADD_CLAUSES; ASSUME `(f:num->real) 0 = &0`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c <= 2 * m ==> (f:num->real)(2 * m - c) = f c`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:num` THEN DISCH_TAC THEN ASM_CASES_TAC `c = 0` THEN
    ASM_REWRITE_TAC[SUB_0] THEN
    MP_TAC(SPEC `2 * m - c`
     (ASSUME `!a. (f:num->real)(a + 2 * m) = --(f a)`)) THEN
    MP_TAC(SPEC `c:num` (ASSUME
     `!a. 1 <= a /\ a <= 4 * m ==> (f:num->real)(4 * m - a) = --(f a)`)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(2 * m - c) + 2 * m = 4 * m - c` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..4 * m - 1) (\a. &a * (f:num->real) a) =
    --(&(2 * m)) * sum(0..2 * m - 1) f`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `sum(1..4 * m - 1) (\a. &a * (f:num->real) a) =
      sum(0..2 * (2 * m) - 1) (\a. &a * f a)`
    SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 * (2 * m) = 4 * m`] THEN
      SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CNC2_SUM_SPLIT_HALF; ARITH_RULE `1 <= m ==> 1 <= 2 * m`] THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `a:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..2 * m - 1) (f:num->real) = &2 * sum(1..m - 1) f`
  SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC] THEN
  SUBGOAL_THEN
   `sum(0..2 * m - 1) (f:num->real) = f 0 + sum(1..2 * m - 1) f /\
    sum(1..2 * m) f = sum(1..2 * m - 1) f + f(2 * m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES];
      MATCH_MP_TAC SUM_CLAUSES_RIGHT THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(0..2 * m - 1) (f:num->real) = sum(1..2 * m) f`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CNC2_SUM_HALVES] THEN
  SUBGOAL_THEN
   `sum(1..m) (\b. (f:num->real) b + f((2 * m + 1) - b)) =
    sum(1..m) (\b. f b + f(b - 1))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `b:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(2 * m + 1) - b = 2 * m - (b - 1)` SUBST1_TAC THENL
     [ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN `sum(1..m) (\b. (f:num->real)(b - 1)) = sum(0..m - 1) f`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`1`; `\b. (f:num->real)(b - 1)`; `0`; `m - 1`]
      SUM_OFFSET) THEN
    ASM_SIMP_TAC[ADD_CLAUSES; SUB_ADD; ADD_SUB; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..m) (f:num->real) = sum(1..m - 1) f + f m /\
    sum(0..m - 1) f = f 0 + sum(1..m - 1) f`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_CLAUSES_RIGHT THEN ASM_ARITH_TAC;
      SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES]];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let CNC2_L1_FOUR = prove
 (`!m f. 1 < m /\ dirichlet_character (4 * m) (\n. Cx(f n)) /\
         f(4 * m - 1) = -- &1 /\ (!a. f(a + 2 * m) = --(f a)) /\
         (?gs. !n. vsum(0..4 * m - 1)
                     (\a. Cx(f a) *
                          cexp(ii * Cx(&2 * pi * &a * &n / &(4 * m)))) =
                   Cx(f n) * gs)
         ==> norm(Lfunction (\n. Cx(f n))) =
             pi * abs(sum(1..m - 1) f) / (&2 * sqrt(&m))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `gs:complex`)) THEN
  MP_TAC(ISPECL [`4 * m`; `f:num->real`; `gs:complex`]
    CLASSNO_GAUSS_LFUNCTION_ODD_NORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`m:num`; `f:num->real`] CNC2_MOMENT_HALF) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MP_TAC(ISPECL [`4 * m`; `\n. Cx((f:num->real) n)`; `0`]
        DIRICHLET_CHARACTER_EQ_0) THEN
      ASM_REWRITE_TAC[CX_INJ; COPRIME_0] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_ARITH_TAC;
      SUBGOAL_THEN `~(m = 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`4 * m`; `\n. Cx((f:num->real) n)`; `m:num`]
        DIRICHLET_CHARACTER_EQ_0) THEN
      ASM_REWRITE_TAC[CX_INJ; COPRIME_RMUL; COPRIME_REFL];
      ASM_REWRITE_TAC[];
      X_GEN_TAC `a:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`4 * m`; `\n. Cx((f:num->real) n)`; `a:num`]
        CLASSNO_GAUSS_CHAR_REFLECT) THEN
      ASM_REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG; REAL_ABS_NUM] THEN
  SUBGOAL_THEN `sqrt(&(4 * m)) = &2 * sqrt(&m)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    SIMP_TAC[SQRT_MUL; REAL_POS] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SQRT_UNIQUE THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt(&m) /\ &0 < &m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  UNDISCH_TAC `&0 < sqrt(&m)` THEN UNDISCH_TAC `&0 < &m` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Products of Dirichlet characters of different moduli.                     *)
(* ------------------------------------------------------------------------- *)

let CN_DIRICHLET_CHARACTER_PRODUCT = prove
 (`!m1 m2 c1 c2.
        dirichlet_character m1 c1 /\ dirichlet_character m2 c2
        ==> dirichlet_character (m1 * m2) (\n. c1 n * c2 n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[dirichlet_character] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(ISPECL [`m1:num`; `c1:num->complex`; `m2:num`; `n:num`]
      DIRICHLET_CHARACTER_PERIODIC_GEN) THEN
    MP_TAC(ISPECL [`m2:num`; `c2:num->complex`; `m1:num`; `n:num`]
      DIRICHLET_CHARACTER_PERIODIC_GEN) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    BINOP_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    X_GEN_TAC `n:num` THEN
    REWRITE_TAC[COMPLEX_ENTIRE; COPRIME_RMUL; DE_MORGAN_THM] THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]));
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN
    REPEAT(FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th])) THEN
    CONV_TAC COMPLEX_RING]);;

let CN_INTEGER_KCHAR4 = prove
 (`!d a. integer(kchar4 d a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[kchar4] THEN COND_CASES_TAC THEN
  REWRITE_TAC[INTEGER_CLOSED] THEN MATCH_MP_TAC INTEGER_MUL THEN
  REWRITE_TAC[INTEGER_REAL_OF_INT] THEN MATCH_MP_TAC INTEGER_POW THEN
  REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* The class number formula in absolute value for (-4 k d / .).              *)
(* ------------------------------------------------------------------------- *)

let CN_L1_KCHAR4 = prove
 (`!k d. squarefree(k * d) /\ k MOD 4 = 1 /\ (d MOD 4 = 1 \/ d MOD 4 = 2) /\
         1 < k * d
         ==> ?t. integer t /\
                 norm(Lfunction (\n. Cx(qchar k n * kchar4 d n))) =
                 pi * abs t / (&2 * sqrt(&(k * d)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SQUAREFREE_MUL] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `ODD k` ASSUME_TAC THENL
   [MATCH_MP_TAC CLASSNO_GAUSS_ODD_MOD4 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0) /\ ~(d = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `ODD 0` THEN REWRITE_TAC[ODD];
      UNDISCH_TAC `0 MOD 4 = 1 \/ 0 MOD 4 = 2` THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?gs. !n. vsum(0..4 * (k * d) - 1)
               (\a. Cx(qchar k a * kchar4 d a) *
                    cexp(ii * Cx(&2 * pi * &a * &n / &(4 * (k * d))))) =
             Cx(qchar k n * kchar4 d n) * gs`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `d:num` CN_KCHAR4_GAUSS_PROPERTY) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `g2:complex`) THEN
    MP_TAC(ISPEC `qchar` CLASSNO_GAUSS_PROPERTY_REAL) THEN ANTS_TAC THENL
     [SIMP_TAC[QCHAR_DIRICHLET; CLASSNO_GAUSS_QCHAR_NONPRINCIPAL;
               CLASSNO_SERIES_QCHAR_RMUL];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `k:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `g1:complex`) THEN
    MP_TAC(ISPECL
     [`k:num`; `4 * d`; `\n. Cx(qchar k n * kchar4 d n)`;
      `\n. Cx(qchar k n)`; `\n. Cx(kchar4 d n)`; `g1:complex`;
      `g2:complex`] CLASSNO_GAUSS_PROPERTY_MUL) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[QCHAR_DIRICHLET; KCHAR4_DIRICHLET; GSYM CX_MUL] THEN
      ASM_REWRITE_TAC[CNC2_COPRIME_4; MULT_EQ_0; ARITH_EQ];
      ALL_TAC] THEN
    SUBST1_TAC(ARITH_RULE `k * 4 * d = 4 * (k * d)`) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `sum(1..k * d - 1) (\a. qchar k a * kchar4 d a)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGER_SUM THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC INTEGER_MUL THEN
    REWRITE_TAC[qchar; INTEGER_REAL_OF_INT; CN_INTEGER_KCHAR4];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k * d`; `\a. qchar k a * kchar4 d a`] CNC2_L1_FOUR) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`k:num`; `4 * d`; `\n. Cx(qchar k n)`;
                   `\n. Cx(kchar4 d n)`] CN_DIRICHLET_CHARACTER_PRODUCT) THEN
    ASM_SIMP_TAC[QCHAR_DIRICHLET; KCHAR4_DIRICHLET; GSYM CX_MUL] THEN
    REWRITE_TAC[ARITH_RULE `k * 4 * d = 4 * (k * d)`];
    SUBGOAL_THEN
     `qchar k (4 * (k * d) - 1) = qchar k (k - 1) /\
      kchar4 d (4 * (k * d) - 1) = kchar4 d (4 * d - 1)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THENL
       [SUBST1_TAC(ARITH_RULE `4 * (k * d) = (4 * d) * k`) THEN
        MATCH_MP_TAC CNC2_CHAR_MINUS1 THEN ASM_SIMP_TAC[QCHAR_DIRICHLET] THEN
        ASM_ARITH_TAC;
        SUBST1_TAC(ARITH_RULE `4 * (k * d) = k * (4 * d)`) THEN
        MATCH_MP_TAC CNC2_CHAR_MINUS1 THEN ASM_SIMP_TAC[KCHAR4_DIRICHLET] THEN
        ASM_ARITH_TAC];
      ASM_SIMP_TAC[CLASSNO_GAUSS_QCHAR_MINUS1; CN_KCHAR4_MINUS1] THEN
      REAL_ARITH_TAC];
    X_GEN_TAC `a:num` THEN
    SUBGOAL_THEN `qchar k (a + 2 * (k * d)) = qchar k a` SUBST1_TAC THENL
     [SUBST1_TAC(ARITH_RULE `2 * (k * d) = (2 * d) * k`) THEN
      REWRITE_TAC[CNC2_QCHAR_PERIODIC];
      ALL_TAC] THEN
    UNDISCH_TAC `ODD k` THEN REWRITE_TAC[ODD_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
    SUBGOAL_THEN `a + 2 * (SUC(2 * j) * d) = (a + 2 * d) + j * 4 * d`
    SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[CNC2_PERIODIC_GEN_REAL; KCHAR4_DIRICHLET; CN_KCHAR4_HALF] THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;
