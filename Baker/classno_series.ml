(* ========================================================================= *)
(* The real quadratic characters as Dirichlet characters, and series tools   *)
(* for the lattice series of binary quadratic forms and the limit s -> 1+.   *)
(*                                                                           *)
(* Purpose: QCHAR_DIRICHLET: for odd m, n -> (n | m) is a Dirichlet          *)
(* character modulo m. The real characters qchar: bounds, congruences,       *)
(* multiplicativity in the modulus and in the argument, the Dirichlet        *)
(* convolution of qchar (k d) and qchar k (CLASSNO_SERIES_DIVISOR_CHAR); the *)
(* L-function of a real non-principal character is real                      *)
(* (CLASSNO_SERIES_LFUNCTION_REAL; qchar m is non-principal for odd          *)
(* squarefree m > 1 by QCHAR_NONPRINCIPAL of Baker/classno_gauss.ml). The    *)
(* tools for the lattice series of a positive definite form                  *)
(* (Baker/qform_series.ml) and for the limit formula (Baker/qform_limit.ml): *)
(* subsequences of partial sums, block bounds and the uniform convergence of *)
(* series of functions (CLASSNO_SERIES_BLOCK_TAIL, _UNIFORM_CONTINUOUS),     *)
(* sums over symmetric boxes of integers and paired series                   *)
(* (CLASSNO_SERIES_BOX_SUM, _PAIRED_BLOCKS), bounded block sums of periodic  *)
(* sequences of mean zero (CLASSNO_SERIES_PERIODIC_BOUND), the Dirichlet     *)
(* test with an explicit bound (CLASSNO_SERIES_DIRICHLET_BOUND), the kernels *)
(* (t^2 + D)^-s and their sums Psi along arithmetic progressions (the        *)
(* CLASSNO_SERIES_KERNEL_* and CLASSNO_SERIES_PSI_* lemmas), the continuity  *)
(* of zeta_k(2s) at s = 1 from the right (CLASSNO_SERIES_ZETA_CONTINUOUS)    *)
(* and limits at s = 1 from the right (CLASSNO_SERIES_WITHIN_LIMIT). The     *)
(* product of the two L-series of the class number one problem as the        *)
(* lattice series of the principal form, and its limit s -> 1+, are          *)
(* corollaries of the general form results (Baker/classno_product.ml).       *)
(*                                                                           *)
(* Main results: QCHAR_DIRICHLET; CLASSNO_SERIES_DIVISOR_CHAR,               *)
(* CLASSNO_SERIES_LFUNCTION_REAL, CLASSNO_SERIES_ZETA_CONTINUOUS,            *)
(* CLASSNO_SERIES_C0; helper names CLASSNO_SERIES_*.                         *)
(*                                                                           *)
(* Uses: Baker/classno_chardefs.ml (qchar, zeta_coprime),                    *)
(* Baker/classno_series_lib.ml (UNIMODAL_INFSUM_LE); Library/jacobi.ml       *)
(* (JACOBI_CONG, JACOBI_EQ_0, JACOBI_LMUL, JACOBI_RMUL, JACOBI_BOUND),       *)
(* 100/dirichlet.ml (dirichlet_character, chi_0, Lfunction, LFUNCTION_CNJ),  *)
(* Multivariate/realanalysis.ml (REAL_SUMMABLE_ZETA_INTEGER).                *)
(* ========================================================================= *)

needs "Baker/classno_chardefs.ml";;
needs "Baker/classno_series_lib.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The real quadratic characters are Dirichlet characters.                   *)
(* ------------------------------------------------------------------------- *)

let QCHAR_DIRICHLET = prove
 (`!m. ODD m ==> dirichlet_character m (\n. Cx(qchar m n))`,
  REWRITE_TAC[dirichlet_character; qchar] THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC JACOBI_CONG THEN CONV_TAC NUMBER_RULE;
    REWRITE_TAC[CX_INJ; GSYM JACOBI_EQ_0; int_eq; int_of_num_th];
    REWRITE_TAC[JACOBI_LMUL; int_mul_th; CX_MUL]]);;

(* The remaining lemmas are parsed with real arithmetic as the default.      *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Generic facts about real series and finite sums: subsequences of partial  *)
(* sums, block bounds, uniform convergence, sums by blocks and by values.    *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_REALLIM_SUBSEQ = prove
 (`!f:num->real l r.
        (f ---> l) sequentially /\ (!n. n <= r n)
        ==> ((\n. f(r n)) ---> l) sequentially`,
  REWRITE_TAC[REALLIM_SEQUENTIALLY] THEN MESON_TAC[LE_TRANS]);;

let CLASSNO_SERIES_BLOCK_TAIL = prove
 (`!f:num->real bd p.
        (bd ---> &0) sequentially /\
        (!m n. p <= m ==> abs(sum(m..n) f) <= bd m)
        ==> real_summable (from p) f /\
            !n. p <= n
                ==> abs(real_infsum (from p) f - sum(p..n) f) <= bd(n + 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `real_summable (from p) (f:num->real)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUMMABLE_CAUCHY] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REALLIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N + p:num` THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REWRITE_TAC[GE] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `from p INTER (m..n) = m..n` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTER; IN_FROM; IN_NUMSEG] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `(bd:num->real) m` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `abs(x:real) < e ==> x < e`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ASM_REWRITE_TAC[]] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` REALLIM_UBOUND) THEN
  EXISTS_TAC `\M. abs(sum(p..M) (f:num->real) - sum(p..n) f)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REALLIM_ABS THEN MATCH_MP_TAC REALLIM_SUB THEN
    ASM_REWRITE_TAC[REALLIM_CONST; GSYM REAL_SERIES_FROM; REAL_SUMS_INFSUM];
    EXISTS_TAC `n + 1` THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(ISPECL [`f:num->real`; `p:num`; `n:num`; `M:num`] SUM_COMBINE_R) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ARITH `(x + y) - x = y:real`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `p <= n:num` THEN ARITH_TAC]);;

let CLASSNO_SERIES_UNIFORM_CONTINUOUS = prove
 (`!f:real->num->real bd S a p.
        (bd ---> &0) sequentially /\
        (!s m n. s IN S /\ p <= m ==> abs(sum(m..n) (f s)) <= bd m) /\
        a IN S /\
        (!n. p <= n ==> (\s. f s n) real_continuous (atreal a within S))
        ==> (\s. real_infsum (from p) (f s)) real_continuous
            (atreal a within S)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "blk")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cont")))) THEN
  SUBGOAL_THEN
   `!s. s IN S
        ==> !n. p <= n
                ==> abs(real_infsum (from p) ((f:real->num->real) s) -
                        sum(p..n) (f s)) <= bd(n + 1)`
  (LABEL_TAC "tail") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(f:real->num->real) s`; `bd:num->real`; `p:num`]
      CLASSNO_SERIES_BLOCK_TAIL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "blk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `(bd ---> &0) sequentially` THEN
  REWRITE_TAC[REALLIM_SEQUENTIALLY; REAL_SUB_RZERO] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
  ABBREV_TAC `N = N0 + p:num` THEN
  SUBGOAL_THEN `abs((bd:num->real)(N + 1)) < e / &3` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "N" THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\s. sum(p..N) ((f:real->num->real) s)) real_continuous (atreal a within S)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`atreal a within S`;
                   `\n:num s:real. (f:real->num->real) s n`;
                   `p..N`] REAL_CONTINUOUS_SUM) THEN
    REWRITE_TAC[FINITE_NUMSEG; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    USE_THEN "cont" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL; REALLIM_WITHINREAL] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ANTS_TAC THENL [UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `dd:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `p <= N:num` ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "tail" (fun th ->
    MP_TAC(MP (SPEC `N:num` (MP (SPEC `s:real` th) (ASSUME `(s:real) IN S`)))
              (ASSUME `p <= N:num`)) THEN
    MP_TAC(MP (SPEC `N:num` (MP (SPEC `a:real` th) (ASSUME `(a:real) IN S`)))
              (ASSUME `p <= N:num`))) THEN
  UNDISCH_TAC `abs((bd:num->real)(N + 1)) < e / &3` THEN
  REAL_ARITH_TAC);;

let CLASSNO_SERIES_ABS_MUL_LE = prove
 (`!a x. abs a <= &1 /\ &0 <= x ==> abs(a * x) <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

let CLASSNO_SERIES_SUM_BLOCKS = prove
 (`!f:num->real p q.
     1 <= p
     ==> sum(0..(q + 1) * p - 1) f =
         sum(0..p - 1) (\a. sum(0..q) (\i. f(a + i * p)))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG; MULT_CLAUSES; ADD_CLAUSES; ETA_AX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:num->real`; `0`; `(q + 1) * p - 1`; `(SUC q + 1) * p - 1`]
    SUM_COMBINE_R) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ADD1; RIGHT_ADD_DISTRIB] THEN UNDISCH_TAC `1 <= p` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q + 1) * p - 1 + 1 = 0 + (q + 1) * p /\
                (SUC q + 1) * p - 1 = (p - 1) + (q + 1) * p`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ADD1; RIGHT_ADD_DISTRIB] THEN UNDISCH_TAC `1 <= p` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; GSYM SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[ADD1]);;

let CLASSNO_SERIES_SUM_DELTA_SWAP = prove
 (`!s:A->bool t:B->bool q h N.
     FINITE s /\ FINITE t
     ==> sum s (\x. sum t (\y. if q x y <= N then h(q x y) else &0)) =
         sum(0..N) (\l. h l * sum s (\x. sum t (\y. if q x y = l then &1
                                                    else &0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x y. (if (q:A->B->num) x y <= N then (h:num->real)(q x y) else &0) =
          sum(0..N) (\l. if q x y = l then h l else &0)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `!l. (if (q:A->B->num) x y = l then (h:num->real) l else &0) =
          (if l = q x y then h(q x y) else &0)`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_MESON_TAC[];
      REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_0]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_LMUL; COND_RAND; REAL_MUL_RID; REAL_MUL_RZERO] THEN
  MP_TAC(ISPECL
   [`\l:num x:A. sum (t:B->bool)
                  (\y. if (q:A->B->num) x y = l then (h:num->real) l else &0)`;
    `0..N`; `s:A->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN BETA_TAC THEN
  MP_TAC(ISPECL
   [`\l:num y:B. if (q:A->B->num) x y = l then (h:num->real) l else &0`;
    `0..N`; `t:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sums over symmetric boxes of integers, and the paired series sum over n   *)
(* of h(n) + h(-n-1) of a function on the integers.                          *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_BOX_SUM = prove
 (`!h:int->real X.
     sum {x:int | --(&X) <= x /\ x <= &X} h =
     h(&0) + sum(1..X) (\n. h(&n) + h(--(&n)))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[INT_NEG_0; INT_ARITH `&0 <= x /\ x <= &0 <=> x = &0:int`] THEN
    REWRITE_TAC[SING_GSPEC; SUM_SING; SUM_CLAUSES_NUMSEG; ARITH; REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x:int | --(&(SUC X)) <= x /\ x <= &(SUC X)} =
    &(SUC X) INSERT (--(&(SUC X)) INSERT {x | --(&X) <= x /\ x <= &X})`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; GSYM INT_OF_NUM_SUC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(&(SUC X) IN (--(&(SUC X)) INSERT {x:int | --(&X) <= x /\ x <= &X})) /\
    ~(--(&(SUC X)) IN {x:int | --(&X) <= x /\ x <= &X})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; IN_ELIM_THM; GSYM INT_OF_NUM_SUC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_INT_SEG] THEN
  ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC X`] THEN
  REAL_ARITH_TAC);;

let CLASSNO_SERIES_BOX_NEG = prove
 (`!h:int->real X.
     sum {x:int | --(&X) <= x /\ x <= &X} (\x. h(--x)) =
     sum {x:int | --(&X) <= x /\ x <= &X} h`,
  REWRITE_TAC[CLASSNO_SERIES_BOX_SUM; INT_NEG_0; INT_NEG_NEG] THEN
  REWRITE_TAC[REAL_ADD_SYM]);;

let CLASSNO_SERIES_PAIRED_BOX = prove
 (`!h:int->real X.
     sum(0..X) (\n. h(&n) + h(--(&n) - &1)) =
     sum {x:int | --(&X) <= x /\ x <= &X} h + h(--(&X) - &1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLASSNO_SERIES_BOX_SUM; SUM_ADD_NUMSEG] THEN
  SUBGOAL_THEN
   `sum(0..X) (\n. (h:int->real)(--(&n) - &1)) =
    sum(1..X) (\n. h(--(&n))) + h(--(&X) - &1)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`1`; `\n. (h:int->real)(--(&n))`; `0`; `X:num`]
      SUM_OFFSET) THEN
    REWRITE_TAC[ADD_CLAUSES; GSYM INT_OF_NUM_ADD;
                INT_ARITH `--(x + &1):int = --x - &1`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC X`] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `--(x + &1):int = --x - &1`];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN REAL_ARITH_TAC);;

let CLASSNO_SERIES_BOX_LIMIT = prove
 (`!h:int->real l.
     ((\n. h(&n) + h(--(&n) - &1)) real_sums l) (from 0) /\
     ((\n. h(--(&n) - &1)) ---> &0) sequentially
     ==> ((\X. sum {x:int | --(&X) <= x /\ x <= &X} h) ---> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_SERIES_FROM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!X. sum {x:int | --(&X) <= x /\ x <= &X} h =
        sum(0..X) (\n. h(&n) + h(--(&n) - &1)) - h(--(&X) - &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[CLASSNO_SERIES_PAIRED_BOX; REAL_ARITH `(a + b) - b:real = a`];
    ALL_TAC] THEN
  SUBST1_TAC(REAL_ARITH `l:real = l - &0`) THEN
  MATCH_MP_TAC REALLIM_SUB THEN ASM_REWRITE_TAC[]);;

let CLASSNO_SERIES_BOX_MONO = prove
 (`!f:int->int->real X Y X' Y'.
     X <= X' /\ Y <= Y' /\ (!x y. &0 <= f x y)
     ==> sum {x:int | --(&X) <= x /\ x <= &X}
          (\x. sum {y:int | --(&Y) <= y /\ y <= &Y} (f x)) <=
         sum {x:int | --(&X') <= x /\ x <= &X'}
          (\x. sum {y:int | --(&Y') <= y /\ y <= &Y'} (f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {x:int | --(&X) <= x /\ x <= &X}
               (\x. sum {y:int | --(&Y') <= y /\ y <= &Y'} (f x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_INT_SEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    ASM_REWRITE_TAC[FINITE_INT_SEG; SUBSET; IN_ELIM_THM] THEN
    UNDISCH_TAC `Y <= Y':num` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    INT_ARITH_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_INT_SEG; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [UNDISCH_TAC `X <= X':num` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      INT_ARITH_TAC;
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
      ASM_REWRITE_TAC[FINITE_INT_SEG]]]);;

(* The paired partial sums up to k (N + 1) - 1, grouped by the residue       *)
(* class m of x modulo k: x = m + k n and x = m - k (n + 1).                 *)

let CLASSNO_SERIES_PAIRED_BLOCK = prove
 (`!h:int->real k q.
     1 <= k
     ==> sum(k * q..k * q + k - 1) (\j. h(&j) + h(--(&j) - &1)) =
         sum(0..k - 1) (\m. h(&m + &k * &q) + h(&m - &k * (&q + &1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k * q:num`; `\j. (h:int->real)(&j) + h(--(&j) - &1)`;
                 `0`; `k - 1`] SUM_OFFSET) THEN
  ASM_SIMP_TAC[ADD_CLAUSES; ARITH_RULE `1 <= k ==> k - 1 + q = q + k - 1`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SUM_REFLECT] THEN
  REWRITE_TAC[ARITH_RULE `~(k - 1 < 0)`; SUB_0] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  BETA_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_SUB;
               ARITH_RULE `i <= k - 1 /\ 1 <= k ==> i <= k - 1`;
               ARITH_RULE `1 <= k ==> 1 <= k`] THEN
  INT_ARITH_TAC);;

let CLASSNO_SERIES_PAIRED_BLOCKS = prove
 (`!h:int->real k N.
     1 <= k
     ==> sum(0..k * (N + 1) - 1) (\j. h(&j) + h(--(&j) - &1)) =
         sum(0..k - 1)
          (\m. sum(0..N) (\n. h(&m + &k * &n) + h(&m - &k * (&n + &1))))`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[SUM_SING_NUMSEG] THEN
    MP_TAC(SPECL [`h:int->real`; `k:num`; `0`] CLASSNO_SERIES_PAIRED_BLOCK) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; MULT_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:int->real`; `k:num`; `SUC N`]
      CLASSNO_SERIES_PAIRED_BLOCK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\j. (h:int->real)(&j) + h(--(&j) - &1)`;
                 `0`; `k * (N + 1) - 1`; `k * (SUC N + 1) - 1`]
                     SUM_COMBINE_R) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] THEN UNDISCH_TAC `1 <= k` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `k * (N + 1) - 1 + 1 = k * SUC N /\
                k * (SUC N + 1) - 1 = k * SUC N + k - 1`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[ADD1; LEFT_ADD_DISTRIB] THEN UNDISCH_TAC `1 <= k` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; LE_0; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[ADD1]);;

(* ------------------------------------------------------------------------- *)
(* Block sums of a periodic sequence of mean zero are bounded.               *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_PERIODIC_SHIFT = prove
 (`!e:num->real k.
     1 <= k /\ (!y. e(y + k) = e y) /\ sum(0..k - 1) e = &0
     ==> !a. sum(a..a + k - 1) e = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  SUBGOAL_THEN `SUC a + k - 1 = a + k /\ a + k = SUC(a + k - 1)`
  STRIP_ASSUME_TAC THENL [UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sum(a..a + k) (e:num->real) = e a + sum(SUC a..a + k) e`
  ASSUME_TAC THENL
   [REWRITE_TAC[ADD1] THEN MATCH_MP_TAC SUM_CLAUSES_LEFT THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(a..a + k) (e:num->real) = sum(a..a + k - 1) e + e(a + k)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `a + k - 1 = (a + k) - 1` SUBST1_TAC THENL
     [UNDISCH_TAC `1 <= k` THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_CLAUSES_RIGHT THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `sum(a..a + k) (e:num->real) = e a + sum(SUC a..a + k) e` THEN
  UNDISCH_TAC
     `sum(a..a + k) (e:num->real) = sum(a..a + k - 1) e + e(a + k)` THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let CLASSNO_SERIES_PERIODIC_BOUND = prove
 (`!e:num->real k B.
     1 <= k /\ (!y. e(y + k) = e y) /\ sum(0..k - 1) e = &0 /\
     (!y. abs(e y) <= B)
     ==> !m n. abs(sum(m..n) e) <= &2 * &k * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  MP_TAC(SPECL [`e:num->real`; `k:num`] CLASSNO_SERIES_PERIODIC_SHIFT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "shift") THEN
  SUBGOAL_THEN `!n. abs(sum(0..n) (e:num->real)) <= &k * B` ASSUME_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `n < k:num` THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&(CARD(0..n)) * B` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_ABS_BOUND THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
        REWRITE_TAC[CARD_NUMSEG; SUB_0] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `n < k:num` THEN
        ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e:num->real`; `0`; `n - k:num`; `n:num`] SUM_COMBINE_R) THEN
    ANTS_TAC THENL [ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    SUBGOAL_THEN `sum(n - k + 1..n) (e:num->real) = &0` SUBST1_TAC THENL
     [SUBGOAL_THEN `(n - k + 1) + (k - 1) = n` MP_TAC THENL
       [UNDISCH_TAC `~(n < k:num)` THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(fun th -> USE_THEN "shift"
        (MP_TAC o REWRITE_RULE[th] o SPEC `n - k + 1`)) THEN
      REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `~(n < k:num)` THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  SUBGOAL_THEN `&0 <= &k * B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  ASM_CASES_TAC `n < m:num` THENL
   [ASM_SIMP_TAC[SUM_TRIV_NUMSEG; REAL_ABS_0] THEN
    UNDISCH_TAC `&0 <= &k * B` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 <= &k * B` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:num->real`; `0`; `m - 1`; `n:num`] SUM_COMBINE_R) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `~(n < m:num)` THEN UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUB_ADD; LE_1] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_ASSUM(MP_TAC o SPEC `m - 1`) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Elementary tail bounds and the Dirichlet test with an explicit bound.     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_INV_SQUARE_BLOCK = prove
 (`!m n. 1 <= m ==> sum(m..n) (\y. inv(&y pow 2)) <= &2 / &m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..n) (\y. &2 * (inv(&y) - inv(&(y + 1))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `y:num` THEN STRIP_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `&1 <= &y` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    SUBGOAL_THEN `inv(&y) - inv(&y + &1) = inv(&y * (&y + &1))` SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD
       `&1 <= y ==> inv(y) - inv(y + &1) = inv(y * (y + &1))`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_ARITH
      `&1 <= y ==> &0 < y /\ &0 < y + &1`] THEN
    ASM_SIMP_TAC[REAL_POW_2; REAL_FIELD
     `&1 <= y ==> inv(y * y) * y * (y + &1) = &1 + inv y`] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> &1 + x <= &2`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUM_LMUL] THEN
    MP_TAC(SPECL [`m:num`; `n:num`]
      (INST [`\y:num. inv(&y)`,`f:num->real`] SUM_DIFFS)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[real_div] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= b ==> &2 * (a - b) <= &2 * a`) THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS];
      REWRITE_TAC[REAL_MUL_RZERO] THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN REAL_ARITH_TAC]]);;

let CLASSNO_SERIES_INV_SQUARE_BLOCK1 = prove
 (`!m N. sum(m..N) (\n. inv((&n + &1) pow 2)) <= &2 / (&m + &1)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`1`; `\j. inv(&j pow 2)`; `m:num`; `N:num`] SUM_OFFSET) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`m + 1`; `N + 1`] CLASSNO_SERIES_INV_SQUARE_BLOCK) THEN
  REWRITE_TAC[ARITH_RULE `1 <= m + 1`; GSYM REAL_OF_NUM_ADD]);;

let CLASSNO_SERIES_DIRICHLET_BOUND = prove
 (`!a b B p.
     &0 < B /\ 1 <= p /\
     (!m n. p <= m ==> abs(sum(m..n) a) <= B) /\
     (!n. p <= n ==> &0 <= b n) /\
     (!n. p <= n ==> b(n + 1) <= b n)
     ==> !m n. p <= m ==> abs(sum(m..n) (\k. a k * b k)) <= &2 * B * b m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. Cx((a:num->real) k)`; `\k. Cx((b:num->real) k)`;
                 `B:real`; `p:num`] SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) THEN
  ASM_SIMP_TAC[VSUM_CX; FINITE_NUMSEG; COMPLEX_NORM_CX; REAL_CX; RE_CX] THEN
  REWRITE_TAC[GSYM CX_MUL] THEN
    SIMP_TAC[VSUM_CX; FINITE_NUMSEG; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `abs((b:num->real) m) = b m`
   (fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[REAL_ABS_REFL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The kernels t -> (t^2 + D)^-s: positive, unimodal with the peak at 0,     *)
(* decreasing in D, and summable along arithmetic progressions.              *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_KERNEL_POS = prove
 (`!D s t. &0 < D ==> &0 < t pow 2 + D /\ &0 <= inv((t pow 2 + D) rpow s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < t pow 2 + D` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN UNDISCH_TAC `&0 < D` THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_INV_EQ; RPOW_POS_LE; REAL_LT_IMP_LE]]);;

let CLASSNO_SERIES_KERNEL_MONO = prove
 (`!D D' s x y.
     &0 < D /\ D <= D' /\ &0 <= s /\ abs x <= abs y
     ==> inv((y pow 2 + D') rpow s) <= inv((x pow 2 + D) rpow s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[RPOW_POS_LT; CLASSNO_SERIES_KERNEL_POS] THEN
  MATCH_MP_TAC RPOW_LE2 THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; CLASSNO_SERIES_KERNEL_POS] THEN
  MP_TAC(SPECL [`x:real`; `y:real`] REAL_LE_SQUARE_ABS) THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `D <= D':real` THEN REAL_ARITH_TAC);;

let CLASSNO_SERIES_KERNEL_LE_INV = prove
 (`!D s t. &1 <= D /\ &1 <= s
           ==> inv((t pow 2 + D) rpow s) <= inv(t pow 2 + D)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= t pow 2 + D` ASSUME_TAC THENL
   [MP_TAC(SPEC `t:real` REAL_LE_POW_2) THEN UNDISCH_TAC `&1 <= D` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
     [UNDISCH_TAC `&1 <= t pow 2 + D` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1`; `s:real`; `t pow 2 + D`] RPOW_MONO_LE) THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let CLASSNO_SERIES_KERNEL_TAIL = prove
 (`!D s t n. &1 <= D /\ &1 <= s /\ &1 <= &n /\ &n / &2 <= abs t
             ==> inv((t pow 2 + D) rpow s) <= &4 * inv(&n pow 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(t pow 2 + D)` THEN
  ASM_SIMP_TAC[CLASSNO_SERIES_KERNEL_LE_INV] THEN
  SUBGOAL_THEN `&4 * inv(&n pow 2) = inv((&n / &2) pow 2)` SUBST1_TAC THENL
   [UNDISCH_TAC `&1 <= &n` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN UNDISCH_TAC `&1 <= &n` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`&n / &2`; `t:real`] REAL_LE_SQUARE_ABS) THEN
  SUBGOAL_THEN `abs(&n / &2) = &n / &2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL] THEN UNDISCH_TAC `&1 <= &n` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&1 <= D` THEN REAL_ARITH_TAC);;

let CLASSNO_SERIES_KERNEL_SUMMABLE = prove
 (`!D s c al.
     &1 <= D /\ &1 <= s /\ &1 <= c
     ==> real_summable (from 0)
          (\n. inv(((al + c * &n) pow 2 + D) rpow s) +
               inv(((al - c * (&n + &1)) pow 2 + D) rpow s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SUMMABLE_COMPARISON THEN
  EXISTS_TAC `\n. &8 * inv(&n pow 2)` THEN
  SIMP_TAC[REAL_SUMMABLE_LMUL; REAL_SUMMABLE_ZETA_INTEGER; LE_REFL] THEN
  MP_TAC(SPEC `&2 * abs al + &1` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[GE; IN_FROM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * abs al + &1 <= &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&n <= c * &n` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= (c - &1) * n ==> n <= c * n`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    UNDISCH_TAC `&1 <= c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &n` ASSUME_TAC THENL
   [MP_TAC(SPEC `al:real` REAL_ABS_POS) THEN
    UNDISCH_TAC `&2 * abs al + &1 <= &n` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= a /\ &0 <= b /\ a <= &4 * x /\ b <= &4 * x
       ==> abs(a + b) <= &8 * x`) THEN
  SIMP_TAC[CLASSNO_SERIES_KERNEL_POS; REAL_ARITH `&1 <= D ==> &0 < D`;
           ASSUME `&1 <= D`] THEN
  CONJ_TAC THEN MATCH_MP_TAC CLASSNO_SERIES_KERNEL_TAIL THEN
  ASM_REWRITE_TAC[] THENL
   [UNDISCH_TAC `&n <= c * &n`; ALL_TAC] THEN
  UNDISCH_TAC `&2 * abs al + &1 <= &n` THEN
  TRY(UNDISCH_TAC `&n <= c * &n`) THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_MUL_RID] THEN
  UNDISCH_TAC `&1 <= c` THEN REAL_ARITH_TAC);;

(* The reference sums Psi = sum over n in Z of (c^2 n^2 + D)^-s: bounded by  *)
(* 8 / y when D >= y^2, and decreasing in D.                                 *)

let CLASSNO_SERIES_PSI_SUMMABLE = prove
 (`!D s c. &1 <= D /\ &1 <= s /\ &1 <= c
           ==> real_summable (from 0)
                (\n. inv(((c * &n) pow 2 + D) rpow s) +
                     inv(((c * (&n + &1)) pow 2 + D) rpow s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`D:real`; `s:real`; `c:real`; `&0`]
    CLASSNO_SERIES_KERNEL_SUMMABLE) THEN
  ASM_REWRITE_TAC[REAL_ADD_LID; REAL_SUB_LZERO; REAL_POW_NEG; ARITH]);;

let CLASSNO_SERIES_PSI_TERM = prove
 (`!D s c y n.
     &1 <= s /\ &1 <= c /\ 1 <= y /\ &y pow 2 <= D
     ==> inv(((c * &n) pow 2 + D) rpow s) +
         inv(((c * (&n + &1)) pow 2 + D) rpow s)
         <= &4 * inv((&n + &y) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &y pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&n <= c * &n /\ &n <= c * (&n + &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= (c - &1) * x /\ n <= x ==> n <= c * x`) THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN UNDISCH_TAC `&1 <= c` THEN
       REAL_ARITH_TAC;
       REAL_ARITH_TAC]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. &n <= z
        ==> inv((z pow 2 + D) rpow s) <= inv(&n pow 2 + &y pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `inv((&n pow 2 + &y pow 2) rpow s)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLASSNO_SERIES_KERNEL_MONO THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
         [UNDISCH_TAC `&1 <= &y pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [UNDISCH_TAC `&1 <= s` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `&n <= z` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC CLASSNO_SERIES_KERNEL_LE_INV THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&n pow 2 + &y pow 2) <= &2 * inv((&n + &y) pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * inv((&n + &y) pow 2) = inv((&n + &y) pow 2 / &2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_INV_MUL; REAL_INV_INV] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < x ==> &0 < x / &2`) THEN
      MATCH_MP_TAC REAL_POW_LT THEN
      SUBGOAL_THEN `&1 <= &y` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
      REWRITE_TAC[REAL_POW_2] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= (a - b) * (a - b)
                     ==> ((a + b) * (a + b)) / &2 <= a * a + b * b`) THEN
      REWRITE_TAC[REAL_LE_SQUARE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(((c * &n) pow 2 + D) rpow s) <= inv(&n pow 2 + &y pow 2) /\
    inv(((c * (&n + &1)) pow 2 + D) rpow s) <= inv(&n pow 2 + &y pow 2)`
  MP_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `inv(&n pow 2 + &y pow 2) <= &2 * inv((&n + &y) pow 2)` THEN
  REAL_ARITH_TAC);;

let CLASSNO_SERIES_PSI_BOUND = prove
 (`!D s c y.
     &1 <= s /\ &1 <= c /\ 1 <= y /\ &y pow 2 <= D
     ==> real_infsum (from 0)
          (\n. inv(((c * &n) pow 2 + D) rpow s) +
               inv(((c * (&n + &1)) pow 2 + D) rpow s)) <= &8 / &y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= D` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&y pow 2` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC UNIMODAL_INFSUM_LE THEN
  ASM_SIMP_TAC[CLASSNO_SERIES_PSI_SUMMABLE] THEN
  X_GEN_TAC `N:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(0..N) (\n. &4 * inv((&n + &y) pow 2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    MATCH_MP_TAC CLASSNO_SERIES_PSI_TERM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MP_TAC(ISPECL [`y:num`; `\j. inv(&j pow 2)`; `0`; `N:num`] SUM_OFFSET) THEN
  REWRITE_TAC[ADD_CLAUSES; GSYM REAL_OF_NUM_ADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &2 * inv(&y) ==> &4 * x <= &8 * inv(&y)`) THEN
  REWRITE_TAC[GSYM real_div] THEN
  MATCH_MP_TAC CLASSNO_SERIES_INV_SQUARE_BLOCK THEN ASM_REWRITE_TAC[]);;

let CLASSNO_SERIES_PSI_MONO = prove
 (`!D D' s c.
     &1 <= D /\ D <= D' /\ &1 <= s /\ &1 <= c
     ==> real_infsum (from 0)
          (\n. inv(((c * &n) pow 2 + D') rpow s) +
               inv(((c * (&n + &1)) pow 2 + D') rpow s)) <=
         real_infsum (from 0)
          (\n. inv(((c * &n) pow 2 + D) rpow s) +
               inv(((c * (&n + &1)) pow 2 + D) rpow s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_LE THEN
  MAP_EVERY EXISTS_TAC
   [`\n. inv(((c * &n) pow 2 + D') rpow s) +
         inv(((c * (&n + &1)) pow 2 + D') rpow s)`;
    `\n. inv(((c * &n) pow 2 + D) rpow s) +
         inv(((c * (&n + &1)) pow 2 + D) rpow s)`;
    `from 0`] THEN
  REWRITE_TAC[REAL_SUMS_INFSUM] THEN
  SUBGOAL_THEN `&1 <= D'` ASSUME_TAC THENL
   [UNDISCH_TAC `D <= D':real` THEN UNDISCH_TAC `&1 <= D` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CLASSNO_SERIES_PSI_SUMMABLE] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC CLASSNO_SERIES_KERNEL_MONO THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  UNDISCH_TAC `&1 <= D` THEN UNDISCH_TAC `&1 <= s` THEN REAL_ARITH_TAC);;

let CLASSNO_SERIES_PSI_POS = prove
 (`!D s c. &1 <= D /\ &1 <= s /\ &1 <= c
           ==> &0 <= real_infsum (from 0)
                      (\n. inv(((c * &n) pow 2 + D) rpow s) +
                           inv(((c * (&n + &1)) pow 2 + D) rpow s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_SERIES_POS THEN
  EXISTS_TAC `\n. inv(((c * &n) pow 2 + D) rpow s) +
                  inv(((c * (&n + &1)) pow 2 + D) rpow s)` THEN
  EXISTS_TAC `from 0` THEN
  ASM_SIMP_TAC[REAL_SUMS_INFSUM; CLASSNO_SERIES_PSI_SUMMABLE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD THEN
  ASM_SIMP_TAC[CLASSNO_SERIES_KERNEL_POS; REAL_ARITH `&1 <= D ==> &0 < D`]);;

(* ------------------------------------------------------------------------- *)
(* The characters qchar: bounds, congruences, multiplicativity, the          *)
(* Dirichlet convolution of qchar (k d) and qchar k; c0 = (d + 1) / 4.       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_C0 = prove
 (`!d. d MOD 4 = 3 ==> 4 * (d + 1) DIV 4 = d + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d + 1`; `4`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  SUBGOAL_THEN `(d + 1) MOD 4 = 0` SUBST1_TAC THENL
   [MP_TAC(SPECL [`d:num`; `4`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
    DISCH_THEN(fun th -> ONCE_REWRITE_TAC[CONJUNCT1 th]) THEN
    REWRITE_TAC[ARITH_RULE `(q * 4 + 3) + 1 = 4 * (q + 1)`] THEN
    REWRITE_TAC[MOD_MULT];
    ARITH_TAC]);;

let CLASSNO_SERIES_QCHAR_BOUND = prove
 (`!m n. abs(qchar m n) <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[qchar] THEN
  MP_TAC(SPECL [`n:num`; `m:num`] JACOBI_BOUND) THEN
  REWRITE_TAC[int_le; int_abs_th; int_of_num_th]);;

let CLASSNO_SERIES_QCHAR_CONG = prove
 (`!k a b. &0 <= a /\ &0 <= b /\ (a == b) (mod &k)
           ==> qchar k (num_of_int a) = qchar k (num_of_int b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[qchar] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC JACOBI_CONG THEN REWRITE_TAC[num_congruent] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT]);;

let CLASSNO_SERIES_QCHAR_RMUL = prove
 (`!k d n. qchar (k * d) n = qchar k n * qchar d n`,
  REWRITE_TAC[qchar; JACOBI_RMUL; int_mul_th]);;

let CLASSNO_SERIES_QCHAR_LMUL = prove
 (`!k a b. qchar k (a * b) = qchar k a * qchar k b`,
  REWRITE_TAC[qchar; JACOBI_LMUL; int_mul_th]);;

let CLASSNO_SERIES_DIVISOR_CHAR = prove
 (`!k d l. sum {m | m divides l} (\m. qchar (k * d) m * qchar k (l DIV m)) =
           qchar k l * sum {m | m divides l} (\m. qchar d m)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN
  REWRITE_TAC[IN_ELIM_THM; DIVIDES_DIV_MULT] THEN DISCH_TAC THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_RMUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [SYM(ASSUME
    `l DIV m * m = l`)] THEN
  REWRITE_TAC[CLASSNO_SERIES_QCHAR_LMUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Continuity in s at s = 1 (from the right) of a^-s and of zeta_k(2s).      *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_RPOW_TERM_CONTINUOUS = prove
 (`!q b a. &0 < b ==> (\s. q / b rpow s) real_continuous atreal a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
  MATCH_MP_TAC REAL_CONTINUOUS_INV_ATREAL THEN
  ASM_SIMP_TAC[REAL_CONTINUOUS_AT_RPOW_RIGHT; RPOW_EQ_0; REAL_LT_IMP_NZ]);;

let CLASSNO_SERIES_ZETA_TERM = prove
 (`!k s n. &1 <= s /\ 1 <= n
           ==> abs(if coprime(n,k) then inv((&n pow 2) rpow s) else &0)
               <= inv(&n pow 2)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC; REWRITE_TAC[REAL_ABS_0; REAL_LE_INV_EQ; REAL_LE_POW_2]] THEN
  SUBGOAL_THEN `&1 <= &n pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&n pow 2) rpow s` ASSUME_TAC THENL
   [MATCH_MP_TAC RPOW_POS_LT THEN UNDISCH_TAC `&1 <= &n pow 2` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_INV; REAL_ARITH `&0 < x ==> abs x = x`] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN CONJ_TAC THENL
   [UNDISCH_TAC `&1 <= &n pow 2` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`&1`; `s:real`; `&n pow 2`] RPOW_MONO_LE) THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1]);;

let CLASSNO_SERIES_ZETA_CONTINUOUS = prove
 (`!k. (!s. &1 <= s
            ==> real_summable (from 1)
                 (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0)) /\
       (\s. real_infsum (from 1)
             (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0))
       real_continuous (atreal (&1) within {s | &1 <= s})`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!s m N. &1 <= s /\ 1 <= m
            ==> abs(sum(m..N)
                 (\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0))
                <= &2 / &m`
  (LABEL_TAC "blk") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m..N) (\n. inv(&n pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(m..N) (\n. abs(if coprime(n,k) then inv((&n pow 2) rpow s)
                                     else &0))` THEN
      REWRITE_TAC[SUM_ABS_NUMSEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC CLASSNO_SERIES_ZETA_TERM THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `1 <= m` THEN UNDISCH_TAC `m <= i:num` THEN ARITH_TAC;
      MATCH_MP_TAC CLASSNO_SERIES_INV_SQUARE_BLOCK THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((\m. &2 / &m) ---> &0) sequentially` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REALLIM_NULL_LMUL THEN
    REWRITE_TAC[REALLIM_1_OVER_N];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0`;
      `\m. &2 / &m`; `1`] CLASSNO_SERIES_BLOCK_TAIL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      USE_THEN "blk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\s n. if coprime(n,k) then inv((&n pow 2) rpow s) else &0`;
    `\m. &2 / &m`; `{s:real | &1 <= s}`; `&1`; `1`]
   CLASSNO_SERIES_UNIFORM_CONTINUOUS) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN USE_THEN "blk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ATREAL_WITHINREAL THEN
    ASM_CASES_TAC `coprime(n,k)` THEN
    ASM_REWRITE_TAC[REAL_CONTINUOUS_CONST] THEN
    MP_TAC(ISPECL [`&1`; `&n pow 2`; `&1`]
      CLASSNO_SERIES_RPOW_TERM_CONTINUOUS) THEN
    REWRITE_TAC[real_div; REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `1 <= n` THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The L-functions of real non-principal characters are real.               *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_LFUNCTION_REAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
         ==> Lfunction c = Cx(Re(Lfunction c))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REWRITE_TAC[GSYM REAL; REAL_CNJ] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_CNJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[REAL_CNJ]);;

(* ------------------------------------------------------------------------- *)
(* Limits as s -> 1+.                                                        *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_SERIES_NONTRIVIAL = prove
 (`~trivial_limit (atreal (&1) within {s | &1 < s})`,
  REWRITE_TAC[GSYM EVENTUALLY_FALSE; EVENTUALLY_WITHINREAL; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1 + e / &2`) THEN
  UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC);;

let CLASSNO_SERIES_ZETA_EQ = prove
 (`!k. zeta_coprime k =
       real_infsum (from 1)
        (\n. if coprime(n,k) then inv((&n pow 2) rpow &1) else &0)`,
  REWRITE_TAC[zeta_coprime; RPOW_POW; REAL_POW_1]);;

let CLASSNO_SERIES_WITHIN_LIMIT = prove
 (`!f:real->real.
     f real_continuous (atreal (&1) within {s | &1 <= s})
     ==> (f ---> f(&1)) (atreal (&1) within {s | &1 < s})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REALLIM_WITHINREAL_SUBSET THEN
  EXISTS_TAC `{s:real | &1 <= s}` THEN
  ASM_REWRITE_TAC[GSYM REAL_CONTINUOUS_WITHINREAL] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* Leave the project default.                                                *)

prioritize_num();;
