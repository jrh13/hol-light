(* ========================================================================= *)
(* Generic lemmas used by the algebraic number theory files ANT/, each of    *)
(* which would naturally belong to a core file of HOL Light or to            *)
(* Multivariate/misc.ml (named in its comment): an upper bound for an        *)
(* integer function on a finite set (UPPER_BOUND_FINITE_SET_INT), the        *)
(* integer segment {k | 0 <= k < n} has n elements (HAS_SIZE_INT_SEG_LT),    *)
(* the integer part of an n-th root (NUM_ROOT_FLOOR), the bridge from        *)
(* integer to num divisibility through num_of_int(abs d)                     *)
(* (INT_DIVIDES_NUM_OF_INT_ABS, NUM_OF_INT_ABS_POW; used for the squarefree  *)
(* integers of ANT/quadratic.ml) and FORALL_LT_2. The general lemmas of the  *)
(* same kind that have homes in library files are there: integer and real    *)
(* sums and products as ring sums and the other ring lemmas in               *)
(* Library/ringtheory.ml, isum and iproduct facts in Library/isum.ml and     *)
(* Library/products.ml, the integer forms of the squarefree lemmas in        *)
(* Library/pocklington.ml.                                                   *)
(*                                                                           *)
(* Uses: the core of HOL Light only. The needs lines of                      *)
(* Library/ringtheory.ml and Library/products.ml serve the files that load   *)
(* this one (ANT/zlattice.ml uses IPRODUCT_ABS_BOUND of Library/products.ml  *)
(* through them).                                                            *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/products.ml";;

(* ------------------------------------------------------------------------- *)
(* An upper bound for an integer function on a finite set.                   *)
(* ------------------------------------------------------------------------- *)

(* Multivariate/misc.ml, next to UPPER_BOUND_FINITE_SET_REAL.                *)
let UPPER_BOUND_FINITE_SET_INT = prove
 (`!f:A->int s. FINITE s ==> ?a. !x. x IN s ==> f x <= a`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`b:A`; `t:A->bool`] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:int` o CONJUNCT1) THEN
  EXISTS_TAC `max ((f:A->int) b) a` THEN CONJ_TAC THENL
   [INT_ARITH_TAC;
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Integers and natural numbers.                                             *)
(* ------------------------------------------------------------------------- *)

(* iterate.ml, after FINITE_INT_SEG.                                         *)
let HAS_SIZE_INT_SEG_LT = prove
 (`!n. {k:int | &0 <= k /\ k < &n} HAS_SIZE n`,
  GEN_TAC THEN
  SUBGOAL_THEN `{k:int | &0 <= k /\ k < &n} = IMAGE int_of_num {m | m < n}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `k:int` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `num_of_int k` THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; GSYM INT_OF_NUM_LT];
      STRIP_TAC THEN ASM_REWRITE_TAC[INT_POS; INT_OF_NUM_LT]];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
    REWRITE_TAC[HAS_SIZE_NUMSEG_LT; INT_OF_NUM_EQ] THEN MESON_TAC[]]);;

(* arith.ml (the integer part of the n-th root of N, from num_MAX).          *)
let NUM_ROOT_FLOOR = prove
 (`!n N. ~(n = 0) ==> ?t. t EXP n <= N /\ N < (t + 1) EXP n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\t. t EXP n <= N` num_MAX) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN ASM_REWRITE_TAC[EXP_ZERO; LE_0];
      EXISTS_TAC `N:num` THEN X_GEN_TAC `t:num` THEN
      MATCH_MP_TAC(ARITH_RULE `t:num <= u ==> u <= N ==> t <= N`) THEN
      MP_TAC(SPECL [`t:num`; `1`; `n:num`] LE_EXP) THEN
      REWRITE_TAC[EXP_1] THEN DISCH_THEN SUBST1_TAC THEN
      COND_CASES_TAC THEN ASM_ARITH_TAC];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `t + 1`)) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* int.ml, after INT_DIVIDES_ABS; with NUM_OF_INT_ABS_POW the                *)
(* bridge from integer divisibility to num divisibility used for             *)
(* squarefree integers, squarefree(num_of_int(abs d)).                       *)
let INT_DIVIDES_NUM_OF_INT_ABS = prove
 (`!d n:int. d divides n <=> num_of_int(abs d) divides num_of_int(abs n)`,
  SIMP_TAC[num_divides; INT_OF_NUM_OF_INT; INT_ABS_POS; INT_DIVIDES_ABS]);;

let NUM_OF_INT_ABS_POW = prove
 (`!x:int n. num_of_int(abs x pow n) = num_of_int(abs x) EXP n`,
  SIMP_TAC[GSYM INT_OF_NUM_EQ; INT_OF_NUM_OF_INT; INT_ABS_POS; INT_POW_LE;
           GSYM INT_OF_NUM_POW]);;

(* arith.ml (cf. FORALL_LT_MOD_THM).                                         *)
let FORALL_LT_2 = prove
 (`!P. (!i. i < 2 ==> P i) <=> P 0 /\ P 1`,
  MESON_TAC[ARITH_RULE `i < 2 <=> i = 0 \/ i = 1`;
            ARITH_RULE `0 < 2 /\ 1 < 2`]);;
