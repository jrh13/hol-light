prioritize_num();;

let FORSTER_PUZZLE = prove
 (`(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n`,
  REWRITE_TAC[GT; GSYM ADD1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n m. f(m) < n ==> m <= f m` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LT] THEN
    INDUCT_TAC THEN ASM_MESON_TAC[LE_0; LE_SUC_LT; LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= f n` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. f(n) < f(SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> f(m) < f(n)` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC[LT; LT_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. (f m < f n) <=> m < n` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_CASES; LT_ANTISYM; LT_REFL]; ALL_TAC] THEN
  ASM_MESON_TAC[LE_ANTISYM; LT_SUC_LE]);;

(* ------------------------------------------------------------------------- *)
(* Alternative; shorter but less transparent and taking longer to run.       *)
(* ------------------------------------------------------------------------- *)

let FORSTER_PUZZLE = prove
 (`(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n`,
  REWRITE_TAC[GT; GSYM ADD1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n m. f(m) < n ==> m <= f m` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LT] THEN
    INDUCT_TAC THEN ASM_MESON_TAC[LE_0; LE_SUC_LT; LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. n <= f n` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. f(n) < f(SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> f(m) < f(n)` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN ASM_MESON_TAC[LT; LT_TRANS]; ALL_TAC] THEN
  ASM_MESON_TAC[LE_ANTISYM; LT_CASES; LT_ANTISYM; LT_REFL; LT_SUC_LE]);;

(* ------------------------------------------------------------------------- *)
(* Robin Milner's proof.                                                     *)
(* ------------------------------------------------------------------------- *)

let FORSTER_PUZZLE = prove
 (`(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n`,
  REWRITE_TAC[GT; GSYM ADD1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= f(n + m)` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LE_0; ADD_CLAUSES; LE_SUC_LT] THEN
    ASM_MESON_TAC[LET_TRANS; SUB_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. f(n) < f(SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LET_TRANS; LE_TRANS; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> f(m) <= f(n)` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    ASM_MESON_TAC[LE; LE_REFL; LT_IMP_LE; LE_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LE_ANTISYM] THEN
  ASM_MESON_TAC[LT_SUC_LE; NOT_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* A variant of Robin's proof avoiding explicit use of addition.             *)
(* ------------------------------------------------------------------------- *)

let FORSTER_PUZZLE = prove
 (`(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n`,
  REWRITE_TAC[GT; GSYM ADD1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> m <= f(n)` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LE_0] THEN
    INDUCT_TAC THEN REWRITE_TAC[LE; NOT_SUC] THEN
    ASM_MESON_TAC[LE_SUC_LT; LET_TRANS; LE_REFL; LT_IMP_LE; LE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!n. f(n) < f(SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m <= n ==> f(m) <= f(n)` ASSUME_TAC THENL
   [GEN_TAC THEN INDUCT_TAC THEN
    ASM_MESON_TAC[LE; LE_REFL; LT_IMP_LE; LE_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM LE_ANTISYM] THEN
  ASM_MESON_TAC[LT_SUC_LE; NOT_LT; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* The shortest?                                                             *)
(* ------------------------------------------------------------------------- *)

let FORSTER_PUZZLE = prove
 (`(!n. f(n + 1) > f(f(n))) ==> !n. f(n) = n`,
  REWRITE_TAC[GT; GSYM ADD1] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m n. m <= f(n + m)` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[LE_0; ADD_CLAUSES; LE_SUC_LT] THEN
    ASM_MESON_TAC[LET_TRANS; SUB_ADD]; ALL_TAC] THEN
  SUBGOAL_THEN `!n. f(n) < f(SUC n)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LET_TRANS; LE_TRANS; ADD_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `!m n. f(m) < f(n) ==> m < n` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_MESON_TAC[LT_LE; LE_0; LTE_TRANS; LE_SUC_LT];
    ALL_TAC] THEN
  ASM_MESON_TAC[LE_ANTISYM; ADD_CLAUSES; LT_SUC_LE]);;
