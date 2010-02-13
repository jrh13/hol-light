(* ========================================================================= *)
(* Analysis of solutions to Pell equation                                    *)
(* ========================================================================= *)

needs "Library/analysis.ml";;
needs "Library/transc.ml";;
needs "Library/prime.ml";;

prioritize_real();;

let PELL_INDUCTION = prove
 (`P 0 /\ P 1 /\ (!n. P n /\ P (n + 1) ==> P(n + 2)) ==> !n. P n`,
  STRIP_TAC THEN
  SUBGOAL_THEN `!n. P n /\ P(n + 1)` (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_SIMP_TAC[ADD1; ARITH_RULE `SUC(n + 1) = n + 2`]);;

(* ------------------------------------------------------------------------- *)
(* Useful number-theoretic basics                                            *)
(* ------------------------------------------------------------------------- *)

let ROOT_NONPOWER = prove
 (`!p q d n. ~(q = 0) /\ (p EXP n = d * q EXP n) ==> ?a. d = a EXP n`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[EXP; MULT_CLAUSES] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `q:num`; `p:num`] DIVIDES_EXP2_REV) THEN
  ASM_REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `d:num`) THEN
  REWRITE_TAC[EQT_INTRO(SPEC_ALL MULT_SYM)] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` SUBST_ALL_TAC) THEN
  EXISTS_TAC `a:num` THEN
  UNDISCH_TAC `(a * q) EXP n = d * q EXP n` THEN
  ASM_SIMP_TAC[MULT_EXP; EQ_MULT_RCANCEL; EXP_EQ_0]);;

let INTEGER_SUB_LEMMA = prove
 (`!x y. ?n. (&x - &y) pow 2 = &n pow 2`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_THEN MP_TAC (SPECL [`&x`; `&y`] REAL_LE_TOTAL) THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN DISCH_TAC THENL
   [EXISTS_TAC `y - x:num`; EXISTS_TAC `x - y:num`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let SQRT_LINEAR_EQ = prove
 (`!a u v x y.
       2 <= a
       ==> ((&u + &v * sqrt(&a pow 2 - &1) = &x + &y * sqrt(&a pow 2 - &1)) <=>
            (u = x) /\ (v = y))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `(a + b = c + d) <=> (a - c = d - b)`] THEN
  REWRITE_TAC[GSYM REAL_SUB_RDISTRIB] THEN
  DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow)`) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  ASM_SIMP_TAC[SQRT_POW_2; REAL_SUB_LE; REAL_POW_LE_1; REAL_OF_NUM_LE;
               ARITH_RULE `2 <= a ==> 1 <= a`] THEN
  X_CHOOSE_TAC `p:num` (SPECL [`u:num`; `x:num`] INTEGER_SUB_LEMMA) THEN
  X_CHOOSE_TAC `q:num` (SPECL [`y:num`; `v:num`] INTEGER_SUB_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `2 <= a ==> 1 <= a`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `a EXP 2 - 1`; `2`] ROOT_NONPOWER) THEN
  ASM_REWRITE_TAC[EQT_INTRO(SPEC_ALL MULT_SYM)] THEN
  MATCH_MP_TAC(TAUT `~b /\ (a ==> c) ==> ((~a ==> b) ==> c)`) THEN
  CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:num` MP_TAC) THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (ARITH_RULE `(a - 1 = b) ==> 1 < a ==> (a - b = 1)`)) THEN
    SUBST1_TAC(SYM(SPEC `a:num` (CONJUNCT1 EXP))) THEN
    ASM_REWRITE_TAC[LT_EXP; ARITH_LE; ARITH_LT] THEN
    REWRITE_TAC[EXP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
      `(a - b = 1) ==> (a = b + 1)`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_ADD; GSYM
                REAL_OF_NUM_POW] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REAL_ARITH `(a * a = b * b + &1) ==> ((a + b) * (a - b) = &1)`)) THEN
    DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow)`) THEN
    REWRITE_TAC[REAL_POW_MUL] THEN
    X_CHOOSE_TAC `c:num` (SPECL [`a:num`; `b:num`] INTEGER_SUB_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; EXP_ONE; EXP_EQ_1; MULT_EQ_1; ARITH_EQ] THEN
    UNDISCH_TAC `2 <= a` THEN ARITH_TAC;
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `p EXP 2 = 0 EXP 2 * (a EXP 2 - 1)` THEN
    REWRITE_TAC[ARITH; MULT_CLAUSES; EXP_EQ_0] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(&u - &x) pow 2 = &0 pow 2` THEN
    UNDISCH_TAC `(&y - &v) pow 2 = &0 pow 2` THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_EQ_0; ARITH_EQ; REAL_SUB_0] THEN
    SIMP_TAC[REAL_OF_NUM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Recurrence defining the solutions.                                        *)
(* ------------------------------------------------------------------------- *)

let X_DEF =
  let th = prove
   (`!a. ?X. !n. X n = if n = 0 then 1
                       else if n = 1 then a
                       else 2 * a * X(n-1) - X(n-2)`,
    GEN_TAC THEN MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    BINOP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `n - m < n <=> ~(m = 0) /\ ~(n = 0)`; ARITH_EQ]) in
  new_specification ["X"] (REWRITE_RULE[SKOLEM_THM] th);;

let X_CLAUSES = prove
 (`(!a. X a 0 = 1) /\
   (!a. X a 1 = a) /\
   (!a n. X a (n + 2) = 2 * a * X a (n + 1) - X a (n))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [X_DEF] THEN
  REWRITE_TAC[ARITH_EQ; ADD_EQ_0; ARITH_RULE `~(n + 2 = 1)`] THEN
  REWRITE_TAC[ARITH_RULE `((n + 2) - 2 = n) /\ ((n + 2) - 1 = n + 1)`]);;

let Y_DEF =
  let th = prove
   (`!a. ?Y. !n. Y n = if n = 0 then 0
                       else if n = 1 then 1
                       else 2 * a * Y(n-1) - Y(n-2)`,
    GEN_TAC THEN MATCH_MP_TAC(MATCH_MP WF_REC WF_num) THEN
    REPEAT STRIP_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    BINOP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `n - m < n <=> ~(m = 0) /\ ~(n = 0)`; ARITH_EQ]) in
  new_specification ["Y"] (REWRITE_RULE[SKOLEM_THM] th);;

let Y_CLAUSES = prove
 (`(!a. Y a 0 = 0) /\
   (!a. Y a 1 = 1) /\
   (!a n. Y a (n + 2) = 2 * a * Y a (n + 1) - Y a (n))`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [Y_DEF] THEN
  REWRITE_TAC[ARITH_EQ; ADD_EQ_0; ARITH_RULE `~(n + 2 = 1)`] THEN
  REWRITE_TAC[ARITH_RULE `((n + 2) - 2 = n) /\ ((n + 2) - 1 = n + 1)`]);;

(* ------------------------------------------------------------------------- *)
(* An obvious but tiresome lemma: the Xs and Ys increase.                    *)
(* ------------------------------------------------------------------------- *)

let X_INCREASES = prove
 (`!a n. ~(a = 0) ==> X a n <= X a (n + 1)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[X_CLAUSES; ADD_CLAUSES;
    ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
  GEN_REWRITE_TAC RAND_CONV [X_DEF] THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ;
    ARITH_RULE `(n + 1 = 1) <=> (n = 0)`] THEN
  REWRITE_TAC[ADD_SUB] THEN
  MATCH_MP_TAC(ARITH_RULE `a + b <= c ==> a <= c - b:num`) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * X a n` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_EQ] THEN
    UNDISCH_TAC `~(a = 0)` THEN SPEC_TAC(`a:num`,`a:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `a <= b + a:num`]] THEN
  MATCH_MP_TAC(ARITH_RULE `b <= a ==> a + b <= 2 * a`) THEN
  SUBGOAL_THEN `n = (n - 1) + 1` SUBST1_TAC THENL
   [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `((n + 1) + 1) - 2 = n`] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC);;

let Y_INCREASES = prove
 (`!a n. ~(a = 0) ==> Y a n <= Y a (n + 1)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[Y_CLAUSES; ADD_CLAUSES; LE_0] THEN
  GEN_REWRITE_TAC RAND_CONV [Y_DEF] THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH_EQ;
    ARITH_RULE `(n + 1 = 1) <=> (n = 0)`] THEN
  REWRITE_TAC[ADD_SUB] THEN
  MATCH_MP_TAC(ARITH_RULE `a + b <= c ==> a <= c - b:num`) THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 * Y a n` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL; ARITH_EQ] THEN
    UNDISCH_TAC `~(a = 0)` THEN SPEC_TAC(`a:num`,`a:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `a <= b + a:num`]] THEN
  MATCH_MP_TAC(ARITH_RULE `b <= a ==> a + b <= 2 * a`) THEN
  SUBGOAL_THEN `n = (n - 1) + 1` SUBST1_TAC THENL
   [UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `((n + 1) + 1) - 2 = n`] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Show that the expression is a power of the basis.                         *)
(* ------------------------------------------------------------------------- *)

let XY_POWER_POS = prove
 (`!a n. ~(a = 0) ==> (&(X a n) + &(Y a n) * sqrt(&a pow 2 - &1) =
                       (&a + sqrt(&a pow 2 - &1)) pow n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[X_DEF; Y_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; real_pow] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN
   `(&(2 * a * X a (n - 1) - X a (n - 2)) =
     &(2 * a * X a (n - 1)) - &(X a (n - 2))) /\
    (&(2 * a * Y a (n - 1) - Y a (n - 2)) =
     &(2 * a * Y a (n - 1)) - &(Y a (n - 2)))`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    MATCH_MP_TAC(ARITH_RULE
     `x <= y /\ y <= 2 * a * y ==> x <= 2 * a * y`) THEN
    ASM_SIMP_TAC[ARITH_RULE
     `~(n = 0) /\ ~(n = 1) ==> (n - 1 = (n - 2) + 1)`] THEN
    ASM_SIMP_TAC[X_INCREASES; Y_INCREASES] THEN
    REWRITE_TAC[MULT_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(x1 - x2) + (y1 - y2) * a = (x1 + y1 * a) - (x2 + y2 * a)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_ADD_LDISTRIB] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `~(n = 0) /\ ~(n = 1) ==> n - 2 < n /\ n - 1 < n`] THEN
  ASM_SIMP_TAC[ARITH_RULE
     `~(n = 0) /\ ~(n = 1) ==> (n - 1 = 1 + (n - 2))`] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC; REAL_POW_1] THEN
  REWRITE_TAC[REAL_ARITH `a * b - b = (a - &1) * b`] THEN
  SUBGOAL_THEN `n = 2 + (n - 2)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL
   [MAP_EVERY UNDISCH_TAC [`~(n = 0)`; `~(n = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_2; REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_SUB_LE;
               REAL_POW_LE_1; REAL_OF_NUM_LE;
               ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let XY_POWER_NEG = prove
 (`!a n. ~(a = 0) ==> (&(X a n) - &(Y a n) * sqrt(&a pow 2 - &1) =
                       (&a - sqrt(&a pow 2 - &1)) pow n)`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[X_DEF; Y_DEF] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO; real_pow] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN
   `(&(2 * a * X a (n - 1) - X a (n - 2)) =
     &(2 * a * X a (n - 1)) - &(X a (n - 2))) /\
    (&(2 * a * Y a (n - 1) - Y a (n - 2)) =
     &(2 * a * Y a (n - 1)) - &(Y a (n - 2)))`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL
   [CONJ_TAC THEN MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN
    MATCH_MP_TAC(ARITH_RULE
     `x <= y /\ y <= 2 * a * y ==> x <= 2 * a * y`) THEN
    ASM_SIMP_TAC[ARITH_RULE
     `~(n = 0) /\ ~(n = 1) ==> (n - 1 = (n - 2) + 1)`] THEN
    ASM_SIMP_TAC[X_INCREASES; Y_INCREASES] THEN
    REWRITE_TAC[MULT_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `(x1 - x2) - (y1 - y2) * a = (x1 - y1 * a) - (x2 - y2 * a)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[ARITH_RULE
   `~(n = 0) /\ ~(n = 1) ==> n - 2 < n /\ n - 1 < n`] THEN
  ASM_SIMP_TAC[ARITH_RULE
     `~(n = 0) /\ ~(n = 1) ==> (n - 1 = 1 + (n - 2))`] THEN
  REWRITE_TAC[REAL_POW_ADD; REAL_MUL_ASSOC; REAL_POW_1] THEN
  REWRITE_TAC[REAL_ARITH `a * b - b = (a - &1) * b`] THEN
  SUBGOAL_THEN `n = 2 + (n - 2)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th])
  THENL
   [MAP_EVERY UNDISCH_TAC [`~(n = 0)`; `~(n = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_POW_2; REAL_SUB_LDISTRIB; REAL_SUB_RDISTRIB] THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_SUB_LE;
               REAL_POW_LE_1; REAL_OF_NUM_LE;
               ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence all members of recurrence relations are Pell solutions.             *)
(* ------------------------------------------------------------------------- *)

let XY_ARE_SOLUTIONS = prove
 (`!a n. ~(a = 0)
         ==> ((X a n) EXP 2 = (a EXP 2 - 1) * (Y a n) EXP 2 + 1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP XY_POWER_NEG) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP XY_POWER_POS) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(fun th ->
   MP_TAC(MK_COMB(AP_TERM `( * )` (CONJUNCT1 th),CONJUNCT2 th))) THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ARITH `(x + y) * (x - y) = x * x - y * y`] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
    `(a * b) * (c * d) = (a * c) * (b * d)`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_SUB_LE;
               REAL_POW_LE_1; REAL_OF_NUM_LE;
               ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
  REWRITE_TAC[REAL_ARITH `a - (a - &1) = &1`; REAL_POW_ONE] THEN
  REWRITE_TAC[REAL_EQ_SUB_RADD] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `1 <= a <=> ~(a = 0)`];
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_EQ;
                REAL_OF_NUM_POW] THEN
    REWRITE_TAC[MULT_AC; ADD_AC]]);;

(* ------------------------------------------------------------------------- *)
(* And they are all solutions.                                               *)
(* ------------------------------------------------------------------------- *)

let X_DEGENERATE = prove
 (`!n. X 1 n = 1`,
  MATCH_MP_TAC PELL_INDUCTION THEN SIMP_TAC[X_CLAUSES; ARITH]);;

let Y_DEGENERATE = prove
 (`!n. Y 1 n = n`,
  MATCH_MP_TAC PELL_INDUCTION THEN SIMP_TAC[Y_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ARITH_TAC);;

let REAL_ARCH_POW = prove
 (`!x y. &1 < x /\ &1 < y
         ==> ?n. x pow n <= y /\ y < x pow (SUC n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `ln(x)` REAL_ARCH_LEAST) THEN ASM_SIMP_TAC[LN_POS_LT] THEN
  DISCH_THEN(MP_TAC o SPEC `ln(y)`) THEN
  ASM_SIMP_TAC[LN_POS_LT; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[GSYM LN_POW; REAL_ARITH `&1 < x ==> &0 < x`;
               REAL_POW_LT; LN_MONO_LT; LN_MONO_LE]);;

let SOLUTIONS_INDUCTION = prove
 (`!a x y.
        ~(a = 0) /\ ~(a = 1) /\ ~(y = 0) /\
        (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1)
        ==> ?x' y'. x' < x /\ y' < y /\
                    (x' EXP 2 = (a EXP 2 - 1) * y' EXP 2 + 1) /\
                    (&x + &y * sqrt(&a pow 2 - &1) =
                     (&x' + &y' * sqrt(&a pow 2 - &1)) *
                     (&a + sqrt(&a pow 2 - &1)))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `a * x - (a EXP 2 - 1) * y` THEN
  EXISTS_TAC `a * y - x:num` THEN
  SUBGOAL_THEN `x <= a * y:num` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(SPECL [`x:num`; `y:num`; `1`] EXP_MONO_LE_SUC)] THEN
    ASM_REWRITE_TAC[ARITH_SUC] THEN
    REWRITE_TAC[GSYM ADD1; LE_SUC_LT] THEN
    REWRITE_TAC[MULT_EXP; LT_MULT_RCANCEL] THEN
    REWRITE_TAC[ARITH_RULE `a - 1 < a <=> ~(a = 0)`] THEN
    ASM_REWRITE_TAC[EXP_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `(a EXP 2 - 1) * y <= a * x:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `(a EXP 2 - 1) * y EXP 2 < a * x * y` MP_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[MULT_ASSOC; EXP_2; LT_MULT_RCANCEL; LT_IMP_LE]] THEN
    REWRITE_TAC[GSYM LE_SUC_LT; ADD1] THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    REWRITE_TAC[EXP_2; GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `d /\ (d ==> a /\ b /\ c)
                     ==> a /\ b /\ c /\ d`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
    EXISTS_TAC `&a - sqrt(&a pow 2 - &1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_0] THEN
      DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow)`) THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_SUB_LE; REAL_POW_LE_1; REAL_OF_NUM_LE;
                   ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) * (a - b) = a * a - b * b`] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
                 REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
    REWRITE_TAC[REAL_ARITH `a - (a - b) = b`; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[REAL_ARITH
     `(x + y * s) * (a - s) = (a * x - (s * s) * y) + (a * y - x) * s`] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
                 REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  SUBGOAL_THEN
   `(&x - &y * sqrt(&a pow 2 - &1)) =
    (&(a * x - (a EXP 2 - 1) * y) - &(a * y - x) * sqrt (&a pow 2 - &1)) *
    (&a - sqrt(&a pow 2 - &1))`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN
    EXISTS_TAC `&a + sqrt(&a pow 2 - &1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `~(a = --b) ==> ~(a + b = &0)`) THEN
      DISCH_THEN(MP_TAC o C AP_THM `2` o AP_TERM `(pow)`) THEN
      REWRITE_TAC[REAL_POW_NEG; ARITH] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_SUB_LE; REAL_POW_LE_1; REAL_OF_NUM_LE;
                   ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ARITH `(a - b) * (a + b) = a * a - b * b`] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
                 REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
    REWRITE_TAC[REAL_ARITH `a - (a - b) = b`; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[REAL_ARITH
     `(x - y * s) * (a + s) = (a * x - (s * s) * y) - (a * y - x) * s`] THEN
    ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
                 REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  DISCH_THEN(fun th1 -> DISCH_THEN (fun th2 ->
   MP_TAC(MK_COMB(AP_TERM `( * )` th1,th2)))) THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `(a * b) * (c * d) = (c * a) * (d * b)`] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) * (a - b) = a * a - b * b`] THEN
  REWRITE_TAC[REAL_ARITH `(a - b) * (a + b) = a * a - b * b`] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC
   `(a * b) * (c * b) = (c * a) * (b * b)`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
               REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
  REWRITE_TAC[REAL_ARITH `a - (a - b) = b`; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_POW] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `((a * b + &1) - b * a = x - y) ==> (x = y + &1)`)) THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_SUB; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ;
               REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
  ABBREV_TAC `u = a * x - (a EXP 2 - 1) * y` THEN
  ABBREV_TAC `v = a * y - x:num` THEN
  DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[MULT_SYM]) THEN
  REWRITE_TAC[MULT_AC] THEN
  MATCH_MP_TAC(TAUT `(a <=> b) /\ (~a /\ ~b ==> F) ==> a /\ b`) THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `1` EXP_MONO_LT_SUC)] THEN
    ASM_REWRITE_TAC[ARITH_SUC] THEN
    REWRITE_TAC[LT_ADD_RCANCEL; LT_MULT_LCANCEL] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT_SUC] THEN
    MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN
    REWRITE_TAC[SUB_EQ_0; ARITH_SUC; NOT_LE] THEN
    SUBST1_TAC(SYM(SPEC `a:num` (CONJUNCT1 EXP))) THEN
    REWRITE_TAC[LT_EXP] THEN REWRITE_TAC[ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `~(a = 0) /\ ~(a = 1) ==> 2 <= a`) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NOT_LT] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `&x + &y * sqrt (&a pow 2 - &1) =
    (&u + &v * sqrt (&a pow 2 - &1)) * (&a + sqrt (&a pow 2 - &1))` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a < b ==> ~(a = b)`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&u + &v * sqrt (&a pow 2 - &1)) * &1` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; SQRT_POS_LE; REAL_POW_LE_1;
                 REAL_SUB_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `0 EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1` THEN
      DISCH_THEN(MP_TAC o SYM) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LE; SQRT_POS_LE; REAL_POW_LE_1;
                 REAL_SUB_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&1 < x /\ &0 <= y ==> &1 < x + y`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; SQRT_POS_LE; REAL_POW_LE_1;
               REAL_SUB_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN
  MATCH_MP_TAC(ARITH_RULE `~(a = 0) /\ ~(a = 1) ==> 1 < a`) THEN
  ASM_REWRITE_TAC[]);;

let SOLUTIONS_ARE_XY = prove
 (`!a x y.
    ~(a = 0) /\
    (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1)
    ==> ?n. (x = X a n) /\ (y = Y a n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; ADD_CLAUSES; EXP_2] THEN
    SIMP_TAC[MULT_EQ_1; X_DEGENERATE; Y_DEGENERATE; GSYM EXISTS_REFL];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?n. &x + &y * sqrt(&a pow 2 - &1) =
                    (&a + sqrt(&a pow 2 - &1)) pow n`
  MP_TAC THENL
   [UNDISCH_TAC `x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1` THEN
    SPEC_TAC(`x:num`,`x:num`) THEN SPEC_TAC(`y:num`,`y:num`) THEN
    MATCH_MP_TAC num_WF THEN X_GEN_TAC `y0:num` THEN DISCH_TAC THEN
    X_GEN_TAC `x0:num` THEN
    ASM_CASES_TAC `y0 = 0` THENL
     [ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES; MULT_EQ_1] THEN
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `0` THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; real_pow]; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`a:num`; `x0:num`; `y0:num`] SOLUTIONS_INDUCTION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_THEN `y1:num`
        STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y1:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x1:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` SUBST1_TAC) THEN
    EXISTS_TAC `SUC n` THEN REWRITE_TAC[real_pow; REAL_MUL_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM XY_POWER_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN
  ASM_SIMP_TAC[SQRT_LINEAR_EQ;
               ARITH_RULE `~(a = 0) /\ ~(a = 1) ==> 2 <= a`]);;

(* ------------------------------------------------------------------------- *)
(* Addition formulas.                                                        *)
(* ------------------------------------------------------------------------- *)

let ADDITION_FORMULA_POS = prove
 (`!a m n.
     ~(a = 0)
     ==> ((X a (m + n) = X a m * X a n + (a EXP 2 - 1) * Y a m * Y a n) /\
          (Y a (m + n) = X a m * Y a n + X a n * Y a m))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC[X_DEGENERATE; Y_DEGENERATE] THEN
    REWRITE_TAC[ARITH; MULT_CLAUSES] THEN REWRITE_TAC[ADD_AC]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `m + n:num`] XY_POWER_POS) THEN
  MP_TAC(SPECL [`a:num`; `m:num`] XY_POWER_POS) THEN
  MP_TAC(SPECL [`a:num`; `n:num`] XY_POWER_POS) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_POW_ADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   `(a + b * s) * (c + d * s) = (a  * c + (s * s) * b * d) +
                                (a * d + b * c) * s`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
               REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_LINEAR_EQ;
               ARITH_RULE `~(a = 0) /\ ~(a = 1) ==> 2 <= a`] THEN
  REWRITE_TAC[MULT_AC]);;

let ADDITION_FORMULA_NEG = prove
 (`!a m n.
     ~(a = 0) /\ m <= n
     ==> ((X a (n - m) = X a m * X a n - (a EXP 2 - 1) * Y a m * Y a n) /\
          (Y a (n - m) = X a m * Y a n - X a n * Y a m))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC[X_DEGENERATE; Y_DEGENERATE] THEN
    REWRITE_TAC[ARITH; MULT_CLAUSES]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `n - m:num`] XY_POWER_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM
   `( * ) (((&a - sqrt (&a pow 2 - &1)) *
            (&a + sqrt (&a pow 2 - &1))) pow m)`) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)
   [REAL_ARITH `(x - y) * (x + y) = x * x - y * y`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_SUB_LE;
               REAL_POW_LE_1; REAL_OF_NUM_LE;
               ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
  REWRITE_TAC[REAL_ARITH `x - (x - &1) = &1`] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW_ONE; REAL_MUL_LID] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM REAL_POW_ADD] THEN
  ASM_SIMP_TAC[ARITH_RULE `m <= n ==> (m + (n - m) = n:num)`] THEN
  MP_TAC(SPECL [`a:num`; `m:num`] XY_POWER_NEG) THEN
  MP_TAC(SPECL [`a:num`; `n:num`] XY_POWER_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_ARITH
   `(a - b * s) * (c + d * s) = (a * c - (s * s) * b * d) +
                                (a * d - b * c) * s`] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2;  REAL_SUB_LE; REAL_POW_LE_1;
               REAL_OF_NUM_LE; ARITH_RULE `~(a = 0) ==> 1 <= a`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(a + b * s = (x1 - x2) + (y1 - y2) * s) =
    ((a + x2) + (b + y2) * s = x1 + y1 * s)`] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_LINEAR_EQ;
               ARITH_RULE `~(a = 0) /\ ~(a = 1) ==> 2 <= a`] THEN
  DISCH_THEN(CONJUNCTS_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_SUB]);;

(* ------------------------------------------------------------------------- *)
(* Some stronger monotonicity theorems for Y.                                *)
(* ------------------------------------------------------------------------- *)

let Y_INCREASES_SUC = prove
 (`!a n. ~(a = 0) ==> Y a n < Y a (SUC n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ADD1; ADDITION_FORMULA_POS] THEN
  REWRITE_TAC[X_CLAUSES; Y_CLAUSES] THEN
  MATCH_MP_TAC(ARITH_RULE `1 * y <= ay /\ ~(x = 0) ==> y < x * 1 + ay`) THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
  MATCH_MP_TAC(ARITH_RULE
    `!n. (n = 1) /\ n <= m ==> ~(m = 0)`) THEN
  EXISTS_TAC `X a 0` THEN CONJ_TAC THENL
   [REWRITE_TAC[X_CLAUSES]; ALL_TAC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[ADD1] THEN ASM_MESON_TAC[LE_TRANS; X_INCREASES]);;

let Y_INCREASES_LT = prove
 (`!a m n. ~(a = 0) /\ m < n ==> Y a m < Y a n`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [LT_EXISTS] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `Y a (SUC m)` THEN
  ASM_SIMP_TAC[Y_INCREASES_SUC] THEN
  REWRITE_TAC[ARITH_RULE `m + SUC d = SUC m + d`] THEN
  SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
  ASM_MESON_TAC[ADD1; LE_TRANS; Y_INCREASES]);;

let Y_INCREASES_LE = prove
 (`!a m n. ~(a = 0) /\ m <= n ==> Y a m <= Y a n`,
  REWRITE_TAC[LE_LT] THEN MESON_TAC[LE_REFL; Y_INCREASES_LT]);;

let Y_INJ = prove
 (`!a m n. ~(a = 0) ==> ((Y a m = Y a n) <=> (m = n))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(SPEC `a:num` Y_INCREASES_LT) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[LT_CASES; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* One for X (to get the same as Y, need a /= 1).                            *)
(* ------------------------------------------------------------------------- *)

let X_INCREASES_LE = prove
 (`!a m n. ~(a = 0) /\ m <= n ==> X a m <= X a n`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `d:num` THEN
  DISCH_THEN(K ALL_TAC) THEN SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[ADD1] THEN ASM_MESON_TAC[LE_TRANS; X_INCREASES]);;

let X_INCREASES_LT = prove
 (`!a m n. ~(a = 0) /\ ~(a = 1) /\ m < n ==> X a m < X a n`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM LE_SUC_LT] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `X a (SUC m)` THEN
  ASM_SIMP_TAC[X_INCREASES_LE] THEN
  SPEC_TAC(`m:num`,`p:num`) THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[ARITH; X_CLAUSES; ARITH_RULE
   `~(a = 0) /\ ~(a = 1) ==> 1 < a`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC p) = p + 2`] THEN
  REWRITE_TAC[X_CLAUSES; ADD1] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b /\ c < b ==> a < 2 * b - c`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `X a (SUC p)` THEN
    ASM_REWRITE_TAC[]] THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
  REWRITE_TAC[LE_MULT_RCANCEL; ADD1] THEN DISJ1_TAC THEN
  MAP_EVERY UNDISCH_TAC [`~(a = 0)`; `~(a = 1)`] THEN ARITH_TAC);;

let X_INCREASES_SUC = prove
 (`!a n. ~(a = 0) /\ ~(a = 1) ==> X a n < X a (SUC n)`,
  SIMP_TAC[X_INCREASES_LT; LT]);;

let X_INJ = prove
 (`!a m n. ~(a = 0) /\ ~(a = 1) ==> ((X a m = X a n) <=> (m = n))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  MP_TAC(SPEC `a:num` X_INCREASES_LT) THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[LT_CASES; LT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Coprimality of "X a n" and "Y a n".                                       *)
(* ------------------------------------------------------------------------- *)

let XY_COPRIME = prove
 (`!a n. ~(a = 0) ==> coprime(X a n,Y a n)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP XY_ARE_SOLUTIONS) THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
  REWRITE_TAC[coprime; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[divides] THEN STRIP_TAC THEN ASM_REWRITE_TAC[EXP_2] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  GEN_REWRITE_TAC (funpow 2 RAND_CONV o LAND_CONV)
   [AC MULT_AC `a * d * x * d * x = d * d * a * x * x:num`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(a = b + 1) ==> (a - b = 1)`)) THEN
  ASM_REWRITE_TAC[GSYM LEFT_SUB_DISTRIB; MULT_EQ_1]);;

(* ------------------------------------------------------------------------- *)
(* Divisibility properties.                                                  *)
(* ------------------------------------------------------------------------- *)

let Y_DIVIDES_LEMMA = prove
 (`!a k n. ~(a = 0) ==> (Y a n) divides (Y a (n * k))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
  REWRITE_TAC[Y_CLAUSES; DIVIDES_0] THEN
  ASM_SIMP_TAC[ADDITION_FORMULA_POS] THEN
  UNDISCH_TAC `Y a n divides Y a (n * k)` THEN
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num` THEN DISCH_TAC THEN
  EXISTS_TAC `X a n * d + X a (n * k)` THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN REWRITE_TAC[MULT_AC; ADD_AC]);;

let Y_DIVIDES = prove
 (`!a m n. ~(a = 0) ==> ((Y a m) divides (Y a n) <=> m divides n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [divides] THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; Y_DIVIDES_LEMMA]] THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[Y_CLAUSES; DIVIDES_ZERO] THEN
    MATCH_MP_TAC(ARITH_RULE
      `!n. (n = 1) /\ n <= m ==> ~(m = 0)`) THEN
    EXISTS_TAC `Y a 1` THEN CONJ_TAC THENL
     [REWRITE_TAC[Y_CLAUSES]; ALL_TAC] THEN
    ASM_SIMP_TAC[Y_INCREASES_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `m:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = n DIV m` THEN ABBREV_TAC `r = n MOD m` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 0` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; DIVIDES_LMUL; DIVIDES_REFL] THEN
  DISCH_TAC THEN
  ASM_SIMP_TAC[ADDITION_FORMULA_POS] THEN
  SUBGOAL_THEN `~((Y a m) divides (X a (q * m) * Y a r))` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN DISCH_TAC THEN
    MATCH_MP_TAC DIVIDES_ADD_REVL THEN
    EXISTS_TAC `X a r * Y a (q * m)` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [MULT_SYM] THEN
    ASM_SIMP_TAC[DIVIDES_LMUL; Y_DIVIDES_LEMMA]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] COPRIME_DIVPROD)) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`a:num`; `q * m:num`] XY_COPRIME) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
    REWRITE_TAC[coprime; NOT_FORALL_THM; NOT_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_MESON_TAC[DIVIDES_TRANS; Y_DIVIDES_LEMMA]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; NOT_LE; Y_INCREASES_LT] THEN
  ONCE_REWRITE_TAC[GSYM(CONJUNCT1 Y_CLAUSES)] THEN ASM_SIMP_TAC[Y_INJ]);;

(* ------------------------------------------------------------------------- *)
(* This lemma would be trivial from binomial theorem.                        *)
(* ------------------------------------------------------------------------- *)

let BINOMIAL_TRIVIALITY = prove
 (`!x y d n. ?p q.
      (&x + &y * sqrt(&d)) pow (n + 2) =
      &x pow (n + 2) +
      &(n + 2) * &x pow (n + 1) * &y * sqrt(&d) +
      &(((n + 1) * (n + 2)) DIV 2) * &x pow n * &y pow 2 * &d +
      &p * &y pow 3 + &q * &y pow 3 * sqrt(&d)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REPEAT(EXISTS_TAC `0`) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_1; real_pow; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN REWRITE_TAC[REAL_POW_2] THEN
    REWRITE_TAC[REAL_ARITH
      `(x + y) * (x + y) = x * x + &2 * x * y + y * y`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[AC REAL_MUL_AC `(a * b) * (a * b) = (a * a) * b * b`] THEN
    SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_POS]; ALL_TAC] THEN
  GEN_REWRITE_TAC (funpow 2 BINDER_CONV o LAND_CONV o TOP_DEPTH_CONV)
    [ADD_CLAUSES; real_pow] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num` SUBST1_TAC)) THEN
  REWRITE_TAC[REAL_ARITH
   `(x + y) * (xn + xn1 + xn2 + p + q) =
    (x * xn) + (x * xn1 + y * xn) + (x * xn2 + y * xn1) +
    (y * xn2 + p * x + q * y) + (p * y + q * x)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x * n2 * xn1 * y * d + (y * d) * xn2 = (n2 * x * xn1 + xn2)  * y * d`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  REWRITE_TAC[ARITH_RULE `SUC(n + m) = n + SUC m`] THEN
  REWRITE_TAC[ARITH_RULE `SUC n + m = n + SUC m`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[REAL_ARITH `&n * x + x = (&n + &1) * x`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; ARITH_RULE `(n + 2) + 1 = n + 3`] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; GSYM REAL_MUL_ASSOC; REAL_EQ_LADD] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x * n12 * xn * y2 * d + y * s * n2 * xn1 * y * s + a =
    (n12 * (x * xn) * y2 * d + n2 * xn1 * (y * y) * (s * s)) + a`] THEN
  REWRITE_TAC[GSYM REAL_POW_2; GSYM(CONJUNCT2 real_pow)] THEN
  SIMP_TAC[SQRT_POW_2; REAL_POS] THEN
  REWRITE_TAC[ADD1; REAL_MUL_ASSOC; GSYM REAL_ADD_RDISTRIB] THEN
  SUBGOAL_THEN `&(((n + 1) * (n + 2)) DIV 2) + &(n + 2) =
                &(((n + 2) * (n + 3)) DIV 2)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIV_UNIQ THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ARITH; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `(n + 2) * (n + 3) = n * n + 5 * n + 6`] THEN
    REWRITE_TAC[ARITH_RULE
     `(x + 5 * n + 6 = (y + n + 2) * 2) <=> (x + 3 * n + 2 = 2 * y)`] THEN
    REWRITE_TAC[ARITH_RULE `n * n + 3 * n + 2 = (n + 1) * (n + 2)`] THEN
    SUBGOAL_THEN `EVEN((n + 1) * (n + 2))` MP_TAC THENL
     [REWRITE_TAC[EVEN_MULT; EVEN_ADD; ARITH_EVEN] THEN
      CONV_TAC(EQT_INTRO o TAUT); ALL_TAC] THEN
    SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    SIMP_TAC[DIV_MULT; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EQ_LADD] THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `q * y3 * s * y * s = q * y * y3 * s * s`] THEN
  SIMP_TAC[GSYM REAL_POW_2; SQRT_POW_2; REAL_POS] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `y * s * nn * xn * y2 * d = nn * d * xn * (y * y2) * s`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  EXISTS_TAC `p * x + q * y * d:num` THEN REWRITE_TAC[ARITH_SUC] THEN
  EXISTS_TAC `((n + 1) * (n + 2)) DIV 2 * d * x EXP n +
              p * y + q * x` THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[REAL_MUL_AC] THEN REWRITE_TAC[REAL_ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* A lower bound theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let Y_LOWERBOUND = prove
 (`!a n. (2 * a - 1) EXP n <= Y a (n + 1)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; ARITH; Y_CLAUSES] THEN
  ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[ARITH; MULT_CLAUSES; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `SUC n + 1 = n + 2`; Y_CLAUSES] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 * a - 1) * Y a (n + 1)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB; MULT_CLAUSES; GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> c - b <= c - a:num`) THEN
  ASM_SIMP_TAC[Y_INCREASES]);;

let Y_UPPERBOUND = prove
 (`!a n. Y a (n + 1) <= (2 * a) EXP n`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; ADD_CLAUSES; Y_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE `SUC(n + 1) = n + 2`; Y_CLAUSES] THEN
  MATCH_MP_TAC(ARITH_RULE `a <= b ==> a - c <= b:num`) THEN
  ASM_REWRITE_TAC[MULT_ASSOC; LE_MULT_LCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Now a key congruence.                                                     *)
(* ------------------------------------------------------------------------- *)

let XY_Y3_CONGRUENCE = prove
 (`!a n k. ~(a = 0)
           ==> ?q. Y a (n * k) =
                   k * (X a n) EXP (k - 1) * Y a n + q * (Y a n) EXP 3`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[Y_CLAUSES; MULT_CLAUSES; ADD_CLAUSES; SUB_0]; ALL_TAC] THEN
  ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC[X_DEGENERATE; Y_DEGENERATE; EXP_ONE] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  ASM_CASES_TAC `k = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; SUB_REFL; EXP] THEN
    EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `n * k:num`] XY_POWER_POS) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN
  MP_TAC(SPECL [`a:num`; `n:num`] XY_POWER_POS) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_POW_POW] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `2 <= k` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`~(k = 0)`; `~(k = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num`
    (SUBST1_TAC o ONCE_REWRITE_RULE[ADD_SYM])) THEN
  MP_TAC(SPECL [`X a n`; `Y a n`; `a EXP 2 - 1`; `d:num`]
               BINOMIAL_TRIVIALITY) THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `q:num` SUBST1_TAC)) THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x1 + y1 + x2 + x3 + y2 = (x1 + x2 + x3) + (y1 + y2)`] THEN
  REWRITE_TAC[REAL_MUL_ASSOC; GSYM REAL_ADD_RDISTRIB] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&a pow 2 - &1 = &(a EXP 2 - 1)` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC[REAL_OF_NUM_POW] THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
    ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE;
                 ARITH_RULE `~(a = 0) ==> 1 <= a`]; ALL_TAC] THEN
  ASM_SIMP_TAC[SQRT_LINEAR_EQ;
               ARITH_RULE `~(p = 0) /\ ~(p = 1) ==> 2 <= p`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[ARITH_RULE `(d + 2) - 1 = d + 1`] THEN
  EXISTS_TAC `q:num` THEN REWRITE_TAC[GSYM MULT_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The other key divisibility result.                                        *)
(* ------------------------------------------------------------------------- *)

let Y2_DIVIDES = prove
 (`!a m n. ~(a = 0)
           ==> (((Y a m) EXP 2) divides (Y a n) <=> (m * Y a m) divides n)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[Y_CLAUSES; MULT_CLAUSES; DIVIDES_ZERO; EXP_2] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 Y_CLAUSES)] THEN
    ASM_SIMP_TAC[Y_INJ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Y a m = 0)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM(CONJUNCT1 Y_CLAUSES)] THEN
    ASM_SIMP_TAC[Y_INJ]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT
   `!c. (a ==> c) /\ (b ==> c) /\ (c ==> (a <=> b)) ==> (a <=> b)`) THEN
  EXISTS_TAC `m divides n` THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(Y a m) divides (Y a n)` MP_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[Y_DIVIDES]] THEN
    UNDISCH_TAC `((Y a m) EXP 2) divides (Y a n)` THEN
    REWRITE_TAC[divides; EXP_2; GSYM MULT_ASSOC] THEN MESON_TAC[];
    REWRITE_TAC[divides; GSYM MULT_ASSOC] THEN MESON_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC) THEN
  MP_TAC(SPECL [`a:num`; `m:num`; `k:num`] XY_Y3_CONGRUENCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST1_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `((Y a m) EXP 2) divides (k * (X a m) EXP (k - 1) * Y a m)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[num_CONV `3`; EXP] THEN
    MESON_TAC[DIVIDES_ADD; DIVIDES_ADD_REVL; DIVIDES_LMUL; DIVIDES_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[MULT_ASSOC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[EXP_2; GSYM MULT_ASSOC] THEN
  ASM_SIMP_TAC[DIVIDES_LMUL2_EQ] THEN
  EQ_TAC THEN SIMP_TAC[DIVIDES_RMUL] THEN
  DISCH_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
  EXISTS_TAC `X a m EXP (k - 1)` THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COPRIME_EXP THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[XY_COPRIME]);;

(* ------------------------------------------------------------------------- *)
(* Some more congruences.                                                    *)
(* ------------------------------------------------------------------------- *)

let Y_N_MOD2 = prove
 (`!a n. ~(a = 0) ==> ?q. Y a n = 2 * q + n`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC[Y_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q1:num`; `q2:num`] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP Y_INCREASES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `2 * q1 + n <= 2 * q2 + n + 1 <=> q1 <= q2`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(2 * a * q2 - q1) + (a - 1) * (n + 1)` THEN
  MATCH_MP_TAC(ARITH_RULE
    `v <= u /\ y <= x /\ (2 * (x + z) + w + v = 2 * y + u)
     ==> (u - v = 2 * ((x - y) + z) + w)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x <= u /\ y <= v ==> 2 * x + y <= 2 * u + v + w`) THEN
    REWRITE_TAC[MULT_ASSOC] THEN CONJ_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC] THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC;
    REWRITE_TAC[MULT_ASSOC] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC;
    UNDISCH_TAC `~(a = 0)` THEN SPEC_TAC(`a:num`,`a:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    REWRITE_TAC[ARITH_RULE `SUC a - 1 = a`] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ARITH_TAC]);;

let Y_N_MODA1 = prove
 (`!a n. ~(a = 0) ==> ?q. Y a n = q * (a - 1) + n`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC[SUB_REFL; Y_DEGENERATE; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC[Y_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q1:num`; `q2:num`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP Y_INCREASES) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `q1 + n <= q2 + n + 1 <=> q1 <= q2 + 1`] THEN
  ASM_CASES_TAC `q2 = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[ARITH_RULE `a <= 1 <=> (a = 0) \/ (a = 1)`] THEN
    ASM_REWRITE_TAC[MULT_EQ_0; MULT_EQ_1] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(a - 1 = 0) <=> (a = 0) \/ (a = 1)`] THEN
    SIMP_TAC[ARITH_RULE `(a - 1 = 1) <=> (a = 2)`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THENL
     [EXISTS_TAC `2 * (n + 1)` THEN
      UNDISCH_TAC `~(a = 0)` THEN SPEC_TAC(`a:num`,`b:num`) THEN
      INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
      REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THEN
      REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
      MATCH_MP_TAC(ARITH_RULE `(a + c = b) ==> (b - a = c:num)`) THEN
      ARITH_TAC;
      REWRITE_TAC[MULT_ASSOC; ARITH] THEN
      REWRITE_TAC[ARITH_RULE `4 * (n + 1) - (1 + n) = 3 * (n + 1)`] THEN
      EXISTS_TAC `2 * n + 1` THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    EXISTS_TAC `2 * (n + 1) + 2 * a * q2 - q1` THEN MP_TAC th) THEN
  UNDISCH_TAC `~(a = 1)` THEN
  UNDISCH_TAC `~(a = 0)` THEN SPEC_TAC(`a:num`,`b:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  REWRITE_TAC[ARITH_RULE `(SUC n = 1) <=> (n = 0)`] THEN DISCH_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`] THEN DISCH_TAC THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; RIGHT_SUB_DISTRIB] THEN
  MATCH_MP_TAC(ARITH_RULE
    `v <= u /\ y <= x /\ (u + y = z + x + w + v)
     ==> (u - v = (z + (x - y)) + w:num)`) THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
    REWRITE_TAC[MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
    ASM_REWRITE_TAC[ARITH_RULE `q1 + n <= q2 + n + 1 <=> q1 <= q2 + 1`] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ARITH_TAC;
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q2 * b + 1` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `a + 1 <= b <=> a < b`] THEN
    ASM_SIMP_TAC[LT_MULT_RCANCEL] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
    REWRITE_TAC[MULT_ASSOC] THEN
    ASM_SIMP_TAC[LT_MULT_RCANCEL] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC;
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN ARITH_TAC]);;

let X_CONGRUENT = prove
 (`!a b c n. ~(a = 0) ==> ?q. X (a + b * c) n = X a n + q * c`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `b * c = 0` THENL
   [GEN_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  UNDISCH_TAC `~(b * c = 0)` THEN
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC[X_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    EXISTS_TAC `b:num` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q1:num`; `q2:num`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
   `2 * (x + y) * (u + v) = 2 * x * u + 2 * u * y + 2 * (x + y) * v`] THEN
  EXISTS_TAC `(2 * X a (n + 1) * b + 2 * (a + b * c) * q2) - q1` THEN
  MATCH_MP_TAC(ARITH_RULE
   `a <= x /\ b <= y + z:num /\ ((x - a) + ((y + z) - b) = u)
    ==> ((x + y + z) - (a + b) = u)`) THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB; RIGHT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 * X a (n + 1)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MULT_CLAUSES; X_INCREASES]; ALL_TAC] THEN
    REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `X (a + b * c) n` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] LE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `X (a + b * c) (n + 1)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[X_INCREASES; ADD_EQ_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = a * 1`] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(ARITH_RULE `a <= y ==> a <= 2 * (x + y)`) THEN
    ONCE_REWRITE_TAC[AC MULT_AC `a * b * c * d = (a * b) * (c * d:num)`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; ARITH_EQ]]);;

let Y_CONGRUENT = prove
 (`!a b c n. ~(a = 0) ==> ?q. Y (a + b * c) n = Y a n + q * c`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `b * c = 0` THENL
   [GEN_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  UNDISCH_TAC `~(b * c = 0)` THEN
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC PELL_INDUCTION THEN REWRITE_TAC[Y_CLAUSES] THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM;
              LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `q1:num`; `q2:num`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE
   `2 * (x + y) * (u + v) = 2 * x * u + 2 * u * y + 2 * (x + y) * v`] THEN
  EXISTS_TAC `(2 * Y a (n + 1) * b + 2 * (a + b * c) * q2) - q1` THEN
  MATCH_MP_TAC(ARITH_RULE
   `a <= x /\ b <= y + z:num /\ ((x - a) + ((y + z) - b) = u)
    ==> ((x + y + z) - (a + b) = u)`) THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB; RIGHT_ADD_DISTRIB; GSYM MULT_ASSOC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 * Y a (n + 1)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[MULT_CLAUSES; Y_INCREASES]; ALL_TAC] THEN
    REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Y (a + b * c) n` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] LE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `Y (a + b * c) (n + 1)` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[Y_INCREASES; ADD_EQ_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = a * 1`] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; ARITH_EQ];
    MATCH_MP_TAC(ARITH_RULE `a <= y ==> a <= 2 * (x + y)`) THEN
    ONCE_REWRITE_TAC[AC MULT_AC `a * b * c * d = (a * b) * (c * d:num)`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; ARITH_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* A more important congruence.                                              *)
(* ------------------------------------------------------------------------- *)

let X_CONGRUENT_2NJ_POS = prove
 (`!a n j. ~(a = 0) ==> ?q. X a (2 * n + j) + X a j = q * X a n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `n + j:num`] ADDITION_FORMULA_POS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `n + n + j = 2 * n + j`] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `j:num`] ADDITION_FORMULA_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  ONCE_REWRITE_TAC[ARITH_RULE
   `(xn * a + d * yn * (xn * yj + xj * yn)) + xj =
    xn * (a + d * yn * yj) + xj * (d * yn * yn + 1)`] THEN
  ASM_SIMP_TAC[GSYM XY_ARE_SOLUTIONS; GSYM EXP_2] THEN
  REWRITE_TAC[EXP_2; ARITH_RULE
   `xn * a + xj * xn * xn = (a + xj * xn) * xn:num`] THEN
  MESON_TAC[]);;

let X_CONGRUENT_4NJ_POS = prove
 (`!a n j. ~(a = 0) ==> ?q. X a (4 * n + j) = q * X a n + X a j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `2 * n + j`] X_CONGRUENT_2NJ_POS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `2 * n + 2 * n + j = 4 * n + j`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` MP_TAC) THEN
  DISCH_THEN(MP_TAC o C AP_THM `X a j` o AP_TERM `(+):num->num->num`) THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `j:num`] X_CONGRUENT_2NJ_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q2:num` MP_TAC) THEN
  DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(y + q2 = q1 + x) ==> x <= y ==> (y = (q1 - q2) + x:num)`)) THEN
  ASM_SIMP_TAC[X_INCREASES_LE; ARITH_RULE `j <= 4 * n + j`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
  MESON_TAC[]);;

let X_CONGRUENT_4MNJ_POS = prove
 (`!a m n j. ~(a = 0) ==> ?q. X a (4 * m * n + j) = q * X a n + X a j`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THENL
   [REPEAT GEN_TAC THEN EXISTS_TAC `0` THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  UNDISCH_TAC `!n j. ?q. X a (4 * m * n + j) = q * X a n + X a j` THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `4 * m * n + j`] X_CONGRUENT_4NJ_POS) THEN
  ASM_REWRITE_TAC[ARITH_RULE
   `4 * (m * n + n) + j = 4 * n + 4 * m * n + j`] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:num` SUBST1_TAC) THEN
  EXISTS_TAC `q2 + q1:num` THEN ARITH_TAC);;

let X_CONGRUENT_2NJ_NEG_LEMMA = prove
 (`!a n j. ~(a = 0) /\ j <= n ==> ?q. X a (2 * n - j) + X a j = q * X a n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j = n:num` THENL
   [EXISTS_TAC `2` THEN ASM_REWRITE_TAC[MULT_2; ADD_SUB]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `n - j:num`] ADDITION_FORMULA_POS) THEN
  ASM_SIMP_TAC[ARITH_RULE `j <= n ==> (n + n - j = 2 * n - j)`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `j:num`; `n:num`] ADDITION_FORMULA_NEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(X a j * X a n - (a EXP 2 - 1) * Y a j * Y a n) +
              (X a j * X a n - (a EXP 2 - 1) * Y a j * Y a n)` THEN
  REWRITE_TAC[ARITH_RULE
   `((xn * a + b) + c = (a + d) * xn) <=> (b + c = xn * d:num)`] THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
  MATCH_MP_TAC(ARITH_RULE
   `b <= a /\ e <= d /\ (e + a + c = d + b)
    ==> ((a - b) + c = d - e:num)`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN REPEAT DISJ2_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `(c = a - b) ==> 1 <= c ==> b <= a`)) THEN
    SUBST1_TAC(SYM(SPEC `a:num` (el 1 (CONJUNCTS Y_CLAUSES)))) THEN
    MATCH_MP_TAC Y_INCREASES_LE THEN
    ASM_SIMP_TAC[ARITH_RULE `j <= n ==> (1 <= n - j <=> ~(j = n))`];
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `(c = a - b) ==> 1 <= c ==> b <= a`)) THEN
    SUBST1_TAC(SYM(SPEC `a:num` (CONJUNCT1 X_CLAUSES))) THEN
    MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC[LE_0];
    REWRITE_TAC[ARITH_RULE
     `xn * a * yj * yn + a * yn * xj * yn + xj =
      xj * (a * yn * yn + 1) + a * yn * xn * yj`] THEN
    ASM_SIMP_TAC[GSYM XY_ARE_SOLUTIONS; GSYM EXP_2] THEN
    REWRITE_TAC[EXP_2; MULT_AC]]);;

let X_CONGRUENT_2NJ_NEG = prove
 (`!a n j. ~(a = 0) /\ j <= 2 * n ==> ?q. X a (2 * n - j) + X a j = q * X a n`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `j <= n:num` THEN ASM_SIMP_TAC[X_CONGRUENT_2NJ_NEG_LEMMA] THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `2 * n - j`] X_CONGRUENT_2NJ_NEG_LEMMA) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(j <= n) ==> 2 * n - j <= n`] THEN
  ASM_SIMP_TAC[ARITH_RULE `y <= x ==> (x - (x - y) = y:num)`] THEN
  SIMP_TAC[ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* The cute GCD fact given by Smorynski.                                     *)
(* ------------------------------------------------------------------------- *)

let XY_GCD_LEMMA = prove
 (`!a m n. ~(a = 0) /\ m < n
           ==> (gcd(Y a m,Y a n) = Y a (gcd(m,n)))`,
  GEN_TAC THEN ASM_CASES_TAC `a = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a = 1` THEN ASM_REWRITE_TAC[Y_DEGENERATE] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `m:num`] DIVISION) THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[Y_CLAUSES; GCD_0] THEN
  ABBREV_TAC `q = n DIV m` THEN ABBREV_TAC `r = n MOD m` THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [EXPAND_TAC "n" THEN ASM_SIMP_TAC[ADDITION_FORMULA_POS] THEN
    GEN_REWRITE_TAC LAND_CONV [GCD_SYM] THEN MATCH_MP_TAC GCD_EQ THEN
    X_GEN_TAC `d:num` THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC(TAUT
     `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
    DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `d divides (X a (q * m) * Y a r)` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `d divides (Y a (q * m))` MP_TAC THENL
       [ASM_MESON_TAC[Y_DIVIDES; DIVIDES_TRANS; DIVIDES_LMUL; DIVIDES_REFL];
        ALL_TAC] THEN
      MESON_TAC[DIVIDES_ADD; DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL;
                DIVIDES_ADD_REVL];
      ALL_TAC] THEN
    EQ_TAC THEN SIMP_TAC[DIVIDES_LMUL] THEN
    SUBGOAL_THEN `coprime(d,X a (q * m))`
     (fun th -> MESON_TAC[COPRIME_DIVPROD; th]) THEN
    SUBGOAL_THEN `d divides (Y a (q * m))` MP_TAC THENL
     [ASM_MESON_TAC[Y_DIVIDES; DIVIDES_TRANS; DIVIDES_LMUL; DIVIDES_REFL];
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:num`; `q * m:num`] XY_COPRIME) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[coprime] THEN
    X_GEN_TAC `e:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `coprime (X a (q * m),Y a (q * m))` THEN
    REWRITE_TAC[coprime] THEN DISCH_THEN(MP_TAC o SPEC `e:num`) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[DIVIDES_TRANS];
    AP_TERM_TAC THEN EXPAND_TAC "n" THEN
    GEN_REWRITE_TAC I [GSYM DIVIDES_ANTISYM] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN NUMBER_TAC]);;

let XY_GCD = prove
 (`!a m n. ~(a = 0) ==> (gcd(Y a m,Y a n) = Y a (gcd(m,n)))`,
  REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (SPECL [`m:num`; `n:num`] LT_CASES)
  THENL
   [ASM_SIMP_TAC[XY_GCD_LEMMA];
    ONCE_REWRITE_TAC[GCD_SYM] THEN ASM_SIMP_TAC[XY_GCD_LEMMA];
    ASM_REWRITE_TAC[GCD_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The "step-down" lemma.                                                    *)
(* ------------------------------------------------------------------------- *)

let STEP_DOWN_LEMMA = prove
 (`!a i j n q.
        ~(a = 0) /\ ~(a = 1) /\
        i <= j /\ j <= 2 * n /\
        (X a j = q * X a n + X a i)
        ==> (i = j) \/ ((a = 2) /\ (n = 1) /\ (i = 0) /\ (j = 2))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j <= n:num` THENL
   [ASM_CASES_TAC `i = j:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i < n:num` ASSUME_TAC THENL
     [ASM_MESON_TAC[LTE_TRANS; LT_LE]; ALL_TAC] THEN
    UNDISCH_TAC `X a j = q * X a n + X a i` THEN
    ASM_CASES_TAC `q = 0` THEN
    ASM_SIMP_TAC[ADD_CLAUSES; MULT_CLAUSES; X_INJ] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`a:num`; `j:num`; `n:num`] X_INCREASES_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= b /\ 1 * x <= qx ==> ~(qx + b <= x)`) THEN
    SIMP_TAC[LE_MULT_RCANCEL] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(x = 0) ==> 1 <= x`] THEN
    ONCE_REWRITE_TAC[GSYM(CONJUNCT1 X_CLAUSES)] THEN
    ASM_SIMP_TAC[X_INCREASES_LE; LE_0]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `i <= j:num` THEN UNDISCH_TAC `j <= 2 * n` THEN
    ASM_SIMP_TAC[LE; MULT_CLAUSES]; ALL_TAC] THEN
  ASM_CASES_TAC `i <= n:num` THENL
   [MP_TAC(SPECL [`a:num`; `n:num`; `j:num`] X_CONGRUENT_2NJ_NEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q1:num` MP_TAC) THEN
    UNDISCH_TAC `X a j = q * X a n + X a i` THEN
    ASM_CASES_TAC `q = 0` THEN
    ASM_SIMP_TAC[ADD_CLAUSES; MULT_CLAUSES; X_INJ] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(a + b + c = d:num) ==> (a + c = d - b)`)) THEN
    REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
    ASM_CASES_TAC `i = n:num` THENL
     [ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `(x + n = q * n) ==> (x = q * n - 1 * n)`)) THEN
      MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
      REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
      ASM_CASES_TAC `q1 - q - 1 = 0` THENL
       [ASM_REWRITE_TAC[MULT_CLAUSES; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
        ONCE_REWRITE_TAC[GSYM(CONJUNCT1 X_CLAUSES)] THEN
        ASM_SIMP_TAC[X_INCREASES_LE; LE_0]; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE
       `j < n /\ 1 * n <= a * n ==> ~(j = a * n)`) THEN
      ASM_SIMP_TAC[LE_MULT_RCANCEL; ARITH_RULE `~(x = 0) ==> 1 <= x`] THEN
      MATCH_MP_TAC X_INCREASES_LT THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(j <= n:num)` THEN
      UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `q1 - q = 0` THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_EQ_0] THEN
      MATCH_MP_TAC(TAUT `~c ==> a /\ c ==> b`) THEN
      REWRITE_TAC[ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
      ONCE_REWRITE_TAC[GSYM(CONJUNCT1 X_CLAUSES)] THEN
      ASM_SIMP_TAC[X_INCREASES_LE; LE_0]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~b ==> a ==> c) ==> a ==> b \/ c`) THEN
    DISCH_TAC THEN DISCH_TAC THEN
    ASM_CASES_TAC `n = 1` THENL
     [UNDISCH_TAC `j <= 2 * n` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
      UNDISCH_TAC `~(j <= n:num)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `~(j <= 1) /\ j <= 2 ==> (j = 2)`)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
      UNDISCH_THEN `n = 1` SUBST_ALL_TAC THEN
      SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`i <= 1`; `~(i = 1)`] THEN ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `X a (2 * 1 - 2) + X a 0 = (q1 - q) * X a 1` THEN
      REWRITE_TAC[ARITH; X_CLAUSES] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      MATCH_MP_TAC(ARITH_RULE
       `~(a = 0) /\ ~(a = 1) /\ a <= 2 ==> (a = 2)`) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_THEN `(q1 - q) * a = 2` (SUBST1_TAC o SYM) THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(q = 0) ==> 1 <= q`]; ALL_TAC] THEN
    UNDISCH_TAC `X a (2 * n - j) + X a i = (q1 - q) * X a n` THEN
    MATCH_MP_TAC(TAUT `~b ==> b ==> a`) THEN
    MATCH_MP_TAC(ARITH_RULE
     `s < x /\ x <= q * x ==> ~(s = q * x:num)`) THEN
    CONJ_TAC THENL
     [ALL_TAC;
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(q = 0) ==> 1 <= q`]] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `2 * X a (n - 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `a <= c /\ b <= c ==> a + b <= 2 * c`) THEN
      CONJ_TAC THEN MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~(n = 0)` THEN UNDISCH_TAC `~(j <= n:num)` THEN ARITH_TAC;
        UNDISCH_TAC `~(i = n:num)` THEN UNDISCH_TAC `i <= n:num` THEN
        ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `n - 1 = (n - 2) + 1` SUBST1_TAC THENL
     [UNDISCH_TAC `~(n = 0)` THEN UNDISCH_TAC `~(n = 1)` THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `n = (n - 2) + 2`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [UNDISCH_TAC `~(n = 0)` THEN UNDISCH_TAC `~(n = 1)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[X_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE `z < x /\ 3 * x <= y ==> 2 * x < y - z`) THEN
    ASM_SIMP_TAC[X_INCREASES_LT; ARITH_RULE `n < n + 1`] THEN
    REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
    UNDISCH_TAC `~(a = 1)` THEN UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `j:num`] X_CONGRUENT_2NJ_NEG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` MP_TAC) THEN
  MP_TAC(SPECL [`a:num`; `n:num`; `i:num`] X_CONGRUENT_2NJ_NEG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:num` MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(a = b) /\ (c = d) ==> (a + d = b + c:num)`)) THEN
  REWRITE_TAC[ARITH_RULE
    `((x + i) + q1 = q2 + y + q3 + i) <=> (x + q1 = y + q2 + q3:num)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(x + q1 = y + q2) ==> y <= x ==> (x = y + (q2 - q1:num))`)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `i <= j:num` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB; GSYM RIGHT_SUB_DISTRIB] THEN
  ASM_CASES_TAC `(q2 + q) - q1 = 0` THENL
   [ASM_SIMP_TAC[ADD_CLAUSES; MULT_CLAUSES; X_INJ] THEN
    MATCH_MP_TAC(TAUT `(a ==> b) ==> (a ==> b \/ c)`) THEN
    UNDISCH_TAC `j <= 2 * n` THEN UNDISCH_TAC `i <= j:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
  MATCH_MP_TAC(ARITH_RULE
   `1 * xi <= qxn /\ 1 <= xj ==> ~(xi = xj + qxn)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
    MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(i <= n:num)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM(CONJUNCT1 X_CLAUSES)] THEN
  MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC[LE_0]);;

let STEP_DOWN_LEMMA_4_ASYM = prove
 (`!a i j n q.
        ~(a = 0) /\ ~(a = 1) /\
        0 < i /\ i <= n /\ j < 4 * n /\
        (X a i + q * X a n = X a j)
        ==> (j = i) \/ (j = 4 * n - i)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j <= 2 * n` THENL
   [MP_TAC(SPECL [`a:num`; `i:num`; `j:num`; `n:num`; `q:num`]
       STEP_DOWN_LEMMA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `X a i + q * X a n = X a j` THEN
      SIMP_TAC[ADD_AC; MULT_AC] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
      SUBGOAL_THEN `X a i <= X a j` MP_TAC THENL
       [ASM_REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] LE_ADD]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
      ASM_SIMP_TAC[X_INCREASES_LT; NOT_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < i ==> ~(i = 0)`]; ALL_TAC] THEN
  DISJ_CASES_TAC(SPECL [`i:num`; `4 * n - j`] LE_CASES) THEN
  (MP_TAC(SPECL [`a:num`; `n:num`; `2 * n - (4 * n - j)`]
                X_CONGRUENT_2NJ_POS) THEN
   MP_TAC(SPECL [`a:num`; `n:num`; `4 * n - j`] X_CONGRUENT_2NJ_NEG) THEN
   ASM_SIMP_TAC[ARITH_RULE `~(j <= 2 * n) ==> 4 * n - j <= 2 * n`] THEN
   ASM_SIMP_TAC[ARITH_RULE
     `j < 4 * n /\ ~(j <= 2 * n)
      ==> (2 * n + 2 * n - (4 * n - j) = j)`] THEN
   DISCH_THEN(X_CHOOSE_THEN `q1:num` ASSUME_TAC) THEN
   DISCH_THEN(X_CHOOSE_THEN `q2:num` MP_TAC) THEN
   SUBST1_TAC(SYM(ASSUME `X a i + q * X a n = X a j`)) THEN
   UNDISCH_TAC
    `X a (2 * n - (4 * n - j)) + X a (4 * n - j) = q1 * X a n` THEN
   REWRITE_TAC[IMP_IMP] THEN
   DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(a + b = c) /\ (d + a = e) ==> (b + e = c + d:num)`)))
  THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(x + q1 = q2 + y + q3)
      ==> y <= x ==> (x = ((q2 + q3) - q1) + y:num)`));
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(x + q1 = q2 + y + q3)
      ==> x <= y ==> (y = (q1 - (q2 + q3)) + x:num)`))] THEN
  REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB; GSYM RIGHT_ADD_DISTRIB] THEN
  ASM_SIMP_TAC[X_INCREASES_LE] THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`a:num`; `i:num`; `4 * n - j`; `n:num`; `(q1 + q) - q2:num`]
      STEP_DOWN_LEMMA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(j <= 2 * n)` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `0 < i ==> ~(i = 0)`] THEN
    DISCH_TAC THEN DISJ2_TAC THEN UNDISCH_TAC `j < 4 * n` THEN ARITH_TAC;
    MP_TAC(SPECL [`a:num`; `4 * n - j`; `i:num`; `n:num`; `q2:num - (q1 + q)`]
      STEP_DOWN_LEMMA) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `i <= n:num` THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISJ2_TAC THEN UNDISCH_TAC `j < 4 * n` THEN ARITH_TAC]);;

let STEP_DOWN_LEMMA_4 = prove
 (`!a i j n q1 q2.
        ~(a = 0) /\ ~(a = 1) /\
        0 < i /\ i <= n /\ j < 4 * n /\
        (X a i + q1 * X a n = X a j + q2 * X a n)
        ==> (j = i) \/ (j = 4 * n - i)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j < i:num` THENL
   [UNDISCH_TAC `X a i + q1 * X a n = X a j + q2 * X a n` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
      `(x + q1 = y + q2) ==> y < x ==> (x = y + (q2 - q1:num))`)) THEN
    ASM_SIMP_TAC[X_INCREASES_LT; GSYM RIGHT_SUB_DISTRIB] THEN
    ASM_CASES_TAC `q2 - q1 = 0` THENL
     [ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; X_INJ]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(i = j + q * n) ==> 1 <= j /\ 1 * n <= q * n ==> ~(i <= n)`)) THEN
    ASM_SIMP_TAC[X_INCREASES_LE] THEN
    ASM_SIMP_TAC[LE_MULT_RCANCEL;
                 ARITH_RULE `~(q2 - q1 = 0) ==> 1 <= q2 - q1`] THEN
    ONCE_REWRITE_TAC[GSYM(CONJUNCT1 X_CLAUSES)] THEN
    ASM_SIMP_TAC[X_INCREASES_LE; LE_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `i:num`; `j:num`; `n:num`; `q1 - q2:num`]
               STEP_DOWN_LEMMA_4_ASYM) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN
  MATCH_MP_TAC(ARITH_RULE
   `(i + q1 = j + q2) /\ ~(j < i) ==> (i + q1 - q2 = j:num)`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[NOT_LT; X_INCREASES_LE]);;

let STEP_DOWN_LEMMA_STRONG_ASYM = prove
 (`!a i j n c.
        ~(a = 0) /\ ~(a = 1) /\
        0 < i /\ i <= n /\
        (X a i + c * X a n = X a j)
        ==> (?q. j = i + 4 * n * q) \/
            (?q. j + i = 4 * n * q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`j:num`; `4 * n`] DIVISION) THEN
  ABBREV_TAC `q = j DIV (4 * n)` THEN ABBREV_TAC `k = j MOD (4 * n)` THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `0 < i` THEN UNDISCH_TAC `i <= n:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  MP_TAC(SPECL [`a:num`; `q:num`; `n:num`; `k:num`] X_CONGRUENT_4MNJ_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num` MP_TAC) THEN
  SUBST1_TAC(ARITH_RULE `4 * q * n + k = q * 4 * n + k`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_CASES_TAC `k < i:num` THENL
   [UNDISCH_TAC `X a i + c * X a n = q1 * X a n + X a k` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(a + q1 = q2 + b) ==> b < a ==> (a = (q2 - q1) + b:num)`)) THEN
    ASM_SIMP_TAC[X_INCREASES_LT] THEN REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
    ASM_CASES_TAC `q1 - c = 0` THENL
     [ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; X_INJ] THEN
      DISCH_TAC THEN DISJ1_TAC THEN EXISTS_TAC `q:num` THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      REWRITE_TAC[ADD_AC; MULT_AC];
      MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
      MATCH_MP_TAC(ARITH_RULE
       `a <= b /\ 1 <= c ==> ~(a = b + c)`) THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 1 * n`] THEN
        MATCH_MP_TAC LE_MULT2 THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
        ASM_SIMP_TAC[X_INCREASES_LE; LT_IMP_LE];
        SUBST1_TAC(SYM(SPEC `a:num` (CONJUNCT1 X_CLAUSES))) THEN
        ASM_SIMP_TAC[X_INCREASES_LE; LE_0]]];
    MP_TAC(SPECL [`a:num`; `i:num`; `k:num`; `n:num`; `c - q1:num`]
                 STEP_DOWN_LEMMA_4_ASYM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `X a i + c * X a n = q1 * X a n + X a k` THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `(a + q1 = q2 + b) ==> ~(b < a) ==> (a + (q1 - q2)= b:num)`)) THEN
      REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[NOT_LT] THEN
      MATCH_MP_TAC X_INCREASES_LE THEN ASM_REWRITE_TAC[GSYM NOT_LT];
      ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `q:num` THEN
      UNDISCH_THEN `q * 4 * n + k = j` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[MULT_AC; ADD_AC];
      DISJ2_TAC THEN EXISTS_TAC `q + 1` THEN
      UNDISCH_THEN `q * 4 * n + k = j` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[GSYM ADD_ASSOC; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE
       `(a' = a) /\ i <= b ==> (a + (b - i) + i = a' + b:num)`) THEN
      REWRITE_TAC[MULT_AC] THEN
      UNDISCH_TAC `i <= n:num` THEN ARITH_TAC]]);;

let STEP_DOWN_LEMMA_STRONG = prove
 (`!a i j n c1 c2.
        ~(a = 0) /\ ~(a = 1) /\ 0 < i /\ i <= n /\
        (X a i + c1 * X a n = X a j + c2 * X a n)
        ==> (?q. j = i + 4 * n * q) \/
            (?q. j + i = 4 * n * q)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `j < i:num` THENL
   [UNDISCH_TAC `X a i + c1 * X a n = X a j + c2 * X a n` THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
      `(x + q1 = y + q2) ==> y < x ==> (x = y + (q2 - q1:num))`)) THEN
    ASM_SIMP_TAC[X_INCREASES_LT; GSYM RIGHT_SUB_DISTRIB] THEN
    ASM_CASES_TAC `c2 - c1 = 0` THENL
     [ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; X_INJ] THEN
      DISCH_THEN(K ALL_TAC) THEN DISJ1_TAC THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `(i = j + q * n) ==> 1 <= j /\ 1 * n <= q * n ==> ~(i <= n)`)) THEN
    ASM_SIMP_TAC[X_INCREASES_LE] THEN
    ASM_SIMP_TAC[LE_MULT_RCANCEL;
                 ARITH_RULE `~(q2 - q1 = 0) ==> 1 <= q2 - q1`] THEN
    ONCE_REWRITE_TAC[GSYM(CONJUNCT1 X_CLAUSES)] THEN
    ASM_SIMP_TAC[X_INCREASES_LE; LE_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`a:num`; `i:num`; `j:num`; `n:num`; `c1 - c2:num`]
               STEP_DOWN_LEMMA_STRONG_ASYM) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB] THEN
  MATCH_MP_TAC(ARITH_RULE
   `(i + q1 = j + q2) /\ ~(j < i) ==> (i + q1 - q2 = j:num)`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  ASM_SIMP_TAC[NOT_LT; X_INCREASES_LE]);;

(* ------------------------------------------------------------------------- *)
(* Diophantine nature of the Y sequence.                                     *)
(* ------------------------------------------------------------------------- *)

let Y_DIOPH = prove
 (`~(a = 0) /\ ~(a = 1) /\ ~(y = 0)
   ==> ((y = Y a k) <=>
        ?x u v r b p q s t c d.
                0 < r /\
                (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1) /\
                (u EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1) /\
                (s EXP 2 = (b EXP 2 - 1) * t EXP 2 + 1) /\
                (v = r * y EXP 2) /\
                (b = 1 + 4 * p * y) /\
                (b = a + q * u) /\
                (s = x + c * u) /\
                (t = k + 4 * d * y) /\
                k <= y)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    MP_TAC(SPECL [`a:num`; `x:num`; `y:num`] SOLUTIONS_ARE_XY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (STRIP_ASSUME_TAC o GSYM)) THEN
    MP_TAC(SPECL [`a:num`; `u:num`; `v:num`] SOLUTIONS_ARE_XY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (STRIP_ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN `~(b = 0)` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `1 + 4 * p * y = b`)) THEN
      REWRITE_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
    MP_TAC(SPECL [`b:num`; `s:num`; `t:num`] SOLUTIONS_ARE_XY) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` (STRIP_ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN `y <= v:num` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `r * y EXP 2 = v`)) THEN REWRITE_TAC[EXP_2] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `y = 1 * y`] THEN
      REWRITE_TAC[MULT_ASSOC; LE_MULT_RCANCEL] THEN DISJ1_TAC THEN
      ASM_REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`; MULT_EQ_0] THEN
      ASM_SIMP_TAC[ARITH_RULE `0 < r ==> ~(r = 0)`]; ALL_TAC] THEN
    SUBGOAL_THEN `i <= n:num` ASSUME_TAC THENL
     [UNDISCH_TAC `y <= v:num` THEN
      SUBST1_TAC(SYM(ASSUME `Y a i = y`)) THEN
      SUBST1_TAC(SYM(ASSUME `Y a n = v`)) THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
      ASM_SIMP_TAC[NOT_LE; Y_INCREASES_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`a:num`; `q:num`; `u:num`; `j:num`] X_CONGRUENT) THEN
    REWRITE_TAC[ASSUME `~(a = 0)`; ASSUME `a + q * u = b:num`] THEN
    DISCH_THEN(X_CHOOSE_THEN `q1:num` MP_TAC) THEN
    SUBST1_TAC(ASSUME `X b j = s`) THEN
    SUBST1_TAC(SYM(ASSUME `x + c * u = s:num`)) THEN
    SUBST1_TAC(SYM(ASSUME `X a i = x`)) THEN
    SUBST1_TAC(SYM(ASSUME `X a n = u`)) THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(i = 0)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(y = 0)` THEN
      REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
      EXPAND_TAC "y" THEN SIMP_TAC[Y_CLAUSES; ASSUME `~(a = 0)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(?q. j = i + 4 * n * q) \/ (?q. j + i = 4 * n * q)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC STEP_DOWN_LEMMA_STRONG THEN
      MAP_EVERY EXISTS_TAC [`a:num`; `c:num`; `q1:num`] THEN
      ASM_SIMP_TAC[ARITH_RULE `~(i = 0) ==> 0 < i`]; ALL_TAC] THEN
    MP_TAC(SPECL [`a:num`; `i:num`; `n:num`] Y2_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
    REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
    SUBST1_TAC(SYM(ASSUME `r * y EXP 2 = v`)) THEN
    REWRITE_TAC[EQT_INTRO(SPEC_ALL MULT_SYM)] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:num` (ASSUME_TAC o SYM)) THEN
    UNDISCH_TAC `(?q. j = i + 4 * n * q) \/ (?q. j + i = 4 * n * q:num)` THEN
    UNDISCH_THEN `(i * y) * d1 = n:num` (SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(?q. j = i + q * 4 * Y a i) \/
                  (?q. j + i = q * 4 * Y a i)`
    MP_TAC THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_disj o concl) THEN
      REWRITE_TAC[OR_EXISTS_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `d2:num`
       (fun th -> EXISTS_TAC `i * d1 * d2:num` THEN MP_TAC th)) THEN
      SUBST1_TAC(ASSUME `Y a i = y`) THEN REWRITE_TAC[MULT_AC];
      FIRST_X_ASSUM(K ALL_TAC o check (is_disj o concl)) THEN
      DISCH_TAC] THEN
    MP_TAC(SPECL [`b:num`; `j:num`] Y_N_MODA1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d3:num` MP_TAC) THEN
    SUBST1_TAC(SYM(ASSUME `1 + 4 * p * y = b`)) THEN REWRITE_TAC[ADD_SUB2] THEN
    SUBST1_TAC(SYM(ASSUME `k + 4 * d * y = t`)) THEN DISCH_TAC THEN
    SUBST1_TAC(SYM(ASSUME `Y a i = y`)) THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `(?q1 q2. k + q1 * 4 * Y a i = i + q2 * 4 * Y a i) \/
                  (?q. i + k = q * 4 * Y a i)`
    MP_TAC THENL
     [UNDISCH_TAC `(?q. j = i + q * 4 * Y a i) \/
                   (?q. j + i = q * 4 * Y a i)` THEN
      MATCH_MP_TAC(TAUT
       `(a1 ==> b1) /\ (a2 ==> b2) ==> a1 \/ a2 ==> b1 \/ b2`) THEN
      CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `k + 4 * d * y = d3 * 4 * p * y + j` THENL
       [FIRST_X_ASSUM(X_CHOOSE_THEN `d4:num` SUBST1_TAC) THEN
        DISCH_THEN(fun th ->
          EXISTS_TAC `d:num` THEN
          EXISTS_TAC `d3 * p + d4:num` THEN MP_TAC th) THEN
        SUBST1_TAC(SYM(ASSUME `Y a i = y`)) THEN
        REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
        REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_AC];
        DISCH_THEN(MP_TAC o C AP_THM `i:num` o
          AP_TERM `(+):num->num->num`) THEN
        REWRITE_TAC[GSYM ADD_ASSOC] THEN
        FIRST_X_ASSUM(X_CHOOSE_THEN `d4:num` SUBST1_TAC) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `(k + q1 + i = q2) ==> (i + k = q2 - q1:num)`)) THEN
        DISCH_THEN SUBST1_TAC THEN
        SUBST1_TAC(SYM(ASSUME `Y a i = y`)) THEN
        REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB; MULT_ASSOC;
                    GSYM RIGHT_SUB_DISTRIB] THEN
        REWRITE_TAC[GSYM MULT_ASSOC] THEN
        REWRITE_TAC[ARITH_RULE
         `(d3 * 4 * p + d4 * 4) - 4 * x =
          ((d3 * p + d4) - x) * 4`] THEN REWRITE_TAC[GSYM MULT_ASSOC] THEN
        EXISTS_TAC `(d3 * p + d4) - d:num` THEN REFL_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `k <= Y a i` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `i <= Y a i` ASSUME_TAC THENL
     [MP_TAC(SPECL [`a:num`; `i:num`] Y_N_MODA1) THEN
      ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] LE_ADD]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `q4:num` (X_CHOOSE_THEN `q5:num` MP_TAC)) THEN
      REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
       (SPECL [`q4:num`; `q5:num`] LT_CASES)
      THENL
       [DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `(k + q4 = i + q5) ==> q4 < q5:num ==> (k = i + (q5 - q4))`)) THEN
        REWRITE_TAC[MULT_ASSOC; LT_MULT_RCANCEL; GSYM RIGHT_SUB_DISTRIB] THEN
        ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `k <= y:num` THEN
        MATCH_MP_TAC(TAUT `(a ==> ~b) ==> b ==> a ==> c`) THEN
        DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(ARITH_RULE `1 * y < k * y ==> ~(i + k * y <= y)`) THEN
        ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
        UNDISCH_TAC `q4 < q5:num` THEN ARITH_TAC;
        DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
         `(k + q4 = i + q5) ==> q5 < q4:num ==> (i = k + (q4 - q5))`)) THEN
        REWRITE_TAC[MULT_ASSOC; LT_MULT_RCANCEL; GSYM RIGHT_SUB_DISTRIB] THEN
        ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
        UNDISCH_TAC `i <= Y a i` THEN
        MATCH_MP_TAC(TAUT `(a ==> ~b) ==> b ==> a ==> c`) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(ARITH_RULE `1 * y < k * y ==> ~(i + k * y <= y)`) THEN
        ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
        UNDISCH_TAC `q5 < q4:num` THEN ARITH_TAC;
        ASM_SIMP_TAC[EQ_ADD_RCANCEL]];
      DISCH_THEN(X_CHOOSE_THEN `q6:num` MP_TAC) THEN
      ASM_CASES_TAC `q6 = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_EQ_0] THEN
      UNDISCH_TAC `k <= Y a i` THEN UNDISCH_TAC `i <= Y a i` THEN
      SUBST1_TAC(ASSUME `Y a i = y`) THEN
      MATCH_MP_TAC(ARITH_RULE
       `2 * y < ay ==> i <= y ==> k <= y ==> (i + k = ay) ==> (i = k)`) THEN
      REWRITE_TAC[MULT_ASSOC; LT_MULT_RCANCEL] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(q6 = 0)` THEN ARITH_TAC]] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN ABBREV_TAC `x = X a k` THEN
  SUBGOAL_THEN `x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1` (ASSUME_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
    SIMP_TAC[XY_ARE_SOLUTIONS; ASSUME `~(a = 0)`]; ALL_TAC] THEN
  EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = 2 * k * Y a k` THEN
  ABBREV_TAC `u = X a m` THEN ABBREV_TAC `v = Y a m` THEN
  SUBGOAL_THEN `u EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1` (ASSUME_TAC o SYM) THENL
   [MAP_EVERY EXPAND_TAC ["u"; "v"] THEN
    SIMP_TAC[XY_ARE_SOLUTIONS; ASSUME `~(a = 0)`]; ALL_TAC] THEN
  EXISTS_TAC `u:num` THEN EXISTS_TAC `v:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y EXP 2) divides v` MP_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `Y a m = v`)) THEN
    SUBST1_TAC(SYM(ASSUME `Y a k = y`)) THEN
    SIMP_TAC[Y2_DIVIDES; ASSUME `~(a = 0)`] THEN
    SUBST1_TAC(SYM(ASSUME `2 * k * Y a k = m`)) THEN
    REWRITE_TAC[divides] THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` (ASSUME_TAC o SYM)) THEN
  EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 0` THENL
   [UNDISCH_TAC `y EXP 2 * r = v` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN REWRITE_TAC[LT_REFL] THEN
    UNDISCH_TAC `Y a m = v` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `m = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `Y a m = 0` THEN
      ONCE_REWRITE_TAC[GSYM(CONJUNCT1 Y_CLAUSES)] THEN
      SIMP_TAC[Y_INJ; ASSUME `~(a = 0)`] THEN
      REWRITE_TAC[Y_CLAUSES]; ALL_TAC] THEN
    SUBGOAL_THEN `k = 0` ASSUME_TAC THENL
     [UNDISCH_TAC `2 * k * Y a k = m` THEN
      REWRITE_TAC[ASSUME `m = 0`; MULT_EQ_0; ARITH_EQ] THEN
      ONCE_REWRITE_TAC[GSYM(CONJUNCT1 Y_CLAUSES)] THEN
      SIMP_TAC[Y_INJ; ASSUME `~(a = 0)`] THEN
      REWRITE_TAC[Y_CLAUSES; EQ_SYM]; ALL_TAC] THEN
    UNDISCH_TAC `Y a k = y` THEN ASM_REWRITE_TAC[Y_CLAUSES];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(r = 0) ==> 0 < r`] THEN
  SUBGOAL_THEN `ODD(u)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a EXP 2 - 1) * v EXP 2 + 1 = u EXP 2` THEN
    DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
    REWRITE_TAC[EXP_2; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
    SUBGOAL_THEN `EVEN v` (fun th -> REWRITE_TAC[GSYM NOT_EVEN; th]) THEN
    SUBST1_TAC(SYM(ASSUME `Y a m = v`)) THEN
    MP_TAC(SPECL [`a:num`; `m:num`] Y_N_MOD2) THEN
    SIMP_TAC[ASSUME `~(a = 0)`; LEFT_IMP_EXISTS_THM] THEN
    SUBST1_TAC(SYM(ASSUME `2 * k * Y a k = m`)) THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]; ALL_TAC] THEN
  SUBGOAL_THEN `?b0 q6 q7. (b0 = 1 + q6 * 4 * y) /\ (b0 = a + q7 * u)`
  MP_TAC THENL
   [MATCH_MP_TAC CHINESE_REMAINDER THEN
    UNDISCH_TAC `ODD u` THEN
    ASM_CASES_TAC `u = 0` THEN ASM_REWRITE_TAC[ARITH_ODD] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_MUL THEN
    CONJ_TAC THENL
     [SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 * 2`)) THEN
      MATCH_MP_TAC COPRIME_MUL THEN REWRITE_TAC[] THEN
      MP_TAC(SPECL [`u:num`; `2`] PRIME_COPRIME) THEN REWRITE_TAC[PRIME_2] THEN
      MATCH_MP_TAC(TAUT `~b /\ (a ==> d) /\ (c ==> d)
                         ==> a \/ b \/ c ==> d`) THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `ODD u` THEN
        ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
        SIMP_TAC[divides; LEFT_IMP_EXISTS_THM; ODD_MULT; ARITH_ODD];
        ONCE_REWRITE_TAC[COPRIME_SYM] THEN SIMP_TAC[COPRIME_1];
        REWRITE_TAC[COPRIME_SYM]];
      MP_TAC(SPECL [`a:num`; `m:num`] XY_COPRIME) THEN ASM_REWRITE_TAC[] THEN
      SUBST1_TAC(SYM(ASSUME `y EXP 2 * r = v`)) THEN
      REWRITE_TAC[coprime; EXP_2] THEN
      MESON_TAC[DIVIDES_RMUL; DIVIDES_LMUL]]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num` (X_CHOOSE_THEN `p:num`
        (X_CHOOSE_THEN `q:num` (STRIP_ASSUME_TAC o GSYM)))) THEN
  MAP_EVERY EXISTS_TAC [`b:num`; `p:num`; `q:num`] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `1 + 4 * p * y = 1 + p * 4 * y`] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `s = X b k` THEN ABBREV_TAC `t = Y b k` THEN
  EXISTS_TAC `s:num` THEN EXISTS_TAC `t:num` THEN
  SUBST1_TAC(ARITH_RULE `r * y EXP 2 = y EXP 2 * r`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBST1_TAC(SYM(ASSUME `X b k = s`)) THEN
  SUBST1_TAC(SYM(ASSUME `Y b k = t`)) THEN
  SUBGOAL_THEN `~(b = 0)` ASSUME_TAC THENL
   [UNDISCH_THEN `1 + p * 4 * y = b` (SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC[TAUT `~b ==> a ==> b ==> ~a`] THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ]; ALL_TAC] THEN
  SIMP_TAC[XY_ARE_SOLUTIONS; ASSUME `~(b = 0)`] THEN
  MP_TAC(SPECL [`a:num`; `q:num`; `u:num`; `k:num`] X_CONGRUENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (ASSUME_TAC o SYM)) THEN
  EXISTS_TAC `c:num` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`b:num`; `k:num`] Y_N_MODA1) THEN
  SUBST1_TAC(SYM(ASSUME `1 + p * 4 * y = b`)) THEN
  REWRITE_TAC[ADD_EQ_0; ADD_SUB2; ARITH_EQ] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q8:num` SUBST1_TAC) THEN
  EXISTS_TAC `q8 * p:num` THEN REWRITE_TAC[MULT_AC; ADD_AC] THEN
  MP_TAC(SPECL [`a:num`; `k:num`] Y_N_MODA1) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] LE_ADD]);;

(* ------------------------------------------------------------------------- *)
(* A ratio approaches a^n for large enough k.                                *)
(* ------------------------------------------------------------------------- *)

let BINOMIALISH_LEMMA = prove
 (`!m n. m EXP n * (m - n) <= m * (m - 1) EXP n`,
  GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; SUB_0; MULT_CLAUSES; LE_REFL] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(m - 1) * m EXP n * (m - n)` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM MULT_ASSOC] THEN
    ONCE_REWRITE_TAC[AC MULT_AC `a * b * c = b * a * c:num`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[LEFT_SUB_DISTRIB; RIGHT_SUB_DISTRIB; MULT_CLAUSES] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a - (b + c) = a - c - b:num`] THEN
    MATCH_MP_TAC(ARITH_RULE `c <= b ==> a - b <= a - c:num`) THEN ARITH_TAC;
    GEN_REWRITE_TAC RAND_CONV
     [AC MULT_AC `m * (m - 1) * n = (m - 1) * m * n`] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL]]);;

let XY_EXP_LEMMA = prove
 (`!a k n.
        ~(a = 0) /\
        2 * n * a EXP n < k
        ==> abs(&(Y (a * k) (n + 1)) / &(Y k (n + 1)) - &a pow n) < &1 / &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [FIRST_ASSUM(ACCEPT_TAC o MATCH_MP (ARITH_RULE
     `a < k ==> ~(k = 0)`)); ALL_TAC] THEN
  SUBGOAL_THEN `0 < Y k (n + 1)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(SPEC `k:num` (CONJUNCT1 Y_CLAUSES))) THEN
    ASM_SIMP_TAC[Y_INCREASES_LT; ARITH_RULE `0 < n + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN
  EXISTS_TAC `abs(&(Y k (n + 1)))` THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[REAL_ABS_NUM; REAL_LT_IMP_NZ;
               REAL_OF_NUM_LT; REAL_DIV_LMUL] THEN
  REWRITE_TAC[real_div; REAL_MUL_LID; REAL_MUL_ASSOC] THEN
  SIMP_TAC[GSYM real_div; REAL_OF_NUM_LT; ARITH; REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!lx ly ux uy.
        lx <= x /\ x <= ux /\ ly <= y /\ y <= uy /\
        &2 * uy < &2 * lx + d /\ &2 * ux < &2 * ly + d
        ==> abs(x - y) * &2 < d`) THEN
  MAP_EVERY EXISTS_TAC
   [`&((2 * a * k - 1) EXP n)`; `&((2 * k - 1) EXP n) * &a pow n`;
    `&((2 * a * k) EXP n)`; `&((2 * k) EXP n) * &a pow n`] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; Y_LOWERBOUND; Y_UPPERBOUND;
               REAL_LE_RMUL_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
               ARITH_RULE `~(a = 0) ==> 0 < a`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_LT] THEN
  MATCH_MP_TAC(ARITH_RULE
   `!x:num. x <= c /\ a < b + x /\ d < e + x ==> a < b + c /\ d < e + c`) THEN
  EXISTS_TAC `(2 * k - 1) EXP n` THEN REWRITE_TAC[Y_LOWERBOUND] THEN
  REWRITE_TAC[GSYM MULT_EXP; GSYM MULT_ASSOC] THEN
  REWRITE_TAC[RIGHT_SUB_DISTRIB; GSYM MULT_ASSOC] THEN
  SUBST1_TAC(AC MULT_AC `2 * k * a = 2 * a * k`) THEN
  REWRITE_TAC[MULT_CLAUSES] THEN
  MATCH_MP_TAC(ARITH_RULE
   `b' <= b /\ a < b' + c ==> a < b + c /\ a < b' + c:num`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    SPEC_TAC(`n:num`,`m:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 EXP; LE_REFL] THEN
    REWRITE_TAC[EXP_MONO_LE_SUC] THEN UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(AC MULT_AC `2 * a * k = 2 * k * a`) THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV)
   [ARITH_RULE `a = 1 * a`] THEN
  REWRITE_TAC[MULT_ASSOC; GSYM RIGHT_SUB_DISTRIB] THEN
  REWRITE_TAC[MULT_EXP] THEN
  REWRITE_TAC[ARITH_RULE `2 * e * a + e = (2 * a + 1) * e`] THEN
  REWRITE_TAC[GSYM MULT_EXP; GSYM MULT_ASSOC] THEN
  SUBST1_TAC(AC MULT_AC `2 * k * a = a * 2 * k`) THEN
  ONCE_REWRITE_TAC[MULT_EXP] THEN REWRITE_TAC[MULT_ASSOC] THEN
  SUBGOAL_THEN `(2 * k) * (2 * a EXP n) * (2 * k) EXP n <
                (2 * k) * (2 * a EXP n + 1) * (2 * k - 1) EXP n`
  MP_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[LT_MULT_LCANCEL; MULT_EQ_0; ARITH_EQ]] THEN
  GEN_REWRITE_TAC RAND_CONV
   [AC MULT_AC `(2 * k) * l * m = l * (2 * k) * m`] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `(2 * a EXP n + 1) * (2 * k) EXP n * (2 * k - n)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[LE_MULT_LCANCEL; BINOMIALISH_LEMMA]] THEN
  REWRITE_TAC[ARITH_RULE
   `(2 * k) * (2 * an) * 2kn < a2na * 2kn * kmn <=>
    2kn * 4 * k * an < 2kn * a2na * kmn`] THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; EXP_EQ_0; MULT_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB] THEN
  MATCH_MP_TAC(ARITH_RULE `a + b < c ==> a < c - b:num`) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `4 * k * an + x < 2 * an * 2 * k + y <=> x < y`] THEN
  ONCE_REWRITE_TAC[AC MULT_AC `2 * a * n = 2 * n * a`] THEN
  UNDISCH_TAC `2 * n * a EXP n < k` THEN
  MATCH_MP_TAC(ARITH_RULE
   `n * 1 <= x ==> 2 * x < k ==> 2 * x + n < 2 * k`) THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  ASM_REWRITE_TAC[EXP_EQ_0]);;

let ABS_LT_REPRESENTATION = prove
 (`!x y z.
    ~(y = 0)
    ==> (abs(&x / &y - &z) < &1 / &2 <=>
         4 * x EXP 2 + 4 * (y * z) EXP 2 < 8 * x * y * z + y EXP 2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&4 * (&x / &y - &z) pow 2 < &1` THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    SUBST1_TAC(SYM(REAL_RAT_REDUCE_CONV `&2 * &2`)) THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_POW_MUL] THEN
    ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN EQ_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
       [SYM(REAL_RAT_REDUCE_CONV `&1 pow 2`)] THEN
      GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
      SIMP_TAC[ARITH_EQ; REAL_POW_LT2; REAL_LE_MUL; REAL_POS; REAL_ABS_POS];
      ONCE_REWRITE_TAC[TAUT `a ==> b <=> ~b ==> ~a`] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
       [SYM(REAL_RAT_REDUCE_CONV `&1 pow 2`)] THEN
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN
      SIMP_TAC[ARITH_EQ; REAL_POW_LE2; REAL_LE_MUL; REAL_POS; REAL_ABS_POS]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&4 * (&x - &y * &z) pow 2 < &y pow 2` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_POW2_ABS] THEN
    REWRITE_TAC[GSYM REAL_ABS_POW] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; GSYM REAL_ABS_NZ; REAL_POW_EQ_0;
                 ARITH_EQ; REAL_OF_NUM_EQ] THEN
    REWRITE_TAC[REAL_ABS_POW; REAL_POW2_ABS] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div; GSYM REAL_POW_DIV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div; REAL_SUB_RDISTRIB; GSYM REAL_MUL_ASSOC] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_DIV_LMUL; REAL_OF_NUM_EQ]; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD;
              GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let Y_EQ_0 = prove
 (`!a n. ~(a = 0) ==> ((Y a n = 0) <=> (n = 0))`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM(SPEC `a:num` (CONJUNCT1 Y_CLAUSES))) THEN
  ASM_SIMP_TAC[Y_INJ] THEN REWRITE_TAC[Y_CLAUSES]);;

let XY_EXP = prove
 (`~(a = 0)
   ==> ((a EXP n = p) <=>
        ?k x y z. (Y (a * k) (n + 1) = x) /\
                  (Y k (n + 1) = y) /\
                  (Y a (n + 1) = z) /\
                  2 * n * z < k /\
                  4 * x EXP 2 + 4 * (y * p) EXP 2 < 8 * x * y * p + y EXP 2)`,
  let lemma1 = prove
   (`(?x y z. (a = x) /\ (b = y) /\ (c = z) /\ P x y z) <=> P a b c`,
    MESON_TAC[])
  and lemma2 =
    CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV SYM_CONV))
             (SPEC_ALL ABS_LT_REPRESENTATION) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[lemma1] THEN
  GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV o LAND_CONV)
    [ARITH_RULE `n < k <=> n < k /\ ~(k = 0)`] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  ASM_SIMP_TAC[lemma2; Y_EQ_0; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[NOT_IMP] THEN
  REWRITE_TAC[ARITH_RULE `n < k /\ ~(k = 0) <=> n < k`] THEN
  EQ_TAC THENL
   [DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `2 * n * Y a (n + 1) + 1` THEN
    REWRITE_TAC[ARITH_RULE `c < c + 1`; GSYM REAL_OF_NUM_POW] THEN
    MATCH_MP_TAC XY_EXP_LEMMA THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `a <= b ==> 2 * a < 2 * b + 1`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(2 * a - 1) EXP n` THEN
    REWRITE_TAC[Y_LOWERBOUND] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[CONJUNCT1 EXP; LE_REFL; EXP_MONO_LE_SUC] THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(SPECL [`a:num`; `k:num`; `n:num`] XY_EXP_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `2 * a < k ==> b <= a ==> 2 * b < k`)) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(2 * a - 1) EXP n` THEN
    REWRITE_TAC[Y_LOWERBOUND] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[CONJUNCT1 EXP; LE_REFL; EXP_MONO_LE_SUC] THEN
    UNDISCH_TAC `~(a = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - a) < e1 /\ abs(x - b) < e2 ==> abs(a - b) < e1 + e2`)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(a - b) < &1
    ==> a + &1 <= b \/ (a = b) \/ b + &1 <= a ==> (a = b)`)) THEN
  REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
              REAL_OF_NUM_EQ; REAL_OF_NUM_LE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let REAL_SUM_OF_SQUARES = prove
 (`(x pow 2 + y pow 2 = &0) <=> (x = &0) /\ (y = &0)`,
  REWRITE_TAC[REAL_POW_2] THEN EQ_TAC THEN
  SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `(a + b = &0) ==> &0 <= a /\ &0 <= b ==> (a = &0) /\ (b = &0)`)) THEN
  REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for conjunction and disjunction.                       *)
(* ------------------------------------------------------------------------- *)

let DIOPH_CONJ = prove
 (`(x1 = x2) /\ (y1 = y2) <=>
   (x1 * x1 + x2 * x2 + y1 * y1 + y2 * y2 = 2 * x1 * x2 + 2 * y1 * y2)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ;
    GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[GSYM REAL_SUM_OF_SQUARES] THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let DIOPH_DISJ = prove
 (`(x1 = x2) \/ (y1 = y2) <=>
   (x1 * y1 + x2 * y2 = x1 * y2 + x2 * y1)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ;
    GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  REWRITE_TAC[GSYM REAL_ENTIRE] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Inequalities.                                                             *)
(* ------------------------------------------------------------------------- *)

let DIOPH_LE = prove
 (`x <= y <=> ?d:num. x + d = y`,
  REWRITE_TAC[LE_EXISTS] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[ADD_AC; EQ_SYM_EQ]);;

let DIOPH_LT = prove
 (`x < y <=> ?d. x + d + 1 = y`,
  REWRITE_TAC[LT_EXISTS] THEN
  REWRITE_TAC[ADD1] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[ADD_AC; EQ_SYM_EQ]);;

let DIOPH_NE = prove
 (`~(x = y) <=> x < y \/ y < x:num`,
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Exponentiation (from the Pell stuff).                                     *)
(* ------------------------------------------------------------------------- *)

let Y_0 = prove
 (`!k. Y 0 k = if k = 1 then 1 else 0`,
  INDUCT_TAC THEN REWRITE_TAC[Y_CLAUSES; ARITH_EQ] THEN
  SPEC_TAC(`k:num`,`k:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[Y_CLAUSES; ARITH] THEN
  REWRITE_TAC[ARITH_RULE `SUC(SUC n) = n + 2`; Y_CLAUSES; ARITH] THEN
  REWRITE_TAC[MULT_CLAUSES; SUB_0; ARITH_RULE `~(k + 2 = 1)`]);;

let Y_0_TRIV = prove
 (`!k. (Y 0 k = 0) <=> ~(k = 1)`,
  GEN_TAC THEN REWRITE_TAC[Y_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH_EQ]);;

let DIOPH_Y = prove
 (`(Y a k = y) <=>
        (a = 0) /\ (k = 1) /\ (y = 1) \/
        (a = 0) /\ ~(k = 1) /\ (y = 0) \/
        (k = 0) /\ (y = 0) \/
        (a = 1) /\ (y = k) \/
        ~(a = 0) /\ ~(k = 0) /\ ~(a = 1) /\ ~(y = 0) /\
        ?x u v r b p q s t c d.
                0 < r /\
                (x EXP 2 = (a EXP 2 - 1) * y EXP 2 + 1) /\
                (u EXP 2 = (a EXP 2 - 1) * v EXP 2 + 1) /\
                (s EXP 2 = (b EXP 2 - 1) * t EXP 2 + 1) /\
                (v = r * y EXP 2) /\
                (b = 1 + 4 * p * y) /\
                (b = a + q * u) /\
                (s = x + c * u) /\
                (t = k + 4 * d * y) /\
                k <= y`,
  ASM_CASES_TAC `a = 0` THENL
   [ASM_CASES_TAC `y = 0` THENL
     [ASM_REWRITE_TAC[Y_0_TRIV; ARITH_EQ] THEN ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[Y_CLAUSES; ARITH_EQ] THEN
    ASM_REWRITE_TAC[ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    REWRITE_TAC[EXP_2; MULT_EQ_1] THEN
    REWRITE_TAC[Y_0] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EQ_SYM_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_EQ] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[Y_CLAUSES] THENL
   [REWRITE_TAC[EQ_SYM_EQ] THEN CONV_TAC(EQT_INTRO o TAUT); ALL_TAC] THEN
  ASM_CASES_TAC `a = 1` THEN ASM_REWRITE_TAC[Y_DEGENERATE] THENL
   [REWRITE_TAC[EQ_SYM_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `y = 0` THEN ASM_SIMP_TAC[Y_EQ_0] THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN ASM_SIMP_TAC[Y_DIOPH]);;

let DIOPH_EXP_LEMMA = prove
 (`(m EXP n = p) <=>
        (m = 0) /\ (n = 0) /\ (p = 1) \/
        (m = 0) /\ ~(n = 0) /\ (p = 0) \/
        ~(m = 0) /\
        ?k x y z. (Y (m * k) (n + 1) = x) /\
                  (Y k (n + 1) = y) /\
                  (Y m (n + 1) = z) /\
                  2 * n * z < k /\
                  4 * x EXP 2 + 4 * (y * p) EXP 2 < 8 * x * y * p + y EXP 2`,
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ARITH_EQ] THENL
   [SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EXP; MULT_CLAUSES; ADD_CLAUSES; NOT_SUC] THEN
    REWRITE_TAC[EQ_SYM_EQ]; ALL_TAC] THEN
  ASM_SIMP_TAC[XY_EXP]);;

let DIOPH_EXP =
  let th1 = REWRITE_RULE[DIOPH_Y] DIOPH_EXP_LEMMA in
  let th2 = REWRITE_RULE[EXP_2] th1 in
  let th3 = REWRITE_RULE[DIOPH_NE; DIOPH_LT; DIOPH_LE] th2 in
  let th4 = REWRITE_RULE[ADD_CLAUSES; ARITH_EQ; ADD_EQ_0;
    ARITH_RULE `(n + 1 = 1) = (n = 0)`; ADD_ASSOC;
    EQ_ADD_RCANCEL] th3 in
  let th5 = REWRITE_RULE[GSYM ADD_ASSOC] th4 in
  REWRITE_RULE
   [OR_EXISTS_THM; LEFT_OR_EXISTS_THM; RIGHT_OR_EXISTS_THM;
    LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] th5;;

(****** This takes about an hour to compute, and longer to print out!

let DIOPH_EXP_ONE_EQUATION =
  REWRITE_RULE[DIOPH_CONJ; DIOPH_DISJ] DIOPH_EXP;;

 *******)
