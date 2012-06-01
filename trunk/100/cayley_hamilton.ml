(* ========================================================================= *)
(* The Cayley-Hamilton theorem (for real matrices).                          *)
(* ========================================================================= *)

needs "Multivariate/complexes.ml";;

(* ------------------------------------------------------------------------- *)
(* Powers of a square matrix (mpow) and sums of matrices (msum).             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("mpow",(24,"left"));;

let mpow = define
  `(!A:real^N^N. A mpow 0 = (mat 1 :real^N^N)) /\
   (!A:real^N^N n. A mpow (SUC n) = A ** A mpow n)`;;

let msum = new_definition
 `msum = iterate (matrix_add)`;;

let NEUTRAL_MATRIX_ADD = prove
 (`neutral((+):real^N^M->real^N^M->real^N^M) = mat 0`,
  REWRITE_TAC[neutral] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  MESON_TAC[MATRIX_ADD_RID; MATRIX_ADD_LID]);;

let MONOIDAL_MATRIX_ADD = prove
 (`monoidal((+):real^N^M->real^N^M->real^N^M)`,
  REWRITE_TAC[monoidal; NEUTRAL_MATRIX_ADD] THEN
  REWRITE_TAC[MATRIX_ADD_LID; MATRIX_ADD_ASSOC] THEN
  REWRITE_TAC[MATRIX_ADD_SYM]);;

let MSUM_CLAUSES = prove
 (`(!(f:A->real^N^M). msum {} f = mat 0) /\
   (!x (f:A->real^N^M) s.
        FINITE(s)
        ==> (msum (x INSERT s) f =
             if x IN s then msum s f else f(x) + msum s f))`,
  REWRITE_TAC[msum; GSYM NEUTRAL_MATRIX_ADD] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_MATRIX_ADD]);;

let MSUM_MATRIX_RMUL = prove
 (`!(f:A->real^N^M) (A:real^P^N) s.
        FINITE s ==> msum s (\i. f(i) ** A) = msum s f ** A`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES; MATRIX_MUL_LZERO; MATRIX_ADD_RDISTRIB]);;

let MSUM_MATRIX_LMUL = prove
 (`!(f:A->real^P^N) (A:real^N^M) s.
        FINITE s ==> msum s (\i. A ** f(i)) = A ** msum s f`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES; MATRIX_MUL_RZERO; MATRIX_ADD_LDISTRIB]);;

let MSUM_ADD = prove
 (`!f g s. FINITE s ==> (msum s (\x. f(x) + g(x)) = msum s f + msum s g)`,
  SIMP_TAC[msum; ITERATE_OP; MONOIDAL_MATRIX_ADD]);;

let MSUM_CMUL = prove
 (`!(f:A->real^N^M) c s.
        FINITE s ==>  msum s (\i. c %% f(i)) = c %% msum s f`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES; MATRIX_CMUL_ADD_LDISTRIB; MATRIX_CMUL_RZERO]);;

let MSUM_NEG = prove
 (`!(f:A->real^N^M) s.
        FINITE s ==>  msum s (\i. --(f(i))) = --(msum s f)`,
  ONCE_REWRITE_TAC[MATRIX_NEG_MINUS1] THEN
  REWRITE_TAC[MSUM_CMUL]);;

let MSUM_SUB = prove
 (`!f g s. FINITE s ==> (msum s (\x. f(x) - g(x)) = msum s f - msum s g)`,
  REWRITE_TAC[MATRIX_SUB; MATRIX_NEG_MINUS1] THEN
  SIMP_TAC[MSUM_ADD; MSUM_CMUL]);;

let MSUM_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> msum(m..n) f = f(m) + msum(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; MSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let MSUM_SUPPORT = prove
 (`!f s. msum (support (+) f s) f = msum s f`,
  SIMP_TAC[msum; iterate; SUPPORT_SUPPORT]);;

let MSUM_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> (msum s f = msum s g)`,
  REWRITE_TAC[msum] THEN
  MATCH_MP_TAC ITERATE_EQ THEN REWRITE_TAC[MONOIDAL_MATRIX_ADD]);;

let MSUM_RESTRICT_SET = prove
 (`!P s f. msum {x:A | x IN s /\ P x} f =
           msum s (\x. if P x then f(x) else mat 0)`,
  ONCE_REWRITE_TAC[GSYM MSUM_SUPPORT] THEN
  REWRITE_TAC[support; NEUTRAL_MATRIX_ADD; IN_ELIM_THM] THEN
  REWRITE_TAC[MESON[] `~((if P x then f x else a) = a) <=> P x /\ ~(f x = a)`;
              GSYM CONJ_ASSOC] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MSUM_EQ THEN SIMP_TAC[IN_ELIM_THM]);;

let MSUM_SING = prove
 (`!f x. msum {x} f = f(x)`,
  SIMP_TAC[MSUM_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; MATRIX_ADD_RID]);;

let MSUM_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (msum (IMAGE f s) g = msum s (g o f))`,
  REWRITE_TAC[msum; GSYM NEUTRAL_MATRIX_ADD] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_MATRIX_ADD]);;

let MSUM_OFFSET = prove
 (`!p f m n. msum(m+p..n+p) f = msum(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; MSUM_IMAGE; EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let MSUM_COMPONENT = prove
 (`!f:A->real^N^M i j s.
        1 <= i /\ i <= dimindex(:M) /\
        1 <= j /\ j <= dimindex(:N) /\
        FINITE s
        ==> (msum s f)$i$j = sum s (\a. f(a)$i$j)`,
  REPLICATE_TAC 3 GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[MSUM_CLAUSES; SUM_CLAUSES] THEN
  ASM_SIMP_TAC[MATRIX_ADD_COMPONENT; MAT_COMPONENT; COND_ID]);;

let MSUM_CLAUSES_NUMSEG = prove
 (`(!m. msum(m..0) f = if m = 0 then f(0) else mat 0) /\
   (!m n. msum(m..SUC n) f = if m <= SUC n then msum(m..n) f + f(SUC n)
                             else msum(m..n) f)`,
  REWRITE_TAC[MATCH_MP ITERATE_CLAUSES_NUMSEG MONOIDAL_MATRIX_ADD;
              NEUTRAL_MATRIX_ADD; msum]);;

let MPOW_ADD = prove
 (`!A:real^N^N m n. A mpow (m + n) = A mpow m ** A mpow n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; mpow; MATRIX_MUL_LID] THEN
  REWRITE_TAC[MATRIX_MUL_ASSOC]);;

let MPOW_1 = prove
 (`!A:real^N^N. A mpow 1 = A`,
  REWRITE_TAC[num_CONV `1`; mpow] THEN
  REWRITE_TAC[SYM(num_CONV `1`); MATRIX_MUL_RID]);;

let MPOW_SUC = prove
 (`!A:real^N^N n. A mpow (SUC n) = A mpow n ** A`,
  REWRITE_TAC[ADD1; MPOW_ADD; MPOW_1]);;

(* ------------------------------------------------------------------------- *)
(* The main lemma underlying the proof.                                      *)
(* ------------------------------------------------------------------------- *)

let MATRIC_POLYFUN_EQ_0 = prove
 (`!n A:num->real^N^M.
        (!x. msum(0..n) (\i. x pow i %% A i) = mat 0) <=>
        (!i. i IN 0..n ==> A i = mat 0)`,
  SIMP_TAC[CART_EQ; MSUM_COMPONENT; MAT_COMPONENT; LAMBDA_BETA;
           FINITE_NUMSEG; COND_ID;
           ONCE_REWRITE_RULE[REAL_MUL_SYM] MATRIX_CMUL_COMPONENT] THEN
  REWRITE_TAC[MESON[]
   `(!x i. P i ==> !j. Q j ==> R x i j) <=>
    (!i. P i ==> !j. Q j ==> !x. R x i j)`] THEN
  REWRITE_TAC[REAL_POLYFUN_EQ_0] THEN MESON_TAC[]);;

let MATRIC_POLY_LEMMA = prove
 (`!(A:real^N^N) B (C:real^N^N) n.
        (!x. msum (0..n) (\i. (x pow i) %% B i) ** (A - x %% mat 1) = C)
        ==> C = mat 0`,
  SIMP_TAC[GSYM MSUM_MATRIX_RMUL; FINITE_NUMSEG; MATRIX_SUB_LDISTRIB] THEN
  REWRITE_TAC[MATRIX_MUL_RMUL] THEN ONCE_REWRITE_TAC[MATRIX_MUL_LMUL] THEN
  ONCE_REWRITE_TAC[MATRIX_CMUL_ASSOC] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  SIMP_TAC[MSUM_SUB; FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. msum(0..SUC n)
         (\i. x pow i %% (((if i = 0 then (--C:real^N^N) else mat 0) +
                           (if i <= n then B i ** (A:real^N^N) else mat 0)) -
                          (if i = 0 then mat 0 else B(i - 1) ** mat 1))) =
        mat 0`
  MP_TAC THENL
   [SIMP_TAC[MATRIX_CMUL_SUB_LDISTRIB; MSUM_SUB; FINITE_NUMSEG;
             MATRIX_CMUL_ADD_LDISTRIB; MSUM_ADD] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MATRIX_CMUL_RZERO] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(if p then mat 0 else x) = (if ~p then x else mat 0)`] THEN
    REWRITE_TAC[GSYM MSUM_RESTRICT_SET; IN_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(0 <= i /\ i <= SUC n) /\ i = 0 <=> i = 0`;
      ARITH_RULE `(0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n`;
      ARITH_RULE `(0 <= i /\ i <= SUC n) /\ ~(i = 0) <=>
                  1 <= i /\ i <= SUC n`] THEN
    REWRITE_TAC[SING_GSPEC; GSYM numseg; MSUM_SING; real_pow] THEN
    REWRITE_TAC[MATRIX_CMUL_LID] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC ONCE_DEPTH_CONV [GSYM th]) THEN
    REWRITE_TAC[MATRIX_NEG_SUB] THEN REWRITE_TAC[MATRIX_SUB; AC MATRIX_ADD_AC
     `(((A:real^N^N) + --B) + B) + C = (--B + B) + A + C`] THEN
    REWRITE_TAC[MATRIX_ADD_LNEG; MATRIX_ADD_LID] THEN
    REWRITE_TAC[num_CONV `1`] THEN REWRITE_TAC[ADD1; MSUM_OFFSET] THEN
    REWRITE_TAC[ADD_CLAUSES; ADD_SUB; MATRIX_ADD_RNEG];
    REWRITE_TAC[MATRIC_POLYFUN_EQ_0; IN_NUMSEG; LE_0] THEN DISCH_TAC THEN
    SUBGOAL_THEN `!i:num. B(n - i) = (mat 0:real^N^N)` MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`) THEN
        REWRITE_TAC[LE_REFL; SUB_0; NOT_SUC; ARITH_RULE `~(SUC n <= n)`] THEN
        REWRITE_TAC[MATRIX_ADD_LID; SUC_SUB1; MATRIX_MUL_RID] THEN
        REWRITE_TAC[MATRIX_SUB_LZERO; MATRIX_NEG_EQ_0];
        X_GEN_TAC `m:num` THEN DISCH_TAC THEN
        DISJ_CASES_TAC(ARITH_RULE `n - SUC m = n - m \/ m < n`) THEN
        ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n - m:num`) THEN
        ASM_SIMP_TAC[ARITH_RULE `m < n ==> ~(n - m = 0)`;
                     ARITH_RULE `n - m <= SUC n /\ n - m <= n`] THEN
        REWRITE_TAC[MATRIX_MUL_LZERO; MATRIX_ADD_LID; MATRIX_SUB_LZERO] THEN
        REWRITE_TAC[MATRIX_MUL_RID; MATRIX_NEG_EQ_0] THEN
        ASM_SIMP_TAC[ARITH_RULE `n - m - 1 = n - SUC m`]];
      DISCH_THEN(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[SUB_REFL] THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[LE_0; MATRIX_MUL_LZERO; MATRIX_ADD_RID] THEN
      REWRITE_TAC[MATRIX_SUB_RZERO; MATRIX_NEG_EQ_0]]]);;

(* ------------------------------------------------------------------------- *)
(* Show that cofactor and determinant are n-1 and n degree polynomials.      *)
(* ------------------------------------------------------------------------- *)

let POLYFUN_N_CONST = prove
 (`!c n. ?b. !x. c = sum(0..n) (\i. b i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. if i = 0 then c else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `(0 <= i /\ i <= n) /\ i = 0 <=> i = 0`] THEN
  REWRITE_TAC[SING_GSPEC; SUM_SING; real_pow; REAL_MUL_RID]);;

let POLYFUN_N_ADD = prove
 (`!f g. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i)) /\
         (?c. !x. g(x) = sum(0..n) (\i. c i * x pow i))
         ==> ?d. !x. f(x) + g(x) = sum(0..n) (\i. d i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. (b:num->real) i + c i` THEN
  ASM_REWRITE_TAC[SUM_ADD_NUMSEG; REAL_ADD_RDISTRIB]);;

let POLYFUN_N_CMUL = prove
 (`!f c. (?b. !x. f(x) = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. c * f(x) = sum(0..n) (\i. b i * x pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\i. c * (b:num->real) i` THEN
  ASM_REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC]);;

let POLYFUN_N_SUM = prove
 (`!f s. FINITE s /\
         (!a. a IN s ==> ?b. !x. f x a = sum(0..n) (\i. b i * x pow i))
         ==> ?b. !x. sum s (f x) = sum(0..n) (\i. b i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY; POLYFUN_N_CONST] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_ADD THEN ASM_SIMP_TAC[]);;

let POLYFUN_N_PRODUCT = prove
 (`!f s n. FINITE s /\
           (!a:A. a IN s ==> ?c d. !x. f x a = c + d * x) /\ CARD(s) <= n
           ==> ?b. !x. product s (f x) = sum(0..n) (\i. b i * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; POLYFUN_N_CONST; FORALL_IN_INSERT] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  INDUCT_TAC THENL [ARITH_TAC; REWRITE_TAC[LE_SUC]] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->real`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_TAC `d:real`)) THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\i. (if i <= n then c * b i else &0) +
                  (if ~(i = 0) then d * b(i - 1) else &0)` THEN
  X_GEN_TAC `x:real` THEN
  REWRITE_TAC[REAL_ADD_RDISTRIB; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; GSYM SUM_LMUL; REAL_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE
   `((0 <= i /\ i <= SUC n) /\ i <= n <=> 0 <= i /\ i <= n) /\
    ((0 <= i /\ i <= SUC n) /\ ~(i = 0) <=> 1 <= i /\ i <= SUC n)`] THEN
  REWRITE_TAC[GSYM numseg] THEN
  REWRITE_TAC[MESON[num_CONV `1`; ADD1] `1..SUC n = 0+1..n+1`] THEN
  REWRITE_TAC[SUM_OFFSET; ADD_SUB; REAL_POW_ADD] THEN
  BINOP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN REAL_ARITH_TAC);;

let COFACTOR_ENTRY_AS_POLYFUN = prove
 (`!A:real^N^N x i j.
        1 <= i /\ i <= dimindex(:N) /\
        1 <= j /\ j <= dimindex(:N)
        ==> ?c. !x. cofactor(A - x %% mat 1)$i$j =
                    sum(0..dimindex(:N)-1) (\i. c(i) * x pow i)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[cofactor; LAMBDA_BETA; det] THEN
  MATCH_MP_TAC POLYFUN_N_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN
  SUBGOAL_THEN `1..dimindex(:N) = i INSERT ((1..dimindex(:N)) DELETE i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN ASM_ARITH_TAC;
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG]] THEN
  ASM_REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN
  MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
  SIMP_TAC[CARD_DELETE; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[IN_NUMSEG; IN_DELETE; CARD_NUMSEG_1; LE_REFL] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(p:num->num) k = j` THEN ASM_REWRITE_TAC[] THENL
   [REPEAT(EXISTS_TAC `&0`) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `a - x * d:real = a + (--d) * x`] THEN MESON_TAC[]);;

let DETERMINANT_AS_POLYFUN = prove
 (`!A:real^N^N.
        ?c. !x. det(A - x %% mat 1) =
                sum(0..dimindex(:N)) (\i. c(i) * x pow i)`,
  GEN_TAC THEN REWRITE_TAC[det] THEN
  MATCH_MP_TAC POLYFUN_N_SUM THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `p:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC POLYFUN_N_CMUL THEN MATCH_MP_TAC POLYFUN_N_PRODUCT THEN
  SIMP_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; LE_REFL; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->num) k IN 1..dimindex(:N)` MP_TAC THENL
   [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LAMBDA_BETA] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_SUB_COMPONENT; MATRIX_CMUL_COMPONENT; MAT_COMPONENT] THEN
  REWRITE_TAC[REAL_ARITH `a - x * d:real = a + (--d) * x`] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence define characteristic polynomial coefficients.                      *)
(* ------------------------------------------------------------------------- *)

let char_poly = new_specification ["char_poly"]
  (REWRITE_RULE[SKOLEM_THM] DETERMINANT_AS_POLYFUN);;

(* ------------------------------------------------------------------------- *)
(* Now the Cayley-Hamilton proof.                                            *)
(* ------------------------------------------------------------------------- *)

let COFACTOR_AS_MATRIC_POLYNOMIAL = prove
 (`!A:real^N^N. ?C.
      !x. cofactor(A - x %% mat 1) =
          msum(0..dimindex(:N)-1) (\i. x pow i %% C i)`,
  GEN_TAC THEN SIMP_TAC[CART_EQ; MSUM_COMPONENT; FINITE_NUMSEG] THEN
  MP_TAC(ISPEC `A:real^N^N` COFACTOR_ENTRY_AS_POLYFUN) THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IMP_IMP] THEN REWRITE_TAC[LAMBDA_SKOLEM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(num->real)^N^N` ASSUME_TAC) THEN
  EXISTS_TAC `(\i. lambda j k. ((c:(num->real)^N^N)$j$k) i):num->real^N^N` THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `i:num`] THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MATRIX_CMUL_COMPONENT; LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let MATRIC_POWER_DIFFERENCE = prove
 (`!A:real^N^N x n.
        A mpow (SUC n) - x pow (SUC n) %% mat 1 =
        msum (0..n) (\i. x pow i %% A mpow (n - i)) ** (A - x %% mat 1)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MSUM_CLAUSES_NUMSEG; real_pow; SUB_0; mpow] THEN
    REWRITE_TAC[MATRIX_MUL_RID; MATRIX_CMUL_LID; MATRIX_MUL_LID] THEN
    REWRITE_TAC[REAL_MUL_RID];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `(A mpow SUC n - x pow SUC n %% mat 1) ** A +
      (x pow (SUC n) %% mat 1 :real^N^N) ** (A - x %% mat 1:real^N^N)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MPOW_SUC] THEN
      REWRITE_TAC[MATRIX_SUB_RDISTRIB; MATRIX_SUB_LDISTRIB] THEN
      REWRITE_TAC[MATRIX_SUB; MATRIX_MUL_LMUL; MATRIX_MUL_LID] THEN
      REWRITE_TAC[GSYM MATRIX_ADD_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MATRIX_ADD_ASSOC; MATRIX_ADD_LNEG; MATRIX_ADD_LID] THEN
      REWRITE_TAC[real_pow; MATRIX_CMUL_ASSOC] THEN REWRITE_TAC[REAL_MUL_AC];

      ASM_REWRITE_TAC[MSUM_CLAUSES_NUMSEG; LE_0] THEN
      REWRITE_TAC[SUB_REFL; mpow; MATRIX_ADD_RDISTRIB] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[GSYM MSUM_MATRIX_RMUL; FINITE_NUMSEG] THEN
      MATCH_MP_TAC MSUM_EQ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[MATRIX_MUL_LMUL] THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `i <= n ==> SUC n - i = SUC(n - i)`] THEN
      REWRITE_TAC[MPOW_SUC; GSYM MATRIX_MUL_ASSOC] THEN AP_TERM_TAC THEN
      REWRITE_TAC[MATRIX_SUB_LDISTRIB; MATRIX_SUB_RDISTRIB] THEN
      REWRITE_TAC[MATRIX_MUL_RMUL; MATRIX_MUL_LMUL] THEN
      REWRITE_TAC[MATRIX_MUL_LID; MATRIX_MUL_RID]]]);;

let MATRIC_CHARPOLY_DIFFERENCE = prove
 (`!A:real^N^N. ?B.
      !x. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) -
          sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1 =
          msum(0..(dimindex(:N)-1)) (\i. x pow i %% B i) ** (A - x %% mat 1)`,
  GEN_TAC THEN SPEC_TAC(`dimindex(:N)`,`n:num`) THEN
  SPEC_TAC(`char_poly(A:real^N^N)`,`c:num->real`) THEN
  GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[MSUM_CLAUSES_NUMSEG; SUM_CLAUSES_NUMSEG; LE_0] THENL
   [EXISTS_TAC `(\i. mat 0):num->real^N^N` THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[MSUM_CLAUSES_NUMSEG] THEN
    REWRITE_TAC[real_pow; MATRIX_MUL_LMUL; MATRIX_MUL_LZERO; mpow;
                REAL_MUL_RID; MATRIX_CMUL_RZERO; MATRIX_SUB_REFL];
    FIRST_X_ASSUM(X_CHOOSE_TAC `B:num->real^N^N`) THEN
    REWRITE_TAC[MATRIX_SUB; MATRIX_NEG_ADD; MATRIX_CMUL_ADD_RDISTRIB] THEN
    ONCE_REWRITE_TAC[AC MATRIX_ADD_AC
     `(A + B) + (C + D):real^N^N = (A + C) + (B + D)`] THEN
    ASM_REWRITE_TAC[GSYM MATRIX_SUB] THEN
    REWRITE_TAC[GSYM MATRIX_CMUL_ASSOC; GSYM MATRIX_CMUL_SUB_LDISTRIB] THEN
    REWRITE_TAC[MATRIC_POWER_DIFFERENCE; SUC_SUB1] THEN
    EXISTS_TAC `(\i. (if i <= n - 1 then B i else mat 0) +
                     c(SUC n) %% A mpow (n - i)):num->real^N^N` THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[MATRIX_CMUL_ADD_LDISTRIB] THEN
    SIMP_TAC[MSUM_ADD; FINITE_NUMSEG; MATRIX_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM MATRIX_MUL_LMUL] THEN
    BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THENL
     [REWRITE_TAC[COND_RAND; COND_RATOR; MATRIX_CMUL_RZERO] THEN
      REWRITE_TAC[GSYM MSUM_RESTRICT_SET; IN_NUMSEG] THEN
      REWRITE_TAC[numseg; ARITH_RULE
       `(0 <= i /\ i <= n) /\ i <= n - 1 <=> 0 <= i /\ i <= n - 1`];
      SIMP_TAC[GSYM MSUM_CMUL; FINITE_NUMSEG; MATRIX_CMUL_ASSOC] THEN
      REWRITE_TAC[REAL_MUL_SYM]]]);;

let CAYLEY_HAMILTON = prove
 (`!A:real^N^N. msum(0..dimindex(:N)) (\i. char_poly A i %% A mpow i) = mat 0`,
  GEN_TAC THEN MATCH_MP_TAC MATRIC_POLY_LEMMA THEN MATCH_MP_TAC(MESON[]
   `!g. (!x. g x = k) /\ (?a b c. !x. f a b c x = g x)
        ==> ?a b c. !x. f a b c x = k`) THEN
  EXISTS_TAC
   `\x. (msum(0..dimindex(:N)) (\i. char_poly A i %% (A:real^N^N) mpow i) -
         sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1) +
        sum(0..dimindex(:N)) (\i. char_poly A i * x pow i) %% mat 1` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MATRIX_SUB; GSYM MATRIX_ADD_ASSOC; MATRIX_ADD_LNEG] THEN
    REWRITE_TAC[MATRIX_ADD_RID];
    X_CHOOSE_THEN `B:num->real^N^N` (fun th -> ONCE_REWRITE_TAC[th])
     (ISPEC `A:real^N^N` MATRIC_CHARPOLY_DIFFERENCE) THEN
    REWRITE_TAC[GSYM char_poly; GSYM MATRIX_MUL_LEFT_COFACTOR] THEN
    REWRITE_TAC[GSYM MATRIX_ADD_RDISTRIB] THEN
    REWRITE_TAC[GSYM COFACTOR_TRANSP; TRANSP_MATRIX_SUB] THEN
    REWRITE_TAC[TRANSP_MATRIX_CMUL; TRANSP_MAT] THEN
    X_CHOOSE_THEN `C:num->real^N^N` (fun th -> ONCE_REWRITE_TAC[th])
     (ISPEC `transp A:real^N^N` COFACTOR_AS_MATRIC_POLYNOMIAL) THEN
    MAP_EVERY EXISTS_TAC
     [`A:real^N^N`; `(\i. B i + C i):num->real^N^N`; `dimindex(:N)-1`] THEN
    SIMP_TAC[GSYM MSUM_ADD; FINITE_NUMSEG; MATRIX_CMUL_ADD_LDISTRIB]]);;
