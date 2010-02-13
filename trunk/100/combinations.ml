(* ========================================================================= *)
(* Binomial coefficients and relation to number of combinations.             *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Binomial coefficients.                                                    *)
(* ------------------------------------------------------------------------- *)

let binom = define
  `(!n. binom(n,0) = 1) /\
   (!k. binom(0,SUC(k)) = 0) /\
   (!n k. binom(SUC(n),SUC(k)) = binom(n,SUC(k)) + binom(n,k))`;;

let BINOM_LT = prove
 (`!n k. n < k ==> (binom(n,k) = 0)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC[binom; ARITH; LT_SUC; LT] THEN
  ASM_SIMP_TAC[ARITH_RULE `n < k ==> n < SUC(k)`; ARITH]);;

let BINOM_REFL = prove
 (`!n. binom(n,n) = 1`,
  INDUCT_TAC THEN ASM_SIMP_TAC[binom; BINOM_LT; LT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Usual "factorial" definition.                                             *)
(* ------------------------------------------------------------------------- *)

let BINOM_FACT = prove
 (`!n k. FACT n * FACT k * binom(n+k,k) = FACT(n + k)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; ADD_CLAUSES; MULT_CLAUSES; BINOM_REFL] THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; FACT; MULT_CLAUSES; binom] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; FACT; binom] THEN CONV_TAC NUM_RING);;

let BINOM_EXPLICIT = prove
 (`!n k. binom(n,k) = 
            if n < k then 0 else FACT(n) DIV (FACT(k) * FACT(n - k))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[BINOM_LT] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_LT; LE_EXISTS] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[ADD_SUB2] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN 
  SIMP_TAC[LT_MULT; FACT_LT; ADD_CLAUSES] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[GSYM BINOM_FACT] THEN
  REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* A tedious lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let lemma = prove
 (`~(a IN t)
   ==> {u | u SUBSET (a:A INSERT t) /\ u HAS_SIZE (SUC m)} =
       {u | u SUBSET t /\ u HAS_SIZE (SUC m)} UNION
       IMAGE (\u. a INSERT u) {u | u SUBSET t /\ u HAS_SIZE m}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `u:A->bool` THEN
  ASM_CASES_TAC `(u:A->bool) SUBSET t` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `(u:A->bool) HAS_SIZE (SUC m)` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `u DELETE (a:A)`  THEN
    REPEAT (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_SIZE_SUC]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC) THEN ASM SET_TAC[];
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE_CLAUSES] THEN
    EXISTS_TAC `a:A` THEN EXISTS_TAC `x':A->bool` THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The "number of combinations" formula.                                     *)
(* ------------------------------------------------------------------------- *)

let BINOM_INDUCT = prove
 (`!P. (!n. P n 0) /\       
       (!k. P 0 (SUC k)) /\                
       (!n k. P n (SUC k) /\ P n k ==> P (SUC n) (SUC k))
       ==> !m n. P m n`,                                                       
  GEN_TAC THEN STRIP_TAC THEN REPEAT INDUCT_TAC THEN ASM_MESON_TAC[]);;     

let NUMBER_OF_COMBINATIONS = prove
 (`!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)`,
  MATCH_MP_TAC BINOM_INDUCT THEN REWRITE_TAC[binom] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC HAS_SIZE_CONV THEN
    EXISTS_TAC `{}:A->bool` THEN SIMP_TAC[EXTENSION; IN_SING; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_IN_EMPTY; HAS_SIZE_0] THEN SET_TAC[];
    SIMP_TAC[HAS_SIZE_0; SUBSET_EMPTY; HAS_SIZE_SUC] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `m:num`] THEN STRIP_TAC THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_SIZE_CLAUSES] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[lemma] THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `~(a:A IN t)` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; HAS_SIZE_SUC] THEN
  UNDISCH_TAC `~(a:A IN t)` THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Explicit version.                                                         *)
(* ------------------------------------------------------------------------- *)

let NUMBER_OF_COMBINATIONS_EXPLICIT = prove                                     
 (`!n m s:A->bool.                                                     
        s HAS_SIZE n                                                   
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE
            (if n < m then 0 else FACT(n) DIV (FACT(m) * FACT(n - m)))`,
  REWRITE_TAC[REWRITE_RULE[BINOM_EXPLICIT] NUMBER_OF_COMBINATIONS]);;
