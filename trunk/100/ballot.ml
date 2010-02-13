(* ========================================================================= *)
(* Ballot problem.                                                           *)
(* ========================================================================= *)

needs "Library/binomial.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Restricted function space.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(13,"right"));;

let funspace = new_definition
 `(s --> t) = {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> f(x) = @y. T)}`;;

let FUNSPACE_EMPTY = prove
 (`({} --> t) = {(\x. @y. T)}`,
  REWRITE_TAC[EXTENSION; IN_SING; funspace; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REWRITE_TAC[FUN_EQ_THM]);;

let HAS_SIZE_FUNSPACE = prove
 (`!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)`,
  REWRITE_TAC[HAS_SIZE; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_RULES; FUNSPACE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[EXP; ARITH];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM HAS_SIZE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(x INSERT s) --> t =
        IMAGE (\(y:B,g) u:A. if u = x then y else g(u))
              {y,g | y IN t /\ g IN s --> t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; funspace; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> d /\ a /\ b /\ c`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    X_GEN_TAC `f:A->B` THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) x`; `\u. if u = x then @y. T else (f:A->B) u`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[IN_INSERT];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`y:B`; `g:A->B`] THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ d <=> d /\ a /\ b`] THEN
    REWRITE_TAC[PAIR_EQ; EXISTS_PAIR_THM; GSYM CONJ_ASSOC] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[FUN_EQ_THM; funspace; IN_ELIM_THM] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
    X_GEN_TAC `u:A` THEN ASM_CASES_TAC `u:A = x` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  MATCH_MP_TAC HAS_SIZE_PRODUCT THEN ASM_MESON_TAC[]);;

let FINITE_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE(s --> t)`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the problem.                                                *)
(* ------------------------------------------------------------------------- *)

let vote_INDUCT,vote_RECURSION = define_type
 "vote = A | B";;

let all_countings = new_definition
 `all_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b}`;;

let valid_countings = new_definition
 `valid_countings a b =
        let n = a + b in
        CARD {f | f IN (1..n --> {A,B}) /\
                  CARD { i | i IN 1..n /\ f(i) = A} = a /\
                  CARD { i | i IN 1..n /\ f(i) = B} = b /\
                  !m. 1 <= m /\ m <= n
                      ==> CARD { i | i IN 1..m /\ f(i) = A} >
                          CARD { i | i IN 1..m /\ f(i) = B}}`;;

(* ------------------------------------------------------------------------- *)
(* Various lemmas.                                                           *)
(* ------------------------------------------------------------------------- *)

let vote_CASES = cases "vote"
and vote_DISTINCT = distinctness "vote";;

let FINITE_COUNTINGS = prove
 (`FINITE {f | f IN (1..n --> {A,B}) /\ P f}`,
  MATCH_MP_TAC FINITE_RESTRICT THEN
  MATCH_MP_TAC FINITE_FUNSPACE THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_INSERT; FINITE_RULES]);;

let UNIV_VOTE = prove
 (`(:vote) = {A,B}`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY; vote_CASES]);;

let ADD1_NOT_IN_NUMSEG = prove
 (`!m n. ~((n + 1) IN m..n)`,
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let NUMSEG_1_CLAUSES = prove
 (`!n. 1..(n+1) = (n + 1) INSERT (1..n)`,
  REWRITE_TAC[GSYM ADD1; NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC n`]);;

let NUMSEG_RESTRICT_SUC = prove
 (`{i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then (n + 1) INSERT {i | i IN 1..n /\ P i}
        else {i | i IN 1..n /\ P i}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; NUMSEG_1_CLAUSES; IN_INSERT] THEN
  ASM_MESON_TAC[ADD1_NOT_IN_NUMSEG]);;

let CARD_NUMSEG_RESTRICT_SUC = prove
 (`CARD {i | i IN 1..(n+1) /\ P i} =
        if P(n + 1) then CARD {i | i IN 1..n /\ P i} + 1
        else CARD {i | i IN 1..n /\ P i}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NUMSEG_RESTRICT_SUC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[IN_ELIM_THM; ADD1_NOT_IN_NUMSEG; ADD1]);;

let FORALL_RANGE_SUC = prove
 (`(!i. 1 <= i /\ i <= n + 1 ==> P i) <=>
      P(n + 1) /\ (!i. 1 <= i /\ i <= n ==> P i)`,
  REWRITE_TAC[ARITH_RULE `i <= n + 1 <=> i <= n \/ i = n + 1`] THEN
  MESON_TAC[ARITH_RULE `1 <= n + 1`]);;

let IN_NUMSEG_RESTRICT_FALSE = prove
 (`m <= n
   ==> (i IN 1..m /\ (if i = n + 1 then p i else q i) <=> i IN 1..m /\ q i)`,
  REWRITE_TAC[IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `i <= m /\ m <= n ==> ~(i = n + 1)`]);;

let CARD_NUMSEG_RESTRICT_EXTREMA = prove
 (`(CARD {i | i IN 1..n /\ P i} = n <=> !i. 1 <= i /\ i <= n ==> P i) /\
   (CARD {i | i IN 1..n /\ P i} = 0 <=> !i. 1 <= i /\ i <= n ==> ~(P i))`,
  SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL [`{i | i IN 1..n /\ P i}`; `1..n`] SUBSET_CARD_EQ) THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; CARD_NUMSEG_1] THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_NUMSEG; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let VOTE_NOT_EQ = prove
 (`(!x. ~(x = A) <=> x = B) /\
   (!x. ~(x = B) <=> x = A)`,
  MESON_TAC[vote_CASES; vote_DISTINCT]);;

let FUNSPACE_FIXED = prove
 (`{f | f IN (s --> t) /\ (!i. i IN s ==> f i = a)} =
   if s = {} \/ a IN t then {(\i. if i IN s then a else @x. T)} else {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN GEN_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; funspace; NOT_IN_EMPTY; IN_SING] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[]);;

let COUNTING_LEMMA = prove
 (`CARD {f | f IN (1..(n+1) --> {A,B}) /\ P f} =
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then A else f i)} +
   CARD {f | f IN (1..n --> {A,B}) /\ P (\i. if i = n + 1 then B else f i)}`,
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = A /\ P f} +
              CARD {f | f IN (1..(n+1) --> {A,B}) /\ f(n+1) = B /\ P f}` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_UNION_EQ THEN
    REWRITE_TAC[FINITE_COUNTINGS; EXTENSION; IN_INTER; IN_UNION] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[vote_CASES; vote_DISTINCT];
    ALL_TAC] THEN
  BINOP_TAC THEN
  MATCH_MP_TAC BIJECTIONS_CARD_EQ THEN
  EXISTS_TAC `\f i. if i = n + 1 then @x:vote. T else f i` THENL
   [EXISTS_TAC `\f i. if i = n + 1 then A else f i`;
    EXISTS_TAC `\f i. if i = n + 1 then B else f i`] THEN
  REWRITE_TAC[FINITE_COUNTINGS] THEN
  REWRITE_TAC[IN_ELIM_THM; funspace; GSYM UNIV_VOTE; IN_UNIV] THEN
  REWRITE_TAC[NUMSEG_1_CLAUSES; IN_INSERT] THEN REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
   `P x ==> x = y ==> P y`))) THEN
  TRY(GEN_REWRITE_TAC I [FUN_EQ_THM]) THEN ASM_MESON_TAC[ADD1_NOT_IN_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Recurrence relations.                                                     *)
(* ------------------------------------------------------------------------- *)

let ALL_COUNTINGS_0 = prove
 (`!a. all_countings a 0 = 1 /\ all_countings 0 a = 1`,
  REWRITE_TAC[all_countings; CARD_NUMSEG_RESTRICT_EXTREMA; GSYM IN_NUMSEG;
              LET_DEF; LET_END_DEF; ADD_CLAUSES; VOTE_NOT_EQ] THEN
  REWRITE_TAC[FUNSPACE_FIXED; IN_INSERT] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH_SUC]);;

let VALID_COUNTINGS_0 = prove
 (`valid_countings 0 0 = 1 /\
   !a. valid_countings (SUC a) 0 = 1 /\ valid_countings 0 (SUC a) = 0`,
  let lemma = prove
   (`{x} INTER s = if x IN s then {x} else {}`,
    COND_CASES_TAC THEN ASM SET_TAC[]) in
  REWRITE_TAC[valid_countings; CARD_NUMSEG_RESTRICT_EXTREMA; GSYM IN_NUMSEG;
              LET_DEF; LET_END_DEF; ADD_CLAUSES; VOTE_NOT_EQ;
              TAUT `a /\ a /\ b <=> a /\ b`] THEN
  REWRITE_TAC[CONJUNCT1 NUMSEG_CLAUSES; ARITH_EQ; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[funspace; IN_ELIM_THM; NOT_IN_EMPTY; GSYM FUN_EQ_THM] THEN
    REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SET_RULE `{x | P x /\ Q x /\ R x} =
                             {x | P x /\ Q x} INTER {x | R x}`] THEN
  REWRITE_TAC[FUNSPACE_FIXED; IN_INSERT; lemma] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  GEN_TAC THEN CONJ_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[NOT_FORALL_THM] THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `b = 0 /\ ~(a = 0) ==> a > b`) THEN
    ASM_SIMP_TAC[CARD_NUMSEG_RESTRICT_EXTREMA] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `1 <= k /\ k <= a ==> 1 <= k /\ !i. i <= k ==> i <= a`)) THEN
    ASM_SIMP_TAC[IN_NUMSEG; vote_DISTINCT] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    EXISTS_TAC `1` THEN REWRITE_TAC[NUMSEG_SING; IN_SING] THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    MATCH_MP_TAC(ARITH_RULE `b = 0 /\ ~(a = 0) ==> ~(b > a)`) THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | x = a /\ P x} = {x | x = a /\ P a}`] THEN
    REWRITE_TAC[IN_NUMSEG; LE_REFL; ARITH_RULE `1 <= SUC n`] THEN
    SIMP_TAC[vote_DISTINCT; SET_RULE `{x | F} = {} /\ {x | x = a} = {a}`;
             CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; ARITH]]);;

let ALL_COUNTINGS_SUC = prove
 (`!a b. all_countings (a + 1) (b + 1) =
                all_countings a (b + 1) + all_countings (a + 1) b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[all_countings] THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + (b + 1) = (a + b + 1) + 1`) THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + b = a + b + 1`) THEN
  ABBREV_TAC `n = a + b + 1` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTING_LEMMA] THEN
  REWRITE_TAC[] THEN BINOP_TAC THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[vote_DISTINCT] THEN
  REWRITE_TAC[CARD_NUMSEG_RESTRICT_SUC] THEN
  SIMP_TAC[IN_NUMSEG_RESTRICT_FALSE; LE_REFL; EQ_ADD_RCANCEL]);;

let VALID_COUNTINGS_SUC = prove
 (`!a b. valid_countings (a + 1) (b + 1) =
                if a <= b then 0
                else valid_countings a (b + 1) + valid_countings (a + 1) b`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `b:num < a` THEN ASM_REWRITE_TAC[GSYM NOT_LT] THEN
  REWRITE_TAC[valid_countings] THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + (b + 1) = (a + b + 1) + 1`) THEN
  SUBST1_TAC(ARITH_RULE `(a + 1) + b = a + b + 1`) THEN
  ABBREV_TAC `n = a + b + 1` THEN
  CONV_TAC(ONCE_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [COUNTING_LEMMA] THEN REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[vote_DISTINCT] THEN
  REWRITE_TAC[FORALL_RANGE_SUC] THEN
  REWRITE_TAC[CARD_NUMSEG_RESTRICT_SUC] THEN
  SIMP_TAC[IN_NUMSEG_RESTRICT_FALSE; LE_REFL; EQ_ADD_RCANCEL] THEN
  SIMP_TAC[MESON[] `x = a /\ y = b /\ P x y <=> x = a /\ y = b /\ P a b`] THEN
  ASM_REWRITE_TAC[GT; LT_ADD_RCANCEL] THEN
  REWRITE_TAC[SET_RULE `{x | F} = EMPTY`; CARD_CLAUSES; ADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Main result.                                                              *)
(* ------------------------------------------------------------------------- *)

let ALL_COUNTINGS = prove
 (`!a b. all_countings a b = binom(a + b,a)`,
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; BINOM_REFL; binom; ALL_COUNTINGS_0] THEN
  INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; BINOM_REFL; binom; ALL_COUNTINGS_0] THEN
  REWRITE_TAC[ARITH_RULE `1 = a + 1 <=> a = 0`; BINOM_EQ_0;
              ARITH_RULE `a < SUC a`] THEN
  REWRITE_TAC[ALL_COUNTINGS_SUC; ADD1] THEN
  ASM_REWRITE_TAC[binom; GSYM ADD1] THEN
  REWRITE_TAC[ADD_CLAUSES; ADD_AC]);;

let VALID_COUNTINGS = prove
 (`!a b. (a + b) * valid_countings a b = (a - b) * binom(a + b,a)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[VALID_COUNTINGS_0; SUB_0; MULT_CLAUSES] THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[VALID_COUNTINGS_0; MULT_CLAUSES; ADD_CLAUSES];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[VALID_COUNTINGS_0; ADD_CLAUSES; BINOM_REFL; SUB_0];
    ALL_TAC] THEN
  REWRITE_TAC[ADD1; VALID_COUNTINGS_SUC] THEN REWRITE_TAC[GSYM ADD1] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ARITH_RULE `a <= b ==> SUC a - SUC b = 0`] THEN
  MATCH_MP_TAC(NUM_RING
   `~(a + b + 1 = 0) /\
    (SUC a + SUC b) * 
    ((SUC a + b) * (a + SUC b) * y + (a + SUC b) * (SUC a + b) * z) =
    (SUC a + b) * (a + SUC b) * w
    ==> (SUC a + SUC b) * (y + z) = w`) THEN
  ASM_REWRITE_TAC[ADD_EQ_0; ARITH] THEN
  MP_TAC(SPECL [`SUC b`; `a:num`] BINOM_FACT) THEN
  MP_TAC(SPECL [`b:num`; `SUC a`] BINOM_FACT) THEN
  MP_TAC(SPECL [`SUC b`; `SUC a`] BINOM_FACT) THEN
  REWRITE_TAC[ADD_CLAUSES; FACT] THEN
  SUBST1_TAC(ARITH_RULE `b + a:num = a + b`) THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t FACT_LT))
   [`a:num`; `b:num`; `a + b:num`] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
    GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_SUB; REAL_OF_NUM_LE; LT_NZ;
    ARITH_RULE `~(a <= b) ==> b <= SUC a /\ SUC b <= a /\ SUC b <= SUC a`] THEN
  CONV_TAC REAL_RING);;

let BALLOT = prove
 (`!a b. &(valid_countings a b) =
            if a <= b then if b = 0 then &1 else &0
            else (&a - &b) / (&a + &b) *  &(all_countings a b)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[ALL_COUNTINGS_0; VALID_COUNTINGS_0] THEN
  REWRITE_TAC[LE_REFL; REAL_MUL_LID; LE_0; NOT_SUC; CONJUNCT1 LE] THEN
  SIMP_TAC[REAL_ADD_RID; REAL_SUB_RZERO; REAL_DIV_REFL; REAL_OF_NUM_EQ;
           NOT_SUC; REAL_MUL_LID] THEN
  MP_TAC(SPECL [`SUC a`; `SUC b`] VALID_COUNTINGS) THEN
  REWRITE_TAC[GSYM ALL_COUNTINGS; LE_SUC] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `a <= b ==> (SUC a - SUC b) = 0`] THEN
  REWRITE_TAC[MULT_EQ_0; MULT_CLAUSES; ADD_EQ_0; NOT_SUC; REAL_OF_NUM_EQ] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD;
               GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_SUB;
               ARITH_RULE `~(a <= b) ==> SUC b <= SUC a`] THEN
  CONV_TAC REAL_FIELD);;
