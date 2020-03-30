(* ========================================================================= *)
(* Products of natural numbers and real numbers.                             *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Products over natural numbers.                                            *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_SUPPORT = prove
 (`!f s. nproduct (support ( * ) f s) f = nproduct s f`,
  REWRITE_TAC[nproduct; ITERATE_SUPPORT]);;

let NPRODUCT_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (nproduct (s UNION t) f = nproduct s f * nproduct t f)`,
  SIMP_TAC[nproduct; ITERATE_UNION; MONOIDAL_MUL]);;

let NPRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
           ==> (nproduct (IMAGE f s) g = nproduct s (g o f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_INJECTION = prove
 (`!f p s. FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
           ==> nproduct s (f o p) = nproduct s f`,
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_ADD_SPLIT = prove
 (`!f m n p.
        m <= n + 1
        ==> (nproduct (m..(n+p)) f = nproduct(m..n) f * nproduct(n+1..n+p) f)`,
  SIMP_TAC[NUMSEG_ADD_SPLIT; NPRODUCT_UNION; DISJOINT_NUMSEG; FINITE_NUMSEG;
           ARITH_RULE `x < x + 1`]);;

let NPRODUCT_POS_LT = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> 0 < f x) ==> 0 < nproduct s f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; ARITH; IN_INSERT; LT_MULT]);;

let NPRODUCT_POS_LT_NUMSEG = prove
 (`!f m n. (!x. m <= x /\ x <= n ==> 0 < f x) ==> 0 < nproduct(m..n) f`,
  SIMP_TAC[NPRODUCT_POS_LT; FINITE_NUMSEG; IN_NUMSEG]);;

let NPRODUCT_OFFSET = prove
 (`!f m p. nproduct(m+p..n+p) f = nproduct(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; NPRODUCT_IMAGE;
           EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let NPRODUCT_SING = prove
 (`!f x. nproduct {x} f = f(x)`,
  SIMP_TAC[NPRODUCT_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; MULT_CLAUSES]);;

let NPRODUCT_SING_NUMSEG = prove
 (`!f n. nproduct(n..n) f = f(n)`,
  REWRITE_TAC[NUMSEG_SING; NPRODUCT_SING]);;

let NPRODUCT_CLAUSES_NUMSEG = prove
 (`(!m. nproduct(m..0) f = if m = 0 then f(0) else 1) /\
   (!m n. nproduct(m..SUC n) f = if m <= SUC n then nproduct(m..n) f * f(SUC n)
                                else nproduct(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_SING; NPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; MULT_AC]);;

let NPRODUCT_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> nproduct s f = nproduct s g`,
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (nproduct(m..n) f = nproduct(m..n) g)`,
  MESON_TAC[NPRODUCT_EQ; FINITE_NUMSEG; IN_NUMSEG]);;

let NPRODUCT_EQ_0 = prove
 (`!f s. FINITE s ==> (nproduct s f = 0 <=> ?x. x IN s /\ f(x) = 0)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; MULT_EQ_0; IN_INSERT; ARITH; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let NPRODUCT_EQ_0_NUMSEG = prove
 (`!f m n. nproduct(m..n) f = 0 <=> ?x. m <= x /\ x <= n /\ f(x) = 0`,
  SIMP_TAC[NPRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG; GSYM CONJ_ASSOC]);;

let NPRODUCT_RESTRICT = prove
 (`!f s. FINITE s
         ==> nproduct s (\i. if i IN s then f i else 1) = nproduct s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_EQ THEN ASM_SIMP_TAC[]);;

let NPRODUCT_RESTRICT_SET = prove
 (`!P s f. nproduct {i:A | i IN s /\ P i} f =
           nproduct s (\i. if P i then f i else 1)`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> f(x) <= g(x))
         ==> nproduct s f <= nproduct s g`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IN_INSERT; NPRODUCT_CLAUSES; NOT_IN_EMPTY; LE_REFL] THEN
  MESON_TAC[LE_MULT2; LE_0]);;

let NPRODUCT_LE_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> f(i) <= g(i))
           ==> nproduct(m..n) f <= nproduct(m..n) g`,
  SIMP_TAC[NPRODUCT_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let NPRODUCT_EQ_1 = prove
 (`!f s. (!x:A. x IN s ==> f(x) = 1) ==> nproduct s f = 1`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_MUL]);;

let NPRODUCT_EQ_1_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> f(i) = 1) ==> nproduct(m..n) f = 1`,
  SIMP_TAC[NPRODUCT_EQ_1; IN_NUMSEG]);;

let NPRODUCT_MUL_GEN = prove
 (`!f g s.
       FINITE {x | x IN s /\ ~(f x = 1)} /\ FINITE {x | x IN s /\ ~(g x = 1)}
       ==> nproduct s (\x. f x * g x) = nproduct s f * nproduct s g`,
  REWRITE_TAC[GSYM NEUTRAL_MUL; GSYM support; nproduct] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_MUL);;

let NPRODUCT_MUL = prove
 (`!f g s. FINITE s
           ==> nproduct s (\x. f x * g x) = nproduct s f * nproduct s g`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; MULT_AC; MULT_CLAUSES]);;

let NPRODUCT_MUL_NUMSEG = prove
 (`!f g m n.
     nproduct(m..n) (\x. f x * g x) = nproduct(m..n) f * nproduct(m..n) g`,
  SIMP_TAC[NPRODUCT_MUL; FINITE_NUMSEG]);;

let NPRODUCT_CONST = prove
 (`!c s. FINITE s ==> nproduct s (\x. c) = c EXP (CARD s)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; CARD_CLAUSES; EXP]);;

let NPRODUCT_CONST_NUMSEG = prove
 (`!c m n. nproduct (m..n) (\x. c) = c EXP ((n + 1) - m)`,
  SIMP_TAC[NPRODUCT_CONST; CARD_NUMSEG; FINITE_NUMSEG]);;

let NPRODUCT_CONST_NUMSEG_1 = prove
 (`!c n. nproduct(1..n) (\x. c) = c EXP n`,
  SIMP_TAC[NPRODUCT_CONST; CARD_NUMSEG_1; FINITE_NUMSEG]);;

let NPRODUCT_ONE = prove
 (`!s. nproduct s (\n. 1) = 1`,
  SIMP_TAC[NPRODUCT_EQ_1]);;

let NPRODUCT_CLOSED = prove
 (`!P f:A->num s.
        P(1) /\ (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nproduct s f)`,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC `P:num->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_MUL; GSYM nproduct]);;

let NPRODUCT_RELATED = prove
 (`!R (f:A->num) g s.
        R 1 1 /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m * m') (n * n')) /\
        FINITE s /\ (!i. i IN s ==> R (f i) (g i))
        ==> R (nproduct s f) (nproduct s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:num->num->bool`
    (MATCH_MP ITERATE_RELATED MONOIDAL_MUL)) THEN
  ASM_REWRITE_TAC[GSYM nproduct; NEUTRAL_MUL] THEN ASM_MESON_TAC[]);;

let NPRODUCT_CLOSED_NONEMPTY = prove
 (`!P f:A->num s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(nproduct s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC `P:num->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_MUL; GSYM nproduct]);;

let NPRODUCT_RELATED_NONEMPTY = prove
 (`!R (f:A->num) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m * m') (n * n')) /\
        FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> R (f i) (g i))
        ==> R (nproduct s f) (nproduct s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:num->num->bool`
    (MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_MUL)) THEN
  ASM_REWRITE_TAC[GSYM nproduct; NEUTRAL_MUL] THEN ASM_MESON_TAC[]);;

let NPRODUCT_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> nproduct(m..n) f = f(m) * nproduct(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; NPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let NPRODUCT_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> nproduct(m..n) f = nproduct(m..n-1) f * f(n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; NPRODUCT_CLAUSES_NUMSEG; SUC_SUB1]);;

let NPRODUCT_SUPERSET = prove
 (`!f:A->num u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f(x) = 1)
        ==> nproduct v f = nproduct u f`,
  SIMP_TAC[nproduct; GSYM NEUTRAL_MUL; ITERATE_SUPERSET; MONOIDAL_MUL]);;

let NPRODUCT_UNIV = prove
 (`!f:A->num s.
        support ( * ) f (:A) SUBSET s ==> nproduct s f = nproduct (:A) f`,
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_UNIV THEN
  REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_PAIR = prove
 (`!f m n. nproduct(2*m..2*n+1) f = nproduct(m..n) (\i. f(2*i) * f(2*i+1))`,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_MUL) THEN
  REWRITE_TAC[nproduct; NEUTRAL_MUL]);;

let NPRODUCT_REFLECT = prove
 (`!x m n. nproduct(m..n) x =
           if n < m then 1 else nproduct(0..n-m) (\i. x(n - i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nproduct] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP ITERATE_REFLECT MONOIDAL_MUL] THEN
  REWRITE_TAC[NEUTRAL_MUL]);;

let NPRODUCT_DELETE = prove
 (`!f s a. FINITE s /\ a IN s
           ==> f(a) * nproduct(s DELETE a) f = nproduct s f`,
  SIMP_TAC[nproduct; ITERATE_DELETE; MONOIDAL_MUL]);;

let NPRODUCT_FACT = prove
 (`!n. nproduct(1..n) (\m. m) = FACT n`,
  INDUCT_TAC THEN REWRITE_TAC[NPRODUCT_CLAUSES_NUMSEG; FACT; ARITH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`; MULT_SYM]);;

let NPRODUCT_DELTA = prove
 (`!s a. nproduct s (\x. if x = a then b else 1) =
         (if a IN s then b else 1)`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  SIMP_TAC[ITERATE_DELTA; MONOIDAL_MUL]);;

let HAS_SIZE_CART = prove
 (`!P m. (!i. 1 <= i /\ i <= dimindex(:N) ==> {x | P i x} HAS_SIZE m i)
         ==> {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)}
             HAS_SIZE nproduct (1..dimindex(:N)) m`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. n <= dimindex(:N)
        ==> {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                          ==> P i (v$i)) /\
                     (!i. 1 <= i /\ i <= dimindex(:N) /\ n < i
                          ==> v$i = @x. F)}
            HAS_SIZE nproduct(1..n) m`
    (MP_TAC o SPEC `dimindex(:N)`) THEN REWRITE_TAC[LE_REFL; LET_ANTISYM] THEN
  INDUCT_TAC THEN REWRITE_TAC[NPRODUCT_CLAUSES_NUMSEG; ARITH_EQ] THENL
   [REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= n /\ i <= 0 <=> F`] THEN
    SIMP_TAC[ARITH_RULE `1 <= i /\ i <= n /\ 0 < i <=> 1 <= i /\ i <= n`] THEN
    SUBGOAL_THEN
     `{v | !i. 1 <= i /\ i <= dimindex (:N) ==> v$i = (@x. F)} =
      {(lambda i. @x. F):A^N}`
     (fun th -> SIMP_TAC[th; HAS_SIZE; FINITE_SING; CARD_SING]) THEN
    SIMP_TAC[EXTENSION; IN_SING; IN_ELIM_THM; CART_EQ; LAMBDA_BETA];
    DISCH_TAC] THEN
  MATCH_MP_TAC(MESON[] `!t. t = s /\ t HAS_SIZE n ==> s HAS_SIZE n`) THEN
  EXISTS_TAC
   `IMAGE (\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)
          {x,v | x IN {x:A | P (SUC n) x} /\
                 v IN {v:A^N | (!i. 1 <= i /\ i <= dimindex(:N) /\ i <= n
                                ==> P i (v$i)) /\
                           (!i. 1 <= i /\ i <= dimindex (:N) /\ n < i
                                ==> v$i = (@x. F))}}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA] THEN
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[LT_REFL] THEN
      TRY ASM_ARITH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_PAIR_THM; EXISTS_PAIR_THM] THEN
      X_GEN_TAC `v:A^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN EXISTS_TAC `(v:A^N)$(SUC n)` THEN
      EXISTS_TAC `(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N` THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA; ARITH_RULE `i <= n ==> ~(i = SUC n)`] THEN
      ASM_MESON_TAC[LE; ARITH_RULE `1 <= SUC n`;
                    ARITH_RULE `n < i /\ ~(i = SUC n) ==> SUC n < i`]];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[IMP_IMP; PAIR_EQ; CART_EQ] THEN
      SIMP_TAC[LAMBDA_BETA] THEN
      X_GEN_TAC `a:A` THEN DISCH_TAC THEN X_GEN_TAC `v:A^N` THEN STRIP_TAC THEN
      X_GEN_TAC `b:A` THEN DISCH_TAC THEN X_GEN_TAC `w:A^N` THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `SUC n`)) THEN
        ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`];
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
        ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(n:num) < i` THEN
        ASM_REWRITE_TAC[GSYM NOT_LT] THEN
        TRY ASM_ARITH_TAC THEN ASM_MESON_TAC[]];
      REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
      GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
      MATCH_MP_TAC HAS_SIZE_PRODUCT THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]]);;

let CARD_CART = prove
 (`!P. (!i. 1 <= i /\ i <= dimindex(:N) ==> FINITE {x | P i x})
       ==> CARD {v:A^N | !i. 1 <= i /\ i <= dimindex(:N) ==> P i (v$i)} =
           nproduct (1..dimindex(:N)) (\i. CARD {x | P i x})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[HAS_SIZE] `s HAS_SIZE n ==> CARD s = n`) THEN
  MATCH_MP_TAC HAS_SIZE_CART THEN
  ASM_REWRITE_TAC[GSYM FINITE_HAS_SIZE]);;

let th = prove
   (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
                ==> nproduct s (\i. f(i)) = nproduct s g) /\
     (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
                ==> nproduct(a..b) (\i. f(i)) = nproduct(a..b) g) /\
     (!f g p.   (!x. p x ==> f x = g x)
                ==> nproduct {y | p y} (\i. f(i)) = nproduct {y | p y} g)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
    extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Now products over integers.                                               *)
(* ------------------------------------------------------------------------- *)

let IPRODUCT_SUPPORT = prove
 (`!f s. iproduct (support ( * ) f s) f = iproduct s f`,
  REWRITE_TAC[iproduct; ITERATE_SUPPORT]);;

let IPRODUCT_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (iproduct (s UNION t) f = iproduct s f * iproduct t f)`,
  SIMP_TAC[iproduct; ITERATE_UNION; MONOIDAL_INT_MUL]);;

let IPRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
           ==> (iproduct (IMAGE f s) g = iproduct s (g o f))`,
  REWRITE_TAC[iproduct; GSYM NEUTRAL_INT_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_INT_MUL]);;

let IPRODUCT_INJECTION = prove
 (`!f p s. FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
           ==> iproduct s (f o p) = iproduct s f`,
  REWRITE_TAC[iproduct] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_INT_MUL]);;

let IPRODUCT_ADD_SPLIT = prove
 (`!f m n p.
        m <= n + 1
        ==> (iproduct (m..(n+p)) f = iproduct(m..n) f * iproduct(n+1..n+p) f)`,
  SIMP_TAC[NUMSEG_ADD_SPLIT; IPRODUCT_UNION; DISJOINT_NUMSEG; FINITE_NUMSEG;
           ARITH_RULE `x < x + 1`]);;

let IPRODUCT_POS_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f x) ==> &0 <= iproduct s f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; INT_POS; IN_INSERT; INT_LE_MUL]);;

let IPRODUCT_POS_LE_NUMSEG = prove
 (`!f m n. (!x. m <= x /\ x <= n ==> &0 <= f x) ==> &0 <= iproduct(m..n) f`,
  SIMP_TAC[IPRODUCT_POS_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let IPRODUCT_POS_LT = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 < f x) ==> &0 < iproduct s f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; INT_LT_01; IN_INSERT; INT_LT_MUL]);;

let IPRODUCT_POS_LT_NUMSEG = prove
 (`!f m n. (!x. m <= x /\ x <= n ==> &0 < f x) ==> &0 < iproduct(m..n) f`,
  SIMP_TAC[IPRODUCT_POS_LT; FINITE_NUMSEG; IN_NUMSEG]);;

let IPRODUCT_OFFSET = prove
 (`!f m p. iproduct(m+p..n+p) f = iproduct(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; IPRODUCT_IMAGE;
           EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let IPRODUCT_SING = prove
 (`!f x. iproduct {x} f = f(x)`,
  SIMP_TAC[IPRODUCT_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; INT_MUL_RID]);;

let IPRODUCT_SING_NUMSEG = prove
 (`!f n. iproduct(n..n) f = f(n)`,
  REWRITE_TAC[NUMSEG_SING; IPRODUCT_SING]);;

let IPRODUCT_CLAUSES_NUMSEG = prove
 (`(!m. iproduct(m..0) f = if m = 0 then f(0) else &1) /\
   (!m n. iproduct(m..SUC n) f = if m <= SUC n then iproduct(m..n) f * f(SUC n)
                                else iproduct(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[IPRODUCT_SING; IPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; INT_MUL_AC]);;

let IPRODUCT_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> iproduct s f = iproduct s g`,
  REWRITE_TAC[iproduct] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_INT_MUL]);;

let IPRODUCT_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (iproduct(m..n) f = iproduct(m..n) g)`,
  MESON_TAC[IPRODUCT_EQ; FINITE_NUMSEG; IN_NUMSEG]);;

let IPRODUCT_EQ_0 = prove
 (`!f s. FINITE s ==> (iproduct s f = &0 <=> ?x. x IN s /\ f(x) = &0)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; INT_ENTIRE; IN_INSERT; INT_OF_NUM_EQ; ARITH;
           NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let IPRODUCT_EQ_0_NUMSEG = prove
 (`!f m n. iproduct(m..n) f = &0 <=> ?x. m <= x /\ x <= n /\ f(x) = &0`,
  SIMP_TAC[IPRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG; GSYM CONJ_ASSOC]);;

let IPRODUCT_RESTRICT = prove
 (`!f s. FINITE s
         ==> iproduct s (\i. if i IN s then f i else &1) = iproduct s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC IPRODUCT_EQ THEN ASM_SIMP_TAC[]);;

let IPRODUCT_RESTRICT_SET = prove
 (`!P s f. iproduct {i:A | i IN s /\ P i} f =
           iproduct s (\i. if P i then f i else &1)`,
  REWRITE_TAC[iproduct; GSYM NEUTRAL_INT_MUL] THEN
  MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC[MONOIDAL_INT_MUL]);;

let IPRODUCT_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f(x) /\ f(x) <= g(x))
         ==> iproduct s f <= iproduct s g`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IN_INSERT; IPRODUCT_CLAUSES; NOT_IN_EMPTY; INT_LE_REFL] THEN
  MESON_TAC[INT_LE_MUL2; IPRODUCT_POS_LE]);;

let IPRODUCT_LE_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> &0 <= f(i) /\ f(i) <= g(i))
           ==> iproduct(m..n) f <= iproduct(m..n) g`,
  SIMP_TAC[IPRODUCT_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let IPRODUCT_EQ_1 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = &1)) ==> (iproduct s f = &1)`,
  REWRITE_TAC[iproduct; GSYM NEUTRAL_INT_MUL] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_INT_MUL]);;

let IPRODUCT_EQ_1_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &1)) ==> (iproduct(m..n) f = &1)`,
  SIMP_TAC[IPRODUCT_EQ_1; IN_NUMSEG]);;

let IPRODUCT_MUL_GEN = prove
 (`!f g s.
       FINITE {x | x IN s /\ ~(f x = &1)} /\ FINITE {x | x IN s /\ ~(g x = &1)}
       ==> iproduct s (\x. f x * g x) = iproduct s f * iproduct s g`,
  REWRITE_TAC[GSYM NEUTRAL_INT_MUL; GSYM support; iproduct] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_INT_MUL);;

let IPRODUCT_MUL = prove
 (`!f g s. FINITE s
           ==> iproduct s (\x. f x * g x) = iproduct s f * iproduct s g`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; INT_MUL_AC; INT_MUL_LID]);;

let IPRODUCT_MUL_NUMSEG = prove
 (`!f g m n.
     iproduct(m..n) (\x. f x * g x) = iproduct(m..n) f * iproduct(m..n) g`,
  SIMP_TAC[IPRODUCT_MUL; FINITE_NUMSEG]);;

let IPRODUCT_CONST = prove
 (`!c s. FINITE s ==> iproduct s (\x. c) = c pow (CARD s)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; CARD_CLAUSES; INT_POW]);;

let IPRODUCT_CONST_NUMSEG = prove
 (`!c m n. iproduct (m..n) (\x. c) = c pow ((n + 1) - m)`,
  SIMP_TAC[IPRODUCT_CONST; CARD_NUMSEG; FINITE_NUMSEG]);;

let IPRODUCT_CONST_NUMSEG_1 = prove
 (`!c n. iproduct(1..n) (\x. c) = c pow n`,
  SIMP_TAC[IPRODUCT_CONST; CARD_NUMSEG_1; FINITE_NUMSEG]);;

let IPRODUCT_NEG = prove
 (`!f s:A->bool.
     FINITE s
     ==> iproduct s (\i. --(f i)) = --(&1) pow (CARD s) * iproduct s f`,
  SIMP_TAC[GSYM IPRODUCT_CONST; GSYM IPRODUCT_MUL] THEN
  REWRITE_TAC[INT_MUL_LNEG; INT_MUL_LID]);;

let IPRODUCT_NEG_NUMSEG = prove
 (`!f m n. iproduct(m..n) (\i. --(f i)) =
           --(&1) pow ((n + 1) - m) * iproduct(m..n) f`,
  SIMP_TAC[IPRODUCT_NEG; CARD_NUMSEG; FINITE_NUMSEG]);;

let IPRODUCT_NEG_NUMSEG_1 = prove
 (`!f n. iproduct(1..n) (\i. --(f i)) = --(&1) pow n * iproduct(1..n) f`,
  REWRITE_TAC[IPRODUCT_NEG_NUMSEG; ADD_SUB]);;

let IPRODUCT_ONE = prove
 (`!s. iproduct s (\n. &1) = &1`,
  SIMP_TAC[IPRODUCT_EQ_1]);;

let IPRODUCT_LE_1 = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f x /\ f x <= &1)
         ==> iproduct s f <= &1`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; INT_LE_REFL; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM INT_MUL_LID] THEN
  MATCH_MP_TAC INT_LE_MUL2 THEN ASM_SIMP_TAC[IPRODUCT_POS_LE]);;

let IPRODUCT_ABS = prove
 (`!f s. FINITE s ==> iproduct s (\x. abs(f x)) = abs(iproduct s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; INT_ABS_MUL; INT_ABS_NUM]);;

let IPRODUCT_CLOSED = prove
 (`!P f:A->int s.
        P(&1) /\ (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(iproduct s f)`,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_INT_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC `P:int->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_INT_MUL; GSYM iproduct]);;

let IPRODUCT_RELATED = prove
 (`!R (f:A->int) g s.
        R (&1) (&1) /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m * m') (n * n')) /\
        FINITE s /\ (!i. i IN s ==> R (f i) (g i))
        ==> R (iproduct s f) (iproduct s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:int->int->bool`
    (MATCH_MP ITERATE_RELATED MONOIDAL_INT_MUL)) THEN
  ASM_REWRITE_TAC[GSYM iproduct; NEUTRAL_INT_MUL] THEN ASM_MESON_TAC[]);;

let IPRODUCT_CLOSED_NONEMPTY = prove
 (`!P f:A->int s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(iproduct s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_INT_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC `P:int->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_INT_MUL; GSYM iproduct]);;

let IPRODUCT_RELATED_NONEMPTY = prove
 (`!R (f:A->int) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m * m') (n * n')) /\
        FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> R (f i) (g i))
        ==> R (iproduct s f) (iproduct s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:int->int->bool`
    (MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_INT_MUL)) THEN
  ASM_REWRITE_TAC[GSYM iproduct; NEUTRAL_INT_MUL] THEN ASM_MESON_TAC[]);;

let IPRODUCT_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> iproduct(m..n) f = f(m) * iproduct(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; IPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let IPRODUCT_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> iproduct(m..n) f = iproduct(m..n-1) f * f(n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; IPRODUCT_CLAUSES_NUMSEG; SUC_SUB1]);;

let INT_OF_NUM_NPRODUCT = prove
 (`!f:A->num s. FINITE s ==> &(nproduct s f) = iproduct s (\x. &(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IPRODUCT_CLAUSES; NPRODUCT_CLAUSES; GSYM INT_OF_NUM_MUL]);;

let IPRODUCT_SUPERSET = prove
 (`!f:A->int u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f(x) = &1)
        ==> iproduct v f = iproduct u f`,
  SIMP_TAC[iproduct; GSYM NEUTRAL_INT_MUL;
           ITERATE_SUPERSET; MONOIDAL_INT_MUL]);;

let IPRODUCT_UNIV = prove
 (`!f:A->int s.
        support ( * ) f (:A) SUBSET s ==> iproduct s f = iproduct (:A) f`,
  REWRITE_TAC[iproduct] THEN MATCH_MP_TAC ITERATE_UNIV THEN
  REWRITE_TAC[MONOIDAL_INT_MUL]);;

let IPRODUCT_PAIR = prove
 (`!f m n. iproduct(2*m..2*n+1) f = iproduct(m..n) (\i. f(2*i) * f(2*i+1))`,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_INT_MUL) THEN
  REWRITE_TAC[iproduct; NEUTRAL_INT_MUL]);;

let IPRODUCT_REFLECT = prove
 (`!x m n. iproduct(m..n) x =
           if n < m then &1 else iproduct(0..n-m) (\i. x(n - i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[iproduct] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP ITERATE_REFLECT MONOIDAL_INT_MUL] THEN
  REWRITE_TAC[NEUTRAL_INT_MUL]);;

let IPRODUCT_DELETE = prove
 (`!f s a.
    FINITE s /\ a IN s ==> f(a) * iproduct(s DELETE a) f = iproduct s f`,
  SIMP_TAC[iproduct; ITERATE_DELETE; MONOIDAL_INT_MUL]);;

let IPRODUCT_DELTA = prove
 (`!s a. iproduct s (\x. if x = a then b else &1) =
         (if a IN s then b else &1)`,
  REWRITE_TAC[iproduct; GSYM NEUTRAL_INT_MUL] THEN
  SIMP_TAC[ITERATE_DELTA; MONOIDAL_INT_MUL]);;

let th = prove
   (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
                ==> iproduct s (\i. f(i)) = iproduct s g) /\
     (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
                ==> iproduct(a..b) (\i. f(i)) = iproduct(a..b) g) /\
     (!f g p.   (!x. p x ==> f x = g x)
                ==> iproduct {y | p y} (\i. f(i)) = iproduct {y | p y} g)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC IPRODUCT_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
    extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Now products over real numbers.                                           *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let PRODUCT_SUPPORT = prove
 (`!f s. product (support ( * ) f s) f = product s f`,
  REWRITE_TAC[product; ITERATE_SUPPORT]);;

let PRODUCT_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (product (s UNION t) f = product s f * product t f)`,
  SIMP_TAC[product; ITERATE_UNION; MONOIDAL_REAL_MUL]);;

let PRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
           ==> (product (IMAGE f s) g = product s (g o f))`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_INJECTION = prove
 (`!f p s. FINITE s /\
           (!x. x IN s ==> p x IN s) /\
           (!x y. x IN s /\ y IN s /\ p x = p y ==> x = y)
           ==> product s (f o p) = product s f`,
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_INJECTION THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_ADD_SPLIT = prove
 (`!f m n p.
        m <= n + 1
        ==> (product (m..(n+p)) f = product(m..n) f * product(n+1..n+p) f)`,
  SIMP_TAC[NUMSEG_ADD_SPLIT; PRODUCT_UNION; DISJOINT_NUMSEG; FINITE_NUMSEG;
           ARITH_RULE `x < x + 1`]);;

let PRODUCT_POS_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f x) ==> &0 <= product s f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_POS; IN_INSERT; REAL_LE_MUL]);;

let PRODUCT_POS_LE_NUMSEG = prove
 (`!f m n. (!x. m <= x /\ x <= n ==> &0 <= f x) ==> &0 <= product(m..n) f`,
  SIMP_TAC[PRODUCT_POS_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let PRODUCT_POS_LT = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 < f x) ==> &0 < product s f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_LT_01; IN_INSERT; REAL_LT_MUL]);;

let PRODUCT_POS_LT_NUMSEG = prove
 (`!f m n. (!x. m <= x /\ x <= n ==> &0 < f x) ==> &0 < product(m..n) f`,
  SIMP_TAC[PRODUCT_POS_LT; FINITE_NUMSEG; IN_NUMSEG]);;

let PRODUCT_OFFSET = prove
 (`!f m p. product(m+p..n+p) f = product(m..n) (\i. f(i + p))`,
  SIMP_TAC[NUMSEG_OFFSET_IMAGE; PRODUCT_IMAGE;
           EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
  REWRITE_TAC[o_DEF]);;

let PRODUCT_SING = prove
 (`!f x. product {x} f = f(x)`,
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; REAL_MUL_RID]);;

let PRODUCT_SING_NUMSEG = prove
 (`!f n. product(n..n) f = f(n)`,
  REWRITE_TAC[NUMSEG_SING; PRODUCT_SING]);;

let PRODUCT_CLAUSES_NUMSEG = prove
 (`(!m. product(m..0) f = if m = 0 then f(0) else &1) /\
   (!m n. product(m..SUC n) f = if m <= SUC n then product(m..n) f * f(SUC n)
                                else product(m..n) f)`,
  REWRITE_TAC[NUMSEG_CLAUSES] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[PRODUCT_SING; PRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`; REAL_MUL_AC]);;

let PRODUCT_EQ = prove
 (`!f g s. (!x. x IN s ==> (f x = g x)) ==> product s f = product s g`,
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_EQ THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_EQ_NUMSEG = prove
 (`!f g m n. (!i. m <= i /\ i <= n ==> (f(i) = g(i)))
             ==> (product(m..n) f = product(m..n) g)`,
  MESON_TAC[PRODUCT_EQ; FINITE_NUMSEG; IN_NUMSEG]);;

let PRODUCT_EQ_0 = prove
 (`!f s. FINITE s ==> (product s f = &0 <=> ?x. x IN s /\ f(x) = &0)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_ENTIRE; IN_INSERT; REAL_OF_NUM_EQ; ARITH;
           NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

let PRODUCT_EQ_0_NUMSEG = prove
 (`!f m n. product(m..n) f = &0 <=> ?x. m <= x /\ x <= n /\ f(x) = &0`,
  SIMP_TAC[PRODUCT_EQ_0; FINITE_NUMSEG; IN_NUMSEG; GSYM CONJ_ASSOC]);;

let PRODUCT_RESTRICT = prove
 (`!f s. FINITE s
         ==> product s (\i. if i IN s then f i else &1) = product s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[]);;

let PRODUCT_RESTRICT_SET = prove
 (`!P s f. product {i:A | i IN s /\ P i} f =
           product s (\i. if P i then f i else &1)`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  MATCH_MP_TAC ITERATE_RESTRICT_SET THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f(x) /\ f(x) <= g(x))
         ==> product s f <= product s g`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IN_INSERT; PRODUCT_CLAUSES; NOT_IN_EMPTY; REAL_LE_REFL] THEN
  MESON_TAC[REAL_LE_MUL2; PRODUCT_POS_LE]);;

let PRODUCT_LE_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> &0 <= f(i) /\ f(i) <= g(i))
           ==> product(m..n) f <= product(m..n) g`,
  SIMP_TAC[PRODUCT_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let PRODUCT_EQ_1 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = &1)) ==> (product s f = &1)`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_REAL_MUL]);;

let PRODUCT_EQ_1_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> (f(i) = &1)) ==> (product(m..n) f = &1)`,
  SIMP_TAC[PRODUCT_EQ_1; IN_NUMSEG]);;

let PRODUCT_MUL_GEN = prove
 (`!f g s.
       FINITE {x | x IN s /\ ~(f x = &1)} /\ FINITE {x | x IN s /\ ~(g x = &1)}
       ==> product s (\x. f x * g x) = product s f * product s g`,
  REWRITE_TAC[GSYM NEUTRAL_REAL_MUL; GSYM support; product] THEN
  MATCH_MP_TAC ITERATE_OP_GEN THEN ACCEPT_TAC MONOIDAL_REAL_MUL);;

let PRODUCT_MUL = prove
 (`!f g s. FINITE s ==> product s (\x. f x * g x) = product s f * product s g`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_MUL_AC; REAL_MUL_LID]);;

let PRODUCT_MUL_NUMSEG = prove
 (`!f g m n.
     product(m..n) (\x. f x * g x) = product(m..n) f * product(m..n) g`,
  SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG]);;

let PRODUCT_CONST = prove
 (`!c s. FINITE s ==> product s (\x. c) = c pow (CARD s)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; CARD_CLAUSES; real_pow]);;

let PRODUCT_CONST_NUMSEG = prove
 (`!c m n. product (m..n) (\x. c) = c pow ((n + 1) - m)`,
  SIMP_TAC[PRODUCT_CONST; CARD_NUMSEG; FINITE_NUMSEG]);;

let PRODUCT_CONST_NUMSEG_1 = prove
 (`!c n. product(1..n) (\x. c) = c pow n`,
  SIMP_TAC[PRODUCT_CONST; CARD_NUMSEG_1; FINITE_NUMSEG]);;

let PRODUCT_NEG = prove
 (`!f s:A->bool.
     FINITE s ==> product s (\i. --(f i)) = --(&1) pow (CARD s) * product s f`,
  SIMP_TAC[GSYM PRODUCT_CONST; GSYM PRODUCT_MUL] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID]);;

let PRODUCT_NEG_NUMSEG = prove
 (`!f m n. product(m..n) (\i. --(f i)) =
           --(&1) pow ((n + 1) - m) * product(m..n) f`,
  SIMP_TAC[PRODUCT_NEG; CARD_NUMSEG; FINITE_NUMSEG]);;

let PRODUCT_NEG_NUMSEG_1 = prove
 (`!f n. product(1..n) (\i. --(f i)) = --(&1) pow n * product(1..n) f`,
  REWRITE_TAC[PRODUCT_NEG_NUMSEG; ADD_SUB]);;

let PRODUCT_INV = prove
 (`!f s. FINITE s ==> product s (\x. inv(f x)) = inv(product s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_INV_1; REAL_INV_MUL]);;

let PRODUCT_DIV = prove
 (`!f g s. FINITE s ==> product s (\x. f x / g x) = product s f / product s g`,
  SIMP_TAC[real_div; PRODUCT_MUL; PRODUCT_INV]);;

let PRODUCT_DIV_NUMSEG = prove
 (`!f g m n.
         product(m..n) (\x. f x / g x) = product(m..n) f / product(m..n) g`,
  SIMP_TAC[PRODUCT_DIV; FINITE_NUMSEG]);;

let PRODUCT_ONE = prove
 (`!s. product s (\n. &1) = &1`,
  SIMP_TAC[PRODUCT_EQ_1]);;

let PRODUCT_LE_1 = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f x /\ f x <= &1)
         ==> product s f <= &1`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_LE_REFL; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[PRODUCT_POS_LE]);;

let PRODUCT_ABS = prove
 (`!f s. FINITE s ==> product s (\x. abs(f x)) = abs(product s f)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; REAL_ABS_MUL; REAL_ABS_NUM]);;

let PRODUCT_CLOSED = prove
 (`!P f:A->real s.
        P(&1) /\ (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(product s f)`,
  REPEAT STRIP_TAC THEN MP_TAC(MATCH_MP ITERATE_CLOSED MONOIDAL_REAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC `P:real->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_REAL_MUL; GSYM product]);;

let PRODUCT_RELATED = prove
 (`!R (f:A->real) g s.
        R (&1) (&1) /\
        (!m n m' n'. R m n /\ R m' n' ==> R (m * m') (n * n')) /\
        FINITE s /\ (!i. i IN s ==> R (f i) (g i))
        ==> R (product s f) (product s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:real->real->bool`
    (MATCH_MP ITERATE_RELATED MONOIDAL_REAL_MUL)) THEN
  ASM_REWRITE_TAC[GSYM product; NEUTRAL_REAL_MUL] THEN ASM_MESON_TAC[]);;

let PRODUCT_CLOSED_NONEMPTY = prove
 (`!P f:A->real s.
        FINITE s /\ ~(s = {}) /\
        (!x y. P x /\ P y ==> P(x * y)) /\ (!a. a IN s ==> P(f a))
        ==> P(product s f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP ITERATE_CLOSED_NONEMPTY MONOIDAL_REAL_MUL) THEN
  DISCH_THEN(MP_TAC o SPEC `P:real->bool`) THEN
  ASM_SIMP_TAC[NEUTRAL_REAL_MUL; GSYM product]);;

let PRODUCT_RELATED_NONEMPTY = prove
 (`!R (f:A->real) g s.
        (!m n m' n'. R m n /\ R m' n' ==> R (m * m') (n * n')) /\
        FINITE s /\ ~(s = {}) /\ (!i. i IN s ==> R (f i) (g i))
        ==> R (product s f) (product s g)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `R:real->real->bool`
    (MATCH_MP ITERATE_RELATED_NONEMPTY MONOIDAL_REAL_MUL)) THEN
  ASM_REWRITE_TAC[GSYM product; NEUTRAL_REAL_MUL] THEN ASM_MESON_TAC[]);;

let PRODUCT_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> product(m..n) f = f(m) * product(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; PRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let PRODUCT_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> product(m..n) f = product(m..n-1) f * f(n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; PRODUCT_CLAUSES_NUMSEG; SUC_SUB1]);;

let REAL_OF_NUM_NPRODUCT = prove
 (`!f:A->num s. FINITE s ==> &(nproduct s f) = product s (\x. &(f x))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NPRODUCT_CLAUSES; GSYM REAL_OF_NUM_MUL]);;

let PRODUCT_SUPERSET = prove
 (`!f:A->real u v.
        u SUBSET v /\ (!x. x IN v /\ ~(x IN u) ==> f(x) = &1)
        ==> product v f = product u f`,
  SIMP_TAC[product; GSYM NEUTRAL_REAL_MUL;
           ITERATE_SUPERSET; MONOIDAL_REAL_MUL]);;

let PRODUCT_UNIV = prove
 (`!f:A->real s.
        support ( * ) f (:A) SUBSET s ==> product s f = product (:A) f`,
  REWRITE_TAC[product] THEN MATCH_MP_TAC ITERATE_UNIV THEN
  REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_PAIR = prove
 (`!f m n. product(2*m..2*n+1) f = product(m..n) (\i. f(2*i) * f(2*i+1))`,
  MP_TAC(MATCH_MP ITERATE_PAIR MONOIDAL_REAL_MUL) THEN
  REWRITE_TAC[product; NEUTRAL_REAL_MUL]);;

let PRODUCT_REFLECT = prove
 (`!x m n. product(m..n) x =
           if n < m then &1 else product(0..n-m) (\i. x(n - i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[product] THEN
  GEN_REWRITE_TAC LAND_CONV [MATCH_MP ITERATE_REFLECT MONOIDAL_REAL_MUL] THEN
  REWRITE_TAC[NEUTRAL_REAL_MUL]);;

let PRODUCT_DELETE = prove
 (`!f s a. FINITE s /\ a IN s ==> f(a) * product(s DELETE a) f = product s f`,
  SIMP_TAC[product; ITERATE_DELETE; MONOIDAL_REAL_MUL]);;

let PRODUCT_DELTA = prove
 (`!s a. product s (\x. if x = a then b else &1) =
         (if a IN s then b else &1)`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  SIMP_TAC[ITERATE_DELTA; MONOIDAL_REAL_MUL]);;

let POLYNOMIAL_FUNCTION_PRODUCT = prove
 (`!s:A->bool p.
        FINITE s /\ (!i. i IN s ==> polynomial_function(\x. p x i))
        ==> polynomial_function (\x. product s (p x))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; POLYNOMIAL_FUNCTION_CONST] THEN
  SIMP_TAC[FORALL_IN_INSERT; POLYNOMIAL_FUNCTION_MUL]);;

let th = prove
   (`(!f g s.   (!x. x IN s ==> f(x) = g(x))
                ==> product s (\i. f(i)) = product s g) /\
     (!f g a b. (!i. a <= i /\ i <= b ==> f(i) = g(i))
                ==> product(a..b) (\i. f(i)) = product(a..b) g) /\
     (!f g p.   (!x. p x ==> f x = g x)
                ==> product {y | p y} (\i. f(i)) = product {y | p y} g)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    ASM_SIMP_TAC[IN_ELIM_THM; IN_NUMSEG]) in
    extend_basic_congs (map SPEC_ALL (CONJUNCTS th));;
