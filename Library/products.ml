(* ========================================================================= *)
(* Products of natural numbers and real numbers.                             *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Products over natural numbers.                                            *)
(* ------------------------------------------------------------------------- *)

let nproduct = new_definition
  `nproduct = iterate(( * ):num->num->num)`;;

let NPRODUCT_CLAUSES = prove
 (`(!f. nproduct {} f = 1) /\
   (!x f s. FINITE(s)
            ==> (nproduct (x INSERT s) f =
                 if x IN s then nproduct s f else f(x) * nproduct s f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_MUL]);;

let NPRODUCT_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (nproduct (s UNION t) f = nproduct s f * nproduct t f)`,
  SIMP_TAC[nproduct; ITERATE_UNION; MONOIDAL_MUL]);;

let NPRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (nproduct (IMAGE f s) g = nproduct s (g o f))`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_MUL]);;

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

let NPRODUCT_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> 0 <= f(x) /\ f(x) <= g(x))
         ==> nproduct s f <= nproduct s g`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IN_INSERT; NPRODUCT_CLAUSES; NOT_IN_EMPTY; LE_REFL] THEN
  MESON_TAC[LE_MULT2; LE_0]);;

let NPRODUCT_LE_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> 0 <= f(i) /\ f(i) <= g(i))
           ==> nproduct(m..n) f <= nproduct(m..n) g`,
  SIMP_TAC[NPRODUCT_LE; FINITE_NUMSEG; IN_NUMSEG]);;

let NPRODUCT_EQ_1 = prove
 (`!f s. (!x:A. x IN s ==> (f(x) = 1)) ==> (nproduct s f = 1)`,
  REWRITE_TAC[nproduct; GSYM NEUTRAL_MUL] THEN
  SIMP_TAC[ITERATE_EQ_NEUTRAL; MONOIDAL_MUL]);;

let NPRODUCT_EQ_1_NUMSEG = prove
 (`!f m n. (!i. m <= i /\ i <= n ==> (f(i) = 1)) ==> (nproduct(m..n) f = 1)`,
  SIMP_TAC[NPRODUCT_EQ_1; IN_NUMSEG]);;

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

let NPRODUCT_CLAUSES_LEFT = prove
 (`!f m n. m <= n ==> nproduct(m..n) f = f(m) * nproduct(m+1..n) f`,
  SIMP_TAC[GSYM NUMSEG_LREC; NPRODUCT_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
  ARITH_TAC);;

let NPRODUCT_CLAUSES_RIGHT = prove
 (`!f m n. 0 < n /\ m <= n ==> nproduct(m..n) f = nproduct(m..n-1) f * f(n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  SIMP_TAC[LT_REFL; NPRODUCT_CLAUSES_NUMSEG; SUC_SUB1]);;

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
(* Now products over real numbers.                                           *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let product = new_definition
  `product = iterate (( * ):real->real->real)`;;

let PRODUCT_CLAUSES = prove
 (`(!f. product {} f = &1) /\
   (!x f s. FINITE(s)
            ==> (product (x INSERT s) f =
                 if x IN s then product s f else f(x) * product s f))`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  MATCH_MP_TAC ITERATE_CLAUSES THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);;

let PRODUCT_UNION = prove
 (`!f s t. FINITE s /\ FINITE t /\ DISJOINT s t
           ==> (product (s UNION t) f = product s f * product t f)`,
  SIMP_TAC[product; ITERATE_UNION; MONOIDAL_REAL_MUL]);;

let PRODUCT_IMAGE = prove
 (`!f g s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))
           ==> (product (IMAGE f s) g = product s (g o f))`,
  REWRITE_TAC[product; GSYM NEUTRAL_REAL_MUL] THEN
  MATCH_MP_TAC ITERATE_IMAGE THEN REWRITE_TAC[MONOIDAL_REAL_MUL]);;

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

(* ------------------------------------------------------------------------- *)
(* Extend congruences.                                                       *)
(* ------------------------------------------------------------------------- *)

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
