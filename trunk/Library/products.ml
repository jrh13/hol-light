(* ========================================================================= *)
(* Products of real numbers.                                                 *)
(* ========================================================================= *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of infinite product.                                           *)
(* ------------------------------------------------------------------------- *)

let product = new_definition
  `product = iterate ( * )`;;

(* ------------------------------------------------------------------------- *)
(* Various elementary properties (should add more comprehensive list).       *)
(* ------------------------------------------------------------------------- *)

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
