(* ========================================================================= *)
(* Sharpening I: arithmetic of the counterpart.                              *)
(*                                                                           *)
(* Purpose: the arithmetic parts of Lemmas 5, 6 and 8 of Baker, Sharpening I *)
(* (Acta Arith. 21, 1972) and A central theorem in transcendence theory      *)
(* (1973) for the counterpart sharp_alg of the auxiliary function with       *)
(* complex coefficients bb r: ONE proof of each lemma for integer and for    *)
(* algebraic coefficients. The numbers cexp(lg r) (sharp_algdata: degree     *)
(* dd r, height H r) and the coefficients bb r (sharpc_coefdata: degree      *)
(* db r, height Hb), r = 1..n, are one family of 2n algebraic numbers over   *)
(* the index set 1..n+n: theta k = cexp(lg k) for k <= n and                 *)
(* theta(n + r) = bb r (SHARP_JOINT_ALGDATA, SHARP_JOINT_SIEGEL,             *)
(* SHARP_JOINT_LIOUVILLE). The Delta factors enter through a Delta           *)
(* representation (sharp_deltarep of Baker/sharp_defs.ml: M m times the      *)
(* Delta product is an integer polynomial in the betas of degree E s with    *)
(* coefficient sum W s, 1 <= M m <= Mb s, s = m 1 + ... + m (n-1)). There    *)
(* are two:                                                                  *)
(*  - integer coefficients (SHARP_DELTAREP_INT): the Delta values are        *)
(*    integers of size (4B+2)^s 2^((n-1)Lm) (the Baker binomial trick,       *)
(*    SHARP_CPRODUCT_DELTA_BOUND): M = 1, E = 0, Mb = 1;                     *)
(*  - algebraic coefficients (SHARP_DELTAREP_ALG): m! Delta(x; m) =          *)
(*    prod_(j=1..m) (x + j) and every factor x_r + j is an integer           *)
(*    polynomial of degree 1 in the betas (SHARP_DELTA_INTPOLY,              *)
(*    SHARP_DELTA_EVAL): M m = prod_r m_r!, E s = s, W s = (2Lm + s)^s,      *)
(*    Mb s = s^s.                                                            *)
(* At a rational point l/q, q^(2h(L0+2)) Nq^(m 0) M m times a term of the    *)
(* counterpart is the Feldman integer (SHARP_FELDMAN_COEFF) times the Delta  *)
(* polynomial times the alpha monomial prod_r cexp(lg r / q)^(mu_r l)        *)
(* (SHARP_ALGTERM_RAT_INTPOLY, SHARP_ALG_RAT_INTPOLY). Lemma 5 (Siegel) by   *)
(* the joint Siegel lemma on the equations (1..h) CROSS Mset times           *)
(* N^(m 0) M m (N a common multiple of 1..2h, N <= e^(36h)); Lemma 6 at the  *)
(* integers l (N | lcm(l+1..l+h)) and Lemma 8 at l/q (Nq | lcm(1..l+qh),     *)
(* the roots cexp(lg r / q) of a r(X^q), SHARP_ALGDATA_ROOT) by the joint    *)
(* Liouville inequality, dividing by the denominators. The bounds are the    *)
(* generic functions sharp_psize, sharp_liou5, sharp_lb8 of                  *)
(* Baker/sharp_defs.ml; at the two Delta representations they are the        *)
(* bounds of the two endings (the body lemmas of the numeric layer).         *)
(*                                                                           *)
(* Main results: SHARP_LEMMA5, SHARP_DICHOTOMY, SHARP_LEMMA8 (used by        *)
(* Baker/sharp_core.ml), SHARP_DELTAREP_INT, SHARP_DELTAREP_ALG (used by the *)
(* numeric layer); SHARP_JOINT_SIEGEL, SHARP_JOINT_LIOUVILLE,                *)
(* SHARP_JOINT_ALGDATA, SHARP_NPRODUCT_JOIN, SHARPC_COEFDATA_HB_GE_1,        *)
(* SHARP_DELTA_INTPOLY, SHARP_DELTA_EVAL, SHARP_FACT_NPRODUCT_LE,            *)
(* SHARP_X_INTEGER, SHARP_DELTA_PRODUCT_INTEGER, SHARP_DELTAREP_W_POS,       *)
(* SHARP_FELDMAN_COEFF, SHARP_ALGTERM_RAT_INTPOLY, SHARP_ALG_RAT_INTPOLY,    *)
(* SHARP_ALGTERM_LINEAR, SHARP_ALGTERM_RESTRICT, SHARP_ALG_RESTRICT,         *)
(* SHARP_ALGDATA_ROOT, SHARP_INDEX_BOUNDS, SHARP_INDEX_NONEMPTY,             *)
(* SHARP_MSET_FINITE_CARD; real helpers PRODUCT_POW_GE_1, REAL_LE_MUL_5,     *)
(* REAL_LE_MUL_6, REAL_DIV_LE_FROM_MUL, REAL_INV_MUL_LE_FROM_MUL; internal   *)
(* helpers SHARP_ARITH_*.                                                    *)
(*                                                                           *)
(* Uses: Baker/sharp_defs.ml (sharp_index, sharp_x, sharp_algterm,           *)
(* sharp_alg, sharp_algdata, sharp_deltarep, sharp_psize, sharp_liou5,       *)
(* sharp_lb8), Baker/uniform.ml (sharpc_coefdata), Baker/sharp_aux.ml        *)
(* (FINITE_SHARP_INDEX, SHARP_CPRODUCT_DELTA_BOUND), Baker/sharp_poly.ml     *)
(* (FELDMAN_DELTA_INTEGER, FELDMAN_BASIS_DERIV_RATIONAL), Baker/delta.ml     *)
(* (feldman_delta, feldman_basis, NUMSEG_COMMON_MULTIPLE,                    *)
(* SHIFTED_COMMON_MULTIPLE_BOUND, FELDMAN_BASIS_DERIV_BOUND_UNIFORM),        *)
(* Baker/aux_arith.ml (VSUM_POLY_POW_SUBST, CEXP_DIV_POW,                    *)
(* CEXP_LINEAR_COMBINATION_RATIONAL, NSUM_RESTRICTION), Baker/siegel.ml      *)
(* (ALGEBRAIC_SIEGEL), Baker/liouville_inequality.ml (INTPOLY_LIOUVILLE),    *)
(* Baker/intpoly.ml (intpoly, INTPOLY_MONO, INTPOLY_CONST, INTPOLY_VAR,      *)
(* INTPOLY_ADD, INTPOLY_SUB, INTPOLY_MUL, INTPOLY_NUM_MUL, INTPOLY_CMUL,     *)
(* INTPOLY_CPRODUCT, INTPOLY_MONOMIAL, INTPOLY_VSUM, INTPOLY_BOUND_POS),     *)
(* Baker/prelim.ml (complex integers), Baker/auxiliary.ml (FACT_LE_POW),     *)
(* Baker/bounds.ml (PRODUCT_GE_1), Baker/lemmas.ml (REAL_LE_1_MUL),          *)
(* Library/products.ml (NPRODUCT_ADD_SPLIT, NPRODUCT_OFFSET,                 *)
(* PRODUCT_ADD_SPLIT, PRODUCT_OFFSET, EXP_NSUM, REAL_OF_NUM_NPRODUCT,        *)
(* REAL_POW_NSUM), Library/floor.ml (REAL_ABS_INTEGER_LEMMA).                *)
(* ========================================================================= *)

needs "Baker/sharp_aux.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Part 1. Generic facts: the index set, real helpers, the derivative orders *)
(* of the Siegel equations, the q-th roots of the alphas, linearity in p and *)
(* the restriction of the derivative orders m to 0..n-1.                     *)
(* ------------------------------------------------------------------------- *)

let SHARP_INDEX_BOUNDS = prove
 (`!h L0 Lv n a b mu.
        (a,b,mu) IN sharp_index h L0 Lv n
        ==> a < h /\ b <= L0 /\ (!r. r IN 1..n ==> mu r <= Lv r)`,
  REWRITE_TAC[sharp_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
              cartesian_product; EXTENSIONAL] THEN
  SIMP_TAC[IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[]);;

let SHARP_INDEX_NONEMPTY = prove
 (`!h L0 Lv n. 1 <= h ==> ~(sharp_index h L0 Lv n = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `(0,0,RESTRICTION (1..n) (\r:num. 0))` THEN
  REWRITE_TAC[sharp_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
              RESTRICTION_IN_CARTESIAN_PRODUCT; LE_0] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A product of powers of real numbers >= 1 is >= 1.                         *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_POW_GE_1 = prove
 (`!n (x:num->real) (k:num->num).
        (!r. r IN 1..n ==> &1 <= x r)
        ==> &1 <= product(1..n) (\r. x r pow k r)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_GE_1 THEN
  ASM_SIMP_TAC[FINITE_NUMSEG; REAL_POW_LE_1]);;

(* ------------------------------------------------------------------------- *)
(* Small real helpers: products of five and of six non-negative factors.     *)
(* ------------------------------------------------------------------------- *)

let REAL_LE_MUL_5 = prove
 (`!x1 x2 x3 x4 x5 y1 y2 y3 y4 y5:real.
     &0 <= x1 /\ x1 <= y1 /\ &0 <= x2 /\ x2 <= y2 /\ &0 <= x3 /\ x3 <= y3 /\
     &0 <= x4 /\ x4 <= y4 /\ &0 <= x5 /\ x5 <= y5
     ==> x1 * x2 * x3 * x4 * x5 <= y1 * y2 * y3 * y4 * y5`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LE_MUL]));;

let REAL_LE_MUL_6 = prove
 (`!x1 x2 x3 x4 x5 x6 y1 y2 y3 y4 y5 y6:real.
     &0 <= x1 /\ x1 <= y1 /\ &0 <= x2 /\ x2 <= y2 /\ &0 <= x3 /\ x3 <= y3 /\
     &0 <= x4 /\ x4 <= y4 /\ &0 <= x5 /\ x5 <= y5 /\ &0 <= x6 /\ x6 <= y6
     ==> x1 * x2 * x3 * x4 * x5 * x6 <= y1 * y2 * y3 * y4 * y5 * y6`,
  REPEAT STRIP_TAC THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
         TRY(FIRST_ASSUM ACCEPT_TAC) THEN
         TRY(REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
             FIRST_ASSUM ACCEPT_TAC)));;

(* ------------------------------------------------------------------------- *)
(* Real helpers for the Liouville bounds: t <= c1 z and c1 <= c2 give        *)
(* t / c2 <= z; inv x <= c1 y and c1 <= c2 give inv(c2 x) <= y.              *)
(* ------------------------------------------------------------------------- *)

let REAL_DIV_LE_FROM_MUL = prove
 (`!t c1 c2 z. &0 <= t /\ &0 < c1 /\ c1 <= c2 /\ t <= c1 * z ==> t / c2 <= z`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `t / c1` THEN CONJ_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let REAL_INV_MUL_LE_FROM_MUL = prove
 (`!c1 c2 x y.
        &0 < c1 /\ c1 <= c2 /\ &0 <= y /\ inv x <= c1 * y
        ==> inv(c2 * x) <= y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_INV_MUL; GSYM real_div; REAL_LE_LDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `c1 * y:real` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The derivative orders of the Siegel equations: the m with m i <= S0       *)
(* (i < n) and |m| <= S0 form a finite set with at most (S0 + 1)^n elements. *)
(* ------------------------------------------------------------------------- *)

let SHARP_MSET_FINITE_CARD = prove
 (`!n S0.
        1 <= n
        ==> FINITE {m:num->num | m IN cartesian_product (0..n-1) (\i. 0..S0) /\
                                 nsum(0..n-1) m <= S0} /\
            CARD {m:num->num | m IN cartesian_product (0..n-1) (\i. 0..S0) /\
                               nsum(0..n-1) m <= S0} <= (S0 + 1) EXP n`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `FINITE(cartesian_product (0..n-1) (\i:num. 0..S0)) /\
    CARD(cartesian_product (0..n-1) (\i:num. 0..S0)) = (S0 + 1) EXP n`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG;
             CARD_CARTESIAN_PRODUCT; CARD_NUMSEG; NPRODUCT_CONST_NUMSEG] THEN
    ASM_SIMP_TAC[SUB_0; ARITH_RULE `1 <= n ==> n - 1 + 1 = n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{m:num->num | m IN cartesian_product (0..n-1) (\i. 0..S0) /\
                  nsum(0..n-1) m <= S0} SUBSET
    cartesian_product (0..n-1) (\i:num. 0..S0)`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[FINITE_SUBSET; CARD_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* The q-th roots cexp(lg r / q) of the numbers cexp(lg r) of sharp_algdata  *)
(* are roots of a r(X^q), of degree q * dd r and height H r.                 *)
(* ------------------------------------------------------------------------- *)

let SHARP_ALGDATA_ROOT = prove
 (`!n (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real) q.
     sharp_algdata n lg a dd H /\ 1 <= q
     ==> sharp_algdata n (\r. lg r / Cx(&q))
           (\r j. if q divides j then a r (j DIV q) else &0)
           (\r. q * dd r) H`,
  REWRITE_TAC[sharp_algdata] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `1 * 1 <= q * (dd:num->num) r` MP_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT;
                 ARITH_RULE `1 <= q ==> ~(q = 0)`];
    ASM_SIMP_TAC[VSUM_POLY_POW_SUBST; CEXP_DIV_POW]]);;

(* ------------------------------------------------------------------------- *)
(* Linearity in p and the restriction of the derivative orders m to 0..n-1.  *)
(* ------------------------------------------------------------------------- *)

let SHARP_ALGTERM_LINEAR = prove
 (`!n h p (bb:num->complex) lg m a b mu z.
        sharp_algterm n h p bb lg m (a,b,mu) z =
        Cx(p(a,b,mu)) * sharp_algterm n h (\x. &1) bb lg m (a,b,mu) z`,
  REWRITE_TAC[sharp_algterm; COMPLEX_MUL_LID]);;

let SHARP_ALGTERM_RESTRICT = prove
 (`!n h p (bb:num->complex) lg m x z.
        1 <= n
        ==> sharp_algterm n h p bb lg (RESTRICTION (0..n-1) m) x z =
            sharp_algterm n h p bb lg m x z`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM(ISPEC `x:num#num#(num->num)` PAIR)) THEN
  SUBST1_TAC(SYM(ISPEC `SND(x:num#num#(num->num))` PAIR)) THEN
  REWRITE_TAC[sharp_algterm] THEN
  SUBGOAL_THEN `RESTRICTION (0..n-1) (m:num->num) 0 = m 0` SUBST1_TAC THENL
   [REWRITE_TAC[RESTRICTION; IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN REWRITE_TAC[IN_NUMSEG; RESTRICTION] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let SHARP_ALG_RESTRICT = prove
 (`!n h L0 Lv p (bb:num->complex) lg m z.
        1 <= n
        ==> sharp_alg n h L0 Lv p bb lg (RESTRICTION (0..n-1) m) z =
            sharp_alg n h L0 Lv p bb lg m z`,
  SIMP_TAC[sharp_alg; SHARP_ALGTERM_RESTRICT]);;

(* ------------------------------------------------------------------------- *)
(* Part 2. The joint family over 1..n+n: theta k = cexp(lg k) for k <= n and *)
(* theta(n + r) = bb r; degrees dd k / db r, heights H k / Hb. Splitting the *)
(* products over 1..n+n at n.                                                *)
(* ------------------------------------------------------------------------- *)

let SHARP_ARITH_PRODUCT_SPLIT = prove
 (`!n (f:num->real).
        product(1..n+n) f = product(1..n) f * product(1..n) (\r. f(r + n))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `1`; `n:num`; `n:num`] PRODUCT_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`f:num->real`; `1`; `n:num`] PRODUCT_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + n = n + 1`]);;

let SHARP_ARITH_NPRODUCT_SPLIT = prove
 (`!n (f:num->num).
        nproduct(1..n+n) f = nproduct(1..n) f * nproduct(1..n) (\r. f(r + n))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`f:num->num`; `1`; `n:num`; `n:num`] NPRODUCT_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC(ISPECL [`f:num->num`; `1`; `n:num`] NPRODUCT_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + n = n + 1`]);;

let SHARP_ARITH_PRODUCT_JOIN_EQ = prove
 (`!n (ff:num->real) f g.
        (!k. 1 <= k /\ k <= n ==> ff k = f k /\ ff(k + n) = g k)
        ==> product(1..n+n) ff = product(1..n) f * product(1..n) g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SHARP_ARITH_PRODUCT_SPLIT] THEN
  BINOP_TAC THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN ASM_SIMP_TAC[]);;

let SHARP_NPRODUCT_JOIN = prove
 (`!n (dd:num->num) db.
        nproduct(1..n+n) (\k. if k <= n then dd k else db(k - n)) =
        nproduct(1..n) dd * nproduct(1..n) db`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SHARP_ARITH_NPRODUCT_SPLIT] THEN
  BINOP_TAC THEN MATCH_MP_TAC NPRODUCT_EQ_NUMSEG THEN
  SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i + n <= n)`; ADD_SUB]);;

let SHARP_ARITH_PRODUCT_JOIN_POW = prove
 (`!n (H:num->real) Hb (e:num->num) E.
        product(1..n+n)
          (\k. (if k <= n then H k else Hb) pow (if k <= n then e k else E)) =
        product(1..n) (\r. H r pow e r) * Hb pow (n * E)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `product(1..n) (\r. (H:num->real) r pow e r) *
    product(1..n) (\r:num. (Hb:real) pow E)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SHARP_ARITH_PRODUCT_JOIN_EQ THEN
    SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k + n <= n)`];
    REWRITE_TAC[PRODUCT_CONST_NUMSEG_1; REAL_POW_POW; MULT_SYM]]);;

let SHARP_ARITH_PRODUCT_JOIN_POW2 = prove
 (`!n (H:num->real) Hb (e:num->num) E.
        product(1..n+n)
          (\k. (&2 * (if k <= n then H k else Hb)) pow
               (if k <= n then e k else E)) =
        product(1..n) (\r. (&2 * H r) pow e r) * (&2 * Hb) pow (n * E)`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS
   `product(1..n) (\r. (&2 * (H:num->real) r) pow e r) *
    product(1..n) (\r:num. (&2 * Hb:real) pow E)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SHARP_ARITH_PRODUCT_JOIN_EQ THEN
    SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k + n <= n)`];
    REWRITE_TAC[PRODUCT_CONST_NUMSEG_1; REAL_POW_POW; MULT_SYM]]);;

let SHARP_ARITH_PRODUCT_JOIN_LIOU = prove
 (`!n (H:num->real) Hb (dd:num->num) db (e:num->num) E.
        product(1..n+n)
          (\k. ((if k <= n then H k else Hb) *
                (&1 + &(if k <= n then dd k else db(k - n)) *
                      (if k <= n then H k else Hb))) pow
               (if k <= n then e k else E)) =
        product(1..n) (\r. (H r * (&1 + &(dd r) * H r)) pow e r) *
        product(1..n) (\r. (Hb * (&1 + &(db r) * Hb)) pow E)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SHARP_ARITH_PRODUCT_JOIN_EQ THEN
  SIMP_TAC[ARITH_RULE `1 <= k ==> ~(k + n <= n)`; ADD_SUB]);;

(* ------------------------------------------------------------------------- *)
(* The alphas (sharp_algdata) and the betas (sharpc_coefdata) as one family  *)
(* of algebraic numbers over 1..n+n (the hypothesis of ALGEBRAIC_SIEGEL and  *)
(* INTPOLY_LIOUVILLE); the height bound Hb of the betas is at least 1.       *)
(* ------------------------------------------------------------------------- *)

let SHARP_JOINT_ALGDATA = prove
 (`!n (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real)
    (bb:num->complex) (ab:num->num->real) (db:num->num) Hb.
     sharp_algdata n lg a dd H /\ sharpc_coefdata n bb ab db Hb
     ==> !k. k IN 1..n+n
             ==> 1 <= (if k <= n then dd k else db(k - n)) /\
                 (!j. integer((if k <= n then a k else ab(k - n)) j) /\
                      abs((if k <= n then a k else ab(k - n)) j) <=
                      (if k <= n then H k else Hb)) /\
                 ~((if k <= n then a k else ab(k - n))
                     (if k <= n then dd k else db(k - n)) = &0) /\
                 vsum(0..(if k <= n then dd k else db(k - n)))
                   (\j. Cx((if k <= n then a k else ab(k - n)) j) *
                        (if k <= n then cexp(lg k) else bb(k - n)) pow j) =
                 Cx(&0)`,
  REWRITE_TAC[sharp_algdata; sharpc_coefdata; IN_NUMSEG] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a") (LABEL_TAC "b")) THEN
  X_GEN_TAC `k:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `k <= n` THEN ASM_REWRITE_TAC[] THENL
   [REMOVE_THEN "a" (MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[];
    REMOVE_THEN "b" (MP_TAC o SPEC `k - n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; MESON_TAC[]]]);;

let SHARPC_COEFDATA_HB_GE_1 = prove
 (`!n (bb:num->complex) (ab:num->num->real) (db:num->num) Hb.
        1 <= n /\ sharpc_coefdata n bb ab db Hb ==> &1 <= Hb`,
  REWRITE_TAC[sharpc_coefdata] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
  ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `abs((ab:num->num->real) 1 (db 1))` THEN
  ASM_SIMP_TAC[REAL_ABS_INTEGER_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* The Liouville inequality and the algebraic Siegel lemma for integer       *)
(* polynomials in the joint family, with the degree vector e r at the alphas *)
(* and E at every beta, in the product forms of sharp_liou5, sharp_lb8 and   *)
(* sharp_psize.                                                              *)
(* ------------------------------------------------------------------------- *)

let SHARP_JOINT_LIOUVILLE = prove
 (`!n (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real)
    (bb:num->complex) (ab:num->num->real) (db:num->num) Hb (e:num->num) E
    b g.
     sharp_algdata n lg a dd H /\ sharpc_coefdata n bb ab db Hb /\
     intpoly (1..n+n) (\k. if k <= n then e k else E) b g /\
     ~(g (\k. if k <= n then cexp(lg k) else bb(k - n)) = Cx(&0))
     ==> inv(&(FACT(nproduct(1..n) dd * nproduct(1..n) db)) *
             (max (&1)
               (b * product(1..n) (\r. H r pow e r) * Hb pow (n * E) *
                product(1..n) (\r. (H r * (&1 + &(dd r) * H r)) pow e r) *
                product(1..n) (\r. (Hb * (&1 + &(db r) * Hb)) pow E)))
             pow (nproduct(1..n) dd * nproduct(1..n) db - 1) *
             product(1..n) (\r. H r pow e r) * Hb pow (n * E))
         <= norm(g (\k. if k <= n then cexp(lg k) else bb(k - n)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `lg:num->complex`; `a:num->num->real`;
                 `dd:num->num`; `H:num->real`; `bb:num->complex`;
                 `ab:num->num->real`; `db:num->num`; `Hb:real`]
         SHARP_JOINT_ALGDATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`1..n+n`; `\k. if k <= n then (e:num->num) k else E`; `b:real`;
    `g:(num->complex)->complex`;
    `\k. if k <= n then cexp((lg:num->complex) k)
         else (bb:num->complex)(k - n)`;
    `\k. if k <= n then (a:num->num->real) k else ab(k - n)`;
    `\k. if k <= n then (dd:num->num) k else db(k - n)`;
    `\k. if k <= n then (H:num->real) k else Hb`] INTPOLY_LIOUVILLE) THEN
  REWRITE_TAC[FINITE_NUMSEG; SHARP_NPRODUCT_JOIN; SHARP_ARITH_PRODUCT_JOIN_POW;
              SHARP_ARITH_PRODUCT_JOIN_LIOU] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[REAL_MUL_ASSOC]]);;

let SHARP_JOINT_SIEGEL = prove
 (`!n (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real)
    (bb:num->complex) (ab:num->num->real) (db:num->num) Hb (e:num->num) E
    U (g:A->B->(num->complex)->complex) eqs unk.
     FINITE eqs /\ FINITE unk /\ ~(unk = {}) /\
     sharp_algdata n lg a dd H /\ sharpc_coefdata n bb ab db Hb /\
     (!i j. i IN eqs /\ j IN unk
            ==> intpoly (1..n+n) (\k. if k <= n then e k else E) U (g i j)) /\
     2 * (nproduct(1..n) dd * nproduct(1..n) db) * CARD eqs <= CARD unk
     ==> ?x. (!j. j IN unk
                  ==> integer(x j) /\
                      abs(x j) <= &(CARD unk) *
                                  max (&1)
                                      (U * product(1..n)
                                             (\r. (&2 * H r) pow e r) *
                                       (&2 * Hb) pow (n * E))) /\
             ~(!j. j IN unk ==> x j = &0) /\
             (!i. i IN eqs
                  ==> vsum unk (\j. Cx(x j) *
                                    g i j (\k. if k <= n then cexp(lg k)
                                               else bb(k - n))) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `lg:num->complex`; `a:num->num->real`;
                 `dd:num->num`; `H:num->real`; `bb:num->complex`;
                 `ab:num->num->real`; `db:num->num`; `Hb:real`]
         SHARP_JOINT_ALGDATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`1..n+n`; `\k. if k <= n then (e:num->num) k else E`; `U:real`;
    `g:A->B->(num->complex)->complex`; `eqs:A->bool`; `unk:B->bool`;
    `\k. if k <= n then cexp((lg:num->complex) k)
         else (bb:num->complex)(k - n)`;
    `\k. if k <= n then (a:num->num->real) k else ab(k - n)`;
    `\k. if k <= n then (dd:num->num) k else db(k - n)`;
    `\k. if k <= n then (H:num->real) k else Hb`] ALGEBRAIC_SIEGEL) THEN
  REWRITE_TAC[FINITE_NUMSEG; SHARP_NPRODUCT_JOIN;
              SHARP_ARITH_PRODUCT_JOIN_POW2] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 3. The Delta representations. Algebraic coefficients: the Delta      *)
(* factors are integer polynomials in the betas, m! Delta(x; m) =            *)
(* prod_(j=1..m) (x + j) and x_r + j = mu_r bb n - mu_n bb r + j has degree  *)
(* 1 in the betas theta(n+r), theta(n+n), degree 0 in the alphas and         *)
(* coefficient sum mu_r + mu_n + j <= 2 Lm + Sm (Sm = nsum(1..n-1) m).       *)
(* Never INTPOLY_LINEAR here: its degree vector is 1 at every variable,      *)
(* also at the alphas.                                                       *)
(* ------------------------------------------------------------------------- *)

let SHARP_ARITH_DELTA_FACTOR_INTPOLY = prove
 (`!n (mu:num->num) r j.
     1 <= r /\ r <= n
     ==> intpoly (1..n+n) (\k. if k <= n then 0 else 1)
          ((&(mu r) * &1 + &(mu n) * &1) + &j)
          (\x. (Cx(&(mu r)) * x(n + n) - Cx(&(mu n)) * x(n + r)) + Cx(&j))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTPOLY_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC INTPOLY_NUM_MUL THEN MATCH_MP_TAC INTPOLY_VAR THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; REAL_LE_REFL] THEN
    REPEAT CONJ_TAC THEN TRY COND_CASES_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC INTPOLY_CONST THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_LE_REFL]]);;

let SHARP_ARITH_DELTA_ROW_INTPOLY = prove
 (`!n (mu:num->num) (m:num->num) Lm S r.
     1 <= r /\ r <= n /\ mu r <= Lm /\ mu n <= Lm /\ m r <= S
     ==> intpoly (1..n+n) (\k. if k <= n then 0 else m r)
          ((&2 * &Lm + &S) pow (m r))
          (\x. cproduct(1..m r)
                (\j. (Cx(&(mu r)) * x(n + n) - Cx(&(mu n)) * x(n + r)) +
                     Cx(&j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTPOLY_MONO THEN
  MAP_EVERY EXISTS_TAC
   [`\k. nsum(1..m(r:num)) (\j:num. if k <= n then 0 else 1)`;
    `(&2 * &Lm + &S) pow (m(r:num))`] THEN
  REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`1..n+n`; `\j:num k:num. if k <= n then 0 else 1`;
      `\j:num. &2 * &Lm + &S`;
      `\j (x:num->complex).
         (Cx(&(mu(r:num))) * x(n + n) - Cx(&(mu n)) * x(n + r)) + Cx(&j)`;
      `1..m(r:num)`] INTPOLY_CPRODUCT) THEN
    REWRITE_TAC[FINITE_NUMSEG; PRODUCT_CONST_NUMSEG_1] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\k. if k <= n then 0 else 1`;
      `(&(mu(r:num)) * &1 + &(mu n) * &1) + &j`] THEN
    ASM_SIMP_TAC[SHARP_ARITH_DELTA_FACTOR_INTPOLY; LE_REFL] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL;
                REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NSUM_0; LE_REFL; NSUM_CONST_NUMSEG] THEN
    ARITH_TAC]);;

let SHARP_DELTA_INTPOLY = prove
 (`!n (mu:num->num) (m:num->num) Lm.
     1 <= n /\ (!r. r IN 1..n ==> mu r <= Lm)
     ==> intpoly (1..n+n) (\k. if k <= n then 0 else nsum(1..n-1) m)
          ((&2 * &Lm + &(nsum(1..n-1) m)) pow (nsum(1..n-1) m))
          (\x. cproduct(1..n-1)
                (\r. cproduct(1..m r)
                      (\j. (Cx(&(mu r)) * x(n + n) - Cx(&(mu n)) * x(n + r)) +
                           Cx(&j))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTPOLY_MONO THEN
  MAP_EVERY EXISTS_TAC
   [`\k. nsum(1..n-1) (\r. if k <= n then 0 else (m:num->num) r)`;
    `product(1..n-1)
      (\r. (&2 * &Lm + &(nsum(1..n-1) m)) pow ((m:num->num) r))`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL
     [`1..n+n`; `\r k. if k <= n then 0 else (m:num->num) r`;
      `\r. (&2 * &Lm + &(nsum(1..n-1) m)) pow ((m:num->num) r)`;
      `\r (x:num->complex).
         cproduct(1..m r)
          (\j. (Cx(&(mu r)) * x(n + n) - Cx(&(mu n)) * x(n + r)) + Cx(&j))`;
      `1..n-1`] INTPOLY_CPRODUCT) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC SHARP_ARITH_DELTA_ROW_INTPOLY THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      MP_TAC(ISPECL [`m:num->num`; `1..n-1`; `r:num`] NSUM_DELETE) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ARITH_TAC];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[NSUM_0; LE_REFL; ETA_AX];
    SIMP_TAC[GSYM REAL_POW_NSUM; FINITE_NUMSEG; REAL_LE_REFL]]);;

let SHARP_DELTA_EVAL = prove
 (`!n (bb:num->complex) (mu:num->num) (m:num->num) (x:num->complex).
     1 <= n /\ (!r. r IN 1..n ==> x(n + r) = bb r)
     ==> cproduct(1..n-1)
          (\r. cproduct(1..m r)
                (\j. (Cx(&(mu r)) * x(n + n) - Cx(&(mu n)) * x(n + r)) +
                     Cx(&j))) =
         Cx(&(nproduct(1..n-1) (\r. FACT(m r)))) *
         cproduct(1..n-1) (\r. feldman_delta (m r) (sharp_x n bb mu r))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `cproduct(1..n-1)
     (\r. Cx(&(FACT(m r))) * feldman_delta (m r) (sharp_x n bb mu r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[feldman_delta] THEN
    SIMP_TAC[COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ; FACT_NZ] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[sharp_x] THEN
    SUBGOAL_THEN `(x:num->complex)(n + n) = bb n /\ x(n + r) = bb r`
     (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      CONV_TAC COMPLEX_RING];
    SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; REAL_OF_NUM_NPRODUCT; CX_PRODUCT]]);;

(* ------------------------------------------------------------------------- *)
(* The factorial denominators: prod_r m_r! <= S^S when the sum of the m_r is *)
(* at most S (FACT k <= S^k for k <= S); monotonicity of (2 L + S)^S.        *)
(* ------------------------------------------------------------------------- *)

let SHARP_FACT_NPRODUCT_LE = prove
 (`!s (m:A->num) S.
     FINITE s /\ nsum s m <= S ==> nproduct s (\r. FACT(m r)) <= S EXP S`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC LE_TRANS `nproduct s (\r:A. S EXP (m r))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:A` THEN DISCH_TAC THEN MATCH_MP_TAC FACT_LE_POW THEN
    TRANS_TAC LE_TRANS `nsum s (m:A->num)` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:A->num`; `s:A->bool`; `r:A`] NSUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ASM_SIMP_TAC[GSYM EXP_NSUM] THEN REWRITE_TAC[LE_EXP] THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let SHARP_ARITH_LIN_POW_MONO = prove
 (`!L S1 S2. S1 <= S2 ==> (&2 * &L + &S1) pow S1 <= (&2 * &L + &S2) pow S2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `S2 = 0` THENL
   [SUBGOAL_THEN `S1 = 0` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(&2 * &L + &S2) pow S1` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Integer coefficients bb r = Cx(b r): the nodes and the Delta products are *)
(* complex integers (their size (4B+2)^|m| 2^((n-1)L) is                     *)
(* SHARP_CPRODUCT_DELTA_BOUND of Baker/sharp_aux.ml).                        *)
(* ------------------------------------------------------------------------- *)

let SHARP_X_INTEGER = prove
 (`!n (b:num->real) mu r.
        integer(b n) /\ integer(b r)
        ==> complex_integer(sharp_x n (\r. Cx(b r)) mu r)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_x] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN
  ASM_REWRITE_TAC[COMPLEX_INTEGER_CX; COMPLEX_INTEGER_CX_NUM]);;

let SHARP_DELTA_PRODUCT_INTEGER = prove
 (`!n (b:num->real) (mu:num->num) (m:num->num).
        1 <= n /\ (!r. r IN 1..n ==> integer(b r))
        ==> complex_integer
             (cproduct(1..n-1)
               (\r. feldman_delta (m r) (sharp_x n (\r. Cx(b r)) mu r)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_INTEGER_CPRODUCT THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `b:num->real`; `mu:num->num`; `r:num`]
         SHARP_X_INTEGER) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC o
             GEN_REWRITE_RULE I [COMPLEX_INTEGER]) THEN
  ASM_SIMP_TAC[FELDMAN_DELTA_INTEGER]);;

(* ------------------------------------------------------------------------- *)
(* The two Delta representations (sharp_deltarep). Integer coefficients:     *)
(* the Delta product itself is the constant integer polynomial (multiplier   *)
(* 1, degree 0, size (4B+2)^s 2^((n-1)Lm)). Algebraic coefficients: the      *)
(* polynomial prod_r prod_(j<=m_r) (x_r + j) of SHARP_DELTA_INTPOLY          *)
(* (multiplier prod_r m_r! <= s^s, degree s, size (2Lm+s)^s).                *)
(* ------------------------------------------------------------------------- *)

let SHARP_DELTAREP_W_POS = prove
 (`!n bb Lm W E Mb M. sharp_deltarep n bb Lm W E Mb M ==> !s. &0 <= W s`,
  REWRITE_TAC[sharp_deltarep] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `(W:num->real) 0` THEN ASM_SIMP_TAC[LE_0] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\r:num. 0`) THEN
  DISCH_THEN(MP_TAC o SPEC `\r:num. 0` o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[LE_0; NSUM_0] THEN MESON_TAC[INTPOLY_BOUND_POS]);;

let SHARP_DELTAREP_INT = prove
 (`!n (b:num->real) B Lm.
     1 <= n /\ &0 <= B /\ (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= B)
     ==> sharp_deltarep n (\r. Cx(b r)) Lm
           (\s. (&4 * B + &2) pow s * &2 pow ((n - 1) * Lm)) (\s. 0)
           (\s. &1) (\m. 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_deltarep; LE_REFL; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num->num`; `mu:num->num`] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `b:num->real`; `mu:num->num`; `m:num->num`]
         SHARP_DELTA_PRODUCT_INTEGER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC o
             GEN_REWRITE_RULE I [COMPLEX_INTEGER]) THEN
  EXISTS_TAC `\x:num->complex. Cx c` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LID; COND_ID] THEN
  MATCH_MP_TAC INTPOLY_CONST THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SHARP_CPRODUCT_DELTA_BOUND THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX]);;

let SHARP_DELTAREP_ALG = prove
 (`!n (bb:num->complex) Lm.
     1 <= n
     ==> sharp_deltarep n bb Lm (\s. (&2 * &Lm + &s) pow s) (\s. s)
           (\s. &s pow s) (\m. nproduct(1..n-1) (\r. FACT(m r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharp_deltarep] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SHARP_ARITH_LIN_POW_MONO] THEN
    ASM_CASES_TAC `t = 0` THENL
     [UNDISCH_TAC `s <= t` THEN ASM_REWRITE_TAC[LE] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&t pow s` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC];
    GEN_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`] THEN
      SIMP_TAC[NPRODUCT_EQ_0; FINITE_NUMSEG; FACT_NZ];
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC SHARP_FACT_NPRODUCT_LE THEN
      REWRITE_TAC[FINITE_NUMSEG; LE_REFL];
      REPEAT STRIP_TAC THEN
      EXISTS_TAC
       `\x:num->complex.
          cproduct(1..n-1)
           (\r. cproduct(1..m r)
                 (\j. (Cx(&(mu r)) * x(n + n) - Cx(&(mu n)) * x(n + r)) +
                      Cx(&j)))` THEN
      ASM_SIMP_TAC[SHARP_DELTA_INTPOLY] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC SHARP_DELTA_EVAL THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4. The counterpart at a rational point l/q. The Feldman part times   *)
(* q^(2h(L0+2)) Nq^j (Nq a common multiple of l+q, ..., l+qh) is an integer  *)
(* of size at most q^(2h(L0+2)) NB^j 2^((L0+2)(Nz+h)).                       *)
(* ------------------------------------------------------------------------- *)

let SHARP_FELDMAN_COEFF = prove
 (`!h L0 a b l q Nq NB Nz j.
     a < h /\ b <= L0 /\ 1 <= q /\
     (!i. 1 <= i /\ i <= h ==> (l + q * i) divides Nq) /\
     &Nq <= NB /\ &l / &q + &1 <= &Nz
     ==> ?c. integer c /\
             abs c <= (&q pow (2 * h * (L0 + 2)) * NB pow j) *
                      &2 pow ((L0 + 2) * (Nz + h)) /\
             Cx c = Cx(&q) pow (2 * h * (L0 + 2)) * Cx(&Nq) pow j *
                    (higher_complex_derivative j (feldman_basis h a b)
                       (Cx(&l) / Cx(&q)) / Cx(&(FACT j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `complex_integer
     (Cx(&q) pow (2 * h * (L0 + 2)) * Cx(&Nq) pow j *
      (higher_complex_derivative j (feldman_basis h a b)
         (Cx(&l) / Cx(&q)) / Cx(&(FACT j))))`
  MP_TAC THENL
   [SUBGOAL_THEN `2 * a + 2 * h * (b + 1) <= 2 * h * (L0 + 2)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
       `a < h /\ h * (b + 1) <= h * (L + 1)
        ==> 2 * a + 2 * h * (b + 1) <= 2 * h * (L + 2)`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `Cx(&q) pow (2 * h * (L0 + 2)) =
      Cx(&q) pow (2 * h * (L0 + 2) - (2 * a + 2 * h * (b + 1))) *
      Cx(&q) pow (2 * a + 2 * h * (b + 1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC COMPLEX_INTEGER_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPLEX_INTEGER_POW THEN
      REWRITE_TAC[COMPLEX_INTEGER_CX_NUM];
      MATCH_MP_TAC FELDMAN_BASIS_DERIV_RATIONAL THEN
      ASM_SIMP_TAC[LT_IMP_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_INTEGER] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX;
              REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [SIMP_TAC[REAL_POW_LE; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[REAL_POW_LE; REAL_POS];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
    REWRITE_TAC[NORM_POS_LE];
    MATCH_MP_TAC FELDMAN_BASIS_DERIV_BOUND_UNIFORM THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM]]);;

(* ------------------------------------------------------------------------- *)
(* A term of the counterpart at l/q times q^(2h(L0+2)) Nq^(m 0) M m is an    *)
(* integer polynomial in the joint family theta k = cexp(lg k / q) (k <= n), *)
(* theta(n + r) = bb r: the Feldman integer times the polynomial of the      *)
(* Delta representation times the monomial prod_r theta r^(mu_r l)           *)
(* (CEXP_LINEAR_COMBINATION_RATIONAL); degrees Lv k * l at the alphas and    *)
(* E s at the betas. The same for the whole counterpart.                     *)
(* ------------------------------------------------------------------------- *)

let SHARP_ALGTERM_RAT_INTPOLY = prove
 (`!n h L0 Lv Lm (bb:num->complex) W E Mb M (m:num->num) l q Nq NB Nz
    a b mu.
     1 <= n /\ 1 <= q /\
     (!i. 1 <= i /\ i <= h ==> (l + q * i) divides Nq) /\
     &Nq <= NB /\ &l / &q + &1 <= &Nz /\
     (!r. r IN 1..n ==> Lv r <= Lm) /\
     (a,b,mu) IN sharp_index h L0 Lv n /\
     sharp_deltarep n bb Lm W E Mb M
     ==> ?g. intpoly (1..n+n)
               (\k. if k <= n then Lv k * l else E(nsum(1..n-1) m))
               ((&q pow (2 * h * (L0 + 2)) * NB pow (m 0)) *
                &2 pow ((L0 + 2) * (Nz + h)) * W(nsum(1..n-1) m)) g /\
             !lg. g (\k. if k <= n then cexp(lg k / Cx(&q)) else bb(k - n)) =
                  Cx(&q) pow (2 * h * (L0 + 2)) * Cx(&Nq) pow (m 0) *
                  Cx(&(M m)) *
                  sharp_algterm n h (\x. &1) bb lg m (a,b,mu)
                    (Cx(&l) / Cx(&q))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SHARP_INDEX_BOUNDS) THEN
  MP_TAC(SPECL [`h:num`; `L0:num`; `a:num`; `b:num`; `l:num`; `q:num`;
                `Nq:num`; `NB:real`; `Nz:num`; `(m:num->num) 0`]
         SHARP_FELDMAN_COEFF) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `sharp_deltarep n bb Lm W E Mb M` THEN
  REWRITE_TAC[sharp_deltarep] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num->num` o CONJUNCT2) THEN
  DISCH_THEN(MP_TAC o SPEC `mu:num->num` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LE_TRANS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(num->complex)->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `\x:num->complex. Cx c * g x * cproduct(1..n) (\r. x r pow (mu r * l))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\k. (if k <= n then 0 else E(nsum(1..n-1) m)) +
           (if k IN 1..n then (mu:num->num) k * l else 0)`;
      `abs c * W(nsum(1..n-1) (m:num->num)) * &1`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INTPOLY_CMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTPOLY_MUL THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INTPOLY_MONOMIAL THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET_NUMSEG] THEN ARITH_TAC;
      X_GEN_TAC `k:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_CASES_TAC `k <= n` THEN ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
      SUBGOAL_THEN `(mu:num->num) k <= Lv k` MP_TAC THENL
       [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
      SIMP_TAC[LE_MULT_RCANCEL];
      REWRITE_TAC[REAL_MUL_RID; REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[INTPOLY_BOUND_POS]];
    ALL_TAC] THEN
  X_GEN_TAC `lg:num->complex` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\k. if k <= n then cexp(lg k / Cx(&q)) else (bb:num->complex)(k - n)`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `1 <= r ==> ~(n + r <= n)`; ADD_SUB2];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `cproduct(1..n)
     (\r. (if r <= n then cexp(lg r / Cx(&q)) else (bb:num->complex)(r - n))
          pow (mu r * l)) =
    cexp(Cx(&l) / Cx(&q) * vsum(1..n) (\r. Cx(&(mu r)) * lg r))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[CEXP_LINEAR_COMBINATION_RATIONAL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN SIMP_TAC[IN_NUMSEG];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[sharp_algterm; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let SHARP_ALG_RAT_INTPOLY = prove
 (`!n h L0 Lv Lm (p:num#num#(num->num)->real) (bb:num->complex) W E Mb M
    m l q P Nz Nq NB.
     1 <= n /\ 1 <= q /\
     (!i. 1 <= i /\ i <= h ==> (l + q * i) divides Nq) /\
     &Nq <= NB /\ &l / &q + &1 <= &Nz /\
     (!x. x IN sharp_index h L0 Lv n ==> integer(p x) /\ abs(p x) <= P) /\
     (!r. r IN 1..n ==> Lv r <= Lm) /\
     sharp_deltarep n bb Lm W E Mb M
     ==> ?psi. intpoly (1..n+n)
                 (\k. if k <= n then Lv k * l else E(nsum(1..n-1) m))
                 (&(CARD(sharp_index h L0 Lv n)) * P *
                  (&q pow (2 * h * (L0 + 2)) * NB pow (m 0)) *
                  &2 pow ((L0 + 2) * (Nz + h)) * W(nsum(1..n-1) m)) psi /\
               !lg. psi (\k. if k <= n then cexp(lg k / Cx(&q))
                             else bb(k - n)) =
                    Cx(&q) pow (2 * h * (L0 + 2)) * Cx(&Nq) pow (m 0) *
                    Cx(&(M m)) *
                    sharp_alg n h L0 Lv p bb lg m (Cx(&l) / Cx(&q))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Cb = (&q pow (2 * h * (L0 + 2)) * NB pow (m 0)) *
         &2 pow ((L0 + 2) * (Nz + h)) * (W:num->real)(nsum(1..n-1) m)` THEN
  SUBGOAL_THEN `&0 <= Cb` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= NB` ASSUME_TAC THENL
     [MP_TAC(SPEC `Nq:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "Cb" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    ASM_MESON_TAC[SHARP_DELTAREP_W_POS; REAL_POS; REAL_LE_ADD; REAL_LE_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. !x. x IN sharp_index h L0 Lv n
            ==> intpoly (1..n+n)
                  (\k. if k <= n then Lv k * l else E(nsum(1..n-1) m)) Cb
                  (g x) /\
                !lg. g x (\k. if k <= n then cexp(lg k / Cx(&q))
                              else (bb:num->complex)(k - n)) =
                     Cx(&q) pow (2 * h * (L0 + 2)) * Cx(&Nq) pow (m 0) *
                     Cx(&(M m)) *
                     sharp_algterm n h (\x. &1) bb lg m x
                       (Cx(&l) / Cx(&q))`
  (X_CHOOSE_THEN `g:num#num#(num->num)->(num->complex)->complex`
    (LABEL_TAC "g")) THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
    EXPAND_TAC "Cb" THEN MATCH_MP_TAC SHARP_ALGTERM_RAT_INTPOLY THEN
    MAP_EVERY EXISTS_TAC [`Lm:num`; `Mb:num->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\y:num->complex.
      vsum (sharp_index h L0 Lv n)
       (\x. Cx((p:num#num#(num->num)->real) x) *
            (g:num#num#(num->num)->(num->complex)->complex) x y)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\k. if k <= n then (Lv:num->num) k * l else E(nsum(1..n-1) m)`;
      `sum (sharp_index h L0 Lv n)
        (\x. abs((p:num#num#(num->num)->real) x) * Cb)`] THEN
    REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTPOLY_VSUM THEN REWRITE_TAC[FINITE_SHARP_INDEX] THEN
      X_GEN_TAC `x:num#num#(num->num)` THEN DISCH_TAC THEN
      MATCH_MP_TAC INTPOLY_CMUL THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_SHARP_INDEX] THEN
      X_GEN_TAC `x:num#num#(num->num)` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `lg:num->complex` THEN REWRITE_TAC[sharp_alg] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_SHARP_INDEX] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SHARP_ALGTERM_LINEAR] THEN
  REMOVE_THEN "g" (MP_TAC o SPEC `(a,b,mu):num#num#(num->num)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SPEC `lg:num->complex` o CONJUNCT2) THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Part 5. Lemma 5 (Siegel): integers p, not all 0, |p| <= sharp_psize, such *)
(* that the counterpart vanishes at l = 1..h for all m with |m| <= S0. The   *)
(* equations (l,m) IN (1..h) CROSS Mset are multiplied by N^(m 0) M m (N a   *)
(* common multiple of 1..2h, N <= e^(36h)); alpha degrees mu_r l <= Lv r h,  *)
(* beta degrees E(|m|) <= E S0.                                              *)
(* ------------------------------------------------------------------------- *)

let SHARP_LEMMA5 = prove
 (`!n h L0 Lv Lm (bb:num->complex) (lg:num->complex) (a:num->num->real)
    (dd:num->num) (H:num->real) (ab:num->num->real) (db:num->num) Hb
    W E Mb M S0.
     1 <= n /\ 1 <= h /\
     sharp_algdata n lg a dd H /\ sharpc_coefdata n bb ab db Hb /\
     sharp_deltarep n bb Lm W E Mb M /\
     (!r. r IN 1..n ==> Lv r <= Lm) /\
     2 * (nproduct(1..n) dd * nproduct(1..n) db) * h * (S0 + 1) EXP n <=
     CARD(sharp_index h L0 Lv n)
     ==> ?p. (!x. x IN sharp_index h L0 Lv n
                  ==> integer(p x) /\
                      abs(p x) <= sharp_psize n h L0 Lv S0 H Hb W E) /\
             ~(!x. x IN sharp_index h L0 Lv n ==> p x = &0) /\
             (!m l. nsum(0..n-1) m <= S0 /\ 1 <= l /\ l <= h
                    ==> sharp_alg n h L0 Lv p bb lg m (Cx(&l)) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [sharp_deltarep]) THEN
  FIRST_ASSUM(ASSUME_TAC o GEN_ALL o CONJUNCT1 o SPEC_ALL o CONJUNCT2 o
              GEN_REWRITE_RULE I [sharp_deltarep]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SHARP_DELTAREP_W_POS) THEN
  MP_TAC(SPEC `2 * h` NUMSEG_COMMON_MULTIPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC
   `Mset = {m:num->num | m IN cartesian_product (0..n-1) (\i. 0..S0) /\
                         nsum(0..n-1) m <= S0}` THEN
  ABBREV_TAC `eqs = (1..h) CROSS (Mset:(num->num)->bool)` THEN
  MP_TAC(SPECL [`n:num`; `S0:num`] SHARP_MSET_FINITE_CARD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE(eqs:num#(num->num)->bool) /\ CARD eqs <= h * (S0 + 1) EXP n`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eqs" THEN
    ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; CARD_CROSS; CARD_NUMSEG_1;
                 LE_MULT_LCANCEL];
    ALL_TAC] THEN
  ABBREV_TAC
   `U = exp(&36 * &h * &S0) * &2 pow ((L0 + 2) * (2 * h + 1)) *
        (W:num->real) S0` THEN
  SUBGOAL_THEN
   `?g. !i x. i IN eqs /\ x IN sharp_index h L0 Lv n
              ==> intpoly (1..n+n)
                    (\k. if k <= n then Lv k * h else (E:num->num) S0) U
                    (g i x) /\
                  g i x (\k. if k <= n then cexp(lg k)
                             else (bb:num->complex)(k - n)) =
                  Cx(&N) pow (SND i 0) *
                  Cx(&((M:(num->num)->num) (SND i))) *
                  sharp_algterm n h (\x. &1) bb lg (SND i) x
                    (Cx(&(FST i)))`
  (X_CHOOSE_THEN `g:num#(num->num)->num#num#(num->num)->
                    (num->complex)->complex` (LABEL_TAC "g")) THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`l:num`; `m:num->num`; `a':num`; `b':num`; `mu:num->num`] THEN
    EXPAND_TAC "eqs" THEN EXPAND_TAC "Mset" THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM; IN_NUMSEG; FST; SND] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `h:num`; `L0:num`; `Lv:num->num`; `Lm:num`;
                   `bb:num->complex`; `W:num->real`; `E:num->num`;
                   `Mb:num->real`; `M:(num->num)->num`;
                   `m:num->num`; `l:num`; `1`; `N:num`;
                   `exp(&18 * &(2 * h))`; `l + 1`; `a':num`; `b':num`;
                   `mu:num->num`] SHARP_ALGTERM_RAT_INTPOLY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LE_REFL; MULT_CLAUSES; REAL_DIV_1; REAL_OF_NUM_ADD;
                      REAL_LE_REFL] THEN
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_DIV_1; COMPLEX_POW_ONE; COMPLEX_MUL_LID;
                REAL_POW_ONE; REAL_MUL_LID] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:(num->complex)->complex` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\k. if k <= n then (Lv:num->num) k * l else E(nsum(1..n-1) m)`;
      `exp(&18 * &(2 * h)) pow (m 0) *
       &2 pow ((L0 + 2) * ((l + 1) + h)) *
       (W:num->real)(nsum(1..n-1) m)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(m:num->num) 0 + nsum(1..n-1) m <= S0` ASSUME_TAC THENL
     [SUBGOAL_THEN `nsum(0..n-1) m = (m:num->num) 0 + nsum(1..n-1) m`
      ASSUME_TAC THENL
       [SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES]; ASM_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[LE_MULT_LCANCEL] THENL
       [ASM_ARITH_TAC;
        SUBGOAL_THEN `nsum(1..n-1) m <= S0` ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          MP_TAC(ASSUME `!s t. s <= t
                         ==> (W:num->real) s <= W t /\ (E:num->num) s <= E t /\
                             (Mb:num->real) s <= Mb t`) THEN
          DISCH_THEN(MP_TAC o SPECL [`nsum(1..n-1) m`; `S0:num`]) THEN
          ASM_SIMP_TAC[]]];
      ALL_TAC] THEN
    EXPAND_TAC "U" THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_EXP_POS_LE];
      REWRITE_TAC[GSYM REAL_EXP_N; REAL_EXP_MONO_LE] THEN
      SUBGOAL_THEN `&h * &((m:num->num) 0) <= &h * &S0` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [SIMP_TAC[REAL_POW_LE; REAL_POS];
        MATCH_MP_TAC REAL_POW_MONO THEN
        REWRITE_TAC[REAL_OF_NUM_LE; LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `nsum(1..n-1) m <= S0` ASSUME_TAC THENL
         [ASM_ARITH_TAC;
          MP_TAC(ASSUME `!s t. s <= t
                         ==> (W:num->real) s <= W t /\ (E:num->num) s <= E t /\
                             (Mb:num->real) s <= Mb t`) THEN
          DISCH_THEN(MP_TAC o SPECL [`nsum(1..n-1) m`; `S0:num`]) THEN
          ASM_SIMP_TAC[]]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`n:num`; `lg:num->complex`; `a:num->num->real`; `dd:num->num`;
    `H:num->real`; `bb:num->complex`; `ab:num->num->real`; `db:num->num`;
    `Hb:real`; `\r. (Lv:num->num) r * h`; `(E:num->num) S0`; `U:real`;
    `g:num#(num->num)->num#num#(num->num)->(num->complex)->complex`;
    `eqs:num#(num->num)->bool`; `sharp_index h L0 Lv n`]
   SHARP_JOINT_SIEGEL) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_SHARP_INDEX; SHARP_INDEX_NONEMPTY] THEN
    TRANS_TAC LE_TRANS
     `2 * (nproduct(1..n) dd * nproduct(1..n) db) * h * (S0 + 1) EXP n` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:num#num#(num->num)->real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "b")
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "v"))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:num#num#(num->num)` THEN DISCH_TAC THEN
    REMOVE_THEN "b" (MP_TAC o SPEC `x:num#num#(num->num)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_binary "real_le" o concl)) THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[sharp_psize; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num->num`; `l:num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP SHARP_ALG_RESTRICT (ASSUME `1 <= n`))] THEN
  ABBREV_TAC `m' = RESTRICTION (0..n-1) (m:num->num)` THEN
  SUBGOAL_THEN `(l,m') IN (eqs:num#(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "eqs" THEN EXPAND_TAC "Mset" THEN EXPAND_TAC "m'" THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM; IN_NUMSEG; NSUM_RESTRICTION] THEN
    ASM_REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    TRANS_TAC LE_TRANS `nsum(0..n-1) m` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:num->num`; `0..n-1`; `i:num`] NSUM_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  REMOVE_THEN "v" (MP_TAC o SPEC `(l,m'):num#(num->num)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum (sharp_index h L0 Lv n)
     (\x. Cx((p:num#num#(num->num)->real) x) *
          g (l,m') x (\k. if k <= n then cexp(lg k)
                          else (bb:num->complex)(k - n))) =
    (Cx(&N) pow (m' 0) * Cx(&((M:(num->num)->num) m'))) *
    sharp_alg n h L0 Lv p bb lg m' (Cx(&l))`
  SUBST1_TAC THENL
   [REWRITE_TAC[sharp_alg] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_SHARP_INDEX] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':num`; `b':num`; `mu:num->num`] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SHARP_ALGTERM_LINEAR] THEN
    USE_THEN "g" (MP_TAC o SPECL [`(l,m'):num#(num->num)`;
                                  `(a',b',mu):num#num#(num->num)`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[FST; SND]] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[COMPLEX_MUL_AC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ;
               ARITH_RULE `1 <= x ==> ~(x = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 6 (arithmetic part): a non-zero value of the counterpart at an      *)
(* integer l >= 1 is at least sharp_liou5. N^(m 0) M m times the value is an *)
(* integer polynomial in the joint family (N a common multiple of            *)
(* l+1..l+h, N <= (e^19 (l+h)/h)^h, M m <= Mb S0).                           *)
(* ------------------------------------------------------------------------- *)

let SHARP_DICHOTOMY = prove
 (`!n h L0 Lv Lm (p:num#num#(num->num)->real) (bb:num->complex)
    (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real)
    (ab:num->num->real) (db:num->num) Hb W E Mb M P S0 m l.
     1 <= n /\ 1 <= h /\ 1 <= l /\
     (!x. x IN sharp_index h L0 Lv n ==> integer(p x) /\ abs(p x) <= P) /\
     sharp_algdata n lg a dd H /\ sharpc_coefdata n bb ab db Hb /\
     sharp_deltarep n bb Lm W E Mb M /\
     (!r. r IN 1..n ==> Lv r <= Lm) /\
     nsum(0..n-1) m <= S0 /\
     ~(sharp_alg n h L0 Lv p bb lg m (Cx(&l)) = Cx(&0))
     ==> sharp_liou5 n h L0 Lv P S0 dd H db Hb W E Mb l <=
         norm(sharp_alg n h L0 Lv p bb lg m (Cx(&l)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `N5 = exp(&19) * (&l + &h) / &h` THEN
  MP_TAC(SPECL [`l:num`; `h:num`] SHIFTED_COMMON_MULTIPLE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= N5` ASSUME_TAC THENL
   [EXPAND_TAC "N5" THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&19` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      REWRITE_TAC[GSYM real_div] THEN
      SUBGOAL_THEN `&0 < &h` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:num->num) 0 <= S0 /\ nsum(1..n-1) m <= S0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `nsum(0..n-1) m = (m:num->num) 0 + nsum(1..n-1) m`
    ASSUME_TAC THENL
     [SIMP_TAC[NSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES]; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P` ASSUME_TAC THENL
   [MP_TAC(SPECL [`h:num`; `L0:num`; `Lv:num->num`; `n:num`]
           SHARP_INDEX_NONEMPTY) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:num#num#(num->num)`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num#num#(num->num)`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sharp_deltarep]) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SHARP_DELTAREP_W_POS) THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L0:num`; `Lv:num->num`; `Lm:num`;
                 `p:num#num#(num->num)->real`; `bb:num->complex`;
                 `W:num->real`; `E:num->num`; `Mb:num->real`;
                 `M:(num->num)->num`;
                 `m:num->num`; `l:num`; `1`; `P:real`; `l + 1`;
                 `N:num`; `N5 pow h`] SHARP_ALG_RAT_INTPOLY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_REFL; MULT_CLAUSES; REAL_DIV_1; REAL_OF_NUM_ADD;
                    REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_DIV_1; COMPLEX_POW_ONE; COMPLEX_MUL_LID;
              REAL_POW_ONE; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:(num->complex)->complex`
   (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `lg:num->complex`))) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`n:num`; `lg:num->complex`; `a:num->num->real`; `dd:num->num`;
    `H:num->real`; `bb:num->complex`; `ab:num->num->real`; `db:num->num`;
    `Hb:real`; `\r. (Lv:num->num) r * l`; `(E:num->num) S0`;
    `&(CARD(sharp_index h L0 Lv n)) * P * N5 pow (h * S0) *
     &2 pow ((L0 + 2) * ((l + 1) + h)) * (W:num->real) S0`;
    `psi:(num->complex)->complex`] SHARP_JOINT_LIOUVILLE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTPOLY_MONO THEN
      MAP_EVERY EXISTS_TAC
       [`\k. if k <= n then (Lv:num->num) k * l else E(nsum(1..n-1) m)`;
        `&(CARD(sharp_index h L0 Lv n)) * P * (N5 pow h) pow (m 0) *
         &2 pow ((L0 + 2) * ((l + 1) + h)) *
         (W:num->real)(nsum(1..n-1) m)`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        COND_CASES_TAC THEN ASM_MESON_TAC[LE_REFL];
        MATCH_MP_TAC REAL_LE_MUL_5 THEN REPEAT CONJ_TAC THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN
        ASM_SIMP_TAC[REAL_POS; REAL_LE_REFL; REAL_LE_ADD; REAL_LE_MUL;
                     REAL_POW_LE; REAL_ARITH `&1 <= x ==> &0 <= x`] THEN
        REWRITE_TAC[REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_MONO THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL]];
      REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ;
                  REAL_OF_NUM_EQ] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> ~(x = 0)`]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[sharp_liou5; ASSUME `exp(&19) * (&l + &h) / &h = N5`] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_INV_MUL_LE_FROM_MUL THEN
  EXISTS_TAC `&N pow (m 0) * &((M:(num->num)->num) m)` THEN
  REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> 0 < x`]];
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [SIMP_TAC[REAL_POW_LE; REAL_POS];
      TRANS_TAC REAL_LE_TRANS `(N5 pow h) pow (m 0)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
        REWRITE_TAC[REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_MONO THEN
        ASM_REWRITE_TAC[LE_MULT_LCANCEL]];
      REWRITE_TAC[REAL_POS];
      ASM_MESON_TAC[REAL_LE_TRANS]];
    FIRST_X_ASSUM(MP_TAC o check (is_binary "real_le" o concl)) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX;
                    REAL_ABS_NUM; REAL_MUL_ASSOC]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 8 (arithmetic part): a non-zero value of the counterpart at l/q is  *)
(* at least sharp_lb8. The value times q^(2h(L0+2)) Nq^(m 0) M m (Nq a       *)
(* common multiple of 1..l+qh, M m <= Mb(|m|)) is an integer polynomial in   *)
(* the roots cexp(lg r / q) of a r(X^q) (SHARP_ALGDATA_ROOT) and the betas.  *)
(* ------------------------------------------------------------------------- *)

let SHARP_LEMMA8 = prove
 (`!n h L0 Lv Lm (p:num#num#(num->num)->real) (bb:num->complex)
    (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real)
    (ab:num->num->real) (db:num->num) Hb W E Mb M m l q P Nz.
     1 <= n /\ 1 <= h /\ 1 <= q /\
     (!x. x IN sharp_index h L0 Lv n ==> integer(p x) /\ abs(p x) <= P) /\
     sharp_algdata n lg a dd H /\ sharpc_coefdata n bb ab db Hb /\
     sharp_deltarep n bb Lm W E Mb M /\
     (!r. r IN 1..n ==> Lv r <= Lm) /\
     &l / &q + &1 <= &Nz /\
     ~(sharp_alg n h L0 Lv p bb lg m (Cx(&l) / Cx(&q)) = Cx(&0))
     ==> sharp_lb8 n h L0 Lv P dd H db Hb W E Mb m l q Nz <=
         norm(sharp_alg n h L0 Lv p bb lg m (Cx(&l) / Cx(&q)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sharp_deltarep]) THEN
  MP_TAC(SPEC `l + q * h` NUMSEG_COMMON_MULTIPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `Nq:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!i. 1 <= i /\ i <= h ==> (l + q * i) divides Nq`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_ADD_LCANCEL; LE_MULT_LCANCEL;
                    ARITH_RULE `1 <= x <=> ~(x = 0)`; ADD_EQ_0; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L0:num`; `Lv:num->num`; `Lm:num`;
                 `p:num#num#(num->num)->real`; `bb:num->complex`;
                 `W:num->real`; `E:num->num`; `Mb:num->real`;
                 `M:(num->num)->num`;
                 `m:num->num`; `l:num`; `q:num`; `P:real`; `Nz:num`;
                 `Nq:num`; `exp(&18 * &(l + q * h))`]
         SHARP_ALG_RAT_INTPOLY) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:(num->complex)->complex`
   (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `lg:num->complex`))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &((M:(num->num)->num) m)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> 0 < x`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`n:num`; `\r. (lg:num->complex) r / Cx(&q)`;
    `\r j. if q divides j then (a:num->num->real) r (j DIV q) else &0`;
    `\r. q * (dd:num->num) r`; `H:num->real`; `bb:num->complex`;
    `ab:num->num->real`; `db:num->num`; `Hb:real`;
    `\r. (Lv:num->num) r * l`; `(E:num->num)(nsum(1..n-1) m)`;
    `&(CARD(sharp_index h L0 Lv n)) * P *
     (&q pow (2 * h * (L0 + 2)) * exp(&18 * &(l + q * h)) pow (m 0)) *
     &2 pow ((L0 + 2) * (Nz + h)) * (W:num->real)(nsum(1..n-1) m)`;
    `psi:(num->complex)->complex`] SHARP_JOINT_LIOUVILLE) THEN
  ASM_SIMP_TAC[SHARP_ALGDATA_ROOT] THEN ANTS_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> ~(x = 0)`] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  REWRITE_TAC[sharp_lb8] THEN MATCH_MP_TAC REAL_DIV_LE_FROM_MUL THEN
  EXISTS_TAC
   `&q pow (2 * h * (L0 + 2)) * &Nq pow (m 0) * &((M:(num->num)->num) m)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THENL
     [REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
      MATCH_MP_TAC PRODUCT_POW_GE_1 THEN
      UNDISCH_TAC `sharp_algdata n lg a dd H` THEN
      REWRITE_TAC[sharp_algdata] THEN MESON_TAC[];
      MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
      MATCH_MP_TAC SHARPC_COEFDATA_HB_GE_1 THEN
      MAP_EVERY EXISTS_TAC
       [`n:num`; `bb:num->complex`; `ab:num->num->real`; `db:num->num`] THEN
      ASM_REWRITE_TAC[]];
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC REAL_POW_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_POS];
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o check (is_binary "real_le" o concl)) THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX;
                REAL_ABS_NUM; REAL_MUL_ASSOC]]);;
