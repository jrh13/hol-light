(* ========================================================================= *)
(* Two logarithms, the Laurent bound: binomial coefficients as               *)
(* shifted polynomials, and the zero lemma with binomial rows.               *)
(*                                                                           *)
(* Purpose: the binomial C(x, k) is a polynomial of degree k in x / b2 - eta *)
(* with top coefficient b2^k / k! (real and complex forms); with the         *)
(* triangular row change the determinant of the binomial rows C(x_j, k)      *)
(* y_l(j) is the product of the top coefficients times the determinant of    *)
(* the rows (x_j / b2 - eta)^k y_l(j). Hence the non-vanishing minor of the  *)
(* power matrix (TL_ZERO_RANK_MINOR of Baker/twolog_zero.ml) transfers to    *)
(* the binomial matrix C(r b2 + s b1, k) a1^(l r) a2^(l s) of M. Laurent,    *)
(* Acta Arith. 66 (1994) and 133 (2008), and a non-vanishing minor has       *)
(* distinct columns (an input of the g-lemma).                               *)
(*                                                                           *)
(* Main results: REAL_BINOM_PRODUCT, BINOM_SHIFT_CPOLY, BINOM_SHIFT_POLY,    *)
(* BINOM_CDET_ROW_CHANGE, BINOM_RDET_ROW_CHANGE, TL_ZERO_RANK_MINOR_BINOM    *)
(* (complex a_i), BINOM_ZERO_MINOR_REAL (real a_i), TWOLOG_ZERO_MINOR_BINOM  *)
(* (rational a_i), BINOM_MINOR_COLUMNS_DISTINCT.                             *)
(*                                                                           *)
(* Uses: Baker/laurent_det.ml (CDET_TRIANGULAR_ROWS, RDET_TRIANGULAR_ROWS),  *)
(* Baker/twolog_zero.ml (TL_ZERO_POLY_CPRODUCT, TL_ZERO_RANK_MINOR,          *)
(* TL_ZERO_CARD_CX_RECT, TL_ZERO_CARD_REAL_RECT), Baker/twolog_det.ml        *)
(* (CDET_CX), Library/ring_det.ml (RING_DET_IDENTICAL_COLUMNS),              *)
(* BINOM_BOTTOM_STEP_REAL of Library/binomial.ml.                            *)
(* ========================================================================= *)

needs "Baker/twolog_zero.ml";;
needs "Baker/laurent_det.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Binomial coefficients as products of linear factors.                      *)
(* ------------------------------------------------------------------------- *)

let REAL_BINOM_PRODUCT = prove
 (`!x k. &(binom(x,k)) = product(1..k) (\t. (&x + &1) - &t) / &(FACT k)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[binom; FACT; PRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC k`] THEN
  REWRITE_TAC[ADD1; BINOM_BOTTOM_STEP_REAL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM ADD1; FACT; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `~(&(FACT k) = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ]; CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* A product of k linear factors a x + d i is a polynomial of degree k with  *)
(* top coefficient a^k.                                                      *)
(* ------------------------------------------------------------------------- *)

let BINOM_LINEAR_CPRODUCT = prove
 (`!k (a:complex) (d:num->complex).
        ?w. w k = a pow k /\
            !x. cproduct(1..k) (\i. a * x + d i) =
                vsum(0..k) (\t. w t * x pow t)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`k:num`; `\i:num. 1`;
                 `\i:num t:num. if t = 0 then (d:num->complex) i else a`]
    TL_ZERO_POLY_CPRODUCT) THEN
  REWRITE_TAC[NSUM_CONST_NUMSEG; CPRODUCT_CONST_NUMSEG; ARITH_EQ;
              ARITH_RULE `((k + 1) - 1) * 1 = k /\ (k + 1) - 1 = k`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:num->complex` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:complex` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CPRODUCT_EQ THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_POW_1; ARITH_EQ] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The binomial C(x,k) as a polynomial of degree k in x / b2 - eta: each     *)
(* factor (x + 1) - t equals b2 (x / b2 - eta) + (b2 eta + 1 - t), so the    *)
(* top coefficient is b2^k / k!. Complex form (any complex eta), then the    *)
(* real form by taking real parts.                                           *)
(* ------------------------------------------------------------------------- *)

let BINOM_SHIFT_CPOLY = prove
 (`!k b2 eta.
     1 <= b2
     ==> ?c. c k = Cx(&b2 pow k / &(FACT k)) /\
             !x. Cx(&(binom(x,k))) =
                 vsum(0..k) (\t. c t * (Cx(&x / &b2) - eta) pow t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&b2) = Cx(&0))` ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN
    UNDISCH_TAC `1 <= b2` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `Cx(&b2)`;
                 `\t:num. Cx(&b2) * eta + Cx(&1) - Cx(&t)`]
    BINOM_LINEAR_CPRODUCT) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. (w:num->complex) t / Cx(&(FACT k))` THEN
  ASM_REWRITE_TAC[CX_DIV; CX_POW] THEN X_GEN_TAC `x:num` THEN
  REWRITE_TAC[REAL_BINOM_PRODUCT; CX_DIV] THEN
  SIMP_TAC[CX_PRODUCT; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `cproduct(1..k) (\i. Cx((&x + &1) - &i)) =
    cproduct(1..k) (\i. Cx(&b2) * (Cx(&x) / Cx(&b2) - eta) +
                        (\t. Cx(&b2) * eta + Cx(&1) - Cx(&t)) i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[CX_SUB; CX_ADD] THEN
    UNDISCH_TAC `~(Cx(&b2) = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[complex_div; GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let BINOM_SHIFT_POLY = prove
 (`!k b2 eta.
     1 <= b2
     ==> ?c. c k = &b2 pow k / &(FACT k) /\
             !x. &(binom(x,k)) = sum(0..k) (\t. c t * (&x / &b2 - eta) pow t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `b2:num`; `Cx eta`] BINOM_SHIFT_CPOLY) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. Re((c:num->complex) t)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[RE_CX]; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Re` o SPEC `x:num`) THEN
  REWRITE_TAC[RE_CX] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_POW; RE_MUL_CX]);;

(* ------------------------------------------------------------------------- *)
(* Binomial rows: with rows (k, l) = ((i - 1) MOD K, (i - 1) DIV K) the      *)
(* matrix C(x_j, k) y_l(j) has the determinant of (x_j / b2 - eta)^k y_l(j)  *)
(* times the product of the top coefficients b2^k / k! (triangular row       *)
(* change CDET_TRIANGULAR_ROWS / RDET_TRIANGULAR_ROWS of                     *)
(* Baker/laurent_det.ml).                                                    *)
(* ------------------------------------------------------------------------- *)

let BINOM_CDET_ROW_CHANGE = prove
 (`!K L b2 (eta:complex) (x:num->num) (y:num->num->complex).
     1 <= b2
     ==> ring_det complex_ring (1..K * L)
              (\i j. Cx(&(binom(x j,(i - 1) MOD K))) * y ((i - 1) DIV K) j) =
         cproduct(1..K * L)
                 (\i. Cx(&b2 pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K)))) *
         ring_det complex_ring (1..K * L)
              (\i j. (Cx(&(x j) / &b2) - eta) pow ((i - 1) MOD K) *
                     y ((i - 1) DIV K) j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `k:num` (ISPECL [`k:num`; `b2:num`; `eta:complex`]
    BINOM_SHIFT_CPOLY)) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num->complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th]))) THEN
  MP_TAC(ISPECL [`K:num`; `L:num`; `c:num->num->complex`;
                 `\j. Cx(&((x:num->num) j) / &b2) - eta`;
                 `y:num->num->complex`] CDET_TRIANGULAR_ROWS) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let BINOM_RDET_ROW_CHANGE = prove
 (`!K L b2 (eta:real) (x:num->num) (y:num->num->real).
     1 <= b2
     ==> ring_det real_ring (1..K * L)
              (\i j. &(binom(x j,(i - 1) MOD K)) * y ((i - 1) DIV K) j) =
         product(1..K * L)
                (\i. &b2 pow ((i - 1) MOD K) / &(FACT((i - 1) MOD K))) *
         ring_det real_ring (1..K * L)
              (\i j. (&(x j) / &b2 - eta) pow ((i - 1) MOD K) *
                     y ((i - 1) DIV K) j)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `k:num` (ISPECL [`k:num`; `b2:num`; `eta:real`]
    BINOM_SHIFT_POLY)) THEN
  ASM_REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->num->real`
    (CONJUNCTS_THEN2 ASSUME_TAC (fun th -> REWRITE_TAC[th]))) THEN
  MP_TAC(ISPECL [`K:num`; `L:num`; `c:num->num->real`;
                 `\j. &((x:num->num) j) / &b2 - eta`;
                 `y:num->num->real`] RDET_TRIANGULAR_ROWS) THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Small bookkeeping lemmas for the transfer of the zero lemma.              *)
(* ------------------------------------------------------------------------- *)

let BINOM_GRID_NONEMPTY = prove
 (`!(f:num->num->A) R S n.
        n < CARD {f r s | r,s | r < R /\ s < S} ==> 1 <= R /\ 1 <= S`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `(~q ==> ~p) ==> p ==> q`) THEN
  REWRITE_TAC[ARITH_RULE `~(1 <= R /\ 1 <= S) <=> R = 0 \/ S = 0`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[LT] THEN
  REWRITE_TAC[SET_RULE `{(f:num->num->A) r s | r,s | F} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; LT]);;

let BINOM_REAL_OF_NUM_LINEAR = prove
 (`!b1 b2 r s. (&b2:real) * &r + &b1 * &s = &(r * b2 + s * b1)`,
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The zero lemma with binomial rows, complex form (for the algebraic case): *)
(* TL_ZERO_RANK_MINOR and the triangular row change with                     *)
(* C(x,k) = x^k / k! + lower terms.                                          *)
(* ------------------------------------------------------------------------- *)

let TL_ZERO_RANK_MINOR_BINOM = prove
 (`!a1 a2 b1 b2 K L R1 S1 R2 S2.
     ~(a1 = Cx(&0)) /\ ~(a2 = Cx(&0)) /\
     L <= CARD {a1 pow r * a2 pow s | r,s | r < R1 /\ s < S1} /\
     (K - 1) * L < CARD {r * b2 + s * b1 | r,s | r < R2 /\ s < S2}
     ==> ?rr ss.
           (!j. j IN 1..K * L
                ==> rr j < (R1 + R2) - 1 /\ ss j < (S1 + S2) - 1) /\
           (!j j'. j IN 1..K * L /\ j' IN 1..K * L /\
                   rr j = rr j' /\ ss j = ss j' ==> j = j') /\
           ~(ring_det complex_ring (1..K * L)
               (\i j. Cx(&(binom(rr j * b2 + ss j * b1,(i - 1) MOD K))) *
                      a1 pow (((i - 1) DIV K) * rr j) *
                      a2 pow (((i - 1) DIV K) * ss j)) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP BINOM_GRID_NONEMPTY) THEN
  SUBGOAL_THEN
   `(K - 1) * L < CARD {(&b2:real) * &r + &b1 * &s | r,s | r < R2 /\ s < S2}`
  ASSUME_TAC THENL
   [REWRITE_TAC[BINOM_REAL_OF_NUM_LINEAR; TL_ZERO_CARD_REAL_RECT] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:complex`; `a2:complex`; `&b1:real`; `&b2:real`;
                 `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    TL_ZERO_RANK_MINOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rr:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ss:num->num` THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `j:num` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= R2`; `1 <= S2`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:num`; `L:num`; `1`; `Cx(&0)`;
                 `\j. (rr:num->num) j * b2 + (ss:num->num) j * b1`;
                 `\l j. (a1:complex) pow (l * (rr:num->num) j) *
                        (a2:complex) pow (l * (ss:num->num) j)`]
    BINOM_CDET_ROW_CHANGE) THEN
  REWRITE_TAC[LE_REFL; REAL_DIV_1; COMPLEX_SUB_RZERO; REAL_POW_ONE] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_POW; BINOM_REAL_OF_NUM_LINEAR;
              COMPLEX_ENTIRE; DE_MORGAN_THM] THEN
  REWRITE_TAC[MULT_SYM] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
  REWRITE_TAC[CX_INJ; REAL_DIV_EQ_0; REAL_OF_NUM_EQ; FACT_NZ; ARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Real forms: real a_i (the algebraic case at the real embedding) and the   *)
(* rational form TWOLOG_ZERO_MINOR_BINOM.                                    *)
(* ------------------------------------------------------------------------- *)

let BINOM_ZERO_MINOR_REAL = prove
 (`!(x1:real) (x2:real) b1 b2 K L R1 S1 R2 S2.
     ~(x1 = &0) /\ ~(x2 = &0) /\
     L <= CARD {x1 pow r * x2 pow s | r,s | r < R1 /\ s < S1} /\
     (K - 1) * L < CARD {r * b2 + s * b1 | r,s | r < R2 /\ s < S2}
     ==> ?rr ss.
           (!j. j IN 1..K * L
                ==> rr j < (R1 + R2) - 1 /\ ss j < (S1 + S2) - 1) /\
           (!j j'. j IN 1..K * L /\ j' IN 1..K * L /\
                   rr j = rr j' /\ ss j = ss j' ==> j = j') /\
           ~(ring_det real_ring (1..K * L)
               (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                      x1 pow (((i - 1) DIV K) * rr j) *
                      x2 pow (((i - 1) DIV K) * ss j)) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`Cx x1`; `Cx x2`; `b1:num`; `b2:num`; `K:num`; `L:num`;
                 `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    TL_ZERO_RANK_MINOR_BINOM) THEN
  REWRITE_TAC[CX_INJ; GSYM CX_POW; GSYM CX_MUL; TL_ZERO_CARD_CX_RECT;
              CDET_CX] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]);;

let TWOLOG_ZERO_MINOR_BINOM = prove
 (`!p1 q1 p2 q2 b1 b2 K L R1 S1 R2 S2.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     1 <= K /\ 1 <= L /\
     L <= CARD {(&p1 / &q1) pow r * (&p2 / &q2) pow s | r,s |
                r < R1 /\ s < S1} /\
     (K - 1) * L < CARD {r * b2 + s * b1 | r,s | r < R2 /\ s < S2}
     ==> ?rr ss.
           (!j. j IN 1..K * L
                ==> rr j < (R1 + R2) - 1 /\ ss j < (S1 + S2) - 1) /\
           ~(ring_det real_ring (1..K * L)
               (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                      (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
                      (&p2 / &q2) pow (((i - 1) DIV K) * ss j)) = &0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`&p1 / &q1`; `&p2 / &q2`; `b1:num`; `b2:num`;
                 `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    BINOM_ZERO_MINOR_REAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_DIV_EQ_0; REAL_OF_NUM_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`1 <= p1`; `1 <= q1`; `1 <= p2`; `1 <= q2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rr:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ss:num->num` THEN
  MATCH_ACCEPT_TAC(TAUT `a /\ b /\ c ==> a /\ c`));;

(* ------------------------------------------------------------------------- *)
(* A non-zero minor has distinct columns (the injectivity hypothesis of the  *)
(* g-lemma TWOLOG_G_LEMMA): two equal columns give a vanishing determinant.  *)
(* ------------------------------------------------------------------------- *)

let BINOM_MINOR_COLUMNS_DISTINCT = prove
 (`!N K b1 b2 (x1:real) (x2:real) (rr:num->num) (ss:num->num).
     ~(ring_det real_ring (1..N)
         (\i j. &(binom(rr j * b2 + ss j * b1,(i - 1) MOD K)) *
                x1 pow (((i - 1) DIV K) * rr j) *
                x2 pow (((i - 1) DIV K) * ss j)) = &0)
     ==> !j j'. j IN 1..N /\ j' IN 1..N /\ rr j = rr j' /\ ss j = ss j'
                ==> j = j'`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `j':num`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`real_ring`; `1..N`;
    `\i j. &(binom((rr:num->num) j * b2 + (ss:num->num) j * b1,
                   (i - 1) MOD K)) *
           (x1:real) pow (((i - 1) DIV K) * rr j) *
           (x2:real) pow (((i - 1) DIV K) * ss j)`;
    `j:num`; `j':num`] RING_DET_IDENTICAL_COLUMNS) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; REAL_RING_CLAUSES]);;
