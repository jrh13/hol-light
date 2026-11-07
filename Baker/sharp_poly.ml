(* ========================================================================= *)
(* Sharpening I: Delta-functions and polynomial lemmas.                      *)
(*                                                                           *)
(* Purpose: tools for the auxiliary function of Baker, Sharpening I (Acta    *)
(* Arith. 21 (1972) 117-129). The Delta-functions                            *)
(* Delta(z;m) = (z+1)...(z+m)/m! (feldman_delta of Baker/delta.ml) satisfy   *)
(* z Delta(z;m) = (m+1)(Delta(z;m+1) - Delta(z;m)), are integers at all      *)
(* integers, have size (4B+2)^m 2^L on |z| <= 2BL (Baker binomial trick),    *)
(* span the polynomials of degree <= L and separate tensor products of       *)
(* distinct nodes (tensor Lagrange argument). Further: a multiplicity count  *)
(* for polynomials and for combinations of the Feldman basis, integrality of *)
(* the normalized derivatives of the Feldman basis at rationals, and a prime *)
(* in (n, 2^70 n] (from MERTENS of Examples/mangoldt.ml).                    *)
(*                                                                           *)
(* Main results: FELDMAN_DELTA_MUL_SHIFT (the identity above),               *)
(*   FELDMAN_DELTA_INTEGER, FELDMAN_DELTA_SIZE, FELDMAN_DELTA_SPAN,          *)
(*   FELDMAN_DELTA_TENSOR_SEPARATION, POLYFUN_MULTIPLE_ROOTS_ZERO,           *)
(*   FELDMAN_BASIS_MULTIPLE_ZEROS, FELDMAN_BASIS_DERIV_RATIONAL,             *)
(*   PRIME_IN_INTERVAL.                                                      *)
(*                                                                           *)
(* Uses: Baker/delta.ml (feldman_delta, feldman_basis,                       *)
(*   CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN,                                 *)
(*   HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR), Baker/sec4.ml (exact degrees *)
(*   of the Feldman basis), Baker/prelim.ml (complex integers),              *)
(*   Baker/algebraic.ml (CPRODUCT_LINEAR_POLYFUN), Baker/intpoly.ml          *)
(*   (VSUM_CPRODUCT_CARTESIAN_PRODUCT), sets.ml                              *)
(*   (FINITE_CARTESIAN_PRODUCT_FINITE),                                      *)
(*   Baker/expoly.ml (COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN).                 *)
(* ========================================================================= *)

needs "Baker/sec4.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The key identity z Delta(z;m) = (m+1)(Delta(z;m+1) - Delta(z;m)).         *)
(* ------------------------------------------------------------------------- *)

let FELDMAN_DELTA_MUL_SHIFT = prove
 (`!m z. z * feldman_delta m z =
         Cx(&(m + 1)) * (feldman_delta (m + 1) z - feldman_delta m z)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[feldman_delta; GSYM ADD1; CPRODUCT_CLAUSES_NUMSEG; FACT;
              ARITH_RULE `1 <= SUC m`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  MP_TAC(SPEC `m:num` FACT_NZ) THEN MP_TAC(SPEC `m:num` NOT_SUC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  SPEC_TAC(`Cx(&(FACT m))`,`f:complex`) THEN
  SPEC_TAC(`Cx(&(SUC m))`,`s:complex`) THEN
  SPEC_TAC(`cproduct(1..m) (\j. z + Cx(&j))`,`p:complex`) THEN
  CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Delta(x;m) is an integer at every integer x (also x < 0), by the          *)
(* Pascal recurrence Delta(z;m+1) = Delta(z+1;m+1) - Delta(z+1;m).           *)
(* ------------------------------------------------------------------------- *)

let FELDMAN_DELTA_0 = prove
 (`!z. feldman_delta 0 z = Cx(&1)`,
  REWRITE_TAC[feldman_delta; CPRODUCT_CLAUSES_NUMSEG; ARITH; FACT;
              COMPLEX_DIV_1]);;

let CPRODUCT_SHIFT1_NUMSEG = prove
 (`!m z. cproduct(1..m+1) (\j. z + Cx(&j)) =
         (z + Cx(&1)) * cproduct(1..m) (\j. (z + Cx(&1)) + Cx(&j))`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; NUMSEG_SING; CPRODUCT_SING;
                CPRODUCT_CLAUSES_NUMSEG; ARITH] THEN
    CONV_TAC COMPLEX_RING;
    ASM_REWRITE_TAC[ARITH_RULE `SUC m + 1 = SUC(m + 1)`;
                    CPRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD; CX_ADD] THEN
    CONV_TAC COMPLEX_RING]);;

let FELDMAN_DELTA_PASCAL = prove
 (`!m z. feldman_delta (m + 1) z =
         feldman_delta (m + 1) (z + Cx(&1)) - feldman_delta m (z + Cx(&1))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`m:num`; `z:complex`] CPRODUCT_SHIFT1_NUMSEG) THEN
  REWRITE_TAC[feldman_delta; GSYM ADD1; CPRODUCT_CLAUSES_NUMSEG; FACT;
              ARITH_RULE `1 <= SUC m`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  MP_TAC(SPEC `m:num` FACT_NZ) THEN MP_TAC(SPEC `m:num` NOT_SUC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  SPEC_TAC(`Cx(&(FACT m))`,`f:complex`) THEN
  SPEC_TAC(`Cx(&(SUC m))`,`s:complex`) THEN
  SPEC_TAC(`cproduct(1..m) (\j. z + Cx(&j))`,`p:complex`) THEN
  SPEC_TAC(`cproduct(1..m) (\j. (z + Cx(&1)) + Cx(&j))`,`q:complex`) THEN
  CONV_TAC COMPLEX_FIELD);;

let FELDMAN_DELTA_NEG_NUM = prove
 (`!n m. complex_integer(feldman_delta m (--Cx(&n)))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[COMPLEX_NEG_0; FELDMAN_DELTA_NUM; COMPLEX_INTEGER_CX_NUM];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REWRITE_TAC[FELDMAN_DELTA_0; COMPLEX_INTEGER_CX_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `--Cx(&(n + 1)) + Cx(&1) = --Cx(&n)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[ADD1] THEN
  ONCE_REWRITE_TAC[FELDMAN_DELTA_PASCAL] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC COMPLEX_INTEGER_SUB THEN ASM_REWRITE_TAC[]);;

let FELDMAN_DELTA_INTEGER = prove
 (`!m x. integer x ==> complex_integer(feldman_delta m (Cx x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INTEGER_CASES] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[FELDMAN_DELTA_NUM; COMPLEX_INTEGER_CX_NUM; CX_NEG;
                  FELDMAN_DELTA_NEG_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Size of Delta(z;m) on |z| <= 2BL (Baker binomial trick):                  *)
(* |z+j| / j <= (1+2B)(1+L/j) and prod_j (1+L/j) = binom(L+m,m) <= 2^(L+m).  *)
(* ------------------------------------------------------------------------- *)

let FELDMAN_DELTA_SIZE = prove
 (`!m z B L. &0 <= B /\ norm z <= &2 * B * &L
             ==> norm(feldman_delta m z) <= (&4 * B + &2) pow m * &2 pow L`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[feldman_delta; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
              REAL_ABS_NUM] THEN
  SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
  TRANS_TAC REAL_LE_TRANS `product(1..m) (\j. (&1 + &2 * B) * (&L + &j))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[NORM_POS_LE] THEN
    TRANS_TAC REAL_LE_TRANS `norm(z:complex) + &j` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(NORM_ARITH
       `norm(w:complex) = j ==> norm(z + w) <= norm z + j`) THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
      MATCH_MP_TAC(REAL_ARITH
       `z <= &2 * B * L /\ &0 <= &2 * B * j /\ &0 <= L
        ==> z + j <= (&1 + &2 * B) * (L + j)`) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_LE_MUL]];
    ALL_TAC] THEN
  REWRITE_TAC[PRODUCT_MUL_NUMSEG; PRODUCT_CONST_NUMSEG_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_NPRODUCT; FINITE_NUMSEG] THEN
  REWRITE_TAC[NPRODUCT_SHIFT_BINOM; GSYM REAL_OF_NUM_MUL] THEN
  SUBGOAL_THEN
   `(&4 * B + &2) pow m * &2 pow L = (&1 + &2 * B) pow m * &2 pow (L + m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_ADD; REAL_ARITH `&4 * B + &2 = &2 * (&1 + &2 * B)`;
                REAL_POW_MUL; REAL_MUL_AC];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_RING `(c * t) * f:real = (c * f) * t`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; BINOM_LE_EXP]]);;

(* ------------------------------------------------------------------------- *)
(* A prime in (n, 2^70 n] from the Mertens estimate: otherwise the sums      *)
(* of log p / p up to n and up to 2^70 n coincide, and differ from log n and *)
(* log n + 70 log 2 by at most 24 each, while 70 log 2 > 48.                 *)
(* ------------------------------------------------------------------------- *)

let PRIME_IN_INTERVAL = prove
 (`!n. 1 <= n ==> ?p. prime p /\ n < p /\ p <= 2 EXP 70 * n`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
  PURE_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{p | prime p /\ p <= 2 EXP 70 * n} = {p | prime p /\ p <= n}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    MP_TAC(ARITH_RULE `n <= 2 EXP 70 * n`) THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `2 EXP 70 * n` MERTENS) THEN MP_TAC(SPEC `n:num` MERTENS) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
  SPEC_TAC(`sum {p | prime p /\ p <= n} (\p. log(&p) / &p)`,`s:real`) THEN
  GEN_TAC THEN ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> ~(n = 0)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MP_TAC LOG2_APPROX_32 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Every polynomial of degree <= L is a combination of Delta(z;0..L).        *)
(* ------------------------------------------------------------------------- *)

let FELDMAN_DELTA_POLYFUN = prove
 (`!k. ?d. d k = inv(Cx(&(FACT k))) /\
           !z. feldman_delta k z = vsum(0..k) (\i. d i * z pow i)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`1..k`; `\j. --Cx(&j)`] CPRODUCT_LINEAR_POLYFUN) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; COMPLEX_SUB_RNEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\i. (c:num->complex) i / Cx(&(FACT k))` THEN
  ASM_REWRITE_TAC[feldman_delta; complex_div; COMPLEX_MUL_LID] THEN
  GEN_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

let FELDMAN_DELTA_SPAN = prove
 (`!L (c:num->complex). ?e. !z. vsum(0..L) (\i. c i * z pow i) =
                               vsum(0..L) (\m. e m * feldman_delta m z)`,
  INDUCT_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `c:num->complex` THEN
    REWRITE_TAC[VSUM_SING_NUMSEG; FELDMAN_DELTA_0; complex_pow];
    ALL_TAC] THEN
  X_GEN_TAC `c:num->complex` THEN
  MP_TAC(SPEC `SUC L` FELDMAN_DELTA_POLYFUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->complex` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `\i. (c:num->complex) i - (c(SUC L) * Cx(&(FACT(SUC L)))) * d i`) THEN
  DISCH_THEN(X_CHOOSE_TAC `e:num->complex`) THEN
  EXISTS_TAC `\m. if m = SUC L then c(SUC L) * Cx(&(FACT(SUC L)))
                  else (e:num->complex) m` THEN
  X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  SUBGOAL_THEN
   `vsum(0..L) (\m. (if m = SUC L then c(SUC L) * Cx(&(FACT(SUC L)))
                     else (e:num->complex) m) * feldman_delta m z) =
    vsum(0..L) (\m. e m * feldman_delta m z)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `m <= L ==> ~(m = SUC L)`];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0] THEN
  REWRITE_TAC[COMPLEX_SUB_RDISTRIB; VSUM_SUB_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MP_TAC(SPEC `SUC L` FACT_NZ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  SPEC_TAC(`Cx(&(FACT(SUC L)))`,`f:complex`) THEN
  SPEC_TAC(`vsum(0..L) (\i. (c:num->complex) i * z pow i)`,`s:complex`) THEN
  SPEC_TAC(`vsum(0..L) (\i. (d:num->complex) i * z pow i)`,`t:complex`) THEN
  CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Tensor Lagrange argument: the products of Delta(x_r(mu_r); m_r) over      *)
(* r = 1..n, 0 <= m_r <= L, separate the tuples mu if every row x_r is       *)
(* injective on 0..L. Target nu: q_r(z) = prod_(i <> nu_r) (z - x_r(i)).     *)
(* ------------------------------------------------------------------------- *)

let FELDMAN_DELTA_SPAN_ROOTS = prove
 (`!L (x:num->complex) a.
        a <= L
        ==> ?e. !z. cproduct((0..L) DELETE a) (\i. z - x i) =
                    vsum(0..L) (\m. e m * feldman_delta m z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(0..L) DELETE a`; `x:num->complex`]
         CPRODUCT_LINEAR_POLYFUN) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG; CARD_DELETE; IN_NUMSEG; LE_0;
               CARD_NUMSEG; ARITH_RULE `(L + 1) - 0 - 1 = L`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`L:num`; `c:num->complex`] FELDMAN_DELTA_SPAN) THEN
  ASM_REWRITE_TAC[]);;

let FELDMAN_DELTA_TENSOR_EXPAND = prove
 (`!n L (x:num->num->complex) (W:(num->num)->complex) (e:num->num->complex).
     vsum (cartesian_product (1..n) (\r. 0..L))
       (\m. cproduct(1..n) (\r. e r (m r)) *
            vsum (cartesian_product (1..n) (\r. 0..L))
              (\mu. W mu *
                    cproduct(1..n) (\r. feldman_delta (m r) (x r (mu r))))) =
     vsum (cartesian_product (1..n) (\r. 0..L))
       (\mu. W mu *
             cproduct(1..n)
               (\r. vsum(0..L) (\k. e r k * feldman_delta k (x r (mu r)))))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `FINITE(cartesian_product (1..n) (\r:num. 0..L))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`1..n`; `\r:num. 0..L`;
    `\r k. (e:num->num->complex) r k *
           feldman_delta k ((x:num->num->complex) r ((mu:num->num) r))`]
   VSUM_CPRODUCT_CARTESIAN_PRODUCT) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `m:num->num` THEN DISCH_TAC THEN
  SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `p:complex = p' /\ t = t' ==> p * w * t = w * p' * t'`) THEN
  REWRITE_TAC[]);;

let TENSOR_LAGRANGE_SELECT = prove
 (`!n L (x:num->num->complex) (W:(num->num)->complex) nu.
     nu IN cartesian_product (1..n) (\r. 0..L)
     ==> vsum (cartesian_product (1..n) (\r. 0..L))
           (\mu. W mu *
                 cproduct(1..n)
                  (\r. cproduct((0..L) DELETE (nu r))
                                (\i. x r (mu r) - x r i))) =
         W nu * cproduct(1..n)
                  (\r. cproduct((0..L) DELETE (nu r))
                                (\i. x r (nu r) - x r i))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `vsum (cartesian_product (1..n) (\r. 0..L))
      (\mu. if mu = nu
            then (W:(num->num)->complex) nu *
                 cproduct(1..n)
                  (\r. cproduct((0..L) DELETE (nu r))
                                (\i. (x:num->num->complex) r (nu r) - x r i))
            else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_VEC_0] THEN
    MATCH_MP_TAC(COMPLEX_RING `p = Cx(&0) ==> w * p = Cx(&0)`) THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; FINITE_DELETE] THEN
    SUBGOAL_THEN `?r. r IN 1..n /\ ~((mu:num->num) r = nu r)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[CARTESIAN_PRODUCT_EQ_MEMBERS_EQ]; ALL_TAC] THEN
    EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(mu:num->num) r` THEN
    ASM_REWRITE_TAC[IN_DELETE; COMPLEX_SUB_REFL] THEN
    UNDISCH_TAC `mu IN cartesian_product (1..n) (\r:num. 0..L)` THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT] THEN ASM_MESON_TAC[];
    ASM_REWRITE_TAC[VSUM_DELTA]]);;

let TENSOR_LAGRANGE_NONZERO = prove
 (`!n L (x:num->num->complex) nu.
     (!r i j. 1 <= r /\ r <= n /\ i <= L /\ j <= L /\ x r i = x r j
              ==> i = j) /\
     nu IN cartesian_product (1..n) (\r. 0..L)
     ==> ~(cproduct(1..n)
            (\r. cproduct((0..L) DELETE (nu r)) (\i. x r (nu r) - x r i)) =
           Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. 1 <= r /\ r <= n ==> (nu:num->num) r <= L` ASSUME_TAC THENL
   [UNDISCH_TAC `nu IN cartesian_product (1..n) (\r:num. 0..L)` THEN
    SIMP_TAC[IN_CARTESIAN_PRODUCT; IN_NUMSEG; LE_0];
    ALL_TAC] THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; FINITE_DELETE] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  REWRITE_TAC[IN_NUMSEG; IN_DELETE; COMPLEX_SUB_0] THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `(nu:num->num) r`; `i:num`] o
    check (is_forall o concl)) THEN
  ASM_SIMP_TAC[]);;

let FELDMAN_DELTA_TENSOR_SEPARATION = prove
 (`!n L (x:num->num->complex) (W:(num->num)->complex).
     (!r i j. 1 <= r /\ r <= n /\ i <= L /\ j <= L /\ x r i = x r j
              ==> i = j) /\
     (!m. (!r. 1 <= r /\ r <= n ==> m r <= L)
          ==> vsum (cartesian_product (1..n) (\r. 0..L))
                   (\mu. W mu *
                         cproduct(1..n)
                           (\r. feldman_delta (m r) (x r (mu r)))) =
              Cx(&0))
     ==> !mu. mu IN cartesian_product (1..n) (\r. 0..L) ==> W mu = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `nu:num->num` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `L:num`; `x:num->num->complex`; `nu:num->num`]
         TENSOR_LAGRANGE_NONZERO) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN
   `!r i j. 1 <= r /\ r <= n /\ i <= L /\ j <= L /\
            (x:num->num->complex) r i = x r j ==> i = j`
   (K ALL_TAC) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!r. 1 <= r /\ r <= n ==> (nu:num->num) r <= L` ASSUME_TAC THENL
   [UNDISCH_TAC `nu IN cartesian_product (1..n) (\r:num. 0..L)` THEN
    SIMP_TAC[IN_CARTESIAN_PRODUCT; IN_NUMSEG; LE_0];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e:num->num->complex.
      !r. 1 <= r /\ r <= n
          ==> !z. cproduct((0..L) DELETE (nu r))
                          (\i. z - (x:num->num->complex) r i) =
                  vsum(0..L) (\m. e r m * feldman_delta m z)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FELDMAN_DELTA_SPAN_ROOTS THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(W:(num->num)->complex) nu *
    cproduct(1..n)
      (\r. cproduct((0..L) DELETE (nu r))
                   (\i. (x:num->num->complex) r (nu r) - x r i)) =
    Cx(&0)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `L:num`; `x:num->num->complex`;
                   `W:(num->num)->complex`; `nu:num->num`]
           TENSOR_LAGRANGE_SELECT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    TRANS_TAC EQ_TRANS
     `vsum (cartesian_product (1..n) (\r. 0..L))
        (\m. cproduct(1..n) (\r. (e:num->num->complex) r (m r)) *
             vsum (cartesian_product (1..n) (\r. 0..L))
               (\mu. (W:(num->num)->complex) mu *
                     cproduct(1..n)
                       (\r. feldman_delta (m r)
                              ((x:num->num->complex) r (mu r)))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FELDMAN_DELTA_TENSOR_EXPAND] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
      X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      X_GEN_TAC `m:num->num` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_VEC_0] THEN
      MATCH_MP_TAC(COMPLEX_RING `y = Cx(&0) ==> x * y = Cx(&0)`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `m IN cartesian_product (1..n) (\r:num. 0..L)` THEN
      SIMP_TAC[IN_CARTESIAN_PRODUCT; IN_NUMSEG; LE_0]];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE]]);;

(* ------------------------------------------------------------------------- *)
(* A polynomial of degree <= N vanishing to total order > N (counted         *)
(* with multiplicities) is zero. Induction on N, splitting off a linear      *)
(* factor z - a at a zero a and lowering the multiplicity at a by one.       *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_POLYFUN = prove
 (`!N (c:num->complex) s.
        (\w. vsum(0..N) (\i. c i * w pow i)) holomorphic_on s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
  SIMP_TAC[FINITE_NUMSEG; HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST;
           HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_ID]);;

let HIGHER_DERIVATIVE_LINEAR_FACTOR_ZEROS = prove
 (`!g a z k.
        g holomorphic_on (:complex) /\
        (!j. j < k
             ==> higher_complex_derivative j (\w. (w - a) * g w) z = Cx(&0))
        ==> !j. j < (if z = a then k - 1 else k)
                ==> higher_complex_derivative j g z = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`g:complex->complex`; `(:complex)`; `a:complex`; `j:num`;
                   `a:complex`] HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR) THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_ADD_LID;
                COMPLEX_ENTIRE; CX_INJ; REAL_OF_NUM_EQ; NOT_SUC];
    INDUCT_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[higher_complex_derivative] THEN
      ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_SUB_0];
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `SUC j`) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`g:complex->complex`; `(:complex)`; `a:complex`; `j:num`;
                     `z:complex`]
             HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR) THEN
      ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; COMPLEX_ENTIRE;
                      COMPLEX_SUB_0]]]);;

let NSUM_NONZERO_EXISTS = prove
 (`!s (k:A->num) N. N < nsum s k ==> ?a. a IN s /\ ~(k a = 0)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP NSUM_EQ_0) THEN ARITH_TAC);;

let POLYFUN_ROOTS_MULTIPLICITY_ZERO = prove
 (`!N (c:num->complex) s (k:complex->num).
     FINITE s /\ N < nsum s k /\
     (!z j. z IN s /\ j < k z
            ==> higher_complex_derivative j
                  (\w. vsum(0..N) (\i. c i * w pow i)) z = Cx(&0))
     ==> !i. i <= N ==> c i = Cx(&0)`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC o
    MATCH_MP NSUM_NONZERO_EXISTS) THEN
  (FIRST_ASSUM(MP_TAC o SPECL [`a:complex`; `0`]) THEN ANTS_TAC THENL
    [ASM_REWRITE_TAC[LT_NZ]; REWRITE_TAC[higher_complex_derivative]]) THENL
   [REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID] THEN
    DISCH_TAC THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[LE] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPLEX_POLYFUN_LINEAR_FACTOR_ROOT) THEN
  REWRITE_TAC[SUC_SUB1] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:num->complex`) THEN
  SUBGOAL_THEN
   `(\w. vsum(0..SUC N) (\i. (c:num->complex) i * w pow i)) =
    (\w. (w - a) * vsum(0..N) (\i. b i * w pow i))`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. i <= N ==> (b:num->complex) i = Cx(&0)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:complex->bool` THEN
    EXISTS_TAC `\z. if z = a then (k:complex->num) z - 1 else k z` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:complex->num`; `s:complex->bool`; `a:complex`]
             NSUM_DELETE) THEN
      MP_TAC(ISPECL [`\z. if z = a then (k:complex->num) z - 1 else k z`;
                     `s:complex->bool`; `a:complex`] NSUM_DELETE) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `nsum (s DELETE a) (\z. if z = a then (k:complex->num) z - 1 else k z) =
        nsum (s DELETE a) k`
      SUBST1_TAC THENL
       [MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
      ASM_ARITH_TAC;
      MAP_EVERY X_GEN_TAC [`z:complex`; `j:num`] THEN STRIP_TAC THEN
      MP_TAC(BETA_RULE(ISPECL
       [`\w. vsum(0..N) (\i. (b:num->complex) i * w pow i)`; `a:complex`;
        `z:complex`; `(k:complex->num) z`]
       HIGHER_DERIVATIVE_LINEAR_FACTOR_ZEROS)) THEN
      REWRITE_TAC[HOLOMORPHIC_ON_POLYFUN] THEN ANTS_TAC THENL
       [X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. vsum(0..SUC N) (\i. (c:num->complex) i * z pow i) = Cx(&0)`
  MP_TAC THENL
   [X_GEN_TAC `z:complex` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(COMPLEX_RING `y = Cx(&0) ==> x * y = Cx(&0)`) THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    REWRITE_TAC[COMPLEX_POLYFUN_EQ_0; IN_NUMSEG; LE_0]]);;

let POLYFUN_MULTIPLE_ROOTS_ZERO = prove
 (`!N (c:num->complex) s L.
     FINITE s /\ N < (L + 1) * CARD s /\
     (!z j. z IN s /\ j <= L
            ==> higher_complex_derivative j
                  (\w. vsum(0..N) (\i. c i * w pow i)) z = Cx(&0))
     ==> !i. i <= N ==> c i = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC POLYFUN_ROOTS_MULTIPLICITY_ZERO THEN
  MAP_EVERY EXISTS_TAC [`s:complex->bool`; `\z:complex. L + 1`] THEN
  ASM_SIMP_TAC[NSUM_CONST; ARITH_RULE `j < L + 1 <=> j <= L`] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A combination of the Feldman basis B_ab, a < h, b <= L0, vanishing to     *)
(* order L+1 at CARD s points with h(L0+2) <= (L+1) CARD s is trivial: it is *)
(* a polynomial of degree < h(L0+2), hence zero, and the B_ab have pairwise  *)
(* distinct exact degrees a + h(b+1).                                        *)
(* ------------------------------------------------------------------------- *)

let FELDMAN_BASIS_COMBINATION_POLYFUN = prove
 (`!h L0 (p:num#num->complex).
        ?C. !w. vsum ({a | a < h} CROSS (0..L0))
                     (\(a,b). p(a,b) * feldman_basis h a b w) =
                vsum(0..h * (L0 + 2) - 1) (\i. C i * w pow i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LAMBDA_PAIR] THEN
  MATCH_MP_TAC COMPLEX_POLYFUN_VSUM THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT; FINITE_NUMSEG; FORALL_PAIR_THM;
           IN_CROSS; IN_ELIM_THM; IN_NUMSEG; LE_0; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `a:num`; `b:num`] FELDMAN_BASIS_POLYFUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`feldman_basis h a b`; `e:num->complex`; `a + h * (b + 1)`;
                 `h * (L0 + 2) - 1`; `(p:num#num->complex)(a,b)`; `Cx(&1)`]
         COMPLEX_POLYFUN_SCALE_ARG) THEN
  ASM_SIMP_TAC[FELDMAN_BASIS_DEGREE_BOUND; COMPLEX_DIV_1]);;

let FELDMAN_BASIS_MULTIPLE_ZEROS = prove
 (`!h L0 L s (p:num#num->complex).
     FINITE s /\ h * (L0 + 2) <= (L + 1) * CARD s /\
     (!z j. z IN s /\ j <= L
            ==> higher_complex_derivative j
                  (\w. vsum ({a | a < h} CROSS (0..L0))
                            (\(a,b). p(a,b) * feldman_basis h a b w))
                  z = Cx(&0))
     ==> !a b. a < h /\ b <= L0 ==> p(a,b) = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `h = 0` THEN ASM_REWRITE_TAC[LT] THEN
  MP_TAC(SPECL [`h:num`; `L0:num`; `p:num#num->complex`]
         FELDMAN_BASIS_COMBINATION_POLYFUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:num->complex` MP_TAC) THEN
  REWRITE_TAC[GSYM FUN_EQ_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i. i <= h * (L0 + 2) - 1 ==> (C:num->complex) i = Cx(&0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POLYFUN_MULTIPLE_ROOTS_ZERO THEN
    MAP_EVERY EXISTS_TAC [`s:complex->bool`; `L:num`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `1 <= h * (L0 + 2)` MP_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. vsum ({a | a < h} CROSS (0..L0))
          (\i. (p:num#num->complex) i * feldman_basis h (FST i) (SND i) w) =
        Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:complex` THEN
    FIRST_X_ASSUM(MP_TAC o C AP_THM `w:complex` o check (is_eq o concl)) THEN
    REWRITE_TAC[LAMBDA_PAIR; PAIR] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{a | a < h} CROSS (0..L0)`;
                 `\i:num#num. feldman_basis h (FST i) (SND i)`;
                 `\i:num#num. FST i + h * (SND i + 1)`;
                 `p:num#num->complex`]
         COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT; FINITE_NUMSEG] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; IN_NUMSEG; LE_0;
              PAIR_EQ; FST; SND] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FELDMAN_BASIS_POLYFUN] THEN
    MESON_TAC[FELDMAN_BASIS_DEGREE_INJ];
    MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Normalized derivatives of the Feldman basis at rationals r/q: with N      *)
(* a common multiple of r + q i (1 <= i <= h), the number                    *)
(* q^(2a+2h(b+1)) N^m (D^m B_ab)(r/q) / m! is an integer (by                 *)
(* CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN of Baker/delta.ml for products of  *)
(* linear factors at an arbitrary point x).                                  *)
(* ------------------------------------------------------------------------- *)

let RATIONAL_LINEAR_FACTOR_INTEGER = prove
 (`!q r j N. ~(q = 0) /\ (r + q * j) divides N /\ 1 <= j
             ==> ~(Cx(&r) / Cx(&q) + Cx(&j) = Cx(&0)) /\
                 complex_integer(Cx(&N) / (Cx(&r) / Cx(&q) + Cx(&j)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:num` SUBST1_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r + q * j = 0)` MP_TAC THENL
   [REWRITE_TAC[ADD_EQ_0; MULT_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Cx(&r) / Cx(&q) + Cx(&j) = Cx(&(r + q * j)) / Cx(&q)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL; CX_ADD;
                CX_MUL] THEN
    UNDISCH_TAC `~(q = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SPEC_TAC(`r + q * j`,`d:num`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `Cx(&(d * t)) / (Cx(&d) / Cx(&q)) = Cx(&(q * t))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
    UNDISCH_TAC `~(q = 0)` THEN UNDISCH_TAC `~(d = 0)` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
    ASM_REWRITE_TAC[COMPLEX_INTEGER_CX_NUM; complex_div; COMPLEX_ENTIRE;
                    COMPLEX_INV_EQ_0; CX_INJ; REAL_OF_NUM_EQ]]);;

let FELDMAN_BASIS_DERIV_RATIONAL = prove
 (`!h a b q r N m.
     a <= h /\ ~(q = 0) /\ (!i. 1 <= i /\ i <= h ==> (r + q * i) divides N)
     ==> complex_integer
          (Cx(&q) pow (2 * a + 2 * h * (b + 1)) * Cx(&N) pow m *
           higher_complex_derivative m (feldman_basis h a b)
             (Cx(&r) / Cx(&q)) /
           Cx(&(FACT m)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = ({0} CROSS (1..a)) UNION ((1..b+1) CROSS (1..h))` THEN
  SUBGOAL_THEN `FINITE(U:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    SIMP_TAC[FINITE_UNION; FINITE_CROSS; FINITE_NUMSEG; FINITE_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN U
        ==> ~(Cx(&r) / Cx(&q) + Cx(&(SND(u:num#num))) = Cx(&0)) /\
            complex_integer(Cx(&N) / (Cx(&r) / Cx(&q) + Cx(&(SND u))))`
  ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_UNION; IN_CROSS; IN_SING; IN_NUMSEG;
                SND] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC RATIONAL_LINEAR_FACTOR_INTEGER THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`U:num#num->bool`; `SND:num#num->num`; `Cx(&r) / Cx(&q)`;
                 `Cx(&N)`] CPRODUCT_LINEAR_DERIVATIVE_INTEGER_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  MP_TAC(SPECL [`h:num`; `a:num`; `b:num`; `q:num`; `r:num`]
         FELDMAN_BASIS_RATIONAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `feldman_basis h a b =
    (\w. inv(Cx(&(FACT a * FACT h EXP (b + 1)))) *
         cproduct U (\u. w + Cx(&(SND(u:num#num)))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FELDMAN_BASIS_CPRODUCT] THEN
    ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z. cproduct U (\u. z + Cx(&(SND(u:num#num))))`;
                 `inv(Cx(&(FACT a * FACT h EXP (b + 1))))`; `(:complex)`;
                 `m:num`; `Cx(&r) / Cx(&q)`]
         HIGHER_COMPLEX_DERIVATIVE_LMUL) THEN
  REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN ANTS_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_ADD; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `~(cproduct U (\u. Cx(&r) / Cx(&q) + Cx(&(SND(u:num#num)))) = Cx(&0))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CPRODUCT_EQ_0] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPLEX_INTEGER_MUL) THEN
  MATCH_MP_TAC(MESON[]
   `x = y ==> complex_integer x ==> complex_integer y`) THEN
  MP_TAC(SPEC `m:num` FACT_NZ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  SUBGOAL_THEN `~(Cx(&(FACT a * FACT h EXP (b + 1))) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; MULT_EQ_0; EXP_EQ_0; FACT_NZ];
    ALL_TAC] THEN
  UNDISCH_TAC
   `~(cproduct U (\u. Cx(&r) / Cx(&q) + Cx(&(SND(u:num#num)))) = Cx(&0))` THEN
  SPEC_TAC(`cproduct U (\u. Cx(&r) / Cx(&q) + Cx(&(SND(u:num#num))))`,
           `p:complex`) THEN
  SPEC_TAC(`higher_complex_derivative m
             (\z. cproduct U (\u. z + Cx(&(SND(u:num#num)))))
             (Cx(&r) / Cx(&q))`,
           `d:complex`) THEN
  SPEC_TAC(`Cx(&(FACT a * FACT h EXP (b + 1)))`,`k:complex`) THEN
  SPEC_TAC(`Cx(&(FACT m))`,`f:complex`) THEN
  SPEC_TAC(`Cx(&q) pow (2 * a + 2 * h * (b + 1))`,`e:complex`) THEN
  SPEC_TAC(`Cx(&N) pow m`,`n:complex`) THEN
  CONV_TAC COMPLEX_FIELD);;
