(* ========================================================================= *)
(* The Schinzel-Tijdeman theorem for every integer polynomial with two       *)
(* distinct complex roots, and its finiteness corollaries.                   *)
(*                                                                           *)
(* Purpose: A. Schinzel and R. Tijdeman, On the equation y^m = P(x), Acta    *)
(* Arith. 31 (1976): if f(x) = sum_{i<=N} a_i x^i has integer coefficients   *)
(* and two distinct complex roots z1, z2 (of any multiplicities, conjugate   *)
(* or not), then the exponent m in y^m = f(x) with integers x, y and         *)
(* abs y >= 2 is bounded by a constant depending on f only                   *)
(* (SCHINZEL_TIJDEMAN). With two simple roots the solutions with m >= 3 are  *)
(* finitely many (SCHINZEL_TIJDEMAN_FINITE; the CARD form                    *)
(* SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS for m >= m0 >= 2, three simple      *)
(* roots if m0 = 2), and x^2 + D = y^n with D <> 0 has only finitely many    *)
(* solutions with abs y >= 2, n >= 2 (SQUARE_PLUS_POW_FINITE). There is no   *)
(* hypothesis on the leading coefficient: the coefficients are trimmed to    *)
(* the exact degree first (POLY_TRIM_EXACT_DEGREE); the zero polynomial has  *)
(* no solution with abs y >= 2.                                              *)
(*                                                                           *)
(* Route. After the monic scaling X = a_N x the equation reads               *)
(* c y^m = F(X), F monic with the distinct roots Z1 = a_N z1, Z2 = a_N z2.   *)
(* At each root the S-unit descent                                           *)
(* SCHINZEL_TIJDEMAN_ROOT_DESCENT gives (X - Z_i)^k_i =                      *)
(* prod_{v in W_i} v^(e_i v) xi_i^m with e_i v < m, a fixed finite set W_i   *)
(* and a fixed integer D_i making D_i xi_i integral                          *)
(* (SCHINZEL_TIJDEMAN_GEN_FIXED_DATA). In the field M = Q(Z1, Z2) the        *)
(* exponentials of both sides give the linear form                           *)
(*                                                                           *)
(*   k1 k2 Log((X - Z1)/(X - Z2)) = sum k2 e1(v) Log v - sum k1 e2(w) Log w  *)
(*                                  + m Log(xi1^k2 / xi2^k1) + t Log(-1)     *)
(*                                                                           *)
(* with an integer t, abs t <= c m (imaginary parts;                         *)
(* SCHINZEL_TIJDEMAN_GEN_LINEAR_FORM). Its fixed numbers are the elements of *)
(* W1 UNION W2 UNION {-1}, enumerated once by 1..CARD, and its only variable *)
(* number is xi = xi1^k2 / xi2^k1. The form is O(1/abs X) and non-zero       *)
(* (SCHINZEL_TIJDEMAN_GEN_LAMBDA_SMALL). The embeddings of M, applied to the *)
(* descent identities, bound the conjugates of xi by exp(c L / m) with       *)
(* L = log(abs X + R0) (SCHINZEL_TIJDEMAN_GEN_EMBED_BOUNDS); the denominator *)
(* of 1/xi2 is the lowest non-zero coefficient of an integer polynomial      *)
(* vanishing at xi2 (COMPLEX_SUBFIELD_ELEMENT_POLY and                       *)
(* SHARP_NFBOUND_INV_ROOT), and the sharp_nfbound calculus combines the      *)
(* denominators and conjugate bounds (SCHINZEL_TIJDEMAN_GEN_VARIABLE).       *)
(* SHARP_BAKER_NUMBER_FIELD then gives log abs X <= C log A log(c m) with    *)
(* log A <= c1 L / m + c2 (SCHINZEL_TIJDEMAN_GEN_BAKER_STEP,                 *)
(* SCHINZEL_TIJDEMAN_GEN_LOG_A), while m log 2 <= N log abs X + C4: hence    *)
(* m <= c3 log m (SCHINZEL_TIJDEMAN_GEN_CHAIN), and finitely many small X    *)
(* are handled by SCHINZEL_TIJDEMAN_FINITE_X. Multiple and conjugate roots   *)
(* need no special treatment. Finiteness: SUPERELLIPTIC_SIMPLE_ROOTS for     *)
(* each exponent up to the bound (SCHINZEL_TIJDEMAN_FINITE is the case       *)
(* m0 = 3 of SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS); for x^2 + D = y^2 both  *)
(* factors of D = (y - x) (y + x) are bounded by abs D. The reducible case   *)
(* (two roots separated by an integer polynomial, for                        *)
(* instance roots with different minimal polynomials) follows at once: a     *)
(* separating polynomial gives z1 <> z2                                      *)
(* (SCHINZEL_TIJDEMAN_SEPARATING_DISTINCT).                                  *)
(*                                                                           *)
(* Main results: SCHINZEL_TIJDEMAN, SCHINZEL_TIJDEMAN_FINITE,                *)
(* SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS, SQUARE_PLUS_POW_FINITE; the monic  *)
(* form SCHINZEL_TIJDEMAN_GENERAL_MONIC; helper names                        *)
(* SCHINZEL_TIJDEMAN_GEN_*; the corollaries SCHINZEL_TIJDEMAN_REDUCIBLE,     *)
(* SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE, SCHINZEL_TIJDEMAN_REDUCIBLE_MULT      *)
(* (the reducible case).                                                     *)
(*                                                                           *)
(* Uses: Baker/schinzel_sunit.ml (SCHINZEL_TIJDEMAN_ROOT_DESCENT),           *)
(* Baker/ant_bridge_complex.ml (COMPLEX_SUBFIELD_RING_PRODUCT),              *)
(* Baker/sharp_tools.ml                                                      *)
(* (COMPLEX_SUBFIELD_ELEMENT_POLY, COMPLEX_EMBEDDING_POLY_ROOT,              *)
(* SHARP_NFBOUND_INV_ROOT, SHARP_NFBOUND_POW, SHARP_NFBOUND_MUL),            *)
(* Baker/sharp_defs.ml (sharp_nfbound), Baker/sharp_main.ml                  *)
(* (SHARP_BAKER_NUMBER_FIELD), Baker/kummer.ml (VSUM_DELTA_CX),              *)
(* Baker/schinzel_mult.ml (SCHINZEL_TIJDEMAN_MULT_ROOT_DATA,                 *)
(* SCHINZEL_TIJDEMAN_MULT_F_BOUND, SCHINZEL_TIJDEMAN_MULT_DEGREE_POS),       *)
(* Baker/schinzel.ml (SCHINZEL_TIJDEMAN_MONIC_SCALING,                       *)
(* SCHINZEL_TIJDEMAN_FINITE_X, SCHINZEL_TIJDEMAN_LOG_LOWER),                 *)
(* Baker/superell.ml (SUPERELL_MONIC_CVALUE), Baker/hyperell.ml              *)
(* (SUPERELLIPTIC_SIMPLE_ROOTS, HYPERELL_MAIN_SIMPLE_ROOTS_2),               *)
(* Baker/prime_factors.ml (POLY_TRIM_EXACT_DEGREE,                           *)
(* SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA), Baker/ant_bridge_complex.ml      *)
(* (NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED, BRIDGE_NF_HOM_INTEGER,          *)
(* BRIDGE_NF_SUBFIELD_RATIONAL), ANT/complex_embeddings.ml                   *)
(* (complex_embeddings, FINITE_COMPLEX_EMBEDDINGS,                           *)
(* COMPLEX_EMBEDDINGS_MONOMORPHISM), Baker/algint.ml                         *)
(* (ALGEBRAIC_INTEGER_EXPLICIT, ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER),     *)
(* Baker/lemmas.ml (LOG_POLY_BOUND, EXP_NEG_LE_RATIO, EXP_1_LE_3,            *)
(* REAL_LE_1_MUL, REAL_INV_LE_FROM_MUL, REAL_FRAC_LE_CROSS,                  *)
(* CLOG_ONE_PLUS_NZ, CLOG_ONE_PLUS_SMALL, IM_CLOG_ABS_LE_PI); library:       *)
(* Library/fieldtheory.ml (SUBFIELD_GENERATED_MONO,                          *)
(* SUBFIELD_GENERATED_INC_GEN, FIELD_SUBFIELD_GENERATED, the                 *)
(* RING_*_IN_SUBFIELD_GENERATED and RING_*_SUBFIELD_GENERATED clauses),      *)
(* Library/ringtheory.ml (RING_HOMOMORPHISM_SUB, _MUL, _POW, _PRODUCT,       *)
(* FIELD_HOMOMORPHISM_INV, RING_MONOMORPHISM_EQ_0),                          *)
(* Multivariate/complex_ring.ml (complex_ring, COMPLEX_RING_PRODUCT),        *)
(* Multivariate/transcendentals.ml (CEXP_EQ, CEXP_CLOG, CLOG_NEG_1,          *)
(* CEXP_VSUM), 100/transcendence.ml (complex_field_clauses).                 *)
(* ========================================================================= *)

needs "Baker/sharp_main.ml";;
needs "Baker/hyperell.ml";;
needs "Baker/prime_factors.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Numeric lemmas: an exponent bounded by a logarithm, the inequality chain  *)
(* of the final step, and the logarithm of the size A of the variable        *)
(* number.                                                                   *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_GEN_LOG_LINEAR = prove
 (`!K1 K2. ?M. !m. 1 <= m /\ &m <= K1 + K2 * log(&m) ==> m <= M`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`abs(K1:real) + abs(K2:real)`; `1`] LOG_POLY_BOUND) THEN
  REWRITE_TAC[REAL_POW_1] THEN
  DISCH_THEN(X_CHOOSE_TAC `M0:real`) THEN
  MP_TAC(SPEC `M0:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M1:num`) THEN
  EXISTS_TAC `MAX 3 M1` THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `m < 3` THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&m)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3` THEN
    REWRITE_TAC[EXP_1_LE_3; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(K1:real) <= abs K1 * log(&m) /\
    (K2:real) * log(&m) <= abs K2 * log(&m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `m <= M1 ==> m <= MAX 3 M1`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `M0:real` THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* The final chain: Baker (exp(-C log A log(cB m)) <= L), the smallness      *)
(* L <= C1 / abs X, the size log A <= c1 log(abs X + R0) / m + c2 and the    *)
(* lower bound m log 2 <= DN log abs X + C4 bound the exponent m.            *)

let SCHINZEL_TIJDEMAN_GEN_CHAIN = prove
 (`!C C1 c1 c2 cB DN C4 R0.
     &0 < C1 /\ &0 <= c1 /\ &0 <= c2 /\ &2 <= cB /\ &0 <= R0 /\ &0 <= DN
     ==> ?M. !X m A L.
           1 <= m /\ &1 + R0 <= abs X /\ exp(&1) <= A /\
           log A <= c1 * (log(abs X + R0) / &m) + c2 /\
           exp(--(C * log A * log(cB * &m))) <= L /\ L <= C1 / abs X /\
           &m * log(&2) <= DN * log(abs X) + C4
           ==> m <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL
   [`(DN * (&2 * abs(log C1) + log(&2) + &2 * abs C * c2 * log cB) +
      abs C4) / log(&2)`;
    `(&2 * DN * abs C * c2) / log(&2)`] SCHINZEL_TIJDEMAN_GEN_LOG_LINEAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `MA:num` (LABEL_TAC "MA")) THEN
  MP_TAC(SPECL [`&2 * abs C * c1 * log cB`; `&2 * abs C * c1`]
    SCHINZEL_TIJDEMAN_GEN_LOG_LINEAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `MB:num` (LABEL_TAC "MB")) THEN
  EXISTS_TAC `MAX MA MB` THEN
  MAP_EVERY X_GEN_TAC [`X:real`; `m:num`; `A:real`; `L:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= log A` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(cB * &m) = log cB + log(&m)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= log cB /\ &0 <= log(&m) /\ &0 <= log(abs X)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(cB * &m)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(abs X + R0) <= log(&2) + log(abs X)` ASSUME_TAC THENL
   [SUBGOAL_THEN `log(&2) + log(abs X) = log(&2 * abs X)` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the Baker bound with abs C *)
  SUBGOAL_THEN `log(abs X) <= log C1 + abs C * log A * log(cB * &m)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EXP_NEG_LE_RATIO THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(--(C * log A * log(cB * &m)))` THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* log A in terms of log abs X *)
  SUBGOAL_THEN
   `abs C * log A * log(cB * &m) <=
    (abs C * log(cB * &m)) *
    (c1 * ((log(&2) + log(abs X)) / &m) + c2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `abs C * log A * log(cB * &m) = (abs C * log(cB * &m)) * log A`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c1 * (log(abs X + R0) / &m) + c2` THEN
    ASM_REWRITE_TAC[REAL_LE_RADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `&2 * abs C * c1 * log(cB * &m) <= &m` THENL
   [ALL_TAC;
    MATCH_MP_TAC(ARITH_RULE `m <= MB ==> m <= MAX MA MB`) THEN
    REMOVE_THEN "MB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(&2 * abs C * c1 * log(cB * &m) <= &m)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `m <= MA ==> m <= MAX MA MB`) THEN
  REMOVE_THEN "MA" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(abs C * log(cB * &m)) * (c1 * ((log(&2) + log(abs X)) / &m)) <=
    (log(&2) + log(abs X)) / &2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(abs C * log(cB * &m)) * (c1 * ((log(&2) + log(abs X)) / &m)) =
      ((abs C * c1 * log(cB * &m)) * (log(&2) + log(abs X))) / &m`
    SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; ASSUME `&1 <= &m`;
             REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    MP_TAC(SPECL [`&2 * abs C * c1 * log(cB * &m)`; `&m`;
                  `log(&2) + log(abs X)`] REAL_LE_RMUL) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(abs X) <= &2 * log C1 + log(&2) + &2 * abs C * c2 * log(cB * &m)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`log(abs X) <= log C1 + abs C * log A * log(cB * &m)`;
      `abs C * log A * log(cB * &m) <=
       (abs C * log(cB * &m)) * (c1 * ((log(&2) + log(abs X)) / &m) + c2)`;
      `(abs C * log(cB * &m)) * (c1 * ((log(&2) + log(abs X)) / &m)) <=
       (log(&2) + log(abs X)) / &2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DN * log(abs X) <=
    DN * (&2 * log C1 + log(&2) + &2 * abs C * c2 * log(cB * &m)) /\
    DN * log C1 <= DN * abs(log C1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; REAL_ARITH
   `(a:real) * i + (b * i) * x = (a + b * x) * i`] THEN
  REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; ASSUME `&0 < log(&2)`] THEN
  UNDISCH_TAC
   `DN * log(abs X) <=
    DN * (&2 * log C1 + log(&2) + &2 * abs C * c2 * log(cB * &m))` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`&m * log(&2) <= DN * log(abs X) + C4`;
    `DN * log C1 <= DN * abs(log C1)`] THEN
  REAL_ARITH_TAC);;

let SCHINZEL_TIJDEMAN_GEN_LE_PROD3 = prove
 (`!e b h. &1 <= e /\ &1 <= b /\ &1 <= h
           ==> b <= e * b * h /\ h <= e * b * h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e - &1`; `b * h:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`b:real`; `h - &1`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`b - &1`; `h:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`b:real`; `h:real`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* The size A = e DB HB of the variable number (denominator bound DB,        *)
(* conjugate bound HB) and its logarithm, linear in                          *)
(* TX = log(abs X + R0) / m.                                                 *)

let SCHINZEL_TIJDEMAN_GEN_LOG_A = prove
 (`!D1 D2 R1 k1 k2 w1 w2 DM TX.
     &1 <= D1 /\ &1 <= D2 /\ &1 <= R1 /\ &0 <= TX
     ==> exp(&1) <=
         exp(&1) *
         (D1 pow k2 *
          ((&2 * D2 * exp(&k2 * TX) * R1 pow w2) pow DM) pow k1) *
         ((exp(&k1 * TX) * R1 pow w1) pow k2 * (R1 pow w2) pow k1) /\
         log(exp(&1) *
             (D1 pow k2 *
              ((&2 * D2 * exp(&k2 * TX) * R1 pow w2) pow DM) pow k1) *
             ((exp(&k1 * TX) * R1 pow w1) pow k2 * (R1 pow w2) pow k1)) =
         (&(k1 * k2) * (&DM + &1)) * TX +
         (&1 + &k2 * log D1 + &k1 * &DM * (log(&2) + log D2 + &w2 * log R1) +
          (&k2 * &w1 + &k1 * &w2) * log R1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x. &0 <= x ==> &1 <= exp x` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_POW_LE_1) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `D1 = exp(log D1) /\ D2 = exp(log D2) /\ R1 = exp(log R1) /\
    &2 = exp(log(&2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[GSYM REAL_EXP_N; GSYM REAL_EXP_ADD; LOG_EXP] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sums over the fixed numbers W1 UNION W2 UNION {-1}: an enumeration by     *)
(* 1..CARD, sums of indicator coefficients, positive bounds for finitely     *)
(* many non-zero values, and the bound for the coefficients of the linear    *)
(* form.                                                                     *)
(* ------------------------------------------------------------------------- *)

(* A finite set of complex numbers enumerated by 1..CARD.                    *)

let SCHINZEL_TIJDEMAN_GEN_ENUMERATE = prove
 (`!t:complex->bool.
     FINITE t
     ==> ?en. (!j. j IN 1..CARD t ==> en j IN t) /\
              (!f:complex->complex.
                 vsum t f = vsum(1..CARD t) (\j. f(en j)))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `t:complex->bool` FINITE_INDEX_NUMSEG) THEN
  ASM_REWRITE_TAC[] THEN ABBREV_TAC `n = CARD(t:complex->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `en:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `en:num->complex` THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let SCHINZEL_TIJDEMAN_GEN_VSUM_INDICATOR = prove
 (`!t w (f:complex->real) (h:complex->complex).
     FINITE t /\ w SUBSET t
     ==> vsum t (\u. Cx(if u IN w then f u else &0) * h u) =
         vsum w (\u. Cx(f u) * h u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum (w:complex->bool)
     (\u. Cx(if u IN w then (f:complex->real) u else &0) *
          (h:complex->complex) u)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[]]);;

let SCHINZEL_TIJDEMAN_GEN_VSUM_SPLIT = prove
 (`!W1 W2 (f1:complex->real) f2 t0.
     FINITE W1 /\ FINITE W2
     ==> vsum (W1 UNION W2 UNION {--Cx(&1)})
              (\u. Cx((if u IN W1 then f1 u else &0) -
                      (if u IN W2 then f2 u else &0) +
                      (if u = --Cx(&1) then t0 else &0)) * clog u) =
         vsum W1 (\v. Cx(f1 v) * clog v) - vsum W2 (\w. Cx(f2 w) * clog w) +
         Cx t0 * clog(--Cx(&1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `t = W1 UNION W2 UNION {--Cx(&1)}` THEN
  SUBGOAL_THEN
   `FINITE(t:complex->bool) /\ W1 SUBSET t /\ W2 SUBSET t /\ --Cx(&1) IN t`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN
    REWRITE_TAC[FINITE_UNION; FINITE_SING; ASSUME `FINITE(W1:complex->bool)`;
                ASSUME `FINITE(W2:complex->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CX_ADD; CX_SUB; COMPLEX_ADD_RDISTRIB; COMPLEX_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[VSUM_ADD; VSUM_SUB; FINITE_UNION; FINITE_SING] THEN
  ASM_SIMP_TAC[SCHINZEL_TIJDEMAN_GEN_VSUM_INDICATOR; VSUM_DELTA_CX]);;

(* Finitely many non-zero values f g v lie in [inv R, R] for one R >= 1      *)
(* (here g ranges over the embeddings and v over W1 UNION W2).               *)

let SCHINZEL_TIJDEMAN_GEN_NORM_BOUNDS = prove
 (`!(f:A->B->complex) E W.
     FINITE E /\ FINITE W /\
     (!g v. g IN E /\ v IN W ==> ~(f g v = Cx(&0)))
     ==> ?R. &1 <= R /\
             !g v. g IN E /\ v IN W
                   ==> inv R <= norm(f g v) /\ norm(f g v) <= R`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\p:A#B. norm((f:A->B->complex) (FST p) (SND p)) +
             inv(norm(f (FST p) (SND p)))`;
    `(E:A->bool) CROSS (W:B->bool)`] UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_SIMP_TAC[FINITE_CROSS; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real`) THEN
  EXISTS_TAC `max (&1) a` THEN REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`g:A`; `v:B`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g:A`; `v:B`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`g:A`; `v:B`]) THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_NORM_ZERO] THEN
  MP_TAC(ISPEC `(f:A->B->complex) g v` NORM_POS_LE) THEN
  SPEC_TAC(`norm((f:A->B->complex) g v)`,`z:real`) THEN
  GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 < z /\ &0 < inv z` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `z:real` REAL_LT_INV_EQ) THEN
    UNDISCH_TAC `~(z = &0)` THEN UNDISCH_TAC `&0 <= z` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC);;

(* The coefficients of the linear form are integers bounded by cB m.         *)

let SCHINZEL_TIJDEMAN_GEN_COEFF_BOUND = prove
 (`!W1 W2 (e1:complex->num) (e2:complex->num) k1 k2 m t (u:complex).
     FINITE W1 /\ FINITE W2 /\ 1 <= m /\
     (!v. v IN W1 ==> e1 v < m) /\ (!v. v IN W2 ==> e2 v < m) /\
     integer t /\
     abs t <= &(k1 * k2) + &(k2 * CARD W1 + k1 * CARD W2 + 1) * &m
     ==> integer((if u IN W1 then &(k2 * e1 u) else &0) -
                 (if u IN W2 then &(k1 * e2 u) else &0) +
                 (if u = --Cx(&1) then t else &0)) /\
         abs((if u IN W1 then &(k2 * e1 u) else &0) -
             (if u IN W2 then &(k1 * e2 u) else &0) +
             (if u = --Cx(&1) then t else &0)) <=
         &(k1 + k2 + k1 * k2 + k2 * CARD W1 + k1 * CARD W2 + 2) * &m /\
         abs(&m) <=
         &(k1 + k2 + k1 * k2 + k2 * CARD W1 + k1 * CARD W2 + 2) * &m /\
         &2 <= &(k1 + k2 + k1 * k2 + k2 * CARD W1 + k1 * CARD W2 + 2) * &m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `abs(if u IN W1 then &(k2 * (e1:complex->num) u) else &0) <= &(k2 * m) /\
    abs(if u IN W2 then &(k1 * (e2:complex->num) u) else &0) <= &(k1 * m) /\
    abs(if u = --Cx(&1) then t else &0) <=
    &(k1 * k2) + &(k2 * CARD(W1:complex->bool) +
                   k1 * CARD(W2:complex->bool) + 1) * &m`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_LE; LE_0] THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS]) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &m` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&(k1 * k2) <= &(k1 * k2) * &m` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC INTEGER_ADD ORELSE MATCH_MP_TAC INTEGER_SUB ORELSE
           CONJ_TAC) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `&(k2 * m) + &(k1 * m) +
      &(k1 * k2) + &(k2 * CARD(W1:complex->bool) +
                     k1 * CARD(W2:complex->bool) + 1) * &m` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&(k1 * k2) <= &(k1 * k2) * &m` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
    UNDISCH_TAC `&1 <= &m` THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ABS_NUM; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(ARITH_RULE `1 * m <= n * m ==> m <= n * m`) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(ARITH_RULE `2 * 1 <= n * m ==> 2 <= n * m`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The linear form: k1 k2 Log((X - Z1)/(X - Z2)) is the linear form in the   *)
(* logarithms of the fixed numbers and of xi1^k2 / xi2^k1 plus t Log(-1),    *)
(* abs t <= c m; it is non-zero and O(1/abs X).                              *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_GEN_POW_SWAP = prove
 (`!(x:complex) m k. (x pow m) pow k = (x pow k) pow m`,
  REWRITE_TAC[COMPLEX_POW_POW] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM]);;

let SCHINZEL_TIJDEMAN_GEN_POW_IDENTITY = prove
 (`!(A1:complex) A2 P1 P2 x1 x2 k1 k2 m.
     ~(P2 = Cx(&0)) /\ ~(x2 = Cx(&0)) /\
     A1 pow k1 = P1 * x1 pow m /\ A2 pow k2 = P2 * x2 pow m
     ==> (A1 / A2) pow (k1 * k2) =
         P1 pow k2 / P2 pow k1 * (x1 pow k2 * inv x2 pow k1) pow m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_DIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_INV] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [SCHINZEL_TIJDEMAN_GEN_POW_SWAP] THEN
  SUBGOAL_THEN `~(P2 pow k1 = Cx(&0)) /\ ~((x2 pow k1) pow m = Cx(&0))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; DE_MORGAN_THM];
    CONV_TAC COMPLEX_FIELD]);;

let SCHINZEL_TIJDEMAN_GEN_CEXP_VSUM = prove
 (`!W (e:complex->num) k.
     FINITE W /\ (!v. v IN W ==> ~(v = Cx(&0)))
     ==> cexp(vsum W (\v. Cx(&(k * e v)) * clog v)) =
         cproduct W (\v. v pow e v) pow k`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CEXP_VSUM; GSYM CPRODUCT_POW] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CEXP_N; CEXP_CLOG; COMPLEX_POW_POW] THEN
  AP_TERM_TAC THEN REWRITE_TAC[MULT_SYM]);;

let SCHINZEL_TIJDEMAN_GEN_IM_VSUM = prove
 (`!W (c:complex->num) b.
     FINITE W /\ (!v. v IN W ==> ~(v = Cx(&0)) /\ c v <= b)
     ==> abs(Im(vsum W (\v. Cx(&(c v)) * clog v))) <= &(CARD W) * &b * pi`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[IM_VSUM; IM_MUL_CX] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (W:complex->bool) (\v. &b * pi)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_ABS_POS; REAL_OF_NUM_LE;
                 IM_CLOG_ABS_LE_PI];
    ASM_SIMP_TAC[SUM_CONST; REAL_LE_REFL]]);;

(* Exponentials of both sides and the principal logarithms: the linear form  *)
(* identity with an integer t, bounded by the imaginary parts.               *)

let SCHINZEL_TIJDEMAN_GEN_LINEAR_FORM = prove
 (`!W1 W2 (e1:complex->num) (e2:complex->num) k1 k2 m (X:complex) Z1 Z2
    xi1 xi2.
     FINITE W1 /\ FINITE W2 /\ 1 <= m /\
     (!v. v IN W1 ==> ~(v = Cx(&0)) /\ e1 v < m) /\
     (!w. w IN W2 ==> ~(w = Cx(&0)) /\ e2 w < m) /\
     ~(X = Z1) /\ ~(X = Z2) /\
     (X - Z1) pow k1 = cproduct W1 (\v. v pow e1 v) * xi1 pow m /\
     (X - Z2) pow k2 = cproduct W2 (\w. w pow e2 w) * xi2 pow m
     ==> ~(xi1 = Cx(&0)) /\ ~(xi2 = Cx(&0)) /\
         ?t. integer t /\
             abs t <= &(k1 * k2) + &(k2 * CARD W1 + k1 * CARD W2 + 1) * &m /\
             Cx(&(k1 * k2)) * clog((X - Z1) / (X - Z2)) =
             vsum W1 (\v. Cx(&(k2 * e1 v)) * clog v) -
             vsum W2 (\w. Cx(&(k1 * e2 w)) * clog w) +
             Cx(&m) * clog(xi1 pow k2 * inv xi2 pow k1) +
             Cx t * clog(--Cx(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(!v. v IN W1 ==> ~(v = Cx(&0))) /\
                (!w. w IN W2 ==> ~(w = Cx(&0)))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(xi1 = Cx(&0)) /\ ~(xi2 = Cx(&0))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC
       `(X - Z1) pow k1 = cproduct W1 (\v. v pow e1 v) * Cx(&0) pow m`;
      UNDISCH_TAC
       `(X - Z2) pow k2 = cproduct W2 (\w. w pow e2 w) * Cx(&0) pow m`] THEN
    ASM_REWRITE_TAC[COMPLEX_POW_ZERO; COMPLEX_MUL_RZERO; COMPLEX_POW_EQ_0;
                    COMPLEX_SUB_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((X - Z1) / (X - Z2) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_DIV_EQ_0; COMPLEX_SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~(xi1 pow k2 * inv xi2 pow k1 = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; COMPLEX_INV_EQ_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cproduct W2 (\w. w pow e2 w) = Cx(&0))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CPRODUCT_EQ_0; COMPLEX_POW_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `cexp(Cx(&(k1 * k2)) * clog((X - Z1) / (X - Z2))) =
    cexp(vsum W1 (\v. Cx(&(k2 * e1 v)) * clog v) -
         vsum W2 (\w. Cx(&(k1 * e2 w)) * clog w) +
         Cx(&m) * clog(xi1 pow k2 * inv xi2 pow k1))`
  MP_TAC THENL
   [REWRITE_TAC[CEXP_ADD; CEXP_SUB; CEXP_N] THEN
    ASM_SIMP_TAC[CEXP_CLOG; SCHINZEL_TIJDEMAN_GEN_CEXP_VSUM] THEN
    MATCH_MP_TAC SCHINZEL_TIJDEMAN_GEN_POW_IDENTITY THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CEXP_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 * n` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[CLOG_NEG_1; CX_MUL] THEN
    CONV_TAC COMPLEX_RING] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Im`) THEN
  REWRITE_TAC[IM_ADD; IM_SUB; IM_MUL_CX; IM_II; REAL_MUL_RID] THEN
  DISCH_THEN(LABEL_TAC "im") THEN
  SUBGOAL_THEN
   `abs(Im(vsum W1 (\v. Cx(&(k2 * e1 v)) * clog v))) <=
    &(CARD(W1:complex->bool)) * &(k2 * m) * pi /\
    abs(Im(vsum W2 (\w. Cx(&(k1 * e2 w)) * clog w))) <=
    &(CARD(W2:complex->bool)) * &(k1 * m) * pi`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN_GEN_IM_VSUM THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL; LT_IMP_LE];
    ALL_TAC] THEN
  MP_TAC(SPEC `((X:complex) - Z1) / (X - Z2)` IM_CLOG_ABS_LE_PI) THEN
  MP_TAC(SPEC `(xi1:complex) pow k2 * inv xi2 pow k1` IM_CLOG_ABS_LE_PI) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `abs(&(k1 * k2) * Im(clog((X - Z1) / (X - Z2)))) <= &(k1 * k2) * pi /\
    abs(&m * Im(clog(xi1 pow k2 * inv xi2 pow k1))) <= &m * pi`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(&2 * n * pi) <=
    &(k1 * k2) * pi + &(CARD(W1:complex->bool)) * &(k2 * m) * pi +
    &(CARD(W2:complex->bool)) * &(k1 * m) * pi + &m * pi`
  MP_TAC THENL
   [USE_THEN "im" MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`abs(&(k1 * k2) * Im(clog((X - Z1) / (X - Z2)))) <= &(k1 * k2) * pi`;
      `abs(&m * Im(clog(xi1 pow k2 * inv xi2 pow k1))) <= &m * pi`;
      `abs(Im(vsum W1 (\v. Cx(&(k2 * e1 v)) * clog v))) <=
       &(CARD(W1:complex->bool)) * &(k2 * m) * pi`;
      `abs(Im(vsum W2 (\w. Cx(&(k1 * e2 w)) * clog w))) <=
       &(CARD(W2:complex->bool)) * &(k1 * m) * pi`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(k1 * k2) * pi + &(CARD(W1:complex->bool)) * &(k2 * m) * pi +
    &(CARD(W2:complex->bool)) * &(k1 * m) * pi + &m * pi =
    (&(k1 * k2) + &(k2 * CARD(W1:complex->bool) +
                    k1 * CARD(W2:complex->bool) + 1) * &m) * pi /\
    abs(&2 * n * pi) = abs(&2 * n) * pi`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_PI; GSYM REAL_OF_NUM_MUL;
                GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[REAL_LE_RMUL_EQ; PI_POS]]);;

(* (X - Z1)/(X - Z2) = 1 + (Z2 - Z1)/(X - Z2): the logarithm is non-zero and *)
(* at most C1 / abs X for large abs X (CLOG_ONE_PLUS_SMALL).                 *)

let SCHINZEL_TIJDEMAN_GEN_LAMBDA_SMALL = prove
 (`!Z1 Z2 k.
     ~(Z1 = Z2) /\ 1 <= k
     ==> ?X0 C1. &1 <= X0 /\ &0 < C1 /\
                 !X. X0 <= abs X
                     ==> ~(Cx X = Z1) /\ ~(Cx X = Z2) /\
                         ~(Cx(&k) * clog((Cx X - Z1) / (Cx X - Z2)) =
                           Cx(&0)) /\
                         norm(Cx(&k) * clog((Cx X - Z1) / (Cx X - Z2))) <=
                         C1 / abs X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(Z2 - Z1:complex)` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`&2 * norm(Z1:complex) + &2 * norm(Z2:complex) +
     &4 * norm(Z2 - Z1:complex) + &1`;
    `&4 * &k * norm(Z2 - Z1:complex)`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `Z1:complex` NORM_POS_LE) THEN
    MP_TAC(ISPEC `Z2:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `X:real` THEN DISCH_TAC THEN
  MP_TAC(ISPEC `Z1:complex` NORM_POS_LE) THEN
  MP_TAC(ISPEC `Z2:complex` NORM_POS_LE) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `abs X / &2 <= norm(Cx X - Z2) /\ norm(Z1:complex) < abs X /\
                norm(Z2:complex) < abs X`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Cx X`; `Z2:complex`] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx X = Z1) /\ ~(Cx X = Z2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_NORM_CX]) THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `~(Cx X - Z2 = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cx X - Z1) / (Cx X - Z2) = Cx(&1) + (Z2 - Z1) / (Cx X - Z2)`
  SUBST1_TAC THENL
   [UNDISCH_TAC `~(Cx X - Z2 = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs X` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `norm((Z2 - Z1) / (Cx X - Z2)) <= (&2 * norm(Z2 - Z1:complex)) / abs X`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV] THEN MATCH_MP_TAC REAL_FRAC_LE_CROSS THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&2 * norm(Z2 - Z1:complex)) * norm(Cx X - Z2) =
      norm(Z2 - Z1:complex) * (&2 * norm(Cx X - Z2))`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((Z2 - Z1) / (Cx X - Z2)) <= &1 / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * norm(Z2 - Z1:complex)) / abs X` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Z2 - Z1) / (Cx X - Z2) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_DIV_EQ_0; COMPLEX_SUB_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[CLOG_ONE_PLUS_NZ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&k * &2 * norm((Z2 - Z1) / (Cx X - Z2))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POS; CLOG_ONE_PLUS_SMALL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&k * &2 * (&2 * norm(Z2 - Z1:complex)) / abs X` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Embeddings of subfields of C generated by s: closure of the carrier, the  *)
(* embedding as a ring homomorphism fixing the integers (the library clauses *)
(* RING_*_IN_SUBFIELD_GENERATED, RING_HOMOMORPHISM_*, FIELD_HOMOMORPHISM_INV *)
(* in the complex notation), the descent identities under an embedding and   *)
(* the resulting bounds for the conjugates of xi.                            *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_GEN_CARRIER = prove
 (`!s. (!x y. x IN ring_carrier(subfield_generated complex_ring s) /\
              y IN ring_carrier(subfield_generated complex_ring s)
              ==> x - y IN ring_carrier(subfield_generated complex_ring s) /\
                  x * y IN ring_carrier(subfield_generated complex_ring s)) /\
       (!x n. x IN ring_carrier(subfield_generated complex_ring s)
              ==> x pow n IN ring_carrier(subfield_generated complex_ring s) /\
                  inv x IN ring_carrier(subfield_generated complex_ring s)) /\
       (!x. integer x
            ==> Cx x IN ring_carrier(subfield_generated complex_ring s)) /\
       --Cx(&1) IN ring_carrier(subfield_generated complex_ring s)`,
  SIMP_TAC[GSYM CX_NEG; BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER;
           INTEGER_CLOSED] THEN
  REWRITE_TAC[GSYM complex_field_clauses; ring_sub] THEN
  SIMP_TAC[RING_ADD_IN_SUBFIELD_GENERATED; RING_NEG_IN_SUBFIELD_GENERATED;
           RING_MUL_IN_SUBFIELD_GENERATED; RING_POW_IN_SUBFIELD_GENERATED;
           RING_INV_IN_SUBFIELD_GENERATED; FIELD_SUBFIELD_GENERATED;
           FIELD_COMPLEX_RING]);;

(* A complex embedding of subfield_generated complex_ring s is a ring        *)
(* homomorphism on the carrier, fixes the integers, has no non-zero kernel   *)
(* element and commutes with inverses and finite products.                   *)

let SCHINZEL_TIJDEMAN_GEN_EMBED = prove
 (`!s g.
     g IN complex_embeddings(subfield_generated complex_ring s)
     ==> (!x y. x IN ring_carrier(subfield_generated complex_ring s) /\
                y IN ring_carrier(subfield_generated complex_ring s)
                ==> g(x - y) = g x - g y /\ g(x * y) = g x * g y) /\
         (!x n. x IN ring_carrier(subfield_generated complex_ring s)
                ==> g(x pow n) = g x pow n) /\
         (!x. integer x ==> g(Cx x) = Cx x) /\
         (!x. x IN ring_carrier(subfield_generated complex_ring s) /\
              ~(x = Cx(&0))
              ==> ~(g x = Cx(&0)) /\ g(inv x) = inv(g x)) /\
         (!W (f:A->complex).
              FINITE W /\
              (!v. v IN W
                   ==> f v IN ring_carrier(subfield_generated complex_ring s))
              ==> g(cproduct W f) = cproduct W (\v. g(f v)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `field(subfield_generated complex_ring s)` ASSUME_TAC THENL
   [SIMP_TAC[FIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP COMPLEX_EMBEDDINGS_MONOMORPHISM o
    CONJ (ASSUME `field(subfield_generated complex_ring s)`)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(MATCH_MP RING_MONOMORPHISM_IMP_HOMOMORPHISM th)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FIELD_HOMOMORPHISM_INV o
    CONJ (ASSUME `field(subfield_generated complex_ring s)`)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_POW) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_MUL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP RING_HOMOMORPHISM_SUB) THEN
  REWRITE_TAC[RING_SUB_SUBFIELD_GENERATED; RING_POW_SUBFIELD_GENERATED;
              CONJUNCT2 SUBFIELD_GENERATED; complex_field_clauses] THEN
  REPEAT DISCH_TAC THEN ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[BRIDGE_NF_HOM_INTEGER];
    X_GEN_TAC `x:complex` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`subfield_generated complex_ring s`; `complex_ring`;
                   `g:complex->complex`; `x:complex`]
      RING_MONOMORPHISM_EQ_0) THEN
    MP_TAC(ISPECL [`complex_ring`; `s:complex->bool`; `x:complex`]
      RING_INV_SUBFIELD_GENERATED) THEN
    ASM_SIMP_TAC[CONJUNCT2 SUBFIELD_GENERATED; complex_field_clauses] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:complex->bool`; `W:A->bool`; `f:A->complex`]
      COMPLEX_SUBFIELD_RING_PRODUCT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(MP_TAC o ISPECL [`f:A->complex`; `W:A->bool`] o
      MATCH_MP RING_HOMOMORPHISM_PRODUCT) THEN
    ASM_SIMP_TAC[COMPLEX_RING_PRODUCT; o_DEF]]);;

let SCHINZEL_TIJDEMAN_GEN_CARRIER_CPRODUCT = prove
 (`!s W (f:A->complex).
     FINITE W /\
     (!v. v IN W ==> f v IN ring_carrier(subfield_generated complex_ring s))
     ==> cproduct W f IN ring_carrier(subfield_generated complex_ring s)`,
  SIMP_TAC[GSYM COMPLEX_SUBFIELD_RING_PRODUCT; RING_PRODUCT]);;

let SCHINZEL_TIJDEMAN_GEN_EMBED_IDENTITY = prove
 (`!s g W (e:complex->num) xi Z k m X.
     g IN complex_embeddings(subfield_generated complex_ring s) /\
     FINITE W /\
     (!v. v IN W ==> v IN ring_carrier(subfield_generated complex_ring s)) /\
     xi IN ring_carrier(subfield_generated complex_ring s) /\
     Z IN ring_carrier(subfield_generated complex_ring s) /\ integer X /\
     (Cx X - Z) pow k = cproduct W (\v. v pow e v) * xi pow m
     ==> (Cx X - g Z) pow k = cproduct W (\v. g v pow e v) * g xi pow m`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 6 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `g:complex->complex`) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHINZEL_TIJDEMAN_GEN_EMBED) THEN
  MP_TAC(SPEC `s:complex->bool` SCHINZEL_TIJDEMAN_GEN_CARRIER) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `W:complex->bool`;
                 `\v:complex. v pow (e:complex->num) v`]
    SCHINZEL_TIJDEMAN_GEN_CARRIER_CPRODUCT) THEN
  MP_TAC(ISPECL [`W:complex->bool`; `\v:complex. v pow (e:complex->num) v`]
    (last(CONJUNCTS(MATCH_MP SCHINZEL_TIJDEMAN_GEN_EMBED (ASSUME
      `g IN complex_embeddings(subfield_generated complex_ring s)`))))) THEN
  ASM_SIMP_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `cproduct W (\v. (g:complex->complex) v pow (e:complex->num) v) =
    cproduct W (\v. g(v pow e v))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN ASM_SIMP_TAC[]; ASM_SIMP_TAC[]]);;

(* From (X - w)^k = prod h(v)^(e v) xi^m with inv R1 <= norm(h v) <= R1,     *)
(* e v < m and norm w <= R0: an upper bound for norm xi, and a lower bound   *)
(* when abs X >= 1 + R0.                                                     *)

let SCHINZEL_TIJDEMAN_GEN_POWER_BOUNDS = prove
 (`!W (h:complex->complex) (e:complex->num) w xi k m X R0 R1.
     FINITE W /\ 1 <= m /\ &1 <= R1 /\ &0 <= R0 /\ &1 <= abs X /\
     (!v. v IN W ==> inv R1 <= norm(h v) /\ norm(h v) <= R1 /\ e v < m) /\
     norm w <= R0 /\
     (Cx X - w) pow k = cproduct W (\v. h v pow e v) * xi pow m
     ==> norm xi <= exp(&k * log(abs X + R0) / &m) * R1 pow CARD W /\
         (&1 + R0 <= abs X ==> inv(R1 pow CARD W) <= norm xi)`,
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 7 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; NORM_CPRODUCT] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(m = 0) /\ &0 < R1 /\ &0 < R1 pow CARD(W:complex->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `inv(R1 pow CARD(W:complex->bool)) pow m <=
    product W (\v. norm((h:complex->complex) v) pow e v) /\
    product W (\v. norm((h:complex->complex) v) pow e v) <=
    (R1 pow CARD(W:complex->bool)) pow m`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `product (W:complex->bool) (\v. inv R1 pow m)` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_POW; REAL_POW_INV] THEN
        REWRITE_TAC[MULT_SYM; REAL_LE_REFL];
        ALL_TAC] THEN
      MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `inv R1 pow ((e:complex->num) v)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1; LT_IMP_LE] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `product (W:complex->bool) (\v. R1 pow m)` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_POW] THEN
        REWRITE_TAC[MULT_SYM; REAL_LE_REFL]] THEN
      MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `v:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `v:complex`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `R1 pow ((e:complex->num) v)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_SIMP_TAC[LT_IMP_LE]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `norm(xi:complex) * inv(R1 pow CARD(W:complex->bool)) <=
      exp(&k * log(abs X + R0) / &m)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
      SUBGOAL_THEN
       `exp(&k * log(abs X + R0) / &m) pow m = (abs X + R0) pow k`
      SUBST1_TAC THENL
       [REWRITE_TAC[GSYM REAL_EXP_N] THEN
        SUBGOAL_THEN `&m * &k * log(abs X + R0) / &m = &k * log(abs X + R0)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `~(m = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
          CONV_TAC REAL_FIELD;
          ALL_TAC] THEN
        REWRITE_TAC[REAL_EXP_N] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm(Cx X - w) pow k` THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[REAL_POW_MUL] THEN
        GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
        MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
        MP_TAC(NORM_ARITH `norm(Cx X - w) <= norm(Cx X) + norm(w:complex)`) THEN
        REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ]];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC REAL_INV_LE_FROM_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `m:num` THEN
  ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LT_IMP_LE; REAL_POW_ONE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(Cx X - w) pow k` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN
    MP_TAC(ISPECL [`Cx X`; `w:complex`] NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[REAL_POW_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE]]);;

let SCHINZEL_TIJDEMAN_GEN_EMBED_BOUNDS = prove
 (`!s g W (e:complex->num) xi Z k m X R0 R1.
     g IN complex_embeddings(subfield_generated complex_ring s) /\
     FINITE W /\
     (!v. v IN W
          ==> v IN ring_carrier(subfield_generated complex_ring s) /\
              inv R1 <= norm(g v) /\ norm(g v) <= R1 /\ e v < m) /\
     xi IN ring_carrier(subfield_generated complex_ring s) /\
     Z IN ring_carrier(subfield_generated complex_ring s) /\
     norm(g Z) <= R0 /\ integer X /\ &1 <= abs X /\ &0 <= R0 /\
     &1 <= R1 /\ 1 <= m /\
     (Cx X - Z) pow k = cproduct W (\v. v pow e v) * xi pow m
     ==> norm(g xi) <= exp(&k * log(abs X + R0) / &m) * R1 pow CARD W /\
         (&1 + R0 <= abs X ==> inv(R1 pow CARD W) <= norm(g xi))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SCHINZEL_TIJDEMAN_GEN_POWER_BOUNDS THEN
  MAP_EVERY EXISTS_TAC [`g:complex->complex`; `e:complex->num`;
                        `(g:complex->complex) Z`] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC SCHINZEL_TIJDEMAN_GEN_EMBED_IDENTITY THEN
  EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The variable number xi1^k2 / xi2^k1: its denominator and its conjugates,  *)
(* and the lower bound of SHARP_BAKER_NUMBER_FIELD for the linear form.      *)
(* ------------------------------------------------------------------------- *)

(* The variable number xi1^k2 / xi2^k1 lies in the field, is non-zero, has a *)
(* denominator den <= DB and conjugates bounded by HB: the denominator of    *)
(* 1 / xi2 by COMPLEX_SUBFIELD_ELEMENT_POLY and SHARP_NFBOUND_INV_ROOT, the  *)
(* product by SHARP_NFBOUND_POW and SHARP_NFBOUND_MUL.                       *)

let SCHINZEL_TIJDEMAN_GEN_VARIABLE = prove
 (`!s W1 W2 (e1:complex->num) (e2:complex->num) xi1 xi2 Z1 Z2 k1 k2 m X
    R0 R1 D1 D2.
     FINITE s /\ (!z. z IN s ==> algebraic_number z) /\
     FINITE W1 /\ FINITE W2 /\
     (!v. v IN W1 UNION W2
          ==> v IN ring_carrier(subfield_generated complex_ring s)) /\
     (!g v. g IN complex_embeddings(subfield_generated complex_ring s) /\
            v IN W1 UNION W2
            ==> inv R1 <= norm(g v) /\ norm(g v) <= R1) /\
     (!g. g IN complex_embeddings(subfield_generated complex_ring s)
          ==> norm(g Z1) <= R0 /\ norm(g Z2) <= R0) /\
     Z1 IN ring_carrier(subfield_generated complex_ring s) /\
     Z2 IN ring_carrier(subfield_generated complex_ring s) /\
     &1 <= R1 /\ &0 <= R0 /\ integer D1 /\ &1 <= D1 /\
     integer D2 /\ &1 <= D2 /\
     integer X /\ &1 + R0 <= abs X /\ 1 <= m /\
     (!v. v IN W1 ==> e1 v < m) /\ (!v. v IN W2 ==> e2 v < m) /\
     xi1 IN ring_carrier(subfield_generated complex_ring s) /\
     xi2 IN ring_carrier(subfield_generated complex_ring s) /\
     ~(xi1 = Cx(&0)) /\ ~(xi2 = Cx(&0)) /\
     algebraic_integer(Cx D1 * xi1) /\ algebraic_integer(Cx D2 * xi2) /\
     (Cx X - Z1) pow k1 = cproduct W1 (\v. v pow e1 v) * xi1 pow m /\
     (Cx X - Z2) pow k2 = cproduct W2 (\v. v pow e2 v) * xi2 pow m
     ==> xi1 pow k2 * inv xi2 pow k1 IN
         ring_carrier(subfield_generated complex_ring s) /\
         ~(xi1 pow k2 * inv xi2 pow k1 = Cx(&0)) /\
         (?den. integer den /\ &1 <= den /\
                den <= D1 pow k2 *
                       ((&2 * D2 * exp(&k2 * log(abs X + R0) / &m) *
                         R1 pow CARD W2) pow
                        extension_degree
                         (subfield_generated complex_ring {Cx(&0)},
                          subfield_generated complex_ring s) I) pow k1 /\
                algebraic_integer(Cx den * (xi1 pow k2 * inv xi2 pow k1))) /\
         (!g. g IN complex_embeddings(subfield_generated complex_ring s)
              ==> norm(g(xi1 pow k2 * inv xi2 pow k1)) <=
                  (exp(&k1 * log(abs X + R0) / &m) * R1 pow CARD W1) pow k2 *
                  (R1 pow CARD W2) pow k1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `s:complex->bool` SCHINZEL_TIJDEMAN_GEN_CARRIER) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= abs X` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!g. g IN complex_embeddings(subfield_generated complex_ring s)
        ==> norm((g:complex->complex) xi1) <=
            exp(&k1 * log(abs X + R0) / &m) *
            R1 pow CARD(W1:complex->bool) /\
            norm(g xi2) <=
            exp(&k2 * log(abs X + R0) / &m) *
            R1 pow CARD(W2:complex->bool) /\
            norm(g(inv xi2)) <= R1 pow CARD(W2:complex->bool)`
  (LABEL_TAC "bd") THENL
   [X_GEN_TAC `g:complex->complex` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:complex->bool`; `g:complex->complex`;
                   `W1:complex->bool`; `e1:complex->num`; `xi1:complex`;
                   `Z1:complex`; `k1:num`; `m:num`; `X:real`; `R0:real`;
                   `R1:real`] SCHINZEL_TIJDEMAN_GEN_EMBED_BOUNDS) THEN
    MP_TAC(ISPECL [`s:complex->bool`; `g:complex->complex`;
                   `W2:complex->bool`; `e2:complex->num`; `xi2:complex`;
                   `Z2:complex`; `k2:num`; `m:num`; `X:real`; `R0:real`;
                   `R1:real`] SCHINZEL_TIJDEMAN_GEN_EMBED_BOUNDS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCHINZEL_TIJDEMAN_GEN_EMBED) THEN
    ASM_SIMP_TAC[IN_UNION; COMPLEX_NORM_INV] THEN REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 <= exp(&k2 * log(abs X + R0) / &m) * R1 pow CARD(W2:complex->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_SIMP_TAC[REAL_POW_LE_1] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`s:complex->bool`; `xi2:complex`; `D2:real`;
                `exp(&k2 * log(abs X + R0) / &m) *
                 R1 pow CARD(W2:complex->bool)`]
    COMPLEX_SUBFIELD_ELEMENT_POLY) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`dx:num`; `ax:num->real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:complex->bool`; `xi2:complex`; `ax:num->real`; `dx:num`;
                `(&2 * D2 * exp(&k2 * log(abs X + R0) / &m) *
                  R1 pow CARD(W2:complex->bool)) pow dx`]
    SHARP_NFBOUND_INV_ROOT) THEN
  ASM_REWRITE_TAC[sharp_nfbound] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `sharp_nfbound s xi1 D1
      (exp(&k1 * log(abs X + R0) / &m) * R1 pow CARD(W1:complex->bool)) /\
    sharp_nfbound s (inv xi2) d (R1 pow CARD(W2:complex->bool))`
  MP_TAC THENL [ASM_SIMP_TAC[sharp_nfbound]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(MATCH_MP SHARP_NFBOUND_MUL (CONJ
    (SPEC `k2:num` (MATCH_MP SHARP_NFBOUND_POW (CONJUNCT1 th)))
    (SPEC `k1:num` (MATCH_MP SHARP_NFBOUND_POW (CONJUNCT2 th)))))) THEN
  REWRITE_TAC[sharp_nfbound] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; COMPLEX_INV_EQ_0];
    ALL_TAC] THEN
  EXISTS_TAC `D1 pow k2 * d pow k1` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&2 * D2 * exp(&k2 * log(abs X + R0) / &m) *
     R1 pow CARD(W2:complex->bool)) pow dx` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_1_MUL THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_1_MUL] THEN
  ASM_REWRITE_TAC[]);;

(* One solution: SHARP_BAKER_NUMBER_FIELD for the enumerated fixed numbers   *)
(* en j with coefficients cf(en j), the variable number with coefficient m,  *)
(* A = e DB HB and B = cB m.                                                 *)

let SCHINZEL_TIJDEMAN_GEN_BAKER_STEP = prove
 (`!s W1 W2 (en:num->complex) C (e1:complex->num) (e2:complex->num) xi1 xi2
    Z1 Z2 k1 k2 m X R0 R1 D1 D2.
     FINITE s /\ (!z. z IN s ==> algebraic_number z) /\
     FINITE W1 /\ FINITE W2 /\
     (!v. v IN W1 UNION W2
          ==> v IN ring_carrier(subfield_generated complex_ring s) /\
              ~(v = Cx(&0))) /\
     (!g v. g IN complex_embeddings(subfield_generated complex_ring s) /\
            v IN W1 UNION W2
            ==> inv R1 <= norm(g v) /\ norm(g v) <= R1) /\
     (!g. g IN complex_embeddings(subfield_generated complex_ring s)
          ==> norm(g Z1) <= R0 /\ norm(g Z2) <= R0) /\
     Z1 IN ring_carrier(subfield_generated complex_ring s) /\
     Z2 IN ring_carrier(subfield_generated complex_ring s) /\
     &1 <= R1 /\ &0 <= R0 /\ integer D1 /\ &1 <= D1 /\
     integer D2 /\ &1 <= D2 /\
     (!f:complex->complex.
          vsum (W1 UNION W2 UNION {--Cx(&1)}) f =
          vsum(1..CARD(W1 UNION W2 UNION {--Cx(&1)})) (\j. f(en j))) /\
     (!x den (bb:num->real) b A B.
        x IN ring_carrier(subfield_generated complex_ring s) /\
        ~(x = Cx(&0)) /\ integer den /\ &1 <= den /\ den <= A /\
        algebraic_integer(Cx den * x) /\
        (!g. g IN complex_embeddings(subfield_generated complex_ring s)
             ==> norm(g x) <= A) /\
        exp(&1) <= A /\ &2 <= B /\
        (!j. j IN 1..CARD(W1 UNION W2 UNION {--Cx(&1)})
             ==> integer(bb j) /\ abs(bb j) <= B) /\
        integer b /\ abs b <= B /\
        ~(vsum(1..CARD(W1 UNION W2 UNION {--Cx(&1)}))
              (\j. Cx(bb j) * clog(en j)) + Cx b * clog x = Cx(&0))
        ==> exp(--(C * log A * log B)) <=
            norm(vsum(1..CARD(W1 UNION W2 UNION {--Cx(&1)}))
                     (\j. Cx(bb j) * clog(en j)) + Cx b * clog x)) /\
     integer X /\ &1 + R0 <= abs X /\ 1 <= m /\
     ~(Cx X = Z1) /\ ~(Cx X = Z2) /\
     (!v. v IN W1 ==> e1 v < m) /\ (!v. v IN W2 ==> e2 v < m) /\
     xi1 IN ring_carrier(subfield_generated complex_ring s) /\
     xi2 IN ring_carrier(subfield_generated complex_ring s) /\
     algebraic_integer(Cx D1 * xi1) /\ algebraic_integer(Cx D2 * xi2) /\
     (Cx X - Z1) pow k1 = cproduct W1 (\v. v pow e1 v) * xi1 pow m /\
     (Cx X - Z2) pow k2 = cproduct W2 (\v. v pow e2 v) * xi2 pow m /\
     ~(Cx(&(k1 * k2)) * clog((Cx X - Z1) / (Cx X - Z2)) = Cx(&0))
     ==> exp(--(C * log(exp(&1) *
                        (D1 pow k2 *
                         ((&2 * D2 * exp(&k2 * log(abs X + R0) / &m) *
                           R1 pow CARD W2) pow
                          extension_degree
                           (subfield_generated complex_ring {Cx(&0)},
                            subfield_generated complex_ring s) I) pow k1) *
                        ((exp(&k1 * log(abs X + R0) / &m) *
                          R1 pow CARD W1) pow k2 *
                         (R1 pow CARD W2) pow k1)) *
                 log(&(k1 + k2 + k1 * k2 + k2 * CARD W1 + k1 * CARD W2 + 2) *
                     &m))) <=
         norm(Cx(&(k1 * k2)) * clog((Cx X - Z1) / (Cx X - Z2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`W1:complex->bool`; `W2:complex->bool`; `e1:complex->num`;
                 `e2:complex->num`; `k1:num`; `k2:num`; `m:num`; `Cx X`;
                 `Z1:complex`; `Z2:complex`; `xi1:complex`; `xi2:complex`]
    SCHINZEL_TIJDEMAN_GEN_LINEAR_FORM) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_UNION]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lf")))))) THEN
  MP_TAC(ISPECL [`s:complex->bool`; `W1:complex->bool`; `W2:complex->bool`;
                 `e1:complex->num`; `e2:complex->num`; `xi1:complex`;
                 `xi2:complex`; `Z1:complex`; `Z2:complex`; `k1:num`;
                 `k2:num`; `m:num`; `X:real`; `R0:real`; `R1:real`;
                 `D1:real`; `D2:real`] SCHINZEL_TIJDEMAN_GEN_VARIABLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `den:real` STRIP_ASSUME_TAC)
      (LABEL_TAC "house")))) THEN
  ABBREV_TAC
   `DM = extension_degree (subfield_generated complex_ring {Cx(&0)},
                           subfield_generated complex_ring s) I` THEN
  ABBREV_TAC `TX = log(abs X + R0) / &m` THEN
  SUBGOAL_THEN `&0 <= TX` ASSUME_TAC THENL
   [EXPAND_TAC "TX" THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`D1:real`; `D2:real`; `R1:real`; `k1:num`; `k2:num`;
                `CARD(W1:complex->bool)`; `CARD(W2:complex->bool)`;
                `DM:num`; `TX:real`] SCHINZEL_TIJDEMAN_GEN_LOG_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`W1:complex->bool`; `W2:complex->bool`; `e1:complex->num`;
                 `e2:complex->num`; `k1:num`; `k2:num`; `m:num`; `t:real`]
    SCHINZEL_TIJDEMAN_GEN_COEFF_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "cf") THEN
  ABBREV_TAC
   `cf = \u:complex. (if u IN W1 then &(k2 * e1 u) else &0) -
                     (if u IN W2 then &(k1 * e2 u) else &0) +
                     (if u = --Cx(&1) then t else &0)` THEN
  SUBGOAL_THEN
   `vsum(1..CARD(W1 UNION W2 UNION {--Cx(&1)}))
        (\j. Cx((cf:complex->real)(en j)) * clog(en j)) +
    Cx(&m) * clog(xi1 pow k2 * inv xi2 pow k1) =
    Cx(&(k1 * k2)) * clog((Cx X - Z1) / (Cx X - Z2))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `\u. Cx((cf:complex->real) u) * clog u` o
      check (fun th -> try is_eq(snd(dest_forall(concl th)))
                       with Failure _ -> false)) THEN
    REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXPAND_TAC "cf" THEN
    ASM_SIMP_TAC[SCHINZEL_TIJDEMAN_GEN_VSUM_SPLIT] THEN
    USE_THEN "lf" SUBST1_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(xi1:complex) pow k2 * inv(xi2:complex) pow k1`; `den:real`;
    `\j. (cf:complex->real)((en:num->complex) j)`; `&m`;
    `exp(&1) *
     (D1 pow k2 *
      ((&2 * D2 * exp(&k2 * TX) * R1 pow CARD(W2:complex->bool)) pow DM)
      pow k1) *
     ((exp(&k1 * TX) * R1 pow CARD(W1:complex->bool)) pow k2 *
      (R1 pow CARD(W2:complex->bool)) pow k1)`;
    `&(k1 + k2 + k1 * k2 + k2 * CARD(W1:complex->bool) +
       k1 * CARD(W2:complex->bool) + 2) * &m`] o
    check (fun th -> length(fst(strip_forall(concl th))) = 6)) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  SUBGOAL_THEN
   `&1 <= (exp(&k1 * TX) * R1 pow CARD(W1:complex->bool)) pow k2 *
          (R1 pow CARD(W2:complex->bool)) pow k1 /\
    &1 <= D1 pow k2 *
          ((&2 * D2 * exp(&k2 * TX) * R1 pow CARD(W2:complex->bool)) pow DM)
          pow k1 /\
    &1 <= exp(&1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x. &0 <= x ==> &1 <= exp x` ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
      ASM_REWRITE_TAC[REAL_EXP_MONO_LE];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    REPEAT(MATCH_MP_TAC REAL_POW_LE_1) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
    TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`exp(&1)`;
    `D1 pow k2 *
     ((&2 * D2 * exp(&k2 * TX) * R1 pow CARD(W2:complex->bool)) pow DM)
     pow k1`;
    `(exp(&k1 * TX) * R1 pow CARD(W1:complex->bool)) pow k2 *
     (R1 pow CARD(W2:complex->bool)) pow k1`]
    SCHINZEL_TIJDEMAN_GEN_LE_PROD3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LE_TRANS];
    X_GEN_TAC `g:complex->complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `(exp(&k1 * TX) * R1 pow CARD(W1:complex->bool)) pow k2 *
      (R1 pow CARD(W2:complex->bool)) pow k1` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "house" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "cf" THEN
    USE_THEN "cf" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[INTEGER_CLOSED];
    USE_THEN "lf" (SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The monic case c y^m = F(X): the fixed data (minimal polynomials, S-unit  *)
(* descents, bounds for the embeddings), then the bound for m.               *)
(* ------------------------------------------------------------------------- *)

(* The data fixed before the solutions: the S-unit descents at Z1 and Z2     *)
(* (SCHINZEL_TIJDEMAN_MULT_ROOT_DATA, SCHINZEL_TIJDEMAN_ROOT_DESCENT) in the *)
(* field Q(Z1, Z2), and the bounds R1 for the embeddings of W1 UNION W2 and  *)
(* R0 for the roots of F.                                                    *)

let SCHINZEL_TIJDEMAN_GEN_FIXED_DATA = prove
 (`!N (a:num->real) c Z1 Z2.
     (!i. integer(a i)) /\ a N = &1 /\ integer c /\ ~(c = &0) /\
     vsum(0..N) (\i. Cx(a i) * Z1 pow i) = Cx(&0) /\
     vsum(0..N) (\i. Cx(a i) * Z2 pow i) = Cx(&0)
     ==> ?W1 W2 D1 D2 k1 k2 R0 R1.
           (!z. z IN {Z1, Z2} ==> algebraic_number z) /\
           Z1 IN ring_carrier(subfield_generated complex_ring {Z1, Z2}) /\
           Z2 IN ring_carrier(subfield_generated complex_ring {Z1, Z2}) /\
           1 <= k1 /\ 1 <= k2 /\ FINITE W1 /\ FINITE W2 /\
           (!v. v IN W1 UNION W2
                ==> v IN ring_carrier(subfield_generated complex_ring
                                        {Z1, Z2}) /\
                    ~(v = Cx(&0))) /\
           (!g v. g IN complex_embeddings
                         (subfield_generated complex_ring {Z1, Z2}) /\
                  v IN W1 UNION W2
                  ==> inv R1 <= norm(g v) /\ norm(g v) <= R1) /\
           (!g. g IN complex_embeddings
                       (subfield_generated complex_ring {Z1, Z2})
                ==> norm(g Z1) <= R0 /\ norm(g Z2) <= R0) /\
           &1 <= R1 /\ &0 <= R0 /\ integer D1 /\ &1 <= D1 /\
           integer D2 /\ &1 <= D2 /\
           !m X y. 1 <= m /\ integer X /\ integer y /\ ~(y = &0) /\
                   c * y pow m = sum(0..N) (\i. a i * X pow i)
                   ==> ?(e1:complex->num) (e2:complex->num) xi1 xi2.
                         (!v. v IN W1 ==> e1 v < m) /\
                         (!v. v IN W2 ==> e2 v < m) /\
                         xi1 IN ring_carrier(subfield_generated complex_ring
                                               {Z1, Z2}) /\
                         xi2 IN ring_carrier(subfield_generated complex_ring
                                               {Z1, Z2}) /\
                         algebraic_integer(Cx D1 * xi1) /\
                         algebraic_integer(Cx D2 * xi2) /\
                         (Cx X - Z1) pow k1 =
                         cproduct W1 (\v. v pow e1 v) * xi1 pow m /\
                         (Cx X - Z2) pow k2 =
                         cproduct W2 (\v. v pow e2 v) * xi2 pow m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `Z1:complex`]
    SCHINZEL_TIJDEMAN_MULT_ROOT_DATA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `g1:num->real`
    (X_CHOOSE_THEN `r1:num->complex` (X_CHOOSE_THEN `k1:num`
     (X_CHOOSE_THEN `M1:num` (X_CHOOSE_THEN `h1:num->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "fac1") ASSUME_TAC))))))))))) THEN
  MP_TAC(SPECL [`n1:num`; `g1:num->real`; `r1:num->complex`; `k1:num`;
                `M1:num`; `h1:num->real`; `c:real`]
    SCHINZEL_TIJDEMAN_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W1:complex->bool` (X_CHOOSE_THEN `D1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "d1"))))))) THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `Z2:complex`]
    SCHINZEL_TIJDEMAN_MULT_ROOT_DATA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `g2:num->real`
    (X_CHOOSE_THEN `r2:num->complex` (X_CHOOSE_THEN `k2:num`
     (X_CHOOSE_THEN `M2:num` (X_CHOOSE_THEN `h2:num->real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "fac2") ASSUME_TAC))))))))))) THEN
  MP_TAC(SPECL [`n2:num`; `g2:num->real`; `r2:num->complex`; `k2:num`;
                `M2:num`; `h2:num->real`; `c:real`]
    SCHINZEL_TIJDEMAN_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W2:complex->bool` (X_CHOOSE_THEN `D2:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "d2"))))))) THEN
  SUBGOAL_THEN
   `ring_carrier(subfield_generated complex_ring {Z1}) SUBSET
    ring_carrier(subfield_generated complex_ring {Z1, Z2}) /\
    ring_carrier(subfield_generated complex_ring {Z2}) SUBSET
    ring_carrier(subfield_generated complex_ring {Z1, Z2})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. z IN {Z1, Z2} ==> algebraic_number z` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER THEN
    REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `a:num->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(complex_embeddings(subfield_generated complex_ring {Z1, Z2}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_COMPLEX_EMBEDDINGS THEN
    MATCH_MP_TAC NUMBER_FIELD_COMPLEX_SUBFIELD_GENERATED THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Z1 IN ring_carrier(subfield_generated complex_ring {Z1, Z2}) /\
    Z2 IN ring_carrier(subfield_generated complex_ring {Z1, Z2})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
    REWRITE_TAC[in_complex_ring; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. v IN W1 UNION W2
        ==> v IN ring_carrier(subfield_generated complex_ring {Z1, Z2}) /\
            ~(v = Cx(&0))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\(g:complex->complex) (v:complex). g v`;
    `complex_embeddings(subfield_generated complex_ring {Z1, Z2})`;
    `W1 UNION W2:complex->bool`] SCHINZEL_TIJDEMAN_GEN_NORM_BOUNDS) THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:complex->complex`; `v:complex`] THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP SCHINZEL_TIJDEMAN_GEN_EMBED) THEN
    DISCH_THEN(MP_TAC o SPEC `v:complex` o CONJUNCT1 o CONJUNCT2 o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `R1:real` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL
   [`norm:complex->real`;
    `{z | vsum(0..N) (\i. Cx((a:num->real) i) * z pow i) = Cx(&0)}`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`N:num`; `\i. Cx((a:num->real) i)`]
      COMPLEX_POLYFUN_FINITE_ROOTS) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL; CX_INJ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `B0:real`)] THEN
  MAP_EVERY EXISTS_TAC
   [`W1:complex->bool`; `W2:complex->bool`; `D1:real`; `D2:real`;
    `k1:num`; `k2:num`; `max (&0) B0`; `R1:real`] THEN
  ASM_REWRITE_TAC[REAL_LE_MAX; REAL_LE_REFL] THEN CONJ_TAC THENL
   [X_GEN_TAC `g:complex->complex` THEN DISCH_TAC THEN
    CONJ_TAC THEN DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC COMPLEX_EMBEDDING_POLY_ROOT THEN
    EXISTS_TAC `{Z1, Z2}:complex->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `X:real`; `y:real`] THEN STRIP_TAC THEN
  USE_THEN "d1" (MP_TAC o SPECL [`m:num`; `X:real`; `y:real`]) THEN
  USE_THEN "d2" (MP_TAC o SPECL [`m:num`; `X:real`; `y:real`]) THEN
  USE_THEN "fac1" (fun th -> REWRITE_TAC[GSYM th]) THEN
  USE_THEN "fac2" (fun th -> REWRITE_TAC[GSYM th]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:complex->num` (X_CHOOSE_THEN `xi2:complex`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:complex->num` (X_CHOOSE_THEN `xi1:complex`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`e1:complex->num`; `e2:complex->num`; `xi1:complex`; `xi2:complex`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The monic case: small abs X by SCHINZEL_TIJDEMAN_FINITE_X, large abs X by *)
(* the descent, SCHINZEL_TIJDEMAN_GEN_BAKER_STEP and                         *)
(* SCHINZEL_TIJDEMAN_GEN_CHAIN.                                              *)

let SCHINZEL_TIJDEMAN_GENERAL_MONIC = prove
 (`!N (a:num->real) c Z1 Z2.
     (!i. integer(a i)) /\ a N = &1 /\ integer c /\ ~(c = &0) /\
     ~(Z1 = Z2) /\
     vsum(0..N) (\i. Cx(a i) * Z1 pow i) = Cx(&0) /\
     vsum(0..N) (\i. Cx(a i) * Z2 pow i) = Cx(&0)
     ==> ?M. !X y m. integer X /\ integer y /\ &2 <= abs y /\
                     c * y pow m = sum(0..N) (\i. a i * X pow i)
                     ==> m <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHINZEL_TIJDEMAN_MULT_DEGREE_POS THEN
    MAP_EVERY EXISTS_TAC [`a:num->real`; `Z1:complex`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `c:real`; `Z1:complex`; `Z2:complex`]
    SCHINZEL_TIJDEMAN_GEN_FIXED_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W1:complex->bool` (X_CHOOSE_THEN
    `W2:complex->bool` (X_CHOOSE_THEN `D1:real` (X_CHOOSE_THEN `D2:real`
    (X_CHOOSE_THEN `k1:num` (X_CHOOSE_THEN `k2:num` (X_CHOOSE_THEN `R0:real`
    (X_CHOOSE_THEN `R1:real` MP_TAC)))))))) THEN
  REPLICATE_TAC 16 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(LABEL_TAC "desc") THEN
  MP_TAC(ISPEC `W1 UNION W2 UNION {--Cx(&1)}`
    SCHINZEL_TIJDEMAN_GEN_ENUMERATE) THEN
  ASM_REWRITE_TAC[FINITE_UNION; FINITE_SING] THEN
  DISCH_THEN(X_CHOOSE_THEN `en:num->complex`
    (CONJUNCTS_THEN2 (LABEL_TAC "enin") ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`{Z1, Z2}:complex->bool`;
                 `CARD(W1 UNION W2 UNION {--Cx(&1)})`; `en:num->complex`]
    SHARP_BAKER_NUMBER_FIELD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    USE_THEN "enin" (MP_TAC o SPEC `j:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION; IN_SING] THEN STRIP_TAC THENL
     [ASM_SIMP_TAC[IN_UNION];
      ASM_SIMP_TAC[IN_UNION];
      ASM_REWRITE_TAC[SCHINZEL_TIJDEMAN_GEN_CARRIER] THEN
      REWRITE_TAC[COMPLEX_NEG_EQ_0; CX_INJ] THEN REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `C:real` (LABEL_TAC "baker"))] THEN
  MP_TAC(SPECL [`Z1:complex`; `Z2:complex`; `k1 * k2:num`]
    SCHINZEL_TIJDEMAN_GEN_LAMBDA_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `1 * 1 <= k1 * k2 ==> 1 <= k1 * k2`) THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `X0:real` (X_CHOOSE_THEN `C1:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "small"))))) THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`] SCHINZEL_TIJDEMAN_MULT_F_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `X3:real` (X_CHOOSE_THEN `C4:real`
    (LABEL_TAC "fb"))) THEN
  ABBREV_TAC
   `DM = extension_degree (subfield_generated complex_ring {Cx(&0)},
                           subfield_generated complex_ring {Z1, Z2}) I` THEN
  MP_TAC(SPECL
   [`C:real`; `C1:real`; `&(k1 * k2) * (&DM + &1)`;
    `&1 + &k2 * log D1 +
     &k1 * &DM * (log(&2) + log D2 + &(CARD(W2:complex->bool)) * log R1) +
     (&k2 * &(CARD(W1:complex->bool)) + &k1 * &(CARD(W2:complex->bool))) *
     log R1`;
    `&(k1 + k2 + k1 * k2 + k2 * CARD(W1:complex->bool) +
       k1 * CARD(W2:complex->bool) + 2)`;
    `&N`; `C4:real`; `R0:real`] SCHINZEL_TIJDEMAN_GEN_CHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POS] THEN
    SUBGOAL_THEN `&0 <= log D1 /\ &0 <= log D2 /\ &0 <= log R1 /\
                  &0 <= log(&2)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS];
      REPEAT((MATCH_MP_TAC REAL_LE_ADD ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
             CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `Mc:num` (LABEL_TAC "chain"))] THEN
  MP_TAC(ISPECL
   [`\X. sum(0..N) (\i. (a:num->real) i * X pow i)`; `c:real`;
    `{X | integer X /\ abs X < max (max X0 X3) (&1 + R0)}`]
    SCHINZEL_TIJDEMAN_FINITE_X) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{X | integer X /\ --(max (max X0 X3) (&1 + R0)) <= X /\
                     X <= max (max X0 X3) (&1 + R0)}` THEN
    REWRITE_TAC[FINITE_INTSEG; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `Ms:num` (LABEL_TAC "fin"))] THEN
  EXISTS_TAC `MAX Mc Ms` THEN
  MAP_EVERY X_GEN_TAC [`X:real`; `y:real`; `m:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs X < max (max X0 X3) (&1 + R0)` THENL
   [MATCH_MP_TAC(ARITH_RULE `m <= Ms ==> m <= MAX Mc Ms`) THEN
    USE_THEN "fin" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `y:real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 0` THENL [ASM_REWRITE_TAC[LE_0]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `m <= Mc ==> m <= MAX Mc Ms`) THEN
  SUBGOAL_THEN `1 <= m /\ ~(y = &0) /\ X0 <= abs X /\ X3 <= abs X /\
                &1 + R0 <= abs X`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "desc" (MP_TAC o SPECL [`m:num`; `X:real`; `y:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:complex->num` (X_CHOOSE_THEN
    `e2:complex->num` (X_CHOOSE_THEN `xi1:complex` (X_CHOOSE_THEN
    `xi2:complex` STRIP_ASSUME_TAC)))) THEN
  USE_THEN "small" (MP_TAC o SPEC `X:real`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{Z1, Z2}:complex->bool`; `W1:complex->bool`; `W2:complex->bool`;
    `en:num->complex`; `C:real`; `e1:complex->num`; `e2:complex->num`;
    `xi1:complex`; `xi2:complex`; `Z1:complex`; `Z2:complex`; `k1:num`;
    `k2:num`; `m:num`; `X:real`; `R0:real`; `R1:real`; `D1:real`;
    `D2:real`] SCHINZEL_TIJDEMAN_GEN_BAKER_STEP) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`D1:real`; `D2:real`; `R1:real`; `k1:num`; `k2:num`;
                `CARD(W1:complex->bool)`; `CARD(W2:complex->bool)`;
                `DM:num`; `log(abs X + R0) / &m`]
    SCHINZEL_TIJDEMAN_GEN_LOG_A) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  USE_THEN "chain" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`X:real`;
    `exp(&1) *
     (D1 pow k2 *
      ((&2 * D2 * exp(&k2 * log(abs X + R0) / &m) *
        R1 pow CARD(W2:complex->bool)) pow DM) pow k1) *
     ((exp(&k1 * log(abs X + R0) / &m) * R1 pow CARD(W1:complex->bool))
      pow k2 *
      (R1 pow CARD(W2:complex->bool)) pow k1)`;
    `norm(Cx(&(k1 * k2)) * clog((Cx X - Z1) / (Cx X - Z2)))`] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `log(abs(c * y pow m))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SCHINZEL_TIJDEMAN_LOG_LOWER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "fb" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c * y pow m = sum(0..N) (\i. (a:num->real) i * X pow i)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[REAL_ENTIRE; REAL_POW_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* The Schinzel-Tijdeman theorem (trimming and monic scaling) and the        *)
(* finiteness corollaries.                                                   *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_GEN_ZERO_POLY = prove
 (`!N (a:num->real) x y m.
     (!i. i <= N ==> a i = &0) /\ &2 <= abs y
     ==> ~(y pow m = sum(0..N) (\i. a i * x pow i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `sum(0..N) (\i. (a:num->real) i * x pow i) = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real) pow m = &0` MP_TAC THENL
   [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_POW_EQ_0] THEN STRIP_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let SCHINZEL_TIJDEMAN = prove
 (`!N (a:num->real) z1 z2.
        (!i. integer(a i)) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0)
        ==> ?M. !x y m. integer x /\ integer y /\ &2 <= abs y /\
                        y pow m = sum(0..N) (\i. a i * x pow i)
                        ==> m <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `!i. i <= N ==> (a:num->real) i = &0` THENL
   [EXISTS_TAC `0` THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`N:num`; `a:num->real`; `x:real`; `y:real`; `m:num`]
      SCHINZEL_TIJDEMAN_GEN_ZERO_POLY) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o
    MATCH_MP POLY_TRIM_EXACT_DEGREE) THEN
  SUBGOAL_THEN
   `vsum(0..n) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
    vsum(0..n) (\i. Cx(a i) * z2 pow i) = Cx(&0)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHINZEL_TIJDEMAN_MULT_DEGREE_POS THEN
    MAP_EVERY EXISTS_TAC [`a:num->real`; `z1:complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`n:num`; `\i. if i = n then &1 else (a:num->real) i * a n pow (n - 1 - i)`;
    `(a:num->real) n pow (n - 1)`;
    `Cx((a:num->real) n) * z1`; `Cx((a:num->real) n) * z2`]
   SCHINZEL_TIJDEMAN_GENERAL_MONIC) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[INTEGER_CLOSED] THEN
      MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC INTEGER_POW) THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      MATCH_MP_TAC INTEGER_POW THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
      MATCH_MP_TAC REAL_POW_NZ THEN FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ];
      MP_TAC(SPECL [`n:num`; `a:num->real`; `z1:complex`]
        SUPERELL_MONIC_CVALUE) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_RZERO];
      MP_TAC(SPECL [`n:num`; `a:num->real`; `z2:complex`]
        SUPERELL_MONIC_CVALUE) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_RZERO]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  MP_TAC(SPECL [`n:num`; `a:num->real`; `M:num`]
    SCHINZEL_TIJDEMAN_MONIC_SCALING) THEN
  ASM_REWRITE_TAC[]);;

let SCHINZEL_TIJDEMAN_GEN_DERIV_NONZERO = prove
 (`!N (a:num->real) z.
     ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))
     ==> ~(!i. i <= N ==> a i = &0)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_RZERO; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]);;

let SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS = prove
 (`!N (a:num->real) m0.
        2 <= m0 /\ (!i. integer(a i)) /\
        (if m0 = 2 then 3 else 2) <=
        CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                  ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))}
        ==> FINITE {x,y,m | integer x /\ integer y /\ &2 <= abs y /\
                            m0 <= m /\
                            y pow m = sum(0..N) (\i. a i * x pow i)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `!i. i <= N ==> (a:num->real) i = &0` THENL
   [UNDISCH_TAC
     `(if m0 = 2 then 3 else 2) <=
      CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                  Cx(&0))}` THEN
    SUBGOAL_THEN
     `{z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
           ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[SCHINZEL_TIJDEMAN_GEN_DERIV_NONZERO];
      REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o
    MATCH_MP POLY_TRIM_EXACT_DEGREE) THEN
  SUBGOAL_THEN
   `{z | vsum(0..n) (\i. Cx(a i) * z pow i) = Cx(&0) /\
         ~(vsum(1..n) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))} =
    {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
         ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `a:num->real`] HYPERELL_MAIN_SIMPLE_ROOTS_2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC
     `(if m0 = 2 then 3 else 2) <=
      CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                  Cx(&0))}` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:complex` (X_CHOOSE_THEN `z2:complex`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z1:complex`; `z2:complex`]
    SCHINZEL_TIJDEMAN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "M")) THEN
  MP_TAC(ISPECL
   [`\(m:num) (p:real#real). (FST p, SND p, m)`; `m0..M`;
    `\m. {(x,y) | integer x /\ integer y /\
                  y pow m = sum(0..n) (\i. (a:num->real) i * x pow i)}`]
   FINITE_PRODUCT_DEPENDENT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUPERELLIPTIC_SIMPLE_ROOTS THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `(if m0 = 2 then 3 else 2) <=
      CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                  Cx(&0))}` THEN
    SPEC_TAC(`CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                        ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                          Cx(&0))}`, `k:num`) THEN
    GEN_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `m:num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `(x:real,y:real)`] THEN
  REWRITE_TAC[FST; SND; IN_NUMSEG; IN_ELIM_PAIR_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "M" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[]);;

let SCHINZEL_TIJDEMAN_FINITE = prove
 (`!N (a:num->real) z1 z2.
        (!i. integer(a i)) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0))
        ==> FINITE {x,y,m | integer x /\ integer y /\ &2 <= abs y /\
                            3 <= m /\
                            y pow m = sum(0..N) (\i. a i * x pow i)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `3`]
    SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS) THEN
  CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN TRANS_TAC LE_TRANS `CARD{z1:complex,z2}` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY; ARITH];
    MATCH_MP_TAC CARD_SUBSET] THEN
  ASM_REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; MATCH_MP_TAC FINITE_SUBSET] THEN
  EXISTS_TAC
   `{z | vsum(0..N) (\i. Cx((a:num->real) i) * z pow i) = Cx(&0)}` THEN
  REWRITE_TAC[COMPLEX_POLYFUN_FINITE_ROOTS; IN_NUMSEG; LE_0; CX_INJ] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SCHINZEL_TIJDEMAN_GEN_DERIV_NONZERO];
                  SET_TAC[]]);;

let SCHINZEL_TIJDEMAN_GEN_SQUARE_DIFF = prove
 (`!x y D. integer x /\ integer y /\ ~(D = &0) /\ x pow 2 + D = y pow 2
           ==> abs x <= abs D /\ abs y <= abs D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(y - x) * abs(y + x) = abs D` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN AP_TERM_TAC THEN
    UNDISCH_TAC `x pow 2 + D = y pow 2` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs(y - x) /\ &1 <= abs(y + x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN DISCH_TAC THEN
    UNDISCH_TAC `abs(y - x) * abs(y + x) = abs D` THEN
    ASM_REWRITE_TAC[REAL_ABS_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(y - x) <= abs D /\ abs(y + x) <= abs D`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
    REAL_ARITH_TAC]);;

let SQUARE_PLUS_POW_FINITE = prove
 (`!D. integer D /\ ~(D = &0)
       ==> FINITE {x,y,n | integer x /\ integer y /\ &2 <= abs y /\ 2 <= n /\
                           x pow 2 + D = y pow n}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA) THEN
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    MP_TAC(BETA_RULE(MATCH_MP SCHINZEL_TIJDEMAN_FINITE
                               (end_itlist CONJ (butlast ths)))) THEN
    ASSUME_TAC(BETA_RULE(last ths))) THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{x,y,m | integer x /\ integer y /\ &2 <= abs y /\ 3 <= m /\
             y pow m =
             sum(0..2) (\i. (if i = 0 then D else if i = 1 then &0
                             else &1) * x pow i)} UNION
    IMAGE (\p:real#real. (FST p, SND p, 2))
          ({x | integer x /\ abs x <= abs D} CROSS
           {y | integer y /\ abs y <= abs D})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CROSS THEN
    CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x | integer x /\ --abs D <= x /\ x <= abs D}` THEN
    REWRITE_TAC[FINITE_INTSEG; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE_THM; IN_UNION] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `n:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `n = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISJ2_TAC THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS; PAIR_EQ; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SCHINZEL_TIJDEMAN_GEN_SQUARE_DIFF THEN ASM_REWRITE_TAC[];
    DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The reducible case as corollaries: two roots separated by an integer      *)
(* polynomial b (b(z1) = 0, b(z2) <> 0; for instance roots with different    *)
(* minimal polynomials) are distinct, so SCHINZEL_TIJDEMAN and               *)
(* SCHINZEL_TIJDEMAN_FINITE apply (the simplicity of the roots and a N <> 0  *)
(* are not needed for the bound).                                            *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_SEPARATING_DISTINCT = prove
 (`!z1 z2:complex.
     (?d b. (!i. integer(b i)) /\
            vsum(0..d) (\i. Cx(b i) * z1 pow i) = Cx(&0) /\
            ~(vsum(0..d) (\i. Cx(b i) * z2 pow i) = Cx(&0)))
     ==> ~(z1 = z2)`,
  MESON_TAC[]);;

let SCHINZEL_TIJDEMAN_REDUCIBLE = prove
 (`!N (a:num->real) z1 z2.
    (!i. integer(a i)) /\ ~(a N = &0) /\
    vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
    ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
    vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
    ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
    (?d (b:num->real). (!i. integer(b i)) /\
         vsum(0..d) (\i. Cx(b i) * z1 pow i) = Cx(&0) /\
         ~(vsum(0..d) (\i. Cx(b i) * z2 pow i) = Cx(&0)))
    ==> ?M. !x y m. integer x /\ integer y /\ &2 <= abs y /\
                    y pow m = sum(0..N) (\i. a i * x pow i)
                    ==> m <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN THEN
  MAP_EVERY EXISTS_TAC [`z1:complex`; `z2:complex`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN_SEPARATING_DISTINCT THEN
  ASM_MESON_TAC[]);;

let SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE = prove
 (`!N (a:num->real) z1 z2.
    (!i. integer(a i)) /\ ~(a N = &0) /\
    vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
    ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
    vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
    ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
    (?d (b:num->real). (!i. integer(b i)) /\
         vsum(0..d) (\i. Cx(b i) * z1 pow i) = Cx(&0) /\
         ~(vsum(0..d) (\i. Cx(b i) * z2 pow i) = Cx(&0)))
    ==> FINITE {x,y,m | integer x /\ integer y /\ &2 <= abs y /\ 3 <= m /\
                        y pow m = sum(0..N) (\i. a i * x pow i)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN_FINITE THEN
  MAP_EVERY EXISTS_TAC [`z1:complex`; `z2:complex`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN_SEPARATING_DISTINCT THEN
  ASM_MESON_TAC[]);;

let SCHINZEL_TIJDEMAN_REDUCIBLE_MULT = prove
 (`!N (a:num->real) z1 z2.
    (!i. integer(a i)) /\ ~(a N = &0) /\
    vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
    vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
    (?d (b:num->real). (!i. integer(b i)) /\
         vsum(0..d) (\i. Cx(b i) * z1 pow i) = Cx(&0) /\
         ~(vsum(0..d) (\i. Cx(b i) * z2 pow i) = Cx(&0)))
    ==> ?M. !x y m. integer x /\ integer y /\ &2 <= abs y /\
                    y pow m = sum(0..N) (\i. a i * x pow i)
                    ==> m <= M`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN THEN
  MAP_EVERY EXISTS_TAC [`z1:complex`; `z2:complex`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN_SEPARATING_DISTINCT THEN
  ASM_MESON_TAC[]);;
