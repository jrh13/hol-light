(* ========================================================================= *)
(* The field Q(sqrt 21, sqrt 33) and the Laurent bound for the logarithms of *)
(* its units.                                                                *)
(*                                                                           *)
(* Purpose: theta = sqrt 21 + sqrt 33 is a root of x^4 - 108 x^2 + 144 with  *)
(* conjugates r k = e1 sqrt 21 + e2 sqrt 33, the signs (e1, e2) being        *)
(* (1, 1), (1, -1), (-1, 1), (-1, -1) for k = 1, 2, 3, 4; the polynomial is  *)
(* irreducible since 1, sqrt 21, sqrt 33 and sqrt 21 sqrt 33 are linearly    *)
(* independent over Q (sqrt 21, sqrt 33 and sqrt 693 are irrational;         *)
(* CLASSNO_NF_SQRT_INDEPENDENT, from the Kummer theory of Baker/kummer.ml at *)
(* the prime 2), which gives NF_DATA_SQRT21_SQRT33. The units                *)
(* eps1 = (5 + sqrt 21) / 2 and eps2 = 23 + 4 sqrt 33 are elements of K, as  *)
(* 48 eps1 = 120 - 96 theta + theta^3 and                                    *)
(* 6 eps2 = 138 + 120 theta - theta^3, and algebraic integers (roots of      *)
(* x^2 - 5 x + 1 and of x^2 - 46 x + 1); their conjugate vectors are         *)
(* (eps1, eps1, 1/eps1, 1/eps1) and (eps2, 1/eps2, eps2, 1/eps2), so that    *)
(* with denominator 1 their pair heights are exactly log(eps1) / 2 and       *)
(* log(eps2) / 2. Then LAURENT_NF_REAL with n = 4 gives                      *)
(* CLASSNO_LAURENT_INSTANCE, the lower bound for b2 log eps2 - b1 log eps1   *)
(* used to bound d (in place of Theorem 3.1 in Baker, Transcendental Number  *)
(* Theory, Ch. 5, sec. 4).                                                   *)
(*                                                                           *)
(* Main results: NF_DATA_SQRT21_SQRT33, CLASSNO_LAURENT_INSTANCE; library    *)
(* style CLASSNO_NF_RATIONAL_IRRATIONAL, CLASSNO_NF_IRRATIONAL_SQRT,         *)
(* CLASSNO_NF_SQRT_INDEPENDENT, CLASSNO_NF_ALGEBRAIC_INTEGER_QUADRATIC,      *)
(* CLASSNO_NF_CPRODUCT_4; helper names CLASSNO_NF_* (and the tactic          *)
(* CLASSNO_NF_RATIONAL_TAC).                                                 *)
(*                                                                           *)
(* Uses: Baker/nf_defs.ml (nf_data), Baker/laurent_nf_defs.ml (nf_elem,      *)
(* nf_alg_int, nf_proj_height), Baker/laurent_alg.ml (LAURENT_NF_REAL,       *)
(* LAURENT_ALG_INT_CONST), Baker/algint.ml (ALGEBRAIC_INTEGER_MONIC,         *)
(* VSUM_NUMSEG_RESTRICT_LE), ANT/complex_embeddings.ml                       *)
(* (COMPLEX_PRIME_SUBFIELD), Baker/lemmas.ml (COMPLEX_SUBRING_CLOSED),       *)
(* Baker/kummer.ml (KUMMER_COMPLEX_INDEPENDENT); 100/sqrt.ml                 *)
(* (IRRATIONAL_SQRT_NONSQUARE).                                              *)
(* ========================================================================= *)

needs "100/sqrt.ml";;
needs "Baker/kummer.ml";;
needs "Baker/laurent_alg.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Rationality side conditions, irrational square roots, and the linear      *)
(* independence of 1, sqrt p, sqrt q, sqrt p sqrt q over the rationals.      *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_NF_RATIONAL_TAC =
  REPEAT(FIRST
   [MATCH_MP_TAC RATIONAL_ADD THEN CONJ_TAC;
    MATCH_MP_TAC RATIONAL_SUB THEN CONJ_TAC;
    MATCH_MP_TAC RATIONAL_MUL THEN CONJ_TAC;
    MATCH_MP_TAC RATIONAL_DIV THEN CONJ_TAC;
    MATCH_MP_TAC RATIONAL_POW;
    MATCH_MP_TAC RATIONAL_NEG;
    MATCH_MP_TAC RATIONAL_ABS]) THEN
  ASM_REWRITE_TAC[RATIONAL_NUM];;

let CLASSNO_NF_RATIONAL_IRRATIONAL = prove
 (`!x y z. rational x /\ rational y /\ ~rational z /\ x + y * z = &0
           ==> x = &0 /\ y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `y:real = &0` THENL
   [UNDISCH_TAC `(x:real) + y * z = &0` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    UNDISCH_TAC `~rational z` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `z = --(x:real) / y` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(x:real) + y * z = &0`; `~(y:real = &0)`] THEN
      CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[RATIONAL_DIV; RATIONAL_NEG]]]);;

let CLASSNO_NF_IRRATIONAL_SQRT = prove
 (`!n k. k EXP 2 < n /\ n < (k + 1) EXP 2 ==> ~rational(sqrt(&n))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
    MATCH_MP IRRATIONAL_SQRT_NONSQUARE) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXP_MONO_LT; ARITH_EQ]) THEN ASM_ARITH_TAC);;

(* 1, sqrt p, sqrt q and sqrt p sqrt q are linearly independent over Q if    *)
(* sqrt p, sqrt q and sqrt(p q) are irrational: the Kummer theory at the     *)
(* prime 2 over the rationals, with the radical sqrt q adjoined, gives       *)
(* a + c sqrt q = b + d sqrt q = 0.                                          *)

let CLASSNO_NF_SQRT_INDEPENDENT = prove
 (`!p q a b c d.
        rational p /\ rational q /\ &0 <= p /\ &0 <= q /\
        ~rational(sqrt p) /\ ~rational(sqrt q) /\ ~rational(sqrt(p * q)) /\
        rational a /\ rational b /\ rational c /\ rational d /\
        a + b * sqrt p + c * sqrt q + d * sqrt p * sqrt q = &0
        ==> a = &0 /\ b = &0 /\ c = &0 /\ d = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p = &0) /\ ~(q = &0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SQRT_0; RATIONAL_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x. Cx x IN {Cx x | rational x} <=> rational x` ASSUME_TAC
  THENL [REWRITE_TAC[IN_ELIM_THM; CX_INJ] THEN MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `{Cx x | rational x}`; `(\r. Cx q):num->complex`;
                 `(\r. Cx(sqrt q)):num->complex`; `1`; `Cx p`; `Cx(sqrt p)`;
                 `\j. if j = 0 then Cx(a + c * sqrt q)
                      else Cx(b + d * sqrt q)`]
    KUMMER_COMPLEX_INDEPENDENT) THEN
  ASM_SIMP_TAC[PRIME_2; GSYM CX_POW; SQRT_POW_2; CX_INJ; NUMSEG_SING;
               CPRODUCT_SING; IMAGE_CLAUSES] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_PRIME_SUBFIELD] THEN
      SIMP_TAC[SUBFIELD_SUBFIELD_GENERATED; FIELD_COMPLEX_RING];
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `jj:num->num` (X_CHOOSE_THEN `g:complex`
       (CONJUNCTS_THEN2 (MP_TAC o SPEC `1`) MP_TAC))) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC)
        MP_TAC) THEN
      ASM_REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; CX_INJ] THEN
      REWRITE_TAC[ARITH_RULE `n < 2 <=> n = 0 \/ n = 1`] THEN
      DISCH_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [UNDISCH_TAC `~rational(sqrt p)`;
        UNDISCH_TAC `~rational(sqrt(p * q))` THEN
        SUBGOAL_THEN `p * q = (q * x) pow 2` SUBST1_TAC THENL
         [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC]] THEN
      ASM_REWRITE_TAC[real_pow; REAL_MUL_LID; POW_2_SQRT_ABS] THEN
      CLASSNO_NF_RATIONAL_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[CX_ADD; CX_MUL] THEN
      ASM_SIMP_TAC[COMPLEX_SUBRING_CLOSED; SUBRING_SUBRING_GENERATED;
                   SUBRING_GENERATED_INC_GEN; COMPLEX_RING_CLAUSES; IN_UNIV;
                   IN_UNION; IN_SING];
      CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC(ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
      REWRITE_TAC[ARITH; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
      UNDISCH_TAC `a + b * sqrt p + c * sqrt q + d * sqrt p * sqrt q = &0` THEN
      CONV_TAC REAL_RING];
    DISCH_THEN(fun th -> MP_TAC(SPEC `0` th) THEN MP_TAC(SPEC `1` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[CX_INJ] THEN
    ASM_MESON_TAC[CLASSNO_NF_RATIONAL_IRRATIONAL]]);;

(* ------------------------------------------------------------------------- *)
(* Two small tools: a real root of a monic integer quadratic is an algebraic *)
(* integer; a product over 1..4 written out.                                 *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_NF_ALGEBRAIC_INTEGER_QUADRATIC = prove
 (`!x a b. integer a /\ integer b /\ x pow 2 + a * x + b = &0
           ==> algebraic_integer(Cx x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALGEBRAIC_INTEGER_MONIC] THEN
  MAP_EVERY EXISTS_TAC [`2`; `\i. if i = 0 then (b:real) else a`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
   [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(LAND_CONV(RAND_CONV EXPAND_VSUM_CONV)) THEN
  REWRITE_TAC[ARITH; GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  UNDISCH_TAC `(x:real) pow 2 + a * x + b = &0` THEN CONV_TAC REAL_RING);;

let CLASSNO_NF_CPRODUCT_4 = prove
 (`!f. cproduct(1..4) f = f 1 * f 2 * f 3 * f 4`,
  SIMP_TAC[num_CONV `4`; num_CONV `3`; num_CONV `2`;
           CPRODUCT_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[NUMSEG_SING; CPRODUCT_SING; ARITH; COMPLEX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* The quartic x^4 - 108 x^2 + 144 = prod (x - (e1 sqrt 21 + e2 sqrt 33))    *)
(* and its irreducibility: no non-zero rational relation of degree <= 3 at   *)
(* any root, since x^2 = 54 + 2 e1 e2 sqrt 21 sqrt 33 and                    *)
(* x^3 = 120 e1 sqrt 21 + 96 e2 sqrt 33 for x = e1 sqrt 21 + e2 sqrt 33.     *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_NF_IRRATIONAL_SQRTS = prove
 (`~rational(sqrt(&21)) /\ ~rational(sqrt(&33)) /\
   ~rational(sqrt(&21 * &33))`,
  REWRITE_TAC[REAL_OF_NUM_MUL; ARITH] THEN REPEAT CONJ_TAC THEN
  MATCH_MP_TAC CLASSNO_NF_IRRATIONAL_SQRT THENL
   [EXISTS_TAC `4`; EXISTS_TAC `5`; EXISTS_TAC `26`] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CLASSNO_NF_QUARTIC_DEGREE = prove
 (`!e1 e2 b0 b1 b2 b3.
        rational e1 /\ rational e2 /\ e1 pow 2 = &1 /\ e2 pow 2 = &1 /\
        rational b0 /\ rational b1 /\ rational b2 /\ rational b3 /\
        b0 + b1 * (e1 * sqrt(&21) + e2 * sqrt(&33)) +
        b2 * (e1 * sqrt(&21) + e2 * sqrt(&33)) pow 2 +
        b3 * (e1 * sqrt(&21) + e2 * sqrt(&33)) pow 3 = &0
        ==> b0 = &0 /\ b1 = &0 /\ b2 = &0 /\ b3 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&21`; `&33`; `(b0:real) + &54 * b2`;
                `((b1:real) + &120 * b3) * e1`; `((b1:real) + &96 * b3) * e2`;
                `&2 * (b2:real) * e1 * e2`]
    CLASSNO_NF_SQRT_INDEPENDENT) THEN
  REWRITE_TAC[CLASSNO_NF_IRRATIONAL_SQRTS; RATIONAL_NUM; REAL_POS] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [CLASSNO_NF_RATIONAL_TAC; CLASSNO_NF_RATIONAL_TAC;
      CLASSNO_NF_RATIONAL_TAC; CLASSNO_NF_RATIONAL_TAC; ALL_TAC] THEN
    MP_TAC(SPEC `&21` SQRT_POW_2) THEN MP_TAC(SPEC `&33` SQRT_POW_2) THEN
    REWRITE_TAC[REAL_POS] THEN
    MAP_EVERY UNDISCH_TAC
     [`(b0:real) + b1 * (e1 * sqrt(&21) + e2 * sqrt(&33)) +
       b2 * (e1 * sqrt(&21) + e2 * sqrt(&33)) pow 2 +
       b3 * (e1 * sqrt(&21) + e2 * sqrt(&33)) pow 3 = &0`;
      `(e1:real) pow 2 = &1`; `(e2:real) pow 2 = &1`] THEN
    CONV_TAC REAL_RING;
    MAP_EVERY UNDISCH_TAC [`(e1:real) pow 2 = &1`; `(e2:real) pow 2 = &1`] THEN
    CONV_TAC REAL_RING]);;

let CLASSNO_NF_DEGREE = prove
 (`!e1 e2 m b.
        rational e1 /\ rational e2 /\ e1 pow 2 = &1 /\ e2 pow 2 = &1 /\
        m < 4 /\ (!i. integer(b i)) /\
        vsum(0..m) (\i. Cx(b i) * Cx(e1 * sqrt(&21) + e2 * sqrt(&33)) pow i) =
        Cx(&0)
        ==> !i. i <= m ==> b i = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `bb = \i. if i <= m then (b:num->real) i else &0` THEN
  SUBGOAL_THEN
   `vsum(0..3) (\i. Cx((bb:num->real) i) *
                    Cx(e1 * sqrt(&21) + e2 * sqrt(&33)) pow i) = Cx(&0)`
  MP_TAC THENL
   [EXPAND_TAC "bb" THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
    ASM_SIMP_TAC[VSUM_NUMSEG_RESTRICT_LE; ARITH_RULE `m < 4 ==> m <= 3`];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_VSUM_CONV)) THEN
  REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  REWRITE_TAC[real_pow; REAL_POW_1; REAL_MUL_RID] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`e1:real`; `e2:real`; `(bb:num->real) 0`; `(bb:num->real) 1`;
                `(bb:num->real) 2`; `(bb:num->real) 3`]
    CLASSNO_NF_QUARTIC_DEGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "bb" THEN REPEAT CONJ_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[RATIONAL_INTEGER; RATIONAL_NUM];
    ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(b:num->real) i = bb i` SUBST1_TAC THENL
   [EXPAND_TAC "bb" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let CLASSNO_NF_SIGN = prove
 (`!P. rational(if P then &1 else -- &1) /\
       (if P then &1 else -- &1) pow 2 = &1`,
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[RATIONAL_NUM; RATIONAL_NEG_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* The roots of NF_DATA_SQRT21_SQRT33 in the uniform form (valid for all k). *)

let CLASSNO_NF_ROOTS_SIGNS = prove
 (`(\k. if k = 1 then Cx(sqrt(&21) + sqrt(&33))
        else if k = 2 then Cx(sqrt(&21) - sqrt(&33))
        else if k = 3 then Cx(--sqrt(&21) + sqrt(&33))
        else Cx(--sqrt(&21) - sqrt(&33))) =
   (\k. Cx((if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21) +
           (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33)))`,
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
  MAP_EVERY ASM_CASES_TAC [`k = 1`; `k = 2`; `k = 3`] THEN
  ASM_REWRITE_TAC[ARITH; CX_INJ] THEN REAL_ARITH_TAC);;

let CLASSNO_NF_DATA_SIGNS = prove
 (`nf_data 4 (\i. if i = 0 then &144 else if i = 2 then -- &108
                 else if i = 4 then &1 else &0)
            (\k. Cx((if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21) +
                    (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33)))`,
  REWRITE_TAC[nf_data; ARITH] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG];
    GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_VSUM_CONV) THEN
    REWRITE_TAC[CLASSNO_NF_CPRODUCT_4; ARITH] THEN
    MP_TAC(SPEC `&21` SQRT_POW_2) THEN MP_TAC(SPEC `&33` SQRT_POW_2) THEN
    REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[GSYM CX_INJ; CX_POW; CX_ADD; CX_MUL; CX_NEG] THEN
    CONV_TAC COMPLEX_RING;
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC CLASSNO_NF_DEGREE THEN
    MAP_EVERY EXISTS_TAC
     [`if k = 1 \/ k = 2 then &1 else -- &1:real`;
      `if k = 1 \/ k = 3 then &1 else -- &1:real`] THEN
    ASM_REWRITE_TAC[CLASSNO_NF_SIGN]]);;

let NF_DATA_SQRT21_SQRT33 = prove
 (`nf_data 4 (\i. if i = 0 then &144 else if i = 2 then -- &108
                 else if i = 4 then &1 else &0)
            (\k. if k = 1 then Cx(sqrt(&21) + sqrt(&33))
                 else if k = 2 then Cx(sqrt(&21) - sqrt(&33))
                 else if k = 3 then Cx(--sqrt(&21) + sqrt(&33))
                 else Cx(--sqrt(&21) - sqrt(&33)))`,
  REWRITE_TAC[CLASSNO_NF_ROOTS_SIGNS; CLASSNO_NF_DATA_SIGNS]);;

(* ------------------------------------------------------------------------- *)
(* The units eps1 = (5 + sqrt 21) / 2 and eps2 = 23 + 4 sqrt 33 as algebraic *)
(* integers of K with their conjugate vectors, and their pair heights.       *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_NF_SQRT_BOUNDS = prove
 (`&4 < sqrt(&21) /\ sqrt(&21) < &5 /\
   &11 / &2 <= sqrt(&33) /\ sqrt(&33) <= &6`,
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RSQRT; MATCH_MP_TAC REAL_LT_LSQRT;
    MATCH_MP_TAC REAL_LE_RSQRT; MATCH_MP_TAC REAL_LE_LSQRT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let CLASSNO_NF_UNITS_GE_2 = prove
 (`&2 <= (&5 + sqrt(&21)) / &2 /\ &2 <= &23 + &4 * sqrt(&33)`,
  MP_TAC CLASSNO_NF_SQRT_BOUNDS THEN REAL_ARITH_TAC);;

let CLASSNO_NF_EPS1_POLY = prove
 (`!e1 e2. e1 pow 2 = &1 /\ e2 pow 2 = &1
           ==> Cx(&48) * Cx((&5 + e1 * sqrt(&21)) / &2) =
               vsum(0..3) (\i. Cx(if i = 0 then &120 else if i = 1 then -- &96
                                  else if i = 3 then &1 else &0) *
                               Cx(e1 * sqrt(&21) + e2 * sqrt(&33)) pow i)`,
  REPEAT STRIP_TAC THEN CONV_TAC(RAND_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[ARITH; GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  MP_TAC(SPEC `&21` SQRT_POW_2) THEN MP_TAC(SPEC `&33` SQRT_POW_2) THEN
  REWRITE_TAC[REAL_POS] THEN
  MAP_EVERY UNDISCH_TAC [`(e1:real) pow 2 = &1`; `(e2:real) pow 2 = &1`] THEN
  CONV_TAC REAL_RING);;

let CLASSNO_NF_EPS2_POLY = prove
 (`!e1 e2. e1 pow 2 = &1 /\ e2 pow 2 = &1
           ==> Cx(&6) * Cx(&23 + &4 * e2 * sqrt(&33)) =
               vsum(0..3) (\i. Cx(if i = 0 then &138 else if i = 1 then &120
                                  else if i = 3 then -- &1 else &0) *
                               Cx(e1 * sqrt(&21) + e2 * sqrt(&33)) pow i)`,
  REPEAT STRIP_TAC THEN CONV_TAC(RAND_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[ARITH; GSYM CX_POW; GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN
  MP_TAC(SPEC `&21` SQRT_POW_2) THEN MP_TAC(SPEC `&33` SQRT_POW_2) THEN
  REWRITE_TAC[REAL_POS] THEN
  MAP_EVERY UNDISCH_TAC [`(e1:real) pow 2 = &1`; `(e2:real) pow 2 = &1`] THEN
  CONV_TAC REAL_RING);;

let CLASSNO_NF_ALG_INT_EPS1 = prove
 (`nf_alg_int 4
    (\k. Cx((if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21) +
            (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33)))
    (\k. Cx((&5 + (if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21)) / &2))`,
  REWRITE_TAC[nf_alg_int; nf_elem; ARITH; REAL_MUL_LID] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`&48:real`;
      `\i. if i = 0 then &120 else if i = 1 then -- &96
           else if i = 3 then &1 else &0:real`] THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_EQ; ARITH] THEN CONJ_TAC THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CLASSNO_NF_EPS1_POLY THEN REWRITE_TAC[CLASSNO_NF_SIGN]];
    MATCH_MP_TAC CLASSNO_NF_ALGEBRAIC_INTEGER_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`-- &5:real`; `&1:real`] THEN
    REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG] THEN
    MP_TAC(SPEC `&21` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING]);;

let CLASSNO_NF_ALG_INT_EPS2 = prove
 (`nf_alg_int 4
    (\k. Cx((if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21) +
            (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33)))
    (\k. Cx(&23 + &4 * (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33)))`,
  REWRITE_TAC[nf_alg_int; nf_elem; ARITH; REAL_MUL_LID] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC
     [`&6:real`;
      `\i. if i = 0 then &138 else if i = 1 then &120
           else if i = 3 then -- &1 else &0:real`] THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_EQ; ARITH] THEN CONJ_TAC THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG];
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC CLASSNO_NF_EPS2_POLY THEN REWRITE_TAC[CLASSNO_NF_SIGN]];
    MATCH_MP_TAC CLASSNO_NF_ALGEBRAIC_INTEGER_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`-- &46:real`; `&1:real`] THEN
    REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG] THEN
    MP_TAC(SPEC `&33` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING]);;

let CLASSNO_NF_HEIGHT_EPS1 = prove
 (`nf_proj_height 4
    (\k. Cx((&5 + (if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21)) / &2))
    (\k. Cx(&1)) =
   log((&5 + sqrt(&21)) / &2) / &2`,
  REWRITE_TAC[nf_proj_height; SUM_4; ARITH; COMPLEX_NORM_CX; REAL_ABS_NUM;
              REAL_MUL_LID; REAL_MUL_LNEG] THEN
  MP_TAC CLASSNO_NF_SQRT_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `max (abs((&5 + sqrt(&21)) / &2)) (&1) = (&5 + sqrt(&21)) / &2 /\
    max (abs((&5 + --sqrt(&21)) / &2)) (&1) = &1`
   (fun th -> REWRITE_TAC[th; LOG_1]) THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let CLASSNO_NF_HEIGHT_EPS2 = prove
 (`nf_proj_height 4
    (\k. Cx(&23 + &4 * (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33)))
    (\k. Cx(&1)) =
   log(&23 + &4 * sqrt(&33)) / &2`,
  REWRITE_TAC[nf_proj_height; SUM_4; ARITH; COMPLEX_NORM_CX; REAL_ABS_NUM;
              REAL_MUL_LID; REAL_MUL_LNEG] THEN
  MP_TAC CLASSNO_NF_SQRT_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `max (abs(&23 + &4 * sqrt(&33))) (&1) = &23 + &4 * sqrt(&33) /\
    max (abs(&23 + &4 * --sqrt(&33))) (&1) = &1`
   (fun th -> REWRITE_TAC[th; LOG_1]) THENL
   [CONJ_TAC THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let CLASSNO_NF_LOG_FACTS = prove
 (`!x. &2 <= x
       ==> &1 < x /\ log x <= &4 * (log x / &2) /\ &1 <= &4 * (log x / &2)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= log x` MP_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log(&2)` THEN REWRITE_TAC[LOG_2_BOUNDS] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `&2 <= (x:real)` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The instance of LAURENT_NF_REAL: n = 4, x1 = eps1, x2 = eps2,             *)
(* be1 = eps1, be2 = eps2, ga1 = ga2 = 1, A1 = log(eps1) / 2 and             *)
(* A2 = log(eps2) / 2 (the pair heights).                                    *)
(* ------------------------------------------------------------------------- *)

let CLASSNO_LAURENT_INSTANCE = prove
 (`!b1 b2. 1 <= b1 /\ 1 <= b2 /\
          ~(&b2 * log(&23 + &4 * sqrt(&33)) = &b1 * log((&5 + sqrt(&21)) / &2))
          ==> exp(--(&32 * &4 pow 4 *
                     max (max (&10 / &4) (&1))
                         (log(&b1 / (&4 * (log(&23 + &4 * sqrt(&33)) / &2)) +
                              &b2 / (&4 * (log((&5 + sqrt(&21)) / &2) / &2))) +
                          &38 / &100) pow 2 *
                     (log((&5 + sqrt(&21)) / &2) / &2) *
                     (log(&23 + &4 * sqrt(&33)) / &2)))
              <= abs(&b2 * log(&23 + &4 * sqrt(&33)) -
                     &b1 * log((&5 + sqrt(&21)) / &2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`4`;
    `\i. if i = 0 then &144 else if i = 2 then -- &108
         else if i = 4 then &1 else &0:real`;
    `\k. Cx((if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21) +
            (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33))`;
    `\k. Cx((&5 + (if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21)) / &2)`;
    `\k:num. Cx(&1)`;
    `\k. Cx(&23 + &4 * (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33))`;
    `\k:num. Cx(&1)`;
    `(&5 + sqrt(&21)) / &2`; `&23 + &4 * sqrt(&33)`; `b1:num`; `b2:num`;
    `log((&5 + sqrt(&21)) / &2) / &2`; `log(&23 + &4 * sqrt(&33)) / &2`]
   LAURENT_NF_REAL) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  MP_TAC(MATCH_MP CLASSNO_NF_LOG_FACTS (CONJUNCT1 CLASSNO_NF_UNITS_GE_2)) THEN
  MP_TAC(MATCH_MP CLASSNO_NF_LOG_FACTS (CONJUNCT2 CLASSNO_NF_UNITS_GE_2)) THEN
  MP_TAC(ISPECL
   [`4`;
    `\i. if i = 0 then &144 else if i = 2 then -- &108
         else if i = 4 then &1 else &0:real`;
    `\k. Cx((if k = 1 \/ k = 2 then &1 else -- &1) * sqrt(&21) +
            (if k = 1 \/ k = 3 then &1 else -- &1) * sqrt(&33))`;
    `&1:real`] LAURENT_ALG_INT_CONST) THEN
  REWRITE_TAC[CLASSNO_NF_DATA_SIGNS; INTEGER_CLOSED] THEN
  REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[CLASSNO_NF_ALG_INT_EPS1; CLASSNO_NF_ALG_INT_EPS2;
                  CLASSNO_NF_HEIGHT_EPS1; CLASSNO_NF_HEIGHT_EPS2;
                  REAL_LE_REFL; ARITH; REAL_MUL_LID; COMPLEX_MUL_RID;
                  CX_INJ; REAL_OF_NUM_EQ]);;
