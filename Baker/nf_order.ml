(* ========================================================================= *)
(* Number field data and the order Z[theta].                                 *)
(*                                                                           *)
(* Purpose: basic theory of nf_data and nf_order (Baker/nf_defs.ml): ring    *)
(* structure of the order, conjugation, representatives of degree < n,       *)
(* characteristic polynomial and norm, adjugate, units; roots of integer     *)
(* cubics without rational roots have degree 3; the example of the cube      *)
(* roots of 2. (The Northcott finiteness NF_ORDER_NORTHCOTT of the order is  *)
(* in Baker/ant_bridge_nf.ml, from that of the ring of integers.)            *)
(*                                                                           *)
(* Main results: NF_ORDER_REDUCE, NF_ORDER_REDUCE_UNIQUE (reduced            *)
(* representatives), NF_ORDER_ZERO (an element vanishing at one conjugate    *)
(* vanishes at all), NF_NORM_INTEGER,                                        *)
(* NF_ADJUGATE, NF_UNIT_NORM, NF_CUBIC_ROOT_DEGREE                           *)
(* (a root of an integer cubic without rational roots has degree 3),         *)
(* NF_CUBE2_DEGREE, NF_EXAMPLE_CUBE_ROOT_2,                                  *)
(* NF_EXAMPLE_CUBE_ROOT_2_UNIT.                                              *)
(*                                                                           *)
(* Uses: Baker/algebraic.ml (COMPLEX_POLYFUN_*, Newton identities),          *)
(* Baker/algint.ml (algebraic integers, int_polyfun),                        *)
(* Baker/nf_defs.ml (NF_DATA_1_IN), Baker/lemmas.ml (COMPLEX_POLYFUN_AT_0).  *)
(* ========================================================================= *)

needs "Baker/algint.ml";;
needs "Baker/nf_defs.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Explicit polynomials: Horner split, products of integer polynomials.      *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_HORNER = prove
 (`!(c:num->complex) d z.
        vsum(0..SUC d) (\i. c i * z pow i) =
        c 0 + z * vsum(0..d) (\i. c(SUC i) * z pow i)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP VSUM_CLAUSES_LEFT (SPEC `SUC d` LE_0)] THEN
  REWRITE_TAC[ADD1; VSUM_OFFSET; complex_pow; COMPLEX_MUL_RID] THEN
  AP_TERM_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_POW_1] THEN
  REPEAT STRIP_TAC THEN CONV_TAC COMPLEX_RING);;

let COMPLEX_POLYFUN_CONST = prove
 (`!m (x:real) z.
        vsum(0..m) (\i. Cx(if i = 0 then x else &0) * z pow i) = Cx x`,
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; NOT_SUC; complex_pow] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; COMPLEX_MUL_RID]);;

let INT_POLYFUN_EQ = prove
 (`!n f g. int_polyfun n f /\ (!z. g z = f z) ==> int_polyfun n g`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_REWRITE_TAC[FUN_EQ_THM]);;

let INT_POLYFUN_ID = prove
 (`int_polyfun 1 (\z. z)`,
  MP_TAC(SPECL [`0`; `\z:complex. Cx(&1)`; `&0`] INT_POLYFUN_MUL_LINEAR) THEN
  SIMP_TAC[INT_POLYFUN_CONST; INTEGER_CLOSED; COMPLEX_SUB_RZERO;
           COMPLEX_MUL_RID; GSYM ONE]);;

let INT_POLYFUN_MUL = prove
 (`!m n f g. int_polyfun m f /\ int_polyfun n g
             ==> int_polyfun (m + n) (\z. f z * g z)`,
  GEN_TAC THEN INDUCT_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [int_polyfun] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID;
                ADD_CLAUSES] THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    MATCH_MP_TAC INT_POLYFUN_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_POLYFUN_HORNER] THEN
  FIRST_X_ASSUM(MP_TAC o BETA_RULE o SPECL
   [`f:complex->complex`;
    `\z. vsum(0..n) (\i. Cx((c:num->real)(SUC i)) * z pow i)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[int_polyfun] THEN
    EXISTS_TAC `\i. (c:num->real)(SUC i)` THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC INT_POLYFUN_EQ THEN
  EXISTS_TAC
   `\z. Cx((c:num->real) 0) * (f:complex->complex) z +
        (z - Cx(&0)) * (f z * vsum(0..n) (\i. Cx(c(SUC i)) * z pow i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_POLYFUN_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_POLYFUN_MONO THEN EXISTS_TAC `m:num` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_POLYFUN_CMUL THEN ASM_REWRITE_TAC[ETA_AX];
        ARITH_TAC];
      REWRITE_TAC[ADD_CLAUSES] THEN MATCH_MP_TAC INT_POLYFUN_MUL_LINEAR THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED]];
    REWRITE_TAC[COMPLEX_SUB_RZERO] THEN CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Elements of the order as values of integer polynomial functions.          *)
(* ------------------------------------------------------------------------- *)

let NF_ORDER_POLYFUN = prove
 (`!n r a. nf_order n r a <=>
           ?d f. int_polyfun d f /\ !k. k IN 1..n ==> a k = f(r k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_order; int_polyfun] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `p:num->real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC
     [`d:num`; `\z. vsum(0..d) (\i. Cx((p:num->real) i) * z pow i)`] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `p:num->real` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `f:complex->complex`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC)
                       ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`d:num`; `p:num->real`] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Ring structure of the order Z[theta].                                     *)
(* ------------------------------------------------------------------------- *)

let NF_ORDER_CX = prove
 (`!n r x. integer x ==> nf_order n r (\k. Cx x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NF_ORDER_POLYFUN] THEN
  MAP_EVERY EXISTS_TAC [`0`; `\z:complex. Cx x`] THEN
  ASM_SIMP_TAC[INT_POLYFUN_CONST]);;

let NF_ORDER_ROOT = prove
 (`!n r. nf_order n r r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NF_ORDER_POLYFUN] THEN
  MAP_EVERY EXISTS_TAC [`1`; `\z:complex. z`] THEN
  REWRITE_TAC[INT_POLYFUN_ID]);;

let NF_ORDER_EQ = prove
 (`!n r a b. nf_order n r a /\ (!k. k IN 1..n ==> b k = a k)
             ==> nf_order n r b`,
  REWRITE_TAC[nf_order] THEN MESON_TAC[]);;

let NF_ORDER_ADD = prove
 (`!n r a b. nf_order n r a /\ nf_order n r b
             ==> nf_order n r (\k. a k + b k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NF_ORDER_POLYFUN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `d1:num` (X_CHOOSE_THEN `f1:complex->complex`
      STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `d2:num` (X_CHOOSE_THEN `f2:complex->complex`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`d1 + d2:num`; `\z. (f1:complex->complex) z + f2 z`] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC INT_POLYFUN_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_POLYFUN_MONO THENL
   [EXISTS_TAC `d1:num`; EXISTS_TAC `d2:num`] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let NF_ORDER_NEG = prove
 (`!n r a. nf_order n r a ==> nf_order n r (\k. --(a k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NF_ORDER_POLYFUN] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `f:complex->complex`
      STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `\z. --((f:complex->complex) z)`] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC INT_POLYFUN_EQ THEN
  EXISTS_TAC `\z. Cx(-- &1) * (f:complex->complex) z` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_POLYFUN_CMUL THEN
    ASM_REWRITE_TAC[ETA_AX; INTEGER_NEG; INTEGER_CLOSED];
    REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING]);;

let NF_ORDER_SUB = prove
 (`!n r a b. nf_order n r a /\ nf_order n r b
             ==> nf_order n r (\k. a k - b k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. (a:num->complex) k + --((b:num->complex) k)` THEN
  REWRITE_TAC[complex_sub] THEN MATCH_MP_TAC NF_ORDER_ADD THEN
  ASM_SIMP_TAC[NF_ORDER_NEG]);;

let NF_ORDER_MUL = prove
 (`!n r a b. nf_order n r a /\ nf_order n r b
             ==> nf_order n r (\k. a k * b k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[NF_ORDER_POLYFUN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `d1:num` (X_CHOOSE_THEN `f1:complex->complex`
      STRIP_ASSUME_TAC))
   (X_CHOOSE_THEN `d2:num` (X_CHOOSE_THEN `f2:complex->complex`
      STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC
   [`d1 + d2:num`; `\z. (f1:complex->complex) z * f2 z`] THEN
  ASM_SIMP_TAC[INT_POLYFUN_MUL]);;

let NF_ORDER_POW = prove
 (`!n r a m. nf_order n r a ==> nf_order n r (\k. a k pow m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`m:num`,`m:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[complex_pow] THENL
   [MATCH_MP_TAC NF_ORDER_CX THEN REWRITE_TAC[INTEGER_CLOSED];
    MATCH_MP_TAC NF_ORDER_MUL THEN ASM_REWRITE_TAC[]]);;

let NF_ORDER_VSUM = prove
 (`!n r (f:A->num->complex) s.
        FINITE s /\ (!i. i IN s ==> nf_order n r (f i))
        ==> nf_order n r (\k. vsum s (\i. f i k))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_VEC_0] THEN MATCH_MP_TAC NF_ORDER_CX THEN
    REWRITE_TAC[INTEGER_CLOSED];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_ADD THEN
    ASM_SIMP_TAC[ETA_AX]]);;

let NF_ORDER_CPRODUCT = prove
 (`!n r (f:A->num->complex) s.
        FINITE s /\ (!i. i IN s ==> nf_order n r (f i))
        ==> nf_order n r (\k. cproduct s (\i. f i k))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_CX THEN REWRITE_TAC[INTEGER_CLOSED];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_MUL THEN
    ASM_SIMP_TAC[ETA_AX]]);;

(* ------------------------------------------------------------------------- *)
(* Basic consequences of nf_data.                                            *)
(* ------------------------------------------------------------------------- *)

let NF_DATA = prove
 (`!n c r. nf_data n c r ==> 1 <= n /\ (!i. integer(c i)) /\ c n = &1`,
  SIMP_TAC[nf_data]);;

let NF_DATA_FACTOR = prove
 (`!n c r. nf_data n c r
           ==> !z. vsum(0..n) (\i. Cx(c i) * z pow i) =
                   cproduct(1..n) (\k. z - r k)`,
  SIMP_TAC[nf_data]);;

let NF_DATA_ROOT = prove
 (`!n c r k. nf_data n c r /\ k IN 1..n
             ==> vsum(0..n) (\i. Cx(c i) * r k pow i) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_FACTOR th]) THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[COMPLEX_SUB_REFL]);;

let NF_DATA_MONIC = prove
 (`!n c r k. nf_data n c r /\ k IN 1..n
             ==> r k pow n + vsum(0..n-1) (\i. Cx(c i) * r k pow i) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_DATA_ROOT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
                MATCH_MP LE_1_SUC_EXISTS) THEN
  ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; SUC_SUB1; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[COMPLEX_ADD_SYM]);;

let NF_DATA_DEGREE = prove
 (`!n c r k b. nf_data n c r /\ k IN 1..n /\ (!i. integer(b i)) /\
               vsum(0..n-1) (\i. Cx(b i) * r k pow i) = Cx(&0)
               ==> !i. i < n ==> b i = &0`,
  REWRITE_TAC[nf_data] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `n - 1`; `b:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let NF_DATA_ALGEBRAIC_INTEGER = prove
 (`!n c r k. nf_data n c r /\ k IN 1..n ==> algebraic_integer(r k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`] THEN
  ASM_MESON_TAC[NF_DATA; NF_DATA_ROOT]);;

let NF_ORDER_ALGEBRAIC_INTEGER = prove
 (`!n c r a k. nf_data n c r /\ nf_order n r a /\ k IN 1..n
               ==> algebraic_integer(a k)`,
  REWRITE_TAC[nf_order] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC ALGEBRAIC_INTEGER_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_INTEGER_INTEGER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ALGEBRAIC_INTEGER_POW THEN
    ASM_MESON_TAC[NF_DATA_ALGEBRAIC_INTEGER]]);;

(* ------------------------------------------------------------------------- *)
(* Representatives of degree < n (reduction with the monic relation).        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_HORNER_PRED = prove
 (`!(c:num->complex) n z.
        1 <= n
        ==> vsum(0..n) (\i. c i * z pow i) =
            c 0 + z * vsum(0..n-1) (\i. c(SUC i) * z pow i)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
                MATCH_MP LE_1_SUC_EXISTS) THEN
  REWRITE_TAC[COMPLEX_POLYFUN_HORNER; SUC_SUB1]);;

let NF_MUL_X_REDUCE = prove
 (`!(p:num->real) (c:num->real) m x.
        x * vsum(0..m) (\i. Cx(p i) * x pow i) =
        vsum(0..m) (\i. Cx((if i = 0 then &0 else p(i - 1)) - p m * c i) *
                        x pow i) +
        Cx(p m) * (x pow SUC m + vsum(0..m) (\i. Cx(c i) * x pow i))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM COMPLEX_SUB_RZERO] THEN
  REWRITE_TAC[COMPLEX_POLYFUN_MUL_LINEAR] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_SUB_RZERO; VSUM_CLAUSES_NUMSEG;
              LE_0; NOT_SUC; SUC_SUB1] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `(w1:complex) = w2 + w3 * w4 ==> w1 + w3 * w5 = w2 + w3 * (w5 + w4)`) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; GSYM VSUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[CX_SUB; CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let NF_REDUCED_MUL_ROOT = prove
 (`!n c r p. nf_data n c r /\ (!i. integer(p i))
             ==> ?q. (!i. integer(q i)) /\
                     !k. k IN 1..n
                         ==> r k * vsum(0..n-1) (\i. Cx(p i) * r k pow i) =
                             vsum(0..n-1) (\i. Cx(q i) * r k pow i)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  EXISTS_TAC `\i. (if i = 0 then &0 else (p:num->real)(i - 1)) -
                  p(n - 1) * (c:num->real) i` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC INTEGER_SUB THEN
    CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
      MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_DATA_MONIC) THEN
  MP_TAC(SPECL [`p:num->real`; `c:num->real`; `n - 1`;
                `(r:num->complex) k`] NF_MUL_X_REDUCE) THEN
  SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]);;

let NF_REDUCE_POLY = prove
 (`!n c r. nf_data n c r
           ==> !d p. (!i. integer(p i))
                     ==> ?q. (!i. integer(q i)) /\
                             !k. k IN 1..n
                                 ==> vsum(0..d) (\i. Cx(p i) * r k pow i) =
                                     vsum(0..n-1) (\i. Cx(q i) * r k pow i)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN X_GEN_TAC `p:num->real` THEN DISCH_TAC THENL
   [EXISTS_TAC `\i. if i = 0 then (p:num->real) 0 else &0` THEN
    REWRITE_TAC[COMPLEX_POLYFUN_CONST; VSUM_SING_NUMSEG; complex_pow;
                COMPLEX_MUL_RID] THEN
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i. (p:num->real)(SUC i)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `q1:num->real`]
    NF_REDUCED_MUL_ROOT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `\i. (q2:num->real) i + (if i = 0 then (p:num->real) 0 else &0)` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC INTEGER_ADD THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POLYFUN_HORNER; CX_ADD; COMPLEX_ADD_RDISTRIB;
              VSUM_ADD_NUMSEG; COMPLEX_POLYFUN_CONST] THEN
  ASM_SIMP_TAC[] THEN CONV_TAC COMPLEX_RING);;

let NF_ORDER_REDUCE = prove
 (`!n c r a. nf_data n c r /\ nf_order n r a
             ==> ?p. (!i. integer(p i)) /\
                     !k. k IN 1..n
                         ==> a k = vsum(0..n-1) (\i. Cx(p i) * r k pow i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_order] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`d:num`; `p:num->real`] o
              MATCH_MP NF_REDUCE_POLY) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_SIMP_TAC[]);;

let NF_ORDER_REDUCE_UNIQUE = prove
 (`!n c r p q k.
        nf_data n c r /\ (!i. integer(p i)) /\ (!i. integer(q i)) /\
        k IN 1..n /\
        vsum(0..n-1) (\i. Cx(p i) * r k pow i) =
        vsum(0..n-1) (\i. Cx(q i) * r k pow i)
        ==> !i. i < n ==> p i = q i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                `\i. (p:num->real) i - q i`] NF_DATA_DEGREE) THEN
  ASM_SIMP_TAC[INTEGER_SUB; REAL_SUB_0; CX_SUB; COMPLEX_SUB_RDISTRIB;
               VSUM_SUB_NUMSEG; COMPLEX_SUB_REFL]);;

let NF_ORDER_ZERO = prove
 (`!n c r a k l. nf_data n c r /\ nf_order n r a /\ k IN 1..n /\ l IN 1..n /\
                 a k = Cx(&0)
                 ==> a l = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
    NF_ORDER_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`;
                `p:num->real`] NF_DATA_DEGREE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG; COMPLEX_VEC_0] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:num->real) i = &0` SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[COMPLEX_MUL_LZERO]]);;

(* ------------------------------------------------------------------------- *)
(* The roots are pairwise distinct: a double root would be a root of the     *)
(* derivative, an integer polynomial of degree n - 1 with top coefficient n. *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_POLYFUN = prove
 (`!n (c:num->complex) z.
        ((\z. vsum(0..n) (\i. c i * z pow i)) has_complex_derivative
         vsum(0..n) (\i. c i * Cx(&i) * z pow (i - 1))) (at z)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING);;

let NF_DERIV_REINDEX = prove
 (`!(c:num->real) m w.
        vsum(0..SUC m) (\i. Cx(c i) * Cx(&i) * w pow (i - 1)) =
        vsum(0..m) (\i. Cx(&(i + 1) * c(i + 1)) * w pow i)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV
   [MATCH_MP VSUM_CLAUSES_LEFT (SPEC `SUC m` LE_0)] THEN
  REWRITE_TAC[ADD1; VSUM_OFFSET; ADD_SUB; COMPLEX_MUL_LZERO;
              COMPLEX_MUL_RZERO; COMPLEX_ADD_LID] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let CPRODUCT_DOUBLE_ROOT_DERIVATIVE = prove
 (`!n (r:num->complex) k l.
        k IN 1..n /\ l IN 1..n /\ ~(k = l) /\ r k = r l
        ==> ((\z. cproduct(1..n) (\j. z - r j)) has_complex_derivative Cx(&0))
            (at (r k))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1..n`; `\j:num z:complex. z - (r:num->complex) j`;
                 `\j:num. Cx(&1)`; `(r:num->complex) k`]
    HAS_COMPLEX_DERIVATIVE_CPRODUCT) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN COMPLEX_DIFF_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..n) (\i. Cx(&1) * cproduct((1..n) DELETE i)
                                     (\j. (r:num->complex) k - r j)) =
    Cx(&0)`
  SUBST1_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LID] THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_DELETE; FINITE_NUMSEG; IN_DELETE] THEN
  ASM_CASES_TAC `i:num = k` THENL
   [EXISTS_TAC `l:num`; EXISTS_TAC `k:num`] THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL] THEN ASM_MESON_TAC[]);;

let NF_DATA_ROOTS_DISTINCT = prove
 (`!n c r k l. nf_data n c r /\ k IN 1..n /\ l IN 1..n /\ r k = r l ==> k = l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `r:num->complex`; `k:num`; `l:num`]
    CPRODUCT_DOUBLE_ROOT_DERIVATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_THEN `(r:num->complex) k = r l` (K ALL_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(REWRITE_RULE
   [MATCH_MP NF_DATA_FACTOR th]
   (ISPECL [`n:num`; `\i. Cx((c:num->real) i)`; `(r:num->complex) k`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN))) THEN
  SUBGOAL_THEN
   `vsum(0..n) (\i. Cx((c:num->real) i) * Cx(&i) *
                    (r:num->complex) k pow (i - 1)) = Cx(&0)`
  MP_TAC THENL
   [MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
    EXISTS_TAC `\z. cproduct(1..n) (\j. z - (r:num->complex) j)` THEN
    EXISTS_TAC `(r:num->complex) k` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
                MATCH_MP LE_1_SUC_EXISTS) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NF_DERIV_REINDEX]) THEN
  MP_TAC(SPECL [`SUC m`; `c:num->real`; `r:num->complex`; `k:num`;
                `\i. &(i + 1) * (c:num->real)(i + 1)`] NF_DATA_DEGREE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUC_SUB1; INTEGER_MUL; INTEGER_CLOSED]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
  ASM_REWRITE_TAC[LT_SUC_LE; LE_REFL; GSYM ADD1; REAL_MUL_RID;
                  REAL_OF_NUM_EQ; NOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Complex conjugation permutes the conjugates.                              *)
(* ------------------------------------------------------------------------- *)

let CNJ_REAL_POLYFUN = prove
 (`!(c:num->real) d z.
        cnj(vsum(0..d) (\i. Cx(c i) * z pow i)) =
        vsum(0..d) (\i. Cx(c i) * cnj z pow i)`,
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG; CNJ_MUL; CNJ_CX; CNJ_POW]);;

let NF_DATA_CNJ_ROOT = prove
 (`!n c r k. nf_data n c r /\ k IN 1..n
             ==> ?j. j IN 1..n /\ r j = cnj(r k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:num->real`; `n:num`; `(r:num->complex) k`]
    CNJ_REAL_POLYFUN) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `k:num`]
    NF_DATA_ROOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_FACTOR th]) THEN
  REWRITE_TAC[CNJ_CX] THEN DISCH_THEN(MP_TAC o SYM) THEN
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; COMPLEX_SUB_0] THEN
  MESON_TAC[]);;

let NF_CONJ_INVOLUTION = prove
 (`!n c r. nf_data n c r
           ==> ?cj. cj permutes 1..n /\
                     !k. k IN 1..n ==> cj(cj k) = k /\ r(cj k) = cnj(r k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. ?j. k IN 1..n ==> j IN 1..n /\ (r:num->complex) j = cnj(r k)`
  MP_TAC THENL [ASM_MESON_TAC[NF_DATA_CNJ_ROOT]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:num->num`) THEN
  SUBGOAL_THEN `!k. k IN 1..n ==> (t:num->num)(t k) = k` ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC NF_DATA_ROOTS_DISTINCT THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    ASM_MESON_TAC[CNJ_CNJ];
    ALL_TAC] THEN
  EXISTS_TAC `\k. if k IN 1..n then (t:num->num) k else k` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PERMUTES_INVOLUTION THEN SIMP_TAC[] THEN
    X_GEN_TAC `k:num` THEN ASM_CASES_TAC `k IN 1..n` THEN ASM_SIMP_TAC[];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN ASM_SIMP_TAC[]]);;

let NF_ORDER_CNJ = prove
 (`!n r a cj k.
        nf_order n r a /\
        (!k. k IN 1..n ==> cj k IN 1..n /\ r(cj k) = cnj(r k)) /\
        k IN 1..n
        ==> a(cj k) = cnj(a k)`,
  REWRITE_TAC[nf_order] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CNJ_REAL_POLYFUN]);;

(* ------------------------------------------------------------------------- *)
(* Power sums and traces are integers; characteristic polynomial and norm.   *)
(* ------------------------------------------------------------------------- *)

let NF_POWER_SUMS = prove
 (`!n c r m. nf_data n c r
             ==> ?t. integer t /\ vsum(1..n) (\k. r k pow m) = Cx t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1..n`; `r:num->complex`; `\i. Cx((c:num->real) i)`]
    NEWTON_INTEGER_POWER_SUMS) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(fun th ->
        REWRITE_TAC[GSYM(MATCH_MP NF_DATA_FACTOR th)]);
      REWRITE_TAC[complex_integer; RE_CX; IM_CX] THEN
      ASM_MESON_TAC[NF_DATA]];
    DISCH_THEN(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[COMPLEX_INTEGER]]);;

let NF_ORDER_TRACE = prove
 (`!n c r a. nf_data n c r /\ nf_order n r a
             ==> ?t. integer t /\ vsum(1..n) a = Cx t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_order] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!i. ?t. integer t /\ vsum(1..n) (\k. (r:num->complex) k pow i) = Cx t`
  MP_TAC THENL
   [ASM_MESON_TAC[NF_POWER_SUMS]; REWRITE_TAC[SKOLEM_THM]] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:num->real`) THEN
  EXISTS_TAC `sum(0..d) (\i. (p:num->real) i * t i)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGER_SUM THEN ASM_SIMP_TAC[INTEGER_MUL]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `vsum(1..n) (\k. vsum(0..d) (\i. Cx((p:num->real) i) *
                                    (r:num->complex) k pow i))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\k i. Cx((p:num->real) i) * (r:num->complex) k pow i`;
                 `1..n`; `0..d`] VSUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  ASM_REWRITE_TAC[GSYM CX_MUL; VSUM_CX]);;

let CPRODUCT_ZERO_SUB_NUMSEG = prove
 (`!(a:num->complex) n.
        cproduct(1..n) (\k. Cx(&0) - a k) =
        (--Cx(&1)) pow n * cproduct(1..n) a`,
  REPEAT GEN_TAC THEN
  TRANS_TAC EQ_TRANS `cproduct(1..n) (\k. --Cx(&1) * (a:num->complex) k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC COMPLEX_RING;
    SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG; CPRODUCT_CONST_NUMSEG; ADD_SUB;
             ETA_AX]]);;

let NF_CHARPOLY_NORM = prove
 (`!n c r a. nf_data n c r /\ nf_order n r a
             ==> ?e. (!j. integer(e j)) /\ e n = &1 /\
                     (!x. cproduct(1..n) (\k. x - a k) =
                          vsum(0..n) (\j. Cx(e j) * x pow j)) /\
                     cproduct(1..n) a = Cx((-- &1) pow n * e 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->complex`; `1..n`] MONIC_CPRODUCT_INTEGER_COEFFS) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[NF_ORDER_ALGEBRAIC_INTEGER];
      X_GEN_TAC `m:num` THEN STRIP_TAC THEN
      MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                    `\k. (a:num->complex) k pow m`] NF_ORDER_TRACE) THEN
      ASM_SIMP_TAC[NF_ORDER_POW] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_INTEGER] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:num->real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
    REWRITE_TAC[CPRODUCT_ZERO_SUB_NUMSEG; COMPLEX_POLYFUN_AT_0] THEN
    REWRITE_TAC[CX_MUL; CX_POW; CX_NEG] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_MUL] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG;
                COMPLEX_MUL_LID; COMPLEX_POW_ONE]]);;

let NF_NORM_INTEGER = prove
 (`!n c r a. nf_data n c r /\ nf_order n r a
             ==> ?m. integer m /\ cproduct(1..n) a = Cx m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->real` STRIP_ASSUME_TAC o
             MATCH_MP NF_CHARPOLY_NORM) THEN
  EXISTS_TAC `(-- &1) pow n * (e:num->real) 0` THEN
  ASM_SIMP_TAC[INTEGER_MUL; INTEGER_POW; INTEGER_NEG; INTEGER_CLOSED]);;

let NF_NORM_EQ_0 = prove
 (`!n c r a.
        nf_data n c r /\ nf_order n r a
        ==> (cproduct(1..n) a = Cx(&0) <=> !k. k IN 1..n ==> a k = Cx(&0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  EQ_TAC THENL [ASM_MESON_TAC[NF_ORDER_ZERO]; ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Adjugate element and units.                                               *)
(* ------------------------------------------------------------------------- *)

let NF_ADJUGATE = prove
 (`!n c r a. nf_data n c r /\ nf_order n r a
             ==> ?b. nf_order n r b /\
                     !k. k IN 1..n ==> a k * b k = cproduct(1..n) a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
    NF_CHARPOLY_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  EXISTS_TAC
   `\k. Cx(--((-- &1) pow n)) *
        vsum(0..n-1) (\j. Cx((e:num->real)(SUC j)) *
                          (a:num->complex) k pow j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_CX THEN
      SIMP_TAC[INTEGER_NEG; INTEGER_POW; INTEGER_CLOSED];
      MP_TAC(ISPECL [`n:num`; `r:num->complex`;
                     `\j:num k:num. Cx((e:num->real)(SUC j)) *
                                    (a:num->complex) k pow j`;
                     `0..n-1`] NF_ORDER_VSUM) THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC NF_ORDER_MUL THEN ASM_SIMP_TAC[NF_ORDER_CX; NF_ORDER_POW]];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(a:num->complex) k`) THEN
  SUBGOAL_THEN `cproduct(1..n) (\i. (a:num->complex) k - a i) = Cx(&0)`
  SUBST1_TAC THENL
   [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_REFL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPLEX_POLYFUN_HORNER_PRED] THEN
  REWRITE_TAC[CX_MUL; CX_NEG] THEN CONV_TAC COMPLEX_RING);;

let NF_UNIT_NORM = prove
 (`!n c r a. nf_data n c r
             ==> (nf_unit n r a <=>
                  nf_order n r a /\
                  (cproduct(1..n) a = Cx(&1) \/ cproduct(1..n) a = --Cx(&1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nf_unit] THEN
  ASM_CASES_TAC `nf_order n r (a:num->complex)` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
      NF_NORM_INTEGER) THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `b:num->complex`]
      NF_NORM_INTEGER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `cproduct(1..n) (\k. (a:num->complex) k * b k) = Cx(&1)`
    MP_TAC THENL
     [MATCH_MP_TAC CPRODUCT_EQ_1 THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    SIMP_TAC[CPRODUCT_MUL; FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[GSYM CX_MUL; CX_INJ; GSYM CX_NEG] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`x:real`; `y:real`] INTEGER_ABS_MUL_EQ_1) THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
      NF_ADJUGATE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [EXISTS_TAC `b:num->complex` THEN ASM_SIMP_TAC[];
      EXISTS_TAC `\k. --((b:num->complex) k)` THEN
      ASM_SIMP_TAC[NF_ORDER_NEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG]]]);;

(* ------------------------------------------------------------------------- *)
(* Elimination: a complex root of a rational cubic without rational roots    *)
(* satisfies no non-trivial rational relation of degree <= 2, so a root of   *)
(* an integer cubic without rational roots has degree 3 (used for the cube   *)
(* root of 2 below, THUE_CUBIC_2 and MORDELL_THUE_CUBIC).                    *)
(* ------------------------------------------------------------------------- *)

let NF_CUBIC_LINEAR = prove
 (`!a b c d t e0 e1.
        (!q. rational q ==> ~(a * q pow 3 + b * q pow 2 + c * q + d = &0)) /\
        Cx a * t pow 3 + Cx b * t pow 2 + Cx c * t + Cx d = Cx(&0) /\
        rational e0 /\ rational e1 /\ ~(e1 = &0) /\
        Cx e1 * t + Cx e0 = Cx(&0)
        ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `--(e0:real) / e1`)
    STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[RATIONAL_DIV; RATIONAL_NEG] THEN
  REWRITE_TAC[GSYM CX_INJ; CX_ADD; CX_MUL; CX_POW; CX_DIV; CX_NEG] THEN
  MAP_EVERY UNDISCH_TAC
   [`Cx a * t pow 3 + Cx b * t pow 2 + Cx c * t + Cx d = Cx(&0)`;
    `Cx e1 * t + Cx e0 = Cx(&0)`; `~(e1:real = &0)`] THEN
  REWRITE_TAC[GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD);;

let NF_CUBIC_DIVISION = prove
 (`!a b c d e0 e1 e2 z:real.
        e2 pow 2 * (a * z pow 3 + b * z pow 2 + c * z + d) =
        (e2 * a * z + (e2 * b - a * e1)) * (e2 * z pow 2 + e1 * z + e0) +
        (e2 pow 2 * c - e2 * a * e0 - e2 * b * e1 + a * e1 pow 2) * z +
        (e2 pow 2 * d - e2 * b * e0 + a * e1 * e0)`,
  REPEAT GEN_TAC THEN CONV_TAC REAL_RING);;

let NF_CUBIC_DEGREE = prove
 (`!a b c d t e0 e1 e2.
        integer a /\ integer b /\ integer c /\ integer d /\ ~(a = &0) /\
        (!q. rational q ==> ~(a * q pow 3 + b * q pow 2 + c * q + d = &0)) /\
        Cx a * t pow 3 + Cx b * t pow 2 + Cx c * t + Cx d = Cx(&0) /\
        integer e0 /\ integer e1 /\ integer e2 /\
        Cx e0 + Cx e1 * t + Cx e2 * t pow 2 = Cx(&0)
        ==> e0 = &0 /\ e1 = &0 /\ e2 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `e2:real = &0` ASSUME_TAC THENL
   [ASM_CASES_TAC `e2:real = &0` THEN ASM_REWRITE_TAC[] THEN
    ABBREV_TAC
     `r1 = (e2:real) pow 2 * c - e2 * a * e0 - e2 * b * e1 + a * e1 pow 2` THEN
    ABBREV_TAC `r0 = (e2:real) pow 2 * d - e2 * b * e0 + a * e1 * e0` THEN
    SUBGOAL_THEN `Cx r1 * t + Cx r0 = Cx(&0)` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["r1"; "r0"] THEN
      REWRITE_TAC[CX_SUB; CX_ADD; CX_MUL; CX_POW] THEN
      MAP_EVERY UNDISCH_TAC
       [`Cx a * t pow 3 + Cx b * t pow 2 + Cx c * t + Cx d = Cx(&0)`;
        `Cx e0 + Cx e1 * t + Cx e2 * t pow 2 = Cx(&0)`] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN `integer r1 /\ integer r0` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["r1"; "r0"] THEN
      REPEAT(MATCH_MP_TAC INTEGER_ADD ORELSE MATCH_MP_TAC INTEGER_SUB ORELSE
             MATCH_MP_TAC INTEGER_MUL ORELSE MATCH_MP_TAC INTEGER_POW ORELSE
             CONJ_TAC) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `r1:real = &0` THENL
     [ALL_TAC;
      MATCH_MP_TAC NF_CUBIC_LINEAR THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `c:real`; `d:real`;
                            `t:complex`; `r0:real`; `r1:real`] THEN
      ASM_SIMP_TAC[RATIONAL_INTEGER]] THEN
    SUBGOAL_THEN `r0:real = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `Cx r1 * t + Cx r0 = Cx(&0)` THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_LID; CX_INJ];
      ALL_TAC] THEN
    ABBREV_TAC `z0 = --((e2:real) * b - a * e1) / (e2 * a)` THEN
    SUBGOAL_THEN `(e2:real) * a * z0 + (e2 * b - a * e1) = &0` ASSUME_TAC THENL
     [EXPAND_TAC "z0" THEN UNDISCH_TAC `~(a:real = &0)` THEN
      UNDISCH_TAC `~(e2:real = &0)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z0:real`) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "z0" THEN MATCH_MP_TAC RATIONAL_DIV THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC RATIONAL_NEG) THEN MATCH_MP_TAC RATIONAL_INTEGER THEN
      ASM_SIMP_TAC[INTEGER_CLOSED];
      ALL_TAC] THEN
    MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`; `e0:real`;
                  `e1:real`; `e2:real`; `z0:real`] NF_CUBIC_DIVISION) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID; REAL_ENTIRE;
                    REAL_POW_EQ_0] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1:real = &0` ASSUME_TAC THENL
   [ASM_CASES_TAC `e1:real = &0` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NF_CUBIC_LINEAR THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `c:real`; `d:real`;
                          `t:complex`; `e0:real`; `e1:real`] THEN
    ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
    UNDISCH_TAC `Cx e0 + Cx e1 * t + Cx e2 * t pow 2 = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  UNDISCH_TAC `Cx e0 + Cx e1 * t + Cx e2 * t pow 2 = Cx(&0)` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; CX_INJ]);;

let NF_CUBIC_ROOT_DEGREE = prove
 (`!a b c d t n e.
        integer a /\ integer b /\ integer c /\ integer d /\ ~(a = &0) /\
        (!q. rational q ==> ~(a * q pow 3 + b * q pow 2 + c * q + d = &0)) /\
        Cx a * t pow 3 + Cx b * t pow 2 + Cx c * t + Cx d = Cx(&0) /\
        n < 3 /\ (!i. integer(e i)) /\
        vsum(0..n) (\i. Cx(e i) * t pow i) = Cx(&0)
        ==> !i. i <= n ==> e i = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ee = \i. if i <= n then (e:num->real) i else &0` THEN
  SUBGOAL_THEN `vsum(0..2) (\i. Cx((ee:num->real) i) * t pow i) = Cx(&0)`
  MP_TAC THENL
   [EXPAND_TAC "ee" THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
    ASM_SIMP_TAC[VSUM_NUMSEG_RESTRICT_LE; ARITH_RULE `n < 3 ==> n <= 2`];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV(LAND_CONV EXPAND_VSUM_CONV)) THEN
  REWRITE_TAC[complex_pow; COMPLEX_POW_1; COMPLEX_MUL_RID] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`; `t:complex`;
                `(ee:num->real) 0`; `(ee:num->real) 1`; `(ee:num->real) 2`]
    NF_CUBIC_DEGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "ee" THEN REPEAT CONJ_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:num->real) i = ee i` SUBST1_TAC THENL
   [EXPAND_TAC "ee" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i = 0 \/ i = 1 \/ i = 2` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Sanity example: the three complex cube roots of 2 (f = x^3 - 2) are       *)
(* number field data of degree 3, and 1 + theta + theta^2 is a unit of the   *)
(* order Z[theta] (inverse theta - 1).                                       *)
(* ------------------------------------------------------------------------- *)

let NO_RATIONAL_CUBE_ROOT_2 = prove
 (`!q. rational q ==> ~(q pow 3 = &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `integer q` ASSUME_TAC THENL
   [MATCH_MP_TAC ALGEBRAIC_INTEGER_RATIONAL THEN
    ASM_REWRITE_TAC[ALGEBRAIC_INTEGER_MONIC] THEN
    MAP_EVERY EXISTS_TAC [`3`; `\i. if i = 0 then -- &2 else &0`] THEN
    REWRITE_TAC[COMPLEX_POLYFUN_CONST; ARITH] THEN CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED];
      ASM_REWRITE_TAC[GSYM CX_POW; GSYM CX_ADD; CX_INJ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(q:real) <= &1` THENL
   [MP_TAC(SPECL [`3`; `q:real`; `&1`] REAL_POW_LE2_ODD) THEN
    ASM_REWRITE_TAC[ARITH; REAL_POW_ONE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= (q:real)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1`; `q:real`] REAL_LT_INTEGERS) THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPECL [`3`; `&2`; `q:real`] REAL_POW_LE2) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let NF_CUBE2_DEGREE = prove
 (`!z m b. z pow 3 = Cx(&2) /\ m < 3 /\ (!i. integer(b i)) /\
           vsum(0..m) (\i. Cx(b i) * z pow i) = Cx(&0)
           ==> !i. i <= m ==> b i = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&1:real`; `&0:real`; `&0:real`; `-- &2:real`; `z:complex`;
                `m:num`; `b:num->real`] NF_CUBIC_ROOT_DEGREE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `q:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `q:real` NO_RATIONAL_CUBE_ROOT_2) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING]);;

let NF_CUBE2_POLY = prove
 (`!z. vsum(0..3) (\i. Cx(if i = 0 then -- &2 else if i = 3 then &1 else &0) *
                       z pow i) =
       z pow 3 - Cx(&2)`,
  GEN_TAC THEN CONV_TAC(LAND_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[ARITH; complex_pow; COMPLEX_POW_1; CX_NEG] THEN
  CONV_TAC COMPLEX_RING);;

let NF_EXAMPLE_CUBE_ROOT_2 = prove
 (`?r. nf_data 3 (\i. if i = 0 then -- &2 else if i = 3 then &1 else &0) r`,
  MP_TAC(ISPECL
   [`3`; `\i. Cx(if i = 0 then -- &2 else if i = 3 then &1 else &0)`]
   COMPLEX_POLYFUN_FACTOR) THEN
  REWRITE_TAC[ARITH; COMPLEX_MUL_LID] THEN ANTS_TAC THENL
   [REWRITE_TAC[CX_INJ] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->complex` THEN
  DISCH_TAC THEN REWRITE_TAC[nf_data; ARITH] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[INTEGER_NEG; INTEGER_CLOSED];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC NF_CUBE2_DEGREE THEN
  EXISTS_TAC `(r:num->complex) k` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(r:num->complex) k`) THEN
  REWRITE_TAC[NF_CUBE2_POLY] THEN
  SUBGOAL_THEN `cproduct(1..3) (\i. (r:num->complex) k - r i) = Cx(&0)`
  SUBST1_TAC THENL
   [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN EXISTS_TAC `k:num` THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_REFL];
    CONV_TAC COMPLEX_RING]);;

let NF_EXAMPLE_CUBE_ROOT_2_UNIT = prove
 (`!r. nf_data 3 (\i. if i = 0 then -- &2 else if i = 3 then &1 else &0) r
       ==> nf_unit 3 r (\k. Cx(&1) + r k + r k pow 2)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[nf_unit] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC NF_ORDER_CX THEN REWRITE_TAC[INTEGER_CLOSED];
      MATCH_MP_TAC NF_ORDER_ADD THEN REWRITE_TAC[ETA_AX; NF_ORDER_ROOT] THEN
      MATCH_MP_TAC NF_ORDER_POW THEN REWRITE_TAC[NF_ORDER_ROOT]];
    ALL_TAC] THEN
  EXISTS_TAC `\k. (r:num->complex) k - Cx(&1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NF_ORDER_SUB THEN REWRITE_TAC[ETA_AX; NF_ORDER_ROOT] THEN
    MATCH_MP_TAC NF_ORDER_CX THEN REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `\i. if i = 0 then -- &2 else if i = 3 then &1 else &0`;
                 `r:num->complex`; `k:num`] NF_DATA_ROOT) THEN
  ASM_REWRITE_TAC[NF_CUBE2_POLY] THEN CONV_TAC COMPLEX_RING);;
