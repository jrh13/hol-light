(* ========================================================================= *)
(* Algebraic integers.                                                       *)
(*                                                                           *)
(* Purpose: algebraic_integer z (z is a root of a monic integer polynomial), *)
(* that is the integral elements of C over Z (INTEGRAL_ELEMENT_COMPLEX_RING, *)
(* integral_element of ANT/integral.ml); they form a subring of C            *)
(* (ALGEBRAIC_INTEGER_SUBRING: the integral closure of ANT/integral.ml),     *)
(* hence the closure under + - * pow vsum cproduct; integers, ii, conjugates *)
(* and roots of unity are algebraic integers, and algebraic integers are     *)
(* algebraic numbers; integer polynomial functions (int_polyfun); rational   *)
(* algebraic integers are integers (Z is integrally closed, and the prime    *)
(* subfield of C is {Cx q | rational q} by COMPLEX_PRIME_SUBFIELD of         *)
(* ANT/complex_embeddings.ml); z is an algebraic integer if some power z^k   *)
(* (k >= 1) is; integrality of the coefficients of monic polynomials with    *)
(* algebraic integer roots.                                                  *)
(*                                                                           *)
(* Main results: INTEGRAL_ELEMENT_COMPLEX_RING, ALGEBRAIC_INTEGER_CLOSED     *)
(* (closure under the ring operations), ALGEBRAIC_INTEGER_RATIONAL,          *)
(* MONIC_CPRODUCT_INTEGER_COEFFS (integer coefficients from integer power    *)
(* sums), ALGEBRAIC_INTEGER_POW_ROOT (z^k algebraic integer implies z).      *)
(*                                                                           *)
(* Uses: ANT/integral.ml (integral_element, INTEGRAL_ELEMENT_EXPLICIT,       *)
(* INTEGRAL_CLOSURE_SUBRING, INTEGRAL_ELEMENT_PRIME_SUBFIELD),               *)
(* ANT/numfield.ml (RING_OF_INTEGERS_CARRIER,                                *)
(* ROOT_OF_UNITY_IN_RING_OF_INTEGERS), ANT/complex_embeddings.ml             *)
(* (COMPLEX_PRIME_SUBFIELD), Multivariate/complex_ring.ml (complex_ring,     *)
(* FIELD_COMPLEX_RING, RING_CHAR_COMPLEX_RING, COMPLEX_RING_OF_INT,          *)
(* COMPLEX_RING_SUM), Library/ringtheory.ml (IN_SUBRING_INT),                *)
(* Baker/algebraic.ml (COMPLEX_POLYFUN_MUL_LINEAR,                           *)
(* NEWTON_INTEGER_COEFFICIENTS), Baker/bridge.ml                             *)
(* (EXPLICIT_IMP_ALGEBRAIC_NUMBER), Baker/lemmas.ml (COMPLEX_SUBRING_CLOSED, *)
(* COMPLEX_SUBRING_VSUM, COMPLEX_SUBRING_CPRODUCT).                          *)
(* ========================================================================= *)

needs "ANT/numfield.ml";;
needs "ANT/complex_embeddings.ml";;
needs "Baker/algebraic.ml";;
needs "Baker/bridge.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Definition: root of a monic polynomial with integer coefficients.         *)
(* ------------------------------------------------------------------------- *)

let algebraic_integer = new_definition
 `algebraic_integer (z:complex) <=>
        ?n c. 1 <= n /\ (!i. integer(c i)) /\ c n = &1 /\
              vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)`;;

let LE_1_SUC_EXISTS = prove
 (`!n. 1 <= n ==> ?m. n = SUC m`,
  GEN_TAC THEN STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
  REWRITE_TAC[ARITH; SUC_INJ] THEN MESON_TAC[]);;

let ALGEBRAIC_INTEGER_EXPLICIT = prove
 (`!z. algebraic_integer z <=>
       ?n c. (!i. integer(c i)) /\ c n = &1 /\
             vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)`,
  GEN_TAC THEN REWRITE_TAC[algebraic_integer] THEN EQ_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[LE_1] THEN
  UNDISCH_TAC `vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0)` THEN
  ASM_REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID] THEN
  ASM_MESON_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_RULE `~(1 = 0)`]);;

let ALGEBRAIC_INTEGER_MONIC = prove
 (`!z. algebraic_integer z <=>
       ?n c. 1 <= n /\ (!i. integer(c i)) /\
             z pow n + vsum(0..n-1) (\i. Cx(c i) * z pow i) = Cx(&0)`,
  GEN_TAC THEN REWRITE_TAC[algebraic_integer] THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
              MATCH_MP LE_1_SUC_EXISTS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[SUC_SUB1]) THEN REWRITE_TAC[SUC_SUB1] THENL
   [EXISTS_TAC `SUC m` THEN EXISTS_TAC `c:num->real` THEN
    UNDISCH_TAC `vsum(0..SUC m) (\i. Cx(c i) * z pow i) = Cx(&0)` THEN
    ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; SUC_SUB1;
                    COMPLEX_MUL_LID] THEN
    CONV_TAC COMPLEX_RING;
    EXISTS_TAC `SUC m` THEN
    EXISTS_TAC `\i. if i = SUC m then &1 else (c:num->real) i` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
      UNDISCH_TAC `z pow SUC m + vsum(0..m) (\i. Cx(c i) * z pow i) =
                   Cx(&0)` THEN
      REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; COMPLEX_MUL_LID] THEN
      MATCH_MP_TAC(COMPLEX_RING
       `a = b ==> p + b = Cx(&0) ==> a + p = Cx(&0)`) THEN
      MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
      SIMP_TAC[ARITH_RULE `i <= m ==> ~(i = SUC m)`]]]);;

let ALGEBRAIC_INTEGER_CNJ = prove
 (`!z. algebraic_integer z ==> algebraic_integer(cnj z)`,
  GEN_TAC THEN REWRITE_TAC[algebraic_integer] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `cnj`) THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG; CNJ_MUL; CNJ_CX; CNJ_POW]);;

let ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER = prove
 (`!z. algebraic_integer z ==> algebraic_number z`,
  REWRITE_TAC[algebraic_integer] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXPLICIT_IMP_ALGEBRAIC_NUMBER THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer polynomial functions of degree <= n (used by the orders, the      *)
(* descents of sections 11 and 12 and by Baker/prime_factors.ml).            *)
(* ------------------------------------------------------------------------- *)

let int_polyfun = new_definition
 `int_polyfun n (f:complex->complex) <=>
        ?c. (!i. integer(c i)) /\
            !z. f z = vsum(0..n) (\i. Cx(c i) * z pow i)`;;

let VSUM_NUMSEG_RESTRICT_LE = prove
 (`!(f:num->complex) m n.
        m <= n
        ==> vsum(0..n) (\i. if i <= m then f i else Cx(&0)) = vsum(0..m) f`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET; ETA_AX] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC);;

let INT_POLYFUN_MONO = prove
 (`!m n f. int_polyfun m f /\ m <= n ==> int_polyfun n f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_polyfun] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `c:num->real`) ASSUME_TAC) THEN
  EXISTS_TAC `\i. if i <= m then (c:num->real) i else &0` THEN
  CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ASM_SIMP_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO;
                 VSUM_NUMSEG_RESTRICT_LE]]);;

let INT_POLYFUN_CONST = prove
 (`!n a. integer a ==> int_polyfun n (\z. Cx a)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_POLYFUN_MONO THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[LE_0; int_polyfun] THEN
  EXISTS_TAC `\i:num. (a:real)` THEN
  ASM_REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID]);;

let INT_POLYFUN_ADD = prove
 (`!n f g. int_polyfun n f /\ int_polyfun n g
           ==> int_polyfun n (\z. f z + g z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_polyfun] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:num->real`)
                             (X_CHOOSE_TAC `b:num->real`)) THEN
  EXISTS_TAC `\i. (a:num->real) i + b i` THEN
  ASM_SIMP_TAC[INTEGER_ADD; CX_ADD; COMPLEX_ADD_RDISTRIB; VSUM_ADD_NUMSEG]);;

let INT_POLYFUN_CMUL = prove
 (`!n f a. integer a /\ int_polyfun n f ==> int_polyfun n (\z. Cx a * f z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_polyfun] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `c:num->real`)) THEN
  EXISTS_TAC `\i. a * (c:num->real) i` THEN
  ASM_SIMP_TAC[INTEGER_MUL; CX_MUL; GSYM COMPLEX_MUL_ASSOC;
               VSUM_COMPLEX_LMUL; FINITE_NUMSEG]);;

let INT_POLYFUN_MUL_LINEAR_TOP = prove
 (`!n c a. integer a /\ (!i. integer(c i))
           ==> ?d. (!i. integer(d i)) /\ d(SUC n) = c n /\
                   !z. (z - Cx a) * vsum(0..n) (\i. Cx(c i) * z pow i) =
                       vsum(0..SUC n) (\i. Cx(d i) * z pow i)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\k. (if k = 0 then &0 else (c:num->real)(k - 1)) -
                  a * (if k <= n then c k else &0)` THEN
  REWRITE_TAC[NOT_SUC; SUC_SUB1; ARITH_RULE `~(SUC n <= n)`] THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC INTEGER_SUB THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
      MATCH_MP_TAC INTEGER_MUL THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED]];
    REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[COMPLEX_POLYFUN_MUL_LINEAR] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[CX_SUB; CX_MUL] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[])]);;

let INT_POLYFUN_MUL_LINEAR = prove
 (`!n f a. integer a /\ int_polyfun n f
           ==> int_polyfun (SUC n) (\z. (z - Cx a) * f z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_polyfun] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `a:real`]
    INT_POLYFUN_MUL_LINEAR_TOP) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Algebraic integers are the integral elements of C over Z                  *)
(* (ANT/integral.ml, with ring_of_int complex_ring n = Cx(real_of_int n)),   *)
(* hence a subring of C (the integral closure) and the closure under the     *)
(* ring operations, finite sums and products; roots of unity are algebraic   *)
(* integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

let INTEGRAL_ELEMENT_COMPLEX_RING = prove
 (`!z. integral_element (integer_ring,complex_ring)
                        (ring_of_int complex_ring) z
       <=> algebraic_integer z`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`integer_ring`; `complex_ring`; `ring_of_int complex_ring`;
                 `z:complex`] INTEGRAL_ELEMENT_EXPLICIT) THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT; INTEGER_RING] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[COMPLEX_RING_CLAUSES; COMPLEX_RING_POW; IN_UNIV;
           COMPLEX_RING_OF_INT; COMPLEX_RING_SUM;
           FINITE_NUMSEG_LT; ALGEBRAIC_INTEGER_MONIC] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`n:num`; `c:num->int`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{i:num | i < n} = 0..n-1` SUBST_ALL_TAC THENL
     [ASM_SIMP_TAC[NUMSEG_LT; LE_1]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `\i. real_of_int((c:num->int) i)`] THEN
    ASM_SIMP_TAC[INTEGER_REAL_OF_INT; LE_1];
    MAP_EVERY X_GEN_TAC [`n:num`; `c:num->real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `\i. int_of_real((c:num->real) i)`] THEN
    SUBGOAL_THEN `{i:num | i < n} = 0..n-1` SUBST1_TAC THENL
     [ASM_SIMP_TAC[NUMSEG_LT; LE_1]; ALL_TAC] THEN
    SUBGOAL_THEN `!i. real_of_int(int_of_real((c:num->real) i)) = c i`
     (fun th -> ASM_SIMP_TAC[th; LE_1]) THEN
    ASM_MESON_TAC[int_tybij]]);;

let ALGEBRAIC_INTEGER_SUBRING = prove
 (`{z | algebraic_integer z} subring_of complex_ring`,
  REWRITE_TAC[GSYM INTEGRAL_ELEMENT_COMPLEX_RING] THEN
  MATCH_MP_TAC INTEGRAL_CLOSURE_SUBRING THEN
  REWRITE_TAC[RING_HOMOMORPHISM_INTEGER_RING_OF_INT]);;

let ALGEBRAIC_INTEGER_CLOSED = prove
 (`(!n. algebraic_integer(Cx(&n))) /\
   (!x. integer x ==> algebraic_integer(Cx x)) /\
   (!x y. algebraic_integer x /\ algebraic_integer y
          ==> algebraic_integer(x + y)) /\
   (!x y. algebraic_integer x /\ algebraic_integer y
          ==> algebraic_integer(x - y)) /\
   (!x y. algebraic_integer x /\ algebraic_integer y
          ==> algebraic_integer(x * y)) /\
   (!x n. algebraic_integer x ==> algebraic_integer(x pow n)) /\
   (!x. algebraic_integer x ==> algebraic_integer(--x))`,
  MP_TAC(MATCH_MP COMPLEX_SUBRING_CLOSED ALGEBRAIC_INTEGER_SUBRING) THEN
  MP_TAC(MATCH_MP IN_SUBRING_INT ALGEBRAIC_INTEGER_SUBRING) THEN
  REWRITE_TAC[COMPLEX_RING_OF_INT; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&n:int`) THEN REWRITE_TAC[int_of_num_th];
    ASM_MESON_TAC[int_tybij]]);;

let ALGEBRAIC_INTEGER_NUM = prove
 (`!n. algebraic_integer(Cx(&n))`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_INTEGER = prove
 (`!x. integer x ==> algebraic_integer(Cx x)`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_ADD = prove
 (`!x y. algebraic_integer x /\ algebraic_integer y
         ==> algebraic_integer(x + y)`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_SUB = prove
 (`!x y. algebraic_integer x /\ algebraic_integer y
         ==> algebraic_integer(x - y)`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_MUL = prove
 (`!x y. algebraic_integer x /\ algebraic_integer y
         ==> algebraic_integer(x * y)`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_POW = prove
 (`!x n. algebraic_integer x ==> algebraic_integer(x pow n)`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_NEG = prove
 (`!x. algebraic_integer x ==> algebraic_integer(--x)`,
  REWRITE_TAC[ALGEBRAIC_INTEGER_CLOSED]);;

let ALGEBRAIC_INTEGER_COMPLEX_INTEGER = prove
 (`!z. complex_integer z ==> algebraic_integer z`,
  REWRITE_TAC[COMPLEX_INTEGER] THEN MESON_TAC[ALGEBRAIC_INTEGER_INTEGER]);;

let ALGEBRAIC_INTEGER_VSUM = prove
 (`!(f:A->complex) s.
        FINITE s /\ (!x. x IN s ==> algebraic_integer(f x))
        ==> algebraic_integer(vsum s f)`,
  MP_TAC(ISPEC `{z | algebraic_integer z}` COMPLEX_SUBRING_VSUM) THEN
  REWRITE_TAC[ALGEBRAIC_INTEGER_SUBRING; IN_ELIM_THM] THEN MESON_TAC[]);;

let ALGEBRAIC_INTEGER_CPRODUCT = prove
 (`!(f:A->complex) s.
        FINITE s /\ (!x. x IN s ==> algebraic_integer(f x))
        ==> algebraic_integer(cproduct s f)`,
  MP_TAC(ISPEC `{z | algebraic_integer z}` COMPLEX_SUBRING_CPRODUCT) THEN
  REWRITE_TAC[ALGEBRAIC_INTEGER_SUBRING; IN_ELIM_THM] THEN MESON_TAC[]);;

let ALGEBRAIC_INTEGER_ROOT_OF_UNITY = prove
 (`!z k. 1 <= k /\ z pow k = Cx(&1) ==> algebraic_integer z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `z:complex`; `k:num`]
    ROOT_OF_UNITY_IN_RING_OF_INTEGERS) THEN
  ASM_SIMP_TAC[LE_1; RING_OF_INTEGERS_CARRIER; IN_ELIM_THM; IN_UNIV;
               COMPLEX_RING_CLAUSES; COMPLEX_RING_POW;
               INTEGRAL_ELEMENT_COMPLEX_RING]);;

let ALGEBRAIC_INTEGER_II = prove
 (`algebraic_integer ii`,
  MATCH_MP_TAC ALGEBRAIC_INTEGER_ROOT_OF_UNITY THEN EXISTS_TAC `4` THEN
  REWRITE_TAC[ARITH_RULE `1 <= 4 /\ 4 = 2 * 2`; GSYM COMPLEX_POW_POW;
              COMPLEX_POW_II_2] THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Rational algebraic integers are integers (INTEGRAL_ELEMENT_PRIME_SUBFIELD *)
(* of ANT/integral.ml: the integers are integrally closed, with the prime    *)
(* subfield {Cx q | rational q} of complex_ring, COMPLEX_PRIME_SUBFIELD of   *)
(* ANT/complex_embeddings.ml).                                               *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_INTEGER_RATIONAL = prove
 (`!x. rational x /\ algebraic_integer(Cx x) ==> integer x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`complex_ring`; `Cx x`] INTEGRAL_ELEMENT_PRIME_SUBFIELD) THEN
  ASM_REWRITE_TAC[FIELD_COMPLEX_RING; RING_CHAR_COMPLEX_RING;
                  COMPLEX_RING_CLAUSES; COMPLEX_PRIME_SUBFIELD;
                  INTEGRAL_ELEMENT_COMPLEX_RING; COMPLEX_RING_OF_INT;
                  IN_ELIM_THM; CX_INJ] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MESON_TAC[INTEGER_REAL_OF_INT]);;

let ALGEBRAIC_INTEGER_CX_RATIONAL = prove
 (`!x. rational x ==> (algebraic_integer(Cx x) <=> integer x)`,
  MESON_TAC[ALGEBRAIC_INTEGER_RATIONAL; ALGEBRAIC_INTEGER_INTEGER]);;

(* ------------------------------------------------------------------------- *)
(* Monic polynomials with algebraic integer roots: their coefficients are    *)
(* algebraic integers, and integers as soon as the power sums of the roots   *)
(* are integers (the integrality engine for norms and characteristic         *)
(* polynomials in number fields).                                            *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_INTEGER_CPRODUCT_COEFFS = prove
 (`!(a:A->complex) s.
        FINITE s /\ (!i. i IN s ==> algebraic_integer(a i))
        ==> ?c. (!k. algebraic_integer(c k)) /\ c(CARD s) = Cx(&1) /\
                !x. cproduct s (\i. x - a i) =
                    vsum(0..CARD s) (\k. c k * x pow k)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; CARD_CLAUSES; FORALL_IN_INSERT;
           NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `\k:num. Cx(&1)` THEN
    REWRITE_TAC[ALGEBRAIC_INTEGER_NUM; VSUM_SING_NUMSEG; complex_pow;
                COMPLEX_MUL_RID];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\k. (if k = 0 then Cx(&0) else c(k - 1)) -
                  (a:A->complex) x *
                  (if k <= CARD(s:A->bool) then c k else Cx(&0))` THEN
  ASM_REWRITE_TAC[COMPLEX_POLYFUN_MUL_LINEAR; NOT_SUC; SUC_SUB1;
                  ARITH_RULE `~(SUC n <= n)`] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC ALGEBRAIC_INTEGER_SUB THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_REWRITE_TAC[ALGEBRAIC_INTEGER_NUM];
      MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[ALGEBRAIC_INTEGER_NUM]];
    CONV_TAC COMPLEX_RING]);;

let MONIC_CPRODUCT_INTEGER_COEFFS = prove
 (`!(a:A->complex) s.
        FINITE s /\ (!i. i IN s ==> algebraic_integer(a i)) /\
        (!m. 1 <= m /\ m <= CARD s
             ==> complex_integer(vsum s (\i. a i pow m)))
        ==> ?c. (!k. integer(c k)) /\ c(CARD s) = &1 /\
                !x. cproduct s (\i. x - a i) =
                    vsum(0..CARD s) (\k. Cx(c k) * x pow k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:A->complex`; `s:A->bool`]
    ALGEBRAIC_INTEGER_CPRODUCT_COEFFS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->complex`; `e:num->complex`]
    NEWTON_INTEGER_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. k <= CARD(s:A->bool) ==> integer(Re(e k)) /\
                                            Cx(Re(e k)) = e k`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
    ASM_REWRITE_TAC[COMPLEX_INTEGER] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `D = &(FACT(CARD(s:A->bool) - k))` THEN
    SUBGOAL_THEN `~(D = &0)` ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN REWRITE_TAC[REAL_OF_NUM_EQ; FACT_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `algebraic_integer((e:num->complex) k)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:num->complex) k = Cx(q / D)` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `Cx D * (e:num->complex) k = Cx q` THEN
      UNDISCH_TAC `~(D = &0)` THEN
      REWRITE_TAC[CX_DIV; GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[RE_CX] THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_INTEGER_RATIONAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC RATIONAL_DIV THEN ASM_SIMP_TAC[RATIONAL_INTEGER] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[RATIONAL_NUM];
    ALL_TAC] THEN
  EXISTS_TAC `\k. if k <= CARD(s:A->bool) then Re((e:num->complex) k)
                  else &0` THEN
  REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[INTEGER_CLOSED];
    ASM_REWRITE_TAC[RE_CX];
    GEN_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SIMP_TAC[] THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* If some power z^k (k >= 1) is an algebraic integer, so is z: if p is a    *)
(* monic integer polynomial with p(z^k) = 0, then p(X^k) is a monic integer  *)
(* polynomial of degree k deg p vanishing at z.                              *)
(* ------------------------------------------------------------------------- *)

let ALGEBRAIC_INTEGER_POW_ROOT = prove
 (`!z k. 1 <= k /\ algebraic_integer(z pow k) ==> algebraic_integer z`,
  REPEAT GEN_TAC THEN REWRITE_TAC[algebraic_integer] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k * n:num`; `\j. if k divides j then (c:num->real)(j DIV k) else &0`] THEN
  ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET] THEN
  SUBGOAL_THEN `{j | j IN 0..k * n /\ k divides j} = IMAGE (\i. k * i) (0..n)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0; divides] THEN
    ASM_MESON_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[EQ_MULT_LCANCEL; FINITE_NUMSEG]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[o_THM; DIV_MULT; COMPLEX_POW_POW]);;
