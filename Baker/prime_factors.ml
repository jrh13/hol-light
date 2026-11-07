(* ========================================================================= *)
(* Prime factors of the values of an integer polynomial: the greatest prime  *)
(* factor of f(x) tends to infinity as soon as f has two distinct roots, a   *)
(* classical theorem (Polya, Siegel), made effective by linear forms in      *)
(* logarithms (Shorey and Tijdeman; see Y. Bugeaud, Linear Forms in          *)
(* Logarithms and Applications, EMS 2018, section 3.5); here in qualitative  *)
(* form through SUPERELLIPTIC.                                               *)
(*                                                                           *)
(* Purpose: for f(x) = sum_{i<=N} a_i x^i with integer coefficients and two  *)
(* distinct complex roots, and a finite set S, only finitely many integers x *)
(* have f(x) <> 0 with all prime factors in S (POLY_SMOOTH_VALUES_FINITE);   *)
(* equivalently, for every bound B all integers x of large absolute value    *)
(* have a prime factor of f(x) above B (POLY_LARGEST_PRIME_FACTOR). A prime  *)
(* p divides the real integer v iff v = &p * k for an integer k. There is no *)
(* hypothesis on the leading coefficient: if every a i vanishes the sets are *)
(* empty.                                                                    *)
(*                                                                           *)
(* Method. (1) Simple roots: f(x) = c y^3 with c from a finite set of        *)
(* non-zero integers (INTEGER_SMOOTH_POW_DECOMPOSITION: c collects the       *)
(* exponents mod 3 of the primes of S); then (x, c y) solves Y^3 = c^2 f(X), *)
(* whose two simple roots are those of f, and SUPERELLIPTIC (m = 3) leaves   *)
(* finitely many x for each c (POLY_SMOOTH_SUPERELL_CUBE,                    *)
(* POLY_SMOOTH_VALUES_FINITE_SIMPLE; the coefficients are first trimmed to   *)
(* the exact degree, POLY_TRIM_EXACT_DEGREE). (2) Any multiplicities: after  *)
(* the monic scaling F(A x) = A^(N-1) f(x) of Baker/superell.ml (A = a N)    *)
(* the minimal polynomials g1, g2 of the roots A z1, A z2 (NF_DATA_EXISTS)   *)
(* give a factor G of F with two distinct simple roots                       *)
(* (POLY_MONIC_SIMPLE_ROOTS_FACTOR: G = g1 if g1(A z2) = 0, G = g2 if g2(A   *)
(* z1) = 0, else G = g1 g2, with NF_DATA_SIMPLE_ROOT and the product rule    *)
(* POLY_FORMAL_DERIV_MUL); the prime factors of G(A x) divide A^(N-1) f(x),  *)
(* so (1) applies to G with S enlarged by the numbers up to abs A.           *)
(*                                                                           *)
(* Main results: POLY_SMOOTH_VALUES_FINITE,                                  *)
(* POLY_SMOOTH_VALUES_FINITE_SIMPLE, POLY_LARGEST_PRIME_FACTOR,              *)
(* POLY_PRIME_POWER_VALUES_FINITE, SQUARE_PLUS_SMOOTH_FINITE,                *)
(* SQUARE_PLUS_PRIME_POWER_FINITE, LARGEST_PRIME_FACTOR_SQUARE_PLUS_1,       *)
(* INTEGER_SMOOTH_POW_DECOMPOSITION; generic lemmas NPRODUCT_EXP,            *)
(* PRIME_FACTORIZATION_SUPERSET, NUM_SMOOTH_POW_DECOMPOSITION,               *)
(* INTEGER_PRIME_DIVPROD, INTEGER_PRIME_DIVPOW, INTEGER_DIVIDES_LE,          *)
(* POLY_TRIM_EXACT_DEGREE, POLY_FORMAL_DERIV_MUL, NF_DATA_SIMPLE_ROOTS,      *)
(* POLY_MONIC_SIMPLE_ROOTS_FACTOR,                                           *)
(* SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA (the two simple roots of x^2 + D,  *)
(* also used by sections 20 and 21), SQUARE_PLUS_POLY_DATA; helper names     *)
(* POLY_SMOOTH_*.                                                            *)
(*                                                                           *)
(* Uses: Baker/schinzel_descent.ml (INTEGER_DIVIDES_ABS), Baker/superell.ml  *)
(* (SUPERELLIPTIC, SUPERELL_MONIC_VALUE, SUPERELL_MONIC_CVALUE),             *)
(* Baker/schinzel_sunit.ml (SUPERELL_DERIV_SHIFT, NF_DATA_SIMPLE_ROOT,       *)
(* NF_DATA_ROOT_1, NF_DESCENT_VSUM_CX), Baker/nf_fields.ml (NF_DATA_EXISTS), *)
(* Baker/descent.ml (NF_DATA_POLY_DIVIDES), Baker/nf_order.ml (NF_DATA,      *)
(* NF_DATA_ROOT, NF_DATA_FACTOR, NF_DATA_DEGREE, NF_DERIV_REINDEX,           *)
(* HAS_COMPLEX_DERIVATIVE_POLYFUN, INT_POLYFUN_MUL), Baker/nf_defs.ml        *)
(* (nf_data), Baker/algint.ml (ALGEBRAIC_INTEGER_EXPLICIT, LE_1_SUC_EXISTS,  *)
(* int_polyfun), Baker/bridge.ml (COMPLEX_POLYFUN_EXACT_DEGREE),             *)
(* Baker/schinzel.ml (SCHINZEL_TIJDEMAN_INTEGER_POLY,                        *)
(* SCHINZEL_TIJDEMAN_REAL_FACTOR), Baker/schinzel_mult.ml                    *)
(* (SCHINZEL_TIJDEMAN_MULT_DEGREE_POS); library: Library/prime.ml (index,    *)
(* PRIME_FACTORIZATION, INDEX_ZERO, PRIME_DIVPROD, PRIME_DIVEXP, EUCLID,     *)
(* FINITE_DIVISORS), int.ml (DIVIDES_LE), Library/products.ml                *)
(* (NPRODUCT_SUPERSET, NPRODUCT_MUL, NPRODUCT_LE), Library/floor.ml          *)
(* (FINITE_INTSEG), UPPER_BOUND_FINITE_SET_REAL, CSQRT.                      *)
(* ========================================================================= *)

needs "Baker/schinzel_descent.ml";;
needs "Baker/schinzel.ml";;
needs "Baker/schinzel_mult.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Number theory: an S-smooth non-zero integer is c y^m with c from a        *)
(* finite set (Library/prime.ml index and PRIME_FACTORIZATION); prime        *)
(* divisors of real integers.                                                *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_EXP = prove
 (`!(f:A->num) m s. FINITE s
                    ==> nproduct s (\x. f x EXP m) = nproduct s f EXP m`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NPRODUCT_CLAUSES; EXP_ONE; MULT_EXP]);;

let PRIME_FACTORIZATION_SUPERSET = prove
 (`!s n. FINITE s /\ (!p. p IN s ==> prime p) /\ ~(n = 0) /\
         (!p. prime p /\ p divides n ==> p IN s)
         ==> nproduct s (\p. p EXP index p n) = n`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    GEN_REWRITE_TAC RAND_CONV [SYM(MATCH_MP PRIME_FACTORIZATION th)]) THEN
  MATCH_MP_TAC NPRODUCT_SUPERSET THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `index p n = 0` (fun th -> REWRITE_TAC[th; EXP]) THEN
  MATCH_MP_TAC INDEX_ZERO THEN ASM_MESON_TAC[]);;

let NUM_SMOOTH_POW_DECOMPOSITION = prove
 (`!S m n. FINITE S /\ 1 <= m /\ ~(n = 0) /\
           (!p. prime p /\ p divides n ==> p IN S)
           ==> ?c y. n = c * y EXP m /\ ~(c = 0) /\
                     c <= nproduct {p | p IN S /\ prime p}
                                   (\p. p EXP (m - 1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `PS = {p | p IN S /\ prime p}` THEN
  SUBGOAL_THEN `FINITE(PS:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "PS" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `S:num->bool` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN PS ==> prime p` ASSUME_TAC THENL
   [EXPAND_TAC "PS" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. prime p /\ p divides n ==> p IN PS` ASSUME_TAC THENL
   [EXPAND_TAC "PS" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`nproduct PS (\p. p EXP (index p n MOD m))`;
    `nproduct PS (\p. p EXP (index p n DIV m))`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(SPECL [`PS:num->bool`; `n:num`]
      PRIME_FACTORIZATION_SUPERSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    ASM_SIMP_TAC[GSYM NPRODUCT_EXP; GSYM NPRODUCT_MUL] THEN
    MATCH_MP_TAC NPRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM EXP_MULT; GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`index p n`; `m:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ARITH_TAC];
    ASM_SIMP_TAC[NPRODUCT_EQ_0; EXP_EQ_0] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[LE_EXP] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    DISJ2_TAC THEN MP_TAC(SPECL [`index p n`; `m:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

let INTEGER_SMOOTH_POW_DECOMPOSITION = prove
 (`!S m. FINITE S /\ 1 <= m
         ==> ?C. FINITE C /\ (!c. c IN C ==> integer c /\ ~(c = &0)) /\
                 !v. integer v /\ ~(v = &0) /\
                     (!p. prime p /\ (?k. integer k /\ v = &p * k)
                          ==> p IN S)
                     ==> ?c y. c IN C /\ integer y /\ v = c * y pow m`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Q = nproduct {p | p IN S /\ prime p} (\p. p EXP (m - 1))` THEN
  EXISTS_TAC `{c | integer c /\ ~(c = &0) /\ abs c <= &Q}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{c | integer c /\ -- &Q <= c /\ c <= &Q}` THEN
    REWRITE_TAC[FINITE_INTSEG; SUBSET; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  X_GEN_TAC `v:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. abs(v:real) = &n` (X_CHOOSE_TAC `n:num`) THENL
   [ASM_REWRITE_TAC[GSYM integer]; ALL_TAC] THEN
  MP_TAC(SPECL [`S:num->bool`; `m:num`; `n:num`]
    NUM_SMOOTH_POW_DECOMPOSITION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[INTEGER_DIVIDES_ABS]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `y:num`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
   (REAL_ARITH `abs v = a ==> v = a \/ v = --a`)) THENL
   [MAP_EVERY EXISTS_TAC [`&c:real`; `&y:real`];
    MAP_EVERY EXISTS_TAC [`-- &c:real`; `&y:real`]] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; INTEGER_CLOSED; INTEGER_NEG; REAL_ABS_NEG;
                  REAL_ABS_NUM;
                  REAL_OF_NUM_LE; REAL_OF_NUM_EQ; REAL_NEG_EQ_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW; REAL_MUL_LNEG]);;

let INTEGER_PRIME_DIVPROD = prove
 (`!p u v. prime p /\ integer u /\ integer v /\
           (?k. integer k /\ u * v = &p * k)
           ==> (?k. integer k /\ u = &p * k) \/
               (?k. integer k /\ v = &p * k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  SUBGOAL_THEN `?m. abs u = &m` (X_CHOOSE_TAC `m:num`) THENL
   [ASM_REWRITE_TAC[GSYM integer]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. abs v = &n` (X_CHOOSE_TAC `n:num`) THENL
   [ASM_REWRITE_TAC[GSYM integer]; ALL_TAC] THEN
  MP_TAC(SPECL [`u * v:real`; `m * n:num`; `p:num`] INTEGER_DIVIDES_ABS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_MUL; GSYM REAL_OF_NUM_MUL]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `m:num`; `n:num`] PRIME_DIVPROD) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`u:real`; `m:num`; `p:num`] INTEGER_DIVIDES_ABS) THEN
  MP_TAC(SPECL [`v:real`; `n:num`; `p:num`] INTEGER_DIVIDES_ABS) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let INTEGER_PRIME_DIVPOW = prove
 (`!p u n. prime p /\ integer u /\ (?k. integer k /\ u pow n = &p * k)
           ==> (?k. integer k /\ u = &p * k)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `?m. abs u = &m` (X_CHOOSE_TAC `m:num`) THENL
   [ASM_REWRITE_TAC[GSYM integer]; ALL_TAC] THEN
  MP_TAC(SPECL [`(u:real) pow n`; `m EXP n`; `p:num`]
    INTEGER_DIVIDES_ABS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ABS_POW; GSYM REAL_OF_NUM_POW]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`u:real`; `m:num`; `p:num`] INTEGER_DIVIDES_ABS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]);;

let INTEGER_DIVIDES_LE = prove
 (`!A p. integer A /\ ~(A = &0) /\ (?k. integer k /\ A = &p * k)
         ==> &p <= abs A`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  SUBGOAL_THEN `?n. abs A = &n` (X_CHOOSE_TAC `n:num`) THENL
   [ASM_REWRITE_TAC[GSYM integer]; ALL_TAC] THEN
  MP_TAC(SPECL [`A:real`; `n:num`; `p:num`] INTEGER_DIVIDES_ABS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Coefficient sequences: constant multiples, trimming to the exact          *)
(* degree, the product rule for the formal derivative; the roots of the      *)
(* polynomial of an nf_data are simple; a monic integer polynomial with      *)
(* two distinct roots has a factor with two distinct simple roots.           *)
(* ------------------------------------------------------------------------- *)

let POLY_SMOOTH_CMUL = prove
 (`!N (a:num->real) c (z:complex).
        vsum(0..N) (\i. Cx(c * a i) * z pow i) =
        Cx c * vsum(0..N) (\i. Cx(a i) * z pow i) /\
        vsum(1..N) (\i. Cx(&i * c * a i) * z pow (i - 1)) =
        Cx c * vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1))`,
  REPEAT GEN_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  CONJ_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let POLY_TRIM_EXACT_DEGREE = prove
 (`!N (a:num->real).
        ~(!i. i <= N ==> a i = &0)
        ==> ?M. M <= N /\ ~(a M = &0) /\
                (!z. vsum(0..M) (\i. Cx(a i) * z pow i) =
                     vsum(0..N) (\i. Cx(a i) * z pow i)) /\
                (!z. vsum(1..M) (\i. Cx(&i * a i) * z pow (i - 1)) =
                     vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1))) /\
                (!x. sum(0..M) (\i. a i * x pow i) =
                     sum(0..N) (\i. a i * x pow i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i. Cx((a:num->real) i)`; `N:num`]
    COMPLEX_POLYFUN_EXACT_DEGREE) THEN
  ASM_REWRITE_TAC[CX_INJ] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET_NUMSEG; IN_NUMSEG] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:num->real) i = &0` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
    X_GEN_TAC `x:real` THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
    ASM_REWRITE_TAC[GSYM NF_DESCENT_VSUM_CX]]);;

let POLY_FORMAL_DERIV_MUL = prove
 (`!N (a:num->real) n (b:num->real) M (c:num->real) (z:complex).
        (!w. vsum(0..N) (\i. Cx(a i) * w pow i) =
             vsum(0..n) (\i. Cx(b i) * w pow i) *
             vsum(0..M) (\i. Cx(c i) * w pow i))
        ==> vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
            vsum(1..n) (\i. Cx(&i * b i) * z pow (i - 1)) *
            vsum(0..M) (\i. Cx(c i) * z pow i) +
            vsum(0..n) (\i. Cx(b i) * z pow i) *
            vsum(1..M) (\i. Cx(&i * c i) * z pow (i - 1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUPERELL_DERIV_SHIFT] THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\w. vsum(0..N) (\i. Cx((a:num->real) i) * w pow i)` THEN
  EXISTS_TAC `z:complex` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`N:num`; `\i. Cx((a:num->real) i)`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. vsum(0..N) (\i. Cx((a:num->real) i) * w pow i)) =
    (\w. vsum(0..n) (\i. Cx((b:num->real) i) * w pow i) *
         vsum(0..M) (\i. Cx((c:num->real) i) * w pow i))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MP_TAC(CONJ
   (BETA_RULE(ISPECL [`n:num`; `\i. Cx((b:num->real) i)`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN))
   (BETA_RULE(ISPECL [`M:num`; `\i. Cx((c:num->real) i)`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_AT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC COMPLEX_RING);;

let NF_DATA_SIMPLE_ROOTS = prove
 (`!n c r w. nf_data n c r /\ vsum(0..n) (\i. Cx(c i) * w pow i) = Cx(&0)
             ==> ~(vsum(1..n) (\i. Cx(&i * c i) * w pow (i - 1)) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k. k IN 1..n /\ w = (r:num->complex) k` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `vsum(0..n) (\i. Cx((c:num->real) i) * w pow i) = Cx(&0)` THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP NF_DATA_FACTOR th]) THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG; COMPLEX_SUB_0];
    ASM_MESON_TAC[NF_DATA_SIMPLE_ROOT]]);;

let POLY_MONIC_SIMPLE_ROOTS_FACTOR = prove
 (`!N (b:num->real) Z1 Z2.
        (!i. integer(b i)) /\ b N = &1 /\ ~(Z1 = Z2) /\
        vsum(0..N) (\i. Cx(b i) * Z1 pow i) = Cx(&0) /\
        vsum(0..N) (\i. Cx(b i) * Z2 pow i) = Cx(&0)
        ==> ?M (g:num->real) K (h:num->real) W1 W2.
              (!i. integer(g i)) /\ (!i. integer(h i)) /\ ~(W1 = W2) /\
              (!z. vsum(0..N) (\i. Cx(b i) * z pow i) =
                   vsum(0..M) (\i. Cx(g i) * z pow i) *
                   vsum(0..K) (\i. Cx(h i) * z pow i)) /\
              vsum(0..M) (\i. Cx(g i) * W1 pow i) = Cx(&0) /\
              ~(vsum(1..M) (\i. Cx(&i * g i) * W1 pow (i - 1)) = Cx(&0)) /\
              vsum(0..M) (\i. Cx(g i) * W2 pow i) = Cx(&0) /\
              ~(vsum(1..M) (\i. Cx(&i * g i) * W2 pow (i - 1)) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `Z1:complex` NF_DATA_EXISTS) THEN ANTS_TAC THENL
   [REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `b:num->real`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `n1:num` (X_CHOOSE_THEN `c1:num->real`
      (X_CHOOSE_THEN `r1:num->complex` STRIP_ASSUME_TAC)))] THEN
  MP_TAC(SPEC `Z2:complex` NF_DATA_EXISTS) THEN ANTS_TAC THENL
   [REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `b:num->real`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `n2:num` (X_CHOOSE_THEN `c2:num->real`
      (X_CHOOSE_THEN `r2:num->complex` STRIP_ASSUME_TAC)))] THEN
  MP_TAC(SPECL [`n1:num`; `c1:num->real`; `r1:num->complex`]
    NF_DATA_ROOT_1) THEN
  MP_TAC(SPECL [`n2:num`; `c2:num->real`; `r2:num->complex`]
    NF_DATA_ROOT_1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(!i. integer((c1:num->real) i)) /\
                (!i. integer((c2:num->real) i))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[NF_DATA]; ALL_TAC] THEN
  ASM_CASES_TAC `vsum(0..n1) (\i. Cx((c1:num->real) i) * Z2 pow i) = Cx(&0)`
  THENL
   [MP_TAC(SPECL [`n1:num`; `c1:num->real`; `r1:num->complex`; `N:num`;
                  `b:num->real`] NF_DATA_POLY_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:num->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`n1:num`; `c1:num->real`; `N:num`; `h:num->real`;
                          `Z1:complex`; `Z2:complex`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC NF_DATA_SIMPLE_ROOTS THEN
    EXISTS_TAC `r1:num->complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `vsum(0..n2) (\i. Cx((c2:num->real) i) * Z1 pow i) = Cx(&0)`
  THENL
   [MP_TAC(SPECL [`n2:num`; `c2:num->real`; `r2:num->complex`; `N:num`;
                  `b:num->real`] NF_DATA_POLY_DIVIDES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:num->real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`n2:num`; `c2:num->real`; `N:num`; `h:num->real`;
                          `Z1:complex`; `Z2:complex`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC NF_DATA_SIMPLE_ROOTS THEN
    EXISTS_TAC `r2:num->complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n1:num`; `c1:num->real`; `r1:num->complex`; `N:num`;
                `b:num->real`] NF_DATA_POLY_DIVIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "f1"))) THEN
  SUBGOAL_THEN `vsum(0..N) (\i. Cx((h1:num->real) i) * Z2 pow i) = Cx(&0)`
  ASSUME_TAC THENL
   [USE_THEN "f1" (MP_TAC o SYM o SPEC `Z2:complex`) THEN
    REWRITE_TAC[ASSUME `vsum(0..N) (\i. Cx((b:num->real) i) * Z2 pow i) =
                        Cx(&0)`;
                ASSUME `~(vsum(0..n1) (\i. Cx((c1:num->real) i) * Z2 pow i) =
                          Cx(&0))`;
                COMPLEX_ENTIRE];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n2:num`; `c2:num->real`; `r2:num->complex`; `N:num`;
                `h1:num->real`] NF_DATA_POLY_DIVIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "f2"))) THEN
  MP_TAC(ISPECL [`n1:num`; `n2:num`;
                 `\z. vsum(0..n1) (\i. Cx((c1:num->real) i) * z pow i)`;
                 `\z. vsum(0..n2) (\i. Cx((c2:num->real) i) * z pow i)`]
    INT_POLYFUN_MUL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[int_polyfun] THEN CONJ_TAC THENL
     [EXISTS_TAC `c1:num->real`; EXISTS_TAC `c2:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[int_polyfun] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "fg"))) THEN
  MAP_EVERY EXISTS_TAC [`n1 + n2:num`; `g:num->real`; `N:num`;
                        `h2:num->real`; `Z1:complex`; `Z2:complex`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN
    USE_THEN "f1" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "f2" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fg" (fun th -> REWRITE_TAC[GSYM th]) THEN
    CONV_TAC COMPLEX_RING;
    USE_THEN "fg" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[ASSUME `vsum(0..n1) (\i. Cx((c1:num->real) i) * Z1 pow i) =
                        Cx(&0)`; COMPLEX_MUL_LZERO];
    MP_TAC(SPECL [`n1 + n2:num`; `g:num->real`; `n1:num`; `c1:num->real`;
                  `n2:num`; `c2:num->real`; `Z1:complex`]
      POLY_FORMAL_DERIV_MUL) THEN
    ANTS_TAC THENL
     [USE_THEN "fg" (fun th -> REWRITE_TAC[GSYM th]); ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; COMPLEX_ENTIRE] THEN
    MATCH_MP_TAC NF_DATA_SIMPLE_ROOTS THEN
    EXISTS_TAC `r1:num->complex` THEN ASM_REWRITE_TAC[];
    USE_THEN "fg" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[ASSUME `vsum(0..n2) (\i. Cx((c2:num->real) i) * Z2 pow i) =
                        Cx(&0)`; COMPLEX_MUL_RZERO];
    MP_TAC(SPECL [`n1 + n2:num`; `g:num->real`; `n1:num`; `c1:num->real`;
                  `n2:num`; `c2:num->real`; `Z2:complex`]
      POLY_FORMAL_DERIV_MUL) THEN
    ANTS_TAC THENL
     [USE_THEN "fg" (fun th -> REWRITE_TAC[GSYM th]); ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_ENTIRE] THEN
    MATCH_MP_TAC NF_DATA_SIMPLE_ROOTS THEN
    EXISTS_TAC `r2:num->complex` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Two simple roots: f(x) = c y^3 with c from a finite set, and              *)
(* SUPERELLIPTIC (m = 3) for c^2 f.                                          *)
(* ------------------------------------------------------------------------- *)

let POLY_SMOOTH_SUPERELL_CUBE = prove
 (`!N (a:num->real) z1 z2 c.
        (!i. integer(a i)) /\ ~(a N = &0) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
        integer c /\ ~(c = &0)
        ==> FINITE {x | integer x /\
                        ?y. integer y /\
                            sum(0..N) (\i. a i * x pow i) = c * y pow 3}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`N:num`; `\i. c pow 2 * (a:num->real) i`; `3`;
                 `z1:complex`; `z2:complex`] SUPERELLIPTIC) THEN
  ASM_REWRITE_TAC[POLY_SMOOTH_CMUL; COMPLEX_MUL_RZERO; COMPLEX_ENTIRE; CX_INJ;
                  REAL_ENTIRE;
                  REAL_POW_EQ_0; ARITH] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTEGER_MUL; INTEGER_POW]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPEC `FST:real#real->real` o MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM;
              IN_ELIM_PAIR_THM] THEN
  X_GEN_TAC `x:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `c * y:real`] THEN
  ASM_SIMP_TAC[INTEGER_MUL; GSYM REAL_MUL_ASSOC; SUM_LMUL] THEN
  CONV_TAC REAL_RING);;

let POLY_SMOOTH_SIMPLE_CORE = prove
 (`!N (a:num->real) z1 z2 S.
        (!i. integer(a i)) /\ ~(a N = &0) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
        FINITE S
        ==> FINITE {x | integer x /\
                        ~(sum(0..N) (\i. a i * x pow i) = &0) /\
                        !p. prime p /\
                            (?k. integer k /\
                                 sum(0..N) (\i. a i * x pow i) = &p * k)
                            ==> p IN S}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`S:num->bool`; `3`] INTEGER_SMOOTH_POW_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS (IMAGE (\c. {x | integer x /\
                            ?y. integer y /\
                                sum(0..N) (\i. (a:num->real) i * x pow i) =
                                c * y pow 3}) C)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC POLY_SMOOTH_SUPERELL_CUBE THEN
    MAP_EVERY EXISTS_TAC [`z1:complex`; `z2:complex`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `sum(0..N) (\i. (a:num->real) i * x pow i)`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCHINZEL_TIJDEMAN_INTEGER_POLY THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `y:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{x | integer x /\
                   ?y. integer y /\
                       sum(0..N) (\i. (a:num->real) i * x pow i) =
                       c * y pow 3}` THEN
  CONJ_TAC THENL [EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `y:real` THEN ASM_REWRITE_TAC[]);;

let POLY_SMOOTH_VALUES_FINITE_SIMPLE = prove
 (`!N (a:num->real) z1 z2 S.
        (!i. integer(a i)) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
        FINITE S
        ==> FINITE {x | integer x /\
                        ~(sum(0..N) (\i. a i * x pow i) = &0) /\
                        !p. prime p /\
                            (?k. integer k /\
                                 sum(0..N) (\i. a i * x pow i) = &p * k)
                            ==> p IN S}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(!i. i <= N ==> (a:num->real) i = &0)` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `~(vsum(1..N) (\i. Cx(&i * (a:num->real) i) * z1 pow (i - 1)) =
        Cx(&0))` THEN
    REWRITE_TAC[] THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN REWRITE_TAC[IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_MUL_RZERO; COMPLEX_MUL_LZERO;
                                       COMPLEX_VEC_0];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC o
    MATCH_MP POLY_TRIM_EXACT_DEGREE) THEN
  MP_TAC(SPECL [`M:num`; `a:num->real`; `z1:complex`; `z2:complex`;
                `S:num->bool`] POLY_SMOOTH_SIMPLE_CORE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Two distinct roots of any multiplicity: monic scaling, the factor with    *)
(* two simple roots, primes of the leading coefficient added to S.           *)
(* ------------------------------------------------------------------------- *)

let POLY_SMOOTH_PROD_NZ = prove
 (`!G H P f:real. G * H = P * f /\ ~(P = &0) /\ ~(f = &0) ==> ~(G = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_MUL_LZERO]) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN ASM_REWRITE_TAC[REAL_ENTIRE]);;

let POLY_SMOOTH_GENERAL_CORE = prove
 (`!N (a:num->real) z1 z2 S.
        (!i. integer(a i)) /\ ~(a N = &0) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
        FINITE S
        ==> FINITE {x | integer x /\
                        ~(sum(0..N) (\i. a i * x pow i) = &0) /\
                        !p. prime p /\
                            (?k. integer k /\
                                 sum(0..N) (\i. a i * x pow i) = &p * k)
                            ==> p IN S}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [MATCH_MP_TAC SCHINZEL_TIJDEMAN_MULT_DEGREE_POS THEN
    MAP_EVERY EXISTS_TAC [`a:num->real`; `z1:complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?nA. abs((a:num->real) N) = &nA`
   (X_CHOOSE_THEN `nA:num` (LABEL_TAC "nA"))
  THENL [ASM_REWRITE_TAC[GSYM integer]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`N:num`; `\i. if i = N then &1 else (a:num->real) i * a N pow (N - 1 - i)`;
    `Cx((a:num->real) N) * z1`; `Cx((a:num->real) N) * z2`]
   POLY_MONIC_SIMPLE_ROOTS_FACTOR) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[INTEGER_CLOSED; INTEGER_MUL; INTEGER_POW];
      ASM_REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ];
      ASM_SIMP_TAC[SUPERELL_MONIC_CVALUE; COMPLEX_MUL_RZERO];
      ASM_SIMP_TAC[SUPERELL_MONIC_CVALUE; COMPLEX_MUL_RZERO]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`MG:num`; `g:num->real`; `K:num`; `h:num->real`;
                       `W1:complex`; `W2:complex`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP SCHINZEL_TIJDEMAN_REAL_FACTOR) THEN
  MP_TAC(SPECL [`MG:num`; `g:num->real`; `W1:complex`; `W2:complex`;
                `S UNION {p | p <= nA}`] POLY_SMOOTH_VALUES_FINITE_SIMPLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; FINITE_NUMSEG_LE]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o ISPEC `\X:real. X / (a:num->real) N` o
    MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  EXISTS_TAC `(a:num->real) N * x` THEN CONJ_TAC THENL
   [UNDISCH_TAC `~((a:num->real) N = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(0..MG) (\i. (g:num->real) i * (a N * x) pow i) *
    sum(0..K) (\i. (h:num->real) i * (a N * x) pow i) =
    a N pow (N - 1) * sum(0..N) (\i. a i * x pow i)`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      REWRITE_TAC[GSYM(BETA_RULE(SPEC `(a:num->real) N * x` th))]) THEN
    MATCH_MP_TAC SUPERELL_MONIC_VALUE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `integer((a:num->real) N * x) /\
                integer(sum(0..MG) (\i. (g:num->real) i * (a N * x) pow i)) /\
                integer(sum(0..K) (\i. (h:num->real) i * (a N * x) pow i)) /\
                integer(sum(0..N) (\i. a i * x pow i)) /\
                integer(a N pow (N - 1))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INTEGER_MUL; INTEGER_POW; SCHINZEL_TIJDEMAN_INTEGER_POLY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC POLY_SMOOTH_PROD_NZ THEN
    MAP_EVERY EXISTS_TAC
     [`sum(0..K) (\i. (h:num->real) i * ((a:num->real) N * x) pow i)`;
      `(a:num->real) N pow (N - 1)`;
      `sum(0..N) (\i. (a:num->real) i * x pow i)`] THEN
    ASM_REWRITE_TAC[REAL_POW_EQ_0];
    ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?k'. integer k' /\
         (a:num->real) N pow (N - 1) * sum(0..N) (\i. a i * x pow i) =
         &p * k'`
  MP_TAC THENL
   [EXISTS_TAC
     `k * sum(0..K) (\i. (h:num->real) i * ((a:num->real) N * x) pow i)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[INTEGER_MUL]; ALL_TAC] THEN
    UNDISCH_TAC
     `sum(0..MG) (\i. (g:num->real) i * (a N * x) pow i) *
      sum(0..K) (\i. (h:num->real) i * (a N * x) pow i) =
      a N pow (N - 1) * sum(0..N) (\i. a i * x pow i)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_MUL_ASSOC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`p:num`; `(a:num->real) N pow (N - 1)`;
                `sum(0..N) (\i. (a:num->real) i * x pow i)`]
    INTEGER_PRIME_DIVPROD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [DISJ2_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    USE_THEN "nA" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC INTEGER_DIVIDES_LE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGER_PRIME_DIVPOW THEN EXISTS_TAC `N - 1` THEN
    ASM_REWRITE_TAC[];
    DISJ1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let POLY_SMOOTH_VALUES_FINITE = prove
 (`!N (a:num->real) z1 z2 S.
        (!i. integer(a i)) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
        FINITE S
        ==> FINITE {x | integer x /\
                        ~(sum(0..N) (\i. a i * x pow i) = &0) /\
                        !p. prime p /\
                            (?k. integer k /\
                                 sum(0..N) (\i. a i * x pow i) = &p * k)
                            ==> p IN S}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `!i. i <= N ==> (a:num->real) i = &0` THENL
   [MATCH_MP_TAC(MESON[FINITE_EMPTY] `(s:real->bool) = {} ==> FINITE s`) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real` THEN
    MATCH_MP_TAC(TAUT `b ==> ~(a /\ ~b /\ c)`) THEN
    MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC o
    MATCH_MP POLY_TRIM_EXACT_DEGREE) THEN
  MP_TAC(SPECL [`M:num`; `a:num->real`; `z1:complex`; `z2:complex`;
                `S:num->bool`] POLY_SMOOTH_GENERAL_CORE) THEN
  ASM_REWRITE_TAC[]);;

let POLY_LARGEST_PRIME_FACTOR = prove
 (`!N (a:num->real) z1 z2 B.
        (!i. integer(a i)) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0)
        ==> ?X. !x. integer x /\ X <= abs x
                    ==> ?p k. prime p /\ B < p /\ integer k /\
                              sum(0..N) (\i. a i * x pow i) = &p * k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z1:complex`; `z2:complex`;
                `{p | p <= B}`] POLY_SMOOTH_VALUES_FINITE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  DISCH_THEN(MP_TAC o SPEC `abs:real->real` o
    MATCH_MP UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `X0:real`) THEN
  EXISTS_TAC `X0 + &1` THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `sum(0..N) (\i. (a:num->real) i * x pow i) = &0` THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `B:num` EUCLID) THEN
    REWRITE_TAC[GT] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN EXISTS_TAC `&0` THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_THEN(LABEL_TAC "neg") THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    REMOVE_THEN "neg" MP_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`p:num`; `k:real`] THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Corollaries: values that are prime powers; x^2 + D.                       *)
(* ------------------------------------------------------------------------- *)

let POLY_PRIME_POWER_VALUES_FINITE = prove
 (`!N (a:num->real) z1 z2 p.
        (!i. integer(a i)) /\ ~(z1 = z2) /\
        vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
        vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\ 2 <= p
        ==> FINITE {(x,n) | integer x /\
                            abs(sum(0..N) (\i. a i * x pow i)) = &p pow n}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z1:complex`; `z2:complex`;
                `{q | q divides p}`] POLY_SMOOTH_VALUES_FINITE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o
    SPEC `\x. abs(sum(0..N) (\i. (a:num->real) i * x pow i))` o
    MATCH_MP UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `B0:real` (LABEL_TAC "B0")) THEN
  MP_TAC(SPEC `B0:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{(x,n) | x IN {x | integer x /\
                       ~(sum(0..N) (\i. (a:num->real) i * x pow i) = &0) /\
                       !q. prime q /\
                           (?k. integer k /\
                                sum(0..N) (\i. a i * x pow i) = &q * k)
                           ==> q divides p} /\
             n IN 0..M}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT THEN ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM;
              IN_NUMSEG; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `n:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p pow n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sum(0..N) (\i. (a:num->real) i * x pow i) = &0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `abs(sum(0..N) (\i. (a:num->real) i * x pow i)) = &p pow n` THEN
    ASM_REWRITE_TAC[REAL_ABS_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. prime q /\
        (?k. integer k /\ sum(0..N) (\i. (a:num->real) i * x pow i) = &q * k)
        ==> q divides p`
  ASSUME_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(SPECL [`sum(0..N) (\i. (a:num->real) i * x pow i)`; `p EXP n`;
                  `q:num`] INTEGER_DIVIDES_ABS) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_POW] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `n:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "B0" (MP_TAC o SPEC `x:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&n < &p pow n` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP n` THEN
    REWRITE_TAC[LT_POW2_REFL] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC);;

(* x^2 + D (D <> 0) has the two distinct simple roots csqrt(-D) and          *)
(* -csqrt(-D).                                                               *)

let SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA = prove
 (`!D. integer D /\ ~(D = &0)
       ==> (!i. integer((\i. if i = 0 then D else if i = 1 then &0 else &1)
                        i)) /\
           ~(csqrt(Cx(--D)) = --csqrt(Cx(--D))) /\
           vsum(0..2) (\i. Cx((\i. if i = 0 then D else if i = 1 then &0
                                   else &1) i) * csqrt(Cx(--D)) pow i) =
           Cx(&0) /\
           ~(vsum(1..2) (\i. Cx(&i * (\i. if i = 0 then D else if i = 1 then &0
                                         else &1) i) *
                             csqrt(Cx(--D)) pow (i - 1)) = Cx(&0)) /\
           vsum(0..2) (\i. Cx((\i. if i = 0 then D else if i = 1 then &0
                                   else &1) i) * (--csqrt(Cx(--D))) pow i) =
           Cx(&0) /\
           ~(vsum(1..2) (\i. Cx(&i * (\i. if i = 0 then D else if i = 1 then &0
                                         else &1) i) *
                             (--csqrt(Cx(--D))) pow (i - 1)) = Cx(&0)) /\
           (!x. sum(0..2) (\i. (\i. if i = 0 then D else if i = 1 then &0
                                   else &1) i * x pow i) = x pow 2 + D)`,
  GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_VSUM_CONV) THEN
  REWRITE_TAC[ARITH_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MP_TAC(SPEC `Cx(--D)` CSQRT) THEN
  SPEC_TAC(`csqrt(Cx(--D))`,`w:complex`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(w = Cx(&0))` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `Cx(&0) pow 2 = Cx(--D)` THEN
    REWRITE_TAC[COMPLEX_POW_2; COMPLEX_MUL_LZERO; CX_INJ] THEN
    ASM_REAL_ARITH_TAC;
    UNDISCH_TAC `w pow 2 = Cx(--D)`] THEN
  REWRITE_TAC[CX_NEG; CX_MUL] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC; ALL_TAC;
    GEN_TAC THEN REAL_ARITH_TAC] THEN
  UNDISCH_TAC `~(w = Cx(&0))` THEN UNDISCH_TAC `w pow 2 = --Cx D` THEN
  CONV_TAC COMPLEX_RING);;

let SQUARE_PLUS_POLY_DATA = prove
 (`!D. integer D /\ ~(D = &0)
       ==> ?a z1 z2. (!i. integer(a i)) /\ ~(z1 = z2) /\
                     vsum(0..2) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
                     vsum(0..2) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
                     !x. sum(0..2) (\i. a i * x pow i) = x pow 2 + D`,
  GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o
    MATCH_MP SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA) THEN
  MAP_EVERY EXISTS_TAC
   [`\i. if i = 0 then D else if i = 1 then &0 else &1`;
    `csqrt(Cx(--D))`; `--csqrt(Cx(--D))`] THEN
  ASM_REWRITE_TAC[]);;

let SQUARE_PLUS_SMOOTH_FINITE = prove
 (`!D S. integer D /\ ~(D = &0) /\ FINITE S
         ==> FINITE {x | integer x /\ ~(x pow 2 + D = &0) /\
                         !p. prime p /\ (?k. integer k /\ x pow 2 + D = &p * k)
                             ==> p IN S}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SQUARE_PLUS_POLY_DATA o
    CONJ (ASSUME `integer D`)) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `z1:complex`; `z2:complex`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `a:num->real`; `z1:complex`; `z2:complex`;
                `S:num->bool`] POLY_SMOOTH_VALUES_FINITE) THEN
  ASM_REWRITE_TAC[]);;

let SQUARE_PLUS_PRIME_POWER_FINITE = prove
 (`!D p. integer D /\ ~(D = &0) /\ 2 <= p
         ==> FINITE {(x,n) | integer x /\ x pow 2 + D = &p pow n}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `D:real` SQUARE_PLUS_POLY_DATA) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `z1:complex`; `z2:complex`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `a:num->real`; `z1:complex`; `z2:complex`; `p:num`]
    POLY_PRIME_POWER_VALUES_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `n:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NUM]);;

let LARGEST_PRIME_FACTOR_SQUARE_PLUS_1 = prove
 (`!B. ?M. !n. M <= n ==> ?p. prime p /\ B < p /\ p divides (n EXP 2 + 1)`,
  GEN_TAC THEN
  MP_TAC(SPEC `&1:real` SQUARE_PLUS_POLY_DATA) THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real`; `z1:complex`; `z2:complex`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`2`; `a:num->real`; `z1:complex`; `z2:complex`; `B:num`]
    POLY_LARGEST_PRIME_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `X:real`) THEN
  MP_TAC(SPEC `X:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&n:real`) THEN
  REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&M` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&n pow 2 + &1:real`; `n EXP 2 + 1`; `p:num`]
    INTEGER_DIVIDES_ABS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_ABS_NUM]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN EXISTS_TAC `k:real` THEN
  ASM_REWRITE_TAC[]);;

prioritize_num();;
