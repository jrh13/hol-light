(* ========================================================================= *)
(* The superelliptic theorem (Baker 1969, qualitative form; Baker,           *)
(* Transcendental Number Theory, Ch. 4).                                     *)
(*                                                                           *)
(* Purpose: for an integer polynomial f with two distinct simple roots and   *)
(* m >= 3 the equation y^m = f(x) has only finitely many integer solutions.  *)
(* SUPERELLIPTIC_MONIC (f monic, equation y^m = c0 f(x)): the descent        *)
(* SUPERELL_ROOT_DESCENT at both roots z1, z2 together with                  *)
(* SUPERELL_TWO_ROOTS puts Cx x into a finite set unless Cx x is z1 or z2;   *)
(* for each x there are only finitely many integers y with y^m = c0 f(x),    *)
(* since abs y <= abs(y^m) + 1. SUPERELLIPTIC: monic reduction. With         *)
(* A = a N (non-zero), b N = 1 and b i = a i A^(N-1-i) for i < N the         *)
(* integer polynomial F = sum b i X^i is monic, F(A z) = A^(N-1) f(z) and    *)
(* A DF(A z) = A^(N-1) Df(z), where D is the formal derivative; so A z1,     *)
(* A z2 are distinct simple roots of F, and the injective map                *)
(* (x, y) |-> (A x, A^(N-1) y) sends the solutions of y^m = f(x) to          *)
(* solutions of Y^m = (A^(N-1))^(m-1) F(X).                                  *)
(*                                                                           *)
(* Main results: SUPERELLIPTIC, SUPERELLIPTIC_MONIC.                         *)
(*                                                                           *)
(* Uses: Baker/superell_descent.ml (SUPERELL_ROOT_DESCENT),                  *)
(* Baker/superell_roots.ml (SUPERELL_TWO_ROOTS), Baker/algint.ml             *)
(* (ALGEBRAIC_INTEGER_EXPLICIT), Baker/lemmas.ml (REAL_POW_PRED).            *)
(* ========================================================================= *)

needs "Baker/superell_descent.ml";;
needs "Baker/superell_roots.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Finitely many integers y with y^m = c, and finiteness of solution sets.   *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_FIN_POW_ABS = prove
 (`!m (y:real). 1 <= m ==> abs y <= abs(y pow m) + &1`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `abs(y:real) <= &1` THENL
   [MP_TAC(SPEC `(y:real) pow m` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) <= y ==> x <= y + &1`) THEN
  REWRITE_TAC[REAL_ABS_POW] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let SUPERELL_FIN_POW_EQ = prove
 (`!m (c:real). 1 <= m ==> FINITE {y | integer y /\ y pow m = c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{y:real | integer y /\ --(abs(c:real) + &1) <= y /\
                        y <= abs c + &1}` THEN
  REWRITE_TAC[FINITE_INTSEG; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`m:num`; `y:real`] SUPERELL_FIN_POW_ABS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let SUPERELL_FIN_PAIRS = prove
 (`!XS. FINITE XS
        ==> !(w1:complex) w2 k (g:real->real) (s:real#real->bool).
              1 <= k /\
              (!x y. (x,y) IN s ==> integer y /\ y pow k = g x) /\
              (!x y. (x,y) IN s /\ ~(Cx x = w1) /\ ~(Cx x = w2)
                     ==> Cx x IN XS)
              ==> FINITE s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{(x,y) | x IN IMAGE Re (w1 INSERT w2 INSERT XS) /\
                       y IN {y | integer y /\ y pow k = (g:real->real) x}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_INSERT; SUPERELL_FIN_POW_EQ];
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_INSERT] THEN CONJ_TAC THENL
     [EXISTS_TAC `Cx x` THEN REWRITE_TAC[RE_CX] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]]]);;

let SUPERELL_FIN_TRANSFER = prove
 (`!Q. FINITE {(x,y) | (Q:real->real->bool) x y}
       ==> !P u v. ~(u = &0) /\ ~(v = &0) /\
                   (!x y. P x y ==> Q (u * x) (v * y))
                   ==> FINITE {(x,y) | (P:real->real->bool) x y}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\p:real#real. (FST p / u, SND p / v))
                    {(x,y) | (Q:real->real->bool) x y}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_IMAGE;
              EXISTS_PAIR_THM; PAIR_EQ; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`u * x:real`; `v * y:real`] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `~(u = &0)` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(v = &0)` THEN CONV_TAC REAL_FIELD;
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The monic case.                                                           *)
(* ------------------------------------------------------------------------- *)

let SUPERELLIPTIC_MONIC = prove
 (`!N (a:num->real) m c0 z1 z2.
   3 <= m /\ (!i. integer(a i)) /\ a N = &1 /\ integer c0 /\
   ~(c0 = &0) /\ ~(z1 = z2) /\
   vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
   ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
   vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
   ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0))
   ==> FINITE {(x,y) | integer x /\ integer y /\
                       y pow m = c0 * sum(0..N) (\i. a i * x pow i)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `a:num->real`; `m:num`; `c0:real`; `z1:complex`]
    SUPERELL_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n1:num`; `DD1:complex->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1")))) THEN
  MP_TAC(ISPECL [`N:num`; `a:num->real`; `m:num`; `c0:real`; `z2:complex`]
    SUPERELL_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n2:num`; `DD2:complex->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2")))) THEN
  MP_TAC(ISPECL [`m:num`; `z1:complex`; `z2:complex`; `DD1:complex->bool`;
                 `DD2:complex->bool`; `n1:num`; `n2:num`]
    SUPERELL_TWO_ROOTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    CONJ_TAC THEN MAP_EVERY EXISTS_TAC [`N:num`; `a:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP SUPERELL_FIN_PAIRS) THEN
  MAP_EVERY EXISTS_TAC
   [`z1:complex`; `z2:complex`; `m:num`;
    `\x. c0 * sum(0..N) (\i. (a:num->real) i * x pow i)`] THEN
  ASM_REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  REMOVE_THEN "D1" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d1:complex`; `q1:num->real`] THEN STRIP_TAC THEN
  REMOVE_THEN "D2" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d2:complex`; `q2:num->real`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`d1:complex`; `d2:complex`; `q1:num->real`; `q2:num->real`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The monic reduction: b N = 1 and b i = a i * a N pow (N - 1 - i).         *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_MONIC_COEFF = prove
 (`!N (a:num->real) i.
        1 <= N /\ i <= N
        ==> (if i = N then &1 else a i * a N pow (N - 1 - i)) * a N pow i =
            a N pow (N - 1) * a i`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(SPECL [`(a:num->real) N`; `N:num`] REAL_POW_PRED) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:num->real) N pow (N - 1) = a N pow (N - 1 - i) * a N pow i`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REAL_ARITH_TAC]);;

let SUPERELL_MONIC_VALUE = prove
 (`!N (a:num->real) (x:real).
        1 <= N
        ==> sum(0..N) (\i. (if i = N then &1 else a i * a N pow (N - 1 - i)) *
                           (a N * x) pow i) =
            a N pow (N - 1) * sum(0..N) (\i. a i * x pow i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `i:num`] SUPERELL_MONIC_COEFF) THEN
  ASM_REWRITE_TAC[REAL_POW_MUL] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[REAL_MUL_ASSOC; th]));;

let SUPERELL_MONIC_CVALUE = prove
 (`!N (a:num->real) (z:complex).
        1 <= N
        ==> vsum(0..N) (\i. Cx(if i = N then &1
                               else a i * a N pow (N - 1 - i)) *
                            (Cx(a N) * z) pow i) =
            Cx(a N pow (N - 1)) * vsum(0..N) (\i. Cx(a i) * z pow i)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `i:num`] SUPERELL_MONIC_COEFF) THEN
  ASM_REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL; th]));;

let SUPERELL_MONIC_CDERIV = prove
 (`!N (a:num->real) (z:complex).
        1 <= N
        ==> Cx(a N) *
            vsum(1..N) (\i. Cx(&i * (if i = N then &1
                                     else a i * a N pow (N - 1 - i))) *
                            (Cx(a N) * z) pow (i - 1)) =
            Cx(a N pow (N - 1)) *
            vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `i:num`] SUPERELL_MONIC_COEFF) THEN
  MP_TAC(SPECL [`(a:num->real) N`; `i:num`] REAL_POW_PRED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; GSYM CX_POW] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM CX_MUL] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`if i = N then &1 else (a:num->real) i * a N pow (N - 1 - i)`,
           `bb:real`) THEN
  GEN_TAC THEN CONV_TAC REAL_RING);;

let SUPERELL_MONIC_ROOT = prove
 (`!N (a:num->real) (z:complex).
        1 <= N /\ ~(a N = &0) /\
        vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))
        ==> vsum(0..N) (\i. Cx(if i = N then &1
                               else a i * a N pow (N - 1 - i)) *
                            (Cx(a N) * z) pow i) = Cx(&0) /\
            ~(vsum(1..N) (\i. Cx(&i * (if i = N then &1
                                       else a i * a N pow (N - 1 - i))) *
                              (Cx(a N) * z) pow (i - 1)) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUPERELL_MONIC_CVALUE; COMPLEX_MUL_RZERO] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z:complex`]
    SUPERELL_MONIC_CDERIV) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
  DISCH_THEN(MP_TAC o SYM) THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; REAL_POW_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* The general case.                                                         *)
(* ------------------------------------------------------------------------- *)

let SUPERELLIPTIC = prove
 (`!N (a:num->real) m z1 z2.
   3 <= m /\ (!i. integer(a i)) /\ ~(a N = &0) /\ ~(z1 = z2) /\
   vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
   ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
   vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
   ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0))
   ==> FINITE {(x,y) | integer x /\ integer y /\
                       y pow m = sum(0..N) (\i. a i * x pow i)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `~(vsum(1..0) (\i. Cx(&i * (a:num->real) i) * z1 pow (i - 1)) =
        Cx(&0))` THEN
    SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH; COMPLEX_VEC_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z1:complex`] SUPERELL_MONIC_ROOT) THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z2:complex`] SUPERELL_MONIC_ROOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`N:num`; `\i. if i = N then &1 else (a:num->real) i * a N pow (N - 1 - i)`;
    `m:num`; `((a:num->real) N pow (N - 1)) pow (m - 1)`;
    `Cx((a:num->real) N) * z1`; `Cx((a:num->real) N) * z2`]
   SUPERELLIPTIC_MONIC) THEN
  ASM_REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; CX_INJ] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED; REAL_POW_NZ] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP SUPERELL_FIN_TRANSFER) THEN
  MAP_EVERY EXISTS_TAC [`(a:num->real) N`; `(a:num->real) N pow (N - 1)`] THEN
  ASM_REWRITE_TAC[REAL_POW_EQ_0] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; SUPERELL_MONIC_VALUE] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  MP_TAC(SPECL [`(a:num->real) N pow (N - 1)`; `m:num`]
    REAL_POW_PRED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;
