(* ========================================================================= *)
(* The hyperelliptic theorem (Baker 1969, qualitative form; Siegel 1926) and *)
(* the superelliptic theorem for all exponents m >= 2.                       *)
(*                                                                           *)
(* Purpose: for an integer polynomial f with three distinct simple roots the *)
(* equation y^2 = f(x) has only finitely many integer solutions              *)
(* (HYPERELLIPTIC); combined with SUPERELLIPTIC (m >= 3, two simple roots)   *)
(* this gives the finiteness of the integer solutions of y^m = f(x) for      *)
(* every m >= 2 as soon as f has at least 3 (m = 2) resp. 2 (m >= 3)         *)
(* distinct simple roots (SUPERELLIPTIC_SIMPLE_ROOTS, the number of simple   *)
(* roots counted by CARD; the set is finite since a N is non-zero).          *)
(*                                                                           *)
(* Method. HYPERELLIPTIC_MONIC (f monic, equation y^2 = c0 f(x)): the        *)
(* descent SUPERELL_ROOT_DESCENT with m = 2 at the three roots z1, z2, z3    *)
(* together with HYPERELL_THREE_ROOTS puts Cx x into a finite set unless Cx  *)
(* x is one of z1, z2, z3; for each x there are only finitely many integers  *)
(* y with y^2 = c0 f(x) (SUPERELL_FIN_PAIRS, with z3 added to the finite     *)
(* set). HYPERELLIPTIC: the monic reduction of Baker/superell.ml (A = a N,   *)
(* F(X) = A^(N-1) f(X/A), SUPERELL_MONIC_ROOT, SUPERELL_MONIC_VALUE) and the *)
(* injective map (x, y) |-> (A x, A^(N-1) y), which sends the solutions of   *)
(* y^2 = f(x) to solutions of Y^2 = A^(N-1) F(X).                            *)
(*                                                                           *)
(* Main results: HYPERELLIPTIC_MONIC, HYPERELLIPTIC,                         *)
(* SUPERELLIPTIC_SIMPLE_ROOTS; helper names HYPERELL_MAIN_*.                 *)
(*                                                                           *)
(* Uses: Baker/hyperell_roots.ml (HYPERELL_THREE_ROOTS),                     *)
(* Baker/superell_descent.ml (SUPERELL_ROOT_DESCENT), Baker/superell.ml      *)
(* (SUPERELL_FIN_PAIRS, SUPERELL_FIN_TRANSFER, SUPERELL_MONIC_ROOT,          *)
(* SUPERELL_MONIC_VALUE, SUPERELLIPTIC), Baker/algint.ml                     *)
(* (ALGEBRAIC_INTEGER_EXPLICIT); library: COMPLEX_POLYFUN_FINITE_ROOTS,      *)
(* CHOOSE_SUBSET_STRONG, HAS_SIZE_CONV.                                      *)
(* ========================================================================= *)

needs "Baker/superell.ml";;
needs "Baker/hyperell_roots.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The monic case.                                                           *)
(* ------------------------------------------------------------------------- *)

let HYPERELLIPTIC_MONIC = prove
 (`!N (a:num->real) c0 z1 z2 z3.
     (!i. integer(a i)) /\ a N = &1 /\ integer c0 /\ ~(c0 = &0) /\
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
     ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
     vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
     ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
     vsum(0..N) (\i. Cx(a i) * z3 pow i) = Cx(&0) /\
     ~(vsum(1..N) (\i. Cx(&i * a i) * z3 pow (i - 1)) = Cx(&0))
     ==> FINITE {(x,y) | integer x /\ integer y /\
                         y pow 2 = c0 * sum(0..N) (\i. a i * x pow i)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`N:num`; `a:num->real`; `2`; `c0:real`; `z1:complex`]
    SUPERELL_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= 2`; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n1:num`; `DD1:complex->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D1")))) THEN
  MP_TAC(ISPECL [`N:num`; `a:num->real`; `2`; `c0:real`; `z2:complex`]
    SUPERELL_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= 2`; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n2:num`; `DD2:complex->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D2")))) THEN
  MP_TAC(ISPECL [`N:num`; `a:num->real`; `2`; `c0:real`; `z3:complex`]
    SUPERELL_ROOT_DESCENT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= 2`; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`n3:num`; `DD3:complex->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D3")))) THEN
  MP_TAC(ISPECL [`z1:complex`; `z2:complex`; `z3:complex`;
                 `DD1:complex->bool`; `DD2:complex->bool`;
                 `DD3:complex->bool`; `n1:num`; `n2:num`; `n3:num`]
    HYPERELL_THREE_ROOTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    REPEAT CONJ_TAC THEN MAP_EVERY EXISTS_TAC [`N:num`; `a:num->real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM(ISPECL [`s:complex->bool`; `z3:complex`]
    FINITE_INSERT)] THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP SUPERELL_FIN_PAIRS) THEN
  MAP_EVERY EXISTS_TAC
   [`z1:complex`; `z2:complex`; `2`;
    `\x. c0 * sum(0..N) (\i. (a:num->real) i * x pow i)`] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; ARITH_RULE `1 <= 2`] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_INSERT] THEN
  ASM_CASES_TAC `Cx x = z3` THEN ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "D1" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d1:complex`; `q1:num->real`] THEN STRIP_TAC THEN
  REMOVE_THEN "D2" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d2:complex`; `q2:num->real`] THEN STRIP_TAC THEN
  REMOVE_THEN "D3" (MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d3:complex`; `q3:num->real`] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC
   [`d1:complex`; `d2:complex`; `d3:complex`;
    `q1:num->real`; `q2:num->real`; `q3:num->real`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The general case: monic reduction as in SUPERELLIPTIC, with m = 2.        *)
(* ------------------------------------------------------------------------- *)

let HYPERELLIPTIC = prove
 (`!N (a:num->real) z1 z2 z3.
     (!i. integer(a i)) /\ ~(a N = &0) /\
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
     ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
     vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
     ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
     vsum(0..N) (\i. Cx(a i) * z3 pow i) = Cx(&0) /\
     ~(vsum(1..N) (\i. Cx(&i * a i) * z3 pow (i - 1)) = Cx(&0))
     ==> FINITE {(x,y) | integer x /\ integer y /\
                         y pow 2 = sum(0..N) (\i. a i * x pow i)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `~(vsum(1..0) (\i. Cx(&i * (a:num->real) i) * z1 pow (i - 1)) =
        Cx(&0))` THEN
    SIMP_TAC[VSUM_TRIV_NUMSEG; ARITH; COMPLEX_VEC_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z1:complex`] SUPERELL_MONIC_ROOT) THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z2:complex`] SUPERELL_MONIC_ROOT) THEN
  MP_TAC(SPECL [`N:num`; `a:num->real`; `z3:complex`] SUPERELL_MONIC_ROOT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`N:num`; `\i. if i = N then &1 else (a:num->real) i * a N pow (N - 1 - i)`;
    `(a:num->real) N pow (N - 1)`; `Cx((a:num->real) N) * z1`;
    `Cx((a:num->real) N) * z2`; `Cx((a:num->real) N) * z3`]
   HYPERELLIPTIC_MONIC) THEN
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
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Distinct elements of a finite set with 2 or 3 elements at least.          *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_MAIN_CARD_2 = prove
 (`!s:A->bool.
     FINITE s /\ 2 <= CARD s ==> ?a b. a IN s /\ b IN s /\ ~(a = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `s:A->bool`] CHOOSE_SUBSET_STRONG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `x:A`; `y:A`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `y:A`] THEN
  ASM SET_TAC[]);;

let HYPERELL_MAIN_CARD_3 = prove
 (`!s:A->bool.
     FINITE s /\ 3 <= CARD s
     ==> ?a b c. a IN s /\ b IN s /\ c IN s /\
                 ~(a = b) /\ ~(a = c) /\ ~(b = c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `s:A->bool`] CHOOSE_SUBSET_STRONG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:A->bool`; `x:A`; `y:A`; `z:A`] THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`x:A`; `y:A`; `z:A`] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The simple roots of a non-zero integer polynomial: a finite set; 2 or 3   *)
(* distinct ones if the set has 2 or 3 elements at least.                    *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_MAIN_SIMPLE_ROOTS_FINITE = prove
 (`!N (a:num->real).
     ~(a N = &0)
     ==> FINITE {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                     ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                       Cx(&0))}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{z | vsum(0..N) (\i. Cx((a:num->real) i) * z pow i) = Cx(&0)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_POLYFUN_FINITE_ROOTS] THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL; CX_INJ];
    SET_TAC[]]);;

let HYPERELL_MAIN_SIMPLE_ROOTS_2 = prove
 (`!N (a:num->real).
     ~(a N = &0) /\
     2 <= CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                    ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                      Cx(&0))}
     ==> ?z1 z2.
           ~(z1 = z2) /\
           vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
           ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
           vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
           ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HYPERELL_MAIN_SIMPLE_ROOTS_FINITE) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HYPERELL_MAIN_CARD_2) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let HYPERELL_MAIN_SIMPLE_ROOTS_3 = prove
 (`!N (a:num->real).
     ~(a N = &0) /\
     3 <= CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
                    ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) =
                      Cx(&0))}
     ==> ?z1 z2 z3.
           ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
           vsum(0..N) (\i. Cx(a i) * z1 pow i) = Cx(&0) /\
           ~(vsum(1..N) (\i. Cx(&i * a i) * z1 pow (i - 1)) = Cx(&0)) /\
           vsum(0..N) (\i. Cx(a i) * z2 pow i) = Cx(&0) /\
           ~(vsum(1..N) (\i. Cx(&i * a i) * z2 pow (i - 1)) = Cx(&0)) /\
           vsum(0..N) (\i. Cx(a i) * z3 pow i) = Cx(&0) /\
           ~(vsum(1..N) (\i. Cx(&i * a i) * z3 pow (i - 1)) = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HYPERELL_MAIN_SIMPLE_ROOTS_FINITE) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HYPERELL_MAIN_CARD_3) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The superelliptic theorem for every exponent m >= 2.                      *)
(* ------------------------------------------------------------------------- *)

let SUPERELLIPTIC_SIMPLE_ROOTS = prove
 (`!N (a:num->real) m.
     2 <= m /\ (!i. integer(a i)) /\ ~(a N = &0) /\
     (if m = 2 then 3 else 2) <=
     CARD {z | vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
               ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))}
     ==> FINITE {(x,y) | integer x /\ integer y /\
                         y pow m = sum(0..N) (\i. a i * x pow i)}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 2` THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`N:num`; `a:num->real`] HYPERELL_MAIN_SIMPLE_ROOTS_3) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z1:complex`; `z2:complex`; `z3:complex`] THEN
    STRIP_TAC THEN MATCH_MP_TAC HYPERELLIPTIC THEN
    MAP_EVERY EXISTS_TAC [`z1:complex`; `z2:complex`; `z3:complex`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `3 <= m` ASSUME_TAC THENL
     [UNDISCH_TAC `~(m = 2)` THEN UNDISCH_TAC `2 <= m` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`N:num`; `a:num->real`] HYPERELL_MAIN_SIMPLE_ROOTS_2) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z1:complex`; `z2:complex`] THEN
    STRIP_TAC THEN MATCH_MP_TAC SUPERELLIPTIC THEN
    MAP_EVERY EXISTS_TAC [`z1:complex`; `z2:complex`] THEN
    ASM_REWRITE_TAC[]]);;
