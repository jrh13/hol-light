(* ========================================================================= *)
(* Perfect powers in Lucas sequences and the equations x^k + D = y^n:        *)
(* applications of the Schinzel-Tijdeman theorem.                            *)
(*                                                                           *)
(* Purpose: for integers P and Q = 1 or Q = -1 with P^2 <> 4 Q, the Lucas    *)
(* sequence u_0 = 0, u_1 = 1, u_(n+2) = P u_(n+1) - Q u_n contains only      *)
(* finitely many perfect powers y^m with |y| >= 2 and m >= 2: the set of the *)
(* triples (n, y, m) is finite (LUCAS_PERFECT_POWERS_FINITE; for Q = 1 and   *)
(* P = +-2 the sequence is u_n = +-n, so the condition is needed). The same  *)
(* holds for the companion sequence v_0 = 2, v_1 = P, without any condition  *)
(* on P (LUCAS_COMPANION_PERFECT_POWERS_FINITE). Corollaries in num form:    *)
(* the Fibonacci numbers (FIBONACCI_PERFECT_POWERS_FINITE, for fib of        *)
(* Examples/gcdrecurrence.ml), the Pell numbers                              *)
(* (PELL_PERFECT_POWERS_FINITE), the Lucas numbers                           *)
(* (LUCAS_NUMBERS_PERFECT_POWERS_FINITE) and every sequence                  *)
(* u_(n+2) = p u_(n+1) + u_n with u_0 = 0, u_1 = 1                           *)
(* (LUCAS_NUM_PERFECT_POWERS_FINITE). These are cases of the theorem of      *)
(* A. Petho (J. Number Theory 15, 1982) and T. N. Shorey and C. L. Stewart   *)
(* (Math. Scand. 52, 1983) on perfect powers in binary recurrences (Y.       *)
(* Bugeaud, Linear Forms in Logarithms and Applications, EMS 2018, Theorem   *)
(* 6.12); the exact lists (0, 1, 8, 144 for the Fibonacci numbers, 1, 4 for  *)
(* the Lucas numbers) need modular methods (Y. Bugeaud, M. Mignotte and S.   *)
(* Siksek, Ann. of Math. 163, 2006). For fixed k >= 2 and D <> 0 the         *)
(* equation x^k + D = y^n has only finitely many integer solutions with      *)
(* |y| >= 2 and n >= 2 (POW_PLUS_POW_FINITE; with k varying as well this is  *)
(* the conjecture of Pillai), and x^2 + C = D y^n with C, D <> 0 has only    *)
(* finitely many with |y| >= 2 and n >= 3 (SQUARE_PLUS_MUL_POW_FINITE).      *)
(*                                                                           *)
(* Method. The invariant u_(n+1)^2 - P u_(n+1) u_n + Q u_n^2 = Q^n           *)
(* (LUCAS_SEQUENCE_INVARIANT) gives X^2 - Delta u_n^2 = 4 Q^n for            *)
(* X = 2 u_(n+1) - P u_n and Delta = P^2 - 4 Q, so u_n = y^m becomes         *)
(* X^2 + C = Delta y^(2 m) with C = -4 or C = 4 when Q = +-1 (C = +-4 Delta  *)
(* for v_n). For x^2 + C = D y^n the monic form of the Schinzel-Tijdeman     *)
(* theorem (SCHINZEL_TIJDEMAN_GENERAL_MONIC: c y^m = F(x) with F = x^2 + C   *)
(* and c = D) bounds n, and for each fixed n the pairs (x, D y) solve        *)
(* Y^n = D^(n-1) (x^2 + C), which has only finitely many solutions           *)
(* (SUPERELLIPTIC_MONIC). So |y| and m are bounded, and n is bounded by the  *)
(* growth |u_n| >= (n - 1) / 2 of the sequences with |P| >= Q + 2            *)
(* (LUCAS_SEQUENCE_GROWTH, after P |-> -P by LUCAS_SEQUENCE_NEG); the other  *)
(* sequences with Delta <> 0 (Q = 1 and |P| <= 1, or Q = -1 and P = 0) are   *)
(* periodic with |u_n| <= 1 and |v_n| <= 2, so they contain no such perfect  *)
(* power at all (LUCAS_SEQUENCE_DEFINITE, LUCAS_SEQUENCE_PERIODIC). For      *)
(* x^k + D the k roots of z^k = -D are simple and distinct                   *)
(* (CARD_COMPLEX_ROOTS), so SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS applies    *)
(* for k >= 3; the case k = 2 is SQUARE_PLUS_POW_FINITE.                     *)
(*                                                                           *)
(* Main results: LUCAS_PERFECT_POWERS_FINITE,                                *)
(* LUCAS_COMPANION_PERFECT_POWERS_FINITE, FIBONACCI_PERFECT_POWERS_FINITE,   *)
(* PELL_PERFECT_POWERS_FINITE, LUCAS_NUMBERS_PERFECT_POWERS_FINITE,          *)
(* LUCAS_NUM_PERFECT_POWERS_FINITE, POW_PLUS_POW_FINITE,                     *)
(* SQUARE_PLUS_MUL_POW_FINITE; generic lemmas CARD_COMPLEX_ROOTS,            *)
(* INTEGER_ABS_LE_SQUARE_LT, REAL_ABS_POW_GE_4, PERFECT_POWERS_FINITE_NUM,   *)
(* POW_PLUS_POLY_DATA; helper names LUCAS_SEQUENCE_*.                        *)
(*                                                                           *)
(* Uses: Baker/schinzel_general.ml (SCHINZEL_TIJDEMAN_GENERAL_MONIC,         *)
(* SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS, SQUARE_PLUS_POW_FINITE),           *)
(* Baker/prime_factors.ml (SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA),          *)
(* Baker/superell.ml (SUPERELLIPTIC_MONIC); library:                         *)
(* Examples/gcdrecurrence.ml (fib), Multivariate/transcendentals.ml          *)
(* (EXISTS_COMPLEX_ROOT, CARD_COMPLEX_ROOTS_UNITY,                           *)
(* FINITE_COMPLEX_ROOTS_UNITY, COMPLEX_ROOT_POLYFUN),                        *)
(* FINITE_PRODUCT_DEPENDENT, FINITE_IMAGE_INJ, UPPER_BOUND_FINITE_SET_REAL.  *)
(* ========================================================================= *)

needs "Examples/gcdrecurrence.ml";;
needs "Baker/schinzel_general.ml";;

(* Examples/gcdrecurrence.ml (the Fibonacci numbers fib) ends in          *)
(* prioritize_int(): restore the project default.                         *)

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The equations x^2 + C = D y^n (n >= 3) and x^k + D = y^n: the monic       *)
(* form of the Schinzel-Tijdeman theorem bounds n, SUPERELLIPTIC_MONIC       *)
(* handles each fixed n; the k distinct roots of x^k + D.                    *)
(* ------------------------------------------------------------------------- *)

let SQUARE_PLUS_MUL_POW_FINITE = prove
 (`!C D. integer C /\ integer D /\ ~(C = &0) /\ ~(D = &0)
         ==> FINITE {x,y,n | integer x /\ integer y /\ &2 <= abs y /\
                             3 <= n /\ x pow 2 + C = D * y pow n}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(SPEC `C:real` SCHINZEL_TIJDEMAN_GEN_SQUARE_PLUS_DATA)) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`csqrt(Cx(--C))`,`w:complex`) THEN GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `\i. if i = 0 then C else if i = 1 then &0 else &1`;
                 `D:real`; `w:complex`; `--w:complex`]
    SCHINZEL_TIJDEMAN_GENERAL_MONIC) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_EQ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `M:num` (LABEL_TAC "M")) THEN
  MP_TAC(ISPECL
   [`\(n:num) (p:real#real). (FST p, SND p, n)`; `3..M`;
    `\n. {(x,y) | integer x /\ integer y /\ x pow 2 + C = D * y pow n}`]
   FINITE_PRODUCT_DEPENDENT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `k:num` SUBST_ALL_TAC o MATCH_MP
     (MESON[ARITH_RULE `3 <= n ==> n = (n - 1) + 1`]
       `3 <= n ==> ?k. n = k + 1`)) THEN
    MP_TAC(ISPECL [`2`; `\i. if i = 0 then C else if i = 1 then &0 else &1`;
                   `k + 1`; `(D:real) pow k`; `w:complex`; `--w:complex`]
      SUPERELLIPTIC_MONIC) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[ARITH_EQ; INTEGER_POW; REAL_POW_NZ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{p | (\p:real#real. (FST p, D * SND p)) p IN
                     {(x,y) | integer x /\ integer y /\
                              y pow (k + 1) = D pow k * (x pow 2 + C)}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND] THEN
      ASM_SIMP_TAC[REAL_EQ_MUL_LCANCEL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM;
                FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real`; `D * y:real`] THEN
    ASM_SIMP_TAC[INTEGER_MUL] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; REAL_POW_MUL] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  DISCH_THEN(MATCH_MP_TAC o
             MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `n:num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `(x:real,y:real)`] THEN
  REWRITE_TAC[FST; SND; IN_NUMSEG; IN_ELIM_PAIR_THM] THEN
  ASM_REWRITE_TAC[] THEN
  REMOVE_THEN "M" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `y:real`] THEN ASM_REWRITE_TAC[]);;

let CARD_COMPLEX_ROOTS = prove
 (`!n a. 1 <= n /\ ~(a = Cx(&0)) ==> CARD {z | z pow n = a} = n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:complex`; `n:num`] EXISTS_COMPLEX_ROOT) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `w:complex`)] THEN
  SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `Cx(&0) pow n = a` THEN
    ASM_SIMP_TAC[COMPLEX_POW_ZERO; LE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{z | z pow n = a} = IMAGE (\u. w * u) {u | u pow n = Cx(&1)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:complex` THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(z:complex) / w` THEN
      ASM_SIMP_TAC[COMPLEX_DIV_LMUL; COMPLEX_POW_DIV] THEN
      MATCH_MP_TAC COMPLEX_DIV_REFL THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[COMPLEX_POW_EQ_0];
      DISCH_THEN(X_CHOOSE_THEN `v:complex` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_MUL_RID]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:complex. w * u`; `{u:complex | u pow n = Cx(&1)}`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_COMPLEX_ROOTS_UNITY; LE_1; COMPLEX_EQ_MUL_LCANCEL];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CARD_COMPLEX_ROOTS_UNITY]]);;

let POW_PLUS_POLY_DATA = prove
 (`!k D. 1 <= k
         ==> (!x. sum(0..k) (\i. (if i = 0 then D else if i = k then &1
                                  else &0) * x pow i) = x pow k + D) /\
             (!z. vsum(0..k) (\i. Cx(if i = 0 then D else if i = k then &1
                                     else &0) * z pow i) = Cx(&0) <=>
                  z pow k = Cx(--D)) /\
             (!z. vsum(1..k) (\i. Cx(&i * (if i = 0 then D
                                           else if i = k then &1 else &0)) *
                                  z pow (i - 1)) =
                  Cx(&k) * z pow (k - 1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THEN GEN_TAC THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_RIGHT; LE_1; LE_0] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[LE_1; ARITH_RULE `1 <= n /\ 1 <= i /\ i <= n - 1
                                   ==> ~(i = n)`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; SUM_0; real_pow] THEN REAL_ARITH_TAC;
    MP_TAC(SPECL [`k:num`; `z:complex`; `Cx(--D)`] COMPLEX_ROOT_POLYFUN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[GEN_ALL(ISPECL [`b:bool`; `Cx`] COND_RAND);
                CX_NEG; COMPLEX_NEG_NEG];
    ASM_SIMP_TAC[VSUM_CLAUSES_RIGHT; LE_1; LE_0] THEN
    ASM_SIMP_TAC[LE_1; ARITH_RULE `1 <= n /\ 1 <= i /\ i <= n - 1
                                   ==> ~(i = n)`] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_0; VECTOR_ADD_LID]]);;

let POW_PLUS_POW_FINITE = prove
 (`!k D. 2 <= k /\ integer D /\ ~(D = &0)
         ==> FINITE {x,y,n | integer x /\ integer y /\ &2 <= abs y /\
                             2 <= n /\ x pow k + D = y pow n}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k = 2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC SQUARE_PLUS_POW_FINITE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`k:num`; `D:real`] POW_PLUS_POLY_DATA) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `\i. if i = 0 then D else if i = k then &1 else &0`;
                 `2`] SCHINZEL_TIJDEMAN_FINITE_SIMPLE_ROOTS) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGER_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `{z | z pow k = Cx(--D) /\ ~(Cx(&k) * z pow (k - 1) = Cx(&0))} =
      {z | z pow k = Cx(--D)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN
      EQ_TAC THENL [SIMP_TAC[]; DISCH_TAC THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; REAL_OF_NUM_EQ; COMPLEX_POW_EQ_0] THEN
      REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; DISJ1_TAC THEN DISCH_THEN SUBST_ALL_TAC] THEN
      UNDISCH_TAC `Cx(&0) pow k = Cx(--D)` THEN
      ASM_SIMP_TAC[COMPLEX_POW_ZERO; ARITH_RULE `2 <= k ==> ~(k = 0)`] THEN
      REWRITE_TAC[CX_INJ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `Cx(--D)`] CARD_COMPLEX_ROOTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[CX_INJ] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE_THM] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lucas sequences w(n+2) = P w(n+1) - Q w(n): integer values, the           *)
(* invariant w(n+1)^2 - P w(n+1) w(n) + Q w(n)^2 = Q^n E, the sign change    *)
(* P |-> -P, growth for P >= Q + 2 and the periodic cases.                   *)
(* ------------------------------------------------------------------------- *)

let LUCAS_SEQUENCE_INTEGER = prove
 (`!P Q (w:num->real).
        integer P /\ integer Q /\ integer(w 0) /\ integer(w 1) /\
        (!n. w(n + 2) = P * w(n + 1) - Q * w n)
        ==> !n. integer(w n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. integer((w:num->real) n) /\ integer(w(n + 1))`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED]);;

let LUCAS_SEQUENCE_INVARIANT = prove
 (`!P Q (w:num->real).
        (!n. w(n + 2) = P * w(n + 1) - Q * w n)
        ==> !n. w(n + 1) pow 2 - P * w(n + 1) * w n + Q * w n pow 2 =
                Q pow n * (w 1 pow 2 - P * w 1 * w 0 + Q * w 0 pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_LID];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[real_pow; ARITH_RULE `SUC n + 1 = n + 2`] THEN
    ASM_REWRITE_TAC[ADD1] THEN CONV_TAC REAL_RING]);;

let LUCAS_SEQUENCE_SQUARE_IDENTITY = prove
 (`!P Q (w:num->real) n.
        (!n. w(n + 2) = P * w(n + 1) - Q * w n)
        ==> (&2 * w(n + 1) - P * w n) pow 2 - (P pow 2 - &4 * Q) * w n pow 2 =
            &4 * Q pow n * (w 1 pow 2 - P * w 1 * w 0 + Q * w 0 pow 2)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP LUCAS_SEQUENCE_INVARIANT) THEN
  CONV_TAC REAL_RING);;

let LUCAS_SEQUENCE_NEG = prove
 (`!P Q (w:num->real) c.
        (!n. w(n + 2) = P * w(n + 1) - Q * w n)
        ==> !n. c * (-- &1) pow (n + 2) * w(n + 2) =
                --P * (c * (-- &1) pow (n + 1) * w(n + 1)) -
                Q * (c * (-- &1) pow n * w n)`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_POW_ADD] THEN
  CONV_TAC REAL_RING);;

let LUCAS_SEQUENCE_GROWTH = prove
 (`!P Q (w:num->real).
        &2 + Q <= P /\ -- &1 <= Q /\
        &0 <= w 0 /\ w 0 <= w 1 /\ &1 <= w 1 /\
        (!n. w(n + 2) = P * w(n + 1) - Q * w n)
        ==> !n. &0 <= w n /\ &n <= &2 * w n + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. &0 <= w n /\ w n <= w(n + 1) /\ &1 <= w(n + 1) /\
        &n <= &2 * w n + &1 /\ &(n + 1) <= &2 * w(n + 1) + &1`
   (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THENL
   [ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  REWRITE_TAC[ARITH_RULE `SUC n + 1 = n + 2`; ADD1] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (P - Q - &2) * (w:num->real)(n + 1) /\
                &0 <= (Q + &1) * (w(n + 1) - w n)`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC);;

let LUCAS_SEQUENCE_CASES = prove
 (`!P Q. integer P /\ (Q = &1 \/ Q = -- &1)
         ==> &2 + Q <= abs P \/ (Q = &1 /\ abs P <= &1) \/
             (Q = -- &1 /\ P = &0) \/ P pow 2 = &4 * Q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `k:num`) DISJ_CASES_TAC) THEN
  ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  ONCE_REWRITE_TAC[GSYM REAL_ABS_ZERO] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_POW; REAL_OF_NUM_EQ] THENL
   [ASM_CASES_TAC `k = 2` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ARITH_TAC]);;

let LUCAS_SEQUENCE_DEFINITE = prove
 (`!P Q (w:num->real) E.
        Q = &1 /\ P pow 2 <= &1 /\
        (!n. w(n + 1) pow 2 - P * w(n + 1) * w n + Q * w n pow 2 =
             Q pow n * E)
        ==> !n. &3 * w n pow 2 <= &4 * E`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= (&2 * (w:num->real)(n + 1) - P * w n) pow 2 /\
    &0 <= (&1 - P pow 2) * w n pow 2`
  MP_TAC THENL
   [REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC);;

let LUCAS_SEQUENCE_PERIODIC = prove
 (`!(w:num->real) B.
        abs(w 0) <= B /\ abs(w 1) <= B /\ (!n. w(n + 2) = w n)
        ==> !n. abs(w n) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!n. abs((w:num->real) n) <= B /\ abs(w(n + 1)) <= B`
   (fun th -> REWRITE_TAC[th]) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
  ASM_REWRITE_TAC[ADD1; ARITH_RULE `(n + 1) + 1 = n + 2`]);;

let INTEGER_ABS_LE_SQUARE_LT = prove
 (`!x k. integer x /\ x pow 2 < (&k + &1) pow 2 ==> abs x <= &k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[integer] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `j:num`) MP_TAC) THEN
  REWRITE_TAC[GSYM REAL_LT_SQUARE_ABS] THEN
  ASM_REWRITE_TAC[REAL_ARITH `abs(&k + &1) = &k + &1`] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  ARITH_TAC);;

let LUCAS_SEQUENCE_Q_INTEGER = prove
 (`!Q. (Q = &1 \/ Q = -- &1) ==> integer Q /\ -- &1 <= Q`,
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  REAL_ARITH_TAC);;

let LUCAS_SEQUENCE_Q_POW = prove
 (`!Q n. (Q = &1 \/ Q = -- &1) ==> Q pow n = &1 \/ Q pow n = -- &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_POW_ONE; REAL_POW_NEG] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let REAL_ABS_POW_GE_4 = prove
 (`!y m. &2 <= abs y /\ 2 <= m ==> &4 <= abs(y pow m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_POW] THEN
  TRANS_TAC REAL_LE_TRANS `&2 pow m` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&2 pow 2` THEN CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let LUCAS_SEQUENCE_U_BOUNDED_OR_GROWTH = prove
 (`!P Q (u:num->real).
        integer P /\ (Q = &1 \/ Q = -- &1) /\ ~(P pow 2 = &4 * Q) /\
        u 0 = &0 /\ u 1 = &1 /\ (!n. u(n + 2) = P * u(n + 1) - Q * u n)
        ==> (!n. abs(u n) <= &1) \/ (!n. &n <= &2 * abs(u n) + &1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LUCAS_SEQUENCE_Q_INTEGER) THEN
  SUBGOAL_THEN `!n. integer((u:num->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LUCAS_SEQUENCE_INTEGER THEN
    MAP_EVERY EXISTS_TAC [`P:real`; `Q:real`] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:real`; `Q:real`] LUCAS_SEQUENCE_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN DISJ_CASES_TAC(REAL_ARITH `&0 <= P \/ P < &0`) THENL
     [MP_TAC(SPECL [`P:real`; `Q:real`; `u:num->real`]
        LUCAS_SEQUENCE_GROWTH) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      STRIP_TAC THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`--P:real`; `Q:real`;
                  `\n. -- &1 * (-- &1) pow n * (u:num->real) n`]
      LUCAS_SEQUENCE_GROWTH) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC LUCAS_SEQUENCE_NEG THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x:real) = abs y ==> &0 <= x /\ n <= &2 * x + &1
                              ==> n <= &2 * abs y + &1`) THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID];
    DISJ1_TAC THEN
    MP_TAC(SPECL [`P:real`; `Q:real`; `u:num->real`;
                  `(u:num->real) 1 pow 2 - P * u 1 * u 0 + Q * u 0 pow 2`]
      LUCAS_SEQUENCE_DEFINITE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LUCAS_SEQUENCE_INVARIANT THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGER_ABS_LE_SQUARE_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    DISJ1_TAC THEN MATCH_MP_TAC LUCAS_SEQUENCE_PERIODIC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    ASM_MESON_TAC[]]);;

let LUCAS_SEQUENCE_V_GROWTH = prove
 (`!P Q (v:num->real).
        &2 + Q <= P /\ (Q = &1 \/ Q = -- &1) /\
        v 0 = &2 /\ v 1 = P /\ (!n. v(n + 2) = P * v(n + 1) - Q * v n)
        ==> !n. &n <= &2 * abs(v n) + &2`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LUCAS_SEQUENCE_Q_INTEGER) THEN
  SUBGOAL_THEN `(v:num->real) 2 = P * P - Q * &2` ASSUME_TAC THENL
   [MP_TAC(SPEC `0` (ASSUME
     `!n. (v:num->real)(n + 2) = P * v(n + 1) - Q * v n`)) THEN
    REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&2 + Q) * P <= P * P` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P /\ P <= P * P - Q * &2 /\ &1 <= P * P - Q * &2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:real`; `Q:real`; `\n. (v:num->real)(n + 1)`]
    LUCAS_SEQUENCE_GROWTH) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `(n + 2) + 1 = (n + 1) + 2`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `n:num` THEN
  DISJ_CASES_THEN2 SUBST1_TAC (X_CHOOSE_THEN `k:num` SUBST1_TAC)
   (SPEC `n:num` num_CASES) THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

let LUCAS_SEQUENCE_V_BOUNDED_OR_GROWTH = prove
 (`!P Q (v:num->real).
        integer P /\ (Q = &1 \/ Q = -- &1) /\
        v 0 = &2 /\ v 1 = P /\ (!n. v(n + 2) = P * v(n + 1) - Q * v n)
        ==> (!n. abs(v n) <= &2) \/
            ~(P pow 2 = &4 * Q) /\ (!n. &n <= &2 * abs(v n) + &2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LUCAS_SEQUENCE_Q_INTEGER) THEN
  SUBGOAL_THEN `!n. integer((v:num->real) n)` ASSUME_TAC THENL
   [MATCH_MP_TAC LUCAS_SEQUENCE_INTEGER THEN
    MAP_EVERY EXISTS_TAC [`P:real`; `Q:real`] THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:real`; `Q:real`] LUCAS_SEQUENCE_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ2_TAC THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      MP_TAC(SPECL [`2`; `&2 + Q`; `abs P`] REAL_POW_LE2) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPEC `Q:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISJ_CASES_TAC(REAL_ARITH `&0 <= P \/ P < &0`) THENL
     [MP_TAC(SPECL [`P:real`; `Q:real`; `v:num->real`]
        LUCAS_SEQUENCE_V_GROWTH) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`--P:real`; `Q:real`;
                  `\n. &1 * (-- &1) pow n * (v:num->real) n`]
      LUCAS_SEQUENCE_V_GROWTH) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LUCAS_SEQUENCE_NEG THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID];
    DISJ1_TAC THEN
    MP_TAC(SPECL [`P:real`; `Q:real`; `v:num->real`;
                  `(v:num->real) 1 pow 2 - P * v 1 * v 0 + Q * v 0 pow 2`]
      LUCAS_SEQUENCE_DEFINITE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
        MATCH_MP_TAC REAL_POW_1_LE THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LUCAS_SEQUENCE_INVARIANT THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_FORALL THEN
    X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC INTEGER_ABS_LE_SQUARE_LT THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `P:real` REAL_LE_POW_2) THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    DISJ1_TAC THEN MATCH_MP_TAC LUCAS_SEQUENCE_PERIODIC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    GEN_TAC THEN REAL_ARITH_TAC;
    DISJ1_TAC THEN
    SUBGOAL_THEN `Q = &1` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(SPEC `P:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!n. (v:num->real) n pow 2 = &4` ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
      MP_TAC(SPECL [`P:real`; `&1`; `v:num->real`; `n:num`]
        LUCAS_SEQUENCE_SQUARE_IDENTITY) THEN
      ASM_REWRITE_TAC[ADD1; REAL_POW_ONE] THEN
      UNDISCH_TAC `(v:num->real) n pow 2 = &4` THEN
      UNDISCH_TAC `P pow 2 = &4 * &1` THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC INTEGER_ABS_LE_SQUARE_LT THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Perfect powers in Lucas sequences with Q = 1 or Q = -1: the finiteness    *)
(* core (from x^2 + C = D y^n) and the sequences U and V.                    *)
(* ------------------------------------------------------------------------- *)

let LUCAS_SEQUENCE_POWERS_CORE = prove
 (`!(w:num->real) D C1 C2 c.
        integer D /\ ~(D = &0) /\ integer C1 /\ ~(C1 = &0) /\
        integer C2 /\ ~(C2 = &0) /\
        (!n. &n <= &2 * abs(w n) + c) /\
        (!n. ?X. integer X /\
                 (X pow 2 + C1 = D * w n pow 2 \/
                  X pow 2 + C2 = D * w n pow 2))
        ==> FINITE {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\
                            w n = y pow m}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C2:real`; `D:real`] SQUARE_PLUS_MUL_POW_FINITE) THEN
  MP_TAC(SPECL [`C1:real`; `D:real`] SQUARE_PLUS_MUL_POW_FINITE) THEN
  ASM_REWRITE_TAC[IMP_IMP; GSYM FINITE_UNION] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ISPEC
    `\p:real#real#num. (FST(SND p), SND(SND p) DIV 2)` FINITE_IMAGE)) THEN
  DISCH_THEN(fun th ->
    let t = rand(concl th) in
    ASSUME_TAC th THEN ABBREV_TAC(mk_eq(mk_var("YM",type_of t),t))) THEN
  FIRST_ASSUM(MP_TAC o SPEC `\p:real#num. abs(FST p) pow (SND p)` o
    MATCH_MP UPPER_BOUND_FINITE_SET_REAL) THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(SPEC `&2 * B + c` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `NB:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(0..NB) CROSS (YM:real#num->bool)` THEN
  ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE_THM; IN_CROSS;
              IN_NUMSEG; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:real`; `m:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real,m:num) IN (YM:real#num->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `X:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq")) o SPEC `n:num`) THEN
    EXPAND_TAC "YM" THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`X:real`; `y:real`; `2 * m`] THEN
    SIMP_TAC[FST; SND; PAIR_EQ; DIV_MULT; ARITH_EQ] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_TRIPLE_THM] THEN
    SUBGOAL_THEN `3 <= 2 * m` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real) pow (2 * m) = (y pow m) pow 2` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW; MULT_SYM]; ALL_TAC] THEN
    REMOVE_THEN "eq" DISJ_CASES_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(y:real,m:num)`) THEN
  ASM_REWRITE_TAC[FST; SND] THEN DISCH_TAC THEN
  MP_TAC(SPEC `n:num` (ASSUME `!n. &n <= &2 * abs((w:num->real) n) + c`)) THEN
  REWRITE_TAC[ASSUME `(w:num->real) n = y pow m`; REAL_ABS_POW;
              GSYM REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `&2 * B + c <= &NB` THEN
  UNDISCH_TAC `abs(y:real) pow m <= B` THEN REAL_ARITH_TAC);;

let LUCAS_PERFECT_POWERS_FINITE = prove
 (`!P Q (u:num->real).
        integer P /\ (Q = &1 \/ Q = -- &1) /\ ~(P pow 2 = &4 * Q) /\
        u 0 = &0 /\ u 1 = &1 /\ (!n. u(n + 2) = P * u(n + 1) - Q * u n)
        ==> FINITE {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\
                            u n = y pow m}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LUCAS_SEQUENCE_U_BOUNDED_OR_GROWTH) THEN
  POP_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LUCAS_SEQUENCE_Q_INTEGER) THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [MATCH_MP_TAC(MESON[FINITE_EMPTY]
     `s = {} ==> FINITE(s:num#real#num->bool)`) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM;
                IN_ELIM_TRIPLE_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real`; `m:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`y:real`; `m:num`] REAL_ABS_POW_GE_4) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LUCAS_SEQUENCE_POWERS_CORE THEN
  MAP_EVERY EXISTS_TAC [`P pow 2 - &4 * Q`; `-- &4`; `&4`; `&1`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED];
    UNDISCH_TAC `~(P pow 2 = &4 * Q)` THEN REAL_ARITH_TAC;
    SIMP_TAC[INTEGER_CLOSED];
    REAL_ARITH_TAC;
    SIMP_TAC[INTEGER_CLOSED];
    REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  EXISTS_TAC `&2 * (u:num->real)(n + 1) - P * u n` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `!n. integer((u:num->real) n)` ASSUME_TAC THENL
     [MATCH_MP_TAC LUCAS_SEQUENCE_INTEGER THEN
      MAP_EVERY EXISTS_TAC [`P:real`; `Q:real`] THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED];
      ASM_SIMP_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:real`; `Q:real`; `u:num->real`; `n:num`]
    LUCAS_SEQUENCE_SQUARE_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`Q:real`; `n:num`] LUCAS_SEQUENCE_Q_POW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

let LUCAS_COMPANION_PERFECT_POWERS_FINITE = prove
 (`!P Q (v:num->real).
        integer P /\ (Q = &1 \/ Q = -- &1) /\
        v 0 = &2 /\ v 1 = P /\ (!n. v(n + 2) = P * v(n + 1) - Q * v n)
        ==> FINITE {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\
                            v n = y pow m}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LUCAS_SEQUENCE_V_BOUNDED_OR_GROWTH) THEN
  POP_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP LUCAS_SEQUENCE_Q_INTEGER) THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC(MESON[FINITE_EMPTY]
     `s = {} ==> FINITE(s:num#real#num->bool)`) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; FORALL_PAIR_THM;
                IN_ELIM_TRIPLE_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `y:real`; `m:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`y:real`; `m:num`] REAL_ABS_POW_GE_4) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LUCAS_SEQUENCE_POWERS_CORE THEN
  MAP_EVERY EXISTS_TAC
   [`P pow 2 - &4 * Q`; `&4 * (P pow 2 - &4 * Q)`;
    `-- &4 * (P pow 2 - &4 * Q)`; `&2`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGER_CLOSED];
    UNDISCH_TAC `~(P pow 2 = &4 * Q)` THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGER_CLOSED];
    UNDISCH_TAC `~(P pow 2 = &4 * Q)` THEN REAL_ARITH_TAC;
    ASM_SIMP_TAC[INTEGER_CLOSED];
    UNDISCH_TAC `~(P pow 2 = &4 * Q)` THEN REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `n:num` THEN
  EXISTS_TAC `&2 * (v:num->real)(n + 1) - P * v n` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `!n. integer((v:num->real) n)` ASSUME_TAC THENL
     [MATCH_MP_TAC LUCAS_SEQUENCE_INTEGER THEN
      MAP_EVERY EXISTS_TAC [`P:real`; `Q:real`] THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED];
      ASM_SIMP_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`P:real`; `Q:real`; `v:num->real`; `n:num`]
    LUCAS_SEQUENCE_SQUARE_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`Q:real`; `n:num`] LUCAS_SEQUENCE_Q_POW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Natural number forms: u(n+2) = p u(n+1) + u(n), the Fibonacci, Pell       *)
(* and Lucas numbers.                                                        *)
(* ------------------------------------------------------------------------- *)

let PERFECT_POWERS_FINITE_NUM = prove
 (`!u:num->num.
        FINITE {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\
                        &(u n) = y pow m}
        ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ u n = y EXP m}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `{q | (\q:num#num#num. (FST q, &(FST(SND q)):real, SND(SND q))) q IN
         {n,y,m | integer y /\ &2 <= abs y /\ 2 <= m /\
                  &((u:num->num) n) = y pow m}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ; FST; SND; REAL_OF_NUM_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_TRIPLE_THM; IN_ELIM_THM;
              FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `y:num`; `m:num`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `&y:real`; `m:num`] THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM; REAL_OF_NUM_LE;
                  REAL_OF_NUM_POW]);;

let LUCAS_NUM_PERFECT_POWERS_FINITE = prove
 (`!p u. u 0 = 0 /\ u 1 = 1 /\ (!n. u(n + 2) = p * u(n + 1) + u n)
         ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ u n = y EXP m}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERFECT_POWERS_FINITE_NUM THEN
  MP_TAC(ISPECL [`&p:real`; `-- &1:real`; `\n. &((u:num->num) n):real`]
    LUCAS_PERFECT_POWERS_FINITE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_OF_NUM_POW] THEN
  REWRITE_TAC[REAL_ARITH `~(&n = &4 * -- &1)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  REAL_ARITH_TAC);;

let FIBONACCI_PERFECT_POWERS_FINITE = prove
 (`FINITE {n,y,m | 2 <= m /\ 2 <= y /\ fib n = y EXP m}`,
  MATCH_MP_TAC LUCAS_NUM_PERFECT_POWERS_FINITE THEN EXISTS_TAC `1` THEN
  REWRITE_TAC[fib; MULT_CLAUSES]);;

let PELL_PERFECT_POWERS_FINITE = prove
 (`!u. u 0 = 0 /\ u 1 = 1 /\ (!n. u(n + 2) = 2 * u(n + 1) + u n)
       ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ u n = y EXP m}`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC LUCAS_NUM_PERFECT_POWERS_FINITE THEN
  EXISTS_TAC `2` THEN ASM_REWRITE_TAC[]);;

let LUCAS_NUMBERS_PERFECT_POWERS_FINITE = prove
 (`!v. v 0 = 2 /\ v 1 = 1 /\ (!n. v(n + 2) = v(n + 1) + v n)
       ==> FINITE {n,y,m | 2 <= m /\ 2 <= y /\ v n = y EXP m}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERFECT_POWERS_FINITE_NUM THEN
  MP_TAC(ISPECL [`&1:real`; `-- &1:real`; `\n. &((v:num->num) n):real`]
    LUCAS_COMPANION_PERFECT_POWERS_FINITE) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC);;

prioritize_num();;
