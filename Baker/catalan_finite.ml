(* ========================================================================= *)
(* Catalan finiteness (Tijdeman 1976).                                       *)
(*                                                                           *)
(* Purpose: the equation x^m = y^n + 1 has only finitely many solutions in   *)
(* natural numbers x, y >= 1, m, n >= 2. Case analysis on the parity of      *)
(* the exponents:                                                            *)
(*  - n even: no solution at all (LEBESGUE, applied to y^(n/2));             *)
(*  - n odd, m even: with an odd prime q dividing n, X = x^(m/2) and         *)
(*    Y = y^(n/q) solve X^2 = Y^q + 1; KO_CHAO_EXPONENT_BOUND bounds q and   *)
(*    SUPERELLIPTIC_MONIC for X^2 - 1 bounds X, Y for each such q;           *)
(*  - n odd, m odd: with odd primes p, q dividing m, n, X^p = Y^q + 1;       *)
(*    CATALAN_ODD_PRIME_FACTORS_BOUNDED bounds p, q and SUPERELLIPTIC_MONIC  *)
(*    for X^p - 1 bounds X, Y for each such pair.                            *)
(* Finally x <= X, m <= p X (as m/p < 2^(m/p) <= X), and similarly for y,    *)
(* n.                                                                        *)
(*                                                                           *)
(* Main results: CATALAN_FINITE, CATALAN_BOUNDED.                            *)
(*                                                                           *)
(* Uses: Baker/lebesgue.ml (LEBESGUE), Baker/kochao.ml                       *)
(* (KO_CHAO_EXPONENT_BOUND), Baker/superell.ml (SUPERELLIPTIC_MONIC),        *)
(* Baker/tijdeman.ml (CATALAN_ODD_PRIME_FACTORS_BOUNDED), Baker/lemmas.ml    *)
(* (ODD_PRIME_GE_3, UNITY_ROOT_CEXP).                                        *)
(* ========================================================================= *)

needs "Baker/lebesgue.ml";;
needs "Baker/kochao.ml";;
needs "Baker/superell.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The binomial X^N - 1 as an explicit coefficient sequence.                 *)
(* ------------------------------------------------------------------------- *)

let CATALAN_BINOMIAL_SUM = prove
 (`!N (x:real).
     1 <= N
     ==> sum(0..N) (\i. (if i = 0 then -- &1 else if i = N then &1 else &0) *
                        x pow i) = x pow N - &1`,
  REPEAT STRIP_TAC THEN SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[ADD_CLAUSES; real_pow; REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `sum(1..N) (\i. (if i = 0 then -- &1 else if i = N then &1 else &0) *
                   (x:real) pow i) =
    sum(1..N) (\i. if i = N then x pow N else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO];
    REWRITE_TAC[SUM_DELTA; IN_NUMSEG; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let CATALAN_BINOMIAL_VSUM = prove
 (`!N (z:complex).
     1 <= N
     ==> vsum(0..N) (\i. Cx(if i = 0 then -- &1 else if i = N then &1
                            else &0) * z pow i) = z pow N - Cx(&1) /\
         vsum(1..N) (\i. Cx(&i * (if i = 0 then -- &1 else if i = N then &1
                                  else &0)) * z pow (i - 1)) =
         Cx(&N) * z pow (N - 1)`,
  REPEAT STRIP_TAC THENL
   [SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[ADD_CLAUSES; complex_pow; COMPLEX_MUL_RID] THEN
    SUBGOAL_THEN
     `vsum(1..N) (\i. Cx(if i = 0 then -- &1 else if i = N then &1 else &0) *
                      (z:complex) pow i) =
      vsum(1..N) (\i. if i = N then z pow N else vec 0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_VEC_0];
      REWRITE_TAC[VSUM_DELTA; IN_NUMSEG; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING];
    SUBGOAL_THEN
     `vsum(1..N) (\i. Cx(&i * (if i = 0 then -- &1 else if i = N then &1
                               else &0)) * (z:complex) pow (i - 1)) =
      vsum(1..N) (\i. if i = N then Cx(&N) * z pow (N - 1) else vec 0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= i ==> ~(i = 0)`] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO; COMPLEX_MUL_LZERO;
                      COMPLEX_VEC_0];
      REWRITE_TAC[VSUM_DELTA; IN_NUMSEG; LE_REFL] THEN ASM_REWRITE_TAC[]]]);;

let CATALAN_BINOMIAL_ROOT = prove
 (`!N (z:complex).
     1 <= N /\ z pow N = Cx(&1)
     ==> vsum(0..N) (\i. Cx(if i = 0 then -- &1 else if i = N then &1
                            else &0) * z pow i) = Cx(&0) /\
         ~(vsum(1..N) (\i. Cx(&i * (if i = 0 then -- &1 else if i = N then &1
                                    else &0)) * z pow (i - 1)) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z = Cx(&0))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `Cx(&0) pow N = Cx(&1)` THEN
    REWRITE_TAC[COMPLEX_POW_ZERO] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= N ==> ~(N = 0)`; CX_INJ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CATALAN_BINOMIAL_VSUM; COMPLEX_SUB_REFL] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A finite set of real pairs bounds the natural numbers inside it.          *)
(* ------------------------------------------------------------------------- *)

let CATALAN_REAL_PAIRS_BOUND = prove
 (`!S:real#real->bool.
     FINITE S ==> ?B. !x y. (&x,&y) IN S ==> x <= B /\ y <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:real#real. FST z + SND z`; `S:real#real->bool`]
    UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
  MP_TAC(SPEC `c:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `B:num`) THEN EXISTS_TAC `B:num` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&x:real,&y:real)` o
    check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[FST; SND] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  MP_TAC(SPEC `x:num` REAL_POS) THEN MP_TAC(SPEC `y:num` REAL_POS) THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* x^N = y^m + 1 (N >= 2, m >= 3 fixed) has only finitely many solutions:    *)
(* SUPERELLIPTIC_MONIC with f = X^N - 1, simple roots 1 and exp(2 pi i/N).   *)
(* ------------------------------------------------------------------------- *)

let CATALAN_BINOMIAL_BOUND = prove
 (`!N m. 2 <= N /\ 3 <= m
         ==> ?B. !x y. x EXP N = y EXP m + 1 ==> x <= B /\ y <= B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N /\ ~(N = 0)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `N:num` UNITY_ROOT_CEXP) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &N))`,`zeta:complex`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&1) = zeta)` ASSUME_TAC THENL
   [DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `0`]) THEN
    REWRITE_TAC[COMPLEX_POW_ONE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(MATCH_MP CATALAN_BINOMIAL_ROOT
    (CONJ (ASSUME `1 <= N`) (SPEC `N:num` COMPLEX_POW_ONE))) THEN
  MP_TAC(MATCH_MP CATALAN_BINOMIAL_ROOT
    (CONJ (ASSUME `1 <= N`) (ASSUME `(zeta:complex) pow N = Cx(&1)`))) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  MP_TAC(BETA_RULE(ISPECL
   [`N:num`; `\i:num. if i = 0 then --(&1:real) else if i = N then &1 else &0`;
    `m:num`; `&1:real`; `Cx(&1)`; `zeta:complex`] SUPERELLIPTIC_MONIC)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(GEN_TAC THEN REPEAT COND_CASES_TAC) THEN
    SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:num` o MATCH_MP CATALAN_REAL_PAIRS_BOUND) THEN
  EXISTS_TAC `B:num` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[CATALAN_BINOMIAL_SUM] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `real_of_num`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_OF_NUM_ADD] THEN
  REAL_ARITH_TAC);;

let CATALAN_PRIME_PAIR_BOUND = prove
 (`!p q. prime p /\ prime q /\ ODD p /\ ODD q
          ==> ?B. !x y. x EXP p = y EXP q + 1 ==> x <= B /\ y <= B`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CATALAN_BINOMIAL_BOUND THEN
  ASM_MESON_TAC[PRIME_GE_2; ODD_PRIME_GE_3]);;

(* ------------------------------------------------------------------------- *)
(* Bounds for finitely many parameters combine into one bound.               *)
(* ------------------------------------------------------------------------- *)

let CATALAN_UNIFORM_BOUND = prove
 (`!(s:A->bool) (P:A->num->num->bool).
     FINITE s /\ (!a. a IN s ==> ?B. !x y. P a x y ==> x <= B /\ y <= B)
     ==> ?B. !a x y. a IN s /\ P a x y ==> x <= B /\ y <= B`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV
    [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN DISCH_THEN(X_CHOOSE_TAC `b:A->num`) THEN
  MP_TAC(ISPECL [`b:A->num`; `s:A->bool`] UPPER_BOUND_FINITE_SET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:num`) THEN
  EXISTS_TAC `c:num` THEN ASM_MESON_TAC[LE_TRANS]);;

let CATALAN_PRIME_PAIRS_UNIFORM = prove
 (`!M. ?B. !p q x y. prime p /\ prime q /\ ODD p /\ ODD q /\
                     p <= M /\ q <= M /\ x EXP p = y EXP q + 1
                     ==> x <= B /\ y <= B`,
  GEN_TAC THEN
  MP_TAC(ISPECL
   [`(0..M) CROSS (0..M)`;
    `\(pq:num#num) (x:num) (y:num).
        prime(FST pq) /\ prime(SND pq) /\ ODD(FST pq) /\ ODD(SND pq) /\
        x EXP (FST pq) = y EXP (SND pq) + 1`]
   CATALAN_UNIFORM_BOUND) THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_NUMSEG; LE_0; FST; SND] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `prime p /\ prime q /\ ODD p /\ ODD q` THENL
     [MP_TAC(SPECL [`p:num`; `q:num`] CATALAN_PRIME_PAIR_BOUND) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      EXISTS_TAC `0` THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Elementary facts on solutions and exponents.                              *)
(* ------------------------------------------------------------------------- *)

let CATALAN_SOLUTION_GE_2 = prove
 (`!x y m n. 1 <= y /\ 2 <= m /\ x EXP m = y EXP n + 1 ==> 2 <= x /\ 2 <= y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= y EXP n` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= x` ASSUME_TAC THENL
   [ASM_CASES_TAC `x <= 1` THENL
     [MP_TAC(SPECL [`x:num`; `1`; `m:num`] EXP_MONO_LE_IMP) THEN
      ASM_REWRITE_TAC[EXP_ONE] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `y = 1` THENL
   [UNDISCH_TAC `x EXP m = y EXP n + 1` THEN ASM_REWRITE_TAC[EXP_ONE] THEN
    MP_TAC(SPECL [`2`; `x:num`; `m:num`] EXP_MONO_LE_IMP) THEN
    MP_TAC(SPECL [`2`; `2`; `m:num`] LE_EXP) THEN
    ASM_REWRITE_TAC[ARITH] THEN ARITH_TAC;
    ASM_ARITH_TAC]);;

let CATALAN_POWER_RECOVER = prove
 (`!x k. 2 <= x /\ 1 <= k ==> x <= x EXP k /\ k <= x EXP k`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`x:num`; `1`; `k:num`] LE_EXP) THEN
    ASM_SIMP_TAC[EXP_1; ARITH_RULE `2 <= x ==> ~(x = 0) /\ ~(x = 1)`];
    TRANS_TAC LE_TRANS `2 EXP k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN REWRITE_TAC[LT_POW2_REFL];
      MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]]]);;

let CATALAN_ODD_PRIME_FACTOR = prove
 (`!n. ODD n /\ ~(n = 1) ==> ?q. prime q /\ ODD q /\ q divides n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `q divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `ODD(q * c)` THEN REWRITE_TAC[ODD_MULT] THEN MESON_TAC[]);;

let CATALAN_EVEN_EXPONENT = prove
 (`!x y m n. 1 <= y /\ 2 <= m /\ EVEN n ==> ~(x EXP m = y EXP n + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:num` SUBST1_TAC))) THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM EXP_EXP] THEN
  MATCH_MP_TAC LEBESGUE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`; EXP_EQ_0] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Case (b): X^2 = Y^q + 1 (Ko Chao).                                        *)
(* ------------------------------------------------------------------------- *)

let CATALAN_KO_CHAO_BOUND = prove
 (`?B. !q x y. prime q /\ ODD q /\ 1 <= y /\ x EXP 2 = y EXP q + 1
                ==> q <= B /\ x <= B /\ y <= B`,
  X_CHOOSE_TAC `M:num` KO_CHAO_EXPONENT_BOUND THEN
  MP_TAC(ISPECL
   [`0..M`;
    `\q x y. prime q /\ ODD q /\ x EXP 2 = y EXP q + 1`]
   CATALAN_UNIFORM_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `q:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `prime q /\ ODD q` THENL
     [MP_TAC(SPECL [`2`; `q:num`] CATALAN_BINOMIAL_BOUND) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[ODD_PRIME_GE_3; LE_REFL]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `0` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `C:num`) THEN EXISTS_TAC `M + C:num` THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `x:num`; `y:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `2`; `q:num`] CATALAN_SOLUTION_GE_2) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `q <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `y:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x <= C /\ y <= C` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The three cases and the headline.                                         *)
(* ------------------------------------------------------------------------- *)

let CATALAN_EVEN_ODD_BOUND = prove
 (`?B. !x y m n. 1 <= x /\ 1 <= y /\ 2 <= m /\ 2 <= n /\ EVEN m /\ ODD n /\
                 x EXP m = y EXP n + 1
                 ==> x <= B /\ y <= B /\ m <= B /\ n <= B`,
  X_CHOOSE_TAC `C:num` CATALAN_KO_CHAO_BOUND THEN
  EXISTS_TAC `2 * C + C * C` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `m:num`; `n:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `m:num`; `n:num`] CATALAN_SOLUTION_GE_2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `n:num` CATALAN_ODD_PRIME_FACTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `EVEN m` THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `q divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `1 <= m1 /\ 1 <= n1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x EXP m1) EXP 2 = (y EXP n1) EXP q + 1` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `m1:num`] CATALAN_POWER_RECOVER) THEN
  MP_TAC(SPECL [`y:num`; `n1:num`] CATALAN_POWER_RECOVER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `x EXP m1`; `y EXP n1`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `q * n1 <= C * C` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

let CATALAN_ODD_ODD_BOUND = prove
 (`?B. !x y m n. 1 <= x /\ 1 <= y /\ 2 <= m /\ 2 <= n /\ ODD m /\ ODD n /\
                 x EXP m = y EXP n + 1
                 ==> x <= B /\ y <= B /\ m <= B /\ n <= B`,
  X_CHOOSE_TAC `M:num` CATALAN_ODD_PRIME_FACTORS_BOUNDED THEN
  MP_TAC(SPEC `M:num` CATALAN_PRIME_PAIRS_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `C:num`) THEN
  EXISTS_TAC `C + M * C` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `m:num`; `n:num`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:num`; `y:num`; `m:num`; `n:num`] CATALAN_SOLUTION_GE_2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC `m:num` CATALAN_ODD_PRIME_FACTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `n:num` CATALAN_ODD_PRIME_FACTOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`; `x:num`; `y:num`;
                                `p:num`; `q:num`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `p divides m` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:num` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `q divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `n1:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `1 <= m1 /\ 1 <= n1` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= a <=> ~(a = 0)`] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[MULT_CLAUSES]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x EXP m1) EXP p = (y EXP n1) EXP q + 1` ASSUME_TAC THENL
   [REWRITE_TAC[EXP_EXP] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:num`; `m1:num`] CATALAN_POWER_RECOVER) THEN
  MP_TAC(SPECL [`y:num`; `n1:num`] CATALAN_POWER_RECOVER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `q:num`; `x EXP m1`; `y EXP n1`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `p * m1 <= M * C /\ q * n1 <= M * C` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_ARITH_TAC);;

let CATALAN_BOUNDED = prove
 (`?B. !x y m n. 1 <= x /\ 1 <= y /\ 2 <= m /\ 2 <= n /\
                  x EXP m = y EXP n + 1
                  ==> x <= B /\ y <= B /\ m <= B /\ n <= B`,
  X_CHOOSE_TAC `B1:num` CATALAN_ODD_ODD_BOUND THEN
  X_CHOOSE_TAC `B2:num` CATALAN_EVEN_ODD_BOUND THEN
  EXISTS_TAC `B1 + B2:num` THEN
  MAP_EVERY X_GEN_TAC [`x:num`; `y:num`; `m:num`; `n:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `EVEN n` THENL
   [ASM_MESON_TAC[CATALAN_EVEN_EXPONENT]; ALL_TAC] THEN
  SUBGOAL_THEN `ODD n` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
  ASM_CASES_TAC `EVEN m` THENL
   [SUBGOAL_THEN `x <= B2 /\ y <= B2 /\ m <= B2 /\ n <= B2` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    SUBGOAL_THEN `ODD m` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM NOT_EVEN]; ALL_TAC] THEN
    SUBGOAL_THEN `x <= B1 /\ y <= B1 /\ m <= B1 /\ n <= B1` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC]]);;

let CATALAN_FINITE = prove
 (`FINITE {(x,y,m,n) | 1 <= x /\ 1 <= y /\ 2 <= m /\ 2 <= n /\
                        x EXP m = y EXP n + 1}`,
  X_CHOOSE_TAC `B:num` CATALAN_BOUNDED THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(0..B) CROSS (0..B) CROSS (0..B) CROSS (0..B)` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ; IN_CROSS;
              IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[]);;
