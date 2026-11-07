(* ========================================================================= *)
(* Elementary number theory for the Catalan equation x^p - y^q = 1.          *)
(*                                                                           *)
(* Purpose: Tijdeman, Acta Arith 29 (1976), sec 5, formulas (11) and (12):   *)
(*   CATALAN_FACTOR_MINUS: p odd prime, x^p = y^q + 1, x >= 2                *)
(*     ==> x - 1 = rho^q  or  p (x - 1) = rho^q,   rho >= 1                  *)
(*   CATALAN_FACTOR_PLUS:  q odd prime, x^p = y^q + 1                        *)
(*     ==> y + 1 = sg^p  or  q (y + 1) = sg^p,   sg >= 1                     *)
(* Route: one integer lemma for z^n - 1 = (z - 1) Phi(z), n odd, with        *)
(* Phi(z) == n mod (z - 1) and, when n divides z - 1, Phi(z) == n mod n^2    *)
(* (used with z = x and z = -y), plus an abstract coprime-factor lemma over  *)
(* the naturals built on COPRIME_POW. The geometric sums are proved under    *)
(* prioritize_int; the file ends with prioritize_real then prioritize_num,   *)
(* which restores the project default (& is num->real again).                *)
(*                                                                           *)
(* Main results: CATALAN_FACTOR_MINUS, CATALAN_FACTOR_PLUS;                  *)
(*   CATALAN_GEOM_ODD, CATALAN_FACTOR_ABSTRACT.                              *)
(*                                                                           *)
(* Uses: Library/prime.ml (COPRIME_POW) and integer arithmetic.              *)
(* ========================================================================= *)

needs "Library/prime.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Geometric sums over the integers, modulo (z - 1) and (z - 1)^2.           *)
(* With d = z - 1: Phi_n(z) == n + d n (n - 1) / 2  (mod d^2).               *)
(* Phi is given existentially, built by the Horner step Phi <- 1 + z Phi.    *)
(* ------------------------------------------------------------------------- *)

prioritize_int();;

let CATALAN_GEOM_CONG_STEP = prove
 (`!z f t n.
        (f == n + (z - &1) * t) (mod ((z - &1) pow 2))
        ==> (&1 + z * f == (n + &1) + (z - &1) * (t + n))
            (mod ((z - &1) pow 2))`,
  INTEGER_TAC);;

let CATALAN_GEOM_CONG = prove
 (`!z n. ?f t. (z - &1) * f = z pow n - &1 /\
               &2 * t = &n * (&n - &1) /\
               (f == &n + (z - &1) * t) (mod ((z - &1) pow 2))`,
  GEN_TAC THEN INDUCT_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&0:int`; `&0:int`] THEN
    REWRITE_TAC[INT_POW] THEN CONV_TAC INTEGER_RULE;
    FIRST_X_ASSUM(X_CHOOSE_THEN `f:int` (X_CHOOSE_THEN `t:int`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`&1 + z * f:int`; `t + &n:int`] THEN
    REWRITE_TAC[INT_POW; GSYM INT_OF_NUM_SUC] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(z - &1) * f = z pow n - &1` THEN CONV_TAC INT_RING;
      UNDISCH_TAC `&2 * t = &n * (&n - &1)` THEN CONV_TAC INT_RING;
      MATCH_MP_TAC CATALAN_GEOM_CONG_STEP THEN ASM_REWRITE_TAC[]]]);;

let CATALAN_GEOM_ODD = prove
 (`!z n. ODD n
         ==> ?f. (z - &1) * f = z pow n - &1 /\
                 (f == &n) (mod (z - &1)) /\
                 (&n divides (z - &1) ==> (f == &n) (mod (&n pow 2)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`z:int`; `n:num`] CATALAN_GEOM_CONG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:int`; `t:int`] THEN STRIP_TAC THEN
  EXISTS_TAC `f:int` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `k:num` o REWRITE_RULE[ODD_EXISTS]) THEN
  SUBGOAL_THEN `&n = &2 * &k + &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&n:int) divides t` ASSUME_TAC THENL
   [REWRITE_TAC[int_divides] THEN EXISTS_TAC `&k:int` THEN
    UNDISCH_TAC `&2 * t = &n * (&n - &1)` THEN
    UNDISCH_TAC `&n = &2 * &k + &1` THEN CONV_TAC INT_RING;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(f == &n + (z - &1) * t) (mod ((z - &1) pow 2))` THEN
    CONV_TAC INTEGER_RULE;
    MAP_EVERY UNDISCH_TAC
     [`(f == &n + (z - &1) * t) (mod ((z - &1) pow 2))`;
      `(&n:int) divides t`] THEN
    CONV_TAC INTEGER_RULE]);;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Abstract factor lemma: u * f = w^n where every common prime factor of u   *)
(* and f is p (f == p mod u), and f == p mod p^2 when p divides u. Then      *)
(* u or p u is an n-th power: if p does not divide u, u and f are coprime;   *)
(* otherwise f = p g with p not dividing g, and p u, g are coprime.          *)
(* ------------------------------------------------------------------------- *)

let CATALAN_FACTOR_ABSTRACT = prove
 (`!p n u f w.
        prime p /\ u * f = w EXP n /\ (f == p) (mod u) /\
        (p divides u ==> (f == p) (mod (p EXP 2)))
        ==> ?rho. ~(p divides u) /\ u = rho EXP n \/
                  p divides u /\ p * u = rho EXP n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. prime r /\ r divides u /\ r divides f ==> r = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r divides p` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(f == p) (mod u)`; `r divides u`; `r divides f`] THEN
      CONV_TAC NUMBER_RULE;
      ASM_MESON_TAC[DIVIDES_PRIME_PRIME]];
    ALL_TAC] THEN
  ASM_CASES_TAC `p divides u` THENL
   [ALL_TAC;
    MP_TAC(SPECL [`n:num`; `u:num`; `f:num`; `w:num`] COPRIME_POW) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[COPRIME_PRIME_EQ] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `r:num` (X_CHOOSE_THEN `s:num`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `r:num` THEN DISJ1_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]] THEN
  SUBGOAL_THEN `(f == p) (mod (p EXP 2))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `p divides f` MP_TAC THENL
   [UNDISCH_TAC `(f == p) (mod (p EXP 2))` THEN CONV_TAC NUMBER_RULE;
    DISCH_THEN(X_CHOOSE_THEN `g:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides])] THEN
  SUBGOAL_THEN `~(p divides g)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `p EXP 2 divides p EXP 1` MP_TAC THENL
     [REWRITE_TAC[EXP_1] THEN
      MAP_EVERY UNDISCH_TAC
       [`(p * g == p) (mod (p EXP 2))`; `p divides g`] THEN
      CONV_TAC NUMBER_RULE;
      ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `p * u:num`; `g:num`; `w:num`] COPRIME_POW) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[COPRIME_PRIME_EQ] THEN X_GEN_TAC `r:num` THEN
      STRIP_TAC THEN
      ASM_MESON_TAC[PRIME_DIVPROD; DIVIDES_PRIME_PRIME; DIVIDES_LMUL];
      UNDISCH_TAC `u * p * g = w EXP n` THEN CONV_TAC NUM_RING];
    DISCH_THEN(X_CHOOSE_THEN `r:num` (X_CHOOSE_THEN `s:num`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `r:num` THEN DISJ2_TAC THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A small sign lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let CATALAN_INT_QUOT_NONNEG = prove
 (`!a b c:int. &0 < a /\ a * b = c /\ &0 <= c ==> &0 <= b`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`a:int`; `--b:int`] INT_LT_MUL) THEN
  ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Tijdeman (12): x - 1 = rho^q when p does not divide x - 1, and            *)
(* p (x - 1) = rho^q when it does. Here Phi = (x^p - 1) / (x - 1).           *)
(* ------------------------------------------------------------------------- *)

let CATALAN_FACTOR_MINUS_CASES = prove
 (`!p q x y.
        prime p /\ ODD p /\ 1 <= q /\ 2 <= x /\ x EXP p = y EXP q + 1
        ==> ?rho. 1 <= rho /\
                  (~(p divides x - 1) /\ x - 1 = rho EXP q \/
                   p divides x - 1 /\ p * (x - 1) = rho EXP q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&x:int`; `p:num`] CATALAN_GEOM_ODD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&(x - 1):int = &x - &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_OF_NUM_SUB; ARITH_RULE `2 <= x ==> 1 <= x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&x:int) pow p = &y pow q + &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_ADD; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0:int <= f` MP_TAC THENL
   [MATCH_MP_TAC CATALAN_INT_QUOT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`&x - &1:int`; `(&y:int) pow q`] THEN
    ASM_SIMP_TAC[INT_POW_LE; INT_POS] THEN
    UNDISCH_TAC `2 <= x` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    ASM_INT_ARITH_TAC;
    REWRITE_TAC[GSYM INT_OF_NUM_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)] THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x - 1`; `m:num`; `y:num`]
    CATALAN_FACTOR_ABSTRACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[num_congruent; num_divides; GSYM INT_OF_NUM_EQ;
                GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW] THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `rho:num`) THEN EXISTS_TAC `rho:num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= r <=> ~(r = 0)`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC[EXP_ZERO; ARITH_RULE `1 <= q ==> ~(q = 0)`; MULT_EQ_0;
               PRIME_IMP_NZ] THEN
  ASM_ARITH_TAC);;

let CATALAN_FACTOR_MINUS = prove
 (`!p q x y.
        prime p /\ ODD p /\ 1 <= q /\ 2 <= x /\ x EXP p = y EXP q + 1
        ==> ?rho. 1 <= rho /\
                  (x - 1 = rho EXP q \/ p * (x - 1) = rho EXP q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CATALAN_FACTOR_MINUS_CASES) THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tijdeman (11): y + 1 = sg^p when q does not divide y + 1, and             *)
(* q (y + 1) = sg^p when it does. Here (y^q + 1) / (y + 1) = Phi(-y);        *)
(* the hypothesis 1 <= y of CATALAN_FACTOR_PLUS is not needed.               *)
(* ------------------------------------------------------------------------- *)

let CATALAN_FACTOR_PLUS_CASES = prove
 (`!p q x y.
        prime q /\ ODD q /\ 1 <= p /\ x EXP p = y EXP q + 1
        ==> ?sg. 1 <= sg /\
                    (~(q divides y + 1) /\ y + 1 = sg EXP p \/
                     q divides y + 1 /\ q * (y + 1) = sg EXP p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`--(&y):int`; `q:num`] CATALAN_GEOM_ODD) THEN
  ASM_REWRITE_TAC[INT_POW_NEG; GSYM NOT_ODD] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(&x:int) pow p = &y pow q + &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_ADD; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&y + &1) * f:int = &y pow q + &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(--(&y) - &1) * f:int = --(&y pow q) - &1` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0:int <= f` MP_TAC THENL
   [MATCH_MP_TAC CATALAN_INT_QUOT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`&y + &1:int`; `&y pow q + &1:int`] THEN
    ASM_SIMP_TAC[INT_POW_LE; INT_POS;
                 INT_ARITH `&0 <= a:int ==> &0 <= a + &1 /\ &0 < a + &1`];
    REWRITE_TAC[GSYM INT_OF_NUM_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)] THEN
  MP_TAC(SPECL [`q:num`; `p:num`; `y + 1`; `m:num`; `x:num`]
    CATALAN_FACTOR_ABSTRACT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[num_congruent; num_divides; GSYM INT_OF_NUM_EQ;
                GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW;
                GSYM INT_OF_NUM_ADD] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      ASM_INT_ARITH_TAC;
      UNDISCH_TAC `(&m == &q) (mod (--(&y) - &1))` THEN
      CONV_TAC INTEGER_RULE;
      DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (is_imp o concl)) THEN
      UNDISCH_TAC `(&q:int) divides &y + &1` THEN CONV_TAC INTEGER_RULE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `sg:num`) THEN EXISTS_TAC `sg:num` THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= r <=> ~(r = 0)`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN POP_ASSUM MP_TAC THEN
  ASM_SIMP_TAC[EXP_ZERO; ARITH_RULE `1 <= p ==> ~(p = 0)`; MULT_EQ_0;
               PRIME_IMP_NZ] THEN
  ARITH_TAC);;

let CATALAN_FACTOR_PLUS = prove
 (`!p q x y.
        prime q /\ ODD q /\ 1 <= p /\ 1 <= y /\ x EXP p = y EXP q + 1
        ==> ?sg. 1 <= sg /\
                    (y + 1 = sg EXP p \/ q * (y + 1) = sg EXP p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `x:num`; `y:num`]
    CATALAN_FACTOR_PLUS_CASES) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* Restore the default of the project files: & is num->real by default and
   the arithmetic operators are num (as after transcendence.ml and
   prioritize_num). *)
prioritize_real();;
prioritize_num();;
