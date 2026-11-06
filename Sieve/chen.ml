(* ========================================================================= *)
(* Chen's theorem (Goldbach and twin forms).                                 *)
(*                                                                           *)
(*   CHEN_GOLDBACH  ?c N0. &0 < c /\                                         *)
(*                         !N. EVEN N /\ N0 <= N                             *)
(*                             ==> c * &N / log(&N) pow 2 <=                 *)
(*                                 &(CARD {p | prime p /\ p < N /\           *)
(*                                             almost_prime 2 (N - p)})      *)
(* every large even N is p + P2, a prime plus a prime or a product of two    *)
(* primes (almost_prime 2), in >> N / log^2 N ways.  Corollary:              *)
(*   CHEN  ?N0. !N. EVEN N /\ N0 <= N                                        *)
(*              ==> ?p q. prime p /\ almost_prime 2 q /\ p + q = N.          *)
(* The twin form                                                             *)
(*   CHEN_TWIN  ?c x0. &0 < c /\                                             *)
(*                     !x. x0 <= x                                           *)
(*                         ==> c * &x / log(&x) pow 2 <=                     *)
(*                             &(CARD {p | prime p /\ p <= x /\              *)
(*                                         almost_prime 2 (p + 2)})          *)
(* and CHEN_TWIN_INFINITE: there are infinitely many primes p such that      *)
(* p + 2 is a prime or a product of two primes.                              *)
(*                                                                           *)
(* Method.  CHEN_GENERAL (chen_sb.ml) for the Goldbach shift h(N) = N,       *)
(* whose sieve condition GOLDBACH_SIEVE_OK (chen_lower.ml) comes from        *)
(* BOMBIERI_VINOGRADOV; the twin form is the case h = 2 of CHEN_SHIFT and    *)
(* CHEN_SHIFT_INFINITE (chen_shift.ml).                                      *)
(* ========================================================================= *)

needs "Sieve/chen_shift.ml";;

prioritize_num(); prioritize_complex();;

let CHEN_GOLDBACH = prove
 (`?c N0. &0 < c /\
          !N. EVEN N /\ N0 <= N
              ==> c * &N / log(&N) pow 2 <=
                  &(CARD {p | prime p /\ p < N /\ almost_prime 2 (N - p)})`,
  MP_TAC(ISPEC `\N:num. N` CHEN_GENERAL) THEN
  ASM_SIMP_TAC[GOLDBACH_SIEVE_OK; CHEN_A_GEN] THEN
  SUBGOAL_THEN
   `!N. &(CARD {n | n IN chen_A N /\ almost_prime 2 n}) <=
        &(CARD {p | prime p /\ p < N /\ almost_prime 2 (N - p)})`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`N:num`; `almost_prime 2`] SUM_CHEN_A) THEN
    SIMP_TAC[SUM_CONST; FINITE_RESTRICT; GSYM CHEN_A_GEN; FINITE_GCHEN_A;
             REAL_MUL_RID] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_CHEN_PRIMES; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[REAL_LE_TRANS]);;

let CHEN = prove
 (`?N0. !N. EVEN N /\ N0 <= N
            ==> ?p q. prime p /\ almost_prime 2 q /\ p + q = N`,
  X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC)
    CHEN_GOLDBACH THEN
  EXISTS_TAC `N0 + 2` THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c * &N / log(&N) pow 2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `S = {p | prime p /\ p < N /\ almost_prime 2 (N - p)}` THEN
  ASM_CASES_TAC `S:num->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`p:num`; `N - p:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let CHEN_TWIN = prove
 (`?c x0. &0 < c /\
          !x. x0 <= x
              ==> c * &x / log(&x) pow 2 <=
                  &(CARD {p | prime p /\ p <= x /\ almost_prime 2 (p + 2)})`,
  MP_TAC(SPEC `2` CHEN_SHIFT) THEN REWRITE_TAC[ARITH]);;

let CHEN_TWIN_INFINITE = prove
 (`INFINITE {p | prime p /\ almost_prime 2 (p + 2)}`,
  MP_TAC(SPEC `2` CHEN_SHIFT_INFINITE) THEN REWRITE_TAC[ARITH]);;
