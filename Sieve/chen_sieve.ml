(* ========================================================================= *)
(* The sieve set-up for Chen's theorem ([N] 10.3).                           *)
(*                                                                           *)
(* The sifted sets: for a shift h and a size N,                              *)
(*   gchen_A h N = {n | 1 <= n < N, coprime(n,h), |h - n| prime}             *)
(* (chen_dist h n = |h - n|).  h = N gives the Goldbach set chen_A N =       *)
(* {N - p | p < N prime, p not | N} (CHEN_A_GEN); a fixed even h > 0 gives   *)
(* the primes p + h (chen_shift.ml).  The density is                         *)
(* chen_g h p = 1/(p - 1) (p not | h), 0 (p | h), h even; CHEN_G_DIMENSION:  *)
(* the dimension condition of JURKAT_RICHERT holds with a constant L         *)
(* independent of h.                                                         *)
(* Remainders: CHEN_REMAINDER_SUM (Goldbach: residue N mod d, x = N - 1)     *)
(* bounds the remainder over squarefree d < Y by a Bombieri-Vinogradov sum   *)
(* plus 2 omega(N) Y.  chen_remainder_ok h is the resulting condition for a  *)
(* family of shifts h(N): for every A there are B, C with remainder          *)
(* <= C N / log^A N + 2 omega(h N) Y at levels Y <= sqrt N / log^B N.        *)
(* GOLDBACH_REMAINDER_OK proves it for h(N) = N from BOMBIERI_VINOGRADOV     *)
(* (bv.ml), which allows any residues a(d) coprime to d.                     *)
(* ========================================================================= *)

needs "Sieve/bv.ml";;
needs "Sieve/jurkat.ml";;
needs "Sieve/goldbach_shnirelman.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The density and the dimension condition.                                  *)
(* ------------------------------------------------------------------------- *)

let chen_g = new_definition
 `chen_g N p = if p divides N then &0 else inv(&p - &1)`;;

let CHEN_G_BOUNDS = prove
 (`!N p. EVEN N /\ prime p ==> &0 <= chen_g N p /\ chen_g N p < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[chen_g] THEN
  COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `3 <= p` MP_TAC THENL
   [MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `~(p = 2) ==> 2 <= p ==> 3 <= p`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(2 divides N)` THEN ASM_MESON_TAC[EVEN_EXISTS; divides];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LT_1 THEN ASM_REAL_ARITH_TAC]);;

let CHEN_G_FACTOR_BOUND = prove
 (`!N p. EVEN N /\ prime p
         ==> inv(&1 - chen_g N p) <=
             inv(&1 - inv(&p)) * (&1 + &3 * inv(&p pow 2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= inv(&1 - inv(&p))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LE THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 - x <= &1`) THEN
      MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &3 * inv(&p pow 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[chen_g] THEN COND_CASES_TAC THENL
   [REWRITE_TAC[REAL_SUB_RZERO; REAL_INV_1] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&3 <= &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `~(p = 2) ==> 2 <= p ==> 3 <= p`) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(2 divides N)` THEN ASM_MESON_TAC[EVEN_EXISTS; divides];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(&1 - inv(&p - &1)) = (&p - &1) / (&p - &2) /\
                inv(&1 - inv(&p)) = &p / (&p - &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&3 <= &p` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &p - &2` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(&p / (&p - &1) * (&1 + &3 * inv(&p pow 2))) * (&p - &2) =
                (&p pow 3 - &2 * &p pow 2 + &3 * &p - &6) / (&p * (&p - &1))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&3 <= &p` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &p * (&p - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  UNDISCH_TAC `&3 <= &p` THEN REAL_ARITH_TAC);;

let REAL_EXP_LE_1_PLUS = prove
 (`!a. &0 <= a ==> exp a <= &1 + a * exp a`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `--a:real` REAL_EXP_LE_X) THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&0 < exp a` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(&1 + --a) * exp a <= inv(exp a) * exp a` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC);;

let CHEN_G_DIMENSION = prove
 (`?L. &0 <= L /\
       !N u v. EVEN N /\ &2 <= u /\ u <= v
               ==> inv(product (sieve_primes u v) (\p. &1 - chen_g N p)) <=
                   log v / log u * (&1 + L / log u)`,
  X_CHOOSE_THEN `C:real` ASSUME_TAC MERTENS_PRODUCT_LOG THEN
  ABBREV_TAC `M = abs C + &9` THEN
  EXISTS_TAC `M * exp(M / log(&2))` THEN
  SUBGOAL_THEN `&0 <= M /\ &0 < log(&2)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log u /\ log(&2) <= log u /\ log u < u`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_LT_X THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(sieve_primes u v) /\
                (!p. p IN sieve_primes u v ==> prime p /\ &2 <= &p)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[sieve_primes; IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{p | prime p /\ &p < v}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      REWRITE_TAC[REAL_OF_NUM_LE] THEN MESON_TAC[PRIME_GE_2]];
    ALL_TAC] THEN
  ABBREV_TAC `S = sieve_primes u v` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `product S (\p. inv(&1 - inv(&p))) *
              product S (\p. &1 + &3 * inv(&p pow 2))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_INV; GSYM PRODUCT_MUL] THEN
    MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `prime p` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CHEN_G_FACTOR_BOUND] THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MP_TAC(SPECL [`N:num`; `p:num`] CHEN_G_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log v` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `product S (\p. inv(&1 - inv(&p))) <= log v / log u * exp(abs C / log u)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `product S (\p. inv(&1 - inv(&p))) =
                  exp(sum S (\p. --log(&1 - inv(&p))))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[REAL_EXP_SUM] THEN MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_EXP_NEG] THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC EXP_LOG THEN
      REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_LT_1 THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(log(log v) - log(log u) + abs C / log u)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_MONO_LE] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`] o
        check (fun th -> can (find_term ((=) `C:real`)) (concl th))) THEN
      EXPAND_TAC "S" THEN REWRITE_TAC[sieve_primes] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!s a c d. c <= d ==> abs(s - a) <= c ==> s <= a + d`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_EXP_ADD; REAL_EXP_SUB; EXP_LOG; real_div] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product S (\p. &1 + &3 * inv(&p pow 2)) <= exp(&9 / log u)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product S (\p. exp(&3 * inv(&p pow 2)))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[REAL_EXP_LE_X] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_EXP_SUM; REAL_EXP_MONO_LE; SUM_LMUL] THEN
    MP_TAC(SPECL [`u:real`; `v:real`] SUM_PRIME_SQUARES_TAIL) THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[sieve_primes] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 * &3 / u` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH `&3 * &3 / u = &9 / u`] THEN
      MP_TAC(SPECL [`u:real`; `log u`; `&9`] REAL_LE_DIV_DENOM) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product S (\p. inv(&1 - inv(&p))) /\
                &0 <= product S (\p. &1 + &3 * inv(&p pow 2))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ; REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_LE_POW_2]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(log v / log u * exp(abs C / log u)) * exp(&9 / log u)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; GSYM REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `abs C / log u + &9 / log u = M / log u` SUBST1_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M / log u /\ M / log u <= M / log(&2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 + M / log u * exp(M / log u)` THEN
  ASM_SIMP_TAC[REAL_EXP_LE_1_PLUS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN
  SUBGOAL_THEN `(M * exp(M / log(&2))) / log u = M / log u * exp(M / log(&2))`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE]);;

let PHI_NPRODUCT_PRIMES = prove
 (`!t. FINITE t /\ (!p. p IN t ==> prime p)
       ==> phi(nproduct t (\p. p)) = nproduct t (\p. p - 1)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL [REWRITE_TAC[NPRODUCT_CLAUSES; PHI_1]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `t:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PHI_MULTIPLICATIVE o lhand o snd) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COPRIME_PRIME_NPRODUCT THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[PHI_PRIME]);;

let REAL_PRODUCT_INV_PRED = prove
 (`!t. FINITE t /\ (!p. p IN t ==> prime p)
       ==> product t (\p. inv(&p - &1)) = inv(&(phi(nproduct t (\p. p))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[PHI_NPRODUCT_PRIMES] THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; GSYM PRODUCT_INV] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `1 <= p` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB]);;

(* ------------------------------------------------------------------------- *)
(* The Goldbach set A.                                                       *)
(* ------------------------------------------------------------------------- *)

let chen_A = new_definition
 `chen_A N = IMAGE (\p. N - p) {p | prime p /\ p < N /\ ~(p divides N)}`;;

let FINITE_CHEN_PRIMES = prove
 (`!N P. FINITE {p | prime p /\ p < N /\ P p}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p:num | p < N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SET_TAC[]);;

let SUM_CHEN_A = prove
 (`!N Q. sum {n | n IN chen_A N /\ Q n} (\n. &1) =
         &(CARD {p | prime p /\ p < N /\ ~(p divides N) /\ Q(N - p)})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chen_A] THEN
  SUBGOAL_THEN
   `{n | n IN IMAGE (\p. N - p) {p | prime p /\ p < N /\ ~(p divides N)} /\
         Q n} =
    IMAGE (\p. N - p) {p | prime p /\ p < N /\ ~(p divides N) /\ Q(N - p)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  SIMP_TAC[SUM_CONST; FINITE_CHEN_PRIMES; REAL_MUL_RID]);;

let CARD_CHEN_A = prove
 (`!N. CARD(chen_A N) = CARD {p | prime p /\ p < N /\ ~(p divides N)}`,
  GEN_TAC THEN REWRITE_TAC[chen_A] THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
  REWRITE_TAC[FINITE_CHEN_PRIMES; IN_ELIM_THM] THEN ARITH_TAC);;

let CHEN_SIEVE_COUNT = prove
 (`!N t. sieve_count (chen_A N) (\n. &1) t =
         &(CARD {p | prime p /\ p < N /\ ~(p divides N) /\
                     !q. q IN t ==> q divides N - p})`,
  REWRITE_TAC[sieve_count; SUM_CHEN_A]);;

(* ------------------------------------------------------------------------- *)
(* Remainders.                                                               *)
(* ------------------------------------------------------------------------- *)

let CHEN_REMAINDER_TERM = prove
 (`!N t. FINITE t /\ (!q. q IN t ==> prime q) /\ 1 <= N
         ==> abs(sieve_count (chen_A N) (\n. &1) t -
                 &(CARD(chen_A N)) * product t (chen_g N)) <=
             (if !q. q IN t ==> ~(q divides N)
              then abs(&(pi_ap (N - 1) (nproduct t (\p. p)) N) -
                       &(pi_upto (N - 1)) /
                       &(phi(nproduct t (\p. p)))) +
                   &2 * &(CARD {p | prime p /\ p divides N})
              else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CHEN_SIEVE_COUNT; CARD_CHEN_A] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    SUBGOAL_THEN `product t (chen_g N) = &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `r:num` THEN
      ASM_REWRITE_TAC[chen_g];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; LE] THEN
    SIMP_TAC[CARD_EQ_0; FINITE_CHEN_PRIMES] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r:num) divides p` MP_TAC THENL
     [SUBGOAL_THEN `p = N - (N - p):num` SUBST1_TAC THENL
       [UNDISCH_TAC `p < N:num` THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC DIVIDES_SUB THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[]] THEN
  ABBREV_TAC `d = nproduct t (\p:num. p)` THEN
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `product t (chen_g N) = inv(&(phi d))` SUBST1_TAC THENL
   [EXPAND_TAC "d" THEN ASM_SIMP_TAC[GSYM REAL_PRODUCT_INV_PRED] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[chen_g];
    ALL_TAC] THEN
  ABBREV_TAC `W = CARD {p | prime p /\ p divides N}` THEN
  SUBGOAL_THEN
   `{p | prime p /\ p < N /\ ~(p divides N) /\
         (!q. q IN t ==> q divides N - p)} =
    {p | prime p /\ p <= N - 1 /\ (p == N) (mod d)} DIFF
    {p | prime p /\ p divides N}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(p:num) divides N` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRIMES_DIVIDE_IFF_NPRODUCT] THEN
    ASM_CASES_TAC `p < N:num` THEN ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[ARITH_RULE `p < N ==> p <= N - 1`] THEN
      REWRITE_TAC[CONG_SUB_CASES; CONG_0] THEN
      ASM_SIMP_TAC[LT_IMP_LE];
      ASM_SIMP_TAC[ARITH_RULE `1 <= N /\ ~(p < N) ==> ~(p <= N - 1)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p < N /\ ~(p divides N)} =
    {p | prime p /\ p <= N - 1} DIFF {p | prime p /\ p divides N}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
    UNDISCH_TAC `1 <= N` THEN MESON_TAC[ARITH_RULE
     `1 <= N ==> (p < N <=> p <= N - 1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {p | prime p /\ p <= N - 1 /\ (p == N) (mod d)} /\
                FINITE {p | prime p /\ p <= N - 1} /\
                FINITE {p | prime p /\ p divides N}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ALL_TAC; ALL_TAC;
      MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN
      UNDISCH_TAC `1 <= N` THEN ARITH_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S1 = {p | prime p /\ p <= N - 1 /\ (p == N) (mod d)}` THEN
  ABBREV_TAC `S3 = {p | prime p /\ p <= N - 1}` THEN
  ABBREV_TAC `S2 = {p | prime p /\ p divides N}` THEN
  SUBGOAL_THEN `CARD((S1:num->bool) DIFF S2) = CARD S1 - CARD(S1 INTER S2) /\
                CARD((S3:num->bool) DIFF S2) = CARD S3 - CARD(S3 INTER S2) /\
                CARD((S1:num->bool) INTER S2) <= CARD S1 /\
                CARD((S3:num->bool) INTER S2) <= CARD S3 /\
                CARD((S1:num->bool) INTER S2) <= W /\
                CARD((S3:num->bool) INTER S2) <= W`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `(s:num->bool) DIFF t = s DIFF (s INTER t)`] THEN
    ASM_SIMP_TAC[CARD_DIFF; INTER_SUBSET] THEN EXPAND_TAC "W" THEN
    REPEAT CONJ_TAC THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  SUBGOAL_THEN `&(CARD(S1:num->bool)) = &(pi_ap (N - 1) d N) /\
                &(CARD(S3:num->bool)) = &(pi_upto (N - 1))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S3"] THEN REWRITE_TAC[pi_ap; pi_upto];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= &(phi d)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `CARD((S1:num->bool) INTER S2)` REAL_POS) THEN
  MP_TAC(SPEC `CARD((S3:num->bool) INTER S2)` REAL_POS) THEN
  MAP_EVERY UNDISCH_TAC
   [`CARD((S1:num->bool) INTER S2) <= W`;
    `CARD((S3:num->bool) INTER S2) <= W`; `&1 <= &(phi d)`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  SPEC_TAC(`&(CARD((S1:num->bool) INTER S2))`,`c2:real`) THEN
  SPEC_TAC(`&(CARD((S3:num->bool) INTER S2))`,`c3:real`) THEN
  SPEC_TAC(`&(phi d)`,`f:real`) THEN
  SPEC_TAC(`&(pi_ap (N - 1) d N)`,`a:real`) THEN
  SPEC_TAC(`&(pi_upto (N - 1))`,`b:real`) THEN
  SPEC_TAC(`&W`,`w:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c3 * inv f <= c3` MP_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_INV_LE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c3 * inv f` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC);;

let CHEN_REMAINDER_SUM = prove
 (`!N z Y. 1 <= N /\ &1 <= Y
           ==> sum {t | t SUBSET {p | prime p /\ &p < z} /\
                        &(nproduct t (\p. p)) < Y}
                   (\t. abs(sieve_count (chen_A N) (\n. &1) t -
                            &(CARD(chen_A N)) * product t (chen_g N)))
               <= sum {d | 1 <= d /\ &d <= Y}
                      (\d. abs(&(pi_ap (N - 1) d
                                   (if coprime(d,N) then N else 1)) -
                               &(pi_upto (N - 1)) / &(phi d))) +
                  &2 * &(CARD {p | prime p /\ p divides N}) * Y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = \d. abs(&(pi_ap (N - 1) d
                                (if coprime(d,N) then N else 1)) -
                          &(pi_upto (N - 1)) / &(phi d))` THEN
  ABBREV_TAC `W = &(CARD {p | prime p /\ p divides N})` THEN
  SUBGOAL_THEN `&0 <= W /\ (!d. &0 <= (E:num->real) d)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "E"] THEN REWRITE_TAC[REAL_POS; REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {t | t SUBSET {p | prime p /\ &p < z} /\
                &(nproduct t (\p. p)) < Y}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:num->bool | t SUBSET {p | prime p /\ &p < z}}` THEN
    SIMP_TAC[FINITE_POWERSET; FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `TT = {t | t SUBSET {p | prime p /\ &p < z} /\
                        &(nproduct t (\p. p)) < Y}` THEN
  SUBGOAL_THEN `!t. t IN TT ==> FINITE t /\ (!q. q IN t ==> prime q) /\
                                &(nproduct t (\p. p)) < Y`
  ASSUME_TAC THENL
   [EXPAND_TAC "TT" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < z}` THEN
      ASM_REWRITE_TAC[FINITE_PRIMES_LT];
      UNDISCH_TAC `t SUBSET {p | prime p /\ &p < z}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum TT (\t. if !q. q IN t ==> ~(q divides N)
                          then (E:num->real)(nproduct t (\p. p)) + &2 * W
                          else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `TT:(num->bool)->bool`))
                           (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL [`N:num`; `t:num->bool`] CHEN_REMAINDER_TERM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y z:real. y = z ==> x <= y ==> x <= z`) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["E"; "W"] THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `coprime(nproduct t (\p. p),N)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[COPRIME_NPRODUCT_EQ; PRIME_COPRIME_EQ];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t1 t2. t1 IN TT /\ t2 IN TT /\
            nproduct t1 (\p. p) = nproduct t2 (\p. p) ==> t1 = t2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN TT ==> 1 <= nproduct t (\p. p)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum TT (\t. if !q. q IN t ==> ~(q divides N)
                          then (E:num->real)(nproduct t (\p. p)) else &0) +
              sum TT (\t:num->bool. &2 * W)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN
     `sum {t | t IN TT /\ (!q. q IN t ==> ~(q divides N))}
          (\t. (E:num->real) (nproduct t (\p. p))) =
      sum (IMAGE (\t. nproduct t (\p. p))
                 {t | t IN TT /\ (!q. q IN t ==> ~(q divides N))}) E`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
                      REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_NUM_RANGE_LE]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LT_IMP_LE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x * &2 * w = (&2 * w) * x /\
                               &2 * w * y = (&2 * w) * y`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {b | 1 <= b /\ &b < Y})` THEN
  ASM_SIMP_TAC[CARD_NUM_RANGE_LE; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\t. nproduct t (\p. p)) (TT:(num->bool)->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUM_RANGE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The general sifted set.                                                   *)
(* ------------------------------------------------------------------------- *)

let chen_dist = new_definition
 `chen_dist (N:num) m = if m <= N then N - m else m - N`;;

let DIVIDES_DIST_CONG = prove
 (`!d m N. d divides (if m <= N then N - m else m - N) <=> (m == N) (mod d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG_SUB_CASES; CONG_0] THEN
  COND_CASES_TAC THEN REWRITE_TAC[]);;

let gchen_A = new_definition
 `gchen_A h N =
    {n | 1 <= n /\ n < N /\ coprime(n,h) /\ prime(chen_dist h n)}`;;

let FINITE_GCHEN_A = prove
 (`!h N. FINITE(gchen_A h N)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{n:num | n < N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[gchen_A] THEN SET_TAC[]);;

let CHEN_A_GEN = prove
 (`!N. gchen_A N N = chen_A N`,
  GEN_TAC THEN REWRITE_TAC[gchen_A; chen_A; EXTENSION; IN_ELIM_THM;
                           IN_IMAGE; chen_dist] THEN
  X_GEN_TAC `n:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN EXISTS_TAC `N - n:num` THEN
    UNDISCH_TAC `prime(if n <= N then N - n else n - N)` THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `coprime(n,N)` THEN
    REWRITE_TAC[COPRIME_PRIME_EQ; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `N - n:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(N - n) divides N - (N - n)` MP_TAC THENL
     [MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[DIVIDES_REFL];
      SUBGOAL_THEN `N - (N - n) = n:num` (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `N - p <= N /\ N - (N - p) = p:num` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
    REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COPRIME_PRIME_EQ] THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r divides p` MP_TAC THENL
     [SUBGOAL_THEN `p = N - (N - p):num` SUBST1_TAC THENL
       [ASM_ARITH_TAC; MATCH_MP_TAC DIVIDES_SUB THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The remainder hypothesis for a family of shifts.                          *)
(* ------------------------------------------------------------------------- *)

let chen_remainder_ok = new_definition
 `chen_remainder_ok (h:num->num) <=>
    !A. ?B C. !N z Y.
        EVEN N /\ 16 <= N /\ &1 <= Y /\ Y <= sqrt(&N) / log(&N) pow B
        ==> sum {t | t SUBSET {p | prime p /\ &p < z} /\
                     &(nproduct t (\p. p)) < Y}
                (\t. abs(sieve_count (gchen_A (h N) N) (\n. &1) t -
                         &(CARD(gchen_A (h N) N)) *
                         product t (chen_g (h N))))
            <= C * &N / log(&N) pow A +
               &2 * &(CARD {p | prime p /\ p divides h N}) * Y`;;

let BV_SHIFT_FACTS = prove
 (`!N k B A. 16 <= N /\ 13 + k <= N /\ 4 * k <= 3 * N
             ==> 2 <= N - k /\
                 sqrt(&N) / log(&N) pow (B + 1) <=
                 sqrt(&(N - k)) / log(&(N - k)) pow B /\
                 &(N - k) / log(&(N - k)) pow A <=
                 &2 pow A * &N / log(&N) pow A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(N - k) = &N - &k` SUBST1_TAC THENL
   [MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&16 <= &N /\ &13 + &k <= &N /\ &4 * &k <= &3 * &N`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = &N - &k` THEN ABBREV_TAC `y = &N` THEN
  SUBGOAL_THEN `&13 <= x /\ x <= y /\ y <= x pow 2 /\ y <= &4 * x`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` REAL_POS) THEN
    SUBGOAL_THEN `&13 * x <= x * x` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x /\ log x <= log y /\ log y <= &2 * log x /\
                &2 <= log y`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&2 * log x = log(x pow 2)` SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_POW THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&2 pow 4)` THEN
      CONJ_TAC THENL
       [SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`] THEN
        MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log x pow B /\ &0 < log y pow (B + 1) /\
                &0 < log x pow A /\ &0 < log y pow A /\
                &0 <= sqrt x /\ &0 <= sqrt y`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_ARITH `&2 <= a ==> &0 < a`] THEN
    CONJ_TAC THEN MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[MESON[real_div; REAL_MUL_ASSOC]
   `!a b c:real. a * b / c = (a * b) / c`] THEN
  ASM_SIMP_TAC[RAT_LEMMA4] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * sqrt x) * log x pow B` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_MUL; SQRT_POW_2;
                   REAL_ARITH `&13 <= a ==> &0 <= a`] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_POW_ADD; REAL_POW_1] THEN
      ONCE_REWRITE_TAC[REAL_ARITH `(&2 * s) * l = s * (&2 * l)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE; REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `y * (&2 pow A * log x pow A)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE;
                   REAL_ARITH `&13 <= a ==> &0 <= a`] THEN
      REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ARITH `&2 <= a ==> &0 <= a`];
      REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]]);;

let GOLDBACH_REMAINDER_OK = prove
 (`chen_remainder_ok (\N. N)`,
  REWRITE_TAC[chen_remainder_ok] THEN X_GEN_TAC `A:num` THEN
  MP_TAC(SPEC `A:num` BOMBIERI_VINOGRADOV) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_TAC `C:real`)) THEN
  MAP_EVERY EXISTS_TAC [`B + 1`; `abs C * &2 pow A`] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `z:real`; `Y:real`] THEN STRIP_TAC THEN
  REWRITE_TAC[CHEN_A_GEN] THEN
  MP_TAC(SPECL [`N:num`; `1`; `B:num`; `A:num`] BV_SHIFT_FACTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {d | 1 <= d /\ &d <= Y}
                (\d. abs(&(pi_ap (N - 1) d (if coprime(d,N) then N else 1)) -
                         &(pi_upto (N - 1)) / &(phi d))) +
              &2 * &(CARD {p | prime p /\ p divides N}) * Y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CHEN_REMAINDER_SUM THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[REAL_LE_RADD]] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {d | 1 <= d /\ &d <= sqrt(&(N - 1)) / log(&(N - 1)) pow B}
                (\d. abs(&(pi_ap (N - 1) d (if coprime(d,N) then N else 1)) -
                         &(pi_upto (N - 1)) / &(phi d)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUM_RANGE_LE; REAL_ABS_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`N - 1`; `\d. if coprime(d,N) then N else 1`]) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[COPRIME_SYM; COPRIME_1];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs C * &(N - 1) / log(&(N - 1)) pow A` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[REAL_ABS_POS]]);;
