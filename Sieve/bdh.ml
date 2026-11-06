(* ========================================================================= *)
(* The Barban-Davenport-Halberstam theorem (Barban 1964, Davenport and       *)
(* Halberstam 1966; Gallagher's proof by the large sieve, as in Davenport,   *)
(* Multiplicative Number Theory, ch. 29).  With theta(N; q, a) the sum of    *)
(* log p over the primes p <= N with p == a (mod q),                         *)
(*   BARBAN_DAVENPORT_HALBERSTAM:                                            *)
(*     !A. ?B. !N Q.                                                         *)
(*       2 <= N /\ 1 <= Q /\ Q <= N                                          *)
(*       ==> sum(1..Q) (\q. sum {a | a < q /\ coprime(a,q)}                  *)
(*                            (\a. (theta(N; q, a) - &N / &(phi q)) pow 2))  *)
(*           <= B * (&N * &Q * log(&N) + &N pow 2 / log(&N) pow A)           *)
(* (theta written out as a sum in the statement), and the classical form     *)
(* BDH_RANGE: the mean square is at most B N Q log N whenever                *)
(* N / log^A N <= Q <= N.                                                    *)
(* Method.  For one modulus q, Parseval over the characters mod q bounds     *)
(* the inner sum by (2/phi(q)) sum_{c <> chi_0} |theta(N, c)|^2 plus a       *)
(* principal term (BDH_PARSEVAL, BDH_ONE_MODULUS).  A nonprincipal c is      *)
(* induced by a primitive character of conductor r > 1, r | q, and differs   *)
(* from it only at the primes dividing q (BDH_PRIMITIVE_REDUCTION).          *)
(* Regrouping by conductor (BDH_REGROUP) leaves                              *)
(*   sum_{1 < r <= Q} E(r) / phi(r) * 4 (1 + log(Q/r)),                      *)
(* E(r) = sum of |theta(N, c)|^2 over the primitive c mod r (bdh_energy).    *)
(* Conductors r <= log^(A+2) N are handled by Siegel-Walfisz (BDH_SMALL),    *)
(* the others by the multiplicative large sieve on dyadic blocks             *)
(* 2^j < r <= 2^(j+1) (BDH_LARGE_SIEVE, BDH_BLOCK_BOUND, BDH_LARGE), and     *)
(* the principal characters by the prime number theorem with error term      *)
(* (PNT_THETA_UNIFORM, BDH_SUM_Q).                                           *)
(* ========================================================================= *)

needs "Sieve/vinogradov.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* One modulus: Parseval over the characters.                                *)
(* ------------------------------------------------------------------------- *)

let CHAR_THETA_RESIDUES = prove
 (`!q (c:num->complex) N.
     1 <= q /\ dirichlet_character q c
     ==> vsum {a | a < q}
           (\a. cnj(c a) *
                Cx(sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                       (\p. log(&p)))) =
         cnj(vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * c p))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[CNJ_VSUM; FINITE_ATMOST; CNJ_MUL; CNJ_CX] THEN
  MP_TAC(ISPECL [`\p. p MOD q`; `\p. Cx(log(&p)) * cnj((c:num->complex) p)`;
                 `{p | prime p /\ p <= N}`; `{a | a < q:num}`] VSUM_GROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_ATMOST; SUBSET; FORALL_IN_IMAGE;
                IN_ELIM_THM] THEN
    ASM_SIMP_TAC[DIVISION; ARITH_RULE `1 <= q ==> ~(q = 0)`];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[GSYM VSUM_CX] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_PRIMES_LE_RESTRICT] THEN
  SUBGOAL_THEN `{x | (prime x /\ x <= N) /\ x MOD q = a} =
                {p | prime p /\ p <= N /\ (p == a) (mod q)}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    X_GEN_TAC `x:num` THEN ASM_SIMP_TAC[CONG; MOD_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `(c:num->complex) a = c p` SUBST1_TAC THENL
   [MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(p:num == a) (mod q)` THEN
    CONV_TAC NUMBER_RULE;
    REWRITE_TAC[COMPLEX_MUL_SYM]]);;

let VSUM_RESIDUES_NUMSEG = prove
 (`!q (c:num->complex).
     1 <= q /\ dirichlet_character q c
     ==> vsum {a | a < q} c = vsum(1..q) c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a < q} = 0..q - 1` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `n = q - 1` THEN
  SUBGOAL_THEN `q = SUC n` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN
  SUBGOAL_THEN `(c:num->complex)(SUC n) = c 0` SUBST1_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_PERIODIC; ADD_CLAUSES];
    REWRITE_TAC[VECTOR_ADD_SYM]]);;

let CHAR_CNJ_RESIDUE_SUM = prove
 (`!q (c:num->complex).
     1 <= q /\ dirichlet_character q c
     ==> vsum {a | a < q} (\a. cnj(c a)) =
         if c = chi_0 q then Cx(&(phi q)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM CNJ_VSUM; FINITE_NUMSEG_LT; ETA_AX] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[PHI_ALT] THEN
    SUBGOAL_THEN
     `vsum {a | a < q} (chi_0 q) =
      vsum {a | a < q} (\a. if coprime(a,q) then Cx(&1) else Cx(&0))`
    SUBST1_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; chi_0]; ALL_TAC] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET] THEN
    SIMP_TAC[VSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID; CNJ_CX] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_SIMP_TAC[VSUM_RESIDUES_NUMSEG; DIRICHLET_CHARACTER_ZEROSUM; CNJ_CX]]);;

let BDH_PARSEVAL = prove
 (`!q N. 1 <= q
         ==> sum ({c | dirichlet_character q c} DELETE chi_0 q)
               (\c. norm(vsum {p | prime p /\ p <= N}
                               (\p. Cx(log(&p)) * c p)) pow 2) =
             &(phi q) *
             sum {a | a < q /\ coprime(a,q)}
               (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                         (\p. log(&p)) -
                     sum {p | prime p /\ p <= N /\ coprime(p,q)}
                         (\p. log(&p)) / &(phi q)) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = sum {p | prime p /\ p <= N /\ coprime(p,q)}
                       (\p. log(&p))` THEN
  MP_TAC(ISPECL [`q:num`;
    `\a. Cx(sum {p | prime p /\ p <= N /\ (p == a) (mod q)} (\p. log(&p)) -
            T0 / &(phi q))`] DIRICHLET_CHARACTER_PARSEVAL) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
   `!c. dirichlet_character q c
        ==> vsum {a | a < q}
              (\a. cnj(c a) *
                   Cx(sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                          (\p. log(&p)) - T0 / &(phi q))) =
            cnj(vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * c p)) -
            Cx(T0 / &(phi q)) *
            (if c = chi_0 q then Cx(&(phi q)) else Cx(&0))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[CX_SUB; COMPLEX_SUB_LDISTRIB] THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG_LT] THEN
    ASM_SIMP_TAC[CHAR_THETA_RESIDUES] THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
    ASM_SIMP_TAC[CHAR_CNJ_RESIDUE_SUM] THEN
    MATCH_ACCEPT_TAC COMPLEX_MUL_SYM;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum ({c | dirichlet_character q c} DELETE chi_0 q)
     (\c. norm(vsum {a | a < q}
            (\a. cnj(c a) *
                 Cx(sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                        (\p. log(&p)) - T0 / &(phi q)))) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO; COMPLEX_NORM_CNJ];
    ALL_TAC] THEN
  SIMP_TAC[SUM_DELETE; FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM;
           DIRICHLET_CHARACTER_CHI_0] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> s - x = s:real`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `chi_0 q`) THEN
  REWRITE_TAC[DIRICHLET_CHARACTER_CHI_0] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * chi_0 q p) =
                Cx T0` SUBST1_TAC THENL
   [REWRITE_TAC[chi_0; COND_RAND; COMPLEX_MUL_RZERO; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET; VSUM_CX] THEN
    AP_TERM_TAC THEN EXPAND_TAC "T0" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[CNJ_CX; GSYM CX_MUL; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_SUB_REFL] THEN
  REAL_ARITH_TAC);;

let SQUARE_SUM_LE = prove
 (`!a b:real. (a + b) pow 2 <= &2 * a pow 2 + &2 * b pow 2`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `a - b:real` REAL_LE_POW_2) THEN
  REAL_ARITH_TAC);;

let BDH_ONE_MODULUS = prove
 (`!q N. 1 <= q
         ==> sum {a | a < q /\ coprime(a,q)}
               (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                         (\p. log(&p)) - &N / &(phi q)) pow 2)
             <= &2 / &(phi q) *
                sum ({c | dirichlet_character q c} DELETE chi_0 q)
                  (\c. norm(vsum {p | prime p /\ p <= N}
                                  (\p. Cx(log(&p)) * c p)) pow 2) +
                &2 * (sum {p | prime p /\ p <= N /\ coprime(p,q)}
                          (\p. log(&p)) - &N) pow 2 / &(phi q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[BDH_PARSEVAL] THEN
  ABBREV_TAC `T0 = sum {p | prime p /\ p <= N /\ coprime(p,q)}
                       (\p. log(&p))` THEN
  ABBREV_TAC `f = \a. sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                        (\p. log(&p))` THEN
  SUBGOAL_THEN `!a. sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                        (\p. log(&p)) = (f:num->real) a`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {a | a < q /\ coprime(a,q)}
      (\a. &2 * ((f:num->real) a - T0 / &(phi q)) pow 2 +
           &2 * ((T0 - &N) / &(phi q)) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
    X_GEN_TAC `a:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(f:num->real) a - &N / &(phi q) =
      (f a - T0 / &(phi q)) + (T0 - &N) / &(phi q)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_ACCEPT_TAC SQUARE_SUM_LE;
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; FINITE_COPRIME_RESIDUES; SUM_LMUL; SUM_CONST] THEN
  SUBGOAL_THEN `CARD {a | a < q /\ coprime(a,q)} = phi q` SUBST1_TAC THENL
   [REWRITE_TAC[PHI_ALT] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < &(phi q)` THEN
  SPEC_TAC(`sum {a | a < q /\ coprime(a,q)}
              (\a. ((f:num->real) a - T0 / &(phi q)) pow 2)`,`S:real`) THEN
  SPEC_TAC(`&(phi q)`,`ph:real`) THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < ph` THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Reduction to primitive characters; regrouping by conductor.               *)
(* ------------------------------------------------------------------------- *)

let THETA_TWIST_BOUND = prove
 (`!N q (c:num->complex).
     1 <= q /\ (!n. norm(c n) <= &1)
     ==> norm(vsum {p | prime p /\ p <= N}
                (\p. Cx(log(&p)) * (if coprime(p,q) then c p else Cx(&0))))
         <= norm(vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * c p)) +
            log(&q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum {p | prime p /\ p <= N}
      (\p. Cx(log(&p)) * (if coprime(p,q) then c p else Cx(&0))) =
    vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * c p) -
    vsum {p | p IN {p | prime p /\ p <= N} /\ ~coprime(p,q)}
      (\p. Cx(log(&p)) * c p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_RESTRICT_SET] THEN
    SIMP_TAC[GSYM VSUM_SUB; FINITE_ATMOST] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y:complex) <= b ==> norm(x - y) <= norm x + b`) THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {p | p IN {p | prime p /\ p <= N} /\ ~coprime(p,q)} (\p. log(&p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_ATMOST] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    SUBGOAL_THEN `&0 <= log(&p)` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `sum {p | prime p /\ p divides q} (\p. log(&p))` THEN
  ASM_SIMP_TAC[LOG_SUM_PRIME_DIVISORS] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRIME_DIVISORS THEN ASM_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[PRIME_COPRIME_EQ; COPRIME_SYM];
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]]);;

let BDH_PRIMITIVE_REDUCTION = prove
 (`!q N. 1 <= q
         ==> sum ({c | dirichlet_character q c} DELETE chi_0 q)
               (\c. norm(vsum {p | prime p /\ p <= N}
                               (\p. Cx(log(&p)) * c p)) pow 2)
             <= sum {r | r divides q /\ ~(r = 1)}
                  (\r. sum {c | primitive_character r c}
                         (\c. &2 * norm(vsum {p | prime p /\ p <= N}
                                             (\p. Cx(log(&p)) * c p)) pow 2 +
                              &2 * log(&q) pow 2))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:num`;
    `\c:num->complex. norm(vsum {p | prime p /\ p <= N}
                               (\p. Cx(log(&p)) * c p)) pow 2`]
    PRIMITIVE_REDUCTION_SUM) THEN
  ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r | r divides q}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
                    SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS] THEN
  X_GEN_TAC `c:num->complex` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `(norm(vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * c p)) +
     log(&q)) pow 2` THEN
  REWRITE_TAC[SQUARE_SUM_LE] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC THETA_TWIST_BOUND THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[primitive_character; DIRICHLET_CHARACTER_NORM_LE]);;

let SUM_PHI_RATIO_LE = prove
 (`!N. sum(1..N) (\n. &n / &(phi n)) <= &4 * &N`,
  GEN_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..N) (\n. sum {d | d divides n} (\d. inv(&(phi d))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PHI_RATIO_LE THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_SUM_DIVISORS] THEN
  TRANS_TAC REAL_LE_TRANS `sum(1..N) (\n. &N * inv(&n * &(phi n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
    REWRITE_TAC[REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[DIV_MUL_LE];
    REWRITE_TAC[SUM_LMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[SUM_INV_MUL_PHI_LE; REAL_POS]]);;

let bdh_energy = new_definition
 `bdh_energy N r =
    sum {c | primitive_character r c}
      (\c. norm(vsum {p | prime p /\ p <= N} (\p. Cx(log(&p)) * c p)) pow 2)`;;

let BDH_Q_BOUND = prove
 (`!N q. 1 <= q
         ==> sum {a | a < q /\ coprime(a,q)}
               (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                         (\p. log(&p)) - &N / &(phi q)) pow 2)
             <= &4 * inv(&(phi q)) *
                sum {r | r divides q /\ ~(r = 1)} (\r. bdh_energy N r) +
                &4 * &q / &(phi q) * log(&q) pow 2 +
                &2 * (sum {p | prime p /\ p <= N /\ coprime(p,q)}
                          (\p. log(&p)) - &N) pow 2 / &(phi q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &(phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {r | r divides q /\ ~(r = 1)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r | r divides q}` THEN
    CONJ_TAC THENL [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
                    SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`q:num`; `N:num`] BDH_ONE_MODULUS) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!v a b c1 c2:real. a <= c1 + c2 ==> v <= a + b ==> v <= c1 + c2 + b`) THEN
  MP_TAC(SPECL [`q:num`; `N:num`] BDH_PRIMITIVE_REDUCTION) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SUM_ADD; FINITE_PRIMITIVE_CHARACTERS; SUM_LMUL; SUM_CONST] THEN
  REWRITE_TAC[GSYM bdh_energy] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_RMUL] THEN
  REWRITE_TAC[real_div] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ETA_AX]) THEN REWRITE_TAC[ETA_AX] THEN
  SUBGOAL_THEN
   `sum {r | r divides q /\ ~(r = 1)}
        (\x. &(CARD {c | primitive_character x c})) <= &q`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum {r | r divides q /\ ~(r = 1)} (\r. &(phi r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC CARD_PRIMITIVE_CHARACTERS_LE THEN
      REWRITE_TAC[ARITH_RULE `1 <= r <=> ~(r = 0)`] THEN
      ASM_MESON_TAC[DIVIDES_ZERO; ARITH_RULE `1 <= d ==> ~(d = 0)`];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `sum {r | r divides q} (\r. &(phi r))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[REAL_POS] THEN
      CONJ_TAC THENL [MATCH_MP_TAC FINITE_DIVISORS THEN ASM_ARITH_TAC;
                      SET_TAC[]];
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUM; FINITE_DIVISORS;
                   ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
      ASM_SIMP_TAC[REWRITE_RULE[ETA_AX] PHI_DIVISORSUM;
                   ARITH_RULE `1 <= d ==> ~(d = 0)`; REAL_LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!X Y Z L i q:real.
      i * X <= i * (&2 * Y + &2 * Z * L) /\ (i * L) * Z <= (i * L) * q
      ==> (&2 * i) * X <= &4 * i * Y + &4 * (q * i) * L`) THEN
  EXISTS_TAC `sum {r | r divides q /\ ~(r = 1)}
                  (\x. &(CARD {c | primitive_character x c}))` THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_MUL; REAL_LE_POW_2]);;

let BDH_ENERGY_POS = prove
 (`!N r. &0 <= bdh_energy N r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[bdh_energy] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; REAL_LE_POW_2]);;

let BDH_REGROUP = prove
 (`!N Q. 1 <= Q
         ==> sum(1..Q) (\q. inv(&(phi q)) *
                            sum {r | r divides q /\ ~(r = 1)}
                                (\r. bdh_energy N r))
             <= sum(1..Q) (\r. if r = 1 then &0
                               else inv(&(phi r)) * bdh_energy N r *
                                    &4 * (&1 + log(&Q / &r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r d:num. bdh_energy N r`; `Q:num`] BILINEAR_REINDEX) THEN
  REWRITE_TAC[BDH_ENERGY_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  ONCE_REWRITE_TAC[SUM_HYPERBOLA_SWAP] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; SUM_0; REAL_LE_REFL] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  TRANS_TAC REAL_LE_TRANS
   `(&4 * (&1 + log(&Q / &r))) * (inv(&(phi r)) * bdh_energy N r)` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[BDH_ENERGY_POS; REAL_LE_INV_EQ; REAL_POS]] THEN
  SUBGOAL_THEN `1 <= Q DIV r` ASSUME_TAC THENL
   [ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= r ==> ~(r = 0)`] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&4 * (&1 + log(&(Q DIV r)))` THEN
  ASM_SIMP_TAC[SUM_INV_PHI_LE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &r` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[DIV_MUL_LE]);;

(* ------------------------------------------------------------------------- *)
(* Large conductors: the large sieve on dyadic blocks.                       *)
(* ------------------------------------------------------------------------- *)

let DYADIC_SUM_SPLIT = prove
 (`!f J. sum(1..2 EXP J) f =
         f 1 + sum {j | j < J} (\j. sum(2 EXP j + 1..2 EXP (j + 1)) f)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[EXP; SUM_SING_NUMSEG; LT; EMPTY_GSPEC; SUM_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{j | j < SUC J} = J INSERT {j | j < J:num}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  SUBGOAL_THEN `2 EXP SUC J = 2 EXP J + 2 EXP J /\
                2 EXP (J + 1) = 2 EXP J + 2 EXP J`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXP; EXP_ADD; EXP_1] THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  ASM_REWRITE_TAC[REAL_ADD_AC]);;

let GEOM_TAIL_DYADIC = prove
 (`!R0. 1 <= R0
        ==> !J. sum {j | j < J /\ R0 < 2 EXP (j + 1)} (\j. inv(&2 pow j)) <=
                (if R0 < 2 EXP J then &4 / &R0 - &2 / &2 pow J else &0)`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; SUM_CLAUSES; EXP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `s = sum {j | j < J /\ R0 < 2 EXP (j + 1)}
                     (\j. inv(&2 pow j))` THEN
  SUBGOAL_THEN `sum {j | j < SUC J /\ R0 < 2 EXP (j + 1)} (\j. inv(&2 pow j)) =
                (if R0 < 2 EXP (J + 1) then inv(&2 pow J) + s else s)`
  SUBST1_TAC THENL
   [COND_CASES_TAC THENL
     [SUBGOAL_THEN `{j | j < SUC J /\ R0 < 2 EXP (j + 1)} =
                    J INSERT {j | j < J /\ R0 < 2 EXP (j + 1)}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM; LT] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `FINITE {j | j < J /\ R0 < 2 EXP (j + 1)}` ASSUME_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < J:num}` THEN
        REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "s" THEN ASM_SIMP_TAC[SUM_CLAUSES; IN_ELIM_THM; LT_REFL];
      EXPAND_TAC "s" THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; LT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow J /\ &1 <= &R0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
                    ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / &2 pow SUC J = inv(&2 pow J)` SUBST1_TAC THENL
   [REWRITE_TAC[real_pow] THEN UNDISCH_TAC `&0 < &2 pow J` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (J + 1) = 2 EXP SUC J` SUBST1_TAC THENL
   [REWRITE_TAC[ADD1]; ALL_TAC] THEN
  ASM_CASES_TAC `R0 < 2 EXP SUC J` THEN ASM_REWRITE_TAC[] THENL
   [ASM_CASES_TAC `R0 < 2 EXP J` THENL
     [UNDISCH_TAC `s <= (if R0 < 2 EXP J then &4 / &R0 - &2 / &2 pow J
                         else &0)` THEN
      ASM_REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `s <= (if R0 < 2 EXP J then &4 / &R0 - &2 / &2 pow J
                         else &0)` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&2 * inv(&2 pow J) <= &4 / &R0` MP_TAC THENL
       [SUBGOAL_THEN `&R0 <= &2 * &2 pow J` ASSUME_TAC THENL
         [UNDISCH_TAC `R0 < 2 EXP SUC J` THEN
          REWRITE_TAC[EXP; REAL_OF_NUM_POW; REAL_OF_NUM_MUL;
                      REAL_OF_NUM_LE] THEN ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `&2 * inv(&2 pow J) = &4 * inv(&2 * &2 pow J)`
        SUBST1_TAC THENL
         [UNDISCH_TAC `&0 < &2 pow J` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    UNDISCH_TAC `s <= (if R0 < 2 EXP J then &4 / &R0 - &2 / &2 pow J
                       else &0)` THEN
    SUBGOAL_THEN `~(R0 < 2 EXP J)` (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `~(R0 < 2 EXP SUC J)` THEN REWRITE_TAC[EXP] THEN
    ARITH_TAC]);;

let BDH_LARGE_SIEVE = prove
 (`!N R. 1 <= R
         ==> sum(1..R) (\r. &r / &(phi r) * bdh_energy N r) <=
             (&4 * &N + &36 * &R pow 2) *
             sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:num`; `N:num`;
                 `\n. Cx(if prime n then log(&n) else &0)`]
                LARGE_SIEVE_MULTIPLICATIVE) THEN
  ASM_REWRITE_TAC[VSUM_THETA_CHAR; bdh_energy] THEN
  MATCH_MP_TAC(REAL_ARITH `!a b c:real. b = c ==> a <= b ==> a <= c`) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
  REWRITE_TAC[COND_RAND; COND_RATOR] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

let BDH_BLOCK_BOUND = prove
 (`!N Q R0 j.
     1 <= R0
     ==> sum(2 EXP j + 1..2 EXP (j + 1))
           (\r. if R0 < r /\ r <= Q
                then inv(&(phi r)) * bdh_energy N r * (&1 + log(&Q / &r))
                else &0)
         <= (if R0 < 2 EXP (j + 1) /\ 2 EXP j < Q
             then (&1 + log(&Q / &2 pow j)) * inv(&2 pow j) *
                  (&4 * &N + &36 * &4 pow (j + 1)) *
                  sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)
             else &0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN ASM_ARITH_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 + log(&Q / &2 pow j)` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(2 EXP j + 1..2 EXP (j + 1))
      (\r. ((&1 + log(&Q / &2 pow j)) * inv(&2 pow j)) *
           (&r / &(phi r) * bdh_energy N r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= &r / &(phi r) * bdh_energy N r` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[BDH_ENERGY_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)) THEN
    SUBGOAL_THEN `&0 < &r /\ &2 pow j <= &r /\ &r <= &Q` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(&(phi r)) * bdh_energy N r * (&1 + log(&Q / &r)) =
                  (inv(&r) * (&1 + log(&Q / &r))) *
                  (&r / &(phi r) * bdh_energy N r)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < &r` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[]]];
    REWRITE_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(1..2 EXP (j + 1)) (\r. &r / &(phi r) * bdh_energy N r)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
        REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[BDH_ENERGY_POS] THEN MATCH_MP_TAC REAL_LE_DIV THEN
        REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`N:num`; `2 EXP (j + 1)`] BDH_LARGE_SIEVE) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM REAL_POW_MUL; REAL_POW_POW] THEN
    REWRITE_TAC[REAL_POW_MUL; GSYM REAL_POW_POW] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[REAL_POW_POW; MULT_SYM] THEN
    SUBGOAL_THEN `&2 pow ((j + 1) * 2) = &4 pow (j + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_POW_POW; REAL_POW_2; GSYM REAL_POW_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      REWRITE_TAC[]]]);;

let SUM_POW2_LT = prove
 (`!n. sum {j | j < n} (\j. &2 pow j) <= &2 pow n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; SUM_CLAUSES; real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{j | j < SUC n} = n INSERT {j | j < n:num}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC(`sum {j | j < n} (\j. &2 pow j)`,`s:real`) THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

let GEOM_LOG_IND = prove
 (`!n. sum {j | j < n} (\j. (&1 + &n - &j) * &2 pow j) <= &3 * &2 pow n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; SUM_CLAUSES; real_pow] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{j | j < SUC n} = n INSERT {j | j < n:num}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  SUBGOAL_THEN
   `sum {j | j < n} (\j. (&1 + (&n + &1) - &j) * &2 pow j) =
    sum {j | j < n} (\j. (&1 + &n - &j) * &2 pow j) +
    sum {j | j < n} (\j. &2 pow j)` SUBST1_TAC THENL
   [SIMP_TAC[GSYM SUM_ADD; FINITE_NUMSEG_LT] THEN MATCH_MP_TAC SUM_EQ THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` SUM_POW2_LT) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_comb o concl)) THEN
  SPEC_TAC(`sum {j | j < n} (\j. (&1 + &n - &j) * &2 pow j)`,`a:real`) THEN
  SPEC_TAC(`sum {j | j < n} (\j. &2 pow j)`,`b:real`) THEN
  REWRITE_TAC[real_pow] THEN REAL_ARITH_TAC);;

let GEOM_LOG_DYADIC = prove
 (`!Q J. 1 <= Q
         ==> sum {j | j < J /\ 2 EXP j < Q}
               (\j. (&1 + log(&Q / &2 pow j)) * &2 pow j) <= &6 * &Q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\k. Q <= 2 EXP k` num_WOP) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [EXISTS_TAC `Q:num` THEN MESON_TAC[LT_POW2_REFL; LT_IMP_LE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `2 EXP K0 < 2 * Q` ASSUME_TAC THENL
   [ASM_CASES_TAC `K0 = 0` THENL
     [ASM_REWRITE_TAC[EXP] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `K0 - 1`) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 < k`; NOT_LE] THEN
      SUBGOAL_THEN `2 EXP K0 = 2 * 2 EXP (K0 - 1)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
        ARITH_TAC]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {j | j < J /\ 2 EXP j < Q} (\j. (&1 + &K0 - &j) * &2 pow j)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    TRANS_TAC REAL_LE_TRANS
     `sum {j | j < K0} (\j. (&1 + &K0 - &j) * &2 pow j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `j:num` THEN
        STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
        SUBGOAL_THEN `2 EXP K0 <= 2 EXP j` MP_TAC THENL
         [ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ASM_ARITH_TAC];
        REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        REWRITE_TAC[REAL_ARITH `&0 <= &1 + a - b <=> b <= a + &1`] THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS `&3 * &2 pow K0` THEN
      REWRITE_TAC[GEOM_LOG_IND] THEN
      UNDISCH_TAC `2 EXP K0 < 2 * Q` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW;
                  GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC]] THEN
  MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < J:num}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[REAL_ARITH `&1 + a - b = &1 + (a - b)`] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
  SUBGOAL_THEN `j < K0:num` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `2 EXP K0 <= 2 EXP j` MP_TAC THENL
     [ASM_REWRITE_TAC[LE_EXP] THEN ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &2 pow j` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `log(&2 pow (K0 - j))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      REWRITE_TAC[GSYM REAL_POW_ADD] THEN
      ASM_SIMP_TAC[ARITH_RULE `j < k ==> k - j + j = k:num`] THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE]];
    SIMP_TAC[LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; LT_IMP_LE] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    MP_TAC LOG_2_UPPER THEN
    REWRITE_TAC[REAL_SUB_LE; REAL_OF_NUM_LE] THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN REAL_ARITH_TAC]);;

let BDH_LARGE = prove
 (`!N Q R0.
     1 <= R0 /\ R0 <= Q
     ==> sum(1..Q) (\r. if R0 < r
                        then inv(&(phi r)) * bdh_energy N r *
                             (&1 + log(&Q / &r))
                        else &0)
         <= (&16 * &N * (&1 + log(&Q)) / &R0 + &864 * &Q) *
            sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `W = sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)` THEN
  SUBGOAL_THEN `&0 <= W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_ATMOST; REAL_LE_POW_2];
    ALL_TAC] THEN
  ABBREV_TAC `f = \r. if R0 < r /\ r <= Q
                      then inv(&(phi r)) * bdh_energy N r * (&1 + log(&Q / &r))
                      else &0` THEN
  SUBGOAL_THEN
   `sum(1..Q) (\r. if R0 < r
                   then inv(&(phi r)) * bdh_energy N r * (&1 + log(&Q / &r))
                   else &0) = sum(1..2 EXP Q) f`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `2 EXP Q = Q + (2 EXP Q - Q)` SUBST1_TAC THENL
     [MP_TAC(SPEC `Q:num` LT_POW2_REFL) THEN ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[SUM_ADD_SPLIT; ARITH_RULE `1 <= Q + 1`] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c:real. a = b /\ c = &0 ==> a = b + c`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      EXPAND_TAC "f" THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DYADIC_SUM_SPLIT] THEN
  SUBGOAL_THEN `(f:num->real) 1 = &0` SUBST1_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {j | j < Q}
      (\j. if R0 < 2 EXP (j + 1) /\ 2 EXP j < Q
           then (&1 + log(&Q / &2 pow j)) * inv(&2 pow j) *
                (&4 * &N + &36 * &4 pow (j + 1)) * W
           else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN EXPAND_TAC "f" THEN
    EXPAND_TAC "W" THEN MATCH_MP_TAC BDH_BLOCK_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ABBREV_TAC
   `S = {j | j IN {j | j < Q} /\ R0 < 2 EXP (j + 1) /\ 2 EXP j < Q}` THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j IN S
        ==> (&1 + log(&Q / &2 pow j)) * inv(&2 pow j) *
            (&4 * &N + &36 * &4 pow (j + 1)) * W =
            (&1 + log(&Q / &2 pow j)) * inv(&2 pow j) * &4 * &N * W +
            &144 * W * ((&1 + log(&Q / &2 pow j)) * &2 pow j)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &2 pow j` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&4 pow (j + 1) = &4 * &2 pow j * &2 pow j` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_ADD; REAL_POW_1; GSYM REAL_POW_MUL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_EQ; SUM_ADD] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_ADD_RDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum S (\x. (&1 + log(&Q)) * inv(&2 pow x) * &4 * &N * W)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `j:num` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
        SUBGOAL_THEN `&1 <= &2 pow j /\ &1 <= &Q` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC;
            REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
          ALL_TAC] THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
          GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
      SUBGOAL_THEN `&0 <= &1 + log(&Q)` ASSUME_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
        MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS
       `sum {j | j < Q /\ R0 < 2 EXP (j + 1)}
          (\x. (&1 + log(&Q)) * inv(&2 pow x) * &4 * &N * W)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < Q:num}` THEN
          REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
          EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          MESON_TAC[];
          REPEAT STRIP_TAC THEN BETA_TAC THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_REWRITE_TAC[REAL_POS; REAL_LE_INV_EQ] THEN
          MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      REWRITE_TAC[SUM_LMUL; SUM_RMUL] THEN
      MP_TAC(SPEC `R0:num` GEOM_TAIL_DYADIC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `Q:num`) THEN
      ABBREV_TAC `T1 = sum {j | j < Q /\ R0 < 2 EXP (j + 1)}
                           (\j. inv(&2 pow j))` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `T1 <= &4 / &R0` ASSUME_TAC THENL
       [UNDISCH_TAC `T1 <= (if R0 < 2 EXP Q then &4 / &R0 - &2 / &2 pow Q
                            else &0)` THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THENL
         [MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= a - y ==> x <= a`) THEN
          MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
          MATCH_MP_TAC(REAL_ARITH `&0 <= a ==> x <= &0 ==> x <= a`) THEN
          MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]];
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `(&1 + log(&Q)) * (&4 / &R0 * &4 * &N * W)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        ASM_REWRITE_TAC[REAL_POS];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div] THEN
        REAL_ARITH_TAC]];
    REWRITE_TAC[SUM_LMUL] THEN
    SUBGOAL_THEN
     `sum S (\x. (&1 + log(&Q / &2 pow x)) * &2 pow x) <= &6 * &Q`
    MP_TAC THENL
     [TRANS_TAC REAL_LE_TRANS
       `sum {j | j < Q /\ 2 EXP j < Q}
          (\x. (&1 + log(&Q / &2 pow x)) * &2 pow x)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{j | j < Q:num}` THEN
          REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
          EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          MESON_TAC[];
          REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC REAL_LE_MUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
          MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
          MATCH_MP_TAC LOG_POS THEN
          SUBGOAL_THEN `&0 < &2 pow x` ASSUME_TAC THENL
           [MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
          REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
        MATCH_MP_TAC GEOM_LOG_DYADIC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    ABBREV_TAC `T2 = sum S (\x. (&1 + log(&Q / &2 pow x)) * &2 pow x)` THEN
    DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `&144 * (W * (&6 * &Q))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]]);;

let BDH_LARGE_ALL = prove
 (`!N Q R0.
     1 <= R0 /\ 1 <= Q
     ==> sum(1..Q) (\r. if R0 < r
                        then inv(&(phi r)) * bdh_energy N r *
                             (&1 + log(&Q / &r))
                        else &0)
         <= (&16 * &N * (&1 + log(&Q)) / &R0 + &864 * &Q) *
            sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `R0 <= Q:num` THENL
   [MATCH_MP_TAC BDH_LARGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..Q) (\r. if R0 < r
                   then inv(&(phi r)) * bdh_energy N r * (&1 + log(&Q / &r))
                   else &0) = &0`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC];
    MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_ATMOST; REAL_LE_POW_2]]);;

(* ------------------------------------------------------------------------- *)
(* Small conductors: the Siegel-Walfisz theorem.                             *)
(* ------------------------------------------------------------------------- *)

let BDH_SMALL_ENERGY = prove
 (`!A B. ?Cb. !N r.
     2 <= N /\ 2 <= r /\ &r <= log(&N) pow B
     ==> bdh_energy N r <= &(phi r) * (Cb * &N / log(&N) pow A) pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`A:num`; `B:num`] SIEGEL_WALFISZ_THETA) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN EXISTS_TAC `Cb:real` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[bdh_energy] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {c | primitive_character r c}
        (\c:num->complex. (Cb * &N / log(&N) pow A) pow 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_PRIMITIVE_CHARACTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    REWRITE_TAC[GSYM VSUM_THETA_CHAR] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`&N:real`; `r:num`; `c:num->complex`; `N:num`]) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      ASM_MESON_TAC[primitive_character];
      MATCH_MP_TAC PRIMITIVE_CHARACTER_NONPRINCIPAL THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    SIMP_TAC[SUM_CONST; FINITE_PRIMITIVE_CHARACTERS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    MATCH_MP_TAC CARD_PRIMITIVE_CHARACTERS_LE THEN ASM_ARITH_TAC]);;

let BDH_SMALL = prove
 (`!A B. ?Cb. !N Q R0.
     2 <= N /\ 1 <= Q /\ &R0 <= log(&N) pow B
     ==> sum(1..Q) (\r. if ~(r = 1) /\ r <= R0
                        then inv(&(phi r)) * bdh_energy N r *
                             (&1 + log(&Q / &r))
                        else &0)
         <= &R0 * (&1 + log(&Q)) * (Cb * &N / log(&N) pow A) pow 2`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`A:num`; `B:num`] BDH_SMALL_ENERGY) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN EXISTS_TAC `Cb:real` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  ABBREV_TAC `S = (Cb * &N / log(&N) pow A) pow 2` THEN
  SUBGOAL_THEN `&0 <= S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[REAL_LE_POW_2]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum {r | r IN 1..Q /\ ~(r = 1) /\ r <= R0}
        (\r. (&1 + log(&Q)) * S)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &(phi r)` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
      MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &r /\ &r <= &Q` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[BDH_ENERGY_POS; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      EXPAND_TAC "S" THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `&R0` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC LOG_POS THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> &1 + x <= &1 + y`) THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      SUBGOAL_THEN `&0 < &Q` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]]);;

let BDH_CONDUCTOR_SPLIT = prove
 (`!N Q R0.
     1 <= Q /\ 1 <= R0
     ==> sum(1..Q) (\q. inv(&(phi q)) *
                        sum {r | r divides q /\ ~(r = 1)}
                            (\r. bdh_energy N r))
         <= &4 * sum(1..Q) (\r. if ~(r = 1) /\ r <= R0
                                then inv(&(phi r)) * bdh_energy N r *
                                     (&1 + log(&Q / &r))
                                else &0) +
            &4 * sum(1..Q) (\r. if R0 < r
                                then inv(&(phi r)) * bdh_energy N r *
                                     (&1 + log(&Q / &r))
                                else &0)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..Q) (\r. if r = 1 then &0
                   else inv(&(phi r)) * bdh_energy N r *
                        &4 * (&1 + log(&Q / &r)))` THEN
  ASM_SIMP_TAC[BDH_REGROUP] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  ASM_CASES_TAC `r = 1` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  ASM_CASES_TAC `r <= R0:num` THEN ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  COND_CASES_TAC THENL [REAL_ARITH_TAC; ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The principal characters and the sum over the moduli.                     *)
(* ------------------------------------------------------------------------- *)

let BDH_W_BOUND = prove
 (`?Cw. &0 <= Cw /\
        !N. 2 <= N
            ==> sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)
                <= Cw * &N * log(&N)`,
  MP_TAC(SPEC `0` PNT_THETA_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN EXISTS_TAC `&1 + abs Cb` THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `log(&N) * sum {p | prime p /\ p <= N} (\p. log(&p))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
    REWRITE_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&N:real`; `N:num`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_LE_REFL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_pow; REAL_DIV_1] THEN
  ABBREV_TAC `th = sum {p | prime p /\ p <= N} (\p. log(&p))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `Cb * &N <= abs Cb * &N` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `th <= (&1 + abs Cb) * &N` MP_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
    (ASSUME `&0 <= log(&N)`)) THEN
  REAL_ARITH_TAC);;

let BDH_PRINCIPAL_SQ = prove
 (`!N q. 1 <= q
         ==> (sum {p | prime p /\ p <= N /\ coprime(p,q)} (\p. log(&p)) -
              &N) pow 2
             <= &2 * (sum {p | prime p /\ p <= N} (\p. log(&p)) - &N) pow 2 +
                &2 * log(&q) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{p | prime p /\ p <= N}`; `\p:num. coprime(p,q)`;
                 `\p:num. log(&p)`; `\p:num. log(&p)`] SUM_CASES) THEN
  REWRITE_TAC[FINITE_ATMOST; COND_ID; IN_ELIM_THM;
              GSYM CONJ_ASSOC; ETA_AX] THEN
  ABBREV_TAC `th = sum {p | prime p /\ p <= N} (\p. log(&p))` THEN
  ABBREV_TAC `t0 = sum {p | prime p /\ p <= N /\ coprime(p,q)}
                       (\p. log(&p))` THEN
  ABBREV_TAC `d = sum {p | prime p /\ p <= N /\ ~coprime(p,q)}
                      (\p. log(&p))` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= d /\ d <= log(&q)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[FINITE_PRIMES_LE_RESTRICT; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum {p | prime p /\ p divides q} (\p. log(&p))` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC LOG_SUM_PRIME_DIVISORS THEN ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{d | d divides q}` THEN
      ASM_SIMP_TAC[FINITE_DIVISORS; ARITH_RULE `1 <= q ==> ~(q = 0)`] THEN
      SET_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[PRIME_COPRIME_STRONG];
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t0 - &N = (th - &N) + --d` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`th - &N:real`; `--d:real`] SQUARE_SUM_LE) THEN
  MP_TAC(SPECL [`2`; `d:real`; `log(&q)`] REAL_POW_LE2) THEN
  ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN REAL_ARITH_TAC);;

let BDH_Q_BOUND2 = prove
 (`!N q. 1 <= q
         ==> sum {a | a < q /\ coprime(a,q)}
               (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                         (\p. log(&p)) - &N / &(phi q)) pow 2)
             <= &4 * inv(&(phi q)) *
                sum {r | r divides q /\ ~(r = 1)} (\r. bdh_energy N r) +
                &8 * &q / &(phi q) * log(&q) pow 2 +
                &4 * (sum {p | prime p /\ p <= N} (\p. log(&p)) - &N) pow 2 *
                inv(&(phi q))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `q:num`] BDH_Q_BOUND) THEN
  MP_TAC(SPECL [`N:num`; `q:num`] BDH_PRINCIPAL_SQ) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv(&(phi q))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n ==> 0 < n`) THEN
    MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ABBREV_TAC `X = sum {a | a < q /\ coprime(a,q)}
                    (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                              (\p. log(&p)) - &N * inv(&(phi q))) pow 2)` THEN
  ABBREV_TAC `Y = sum {r | r divides q /\ ~(r = 1)} (\r. bdh_energy N r)` THEN
  ABBREV_TAC `t0 = sum {p | prime p /\ p <= N /\ coprime(p,q)}
                       (\p. log(&p))` THEN
  ABBREV_TAC `th = sum {p | prime p /\ p <= N} (\p. log(&p))` THEN
  ABBREV_TAC `ip = inv(&(phi q))` THEN
  ABBREV_TAC `L = log(&q)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(t0 - &N) pow 2 * ip <=
                (&2 * (th - &N) pow 2 + &2 * L pow 2) * ip`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&q - &1) * L pow 2 * ip` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_POW_2; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let BDH_SUM_Q = prove
 (`!N Q. 1 <= Q
         ==> sum(1..Q)
               (\q. sum {a | a < q /\ coprime(a,q)}
                      (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                                (\p. log(&p)) - &N / &(phi q)) pow 2))
             <= &4 * sum(1..Q) (\q. inv(&(phi q)) *
                                    sum {r | r divides q /\ ~(r = 1)}
                                        (\r. bdh_energy N r)) +
                &32 * &Q * log(&Q) pow 2 +
                &16 * (sum {p | prime p /\ p <= N} (\p. log(&p)) - &N)
                      pow 2 * (&1 + log(&Q))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `th = sum {p | prime p /\ p <= N} (\p. log(&p))` THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..Q) (\q. &4 * inv(&(phi q)) *
                   sum {r | r divides q /\ ~(r = 1)} (\r. bdh_energy N r) +
                   &8 * &q / &(phi q) * log(&q) pow 2 +
                   &4 * (th - &N) pow 2 * inv(&(phi q)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    EXPAND_TAC "th" THEN MATCH_MP_TAC BDH_Q_BOUND2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_LMUL] THEN
  ABBREV_TAC `Y = sum(1..Q) (\q. inv(&(phi q)) *
                                 sum {r | r divides q /\ ~(r = 1)}
                                     (\r. bdh_energy N r))` THEN
  SUBGOAL_THEN `&0 <= log(&Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1..Q) (\q. &q / &(phi q) * log(&q) pow 2) <= &4 * &Q * log(&Q) pow 2`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `sum(1..Q) (\q. &q / &(phi q) * log(&Q) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
      REWRITE_TAC[SUM_RMUL] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[SUM_PHI_RATIO_LE; REAL_LE_POW_2]];
    ALL_TAC] THEN
  MP_TAC(SPEC `Q:num` SUM_INV_PHI_LE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
    (SPEC `th - &N:real` REAL_LE_POW_2)) THEN
  ABBREV_TAC `Z = sum(1..Q) (\q. &q / &(phi q) * log(&q) pow 2)` THEN
  ABBREV_TAC `V = sum(1..Q) (\q. inv(&(phi q)))` THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Barban-Davenport-Halberstam theorem.                                  *)
(* ------------------------------------------------------------------------- *)

let BDH_ARITH_SMALL = prove
 (`!s r0 lq L P c.
     &1 <= L /\ &1 <= P /\ &0 <= lq /\ lq <= L /\ &0 <= r0 /\
     r0 <= P * L pow 2 /\ s <= r0 * (&1 + lq) * (c / (P * L pow 2)) pow 2
     ==> s <= &2 * c pow 2 / P`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `r0 * (&1 + lq) * (c / (P * L pow 2)) pow 2` THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS
   `(P * L pow 2) * (&2 * L) * (c / (P * L pow 2)) pow 2` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(P * L pow 2) * (&2 * L) * (c / (P * L pow 2)) pow 2 =
    (&2 * c pow 2 / P) * inv L`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(P = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_INV_LE_1] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

let BDH_ARITH_LARGE = prove
 (`!g W N Q L P r0 lq Cw.
     &1 <= L /\ &1 <= P /\ &0 <= lq /\ lq <= L /\ &0 < r0 /\
     P * L pow 2 <= &2 * r0 /\ &0 <= N /\ &0 <= Q /\ &0 <= W /\
     W <= Cw * N * L /\
     g <= (&16 * N * (&1 + lq) / r0 + &864 * Q) * W
     ==> g <= &64 * Cw * N pow 2 / P + &864 * Cw * N * Q * L`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&16 * N * (&1 + lq) / r0 + &864 * Q) * W` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < P /\ &0 < L` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + lq) / r0 <= &4 / (P * L)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `&4 / (P * L) * r0 = (&4 * r0) / (P * L)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_MUL] THEN
    TRANS_TAC REAL_LE_TRANS `(&2 * L) * (P * L)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MP_TAC(ASSUME `P * L pow 2 <= &2 * r0`) THEN
      REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * N * (&1 + lq) / r0 <= &64 * N / (P * L)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&64 * N / (P * L) = &16 * N * &4 / (P * L)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(&64 * N / (P * L) + &864 * Q) * W` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(&64 * N / (P * L) + &864 * Q) * (Cw * N * L)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    UNDISCH_TAC `&0 < P` THEN UNDISCH_TAC `&0 < L` THEN
    CONV_TAC REAL_FIELD]);;

let BDH_ARITH_PRINC = prove
 (`!d c L P lq.
     &1 <= L /\ &1 <= P /\ &0 <= lq /\ lq <= L /\ abs d <= c / (P * L)
     ==> &16 * d pow 2 * (&1 + lq) <= &32 * c pow 2 / P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(d:real) pow 2 <= (c / (P * L)) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`2`; `abs(d:real)`; `c / (P * L):real`] REAL_POW_LE2) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS; REAL_POW2_ABS];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&16 * (c / (P * L)) pow 2 * (&2 * L)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&16 * (c / (P * L)) pow 2 * (&2 * L) = (&32 * c pow 2 / P) * inv(P * L)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `~(P = &0) /\ ~(L = &0)` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LE_1 THEN
    MP_TAC(SPECL [`&1:real`; `P:real`; `&1:real`; `L:real`] REAL_LE_MUL2) THEN
    ASM_REAL_ARITH_TAC]);;

let BDH_MAIN = prove
 (`!A. ?B. !N Q.
     3 <= N /\ 1 <= Q /\ Q <= N
     ==> sum(1..Q)
           (\q. sum {a | a < q /\ coprime(a,q)}
                  (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                            (\p. log(&p)) - &N / &(phi q)) pow 2))
         <= B * (&N * &Q * log(&N) + &N pow 2 / log(&N) pow A)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`A + 2`; `A + 2`] BDH_SMALL) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cb:real`) THEN
  MP_TAC BDH_W_BOUND THEN
  DISCH_THEN(X_CHOOSE_THEN `Cw:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `A + 1` PNT_THETA_UNIFORM) THEN
  DISCH_THEN(X_CHOOSE_TAC `Cp:real`) THEN
  EXISTS_TAC `&32 * Cb pow 2 + &32 * Cp pow 2 + &14848 * Cw + &32` THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `Q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [MP_TAC LOG_3_LOWER THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> &5493 / &5000 <= b ==> &1 <= c`) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `log(&N) pow (A + 2)` FLOOR_POS) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `R0:num`) THEN
  MP_TAC(SPEC `log(&N) pow (A + 2)` FLOOR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&N) pow (A + 2)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= R0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&0 < &R0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`] BDH_SUM_Q) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`; `R0:num`] BDH_CONDUCTOR_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`N:num`; `Q:num`; `R0:num`] BDH_LARGE_ALL) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `Q:num`; `R0:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&N:real`; `N:num`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; REAL_LE_REFL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `X = sum(1..Q)
          (\q. sum {a | a < q /\ coprime(a,q)}
                 (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                           (\p. log(&p)) - &N / &(phi q)) pow 2))` THEN
  ABBREV_TAC
   `Y = sum(1..Q) (\q. inv(&(phi q)) *
                       sum {r | r divides q /\ ~(r = 1)}
                           (\r. bdh_energy N r))` THEN
  ABBREV_TAC
   `Sm = sum(1..Q) (\r. if ~(r = 1) /\ r <= R0
                        then inv(&(phi r)) * bdh_energy N r *
                             (&1 + log(&Q / &r))
                        else &0)` THEN
  ABBREV_TAC
   `Lg = sum(1..Q) (\r. if R0 < r
                        then inv(&(phi r)) * bdh_energy N r *
                             (&1 + log(&Q / &r))
                        else &0)` THEN
  ABBREV_TAC `W = sum {p | prime p /\ p <= N} (\p. log(&p) pow 2)` THEN
  ABBREV_TAC `th = sum {p | prime p /\ p <= N} (\p. log(&p))` THEN
  ABBREV_TAC `L = log(&N)` THEN
  ABBREV_TAC `lq = log(&Q)` THEN
  ABBREV_TAC `P = (L:real) pow A` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(L:real) pow (A + 2) = P * L pow 2 /\ L pow (A + 1) = P * L`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]; ALL_TAC] THEN
  SUBGOAL_THEN `&R0 <= P * (L:real) pow 2 /\ P * L pow 2 <= &2 * &R0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&R0 <= (L:real) pow (A + 2)` THEN
    UNDISCH_TAC `(L:real) pow (A + 2) < &R0 + &1` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 <= &R0:real` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= P:real` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lq /\ lq <= L /\ L <= &N:real` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lq" THEN EXPAND_TAC "L" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC LOG_LT_X THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &R0:real /\ &0 <= W` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      EXPAND_TAC "W" THEN MATCH_MP_TAC SUM_POS_LE THEN
      REWRITE_TAC[FINITE_ATMOST; REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Sm <= &2 * (Cb * &N) pow 2 / P` ASSUME_TAC THENL
   [MATCH_MP_TAC BDH_ARITH_SMALL THEN
    MAP_EVERY EXISTS_TAC [`&R0:real`; `lq:real`; `L:real`] THEN
    ASM_REWRITE_TAC[REAL_POS] THEN
    UNDISCH_TAC
     `Sm <= &R0 * (&1 + lq) * (Cb * &N / (L:real) pow (A + 2)) pow 2` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `Lg <= &64 * Cw * &N pow 2 / P + &864 * Cw * &N * &Q * L`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BDH_ARITH_LARGE THEN
    MAP_EVERY EXISTS_TAC [`W:real`; `&R0:real`; `lq:real`] THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&16 * (th - &N) pow 2 * (&1 + lq) <= &32 * (Cp * &N) pow 2 / P`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BDH_ARITH_PRINC THEN EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs(th - &N) <= Cp * &N / (L:real) pow (A + 1)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&32 * &Q * lq pow 2 <= &32 * (&N * &Q * L)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&N * &Q * L = &Q * (L * &N)` SUBST1_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    TRANS_TAC REAL_LE_TRANS `(L:real) pow 2` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N * &Q * L /\ &0 <= &N pow 2 / P` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= Cb pow 2 * (&N * &Q * L) /\ &0 <= Cp pow 2 * (&N * &Q * L) /\
    &0 <= Cw * (&N * &Q * L) /\ &0 <= Cw * (&N pow 2 / P)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`X <= &4 * Y + &32 * &Q * lq pow 2 + &16 * (th - &N) pow 2 * (&1 + lq)`;
    `Y <= &4 * Sm + &4 * Lg`;
    `Sm <= &2 * (Cb * &N) pow 2 / P`;
    `Lg <= &64 * Cw * &N pow 2 / P + &864 * Cw * &N * &Q * L`;
    `&16 * (th - &N) pow 2 * (&1 + lq) <= &32 * (Cp * &N) pow 2 / P`;
    `&32 * &Q * lq pow 2 <= &32 * (&N * &Q * L)`;
    `&0 <= &N * &Q * L`; `&0 <= &N pow 2 / P`;
    `&0 <= Cb pow 2 * (&N * &Q * L)`; `&0 <= Cp pow 2 * (&N * &Q * L)`;
    `&0 <= Cw * (&N * &Q * L)`; `&0 <= Cw * (&N pow 2 / P)`] THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let BDH_LHS_POS = prove
 (`!N Q. &0 <= sum(1..Q)
                (\q. sum {a | a < q /\ coprime(a,q)}
                       (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                                 (\p. log(&p)) - &N / &(phi q)) pow 2))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REWRITE_TAC[REAL_LE_POW_2]);;

let BARBAN_DAVENPORT_HALBERSTAM = prove
 (`!A. ?B. !N Q.
     2 <= N /\ 1 <= Q /\ Q <= N
     ==> sum(1..Q)
           (\q. sum {a | a < q /\ coprime(a,q)}
                  (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                            (\p. log(&p)) - &N / &(phi q)) pow 2))
         <= B * (&N * &Q * log(&N) + &N pow 2 / log(&N) pow A)`,
  GEN_TAC THEN MP_TAC(SPEC `A:num` BDH_MAIN) THEN
  DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN
  ABBREV_TAC
   `M = sum(1..2)
          (\Q. sum(1..Q)
                 (\q. sum {a | a < q /\ coprime(a,q)}
                        (\a. (sum {p | prime p /\ p <= 2 /\ (p == a) (mod q)}
                                  (\p. log(&p)) - &2 / &(phi q)) pow 2)))` THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    REWRITE_TAC[BDH_LHS_POS];
    ALL_TAC] THEN
  EXISTS_TAC `max B0 (M / log(&2))` THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `Q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &N * &Q * log(&N) + &N pow 2 / log(&N) pow A`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  ASM_CASES_TAC `N = 2` THENL
   [ALL_TAC;
    TRANS_TAC REAL_LE_TRANS
     `B0 * (&N * &Q * log(&N) + &N pow 2 / log(&N) pow A)` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  TRANS_TAC REAL_LE_TRANS `M:real` THEN CONJ_TAC THENL
   [EXPAND_TAC "M" THEN GEN_REWRITE_TAC RAND_CONV [SUM_2] THEN BETA_TAC THEN
    SUBGOAL_THEN `Q = 1 \/ Q = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
     [MATCH_MP_TAC(REAL_ARITH `!a b:real. &0 <= b ==> a <= a + b`);
      MATCH_MP_TAC(REAL_ARITH `!a b:real. &0 <= a ==> b <= a + b`)] THEN
    REWRITE_TAC[BDH_LHS_POS];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `M / log(&2) * (&2 * &Q * log(&2) + &2 pow 2 / log(&2) pow A)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    SUBGOAL_THEN `M / log(&2) * &2 * &Q * log(&2) = &2 * &Q * M`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < log(&2)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC
     (REAL_ARITH `!a b c:real. a <= b /\ &0 <= c ==> a <= b + c`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `&1 <= &Q` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= (&2 * &Q - &1) * M` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_POW_2; REAL_POW_LE]];
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let BDH_RANGE = prove
 (`!A. ?B. !N Q.
     2 <= N /\ Q <= N /\ &N / log(&N) pow A <= &Q
     ==> sum(1..Q)
           (\q. sum {a | a < q /\ coprime(a,q)}
                  (\a. (sum {p | prime p /\ p <= N /\ (p == a) (mod q)}
                            (\p. log(&p)) - &N / &(phi q)) pow 2))
         <= B * &N * &Q * log(&N)`,
  GEN_TAC THEN MP_TAC(SPEC `A:num` BARBAN_DAVENPORT_HALBERSTAM) THEN
  DISCH_THEN(X_CHOOSE_TAC `B0:real`) THEN
  EXISTS_TAC `&3 * abs B0` THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `Q:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= log(&N)` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log(&2)` THEN CONJ_TAC THENL
     [MP_TAC LOG_2_LOWER THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&N) pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Q` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&0 < &N / log(&N) pow A` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&N / log(&N) pow A <= &Q` THEN
    SUBGOAL_THEN `&0 < &Q ==> &1 <= &Q` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `Q:num`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y:real. y <= z ==> x <= y ==> x <= z`) THEN
  SUBGOAL_THEN `&N pow 2 / log(&N) pow A <= &2 * &N * &Q * log(&N)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&N * &Q` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2; real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REWRITE_TAC[GSYM real_div];
      SUBGOAL_THEN `&2 * &N * &Q * log(&N) = (&N * &Q) * (&2 * log(&N))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `abs B0 * (&N * &Q * log(&N) +
                                     &N pow 2 / log(&N) pow A)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&3 * abs B0) * &N * &Q * log(&N) =
                abs B0 * (&N * &Q * log(&N) + &2 * &N * &Q * log(&N))`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_REAL_ARITH_TAC);;
