(* ========================================================================= *)
(* The upper bound for sum_q S(A_q,P,z) in Chen's theorem ([N] Thm 10.5).    *)
(*                                                                           *)
(* CHEN_SUM_AQ_UPPER_GEN: if chen_sieve_ok h, for every e > 0 and every      *)
(* large even N, with z = N^(1/8) and y = N^(1/3),                           *)
(*   sum_{z <= q < y} S(A_q,P,z) <= (A log 6 / 4 + e) (N / log N) V(z),      *)
(* where A_q is A = gchen_A (h N) N with the weight [q | n], V(z) is the     *)
(* product for chen_g (h N) and A = sieve_A.                                 *)
(*                                                                           *)
(* Method.  Unlike [N], |A_q| is never estimated: the sieve problem A_q is   *)
(* given the density X g(q), X = |A|, so that its remainder at t is the      *)
(* remainder of A at t + {q} (SIEVE_COUNT_DIVIDES).  The remainders over     *)
(* all q are regrouped by SUM_PAIRS_INSERT_LE (each set arises at most |t|   *)
(* <= log N times) and bounded by chen_remainder_ok at z := y with A = 4     *)
(* (CHEN_R_ARITH_LOG).  The main term uses F(s) = A/s on [1,3] and the       *)
(* prime sum                                                                 *)
(*   sum_{z <= q < y} 1/(q log(N^(1/2)/q)) <= (2 log 6 + O(1/log N))/log N   *)
(* (CHEN_Q_SUM), an instance of the general PRIME_SUM_SCALED: for monotone   *)
(* phi with G' = phi(u)/u, sum_{X^a < p <= X^b} phi(log p/log X)/p =         *)
(* G(b) - G(a) + O(1/log X), from Abel summation against Mertens' theorem    *)
(* (PRIME_SUM_ABEL; no Stieltjes integrals).                                 *)
(* ========================================================================= *)

needs "Sieve/chen_lower.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* General lemmas: sums over primes against log log t.                       *)
(* ------------------------------------------------------------------------- *)

let PRIME_SUM_ABEL = prove
 (`!f f' g u v.
        &2 <= u /\ u <= v /\
        (!t. u <= t /\ t <= v ==> (f has_real_derivative f' t) (atreal t)) /\
        ((!t. u <= t /\ t <= v ==> &0 <= f' t) \/
         (!t. u <= t /\ t <= v ==> f' t <= &0)) /\
        (!t. u <= t /\ t <= v
             ==> (g has_real_derivative f t / (t * log t)) (atreal t))
        ==> abs(sum {p | prime p /\ u < &p /\ &p <= v} (\p. f(&p) / &p) -
                (g v - g u))
            <= &50 / log u * (abs(f v) + abs(f v - f u))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\n. if prime n then inv(&n) else &0`;
    `f:real->real`; `f':real->real`;
    `\t. log(log t)`; `\t. inv t * inv(log t)`; `&50 / log u`;
    `v:real`; `u:real`] ABEL_SUMMATION_ASYMPTOTIC) THEN
  REWRITE_TAC[IN_REAL_INTERVAL] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&0 < t /\ &0 < log t` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\t. log(log t)) has_real_derivative f') (atreal t)`)) THEN
      ASM_SIMP_TAC[REAL_MUL_LID];
      MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\t:real. t`; `real_interval[u,v]`]
          REAL_CONTINUOUS_ON_INV) THEN
        REWRITE_TAC[REAL_CONTINUOUS_ON_ID; ETA_AX; IN_REAL_INTERVAL] THEN
        DISCH_THEN MATCH_MP_TAC THEN REPEAT STRIP_TAC THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_CONTINUOUS_ON_INV THEN
        REWRITE_TAC[IN_REAL_INTERVAL] THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_CONTINUOUS_ON_LOG THEN
          REWRITE_TAC[IN_REAL_INTERVAL] THEN REPEAT STRIP_TAC THEN
          ASM_REAL_ARITH_TAC;
          X_GEN_TAC `t:real` THEN STRIP_TAC THEN
          MATCH_MP_TAC(REAL_ARITH `!x:real. &0 < x ==> ~(x = &0)`) THEN
          MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC]];
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[SUM_PRIMES_INTERVAL] THEN
      MP_TAC(SPECL [`u:real`; `t:real`] MERTENS_RECIP_VARIATION) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ABBREV_TAC `S1 = sum {p | prime p /\ &p <= u} (\p. inv(&p))` THEN
      ABBREV_TAC `S2 = sum {p | prime p /\ &p <= t} (\p. inv(&p))` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {n | u < &n /\ &n <= v}
        (\n. (if prime n then inv(&n) else &0) * f(&n)) =
    sum {p | prime p /\ u < &p /\ &p <= v} (\p. f(&p) / &p)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `{p | prime p /\ u < &p /\ &p <= v} =
                  {p | p IN {n | u < &n /\ &n <= v} /\ prime p}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[real_div; REAL_MUL_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[u,v]) (\t. (inv t * inv(log t)) * f t) =
    g v - g u`
  SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\t. f t / (t * log t)` THEN CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_TAC THEN REWRITE_TAC[real_div; REAL_INV_MUL] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC HAS_REAL_DERIVATIVE_ATREAL_WITHIN THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[]);;

let HAS_REAL_DERIVATIVE_LOG_SCALED = prove
 (`!h d X t.
        &1 < X /\ &0 < t /\
        (h has_real_derivative d) (atreal(log t / log X))
        ==> ((\t. h(log t / log X)) has_real_derivative
             d * (inv t * inv(log X))) (atreal t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\t. log t / log X`; `h:real->real`;
                 `inv t * inv(log X)`; `d:real`; `t:real`]
         REAL_DIFF_CHAIN_ATREAL) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC HAS_REAL_DERIVATIVE_RMUL_ATREAL THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG THEN
  ASM_REWRITE_TAC[]);;

let PRIME_SUM_SCALED = prove
 (`!h h' G X a b.
        &1 < X /\ &0 < a /\ a <= b /\ &2 <= exp(a * log X) /\
        (!u. a <= u /\ u <= b
             ==> (h has_real_derivative h' u) (atreal u)) /\
        ((!u. a <= u /\ u <= b ==> &0 <= h' u) \/
         (!u. a <= u /\ u <= b ==> h' u <= &0)) /\
        (!u. a <= u /\ u <= b
             ==> (G has_real_derivative h u / u) (atreal u))
        ==> abs(sum {p | prime p /\ exp(a * log X) < &p /\
                         &p <= exp(b * log X)}
                    (\p. h(log(&p) / log X) / &p) - (G b - G a))
            <= &50 / (a * log X) * (abs(h b) + abs(h b - h a))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < log X` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. exp(a * log X) <= t /\ t <= exp(b * log X)
        ==> &2 <= t /\ &0 < log t /\
            a <= log t / log X /\ log t / log X <= b`
  (LABEL_TAC "rng") THENL
   [X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= t` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. h(log t / log X):real`;
    `\t. h'(log t / log X) * (inv t * inv(log X)):real`;
    `\t. G(log t / log X):real`;
    `exp(a * log X)`; `exp(b * log X)`] PRIME_SUM_ABEL) THEN
  REWRITE_TAC[LOG_EXP] THEN
  SUBGOAL_THEN `(a * log X) / log X = a /\ (b * log X) / log X = b`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `&0 < log X` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "rng" (MP_TAC o SPEC `t:real`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MATCH_MP_TAC HAS_REAL_DERIVATIVE_LOG_SCALED THEN
    ASM_SIMP_TAC[REAL_ARITH `&2 <= t ==> &0 < t`];
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "rng" (MP_TAC o SPEC `t:real`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    (SUBGOAL_THEN `&0 < inv t * inv(log X)` ASSUME_TAC THENL
      [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN
       MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
       ALL_TAC]) THEN
    REWRITE_TAC[REAL_ARITH `(x:real) * c <= &0 <=> &0 <= --x * c`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_NEG_GE0] THEN ASM_SIMP_TAC[];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN
    USE_THEN "rng" (MP_TAC o SPEC `t:real`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MP_TAC(ISPECL [`G:real->real`; `h(log t / log X) / (log t / log X)`;
                   `X:real`; `t:real`] HAS_REAL_DERIVATIVE_LOG_SCALED) THEN
    ASM_SIMP_TAC[REAL_ARITH `&2 <= t ==> &0 < t`] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC [`&0 < log t`; `&0 < log X`; `&2 <= t`] THEN
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Other general lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let ROOT_NOT_PRIME = prove
 (`!N k q. EVEN N /\ 1 <= k /\ 2 EXP k < N /\ prime q
           ==> ~(&q = exp(&1 / &k * log(&N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q EXP k = N` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_POW] THEN
    ASM_REWRITE_TAC[GSYM REAL_EXP_N] THEN
    SUBGOAL_THEN `&k * &1 / &k * log(&N) = log(&N)` SUBST1_TAC THENL
     [SUBGOAL_THEN `~(&k = &0)` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD];
      MATCH_MP_TAC EXP_LOG THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP PRIME_ODD) THENL
   [UNDISCH_TAC `2 EXP k < q EXP k` THEN ASM_REWRITE_TAC[LT_REFL];
    UNDISCH_TAC `EVEN(q EXP k)` THEN
    ASM_REWRITE_TAC[EVEN_EXP; GSYM NOT_ODD]]);;

let SIEVE_COUNT_DIVIDES = prove
 (`!A q t. sieve_count A (\n. if q divides n then &1 else &0) t =
           sieve_count A (\n. &1) (q INSERT t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sieve_count; GSYM SUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[]);;

let SUM_PAIRS_INSERT_LE = prove
 (`!(Q:A->bool) U S f.
        FINITE Q /\ (!q. q IN Q ==> FINITE(U q)) /\ FINITE S /\
        (!s. s IN S ==> FINITE s /\ &0 <= f s) /\
        (!q t. q IN Q /\ t IN U q ==> ~(q IN t) /\ (q INSERT t) IN S)
        ==> sum Q (\q. sum (U q) (\t. f(q INSERT t))) <=
            sum S (\s. &(CARD s) * f s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT] THEN
  ABBREV_TAC `P = {q,t | (q:A) IN Q /\ (t:A->bool) IN U q}` THEN
  SUBGOAL_THEN `FINITE(P:A#(A->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(q:A,t:A->bool). q INSERT t`;
                 `\(q:A,t:A->bool). f(q INSERT t):real`;
                 `P:A#(A->bool)->bool`; `S:(A->bool)->bool`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum {x | x IN P /\ (\(q:A,t:A->bool). q INSERT t) x = s}
        (\(q:A,t:A->bool). f(q INSERT t)) =
    sum {x | x IN P /\ (\(q:A,t:A->bool). q INSERT t) x = s} (\x. f s)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN P /\ (\(q:A,t:A->bool). q INSERT t) x = s} SUBSET
    IMAGE (\q. q,s DELETE q) s`
  ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM;
                IN_IMAGE; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`q:A`; `t:A->bool`] THEN STRIP_TAC THEN
    EXISTS_TAC `q:A` THEN
    SUBGOAL_THEN `~((q:A) IN t)` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(q:A) INSERT t = s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:A->bool) /\ &0 <= f s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {x | x IN P /\ (\(q:A,t:A->bool). q INSERT t) x = s}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\q. (q:A),s DELETE q) s` THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\q. (q:A),s DELETE q) s)` THEN
  ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_IMAGE; CARD_SUBSET]);;

let CARD_LOG_NPRODUCT = prove
 (`!s. FINITE s /\ (!p. p IN s ==> prime p)
       ==> &(CARD s) * log(&2) <= log(&(nproduct s (\p. p)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `2 EXP CARD(s:num->bool) <= nproduct s (\p. p)` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM NPRODUCT_CONST] THEN MATCH_MP_TAC NPRODUCT_LE THEN
    ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN DISCH_TAC THEN
  SUBGOAL_THEN `log(&2 pow CARD(s:num->bool)) <= log(&(nproduct s (\p. p)))`
  MP_TAC THENL
   [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN REAL_ARITH_TAC;
    SIMP_TAC[LOG_POW; REAL_ARITH `&0 < &2`]]);;

let REAL_POW5_LINEAR = prove
 (`!h. &0 <= h /\ h <= &1 ==> (&1 + h) pow 5 <= &1 + &31 * h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k. 1 <= k ==> h pow k <= h` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `2` (ASSUME `!k. 1 <= k ==> h pow k <= h`)) THEN
  MP_TAC(SPEC `3` (ASSUME `!k. 1 <= k ==> h pow k <= h`)) THEN
  MP_TAC(SPEC `4` (ASSUME `!k. 1 <= k ==> h pow k <= h`)) THEN
  MP_TAC(SPEC `5` (ASSUME `!k. 1 <= k ==> h pow k <= h`)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  SUBGOAL_THEN `(&1 + h) pow 5 = &1 + &5 * h + &10 * h pow 2 +
                &10 * h pow 3 + &5 * h pow 4 + h pow 5`
  SUBST1_TAC THENL [REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The prime sum over z <= q < y.                                            *)
(* ------------------------------------------------------------------------- *)

let CHEN_Q_SUM = prove
 (`!N. EVEN N /\ 256 < N
       ==> sum {q | prime q /\ exp(&1 / &8 * log(&N)) <= &q /\
                    &q < exp(&1 / &3 * log(&N))}
               (\q. inv(&1 / &2 - log(&q) / log(&N)) / &q)
           <= &2 * log(&6) + &4000 / log(&N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{q | prime q /\ exp(&1 / &8 * log(&N)) <= &q /\
         &q < exp(&1 / &3 * log(&N))} =
    {q | prime q /\ exp(&1 / &8 * log(&N)) < &q /\
         &q <= exp(&1 / &3 * log(&N))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `q:num` THEN
    ASM_CASES_TAC `prime q` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(&q = exp(&1 / &8 * log(&N))) /\
                  ~(&q = exp(&1 / &3 * log(&N)))` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ROOT_NOT_PRIME THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log(&N) /\ &8 * log(&2) <= log(&N)` STRIP_ASSUME_TAC
  THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\u. inv(&1 / &2 - u)`; `\u. inv((&1 / &2 - u) pow 2)`;
    `\u. &2 * (log u - log(&1 / &2 - u))`; `&N`; `&1 / &8`; `&1 / &3`]
   PRIME_SUM_SCALED) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\u. inv(&1 / &2 - u)) has_real_derivative f') (atreal u)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      DISJ1_TAC THEN X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[REAL_LE_POW_2];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      MP_TAC(DISCH_ALL(REAL_DIFF_CONV
        `((\u. &2 * (log u - log(&1 / &2 - u))) has_real_derivative f')
         (atreal u)`)) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `~(u = &0) /\ ~(&1 / &2 - u = &0)` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&2 * (log(&1 / &3) - log(&1 / &2 - &1 / &3)) -
    &2 * (log(&1 / &8) - log(&1 / &2 - &1 / &8)) = &2 * log(&6)`
  SUBST1_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SIMP_TAC[LOG_DIV; REAL_ARITH `&0 < &1 /\ &0 < &3 /\ &0 < &6 /\
                                  &0 < &8`; LOG_1] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s a e f:real. e <= f ==> abs(s - a) <= e ==> s <= a + f`) THEN
  SUBGOAL_THEN `&50 / (&1 / &8 * log(&N)) * &28 / &3 =
                (&11200 / &3) * inv(log(&N))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < log(&N)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  CONJ_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC);;

let CHEN_Q_TERM = prove
 (`!LN LD z d q.
        &0 < LN /\ &2 <= z /\ z <= &q /\ &0 <= d /\ d <= &1 / &24 /\
        &1 / &8 * LN <= log(&q) /\ log(&q) < &1 / &3 * LN /\
        (&1 / &2 - d) * LN <= LD
        ==> inv(&q - &1) * (&1 / &8 * LN) / (LD - log(&q)) <=
            (&1 / &8 * (&1 + &12 * d) * (&1 + &2 / z)) *
            (inv(&1 / &2 - log(&q) / LN) / &q)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `al = log(&q) / LN` THEN
  SUBGOAL_THEN `log(&q) = al * LN` SUBST_ALL_TAC THENL
   [EXPAND_TAC "al" THEN UNDISCH_TAC `&0 < LN` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &8 <= al /\ al < &1 / &3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `LN:real`;
      MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `LN:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q - &1 /\ &0 < z /\ &0 < &q` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < LN * (&1 / &2 - d - al) /\
                LN * (&1 / &2 - d - al) <= LD - al * LN /\
                &0 < LD - al * LN`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < LN * (&1 / &2 - d - al)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 / &8 * (&1 + &12 * d) * (&1 + &2 / z)) *
    (inv(&1 / &2 - al) / &q) =
    ((&1 + &2 / z) / &q) * ((&1 / &8 * (&1 + &12 * d)) / (&1 / &2 - al))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `inv(&q - &1) = &1 / (&q - &1)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_LID]; ALL_TAC] THEN
    ASM_SIMP_TAC[RAT_LEMMA4] THEN
    SUBGOAL_THEN `&1 <= (&2 * (&q - &1)) / z` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 + &2 / z) * (&q - &1) = (&q - &1) + (&2 * (&q - &1)) / z`
    SUBST1_TAC THENL
     [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&1 / &8 * LN) / (LN * (&1 / &2 - d - al))` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[RAT_LEMMA4] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 / &8 * LN) / (LN * (&1 / &2 - d - al)) =
                  (&1 / &8) / (&1 / &2 - d - al)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(REAL_FIELD
       `!a b c:real. ~(b = &0) /\ ~(c = &0)
                     ==> (a * b) / (b * c) = a / c`) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= d * (&12 * (&1 / &2 - al) - &1 - &12 * d)`
    MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &1 / &2 - d - al /\ &0 < &1 / &2 - al`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[RAT_LEMMA4] THEN REAL_ARITH_TAC]);;

let CHEN_Q_SUM_LEVEL = prove
 (`!N d LD.
        EVEN N /\ 256 < N /\ &0 <= d /\ d <= &1 / &24 /\
        (&1 / &2 - d) * log(&N) <= LD
        ==> sum {q | prime q /\ exp(&1 / &8 * log(&N)) <= &q /\
                     &q < exp(&1 / &3 * log(&N))}
                (\q. inv(&q - &1) * (&1 / &8 * log(&N)) / (LD - log(&q)))
            <= (&1 / &8 * (&1 + &12 * d) *
                (&1 + &2 / exp(&1 / &8 * log(&N)))) *
               (&2 * log(&6) + &4000 / log(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&N) /\ &2 <= exp(&1 / &8 * log(&N))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&8 * log(&2) <= log(&N)` ASSUME_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {q | prime q /\ exp(&1 / &8 * log(&N)) <= &q /\
             &q < exp(&1 / &3 * log(&N))}
        (\q. (&1 / &8 * (&1 + &12 * d) *
              (&1 + &2 / exp(&1 / &8 * log(&N)))) *
             (inv(&1 / &2 - log(&q) / log(&N)) / &q))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{q | prime q /\ &q < exp(&1 / &3 * log(&N))}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC CHEN_Q_TERM THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `!x:real. &0 <= x ==> &0 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC CHEN_Q_SUM THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic for the main term and the remainder.                           *)
(* ------------------------------------------------------------------------- *)

let CHEN_AQ_MAIN_ARITH = prove
 (`!A L6 e h e1 d z LN X NL V S.
        &3 <= A /\ &1 <= L6 /\ &0 <= h /\ h <= &1 /\
        &0 <= e1 /\ e1 <= h /\ &0 <= d /\ &12 * d <= h /\
        &0 < z /\ &2 / z <= h /\ &0 < LN /\ &4000 / LN <= &2 * L6 * h /\
        &31 * h * (A * L6 / &4) <= e /\
        &0 <= X /\ X <= (&1 + h) * NL /\ &0 <= V /\ &0 <= S /\
        S <= (&1 / &8 * (&1 + &12 * d) * (&1 + &2 / z)) *
             (&2 * L6 + &4000 / LN)
        ==> X * V * ((A + &3 * e1) * S) <= (A * L6 / &4 + e) * NL * V`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= NL` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `X / (&1 + h)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 <= h ==> &0 < &1 + h`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A + &3 * e1) * S <= (A * L6 / &4) * (&1 + h) pow 4`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(A * (&1 + h)) *
                ((&1 / &8 * (&1 + h) * (&1 + h)) * (&2 * L6 * (&1 + h)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        SUBGOAL_THEN `&3 * h <= A * h` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `(&1 / &8 * (&1 + &12 * d) * (&1 + &2 / z)) *
                    (&2 * L6 + &4000 / LN)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC(REAL_ARITH `!x:real. &0 <= x ==> &0 <= &1 + x`) THEN
            MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_LMUL THEN
          CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
          TRY(MATCH_MP_TAC(REAL_ARITH `!x:real. &0 <= x ==> &0 <= &1 + x`) THEN
              MATCH_MP_TAC REAL_LE_DIV) THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH
           `!a x:real. &0 <= a /\ &0 <= x ==> &0 <= &2 * a + x`) THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + h) * (&1 + h) pow 4 <= &1 + &31 * h` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    CONV_TAC NUM_REDUCE_CONV THEN MATCH_MP_TAC REAL_POW5_LINEAR THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A * L6 / &4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((&1 + h) * NL) * V * ((A * L6 / &4) * (&1 + h) pow 4)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&1 + h) * NL) * V * ((A * L6 / &4) * (&1 + h) pow 4) =
    ((A * L6 / &4) * ((&1 + h) * (&1 + h) pow 4)) * NL * V`
  SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(A * L6 / &4) * (&1 + &31 * h)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]);;

let CHEN_R_ARITH_LOG = prove
 (`!R Cb W Y Nr LN lx e1 c V.
        &16 <= Nr /\ LN = log Nr /\ LN / &2 <= lx /\ &1 <= lx /\
        &0 < c /\ &0 < e1 /\ c / LN <= V /\ W <= LN / log(&2) /\ &0 <= W /\
        Y <= sqrt Nr /\ &0 <= Y /\
        (&16 * abs Cb + &400000) / (e1 * c) + &1 <= LN /\
        R <= LN * (Cb * (Nr - &1) / lx pow 4 + &2 * W * Y)
        ==> R <= e1 * (Nr / LN) * V`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `LN pow 5 <= &100000 * sqrt Nr /\ sqrt Nr pow 2 = Nr /\
                &0 <= sqrt Nr /\ &1 <= LN`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(SPECL [`5`; `Nr:real`] LOG_POW_LE_SQRT) THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SQRT_POS_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
      CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MP_TAC E_BOUNDS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `LN = log Nr` THEN DISCH_THEN(K ALL_TAC) THEN
  ABBREV_TAC `Kc = &16 * abs Cb + &400000` THEN
  SUBGOAL_THEN `&0 < e1 * c /\ &0 < LN /\ &0 < lx /\ &1 <= Nr`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < LN pow 3 /\ &0 < lx pow 4 /\ &0 < LN pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `LN pow 4 <= &16 * lx pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&16 * ((LN:real) / &2) pow 4` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_DIV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `LN * (Cb * (Nr - &1) / lx pow 4) <= (&16 * abs Cb * Nr) / LN pow 3`
  ASSUME_TAC THENL
   [REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN ASM_SIMP_TAC[RAT_LEMMA4] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(abs Cb * Nr) * (LN:real) pow 4` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH
       `(LN * c * n) * (LN:real) pow 3 = (c * n) * LN pow 4`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC REAL_POW_LE THEN
                                ASM_REAL_ARITH_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!c x y:real. abs(c * x) <= y ==> c * x <= y`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ARITH
       `(&16 * c * n) * l:real = (c * n) * (&16 * l)`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `W <= &2 * LN` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `LN / log(&2)` THEN
    ASM_REWRITE_TAC[] THEN MP_TAC LOG_2_BOUNDS THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 / &2 <= x ==> &0 < x`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= LN * (&2 * l - &1) ==> LN <= (&2 * LN) * l:real`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `LN * (&2 * W * Y) <= (&400000 * Nr) / LN pow 3`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * sqrt Nr * LN pow 5` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_ARITH
       `&4 * s * (LN:real) pow 5 =
        (LN * (&2 * (&2 * LN) * s)) * LN pow 3`] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&4 * sqrt Nr * (&100000 * sqrt Nr)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `sqrt Nr pow 2 = Nr` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Kc <= LN * (e1 * c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(Kc * Nr) / LN pow 3 <= ((e1 * c) * Nr) / LN pow 2`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RAT_LEMMA4] THEN
    REWRITE_TAC[REAL_ARITH
     `((e * c) * n) * (l:real) pow 3 = (l * (e * c)) * (n * l pow 2)`;
     REAL_ARITH `(k * n) * (l:real) pow 2 = k * (n * l pow 2)`] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((e1 * c) * Nr) / LN pow 2 <= e1 * (Nr / LN) * V`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `e1 * ((Nr:real) / LN) * (c / LN)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < LN` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`R <= LN * (Cb * (Nr - &1) / lx pow 4 + &2 * W * Y)`;
    `LN * (Cb * (Nr - &1) / lx pow 4) <= (&16 * abs Cb * Nr) / LN pow 3`;
    `LN * (&2 * W * Y) <= (&400000 * Nr) / LN pow 3`;
    `(Kc * Nr) / LN pow 3 <= ((e1 * c) * Nr) / LN pow 2`;
    `((e1 * c) * Nr) / LN pow 2 <= e1 * (Nr / LN) * V`] THEN
  EXPAND_TAC "Kc" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The upper bound ([N] Theorem 10.5).                                       *)
(* ------------------------------------------------------------------------- *)

let CHEN_SUM_AQ_UPPER_GEN = prove
 (`!h. chen_sieve_ok h
       ==> !e. &0 < e
       ==> ?N0. !N. EVEN N /\ N0 <= N
                ==> sum {q | prime q /\ exp(&1 / &8 * log(&N)) <= &q /\
                             &q < exp(&1 / &3 * log(&N))}
                        (\q. sifted (gchen_A (h N) N)
                                    (\n. if q divides n then &1 else &0)
                                    {p | prime p /\
                                         &p < exp(&1 / &8 * log(&N))})
                    <= (sieve_A * log(&6) / &4 + e) * &N / log(&N) *
                       product {p | prime p /\ &p < exp(&1 / &8 * log(&N))}
                               (\p. &1 - chen_g (h N) p)`,
  GEN_TAC THEN REWRITE_TAC[chen_sieve_ok; chen_remainder_ok] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "h")
    (CONJUNCTS_THEN2 (LABEL_TAC "rem") (LABEL_TAC "card"))) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  USE_THEN "rem" (MP_TAC o SPEC `4`) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_THEN `Cb:real`
    (LABEL_TAC "remB"))) THEN
  X_CHOOSE_THEN `L:real` STRIP_ASSUME_TAC CHEN_G_DIMENSION THEN
  MP_TAC SIEVE_A_GE_3 THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= log(&6)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC E_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `hh = e / (&2 * e + &16 * (sieve_A * log(&6) + &1))` THEN
  SUBGOAL_THEN `&0 < hh /\ hh <= &1 / &2 /\
                &31 * hh * (sieve_A * log(&6) / &4) <= e / &2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &2 * e + &16 * (sieve_A * log(&6) + &1)`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= sieve_A * log(&6)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `hh * (&2 * e + &16 * (sieve_A * log(&6) + &1)) = e`
    ASSUME_TAC THENL
     [EXPAND_TAC "hh" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < hh` ASSUME_TAC THENL
     [EXPAND_TAC "hh" THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "hh" THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      SUBGOAL_THEN `&0 <= sieve_A * log(&6)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `&0 <= hh * e /\ &0 <= hh * sieve_A * log(&6)` MP_TAC
      THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC
         `hh * (&2 * e + &16 * (sieve_A * log(&6) + &1)) = e` THEN
        UNDISCH_TAC `&0 < hh` THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`L:real`; `hh:real`] JURKAT_RICHERT) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` STRIP_ASSUME_TAC) THEN
  X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC CHEN_V_LOWER THEN
  ABBREV_TAC `Pw = &(nproduct {p | prime p /\ &p < w} (\p. p))` THEN
  SUBGOAL_THEN `&1 <= Pw` ASSUME_TAC THENL
   [EXPAND_TAC "Pw" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  USE_THEN "card" (MP_TAC o SPEC `hh:real`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  MP_TAC(SPEC `(&16 * abs(&2 * abs Cb) + &400000) / (e / &2 * c) + &1`
              EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MP_TAC(SPEC `(&16 * (&1 / &2 + log Pw)) / (hh / &12) +
               ((&32 * &B) / (hh / &12)) pow 2 + &1` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  MP_TAC(SPEC `&8 * log w + &1` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N4:num`) THEN
  MP_TAC(SPEC `&2016 / hh + &1` EVENTUALLY_LOG_GE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N5:num`) THEN
  EXISTS_TAC `N1 + N2 + N3 + N4 + N5 + 257` THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  USE_THEN "h" (MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&16 <= &N` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= log(&N)` ASSUME_TAC THENL
   [MP_TAC E_BOUNDS THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(exp(&1) * exp(&1))` THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD; LOG_EXP] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      SIMP_TAC[REAL_LT_MUL; REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * &3` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN
   `w <= exp(&1 / &8 * LN) /\ &2 <= exp(&1 / &8 * LN) /\
    exp(&1 / &8 * LN) <= exp(&1 / &3 * LN) /\
    log(exp(&1 / &8 * LN)) = &1 / &8 * LN /\
    &2 / exp(&1 / &8 * LN) <= hh /\ &4000 / LN <= &2 * log(&6) * hh`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < LN /\ &2016 / hh <= LN` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `w <= exp(&1 / &8 * LN)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log w)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC EXP_LOG THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[LOG_EXP; REAL_EXP_MONO_LE] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&16 / LN` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[RAT_LEMMA4; REAL_EXP_POS_LT] THEN
        MP_TAC(SPEC `&1 / &8 * LN` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        UNDISCH_TAC `&2016 / hh <= LN` THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
      UNDISCH_TAC `&2016 / hh <= LN` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&2 * hh * LN <= &2 * log(&6) * hh * LN` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ABBREV_TAC `z = exp(&1 / &8 * LN)` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  ABBREV_TAC
   `V = product {p | prime p /\ &p < z} (\p. &1 - chen_g ((h:num->num) N) p)`
  THEN
  SUBGOAL_THEN `c / LN <= V /\ &0 < V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c / log z` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `&0 < LN` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[RAT_LEMMA4; REAL_ARITH `&0 < x ==> &0 < &1 / &8 * x`] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        EXPAND_TAC "V" THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `c:real`)) (concl th) &&
          is_forall(concl th))) THEN
        ASM_REWRITE_TAC[]];
      EXPAND_TAC "V" THEN ASM_SIMP_TAC[CHEN_V_POS]];
    ALL_TAC] THEN
  ABBREV_TAC `X = &(CARD(gchen_A ((h:num->num) N) N))` THEN
  SUBGOAL_THEN `&0 < sqrt(&N) / LN pow B /\
                sqrt(&N) / LN pow B <= sqrt(&N) /\
                log(sqrt(&N) / LN pow B) = LN / &2 - &B * log LN`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= LN pow B /\ &0 < sqrt(&N)` STRIP_ASSUME_TAC
    THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LT THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < LN pow B /\ &0 < LN /\ &0 < &N`
    STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; LOG_DIV; LOG_POW; LOG_SQRT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ABBREV_TAC `Y = sqrt(&N) / LN pow B` THEN
  SUBGOAL_THEN `&0 < Pw /\ &0 <= Y /\ log(Y / Pw) = log Y - log Pw`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `D = (Y:real) / Pw` THEN
  SUBGOAL_THEN `&0 < D /\ D * Pw = Y` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&1 <= Pw` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `log D = LN / &2 - &B * log LN - log Pw`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `log D = log Y - log Pw` THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC `log Y = LN / &2 - &B * log LN` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `log D <= LN / &2 /\ (&1 / &2 - hh / &12) * LN <= log D`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1`; `LN:real`; `LN:real`; `B:num`; `Pw:real`;
                  `hh / &12`] CHEN_S_BOUND) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      lhs(concl th) = `log D`)) THEN
    REWRITE_TAC[REAL_MUL_LID] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `&0 < LN` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `a - b <= c <=> a - c <= b:real`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `log D = LN / &2 - &B * log LN - log Pw` THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `&0 < LN /\ hh * LN <= LN / &2 /\ log z = &1 / &8 * LN /\
                log y = &1 / &3 * LN`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &2 * LN` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REWRITE_TAC[];
      EXPAND_TAC "y" THEN REWRITE_TAC[LOG_EXP]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. prime q /\ z <= &q /\ &q < y
        ==> sifted (gchen_A ((h:num->num) N) N)
                   (\n. if q divides n then &1 else &0)
                   {p | prime p /\ &p < z} <=
            X * V * (sieve_A + &3 * hh) *
            (inv(&q - &1) * (&1 / &8 * LN) / (log D - log(&q))) +
            sum {t | t SUBSET {p | prime p /\ &p < z} /\
                     &(nproduct t (\p. p)) < D / &q * Pw}
                (\t. abs(sieve_count (gchen_A (h N) N) (\n. &1) (q INSERT t) -
                         X * product (q INSERT t) (chen_g (h N))))`
  (LABEL_TAC "perq") THENL
   [X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &q /\ &1 / &8 * LN <= log(&q) /\
                  log(&q) < &1 / &3 * LN`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `log z = &1 / &8 * LN`)) THEN
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `log y = &1 / &3 * LN`)) THEN
        MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < log D - log(&q) /\ log(D / &q) = log D - log(&q)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&1 <= log(D / &q) / (&1 / &8 * LN) /\
      log(D / &q) / (&1 / &8 * LN) <= &3 /\
      inv(log(D / &q) / (&1 / &8 * LN)) =
      (&1 / &8 * LN) / (log D - log(&q))`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_INV_DIV] THEN
      SUBGOAL_THEN `&0 < &1 / &8 * LN` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `sq = log(D / &q) / (&1 / &8 * LN)` THEN
    FIRST_ASSUM(MP_TAC o SPEC `chen_g ((h:num->num) N)` o check (fun th ->
      can (find_term ((=) `sieve_F`)) (concl th))) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[CHEN_G_BOUNDS];
        REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `L:real`)) (concl th) &&
          is_forall(concl th))) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`gchen_A ((h:num->num) N) N`; `\n. if q divides n then &1 else &0`;
      `X * chen_g ((h:num->num) N) q`; `D / &q`; `z:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[FINITE_GCHEN_A] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_POS];
          ASM_MESON_TAC[CHEN_G_BOUNDS]];
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[ASSUME `log z = &1 / &8 * LN`;
                ASSUME `log(D / &q) / (&1 / &8 * LN) = sq`;
                ASSUME `&1 <= sq`;
                ASSUME `product {p | prime p /\ &p < z}
                                (\p. &1 - chen_g ((h:num->num) N) p) = V`;
                SIEVE_COUNT_DIVIDES] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a b c d e:real. b <= d /\ c = e ==> a <= b + c ==> a <= d + e`) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `sieve_F sq + hh <= (sieve_A + &3 * hh) * inv sq`
      ASSUME_TAC THENL
       [SIMP_TAC[SIEVE_UPPER_13; ASSUME `&1 <= sq`; ASSUME `sq <= &3`] THEN
        REWRITE_TAC[real_div] THEN
        SUBGOAL_THEN `&1 / &3 <= inv sq` ASSUME_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&3)` THEN
          CONJ_TAC THENL
           [CONV_TAC REAL_RAT_REDUCE_CONV;
            MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        SUBGOAL_THEN `(&3 * hh) * (&1 / &3) <= (&3 * hh) * inv sq` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBST1_TAC(SYM(ASSUME
        `inv sq = (&1 / &8 * LN) / (log D - log(&q))`)) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(X * inv(&q - &1)) * V * ((sieve_A + &3 * hh) * inv sq)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_POS];
            ASM_MESON_TAC[CHEN_G_BOUNDS]];
          MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
           [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
          REWRITE_TAC[chen_g] THEN COND_CASES_TAC THEN
          REWRITE_TAC[REAL_LE_REFL] THEN MATCH_MP_TAC REAL_LE_INV THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SIMP_TAC[SIEVE_UPPER_13; ASSUME `&1 <= sq`; ASSUME `sq <= &3`] THEN
          MATCH_MP_TAC(REAL_ARITH
           `!a b:real. &0 <= a /\ &0 <= b ==> &0 <= a + b`) THEN
          CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
          MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC];
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:num->bool` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `FINITE (t:num->bool) /\ ~(q IN t)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{p | prime p /\ &p < z}` THEN
          ASM_REWRITE_TAC[FINITE_PRIMES_LT];
          DISCH_TAC THEN
          UNDISCH_TAC `t SUBSET {p | prime p /\ &p < z}` THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN REWRITE_TAC[REAL_MUL_ASSOC]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  SUBGOAL_THEN `FINITE (Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{q | prime q /\ &q < y}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum Q (\q. X * V * (sieve_A + &3 * hh) *
               (inv(&q - &1) * (&1 / &8 * LN) / (log D - log(&q)))) +
    sum Q (\q. sum {t | t SUBSET {p | prime p /\ &p < z} /\
                        &(nproduct t (\p. p)) < D / &q * Pw}
                   (\t. abs(sieve_count (gchen_A ((h:num->num) N) N) (\n. &1)
                     (q INSERT t) -
                            X * product (q INSERT t) (chen_g (h N)))))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `q:num` THEN DISCH_TAC THEN BETA_TAC THEN
    USE_THEN "perq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b u w:real. a <= (u + e / &2) * w /\ b <= e / &2 * w
                   ==> a + b <= (u + e) * w`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUM_LMUL] THEN
    SUBGOAL_THEN
     `&0 <= sum Q (\q. inv(&q - &1) * (&1 / &8 * LN) / (log D - log(&q)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN EXPAND_TAC "Q" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `&1 / &8 * LN <= log(&q) /\ log(&q) < &1 / &3 * LN`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `log z = &1 / &8 * LN`)) THEN
          MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `log y = &1 / &3 * LN`)) THEN
          MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(SPECL [`N:num`; `hh / &12`; `log D`] CHEN_Q_SUM_LEVEL) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC CHEN_AQ_MAIN_ARITH THEN
    MAP_EVERY EXISTS_TAC [`hh:real`; `hh / &12`; `z:real`; `LN:real`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `S = {s | s SUBSET {p | prime p /\ &p < y} /\
                       &(nproduct s (\p. p)) < Y}` THEN
  SUBGOAL_THEN `FINITE (S:(num->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s | s SUBSET {p | prime p /\ &p < y}}` THEN
    SIMP_TAC[FINITE_POWERSET; FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN S ==> FINITE s /\ (!p. p IN s ==> prime p) /\
                   &(nproduct s (\p. p)) < Y`
  (LABEL_TAC "Sfacts") THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:num->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < y}` THEN
      ASM_REWRITE_TAC[FINITE_PRIMES_LT];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `LN * sum S (\s. abs(sieve_count (gchen_A ((h:num->num) N) N)
              (\n. &1) s -
                                  X * product s (chen_g (h N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum S (\s. &(CARD s) *
                           abs(sieve_count (gchen_A ((h:num->num) N) N)
                                           (\n. &1) s -
                               X * product s (chen_g (h N))))` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`Q:num->bool`;
        `\q. {t | t SUBSET {p | prime p /\ &p < z} /\
                  &(nproduct t (\p. p)) < D / &q * Pw}`;
        `S:(num->bool)->bool`;
        `\s. abs(sieve_count (gchen_A ((h:num->num) N) N) (\n. &1) s -
                 X * product s (chen_g (h N)))`] SUM_PAIRS_INSERT_LE) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_ABS_POS] THEN CONJ_TAC THENL
       [X_GEN_TAC `q:num` THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{t | t SUBSET {p | prime p /\ &p < z}}` THEN
        SIMP_TAC[FINITE_POWERSET; FINITE_PRIMES_LT] THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`q:num`; `t:num->bool`] THEN
      EXPAND_TAC "Q" THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `FINITE (t:num->bool) /\ ~(q IN t)` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN
          EXISTS_TAC `{p | prime p /\ &p < z}` THEN
          ASM_REWRITE_TAC[FINITE_PRIMES_LT];
          DISCH_TAC THEN
          UNDISCH_TAC `t SUBSET {p | prime p /\ &p < z}` THEN
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `t SUBSET {p | prime p /\ &p < z}` THEN
        REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
        DISCH_THEN(LABEL_TAC "tsub") THEN X_GEN_TAC `p:num` THEN
        DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
         [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
          USE_THEN "tsub" (MP_TAC o SPEC `p:num`) THEN
          (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
          ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[NPRODUCT_CLAUSES; GSYM REAL_OF_NUM_MUL] THEN
        SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LTE_TRANS THEN
        EXISTS_TAC `&q * (D / &q * Pw)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          UNDISCH_TAC `D * Pw = Y:real` THEN UNDISCH_TAC `&0 < &q` THEN
          CONV_TAC REAL_FIELD]];
      REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:num->bool` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      USE_THEN "Sfacts" (MP_TAC o SPEC `s:num->bool`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      MP_TAC(SPEC `s:num->bool` CARD_LOG_NPRODUCT) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `log(&(nproduct s (\p. p))) <= LN / &2` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log Y` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
           [REWRITE_TAC[REAL_OF_NUM_LT] THEN
            MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
            ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
            ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(sqrt(&N))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
            ASM_SIMP_TAC[LOG_SQRT; REAL_ARITH `&16 <= x ==> &0 < x`] THEN
            ASM_REAL_ARITH_TAC]];
        ALL_TAC] THEN
      MP_TAC LOG_2_BOUNDS THEN
      SUBGOAL_THEN `&0 <= &(CARD(s:num->bool))` MP_TAC THENL
       [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      SPEC_TAC(`&(CARD(s:num->bool))`, `k:real`) THEN
      X_GEN_TAC `k:real` THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `k * &1 / &2 <= k * log(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= Y` THENL
   [ALL_TAC;
    SUBGOAL_THEN `S:(num->bool)->bool = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
      X_GEN_TAC `s:num->bool` THEN DISCH_TAC THEN
      USE_THEN "Sfacts" (MP_TAC o SPEC `s:num->bool`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      SUBGOAL_THEN `1 <= nproduct s (\p:num. p)` MP_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
        MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
        REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[SUM_CLAUSES; REAL_MUL_RZERO] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]] THEN
  USE_THEN "remB" (MP_TAC o SPECL [`N:num`; `y:real`; `Y:real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `(h:num->num) N` OMEGA_LE_LOG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `log(&((h:num->num) N)) <= LN` ASSUME_TAC THENL
   [EXPAND_TAC "LN" THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Y <= sqrt(&N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CHEN_R_ARITH_LOG THEN
  MAP_EVERY EXISTS_TAC
   [`&2 * abs Cb`; `&(CARD {p | prime p /\ p divides (h:num->num) N})`;
    `Y:real`; `LN:real`; `c:real`] THEN
  ASM_REWRITE_TAC[REAL_POS] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log(&((h:num->num) N)) / log(&2)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
    MP_TAC LOG_2_BOUNDS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!r a b d:real. r <= a + d /\ a <= b ==> r <= b + d`) THEN
  EXISTS_TAC `Cb * &N / LN pow 4` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < LN pow 4` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SIEVE_MUL_DIV_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs Cb * &N` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH
     `(&2 * c) * (n - &1) = c * (&2 * n - &2)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC]);;
