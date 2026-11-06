(* ========================================================================= *)
(* Chen's theorem for every even shift: for each even h > 0 there are        *)
(* >> x / log^2 x primes p <= x such that p + h is a product of at most two  *)
(* primes (CHEN_SHIFT), hence infinitely many (CHEN_SHIFT_INFINITE); the     *)
(* lower bound sieve alone gives p + h = P4 (SHIFT_P4).  The case h = 2 is   *)
(* TWIN_P4 here and CHEN_TWIN in chen.ml.                                    *)
(*                                                                           *)
(* Method.  CHEN_GENERAL (chen_sb.ml) and CHEN_P4_GEN (chen_lower.ml) apply  *)
(* to every family of shifts h(N) satisfying chen_sieve_ok.  Here h(N) = h   *)
(* for N >= 2h + 16 and h(N) = N for smaller N, so that h(N) <= N always     *)
(* and GOLDBACH_REMAINDER_OK covers the small N.  For n > h the sifted set   *)
(* gchen_A h N is {p + h | p prime, p not dividing h} (SHIFT_A_LARGE); its   *)
(* at most h elements n <= h (SHIFT_A_SMALL) cost at most 2h per sieve term  *)
(* (SHIFT_REMAINDER_TERM).  With the residue -h mod d (DIVIDES_ADDH_CONG),   *)
(* Bombieri-Vinogradov absorbs this with a larger constant, since the level  *)
(* is Y <= sqrt N (SHIFT_REMAINDER_SUM, SHIFT_REMAINDER_OK).  The size of    *)
(* gchen_A h N comes from the prime number theorem (SHIFT_A_CARD_UPPER,      *)
(* SHIFT_A_CARD_LOWER), and SHIFT_COUNT_TRANSFER turns a lower bound for     *)
(* the sifted elements with a property P into one for the primes p <= x      *)
(* with P(p + h).                                                            *)
(* ========================================================================= *)

needs "Sieve/chen_sb.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The sifted set for a fixed shift h.                                       *)
(* ------------------------------------------------------------------------- *)

let FINITE_SHIFT_PRIMES = prove
 (`!h N P. FINITE {p | prime p /\ p + h < N /\ P p}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p:num | p < N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC);;

let SHIFT_A_LARGE = prove
 (`!h N. {n | n IN gchen_A h N /\ h < n} =
         IMAGE (\p. p + h) {p | prime p /\ p + h < N /\ ~(p divides h)}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[gchen_A; EXTENSION; IN_ELIM_THM; IN_IMAGE; chen_dist] THEN
  X_GEN_TAC `n:num` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?m. n = m + h:num` (X_CHOOSE_THEN `m:num` SUBST_ALL_TAC)
    THENL
     [EXISTS_TAC `n - h:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `m:num` THEN
    SUBGOAL_THEN `~(m + h <= h:num)`
     (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; ADD_SUB]))
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_MESON_TAC[PRIME_1; NUMBER_RULE
     `!m h:num. m divides h /\ coprime(m + h,h) ==> m = 1`];
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    SUBGOAL_THEN `~(p + h <= h:num)` (fun th -> REWRITE_TAC[th; ADD_SUB])
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `coprime(p,h)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[PRIME_COPRIME_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
    UNDISCH_TAC `coprime(p,h)` THEN CONV_TAC NUMBER_RULE]);;

let SHIFT_A_SMALL = prove
 (`!h N. FINITE {n | n IN gchen_A h N /\ n <= h} /\
         CARD {n | n IN gchen_A h N /\ n <= h} <= h`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{n | n IN gchen_A h N /\ n <= h} SUBSET 1..h` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; gchen_A] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..h` THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD(1..h)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC CARD_SUBSET THEN
                    ASM_REWRITE_TAC[FINITE_NUMSEG];
                    REWRITE_TAC[CARD_NUMSEG_1; LE_REFL]]]);;

let SUM_SHIFT_A = prove
 (`!h N Q. sum {n | n IN gchen_A h N /\ Q n} (\n. &1) =
           &(CARD {p | prime p /\ p + h < N /\ ~(p divides h) /\ Q(p + h)}) +
           &(CARD {n | n IN gchen_A h N /\ n <= h /\ Q n})`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{n | n IN gchen_A h N /\ Q n} =
    IMAGE (\p. p + h) {p | prime p /\ p + h < N /\ ~(p divides h) /\
                           Q(p + h)} UNION
    {n | n IN gchen_A h N /\ n <= h /\ Q n}`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`h:num`; `N:num`] SHIFT_A_LARGE) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_UNION] THEN
    DISCH_TAC THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
    ASM_CASES_TAC `h < n:num` THEN ASM_REWRITE_TAC[] THENL
     [DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      ASM_SIMP_TAC[ARITH_RULE `h < n ==> ~(n <= h:num)`] THEN MESON_TAC[];
      DISCH_TAC THEN ASM_SIMP_TAC[ARITH_RULE `~(h < n) ==> n <= h:num`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {n | n IN gchen_A h N /\ n <= h /\ Q n}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n | n IN gchen_A h N /\ n <= h}` THEN
    REWRITE_TAC[SHIFT_A_SMALL] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FINITE_SHIFT_PRIMES] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN
    X_GEN_TAC `n:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `n <= h:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ARITH_RULE `~(p = 0) ==> ~(p + h <= h)`) THEN
    ASM_MESON_TAC[PRIME_0];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_IMAGE; FINITE_SHIFT_PRIMES; REAL_MUL_RID] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_SHIFT_PRIMES] THEN
  ARITH_TAC);;

let CARD_SHIFT_A = prove
 (`!h N. &(CARD(gchen_A h N)) =
         &(CARD {p | prime p /\ p + h < N /\ ~(p divides h)}) +
         &(CARD {n | n IN gchen_A h N /\ n <= h})`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`h:num`; `N:num`; `\n:num. T`] SUM_SHIFT_A) THEN
  REWRITE_TAC[SET_RULE `{x:num | x IN s} = s`] THEN
  SIMP_TAC[SUM_CONST; FINITE_GCHEN_A; REAL_MUL_RID]);;

let SHIFT_SIEVE_COUNT = prove
 (`!h N t. sieve_count (gchen_A h N) (\n. &1) t =
           &(CARD {p | prime p /\ p + h < N /\ ~(p divides h) /\
                       !q. q IN t ==> q divides p + h}) +
           &(CARD {n | n IN gchen_A h N /\ n <= h /\
                       !q. q IN t ==> q divides n})`,
  REWRITE_TAC[sieve_count; SUM_SHIFT_A]);;

(* ------------------------------------------------------------------------- *)
(* Remainders.                                                               *)
(* ------------------------------------------------------------------------- *)

let SHIFT_REMAINDER_TERM = prove
 (`!h N t. ~(h = 0) /\ FINITE t /\ (!q. q IN t ==> prime q)
           ==> abs(sieve_count (gchen_A h N) (\n. &1) t -
                   &(CARD(gchen_A h N)) * product t (chen_g h)) <=
               (if !q. q IN t ==> ~(q divides h)
                then abs(&(pi_ap (N - h - 1) (nproduct t (\p. p))
                              (nproduct t (\p. p) -
                               h MOD nproduct t (\p. p))) -
                         &(pi_upto (N - h - 1)) /
                         &(phi(nproduct t (\p. p)))) +
                     &2 * &(CARD {p | prime p /\ p divides h}) + &2 * &h
                else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SHIFT_SIEVE_COUNT; CARD_SHIFT_A] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    SUBGOAL_THEN `product t (chen_g h) = &0` SUBST1_TAC THENL
     [ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `r:num` THEN
      ASM_REWRITE_TAC[chen_g];
      ALL_TAC] THEN
    SUBGOAL_THEN `prime r` ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `a = &0 /\ b = &0 ==> abs(a + b) <= &0`) THEN
    REWRITE_TAC[REAL_OF_NUM_EQ] THEN CONJ_TAC THENL
     [SIMP_TAC[CARD_EQ_0; FINITE_SHIFT_PRIMES] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `r divides p` ASSUME_TAC THENL
       [SUBGOAL_THEN `r divides p + h` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `r divides h` THEN CONV_TAC NUMBER_RULE;
        ALL_TAC] THEN
      SUBGOAL_THEN `r:num = p` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[DIVIDES_PRIME_PRIME]; ASM_MESON_TAC[]];
      MATCH_MP_TAC(MESON[CARD_CLAUSES] `s:num->bool = {} ==> CARD s = 0`) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; gchen_A] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      SUBGOAL_THEN `r divides 1` MP_TAC THENL
       [SUBGOAL_THEN `r divides n` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC [`r divides h`; `coprime(n,h)`] THEN
        CONV_TAC NUMBER_RULE;
        ASM_MESON_TAC[DIVIDES_ONE; PRIME_1]]]] THEN
  ABBREV_TAC `d = nproduct t (\p:num. p)` THEN
  SUBGOAL_THEN `1 <= d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `product t (chen_g h) = inv(&(phi d))` SUBST1_TAC THENL
   [EXPAND_TAC "d" THEN ASM_SIMP_TAC[GSYM REAL_PRODUCT_INV_PRED] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[chen_g];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p + h < N /\ ~(p divides h) /\
         (!q. q IN t ==> q divides p + h)} =
    {p | prime p /\ p <= N - h - 1 /\ (p == d - h MOD d) (mod d)} DIFF
    {p | prime p /\ p divides h}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(p:num) divides h` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRIMES_DIVIDE_IFF_NPRODUCT] THEN
    ASM_SIMP_TAC[DIVIDES_ADDH_CONG; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | prime p /\ p + h < N /\ ~(p divides h)} =
    {p | prime p /\ p <= N - h - 1} DIFF {p | prime p /\ p divides h}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {p | prime p /\ p <= N - h - 1 /\ (p == d - h MOD d) (mod d)} /\
    FINITE {p | prime p /\ p <= N - h - 1} /\
    FINITE {p | prime p /\ p divides h}`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_PRIMES_LE_RESTRICT; FINITE_ATMOST;
                 FINITE_PRIME_DIVISORS];
    ALL_TAC] THEN
  ABBREV_TAC
   `S1 = {p | prime p /\ p <= N - h - 1 /\ (p == d - h MOD d) (mod d)}` THEN
  ABBREV_TAC `S3 = {p | prime p /\ p <= N - h - 1}` THEN
  ABBREV_TAC `S2 = {p | prime p /\ p divides h}` THEN
  ABBREV_TAC `W = CARD(S2:num->bool)` THEN
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
  SUBGOAL_THEN `&(CARD(S1:num->bool)) =
                &(pi_ap (N - h - 1) d (d - h MOD d)) /\
                &(CARD(S3:num->bool)) = &(pi_upto (N - h - 1))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["S1"; "S3"] THEN REWRITE_TAC[pi_ap; pi_upto];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 <= &(phi d)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC PHI_LOWERBOUND_1_STRONG THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(CARD {n | n IN gchen_A h N /\ n <= h /\
                (!q. q IN t ==> q divides n)}) <=
    &(CARD {n | n IN gchen_A h N /\ n <= h}) /\
    &(CARD {n | n IN gchen_A h N /\ n <= h}) <= &h`
  MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; SHIFT_A_SMALL] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[SHIFT_A_SMALL] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `CARD {n | n IN gchen_A h N /\ n <= h /\
                         (!q. q IN t ==> q divides n)}` REAL_POS) THEN
  MP_TAC(SPEC `CARD((S1:num->bool) INTER S2)` REAL_POS) THEN
  MP_TAC(SPEC `CARD((S3:num->bool) INTER S2)` REAL_POS) THEN
  SUBGOAL_THEN `&(CARD((S1:num->bool) INTER S2)) <= &W /\
                &(CARD((S3:num->bool) INTER S2)) <= &W`
  MP_TAC THENL [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  UNDISCH_TAC `&1 <= &(phi d)` THEN
  SPEC_TAC(`&(CARD {n | n IN gchen_A h N /\ n <= h /\
                        (!q. q IN t ==> q divides n)})`,`st:real`) THEN
  SPEC_TAC(`&(CARD {n | n IN gchen_A h N /\ n <= h})`,`s0:real`) THEN
  SPEC_TAC(`&(CARD((S1:num->bool) INTER S2))`,`c2:real`) THEN
  SPEC_TAC(`&(CARD((S3:num->bool) INTER S2))`,`c3:real`) THEN
  SPEC_TAC(`&(phi d)`,`f:real`) THEN
  SPEC_TAC(`&(pi_ap (N - h - 1) d (d - h MOD d))`,`a:real`) THEN
  SPEC_TAC(`&(pi_upto (N - h - 1))`,`b:real`) THEN
  SPEC_TAC(`&W`,`w:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c3 * inv f <= c3 /\ s0 * inv f <= s0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_INV_LE_1] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c3 * inv f /\ &0 <= s0 * inv f` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN ASM_REAL_ARITH_TAC);;

let SHIFT_REMAINDER_SUM = prove
 (`!h N z Y. ~(h = 0) /\ &1 <= Y
           ==> sum {t | t SUBSET {p | prime p /\ &p < z} /\
                        &(nproduct t (\p. p)) < Y}
                   (\t. abs(sieve_count (gchen_A h N) (\n. &1) t -
                            &(CARD(gchen_A h N)) * product t (chen_g h)))
               <= sum {d | 1 <= d /\ &d <= Y}
                      (\d. abs(&(pi_ap (N - h - 1) d
                                   (if coprime(d,h) then d - h MOD d else 1)) -
                               &(pi_upto (N - h - 1)) / &(phi d))) +
                  (&2 * &(CARD {p | prime p /\ p divides h}) + &2 * &h) * Y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = \d. abs(&(pi_ap (N - h - 1) d
                                (if coprime(d,h) then d - h MOD d else 1)) -
                          &(pi_upto (N - h - 1)) / &(phi d))` THEN
  ABBREV_TAC `W = &(CARD {p | prime p /\ p divides h})` THEN
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
  EXISTS_TAC `sum TT (\t. if !q. q IN t ==> ~(q divides h)
                          then (E:num->real)(nproduct t (\p. p)) +
                               (&2 * W + &2 * &h)
                          else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:num->bool` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `TT:(num->bool)->bool`))
                           (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(SPECL [`h:num`; `N:num`; `t:num->bool`] SHIFT_REMAINDER_TERM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!x y z:real. y = z ==> x <= y ==> x <= z`) THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["E"; "W"] THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `coprime(nproduct t (\p. p),h)` ASSUME_TAC THENL
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
  EXISTS_TAC `sum TT (\t. if !q. q IN t ==> ~(q divides h)
                          then (E:num->real)(nproduct t (\p. p)) else &0) +
              sum TT (\t:num->bool. &2 * W + &2 * &h)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SUBGOAL_THEN
     `sum {t | t IN TT /\ (!q. q IN t ==> ~(q divides h))}
          (\t. (E:num->real) (nproduct t (\p. p))) =
      sum (IMAGE (\t. nproduct t (\p. p))
                 {t | t IN TT /\ (!q. q IN t ==> ~(q divides h))}) E`
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
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MP_TAC(SPEC `h:num` REAL_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
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

let COPRIME_SUB_MOD = prove
 (`!d h. ~(d = 0) /\ coprime(d,h) ==> coprime(d - h MOD d,d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`h:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`h DIV d`,`q:num`) THEN SPEC_TAC(`h MOD d`,`r:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?a. d = a + r:num` (X_CHOOSE_THEN `a:num` SUBST_ALL_TAC)
  THENL
   [EXISTS_TAC `d - r:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_SUB] THEN
  UNDISCH_TAC `coprime(a + r,h)` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUMBER_RULE);;

let SQRT_LOG_POW_MONO = prove
 (`!N B B'. 16 <= N /\ B <= B'
            ==> sqrt(&N) / log(&N) pow B' <= sqrt(&N) / log(&N) pow B`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_GE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[SQRT_POS_LE; REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]]);;

let SHIFT_REMAINDER_OK = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> chen_remainder_ok (\N. if 2 * h + 16 <= N then h else N)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC GOLDBACH_REMAINDER_OK THEN
  REWRITE_TAC[chen_remainder_ok] THEN DISCH_TAC THEN
  X_GEN_TAC `A:num` THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `B2:num` (X_CHOOSE_TAC `C2:real`) o
    SPEC `A:num`) THEN
  MP_TAC(SPEC `A:num` BOMBIERI_VINOGRADOV) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:num` (X_CHOOSE_TAC `C:real`)) THEN
  MAP_EVERY EXISTS_TAC
   [`(B + 1) + B2`;
    `(abs C * &2 pow A + &2 * &h * (&2 * &A) pow A) + abs C2`] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `z:real`; `Y:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &N / log(&N) pow A` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `z:real`; `Y:real`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sqrt(&N) / log(&N) pow ((B + 1) + B2)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SQRT_LOG_POW_MONO THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a + c ==> x <= b + c`) THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      MP_TAC(SPEC `h:num` REAL_POS) THEN
      SUBGOAL_THEN `&0 <= abs C * &2 pow A /\ &0 <= (&2 * &A) pow A`
      MP_TAC THENL
       [CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
        REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &2 * &h * (&2 * &A) pow A` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_INV THEN MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC]] THEN
  MP_TAC(SPECL [`N:num`; `h + 1`; `B:num`; `A:num`] BV_SHIFT_FACTS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `N - (h + 1) = N - h - 1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= log(&N) /\ &1 <= log(&N) pow ((B + 1) + B2)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_GE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Y <= sqrt(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&N) / log(&N) pow ((B + 1) + B2)` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[SQRT_POS_LE; REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &h * Y <= &2 * &h * (&2 * &A) pow A * &N / log(&N) pow A`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MP_TAC(SPEC `h:num` REAL_POS) THEN REAL_ARITH_TAC;
                    ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt(&N)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`A:num`; `&N`] LOG_POW_LE_SQRT) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < log(&N) pow A /\ &0 < sqrt(&N) /\
                  sqrt(&N) * sqrt(&N) = &N`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC SQRT_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[GSYM REAL_POW_2] THEN SIMP_TAC[SQRT_POW_2; REAL_POS]];
      ALL_TAC] THEN
    DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `a * b / c = (a * b) / c:real`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sqrt(&N) * ((&2 * &A) pow A * sqrt(&N))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `sqrt(&N) * sqrt(&N) = &N` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum {d | 1 <= d /\ &d <= Y}
        (\d. abs(&(pi_ap (N - h - 1) d
                     (if coprime(d,h) then d - h MOD d else 1)) -
                 &(pi_upto (N - h - 1)) / &(phi d))) +
    (&2 * &(CARD {p | prime p /\ p divides h}) + &2 * &h) * Y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SHIFT_REMAINDER_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {d | 1 <= d /\ &d <= Y}
        (\d. abs(&(pi_ap (N - h - 1) d
                     (if coprime(d,h) then d - h MOD d else 1)) -
                 &(pi_upto (N - h - 1)) / &(phi d))) <=
    abs C * &2 pow A * &N / log(&N) pow A`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {d | 1 <= d /\ &d <= sqrt(&(N - h - 1)) /
                                 log(&(N - h - 1)) pow B}
          (\d. abs(&(pi_ap (N - h - 1) d
                       (if coprime(d,h) then d - h MOD d else 1)) -
                   &(pi_upto (N - h - 1)) / &(phi d)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUM_RANGE_LE; REAL_ABS_POS] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`N:num`; `B + 1`; `(B + 1) + B2`] SQRT_LOG_POW_MONO) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`N - h - 1`; `\d. if coprime(d,h) then d - h MOD d else 1`] o
     check (fun th -> is_forall(concl th) &&
                      can (find_term ((=) `C:real`)) (concl th))) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:num` THEN COND_CASES_TAC THEN
      REWRITE_TAC[COPRIME_1] THEN MATCH_MP_TAC COPRIME_SUB_MOD THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `coprime(0,h)` THEN REWRITE_TAC[COPRIME_0] THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `EVEN 1` THEN
      CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs C * &(N - h - 1) / log(&(N - h - 1)) pow A` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC LOG_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= abs C2 * &N / log(&N) pow A` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&2 * &h * Y <= &2 * &h * (&2 * &A) pow A * &N / log(&N) pow A`] THEN
  ABBREV_TAC
   `SS = sum {d | 1 <= d /\ &d <= Y}
             (\d. abs(&(pi_ap (N - h - 1) d
                          (if coprime(d,h) then d - h MOD d else 1)) -
                      &(pi_upto (N - h - 1)) / &(phi d)))` THEN
  ABBREV_TAC `W = &(CARD {p | prime p /\ p divides h})` THEN
  REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The sieve hypotheses and Chen's theorem for the shift h.                  *)
(* ------------------------------------------------------------------------- *)

let SHIFT_A_CARD_UPPER = prove
 (`!h e. &0 < e
         ==> ?N1. !N. N1 <= N
                      ==> &(CARD(gchen_A h N)) <= (&1 + e) * &N / log(&N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e / &2` PI_UPTO_ASYMPTOTIC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MP_TAC(SPECL [`&h`; `e / &2`] LOG_SMALL_EVENTUALLY) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  EXISTS_TAC `N2 + N3 + 3` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC E_BOUNDS THEN
    SUBGOAL_THEN `&3 <= &N` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&h <= e / &2 * &N / log(&N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `e / &2 * n / l = (e / &2 * n) / l`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= l ==> &0 < l`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&h * log(&N) pow 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CARD_SHIFT_A] THEN
  SUBGOAL_THEN
   `&(CARD {p | prime p /\ p + h < N /\ ~(p divides h)}) <= &(pi_upto N) /\
    &(CARD {n | n IN gchen_A h N /\ n <= h}) <= &h`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; SHIFT_A_SMALL; pi_upto] THEN
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_ATMOST] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[ARITH_RULE `x + h < N ==> x <= N:num`];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`&(pi_upto N) <= (&1 + e / &2) * &N / log(&N)`;
    `&h <= e / &2 * &N / log(&N)`;
    `&(CARD {p | prime p /\ p + h < N /\ ~(p divides h)}) <=
     &(pi_upto N)`;
    `&(CARD {n | n IN gchen_A h N /\ n <= h}) <= &h`] THEN
  ABBREV_TAC `c1 = &(CARD {p | prime p /\ p + h < N /\ ~(p divides h)})` THEN
  ABBREV_TAC `c2 = &(CARD {n | n IN gchen_A h N /\ n <= h})` THEN
  ABBREV_TAC `u = &N / log(&N)` THEN REAL_ARITH_TAC);;

let SHIFT_A_CARD_LOWER = prove
 (`!h e. ~(h = 0) /\ &0 < e
         ==> ?N1. !N. N1 <= N
                      ==> (&1 - e) * &N / log(&N) <= &(CARD(gchen_A h N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e / &2` PI_UPTO_ASYMPTOTIC) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  MP_TAC(SPECL [`&2 * &h + &1`; `e / &2`] LOG_SMALL_EVENTUALLY) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  EXISTS_TAC `N2 + N3 + h + 3` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(exp(&1))` THEN
    CONJ_TAC THENL [REWRITE_TAC[LOG_EXP; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC E_BOUNDS THEN
    SUBGOAL_THEN `&3 <= &N` MP_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &h + &1 <= e / &2 * &N / log(&N)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `e / &2 * n / l = (e / &2 * n) / l`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&1 <= l ==> &0 < l`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * &h + &1) * log(&N) pow 2` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(pi_upto N) <=
    &(CARD {p | prime p /\ p + h < N /\ ~(p divides h)}) + &2 * &h + &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[pi_upto; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD({p | prime p /\ p + h < N /\ ~(p divides h)} UNION
                     (1..h) UNION (N - h..N))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_NUMSEG] THEN
        X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_CASES_TAC `(p:num) divides h` THEN ASM_REWRITE_TAC[] THENL
         [MP_TAC(SPECL [`p:num`; `h:num`] DIVIDES_LE) THEN
          ASM_REWRITE_TAC[] THEN
          FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
          ASM_ARITH_TAC];
        REWRITE_TAC[FINITE_UNION; FINITE_NUMSEG; FINITE_SHIFT_PRIMES]];
      ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {p | prime p /\ p + h < N /\ ~(p divides h)} +
                CARD(1..h) + CARD(N - h..N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {p | prime p /\ p + h < N /\ ~(p divides h)} +
                  CARD((1..h) UNION (N - h..N))` THEN
      SIMP_TAC[CARD_UNION_LE; FINITE_UNION; FINITE_NUMSEG;
               FINITE_SHIFT_PRIMES; LE_ADD_LCANCEL];
      REWRITE_TAC[CARD_NUMSEG; CARD_NUMSEG_1] THEN ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(&1 - e / &2) * &N / log(&N) <= &(pi_upto N)`;
    `&2 * &h + &1 <= e / &2 * &N / log(&N)`;
    `&(pi_upto N) <=
     &(CARD {p | prime p /\ p + h < N /\ ~(p divides h)}) + &2 * &h + &1`]
  THEN REWRITE_TAC[CARD_SHIFT_A] THEN
  MP_TAC(SPEC `CARD {n | n IN gchen_A h N /\ n <= h}` REAL_POS) THEN
  ABBREV_TAC `c1 = &(CARD {p | prime p /\ p + h < N /\ ~(p divides h)})` THEN
  ABBREV_TAC `c2 = &(CARD {n | n IN gchen_A h N /\ n <= h})` THEN
  ABBREV_TAC `u = &N / log(&N)` THEN REAL_ARITH_TAC);;

let SHIFT_SIEVE_OK = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> chen_sieve_ok (\N. if 2 * h + 16 <= N then h else N)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[chen_sieve_ok] THEN
  ASM_SIMP_TAC[SHIFT_REMAINDER_OK] THEN CONJ_TAC THENL
   [X_GEN_TAC `N:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[ARITH] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`h:num`; `e:real`] SHIFT_A_CARD_LOWER) THEN
  MP_TAC(SPECL [`h:num`; `e:real`] SHIFT_A_CARD_UPPER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN
  EXISTS_TAC `N1 + N2 + 2 * h + 16` THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `2 * h + 16 <= N:num` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let SHIFT_COUNT_TRANSFER = prove
 (`!h P c N0.
     EVEN h /\ ~(h = 0) /\ &0 < c /\
     (!N. EVEN N /\ N0 <= N
          ==> c * &N / log(&N) pow 2 <=
              &(CARD {n | n IN gchen_A (if 2 * h + 16 <= N then h else N) N /\
                          P n}))
     ==> ?c x0. &0 < c /\
                !x. x0 <= x
                    ==> c * &x / log(&x) pow 2 <=
                        &(CARD {p | prime p /\ p <= x /\ P(p + h)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&2 * &h / c`; `&1`] LOG_SMALL_EVENTUALLY) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_LID] THEN
  DISCH_THEN(X_CHOOSE_TAC `N3:num`) THEN
  MATCH_MP_TAC EVEN_TO_ALL_LOWER THEN
  MAP_EVERY EXISTS_TAC [`c / &2`; `N0 + N3 + 2 * h + 16`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[LE_TRANS];
      REWRITE_TAC[FINITE_PRIMES_LE_RESTRICT]];
    ALL_TAC] THEN
  X_GEN_TAC `N:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (is_forall o concl) o
    check (fun th -> can (find_term ((=) `gchen_A`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 * h + 16 <= N:num` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:num`; `N:num`; `P:num->bool`] SUM_SHIFT_A) THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_GCHEN_A; REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `&(CARD {p | prime p /\ p + h < N /\ ~(p divides h) /\
                (P:num->bool) (p + h)}) <=
    &(CARD {p | prime p /\ p <= N /\ (P:num->bool) (p + h)}) /\
    &(CARD {n | n IN gchen_A h N /\ n <= h /\ (P:num->bool) n}) <= &h`
  MP_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[REAL_OF_NUM_LE] THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_PRIMES_LE_RESTRICT; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[ARITH_RULE `x + h < N ==> x <= N:num`];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {n | n IN gchen_A h N /\ n <= h}` THEN
      REWRITE_TAC[SHIFT_A_SMALL] THEN MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[SHIFT_A_SMALL] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&h <= c / &2 * &N / log(&N) pow 2` MP_TAC THENL
   [SUBGOAL_THEN `&0 < log(&N) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC LOG_POS_LT THEN
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `c / &2 * n / l = (c / &2 * n) / l`] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `N:num` o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `N3:num`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `c / &2 * ((&2 * &h / c) * log(&N) pow 2)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&0 < c` THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `L2 = log(&N) pow 2` THEN
  ABBREV_TAC
   `a1 = &(CARD {p | prime p /\ p + h < N /\ ~(p divides h) /\
                     (P:num->bool) (p + h)})` THEN
  ABBREV_TAC
   `a2 = &(CARD {n | n IN gchen_A h N /\ n <= h /\ (P:num->bool) n})` THEN
  ABBREV_TAC `f = &(CARD {p | prime p /\ p <= N /\ (P:num->bool) (p + h)})`
  THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

let CHEN_SHIFT = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> ?c x0. &0 < c /\
                  !x. x0 <= x
                      ==> c * &x / log(&x) pow 2 <=
                          &(CARD {p | prime p /\ p <= x /\
                                      almost_prime 2 (p + h)})`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\N. if 2 * h + 16 <= N then h else N` CHEN_GENERAL) THEN
  ASM_SIMP_TAC[SHIFT_SIEVE_OK] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SHIFT_COUNT_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `N0:num`] THEN ASM_REWRITE_TAC[]);;

let CHEN_SHIFT_INFINITE = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> INFINITE {p | prime p /\ almost_prime 2 (p + h)}`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x0:num`
    STRIP_ASSUME_TAC) o MATCH_MP CHEN_SHIFT) THEN
  MATCH_MP_TAC COUNT_LOWER_INFINITE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `x0:num`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONV_TAC TAUT);;

let SHIFT_P4 = prove
 (`!h. EVEN h /\ ~(h = 0)
       ==> ?c x0. &0 < c /\
                  !x. x0 <= x
                      ==> c * &x / log(&x) pow 2 <=
                          &(CARD {p | prime p /\ p <= x /\
                                      almost_prime 4 (p + h)})`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\N. if 2 * h + 16 <= N then h else N` CHEN_P4_GEN) THEN
  ASM_SIMP_TAC[SHIFT_SIEVE_OK] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `N0:num`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC SHIFT_COUNT_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `N0:num`] THEN ASM_REWRITE_TAC[]);;

let TWIN_P4 = prove
 (`?c x0. &0 < c /\
          !x. x0 <= x
              ==> c * &x / log(&x) pow 2 <=
                  &(CARD {p | prime p /\ p <= x /\ almost_prime 4 (p + 2)})`,
  MP_TAC(SPEC `2` SHIFT_P4) THEN REWRITE_TAC[ARITH]);;
