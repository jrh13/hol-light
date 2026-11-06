(* ========================================================================= *)
(* Selberg's sieve for problems of dimension two (prime pairs).              *)
(*                                                                           *)
(* SIEVE_TWO_RESIDUES: let N be even and suppose that for each prime p not   *)
(* dividing N, p divides f(n) (n IN 1..M) exactly when n lies in one of two  *)
(* residue classes 0, c(p) mod p.  Then for z > 1                            *)
(*                                                                           *)
(*   #{n IN 1..M | no prime p < z, p not dividing N, divides f(n)}           *)
(*       <= 4 M / (prod_{p | N} (1 - 1/p) log z)^2 + z^6.                    *)
(*                                                                           *)
(* The sieve problem is the image of f with multiplicities, so that          *)
(* SELBERG_SIEVE (selberg.ml) applies with g(p) = 2/p:                       *)
(* * remainders: CRT_COUNT counts n IN 1..M in prescribed residue classes    *)
(*   modulo the primes of t (Chinese remainder theorem), |r_t| <= 2^|t|,     *)
(*   and the sum of 4^|t| 2^|t| over squarefree d = prod t < z^2 is <= z^6;  *)
(* * main term: with h(p) = g(p) / (1 - g(p)), Selberg's G satisfies         *)
(*   G_s(y) = G_{s-p}(y) + h(p) G_{s-p}(y/p) (SELBERG_G_INSERT), and         *)
(*   SELBERG_G_COMPARISON turns any function with the matching recursive     *)
(*   upper bound into a lower bound for G; for the sum of 1/(ab) over pairs  *)
(*   with ab < y (recip_pairs) this gives                                    *)
(*   G >= (sum_{b < sqrt z, (b,N) = 1} 1/b)^2 >= (prod (1 - 1/p) log z/2)^2, *)
(*   without infinite series or unique factorisation.                        *)
(* ========================================================================= *)

needs "Sieve/selberg.ml";;
needs "Sieve/nt.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Counting in residue classes; the Chinese remainder theorem.               *)
(* ------------------------------------------------------------------------- *)

let REAL_DIV_BOUNDS = prove
 (`!M d. ~(d = 0) ==> &(M DIV d) <= &M / &d /\ &M / &d < &(M DIV d) + &1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &d` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ] THEN
  MP_TAC(SPECL [`M:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`M DIV d`,`q:num`) THEN SPEC_TAC(`M MOD d`,`r:num`) THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC MP_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              GSYM REAL_OF_NUM_LT] THEN
  MP_TAC(SPEC `r:num` REAL_POS) THEN REAL_ARITH_TAC);;

let CARD_RESIDUE_CLASS = prove
 (`!d r M. r < d
           ==> M DIV d <= CARD {n | n IN 1..M /\ n MOD d = r} /\
               CARD {n | n IN 1..M /\ n MOD d = r} <= M DIV d + 1`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {n | n IN 1..M /\ n MOD d = r}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (IMAGE (\k. k * d + (if r = 0 then d else r))
                            {k | k < M DIV d})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
      DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_RCANCEL] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(k + 1) * d <= M` ASSUME_TAC THENL
       [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(M DIV d) * d` THEN
        ASM_SIMP_TAC[LE_MULT_RCANCEL; DIV_MUL_LE] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      COND_CASES_TAC THENL
       [ASM_REWRITE_TAC[ARITH_RULE `k * d + d = (k + 1) * d`; MOD_MULT;
                        MOD_MULT_LMOD] THEN
        REWRITE_TAC[MOD_MULT2] THEN
        ASM_SIMP_TAC[MOD_EQ_0] THEN
        CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
        REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC;
        ASM_SIMP_TAC[MOD_MULT_ADD; MOD_LT] THEN
        REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN ASM_ARITH_TAC]];
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (IMAGE (\n. n DIV d) {n | n IN 1..M /\ n MOD d = r})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN STRIP_TAC THEN
      MP_TAC(SPECL [`x:num`; `d:num`] DIVISION) THEN
      MP_TAC(SPECL [`y:num`; `d:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      GEN_REWRITE_TAC RAND_CONV [ARITH_RULE `n + 1 = (n + 1) - 0`] THEN
      REWRITE_TAC[GSYM CARD_NUMSEG] THEN MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM;
                  IN_NUMSEG; LE_0] THEN
      SIMP_TAC[DIV_MONO]]]);;

let CARD_RESIDUE_SET = prove
 (`!d P M. ~(d = 0)
           ==> abs(&(CARD {n | n IN 1..M /\ P(n MOD d)}) -
                   &M * &(CARD {r | r < d /\ P r}) / &d)
               <= &(CARD {r | r < d /\ P r})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {r:num | r < d /\ P r}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < d}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {n | n IN 1..M /\ P(n MOD d)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `&M * &(CARD {r:num | r < d /\ P r}) / &d =
                sum {r | r < d /\ P r} (\r. &M / &d)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SUM_CONST] THEN REWRITE_TAC[real_div; REAL_MUL_AC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{n | n IN 1..M /\ P(n MOD d)}` CARD_EQ_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\n. n MOD d`; `\n:num. &1`;
                 `{n | n IN 1..M /\ P(n MOD d)}`; `{r:num | r < d /\ P r}`]
                SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[DIVISION];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  MP_TAC(ISPEC `{r:num | r < d /\ P r}` CARD_EQ_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `sum {n | n IN {n | n IN 1..M /\ P(n MOD d)} /\ n MOD d = r}
                    (\n. &1) =
                &(CARD {n | n IN 1..M /\ n MOD d = r})` SUBST1_TAC THENL
   [SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; FINITE_NUMSEG] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `r IN {r:num | r < d /\ P r}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `r < d:num` ASSUME_TAC THENL
   [UNDISCH_TAC `r IN {r:num | r < d /\ P r}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `r:num`; `M:num`] CARD_RESIDUE_CLASS) THEN
  MP_TAC(SPECL [`M:num`; `d:num`] REAL_DIV_BOUNDS) THEN
  ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
  SPEC_TAC(`CARD {n | n IN 1..M /\ n MOD d = r}`, `c:num`) THEN
  REAL_ARITH_TAC);;

let CONG_DIVIDES_MOD_PRODUCT = prove
 (`!n a q d. ((n == a) (mod q) /\ d divides n) <=>
             ((n MOD (q * d) == a) (mod q) /\ d divides n MOD (q * d))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONG; DIVIDES_MOD; MOD_MOD] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o LAND_CONV o RAND_CONV)
    [MULT_SYM] THEN
  REWRITE_TAC[MOD_MOD]);;

let AP_MULTIPLES_COUNT = prove
 (`!x q a d. 1 <= q /\ 1 <= d /\ coprime(d,q)
             ==> abs(&(CARD {n | n IN 1..x /\ (n == a) (mod q) /\
                                 d divides n}) -
                     &x / (&q * &d)) <= &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q * d = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[MULT_EQ_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{n | n IN 1..x /\ (n == a) (mod q) /\ d divides n} =
                {n | n IN 1..x /\
                     (\r. (r == a) (mod q) /\ d divides r) (n MOD (q * d))}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
    BETA_TAC THEN AP_TERM_TAC THEN MATCH_ACCEPT_TAC CONG_DIVIDES_MOD_PRODUCT;
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `a:num`; `q:num`] CONG_SOLVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `y:num`) THEN
  SUBGOAL_THEN `((d * y) MOD (q * d) == a) (mod q) /\
                d divides (d * y) MOD (q * d)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CONG_DIVIDES_MOD_PRODUCT] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `{r | r < q * d /\ (r == a) (mod q) /\ d divides r} =
                {(d * y) MOD (q * d)}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `r:num` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
      EXISTS_TAC `(q:num) * d` THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
      MATCH_MP_TAC CONG_CHINESE THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `((r:num) == a) (mod q)` THEN
        UNDISCH_TAC `((d * y) MOD (q * d) == a) (mod q)` THEN
        CONV_TAC NUMBER_RULE;
        UNDISCH_TAC `(d:num) divides r` THEN
        UNDISCH_TAC `d divides (d * y) MOD (q * d)` THEN
        CONV_TAC NUMBER_RULE];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[MOD_LT_EQ]];
    ALL_TAC] THEN
  MP_TAC(BETA_RULE(ISPECL [`(q:num) * d`;
                 `\r:num. (r == a) (mod q) /\ d divides r`; `x:num`]
                CARD_RESIDUE_SET)) THEN
  ASM_REWRITE_TAC[CARD_SING; GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[real_div; REAL_MUL_RID; REAL_MUL_LID]);;

let NPRODUCT_PRIMES_MOD = prove
 (`!t q n. FINITE t /\ q IN t
           ==> (n MOD nproduct t (\p. p)) MOD q = n MOD q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\p:num. p`; `t:num->bool`; `q:num`] NPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[MOD_MOD]);;

let CRT_CARD = prove
 (`!P t. FINITE t /\ (!p. p IN t ==> prime p)
         ==> CARD {r | r < nproduct t (\p. p) /\
                       !p. p IN t ==> P p (r MOD p)} =
             nproduct t (\p. CARD {r | r < p /\ P p r})`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NPRODUCT_CLAUSES; NOT_IN_EMPTY; ARITH_RULE `r < 1 <=> r = 0`;
                SING_GSPEC; CARD_SING];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `t:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `prime p /\ !q. q IN t ==> prime q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES] THEN
  MATCH_MP_TAC(MESON[HAS_SIZE]
   `(s:num->bool) HAS_SIZE n ==> CARD s = n`) THEN
  MATCH_MP_TAC CHINESE_REMAINDER_COUNT THEN
  MAP_EVERY EXISTS_TAC
   [`(P:num->num->bool) p`;
    `\r. !q. q IN t ==> (P:num->num->bool) q (r MOD q)`] THEN
  ASM_SIMP_TAC[COPRIME_PRIME_NPRODUCT] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[NPRODUCT_PRIMES_MOD; FORALL_IN_INSERT] THEN
    REWRITE_TAC[ETA_AX];
    REWRITE_TAC[HAS_SIZE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < p}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ASM_REWRITE_TAC[HAS_SIZE] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r:num | r < nproduct t (\q. q)}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]]);;

let CRT_COUNT = prove
 (`!P t M. FINITE t /\ (!p. p IN t ==> prime p)
           ==> abs(&(CARD {n | n IN 1..M /\ !p. p IN t ==> P p (n MOD p)}) -
                   &M * product t (\p. &(CARD {r | r < p /\ P p r}) / &p))
               <= product t (\p. &(CARD {r | r < p /\ P p r}))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `d = nproduct t (\p:num. p)` THEN
  SUBGOAL_THEN `~(d = 0)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[GSYM LT_NZ] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIME_IMP_NZ; LT_NZ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `\r. !p. p IN t ==> (P:num->num->bool) p (r MOD p)`;
                `M:num`] CARD_RESIDUE_SET) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. (!p. p IN t ==> (P:num->num->bool) p ((n MOD d) MOD p)) <=>
                    (!p. p IN t ==> P p (n MOD p))`
   (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "d" THEN ASM_MESON_TAC[NPRODUCT_PRIMES_MOD]; ALL_TAC] THEN
  MP_TAC(SPECL [`P:num->num->bool`; `t:num->bool`] CRT_CARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; PRODUCT_DIV] THEN
  EXPAND_TAC "d" THEN ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT] THEN
  REWRITE_TAC[real_div; REAL_MUL_ASSOC]);;

let CARD_TWO_RESIDUES = prove
 (`!p c. ~(c = 0) /\ c < p ==> CARD {r | r < p /\ (r = 0 \/ r = c)} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{r | r < p /\ (r = 0 \/ r = c)} = {0,c}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* ------------------------------------------------------------------------- *)
(* Sieving the values of a function (an image with multiplicities).          *)
(* ------------------------------------------------------------------------- *)

let SUM_IMAGE_MULTIPLICITY = prove
 (`!f:A->num u Q.
        FINITE u
        ==> sum {m | m IN IMAGE f u /\ Q m}
                (\m. &(CARD {n | n IN u /\ f n = m})) =
            &(CARD {n | n IN u /\ Q(f n)})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {n | n IN u /\ Q((f:A->num) n)}` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_SUM] THEN
  MP_TAC(ISPECL [`f:A->num`; `\n:A. &1`;
   `{n | n IN u /\ Q((f:A->num) n)}`;
                 `{m | m IN IMAGE (f:A->num) u /\ Q m}`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  SUBGOAL_THEN `{n | n IN {n | n IN u /\ Q((f:A->num) n)} /\ f n = m} =
                {n | n IN u /\ f n = m}` SUBST1_TAC THENL
   [UNDISCH_TAC `m IN {m | m IN IMAGE (f:A->num) u /\ Q m}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT]]);;

let SIFTED_IMAGE = prove
 (`!f:A->num u s.
        FINITE u
        ==> sifted (IMAGE f u) (\m. &(CARD {n | n IN u /\ f n = m})) s =
            &(CARD {n | n IN u /\ !p. p IN s ==> ~(p divides f n)})`,
  SIMP_TAC[sifted; SUM_IMAGE_MULTIPLICITY]);;

let SIEVE_COUNT_IMAGE = prove
 (`!f:A->num u t.
        FINITE u
        ==> sieve_count (IMAGE f u) (\m. &(CARD {n | n IN u /\ f n = m})) t =
            &(CARD {n | n IN u /\ !p. p IN t ==> p divides f n})`,
  SIMP_TAC[sieve_count; SUM_IMAGE_MULTIPLICITY]);;

(* ------------------------------------------------------------------------- *)
(* Selberg's G as a function of the sifting set and the level.               *)
(* ------------------------------------------------------------------------- *)

let selberg_G = new_definition
 `selberg_G (g:num->real) s y =
        sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < y} (selberg_H g)`;;

let SELBERG_G_ALT = prove
 (`!g s y. selberg_G g s y =
           sum {t | t SUBSET s}
               (\t. if &(nproduct t (\p. p)) < y then selberg_H g t else &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[selberg_G; GSYM SUM_RESTRICT_SET] THEN
  REWRITE_TAC[IN_ELIM_THM; ETA_AX]);;

let SELBERG_G_INSERT = prove
 (`!g p s y.
        FINITE s /\ ~(p IN s) /\ 1 <= p
        ==> selberg_G g (p INSERT s) y =
            selberg_G g s y + g p / (&1 - g p) * selberg_G g s (y / &p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SELBERG_G_ALT] THEN
  ASM_SIMP_TAC[SUM_POWERSET_INSERT] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(t:num->bool) /\ ~((p:num) IN t)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES; selberg_H; PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; GSYM REAL_OF_NUM_MUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o LAND_CONV o LAND_CONV)
   [REAL_MUL_SYM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO]);;

let SELBERG_G_POS = prove
 (`!g s y. FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1)
           ==> &0 <= selberg_G g s y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_G] THEN
  MATCH_MP_TAC SUM_POS_LE THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SELBERG_H_POS THEN
  EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[]);;

let SELBERG_G_MONO = prove
 (`!g s y y'. FINITE s /\ (!p. p IN s ==> &0 < g p /\ g p < &1) /\ y <= y'
              ==> selberg_G g s y <= selberg_G g s y'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_G] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[REAL_LTE_TRANS];
    X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    MATCH_MP_TAC SELBERG_H_POS THEN
    EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[]]);;

let SELBERG_G_EMPTY = prove
 (`!g y. selberg_G g {} y = if &1 < y then &1 else &0`,
  REWRITE_TAC[SELBERG_G_ALT; SUBSET_EMPTY; SING_GSPEC; SUM_SING] THEN
  REWRITE_TAC[NPRODUCT_CLAUSES; selberg_H; PRODUCT_CLAUSES]);;

let SELBERG_G_COMPARISON = prove
 (`!(Phi:(num->bool)->real->real) g U.
        (!p. p IN U ==> prime p /\ &0 < g p /\ g p < &1) /\
        (!s y. FINITE s /\ s SUBSET U /\ y <= &1 ==> Phi s y <= &0) /\
        (!y. Phi {} y <= &1) /\
        (!s p y. FINITE s /\ s SUBSET U /\ p IN s
                 ==> Phi s y <= Phi (s DELETE p) y + g p * Phi s (y / &p))
        ==> !s y. FINITE s /\ s SUBSET U ==> Phi s y <= selberg_G g s y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SELBERG_G_EMPTY] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `s:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(s:num->bool) SUBSET U /\ p IN U` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `prime p /\ &0 < (g:num->real) p /\ g p < &1`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!q. q IN (p:num) INSERT s ==> &0 < (g:num->real) q /\ g q < &1`
  ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!q:num. q IN s ==> &0 < (g:num->real) q /\ g q < &1`
  ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  SUBGOAL_THEN `!n y. y <= &2 pow n
                      ==> Phi (p INSERT s) y <= selberg_G g (p INSERT s) y`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `y:real` THEN
    MP_TAC(SPECL [`&2`; `y:real`] REAL_ARCH_POW) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE]] THEN
  SUBGOAL_THEN `!y. y <= &1
                    ==> Phi (p INSERT s) y <= selberg_G g (p INSERT s) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN
    ASM_SIMP_TAC[SELBERG_G_POS; FINITE_INSERT] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT];
    ALL_TAC] THEN
  INDUCT_TAC THENL [ASM_REWRITE_TAC[real_pow]; ALL_TAC] THEN
  X_GEN_TAC `y:real` THEN DISCH_TAC THEN
  ASM_CASES_TAC `y <= &1` THEN ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`(p:num) INSERT s`; `p:num`; `y:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_INSERT; IN_INSERT]; ALL_TAC] THEN
  ASM_SIMP_TAC[SET_RULE `~((p:num) IN s) ==> (p INSERT s) DELETE p = s`] THEN
  SUBGOAL_THEN `y / &p <= &2 pow n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&2 <= p ==> &0 < p`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow n * &2` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `y <= &2 pow SUC n` THEN REWRITE_TAC[real_pow] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y / &p`) THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SELBERG_G_INSERT; PRIME_GE_2;
               ARITH_RULE `2 <= p ==> 1 <= p`] THEN
  MP_TAC(SPEC `y:real` (ASSUME
   `!y. (Phi:(num->bool)->real->real) s y <= selberg_G g s y`)) THEN
  MP_TAC(SPECL [`g:num->real`; `s:num->bool`; `y / &p / &p`; `y / &p`]
               SELBERG_G_MONO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < y / &p` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `y / &p / &p = (y / &p) * inv(&p)` SUBST1_TAC THENL
     [REWRITE_TAC[real_div]; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_INV_LE_1; REAL_ARITH
     `&2 <= p ==> &1 <= p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (g:num->real) p / (&1 - g p) /\
                g p * (&1 + g p / (&1 - g p)) = g p / (&1 - g p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(g:num->real) p < &1` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  ABBREV_TAC `H = (g:num->real) p / (&1 - g p)` THEN
  ABBREV_TAC `G0 = selberg_G g (s:num->bool) y` THEN
  ABBREV_TAC `G1 = selberg_G g (s:num->bool) (y / &p)` THEN
  ABBREV_TAC `G2 = selberg_G g (s:num->bool) (y / &p / &p)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(g:num->real) p * H * G2 <= g p * H * G1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:num->real) p * Phi ((p:num) INSERT s) (y / &p) <=
                g p * (G1 + H * G2)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `H * G1 = (g:num->real) p * G1 + g p * H * G1` MP_TAC THENL
   [UNDISCH_TAC `(g:num->real) p * (&1 + H) = H` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [SYM th]) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Sums of 1/(ab) over pairs with ab < y and all prime factors in s.         *)
(* ------------------------------------------------------------------------- *)

let recip_pairs = new_definition
 `recip_pairs s y =
        sum {x:num#num | 1 <= FST x /\ 1 <= SND x /\ &(FST x * SND x) < y /\
                         !q. prime q /\ q divides FST x * SND x ==> q IN s}
            (\x. inv(&(FST x * SND x)))`;;

let FINITE_RECIP_PAIRS = prove
 (`!s y. FINITE {x:num#num | 1 <= FST x /\ 1 <= SND x /\
                             &(FST x * SND x) < y /\
                             !q. prime q /\ q divides FST x * SND x
                                 ==> q IN s}`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `y:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `(0..N) CROSS (0..N)` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; IN_NUMSEG] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `a * b <= (N:num)` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(a:num) <= a * b /\ (b:num) <= a * b` MP_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = a * 1`];
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `b = 1 * b`]] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_RCANCEL];
    ARITH_TAC]);;

let RECIP_PAIRS_SMALL = prove
 (`!s y. y <= &1 ==> recip_pairs s y <= &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[recip_pairs] THEN
  MATCH_MP_TAC(REAL_ARITH `x = &0 ==> x <= &0`) THEN
  MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= a * b` MP_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC]);;

let RECIP_PAIRS_EMPTY = prove
 (`!y. recip_pairs {} y <= &1`,
  GEN_TAC THEN REWRITE_TAC[recip_pairs; NOT_IN_EMPTY] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {(1,1)} (\x. inv(&(FST x * SND x)))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_SING; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_SING; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `a * b = 1` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_FACTOR]; REWRITE_TAC[MULT_EQ_1]];
    REWRITE_TAC[SUM_SING; MULT_CLAUSES] THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let SIEVE_SUM_UNION_LE_POS = prove
 (`!f:A->real s t.
        FINITE s /\ FINITE t /\ (!x. x IN s UNION t ==> &0 <= f x)
        ==> sum (s UNION t) f <= sum s f + sum t f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s UNION t:A->bool = s UNION (t DIFF s)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_DIFF; SET_RULE
   `DISJOINT (s:A->bool) (t DIFF s)`; REAL_LE_LADD] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [SET_TAC[]; ASM SET_TAC[]]);;

let RECIP_PAIRS_IMAGE = prove
 (`!s p y. prime p /\ p IN s
           ==> sum (IMAGE (\x. (p * FST x,SND x))
                     {x:num#num | 1 <= FST x /\ 1 <= SND x /\
                                  &(FST x * SND x) < y / &p /\
                                  !q. prime q /\ q divides FST x * SND x
                                      ==> q IN s})
                   (\x. inv(&(FST x * SND x))) =
               inv(&p) * recip_pairs s (y / &p) /\
               sum (IMAGE (\x. (FST x,p * SND x))
                     {x:num#num | 1 <= FST x /\ 1 <= SND x /\
                                  &(FST x * SND x) < y / &p /\
                                  !q. prime q /\ q divides FST x * SND x
                                      ==> q IN s})
                   (\x. inv(&(FST x * SND x))) =
               inv(&p) * recip_pairs s (y / &p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[recip_pairs; GSYM SUM_LMUL] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  CONJ_TAC THEN
  (W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
   ANTS_TAC THENL
    [REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ] THEN
     ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN MESON_TAC[];
     DISCH_THEN SUBST1_TAC] THEN
   MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; o_THM] THEN
   REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL] THEN REAL_ARITH_TAC));;

let RECIP_PAIRS_STEP = prove
 (`!s p y. prime p /\ p IN s
           ==> recip_pairs s y <=
               recip_pairs (s DELETE p) y + &2 / &p * recip_pairs s (y / &p)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:num->bool`; `p:num`; `y:real`] RECIP_PAIRS_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `PT = {x:num#num | 1 <= FST x /\ 1 <= SND x /\
                                &(FST x * SND x) < y / &p /\
                                !q. prime q /\ q divides FST x * SND x
                                    ==> q IN s}` THEN
  ABBREV_TAC `w = \x:num#num. inv(&(FST x * SND x))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(PT:num#num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "PT" THEN REWRITE_TAC[FINITE_RECIP_PAIRS]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:num#num. &0 <= w x` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `recip_pairs (s DELETE p) y +
              sum (IMAGE (\x. (p * FST x,SND x)) PT UNION
                   IMAGE (\x. (FST x,p * SND x)) PT) w` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (\x. ((p:num) * FST x,SND x)) PT) w +
                sum (IMAGE (\x. (FST x,(p:num) * SND x)) PT) w` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIEVE_SUM_UNION_LE_POS THEN ASM_SIMP_TAC[FINITE_IMAGE];
      ASM_REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]] THEN
  REWRITE_TAC[recip_pairs] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `PS = {x:num#num | 1 <= FST x /\ 1 <= SND x /\
                                &(FST x * SND x) < y /\
                                !q. prime q /\ q divides FST x * SND x
                                    ==> q IN s}` THEN
  ABBREV_TAC `PD = {x:num#num | 1 <= FST x /\ 1 <= SND x /\
                                &(FST x * SND x) < y /\
                                !q. prime q /\ q divides FST x * SND x
                                    ==> q IN s DELETE p}` THEN
  SUBGOAL_THEN `FINITE(PS:num#num->bool) /\ FINITE(PD:num#num->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["PS"; "PD"] THEN REWRITE_TAC[FINITE_RECIP_PAIRS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum PS w = sum {x | x IN PS /\ ~((p:num) divides FST x * SND x)} w +
               sum {x | x IN PS /\ (p:num) divides FST x * SND x} w`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_UNION_EQ THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  MAP_EVERY EXPAND_TAC ["PS"; "PD"; "PT"] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; IN_UNION; IN_IMAGE;
              EXISTS_PAIR_THM; PAIR_EQ; IN_DELETE] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  MP_TAC(SPECL [`p:num`; `a:num`; `b:num`] PRIME_DIVPROD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `c:num` SUBST_ALL_TAC o
    REWRITE_RULE[divides])) THENL
   [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`c:num`; `b:num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 <= p * c` THEN
      REWRITE_TAC[MULT_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      MESON_TAC[];
      UNDISCH_TAC `&((p * c) * b) < y` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(p * c) * b = p * c * b:num`] THEN
      ASM_SIMP_TAC[DIVIDES_LMUL]];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`a:num`; `c:num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `1 <= p * c` THEN
      REWRITE_TAC[MULT_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      MESON_TAC[];
      UNDISCH_TAC `&(a * p * c) < y` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `a * p * c = p * a * c:num` SUBST1_TAC THENL
       [REWRITE_TAC[MULT_AC]; ASM_SIMP_TAC[DIVIDES_LMUL]]]]);;

let SELBERG_G_RECIP_PAIRS = prove
 (`!s y. FINITE s /\ (!p. p IN s ==> prime p /\ 3 <= p)
         ==> recip_pairs s y <= selberg_G (\p. &2 / &p) s y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`recip_pairs`; `\p:num. &2 / &p`;
                 `{p | prime p /\ 3 <= p}`] SELBERG_G_COMPARISON) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; RECIP_PAIRS_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `p:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&3 <= &p` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      DISCH_TAC THEN SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[RECIP_PAIRS_SMALL];
      MAP_EVERY X_GEN_TAC [`t:num->bool`; `p:num`; `z:real`] THEN
      STRIP_TAC THEN MATCH_MP_TAC RECIP_PAIRS_STEP THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let RECIP_PAIRS_SQUARE = prove
 (`!s x. &0 <= x
         ==> sum {b | 1 <= b /\ &b < x /\
                      !q. prime q /\ q divides b ==> q IN s} (\b. inv(&b))
             pow 2 <= recip_pairs s (x pow 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `B = {b | 1 <= b /\ &b < x /\
                       !q. prime q /\ q divides b ==> q IN s}` THEN
  SUBGOAL_THEN `FINITE(B:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n | &n <= x}` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
      DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[REAL_LE_TRANS];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT] THEN
  REWRITE_TAC[recip_pairs] THEN
  SUBGOAL_THEN `(\(i,j). inv(&i) * inv(&j)) =
                (\x:num#num. inv(&(FST x * SND x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_INV_MUL];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  REWRITE_TAC[FINITE_RECIP_PAIRS; REAL_LE_INV_EQ; REAL_POS] THEN
  EXPAND_TAC "B" THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC REAL_LT_MUL2 THEN ASM_REWRITE_TAC[REAL_POS];
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`q:num`; `a:num`; `b:num`] PRIME_DIVPROD) THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Sums of 1/b over integers b < x, and those coprime to N.                  *)
(* ------------------------------------------------------------------------- *)

let FINITE_RECIP_RANGE = prove
 (`!x P. FINITE {b | 1 <= b /\ &b < x /\ P b}`,
  REPEAT GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..N` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_MESON_TAC[REAL_LT_IMP_LE;
                                                      REAL_LE_TRANS]);;

let FINITE_NUM_RANGE = prove
 (`!x. FINITE {b | 1 <= b /\ &b < x}`,
  GEN_TAC THEN MP_TAC(ISPECL [`x:real`; `\b:num. T`] FINITE_RECIP_RANGE) THEN
  REWRITE_TAC[]);;

let NUM_RANGE_EXISTS = prove
 (`!x. &1 <= x
       ==> ?n. &n < x /\ x <= &n + &1 /\ {b | 1 <= b /\ &b < x} = 1..n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\n. x <= &n + &1` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&n < x` ASSUME_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(n = 0) ==> 1 <= n`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN X_GEN_TAC `b:num` THEN
  AP_TERM_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&b < &n + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC]);;

let CARD_NUM_RANGE_LE = prove
 (`!x. &1 <= x ==> &(CARD {b | 1 <= b /\ &b < x}) <= x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o
    MATCH_MP NUM_RANGE_EXISTS) THEN
  ASM_REWRITE_TAC[CARD_NUMSEG_1] THEN ASM_REAL_ARITH_TAC);;

let RECIP_COPRIME_SPLIT = prove
 (`!p P x.
        prime p /\ ~(p IN P) /\ (!q. q IN P ==> prime q)
        ==> {b | 1 <= b /\ &b < x /\ !q. q IN P ==> ~(q divides b)} =
            {b | 1 <= b /\ &b < x /\ ~(p divides b) /\
                 !q. q IN P ==> ~(q divides b)} UNION
            IMAGE (\c. p * c) {b | 1 <= b /\ &b < x / &p /\
                                   !q. q IN P ==> ~(q divides b)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `b:num` THEN ASM_CASES_TAC `(p:num) divides b` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `c:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; GSYM REAL_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[EQ_MULT_LCANCEL; UNWIND_THM1] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `(c <=> c') /\ (b <=> b')
                       ==> (a /\ b /\ c <=> a /\ b' /\ c')`) THEN
    CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_CASES_TAC `(q:num) IN P` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `prime q /\ ~(q = p)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME];
    REWRITE_TAC[TAUT `(a <=> a \/ b) <=> (b ==> a)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((p:num) divides b)` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL]]);;

let SUM_RECIP_COPRIME = prove
 (`!P x. FINITE P /\ (!p. p IN P ==> prime p)
         ==> product P (\p. &1 - inv(&p)) *
             sum {b | 1 <= b /\ &b < x} (\b. inv(&b)) <=
             sum {b | 1 <= b /\ &b < x /\ !p. p IN P ==> ~(p divides b)}
                 (\b. inv(&b))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; NOT_IN_EMPTY; REAL_MUL_LID; REAL_LE_REFL];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `P:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN X_GEN_TAC `x:real` THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real`) THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = sum {b | 1 <= b /\ &b < x} (\b. inv(&b))` THEN
  ABBREV_TAC `T1 = sum {b | 1 <= b /\ &b < x /\
                            !q. q IN P ==> ~(q divides b)} (\b. inv(&b))` THEN
  ABBREV_TAC `T3 = sum {b | 1 <= b /\ &b < x / &p /\
                            !q. q IN P ==> ~(q divides b)} (\b. inv(&b))` THEN
  ABBREV_TAC `T2 = sum {b | 1 <= b /\ &b < x /\ ~(p divides b) /\
                            !q. q IN P ==> ~(q divides b)} (\b. inv(&b))` THEN
  SUBGOAL_THEN `T1 = T2 + inv(&p) * T3` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T2"; "T3"] THEN
    MP_TAC(SPECL [`p:num`; `P:num->bool`; `x:real`] RECIP_COPRIME_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [SIMP_TAC[FINITE_IMAGE; FINITE_RECIP_RANGE] THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE;
                  NOT_IN_EMPTY] THEN
      MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[PRIME_IMP_NZ];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[GSYM SUM_LMUL; o_DEF; GSYM REAL_OF_NUM_MUL; REAL_INV_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `T3 <= T1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["T1"; "T3"] THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_RECIP_RANGE; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `b:num` THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&b * &p` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
    ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - inv(&p) /\ &0 <= inv(&p)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[PRIME_GE_2;
      ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `inv(&p) * T3 <= inv(&p) * T1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - inv(&p)) * product P (\p. &1 - inv(&p)) * T0 <=
                (&1 - inv(&p)) * T1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let LOG_LE_HARMONIC = prove
 (`!n. log(&n + &1) <= sum(1..n) (\b. inv(&b))`,
  INDUCT_TAC THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[REAL_ADD_LID; LOG_1;
   REAL_LE_REFL] THEN
  SUBGOAL_THEN `&(SUC n) + &1 = (&n + &1) * (&1 + inv(&n + &1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &n + &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` REAL_POS) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 + inv(&n + &1)` ASSUME_TAC THENL
   [MP_TAC(SPEC `&n + &1` REAL_LT_INV) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN MATCH_MP_TAC LOG_LE THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE]);;

let LOG_LE_RECIP_SUM = prove
 (`!x. &1 <= x ==> log x <= sum {b | 1 <= b /\ &b < x} (\b. inv(&b))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC o
    MATCH_MP NUM_RANGE_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `log(&n + &1)` THEN
  REWRITE_TAC[LOG_LE_HARMONIC] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The lower bound for G in the two-residue problem.                         *)
(* ------------------------------------------------------------------------- *)

let SELBERG_G_TWO_LOWER = prove
 (`!N z. EVEN N /\ ~(N = 0) /\ &1 <= z
         ==> (product {p | prime p /\ p divides N} (\p. &1 - inv(&p)) *
              log z / &2) pow 2
             <= selberg_G (\p. &2 / &p)
                          {p | prime p /\ &p < z /\ ~(p divides N)} z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {p | prime p /\ &p < z /\ ~(p divides N)}` THEN
  ABBREV_TAC `P = {p | prime p /\ p divides N}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> prime p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:num->bool) /\ (!p. p IN s ==> prime p /\ 3 <= p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < z}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `~(p = 2) ==> 2 <= p ==> 3 <= p`) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(2 divides N)` THEN ASM_REWRITE_TAC[GSYM EVEN_EXISTS;
        divides] THEN
      ASM_MESON_TAC[EVEN_EXISTS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `recip_pairs s z` THEN
  ASM_SIMP_TAC[SELBERG_G_RECIP_PAIRS] THEN
  SUBGOAL_THEN `&1 <= sqrt z /\ sqrt z <= z /\ sqrt z pow 2 = z`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= sqrt z` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `&1 <= z ==> &0 <= z`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sqrt z pow 2` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_2] THEN GEN_REWRITE_TAC LAND_CONV
        [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[SQRT_POW_2; REAL_ARITH `&1 <= z ==> &0 <= z`;
                   REAL_LE_REFL]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {b | 1 <= b /\ &b < sqrt z /\
                       !q. prime q /\ q divides b ==> q IN s}
                  (\b. inv(&b)) pow 2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC RECIP_PAIRS_SQUARE THEN ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {b | 1 <= b /\ &b < sqrt z /\
                       !q. q IN P ==> ~(q divides b)} (\b. inv(&b))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product P (\p. &1 - inv(&p)) *
                sum {b | 1 <= b /\ &b < sqrt z} (\b. inv(&b))` THEN
    ASM_SIMP_TAC[SUM_RECIP_COPRIME] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      ALL_TAC] THEN
    MP_TAC(SPEC `sqrt z` LOG_LE_RECIP_SUM) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LOG_SQRT; REAL_ARITH `&1 <= z ==> &0 < z`];
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_RECIP_RANGE; REAL_LE_INV_EQ; REAL_POS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `b:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `q <= b:num` MP_TAC THENL
       [MP_TAC(SPECL [`q:num`; `b:num`] DIVIDES_LE) THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `1 <= b` THEN ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN
      EXPAND_TAC "P" THEN ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* ------------------------------------------------------------------------- *)
(* The remainder sum.                                                        *)
(* ------------------------------------------------------------------------- *)

let PRIME_DIVIDES_NPRODUCT_PRIMES = prove
 (`!p t. prime p /\ FINITE t /\ (!q. q IN t ==> prime q)
         ==> (p divides nproduct t (\q. q) <=> p IN t)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NPRODUCT_CLAUSES; DIVIDES_ONE; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[PRIME_1];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `t:num->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[NPRODUCT_CLAUSES; PRIME_DIVPROD_EQ; DIVIDES_PRIME_PRIME] THEN
  REWRITE_TAC[IN_INSERT]);;

let NPRODUCT_PRIMES_INJ = prove
 (`!t1 t2. FINITE t1 /\ FINITE t2 /\
           (!q. q IN t1 ==> prime q) /\ (!q. q IN t2 ==> prime q) /\
           nproduct t1 (\q. q) = nproduct t2 (\q. q)
           ==> t1 = t2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `p:num` THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`p:num`; `t2:num->bool`] PRIME_DIVIDES_NPRODUCT_PRIMES) THEN
    MP_TAC(SPECL [`p:num`; `t1:num->bool`] PRIME_DIVIDES_NPRODUCT_PRIMES);
    MP_TAC(SPECL [`p:num`; `t1:num->bool`] PRIME_DIVIDES_NPRODUCT_PRIMES) THEN
    MP_TAC(SPECL [`p:num`; `t2:num->bool`] PRIME_DIVIDES_NPRODUCT_PRIMES)] THEN
  ASM_SIMP_TAC[]);;

let REMAINDER_SUM_TWO = prove
 (`!s z. FINITE s /\ (!p. p IN s ==> prime p /\ 3 <= p) /\ &1 <= z
         ==> sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}
                 (\t. &4 pow CARD t * &2 pow CARD t) <= z pow 6`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `FINITE {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `D = {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD(D:(num->bool)->bool)) * z pow 4` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[GSYM PRODUCT_CONST] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product t (\p. &p * &p)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `3 <= p` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 * &3` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `product t (\p. &p * &p) = &(nproduct t (\p. p)) pow 2`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[REAL_OF_NUM_NPRODUCT; PRODUCT_MUL; REAL_POW_2];
        ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `4 = 2 * 2`; GSYM REAL_POW_POW] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `6 = 2 + 4`; REAL_POW_ADD] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE;
    ASSUME `&1 <= z`; REAL_ARITH `&1 <= z ==> &0 <= z`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(CARD {b | 1 <= b /\ &b < z pow 2})` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC CARD_NUM_RANGE_LE THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\t. nproduct t (\p. p)) (D:(num->bool)->bool))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NPRODUCT_PRIMES_INJ THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ASM_MESON_TAC[FINITE_SUBSET];
      ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[SUBSET]];
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUM_RANGE] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN D ==> f x IN S)
      ==> IMAGE (f:(num->bool)->num) D SUBSET S`) THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `3 <= p` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The sieve bound.                                                          *)
(* ------------------------------------------------------------------------- *)

let SIEVE_TWO_RESIDUES = prove
 (`!f c N M z.
        EVEN N /\ ~(N = 0) /\ &1 < z /\
        (!p. prime p /\ ~(p divides N) ==> ~(c p = 0) /\ c p < p) /\
        (!p n. prime p /\ ~(p divides N) /\ n IN 1..M
               ==> (p divides f n <=> n MOD p = 0 \/ n MOD p = c p))
        ==> &(CARD {n | n IN 1..M /\
                        !p. prime p /\ &p < z /\ ~(p divides N)
                            ==> ~(p divides f n)})
            <= &4 * &M /
               (product {p | prime p /\ p divides N} (\p. &1 - inv(&p)) *
                log z) pow 2 + z pow 6`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = {p | prime p /\ &p < z /\ ~(p divides N)}` THEN
  SUBGOAL_THEN `FINITE(s:num->bool) /\ (!p. p IN s ==> prime p /\ 3 <= p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{p | prime p /\ &p < z}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC `p:num` PRIME_GE_2) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(ARITH_RULE `~(p = 2) ==> 2 <= p ==> 3 <= p`) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(2 divides N)` THEN
      ASM_MESON_TAC[EVEN_EXISTS; divides]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:num->num) (1..M)`;
                 `\m. &(CARD {n | n IN 1..M /\ (f:num->num) n = m})`;
                 `s:num->bool`; `&M`; `\p:num. &2 / &p`; `z:real`]
                SELBERG_SIEVE) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; REAL_POS] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `3 <= p ==> 1 <= p`]; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&3 <= &p` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SIFTED_IMAGE; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `{n | n IN 1..M /\ !p. p IN s ==> ~(p divides (f:num->num) n)} =
    {n | n IN 1..M /\ !p. prime p /\ &p < z /\ ~(p divides N)
                          ==> ~(p divides f n)}` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b a' b' x:real. a <= a' /\ b <= b'
                       ==> x <= a + b ==> x <= a' + b'`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM selberg_G] THEN
    MP_TAC(SPECL [`N:num`; `z:real`] SELBERG_G_TWO_LOWER) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC
     `Q = product {p | prime p /\ p divides N} (\p. &1 - inv(&p))` THEN
    SUBGOAL_THEN `&0 < Q` ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
      ASM_SIMP_TAC[FINITE_PRIME_DIVISORS; IN_ELIM_THM] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN
      MATCH_MP_TAC REAL_INV_LT_1 THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 < p`];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < log z` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ABBREV_TAC `G = selberg_G (\p. &2 / &p) s z` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (Q * log z / &2) pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&M / (Q * log z / &2) pow 2` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC BINOP_CONV [real_div] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < Q` THEN UNDISCH_TAC `&0 < log z` THEN
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET s /\ &(nproduct t (\p. p)) < z pow 2}
                  (\t. &4 pow CARD t * &2 pow CARD t)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REMAINDER_SUM_TWO THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  SUBGOAL_THEN `FINITE(t:num->bool) /\
                (!p. p IN t ==> prime p /\ ~(p divides N))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(t:num->bool) SUBSET s` THEN EXPAND_TAC "s" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SIEVE_COUNT_IMAGE; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `{n | n IN 1..M /\ !p. p IN t ==> p divides (f:num->num) n} =
    {n | n IN 1..M /\ !p. p IN t ==> n MOD p = 0 \/ n MOD p = c p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `n:num` THEN
    ASM_CASES_TAC `n IN 1..M` THEN ASM_REWRITE_TAC[] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_CASES_TAC `(p:num) IN t` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p r. r = 0 \/ r = (c:num->num) p`; `t:num->bool`; `M:num`]
                CRT_COUNT) THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `!p. p IN t ==> CARD {r | r < p /\ (r = 0 \/ r = c p)} = 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_TWO_RESIDUES THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CONST; REAL_POW_LE] THEN
  SUBGOAL_THEN
   `product t (\p. &(CARD {r | r < p /\ (r = 0 \/ r = c p)}) / &p) =
                product t (\p. &2 / &p)` SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `product t (\p. &(CARD {r | r < p /\ (r = 0 \/ r = c p)})) =
                &2 pow CARD t` SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_CONST] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[]]);;
