(* ========================================================================= *)
(* The Jurkat-Richert theorem for the linear sieve ([N] Theorems 9.5-9.7).   *)
(* Final form: JURKAT_RICHERT (classical dimension condition with constant   *)
(* L, error e > 0 for a suitable w depending only on L and e, uniformly in   *)
(* the density g).                                                           *)
(*                                                                           *)
(* The sifting primes are those in [w,z) (sieve_primes w z), with            *)
(* V(z) = prod (1 - g p) over them (sieve_V g w z), and the dimension        *)
(* condition is V(u) <= K (log v / log u) V(v) for w <= u <= v.  Theorem     *)
(* 9.5 is ROSSER_T_BOUND.  Unlike [N], its odd case 1 <= s < 3 reduces       *)
(* to the level D^(1/3) and pays a factor K there; the modified h of         *)
(* linear.ml absorbs it.                                                     *)
(* ========================================================================= *)

needs "Sieve/linear.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* [N] Lemma 9.2: sums of g(p) V(p) over a tail telescope.                   *)
(* ------------------------------------------------------------------------- *)

let FINITE_NUM_MAX_INDUCT = prove
 (`!P:(num->bool)->bool.
        P {} /\
        (!q s. FINITE s /\ (!r. r IN s ==> r < q) /\ P s ==> P(q INSERT s))
        ==> !s. FINITE s ==> P s`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "step")) THEN
  GEN_TAC THEN WF_INDUCT_TAC `CARD(s:num->bool)` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:num->bool = {}` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:num->bool` FINITE_NUM_MAX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s = (q:num) INSERT (s DELETE q)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  USE_THEN "step" MATCH_MP_TAC THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[LT_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(s:num->bool) DELETE q` o
                check (is_forall o concl)) THEN
  ASM_SIMP_TAC[CARD_DELETE; FINITE_DELETE] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
  ASM_SIMP_TAC[CARD_EQ_0]);;

let SUM_PRODUCT_TAIL = prove
 (`!(g:num->real) s.
        FINITE s
        ==> !u. sum {p | p IN s /\ u <= &p}
                    (\p. g p * product {q | q IN s /\ q < p} (\q. &1 - g q)) =
                product {q | q IN s /\ &q < u} (\q. &1 - g q) -
                product s (\q. &1 - g q)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_NUM_MAX_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; SUM_CLAUSES; PRODUCT_CLAUSES] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `s:num->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `u:real` THEN
  SUBGOAL_THEN `~((q:num) IN s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:num. u <= &p`;
                 `\p:num t:num->bool.
                    (g:num->real) p * product t (\q. &1 - g q)`;
                 `q:num`; `s:num->bool`] SUM_INSERT_MAX_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN
  ABBREV_TAC `V = product s (\q. &1 - (g:num->real) q)` THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{r | r IN (q:num) INSERT s /\ &r < u} =
                  {r | r IN s /\ &r < u}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
      X_GEN_TAC `r:num` THEN ASM_CASES_TAC `r:num = q` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `A = product {r | r IN s /\ &r < u} (\q. &1 - (g:num->real) q)`
    THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{r | r IN (q:num) INSERT s /\ &r < u} = q INSERT s /\
                {r | r IN s /\ &r < u} = s`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN CONJ_TAC THEN
    X_GEN_TAC `r:num` THEN EQ_TAC THEN SIMP_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The sifting range [w,z), the product V and the dimension condition.       *)
(* ------------------------------------------------------------------------- *)

let sieve_primes = new_definition
 `sieve_primes w z = {p | prime p /\ w <= &p /\ &p < z}`;;

let sieve_V = new_definition
 `sieve_V (g:num->real) w z = product (sieve_primes w z) (\p. &1 - g p)`;;

let IN_SIEVE_PRIMES = prove
 (`!w z p. p IN sieve_primes w z <=> prime p /\ w <= &p /\ &p < z`,
  REWRITE_TAC[sieve_primes; IN_ELIM_THM]);;

let FINITE_SIEVE_PRIMES = prove
 (`!w z. FINITE(sieve_primes w z)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p | prime p /\ &p < z}` THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SIEVE_PRIMES] THEN MESON_TAC[]);;

let SIEVE_PRIMES_EMPTY = prove
 (`!w z. z <= w ==> sieve_primes w z = {}`,
  REWRITE_TAC[EXTENSION; IN_SIEVE_PRIMES; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

let SIEVE_PRIMES_RESTRICT = prove
 (`!w z u. u <= z
           ==> {q | q IN sieve_primes w z /\ &q < u} = sieve_primes w u`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SIEVE_PRIMES] THEN
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `prime x` THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_PRIMES_LT = prove
 (`!w z p. &p <= z
           ==> {q | q IN sieve_primes w z /\ q < p} = sieve_primes w (&p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN
  MATCH_MP_TAC SIEVE_PRIMES_RESTRICT THEN ASM_REWRITE_TAC[]);;

let SIEVE_V_EMPTY = prove
 (`!g w z. z <= w ==> sieve_V g w z = &1`,
  SIMP_TAC[sieve_V; SIEVE_PRIMES_EMPTY; PRODUCT_CLAUSES]);;

let SIEVE_V_POS = prove
 (`!g w z. (!p. prime p /\ w <= &p ==> g p < &1) ==> &0 < sieve_V g w z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_V] THEN
  MATCH_MP_TAC PRODUCT_POS_LT THEN
  REWRITE_TAC[FINITE_SIEVE_PRIMES; IN_SIEVE_PRIMES] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN ASM_SIMP_TAC[]);;

let SIEVE_V_TAIL = prove
 (`!g w z u.
        u <= z
        ==> sum {p | p IN sieve_primes w z /\ u <= &p}
                (\p. g p * sieve_V g w (&p)) =
            sieve_V g w u - sieve_V g w z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:num->real`; `sieve_primes w z`] SUM_PRODUCT_TAIL) THEN
  REWRITE_TAC[FINITE_SIEVE_PRIMES] THEN DISCH_THEN(MP_TAC o SPEC `u:real`) THEN
  ASM_SIMP_TAC[SIEVE_PRIMES_RESTRICT; GSYM sieve_V] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&p <= z` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SIEVE_PRIMES; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[sieve_V; SIEVE_PRIMES_LT]);;

let SIEVE_K_EXTEND = prove
 (`!g w K.
        &2 <= w /\ &0 <= K /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v)
        ==> !u v. &1 < u /\ u <= v /\ w <= v
                  ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `w <= u` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `sieve_V g w u = sieve_V g w w` SUBST1_TAC THENL
   [ASM_SIMP_TAC[SIEVE_V_EMPTY; REAL_LE_REFL] THEN
    MATCH_MP_TAC SIEVE_V_EMPTY THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `K * (log v / log w) * sieve_V g w v` THEN
  ASM_SIMP_TAC[REAL_LE_REFL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SIEVE_V_POS THEN
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `&0 < log u /\ log u <= log w /\ &0 <= log v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* [N] Lemma 9.8 for the sieve: sum_p g(p) V(p) psi(log D / log p) <=        *)
(* V(z) ((K - 1) psi(s) + (K / s) int_s^S psi), s = log D / log z.           *)
(* ------------------------------------------------------------------------- *)

let SIEVE_WEIGHTED_SUM_BOUND = prove
 (`!g w K psi D z.
        &2 <= w /\ &1 <= K /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v) /\
        w < z /\ &0 < log D /\
        (!u v. log D / log z <= u /\ u <= v /\ v <= log D / log(&2)
               ==> psi v <= psi u) /\
        (!u. log D / log z <= u /\ u <= log D / log(&2) ==> &0 <= psi u)
        ==> sum (sieve_primes w z)
                (\p. (g p * sieve_V g w (&p)) * psi(log D / log(&p))) <=
            sieve_V g w z *
            ((K - &1) * psi(log D / log z) +
             K / (log D / log z) *
             real_integral (real_interval[log D / log z,log D / log(&2)])
                           psi)`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `s = log D / log z` THEN ABBREV_TAC `S = log D / log(&2)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log z /\ &0 < log(&2) /\ log(&2) <= log z`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s /\ s <= S` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s"; "S"] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_DIV_DENOM];
    ALL_TAC] THEN
  ABBREV_TAC `V = sieve_V g w z` THEN
  SUBGOAL_THEN `&0 < V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN sieve_primes w z
        ==> &0 < log(&p) /\ log(&2) <= log(&p) /\ log(&p) < log z /\
            w <= &p /\ &p < z`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_SIEVE_PRIMES] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_GE_2]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`psi:real->real`; `\p:num. log D / log(&p)`;
                 `\p:num. (g:num->real) p * sieve_V g w (&p)`;
                 `s:real`; `S:real`; `(K - &1) * (V:real)`; `K * (V:real) / s`;
                 `sieve_primes w z`] SUM_CUMULATIVE_DECREASING_BOUND) THEN
  REWRITE_TAC[FINITE_SIEVE_PRIMES] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["s"; "S"] THEN
      ASM_SIMP_TAC[REAL_LE_DIV_DENOM; REAL_LT_IMP_LE];
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_SIEVE_PRIMES] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SIEVE_V_POS THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `{q | q IN sieve_primes w z /\ log D / log(&q) <= log D / log(&p)} =
      {q | q IN sieve_primes w z /\ &p <= &q}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `q:num` THEN
      ASM_CASES_TAC `(q:num) IN sieve_primes w z` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_DIV_DENOM] THEN
      MATCH_MP_TAC LOG_MONO_LE THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
      UNDISCH_TAC `(q:num) IN sieve_primes w z` THEN
      UNDISCH_TAC `(p:num) IN sieve_primes w z` THEN
      REWRITE_TAC[IN_SIEVE_PRIMES] THEN MESON_TAC[PRIME_IMP_NZ; LT_NZ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SIEVE_V_TAIL; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `K * (log z / log(&p)) * V - V` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `a <= b ==> a - v <= b - v`) THEN
      EXPAND_TAC "V" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "s" THEN
      UNDISCH_TAC `&0 < log D` THEN UNDISCH_TAC `&0 < log z` THEN
      UNDISCH_TAC `&0 < log(&p)` THEN CONV_TAC REAL_FIELD];
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* The recursion for T_n on the sifting range, and the reduction of the      *)
(* odd terms to the level D^(1/3).                                           *)
(* ------------------------------------------------------------------------- *)

let ROSSER_T_SIEVE_PRIMES = prove
 (`!n g D w z.
        ~(n = 0)
        ==> rosser_T (SUC n) g D (sieve_primes w z) =
            sum {p | p IN sieve_primes w z /\
                     (if EVEN n then &(p EXP 3) < D else &p < D)}
                (\p. g p * rosser_T n g (D / &p) (sieve_primes w (&p)))`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[rosser_T] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&p <= z` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SIEVE_PRIMES; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_PRIMES_LT]);;

let ROSSER_T1_SIEVE_PRIMES = prove
 (`!g D w z.
        rosser_T 1 g D (sieve_primes w z) =
        sum {p | p IN sieve_primes w z /\ D <= &(p EXP 3)}
            (\p. g p * sieve_V g w (&p))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 3 RATOR_CONV o RAND_CONV) [ONE] THEN
  REWRITE_TAC[rosser_T] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&p <= z` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_SIEVE_PRIMES; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_SIMP_TAC[sieve_V; SIEVE_PRIMES_LT]);;

let CUBE_LE_EXP_LOG = prove
 (`!D x. &0 < D /\ &0 < x ==> (D <= x pow 3 <=> exp(log D / &3) <= x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = exp(log x)`
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[REAL_EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN
  SUBGOAL_THEN `D <= x pow 3 <=> log D <= log(x pow 3)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_MONO_LE THEN
    ASM_SIMP_TAC[REAL_POW_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC);;

let CUBE_LT_EXP_LOG = prove
 (`!D x. &0 < D /\ &0 < x ==> (x pow 3 < D <=> x < exp(log D / &3))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  ASM_SIMP_TAC[CUBE_LE_EXP_LOG]);;

let PRIME_CUBE_LE = prove
 (`!D p. &0 < D /\ prime p ==> (D <= &(p EXP 3) <=> exp(log D / &3) <= &p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC CUBE_LE_EXP_LOG THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ]);;

let PRIME_CUBE_LT = prove
 (`!D p. &0 < D /\ prime p ==> (&(p EXP 3) < D <=> &p < exp(log D / &3))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN
  MATCH_MP_TAC CUBE_LT_EXP_LOG THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LT; LT_NZ; PRIME_IMP_NZ]);;

let ROSSER_T_ODD_REDUCE = prove
 (`!n g D w z.
        EVEN n /\ ~(n = 0) /\ &0 < D /\ exp(log D / &3) <= z
        ==> rosser_T (SUC n) g D (sieve_primes w z) =
            rosser_T (SUC n) g D (sieve_primes w (exp(log D / &3)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[ROSSER_T_SIEVE_PRIMES] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SIEVE_PRIMES] THEN
  X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[PRIME_CUBE_LT] THEN ASM_REAL_ARITH_TAC);;

let EXP_LOG_DIV3_LE = prove
 (`!D z. &0 < z /\ &0 < log z
         ==> (exp(log D / &3) <= z <=> log D / log z <= &3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z = exp(log z)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[REAL_EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

let EXP_LOG_DIV3_GE = prove
 (`!D z. &0 < z /\ &0 < log z
         ==> (z <= exp(log D / &3) <=> &3 <= log D / log z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `z = exp(log z)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[REAL_EXP_LOG]; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* [N] Theorem 9.5: T_n(D,z) <= V(z) (f_n(s) + (K - 1) E R^n h(s)) with      *)
(* E = 10^5 and R = 199/200, for K <= 1 + 1/10000.                           *)
(* ------------------------------------------------------------------------- *)

let ROSSER_T1_BOUND = prove
 (`!g w K D z.
        &2 <= w /\ &1 <= K /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v) /\
        &0 < D /\ &1 <= log D / log z
        ==> rosser_T 1 g D (sieve_primes w z) <=
            sieve_V g w z *
            (sieve_fn 1 (log D / log z) +
             (K - &1) * exp(&3) * sieve_h(log D / log z))`,
  REPEAT GEN_TAC THEN ABBREV_TAC `s = log D / log z` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= sieve_fn 1 s + (K - &1) * exp(&3) * sieve_h s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIEVE_FN_POS THEN ASM_REWRITE_TAC[LE_REFL] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE; SIEVE_H_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sieve_V g w z` ASSUME_TAC THENL
   [MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ROSSER_T1_SIEVE_PRIMES] THEN
  ASM_CASES_TAC `z <= w` THENL
   [ASM_SIMP_TAC[SIEVE_PRIMES_EMPTY; SIEVE_V_EMPTY; NOT_IN_EMPTY; EMPTY_GSPEC;
                 SUM_CLAUSES; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log z` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log D` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= s` THEN EXPAND_TAC "s" THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = exp(log D / &3)` THEN
  SUBGOAL_THEN `log u = log D / &3 /\ &1 < u` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[LOG_EXP] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
    REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{p | p IN sieve_primes w z /\ D <= &(p EXP 3)} =
    {p | p IN sieve_primes w z /\ u <= &p}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `(p:num) IN sieve_primes w z` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "u" THEN MATCH_MP_TAC PRIME_CUBE_LE THEN
    ASM_MESON_TAC[IN_SIEVE_PRIMES];
    ALL_TAC] THEN
  ASM_CASES_TAC `&3 <= s` THENL
   [SUBGOAL_THEN `z <= u` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN
      MP_TAC(SPECL [`D:real`; `z:real`] EXP_LOG_DIV3_GE) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{p | p IN sieve_primes w z /\ u <= &p} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_SIEVE_PRIMES] THEN
      X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUM_CLAUSES] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `u <= z` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN
    MP_TAC(SPECL [`D:real`; `z:real`] EXP_LOG_DIV3_LE) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_V_TAIL] THEN
  MP_TAC(ISPECL [`g:num->real`; `w:real`; `K:real`] SIEVE_K_EXTEND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real`; `z:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `log z / (log D / &3) = &3 / s` SUBST1_TAC THENL
   [EXPAND_TAC "s" THEN UNDISCH_TAC `&0 < log D` THEN
    UNDISCH_TAC `&0 < log z` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[SIEVE_FN_1] THEN ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 - s) / s = &3 / s - &1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MP_TAC(SPEC `s:real` SIEVE_H_SMALL_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `((K - &1) * sieve_V g w z) * &3 / s <=
    ((K - &1) * sieve_V g w z) * exp(&3) * sieve_h s`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `t = &3 / s` THEN ABBREV_TAC `V = sieve_V g w z` THEN
  ABBREV_TAC `e = exp(&3) * sieve_h s` THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REPEAT DISCH_TAC THEN
  ASM_REAL_ARITH_TAC);;

let ROSSER_T_STEP = prove
 (`!g w K n C.
        &2 <= w /\ &1 <= K /\ &0 <= C /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v) /\
        1 <= n /\
        (!D z. &0 < D /\ (if ODD n then &1 else &2) <= log D / log z
               ==> rosser_T n g D (sieve_primes w z) <=
                   sieve_V g w z *
                   (sieve_fn n (log D / log z) +
                    (K - &1) * C * sieve_h(log D / log z)))
        ==> !D z. &0 < D /\ (if EVEN n then &3 else &2) <= log D / log z
                  ==> rosser_T (SUC n) g D (sieve_primes w z) <=
                      sieve_V g w z *
                      (sieve_fn (SUC n) (log D / log z) +
                       (K - &1) *
                       (&2 * exp(&2) * sieve_a pow (n - 1) * (sieve_a + &4) +
                        (K * sieve_a + &4 * (K - &1)) * C) *
                       sieve_h(log D / log z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `s = log D / log z` THEN STRIP_TAC THEN
  ABBREV_TAC `X = &2 * exp(&2) * sieve_a pow (n - 1) * (sieve_a + &4) +
                  (K * sieve_a + &4 * (K - &1)) * C` THEN
  SUBGOAL_THEN `&2 <= s` ASSUME_TAC THENL
   [UNDISCH_TAC `(if EVEN n then &3 else &2) <= s` THEN COND_CASES_TAC THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE] THEN
    TRY(MATCH_MP_TAC REAL_LE_ADD) THEN
    REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sieve_V g w z` ASSUME_TAC THENL
   [MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sieve_fn (SUC n) s + (K - &1) * X * sieve_h s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC SIEVE_FN_POS THEN CONJ_TAC THENL
       [ARITH_TAC; ASM_REAL_ARITH_TAC];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[SIEVE_H_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ROSSER_T_SIEVE_PRIMES] THEN
  ASM_CASES_TAC `z <= w` THENL
   [ASM_SIMP_TAC[SIEVE_PRIMES_EMPTY; SIEVE_V_EMPTY; NOT_IN_EMPTY;
                 EMPTY_GSPEC; SUM_CLAUSES; REAL_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log z` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log D` ASSUME_TAC THENL
   [UNDISCH_TAC `&2 <= s` THEN EXPAND_TAC "s" THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `psi = \t. sieve_fn n (t - &1) + ((K - &1) * C) * sieve_h(t - &1)` THEN
  SUBGOAL_THEN
   `!t. &2 <= t ==> &0 <= psi t /\
                    !t'. t <= t' ==> psi t' <= psi t`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "psi" THEN
    MP_TAC(SPEC `n:num` SIEVE_FN_PROPS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= (K - &1) * C` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[SIEVE_H_POS_LE]];
      X_GEN_TAC `t':real` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SIEVE_H_DECREASING THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum (sieve_primes w z)
        (\p. ((g:num->real) p * sieve_V g w (&p)) * psi(log D / log(&p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum {p | p IN sieve_primes w z /\
               (if EVEN n then &(p EXP 3) < D else &p < D)}
          (\p. ((g:num->real) p * sieve_V g w (&p)) *
               psi(log D / log(&p)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_SIEVE_PRIMES] THEN
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_SIEVE_PRIMES] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_GE_2]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < log(&p) /\ log(&p) < log z` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `s < log D / log(&p)` ASSUME_TAC THENL
       [EXPAND_TAC "s" THEN
        MP_TAC(SPECL [`log z`; `log(&p)`; `log D`] REAL_LT_DIV_DENOM) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `log(D / &p) / log(&p) = log D / log(&p) - &1`
      ASSUME_TAC THENL
       [ASM_SIMP_TAC[LOG_DIV; REAL_ARITH `&2 <= x ==> &0 < x`] THEN
        UNDISCH_TAC `&0 < log(&p)` THEN CONV_TAC REAL_FIELD;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`D / &p`; `&p`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(if EVEN n then &3 else &2) <= s` THEN
        ASM_CASES_TAC `ODD n` THEN ASM_REWRITE_TAC[GSYM NOT_ODD] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
      AP_TERM_TAC THEN EXPAND_TAC "psi" THEN REWRITE_TAC[REAL_MUL_ASSOC];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_SIEVE_PRIMES; SUBSET; IN_ELIM_THM; IN_DIFF] THEN
      SIMP_TAC[] THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      UNDISCH_TAC `(p:num) IN sieve_primes w z` THEN
      REWRITE_TAC[IN_SIEVE_PRIMES] THEN STRIP_TAC THEN
      SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_OF_NUM_LE; PRIME_GE_2]; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < log(&p) /\ log(&p) < log z` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC LOG_MONO_LT_IMP THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `s <= log D / log(&p)` ASSUME_TAC THENL
       [EXPAND_TAC "s" THEN
        MP_TAC(SPECL [`log z`; `log(&p)`; `log D`] REAL_LE_DIV_DENOM) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC SIEVE_V_POS THEN
        ASM_SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `log D / log(&p)`) THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]]];
    ALL_TAC] THEN
  ABBREV_TAC `S = log D / log(&2)` THEN
  MP_TAC(ISPECL [`g:num->real`; `w:real`; `K:real`; `psi:real->real`;
                 `D:real`; `z:real`] SIEVE_WEIGHTED_SUM_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `psi:real->real`)) (concl th)))
      THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `u:real` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `psi:real->real`)) (concl th)))
      THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `&1 < s /\ s <= S` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["s"; "S"] THEN
    MP_TAC(SPECL [`log z`; `log(&2)`; `log D`] REAL_LE_DIV_DENOM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `real_integral (real_interval[s,S]) psi =
    real_integral (real_interval[s,S]) (\t. sieve_fn n (t - &1)) +
    ((K - &1) * C) *
    real_integral (real_interval[s,S]) (\t. sieve_h(t - &1))`
  SUBST1_TAC THENL
   [EXPAND_TAC "psi" THEN
    MP_TAC(ISPECL [`\t. sieve_fn n (t - &1)`;
                   `\t. ((K - &1) * C) * sieve_h(t - &1)`;
                   `real_interval[s,S]`] REAL_INTEGRAL_ADD) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[SIEVE_FN_SHIFT_INTEGRABLE; REAL_INTEGRABLE_LMUL;
                   SIEVE_H_SHIFT_INTEGRABLE];
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC REAL_INTEGRAL_LMUL THEN
    REWRITE_TAC[SIEVE_H_SHIFT_INTEGRABLE];
    ALL_TAC] THEN
  EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `s:real`; `S:real`] SIEVE_FN_INTEGRAL_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`s:real`; `S:real`] SIEVE_H_INTEGRAL_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`n:num`; `s - &1`] SIEVE_FN_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(if EVEN n then &3 else &2) <= s` THEN
    REWRITE_TAC[GSYM NOT_ODD] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`SUC n`; `s:real`] SIEVE_FN_BOUND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPEC `s:real` SIEVE_H_SHIFT) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
  SUBGOAL_THEN `sieve_a pow (SUC n - 1) = sieve_a * sieve_a pow (n - 1)`
  SUBST_ALL_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = sieve_a pow (n - 1)` THEN
  ABBREV_TAC `E = exp(&2)` THEN
  ABBREV_TAC `f1 = sieve_fn n (s - &1)` THEN
  ABBREV_TAC `fS = sieve_fn (SUC n) s` THEN
  ABBREV_TAC `h1 = sieve_h(s - &1)` THEN
  ABBREV_TAC `hs = sieve_h s` THEN
  ABBREV_TAC `If = real_integral (real_interval[s,S])
                                 (\t. sieve_fn n (t - &1))` THEN
  ABBREV_TAC `Ih = real_integral (real_interval[s,S])
                                 (\t. sieve_h(t - &1))` THEN
  ABBREV_TAC `Ks = (K:real) / s` THEN
  SUBGOAL_THEN `&0 <= Ks /\ Ks * s = K` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ks" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= E /\ &0 <= P /\ &0 <= hs` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["E"; "P"; "hs"] THEN
    ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE;
                 SIEVE_H_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K - &1) * f1 <= (K - &1) * (&8 * E * P * hs)` ASSUME_TAC
  THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 * E * P * h1` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&8 * E * P * hs = (&2 * E * P) * (&4 * hs)`;
                REAL_ARITH `&2 * E * P * h1 = (&2 * E * P) * h1`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((K - &1) * ((K - &1) * C)) * h1 <=
    ((K - &1) * ((K - &1) * C)) * (&4 * hs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Ks * If <= K * fS` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(Ks:real) * (s * fS)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Ks * (((K - &1) * C) * Ih) <= K * ((K - &1) * C) * sieve_a * hs`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(Ks:real) * (((K - &1) * C) * (sieve_a * s * hs))` THEN
      CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `(Ks:real) * s = K` THEN CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K - &1) * fS <= (K - &1) * (&2 * E * (sieve_a * P) * hs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXPAND_TAC "X" THEN
  ABBREV_TAC `a = sieve_a` THEN
  ASM_REAL_ARITH_TAC);;

let SIEVE_T_CONSTANTS = prove
 (`!K n. &1 <= K /\ K <= &1 + &1 / &10000 /\ 1 <= n
         ==> &2 * exp(&2) * sieve_a pow n +
             K * (&2 * exp(&2) * sieve_a pow (n - 1) * (sieve_a + &4) +
                  (K * sieve_a + &4 * (K - &1)) *
                  (&100000 * (&199 / &200) pow n))
             <= &100000 * (&199 / &200) pow (SUC n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sieve_a pow n = sieve_a * sieve_a pow (n - 1) /\
    (&199 / &200) pow n = (&199 / &200) * (&199 / &200) pow (n - 1) /\
    (&199 / &200) pow (SUC n) =
    (&199 / &200) * (&199 / &200) * (&199 / &200) pow (n - 1)`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> SUC(n - 1) = n`];
    ALL_TAC] THEN
  REWRITE_TAC[sieve_a] THEN
  MP_TAC(SPECL [`n - 1`; `&99 / &100`; `&199 / &200`] REAL_POW_LE2) THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= (&199 / &200) pow (n - 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= exp(&2) /\ exp(&2) <= &7393 / &1000` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[REAL_EXP_POS_LE] THEN
    SUBGOAL_THEN `exp(&2) = exp(&1) * exp(&1)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM REAL_EXP_ADD] THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC E_BOUNDS THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2719 / &1000 * &2719 / &1000` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `P = (&99 / &100) pow (n - 1)` THEN
  ABBREV_TAC `Q = (&199 / &200) pow (n - 1)` THEN
  ABBREV_TAC `E = exp(&2)` THEN
  SUBGOAL_THEN `&0 <= K * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `E * P <= E * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(E * K) * P <= (E * K) * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `E * Q <= &7393 / &1000 * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `E * (K * Q) <= &7393 / &1000 * (K * Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `K * Q <= (&1 + &1 / &10000) * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `K * (K * Q) <= (&1 + &1 / &10000) * (K * Q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 * Q <= K * Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let ROSSER_T_BOUND = prove
 (`!g w K.
        &2 <= w /\ &1 <= K /\ K <= &1 + &1 / &10000 /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v)
        ==> !n D z.
              1 <= n /\ &0 < D /\
              (if ODD n then &1 else &2) <= log D / log z
              ==> rosser_T n g D (sieve_primes w z) <=
                  sieve_V g w z *
                  (sieve_fn n (log D / log z) +
                   (K - &1) * (&100000 * (&199 / &200) pow n) *
                   sieve_h(log D / log z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC SIEVE_A_BOUNDS THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. &0 < sieve_V g w z` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  INDUCT_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[GSYM ONE; ARITH; REAL_POW_1] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sieve_V g w z * (sieve_fn 1 (log D / log z) +
                (K - &1) * exp(&3) * sieve_h(log D / log z))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ROSSER_T1_BOUND THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a + b <= a + c:real`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[SIEVE_H_POS_LE] THEN
    MP_TAC EXP_3_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_forall(concl th) &&
                                          free_in `n:num` (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`g:num->real`; `w:real`; `K:real`; `n:num`;
                `&100000 * (&199 / &200) pow n`] ROSSER_T_STEP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`K:real`; `n:num`] SIEVE_T_CONSTANTS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `X = &2 * exp(&2) * sieve_a pow (n - 1) * (sieve_a + &4) +
                  (K * sieve_a + &4 * (K - &1)) *
                  (&100000 * (&199 / &200) pow n)` THEN
  ABBREV_TAC `Z = &100000 * (&199 / &200) pow (SUC n)` THEN
  ABBREV_TAC `G = &2 * exp(&2) * sieve_a pow n` THEN
  DISCH_TAC THEN DISCH_THEN(LABEL_TAC "main") THEN
  SUBGOAL_THEN `&0 <= X /\ &0 <= G` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["X"; "G"] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE] THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN
      TRY(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_LE_MUL) THEN ASM_REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_POS; REAL_EXP_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `X <= Z` ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 * X <= K * X` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN ABBREV_TAC `s = log D / log z` THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [UNDISCH_TAC `(if ODD (SUC n) then &1 else &2) <= s` THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sieve_fn (SUC n) s /\ &0 <= sieve_h s`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[SIEVE_FN_POS; SIEVE_H_POS_LE; ARITH_RULE `1 <= SUC n`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!T. T <= sieve_V g w z * (sieve_fn (SUC n) s + (K - &1) * X * sieve_h s)
        ==> T <= sieve_V g w z *
                 (sieve_fn (SUC n) s + (K - &1) * Z * sieve_h s)`
  (LABEL_TAC "XZ") THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a + b <= a + c:real`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `EVEN n /\ s < &3` THENL
   [POP_ASSUM STRIP_ASSUME_TAC;
    USE_THEN "XZ" MATCH_MP_TAC THEN EXPAND_TAC "s" THEN
    USE_THEN "main" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(if ODD (SUC n) then &1 else &2) <= s` THEN
    UNDISCH_TAC `~(EVEN n /\ s < &3)` THEN
    REWRITE_TAC[ODD; NOT_ODD] THEN
    ASM_CASES_TAC `EVEN n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `z <= w` THENL
   [ASM_SIMP_TAC[ROSSER_T_SIEVE_PRIMES; SIEVE_PRIMES_EMPTY; NOT_IN_EMPTY;
                 EMPTY_GSPEC; SUM_CLAUSES] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Z" THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log z` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= s` ASSUME_TAC THENL
   [UNDISCH_TAC `(if ODD (SUC n) then &1 else &2) <= s` THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log D` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= s` THEN EXPAND_TAC "s" THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `u = exp(log D / &3)` THEN
  SUBGOAL_THEN `log u = log D / &3 /\ &1 < u /\ u <= z` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[LOG_EXP] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
      REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`D:real`; `z:real`] EXP_LOG_DIV3_LE) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `g:num->real`; `D:real`; `w:real`; `z:real`]
         ROSSER_T_ODD_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  USE_THEN "main" (MP_TAC o SPECL [`D:real`; `u:real`]) THEN
  SUBGOAL_THEN `log D / log u = &3` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < log D` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; SIEVE_H_3] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`g:num->real`; `w:real`; `K:real`] SIEVE_K_EXTEND) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real`; `z:real`]) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log z / log u = &3 / s` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "s" THEN
    UNDISCH_TAC `&0 < log D` THEN UNDISCH_TAC `&0 < log z` THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `s:real`] SIEVE_FN_ODD_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `s:real` SIEVE_H_SMALL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`SUC n`; `s:real`] SIEVE_FN_BOUND) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`; ODD; NOT_ODD;
                  ARITH_RULE `SUC n - 1 = n`] THEN
  DISCH_TAC THEN
  ABBREV_TAC `A = sieve_V g w z` THEN
  ABBREV_TAC `t3 = &3 / s` THEN
  ABBREV_TAC `f3 = sieve_fn (SUC n) (&3)` THEN
  ABBREV_TAC `fs = sieve_fn (SUC n) s` THEN
  ABBREV_TAC `e3 = exp(-- &3)` THEN
  ABBREV_TAC `hs = sieve_h s` THEN
  SUBGOAL_THEN `&0 <= f3 + (K - &1) * X * e3` ASSUME_TAC THENL
   [EXPAND_TAC "f3" THEN EXPAND_TAC "e3" THEN MATCH_MP_TAC REAL_LE_ADD THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SIEVE_FN_POS THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN REAL_ARITH_TAC;
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `t3 * f3 = fs /\ t3 * e3 <= hs` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t3" THEN CONJ_TAC THENL
     [UNDISCH_TAC `s * fs = &3 * f3` THEN UNDISCH_TAC `&0 < s` THEN
      CONV_TAC REAL_FIELD;
      REWRITE_TAC[REAL_ARITH `&3 / s * e = (&3 * e) / s`] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `sieve_V g w u * (f3 + (K - &1) * X * e3) <=
                (K * t3 * A) * (f3 + (K - &1) * X * e3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `((K:real) * A) * (t3 * f3) = (K * A) * fs` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(K * (K - &1) * A * X) * (t3 * e3) <=
                (K * (K - &1) * A * X) * hs`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(A * (K - &1)) * fs <= (A * (K - &1)) * (G * hs)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "G" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A * (K - &1) * hs) * (G + K * X) <= (A * (K - &1) * hs) * Z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* [N] Theorem 9.6: the main terms G+ and G- of Rosser's sieve against       *)
(* V(z) F(s) and V(z) f(s), via the Buchstab identity.                       *)
(* ------------------------------------------------------------------------- *)

let SIEVE_GEOMETRIC_SUMS = prove
 (`!N. sum(0..N) (\k. (&199 / &200) pow (2 * k + 1)) <= &200 /\
       sum(1..N) (\k. (&199 / &200) pow (2 * k)) <= &200`,
  GEN_TAC THEN
  SUBGOAL_THEN `!m. sum(m..N) (\k. (&199 / &200) pow k) <= &200`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[SUM_GP] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_EQ_CONV) THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= y /\ x <= &1 ==> (x - y) / (&1 / &200) <= &200`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_1_LE THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `sum(0..N) (\k. (&199 / &200) pow k)`;
    EXISTS_TAC `sum(1..N) (\k. (&199 / &200) pow k)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC);;

let ROSSER_G_UPPER_BOUND = prove
 (`!g w K.
        &2 <= w /\ &1 <= K /\ K <= &1 + &1 / &10000 /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v)
        ==> !D z. &0 < D /\ &1 <= log D / log z
                  ==> sum {t | t SUBSET sieve_primes w z}
                          (\t. rosser_lambda_plus D t * product t g) <=
                      sieve_V g w z *
                      (sieve_F(log D / log z) +
                       (K - &1) * &20000000 * sieve_h(log D / log z))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `s = log D / log z` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sieve_primes w z`; `g:num->real`; `D:real`;
                 `CARD(sieve_primes w z)`] ROSSER_BUCHSTAB_IDENTITY) THEN
  REWRITE_TAC[FINITE_SIEVE_PRIMES; LE_REFL] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_SIEVE_PRIMES; PRIME_0]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[GSYM sieve_V] THEN
  ABBREV_TAC `N = CARD(sieve_primes w z)` THEN
  ABBREV_TAC `V = sieve_V g w z` THEN
  SUBGOAL_THEN `&0 < V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:num->real`; `w:real`; `K:real`] ROSSER_T_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = (K - &1) * &100000 * sieve_h s` THEN
  SUBGOAL_THEN
   `sum (0..N) (\k. rosser_T (2 * k + 1) g D (sieve_primes w z)) <=
    V * (sum (0..N) (\k. sieve_fn (2 * k + 1) s) +
         c * sum (0..N) (\k. (&199 / &200) pow (2 * k + 1)))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2 * k + 1`; `D:real`; `z:real`]) THEN
    ASM_REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH; ARITH_RULE `1 <= 2 * k + 1`] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `s:real` SIEVE_FODD_SERIES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. sieve_fn (2 * k + 1) s`; `from 0`; `N:num`]
         REAL_PARTIAL_SUMS_LE_INFSUM) THEN
  ASM_REWRITE_TAC[FROM_INTER_NUMSEG; IN_FROM] THEN ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIEVE_FN_POS THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(SPEC `N:num` SIEVE_GEOMETRIC_SUMS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[SIEVE_H_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c * sum (0..N) (\k. (&199 / &200) pow (2 * k + 1)) <= c * &200`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[sieve_F] THEN
  ABBREV_TAC `Sf = sum (0..N) (\k. sieve_fn (2 * k + 1) s)` THEN
  ABBREV_TAC `Sg = sum (0..N) (\k. (&199 / &200) pow (2 * k + 1))` THEN
  ABBREV_TAC `Iinf = real_infsum (from 0) (\k. sieve_fn (2 * k + 1) s)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `V * (Sf + c * Sg) <= V * (Iinf + c * &200)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K - &1) * &20000000 * sieve_h s = &200 * c` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Tsum = sum (0..N)
                       (\k. rosser_T (2 * k + 1) g D (sieve_primes w z))` THEN
  ASM_REAL_ARITH_TAC);;

let ROSSER_G_LOWER_BOUND = prove
 (`!g w K.
        &2 <= w /\ &1 <= K /\ K <= &1 + &1 / &10000 /\
        (!p. prime p /\ w <= &p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v)
        ==> !D z. &0 < D /\ &2 <= log D / log z
                  ==> sieve_V g w z *
                      (sieve_f(log D / log z) -
                       (K - &1) * &20000000 * sieve_h(log D / log z)) <=
                      sum {t | t SUBSET sieve_primes w z}
                          (\t. rosser_lambda_minus D t * product t g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ABBREV_TAC `s = log D / log z` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`sieve_primes w z`; `g:num->real`; `D:real`;
                 `CARD(sieve_primes w z)`] ROSSER_BUCHSTAB_IDENTITY) THEN
  REWRITE_TAC[FINITE_SIEVE_PRIMES; LE_REFL] THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_SIEVE_PRIMES; PRIME_0]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_SIEVE_PRIMES] THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 < log z` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `log z < log D` ASSUME_TAC THENL
     [UNDISCH_TAC `&2 <= s` THEN EXPAND_TAC "s" THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `z < D` MP_TAC THENL
     [MP_TAC(SPECL [`z:real`; `D:real`] LOG_MONO_LT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
      ASM_REAL_ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[GSYM sieve_V] THEN
  ABBREV_TAC `N = CARD(sieve_primes w z)` THEN
  ABBREV_TAC `V = sieve_V g w z` THEN
  SUBGOAL_THEN `&0 < V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:num->real`; `w:real`; `K:real`] ROSSER_T_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `c = (K - &1) * &100000 * sieve_h s` THEN
  SUBGOAL_THEN
   `sum (1..N) (\k. rosser_T (2 * k) g D (sieve_primes w z)) <=
    V * (sum (1..N) (\k. sieve_fn (2 * k) s) +
         c * sum (1..N) (\k. (&199 / &200) pow (2 * k)))`
  MP_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_ADD_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`2 * k`; `D:real`; `z:real`]) THEN
    ASM_REWRITE_TAC[ODD_MULT; ARITH] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> x <= a ==> x <= b`) THEN
    EXPAND_TAC "c" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `s:real` SIEVE_FEVEN_SERIES) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`\k. sieve_fn (2 * k) s`; `from 1`; `N:num`]
         REAL_PARTIAL_SUMS_LE_INFSUM) THEN
  ASM_REWRITE_TAC[FROM_INTER_NUMSEG; IN_FROM] THEN ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SIEVE_FN_POS THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(SPEC `N:num` SIEVE_GEOMETRIC_SUMS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c` ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[SIEVE_H_POS_LE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c * sum (1..N) (\k. (&199 / &200) pow (2 * k)) <= c * &200`
  MP_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[sieve_f] THEN
  ABBREV_TAC `Sf = sum (1..N) (\k. sieve_fn (2 * k) s)` THEN
  ABBREV_TAC `Sg = sum (1..N) (\k. (&199 / &200) pow (2 * k))` THEN
  ABBREV_TAC `Iinf = real_infsum (from 1) (\k. sieve_fn (2 * k) s)` THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `V * (Sf + c * Sg) <= V * (Iinf + c * &200)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(K - &1) * &20000000 * sieve_h s = &200 * c` SUBST1_TAC THENL
   [EXPAND_TAC "c" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `Tsum = sum (1..N) (\k. rosser_T (2 * k) g D (sieve_primes w z))`
  THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* [N] Theorem 9.7 (Jurkat-Richert).  The primes below w are handled by      *)
(* Moebius inversion (ROSSER_SIEVE_*_EXTENDED), which multiplies the         *)
(* level by prod_{p < w} p; choosing w large makes K close to 1.             *)
(* ------------------------------------------------------------------------- *)

let SIEVE_PRIMES_SPLIT = prove
 (`!w z. w <= z
         ==> {p | prime p /\ &p < z} =
             sieve_primes w z UNION {p | prime p /\ &p < w} /\
             DISJOINT (sieve_primes w z) {p | prime p /\ &p < w}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; DISJOINT; IN_UNION; IN_INTER; NOT_IN_EMPTY;
              IN_ELIM_THM; IN_SIEVE_PRIMES] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let JR_SETUP = prove
 (`!w z D. &2 <= w /\ w <= z /\ &0 < D /\ &1 <= log D / log z
           ==> &0 < log z /\ log z <= log D /\ &1 < D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log z` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log z <= log D` ASSUME_TAC THENL
   [UNDISCH_TAC `&1 <= log D / log z` THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `D = exp(log D)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ASM_REWRITE_TAC[REAL_EXP_LOG]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_EXP_0] THEN
  REWRITE_TAC[REAL_EXP_MONO_LT] THEN ASM_REAL_ARITH_TAC);;

let JURKAT_RICHERT_UPPER_K = prove
 (`!A a X g w K D z.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ &0 <= X /\
        &2 <= w /\ w <= z /\ &1 <= K /\ K <= &1 + &1 / &10000 /\
        (!p. prime p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v) /\
        &0 < D /\ &1 <= log D / log z
        ==> sifted A a {p | prime p /\ &p < z} <=
            X * product {p | prime p /\ &p < z} (\p. &1 - g p) *
            (sieve_F(log D / log z) +
             (K - &1) * &20000000 * sieve_h(log D / log z)) +
            sum {t | t SUBSET {p | prime p /\ &p < z} /\
                     &(nproduct t (\p. p)) <
                     D * &(nproduct {p | prime p /\ &p < w} (\p. p))}
                (\t. abs(sieve_count A a t - X * product t g))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:real`; `z:real`; `D:real`] JR_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:real`; `z:real`] SIEVE_PRIMES_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ABBREV_TAC `q = {p | prime p /\ &p < w}` THEN
  SUBGOAL_THEN `FINITE(q:num->bool) /\ ~(0 IN q) /\
                (!p. p IN q ==> &0 <= &1 - g p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[FINITE_PRIMES_LT; IN_ELIM_THM;
    PRIME_0] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `sieve_primes w z`;
                 `q:num->bool`; `D:real`; `X:real`; `g:num->real`]
         ROSSER_SIEVE_UPPER_EXTENDED) THEN
  ASM_REWRITE_TAC[FINITE_SIEVE_PRIMES; IN_SIEVE_PRIMES; PRIME_0] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a + r ==> x <= b + r`) THEN
  ASM_SIMP_TAC[PRODUCT_UNION; FINITE_SIEVE_PRIMES; GSYM sieve_V] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `!X V Q Y. X * (V * Q) * Y = X * (V * Y) * (Q:real)`]
  THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[PRODUCT_POS_LE] THEN
  MP_TAC(SPECL [`g:num->real`; `w:real`; `K:real`] ROSSER_G_UPPER_BOUND) THEN
  ASM_SIMP_TAC[]);;

let JURKAT_RICHERT_LOWER_K = prove
 (`!A a X g w K D z.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ &0 <= X /\
        &2 <= w /\ w <= z /\ &1 <= K /\ K <= &1 + &1 / &10000 /\
        (!p. prime p ==> &0 <= g p /\ g p < &1) /\
        (!u v. w <= u /\ u <= v
               ==> sieve_V g w u <= K * (log v / log u) * sieve_V g w v) /\
        &0 < D /\ &2 <= log D / log z
        ==> X * product {p | prime p /\ &p < z} (\p. &1 - g p) *
            (sieve_f(log D / log z) -
             (K - &1) * &20000000 * sieve_h(log D / log z)) -
            sum {t | t SUBSET {p | prime p /\ &p < z} /\
                     &(nproduct t (\p. p)) <
                     D * &(nproduct {p | prime p /\ &p < w} (\p. p))}
                (\t. abs(sieve_count A a t - X * product t g))
            <= sifted A a {p | prime p /\ &p < z}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`w:real`; `z:real`; `D:real`] JR_SETUP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`w:real`; `z:real`] SIEVE_PRIMES_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  ABBREV_TAC `q = {p | prime p /\ &p < w}` THEN
  SUBGOAL_THEN `FINITE(q:num->bool) /\ ~(0 IN q) /\
                (!p. p IN q ==> &0 <= &1 - g p)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN REWRITE_TAC[FINITE_PRIMES_LT; IN_ELIM_THM;
    PRIME_0] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN sieve_primes w z ==> &p < D` ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_SIEVE_PRIMES] THEN STRIP_TAC THEN
    SUBGOAL_THEN `log z < log D` ASSUME_TAC THENL
     [UNDISCH_TAC `&2 <= log D / log z` THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `z < D` MP_TAC THENL
     [MP_TAC(SPECL [`z:real`; `D:real`] LOG_MONO_LT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `sieve_primes w z`;
                 `q:num->bool`; `D:real`; `X:real`; `g:num->real`]
         ROSSER_SIEVE_LOWER_EXTENDED) THEN
  ASM_REWRITE_TAC[FINITE_SIEVE_PRIMES; IN_SIEVE_PRIMES; PRIME_0] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b - r <= x ==> a - r <= x`) THEN
  ASM_SIMP_TAC[PRODUCT_UNION; FINITE_SIEVE_PRIMES; GSYM sieve_V] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `!X V Q Y. X * (V * Q) * Y = X * (V * Y) * (Q:real)`]
  THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[PRODUCT_POS_LE] THEN
  MP_TAC(SPECL [`g:num->real`; `w:real`; `K:real`] ROSSER_G_LOWER_BOUND) THEN
  ASM_SIMP_TAC[]);;

let SIEVE_PRIMES_SPLIT_INTERVAL = prove
 (`!w u v. w <= u /\ u <= v
           ==> sieve_primes w v = sieve_primes w u UNION sieve_primes u v /\
               DISJOINT (sieve_primes w u) (sieve_primes u v)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[EXTENSION; DISJOINT; IN_UNION; IN_INTER; NOT_IN_EMPTY;
              IN_SIEVE_PRIMES] THEN
  CONJ_TAC THEN X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let SIEVE_K_FROM_DIMENSION = prove
 (`!g L w.
        &2 <= w /\ &0 <= L /\
        (!p. prime p ==> &0 <= g p /\ g p < &1) /\
        (!u v. &2 <= u /\ u <= v
               ==> inv(product (sieve_primes u v) (\p. &1 - g p)) <=
                   log v / log u * (&1 + L / log u))
        ==> !u v. w <= u /\ u <= v
                  ==> sieve_V g w u <=
                      (&1 + L / log w) * (log v / log u) * sieve_V g w v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`w:real`; `u:real`; `v:real`] SIEVE_PRIMES_SPLIT_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `P = product (sieve_primes u v) (\p. &1 - g p)` THEN
  SUBGOAL_THEN `&0 < P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
    REWRITE_TAC[FINITE_SIEVE_PRIMES; IN_SIEVE_PRIMES] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_SUB_LT] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sieve_V g w v = sieve_V g w u * P` SUBST1_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[sieve_V] THEN
    ASM_SIMP_TAC[PRODUCT_UNION; FINITE_SIEVE_PRIMES];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sieve_V g w u` ASSUME_TAC THENL
   [MATCH_MP_TAC SIEVE_V_POS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < log w /\ log w <= log u /\ log u <= log v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real`; `v:real`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `inv:real->real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN DISCH_TAC THEN
  SUBGOAL_THEN `L / log u <= L / log w` ASSUME_TAC THENL
   [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log v / log u` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `inv P <= log v / log u * (&1 + L / log w)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `log v / log u * (&1 + L / log u)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Vu = sieve_V g w u` THEN
  ABBREV_TAC `r = log v / log u * (&1 + L / log w)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(Vu * P) * inv P <= (Vu * P) * r` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; GSYM REAL_MUL_ASSOC;
               REAL_MUL_RID] THEN
  EXPAND_TAC "r" THEN REAL_ARITH_TAC);;

let JURKAT_RICHERT = prove
 (`!L e.
        &0 <= L /\ &0 < e
        ==> ?w. &2 <= w /\
                !g. (!p. prime p ==> &0 <= g p /\ g p < &1) /\
                    (!u v. &2 <= u /\ u <= v
                           ==> inv(product (sieve_primes u v)
                                           (\p. &1 - g p)) <=
                               log v / log u * (&1 + L / log u))
                    ==> !A a X D z.
                  FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ &0 <= X /\
                  w <= z /\ &0 < D
                  ==> (&1 <= log D / log z
                       ==> sifted A a {p | prime p /\ &p < z} <=
                           X * product {p | prime p /\ &p < z}
                                       (\p. &1 - g p) *
                           (sieve_F(log D / log z) + e) +
                           sum {t | t SUBSET {p | prime p /\ &p < z} /\
                                    &(nproduct t (\p. p)) <
                                    D * &(nproduct {p | prime p /\ &p < w}
                                                   (\p. p))}
                               (\t. abs(sieve_count A a t -
                                        X * product t g))) /\
                      (&2 <= log D / log z
                       ==> X * product {p | prime p /\ &p < z}
                                       (\p. &1 - g p) *
                           (sieve_f(log D / log z) - e) -
                           sum {t | t SUBSET {p | prime p /\ &p < z} /\
                                    &(nproduct t (\p. p)) <
                                    D * &(nproduct {p | prime p /\ &p < w}
                                                   (\p. p))}
                               (\t. abs(sieve_count A a t -
                                        X * product t g))
                           <= sifted A a {p | prime p /\ &p < z})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `d = min (&1 / &10000) (e / &20000000)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= &1 / &10000 /\ &20000000 * d <= e`
  STRIP_ASSUME_TAC THENL [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `max (&2) (exp(L / d))` THEN
  ABBREV_TAC `w = max (&2) (exp(L / d))` THEN
  SUBGOAL_THEN `&2 <= w /\ L / log w <= d` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 <= w /\ exp(L / d) <= w` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "w" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < log w` ASSUME_TAC THENL
     [MATCH_MP_TAC LOG_POS_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    SUBGOAL_THEN `L / d <= log w` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:num->real` THEN STRIP_TAC THEN
  ABBREV_TAC `K = &1 + L / log w` THEN
  SUBGOAL_THEN `&1 <= K /\ K <= &1 + &1 / &10000 /\
                (K - &1) * &20000000 <= e`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN
    SUBGOAL_THEN `&0 <= L / log w` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`g:num->real`; `L:real`; `w:real`] SIEVE_K_FROM_DIMENSION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= X * product {p | prime p /\ &p < z} (\p. &1 - g p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_POS_LE THEN REWRITE_TAC[FINITE_PRIMES_LT] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `prime`)) (concl th) &&
      not(can (find_term ((=) `inv:real->real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. (K - &1) * &20000000 * sieve_h s <= e` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(K - &1) * &20000000 * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[SIEVE_H_LE_1] THEN
        REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`A:num->bool`; `a:num->real`; `X:real`; `g:num->real`;
                  `w:real`; `K:real`; `D:real`; `z:real`]
           JURKAT_RICHERT_UPPER_K) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a + r ==> x <= b + r`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= e ==> f + y <= f + e`) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`A:num->bool`; `a:num->real`; `X:real`; `g:num->real`;
                  `w:real`; `K:real`; `D:real`; `z:real`]
           JURKAT_RICHERT_LOWER_K) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b - r <= x ==> a - r <= x`) THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= e ==> f - e <= f - y`) THEN
    ASM_REWRITE_TAC[]]);;
