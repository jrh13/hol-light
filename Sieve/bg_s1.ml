(* ========================================================================= *)
(* Bounded gaps between primes, part 1: colourings and the sum S1.           *)
(* (Maynard, "Small gaps between primes", Annals 181 (2015), at level of     *)
(* distribution 1/2; files bg_s1, bg_s2, bg_weights, bg_dyadic, bg_assembly, *)
(* bounded_gaps.)                                                            *)
(*                                                                           *)
(* Representation.  Maynard's divisor tuples (d_1, ..., d_k), pairwise       *)
(* coprime, squarefree and free of small primes, are COLOURINGS c : num ->   *)
(* num with finite support col_supp c = {p | ~(c p = 0)}, d_i = prod of the  *)
(* primes of colour i.  col_sub c' c (c' agrees with c on its support) is    *)
(* the divisibility order; sums over divisors become sums over               *)
(* sub-colourings.                                                           *)
(*                                                                           *)
(* * Products of sums are sums over cartesian products                       *)
(*   (PRODUCT_SUM_CARTESIAN); the average of a product of p-periodic         *)
(*   functions over a period prod t factorises (CRT_SUM_PRODUCT).            *)
(* * SIEVE_EXPAND: sum_{c'} prod_{col_supp c'} alpha * sum_{c >= c'} Y c,    *)
(*   over the c' whose primes satisfy a condition, equals                    *)
(*   sum_c Y c prod_{p IN col_supp c} (1 + alpha p [condition at p]).        *)
(* * With maynard_lfac h c p n = 1 - p if p divides n + h(c p), else 1, the  *)
(*   sieve weight of n is sum_c Y c prod_{col_supp c} maynard_lfac h c p n   *)
(*   (alpha p = -p).  S1_PAIR, S1_TOTAL: over N <= n < 2N, n == nu (mod W),  *)
(*     sum_n (sum_c Y c prod maynard_lfac)^2                                 *)
(*       = (N/W) sum_{c,c'} Y c Y c' col_corr c c' + error,                  *)
(*   col_corr c c' = [col_supp c = col_supp c'] prod (p - 1 or -1), with the *)
(*   error from incomplete periods at most 2 sum |Y c| |Y c'| 3^|U| times    *)
(*   prod_{col_supp c} (p - 1) prod_{col_supp c'} (p - 1), U = col_supp c    *)
(*   UNION col_supp c'.                                                      *)
(* * col_set k P: colours <= k, support in P.  OFFDIAG_STATES: the sum over  *)
(*   pairs c <> c' of prod_P wt(p, c p, c' p) is at most prod_P (sum of wt   *)
(*   over all states) - prod_P (sum over the diagonal states).               *)
(* * S1_MAIN_TERM: for Y c = y c / prod_{col_supp c} (p - 1), |y| <= ym,     *)
(*     sum_{c,c'} Y c Y c' col_corr c c' = sum_c y c^2 / prod (p - 1)        *)
(*   up to ym^2 (prod_P (1 + k (u + (k - 1) u^2)) - prod_P (1 + k u)),       *)
(*   u = 1/(p - 1).                                                          *)
(* ========================================================================= *)

needs "Sieve/brun_titchmarsh.ml";;
needs "Sieve/characters.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Products of sums over cartesian products; the CRT average.                *)
(* ------------------------------------------------------------------------- *)

let CARTESIAN_PRODUCT_INSERT_IMAGE = prove
 (`!a k (s:K->A->bool).
        ~(a IN k)
        ==> cartesian_product (a INSERT k) s =
            IMAGE (\(u,x). \i. if i = a then u else x i)
                  {u,x | u IN s a /\ x IN cartesian_product k s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM] THEN
  REWRITE_TAC[IN_ELIM_PAIR_THM; cartesian_product; IN_ELIM_THM;
              EXTENSIONAL; IN_INSERT] THEN
  X_GEN_TAC `y:K->A` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(y:K->A) a`;
     `\i. if i = a then ARB else (y:K->A) i`]
    THEN REWRITE_TAC[FUN_EQ_THM] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:K` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      X_GEN_TAC `i:K` THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
      X_GEN_TAC `i:K` THEN COND_CASES_TAC THEN ASM_MESON_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:A`; `x:K->A`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:K` THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[]]);;

let PRODUCT_SUM_CARTESIAN = prove
 (`!k (s:K->A->bool) (f:K->A->real).
        FINITE k /\ (!i. i IN k ==> FINITE(s i))
        ==> product k (\i. sum (s i) (f i)) =
            sum (cartesian_product k s) (\x. product k (\i. f i (x i)))`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN SPEC_TAC(`k:K->bool`,`k:K->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[PRODUCT_CLAUSES; CARTESIAN_PRODUCT_EMPTY; SUM_SING];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:K`; `k:K->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; CARTESIAN_PRODUCT_INSERT_IMAGE] THEN
  SUBGOAL_THEN `FINITE(cartesian_product k (s:K->A->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_CARTESIAN_PRODUCT] THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `k:K->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:A`; `x:K->A`; `v:A`; `z:K->A`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[];
      MATCH_MP_TAC CARTESIAN_PRODUCT_EQ_MEMBERS THEN
      MAP_EVERY EXISTS_TAC [`k:K->bool`; `s:K->A->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
      COND_CASES_TAC THEN ASM_MESON_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  REWRITE_TAC[GSYM SUM_RMUL] THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MP_TAC(ISPECL
   [`(s:K->A->bool) a`; `\u:A. cartesian_product k (s:K->A->bool)`;
    `\u:A x:K->A. (f:K->A->real) a u * product k (\i. f i (x i))`]
   SUM_SUM_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A`; `x:K->A`] THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[]);;
let CRT_SUM_PRODUCT = prove
 (`!t (f:num->num->real).
        FINITE t /\ (!p. p IN t ==> prime p)
        ==> sum {c | c < nproduct t (\p. p)}
                (\c. product t (\p. f p (c MOD p)))
            = product t (\p. sum {r | r < p} (f p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN t ==> ~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  ABBREV_TAC `Q = nproduct t (\p:num. p)` THEN
  ABBREV_TAC `Cp = cartesian_product t (\p:num. {r:num | r < p})` THEN
  SUBGOAL_THEN `FINITE(Cp:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Cp" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum {c | c < Q}
        (\c. sum Cp (\x. product t (\p. if x p = c MOD p then f p (x p)
                                       else &0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN EXPAND_TAC "Cp" THEN
    MP_TAC(ISPECL
     [`t:num->bool`; `\p:num. {r:num | r < p}`;
      `\p:num r:num. if r = c MOD p then (f:num->num->real) p r else &0`]
     PRODUCT_SUM_CARTESIAN) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {r | r < p}
                    (\r. if r = c MOD p then (f:num->num->real) p (c MOD p)
                          else &0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN ASM_SIMP_TAC[MOD_LT_EQ];
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\c x. product t (\p. if (x:num->num) p = c MOD p
                           then (f:num->num->real) p (x p) else &0)`;
    `{c:num | c < Q}`; `Cp:(num->num)->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "Cp" THEN
  ASM_SIMP_TAC[PRODUCT_SUM_CARTESIAN; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num->num` THEN
  REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {c | c < Q}
                  (\c. if !p. p IN t ==> c MOD p = (x:num->num) p
                       then product t (\p. (f:num->num->real) p (x p))
                       else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[];
      FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
        REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
      ASM_SIMP_TAC[PRODUCT_EQ_0] THEN EXISTS_TAC `q:num` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((x:num->num) q = c MOD q)` (fun th -> REWRITE_TAC[th])
      THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[REAL_OF_NUM_EQ; IN_ELIM_THM] THEN
  MP_TAC(SPECL [`\p:num r:num. r = (x:num->num) p`; `t:num->bool`]
    CRT_CARD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NPRODUCT_EQ_1 THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `{r | r < p /\ r = (x:num->num) p} = {x p}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `r:num` THEN
    EQ_TAC THENL [SIMP_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[] THEN UNDISCH_TAC `(x:num->num) IN Cp` THEN
      EXPAND_TAC "Cp" THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[CARD_SING]]);;

(* ------------------------------------------------------------------------- *)
(* Colourings, sub-colourings and the sieve expansion.                       *)
(* ------------------------------------------------------------------------- *)

let col_supp = new_definition
 `col_supp (c:num->num) = {p | ~(c p = 0)}`;;

let col_sub = new_definition
 `col_sub (c':num->num) c <=> !p. ~(c' p = 0) ==> c' p = c p`;;

let col_restrict = new_definition
 `col_restrict t (c:num->num) = \p. if p IN t then c p else 0`;;

let COL_SUB_RESTRICT = prove
 (`!c c'. col_sub c' c <=> c' = col_restrict (col_supp c') c`,
  REWRITE_TAC[col_sub; col_restrict; col_supp; IN_ELIM_THM; FUN_EQ_THM] THEN
  MESON_TAC[]);;

let COL_SUPP_RESTRICT = prove
 (`!t c. t SUBSET col_supp c ==> col_supp(col_restrict t c) = t`,
  REWRITE_TAC[col_supp; col_restrict; SUBSET; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let SUBCOLOURINGS = prove
 (`!c. {c' | col_sub c' c} =
       IMAGE (\t. col_restrict t c) {t | t SUBSET col_supp c}`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `c':num->num` THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `col_supp c'` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[COL_SUB_RESTRICT]; ALL_TAC] THEN
    UNDISCH_TAC `col_sub c' c` THEN
    REWRITE_TAC[col_sub; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:num->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[col_sub; col_restrict] THEN MESON_TAC[]]);;

let FINITE_SUBCOLOURINGS = prove
 (`!c. FINITE(col_supp c) ==> FINITE {c' | col_sub c' c}`,
  SIMP_TAC[SUBCOLOURINGS; FINITE_IMAGE; FINITE_POWERSET]);;

let SUM_SUBCOLOURINGS = prove
 (`!c (g:(num->num)->real).
        FINITE(col_supp c)
        ==> sum {c' | col_sub c' c} g =
            sum {t | t SUBSET col_supp c} (\t. g(col_restrict t c))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBCOLOURINGS] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[COL_SUPP_RESTRICT];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let COLOUR_EXPAND = prove
 (`!c (alpha:num->real) (P:num->num->bool).
        FINITE(col_supp c)
        ==> sum {c' | col_sub c' c /\ !p. p IN col_supp c' ==> P p (c' p)}
                (\c'. product (col_supp c') alpha) =
            product (col_supp c)
              (\p. &1 + (if P p (c p) then alpha p else &0))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `{x:num->num | P x /\ Q x} = {x | x IN {y | P y} /\ Q x}`]
  THEN REWRITE_TAC[SUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SUM_SUBCOLOURINGS; PRODUCT_ADD_EXPAND] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[COL_SUPP_RESTRICT] THEN
  SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN t ==> col_restrict t c p = (c:num->num) p`
   (fun th -> SIMP_TAC[th]) THENL [SIMP_TAC[col_restrict]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[];
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[PRODUCT_EQ_0] THEN
    EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[]]);;
let FINITE_DOWN_COLOURINGS = prove
 (`!fam. FINITE fam /\ (!c. c IN fam ==> FINITE(col_supp c))
         ==> FINITE {c' | ?c. c IN fam /\ col_sub c' c}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{c' | ?c. c IN fam /\ col_sub c' c} =
                UNIONS (IMAGE (\c. {c' | col_sub c' c}) fam)` SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[FINITE_SUBCOLOURINGS]);;

let SIEVE_EXPAND = prove
 (`!fam (Y:(num->num)->real) (alpha:num->real) (P:num->num->bool).
        FINITE fam /\ (!c. c IN fam ==> FINITE(col_supp c))
        ==> sum {c' | (?c. c IN fam /\ col_sub c' c) /\
                      !p. p IN col_supp c' ==> P p (c' p)}
                (\c'. product (col_supp c') alpha *
                      sum {c | c IN fam /\ col_sub c' c} Y) =
            sum fam (\c. Y c *
                         product (col_supp c)
                           (\p. &1 + (if P p (c p) then alpha p else &0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MP_TAC(ISPECL
   [`\c':num->num c:num->num. col_sub c' c`;
    `\c':num->num c:num->num. product (col_supp c') (alpha:num->real) *
                              (Y:(num->num)->real) c`;
    `{c' | (?c. c IN fam /\ col_sub c' c) /\
           !p. p IN col_supp c' ==> (P:num->num->bool) p (c' p)}`;
    `fam:(num->num)->bool`] SUM_SUM_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{c' | ?c. c IN fam /\ col_sub c' c}` THEN
    ASM_SIMP_TAC[FINITE_DOWN_COLOURINGS] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM COLOUR_EXPAND] THEN
  REWRITE_TAC[SUM_RMUL] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:num->num` THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `c:num->num` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Periodic sums over arithmetic progressions; residue sums.                 *)
(* ------------------------------------------------------------------------- *)

let AP_INTERVAL_COUNT = prove
 (`!q a N. 1 <= q
           ==> abs(&(CARD {n | N <= n /\ n < 2 * N /\ (n == a) (mod q)}) -
                   &N / &q) <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `N = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; LT; EMPTY_GSPEC] THEN
    REWRITE_TAC[CARD_CLAUSES; real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`2 * N - 1`; `q:num`; `a:num`; `1`] AP_MULTIPLES_COUNT) THEN
  MP_TAC(SPECL [`N - 1`; `q:num`; `a:num`; `1`] AP_MULTIPLES_COUNT) THEN
  ASM_REWRITE_TAC[COPRIME_1; LE_REFL; DIVIDES_1; REAL_MUL_RID] THEN
  SUBGOAL_THEN
   `{n | N <= n /\ n < 2 * N /\ (n == a) (mod q)} =
    {n | n IN 1..2 * N - 1 /\ (n == a) (mod q)} DIFF
    {n | n IN 1..N - 1 /\ (n == a) (mod q)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN ASM_CASES_TAC `(n:num == a) (mod q)` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD({n | n IN 1..2 * N - 1 /\ (n == a) (mod q)} DIFF
         {n | n IN 1..N - 1 /\ (n == a) (mod q)}) =
    CARD {n | n IN 1..2 * N - 1 /\ (n == a) (mod q)} -
    CARD {n | n IN 1..N - 1 /\ (n == a) (mod q)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_DIFF THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {n | n IN 1..N - 1 /\ (n == a) (mod q)} <=
    CARD {n | n IN 1..2 * N - 1 /\ (n == a) (mod q)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN GEN_TAC THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB] THEN
  SUBGOAL_THEN `&(2 * N - 1) = &2 * &N - &1 /\ &(N - 1) = &N - &1`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL] THEN CONJ_TAC THEN
    MATCH_MP_TAC(GSYM REAL_OF_NUM_SUB) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `A = &(CARD {n | n IN 1..2 * N - 1 /\ (n == a) (mod q)})` THEN
  ABBREV_TAC `B = &(CARD {n | n IN 1..N - 1 /\ (n == a) (mod q)})` THEN
  SUBGOAL_THEN `(&2 * &N - &1) / &q - (&N - &1) / &q = &N / &q`
  MP_TAC THENL
   [UNDISCH_TAC `&0 < &q` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  REAL_ARITH_TAC);;
let PERIODIC_SUM_AP = prove
 (`!(f:num->real) Q W nu N.
        1 <= Q /\ 1 <= W /\ coprime(Q,W) /\ (!n. f n = f(n MOD Q))
        ==> abs(sum {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)} f -
                &N / (&W * &Q) * sum {c | c < Q} f)
            <= &2 * sum {c | c < Q} (\c. abs(f c))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}` THEN
  SUBGOAL_THEN `FINITE(A:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n:num | n < 2 * N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. n MOD Q`; `f:num->real`; `A:num->bool`;
                 `{c:num | c < Q}`] SUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC;
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_SUB_NUMSEG] THEN
  SIMP_TAC[GSYM SUM_SUB; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {c | c < Q} (\c. abs((f:num->real) c) * &2)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {c | c < Q}
                  (\c. abs(sum {x | x IN A /\ x MOD Q = c} f -
                           &N / (&W * &Q) * (f:num->real) c))` THEN
  SIMP_TAC[SUM_ABS; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
  X_GEN_TAC `c:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `sum {x | x IN A /\ x MOD Q = c} (f:num->real) =
                f c * &(CARD {x | x IN A /\ x MOD Q = c})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {x | x IN A /\ x MOD Q = c} (\x. (f:num->real) c)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      SIMP_TAC[SUM_CONST; FINITE_RESTRICT; ASSUME `FINITE(A:num->bool)`] THEN
      MATCH_ACCEPT_TAC REAL_MUL_SYM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`nu:num`; `c:num`; `W:num`; `Q:num`] CONG_CRT_STRONG) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `gcd(W,Q) = 1` SUBST1_TAC THENL
     [ASM_MESON_TAC[COPRIME_SYM; COPRIME_GCD]; REWRITE_TAC[CONG_MOD_1]];
    DISCH_THEN(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `{x | x IN A /\ x MOD Q = c} =
                {n | N <= n /\ n < 2 * N /\ (n == x) (mod (W * Q))}`
  SUBST1_TAC THENL
   [EXPAND_TAC "A" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN
    SUBGOAL_THEN `n MOD Q = c <=> (n == c) (mod Q)` SUBST1_TAC THENL
     [REWRITE_TAC[CONG] THEN ASM_SIMP_TAC[MOD_LT]; ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `x:num`; `nu:num`; `c:num`; `W:num`; `Q:num`]
     (NUMBER_RULE
       `!n x nu c W Q:num.
          coprime(Q,W) /\ (x == nu) (mod W) /\ (x == c) (mod Q)
          ==> ((n == nu) (mod W) /\ (n == c) (mod Q) <=>
               (n == x) (mod (W * Q)))`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC(SPECL [`W * Q:num`; `x:num`; `N:num`] AP_INTERVAL_COUNT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ABBREV_TAC `C0 = &(CARD {n | N <= n /\ n < 2 * N /\ (n == x) (mod (W * Q))})`
  THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_ARITH `a * c0 - u * a = a * (c0 - u:real)`] THEN
  REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;
let RESIDUES_DIVIDING = prove
 (`!p i. ~(p = 0) ==> {r | r < p /\ p divides r + i} = {(p - i MOD p) MOD p}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN
  X_GEN_TAC `r:num` THEN
  MP_TAC(SPECL [`p:num`; `i:num`; `r:num`] DIVIDES_ADDH_CONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CONG] THEN EQ_TAC THENL
   [STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MOD_LT];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[MOD_LT_EQ; MOD_MOD_REFL]]);;

let SUM_RESIDUES_ONE = prove
 (`!p i a b. ~(p = 0)
             ==> sum {r | r < p} (\r. if p divides r + i then a else b) =
                 a + (&p - &1) * b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{r | r < p} = {r | r < p /\ p divides r + i} UNION
                  {r | r < p /\ ~(p divides r + i)}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < p}`;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < p}`;
      ALL_TAC] THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `sum {r | r < p /\ p divides r + i} (\r. if p divides r + i then a else b) =
    sum {r | r < p /\ p divides r + i} (\r. a) /\
    sum {r | r < p /\ ~(p divides r + i)}
        (\r. if p divides r + i then a else b) =
    sum {r | r < p /\ ~(p divides r + i)} (\r. b)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {r | r < p /\ ~(p divides r + i)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{r:num | r < p}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; RESIDUES_DIVIDING; FINITE_SING; CARD_SING] THEN
  SUBGOAL_THEN `CARD {r | r < p /\ ~(p divides r + i)} = p - 1`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `{r | r < p /\ ~(p divides r + i)} =
                  {r | r < p} DIFF {r | r < p /\ p divides r + i}`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_DIFF o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_SIMP_TAC[RESIDUES_DIVIDING; CARD_NUMSEG_LT; CARD_SING];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `~(p = 0) ==> 1 <= p`] THEN
  REAL_ARITH_TAC);;
let SUM_RESIDUES_SINGLE = prove
 (`!p i. ~(p = 0)
         ==> sum {r | r < p} (\r. if p divides r + i then &1 - &p else &1) =
             &0`,
  SIMP_TAC[SUM_RESIDUES_ONE] THEN REAL_ARITH_TAC);;

let SUM_RESIDUES_PAIR_GEN = prove
 (`!p i j a b.
        ~(p = 0) /\ (~(i = j) ==> ~((i == j) (mod p)))
        ==> sum {r | r < p}
                (\r. (if p divides r + i then a else &1) *
                     (if p divides r + j then b else &1)) =
            (if i = j then a * b + &p - &1 else a + b + &p - &2)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[MESON[]
     `(if c then x else y) * (if c then z else y) =
      (if c then x * z else y * y:real)`] THEN
    ASM_SIMP_TAC[SUM_RESIDUES_ONE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {r | r < p}
                  (\r. &1 + (if p divides r + i then a - &1 else &0) +
                       (if p divides r + j then b - &1 else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_CASES_TAC `(p:num) divides r + i` THEN
    ASM_CASES_TAC `(p:num) divides r + j` THEN
    ASM_REWRITE_TAC[] THEN TRY REAL_ARITH_TAC THEN
    MATCH_MP_TAC(TAUT `F ==> x`) THEN
    UNDISCH_TAC `~((i:num == j) (mod p))` THEN
    MAP_EVERY UNDISCH_TAC [`(p:num) divides r + i`; `(p:num) divides r + j`]
    THEN CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[SUM_RESIDUES_ONE; SUM_CONST; FINITE_NUMSEG_LT;
               CARD_NUMSEG_LT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local factors; S1 up to the incomplete periods.                           *)
(* ------------------------------------------------------------------------- *)

let maynard_lfac = new_definition
 `maynard_lfac (h:num->num) (c:num->num) p n =
    if p IN col_supp c /\ p divides n + h(c p) then &1 - &p else &1`;;

let col_corr = new_definition
 `col_corr (c:num->num) c' =
    if col_supp c = col_supp c'
    then product (col_supp c) (\p. if c p = c' p then &p - &1 else --(&1))
    else &0`;;

let MAYNARD_LFAC_MOD = prove
 (`!h c p n. ~(p = 0) ==> maynard_lfac h c p n = maynard_lfac h c p (n MOD p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[maynard_lfac] THEN
  SUBGOAL_THEN `!x. p divides n + x <=> p divides n MOD p + x`
   (fun th -> REWRITE_TAC[th]) THEN
  GEN_TAC THEN MP_TAC(SPECL [`n:num`; `p:num`] DIVISION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
    [CONJUNCT1 th]) THEN
  SPEC_TAC(`n MOD p`,`m:num`) THEN SPEC_TAC(`n DIV p`,`q:num`) THEN
  CONV_TAC NUMBER_RULE);;
let LOCAL_SUM_MAYNARD_LFAC = prove
 (`!h c c' p.
        prime p /\
        (p IN col_supp c /\ p IN col_supp c' /\ ~(c p = c' p)
         ==> ~((h(c p) == h(c' p)) (mod p)))
        ==> sum {r | r < p}
              (\r. maynard_lfac h c p r * maynard_lfac h c' p r) =
            (if p IN col_supp c /\ p IN col_supp c'
             then (if c p = c' p then &p * (&p - &1) else --(&p))
             else if p IN col_supp c \/ p IN col_supp c' then &0 else &p)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  REWRITE_TAC[maynard_lfac] THEN
  ASM_CASES_TAC `(p:num) IN col_supp c` THEN
  ASM_CASES_TAC `(p:num) IN col_supp c'` THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THENL
   [MP_TAC(SPECL [`p:num`; `(h:num->num)((c:num->num) p)`;
    `(h:num->num)((c':num->num) p)`;
                  `&1 - &p`; `&1 - &p`] SUM_RESIDUES_PAIR_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    ASM_CASES_TAC `(c:num->num) p = c' p` THEN ASM_REWRITE_TAC[] THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((h:num->num)((c:num->num) p) = h((c':num->num) p))`
    (fun th -> REWRITE_TAC[th])
    THENL
     [DISCH_TAC THEN UNDISCH_TAC
       `p IN col_supp c /\ p IN col_supp c' /\ ~((c:num->num) p = c' p)
        ==> ~(((h:num->num) (c p) == h (c' p)) (mod p))` THEN
      ASM_REWRITE_TAC[CONG_REFL];
      REAL_ARITH_TAC];
    ASM_SIMP_TAC[SUM_RESIDUES_SINGLE];
    REWRITE_TAC[REAL_MUL_LID] THEN ASM_SIMP_TAC[SUM_RESIDUES_SINGLE];
    REWRITE_TAC[REAL_MUL_LID; SUM_CONST_NUMSEG] THEN
    SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_MUL_RID]]);;

let LOCAL_ABS_SUM_MAYNARD_LFAC = prove
 (`!h c c' p.
        prime p /\ (p IN col_supp c \/ p IN col_supp c') /\
        (p IN col_supp c /\ p IN col_supp c' /\ ~(c p = c' p)
         ==> ~((h(c p) == h(c' p)) (mod p)))
        ==> sum {r | r < p}
              (\r. abs(maynard_lfac h c p r * maynard_lfac h c' p r)) <=
            &3 * (if p IN col_supp c then &p - &1 else &1) *
                 (if p IN col_supp c' then &p - &1 else &1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  SUBGOAL_THEN `&2 <= &p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e r. abs(maynard_lfac h e p r) =
          (if p IN col_supp e /\ p divides r + h(e p) then &p - &1 else &1)`
  (fun th -> REWRITE_TAC[REAL_ABS_MUL; th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[maynard_lfac] THEN COND_CASES_TAC THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `(p:num) IN col_supp c` THEN
  ASM_CASES_TAC `(p:num) IN col_supp c'` THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THENL
   [MP_TAC(SPECL [`p:num`; `(h:num->num)((c:num->num) p)`;
    `(h:num->num)((c':num->num) p)`;
                  `&p - &1`; `&p - &1`] SUM_RESIDUES_PAIR_GEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `&0 <= (&p - &2) * (&p - &2)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SUM_RESIDUES_ONE] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_MUL_LID] THEN ASM_SIMP_TAC[SUM_RESIDUES_ONE] THEN
    ASM_REAL_ARITH_TAC;
    ASM_MESON_TAC[]]);;
let S1_PAIR = prove
 (`!h W nu N c c'.
     1 <= W /\ FINITE(col_supp c) /\ FINITE(col_supp c') /\
     (!p. p IN col_supp c UNION col_supp c' ==> prime p /\ ~(p divides W)) /\
     (!p. p IN col_supp c /\ p IN col_supp c' /\ ~(c p = c' p)
          ==> ~((h(c p) == h(c' p)) (mod p)))
     ==> abs(sum {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}
                 (\n. product (col_supp c) (\p. maynard_lfac h c p n) *
                      product (col_supp c') (\p. maynard_lfac h c' p n)) -
             &N / &W * col_corr c c')
         <= &2 * &3 pow CARD(col_supp c UNION col_supp c') *
            product (col_supp c) (\p. &p - &1) *
            product (col_supp c') (\p. &p - &1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `U = col_supp c UNION col_supp c'` THEN
  SUBGOAL_THEN `FINITE(U:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN ASM_REWRITE_TAC[FINITE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN U ==> prime p /\ ~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `col_supp c SUBSET U /\ col_supp c' SUBSET U` STRIP_ASSUME_TAC
  THENL [EXPAND_TAC "U" THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `Q = nproduct U (\p:num. p)` THEN
  SUBGOAL_THEN `1 <= Q /\ coprime(Q,W)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`] THEN
      MATCH_MP_TAC NPRODUCT_POS_LT THEN ASM_SIMP_TAC[LT_NZ];
      ASM_SIMP_TAC[COPRIME_NPRODUCT_EQ] THEN
      ASM_MESON_TAC[PRIME_COPRIME_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. product (col_supp c) (\p. maynard_lfac h c p n) *
        product (col_supp c') (\p. maynard_lfac h c' p n) =
        product U
          (\p. maynard_lfac h c p (n MOD p) * maynard_lfac h c' p (n MOD p))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `product (col_supp c) (\p. maynard_lfac h c p n) =
      product U (\p. maynard_lfac h c p n) /\
      product (col_supp c') (\p. maynard_lfac h c' p n) =
      product U (\p. maynard_lfac h c' p n)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN
      ASM_REWRITE_TAC[maynard_lfac] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    BINOP_TAC THEN MATCH_MP_TAC MAYNARD_LFAC_MOD THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Fp = \p r. maynard_lfac h c p r * maynard_lfac h c' p r` THEN
  SUBGOAL_THEN `!n. product U (\p. maynard_lfac h c p (n MOD p) *
                                   maynard_lfac h c' p (n MOD p))
                    = product U (\p. (Fp:num->num->real) p (n MOD p))`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Fp" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. product U (\p. (Fp:num->num->real) p (n MOD p))`;
                 `Q:num`; `W:num`; `nu:num`; `N:num`] PERIODIC_SUM_AP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN EXPAND_TAC "Q" THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC NPRODUCT_PRIMES_MOD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!p. p IN U ==> prime p` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {c | c < Q} (\c. abs(product U (\p. (Fp:num->num->real) p (c MOD p))))
    = product U (\p. sum {r | r < p} (\r. abs(Fp p r)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {c | c < Q}
                  (\c. product U (\p. abs((Fp:num->num->real) p (c MOD p))))`
    THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[PRODUCT_ABS];
      EXPAND_TAC "Q" THEN
      MP_TAC(ISPECL [`U:num->bool`; `\p r. abs((Fp:num->num->real) p r)`]
        CRT_SUM_PRODUCT) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {c | c < Q} (\c. product U (\p. (Fp:num->num->real) p (c MOD p)))
    = product U (\p. sum {r | r < p} (Fp p))`
  SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN
    MP_TAC(ISPECL [`U:num->bool`; `Fp:num->num->real`] CRT_SUM_PRODUCT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&N / (&W * &Q) * product U (\p. sum {r | r < p} ((Fp:num->num->real) p)) =
    &N / &W * col_corr c c'`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `product U (\p. sum {r | r < p} ((Fp:num->num->real) p)) =
      product U (\p. if p IN col_supp c /\ p IN col_supp c'
                     then (if (c:num->num) p = c' p then &p * (&p - &1)
                           else --(&p))
                     else if p IN col_supp c \/
                     p IN col_supp c' then &0 else &p)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      EXPAND_TAC "Fp" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCAL_SUM_MAYNARD_LFAC THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[col_corr] THEN COND_CASES_TAC THENL
     [SUBGOAL_THEN `U = col_supp c` SUBST_ALL_TAC THENL
       [EXPAND_TAC "U" THEN
        REWRITE_TAC[ASSUME `col_supp c = col_supp c'`; UNION_IDEMPOT];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `product (col_supp c)
         (\p. if p IN col_supp c /\ p IN col_supp c'
              then (if (c:num->num) p = c' p then &p * (&p - &1)
                    else --(&p))
              else if p IN col_supp c \/ p IN col_supp c' then &0 else &p) =
        product (col_supp c) (\p. &p) *
        product (col_supp c) (\p. if (c:num->num) p = c' p then &p - &1
                               else --(&1))`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM PRODUCT_MUL] THEN MATCH_MP_TAC PRODUCT_EQ THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(p:num) IN col_supp c'` (fun th -> ASM_REWRITE_TAC[th])
        THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        COND_CASES_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `product (col_supp c) (\p. &p) = &Q` SUBST1_TAC THENL
       [EXPAND_TAC "Q" THEN
        SIMP_TAC[REAL_OF_NUM_NPRODUCT; ASSUME `FINITE(col_supp c)`] THEN
        REWRITE_TAC[ETA_AX];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 <= &Q /\ &1 <= &W` MP_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RZERO] THEN
    MATCH_MP_TAC(MESON[REAL_MUL_RZERO] `x = &0 ==> a * x = &0:real`) THEN
    ASM_SIMP_TAC[PRODUCT_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [EXTENSION] o
      check (is_neg o concl)) THEN
    REWRITE_TAC[NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN EXISTS_TAC `p:num` THEN
    EXPAND_TAC "U" THEN REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product U (\p. sum {r | r < p} (\r. abs((Fp:num->num->real) p r))) <=
    &3 pow CARD(U:num->bool) * product (col_supp c) (\p. &p - &1) *
    product (col_supp c') (\p. &p - &1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `product U (\p. &3 * (if p IN col_supp c then &p - &1 else &1) *
                         (if p IN col_supp c' then &p - &1 else &1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_POS_LE THEN
        REWRITE_TAC[FINITE_NUMSEG_LT; REAL_ABS_POS];
        EXPAND_TAC "Fp" THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC LOCAL_ABS_SUM_MAYNARD_LFAC THEN ASM_SIMP_TAC[] THEN
        UNDISCH_TAC `(p:num) IN U` THEN EXPAND_TAC "U" THEN
        REWRITE_TAC[IN_UNION]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_MUL; PRODUCT_CONST] THEN
    SUBGOAL_THEN
     `!s. s SUBSET U
          ==> product U (\p. if p IN s then &p - &1 else &1) =
              product s (\p. &p - &1)`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `product s (\p. if p IN s then &p - &1 else &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PRODUCT_SUPERSET THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[REAL_MUL_ASSOC; REAL_LE_REFL];
    ALL_TAC] THEN
  ABBREV_TAC `S0 = sum {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}
                       (\n. product U (\p. (Fp:num->num->real) p (n MOD p)))`
  THEN
  ABBREV_TAC `E0 = product U (\p. sum {r | r < p}
                                       (\r. abs((Fp:num->num->real) p r)))`
  THEN
  ABBREV_TAC `B0 = &3 pow CARD(U:num->bool) *
                   product (col_supp c) (\p. &p - &1) *
                   product (col_supp c') (\p. &p - &1)` THEN
  REAL_ARITH_TAC);;
let SUM_SQUARE_SWAP = prove
 (`!s t (a:A->B->real).
        FINITE s /\ FINITE t
        ==> sum s (\n. sum t (\c. a n c) pow 2) =
            sum t (\c. sum t (\d. sum s (\n. a n c * a n d)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_SIMP_TAC[REAL_MUL_SUM] THEN
  MP_TAC(ISPECL [`\n:A c:B. sum t (\d:B. (a:A->B->real) n c * a n d)`;
                 `s:A->bool`; `t:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:B` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\n:A d:B. (a:A->B->real) n c * a n d`;
                 `s:A->bool`; `t:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[]);;
let S1_TOTAL = prove
 (`!h W nu N fam (Y:(num->num)->real).
     1 <= W /\ FINITE fam /\
     (!c. c IN fam
          ==> FINITE(col_supp c) /\
              !p. p IN col_supp c ==> prime p /\ ~(p divides W)) /\
     (!c c' p. c IN fam /\ c' IN fam /\
               p IN col_supp c /\ p IN col_supp c' /\ ~(c p = c' p)
               ==> ~((h(c p) == h(c' p)) (mod p)))
     ==> abs(sum {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}
                 (\n. sum fam (\c. Y c * product (col_supp c)
                                           (\p. maynard_lfac h c p n)) pow 2) -
             &N / &W * sum fam (\c. sum fam (\c'. Y c * Y c' *
                                                  col_corr c c')))
         <= &2 * sum fam (\c. sum fam (\c'.
                abs(Y c) * abs(Y c') *
                &3 pow CARD(col_supp c UNION col_supp c') *
                product (col_supp c) (\p. &p - &1) *
                product (col_supp c') (\p. &p - &1)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `A = {n | N <= n /\ n < 2 * N /\ (n == nu) (mod W)}` THEN
  SUBGOAL_THEN `FINITE(A:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{n:num | n < 2 * N}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `fam:(num->num)->bool`;
                 `\n c. (Y:(num->num)->real) c *
                        product (col_supp c) (\p. maynard_lfac h c p n)`]
         SUM_SQUARE_SWAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM SUM_LMUL; GSYM SUM_RMUL] THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum fam (\c. abs(sum fam (\c'.
       sum A (\n. (Y c * product (col_supp c) (\p. maynard_lfac h c p n)) *
                  (Y c' * product (col_supp c') (\p. maynard_lfac h c' p n))) -
       &N / &W * (Y c * Y c' * col_corr c c'))))` THEN
  ASM_SIMP_TAC[SUM_ABS] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum fam (\c'. abs(
       sum A (\n. (Y c * product (col_supp c) (\p. maynard_lfac h c p n)) *
                  (Y c' * product (col_supp c') (\p. maynard_lfac h c' p n))) -
       &N / &W * (Y c * Y c' * col_corr c c')))` THEN
  ASM_SIMP_TAC[SUM_ABS] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c':num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `sum A (\n. ((Y:(num->num)->real) c * product (col_supp c)
                                           (\p. maynard_lfac h c p n)) *
               (Y c' * product (col_supp c') (\p. maynard_lfac h c' p n))) =
    Y c * Y c' *
    sum A (\n. product (col_supp c) (\p. maynard_lfac h c p n) *
               product (col_supp c') (\p. maynard_lfac h c' p n))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`h:num->num`; `W:num`; `nu:num`; `N:num`;
                `c:num->num`; `c':num->num`] S1_PAIR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_UNION] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = sum A (\n. product (col_supp c) (\p. maynard_lfac h c p n) *
                             product (col_supp c')
                               (\p. maynard_lfac h c' p n))` THEN
  ABBREV_TAC `B = &3 pow CARD(col_supp c UNION col_supp c') *
                  product (col_supp c) (\p. &p - &1) *
                  product (col_supp c') (\p. &p - &1)` THEN
  ABBREV_TAC `L = col_corr c c'` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `abs((Y:(num->num)->real) c) * abs(Y c') * abs(S - &N / &W * L)
                <= abs(Y c) * abs(Y c') * (&2 * B)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
  ABBREV_TAC `y1 = (Y:(num->num)->real) c` THEN
    ABBREV_TAC `y2 = (Y:(num->num)->real) c'` THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL [AP_TERM_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  EXPAND_TAC "B" THEN REWRITE_TAC[REAL_ABS_MUL] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Colourings with k colours; the off-diagonal bound.                        *)
(* ------------------------------------------------------------------------- *)

let SUM_NUMSEG_DELTA_ELSE = prove
 (`!k a u v. a IN 1..k
             ==> sum (1..k) (\b. if a = b then u else v) = u + (&k - &1) * v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!b:num. (if (a:num) = b then u else v) = (if b = a then u - v else &0) + v`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN ASM_CASES_TAC `b:num = a` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[SUM_ADD_NUMSEG; SUM_DELTA; SUM_CONST_NUMSEG] THEN
  ASM_REWRITE_TAC[ADD_SUB] THEN
  UNDISCH_TAC `a IN 1..k` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; ARITH_RULE `1 <= a /\ a <= k ==> 1 <= k`]
  THEN REAL_ARITH_TAC);;

let col_set = new_definition
 `col_set k P = {c:num->num | !p. (p IN P ==> c p <= k) /\
                                 (~(p IN P) ==> c p = 0)}`;;

let COL_SET_AS_IMAGE = prove
 (`!k P. col_set k P =
         IMAGE (\x p. if p IN P then x p else 0)
               (cartesian_product P (\p:num. 0..k))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; col_set; IN_ELIM_THM; IN_IMAGE; IN_CARTESIAN_PRODUCT;
              IN_NUMSEG; LE_0] THEN
  X_GEN_TAC `c:num->num` THEN EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `RESTRICTION P (c:num->num)` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; RESTRICTION] THEN X_GEN_TAC `p:num` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      REWRITE_TAC[REWRITE_RULE[IN] RESTRICTION_IN_EXTENSIONAL];
      ASM_MESON_TAC[RESTRICTION]];
    DISCH_THEN(X_CHOOSE_THEN `x:num->num` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

let FINITE_COL_SET = prove
 (`!k P. FINITE P ==> FINITE(col_set k P)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COL_SET_AS_IMAGE] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG]);;

let COL_SET_SUM_PRODUCT = prove
 (`!k P (f:num->num->real).
        FINITE P
        ==> sum (col_set k P) (\c. product P (\p. f p (c p))) =
            product P (\p. sum (0..k) (f p))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COL_SET_AS_IMAGE] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_CARTESIAN_PRODUCT; FUN_EQ_THM; EXTENSIONAL; IN_ELIM_THM]
    THEN MAP_EVERY X_GEN_TAC [`x:num->num`; `y:num->num`] THEN
    STRIP_TAC THEN X_GEN_TAC `p:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN
    ASM_CASES_TAC `(p:num) IN P` THEN ASM_SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[PRODUCT_SUM_CARTESIAN; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[]);;

let COL_SET_SUM_PRODUCT2 = prove
 (`!k P (f:num->num->num->real).
        FINITE P
        ==> sum (col_set k P) (\c. sum (col_set k P) (\c'.
                product P (\p. f p (c p) (c' p)))) =
            product P (\p. sum (0..k) (\i. sum (0..k) (\j. f p i j)))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (col_set k P)
                  (\c. product P (\p. sum (0..k) (\j. f p (c p) j)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k:num`; `P:num->bool`;
                   `\p j. (f:num->num->num->real) p (c p) j`]
           COL_SET_SUM_PRODUCT) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`k:num`; `P:num->bool`;
                   `\p i. sum (0..k) (\j. (f:num->num->num->real) p i j)`]
           COL_SET_SUM_PRODUCT) THEN
    ASM_REWRITE_TAC[]]);;

let OFFDIAG_STATES = prove
 (`!k P fam (wt:num->num->num->real).
        FINITE P /\ fam SUBSET col_set k P /\
        (!p i j. p IN P ==> &0 <= wt p i j)
        ==> sum fam (\c. sum (fam DELETE c) (\c'.
                product P (\p. wt p (c p) (c' p))))
            <= product P (\p. sum (0..k) (\i. sum (0..k) (\j. wt p i j))) -
               product P (\p. sum (0..k) (\i. wt p i i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(col_set k P)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`; `wt:num->num->num->real`]
         COL_SET_SUM_PRODUCT2) THEN
  MP_TAC(ISPECL [`k:num`; `P:num->bool`;
                 `\p i. (wt:num->num->num->real) p i i`]
         COL_SET_SUM_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  ASM_SIMP_TAC[GSYM SUM_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (col_set k P) (\c. sum (col_set k P DELETE c) (\c'.
                product P (\p. (wt:num->num->num->real) p (c p) (c' p))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum fam (\c. sum (col_set k P DELETE c) (\c'.
                product P (\p. (wt:num->num->num->real) p (c p) (c' p))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_SIMP_TAC[FINITE_DELETE; PRODUCT_POS_LE] THEN ASM SET_TAC[];
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
      ASM_SIMP_TAC[FINITE_DELETE; PRODUCT_POS_LE]];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[SUM_DELETE]]);;

let STATE_SUMS_DIAG = prove
 (`!k (w:num->num->real) u v.
     w 0 0 = &1 /\ (!j. ~(j = 0) ==> w 0 j = &0 /\ w j 0 = &0) /\
     (!i. ~(i = 0) ==> w i i = u) /\
     (!i j. ~(i = 0) /\ ~(j = 0) /\ ~(i = j) ==> w i j = v)
     ==> sum(0..k) (\i. sum(0..k) (\j. w i j)) =
         &1 + &k * (u + (&k - &1) * v) /\
         sum(0..k) (\i. w i i) = &1 + &k * u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..k) (\j. (w:num->num->real) 0 j) = &0 /\
    sum(1..k) (\i. w i 0 + sum(1..k) (\j. w i j)) =
    sum(1..k) (\i. u + (&k - &1) * v) /\
    sum(1..k) (\i. w i i) = sum(1..k) (\i. u)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(j = 0)`];
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(j = 0)`; REAL_ADD_LID] THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1..k) (\j. if i = j then u else v)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
        REWRITE_TAC[] THEN COND_CASES_TAC THENL
         [ASM_MESON_TAC[ARITH_RULE `1 <= j ==> ~(j = 0)`];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC];
        MATCH_MP_TAC SUM_NUMSEG_DELTA_ELSE THEN ASM_REWRITE_TAC[IN_NUMSEG]];
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(j = 0)`]];
    ASM_REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The main term of S1.                                                      *)
(* ------------------------------------------------------------------------- *)

let S1_PAIR_WEIGHT = prove
 (`!k P (y:(num->num)->real) ym c c'.
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\
     c IN col_set k P /\ c' IN col_set k P /\
     abs(y c) <= ym /\ abs(y c') <= ym
     ==> abs(y c / product (col_supp c) (\p. &p - &1) *
             y c' / product (col_supp c') (\p. &p - &1) * col_corr c c')
         <= ym pow 2 *
            product P (\p. if c p = 0 /\ c' p = 0 then &1
                           else if c p = 0 \/ c' p = 0 then &0
                           else if c p = c' p then inv(&p - &1)
                           else inv(&p - &1) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `col_supp c SUBSET P /\ col_supp c' SUBSET P`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c:num->num) IN col_set k P` THEN
    UNDISCH_TAC `(c':num->num) IN col_set k P` THEN
    REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(col_supp c) /\ FINITE(col_supp c')`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ym` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= product P (\p. if c p = 0 /\ c' p = 0 then &1
                         else if c p = 0 \/ c' p = 0 then &0
                         else if c p = c' p then inv(&p - &1)
                         else inv(&p - &1) pow 2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= inv(&p - &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 <= x ==> &0 <= x`];
      ALL_TAC] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POS; REAL_LE_POW_2];
    ALL_TAC] THEN
  REWRITE_TAC[col_corr] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_MUL_RZERO; REAL_ABS_0] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]] THEN
  SUBGOAL_THEN `!p. (c:num->num) p = 0 <=> (c':num->num) p = 0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `col_supp c = col_supp c'` THEN
    REWRITE_TAC[col_supp; EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o
    check (fun th -> concl th = `col_supp c = col_supp c'`)) THEN
  ABBREV_TAC `t = col_supp c` THEN
  SUBGOAL_THEN
   `y c / product t (\p. &p - &1) * y c' / product t (\p. &p - &1) *
    product t (\p. if (c:num->num) p = c' p then &p - &1 else --(&1)) =
    y c * y c' * product t (\p. if c p = c' p then inv(&p - &1)
                                else --(inv(&p - &1) pow 2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN
    ASM_SIMP_TAC[GSYM PRODUCT_INV] THEN
    ABBREV_TAC `ip = product t (\p. inv(&p - &1))` THEN
    SUBGOAL_THEN
     `product t (\p. if (c:num->num) p = c' p then inv(&p - &1)
                     else --(inv (&p - &1) pow 2)) =
      ip * ip * product t (\p. if c p = c' p then &p - &1 else --(&1))`
    SUBST1_TAC THENL
     [EXPAND_TAC "ip" THEN
      SIMP_TAC[GSYM PRODUCT_MUL; ASSUME `FINITE(t:num->bool)`] THEN
      MATCH_MP_TAC PRODUCT_EQ THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `&1 <= &p - &1` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      COND_CASES_TAC THEN CONV_TAC REAL_FIELD;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product P (\p. if c p = 0 /\ c' p = 0 then &1
                   else if c p = 0 \/ c' p = 0 then &0
                   else if c p = c' p then inv(&p - &1)
                   else inv(&p - &1) pow 2) =
    product t (\p. abs(if (c:num->num) p = c' p then inv(&p - &1)
                       else --(inv(&p - &1) pow 2)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `product t (\p. if c p = 0 /\ c' p = 0 then &1
                     else if c p = 0 \/ c' p = 0 then &0
                     else if c p = c' p then inv(&p - &1)
                     else inv(&p - &1) pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_SUPERSET THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "t" THEN REWRITE_TAC[col_supp; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((c:num->num) p = 0) /\ ~((c':num->num) p = 0)`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(p:num) IN t` THEN EXPAND_TAC "t" THEN
        REWRITE_TAC[col_supp; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= inv(&p - &1)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_POW] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_ABS; REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS]);;

let S1_MAIN_TERM = prove
 (`!k P fam (y:(num->num)->real) ym.
     FINITE P /\ (!p. p IN P ==> 2 <= p) /\ fam SUBSET col_set k P /\
     (!c. c IN fam ==> abs(y c) <= ym)
     ==> abs(sum fam (\c. sum fam (\c'.
                 y c / product (col_supp c) (\p. &p - &1) *
                 y c' / product (col_supp c') (\p. &p - &1) *
                 col_corr c c')) -
             sum fam (\c. y c pow 2 / product (col_supp c) (\p. &p - &1)))
         <= ym pow 2 *
            (product P (\p. &1 + &k * (inv(&p - &1) +
                                      (&k - &1) * inv(&p - &1) pow 2)) -
             product P (\p. &1 + &k * inv(&p - &1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(fam:(num->num)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_COL_SET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> &1 <= &p - &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `F2 = \c c'. y c / product (col_supp c) (\p. &p - &1) *
                          y c' / product (col_supp c') (\p. &p - &1) *
                          col_corr c c'` THEN
  SUBGOAL_THEN
   `!c c'. y c / product (col_supp c) (\p. &p - &1) *
           y c' / product (col_supp c') (\p. &p - &1) * col_corr c c' =
           (F2:(num->num)->(num->num)->real) c c'`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "F2" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sum fam (\c. y c pow 2 / product (col_supp c) (\p. &p - &1)) =
    sum fam (\c. (F2:(num->num)->(num->num)->real) c c)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    EXPAND_TAC "F2" THEN REWRITE_TAC[col_corr] THEN
    SUBGOAL_THEN `col_supp c SUBSET P` ASSUME_TAC THENL
     [UNDISCH_TAC `fam SUBSET col_set k P` THEN
      UNDISCH_TAC `(c:num->num) IN fam` THEN
      REWRITE_TAC[col_set; col_supp; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < product (col_supp c) (\p. &p - &1)` MP_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LT THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET];
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 < x`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]];
      CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum fam (\c. sum fam (\c'. (F2:(num->num)->(num->num)->real) c c')) -
    sum fam (\c. F2 c c) =
    sum fam (\c. sum (fam DELETE c) (\c'. F2 c c'))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SUM_DELETE];
    ALL_TAC] THEN
  ABBREV_TAC
   `wt = \p:num i:num j:num. if i = 0 /\ j = 0 then &1
                             else if i = 0 \/ j = 0 then &0
                             else if i = j then inv(&p - &1)
                             else inv(&p - &1) pow 2` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `sum fam (\c. sum (fam DELETE c) (\c'.
       ym pow 2 * product P (\p. (wt:num->num->num->real) p (c p) (c' p))))`
  THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum fam (\c. abs(sum (fam DELETE c)
                    (\c'. (F2:(num->num)->(num->num)->real) c c')))` THEN
    ASM_SIMP_TAC[SUM_ABS] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:num->num` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (fam DELETE c)
                    (\c'. abs((F2:(num->num)->(num->num)->real) c c'))` THEN
    ASM_SIMP_TAC[SUM_ABS; FINITE_DELETE] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    X_GEN_TAC `c':num->num` THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["F2"; "wt"] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC S1_PAIR_WEIGHT THEN EXISTS_TAC `k:num` THEN
    ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_LMUL; FINITE_DELETE] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `product P (\p. sum (0..k) (\i. sum (0..k) (\j.
                     (wt:num->num->num->real) p i j))) -
    product P (\p. sum (0..k) (\i. wt p i i))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OFFDIAG_STATES THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "wt" THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= inv(&p - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &0 <= x`) THEN ASM_SIMP_TAC[];
      REPEAT COND_CASES_TAC THEN SIMP_TAC[REAL_POS; REAL_LE_POW_2]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `(wt:num->num->num->real) p`; `inv(&p - &1)`;
                 `inv(&p - &1) pow 2`] STATE_SUMS_DIAG) THEN
  (ANTS_TAC THENL
    [EXPAND_TAC "wt" THEN REWRITE_TAC[] THEN SIMP_TAC[];
     SIMP_TAC[]]));;
