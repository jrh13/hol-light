(* ========================================================================= *)
(* Linnik's theorem on the least quadratic non-residue (Linnik, "The large   *)
(* sieve", Doklady 1941: the first application of the large sieve).          *)
(* Vinogradov conjectured that the least quadratic non-residue n(p) mod p    *)
(* is O(p^e) for every e > 0 (still open; Burgess proved n(p) <<             *)
(* p^(1/(4 sqrt e) + e)).  Linnik showed that the conjecture fails for at    *)
(* most boundedly many primes at each scale:                                 *)
(*   LINNIK_NONRESIDUE:                                                      *)
(*     !e. &0 < e                                                            *)
(*         ==> ?B. !N. &(CARD {p | prime p /\ p <= N /\                      *)
(*                                 !n. 1 <= n /\ &n <= &N rpow e             *)
(*                                     ==> ?x. (x EXP 2 == n) (mod p)}) <= B *)
(* and, sorting the primes into the ranges 2^(2^k) <= p < 2^(2^(k+1)),       *)
(*   LINNIK_NONRESIDUE_LOGLOG: for every e > 0 there is B such that, for     *)
(*   N >= 3, at most B (1 + log log N) primes p <= N have no quadratic       *)
(*   non-residue n <= p^e.                                                   *)
(* Method.  Let X = N^2 and let S be the set of N^e-smooth numbers up to X.  *)
(* If every n <= N^e is a square mod p then so is every element of S         *)
(* (SMOOTH_SQUARE), and S meets at most (p + 1)/2 classes mod p for odd p    *)
(* (SQUARE_CLASSES_ODD).  Parseval mod p (DFT_PARSEVAL) and Cauchy-Schwarz   *)
(* over the occupied classes give ONE_PRIME_SIEVE:                           *)
(*   |S|^2 (p - 1)/(p + 1) <= sum_{0 < a < p} |sum_{n in S} e(a n / p)|^2,   *)
(* and the large sieve (LARGE_SIEVE_FAREY with Q = N) bounds the sum of      *)
(* these over the exceptional odd primes by 40 N^2 |S| (LINNIK_SIEVE_BOUND). *)
(* Smooth numbers are a positive proportion, |S| >= c(e) X (SMOOTH_LOWER:    *)
(* induction on the exponent m in X^2 <= y^m, counting n = p j with p a      *)
(* prime in (sqrt y, y], with Mertens' theorem for these primes and a        *)
(* Chebyshev bound; no Dickman function), so at most 80/c(e) odd primes      *)
(* are exceptional.                                                          *)
(* ========================================================================= *)

needs "Sieve/goldbach_almost.ml";;
needs "Sieve/romanov.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Squares modulo a prime.                                                   *)
(* ------------------------------------------------------------------------- *)

let SQUARE_MOD_MUL = prove
 (`!p a b. (?x. (x EXP 2 == a) (mod p)) /\ (?x. (x EXP 2 == b) (mod p))
           ==> ?x. (x EXP 2 == a * b) (mod p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `x:num`) (X_CHOOSE_TAC `z:num`)) THEN
  EXISTS_TAC `x * z:num` THEN REWRITE_TAC[MULT_EXP] THEN
  MAP_EVERY UNDISCH_TAC
   [`(x EXP 2 == a) (mod p)`; `(z EXP 2 == b) (mod p)`] THEN
  CONV_TAC NUMBER_RULE);;

let SMOOTH_SQUARE = prove
 (`!p y. (!q. prime q /\ q <= y ==> ?x. (x EXP 2 == q) (mod p))
         ==> !n. 1 <= n /\ (!q. prime q /\ q divides n ==> q <= y)
                 ==> ?x. (x EXP 2 == n) (mod p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[EXP_ONE] THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` PRIME_FACTOR) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `q divides n` THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `2 <= q /\ 1 <= r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    UNDISCH_TAC `1 <= q * r` THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SQUARE_MOD_MUL THEN CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL];
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `1 * r < q * r ==> r < q * r`) THEN
      REWRITE_TAC[LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
      X_GEN_TAC `t:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[DIVIDES_LMUL]]]);;

let SQUARE_CLASSES_ODD = prove
 (`!p. prime p /\ ODD p
       ==> &2 * &(CARD {h | h < p /\ ?x. (x EXP 2 == h) (mod p)}) <= &p + &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC o
    REWRITE_RULE[ODD_EXISTS]) THEN
  SUBGOAL_THEN `(SUC(2 * j) - 1) DIV 2 = j` ASSUME_TAC THENL
   [MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `{h | h < SUC(2 * j) /\ ?x. (x EXP 2 == h) (mod (SUC(2 * j)))}
                SUBSET IMAGE (\x. (x EXP 2) MOD SUC(2 * j)) (0..j)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `h:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x:num`)) THEN
    SUBGOAL_THEN `~(SUC(2 * j) = 0)` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x MOD SUC(2 * j) < SUC(2 * j) /\
                  ((x MOD SUC(2 * j)) EXP 2 == h) (mod (SUC(2 * j)))`
    MP_TAC THENL
     [ASM_SIMP_TAC[DIVISION] THEN
      UNDISCH_TAC `(x EXP 2 == h) (mod (SUC(2 * j)))` THEN
      MATCH_MP_TAC(NUMBER_RULE
       `(a == x) (mod n) ==> (x EXP 2 == h) (mod n) ==> (a EXP 2 == h) (mod
         n)`)
      THEN REWRITE_TAC[CONG_LMOD; CONG_REFL];
      SPEC_TAC(`x MOD SUC(2 * j)`,`r:num`) THEN REPEAT STRIP_TAC] THEN
    ASM_CASES_TAC `r <= j:num` THENL
     [EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(r EXP 2 == h) (mod (SUC(2 * j)))` THEN
      ASM_SIMP_TAC[CONG; MOD_LT];
      EXISTS_TAC `SUC(2 * j) - r` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      SUBGOAL_THEN `((SUC(2 * j) - r) EXP 2 == r EXP 2) (mod (SUC(2 * j)))`
      MP_TAC THENL
       [MATCH_MP_TAC(NUMBER_RULE
         `s + r = p ==> (s EXP 2 == r EXP 2) (mod p)`) THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(r EXP 2 == h) (mod (SUC(2 * j)))` THEN
      ASM_SIMP_TAC[CONG; MOD_LT]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `&2 * &(CARD(IMAGE (\x. (x EXP 2) MOD SUC(2 * j)) (0..j)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG];
    TRANS_TAC REAL_LE_TRANS `&2 * &(CARD(0..j))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE; LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN MATCH_MP_TAC CARD_IMAGE_LE THEN
      REWRITE_TAC[FINITE_NUMSEG];
      REWRITE_TAC[CARD_NUMSEG; REAL_OF_NUM_MUL; REAL_OF_NUM_ADD;
                  REAL_OF_NUM_LE] THEN ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The large sieve inequality at one prime.                                  *)
(* ------------------------------------------------------------------------- *)

let VSUM_RESIDUE_GROUP = prove
 (`!S X p a. ~(p = 0) /\ S SUBSET 1..X
             ==> vsum(1..X) (\n. (if n IN S then Cx(&1) else Cx(&0)) *
                                 expi(&n * &a / &p)) =
                 vsum {h | h < p}
                   (\h. Cx(&(CARD {n | n IN S /\ n MOD p = h})) *
                        expi(&a * &h / &p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `vsum S (\n. expi(&n * &a / &p))` THEN CONJ_TAC THENL
   [REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LID; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `S SUBSET 1..X` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. n MOD p`; `\n. expi(&n * &a / &p)`; `S:num->bool`;
                 `{h | h < p:num}`] VSUM_GROUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; DIVISION];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `h:num` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN BETA_TAC THEN
  TRANS_TAC EQ_TRANS
   `vsum {n | n IN S /\ n MOD p = h} (\n. expi(&a * &h / &p))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`p:num`; `a:num`; `n:num`] EXPI_MOD) THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[VSUM_CONST; FINITE_RESTRICT; COMPLEX_CMUL]]);;

let RESIDUE_PARSEVAL = prove
 (`!(Z:num->real) p.
     ~(p = 0)
     ==> sum {a | a < p}
           (\a. norm(vsum {h | h < p} (\h. Cx(Z h) * expi(&a * &h / &p)))
                pow 2) =
         &p * sum {h | h < p} (\h. Z h pow 2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\h. Cx((Z:num->real) h)`; `p:num`] DFT_PARSEVAL) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_POW2_ABS] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
  BETA_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM COMPLEX_NORM_CNJ] THEN AP_TERM_TAC THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG_LT; CNJ_MUL; CNJ_CX; CNJ_EXPI;
           REAL_NEG_NEG]);;

let SIEVE_ARITH = prove
 (`!c W p R:real.
     &0 <= W /\ &3 <= p /\ c pow 2 <= R * W /\ &2 * R <= p + &1
     ==> c pow 2 * (p - &1) / (p + &1) <= p * W - c pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&2 * c pow 2 <= (p + &1) * W` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(&2 * R) * W` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV
   [REAL_ARITH `!a b d:real. a * b / d = (a * b) / d`] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&3 <= p ==> &0 < p + &1`] THEN
  SUBGOAL_THEN `&0 <= p * ((p + &1) * W - &2 * c pow 2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

let SUM_PRIME_SPLIT0 = prove
 (`!(f:num->real) p.
     prime p
     ==> sum {a | a < p} f = f 0 + sum {a | a < p /\ coprime(a,p)} f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a < p} = 0 INSERT {a | a < p /\ coprime(a,p)} /\
                ~(0 IN {a | a < p /\ coprime(a,p)}) /\
                FINITE {a | a < p /\ coprime(a,p)}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
      X_GEN_TAC `a:num` THEN ASM_CASES_TAC `a = 0` THEN
      ASM_REWRITE_TAC[] THENL
       [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `a < p:num` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; COPRIME_0] THEN ASM_MESON_TAC[PRIME_1];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a | a < p:num}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]];
    ASM_SIMP_TAC[SUM_CLAUSES]]);;

let ONE_PRIME_SIEVE = prove
 (`!S X p. prime p /\ ODD p /\ S SUBSET 1..X /\
           (!n. n IN S ==> ?x. (x EXP 2 == n) (mod p))
           ==> &(CARD S) pow 2 * (&p - &1) / (&p + &1) <=
               sum {a | a < p /\ coprime(a,p)}
                 (\a. norm(vsum(1..X)
                        (\n. (if n IN S then Cx(&1) else Cx(&0)) *
                             expi(&n * &a / &p))) pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0) /\ 3 <= p` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
    SUBGOAL_THEN `~(p = 2)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `ODD p` THEN ASM_REWRITE_TAC[ARITH];
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_RESIDUE_GROUP] THEN
  ABBREV_TAC `Z = \h. &(CARD {n | n IN S /\ n MOD p = h})` THEN
  SUBGOAL_THEN `!h. &(CARD {n | n IN S /\ n MOD p = h}) = (Z:num->real) h`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sum {h | h < p} (Z:num->real) = &(CARD(S:num->bool))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN
    MP_TAC(ISPECL [`\n. n MOD p`; `\n:num. 1`; `S:num->bool`;
                   `{h | h < p:num}`] NSUM_GROUP) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; DIVISION];
      ALL_TAC] THEN
    SIMP_TAC[GSYM CARD_EQ_NSUM; FINITE_RESTRICT;
             ASSUME `FINITE(S:num->bool)`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[REAL_OF_NUM_SUM; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(CARD(S:num->bool)) pow 2 <=
    &(CARD {h | h < p /\ ?x. (x EXP 2 == h) (mod p)}) *
    sum {h | h < p} (\h. (Z:num->real) h pow 2)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!h. h < p /\ ~(?x. (x EXP 2 == h) (mod p))
                      ==> (Z:num->real) h = &0` ASSUME_TAC THENL
     [X_GEN_TAC `h:num` THEN STRIP_TAC THEN EXPAND_TAC "Z" THEN
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      SIMP_TAC[CARD_EQ_0; FINITE_RESTRICT; ASSUME `FINITE(S:num->bool)`] THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_TAC `x:num`) THEN
      UNDISCH_TAC `~(?x. (x EXP 2 == h) (mod p))` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `x:num` THEN
      UNDISCH_TAC `(x EXP 2 == n) (mod p)` THEN
      UNDISCH_TAC `n MOD p = h` THEN
      SIMP_TAC[CONG; MOD_MOD_REFL] THEN ASM_SIMP_TAC[MOD_LT];
      ALL_TAC] THEN
    ABBREV_TAC `R = {h | h < p /\ ?x. (x EXP 2 == h) (mod p)}` THEN
    SUBGOAL_THEN `R SUBSET {h | h < p:num}` ASSUME_TAC THENL
     [EXPAND_TAC "R" THEN SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE(R:num->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&(CARD(S:num->bool)) = sum R (Z:num->real)` SUBST1_TAC THENL
     [UNDISCH_TAC `sum {h | h < p} (Z:num->real) = &(CARD(S:num->bool))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUM_SUPERSET THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `h:num` THEN EXPAND_TAC "R" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `&(CARD(R:num->bool)) * sum R (\h. (Z:num->real) h pow 2)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\h:num. &1`; `Z:num->real`; `R:num->bool`]
                    SIEVE_SUM_CAUCHY_SCHWARZ) THEN
      ASM_SIMP_TAC[REAL_MUL_LID; REAL_POW_ONE; SUM_CONST; REAL_MUL_RID;
                   ETA_AX];
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      SIMP_TAC[REAL_POW_2; REAL_LE_SQUARE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(vsum {h | h < p} (\h. Cx((Z:num->real) h) * expi(&0 * &h / &p)))
    pow 2 = &(CARD(S:num->bool)) pow 2`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_LZERO; real_div; EXPI_0; COMPLEX_MUL_RID;
                VSUM_CX; COMPLEX_NORM_CX; ETA_AX] THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Z:num->real`; `p:num`] RESIDUE_PARSEVAL) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\x. norm(vsum {h | h < p} (\h. Cx((Z:num->real) h) * expi(&x * &h / &p)))
         pow 2`; `p:num`] SUM_PRIME_SPLIT0) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `&p * sum {h | h < p} (\h. (Z:num->real) h pow 2) -
    &(CARD(S:num->bool)) pow 2` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIEVE_ARITH THEN
    EXISTS_TAC `&(CARD {h | h < p /\ ?x. (x EXP 2 == h) (mod p)})` THEN
    ASM_SIMP_TAC[SQUARE_CLASSES_ODD; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    SIMP_TAC[REAL_POW_2; REAL_LE_SQUARE];
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (term_match [] `a + b = c:real`) (concl th))) THEN
    MATCH_ACCEPT_TAC(REAL_ARITH `!a b c:real. a + b = c ==> c - a <= b`)]);;

(* ------------------------------------------------------------------------- *)
(* Smooth numbers are a positive proportion.                                 *)
(* ------------------------------------------------------------------------- *)

let smooth_upto = new_definition
 `smooth_upto X y =
    {n | 1 <= n /\ n <= X /\ !q. prime q /\ q divides n ==> q <= y}`;;

let FINITE_SMOOTH_UPTO = prove
 (`!X y. FINITE(smooth_upto X y)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `1..X` THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  REWRITE_TAC[smooth_upto; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
  MESON_TAC[]);;

let SMOOTH_UPTO_SMALL = prove
 (`!X y. X <= y ==> CARD(smooth_upto X y) = X`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `smooth_upto X y = 1..X` SUBST1_TAC THENL
   [REWRITE_TAC[smooth_upto; EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN EQ_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG_1]]);;

let SMOOTH_UPTO_FIBRE = prove
 (`!X y p. prime p /\ p <= y
           ==> CARD {n | n IN smooth_upto X y /\ p divides n} =
               CARD(smooth_upto (X DIV p) y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `{n | n IN smooth_upto X y /\ p divides n} =
                IMAGE (\j. p * j) (smooth_upto (X DIV p) y)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; smooth_upto] THEN
    X_GEN_TAC `n:num` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      UNDISCH_TAC `p divides n` THEN GEN_REWRITE_TAC LAND_CONV [divides] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` SUBST_ALL_TAC) THEN
      EXISTS_TAC `j:num` THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[LE_RDIV_EQ] THEN REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `1 <= p * j` THEN
        REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ARITH_TAC;
        X_GEN_TAC `q:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_MESON_TAC[DIVIDES_LMUL]];
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `j <= X DIV p` THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
      DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC;
        X_GEN_TAC `q:num` THEN STRIP_TAC THEN
        MP_TAC(SPECL [`q:num`; `p:num`; `j:num`] PRIME_DIVPROD) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [SUBGOAL_THEN `q = p:num` (fun th -> ASM_REWRITE_TAC[th]) THEN
          ASM_MESON_TAC[DIVIDES_PRIME_PRIME];
          ASM_MESON_TAC[]];
        ASM_MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_SMOOTH_UPTO] THEN
    ASM_SIMP_TAC[EQ_MULT_LCANCEL]]);;

let SMOOTH_FEW_LARGE = prove
 (`!X y m n. 2 <= y /\ X EXP 2 <= y EXP (m + 1) /\ 1 <= n /\ n <= X
             ==> CARD {p | prime p /\ y < p EXP 2 /\ p <= y /\ p divides n}
                 <= m`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `T0 = {p | prime p /\ y < p EXP 2 /\ p <= y /\ p divides n}` THEN
  SUBGOAL_THEN `FINITE(T0:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "T0" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..y` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `nproduct T0 (\p. p) <= X` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `n:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`nproduct T0 (\p. p)`; `n:num`] DIVIDES_LE) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    SUBGOAL_THEN `(!p. p IN T0 ==> prime p) /\ (!p. p IN T0 ==> p divides n)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "T0" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    MP_TAC(ISPECL [`T0:num->bool`; `n:num`] PRIMES_DIVIDE_IFF_NPRODUCT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y + 1) EXP (CARD(T0:num->bool)) <= X EXP 2` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `nproduct T0 (\p. p) EXP 2` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[GSYM NPRODUCT_CONST; EXP_2; GSYM NPRODUCT_MUL] THEN
      MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "T0" THEN REWRITE_TAC[IN_ELIM_THM; EXP_2] THEN ARITH_TAC;
      MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y + 1) EXP (CARD(T0:num->bool)) < (y + 1) EXP (m + 1)`
  MP_TAC THENL
   [TRANS_TAC LET_TRANS `X EXP 2` THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC LET_TRANS `y EXP (m + 1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EXP_MONO_LT_IMP THEN ARITH_TAC;
    REWRITE_TAC[LT_EXP] THEN ARITH_TAC]);;

let SMOOTH_DOUBLE_COUNT = prove
 (`!X y m. 2 <= y /\ X EXP 2 <= y EXP (m + 1)
           ==> nsum {p | prime p /\ y < p EXP 2 /\ p <= y}
                    (\p. CARD(smooth_upto (X DIV p) y))
               <= m * CARD(smooth_upto X y)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = {p | prime p /\ y < p EXP 2 /\ p <= y}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `0..y` THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC LE_TRANS
   `nsum P (\p. nsum (smooth_upto X y)
                     (\n. if p divides n then 1 else 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NSUM_EQ THEN
    X_GEN_TAC `p:num` THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`X:num`; `y:num`; `p:num`] SMOOTH_UPTO_FIBRE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT; FINITE_SMOOTH_UPTO] THEN
    REWRITE_TAC[NSUM_RESTRICT_SET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p n. if (p:num) divides n then 1 else 0`; `P:num->bool`;
                 `smooth_upto X y`] NSUM_SWAP) THEN
  ASM_SIMP_TAC[FINITE_SMOOTH_UPTO] THEN DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_MP_TAC NSUM_BOUND THEN
  REWRITE_TAC[FINITE_SMOOTH_UPTO] THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN
  TRANS_TAC LE_TRANS
   `CARD {p | prime p /\ y < p EXP 2 /\ p <= y /\ p divides n}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN
    SUBGOAL_THEN `{p | prime p /\ y < p EXP 2 /\ p <= y /\ p divides n} =
                  {p | p IN P /\ p divides n}` SUBST1_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT] THEN
    REWRITE_TAC[NSUM_RESTRICT_SET];
    MATCH_MP_TAC SMOOTH_FEW_LARGE THEN EXISTS_TAC `X:num` THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `n IN smooth_upto X y` THEN
    SIMP_TAC[smooth_upto; IN_ELIM_THM]]);;

let MERTENS_DIFF_ARITH = prove
 (`!A B Pp LL M l2 e1 e2.
     A = Pp + B /\ abs(A - LL - M) <= e1 /\ abs(B - (LL - l2) - M) <= e2 /\
     &6931 / &10000 <= l2 /\ e1 <= &1 / &16 /\ e2 <= &1 / &8
     ==> &1 / &2 <= Pp`,
  REAL_ARITH_TAC);;

let MERTENS_HALF = prove
 (`?y1. !y. y1 <= y
            ==> &1 / &2 <=
                sum {p | prime p /\ y < p EXP 2 /\ p <= y} (\p. inv(&p))`,
  X_CHOOSE_TAC `M:real` MERTENS_RECIP THEN
  MP_TAC(SPEC `exp(&800)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `y1:num`) THEN EXISTS_TAC `y1:num` THEN
  X_GEN_TAC `y:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&800 <= log(&y)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    TRANS_TAC REAL_LE_TRANS `&y1` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 <= &y` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `exp(&800)` THEN CONJ_TAC THENL
     [MP_TAC(SPEC `&800` REAL_EXP_LE_X) THEN REAL_ARITH_TAC;
      TRANS_TAC REAL_LE_TRANS `&y1` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. &p <= sqrt(&y) <=> p EXP 2 <= y` ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW] THEN
      TRANS_TAC REAL_LE_TRANS `sqrt(&y) pow 2` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
        SIMP_TAC[SQRT_POW_2; REAL_POS; REAL_LE_REFL]];
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_RSQRT THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p | prime p /\ &p <= &y} =
                {p | prime p /\ y < p EXP 2 /\ p <= y} UNION
                {p | prime p /\ &p <= sqrt(&y)}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; REAL_OF_NUM_LE] THEN
    X_GEN_TAC `p:num` THEN ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `p <= p EXP 2` MP_TAC THENL
     [REWRITE_TAC[EXP_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM MULT_CLAUSES] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. inv(&p)`; `{p | prime p /\ y < p EXP 2 /\ p <= y}`;
                 `{p | prime p /\ &p <= sqrt(&y)}`] SUM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..y` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..y` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `p:num` THEN STRIP_TAC THEN
      TRANS_TAC LE_TRANS `p EXP 2` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[EXP_2] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM MULT_CLAUSES] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC;
      ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM(ASSUME `{p | prime p /\ &p <= &y} =
                {p | prime p /\ y < p EXP 2 /\ p <= y} UNION
                {p | prime p /\ &p <= sqrt(&y)}`)] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&y` o check (is_forall o concl)) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `sqrt(&y)` o check (is_forall o concl)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_RSQRT THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ALL_TAC THEN
  SUBGOAL_THEN `log(sqrt(&y)) = log(&y) / &2`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC LOG_SQRT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(log(&y) / &2) = log(log(&y)) - log(&2)`
   (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [MATCH_MP_TAC LOG_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&50 / log(&y) <= &1 / &16 /\ &50 / (log(&y) / &2) <= &1 / &8`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < log(&y) /\ &0 < log(&y) / &2` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MERTENS_DIFF_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`sum {p | prime p /\ &p <= &y} (\p. inv(&p))`;
    `sum {p | prime p /\ &p <= sqrt(&y)} (\p. inv(&p))`;
    `log(log(&y))`; `M:real`; `log(&2)`; `&50 / log(&y)`;
    `&50 / (log(&y) / &2)`] THEN
  ASM_REWRITE_TAC[LOG_2_LOWER]);;

let DIV_LOWER_REAL = prove
 (`!X p. ~(p = 0) ==> &X / &p - &1 <= &(X DIV p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < p <=> ~(p = 0)`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x < y + &1 ==> x - &1 <= y`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
  MP_TAC(SPECL [`X:num`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ARITH_TAC);;

let SUM_DIV_LOWER = prove
 (`!X P. FINITE P /\ (!p. p IN P ==> ~(p = 0))
         ==> &X * sum P (\p. inv(&p)) - &(CARD P) <=
             sum P (\p. &(X DIV p))`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS `sum P (\p. &X / &p - &1)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_SUB; SUM_LMUL; SUM_CONST; real_div; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_LE_REFL];
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[DIV_LOWER_REAL]]);;

let SMOOTH_LOWER = prove
 (`?y0. 2 <= y0 /\
        !m. ?c. &0 < c /\ c <= &1 /\
                !X y. y0 <= y /\ X EXP 2 <= y EXP m
                      ==> c * &X <= &(CARD(smooth_upto X y))`,
  X_CHOOSE_TAC `y1:num` MERTENS_HALF THEN
  X_CHOOSE_TAC `N0:num` PI_UPPER_EVENTUALLY THEN
  MP_TAC(SPEC `exp(&8)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `y2:num`) THEN
  EXISTS_TAC `y1 + N0 + y2 + 2` THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  INDUCT_TAC THENL
   [EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01; REAL_LE_REFL; REAL_MUL_LID] THEN
    REWRITE_TAC[EXP] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `X <= y:num` (fun th -> SIMP_TAC[SMOOTH_UPTO_SMALL; th;
                                                REAL_LE_REFL]) THEN
    MP_TAC(SPEC `X:num` LE_SQUARE_REFL) THEN
    UNDISCH_TAC `X EXP 2 <= 1` THEN REWRITE_TAC[EXP_2] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c / (&4 * &(m + 1))` THEN
  SUBGOAL_THEN `&0 < &4 * &(m + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV];
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    TRANS_TAC REAL_LE_TRANS `&1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`X:num`; `y:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `X <= y:num` THENL
   [ASM_SIMP_TAC[SMOOTH_UPTO_SMALL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    TRANS_TAC REAL_LE_TRANS `&1` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `X EXP 2 <= y EXP SUC m` THEN
    ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN
    MP_TAC(SPEC `X:num` LE_SQUARE_REFL) THEN REWRITE_TAC[EXP_2] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `P = {p | prime p /\ y < p EXP 2 /\ p <= y}` THEN
  SUBGOAL_THEN `FINITE(P:num->bool) /\ (!p. p IN P ==> ~(p = 0))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..y` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
      ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> c * &(X DIV p) <= &(CARD(smooth_upto (X DIV p)
    y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(p EXP 2 = 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[EXP_EQ_0; PRIME_IMP_NZ]; ALL_TAC] THEN
    SUBGOAL_THEN `(X DIV p) EXP 2 * p EXP 2 <= y EXP m * p EXP 2` MP_TAC THENL
     [TRANS_TAC LE_TRANS `X EXP 2` THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MULT_EXP] THEN MATCH_MP_TAC EXP_MONO_LE_IMP THEN
        ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[DIV_MUL_LE];
        TRANS_TAC LE_TRANS `y EXP SUC m` THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [EXP] THEN
        GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
      ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`X:num`; `y:num`; `m:num`] SMOOTH_DOUBLE_COUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM ADD1] THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 / &2 <= sum P (\p. inv(&p))` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&8 <= log(&y)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    TRANS_TAC REAL_LE_TRANS `&y2` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * &(CARD(P:num->bool)) <= &y` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&4 * &(CARD {p | prime p /\ p <= y})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [EXPAND_TAC "P" THEN SET_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..y` THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
        ARITH_TAC];
      TRANS_TAC REAL_LE_TRANS `&4 * (&2 * &y / log(&y))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `&4 * (&2 * &y / log(&y)) = (&8 * &y) / log(&y)`
        SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN
        REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&8 <= x ==> &0 < x`] THEN
        GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_REWRITE_TAC[REAL_POS]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&X / &4 <= sum P (\p. &(X DIV p))` ASSUME_TAC THENL
   [MP_TAC(SPECL [`X:num`; `P:num->bool`] SUM_DIV_LOWER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&X * &1 / &2 <= &X * sum P (\p. inv(&p))` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    UNDISCH_TAC `~(X <= y:num)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `&4 * &(CARD(P:num->bool)) <= &y` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * sum P (\p. &(X DIV p)) <= &m * &(CARD(smooth_upto X y))`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `sum P (\p. &(CARD(smooth_upto (X DIV p) y)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUM] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c / (&4 * &(m + 1)) * &X = (c * (&X / &4)) / &(m + 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div; REAL_INV_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &(m + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  TRANS_TAC REAL_LE_TRANS `&m * &(CARD(smooth_upto X y))` THEN CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `c * sum P (\p. &(X DIV p))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REAL_ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Linnik's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

let LINNIK_ARITH = prove
 (`!k s n2 c:real.
     &0 <= k /\ &0 < c /\ &0 < n2 /\ c * n2 <= s /\
     k * (s pow 2 / &2) <= &40 * n2 * s
     ==> k <= &80 / c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL
   [TRANS_TAC REAL_LTE_TRANS `c * n2:real` THEN ASM_SIMP_TAC[REAL_LT_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `k * s <= &80 * n2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `(s:real) / &2` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y z w:real. x = y /\ y <= z /\ z = w ==> x <= w`) THEN
    EXISTS_TAC `(k:real) * (s pow 2 / &2)` THEN EXISTS_TAC `&40 * n2 *
      (s:real)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN EXISTS_TAC `n2:real` THEN
  ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LE_TRANS `(k:real) * s` THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV
     [REAL_ARITH `n2 * k * c = k * (c * n2:real)`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let LINNIK_SIEVE_BOUND = prove
 (`!N y c E.
     1 <= N /\ &0 < c /\
     c * &(N EXP 2) <= &(CARD(smooth_upto (N EXP 2) y)) /\
     (!p. p IN E
          ==> prime p /\ ODD p /\ p <= N /\
              !q. prime q /\ q <= y ==> ?x. (x EXP 2 == q) (mod p))
     ==> &(CARD E) <= &80 / c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `E SUBSET 1..N` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_NUMSEG] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(E:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  ABBREV_TAC `S = smooth_upto (N EXP 2) y` THEN
  SUBGOAL_THEN `S SUBSET 1..N EXP 2` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN
    REWRITE_TAC[smooth_upto; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p. p IN E
        ==> &(CARD(S:num->bool)) pow 2 / &2 <=
            sum {a | a < p /\ coprime(a,p)}
              (\a. norm(vsum(1..N EXP 2)
                     (\n. (if n IN S then Cx(&1) else Cx(&0)) *
                          expi(&n * &a / &p))) pow 2)`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`S:num->bool`; `N EXP 2`; `p:num`] ONE_PRIME_SIEVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[smooth_upto; IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM; IMP_IMP]
                     SMOOTH_SQUARE) THEN
      EXISTS_TAC `y:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c:real. a <= b ==> b <= c ==> a <= c`) THEN
    SUBGOAL_THEN `&3 <= &p` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
      SUBGOAL_THEN `~(p = 2)` MP_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `ODD p` THEN ASM_REWRITE_TAC[ARITH];
        ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_ARITH `&3 <= p ==> &0 < p + &1`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`N:num`; `N EXP 2`;
                 `\n:num. if n IN (S:num->bool) then Cx(&1) else Cx(&0)`]
                LARGE_SIEVE_FAREY) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `sum(1..N EXP 2) (\n. norm(if n IN S then Cx(&1) else Cx(&0)) pow 2) =
    &(CARD(S:num->bool))`
  SUBST1_TAC THENL
   [REWRITE_TAC[COND_RAND; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; REAL_POW_ONE] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
    SIMP_TAC[SUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG; REAL_MUL_RID] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `S SUBSET 1..N EXP 2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC LINNIK_ARITH THEN
  EXISTS_TAC `&(CARD(S:num->bool))` THEN EXISTS_TAC `&(N EXP 2)` THEN
  ASM_REWRITE_TAC[REAL_POS] THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum E (\p. sum {a | a < p /\ coprime(a,p)}
                (\a. norm(vsum(1..N EXP 2)
                       (\n. (if n IN S then Cx(&1) else Cx(&0)) *
                            expi(&n * &a / &p))) pow 2))` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_CONST] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(1..N) (\q. sum {a | a < q /\ coprime(a,q)}
                (\a. norm(vsum(1..N EXP 2)
                       (\n. (if n IN S then Cx(&1) else Cx(&0)) *
                            expi(&n * &a / &q))) pow 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_COPRIME_RESIDUES] THEN
    SIMP_TAC[REAL_POW_LE; NORM_POS_LE];
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `!x y z:real. x <= y ==> y = z ==> x <= z`)) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW] THEN REAL_ARITH_TAC]);;

let LINNIK_NONRESIDUE = prove
 (`!e. &0 < e
       ==> ?B. !N. &(CARD {p | prime p /\ p <= N /\
                               !n. 1 <= n /\ &n <= &N rpow e
                                   ==> ?x. (x EXP 2 == n) (mod p)}) <= B`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `y0:num` STRIP_ASSUME_TAC SMOOTH_LOWER THEN
  MP_TAC(SPEC `&5 / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC o SPEC `m:num`) THEN
  MP_TAC(SPEC `(&2 * &y0) rpow inv(e)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n1:num`) THEN
  EXISTS_TAC `&(2 EXP m + n1 + 1) + &80 / c + &1` THEN
  X_GEN_TAC `N:num` THEN
  ABBREV_TAC `E = {p | prime p /\ p <= N /\
                       !n. 1 <= n /\ &n <= &N rpow e
                           ==> ?x. (x EXP 2 == n) (mod p)}` THEN
  SUBGOAL_THEN `FINITE(E:num->bool) /\ E SUBSET 0..N` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      MESON_TAC[];
      MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &80 / c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `N < 2 EXP m + n1 + 1` THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= a /\ &0 <= b ==> x <= a + b + &1`) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    TRANS_TAC LE_TRANS `CARD(0..N)` THEN
    ASM_SIMP_TAC[CARD_SUBSET; FINITE_NUMSEG; CARD_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &y0 <= &N rpow e` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&n1 rpow e` THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `((&2 * &y0) rpow inv e) rpow e` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
        SIMP_TAC[RPOW_RPOW; REAL_LE_MUL; REAL_POS] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
        REWRITE_TAC[RPOW_POW; REAL_POW_1];
        MATCH_MP_TAC RPOW_LE2 THEN
        ASM_SIMP_TAC[RPOW_POS_LE; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE]];
      MATCH_MP_TAC RPOW_LE2 THEN
      ASM_SIMP_TAC[REAL_POS; REAL_OF_NUM_LE; REAL_LT_IMP_LE] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&N rpow e` FLOOR_POS) THEN
  ANTS_TAC THENL [SIMP_TAC[RPOW_POS_LE; REAL_POS]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:num`) THEN
  MP_TAC(SPEC `&N rpow e` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `y0 <= y:num` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * &y0 < &y + &1` MP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N EXP 2) EXP 2 <= y EXP m` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_POW; REAL_POW_POW] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
    SUBGOAL_THEN `&1 <= &N /\ &(2 EXP m) <= &N /\ &2 <= &y0`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&5 <= &m * e` ASSUME_TAC THENL
     [UNDISCH_TAC `&5 / e <= &m` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(&N rpow e / &2) pow m` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_POW_DIV] THEN
      SUBGOAL_THEN `(&N rpow e) pow m = &N rpow (&m * e)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM RPOW_POW] THEN SIMP_TAC[RPOW_RPOW; REAL_POS] THEN
        AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
      TRANS_TAC REAL_LE_TRANS `&N rpow &5` THEN CONJ_TAC THENL
       [REWRITE_TAC[RPOW_POW] THEN
        SUBGOAL_THEN `&N pow 5 = &N pow 4 * &N` SUBST1_TAC THENL
         [CONV_TAC REAL_RING; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_POW];
        MATCH_MP_TAC RPOW_MONO_LE THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[RPOW_POS_LE; REAL_POS];
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * &(N EXP 2) <= &(CARD(smooth_upto (N EXP 2) y))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `y:num`; `c:real`; `{p | p IN E /\ ODD p}`]
               LINNIK_SIEVE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN EXPAND_TAC "E" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= q ==> 1 <= q`];
      TRANS_TAC REAL_LE_TRANS `&y` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD(E:num->bool)) <= &(CARD {p | p IN E /\ ODD p}) + &1`
  MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    TRANS_TAC LE_TRANS `CARD({p | p IN E /\ ODD p} UNION {2})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_SING] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(p:num) IN E` THEN EXPAND_TAC "E" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PRIME_ODD];
        ASM_SIMP_TAC[FINITE_UNION; FINITE_RESTRICT; FINITE_SING]];
      TRANS_TAC LE_TRANS `CARD {p | p IN E /\ ODD p} + CARD {2}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CARD_UNION_LE THEN
        ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_SING];
        REWRITE_TAC[CARD_SING; LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(SPEC `2 EXP m + n1 + 1` REAL_POS) THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!z a k b:real. &0 <= z ==> a <= k + &1 ==> k <= b ==> a <= z + b + &1`));;

(* ------------------------------------------------------------------------- *)
(* The least non-residue below p^e for almost all primes.                    *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_EXP_RANGE = prove
 (`!p. 2 <= p ==> ?k. 2 EXP (2 EXP k) <= p /\ p < 2 EXP (2 EXP (k + 1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\k. p < 2 EXP (2 EXP (k + 1))` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [EXISTS_TAC `p:num` THEN TRANS_TAC LTE_TRANS `2 EXP p` THEN
    REWRITE_TAC[LT_POW2_REFL; LE_EXP; ARITH_EQ] THEN
    MP_TAC(SPEC `p + 1` LT_POW2_REFL) THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `k = 0` THENL
     [ASM_REWRITE_TAC[EXP] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `k - 1`) THEN
      ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> k - 1 < k /\ k - 1 + 1 = k`;
                   NOT_LT]]]);;

let LOGLOG_COUNT = prove
 (`!N. 3 <= N
       ==> FINITE {k | 2 EXP (2 EXP k) <= N} /\
           &(CARD {k | 2 EXP (2 EXP k) <= N}) <= &2 * (&1 + log(log(&N)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= log(&N)` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    TRANS_TAC REAL_LE_TRANS `&3` THEN REWRITE_TAC[EXP_1_LE_3] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(log(&N))` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC LOG_2_LOWER THEN DISCH_TAC THEN
  SUBGOAL_THEN `!k. 2 EXP (2 EXP k) <= N ==> &k <= &1 + &2 * log(log(&N))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&(2 EXP k) * log(&2) <= log(&N)` ASSUME_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      REWRITE_TAC[EXP_LT_0; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN `&k * log(&2) <= log(&2) + log(log(&N))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&k * log(&2) = log(&(2 EXP k))` SUBST1_TAC THENL
       [SIMP_TAC[GSYM REAL_OF_NUM_POW; LOG_POW; REAL_OF_NUM_LT; ARITH];
        ALL_TAC] THEN
      SUBGOAL_THEN `log(&2) + log(log(&N)) = log(&2 * log(&N))`
      SUBST1_TAC THENL
       [CONV_TAC SYM_CONV THEN MATCH_MP_TAC LOG_MUL THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_LT; EXP_LT_0; ARITH] THEN
      SUBGOAL_THEN `&0 <= &(2 EXP k)` MP_TAC THENL
       [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      SUBGOAL_THEN `&(2 EXP k) * &1 / &2 <= &(2 EXP k) * log(&2)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `log(&2)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= log(log(&N)) * (&2 * log(&2) - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `&1 + &2 * log(log(&N))` FLOOR_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `K1:num`) THEN
  MP_TAC(SPEC `&1 + &2 * log(log(&N))` FLOOR) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `{k | 2 EXP (2 EXP k) <= N} SUBSET 0..K1` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&k < &K1 + &1` MP_TAC THENL
     [TRANS_TAC REAL_LET_TRANS `&1 + &2 * log(log(&N))` THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&(CARD(0..K1))` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    REWRITE_TAC[CARD_NUMSEG; ARITH_RULE `(K1 + 1) - 0 = K1 + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC]);;

let LINNIK_NONRESIDUE_LOGLOG = prove
 (`!e. &0 < e
       ==> ?B. !N. 3 <= N
                   ==> &(CARD {p | prime p /\ p <= N /\
                                   !n. 1 <= n /\ &n <= &p rpow e
                                       ==> ?x. (x EXP 2 == n) (mod p)})
                       <= B * (&1 + log(log(&N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e / &2` LINNIK_NONRESIDUE) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `C0:real`)] THEN
  MP_TAC(SPEC `C0:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n0:num`) THEN
  EXISTS_TAC `&2 * &n0` THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
  MP_TAC(SPEC `N:num` LOGLOG_COUNT) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{p | prime p /\ p <= N /\
         !n. 1 <= n /\ &n <= &p rpow e ==> ?x. (x EXP 2 == n) (mod p)}
    SUBSET
    UNIONS {{p | prime p /\ p <= 2 EXP (2 EXP (k + 1)) /\
                 !n. 1 <= n /\ &n <= &(2 EXP (2 EXP (k + 1))) rpow (e / &2)
                     ==> ?x. (x EXP 2 == n) (mod p)} |
            k IN {k | 2 EXP (2 EXP k) <= N}}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `p:num` THEN STRIP_TAC THEN
    MP_TAC(SPEC `p:num` DOUBLE_EXP_RANGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC REAL_LE_TRANS `&(2 EXP (2 EXP (k + 1))) rpow (e / &2)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&(2 EXP (2 EXP (k + 1))) rpow (e / &2) =
                  &(2 EXP (2 EXP k)) rpow e` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1; GSYM EXP_EXP] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_POW; GSYM RPOW_POW] THEN
      SIMP_TAC[RPOW_RPOW; REAL_POS; REAL_POW_LE; RPOW_POS_LE] THEN
      AP_TERM_TAC THEN REAL_ARITH_TAC;
      MATCH_MP_TAC RPOW_LE2 THEN ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. FINITE {p | prime p /\ p <= 2 EXP (2 EXP (k + 1)) /\
                    !n. 1 <= n /\ &n <= &(2 EXP (2 EXP (k + 1))) rpow (e / &2)
                        ==> ?x. (x EXP 2 == n) (mod p)} /\
        CARD {p | prime p /\ p <= 2 EXP (2 EXP (k + 1)) /\
                  !n. 1 <= n /\ &n <= &(2 EXP (2 EXP (k + 1))) rpow (e / &2)
                      ==> ?x. (x EXP 2 == n) (mod p)} <= n0`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `0..2 EXP (2 EXP (k + 1))` THEN
      REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG; LE_0] THEN
      MESON_TAC[];
      MATCH_MP_TAC(REWRITE_RULE[REAL_OF_NUM_LE] (REAL_ARITH
       `!a. &a <= C0 /\ C0 <= &n0 ==> &a <= &n0`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `&(CARD {k | 2 EXP (2 EXP k) <= N} * n0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] CARD_SUBSET)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE];
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `b <= c ==> a <= b ==> a <= c:num`) THEN
    MATCH_MP_TAC CARD_UNIONS_LE THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[HAS_SIZE] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    TRANS_TAC REAL_LE_TRANS `(&2 * (&1 + log(log(&N)))) * &n0` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_POS];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC]]);;
