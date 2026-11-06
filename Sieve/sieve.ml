(* ========================================================================= *)
(* The combinatorial sieve: Rosser's beta-sieve with beta = 2.               *)
(*                                                                           *)
(* A squarefree number d = p_1 p_2 ... p_k (p_1 > ... > p_k) is represented  *)
(* by the finite set t = {p_1,...,p_k} of its prime factors; p_m is the m-th *)
(* largest element of t exactly when CARD {q | q IN t /\ p_m <= q} = m.      *)
(* Rosser's upper and lower sets of level D are                              *)
(*                                                                           *)
(*   rosser_plus D t  : p_1 ... p_m p_m^2 < D for all odd m                  *)
(*   rosser_minus D t : p_1 ... p_m p_m^2 < D for all even m, all p_i < D    *)
(*                                                                           *)
(* and the sieve weights are (-1)^k on these sets and 0 elsewhere.           *)
(* ROSSER_SIEVE shows that they are upper and lower bound sieves             *)
(* (Nathanson, "Additive Number Theory: The Classical Bases", Theorem 9.3),  *)
(* by peeling off the largest prime q:  q t is in the upper set of level D   *)
(* iff q^3 < D and t is in the lower set of level D / q, and dually.         *)
(* ========================================================================= *)

needs "Sieve/primes.ml";;
needs "Library/multiplicative.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Sums over all subsets of a finite set.                                    *)
(* ------------------------------------------------------------------------- *)

let SUM_POWERSET_INSERT = prove
 (`!f:(A->bool)->real a t.
        FINITE t /\ ~(a IN t)
        ==> sum {s | s SUBSET a INSERT t} f =
            sum {s | s SUBSET t} f + sum {s | s SUBSET t} (\s. f(a INSERT s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[POWERSET_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE;
                NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]);;

let FINITE_NUM_MAX = prove
 (`!t:num->bool. FINITE t /\ ~(t = {})
                 ==> ?q. q IN t /\ !r. r IN t ==> r <= q`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\x:num. x IN t` num_MAX) THEN REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[MEMBER_NOT_EMPTY; GSYM num_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* Rosser's sets and weights.                                                *)
(* ------------------------------------------------------------------------- *)

let rosser_plus = new_definition
 `rosser_plus D (t:num->bool) <=>
        !p. p IN t /\ ODD(CARD {q | q IN t /\ p <= q})
            ==> &(nproduct {q | q IN t /\ p <= q} (\q. q) * p EXP 2) < D`;;

let rosser_minus = new_definition
 `rosser_minus D (t:num->bool) <=>
        (!p. p IN t ==> &p < D) /\
        !p. p IN t /\ EVEN(CARD {q | q IN t /\ p <= q})
            ==> &(nproduct {q | q IN t /\ p <= q} (\q. q) * p EXP 2) < D`;;

let rosser_lambda_plus = new_definition
 `rosser_lambda_plus D (t:num->bool) =
        if rosser_plus D t then (-- &1) pow (CARD t) else &0`;;

let rosser_lambda_minus = new_definition
 `rosser_lambda_minus D (t:num->bool) =
        if rosser_minus D t then (-- &1) pow (CARD t) else &0`;;

(* ------------------------------------------------------------------------- *)
(* Peeling off the largest prime.                                            *)
(* ------------------------------------------------------------------------- *)

let TOP_INSERT_MAX_SELF = prove
 (`!t q:num. (!r. r IN t ==> r < q)
             ==> {r | r IN q INSERT t /\ q <= r} = {q}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; IN_SING] THEN
  X_GEN_TAC `r:num` THEN ASM_CASES_TAC `r:num = q` THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[NOT_LT]);;

let TOP_INSERT_MAX_OTHER = prove
 (`!t q p:num. (!r. r IN t ==> r < q) /\ p IN t
           ==> {r | r IN q INSERT t /\ p <= r} =
               q INSERT {r | r IN t /\ p <= r}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
  X_GEN_TAC `r:num` THEN ASM_CASES_TAC `r:num = q` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_IMP_LE]);;

let ROSSER_INSERT_TOP_LEMMA = prove
 (`!t q. FINITE t /\ (!r. r IN t ==> r < q)
         ==> !p. p IN t
                 ==> CARD(q INSERT {r | r IN t /\ p <= r}) =
                     SUC(CARD {r | r IN t /\ p <= r}) /\
                     nproduct (q INSERT {r | r IN t /\ p <= r}) (\q. q) =
                     q * nproduct {r | r IN t /\ p <= r} (\q. q)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; NPRODUCT_CLAUSES; FINITE_RESTRICT;
   IN_ELIM_THM] THEN
  ASM_MESON_TAC[LT_REFL]);;

let ROSSER_PLUS_INSERT = prove
 (`!D q t. FINITE t /\ ~(q = 0) /\ (!r. r IN t ==> r < q)
           ==> (rosser_plus D (q INSERT t) <=>
                &(q EXP 3) < D /\ rosser_minus (D / &q) t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  REWRITE_TAC[rosser_plus; rosser_minus; IMP_CONJ; FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC[TOP_INSERT_MAX_SELF; TOP_INSERT_MAX_OTHER] THEN
  REWRITE_TAC[CARD_SING; NPRODUCT_SING; ARITH] THEN
  ASM_SIMP_TAC[ROSSER_INSERT_TOP_LEMMA] THEN
  ASM_SIMP_TAC[ODD; EVEN; NOT_ODD] THEN
  REWRITE_TAC[ARITH_RULE `q * q EXP 2 = q EXP 3`] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[MULT_AC] THEN
  MATCH_MP_TAC(TAUT `(a ==> c) ==> (a /\ b <=> a /\ c /\ b)`) THEN
  DISCH_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&(q EXP 3)` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(q:num) * q` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL; LE_MULT_LCANCEL] THEN
    ASM_MESON_TAC[LT_IMP_LE];
    REWRITE_TAC[ARITH_RULE `q EXP 3 = (q * q) * q`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `q * q = (q * q) * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]);;

let ROSSER_MINUS_INSERT = prove
 (`!D q t. FINITE t /\ ~(q = 0) /\ (!r. r IN t ==> r < q)
           ==> (rosser_minus D (q INSERT t) <=>
                &q < D /\ rosser_plus (D / &q) t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  REWRITE_TAC[rosser_plus; rosser_minus; IMP_CONJ; FORALL_IN_INSERT] THEN
  ASM_SIMP_TAC[TOP_INSERT_MAX_SELF; TOP_INSERT_MAX_OTHER] THEN
  REWRITE_TAC[CARD_SING; NPRODUCT_SING; ARITH] THEN
  ASM_SIMP_TAC[ROSSER_INSERT_TOP_LEMMA] THEN
  ASM_SIMP_TAC[ODD; EVEN; NOT_EVEN] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[MULT_AC; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) ==> (a /\ b /\ c <=> a /\ c)`) THEN
  DISCH_TAC THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&q` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_MESON_TAC[]);;

let ROSSER_LAMBDA_PLUS_INSERT = prove
 (`!D q t. FINITE t /\ ~(q = 0) /\ (!r. r IN t ==> r < q)
           ==> rosser_lambda_plus D (q INSERT t) =
               if &(q EXP 3) < D then --(rosser_lambda_minus (D / &q) t)
               else &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[rosser_lambda_plus; rosser_lambda_minus;
               ROSSER_PLUS_INSERT] THEN
  SUBGOAL_THEN `~((q:num) IN t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; real_pow] THEN
  MAP_EVERY ASM_CASES_TAC [`&(q EXP 3) < D`; `rosser_minus (D / &q) t`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let ROSSER_LAMBDA_MINUS_INSERT = prove
 (`!D q t. FINITE t /\ ~(q = 0) /\ (!r. r IN t ==> r < q)
           ==> rosser_lambda_minus D (q INSERT t) =
               if &q < D then --(rosser_lambda_plus (D / &q) t)
               else &0`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[rosser_lambda_plus; rosser_lambda_minus;
               ROSSER_MINUS_INSERT] THEN
  SUBGOAL_THEN `~((q:num) IN t)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; real_pow] THEN
  MAP_EVERY ASM_CASES_TAC [`&q < D`; `rosser_plus (D / &q) t`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let ROSSER_LAMBDA_EMPTY = prove
 (`!D. rosser_lambda_plus D {} = &1 /\ rosser_lambda_minus D {} = &1`,
  REWRITE_TAC[rosser_lambda_plus; rosser_lambda_minus; rosser_plus;
              rosser_minus; NOT_IN_EMPTY; CARD_CLAUSES; real_pow]);;

(* ------------------------------------------------------------------------- *)
(* Rosser's weights are upper and lower bound sieves.                        *)
(* ------------------------------------------------------------------------- *)

let LT_CUBE_DIV = prove
 (`!p q D. p < q /\ &(q EXP 3) < D ==> &p < D / &q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&(q EXP 3)` THEN
  ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(q:num) * q` THEN CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    REWRITE_TAC[ARITH_RULE `q EXP 3 = (q * q) * q`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `q * q = (q * q) * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]);;

let ROSSER_SIEVE = prove
 (`!t D. FINITE t /\ ~(0 IN t)
         ==> &0 <= sum {u | u SUBSET t} (rosser_lambda_plus D) /\
             (~(t = {}) /\ (!p. p IN t ==> &p < D)
              ==> sum {u | u SUBSET t} (rosser_lambda_minus D) <= &0)`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(t:num->bool)` THEN
  X_GEN_TAC `D:real` THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:num->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING;
                    ROSSER_LAMBDA_EMPTY] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `t:num->bool` FINITE_NUM_MAX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = (t:num->bool) DELETE q` THEN
  SUBGOAL_THEN `t = (q:num) INSERT s` SUBST_ALL_TAC THENL
   [EXPAND_TAC "s" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((q:num) IN s)` ASSUME_TAC THENL
   [UNDISCH_TAC `(q INSERT s) DELETE (q:num) = s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (s:num->bool) /\ (!r. r IN s ==> r < q) /\
    ~(q = 0) /\ ~(0 IN s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_INSERT];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[LT_LE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[IN_INSERT];
      ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:num->bool` o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[SUM_POWERSET_INSERT] THEN
  SUBGOAL_THEN
   `sum {u | u SUBSET s} (\u. rosser_lambda_plus D (q INSERT u)) =
    (if &(q EXP 3) < D
     then --(sum {u | u SUBSET s} (rosser_lambda_minus (D / &q)))
     else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {u | u SUBSET s}
                 (\u. if &(q EXP 3) < D
                      then --(rosser_lambda_minus (D / &q) u) else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `u:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC ROSSER_LAMBDA_PLUS_INSERT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ASM_MESON_TAC[SUBSET]];
      COND_CASES_TAC THEN REWRITE_TAC[SUM_NEG; SUM_0; ETA_AX]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {u | u SUBSET s} (\u. rosser_lambda_minus D (q INSERT u)) =
    (if &q < D
     then --(sum {u | u SUBSET s} (rosser_lambda_plus (D / &q)))
     else &0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum {u | u SUBSET s}
                 (\u. if &q < D
                      then --(rosser_lambda_plus (D / &q) u) else &0)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `u:num->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC ROSSER_LAMBDA_MINUS_INSERT THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ASM_MESON_TAC[SUBSET]];
      COND_CASES_TAC THEN REWRITE_TAC[SUM_NEG; SUM_0; ETA_AX]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s:num->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; ROSSER_LAMBDA_EMPTY;
                    FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [COND_CASES_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!a b. &0 <= a /\ b <= &0 ==> &0 <= a + --b`) THEN
      CONJ_TAC THENL
       [FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `D:real`) THEN REWRITE_TAC[];
        FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `D / &q`) THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `p:num` THEN DISCH_TAC THEN MATCH_MP_TAC LT_CUBE_DIV THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[REAL_ADD_RID] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `D:real`) THEN REWRITE_TAC[]];
    REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a b. a <= &0 /\ &0 <= b ==> a + --b <= &0`) THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o CONJUNCT2 o SPEC `D:real`) THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o CONJUNCT1 o SPEC `D / &q`) THEN REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Sifting a finite weighted sequence: the general sieve inequality.         *)
(* The sequence is a finite set A with weights a(n) >= 0; s is the set of    *)
(* sifting primes, and sieve_count A a t = |A_d| for d = product of t.       *)
(* ------------------------------------------------------------------------- *)

let sifted = new_definition
 `sifted (A:num->bool) (a:num->real) (s:num->bool) =
        sum {n | n IN A /\ !p. p IN s ==> ~(p divides n)} a`;;

let sieve_count = new_definition
 `sieve_count (A:num->bool) (a:num->real) (t:num->bool) =
        sum {n | n IN A /\ !p. p IN t ==> p divides n} a`;;

let SUM_POWERSET_RESTRICT = prove
 (`!f:(A->bool)->real s u.
        u SUBSET s
        ==> sum {v | v SUBSET u} f =
            sum {t | t SUBSET s} (\t. if t SUBSET u then f t else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RESTRICT_SET] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM SET_TAC[]);;

let SIEVE_INEQUALITY_LEMMA = prove
 (`!A a s lam.
        FINITE A /\ FINITE s
        ==> sum {t | t SUBSET s} (\t. lam t * sieve_count A a t) =
            sum A (\n. a n * sum {v | v SUBSET {p | p IN s /\ p divides n}}
                                 lam)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sieve_count] THEN
  REWRITE_TAC[SUM_RESTRICT_SET; GSYM SUM_LMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\x:num->bool. (a:num->real) n * lam x`; `s:num->bool`;
                 `{p | p IN s /\ p divides n}`] SUM_POWERSET_RESTRICT) THEN
  ANTS_TAC THENL [SET_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `t:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `t SUBSET {p | p IN s /\ p divides n} <=> !p. p IN t ==> p divides n`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_SYM]);;

let SIEVE_UPPER_GENERAL = prove
 (`!A a s lam.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ FINITE s /\
        lam {} = &1 /\
        (!u. u SUBSET s ==> &0 <= sum {v | v SUBSET u} lam)
        ==> sifted A a s <=
            sum {t | t SUBSET s} (\t. lam t * sieve_count A a t)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIEVE_INEQUALITY_LEMMA] THEN
  REWRITE_TAC[sifted; SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{p | p IN s /\ p divides n} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; REAL_MUL_RID;
                    REAL_LE_REFL];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[]]);;

let SIEVE_LOWER_GENERAL = prove
 (`!A a s lam.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\ FINITE s /\
        lam {} = &1 /\
        (!u. u SUBSET s /\ ~(u = {}) ==> sum {v | v SUBSET u} lam <= &0)
        ==> sum {t | t SUBSET s} (\t. lam t * sieve_count A a t) <=
            sifted A a s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIEVE_INEQUALITY_LEMMA] THEN
  REWRITE_TAC[sifted; SUM_RESTRICT_SET] THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `{p | p IN s /\ p divides n} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; REAL_MUL_RID;
                    REAL_LE_REFL];
    REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= a * --b`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_NEG_GE0] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Support and size of Rosser's weights; the sieve bounds with remainder.    *)
(* ------------------------------------------------------------------------- *)

let ROSSER_SUPPORT = prove
 (`!t D. FINITE t /\ ~(0 IN t) /\ ~(t = {})
         ==> (rosser_plus D t ==> &(nproduct t (\q. q)) < D) /\
             (rosser_minus D t ==> &(nproduct t (\q. q)) < D)`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(t:num->bool)` THEN
  X_GEN_TAC `D:real` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `t:num->bool` FINITE_NUM_MAX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s = (t:num->bool) DELETE q` THEN
  SUBGOAL_THEN `t = (q:num) INSERT s` SUBST_ALL_TAC THENL
   [EXPAND_TAC "s" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((q:num) IN s)` ASSUME_TAC THENL
   [UNDISCH_TAC `(q INSERT s) DELETE (q:num) = s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (s:num->bool) /\ (!r. r IN s ==> r < q) /\
    ~(q = 0) /\ ~(0 IN s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_INSERT];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[LT_LE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[IN_INSERT];
      ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:num->bool` o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LT] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[ROSSER_PLUS_INSERT; ROSSER_MINUS_INSERT; NPRODUCT_CLAUSES] THEN
  SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ]; ALL_TAC] THEN
  ASM_CASES_TAC `s:num->bool = {}` THENL
   [ASM_REWRITE_TAC[NPRODUCT_CLAUSES; MULT_CLAUSES] THEN
    CONJ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&(q EXP 3)` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    REWRITE_TAC[ARITH_RULE `q EXP 3 = q * q * q`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `q = q * 1 * 1`] THEN
    REPEAT(MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
  CONJ_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `D / &q`) THEN ASM_MESON_TAC[]);;

let ROSSER_LAMBDA_BOUND = prove
 (`!D t. abs(rosser_lambda_plus D t) <= &1 /\
         abs(rosser_lambda_minus D t) <= &1`,
  REWRITE_TAC[rosser_lambda_plus; rosser_lambda_minus] THEN
  REPEAT GEN_TAC THEN CONJ_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_ABS_POW; REAL_ABS_NEG; REAL_ABS_NUM; REAL_POW_ONE] THEN
  REAL_ARITH_TAC);;

let ROSSER_LAMBDA_SUPPORT = prove
 (`!D t. FINITE t /\ ~(0 IN t) /\ &1 < D
         ==> (~(rosser_lambda_plus D t = &0)
              ==> &(nproduct t (\q. q)) < D) /\
             (~(rosser_lambda_minus D t = &0)
              ==> &(nproduct t (\q. q)) < D)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `t:num->bool = {}` THEN
  ASM_REWRITE_TAC[NPRODUCT_CLAUSES] THEN
  REWRITE_TAC[rosser_lambda_plus; rosser_lambda_minus] THEN
  MP_TAC(SPECL [`t:num->bool`; `D:real`] ROSSER_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let SIEVE_REMAINDER_BOUND = prove
 (`!lam s A a X g D.
        FINITE s /\ (!t. t SUBSET s ==> abs(lam t) <= &1) /\
        (!t. t SUBSET s /\ ~(lam t = &0) ==> &(nproduct t (\q. q)) < D)
        ==> abs(sum {t | t SUBSET s} (\t. lam t * sieve_count A a t) -
                X * sum {t | t SUBSET s} (\t. lam t * product t g))
            <= sum {t | t SUBSET s /\ &(nproduct t (\q. q)) < D}
                   (\t. abs(sieve_count A a t - X * product t g))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB; FINITE_POWERSET] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET s}
                (\t. abs(lam t * (sieve_count A a t - X * product t g)))` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) SUM_ABS o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> c <= a ==> c <= b`) THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {t | t SUBSET s /\ &(nproduct t (\q. q)) < D}
                (\t. abs(lam t * (sieve_count A a t - X * product t g)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_SUPERSET THEN
    CONJ_TAC THENL [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
                    ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `t:num->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(lam:(num->bool)->real) t = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[REAL_MUL_LZERO; REAL_ABS_0]];
    MATCH_MP_TAC SUM_LE THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{t:num->bool | t SUBSET s}` THEN
      ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_ABS_POS]]]);;

let ROSSER_SIEVE_UPPER = prove
 (`!A a s D X g.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\
        FINITE s /\ ~(0 IN s) /\ &1 < D
        ==> sifted A a s <=
            X * sum {t | t SUBSET s}
                    (\t. rosser_lambda_plus D t * product t g) +
            sum {t | t SUBSET s /\ &(nproduct t (\q. q)) < D}
                (\t. abs(sieve_count A a t - X * product t g))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `s:num->bool`;
                 `rosser_lambda_plus D`] SIEVE_UPPER_GENERAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ROSSER_LAMBDA_EMPTY] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`u:num->bool`; `D:real`] ROSSER_SIEVE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rosser_lambda_plus D`; `s:num->bool`; `A:num->bool`;
                 `a:num->real`; `X:real`; `g:num->real`; `D:real`]
         SIEVE_REMAINDER_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ROSSER_LAMBDA_BOUND] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`D:real`; `t:num->bool`] ROSSER_LAMBDA_SUPPORT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!c s1 x g r:real. abs(s1 - x * g) <= r ==> c <= s1 ==> c <= x * g + r`));;

let ROSSER_SIEVE_LOWER = prove
 (`!A a s D X g.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\
        FINITE s /\ ~(0 IN s) /\ &1 < D /\ (!p. p IN s ==> &p < D)
        ==> X * sum {t | t SUBSET s}
                    (\t. rosser_lambda_minus D t * product t g) -
            sum {t | t SUBSET s /\ &(nproduct t (\q. q)) < D}
                (\t. abs(sieve_count A a t - X * product t g))
            <= sifted A a s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `s:num->bool`;
                 `rosser_lambda_minus D`] SIEVE_LOWER_GENERAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ROSSER_LAMBDA_EMPTY] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`u:num->bool`; `D:real`] ROSSER_SIEVE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`rosser_lambda_minus D`; `s:num->bool`; `A:num->bool`;
                 `a:num->real`; `X:real`; `g:num->real`; `D:real`]
         SIEVE_REMAINDER_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ROSSER_LAMBDA_BOUND] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`D:real`; `t:num->bool`] ROSSER_LAMBDA_SUPPORT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!c s1 x g r:real. abs(s1 - x * g) <= r ==> s1 <= c ==> x * g - r <= c`));;

(* ------------------------------------------------------------------------- *)
(* The main terms G+-(D,s) = sum_{t SUBSET s} lambda+-_D(t) prod_{p IN t} g  *)
(* expressed through V(s) = prod_{p IN s} (1 - g p) and the quantities       *)
(* T_n(D,s) of Nathanson's Lemmas 9.3 and 9.4, defined by recursion:         *)
(*   T_1(D,s)     = sum_{p IN s, D <= p^3} g(p) V(s_<p),                     *)
(*   T_{n+1}(D,s) = sum_{p IN s, c_n(p)} g(p) T_n(D/p, s_<p),                *)
(* where c_n(p) is p^3 < D for n even and p < D for n odd.                   *)
(* ------------------------------------------------------------------------- *)

let rosser_T = new_recursive_definition num_RECURSION
 `(rosser_T 0 (g:num->real) D (s:num->bool) = &0) /\
  (rosser_T (SUC n) g D s =
     if n = 0 then
       sum {p | p IN s /\ D <= &(p EXP 3)}
           (\p. g p * product {q | q IN s /\ q < p} (\q. &1 - g q))
     else
       sum {p | p IN s /\ (if EVEN n then &(p EXP 3) < D else &p < D)}
           (\p. g p * rosser_T n g (D / &p) {q | q IN s /\ q < p}))`;;

let ROSSER_T_ZERO = prove
 (`!n g D s. FINITE s /\ CARD s < n ==> rosser_T n g D s = &0`,
  INDUCT_TAC THEN REWRITE_TAC[rosser_T] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `s:num->bool = {}` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0; ARITH_RULE `c < SUC 0 ==> c = 0`];
      REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; SUM_CLAUSES]];
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `p:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `CARD(s:num->bool)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[PSUBSET] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[LT_REFL]]);;

let SUM_INSERT_MAX_LOWER = prove
 (`!c (h:num->(num->bool)->real) q s.
        FINITE s /\ (!r. r IN s ==> r < q)
        ==> sum {p | p IN q INSERT s /\ c p}
                (\p. h p {r | r IN q INSERT s /\ r < p}) =
            sum {p | p IN s /\ c p} (\p. h p {r | r IN s /\ r < p}) +
            (if c q then h q s else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((q:num) IN s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:num. p IN s
            ==> {r | r IN q INSERT s /\ r < p} = {r | r IN s /\ r < p}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    X_GEN_TAC `r:num` THEN ASM_CASES_TAC `r:num = q` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[LT_ANTISYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `{r | r IN (q:num) INSERT s /\ r < q} = s` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    X_GEN_TAC `r:num` THEN ASM_CASES_TAC `r:num = q` THEN
    ASM_REWRITE_TAC[LT_REFL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(c:num->bool) q` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `{p | p IN (q:num) INSERT s /\ (c:num->bool) p} =
      q INSERT {p | p IN s /\ c p}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CLAUSES; FINITE_RESTRICT; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_ADD_SYM] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM];
    REWRITE_TAC[REAL_ADD_RID] THEN
    SUBGOAL_THEN `{p | p IN (q:num) INSERT s /\ (c:num->bool) p} =
                  {p | p IN s /\ c p}`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]]);;

let ROSSER_T_INSERT = prove
 (`!n g D q s.
        FINITE s /\ (!r. r IN s ==> r < q)
        ==> rosser_T (SUC n) g D (q INSERT s) =
            rosser_T (SUC n) g D s +
            (if n = 0
             then if D <= &(q EXP 3)
                  then g q * product s (\r. &1 - g r) else &0
             else if (if EVEN n then &(q EXP 3) < D else &q < D)
                  then g q * rosser_T n g (D / &q) s else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rosser_T] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`\p:num. D <= &(p EXP 3)`;
                   `\p:num t:num->bool.
                       (g:num->real) p * product t (\q. &1 - g q)`;
                   `q:num`; `s:num->bool`] SUM_INSERT_MAX_LOWER);
    MP_TAC(ISPECL [`\p:num. if EVEN n then &(p EXP 3) < D else &p < D`;
                   `\p:num t:num->bool.
                       (g:num->real) p * rosser_T n g (D / &p) t`;
                   `q:num`; `s:num->bool`] SUM_INSERT_MAX_LOWER)] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let SUM_POWERSET_INSERT_WEIGHTED = prove
 (`!(lam:(num->bool)->real) mu c (g:num->real) (q:num) s.
        FINITE s /\ ~(q IN s) /\
        (!t. t SUBSET s ==> lam(q INSERT t) = c * mu t)
        ==> sum {t | t SUBSET q INSERT s} (\t. lam t * product t g) =
            sum {t | t SUBSET s} (\t. lam t * product t g) +
            c * g q * sum {t | t SUBSET s} (\t. mu t * product t g)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SUM_POWERSET_INSERT] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM SUM_LMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(t:num->bool) /\ ~((q:num) IN t)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES] THEN REAL_ARITH_TAC);;

let ROSSER_G_INSERT = prove
 (`!g D q s.
        FINITE s /\ ~(q = 0) /\ (!r. r IN s ==> r < q)
        ==> sum {t | t SUBSET q INSERT s}
                (\t. rosser_lambda_plus D t * product t g) =
            sum {t | t SUBSET s} (\t. rosser_lambda_plus D t * product t g) +
            (if &(q EXP 3) < D then -- &1 else &0) * g q *
            sum {t | t SUBSET s}
                (\t. rosser_lambda_minus (D / &q) t * product t g) /\
            sum {t | t SUBSET q INSERT s}
                (\t. rosser_lambda_minus D t * product t g) =
            sum {t | t SUBSET s} (\t. rosser_lambda_minus D t * product t g) +
            (if &q < D then -- &1 else &0) * g q *
            sum {t | t SUBSET s}
                (\t. rosser_lambda_plus (D / &q) t * product t g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((q:num) IN s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_REFL]; ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_POWERSET_INSERT_WEIGHTED THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:num->bool` THEN DISCH_TAC THEN
  (SUBGOAL_THEN `FINITE(t:num->bool) /\ (!r. r IN t ==> r < q)`
   STRIP_ASSUME_TAC THENL
    [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
   ASM_SIMP_TAC[ROSSER_LAMBDA_PLUS_INSERT; ROSSER_LAMBDA_MINUS_INSERT] THEN
   COND_CASES_TAC THEN REAL_ARITH_TAC));;

let ROSSER_TODD_INSERT = prove
 (`!g D q s N.
        FINITE s /\ (!r. r IN s ==> r < q)
        ==> sum (0..N) (\k. rosser_T (2 * k + 1) g D (q INSERT s)) =
            sum (0..N) (\k. rosser_T (2 * k + 1) g D s) +
            (if D <= &(q EXP 3) then g q * product s (\r. &1 - g r)
             else &0) +
            (if &(q EXP 3) < D
             then g q * sum (1..N) (\k. rosser_T (2 * k) g (D / &q) s)
             else &0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ARITH_RULE `2 * k + 1 = SUC(2 * k)`] THEN
  ASM_SIMP_TAC[ROSSER_T_INSERT; SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[GSYM REAL_ADD_ASSOC; REAL_EQ_ADD_LCANCEL] THEN
  SIMP_TAC[SUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[MULT_CLAUSES; REAL_EQ_ADD_LCANCEL] THEN
  SIMP_TAC[ADD_CLAUSES; MULT_EQ_0; ARITH_EQ; EVEN_MULT; ARITH_EVEN] THEN
  SUBGOAL_THEN `!k. k IN 1..N ==> ~(2 * k = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (1..N) (\k. if &(q EXP 3) < D
                              then g q * rosser_T (2 * k) g (D / &q) s
                              else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[SUM_LMUL; SUM_0]]);;

let ROSSER_TEVEN_INSERT = prove
 (`!g D q s N.
        FINITE s /\ (!r. r IN s ==> r < q) /\ 1 <= N
        ==> sum (1..N) (\k. rosser_T (2 * k) g D (q INSERT s)) =
            sum (1..N) (\k. rosser_T (2 * k) g D s) +
            (if &q < D
             then g q * sum (0..N-1) (\k. rosser_T (2 * k + 1) g (D / &q) s)
             else &0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum (1..N) (\k. rosser_T (2 * k) g D s +
                              (if &q < D
                               then g q * rosser_T (2 * k - 1) g (D / &q) s
                               else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN
    MP_TAC(SPECL [`2 * k - 1`; `g:num->real`; `D:real`; `q:num`;
                  `s:num->bool`] ROSSER_T_INSERT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC(2 * k - 1) = 2 * k` SUBST1_TAC THENL
     [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `~(2 * k - 1 = 0) /\ ~EVEN(2 * k - 1)`
    (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[NOT_EVEN; ODD_SUB; ODD_MULT; ARITH_ODD] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; REAL_EQ_ADD_LCANCEL] THEN
  COND_CASES_TAC THEN REWRITE_TAC[SUM_0; SUM_LMUL] THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`1`; `\k. rosser_T (2 * k - 1) g (D / &q) (s:num->bool)`;
                 `0`; `N - 1`] SUM_OFFSET) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= N ==> N - 1 + 1 = N`; ADD_CLAUSES] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let ROSSER_BUCHSTAB_IDENTITY = prove
 (`!s g D N.
        FINITE s /\ ~(0 IN s) /\ CARD s <= N
        ==> sum {t | t SUBSET s} (\t. rosser_lambda_plus D t * product t g) =
            product s (\p. &1 - g p) +
            sum (0..N) (\k. rosser_T (2 * k + 1) g D s) /\
            ((!p. p IN s ==> &p < D)
             ==> sum {t | t SUBSET s}
                     (\t. rosser_lambda_minus D t * product t g) =
                 product s (\p. &1 - g p) -
                 sum (1..N) (\k. rosser_T (2 * k) g D s))`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(s:num->bool)` THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:num->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; ROSSER_LAMBDA_EMPTY;
                    PRODUCT_CLAUSES; REAL_MUL_LID] THEN
    SUBGOAL_THEN `!n. 0 < n ==> rosser_T n g D {} = &0` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC ROSSER_T_ZERO THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_EQ_0_NUMSEG; ARITH_RULE `0 < 2 * k + 1`;
                 ARITH_RULE `1 <= k ==> 0 < 2 * k`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:num->bool` FINITE_NUM_MAX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `s' = (s:num->bool) DELETE q` THEN
  SUBGOAL_THEN `s = (q:num) INSERT s'` SUBST_ALL_TAC THENL
   [EXPAND_TAC "s'" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((q:num) IN s')` ASSUME_TAC THENL
   [UNDISCH_TAC `(q INSERT s') DELETE (q:num) = s'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (s':num->bool) /\ (!r. r IN s' ==> r < q) /\
    ~(q = 0) /\ ~(0 IN s')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_INSERT];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[LT_LE] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[IN_INSERT];
      ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s':num->bool` o check (is_forall o concl)) THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LT] THEN DISCH_THEN(LABEL_TAC "IH") THEN
  SUBGOAL_THEN `1 <= N /\ CARD(s':num->bool) <= N - 1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD((q:num) INSERT s') <= N` THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ROSSER_G_INSERT; ROSSER_TODD_INSERT; ROSSER_TEVEN_INSERT;
               PRODUCT_CLAUSES] THEN
  CONJ_TAC THENL
   [USE_THEN "IH" (MP_TAC o SPECL [`g:num->real`; `D:real`; `N:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [USE_THEN "IH" (MP_TAC o SPECL [`g:num->real`; `D / &q`; `N:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN ANTS_TAC THENL
       [X_GEN_TAC `p:num` THEN DISCH_TAC THEN MATCH_MP_TAC LT_CUBE_DIV THEN
        ASM_SIMP_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[REAL_ARITH `x < y ==> ~(y <= x)`] THEN
      ABBREV_TAC `V = product s' (\p. &1 - (g:num->real) p)` THEN
      REAL_ARITH_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
      ABBREV_TAC `V = product s' (\p. &1 - (g:num->real) p)` THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "IH" (MP_TAC o SPECL [`g:num->real`; `D:real`; `N:num`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    USE_THEN "IH" (MP_TAC o SPECL [`g:num->real`; `D / &q`; `N - 1`]) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
    ABBREV_TAC `V = product s' (\p. &1 - (g:num->real) p)` THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Extending a sieve on s1 by the full Mobius function on a finite set q of  *)
(* further (small) primes ([N] Lemma 9.1, Theorem 9.2): the weights          *)
(* lambda*(t) = lambda(t INTER s1) (-1)^|t DIFF s1| sieve s1 UNION q, with   *)
(* main term G(s1) prod_{p IN q} (1 - g p) and support level D prod q.       *)
(* ------------------------------------------------------------------------- *)

let SUM_POWERSET_SIGN = prove
 (`!w:A->bool. FINITE w
               ==> sum {v | v SUBSET w} (\v. (-- &1) pow (CARD v)) =
                   if w = {} then &1 else &0`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; CARD_CLAUSES; real_pow];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `w:A->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_POWERSET_INSERT; NOT_INSERT_EMPTY] THEN
  SUBGOAL_THEN
   `sum {v | v SUBSET w} (\v. (-- &1) pow CARD((a:A) INSERT v)) =
    --(sum {v | v SUBSET w} (\v. (-- &1) pow CARD v))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `v:A->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(v:A->bool) /\ ~((a:A) IN v)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let SUM_POWERSET_DISJOINT_UNION = prove
 (`!u1 u2 (f:(A->bool)->real) h.
        FINITE u1 /\ FINITE u2 /\ DISJOINT u1 u2
        ==> sum {v | v SUBSET u1 UNION u2}
                (\v. f(v INTER u1) * h(v INTER u2)) =
            sum {v | v SUBSET u1} f * sum {v | v SUBSET u2} h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!w. FINITE w
        ==> DISJOINT (u1:A->bool) w
            ==> !k. sum {v | v SUBSET u1 UNION w}
                        (\v. f(v INTER u1) * k(v INTER w)) =
                    sum {v | v SUBSET u1} f * sum {v | v SUBSET w} k`
  (fun th -> ASM_SIMP_TAC[th]) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[UNION_EMPTY; INTER_EMPTY; SUBSET_EMPTY; SING_GSPEC;
                SUM_SING] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `w:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "IH") STRIP_ASSUME_TAC) THEN
  DISCH_TAC THEN X_GEN_TAC `k:(A->bool)->real` THEN
  SUBGOAL_THEN `DISJOINT (u1:A->bool) w /\ ~(x IN u1)` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `u1 UNION (x:A) INSERT w = x INSERT (u1 UNION w)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_POWERSET_INSERT; FINITE_UNION; IN_UNION] THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  USE_THEN "IH" (fun th ->
    let th' = MP th (ASSUME `DISJOINT (u1:A->bool) w`) in
    MP_TAC(SPEC `k:(A->bool)->real` th') THEN
    MP_TAC(SPEC `\v. (k:(A->bool)->real)(x INSERT v)` th')) THEN
  REWRITE_TAC[] THEN REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  BINOP_TAC THEN MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `v:A->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

let SUM_POWERSET_SIGN_PRODUCT = prove
 (`!(g:num->real) w.
        FINITE w
        ==> sum {v | v SUBSET w} (\v. (-- &1) pow (CARD v) * product v g) =
            product w (\q. &1 - g q)`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_EMPTY; SING_GSPEC; SUM_SING; CARD_CLAUSES; real_pow;
                PRODUCT_CLAUSES] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `w:num->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_POWERSET_INSERT; PRODUCT_CLAUSES] THEN
  SUBGOAL_THEN
   `sum {v | v SUBSET w}
        (\v. (-- &1) pow CARD((a:num) INSERT v) *
             product (a INSERT v) (g:num->real)) =
    --(g a) * sum {v | v SUBSET w} (\v. (-- &1) pow (CARD v) * product v g)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `v:num->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(v:num->bool) /\ ~((a:num) IN v)` STRIP_ASSUME_TAC
    THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; PRODUCT_CLAUSES; real_pow] THEN REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let PRODUCT_INTER_UNION = prove
 (`!(g:num->real) s1 q t.
        FINITE t /\ DISJOINT s1 q /\ t SUBSET s1 UNION q
        ==> product t g = product (t INTER s1) g * product (t INTER q) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = (t INTER s1) UNION (t INTER q:num->bool)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [th]) THEN
  MATCH_MP_TAC PRODUCT_UNION THEN
  ASM_SIMP_TAC[FINITE_INTER] THEN ASM SET_TAC[]);;

let sieve_extend = new_definition
 `sieve_extend (lam:(num->bool)->real) s1 (t:num->bool) =
        lam(t INTER s1) * (-- &1) pow CARD(t DIFF s1)`;;

let SIEVE_EXTEND_SUBSET_SUM = prove
 (`!lam s1 q u.
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q /\ u SUBSET s1 UNION q
        ==> sum {v | v SUBSET u} (sieve_extend lam s1) =
            sum {v | v SUBSET u INTER s1} lam *
            (if u INTER q = {} then &1 else &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(u INTER s1:num->bool) /\ FINITE(u INTER q:num->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_INTER]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SUM_POWERSET_SIGN] THEN
  W(MP_TAC o PART_MATCH (rand o rand) SUM_POWERSET_DISJOINT_UNION o
    rand o snd) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `(u INTER s1) UNION (u INTER q) = u:num->bool` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; sieve_extend] THEN DISCH_TAC THEN
  BINOP_TAC THENL [AP_TERM_TAC; AP_TERM_TAC THEN AP_TERM_TAC] THEN
  ASM SET_TAC[]);;

let SIEVE_EXTEND_EMPTY = prove
 (`!lam s1. sieve_extend lam s1 {} = lam {}`,
  REWRITE_TAC[sieve_extend; INTER_EMPTY; EMPTY_DIFF; CARD_CLAUSES; real_pow;
              REAL_MUL_RID]);;

let SIEVE_EXTEND_UPPER = prove
 (`!lam s1 q.
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q /\
        (!u. u SUBSET s1 ==> &0 <= sum {v | v SUBSET u} lam)
        ==> !u. u SUBSET s1 UNION q
                ==> &0 <= sum {v | v SUBSET u} (sieve_extend lam s1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIEVE_EXTEND_SUBSET_SUM] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let SIEVE_EXTEND_LOWER = prove
 (`!lam s1 q.
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q /\
        (!u. u SUBSET s1 /\ ~(u = {}) ==> sum {v | v SUBSET u} lam <= &0)
        ==> !u. u SUBSET s1 UNION q /\ ~(u = {})
                ==> sum {v | v SUBSET u} (sieve_extend lam s1) <= &0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SIEVE_EXTEND_SUBSET_SUM] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

let SIEVE_EXTEND_MAIN = prove
 (`!lam (g:num->real) s1 q.
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q
        ==> sum {t | t SUBSET s1 UNION q}
                (\t. sieve_extend lam s1 t * product t g) =
            sum {t | t SUBSET s1} (\t. lam t * product t g) *
            product q (\p. &1 - g p)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM SUM_POWERSET_SIGN_PRODUCT] THEN
  W(MP_TAC o PART_MATCH (rand o rand) SUM_POWERSET_DISJOINT_UNION o
    rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `t:num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; sieve_extend] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:num->real`; `s1:num->bool`; `q:num->bool`;
                 `t:num->bool`] PRODUCT_INTER_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `t DIFF s1 = t INTER q:num->bool` SUBST1_TAC THENL
   [ASM SET_TAC[]; REAL_ARITH_TAC]);;

let SIEVE_EXTEND_SUPPORT = prove
 (`!lam s1 q D t.
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q /\ ~(0 IN q) /\
        t SUBSET s1 UNION q /\ ~(sieve_extend lam s1 t = &0) /\
        (!u. u SUBSET s1 /\ ~(lam u = &0) ==> &(nproduct u (\p. p)) < D)
        ==> &(nproduct t (\p. p)) < D * &(nproduct q (\p. p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&(nproduct (t INTER s1) (\p. p)) < D` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~(sieve_extend lam s1 t = &0)` THEN
    REWRITE_TAC[sieve_extend] THEN MESON_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(t:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w SUBSET q ==> &1 <= &(nproduct w (\p:num. p))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> 0 < n`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[LT_NZ] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nproduct t (\p:num. p) =
    nproduct (t INTER s1) (\p. p) * nproduct (t INTER q) (\p. p) /\
    nproduct q (\p:num. p) =
    nproduct (t INTER q) (\p. p) * nproduct (q DIFF t) (\p. p)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC EQ_TRANS THENL
     [EXISTS_TAC `nproduct ((t INTER s1) UNION (t INTER q)) (\p:num. p)`;
      EXISTS_TAC `nproduct ((t INTER q) UNION (q DIFF t)) (\p:num. p)`] THEN
    (CONJ_TAC THENL
      [AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
       MATCH_MP_TAC NPRODUCT_UNION THEN
       ASM_SIMP_TAC[FINITE_INTER; FINITE_DIFF] THEN ASM SET_TAC[]]);
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `D * &(nproduct (t INTER q) (\p:num. p))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&1` THEN
    REWRITE_TAC[REAL_LT_01] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `&(nproduct (t INTER s1) (\p:num. p))` THEN
      ASM_REWRITE_TAC[REAL_POS];
      REWRITE_TAC[REAL_POS]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN SET_TAC[]]);;

let SIEVE_EXTEND_BOUND = prove
 (`!lam s1 t. (!u. abs(lam u) <= &1) ==> abs(sieve_extend lam s1 t) <= &1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[sieve_extend; REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NEG;
              REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_RID] THEN
  ASM_REWRITE_TAC[]);;

let ROSSER_SIEVE_UPPER_EXTENDED = prove
 (`!A a s1 q D X g.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q /\
        ~(0 IN s1) /\ ~(0 IN q) /\ &1 < D
        ==> sifted A a (s1 UNION q) <=
            X * sum {t | t SUBSET s1}
                    (\t. rosser_lambda_plus D t * product t g) *
                product q (\p. &1 - g p) +
            sum {t | t SUBSET s1 UNION q /\
                     &(nproduct t (\p. p)) < D * &(nproduct q (\p. p))}
                (\t. abs(sieve_count A a t - X * product t g))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s1 UNION q:num->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `s1 UNION q:num->bool`;
                 `sieve_extend (rosser_lambda_plus D) s1`]
         SIEVE_UPPER_GENERAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SIEVE_EXTEND_EMPTY; ROSSER_LAMBDA_EMPTY] THEN
    MATCH_MP_TAC SIEVE_EXTEND_UPPER THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`u:num->bool`; `D:real`] ROSSER_SIEVE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sieve_extend (rosser_lambda_plus D) s1`;
                 `s1 UNION q:num->bool`; `A:num->bool`; `a:num->real`;
                 `X:real`; `g:num->real`; `D * &(nproduct q (\p:num. p))`]
         SIEVE_REMAINDER_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SIEVE_EXTEND_BOUND; ROSSER_LAMBDA_BOUND] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIEVE_EXTEND_SUPPORT THEN
    EXISTS_TAC `rosser_lambda_plus D` THEN EXISTS_TAC `s1:num->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`D:real`; `u:num->bool`] ROSSER_LAMBDA_SUPPORT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_EXTEND_MAIN] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!c s x g v r:real.
        abs(s - x * g * v) <= r ==> c <= s ==> c <= x * g * v + r`));;

let ROSSER_SIEVE_LOWER_EXTENDED = prove
 (`!A a s1 q D X g.
        FINITE A /\ (!n. n IN A ==> &0 <= a n) /\
        FINITE s1 /\ FINITE q /\ DISJOINT s1 q /\
        ~(0 IN s1) /\ ~(0 IN q) /\ &1 < D /\ (!p. p IN s1 ==> &p < D)
        ==> X * sum {t | t SUBSET s1}
                    (\t. rosser_lambda_minus D t * product t g) *
                product q (\p. &1 - g p) -
            sum {t | t SUBSET s1 UNION q /\
                     &(nproduct t (\p. p)) < D * &(nproduct q (\p. p))}
                (\t. abs(sieve_count A a t - X * product t g))
            <= sifted A a (s1 UNION q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s1 UNION q:num->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:num->bool`; `a:num->real`; `s1 UNION q:num->bool`;
                 `sieve_extend (rosser_lambda_minus D) s1`]
         SIEVE_LOWER_GENERAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SIEVE_EXTEND_EMPTY; ROSSER_LAMBDA_EMPTY] THEN
    MATCH_MP_TAC SIEVE_EXTEND_LOWER THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`u:num->bool`; `D:real`] ROSSER_SIEVE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sieve_extend (rosser_lambda_minus D) s1`;
                 `s1 UNION q:num->bool`; `A:num->bool`; `a:num->real`;
                 `X:real`; `g:num->real`; `D * &(nproduct q (\p:num. p))`]
         SIEVE_REMAINDER_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[SIEVE_EXTEND_BOUND; ROSSER_LAMBDA_BOUND] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SIEVE_EXTEND_SUPPORT THEN
    EXISTS_TAC `rosser_lambda_minus D` THEN EXISTS_TAC `s1:num->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`D:real`; `u:num->bool`] ROSSER_LAMBDA_SUPPORT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SIEVE_EXTEND_MAIN] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH
   `!c s x g v r:real.
        abs(s - x * g * v) <= r ==> s <= c ==> x * g * v - r <= c`));;
