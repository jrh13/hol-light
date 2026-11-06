(* ========================================================================= *)
(* Chen's weights ([N] Theorem 10.2), for any shift h.                       *)
(*                                                                           *)
(* For n with all prime factors >= z = N^(1/8) and n < N = y^3, y = N^(1/3), *)
(*   nu(n)  = #{(q,k) | q prime, z <= q < y, k >= 1, q^k | n}   (chen_nu),   *)
(*   tau(n) = [n = p1 p2 p3, z <= p1 < y <= p2 <= p3]   (chen_triple);       *)
(* CHEN_WEIGHT_P2: for n > 1, nu(n) + tau(n) <= 1 implies that n is a prime  *)
(* or a product of two primes (almost_prime 2, see ALMOST_PRIME_2).  Summing *)
(* the weight 1 - nu/2 - tau/2 over the sifted A = gchen_A h N (n = 1 costs  *)
(* at most 1) gives CHEN_WEIGHTS_GEN: for even N > 256 and every h,          *)
(*   S(A,P,z) - 1/2 sum_{z <= q < y} S(A_q,P,z) - 1/2 S_B                    *)
(*     <= #{n in A | n = P2} + 3 N/z + 2 y,                                  *)
(* where S_B counts the triples of chen_T h N (z <= p1 < y <= p2 <= p3,      *)
(* p1 p2 p3 < N, coprime to h) with |h - p1 p2 p3| free of primes < y: a     *)
(* triple n = p1 p2 p3 in A has |h - n| prime, so it is counted by S_B       *)
(* unless |h - n| < y (at most 2 y + 2 such n).  Prime powers q^k, k >= 2,   *)
(* cost at most sum_q 2N/q^2 <= 6N/z (GEOM_TAIL_INV,                         *)
(* SUM_PRIME_SQUARES_TAIL).  No unique factorisation is used.                *)
(* ========================================================================= *)

needs "Sieve/chen_lower.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Almost primes of order two; small lemmas.                                 *)
(* ------------------------------------------------------------------------- *)

let ALMOST_PRIME_2 = prove
 (`!n. almost_prime 2 n <=>
       prime n \/ ?p q. prime p /\ prime q /\ n = p * q`,
  GEN_TAC THEN REWRITE_TAC[almost_prime] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `l:num list` STRIP_ASSUME_TAC) THEN
    POP_ASSUM(SUBST1_TAC o SYM) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    STRUCT_CASES_TAC(ISPEC `l:num list` list_CASES) THEN
    REWRITE_TAC[ALL; ITLIST; LENGTH; NOT_CONS_NIL] THEN
    STRUCT_CASES_TAC(ISPEC `t:num list` list_CASES) THEN
    REWRITE_TAC[ALL; ITLIST; LENGTH; MULT_CLAUSES] THENL
     [MESON_TAC[]; ALL_TAC] THEN
    STRUCT_CASES_TAC(ISPEC `t':num list` list_CASES) THEN
    REWRITE_TAC[ALL; ITLIST; LENGTH; MULT_CLAUSES] THENL
     [MESON_TAC[]; ARITH_TAC];
    STRIP_TAC THENL
     [EXISTS_TAC `[n:num]` THEN
      ASM_REWRITE_TAC[ALL; ITLIST; LENGTH; MULT_CLAUSES; NOT_CONS_NIL] THEN
      ARITH_TAC;
      EXISTS_TAC `[p:num; q]` THEN
      ASM_REWRITE_TAC[ALL; ITLIST; LENGTH; MULT_CLAUSES; NOT_CONS_NIL] THEN
      ARITH_TAC]]);;

let CARD_GE_2 = prove
 (`!s a b:A. FINITE s /\ a IN s /\ b IN s /\ ~(a = b) ==> 2 <= CARD s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {a:A,b}` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    ARITH_TAC;
    MATCH_MP_TAC CARD_SUBSET THEN ASM SET_TAC[]]);;

let LE_MULT_NZ = prove
 (`(!a b. ~(b = 0) ==> a <= a * b) /\ (!a b. ~(b = 0) ==> a <= b * a)`,
  CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`a:num`; `1`; `b:num`] LE_MULT_LCANCEL);
    MP_TAC(SPECL [`1`; `b:num`; `a:num`] LE_MULT_RCANCEL)] THEN
  REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC);;

let FINITE_NUM_LT_REAL = prove
 (`!y. FINITE {p:num | &p < y}`,
  GEN_TAC THEN MP_TAC(SPEC `y:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p:num | p < n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; GSYM REAL_OF_NUM_LT] THEN
  ASM_MESON_TAC[REAL_LTE_TRANS]);;

let CARD_NUM_LT_REAL = prove
 (`!y. &0 <= y ==> &(CARD {p:num | &p < y}) <= y + &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_TAC `n:num` o MATCH_MP FLOOR_POS) THEN
  MP_TAC(SPEC `y:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(n + 1)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {p:num | p < n + 1}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
      DISCH_TAC THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[CARD_NUMSEG_LT; LE_REFL]];
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC]);;

let GEOM_TAIL_INV = prove
 (`!q M. 2 <= q ==> sum(2..M) (\k. inv(&q pow k)) <= &2 / &q pow 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_POW_INV; SUM_GP] THEN
  SUBGOAL_THEN `&0 < inv(&q) /\ inv(&q) <= &1 / &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ONCE_REWRITE_TAC[GSYM REAL_INV_DIV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 / &q pow 2 = &2 * inv(&q) pow 2` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_POW_INV; real_div]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = inv(&q)` THEN
  SUBGOAL_THEN `&0 < &1 - x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= x pow SUC M` MP_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `x pow 2 <= (&2 * x pow 2) * (&1 - x)` MP_TAC THENL
   [REWRITE_TAC[REAL_ARITH `(&2 * a) * (&1 - x) = a + a * (&1 - &2 * x)`] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b:real. &0 <= b ==> a <= a + b`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
                    ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let IN_ELIM_TRIPLE = prove
 (`!P a:A b:B c:C. (a,b,c) IN {x,y,z | P x y z} <=> P a b c`,
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The weights.                                                              *)
(* ------------------------------------------------------------------------- *)

let chen_nu = new_definition
 `chen_nu z y n =
    CARD {q,k | prime q /\ z <= &q /\ &q < y /\ 1 <= k /\
                q EXP k divides n}`;;

let chen_triple = new_definition
 `chen_triple z y n <=>
    ?p1 p2 p3. prime p1 /\ prime p2 /\ prime p3 /\
               z <= &p1 /\ &p1 < y /\ y <= &p2 /\ p2 <= p3 /\
               n = p1 * p2 * p3`;;

let FINITE_CHEN_NU = prove
 (`!z y n. ~(n = 0)
           ==> FINITE {q,k | prime q /\ z <= &q /\ &q < y /\ 1 <= k /\
                             q EXP k divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(0..n) CROSS (0..n)` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
              IN_NUMSEG; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `q EXP k <= n` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIVIDES_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= q` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q EXP k` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP k` THEN REWRITE_TAC[LT_POW2_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `q EXP k` THEN
    ASM_REWRITE_TAC[EXP_MONO_LE]]);;

let CHEN_NU_SUM = prove
 (`!z y N n.
        ~(n = 0) /\ n < N
        ==> &(chen_nu z y n) =
            sum {q | prime q /\ z <= &q /\ &q < y}
                (\q. sum(1..N) (\k. if q EXP k divides n then &1 else &0))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chen_nu] THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  SUBGOAL_THEN `FINITE(Q:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{q | prime q /\ &q < y}` THEN
    REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `{q,k | prime q /\ z <= &q /\ &q < y /\ 1 <= k /\ q EXP k divides n} =
    {x | x IN {i,j | i IN Q /\ j IN 1..N} /\ FST x EXP SND x divides n}`
  SUBST1_TAC THENL
   [EXPAND_TAC "Q" THEN
    REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_ELIM_THM;
                IN_NUMSEG] THEN
    MAP_EVERY X_GEN_TAC [`q:num`; `k:num`] THEN
    ASM_CASES_TAC `q EXP k divides n` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q EXP k <= n /\ 2 <= q` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[DIVIDES_LE; PRIME_GE_2]; ALL_TAC] THEN
    MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN
    SUBGOAL_THEN `2 EXP k <= q EXP k` MP_TAC THENL
     [ASM_REWRITE_TAC[EXP_MONO_LE]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {i,j | (i:num) IN Q /\ (j:num) IN 1..N}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN MATCH_MP_TAC SUM_EQ THEN
  REWRITE_TAC[FORALL_PAIR_THM]);;

let CHEN_WEIGHT_P2 = prove
 (`!z y N n.
        &1 <= z /\ z <= y /\ &N <= y pow 3 /\ ~(n = 0) /\ ~(n = 1) /\
        n < N /\ (!q. prime q /\ q divides n ==> z <= &q) /\
        chen_nu z y n + (if chen_triple z y n then 1 else 0) <= 1
        ==> almost_prime 2 n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `?q. prime q /\ z <= &q /\ &q < y /\ q divides n` THENL
   [ALL_TAC;
    MATCH_MP_TAC ALMOST_PRIME_LARGE_FACTORS THEN EXISTS_TAC `y:real` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LT];
      X_GEN_TAC `q:num` THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(?q. prime q /\ z <= &q /\ &q < y /\ q divides n)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `q:num` THEN ASM_SIMP_TAC[]]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `q0:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Ks = {q,k | prime q /\ z <= &q /\ &q < y /\ 1 <= k /\
                         q EXP k divides n}` THEN
  SUBGOAL_THEN `!r. prime r /\ z <= &r /\ &r < y /\ r divides n
                    ==> (r:num,1) IN Ks`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "Ks" THEN
    ASM_REWRITE_TAC[IN_ELIM_PAIR_THM; EXP_1; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Ks:num#num->bool) /\ CARD Ks <= 1 /\
                ~(chen_triple z y n)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE(Ks:num#num->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Ks" THEN MATCH_MP_TAC FINITE_CHEN_NU THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `1 <= CARD(Ks:num#num->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[CARD_EQ_0] THEN
      SUBGOAL_THEN `(q0:num,1) IN Ks` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC
     `chen_nu z y n + (if chen_triple z y n then 1 else 0) <= 1` THEN
    ASM_REWRITE_TAC[chen_nu] THEN COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:num#num. a IN Ks /\ b IN Ks ==> a = b` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`Ks:num#num->bool`; `a:num#num`;
                                  `b:num#num`] CARD_GE_2) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. prime r /\ z <= &r /\ &r < y /\ r divides n ==> r = q0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(r:num,1)`; `(q0:num,1)`]) THEN
    REWRITE_TAC[PAIR_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q0 EXP 2 divides n)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(q0:num,1)`; `(q0:num,2)`] o check
     (fun th -> can (find_term ((=) `Ks:num#num->bool`)) (concl th) &&
                is_forall(concl th) &&
                not(can (find_term ((=) `chen_triple`)) (concl th)))) THEN
    REWRITE_TAC[PAIR_EQ] THEN CONV_TAC NUM_REDUCE_CONV THEN
    EXPAND_TAC "Ks" THEN REWRITE_TAC[IN_ELIM_PAIR_THM; EXP_1] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides] o
    check (fun th -> concl th = `q0 divides n`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `~(m = 0) /\ ~(q0 divides m) /\ 2 <= q0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(q0 * m = 0)` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES];
      DISCH_TAC THEN UNDISCH_TAC `~(q0 EXP 2 divides q0 * m)` THEN
      REWRITE_TAC[EXP_2] THEN ASM_SIMP_TAC[DIVIDES_MUL_L];
      MATCH_MP_TAC PRIME_GE_2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. prime r /\ r divides m ==> y <= &r` ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `r divides q0 * m` ASSUME_TAC THENL
     [MATCH_MP_TAC DIVIDES_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `r:num = q0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `q0:num`)) (concl th) &&
        not(can (find_term ((=) `Ks:num#num->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ALMOST_PRIME_2]; ALL_TAC] THEN
  SUBGOAL_THEN `almost_prime 2 m` MP_TAC THENL
   [MATCH_MP_TAC ALMOST_PRIME_LARGE_FACTORS THEN EXISTS_TAC `y:real` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&N` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `q0 * m:num` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m`] THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ALMOST_PRIME_2] THEN STRIP_TAC THENL
   [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`q0:num`; `m:num`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(chen_triple z y (q0 * m))` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    ASM_REWRITE_TAC[chen_triple] THEN
    SUBGOAL_THEN `y <= &p /\ y <= &q` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `m:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL];
      ALL_TAC] THEN
    DISJ_CASES_TAC(ARITH_RULE `p <= q \/ q <= p:num`) THENL
     [MAP_EVERY EXISTS_TAC [`q0:num`; `p:num`; `q:num`];
      MAP_EVERY EXISTS_TAC [`q0:num`; `q:num`; `p:num`]] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The triples of B and the weighted inequality.                             *)
(* ------------------------------------------------------------------------- *)

let chen_T = new_definition
 `chen_T h N =
    {p1,p2,p3 | prime p1 /\ prime p2 /\ prime p3 /\
                exp(&1 / &8 * log(&N)) <= &p1 /\
                &p1 < exp(&1 / &3 * log(&N)) /\
                exp(&1 / &3 * log(&N)) <= &p2 /\ p2 <= p3 /\
                p1 * p2 * p3 < N /\ coprime(p1 * p2 * p3,h)}`;;

let FINITE_CHEN_T = prove
 (`!h N. FINITE(chen_T h N)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(0..N) CROSS ((0..N) CROSS (0..N))` THEN
  SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; chen_T; IN_ELIM_THM; PAIR_EQ;
              IN_CROSS; IN_NUMSEG; LE_0] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `c:num`] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `p2:num`
    (X_CHOOSE_THEN `p3:num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(p1 = 0) /\ ~(p2 = 0) /\ ~(p3 = 0)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `~(p2 * p3 = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MULT_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `p1 <= p1 * p2 * p3 /\ p2 <= p1 * p2 * p3 /\
                p3 <= p1 * p2 * (p3:num)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1 LE_MULT_NZ) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p2 * p3:num` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(CONJUNCT1 LE_MULT_NZ);
        MATCH_MP_TAC(CONJUNCT2 LE_MULT_NZ)] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p2 * p3:num` THEN
      CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT2 LE_MULT_NZ) THEN
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `p1 * p2 * p3 < N:num` THEN ARITH_TAC]);;

let CHEN_WEIGHTS_GEN = prove
 (`!h N. EVEN N /\ 256 < N
       ==> sifted (gchen_A h N) (\n. &1)
                  {p | prime p /\ &p < exp(&1 / &8 * log(&N))} -
           &1 / &2 *
           sum {q | prime q /\ exp(&1 / &8 * log(&N)) <= &q /\
                    &q < exp(&1 / &3 * log(&N))}
               (\q. sifted (gchen_A h N)
                           (\n. if q divides n then &1 else &0)
                           {p | prime p /\ &p < exp(&1 / &8 * log(&N))}) -
           &1 / &2 *
           &(CARD {p1,p2,p3 | (p1,p2,p3) IN chen_T h N /\
                              !q. prime q /\ &q < exp(&1 / &3 * log(&N))
                                  ==> ~(q divides
                                        chen_dist h (p1 * p2 * p3))})
           <= &(CARD {n | n IN gchen_A h N /\ almost_prime 2 n}) +
              &3 * &N / exp(&1 / &8 * log(&N)) +
              &2 * exp(&1 / &3 * log(&N))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&8 * log(&2) <= log(&N) /\ &0 < log(&N) /\ &0 < &N`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[GSYM LOG_POW; REAL_ARITH `&0 < &2`] THEN
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN
      REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      MATCH_MP_TAC LOG_POS_LT THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `LN = log(&N)` THEN
  SUBGOAL_THEN
   `&2 <= exp(&1 / &8 * LN) /\ exp(&1 / &8 * LN) <= exp(&1 / &3 * LN) /\
    &N <= exp(&1 / &3 * LN) pow 3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(log(&2))` THEN
      CONJ_TAC THENL
       [SIMP_TAC[EXP_LOG; REAL_ARITH `&0 < &2`; REAL_LE_REFL];
        REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC];
      REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[GSYM REAL_EXP_N] THEN
      SUBGOAL_THEN `&3 * &1 / &3 * LN = LN` SUBST1_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "LN" THEN ASM_SIMP_TAC[EXP_LOG; REAL_LE_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `z = exp(&1 / &8 * LN)` THEN
  ABBREV_TAC `y = exp(&1 / &3 * LN)` THEN
  ABBREV_TAC `Q = {q | prime q /\ z <= &q /\ &q < y}` THEN
  ABBREV_TAC `A' = {n | n IN gchen_A h N /\
                        !p. p IN {p | prime p /\ &p < z}
                            ==> ~(p divides n)}` THEN
  SUBGOAL_THEN `FINITE(Q:num->bool) /\ FINITE(A':num->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{q | prime q /\ &q < y}` THEN
      REWRITE_TAC[FINITE_PRIMES_LT] THEN SET_TAC[];
      EXPAND_TAC "A'" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
      REWRITE_TAC[FINITE_GCHEN_A]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. n IN A' ==> ~(n = 0) /\ n < N /\ coprime(n,h) /\
                    prime(chen_dist h n) /\ n IN gchen_A h N /\
                    (!q. prime q /\ q divides n ==> z <= &q)`
  (LABEL_TAC "A'") THENL
   [EXPAND_TAC "A'" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `n IN gchen_A h N` THEN
    REWRITE_TAC[gchen_A; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `q:num` THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:num`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sifted] THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `SBc = &(CARD {p1,p2,p3 | (p1,p2,p3) IN chen_T h N /\
                             !q. prime q /\ &q < y
                                 ==> ~(q divides
                                       chen_dist h (p1 * p2 * p3))})` THEN
  ABBREV_TAC
   `P2c = &(CARD {n | n IN gchen_A h N /\ almost_prime 2 n})` THEN
  SUBGOAL_THEN
   `!n. n IN A'
        ==> &1 <= &1 / &2 * &(chen_nu z y n) +
                  (&1 / &2 * (if chen_triple z y n then &1 else &0) +
                   ((if almost_prime 2 n then &1 else &0) +
                    (if n = 1 then &1 else &0)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `n = 1` THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!a b c:real. &0 <= a /\ &0 <= b /\ &0 <= c
                     ==> &1 <= &1 / &2 * a + (&1 / &2 * b + (c + &1))`) THEN
      REWRITE_TAC[REAL_POS] THEN CONJ_TAC THEN COND_CASES_TAC THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
    USE_THEN "A'" (MP_TAC o SPEC `n:num`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    ASM_CASES_TAC
     `chen_nu z y n + (if chen_triple z y n then 1 else 0) <= 1` THENL
     [SUBGOAL_THEN `almost_prime 2 n` (fun th -> REWRITE_TAC[th]) THENL
       [MATCH_MP_TAC CHEN_WEIGHT_P2 THEN
        MAP_EVERY EXISTS_TAC [`z:real`; `y:real`; `N:num`] THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!a b:real. &0 <= a /\ &0 <= b
                   ==> &1 <= &1 / &2 * a + (&1 / &2 * b + &1)`) THEN
      REWRITE_TAC[REAL_POS] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_LE]) THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 < a + 1 <=> 1 <= a`; ADD_CLAUSES;
                  ARITH_RULE `1 < a <=> 2 <= a`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum A' (\n. &(chen_nu z y n)) <=
    sum A' (\n. sum Q (\q. if q divides n then &1 else &0)) + &6 * &N / z`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `sum A' (\n. sum Q (\q. (if q divides n then &1 else &0) +
                             sum(2..N) (\k. if q EXP k divides n
                                            then &1 else &0)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      USE_THEN "A'" (MP_TAC o SPEC `n:num`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      MP_TAC(SPECL [`z:real`; `y:real`; `N:num`; `n:num`] CHEN_NU_SUM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SIMP_TAC[SUM_CLAUSES_LEFT; ASSUME `256 < N`;
               ARITH_RULE `256 < N ==> 1 <= N`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[EXP_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_ADD; FINITE_NUMSEG] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN
    SUBGOAL_THEN
     `sum A' (\n. sum Q (\q. sum(2..N) (\k. if q EXP k divides n
                                            then &1 else &0))) =
      sum Q (\q. sum(2..N) (\k. sum A' (\n. if q EXP k divides n
                                             then &1 else &0)))`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL
       [`\n q. sum(2..N) (\k. if q EXP k divides n then &1 else &0)`;
        `A':num->bool`; `Q:num->bool`] SUM_SWAP) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `q:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL
       [`\n k. if q EXP k divides n then &1 else &0`;
        `A':num->bool`; `2..N`] SUM_SWAP) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum Q (\q. &N * (&2 / &q pow 2))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `q:num` THEN EXPAND_TAC "Q" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `2 <= q` ASSUME_TAC THENL
       [ASM_MESON_TAC[PRIME_GE_2]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `sum(2..N) (\k. &N * inv(&q pow k))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
        X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(q EXP k = 0)` ASSUME_TAC THENL
         [REWRITE_TAC[EXP_EQ_0] THEN UNDISCH_TAC `2 <= q` THEN ARITH_TAC;
          ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&(CARD {n | n IN 1..N /\ q EXP k divides n})` THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET] THEN
          SIMP_TAC[CARD_EQ_SUM; FINITE_RESTRICT; FINITE_NUMSEG] THEN
          MATCH_MP_TAC SUM_SUBSET THEN
          ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG; REAL_POS] THEN
          REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_NUMSEG] THEN
          X_GEN_TAC `x:num` THEN STRIP_TAC THEN
          REWRITE_TAC[REAL_ARITH `&1 <= &0 <=> F`] THEN
          USE_THEN "A'" (MP_TAC o SPEC `x:num`) THEN
          (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
          UNDISCH_TAC `~((1 <= x /\ x <= N) /\ q EXP k divides x)` THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `x < N:num` THEN UNDISCH_TAC `~(x = 0)` THEN ARITH_TAC;
          MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N / &(q EXP k)` THEN
          ASM_SIMP_TAC[CARD_MULTIPLES_LE] THEN
          REWRITE_TAC[real_div; REAL_OF_NUM_POW; REAL_LE_REFL]];
        REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[GEOM_TAIL_INV; REAL_POS]];
      REWRITE_TAC[SUM_LMUL; real_div; REAL_MUL_LID] THEN
      REWRITE_TAC[REAL_ARITH `n * &2 * x = (&2 * n) * x:real`] THEN
      REWRITE_TAC[SUM_LMUL] THEN
      REWRITE_TAC[REAL_ARITH
       `&6 * n * inv z = (&2 * n) * (&3 * inv z):real`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`z:real`; `y:real`] SUM_PRIME_SQUARES_TAIL) THEN
      ASM_REWRITE_TAC[real_div; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum A' (\n. if chen_triple z y n then &1 else &0) <= SBc + &2 * y + &2`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; GSYM CARD_EQ_SUM; FINITE_RESTRICT] THEN
    ABBREV_TAC
     `TB = {p1,p2,p3 | (p1,p2,p3) IN chen_T h N /\
                       !q. prime q /\ &q < y
                           ==> ~(q divides chen_dist h (p1 * p2 * p3))}` THEN
    SUBGOAL_THEN `FINITE(TB:num#num#num->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `chen_T h N` THEN
      REWRITE_TAC[FINITE_CHEN_T] THEN EXPAND_TAC "TB" THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `IB = IMAGE (\(p1,p2,p3). p1 * p2 * p3)
                           (TB:num#num#num->bool)` THEN
    SUBGOAL_THEN
     `FINITE(IB:num->bool) /\ CARD IB <= CARD(TB:num#num#num->bool)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "IB" THEN ASM_SIMP_TAC[FINITE_IMAGE; CARD_IMAGE_LE];
      ALL_TAC] THEN
    ABBREV_TAC `IY = IMAGE (\p. h - p) {p:num | &p < y} UNION
                     IMAGE (\p. h + p) {p:num | &p < y}` THEN
    SUBGOAL_THEN `FINITE(IY:num->bool) /\ &(CARD IY) <= &2 * y + &2`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "IY" THEN
      SIMP_TAC[FINITE_UNION; FINITE_IMAGE; FINITE_NUM_LT_REAL] THEN
      SUBGOAL_THEN `&(CARD {p:num | &p < y}) <= y + &1` MP_TAC THENL
       [MATCH_MP_TAC CARD_NUM_LT_REAL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `u <= &2 * c ==> c <= y + &1 ==> u <= &2 * y + &2`) THEN
      REWRITE_TAC[REAL_ARITH `&2 * c = c + c`; REAL_OF_NUM_ADD;
                  REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD(IMAGE (\p. h - p) {p:num | &p < y}) +
                  CARD(IMAGE (\p. h + p) {p:num | &p < y})` THEN
      SIMP_TAC[CARD_UNION_LE; FINITE_IMAGE; FINITE_NUM_LT_REAL] THEN
      MATCH_MP_TAC LE_ADD2 THEN SIMP_TAC[CARD_IMAGE_LE; FINITE_NUM_LT_REAL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD((IB:num->bool) UNION IY))` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[FINITE_UNION] THEN
      EXPAND_TAC "IB" THEN EXPAND_TAC "IY" THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN
      USE_THEN "A'" (MP_TAC o SPEC `n:num`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      ASM_CASES_TAC `&(chen_dist h n) < y` THENL
       [DISJ2_TAC THEN
        UNDISCH_TAC `&(chen_dist h n) < y` THEN REWRITE_TAC[chen_dist] THEN
        COND_CASES_TAC THEN DISCH_TAC THENL
         [DISJ1_TAC THEN EXISTS_TAC `h - n:num`;
          DISJ2_TAC THEN EXISTS_TAC `n - h:num`] THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        DISJ1_TAC] THEN
      UNDISCH_TAC `chen_triple z y n` THEN REWRITE_TAC[chen_triple] THEN
      DISCH_THEN(X_CHOOSE_THEN `p1:num` (X_CHOOSE_THEN `p2:num`
        (X_CHOOSE_THEN `p3:num` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `(p1:num,p2:num,p3:num)` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "TB" THEN
      REWRITE_TAC[IN_ELIM_TRIPLE; chen_T] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `n = p1 * p2 * p3:num` THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[DIVIDES_PRIME_PRIME] THEN DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&(CARD(IB:num->bool)) + &(CARD(IY:num->bool))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      MATCH_MP_TAC CARD_UNION_LE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a b c d:real. a <= c /\ b <= d ==> a + b <= c + d`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "SBc" THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum A' (\n. if n = 1 then &1 else &0) <= &1`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; GSYM CARD_EQ_SUM; FINITE_RESTRICT] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {1}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      REWRITE_TAC[FINITE_SING; SUBSET; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
      REWRITE_TAC[CARD_SING; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum A' (\n. if almost_prime 2 n then &1 else &0) <= P2c`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_RESTRICT_SET; GSYM CARD_EQ_SUM; FINITE_RESTRICT] THEN
    EXPAND_TAC "P2c" THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_GCHEN_A] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum Q (\q. sum A' (\n. if q divides n then &1 else &0)) =
    sum A' (\n. sum Q (\q. if q divides n then &1 else &0))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\q n. if q divides n then &1 else &0`;
                   `Q:num->bool`; `A':num->bool`] SUM_SWAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum A' (\n. &1) <=
    &1 / &2 * sum A' (\n. &(chen_nu z y n)) +
    (&1 / &2 * sum A' (\n. if chen_triple z y n then &1 else &0) +
     (sum A' (\n. if almost_prime 2 n then &1 else &0) +
      sum A' (\n. if n = 1 then &1 else &0)))`
  MP_TAC THENL
   [ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_LE THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`sum A' (\n. &(chen_nu z y n)) <=
     sum A' (\n. sum Q (\q. if q divides n then &1 else &0)) + &6 * &N / z`;
    `sum A' (\n. if chen_triple z y n then &1 else &0) <= SBc + &2 * y + &2`;
    `sum A' (\n. if almost_prime 2 n then &1 else &0) <= P2c`;
    `sum A' (\n. if n = 1 then &1 else &0) <= &1`;
    `&2 <= z`; `z <= y`] THEN
  REAL_ARITH_TAC);;
