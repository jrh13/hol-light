(* ========================================================================= *)
(* The theorem of Steiner (1977) on circuits of the 3x+1 problem.            *)
(*                                                                           *)
(* Purpose: the only circuit of the shortcut 3x+1 map is 1 -> 2 -> 1; first  *)
(* conditionally on an explicit lower bound for the linear form              *)
(* b2 log 2 - b1 log 3, then unconditionally by TWOLOG_LOG2_LOG3_EXISTS.     *)
(* References: R. P. Steiner, A theorem on the Syracuse problem, Proc. 7th   *)
(* Manitoba Conf. Numer. Math. 1977, Congr. Numer. 20 (1978) 553-559, and    *)
(* J. Simons, B. de Weger, Acta Arith. 117 (2005) 51-70.                     *)
(*                                                                           *)
(* Main results: STEINER_BOUNDED (no nontrivial circuit with k < 6586818670; *)
(* unconditional), STEINER_CONDITIONAL, STEINER and STEINER_CIRCUITS; the    *)
(* real Taylor bound CLASSNO_CF_LOG_TAYLOR for log(1 - x) and the            *)
(* enclosures CLASSNO_CF_LOG_16_15_BOUNDS, CLASSNO_CF_LOG_25_24_BOUNDS,      *)
(* CLASSNO_CF_LOG_81_80_BOUNDS, also used by Baker/classno_cf.ml.            *)
(*                                                                           *)
(* Uses: Multivariate/cauchy.ml (TAYLOR_CLOG_NEG) and                        *)
(* Multivariate/transcendentals.ml in sections 1 to 7 of the file; section 8 *)
(* uses TWOLOG_LOG2_LOG3_EXISTS (Baker/twolog.ml).                           *)
(*                                                                           *)
(* Contents.                                                                 *)
(*  1. The shortcut map collatz_t and circuits; the circuit equation         *)
(*     n * (2 EXP (k + l) - 3 EXP k) = 3 EXP k - 2 EXP k, n + 1 >= 2 EXP k,  *)
(*     l <= k; circuits with k <= 4.                                         *)
(*  2. The linear form Lam = (k + l) log 2 - k log 3 of a circuit:           *)
(*     0 < Lam and n * Lam < 1.                                              *)
(*  3. Farey neighbours: a fraction above the lower neighbour with a small   *)
(*     denominator lies above the upper neighbour.                           *)
(*  4. Rational enclosures of log 2 and log 3 of width < 10 pow -22, from    *)
(*     log 2 = 7 a + 5 b + 3 c, log 3 = 11 a + 8 b + 5 c with                *)
(*     a = log(16/15), b = log(25/24), c = log(81/80) (Taylor series;        *)
(*     enclosures of a, b, c of width < 2e-30).                              *)
(*  5. Growth of (log y) pow 2.                                              *)
(*  6. Circuits with 5 <= k < 6586818670 do not exist (convergents 8/5,      *)
(*     65/41 and 630138897/397573379 of log 3 / log 2); unconditional.       *)
(*  7. The conditional theorem: the hypothesised lower bound for the linear  *)
(*     form excludes k >= 2 EXP 31.                                          *)
(*  8. The unconditional theorem STEINER_CIRCUITS.                           *)
(* ========================================================================= *)

needs "Baker/twolog.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* 1. The shortcut 3x+1 map and circuits.                                    *)
(* ------------------------------------------------------------------------- *)

let collatz_t = new_definition
 `collatz_t n = if EVEN n then n DIV 2 else (3 * n + 1) DIV 2`;;

(* A circuit of type (k,l) starting at n: k odd iterates followed by l even  *)
(* iterates, returning to n.                                                 *)

let circuit = new_definition
 `circuit k l n <=>
    1 <= k /\ 1 <= l /\ 1 <= n /\
    (!i. i < k ==> ODD(ITER i collatz_t n)) /\
    (!i. k <= i /\ i < k + l ==> EVEN(ITER i collatz_t n)) /\
    ITER (k + l) collatz_t n = n`;;

let COLLATZ_T_EVEN = prove
 (`!n. EVEN n ==> 2 * collatz_t n = n`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[collatz_t; EVEN_DOUBLE] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ]);;

let COLLATZ_T_ODD = prove
 (`!n. ODD n ==> 2 * collatz_t n = 3 * n + 1`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  REWRITE_TAC[collatz_t; EVEN; EVEN_DOUBLE] THEN
  SUBGOAL_THEN `3 * SUC(2 * m) + 1 = 2 * (3 * m + 2)` SUBST1_TAC THENL
   [ARITH_TAC; SIMP_TAC[DIV_MULT; ARITH_EQ]]);;

let CIRCUIT_1_1_1 = prove
 (`circuit 1 1 1`,
  REWRITE_TAC[circuit; ARITH_RULE `i < 1 <=> i = 0`;
              ARITH_RULE `1 <= i /\ i < 1 + 1 <=> i = 1`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; ITER_1; ITER; ARITH_RULE `1 + 1 = 2`] THEN
  REWRITE_TAC[num_CONV `2`; ITER; ITER_1; collatz_t] THEN
  CONV_TAC NUM_REDUCE_CONV);;

let CIRCUIT_ODD_PART = prove
 (`!k l n. circuit k l n
           ==> !i. i <= k
                   ==> 2 EXP i * (ITER i collatz_t n + 1) =
                       3 EXP i * (n + 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[circuit] THEN STRIP_TAC THEN
  INDUCT_TAC THENL [REWRITE_TAC[ITER; EXP; MULT_CLAUSES]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ODD(ITER i collatz_t n)` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COLLATZ_T_ODD) THEN
  REWRITE_TAC[ITER; EXP; IMP_IMP] THEN CONV_TAC NUM_RING);;

let CIRCUIT_EVEN_PART = prove
 (`!k l n. circuit k l n
           ==> !j. j <= l
                   ==> 2 EXP j * ITER (k + j) collatz_t n =
                       ITER k collatz_t n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[circuit] THEN STRIP_TAC THEN
  INDUCT_TAC THENL [REWRITE_TAC[ADD_CLAUSES; EXP; MULT_CLAUSES]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `EVEN(ITER (k + j) collatz_t n)` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COLLATZ_T_EVEN) THEN
  REWRITE_TAC[ADD_CLAUSES; ITER; EXP; IMP_IMP] THEN CONV_TAC NUM_RING);;

let CIRCUIT_EQUATION = prove
 (`!k l n. circuit k l n
           ==> 2 EXP (k + l) * n + 2 EXP k = 3 EXP k * n + 3 EXP k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP CIRCUIT_ODD_PART) THEN
  FIRST_ASSUM(MP_TAC o SPEC `l:num` o MATCH_MP CIRCUIT_EVEN_PART) THEN
  FIRST_ASSUM(MP_TAC o last o CONJUNCTS o GEN_REWRITE_RULE I [circuit]) THEN
  REWRITE_TAC[LE_REFL; EXP_ADD; IMP_IMP] THEN CONV_TAC NUM_RING);;

let CIRCUIT_BASIC = prove
 (`!k l n. circuit k l n
           ==> 1 <= k /\ 1 <= l /\ 1 <= n /\ l <= k /\
               3 EXP k < 2 EXP (k + l) /\ 2 EXP k <= n + 1 /\
               2 EXP (k + l) * n + 2 EXP k = 3 EXP k * n + 3 EXP k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP CIRCUIT_EQUATION) THEN
  FIRST_ASSUM(MP_TAC o SPEC `k:num` o MATCH_MP CIRCUIT_ODD_PART) THEN
  REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [circuit]) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 EXP k < 3 EXP k /\ 0 < 2 EXP k` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[EXP_MONO_LT; EXP_LT_0] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `3 EXP k < 2 EXP (k + l)` ASSUME_TAC THENL
   [SUBGOAL_THEN `3 EXP k * n < 2 EXP (k + l) * n` MP_TAC THENL
     [ASM_ARITH_TAC; SIMP_TAC[LT_MULT_RCANCEL]];
    ASM_REWRITE_TAC[]] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `2 EXP (k + l) < 2 EXP (2 * k + 1)` MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[LT_EXP] THEN ARITH_TAC] THEN
    SUBGOAL_THEN `3 EXP k <= 3 EXP k * n` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP (k + l) * n < (2 * 3 EXP k) * n` MP_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[LT_MULT_RCANCEL] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `3 EXP k < 4 EXP k` MP_TAC THENL
     [REWRITE_TAC[EXP_MONO_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `2 EXP (2 * k + 1) = 2 * 4 EXP k` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_MULT] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(2 EXP k) divides (3 EXP k * (n + 1))` MP_TAC THENL
   [REWRITE_TAC[divides] THEN EXISTS_TAC `ITER k collatz_t n + 1` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] COPRIME_DIVPROD)) THEN
  REWRITE_TAC[COPRIME_EXP2] THEN CONV_TAC(ONCE_DEPTH_CONV COPRIME_CONV) THEN
  REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ARITH_TAC);;

(* Circuits with k <= 4: only the trivial circuit 1 -> 2 -> 1.               *)

let CIRCUIT_SMALL = prove
 (`!k l n. circuit k l n /\ k <= 4 ==> n = 1 /\ k = 1 /\ l = 1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_BASIC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `(k = 1 \/ k = 2 \/ k = 3 \/ k = 4) /\
                (l = 1 \/ l = 2 \/ l = 3 \/ l = 4)`
  MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. The linear form of a circuit: 0 < Lam < 1 / n.                         *)
(* ------------------------------------------------------------------------- *)

let CIRCUIT_LINEAR_FORM = prove
 (`!k l n. circuit k l n
           ==> &0 < &(k + l) * log(&2) - &k * log(&3) /\
               &n * (&(k + l) * log(&2) - &k * log(&3)) < &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_BASIC) THEN
  SUBGOAL_THEN
   `exp(&(k + l) * log(&2) - &k * log(&3)) = &2 pow (k + l) / &3 pow k`
  ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_SUB; REAL_EXP_N] THEN
    SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&3 pow k < &2 pow (k + l) /\ &0 < &3 pow k /\ &0 < &2 pow k /\
    &2 pow (k + l) * &n + &2 pow k = &3 pow k * &n + &3 pow k`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; REAL_OF_NUM_MUL;
                    REAL_OF_NUM_ADD; REAL_OF_NUM_EQ; EXP_LT_0] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
    ASM_SIMP_TAC[REAL_EXP_0; REAL_LT_RDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(SPEC `&(k + l) * log(&2) - &k * log(&3)` REAL_EXP_LE_X) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`&(k + l) * log(&2) - &k * log(&3)`,`x:real`) THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&n * (&2 pow (k + l) / &3 pow k) < &n + &1` MP_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&n * (&1 + x) <= &n * (&2 pow (k + l) / &3 pow k)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 3. Farey neighbours p/q > r/s (p s - r q = 1): every fraction a/b above   *)
(* r/s with b < q + s satisfies a/b >= p/q.                                  *)
(* ------------------------------------------------------------------------- *)

let STEINER_FAREY_NEIGHBOUR = prove
 (`!p q r s a b.
        p * s = r * q + 1 /\ r * b < a * s /\ b < q + s
        ==> p * b <= a * q`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?u v. p * b = a * q + SUC u /\ a * s = r * b + SUC v`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[LT_EXISTS]; ALL_TAC] THEN
  SUBGOAL_THEN `s * SUC u + q * SUC v = b` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`p * s = r * q + 1`; `p * b = a * q + SUC u`;
      `a * s = r * b + SUC v`] THEN
    REWRITE_TAC[IMP_IMP] THEN CONV_TAC NUM_RING;
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_ARITH_TAC]);;

(* The same in terms of the linear forms m log 2 - k log 3.                  *)

let STEINER_FAREY_LOG_BOUND = prove
 (`!p q r s k m.
        p * s = r * q + 1 /\ k < q + s /\ ~(k = 0) /\
        &r * log(&2) < &s * log(&3) /\ &k * log(&3) < &m * log(&2)
        ==> &k * (&p * log(&2) - &q * log(&3)) <=
            &q * (&m * log(&2) - &k * log(&3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < log(&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS_LT THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p * k <= m * q` MP_TAC THENL
   [MATCH_MP_TAC STEINER_FAREY_NEIGHBOUR THEN
    MAP_EVERY EXISTS_TAC [`r:num`; `s:num`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC `log(&2)` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&k * &r * log(&2) < &k * &s * log(&3) /\
                  &s * &k * log(&3) <= &s * &m * log(&2)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
        ASM_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POS; REAL_LT_IMP_LE]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_MUL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&p * &k) * log(&2) <= (&m * &q) * log(&2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 4. Rational enclosures of log 2 and log 3 (Taylor series of log(1 - z)).  *)
(* ------------------------------------------------------------------------- *)

(* The real Taylor bound for log(1 - x), with an upper bound r for |x|.      *)

let CLASSNO_CF_LOG_TAYLOR = prove
 (`!n x r. abs x <= r /\ r < &1
           ==> abs(log(&1 - x) + sum(1..n) (\k. x pow k / &k))
               <= r pow (n + 1) / (&1 - r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `Cx x`] TAYLOR_CLOG_NEG) THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN ANTS_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - x` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM CX_DIV; GSYM CX_POW; GSYM CX_SUB; VSUM_CX; GSYM CX_ADD;
               COMPLEX_NORM_CX; GSYM CX_LOG] THEN
  MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
  REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REAL_ARITH_TAC]);;

(* Enclosures of width below 2e-30 of log(16/15), log(25/24), log(81/80) by  *)
(* the Taylor series of log(1 - 1/N) (24, 21 and 15 terms); they also serve  *)
(* the enclosures of log eps_21 and log eps_33 of Baker/classno_cf.ml.       *)

let CLASSNO_CF_LOG_16_15_BOUNDS = prove
 (`&6453852113757117167292391568311 / &10 pow 32 <= log(&16 / &15) /\
   log(&16 / &15) <= &6453852113757117167292391568481 / &10 pow 32`,
  MP_TAC(SPEC `&15 / &16` LOG_INV) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`24`; `&1 / &16`; `&1 / &16`] CLASSNO_CF_LOG_TAYLOR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let CLASSNO_CF_LOG_25_24_BOUNDS = prove
 (`&4082199452025512955457706515512 / &10 pow 32 <= log(&25 / &24) /\
   log(&25 / &24) <= &4082199452025512955457706515550 / &10 pow 32`,
  MP_TAC(SPEC `&24 / &25` LOG_INV) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`21`; `&1 / &25`; `&1 / &25`] CLASSNO_CF_LOG_TAYLOR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

let CLASSNO_CF_LOG_81_80_BOUNDS = prove
 (`&1242251999855715331129312863089 / &10 pow 32 <= log(&81 / &80) /\
   log(&81 / &80) <= &1242251999855715331129312863149 / &10 pow 32`,
  MP_TAC(SPEC `&80 / &81` LOG_INV) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`15`; `&1 / &81`; `&1 / &81`] CLASSNO_CF_LOG_TAYLOR) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV EXPAND_SUM_CONV) THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REAL_ARITH_TAC);;

(* 2 = (16/15)^7 (25/24)^5 (81/80)^3 and 3 = (16/15)^11 (25/24)^8 (81/80)^5. *)

let STEINER_LOG_2_DECOMP = prove
 (`log(&2) =
   &7 * log(&16 / &15) + &5 * log(&25 / &24) + &3 * log(&81 / &80)`,
  SIMP_TAC[GSYM LOG_POW; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM LOG_MUL; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let STEINER_LOG_3_DECOMP = prove
 (`log(&3) =
   &11 * log(&16 / &15) + &8 * log(&25 / &24) + &5 * log(&81 / &80)`,
  SIMP_TAC[GSYM LOG_POW; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM LOG_MUL; REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let STEINER_LOG_2_BOUNDS = prove
 (`&69314718055994530941721556 / &10 pow 26 <= log(&2) /\
   log(&2) <= &69314718055994530941724691 / &10 pow 26`,
  REWRITE_TAC[STEINER_LOG_2_DECOMP] THEN
  MP_TAC CLASSNO_CF_LOG_16_15_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_25_24_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_81_80_BOUNDS THEN REAL_ARITH_TAC);;

let STEINER_LOG_3_BOUNDS = prove
 (`&109861228866810969139521889 / &10 pow 26 <= log(&3) /\
   log(&3) <= &109861228866810969139526876 / &10 pow 26`,
  REWRITE_TAC[STEINER_LOG_3_DECOMP] THEN
  MP_TAC CLASSNO_CF_LOG_16_15_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_25_24_BOUNDS THEN
  MP_TAC CLASSNO_CF_LOG_81_80_BOUNDS THEN REAL_ARITH_TAC);;

(* The linear forms of the convergents used below: 8/5, 65/41 and            *)
(* 630138897/397573379 of log 3 / log 2 lie above it, with the lower         *)
(* Farey neighbours 19/12, 84/53 and 9809721694/6189245291 below it.         *)

let STEINER_LOG_CONVERGENTS = prove
 (`&19 * log(&2) < &12 * log(&3) /\
   &1 / &20 <= &8 * log(&2) - &5 * log(&3) /\
   &84 * log(&2) < &53 * log(&3) /\
   &1 / &100 <= &65 * log(&2) - &41 * log(&3) /\
   &9809721694 * log(&2) < &6189245291 * log(&3) /\
   &1 / &10 pow 10 <= &630138897 * log(&2) - &397573379 * log(&3)`,
  MP_TAC STEINER_LOG_2_BOUNDS THEN MP_TAC STEINER_LOG_3_BOUNDS THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 5. Growth of (log y) pow 2: for a <= y, (log y)^2 / y <= (log a)^2 / a    *)
(* as soon as log a >= 2.                                                    *)
(* ------------------------------------------------------------------------- *)

let STEINER_LOG_SQUARE_GROWTH = prove
 (`!a y. &0 < a /\ a <= y /\ &2 <= log a
         ==> log y pow 2 * a <= log a pow 2 * y`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `s = sqrt((y:real) / a)` THEN
  SUBGOAL_THEN `&0 < (y:real)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real) pow 2 = y / a /\ &1 <= s` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THENL
     [MATCH_MP_TAC SQRT_POW_2 THEN ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
      MATCH_MP_TAC REAL_LE_RSQRT THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real) = a * s pow 2` SUBST1_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `log(a * s pow 2) = log a + &2 * log s` SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT;
                 REAL_ARITH `&1 <= s ==> &0 < s`];
    ALL_TAC] THEN
  SUBGOAL_THEN `log s <= s - &1 /\ &0 <= log s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[LOG_POS] THEN
    MP_TAC(SPEC `s - &1` LOG_LE_STRONG) THEN REWRITE_TAC[REAL_SUB_ADD2] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log a + &2 * log s <= s * log a` ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * (s - &1) <= log a * (s - &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(log a + &2 * log s) pow 2 <= (s * log a) pow 2`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(s * log a) pow 2 * a` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 6. No circuit with k0 <= k < q + s when p/q > r/s are Farey neighbours    *)
(* around log 3 / log 2 and k0 (2^k0 - 1) d >= q for some lower bound d of   *)
(* p log 2 - q log 3.                                                        *)
(* ------------------------------------------------------------------------- *)

let CIRCUIT_FAREY_RANGE = prove
 (`!p q r s k0 d k l n.
        circuit k l n /\ p * s = r * q + 1 /\ 1 <= q /\
        k0 <= k /\ k < q + s /\
        &r * log(&2) < &s * log(&3) /\
        &0 <= d /\ d <= &p * log(&2) - &q * log(&3) /\
        &q <= &k0 * (&2 pow k0 - &1) * d
        ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_LINEAR_FORM) THEN
  MP_TAC(SPECL [`p:num`; `q:num`; `r:num`; `s:num`; `k:num`; `k + l`]
    STEINER_FAREY_LOG_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `&2 pow k0 - &1 <= &n /\ &0 <= &2 pow k0 - &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 pow k0 <= &2 pow k /\ &2 pow k <= &n + &1 /\
                  &1 <= &2 pow k0`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_LE];
        MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&k0 * (&2 pow k0 - &1) <= &k * &n` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_POS; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&k0 * (&2 pow k0 - &1)) * d <= (&k * &n) * d` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&k * d <= &k * (&p * log(&2) - &q * log(&3))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&n * (&k * d) <= &n * (&q * (&(k + l) * log(&2) - &k * log(&3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&q * (&n * (&(k + l) * log(&2) - &k * log(&3))) < &q * &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Unconditionally, there is no nontrivial circuit with k < 6586818670.      *)

let STEINER_BOUNDED = prove
 (`!n k l. circuit k l n /\ k < 6586818670 ==> n = 1 /\ k = 1 /\ l = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `k <= 4` THENL [ASM_MESON_TAC[CIRCUIT_SMALL]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  STRIP_ASSUME_TAC STEINER_LOG_CONVERGENTS THEN
  SUBGOAL_THEN `5 <= k /\ k < 17 \/ 17 <= k /\ k < 94 \/ 94 <= k` MP_TAC THENL
   [ASM_ARITH_TAC; STRIP_TAC] THENL
   [MP_TAC(SPECL [`8`; `5`; `19`; `12`; `5`; `&1 / &20`;
                  `k:num`; `l:num`; `n:num`] CIRCUIT_FAREY_RANGE);
    MP_TAC(SPECL [`65`; `41`; `84`; `53`; `17`; `&1 / &100`;
                  `k:num`; `l:num`; `n:num`] CIRCUIT_FAREY_RANGE);
    MP_TAC(SPECL [`630138897`; `397573379`; `9809721694`; `6189245291`; `94`;
                  `&1 / &10 pow 10`; `k:num`; `l:num`; `n:num`]
                 CIRCUIT_FAREY_RANGE)] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. The hypothesised lower bound excludes circuits with k >= 2^31.         *)
(* ------------------------------------------------------------------------- *)

let CIRCUIT_LARGE = prove
 (`!C k l n.
        &0 <= C /\ C <= &10 pow 6 /\ circuit k l n /\ 2147483648 <= k /\
        exp(--(C * max (&10) (log(&k + &(k + l))) pow 2)) <=
        abs(&(k + l) * log(&2) - &k * log(&3))
        ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_LINEAR_FORM) THEN
  ABBREV_TAC `y = &k + &(k + l)` THEN
  ABBREV_TAC `mm = max (&10) (log y)` THEN
  ABBREV_TAC `lam = &(k + l) * log(&2) - &k * log(&3)` THEN
  SUBGOAL_THEN
   `&0 < log(&2) /\ log(&2) <= &6932 / &10000 /\ &10 <= &32 * log(&2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC STEINER_LOG_2_BOUNDS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&n < exp(C * mm pow 2)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&n * exp(--(C * mm pow 2)) < &1` MP_TAC THENL
     [MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&n * lam` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_EXP_NEG; GSYM real_div] THEN
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_EXP_POS_LT; REAL_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&k * log(&2) < log(&2) + C * mm pow 2` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LT] THEN
    REWRITE_TAC[REAL_EXP_N; REAL_EXP_ADD] THEN
    SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&2 * &n` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_LMUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow 32 <= y /\ y <= &3 * &k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_MUL;
                REAL_OF_NUM_LE] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `mm pow 2 * &2 pow 32 <= (&32 * log(&2)) pow 2 * y`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `mm = &10 \/ mm = log y` MP_TAC THENL
     [EXPAND_TAC "mm" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MP_TAC(SPECL [`&2 pow 32`; `y:real`] STEINER_LOG_SQUARE_GROWTH) THEN
      SIMP_TAC[LOG_POW; REAL_OF_NUM_LT; ARITH] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `C * mm pow 2 <= &10 pow 6 * mm pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&32 * log(&2)) pow 2 * y <= (&32 * log(&2)) pow 2 * (&3 * &k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `log(&2) * (log(&2) * &k) <= &6932 / &10000 * (log(&2) * &k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) * &2147483648 <= log(&2) * &k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_OF_NUM_LE];
    ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorem of Steiner, conditional on a lower bound for the linear form. *)
(* ------------------------------------------------------------------------- *)

let STEINER_CONDITIONAL = prove
 (`!C. &0 <= C /\ C <= &10 pow 6 /\
       (!b1 b2. 1 <= b1 /\ 1 <= b2
                ==> exp(--(C * max (&10) (log(&b1 + &b2)) pow 2)) <=
                    abs(&b2 * log(&2) - &b1 * log(&3)))
       ==> !n k l. circuit k l n ==> n = 1 /\ k = 1 /\ l = 1`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  ASM_CASES_TAC `k < 6586818670` THENL
   [ASM_MESON_TAC[STEINER_BOUNDED]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP CIRCUIT_BASIC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `k + l`]) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN MATCH_MP_TAC CIRCUIT_LARGE THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `k:num`; `l:num`; `n:num`] THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 8. The theorem of Steiner (1977), unconditional: the explicit             *)
(* two-logarithm bound TWOLOG_LOG2_LOG3_EXISTS (Baker/twolog.ml) discharges  *)
(* the hypothesis of STEINER_CONDITIONAL. The only circuit of the shortcut   *)
(* 3x+1 map (k odd steps followed by l even steps) is the trivial cycle      *)
(* 1 -> 2 -> 1.                                                              *)
(* ------------------------------------------------------------------------- *)

let STEINER = prove
 (`!n k l. circuit k l n ==> n = 1 /\ k = 1 /\ l = 1`,
  MATCH_MP_TAC STEINER_CONDITIONAL THEN
  MATCH_ACCEPT_TAC TWOLOG_LOG2_LOG3_EXISTS);;

let STEINER_CIRCUITS = prove
 (`!n k l. circuit k l n <=> n = 1 /\ k = 1 /\ l = 1`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[STEINER] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[CIRCUIT_1_1_1]);;
