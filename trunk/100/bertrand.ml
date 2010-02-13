(* ========================================================================= *)
(* Proof of Bertrand conjecture and weak form of prime number theorem.       *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;
needs "Library/analysis.ml";;
needs "Library/transc.ml";;
needs "Library/calc_real.ml";;
needs "Library/floor.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* A ridiculous ommission from the OCaml Num library.                        *)
(* ------------------------------------------------------------------------- *)

let num_of_float =
  let p22 = Pervasives.( ** ) 2.0 22.0
  and p44 = Pervasives.( ** ) 2.0 44.0
  and p66 = Pervasives.( ** ) 2.0 66.0
  and q22 = pow2 22 and q44 = pow2 44 and q66 = pow2 66 in
  fun x ->
    let y0,n = frexp x in
    let u0 = int_of_float(y0 *. p22) in
    let y1 = p22 *. y0 -. float_of_int u0 in
    let u1 = int_of_float(y1 *. p22) in
    let y2 = p22 *. y1 -. float_of_int u1 in
    let u2 = int_of_float(y2 *. p22) in
    let y3 = p22 *. y2 -. float_of_int u2 in
    if y3 <> 0.0 then failwith "num_of_float: inexactness!" else
    (Int u0 // q22 +/ Int u1 // q44 +/ Int u2 // q66) */ pow2 n;;

(* ------------------------------------------------------------------------- *)
(* Integer truncated square root                                             *)
(* ------------------------------------------------------------------------- *)

let ISQRT = new_definition
  `ISQRT n = @m. m EXP 2 <= n /\ n < (m + 1) EXP 2`;;

let ISQRT_WORKS = prove
 (`!n. ISQRT(n) EXP 2 <= n /\ n < (ISQRT(n) + 1) EXP 2`,
  GEN_TAC THEN REWRITE_TAC[ISQRT] THEN CONV_TAC SELECT_CONV THEN
  SUBGOAL_THEN `(?m. m EXP 2 <= n) /\ (?a. !m. m EXP 2 <= n ==> m <= a)`
  MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[num_MAX] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    MESON_TAC[ARITH_RULE `~(m + 1 <= m)`; NOT_LE]] THEN
  CONJ_TAC THENL [EXISTS_TAC `0` THEN REWRITE_TAC[ARITH; LE_0]; ALL_TAC] THEN
  EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN
  MESON_TAC[LE_SQUARE_REFL; EXP_2; LE_TRANS]);;

let ISQRT_0 = prove
 (`ISQRT 0 = 0`,
  MP_TAC(SPEC `0` ISQRT_WORKS) THEN
  SIMP_TAC[ARITH_RULE `x <= 0 <=> (x = 0)`; EXP_EQ_0; ARITH_EQ]);;

let ISQRT_UNIQUE = prove
 (`!m n. (ISQRT n = m) <=> m EXP 2 <= n /\ n < (m + 1) EXP 2`,
  REPEAT GEN_TAC THEN EQ_TAC THEN MP_TAC (SPEC `n:num` ISQRT_WORKS) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(ISQRT n) EXP 2 < (m + 1) EXP 2 /\
                m EXP 2 < (ISQRT n + 1) EXP 2`
  MP_TAC THENL
   [ASM_MESON_TAC[LT_SUC_LE; LE_SUC_LT; LET_TRANS; LTE_TRANS];
    SIMP_TAC[num_CONV `2`; EXP_MONO_LT_SUC; GSYM LE_ANTISYM] THEN ARITH_TAC]);;

let ISQRT_SUC = prove
 (`!n. ISQRT(SUC n) =
       if ?m. SUC n = m EXP 2 then SUC(ISQRT n) else ISQRT n`,
  GEN_TAC THEN REWRITE_TAC[ISQRT_UNIQUE] THEN COND_CASES_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[ISQRT_WORKS; ARITH_RULE
     `a <= n /\ n < b /\ ~(SUC n = a) /\ ~(SUC n = b)
      ==> a <= SUC n /\ SUC n < b`]] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(CONJUNCT2(SPEC `n:num` ISQRT_WORKS)) THEN
    REWRITE_TAC[EXP_2; GSYM ADD1; MULT_CLAUSES; ADD_CLAUSES; LT_SUC] THEN
    ARITH_TAC] THEN
  POP_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `m = SUC(ISQRT n)` SUBST_ALL_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[LE_REFL]] THEN
  SUBGOAL_THEN `ISQRT(n) EXP 2 < m EXP 2 /\ m EXP 2 <= SUC(ISQRT n) EXP 2`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LE_SUC; EXP_MONO_LT_SUC] THEN ARITH_TAC] THEN
  MP_TAC(SPEC `n:num` ISQRT_WORKS) THEN REWRITE_TAC[ADD1] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[LT_SUC_LE; LE_SUC_LT]);;

(* ------------------------------------------------------------------------- *)
(* To allow us to deal with ln(2) numerically using standard conversion.     *)
(* ------------------------------------------------------------------------- *)

let LN_2_COMPOSITION = prove
 (`ln(&2) =
   &7 * ln(&1 + inv(&8)) - &2 * ln(&1 + inv(&24)) - &4 * ln(&1 + inv(&80))`,
  CONV_TAC(GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4
        [GSYM LN_POW; GSYM LN_MUL; GSYM LN_DIV; REAL_POW_LT; real_div;
         REAL_LT_ADD; REAL_LT_MUL; REAL_LT_INV_EQ; REAL_OF_NUM_LT; ARITH]) THEN
  AP_TERM_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Automatically process any ln(n) to allow us to use standard conversions.  *)
(* ------------------------------------------------------------------------- *)

let LN_N_CONV =
  let pth = prove
   (`x = (&1 + inv(&8)) pow n * (x / (&1 + inv(&8)) pow n)`,
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and qth = prove
   (`&0 < x
     ==> (ln((&1 + inv(&8)) pow n * x / (&1 + inv(&8)) pow n) =
          &n * ln(&1 + inv(&8)) + ln(&1 + (x / (&1 + inv(&8)) pow n - &1)))`,
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    SIMP_TAC[LN_MUL; LN_POW; REAL_LT_DIV; REAL_POW_LT;
             REAL_RAT_REDUCE_CONV `&0 < &1 + inv(&8)`])
  and ln_tm = `ln` and x_tm = `x:real` and n_tm = `n:num` in
  fun tm0 ->
    let ltm,tm = dest_comb tm0 in
    if ltm <> ln_tm then failwith "expected ln(ratconst)" else
    let x = rat_of_term tm in
    let rec dlog n y =
      let y' = y +/ y // Int 8 in
      if y' </ x then dlog (n + 1) y' else n in
    let n = dlog 0 (Int 1) in
    let th1 = INST [mk_small_numeral n,n_tm; tm,x_tm] pth in
    let th2 = AP_TERM ltm th1 in
    let th3 = PART_MATCH (lhs o rand) qth (rand(concl th2)) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    let th5 = TRANS th2 th4 in
    CONV_RULE(funpow 4 RAND_CONV REAL_RAT_REDUCE_CONV) th5;;

(* ------------------------------------------------------------------------- *)
(* Coarser version subtracting off multiples of ln(2) first, then using it.  *)
(* ------------------------------------------------------------------------- *)

let LN_N2_CONV =
  let pth = prove
   (`x = &2 pow n * (x / &2 pow n)`,
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    MATCH_MP_TAC REAL_POW_NZ THEN CONV_TAC REAL_RAT_REDUCE_CONV)
  and qth = prove
   (`&0 < x
     ==> (ln(&2 pow n * x / &2 pow n) =
          &n * ln(&2) + ln(&1 + (x / &2 pow n - &1)))`,
    REWRITE_TAC[REAL_ARITH `&1 + (x - &1) = x`] THEN
    SIMP_TAC[LN_MUL; LN_POW; REAL_LT_DIV; REAL_POW_LT;
             REAL_RAT_REDUCE_CONV `&0 < &2`])
  and ln_tm = `ln` and x_tm = `x:real` and n_tm = `n:num` in
  fun tm0 ->
    let ltm,tm = dest_comb tm0 in
    if ltm <> ln_tm then failwith "expected ln(ratconst)" else
    let x = rat_of_term tm in
    let rec dlog n y =
      let y' = y */ Int 2 in
      if y' </ x then dlog (n + 1) y' else n in
    let n = dlog 0 (Int 1) in
    let th1 = INST [mk_small_numeral n,n_tm; tm,x_tm] pth in
    let th2 = AP_TERM ltm th1 in
    let th3 = PART_MATCH (lhs o rand) qth (rand(concl th2)) in
    let th4 = MP th3 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th3)))) in
    let th5 = TRANS th2 th4 in
    let th6 = CONV_RULE(funpow 4 RAND_CONV REAL_RAT_REDUCE_CONV) th5 in
    let th7 = CONV_RULE (funpow 3 RAND_CONV REAL_RAT_REDUCE_CONV) th6 in
    CONV_RULE(RAND_CONV(ONCE_DEPTH_CONV LN_N_CONV)) th7;;

(* ------------------------------------------------------------------------- *)
(* Lemmas about floor and frac.                                              *)
(* ------------------------------------------------------------------------- *)

let FLOOR_DOUBLE_NUM = prove
 (`!n r d.
        d < 2 /\ 0 < r
        ==> &2 * floor(&n / &r) <= floor(&(2 * n + d) / &r) /\
            floor(&(2 * n + d) / &r) <= &2 * floor(&n / &r) + &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `floor(&n / &r) = floor((&n + &d / &2) / &r)` SUBST1_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&2 * &n + &d = &2 * (&n + &d / &2)` SUBST1_TAC THENL
     [SIMP_TAC[REAL_ADD_LDISTRIB; REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; GSYM REAL_MUL_ASSOC; real_div] THEN
    REWRITE_TAC[GSYM real_div; FLOOR_DOUBLE]] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
  MP_TAC(SPEC `&n / &r` FLOOR) THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n / &r` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_div; REAL_ADD_RDISTRIB; REAL_LE_ADDR] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_INV_EQ];
    ALL_TAC] THEN
  UNDISCH_TAC `&n / &r < floor (&n / &r) + &1` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
  SIMP_TAC[REAL_LT_INTEGERS; FLOOR; INTEGER_CLOSED] THEN
  MATCH_MP_TAC(REAL_ARITH `b < a ==> n + a <= c ==> n + b < c`) THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Range bounds on ln(n!).                                                   *)
(* ------------------------------------------------------------------------- *)

let LN_FACT = prove
 (`!n. ln(&(FACT n)) = sum(1,n) (\d. ln(&d))`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; sum; LN_1] THEN
  SIMP_TAC[GSYM REAL_OF_NUM_MUL; LN_MUL; REAL_OF_NUM_LT; FACT_LT; LT_0] THEN
  ASM_REWRITE_TAC[ADD1] THEN REWRITE_TAC[ADD_AC; REAL_ADD_AC]);;

let LN_FACT_BOUNDS = prove
 (`!n. ~(n = 0) ==> abs(ln(&(FACT n)) - (&n * ln(&n) - &n)) <= &1 + ln(&n)`,
  SUBGOAL_THEN
   `!n. ~(n = 0)
        ==> ?z. &n < z /\ z < &(n + 1) /\
                (&(n + 1) * ln(&(n + 1)) - &n * ln(&n) = ln(z) + &1)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`\x. x * ln(x)`; `\x. ln(x) + &1`; `&n`; `&(n + 1)`]
                 MVT_ALT) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(n + &1) - n = &1`] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_ARITH `a < a + &1`] THEN
    X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real` (DIFF_CONV `\x. x * ln(x)`)) THEN
    SIMP_TAC[REAL_MUL_LID; REAL_MUL_RID; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
    DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `&n` THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `~(n = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num->real`) THEN
  SUBGOAL_THEN
   `!n. &(n + 1) * ln(&(n + 1)) = sum(1,n) (\i. ln(k i) + &1)`
  MP_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
    REWRITE_TAC[sum; ADD_CLAUSES; LN_1; REAL_MUL_RZERO] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n + 1`) THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = n + 2`;
                ARITH_RULE `SUC(n + 1) = n + 2`] THEN
    DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
    REWRITE_TAC[REAL_ARITH `(a - b = c) <=> (a = b + c)`] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_AC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_ADD] THEN
  CONV_TAC(LAND_CONV(BINDER_CONV(RAND_CONV(RAND_CONV(LAND_CONV
    (LAND_CONV num_CONV)))))) THEN
  REWRITE_TAC[ADD1; SUM_REINDEX; SUM_CONST] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a = b + c * &1) <=> (b = a - c)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. abs(sum(1,n+1) (\i. ln(&i)) - (&(n + 1) * ln (&(n + 1)) - &(n + 1)))
        <= &1 + ln(&(n + 1))`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o funpow 3 RAND_CONV)
     [GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC(REAL_ARITH
     `abs(x - (y - z)) <= a ==> abs(x - (y - (z + &1))) <= &1 + a`) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o RAND_CONV o RAND_CONV) [GSYM th]) THEN
    SUBGOAL_THEN
     `sum(1,n + 1) (\i. ln (&i)) = sum(1,n) (\i. ln(&(i + 1)))`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [SUM_DIFF] THEN
      REWRITE_TAC[SUM_1; ADD_CLAUSES; LN_1; REAL_SUB_RZERO] THEN
      GEN_REWRITE_TAC (funpow 3 LAND_CONV) [SYM(NUM_REDUCE_CONV `0 + 1`)] THEN
      REWRITE_TAC[SUM_REINDEX] THEN REWRITE_TAC[ADD_AC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_SUB] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1,n) (\n. abs(ln(&(n + 1)) - ln(k n)))` THEN
    REWRITE_TAC[ABS_SUM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1,n) (\i. ln(&(i + 1)) - ln(&i))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `a < b /\ b < c ==> abs(c - b) <= c - a`) THEN
      SUBGOAL_THEN `&0 < &r /\ &r < k r /\ k r < &(r + 1)` MP_TAC THENL
       [ALL_TAC; MESON_TAC[LN_MONO_LT; REAL_LT_TRANS]] THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < r <=> 1 <= r`;
                   ARITH_RULE `~(r = 0) <=> 1 <= r`];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_SUB] THEN
    REWRITE_TAC[GSYM(SPECL [`f:num->real`; `m:num`; `1`] SUM_REINDEX)] THEN
    ONCE_REWRITE_TAC[SUM_DIFF] THEN
    REWRITE_TAC[ARITH; SUM_2; SUM_1; LN_1; REAL_ADD_RID] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 + n = SUC(1 + n)`] THEN
    REWRITE_TAC[sum; ADD_CLAUSES] THEN
    REWRITE_TAC[ADD_AC] THEN
    REWRITE_TAC[REAL_ARITH `(a + b) - c - (a - c) = b`; REAL_LE_REFL];
    ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  ASM_REWRITE_TAC[ADD1; LN_FACT]);;

(* ------------------------------------------------------------------------- *)
(* Some extra number-theoretic odds and ends are useful.                     *)
(* ------------------------------------------------------------------------- *)

let primepow = new_definition
  `primepow q <=> ?p k. 1 <= k /\ prime p /\ (q = p EXP k)`;;

let aprimedivisor = new_definition
  `aprimedivisor q = @p. prime p /\ p divides q`;;

let PRIMEPOW_GE_2 = prove
 (`!q. primepow q ==> 2 <= q`,
  REWRITE_TAC[primepow; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`q:num`; `p:num`; `k:num`] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p:num` THEN
  ASM_SIMP_TAC[PRIME_GE_2] THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[LE_EXP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH]);;

let PRIMEPOW_0 = prove
 (`~(primepow 0)`,
  MESON_TAC[NUM_REDUCE_CONV `2 <= 0`; PRIMEPOW_GE_2]);;

let APRIMEDIVISOR_PRIMEPOW = prove
 (`!p k. prime p /\ 1 <= k ==> (aprimedivisor(p EXP k) = p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aprimedivisor] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN REWRITE_TAC[] THEN
  X_GEN_TAC `q:num` THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `1 <= k ==> (k = SUC(k - 1))`)) THEN
  REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_RMUL; PRIME_DIVEXP; PRIME_DIVPROD;
                prime; PRIME_1]);;

let APRIMEDIVISOR = prove
 (`!n. ~(n = 1) ==> prime(aprimedivisor n) /\ (aprimedivisor n) divides n`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[aprimedivisor] THEN
  CONV_TAC SELECT_CONV THEN ASM_SIMP_TAC[PRIME_FACTOR]);;

let BIG_POWER_LEMMA = prove
 (`!m n. 2 <= m ==> ?k. n <= m EXP k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `SUC n` THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP (SUC n)` THEN
  ASM_REWRITE_TAC[EXP_MONO_LE_SUC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN
  REWRITE_TAC[EXP; ARITH] THEN
  UNDISCH_TAC `n <= 2 EXP SUC n` THEN REWRITE_TAC[EXP] THEN
  MP_TAC(SPECL [`2:num`; `n:num`] EXP_EQ_0) THEN
  REWRITE_TAC[ARITH] THEN SPEC_TAC(`2 EXP n`,`m:num`) THEN ARITH_TAC);;

let PRIME_PRIMEPOW = prove
 (`!p. prime p ==> primepow p`,
  MESON_TAC[prime; primepow; LE_REFL; EXP_1]);;

(* ------------------------------------------------------------------------- *)
(* Derive Bezout-type identity by finding gcd.                               *)
(* ------------------------------------------------------------------------- *)

let rec bezout (m,n) =
  if m =/ Int 0 then (Int 0,Int 1) else if n =/ Int 0 then (Int 1,Int 0)
  else if m <=/ n then
    let q = quo_num n m and r = mod_num n m in
    let (x,y) = bezout(m,r) in
    (x -/ q */ y,y)
  else let (x,y) = bezout(n,m) in (y,x);;

(* ------------------------------------------------------------------------- *)
(* Conversion for "primepow" applied to particular numeral.                  *)
(* ------------------------------------------------------------------------- *)

let PRIMEPOW_CONV =
  let pth0 = prove
   (`primepow 0 <=> F`,
    REWRITE_TAC[primepow] THEN MESON_TAC[EXP_EQ_0; PRIME_0])
  and pth1 = prove
   (`primepow 1 <=> F`,
    REWRITE_TAC[primepow] THEN
    MESON_TAC[EXP_EQ_1; PRIME_1; NUM_REDUCE_CONV `1 <= 0`])
  and pth2 = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (primepow q <=> T)`,
    MESON_TAC[primepow])
  and pth3 = prove
   (`(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (primepow q <=> F)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `r:num` PRIME_FACTOR) THEN
    MP_TAC(SPEC `p:num` PRIME_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P_p:num` MP_TAC) THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_p:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `P_r:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_r:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `P_p divides P /\ P_r divides P` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[divides; MULT_AC]; ALL_TAC] THEN
    SUBGOAL_THEN `(P_p = P) /\ (P_r = P:num)` (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_ADD_REVR; divides; MULT_AC; DIVIDES_ONE; prime])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and r_tm = `r:num` and d_tm = `d:num`
  and x_tm = `x:num` and y_tm = `y:num` and primepow_tm = `primepow` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> primepow_tm then failwith "expected primepow(numeral)" else
    let q = dest_numeral tm in
    if q =/ Int 0 then pth0
    else if q =/ Int 1 then pth1 else
    match factor q with
      [] -> failwith "internal failure in PRIMEPOW_CONV"
    | [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth2 in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | (p,_)::(r,_)::_ ->
               let d = q // (p */ r) in
               let (x,y) = bezout(p,r) in
               let p,r,x,y =
                 if x </ Int 0 then r,p,y,minus_num x
                 else p,r,x,minus_num y in
               let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral r,r_tm;
                               mk_numeral x,x_tm;
                               mk_numeral y,y_tm;
                               mk_numeral d,d_tm] pth3 in
               MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))));;

(* ------------------------------------------------------------------------- *)
(* Conversion for "aprimedivisor" applied to prime power (only).             *)
(* ------------------------------------------------------------------------- *)

let APRIMEDIVISOR_CONV =
  let pth = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (aprimedivisor q = p)`,
    MESON_TAC[APRIMEDIVISOR_PRIMEPOW])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and aprimedivisor_tm = `aprimedivisor` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> aprimedivisor_tm then failwith "expected primepow(numeral)" else
    let q = dest_numeral tm in
    if q =/ Int 0 then failwith "APRIMEDIVISOR_CONV: not a prime power" else
    match factor q with
      [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | _ -> failwith "APRIMEDIVISOR_CONV: not a prime power";;

(* ------------------------------------------------------------------------- *)
(* The Mangoldt function.                                                    *)
(* ------------------------------------------------------------------------- *)

let mangoldt = new_definition
  `mangoldt d = if primepow d then ln(&(aprimedivisor d)) else &0`;;

let MANGOLDT_POS = prove
 (`!d. &0 <= mangoldt d`,
  GEN_TAC THEN REWRITE_TAC[mangoldt] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW; ARITH_RULE `2 <= a ==> 1 <= a`;
                PRIME_GE_2; LN_POS; REAL_OF_NUM_LE; primepow]);;

(* ------------------------------------------------------------------------- *)
(* The key lemma.                                                            *)
(* ------------------------------------------------------------------------- *)

let LN_PRIMEFACT = prove
 (`!n. ~(n = 0)
       ==> (ln(&n) =
            sum(1,n) (\d. if primepow d /\ d divides n
                          then ln(&(aprimedivisor d)) else &0))`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 1` THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1,n) (\d. &0)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUM_0; LN_1]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[PRIMEPOW_GE_2; DIVIDES_LE; NUM_REDUCE_CONV `2 <= 1`;
                  LE_TRANS];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_FACTOR) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `m < p * m <=> 1 * m < p * m`] THEN
    SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 < p <=> 2 <= p`] THEN
    ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  DISCH_THEN(K ALL_TAC) THEN
  SUBGOAL_THEN `?k. 1 <= k /\ (p EXP k) divides (p * m)` MP_TAC THENL
   [EXISTS_TAC `1` THEN SIMP_TAC[EXP_1; DIVIDES_RMUL; DIVIDES_REFL; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. !j. 1 <= j /\ (p EXP j) divides (p * m) ==> j <= k`
  MP_TAC THENL
   [MP_TAC(SPECL [`p:num`; `p * m:num`] BIG_POWER_LEMMA) THEN
    ASM_SIMP_TAC[PRIME_GE_2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[MULT_EQ_0] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p EXP k` THEN
    ASM_REWRITE_TAC[LT_EXP] THEN ASM_SIMP_TAC[PRIME_GE_2];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  GEN_REWRITE_TAC LAND_CONV [num_MAX] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `sum (1,m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0) =
    sum (1,p * m)
     (\d. if primepow d /\ d divides m then ln (&(aprimedivisor d)) else &0)`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SUM_DIFF] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `1 + p * m = (1 + m) + (p * m - m)` SUBST1_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE
        `1 * y <= x ==> (1 + x = (1 + y) + (x - y))`) THEN
      SIMP_TAC[LE_MULT_RCANCEL] THEN
      ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SUM_TWO] THEN
    MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a = a + b)`) THEN
    SUBGOAL_THEN
     `!d. d >= 1 + m
          ==> ((if primepow d /\ d divides m then ln (&(aprimedivisor d))
                else &0) = &0)`
    MP_TAC THENL
     [X_GEN_TAC `d:num` THEN REWRITE_TAC[GE] THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(1 + m <= d /\ d <= m)`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUM_ZERO) THEN DISCH_THEN MATCH_MP_TAC THEN
    ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[PRIMEPOW_0; REAL_SUB_RZERO] THEN
  SUBGOAL_THEN `1 + p * m = p EXP k + 1 + (p * m - p EXP k)` SUBST1_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `k <= p ==> (1 + p = k + 1 + (p - k))`) THEN
    ASM_MESON_TAC[DIVIDES_LE; MULT_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_TWO] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(a = a') /\ (l + b = c) ==> (l + a + b = a' + c)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `d:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN STRIP_TAC THEN
    ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `d divides (p * m) <=> d divides m`
     (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `primepow d` THEN REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_CASES_TAC `q = p:num` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MATCH_MP_TAC(TAUT `(b ==> a) /\ b ==> (a <=> b)`) THEN
      REWRITE_TAC[DIVIDES_LMUL] THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN
      EXISTS_TAC `p EXP (k - 1)` THEN CONJ_TAC THENL
       [REWRITE_TAC[divides] THEN EXISTS_TAC `p EXP ((k - 1) - j)` THEN
        REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `p EXP j < p EXP k` THEN ASM_REWRITE_TAC[LT_EXP] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `p EXP k divides (p * m)` THEN
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV o RAND_CONV)
                  [th]) o MATCH_MP
          (ARITH_RULE `1 <= k ==> (k = SUC(k - 1))`)) THEN
      REWRITE_TAC[divides; EXP] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EQ_TAC THEN REWRITE_TAC[DIVIDES_LMUL] THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
    DISCH_THEN(fun th -> ASSUME_TAC th THEN
      MP_TAC(AP_TERM `(divides) p` th)) THEN
    SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `p divides (q EXP j) \/ p divides r` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
    DISCH_THEN DISJ_CASES_TAC THENL
     [SUBGOAL_THEN `p divides q` MP_TAC THENL
       [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
      ASM_MESON_TAC[prime; PRIME_1];
      ALL_TAC] THEN
    UNDISCH_TAC `p * m = q EXP j * r` THEN
    UNDISCH_TAC `p divides r` THEN
    REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
    ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
    SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN REWRITE_TAC[SUM_1] THEN
  REWRITE_TAC[REAL_ADD_ASSOC] THEN BINOP_TAC THENL
   [SUBGOAL_THEN `primepow (p EXP k)` ASSUME_TAC THENL
     [ASM_MESON_TAC[primepow]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((p EXP k) divides m)` ASSUME_TAC THENL
     [REWRITE_TAC[divides] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
      MP_TAC(ARITH_RULE `~(k + 1 <= k)`) THEN REWRITE_TAC[] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[ARITH_RULE `1 <= k + 1`] THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN
      MESON_TAC[MULT_ASSOC; DIVIDES_REFL; DIVIDES_RMUL];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[ADD_CLAUSES; LE_0] THEN STRIP_TAC THEN
  ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d divides (p * m) <=> d divides m`
   (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `primepow d` THEN REWRITE_TAC[primepow] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `q = p:num` THENL
   [UNDISCH_THEN `q = p:num` SUBST_ALL_TAC THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MATCH_MP_TAC(TAUT `(b ==> a) /\ ~a ==> (a <=> b)`) THEN
    REWRITE_TAC[DIVIDES_LMUL] THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a + 1 <= b ==> a < b`)) THEN
    REWRITE_TAC[LT_EXP] THEN ASM_SIMP_TAC[PRIME_GE_2; NOT_LT];
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN EQ_TAC THEN REWRITE_TAC[DIVIDES_LMUL] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    MP_TAC(AP_TERM `(divides) p` th)) THEN
  SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL] THEN DISCH_TAC THEN
  SUBGOAL_THEN `p divides (q EXP j) \/ p divides r` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD]; ALL_TAC] THEN
  DISCH_THEN DISJ_CASES_TAC THENL
   [SUBGOAL_THEN `p divides q` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVEXP]; ALL_TAC] THEN
    ASM_MESON_TAC[prime; PRIME_1];
    ALL_TAC] THEN
  UNDISCH_TAC `p * m = q EXP j * r` THEN
  UNDISCH_TAC `p divides r` THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c:num`] THEN
  SIMP_TAC[EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The key expansion using the Mangoldt function.                            *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT = prove
 (`!n. ln(&(FACT n)) = sum(1,n) (\d. mangoldt(d) * floor(&n / &d))`,
  GEN_TAC THEN REWRITE_TAC[LN_FACT] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1,n) (\m. sum(1,n) (\d. if primepow d /\ d divides m
                                then ln (&(aprimedivisor d))
                                else &0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[LN_PRIMEFACT; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `d < n + 1 ==> (n = d + (n - d))`)) THEN
    DISCH_THEN(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[GSYM SUM_SPLIT] THEN
    REWRITE_TAC[REAL_ARITH `(a = a + b) <=> (b = &0)`] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `sum(1 + d,n - d) (\k. &0)` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE
     `1 <= d /\ 1 + d <= r /\ (r <= d \/ (d = 0)) ==> F`];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_SWAP] THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `d:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[mangoldt] THEN
  ASM_CASES_TAC `primepow d` THEN ASM_REWRITE_TAC[SUM_0; REAL_MUL_LZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 <= d ==> ~(d = 0)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV d`; `r = n MOD d`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  SUBGOAL_THEN `floor (&(q * d + r) / &d) = &q` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[GSYM FLOOR_UNIQUE] THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ;
                 REAL_OF_NUM_LT; ARITH_RULE `0 < d <=> 1 <= d`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `r < d:num` THEN ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) /\ (a = c) ==> (a + b = c)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1 + q * d,r) (\x. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[] THEN
    X_GEN_TAC `s:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `d divides s` THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `1 + x <= y * z ==> x < z * y`)) THEN
    ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    REWRITE_TAC[LT_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:num` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `d * (q + SUC e) < r + 1 + q * d` THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES; GSYM ADD_ASSOC] THEN
    REWRITE_TAC[ARITH_RULE `d * q + x < y + 1 + q * d <=> x <= y`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE `a + b <= c ==> a <= c:num`)) THEN
    ASM_REWRITE_TAC[NOT_LE];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SUM_DIFF] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[GSYM SUM_TWO] THEN
  SIMP_TAC[SUM_1; DIVIDES_0; DIVIDES_LMUL; DIVIDES_REFL] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) - b = a`] THEN
  REWRITE_TAC[GSYM SUM_GROUP] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(0,q) (\x. ln (&(aprimedivisor d)))` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_CONST; REAL_MUL_AC]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
    `1 <= d ==> (d = 1 + (d - 1))`)) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC
    (funpow 2 LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; SUM_1] THEN
  SIMP_TAC[DIVIDES_LMUL; DIVIDES_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a + b = a)`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum(m * d + 1,d - 1) (\x. &0)` THEN CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `s:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [LE_EXISTS] THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` SUBST_ALL_TAC) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(d divides (t + 1))` MP_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    UNDISCH_TAC `t + m * d + 1 < d - 1 + m * d + 1` THEN
    REWRITE_TAC[LT_ADD_RCANCEL] THEN
    UNDISCH_TAC `d divides (t + m * d + 1)` THEN
    ASM_CASES_TAC `t = 0` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THENL
     [ASM_MESON_TAC[DIVIDES_REFL; DIVIDES_LMUL; DIVIDES_ADD_REVR;
                    DIVIDES_ONE; PRIMEPOW_GE_2; NUM_REDUCE_CONV `2 <= 1`];
      DISCH_TAC THEN ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `d divides (t + m * d + 1)` THEN
  ONCE_REWRITE_TAC[ARITH_RULE `t + m * d + 1 = (t + 1) + m * d`] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_LMUL; DIVIDES_ADD_REVL]);;

(* ------------------------------------------------------------------------- *)
(* The Chebyshev psi function.                                               *)
(* ------------------------------------------------------------------------- *)

let psi = new_definition
  `psi(n) = sum(1,n) (\d. mangoldt(d))`;;

(* ------------------------------------------------------------------------- *)
(* The key bounds on the psi function.                                       *)
(* ------------------------------------------------------------------------- *)

let PSI_BOUNDS_LN_FACT = prove
 (`!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) <= psi(n) /\
       psi(n) - psi(n DIV 2) <= ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))`,
  X_GEN_TAC `k:num` THEN MP_TAC(SPECL [`k:num`; `2`] DIVISION) THEN
  REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`n = k DIV 2`; `d = k MOD 2`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN
  REWRITE_TAC[psi; MANGOLDT] THEN
  SUBGOAL_THEN
   `sum (1,n) (\d. mangoldt d * floor (&n / &d)) =
    sum (1,2 * n + d) (\d. mangoldt d * floor (&n / &d))`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * n + d = n + (n + d)`] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    REWRITE_TAC[REAL_ARITH `(a = a + b) <=> (b = &0)`] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(1 + n,n + d) (\k. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN REWRITE_TAC[FLOOR_EQ_0] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
     `1 + n <= r ==> 0 < r`)) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_OF_NUM_LT] THEN
    UNDISCH_TAC `1 + n <= r` THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `m * f - &2 * m * f' = m * (f - &2 * f')`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&2 * a <= b /\ b <= &2 * a + &1
      ==> b - &2 * a <= &1`) THEN
    ASM_SIMP_TAC[FLOOR_DOUBLE_NUM; ARITH_RULE `0 < r <=> 1 <= r`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum(1,2 * n + d) (\d. mangoldt d) - sum(1,n) (\d. mangoldt d) =
    sum(1,2 * n + d) (\d. if d <= n then &0 else mangoldt d)`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `2 * n + d = n + (n + d)`] THEN
    ONCE_REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH
     `(c = &0) /\ (b = d) ==> ((a + b) - a = c + d)`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum(1,n) (\k. &0)` THEN CONJ_TAC THENL
       [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
      MATCH_MP_TAC SUM_EQ THEN
      SIMP_TAC[ARITH_RULE `r < n + 1 <=> r <= n`];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[ARITH_RULE `1 + n <= r ==> ~(r <= n)`];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN MATCH_MP_TAC SUM_LE THEN
  X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `m * a - &2 * m * b = m * (a - &2 * b)`] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
    ASM_SIMP_TAC[REAL_SUB_LE; FLOOR_DOUBLE_NUM; ARITH_RULE `0 < r <=> 1 <= r`];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `a = a * &1`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[MANGOLDT_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `(b = &0) /\ &1 <= a ==> &1 <= a - &2 * b`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FLOOR_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < r <=> 1 <= r`] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_POS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_REWRITE_TAC[GSYM NOT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a = &1) ==> &1 <= a`) THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < r <=> 1 <= r`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_MUL;
              REAL_OF_NUM_ADD] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Map the middle term into multiples of log(n).                             *)
(* ------------------------------------------------------------------------- *)

let LN_FACT_DIFF_BOUNDS = prove
 (`!n. abs((ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2)))) - &n * ln(&2))
       <= &4 * ln(if n = 0 then &1 else &n) + &3`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[FACT; MULT_CLAUSES; LN_1; DIV_0; ARITH_EQ] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ASM_REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_CASES_TAC `q = 0` THENL
   [UNDISCH_TAC `~(q * 2 + r = 0)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `r < 2 ==> ((r = 0) <=> ~(r = 1))`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    REWRITE_TAC[num_CONV `1`; FACT; MULT_CLAUSES] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LN_1] THEN
    REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_SUB_RZERO] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_SUB_LZERO; REAL_ADD_LID; REAL_MUL_LID] THEN
    REWRITE_TAC[REAL_ABS_NEG] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= &2 ==> x <= &3`) THEN
    SUBST1_TAC(REAL_ARITH `&2 = &1 + &1`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x <= &1 ==> abs(x) <= &1 + &1`) THEN
    ASM_SIMP_TAC[LN_POS; LN_LE; REAL_OF_NUM_LE; ARITH; REAL_LE_ADDL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a'. abs((a' - b) - c) <= d - abs(a' - a) ==> abs((a - b) - c) <= d`) THEN
  EXISTS_TAC `ln(&(FACT(q * 2)))` THEN
  MP_TAC(SPEC `q:num` LN_FACT_BOUNDS) THEN
  MP_TAC(SPEC `q * 2` LN_FACT_BOUNDS) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; ARITH_EQ] THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(a - (a2 - &2 * a1)) <= b - &2 * b1 - b2
    ==> abs(l2 - a2) <= b2
        ==> abs(l1 - a1) <= b1
            ==> abs((l2 - &2 * l1) - a) <= b`) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `0 < q <=> ~(q = 0)`] THEN
  REWRITE_TAC[REAL_ARITH
   `(q * &2 + r) * l2 - ((q * &2) * (lq + l2) - q * &2 - &2 * (q * lq - q)) =
    r * l2`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `x <= a - b - c - d <=> x + b <= a - c - d`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `ln(&2) + ln(&q * &2 + &r)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ x <= &1 * y ==> abs(x) <= y`) THEN
      SIMP_TAC[LN_POS_LT; REAL_LT_IMP_LE; REAL_LE_RMUL_EQ;
               REAL_LE_MUL; REAL_POS; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN UNDISCH_TAC `r < 2` THEN ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o MATCH_MP (ARITH_RULE
     `r < 2 ==> (r = 0) \/ (r = 1)`))
    THENL
     [REWRITE_TAC[ADD_CLAUSES; REAL_SUB_REFL; REAL_ADD_RID; REAL_ABS_NUM] THEN
      MATCH_MP_TAC LN_POS THEN
      REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_MUL] THEN
      UNDISCH_TAC `~(q = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM ADD1; FACT] THEN
    SIMP_TAC[GSYM REAL_OF_NUM_MUL; LN_MUL; REAL_OF_NUM_LT;
             FACT_LT; LT_0] THEN
    REWRITE_TAC[REAL_ARITH `abs(b - (a + b)) = abs a`] THEN
    REWRITE_TAC[ADD1; GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_ADD;
                GSYM REAL_OF_NUM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> abs(x) <= x`) THEN
    MATCH_MP_TAC LN_POS THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH
   `l2 + lnn <= (&4 * lnn + &3) - a - b
    <=> a + b + l2 <= &3 * lnn + &3`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&3 * ln(&q * &2) + &3` THEN CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_LE_RADD; REAL_LE_LMUL_EQ; REAL_OF_NUM_LT; ARITH] THEN
    ASM_SIMP_TAC[LN_MONO_LE; REAL_POS; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < q <=> ~(q = 0)`;
                 REAL_ARITH `&0 < q /\ &0 <= r ==> &0 < q * &2 + r`;
                 REAL_ARITH `&0 < q ==> &0 < q * &2`] THEN
    REWRITE_TAC[REAL_LE_ADDR; REAL_POS]] THEN
  ASM_SIMP_TAC[LN_MUL; REAL_OF_NUM_LT; ARITH;
               ARITH_RULE `0 < q <=> ~(q = 0)`] THEN
  SUBGOAL_THEN `&0 <= ln(&2)` (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  MATCH_MP_TAC LN_POS THEN REWRITE_TAC[REAL_OF_NUM_LE; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Hence overall bounds in terms of n * log(2) + constant.                   *)
(* ------------------------------------------------------------------------- *)

let PSI_BOUNDS_INDUCT = prove
 (`!n. &n * ln(&2) - (&4 * ln (if n = 0 then &1 else &n) + &3) <= psi(n) /\
       psi(n) - psi(n DIV 2)
       <= &n * ln(&2) + (&4 * ln (if n = 0 then &1 else &n) + &3)`,
  MESON_TAC[PSI_BOUNDS_LN_FACT; LN_FACT_DIFF_BOUNDS; REAL_ARITH
             `m <= a /\ b <= m /\ abs(m - n) <= k
              ==> n - k <= a /\ b <= n + k`]);;

(* ------------------------------------------------------------------------- *)
(* Evaluation of mangoldt(numeral).                                          *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_CONV =
  GEN_REWRITE_CONV I [mangoldt] THENC
  RATOR_CONV(LAND_CONV PRIMEPOW_CONV) THENC
  GEN_REWRITE_CONV I [COND_CLAUSES] THENC
  TRY_CONV(funpow 2 RAND_CONV APRIMEDIVISOR_CONV);;

(* ------------------------------------------------------------------------- *)
(* More efficient version without two primality tests.                       *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_CONV =
  let pth0 = prove
   (`mangoldt 0 = ln(&1)`,
    REWRITE_TAC[mangoldt; primepow; LN_1] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[EXP_EQ_0; PRIME_0])
  and pth1 = prove
   (`mangoldt 1 = ln(&1)`,
    REWRITE_TAC[mangoldt; primepow; LN_1] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[EXP_EQ_1; PRIME_1; NUM_REDUCE_CONV `1 <= 0`])
  and pth2 = prove
   (`prime p ==> 1 <= k /\ (q = p EXP k) ==> (mangoldt q = ln(&p))`,
    SIMP_TAC[mangoldt; APRIMEDIVISOR_PRIMEPOW] THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[primepow])
  and pth3 = prove
   (`(p * x = r * y + 1) /\ ~(p = 1) /\ ~(r = 1) /\ (q = p * r * d)
     ==> (mangoldt q = ln(&1))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(primepow q)`
     (fun th -> REWRITE_TAC[LN_1; th; mangoldt]) THEN
    REWRITE_TAC[primepow] THEN
    DISCH_THEN(X_CHOOSE_THEN `P:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(SPEC `r:num` PRIME_FACTOR) THEN
    MP_TAC(SPEC `p:num` PRIME_FACTOR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `P_p:num` MP_TAC) THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_p:num` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `P_r:num` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `d_r:num` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `P_p divides P /\ P_r divides P` ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k:num` THEN
      ASM_MESON_TAC[divides; MULT_AC]; ALL_TAC] THEN
    SUBGOAL_THEN `(P_p = P) /\ (P_r = P:num)` (CONJUNCTS_THEN SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    ASM_MESON_TAC[DIVIDES_ADD_REVR; divides; MULT_AC; DIVIDES_ONE; prime])
  and p_tm = `p:num` and k_tm = `k:num` and q_tm = `q:num`
  and r_tm = `r:num` and d_tm = `d:num`
  and x_tm = `x:num` and y_tm = `y:num` and mangoldt_tm = `mangoldt` in
  fun tm0 ->
    let ptm,tm = dest_comb tm0 in
    if ptm <> mangoldt_tm then failwith "expected mangoldt(numeral)" else
    let q = dest_numeral tm in
    if q =/ Int 0 then pth0
    else if q =/ Int 1 then pth1 else
    match factor q with
      [] -> failwith "internal failure in MANGOLDT_CONV"
    | [p,k] -> let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral k,k_tm] pth2 in
               let th2 = MP th1 (EQT_ELIM(PRIME_CONV(lhand(concl th1)))) in
               MP th2 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th2))))
    | (p,_)::(r,_)::_ ->
               let d = q // (p */ r) in
               let (x,y) = bezout(p,r) in
               let p,r,x,y =
                 if x </ Int 0 then r,p,y,minus_num x
                 else p,r,x,minus_num y in
               let th1 = INST [mk_numeral q,q_tm;
                               mk_numeral p,p_tm;
                               mk_numeral r,r_tm;
                               mk_numeral x,x_tm;
                               mk_numeral y,y_tm;
                               mk_numeral d,d_tm] pth3 in
               MP th1 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th1))));;

(* ------------------------------------------------------------------------- *)
(* Hence an evaluation function for psi, applied to all n <= some N.         *)
(* ------------------------------------------------------------------------- *)

let PSI_LIST =
  let PSI_0 = prove
   (`psi(0) = ln(&1)`,
    REWRITE_TAC[psi; sum; LN_1])
  and PSI_SUC = prove
   (`psi(SUC n) = psi(n) + mangoldt(SUC n)`,
    REWRITE_TAC[psi; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    SIMP_CONV [REAL_ADD_RID; GSYM LN_MUL; REAL_OF_NUM_MUL;
               REAL_OF_NUM_LT; ARITH] in
  let rec PSI_LIST n =
    if n = 0 then [PSI_0] else
    let ths = PSI_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] PSI_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    let th3 = CONV_RULE(COMB_CONV (funpow 2 RAND_CONV NUM_SUC_CONV)) th2 in
    let th4 = CONV_RULE (funpow 2 RAND_CONV MANGOLDT_CONV) th3 in
    (CONV_RULE(RAND_CONV SIMPER_CONV) th4)::ths in
  PSI_LIST;;

(* ------------------------------------------------------------------------- *)
(* Run it up to 300.                                                         *)
(* ------------------------------------------------------------------------- *)

let PSI_LIST_300 = PSI_LIST 300;;

(* ------------------------------------------------------------------------- *)
(* Prove a sharpish linear bound on psi(n) for n <= 128.                     *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_128 = prove
 (`!n. n <= 128 ==> psi(n) <= &133 / &128 * &n`,
  let lemma = prove
   (`a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REWRITE_TAC[ARITH_RULE `n <= 128 <=> n < 129`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC(PSI_LIST_300) THEN
  REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT
   ((MATCH_MP_TAC lemma THEN
     CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
    ORELSE
     (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
    ORELSE tac));;

(* ------------------------------------------------------------------------- *)
(* As a multiple of log(2) is often more useful.                             *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_128_LOG = prove
 (`!n. n <= 128 ==> psi(n) <= (&3 / &2 * ln(&2)) * &n`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PSI_UBOUND_128) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV));;

(* ------------------------------------------------------------------------- *)
(* Useful "overpowering" lemma.                                              *)
(* ------------------------------------------------------------------------- *)

let OVERPOWER_LEMMA = prove
 (`!f g d a.
        f(a) <= g(a) /\
        (!x. a <= x ==> ((\x. g(x) - f(x)) diffl (d(x)))(x)) /\
        (!x. a <= x ==> &0 <= d(x))
        ==> !x. a <= x ==> f(x) <= g(x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. g(x) - f(x)`; `d:real->real`; `a:real`; `x:real`]
               MVT_ALT) THEN
  UNDISCH_TAC `a <= x` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `x:real = a` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `fa <= ga /\ &0 <= d ==> (gx - fx - (ga - fa) = d) ==> fx <= gx`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Repeatedly extend range of explicit cases using recurrence.               *)
(* ------------------------------------------------------------------------- *)

let DOUBLE_CASES_RULE th =
  let bod = snd(dest_forall(concl th)) in
  let ant,cons = dest_imp bod in
  let m = dest_numeral (rand ant)
  and c = rat_of_term (lhand(lhand(rand cons))) in
  let x = float_of_num(m +/ Int 1) in
  let d = (4.0 *. log x +. 3.0) /. (x *. log 2.0) in
  let c' = c // Int 2 +/ Int 1 +/
           (floor_num(num_of_float(1024.0 *. d)) +/ Int 2) // Int 1024 in
  let c'' = max_num c c' in
  let tm = mk_forall
   (`n:num`,
    subst [mk_numeral(Int 2 */ m),rand ant;
          term_of_rat c'',lhand(lhand(rand cons))] bod) in
  prove(tm,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC (mk_comb(`(<=) (n:num)`,mk_numeral m)) THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP th) THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
    SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `pn2 <= ((a - &1) * l2) * n - logtm
      ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
    MP_TAC(SPEC `n DIV 2` th) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
      FIRST_ASSUM(UNDISCH_TAC o check ((not) o is_neg) o concl) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    W(fun (asl,w) ->
       MATCH_MP_TAC REAL_LE_TRANS THEN
       EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ALL_TAC] THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
    MATCH_MP_TAC(REAL_ARITH
     `logtm <= ((c - a * b) * l2) * n
      ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
     `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `a <= n ==> a - &1 <= n - &1`)) THEN
    ABBREV_TAC `x = &n - &1` THEN
    CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
    SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    MATCH_MP_TAC OVERPOWER_LEMMA THEN
    W(fun (asl,w) ->
        let th = DIFF_CONV
         (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
        MP_TAC th) THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
      REAL_MUL_RID; REAL_MUL_LID] THEN
    W(fun (asl,w) ->
        let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
        DISCH_TAC THEN EXISTS_TAC tm) THEN
    CONJ_TAC THENL
     [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
      CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
      CONV_TAC REALCALC_REL_CONV;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [GEN_TAC THEN
      DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
                 inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV);;

(* ------------------------------------------------------------------------- *)
(* Bring it to the self-sustaining point.                                    *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_1024_LOG = funpow 3 DOUBLE_CASES_RULE PSI_UBOUND_128_LOG;;

(* ------------------------------------------------------------------------- *)
(* A generic proof of the same kind that we're self-sustaining.              *)
(* ------------------------------------------------------------------------- *)

let PSI_BOUNDS_SUSTAINED_INDUCT = prove
 (`&4 * ln(&1 + &2 pow j) + &3 <= (d * ln(&2)) * (&1 + &2 pow j) /\
   &4 / (&1 + &2 pow j) <= d * ln(&2) /\ &0 <= c /\ c / &2 + d + &1 <= c
   ==> !k. j <= k /\
           (!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
           ==> !n. n <= 2 EXP (SUC k) ==> psi(n) <= (c * ln(&2)) * &n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n <= 2 EXP k` THEN ASM_SIMP_TAC[] THEN
  MP_TAC(SPEC `n:num` PSI_BOUNDS_INDUCT) THEN
  SUBGOAL_THEN `~(n = 0)` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC(ARITH_RULE `!a. ~(a = 0) /\ ~(n <= a) ==> ~(n = 0)`) THEN
    EXISTS_TAC `2 EXP k` THEN ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `pn2 <= ((a - &1) * l2) * n - logtm
    ==> u <= v /\ pn - pn2 <= n * l2 + logtm ==> pn <= (a * l2) * n`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n DIV 2`) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LE_LDIV_EQ; ARITH] THEN
    MATCH_MP_TAC(ARITH_RULE `n <= 2 * k ==> n < 2 * (k + 1)`) THEN
    ASM_REWRITE_TAC[GSYM(CONJUNCT2 EXP)];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  W(fun (asl,w) ->
     MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC(mk_comb(rator(lhand w),`&n / &2`))) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LN_POS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
    MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [real_div] THEN
  MATCH_MP_TAC(REAL_ARITH
   `logtm <= ((c - a * b) * l2) * n
    ==> (a * l2) * n * b <= (c * l2) * n - logtm`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(d * ln (&2)) * &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN SIMP_TAC[LN_POS; REAL_OF_NUM_LE; ARITH] THEN
    REWRITE_TAC[GSYM real_div] THEN
    ASM_REWRITE_TAC[REAL_ARITH `d <= c - &1 - c2 <=> c2 + d + &1 <= c`]] THEN
  SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
  SUBGOAL_THEN `&2 pow j <= &n - &1` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow k` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_POW_MONO; REAL_OF_NUM_LE; ARITH]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
      `~(n <= b) ==> b + 1 <= n`)) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `x = &n - &1` THEN SPEC_TAC(`x:real`,`x:real`) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < a ==> a <= x ==> &0 < &1 + x`) THEN
    SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  X_GEN_TAC `z:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[REAL_LE_LADD] THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH; REAL_ARITH
     `&0 < x ==> &0 < &1 + x`];
    ALL_TAC] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  ASM_REWRITE_TAC[GSYM real_div]);;

let PSI_BOUNDS_SUSTAINED = prove
 (`(!n. n <= 2 EXP k ==> psi(n) <= (c * ln(&2)) * &n)
   ==> &4 * ln(&1 + &2 pow k) + &3
         <= ((c / &2 - &1) * ln(&2)) * (&1 + &2 pow k) /\
       &4 / (&1 + &2 pow k) <= (c / &2 - &1) * ln(&2) /\ &0 <= c
           ==> !n. psi(n) <= (c * ln(&2)) * &n`,
  let lemma = prove
   (`c / &2 + (c / &2 - &1) + &1 <= c`,
    REWRITE_TAC[REAL_ARITH `c2 + (c2 - &1) + &1 = &2 * c2`] THEN
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LE_REFL]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o C CONJ lemma) THEN
  ABBREV_TAC `d = c / &2 - &1` THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP PSI_BOUNDS_SUSTAINED_INDUCT) THEN
  X_GEN_TAC `m:num` THEN
  SUBGOAL_THEN `?j. m <= 2 EXP j` MP_TAC THENL
   [EXISTS_TAC `m:num` THEN SPEC_TAC(`m:num`,`m:num`) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
    REWRITE_TAC[EXP] THEN MATCH_MP_TAC(ARITH_RULE
     `~(a = 0) /\ m <= a ==> SUC m <= 2 * a`) THEN
    ASM_REWRITE_TAC[EXP_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN SPEC_TAC(`m:num`,`m:num`) THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP 0` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[LE_EXP; ARITH_EQ; LE_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `k <= j:num` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `2 EXP (SUC j) <= 2 EXP k`
   (fun th -> ASM_MESON_TAC[th; LE_TRANS]) THEN
  ASM_REWRITE_TAC[LE_EXP; ARITH] THEN
  UNDISCH_TAC `~(k <= j:num)` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Now apply it and get our reasonable bound.                                *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_LOG = prove
 (`!n. psi(n) <= (&4407 / &2048 * ln (&2)) * &n`,
  MP_TAC PSI_UBOUND_1024_LOG THEN
  SUBST1_TAC(SYM(NUM_REDUCE_CONV `2 EXP 10`)) THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP PSI_BOUNDS_SUSTAINED) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
  CONJ_TAC THEN CONV_TAC REALCALC_REL_CONV);;

let PSI_UBOUND_3_2 = prove
 (`!n. psi(n) <= &3 / &2 * &n`,
  GEN_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&4407 / &2048 * ln (&2)) * &n` THEN
  REWRITE_TAC[PSI_UBOUND_LOG] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
  CONV_TAC REALCALC_REL_CONV);;

(* ------------------------------------------------------------------------- *)
(* Now get a lower bound.                                                    *)
(* ------------------------------------------------------------------------- *)

let PSI_LBOUND_3_5 = prove
 (`!n. 4 <= n ==> &3 / &5 * &n <= psi(n)`,
  let lemma = prove
   (`a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  GEN_TAC THEN ASM_CASES_TAC `n < 300` THENL
   [POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
    CONV_TAC EXPAND_CASES_CONV THEN
    REWRITE_TAC(PSI_LIST_300) THEN
    REWRITE_TAC[LN_1; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT
     ((MATCH_MP_TAC lemma THEN
       CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
      ORELSE
       (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
      ORELSE tac);
    ALL_TAC] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MP_TAC(CONJUNCT1 (SPEC `n:num` PSI_BOUNDS_INDUCT)) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= x ==> a <= x`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n < 300) ==> ~(n = 0)`] THEN
  MATCH_MP_TAC(REAL_ARITH `c <= n * (b - a) ==> a * n <= n * b - c`) THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 / &11 * &n` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_POS] THEN
    REWRITE_TAC[real_sub] THEN CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV] THEN
  ABBREV_TAC `x = &n - &1` THEN
  SUBGOAL_THEN `&n = &1 + x` SUBST1_TAC THENL
   [EXPAND_TAC "x" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&299 <= x` MP_TAC THENL
   [EXPAND_TAC "x" THEN REWRITE_TAC[REAL_LE_SUB_LADD] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; ARITH] THEN
    UNDISCH_TAC `~(n < 300)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `inv(&1 + &299)` THEN CONJ_TAC THENL
   [ALL_TAC; CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Now the related theta function.                                           *)
(* ========================================================================= *)

let theta = new_definition
  `theta(n) = sum(1,n) (\p. if prime p then ln(&p) else &0)`;;

(* ------------------------------------------------------------------------- *)
(* An optimized rule to give theta(n) for all n <= some N.                   *)
(* ------------------------------------------------------------------------- *)

let THETA_LIST =
  let THETA_0 = prove
   (`theta(0) = ln(&1)`,
    REWRITE_TAC[theta; sum; LN_1])
  and THETA_SUC = prove
   (`theta(SUC n) = theta(n) + (if prime(SUC n) then ln(&(SUC n)) else &0)`,
    REWRITE_TAC[theta; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV
     [COND_CLAUSES; REAL_ADD_LID; REAL_ADD_RID] THENC
    SIMP_CONV [GSYM LN_MUL; REAL_OF_NUM_MUL; REAL_OF_NUM_LT; ARITH] in
  let rec THETA_LIST n =
    if n = 0 then [THETA_0] else
    let ths = THETA_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] THETA_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    CONV_RULE SIMPER_CONV th2::ths in
  THETA_LIST;;

(* ------------------------------------------------------------------------- *)
(* Split up the psi sum to show close relationship with theta.               *)
(* ------------------------------------------------------------------------- *)

let PRIMEPOW_ODD_EVEN = prove
 (`!p q j k.
     ~(prime(p) /\ prime(q) /\ 1 <= j /\ (p EXP (2 * j) = q EXP (2 * k + 1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * j` THEN
    UNDISCH_TAC `p EXP (2 * j) = q EXP (2 * k + 1)` THEN
    REWRITE_TAC[EXP_ADD; EXP_1] THEN
    ASM_MESON_TAC[divides; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  UNDISCH_TAC `p EXP (2 * j) = p EXP (2 * k + 1)` THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(p = 1)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  REWRITE_TAC[LE_ANTISYM] THEN
  DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN]);;

let PSI_SPLIT = prove
 (`psi(n) = theta(n) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                          then ln(&(aprimedivisor d)) else &0) +
            sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                          then ln(&(aprimedivisor d)) else &0)`,
  REWRITE_TAC[psi; theta; GSYM SUM_ADD] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[mangoldt; primepow] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))) /\
                  ~(?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k + 1))) /\
                  ~(prime r)`
     (fun th -> REWRITE_TAC[th; REAL_ADD_LID]) THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1`;
                  EXP_1; LE_REFL]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` (X_CHOOSE_THEN `m:num` MP_TAC)) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(SPECL [`m:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`k = m DIV 2`; `d = m MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW] THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `d < 2 ==> (d = 0) \/ (d = 1)`)) THEN
  ASM_REWRITE_TAC[PRIME_EXP; ADD_EQ_0; MULT_EQ_0; ARITH_EQ] THENL
   [UNDISCH_TAC `1 <= k * 2 + 0` THEN REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(k * 2 = 1)` (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; ARITH_EVEN]; ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN
           ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
    ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM;
                  ARITH_RULE `~(k = 0) ==> 1 <= k`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = 0` THENL
   [MATCH_MP_TAC(REAL_ARITH
     `(a = a') /\ (b = &0) /\ (c = &0) ==> (a = a' + b + c)`) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[ARITH; EXP_1]; ALL_TAC] THEN
    CONJ_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM]; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `q:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` MP_TAC) THEN STRIP_TAC THEN
    SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
     [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `k * 2 + 1` THEN
      UNDISCH_TAC `p EXP (k * 2 + 1) = q EXP (2 * j + 1)` THEN
      REWRITE_TAC[EXP_ADD; EXP_1] THEN
      ASM_MESON_TAC[divides; MULT_SYM];
      ALL_TAC] THEN
    SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[prime]; ALL_TAC] THEN
    UNDISCH_TAC `p EXP (k * 2 + 1) = p EXP (2 * j + 1)` THEN
    REWRITE_TAC[GSYM LE_ANTISYM] THEN REWRITE_TAC[LE_EXP] THEN
    ASM_CASES_TAC `p = 0` THENL [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
    REWRITE_TAC[LE_ANTISYM] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= j ==> ~(1 = 2 * j + 1)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `(k * 2 + 1 = 1) <=> (k = 0)`; ARITH_EQ] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID]) THEN
  ASM_MESON_TAC[PRIMEPOW_ODD_EVEN; MULT_SYM; ARITH_RULE
   `~(k = 0) ==> 1 <= k`]);;

(* ------------------------------------------------------------------------- *)
(* General lemma about sums.                                                 *)
(* ------------------------------------------------------------------------- *)

let SUM_SURJECT = prove
 (`!f i m n p q.
        (!r. m <= r /\ r < m + n ==> &0 <= f(i r)) /\
        (!s. p <= s /\ s < p + q /\ ~(f(s) = &0)
             ==> ?r. m <= r /\ r < m + n /\ (i r = s))
        ==> sum(p,q) f <= sum(m,n) (\r. f(i r))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m,n) (\r. if p:num <= i(r) /\ i(r) < p + q
                            then f(i(r)) else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[REAL_LE_REFL; ADD_AC]] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`q:num`,`q:num`) THEN INDUCT_TAC THENL
   [STRIP_TAC THEN REWRITE_TAC[sum] THEN
    REWRITE_TAC[ARITH_RULE `~(p <= q /\ q < p + 0)`] THEN
    REWRITE_TAC[SUM_0; REAL_LE_REFL];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `s < p + q ==> s < p + SUC q`];
    ALL_TAC] THEN
  REWRITE_TAC[sum] THEN
  SUBGOAL_THEN
   `sum(m,n) (\r. if p <= i r /\ i r < p + SUC q then f (i r) else &0) =
    sum(m,n) (\r. if p <= i r /\ i r < p + q then f (i r) else &0) +
    sum(m,n) (\r. if i r = p + q then f(i r) else &0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_ADD] THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `(i:num->num) r = p + q` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[LE_ADD; LT_REFL; ARITH_RULE `p + q < p + SUC q`] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH_RULE
       `r < p + SUC q <=> (r = p + q) \/ r < p + q`] THEN
    REWRITE_TAC[REAL_ADD_RID];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `f <= s'' ==> s <= s' ==> s + f <= s' + s''`) THEN
  UNDISCH_TAC
   `!s. p <= s /\ s < p + SUC q /\ ~(f s = &0)
           ==> (?r:num. m <= r /\ r < m + n /\ (i r = s))` THEN
  DISCH_THEN(MP_TAC o SPEC `p + q:num`) THEN
  ASM_CASES_TAC `f(p + q:num) = &0` THEN ASM_REWRITE_TAC[] THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m,n) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[REAL_LE_REFL] THEN ASM_MESON_TAC[ADD_SYM];
    ALL_TAC] THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `n = (s - m) + 1 + ((m + n) - (s + 1))` SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`m <= s:num`; `s < m + n:num`] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  ASM_SIMP_TAC[SUM_1; ARITH_RULE `m <= s ==> (m + (s - m) = s:num)`] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> a <= x + a + y`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(m,s - m) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
      [`m <= r:num`; `r < s - m + m:num`; `s < m + n:num`; `m <= s:num`] THEN
    ARITH_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(s + 1,(m + n) - (s + 1)) (\r. &0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_0; REAL_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
      [`r < (m + n) - (s + 1) + s + 1:num`;
       `s + 1 <= r`; `s < m + n:num`; `m <= s:num`] THEN
    ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Apply this to show that one of the residuals is bounded by the other.     *)
(* ------------------------------------------------------------------------- *)

let PSI_RESIDUES_COMPARE_2 = prove
 (`sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                 then ln(&(aprimedivisor d)) else &0)
   <= sum(2,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                    then ln(&(aprimedivisor d)) else &0)`,
  MP_TAC(SPECL
   [`\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                    then ln(&(aprimedivisor d)) else &0`;
    `\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP k)
                  then d * (aprimedivisor d) else d`;
    `2`; `n:num`; `2`; `n:num`] SUM_SURJECT) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC;
        COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
        ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`]] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
      SUBGOAL_THEN `p EXP k * p = p EXP (k + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]; ALL_TAC] THEN
      ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; ARITH_RULE `1 <= k + 1`] THEN
      ASM_MESON_TAC[LN_POS; REAL_OF_NUM_LE; PRIME_GE_2; REAL_LE_REFL;
                    ARITH_RULE `2 <= n ==> 1 <= n`];
      ALL_TAC] THEN
    X_GEN_TAC `s:num` THEN
    ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (s = p EXP (2 * k + 1))` THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    EXISTS_TAC `p EXP (2 * k)` THEN
    COND_CASES_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k`]] THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; EXP_ADD; EXP_1;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`;
                  EXP_EQ_0; EXP_EQ_1] THEN
      ASM_MESON_TAC[PRIME_1; PRIME_0;
                    ARITH_RULE `1 <= k ==> ~(2 * k = 0)`];
      ALL_TAC] THEN
    MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `p EXP (2 * k + 1)` THEN
    ASM_REWRITE_TAC[LE_EXP] THEN
    COND_CASES_TAC THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP k)` THEN
  ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
    ASM_MESON_TAC[ARITH_RULE `1 <= k ==> 1 <= 2 * k /\ 1 <= 2 * k + 1`]] THEN
  FIRST_X_ASSUM(CHOOSE_THEN (K ALL_TAC)) THEN
  ASM_CASES_TAC `?p k. 1 <= k /\ prime p /\ (r = p EXP (2 * k))` THEN
  ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k`] THEN
    SUBGOAL_THEN `p EXP (2 * k) * p = p EXP (2 * k + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[EXP_ADD; EXP_1; MULT_AC]; ALL_TAC] THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW; REAL_LE_REFL;
                 ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_neg o concl) THEN
  MATCH_MP_TAC(TAUT `(b ==> a) ==> ~a ==> b ==> c`) THEN
  STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`p:num`; `k:num`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `r:num` APRIMEDIVISOR) THEN
  ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
  ABBREV_TAC `q = aprimedivisor r` THEN STRIP_TAC THEN
  SUBGOAL_THEN `q divides p` ASSUME_TAC THENL
   [MATCH_MP_TAC PRIME_DIVEXP THEN EXISTS_TAC `2 * k + 1` THEN
    ASM_MESON_TAC[divides; MULT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = p:num` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[prime]; ALL_TAC] THEN
  UNDISCH_TAC `r * p = p EXP (2 * k + 1)` THEN
  REWRITE_TAC[EXP_ADD; EXP_1; EQ_MULT_RCANCEL] THEN
  ASM_MESON_TAC[PRIME_0]);;

let PSI_RESIDUES_COMPARE = prove
 (`!n. sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k + 1))
                     then ln(&(aprimedivisor d)) else &0)
       <= sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                        then ln(&(aprimedivisor d)) else &0)`,
  GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[sum; REAL_LE_REFL] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> (n = 1 + (n - 1))`)) THEN
  REWRITE_TAC[GSYM SUM_SPLIT; SUM_1] THEN
  MATCH_MP_TAC(REAL_ARITH
   `b <= d /\ (a = &0) /\ (c = &0) ==> a + b <= c + d`) THEN
  REWRITE_TAC[PSI_RESIDUES_COMPARE_2; ARITH] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  ASM_MESON_TAC[EXP_EQ_1; PRIME_1; ARITH_RULE
    `1 <= k ==> ~(2 * k = 0) /\ ~(2 * k + 1 = 0)`]);;

(* ------------------------------------------------------------------------- *)
(* The even residual reduces to the square root case.                        *)
(* ------------------------------------------------------------------------- *)

let PSI_SQRT = prove
 (`!n. psi(ISQRT(n)) =
        sum(1,n) (\d. if ?p k. 1 <= k /\ prime p /\ (d = p EXP (2 * k))
                      then ln(&(aprimedivisor d)) else &0)`,
  REWRITE_TAC[psi] THEN INDUCT_TAC THEN
  REWRITE_TAC[ISQRT_0; sum; ISQRT_SUC] THEN
  ASM_CASES_TAC `?m. SUC n = m EXP 2` THENL
   [ALL_TAC;
    SUBGOAL_THEN `~(?p k. 1 <= k /\ prime p /\ (1 + n = p EXP (2 * k)))`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_MULT] THEN
      ASM_MESON_TAC[ARITH_RULE `1 + n = SUC n`];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID]] THEN
  ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL; sum] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `1 + ISQRT n = m` SUBST1_TAC THENL
   [SUBGOAL_THEN `(1 + ISQRT n) EXP 2 = SUC n` MP_TAC THENL
     [ALL_TAC;
      ASM_REWRITE_TAC[num_CONV `2`; GSYM LE_ANTISYM] THEN
      REWRITE_TAC[EXP_MONO_LE_SUC; EXP_MONO_LT_SUC]] THEN
    MP_TAC(SPEC `n:num` ISQRT_SUC) THEN
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(SPEC `SUC n` ISQRT_WORKS) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[num_CONV `2`; GSYM LE_ANTISYM] THEN
    REWRITE_TAC[EXP_MONO_LE_SUC; EXP_MONO_LT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  REWRITE_TAC[mangoldt; primepow] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_MULT] THEN
  REWRITE_TAC[GSYM LE_ANTISYM; EXP_MONO_LE_SUC; num_CONV `2`] THEN
  REWRITE_TAC[LE_ANTISYM] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[aprimedivisor] THEN
  REPEAT AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  DISCH_TAC THEN REWRITE_TAC[EXP; EXP_1] THEN
  ASM_MESON_TAC[DIVIDES_LMUL; PRIME_DIVPROD]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main comparison result.                                         *)
(* ------------------------------------------------------------------------- *)

let PSI_THETA = prove
 (`!n. theta(n) + psi(ISQRT n) <= psi(n) /\
       psi(n) <= theta(n) + &2 * psi(ISQRT n)`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [PSI_SPLIT] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [PSI_SPLIT] THEN
  MP_TAC(SPEC `n:num` PSI_RESIDUES_COMPARE) THEN
  REWRITE_TAC[GSYM PSI_SQRT] THEN
  SIMP_TAC[REAL_MUL_2; GSYM REAL_ADD_ASSOC; REAL_LE_LADD; REAL_LE_ADDR] THEN
  DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC SUM_POS_GEN THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `p:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[APRIMEDIVISOR_PRIMEPOW;
    ARITH_RULE `1 <= k ==> 1 <= 2 * k + 1`] THEN
  MATCH_MP_TAC LN_POS THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  ASM_MESON_TAC[PRIME_0; ARITH_RULE `~(p = 0) ==> 1 <= p`]);;

(* ------------------------------------------------------------------------- *)
(* A trivial one-way comparison is immediate.                                *)
(* ------------------------------------------------------------------------- *)

let THETA_LE_PSI = prove
 (`!n. theta(n) <= psi(n)`,
  GEN_TAC THEN REWRITE_TAC[theta; psi] THEN MATCH_MP_TAC SUM_LE THEN
  X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[MANGOLDT_POS] THEN
  ASM_SIMP_TAC[mangoldt; PRIME_PRIMEPOW] THEN
  SUBGOAL_THEN `aprimedivisor p = p`
   (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
  ASM_MESON_TAC[APRIMEDIVISOR_PRIMEPOW; EXP_1; LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* A tighter bound on psi on a smaller range, to reduce later case analysis. *)
(* ------------------------------------------------------------------------- *)

let PSI_UBOUND_30 = prove
 (`!n. n <= 30 ==> psi(n) <= &65 / &64 * &n`,
  let lemma = prove
   (`a <= b /\ l <= a /\ rest ==> l <= a /\ l <= b /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(LAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REWRITE_TAC[ARITH_RULE `n <= 30 <=> n < 31`] THEN
  CONV_TAC EXPAND_CASES_CONV THEN REWRITE_TAC(PSI_LIST_300) THEN
  REWRITE_TAC[LN_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT
   ((MATCH_MP_TAC lemma THEN
     CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
     GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
    ORELSE
     (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
    ORELSE tac));;

(* ------------------------------------------------------------------------- *)
(* Bounds for theta, derived from those for psi.                             *)
(* ------------------------------------------------------------------------- *)

let THETA_UBOUND_3_2 = prove
 (`!n. theta(n) <= &3 / &2 * &n`,
  MESON_TAC[REAL_LE_TRANS; PSI_UBOUND_3_2; THETA_LE_PSI]);;

let THETA_LBOUND_1_2 = prove
 (`!n. 5 <= n ==> &1 / &2 * &n <= theta(n)`,
  let lemma = prove
   (`a <= b /\ b <= l /\ rest ==> a <= l /\ b <= l /\ rest`,
    MESON_TAC[REAL_LE_TRANS])
  and tac = time (CONV_TAC(RAND_CONV LN_N2_CONV THENC REALCALC_REL_CONV)) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n >= 900` THENL
   [MP_TAC(CONJUNCT2(SPEC `n:num` PSI_THETA)) THEN
    MP_TAC(SPEC `n:num` PSI_LBOUND_3_5) THEN
    ASM_SIMP_TAC[ARITH_RULE `n >= 900 ==> 4 <= n`] THEN
    MATCH_MP_TAC(REAL_ARITH
     `d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th`) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&3 / &2 * &(ISQRT n)` THEN
    REWRITE_TAC[PSI_UBOUND_3_2] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    SUBGOAL_THEN `&(ISQRT n) pow 2 <= (&n * &1 / &30) pow 2` MP_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ISQRT_WORKS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2; REAL_ARITH
     `(a * b) * (a * b) = a * a * b * b`] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SIMP_TAC[REAL_MUL_ASSOC; GSYM REAL_LE_LDIV_EQ;
             REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `n >= 900` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `n < 413` THENL
   [UNDISCH_TAC `5 <= n` THEN UNDISCH_TAC `n < 413` THEN
    SPEC_TAC(`n:num`,`n:num`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
    CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC(THETA_LIST 412) THEN
    REWRITE_TAC[LN_1; ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REPEAT
     ((MATCH_MP_TAC lemma THEN
       CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
       GEN_REWRITE_TAC I [TAUT `T /\ a <=> a`])
      ORELSE
       (CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC])
      ORELSE tac);
    ALL_TAC] THEN
  MP_TAC(CONJUNCT2(SPEC `n:num` PSI_THETA)) THEN
  MP_TAC(SPEC `n:num` PSI_LBOUND_3_5) THEN
  ASM_SIMP_TAC[ARITH_RULE `5 <= n ==> 4 <= n`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= (a - b) * n ==> a * n <= ps ==> ps <= th + d ==> b * n <= th`) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&65 / &64 * &(ISQRT n)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PSI_UBOUND_30 THEN
    SUBGOAL_THEN `(ISQRT n) EXP (SUC 1) <= 30 EXP (SUC 1)` MP_TAC THENL
     [ALL_TAC; REWRITE_TAC[EXP_MONO_LE_SUC]] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `n:num` THEN
    REWRITE_TAC[ARITH; ISQRT_WORKS] THEN
    UNDISCH_TAC `~(n >= 900)` THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SUBGOAL_THEN `&(ISQRT n) pow 2 <= (&n * &16 / &325) pow 2` MP_TAC THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_TAC THEN MATCH_MP_TAC REAL_POW_LT2 THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&n` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LE; ISQRT_WORKS];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2; REAL_ARITH
   `(a * b) * (a * b) = a * a * b * b`] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ;
           REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&413` THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `~(n < 413)` THEN ARITH_TAC);;

(* ========================================================================= *)
(* Tighten the bounds on weak PNT to get the Bertrand conjecture.            *)
(* ========================================================================= *)

let FLOOR_POS = prove
 (`!x. &0 <= x ==> &0 <= floor x`,
  GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `x < &1` THENL
   [ASM_MESON_TAC[FLOOR_EQ_0; REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(last(CONJUNCTS(SPEC `x:real` FLOOR))) THEN
  UNDISCH_TAC `~(x < &1)` THEN REAL_ARITH_TAC);;

let FLOOR_NUM_EXISTS = prove
 (`!x. &0 <= x ==> ?k. floor x = &k`,
  REPEAT STRIP_TAC THEN MP_TAC(CONJUNCT1(SPEC `x:real` FLOOR)) THEN
  REWRITE_TAC[integer] THEN
  ASM_MESON_TAC[FLOOR_POS; REAL_ARITH `&0 <= x ==> (abs x = x)`]);;

let FLOOR_DIV_INTERVAL = prove
 (`!n d k. ~(d = 0)
           ==> ((floor(&n / &d) = &k) =
                  if k = 0 then &n < &d
                  else &n / &(k + 1) < &d /\ &d <= &n / &k)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k = 0` THENL
   [ASM_REWRITE_TAC[FLOOR_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < d <=> ~(d = 0)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID; REAL_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM FLOOR_UNIQUE; INTEGER_CLOSED] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ; REAL_OF_NUM_LT;
                 ARITH_RULE `0 < d <=> ~(d = 0)`; ARITH_RULE `0 < k + 1`] THEN
  REWRITE_TAC[REAL_MUL_AC; CONJ_ACI; REAL_OF_NUM_ADD]);;

let FLOOR_DIV_EXISTS = prove
 (`!n d. ~(d = 0)
         ==> ?k. (floor(&n / &d) = &k) /\
                 d * k <= n /\ n < d * (k + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?k. floor (&n / &d) = &k` MP_TAC THENL
   [ASM_SIMP_TAC[FLOOR_NUM_EXISTS; REAL_LE_DIV; REAL_POS]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:num` THEN SIMP_TAC[] THEN ASM_SIMP_TAC[FLOOR_DIV_INTERVAL] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0; ADD_CLAUSES; REAL_OF_NUM_LT] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < k + 1 /\ (~(k = 0) ==> 0 < k)`] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  REWRITE_TAC[CONJ_ACI]);;

let FLOOR_HALF_INTERVAL = prove
 (`!n d. ~(d = 0)
         ==> (floor (&n / &d) - &2 * floor (&(n DIV 2) / &d) =
                if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                then &1 else &0)`,
  let lemma = prove(`ODD(k) ==> ~(k = 0)`,MESON_TAC[EVEN; NOT_EVEN]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP FLOOR_DIV_EXISTS) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n DIV 2` o MATCH_MP FLOOR_DIV_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:num`
   (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:num`
   (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
  MAP_EVERY UNDISCH_TAC [`n DIV 2 < d * (k1 + 1)`; `d * k1 <= n DIV 2`] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a ==> ~(b /\ c))`] THEN
  SIMP_TAC[GSYM NOT_LE; LE_LDIV_EQ; LE_RDIV_EQ; ARITH_EQ; lemma; ADD_EQ_0] THEN
  REWRITE_TAC[NOT_LE; NOT_IMP] THEN DISCH_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `d * 2 * k1 < d * (k2 + 1) /\ d * k2 < d * 2 * (k1 + 1)`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (ARITH_RULE
     `2 * k1 < k2 + 1 /\ k2 < 2 * (k1 + 1)
      ==> (k2 = 2 * k1) \/ (k2 = 2 * k1 + 1)`)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL;
              REAL_ADD_SUB; REAL_SUB_REFL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * k1 + 1`) THEN
    ASM_REWRITE_TAC[ARITH_ODD; ODD_ADD; ODD_MULT] THEN
    ASM_MESON_TAC[MULT_AC]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `k:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ODD_EXISTS; ADD1] THEN
  DISCH_THEN(X_CHOOSE_THEN `k3:num` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `d * 2 * k1 < d * ((2 * k3 + 1) + 1) /\
                d * (2 * k3 + 1) < d * 2 * (k1 + 1)`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_LCANCEL] THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `2 * k1 < (2 * k3 + 1) + 1 /\ 2 * k3 + 1 < 2 * (k1 + 1)
    ==> (k3 = k1)`)) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC);;

let SUM_EXPAND_LEMMA = prove
 (`!n m k. (m + 2 * k = n)
         ==> (sum (1,n DIV (2 * k + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0) =
              sum (1,n) (\d. --(&1) pow (d + 1) * psi (n DIV d)) -
              sum (1,2 * k)
                  (\d. --(&1) pow (d + 1) * psi (n DIV d)))`,
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[DIV_0; ADD_EQ_0; ARITH_EQ; REAL_SUB_REFL; sum]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN ASM_CASES_TAC `m = 0` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_SIMP_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[DIV_REFL; SUM_1; DIV_1; REAL_SUB_REFL] THEN
    SUBGOAL_THEN `n DIV (n + 1) = 0` (fun th -> REWRITE_TAC[th; sum]) THEN
    ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `n < n + 1 /\ ~(n + 1 = 0)`];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THENL
   [DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `k:num` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM ADD1; ARITH_RULE `1 + n = SUC n`] THEN
    SIMP_TAC[DIV_REFL; NOT_SUC; sum; SUM_1] THEN
    REWRITE_TAC[REAL_ADD_SUB; mangoldt] THEN
    CONV_TAC(ONCE_DEPTH_CONV PRIMEPOW_CONV) THEN
    REWRITE_TAC[COND_ID] THEN CONV_TAC SYM_CONV THEN
    REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
    SIMP_TAC[DIV_REFL; NOT_SUC] THEN REWRITE_TAC(LN_1::PSI_LIST 1);
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `m - 2`) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> m - 2 < m`] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN ANTS_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o funpow 2 RAND_CONV o TOP_DEPTH_CONV)
   [ARITH_RULE `2 * SUC k = SUC(SUC(2 * k))`; sum] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(s - ss = x + y) ==> (ss = a - ((b + x) + y)) ==> (s = a - b)`) THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; ARITH_EVEN; EVEN; EVEN_MULT] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_LNEG] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  REWRITE_TAC[psi; GSYM real_sub] THEN
  MATCH_MP_TAC(REAL_ARITH `!b. (a - b = d) /\ (b = c) ==> (a - c = d)`) THEN
  EXISTS_TAC `sum (1,n DIV (SUC (2 * k) + 1))
                  (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                       then mangoldt d else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_DIFFERENCES_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `r:num` THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EXISTS_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `2 * k + 1`) THEN
    REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH_ODD] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= r <=> n < 1 + r`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < r <=> 1 + n <= r`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `(2 * k + 1) + 1 = SUC(2 * k) + 1`];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_MORETERMS_EQ THEN CONJ_TAC THENL
   [MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC k + 1 = 2 * k + 3`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) + 1 = 2 * k + 2`] THEN STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `oj:num` MP_TAC) THEN
  REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `j:num` SUBST1_TAC) THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) + 1 = 2 * k + 2`] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * k) = 2 * k + 1`] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 + a <= b ==> a < b`)) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `a < 1 + b ==> a <= b`)) THEN
  SIMP_TAC[GSYM NOT_LE; LE_RDIV_EQ; LE_LDIV_EQ; ADD_EQ_0; ARITH_EQ] THEN
  REWRITE_TAC[NOT_LE] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(2 * j + 1) * r < (2 * k + 3) * r /\
                (2 * k + 2) * r < (2 * j + 2) * r`
  MP_TAC THENL [ASM_MESON_TAC[LET_TRANS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[LT_MULT_RCANCEL] THEN
  ASM_CASES_TAC `r = 0` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o MATCH_MP (ARITH_RULE
   `2 * j + 1 < 2 * k + 3 /\ 2 * k + 2 < 2 * j + 2 ==> (j = k)`)) THEN
  ASM_MESON_TAC[LET_TRANS; LT_REFL; MULT_AC]);;

let FACT_EXPAND_PSI = prove
 (`!n. ln(&(FACT(n))) - &2 * ln(&(FACT(n DIV 2))) =
          sum(1,n) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  GEN_TAC THEN REWRITE_TAC[MANGOLDT] THEN
  SUBGOAL_THEN
   `sum (1,n DIV 2) (\d. mangoldt d * floor (&(n DIV 2) / &d)) =
    sum (1,n) (\d. mangoldt d * floor (&(n DIV 2) / &d))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `n = n DIV 2 + (n - n DIV 2)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
    THENL [MESON_TAC[SUB_ADD; DIV_LE; ADD_SYM; NUM_REDUCE_CONV `2 = 0`];
           ALL_TAC] THEN
    REWRITE_TAC[GSYM SUM_SPLIT] THEN
    MATCH_MP_TAC(REAL_ARITH `(b = &0) ==> (a = a + b)`) THEN
    MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ENTIRE; FLOOR_EQ_0] THEN DISJ2_TAC THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    SUBGOAL_THEN `0 < r /\ n DIV 2 < r` MP_TAC THENL
     [UNDISCH_TAC `1 + n DIV 2 <= r` THEN ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_OF_NUM_LT; REAL_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM SUM_CMUL; GSYM SUM_SUB] THEN
  REWRITE_TAC[REAL_ARITH `m * x - &2 * m * y = m * (x - &2 * y)`] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum(1,n) (\d. if ?k. ODD k /\ n DIV (k + 1) < d /\ d <= n DIV k
                  then mangoldt d else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FLOOR_HALF_INTERVAL; ARITH_RULE `1 <= d ==> ~(d = 0)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `n:num`; `0`] SUM_EXPAND_LEMMA) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; sum; REAL_SUB_RZERO; DIV_1]);;

(* ------------------------------------------------------------------------- *)
(* Show that we can get bounds by cutting off at odd/even points.            *)
(* ------------------------------------------------------------------------- *)

let PSI_MONO = prove
 (`!m n. m <= n ==> psi(m) <= psi(n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; psi] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN REWRITE_TAC[MANGOLDT_POS]);;

let PSI_POS = prove
 (`!n. &0 <= psi(n)`,
  SUBGOAL_THEN `psi(0) = &0` (fun th -> MESON_TAC[th; PSI_MONO; LE_0]) THEN
  REWRITE_TAC(LN_1::PSI_LIST 0));;

let PSI_EXPANSION_CUTOFF = prove
 (`!n m p. m <= p
         ==> sum(1,2 * m) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * p) (\d. --(&1) pow (d + 1) * psi(n DIV d)) /\
             sum(1,2 * p + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))
               <= sum(1,2 * m + 1) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  GEN_TAC THEN SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  SIMP_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  X_GEN_TAC `m:num` THEN INDUCT_TAC THEN
  REWRITE_TAC[ADD_CLAUSES; REAL_LE_REFL] THEN
  REWRITE_TAC[ARITH_RULE `2 * SUC n = SUC(SUC(2 * n))`;
              ARITH_RULE `SUC(SUC n) + 1 = SUC(SUC(n + 1))`; sum] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `s1 <= s1' /\ s2' <= s2
    ==> &0 <= a + b /\ &0 <= --c + --d
        ==> s1 <= (s1' + a) + b /\ (s2' + c) + d <= s2`)) THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN_ADD; EVEN_MULT; ARITH_EVEN; EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; REAL_MUL_LNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= a + --b <=> b <= a`] THEN
  CONJ_TAC THEN MATCH_MP_TAC PSI_MONO THEN
  MATCH_MP_TAC DIV_MONO2 THEN ARITH_TAC);;

let FACT_PSI_BOUND_ODD = prove
 (`!n k. ODD(k)
         ==> ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
             <= sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_EXPAND_PSI] THEN
  ASM_CASES_TAC `k <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(b = a) ==> a <= b`) THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= n) ==> n <= k:num`] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `n DIV r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `1 + n <= r ==> n < r /\ ~(r = 0)`];
      REWRITE_TAC(LN_1::PSI_LIST 0)]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ODD_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1,SUC(2 * n DIV 2))
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `m <= n DIV 2`
     (fun th -> SIMP_TAC[th; ADD1; PSI_EXPANSION_CUTOFF]) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV) [th])
   MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `r < 2 <=> (r = 0) \/ (r = 1)`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD1; MULT_AC; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; sum; REAL_LE_ADDR] THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; PSI_POS]);;

let FACT_PSI_BOUND_EVEN = prove
 (`!n k. EVEN(k)
         ==> sum(1,k) (\d. --(&1) pow (d + 1) * psi(n DIV d))
             <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FACT_EXPAND_PSI] THEN
  ASM_CASES_TAC `k <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `(a = b) ==> a <= b`) THEN
    MATCH_MP_TAC SUM_MORETERMS_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE `~(k <= n) ==> n <= k:num`] THEN
    X_GEN_TAC `r:num` THEN STRIP_TAC THEN REWRITE_TAC[REAL_ENTIRE] THEN
    DISJ2_TAC THEN SUBGOAL_THEN `n DIV r = 0` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIV_EQ_0; ARITH_RULE `1 + n <= r ==> n < r /\ ~(r = 0)`];
      REWRITE_TAC(LN_1::PSI_LIST 0)]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1,2 * n DIV 2)
                 (\d. -- &1 pow (d + 1) * psi (n DIV d))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `m <= n DIV 2`
     (fun th -> SIMP_TAC[th; ADD1; PSI_EXPANSION_CUTOFF]) THEN
    SIMP_TAC[LE_RDIV_EQ; ARITH_EQ] THEN
    POP_ASSUM MP_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `2`] DIVISION) THEN REWRITE_TAC[ARITH_EQ] THEN
  MAP_EVERY ABBREV_TAC [`q = n DIV 2`; `r = n MOD 2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [th])
   MP_TAC) THEN
  REWRITE_TAC[ARITH_RULE `r < 2 <=> (r = 0) \/ (r = 1)`] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[ADD1; MULT_AC; ADD_CLAUSES; REAL_LE_REFL] THEN
  REWRITE_TAC[GSYM ADD1; ADD_CLAUSES; sum; REAL_LE_ADDR] THEN
  REWRITE_TAC[REAL_POW_NEG; EVEN; EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_LID; PSI_POS]);;

(* ------------------------------------------------------------------------- *)
(* In particular, we will use these.                                         *)
(* ------------------------------------------------------------------------- *)

let FACT_PSI_BOUND_2_3 = prove
 (`!n. psi(n) - psi(n DIV 2)
       <= ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2))) /\
       ln(&(FACT n)) - &2 * ln(&(FACT (n DIV 2)))
       <= psi(n) - psi(n DIV 2) + psi(n DIV 3)`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `2`] FACT_PSI_BOUND_EVEN) THEN
  MP_TAC(SPECL [`n:num`; `3`] FACT_PSI_BOUND_ODD) THEN
  REWRITE_TAC[ARITH] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_SUM_CONV) THEN
  REWRITE_TAC[ARITH; REAL_ADD_LID; DIV_1] THEN
  REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_ONE; REAL_MUL_LID] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence get a good lower bound on psi(n) - psi(n/2).                        *)
(* ------------------------------------------------------------------------- *)

let PSI_DOUBLE_LEMMA = prove
 (`!n. n >= 1200 ==> &n / &6 <= psi(n) - psi(n DIV 2)`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `n:num` FACT_PSI_BOUND_2_3) THEN
  MATCH_MP_TAC(REAL_ARITH
   `b + p3 <= a ==> u <= v /\ a <= p - p2 + p3 ==> b <= p - p2`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n / &6 + &n / &2` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_LE_LADD] THEN MP_TAC(SPEC `n DIV 3` PSI_UBOUND_3_2) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&3 / &2 * &n / &3` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      MP_TAC(SPECL [`n:num`; `3`] DIVISION) THEN ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(SPEC `n:num` LN_FACT_DIFF_BOUNDS) THEN
  MATCH_MP_TAC(REAL_ARITH
   `ltm <= nl2 - a ==> abs(lf - nl2) <= ltm ==> a <= lf`) THEN
  ASM_SIMP_TAC[ARITH_RULE `n >= 1200 ==> ~(n = 0)`] THEN
  REWRITE_TAC[real_div; GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&n * &1 / &38` THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SIMP_TAC[REAL_LE_SUB_LADD] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    CONV_TAC(RAND_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV] THEN
  SUBST1_TAC(REAL_ARITH `&n = &1 + (&n - &1)`) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `n >= b ==> b <= n:num`)) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_OF_NUM_LE] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `a <= n ==> a - &1 <= n - &1`)) THEN
  ABBREV_TAC `x = &n - &1` THEN
  CONV_TAC(LAND_CONV NUM_REDUCE_CONV THENC REAL_RAT_REDUCE_CONV) THEN
  SPEC_TAC(`x:real`,`x:real`) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN REWRITE_TAC[REAL_SUB_LE] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `a <= x ==> inv(&1 + x) <= inv(&1 + a) /\
               inv(&1 + a) <= b ==> inv(&1 + x) <= b`)) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Hence show that theta changes (could get a lower bound like n/10).        *)
(* ------------------------------------------------------------------------- *)

let THETA_DOUBLE_LEMMA = prove
 (`!n. n >= 1200 ==> theta(n DIV 2) < theta(n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(CONJUNCT2 (SPEC `n:num` PSI_THETA)) THEN
  MP_TAC(CONJUNCT1 (SPEC `n DIV 2` PSI_THETA)) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PSI_DOUBLE_LEMMA) THEN
  MP_TAC(SPEC `ISQRT(n DIV 2)` PSI_POS) THEN
  SUBGOAL_THEN
   `&2 * psi (ISQRT n) < &n / &6`
   (fun th -> MP_TAC th THEN REAL_ARITH_TAC) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&3 / &2 * &(ISQRT n)` THEN
  REWRITE_TAC[PSI_UBOUND_3_2] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN
  SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LT] THEN
  SUBGOAL_THEN `(ISQRT n * 18) EXP (SUC 1) < n EXP (SUC 1)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[EXP_MONO_LT_SUC]] THEN
  REWRITE_TAC[EXP; EXP_1] THEN
  MATCH_MP_TAC(ARITH_RULE `324 * i * i < a ==> (i * 18) * (i * 18) < a`) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `324 * n` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM EXP_2; ISQRT_WORKS; LE_MULT_LCANCEL];
    REWRITE_TAC[LT_MULT_RCANCEL] THEN POP_ASSUM MP_TAC THEN ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Hence Bertrand for sufficiently large n.                                  *)
(* ------------------------------------------------------------------------- *)

let BIG_BERTRAND = prove
 (`!n. n >= 2400 ==> ?p. prime(p) /\ n <= p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `2 * n` THETA_DOUBLE_LEMMA) THEN
  ANTS_TAC THENL [POP_ASSUM MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b /\ c) <=> b /\ c ==> ~a`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `sum(n + 1,n) (\p. if prime p then ln (&p) else &0) = &0`
  MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `sum(n + 1,n) (\r. &0)` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[SUM_0]] THEN
    MATCH_MP_TAC SUM_EQ THEN
    ASM_SIMP_TAC[ARITH_RULE
     `n + 1 <= r /\ r < n + n + 1 ==> n <= r /\ r <= 2 * n`];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(b + a = c) ==> (a = &0) ==> ~(b < c)`) THEN
  REWRITE_TAC[theta] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[SUM_SPLIT] THEN
  REWRITE_TAC[MULT_2]);;

(* ------------------------------------------------------------------------- *)
(* Landau trick. Should be automatic but ARITH_RULE is a bit slow.           *)
(* (Direct use of ARITH_RULE takes about 3 minutes on my current laptop.)    *)
(* ------------------------------------------------------------------------- *)

let LANDAU_TRICK = prove
 (`!n. 0 < n /\ n < 2400
       ==> n <= 2 /\ 2 <= 2 * n \/
           n <= 3 /\ 3 <= 2 * n \/
           n <= 5 /\ 5 <= 2 * n \/
           n <= 7 /\ 7 <= 2 * n \/
           n <= 13 /\ 13 <= 2 * n \/
           n <= 23 /\ 23 <= 2 * n \/
           n <= 43 /\ 43 <= 2 * n \/
           n <= 83 /\ 83 <= 2 * n \/
           n <= 163 /\ 163 <= 2 * n \/
           n <= 317 /\ 317 <= 2 * n \/
           n <= 631 /\ 631 <= 2 * n \/
           n <= 1259 /\ 1259 <= 2 * n \/
           n <= 2503 /\ 2503 <= 2 * n`,
  let lemma = TAUT
   `(p /\ b1 ==> a1) /\ (~b1 ==> a2) ==> p ==> b1 /\ a1 \/ a2` in
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> c \/ ~b`] THEN
  REWRITE_TAC[GSYM DISJ_ASSOC] THEN
  REPEAT(MATCH_MP_TAC lemma THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bertrand for all nonzero n using "Landau trick".                          *)
(* ------------------------------------------------------------------------- *)

let BERTRAND = prove
 (`!n. ~(n = 0) ==> ?p. prime p /\ n <= p /\ p <= 2 * n`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `n >= 2400 \/ n < 2400`) THEN
  ASM_SIMP_TAC[BIG_BERTRAND] THEN MP_TAC(SPEC `n:num` LANDAU_TRICK) THEN
  ASM_REWRITE_TAC[ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  STRIP_TAC THEN
  ASM_MESON_TAC(map (PRIME_CONV o curry mk_comb `prime` o mk_small_numeral)
                    [2;3;5;7;13;23;43;83;163;317;631;1259;2503]));;

(* ========================================================================= *)
(* Weak form of the Prime Number Theorem.                                    *)
(* ========================================================================= *)

let pii = new_definition
  `pii(n) = sum(1,n) (\p. if prime(p) then &1 else &0)`;;

(* ------------------------------------------------------------------------- *)
(* An optimized rule to give pii(n) for all n <= some N.                     *)
(* ------------------------------------------------------------------------- *)

let PII_LIST =
  let PII_0 = prove
   (`pii(0) = &0`,
    REWRITE_TAC[pii; sum])
  and PII_SUC = prove
   (`pii(SUC n) = pii(n) + (if prime(SUC n) then &1 else &0)`,
    REWRITE_TAC[pii; sum; ADD1] THEN REWRITE_TAC[ADD_AC])
  and n_tm = `n:num`
  and SIMPER_CONV =
    NUM_REDUCE_CONV THENC
    ONCE_DEPTH_CONV PRIME_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV [COND_CLAUSES] THENC
    REAL_RAT_REDUCE_CONV in
  let rec PII_LIST n =
    if n = 0 then [PII_0] else
    let ths = PII_LIST (n - 1) in
    let th1 = INST [mk_small_numeral(n-1),n_tm] PII_SUC in
    let th2 = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [hd ths] th1 in
    CONV_RULE SIMPER_CONV th2::ths in
  PII_LIST;;

(* ------------------------------------------------------------------------- *)
(* Prove the usual characterization.                                         *)
(* ------------------------------------------------------------------------- *)

let PRIMES_FINITE = prove
 (`!n. FINITE {p | p <= n /\ prime(p)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{p | p < SUC n}` THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC);;

let PII = prove
 (`!n. pii(n) = &(CARD {p | p <= n /\ prime(p)})`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{p | p <= 0 /\ prime p} = {}`
     (fun th -> REWRITE_TAC(th::CARD_CLAUSES::PII_LIST 0)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    MESON_TAC[LE; PRIME_0; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p | p <= SUC n /\ prime p} =
                if prime(SUC n) then (SUC n) INSERT {p | p <= n /\ prime p}
                else {p | p <= n /\ prime p}`
  SUBST1_TAC THENL
   [COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[LE];
    ALL_TAC] THEN
  REWRITE_TAC[pii; sum] THEN REWRITE_TAC[GSYM pii] THEN
  REWRITE_TAC[ARITH_RULE `1 + n = SUC n`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SIMP_TAC[CARD_CLAUSES; PRIMES_FINITE] THEN COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
    ASM_MESON_TAC[ARITH_RULE `~(SUC n <= n)`];
    REWRITE_TAC[REAL_OF_NUM_SUC]]);;

(* ------------------------------------------------------------------------- *)
(* One bound is a simple consequence of the one for theta.                   *)
(* ------------------------------------------------------------------------- *)

let PII_LBOUND = prove
 (`!n. 3 <= n ==> &1 / &2 * (&n / ln(&n)) <= pii(n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; LN_POS_LT; REAL_OF_NUM_LT;
               ARITH_RULE `3 <= n ==> 1 < n`] THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o MATCH_MP
   (ARITH_RULE `3 <= n ==> (n = 3) \/ (n = 4) \/ 5 <= n`)) THEN
  ASM_REWRITE_TAC(PII_LIST 4) THENL
   [CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV;
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP THETA_LBOUND_1_2) THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> a <= x ==> a <= y`) THEN
  REWRITE_TAC[theta; pii; GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_REFL] THEN
  SUBGOAL_THEN `&0 < &r /\ &r <= &n`
   (fun th -> MESON_TAC[th; LN_MONO_LE; REAL_LTE_TRANS]) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 <= r` THEN UNDISCH_TAC `r < n + 1` THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* First prove the upper bound for the first 50 numbers, to start with.      *)
(* ------------------------------------------------------------------------- *)

let PII_UBOUND_CASES_50 = prove
 (`!n. n < 50 ==> 3 <= n ==> ln(&n) * pii(n) <= &5 * &n`,
  let tac = CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV THENC REALCALC_REL_CONV) in
  CONV_TAC EXPAND_CASES_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC(PII_LIST 49) THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT(CONJ_TAC THENL [tac THEN NO_TAC; ALL_TAC]) THEN tac);;

(* ------------------------------------------------------------------------- *)
(* An extra trivial pair of lemmas.                                          *)
(* ------------------------------------------------------------------------- *)

let THETA_POS = prove
 (`!n. &0 <= theta n`,
  GEN_TAC THEN REWRITE_TAC[theta] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[LE_REFL; LN_POS; REAL_OF_NUM_LE]);;

let PII_MONO = prove
 (`!m n. m <= n ==> pii(m) <= pii(n)`,
  SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; pii] THEN
  REWRITE_TAC[GSYM SUM_SPLIT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_ADDR] THEN
  MATCH_MP_TAC SUM_POS_GEN THEN
  GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let PII_POS = prove
 (`!n. &0 <= pii(n)`,
  SUBGOAL_THEN `pii(0) = &0` (fun th -> MESON_TAC[th; PII_MONO; LE_0]) THEN
  REWRITE_TAC(LN_1::PII_LIST 0));;

(* ------------------------------------------------------------------------- *)
(* The induction principle we can use.                                       *)
(* ------------------------------------------------------------------------- *)

let PII_CHANGE = prove
 (`!m n. ~(m = 0) ==> ln(&m) * (pii n - pii m) <= &3 / &2 * &n`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `m <= n:num` THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&0` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a * (c - b) ==> a * (b - c) <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[LN_POS; REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC PII_MONO THEN
    UNDISCH_TAC `~(m <= n:num)` THEN ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `theta n` THEN REWRITE_TAC[THETA_UBOUND_3_2] THEN
  MP_TAC(SPEC `m:num` THETA_POS) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= n - m ==> &0 <= m ==> a <= n`) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  REWRITE_TAC[pii; theta; GSYM SUM_SPLIT; REAL_ADD_SUB] THEN
  REWRITE_TAC[GSYM SUM_CMUL] THEN
  MATCH_MP_TAC SUM_LE THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL; REAL_MUL_RID] THEN
  SUBGOAL_THEN `&0 < &m /\ &m <= &r`
   (fun th -> MESON_TAC[th; LN_MONO_LE; REAL_LTE_TRANS]) THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `1 + m <= r` THEN UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC);;

let PII_ISQRT_INDUCT = prove
 (`!n. 50 <= n
       ==> ln(&n) * pii(n)
           <= &9 / &4 * (&3 / &2 * &n + ln(&(ISQRT(n))) * pii(ISQRT(n)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  GEN_REWRITE_TAC LAND_CONV [real_div] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN
  MP_TAC(SPECL [`ISQRT n`; `n:num`] PII_CHANGE) THEN
  SUBGOAL_THEN `~(ISQRT n = 0)` ASSUME_TAC THENL
   [MP_TAC(SPEC `n:num` ISQRT_WORKS) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN SIMP_TAC[ARITH] THEN
    DISCH_TAC THEN UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
   `a * p <= ls * p ==> ls * (p - ps) <= an ==> a * p <= an + ls * ps`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[PII_POS] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ln((&(ISQRT n) + &1) pow 2)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < &n /\ &n <= (&(ISQRT n) + &1) pow 2`
     (fun th -> MESON_TAC[th; REAL_LTE_TRANS; LN_MONO_LE]) THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE;
                REAL_OF_NUM_LT] THEN
    SIMP_TAC[ISQRT_WORKS; LT_IMP_LE] THEN
    UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LN_POW; REAL_POS; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH `a - b <= b * (d - &1) ==> a <= b * d`) THEN
  ASM_SIMP_TAC[GSYM LN_DIV; REAL_ARITH `&0 < x ==> &0 < x + &1`;
               REAL_OF_NUM_LT; ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; ARITH; REAL_MUL_LID] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&(ISQRT n))` THEN
  ASM_SIMP_TAC[LN_LE; REAL_POS; REAL_LE_INV_EQ] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
  SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT;
               ARITH_RULE `0 < n <=> ~(n = 0)`] THEN
  SUBGOAL_THEN `&7 <= &(ISQRT n)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `7 EXP 2 < (ISQRT n + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`&(ISQRT n)`,`x:real`) THEN
  MATCH_MP_TAC OVERPOWER_LEMMA THEN
  W(fun (asl,w) ->
      let th = DIFF_CONV
       (lhand(rator(rand(body(rand(lhand(rand(body(rand w))))))))) in
      MP_TAC th) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID;
    REAL_MUL_RID; REAL_MUL_LID] THEN
  SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  W(fun (asl,w) ->
      let tm = mk_abs(`x:real`,rand(rator(rand(body(rand(lhand w)))))) in
      DISCH_TAC THEN EXISTS_TAC tm) THEN
  CONJ_TAC THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[real_sub] THEN
    CONV_TAC(ONCE_DEPTH_CONV LN_N2_CONV) THEN
    CONV_TAC REALCALC_REL_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN(fun th -> FIRST_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  SIMP_TAC[LN_POS; REAL_LE_ADD; REAL_POS; REAL_ARITH `&7 <= x ==> &1 <= x`]);;

(* ------------------------------------------------------------------------- *)
(* Hence a bound by wellfounded induction.                                   *)
(* ------------------------------------------------------------------------- *)

let PII_UBOUND_5 = prove
 (`!n. 3 <= n ==> pii(n) <= &5 * (&n / ln(&n))`,
  REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
  SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; LN_POS_LT; REAL_OF_NUM_LT;
           ARITH_RULE `3 <= n ==> 1 < n`] THEN
  GEN_REWRITE_TAC (BINDER_CONV o RAND_CONV o LAND_CONV) [REAL_MUL_SYM] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n < 50` THEN ASM_SIMP_TAC[PII_UBOUND_CASES_50] THEN
  DISCH_THEN(MP_TAC o SPEC `ISQRT n`) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NOT_LT]) THEN
  SUBGOAL_THEN `7 <= ISQRT n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `7 EXP 2 < (ISQRT n + 1) EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN CONV_TAC NUM_REDUCE_CONV THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT_SUC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ARITH_RULE `7 <= n ==> 3 <= n`;
               ARITH_RULE `50 <= n ==> 3 <= n`] THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `(ISQRT n) EXP 2 < n EXP 2` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `n:num` THEN
      REWRITE_TAC[ISQRT_WORKS] THEN REWRITE_TAC[EXP_2] THEN
      MATCH_MP_TAC(ARITH_RULE `1 * n < m ==> n < m`) THEN
      REWRITE_TAC[LT_MULT_RCANCEL] THEN
      UNDISCH_TAC `50 <= n` THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[num_CONV `2`; EXP_MONO_LT_SUC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PII_ISQRT_INDUCT) THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&9 / &4 * (&3 / &2 * &n + &5 * &(ISQRT n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REWRITE_TAC[REAL_LE_LADD];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `i * (a * c) <= n * (d - a * b) ==> a * (b * n + c * i) <= d * n`) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(ISQRT n) * &7` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `ISQRT n * ISQRT n` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    REWRITE_TAC[GSYM EXP_2; ISQRT_WORKS]]);;
