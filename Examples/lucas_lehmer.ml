(* ========================================================================= *)
(* The Lucas-Lehmer test.                                                    *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Library/pocklington.ml";;
needs "Library/floor.ml";;
needs "Multivariate/vectors.ml";;
needs "100/sqrt.ml";;

(* ------------------------------------------------------------------------- *)
(* Relate real powers to iteration.                                          *)
(* ------------------------------------------------------------------------- *)

let REAL_POW_ITER = prove
 (`!x n. x pow n = ITER n (\y. x * y) (&1)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITER; real_pow]);;

(* ------------------------------------------------------------------------- *)
(* Basic definition of the Lucas-Lehmer sequence. To avoid troubles with     *)
(* cutoff subtraction and keep things in N we use m^2 + (p - 2) not m^2 - 2. *)
(* ------------------------------------------------------------------------- *)

let llseq = define
 `llseq p 0 = 4 MOD p /\
  llseq p (SUC n) = ((llseq p n) EXP 2 + (p - 2)) MOD p`;;

(* ------------------------------------------------------------------------- *)
(* Closed form for the Lucas-Lehmer sequence.                                *)
(* ------------------------------------------------------------------------- *)

let LLSEQ_CLOSEDFORM = prove
 (`!p n. ~(p = 0)
         ==> ?x. llseq p n = x MOD p /\
                 &x = (&2 + sqrt(&3)) pow (2 EXP n) +
                      (&2 - sqrt(&3)) pow (2 EXP n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL
   [EXISTS_TAC `4` THEN REWRITE_TAC[llseq; EXP] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `x:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x EXP 2 - 2` THEN ASM_REWRITE_TAC[llseq] THEN
  SUBGOAL_THEN `2 <= x EXP 2` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 EXP 2 <= x ==> 2 <= x`) THEN
    REWRITE_TAC[EXP_MONO_LE; ARITH_EQ] THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `x <= y /\ y pow 1 <= y pow n /\ &0 <= z pow n
      ==> x <= y pow n + z pow n`) THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[REAL_LE_ADDR; SQRT_POS_LE; REAL_POS];
      MATCH_MP_TAC REAL_POW_MONO THEN
      SIMP_TAC[LE_1; EXP_EQ_0; ARITH_EQ] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &2 + x`) THEN
      SIMP_TAC[SQRT_POS_LE; REAL_POS];
      MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_SUB_LE] THEN
      MATCH_MP_TAC REAL_LE_LSQRT THEN CONV_TAC REAL_RAT_REDUCE_CONV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `p = 1` THENL [ASM_REWRITE_TAC[MOD_1]; ALL_TAC] THEN
    TRANS_TAC EQ_TRANS `(x EXP 2 + (p - 2)) MOD p` THEN CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[ARITH_RULE
       `2 <= x /\ ~(p = 0) /\ ~(p = 1) ==> x + p - 2 = (x - 2) + p`]] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THENL
     [ASM_MESON_TAC[MOD_EXP_MOD];
      ASM_SIMP_TAC[MOD_REFL; ADD_CLAUSES; MOD_MOD_REFL]];
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_POW] THEN
    REWRITE_TAC[ADD1; EXP_ADD; GSYM REAL_POW_MUL; REAL_ARITH
     `(x + y) pow 2 = x pow 2 + y pow 2 + &2 * x * y`] THEN
    REWRITE_TAC[REAL_ARITH `(&2 + s) * (&2 - s) = &4 - s pow 2`] THEN
    REWRITE_TAC[REAL_SQRT_POW_2; REAL_ABS_NUM; GSYM REAL_POW_POW] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_POW_ONE] THEN CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* The main Lucas-Lehmer theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let LUCAS_LEHMER = prove
 (`!p. 2 <= p /\ llseq (2 EXP p - 1) (p - 2) = 0 ==> prime(2 EXP p - 1)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[PRIME_PRIME_FACTOR_SQRT] THEN
  SUBGOAL_THEN `2 <= 2 EXP p - 1` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `2 EXP 2 <= x ==> 2 <= x - 1`) THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
         CONJ_TAC THENL [ASM_ARITH_TAC; DISCH_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_GE_2) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIME_IMP_NZ) THEN
  ABBREV_TAC
   `equiv =
    \x y. ?a b. integer a /\ integer b /\
                x - y = (a + b * sqrt(&3)) * &q` THEN
  SUBGOAL_THEN `!x:real. (x == x) equiv` ASSUME_TAC THENL
   [REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    GEN_TAC THEN REPEAT(EXISTS_TAC `&0`) THEN
    REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real. (x == y) equiv <=> (y == x) equiv`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[]
     `(!x y. P x y ==> P y x) ==> (!x y. P x y <=> P y x)`) THEN
    REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    MESON_TAC[INTEGER_CLOSED; REAL_ARITH
      `x - y:real = (a + b * s) * q ==> y - x = (--a + --b * s) * q`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y z:real. (x == y) equiv /\ (y == z) equiv ==> (x == z) equiv`
  ASSUME_TAC THENL
   [REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    MESON_TAC[INTEGER_CLOSED; REAL_ARITH
      `x - y = (a + b * s) * q /\
       y - z = (a' + b' * s) * q
       ==> x - z:real = ((a + a') + (b + b') * s) * q`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. ?a b. (&2 + sqrt(&3)) pow k = &a + &b * sqrt(&3)`
  STRIP_ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [MAP_EVERY EXISTS_TAC [`1`; `0`] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` MP_TAC) THEN
      REWRITE_TAC[real_pow; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `b:num` THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY EXISTS_TAC [`2 * a + 3 * b`; `2 * b + a`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_ADD] THEN
      MP_TAC(SPEC `&3` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
      CONV_TAC REAL_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. ((&2 + sqrt(&3)) * x == (&2 + sqrt(&3)) * y) equiv <=>
          (x == y) equiv`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!x y:real. (x == y) equiv <=> (x - y == &0) equiv`
     (fun th -> ONCE_REWRITE_TAC[th])
    THENL
     [REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN SIMP_TAC[REAL_SUB_RZERO];
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB]] THEN
    REPEAT GEN_TAC THEN SPEC_TAC(`x - y:real`,`x:real`) THEN
    X_GEN_TAC `x:real` THEN REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN EQ_TAC THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_SUB_RZERO] THEN DISCH_TAC THENL
     [MAP_EVERY EXISTS_TAC [`&2 * u - &3 * v`; `&2 * v - u`];
      MAP_EVERY EXISTS_TAC [`&2 * u + &3 * v`; `&2 * v + u`]] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN
    MP_TAC(SPEC `&3` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&2 + sqrt(&3)) pow (2 EXP (p - 1)) == -- &1) equiv`
  ASSUME_TAC THENL
   [UNDISCH_THEN `!x y:real. (x == y) equiv <=> (y == x) equiv`
      (K ALL_TAC) THEN
    MP_TAC(ISPECL [`2 EXP p - 1`; `p - 2`] LLSEQ_CLOSEDFORM) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[MOD_EQ_0; LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` (MP_TAC o
     AP_TERM `(*) ((&2 + sqrt(&3)) pow (2 EXP (p - 2)))`)) THEN
    REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL; GSYM REAL_POW_2; REAL_POW_POW] THEN
    REWRITE_TAC[REAL_ARITH `(&2 + s) * (&2 - s) = &4 - s pow 2`] THEN
    REWRITE_TAC[REAL_SQRT_POW_2; REAL_ABS_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_POW_ONE] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= p ==> SUC(p - 2) = p - 1`] THEN
    SUBGOAL_THEN
     `?a b. (&2 + sqrt(&3)) pow (2 EXP (p - 2)) = &a + &b * sqrt(&3)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    REWRITE_TAC[REAL_SUB_RNEG] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `s:num` SUBST1_TAC o
       REWRITE_RULE[divides]) THEN
    MAP_EVERY EXISTS_TAC [`&a * &r * &s`; `&b * &r * &s`] THEN
    SIMP_TAC[INTEGER_CLOSED; GSYM REAL_OF_NUM_MUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&2 + sqrt(&3)) pow (2 EXP p) == &1) equiv`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [cong]) THEN
    REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_ARITH
     `a - -- &1  = b <=> a = b - &1`] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p = (p - 1) + 1` SUBST1_TAC THENL
     [UNDISCH_TAC `2 <= p` THEN ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[EXP_ADD; GSYM REAL_POW_POW] THEN
    EXISTS_TAC `&q * (a pow 2 + &3 * b pow 2) - &2 * a` THEN
    EXISTS_TAC `&2 * a * b * &q - &2 * b` THEN
    REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[INTEGER_CLOSED]; ALL_TAC]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MP_TAC(SPEC `&3` SQRT_POW_2) THEN REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?k. 0 < k /\ k <= 2 EXP p - 1 /\
        !n. ((&2 + sqrt(&3)) pow n == &1) equiv <=> k divides n`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `\x y:real. (x == y) equiv` ORDER_EXISTENCE_CARD) THEN
    REWRITE_TAC[REAL_POW_ITER] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
     (MESON[CARD_SUBSET; FINITE_SUBSET; LE_TRANS; CARD_IMAGE_LE; FINITE_IMAGE]
     `!f:num#num->A t. s SUBSET IMAGE f t /\ FINITE t /\ CARD t <= n
            ==> FINITE s /\ CARD s <= n`) THEN
    EXISTS_TAC `\(a,b) y. (y == &a + &b * sqrt(&3)) equiv` THEN
    EXISTS_TAC `(0..q-1) CROSS (0..q-1)` THEN
    SIMP_TAC[CARD_CROSS; FINITE_CROSS; FINITE_NUMSEG; CARD_NUMSEG] THEN
    ASM_SIMP_TAC[SUB_ADD; SUB_0; LE_1; GSYM EXP_2; SUBSET] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; IN_IMAGE; EXISTS_PAIR_THM] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_CROSS; GSYM REAL_POW_ITER] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `a:num` MP_TAC o SPEC `n:num`) THEN
    DISCH_THEN(X_CHOOSE_TAC `b:num`) THEN
    MAP_EVERY EXISTS_TAC [`a MOD q`; `b MOD q`] THEN
    ASM_SIMP_TAC[IN_NUMSEG; LE_0; DIVISION; FUN_EQ_THM;
                 ARITH_RULE `a <= q - 1 <=> a = 0 \/ a < q`] THEN
    MATCH_MP_TAC(MESON[]
     `(a == b) equiv /\
      ((a == b) equiv ==> !x. (x == a) equiv <=> (x == b) equiv)
      ==> !x. (x == a) equiv <=> (x == b) equiv`) THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    MAP_EVERY EXISTS_TAC [`&(a DIV q)`; `&(b DIV q)`] THEN
    REWRITE_TAC[INTEGER_CLOSED; REAL_RING
     `(a + b * s) - (a' + b' * s):real = (a'' + b'' * s) * q <=>
      a + b * s = (a'' * q + a') + (b'' * q + b') * s`] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL] THEN
    ASM_SIMP_TAC[GSYM DIVISION];
    SUBGOAL_THEN `k divides 2 EXP p` MP_TAC THENL
     [ASM_MESON_TAC[]; SIMP_TAC[DIVIDES_PRIMEPOW; PRIME_2]] THEN
    REWRITE_TAC[LE_LT; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
    ASM_SIMP_TAC[ARITH_RULE `k <= p - 1 ==> (k = p <=> p = 0)`] THEN
    REWRITE_TAC[EXP_EQ_0; ARITH_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `((&2 + sqrt (&3)) pow (2 EXP (p - 1)) == &1) (equiv)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN SIMP_TAC[DIVIDES_EXP_LE; LE_REFL] THEN
      ASM_SIMP_TAC[ARITH_RULE `i < p ==> i <= p - 1`];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&1 == -- &1) (equiv)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[cong] THEN EXPAND_TAC "equiv" THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[REAL_ARITH `&1 - -- &1 = &2`] THEN
    ASM_CASES_TAC `b = &0` THENL
     [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID] THEN
      DISCH_THEN(MP_TAC o AP_TERM `abs`) THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `?q. abs a = &q` (CHOOSE_THEN SUBST1_TAC)
      THENL [ASM_MESON_TAC[integer]; REWRITE_TAC[REAL_ABS_NUM]] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      MP_TAC PRIME_2 THEN REWRITE_TAC[prime; ARITH_EQ] THEN
      DISCH_THEN(MP_TAC o SPEC `q:num`) THEN ANTS_TAC THENL
       [REWRITE_TAC[divides] THEN ASM_MESON_TAC[MULT_SYM]; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [ASM_MESON_TAC[NUM_REDUCE_CONV `2 <= 1`]; ALL_TAC] THEN
      SUBGOAL_THEN `2 divides (2 EXP p - 1) + 2` MP_TAC THENL
       [MATCH_MP_TAC DIVIDES_ADD THEN ASM_REWRITE_TAC[DIVIDES_REFL];
        ASM_SIMP_TAC[ARITH_RULE `~(n - 1 = 0) ==> n - 1 + 2 = n + 1`]] THEN
      REWRITE_TAC[DIVIDES_2; EVEN_ADD; EVEN_EXP; ARITH] THEN
      UNDISCH_TAC `2 <= p` THEN ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_FIELD
       `&2 = (a + b * x) * q
        ==> ~(b = &0) ==> x = (&2 - a * q) / (b * q)`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o AP_TERM `rational`) THEN
      SIMP_TAC[IRRATIONAL_SQRT_PRIME; PRIME_CONV `prime 3`] THEN
      ASM_MESON_TAC[RATIONAL_CLOSED; INTEGER_CLOSED]]]);;

(* ------------------------------------------------------------------------- *)
(* Actual evaluation of the LL sequence.                                     *)
(* ------------------------------------------------------------------------- *)

let ll_verbose = ref false;;

let LUCAS_LEHMER_RULE =
  let pth_base = prove
   (`llseq (2 EXP p - 1) 0 = 4 MOD (2 EXP p - 1)`,
    REWRITE_TAC[llseq])
  and pth_step = prove
   (`llseq (2 EXP p - 1) n = m
     ==> m * m + q = 2 EXP p * q + 2 + r /\ r < 2 EXP p - 1
         ==> llseq (2 EXP p - 1) (SUC n) = r`,
    REWRITE_TAC[llseq] THEN
    ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[LT] THEN
    ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SIMP_TAC[MOD_1; ARITH_RULE `r < 1 <=> r = 0`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC `q + 1` THEN ASM_REWRITE_TAC[EXP_2] THEN
    MATCH_MP_TAC(ARITH_RULE `!p:num. (x + p) + y = p + z ==> x + y = z`) THEN
    EXISTS_TAC `q:num` THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
    MATCH_MP_TAC(ARITH_RULE
     `x + y - 1 + w = u + v + z + r + 2 /\ 2 EXP 2 <= y /\ w * 1 <= v
      ==> x + y - 1 - 2 = u + (v - w + z) + r`) THEN
    REWRITE_TAC[LE_MULT_LCANCEL; LE_EXP; EXP_EQ_0; ARITH_RULE
      `1 <= n <=> ~(n = 0)`] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC)
  and pconv_tt = GEN_REWRITE_CONV I [TAUT `T /\ T <=> T`]
  and p_tm = `p:num` and n_tm = `n:num` and m_tm = `m:num`
  and q_tm = `q:num` and r_tm = `r:num` in
  let ariconv =
    let BINOP2_CONV conv1 conv2 = COMB2_CONV (RAND_CONV conv1) conv2 in
    (BINOP2_CONV (BINOP2_CONV (LAND_CONV NUM_MULT_CONV THENC NUM_ADD_CONV)
                             (BINOP2_CONV NUM_MULT_CONV NUM_ADD_CONV THENC
                              NUM_ADD_CONV) THENC
                            NUM_EQ_CONV)
                 NUM_LT_CONV THENC pconv_tt) in
  fun p ->
    let th_base = CONV_RULE(RAND_CONV NUM_REDUCE_CONV)
     (INST [mk_small_numeral p,p_tm] pth_base)
    and th_step =  CONV_RULE(RAND_CONV(LAND_CONV NUM_REDUCE_CONV))
     (INST [mk_small_numeral p,p_tm] pth_step)
    and pp1 = pow2 p -/ num 1 in
    let rec lucas_lehmer k =
      if k = 0 then th_base,dest_numeral(rand(concl th_base)) else
      let th1,mval = lucas_lehmer (k - 1) in
      let gofer() =
        let mtm = rand(concl th1) in
        let yval = power_num mval (num 2) in
        let qval = quo_num yval pp1 and rval = mod_num yval pp1 -/ num 2 in
        let th3 = INST [mk_small_numeral(k - 1),n_tm; mtm,m_tm;
                        mk_numeral qval,q_tm; mk_numeral rval,r_tm] th_step in
        let th4 = MP th3 th1 in
        let th5 = MP th4 (EQT_ELIM(ariconv(lhand(concl th4)))) in
        CONV_RULE (LAND_CONV(RAND_CONV NUM_SUC_CONV)) th5,rval in
      if !ll_verbose then
       (Format.print_string("Iteration "^string_of_int k^" of "^
                            string_of_int(p-2));
        Format.print_newline();
        time gofer())
      else gofer() in
    let th1,y = lucas_lehmer (p - 2) in
    if y <>/ num 0 then failwith "LUCAS_LEHMER_RULE: not a prime" else
    let th2 = SPEC(mk_small_numeral p) LUCAS_LEHMER in
    let th3 = CONV_RULE
     (LAND_CONV(RAND_CONV(LAND_CONV
       (RAND_CONV NUM_SUB_CONV THENC K th1)))) th2 in
    MP th3 (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th3))));;

(* ------------------------------------------------------------------------- *)
(* Time a few small examples.                                                *)
(* ------------------------------------------------------------------------- *)

ll_verbose := false;;

time LUCAS_LEHMER_RULE 3;;
time LUCAS_LEHMER_RULE 5;;
time LUCAS_LEHMER_RULE 7;;
time LUCAS_LEHMER_RULE 13;;
time LUCAS_LEHMER_RULE 17;;
time LUCAS_LEHMER_RULE 19;;
time LUCAS_LEHMER_RULE 31;;
time LUCAS_LEHMER_RULE 61;;
time LUCAS_LEHMER_RULE 89;;
time LUCAS_LEHMER_RULE 107;;
time LUCAS_LEHMER_RULE 127;;
time LUCAS_LEHMER_RULE 521;;
time LUCAS_LEHMER_RULE 607;;

(* ------------------------------------------------------------------------- *)
(* These take a while, so they're commented out here.                        *)
(* ------------------------------------------------------------------------- *)

(***

ll_verbose := true;;

time LUCAS_LEHMER_RULE 1279;;
time LUCAS_LEHMER_RULE 2203;;
time LUCAS_LEHMER_RULE 2281;;
time LUCAS_LEHMER_RULE 3217;;
time LUCAS_LEHMER_RULE 4253;;
time LUCAS_LEHMER_RULE 4423;;
time LUCAS_LEHMER_RULE 9689;;
time LUCAS_LEHMER_RULE 9941;;
time LUCAS_LEHMER_RULE 11213;;
time LUCAS_LEHMER_RULE 19937;;
time LUCAS_LEHMER_RULE 21701;;
time LUCAS_LEHMER_RULE 23209;;
time LUCAS_LEHMER_RULE 44497;;
time LUCAS_LEHMER_RULE 86243;;
time LUCAS_LEHMER_RULE 110503;;
time LUCAS_LEHMER_RULE 132049;;
time LUCAS_LEHMER_RULE 216091;;
time LUCAS_LEHMER_RULE 756839;;
time LUCAS_LEHMER_RULE 859433;;
time LUCAS_LEHMER_RULE 1257787;;
time LUCAS_LEHMER_RULE 1398269;;
time LUCAS_LEHMER_RULE 2976221;;
time LUCAS_LEHMER_RULE 3021377;;
time LUCAS_LEHMER_RULE 6972593;;
time LUCAS_LEHMER_RULE 13466917;;
time LUCAS_LEHMER_RULE 20996011;;
time LUCAS_LEHMER_RULE 24036583;;
time LUCAS_LEHMER_RULE 25964951;;
time LUCAS_LEHMER_RULE 30402457;;

****)
