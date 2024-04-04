(* ========================================================================= *)
(* Prove that a congruence x^3 + a * x + b == 0 (mod p) has no solution      *)
(* (fails with an exception if it does). This is essentually done via a      *)
(* computation of gcd(x^p - x,x^3 + a * x + b) over F_p[x].                  *)
(*                                                                           *)
(* This can be used to show that a Weierstrass curve y^2 = x^3 + a * x + b   *)
(* has no 2-torsion points, since such points would necessarily have y = 0   *)
(* because the negation in the curve group of (x,y) is (x,-y).               *)
(* ========================================================================= *)

needs "Library/pocklington.ml";;

let num_modinv =
  let rec gcdex(m,n) =
    if n </ m then let (x,y) = gcdex(n,m) in (y,x)
    else if m =/ num 0 then (num 0,num 1) else
    let q = quo_num n m in
    let r = n -/ q */ m in
    let (x,y) = gcdex(r,m) in (y -/ q */ x,x) in
  fun p n -> let (x,y) = gcdex(n,p) in
             if mod_num (x */ n) p =/ num_1 then mod_num x p
             else failwith "num_modinv";;

let EXCLUDE_MODULAR_CUBIC_ROOTS =
  let lemma_flt = prove
   (`((x pow 3 + a * x + b:int == &0) (mod &p)
      ==> (x pow p == c2 * x pow 2 + c1 * x + c0) (mod &p))
     ==> prime p
         ==> ~(b rem &p = &0)
             ==> ((x pow 3 + a * x + b == &0) (mod &p)
                 ==> (&0 == c2 * x pow 2 + (c1 - &1) * x + c0) (mod &p))`,
    DISCH_THEN(fun th -> REPEAT DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(INTEGER_RULE
     `(xp == x) (mod p)
      ==> (xp:int == c2 * x pow 2 + c1 * x + c0) (mod p)
           ==> (&0 == c2 * x pow 2 + (c1 - &1) * x + c0) (mod p)`) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (INTEGER_RULE
     `(x pow 3 + a * x + b:int == &0) (mod p)
      ==> coprime(b,p) ==> coprime(x,p)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(INTEGER_RULE
       `(b rem p == b) (mod p) /\ coprime(b rem p,p) ==> coprime(b,p)`) THEN
      REWRITE_TAC[INT_REM_MOD_SELF] THEN UNDISCH_TAC `~(b rem &p = &0)` THEN
      SUBGOAL_THEN `&0 <= b rem &p /\ b rem &p < &p` MP_TAC THENL
       [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
        ASM_SIMP_TAC[INT_OF_NUM_EQ; PRIME_IMP_NZ; INT_OF_NUM_LT; LE_1];
        SPEC_TAC(`b rem &p`,`x:int`)] THEN
      REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[INT_OF_NUM_EQ; INT_OF_NUM_LT] THEN
      REPEAT DISCH_TAC THEN REWRITE_TAC[GSYM num_coprime] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
      DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN ASM_ARITH_TAC;
      DISCH_THEN(MP_TAC o MATCH_MP (INTEGER_RULE
       `coprime(b,p) ==> (b rem p == b) (mod p) ==> coprime(b rem p,p)`)) THEN
      REWRITE_TAC[INT_REM_MOD_SELF]] THEN
    REWRITE_TAC[GSYM INT_REM_EQ] THEN ONCE_REWRITE_TAC[GSYM INT_POW_REM] THEN
    SUBGOAL_THEN `&0 <= x rem &p /\ x rem &p < &p` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_REM_POS_EQ; INT_LT_REM_EQ] THEN
      ASM_SIMP_TAC[INT_OF_NUM_EQ; PRIME_IMP_NZ; INT_OF_NUM_LT; LE_1];
      SPEC_TAC(`x rem &p`,`x:int`)] THEN
    REWRITE_TAC[GSYM INT_FORALL_POS; IMP_CONJ] THEN
    REWRITE_TAC[INT_POW_REM; GSYM num_coprime; INT_OF_NUM_LT] THEN
    X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_REM; INT_OF_NUM_EQ] THEN
    MP_TAC(SPECL [`n:num`; `p:num`] FERMAT_LITTLE_PRIME) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(x EXP a == 1) (mod p) ==> (x * x EXP a == x) (mod p)`)) THEN
    ASM_SIMP_TAC[GSYM(CONJUNCT2 EXP); CONG; MOD_LT] THEN
    ASM_SIMP_TAC[PRIME_IMP_NZ; ARITH_RULE `~(p = 0) ==> SUC(p - 1) = p`])
  and lemma_tolin = prove
   (`(x pow 3 + a * x + b == &0) (mod p) /\
     (&0 == &1 * x pow 2 + c1 * x + c0) (mod p)
     ==> (&0:int == &0 * x pow 2 +
                    (a + c1 pow 2 - c0) * x + (b + c0 * c1)) (mod p)`,
    INTEGER_TAC)
  and lemma_toconst = prove
   (`(x pow 3 + a * x + b == &0) (mod p) /\
     (&0:int == &0 * x pow 2 + &1 * x + c0) (mod p)
     ==> (&0:int == --c0 pow 3 - a * c0 + b) (mod p)`,
    INTEGER_TAC)
  and lemma_3_2 = prove
   (`(x pow 3 + a * x + b:int == &0) (mod p)
     ==> (y == c3 * x pow 3 + c2 * x pow 2 + c1 * x + c0) (mod p)
         ==> (y == c2 * x pow 2 + (c1 - a * c3) * x + (c0 - b * c3)) (mod p)`,
    INTEGER_TAC)
  and lemma_4_3 = prove
   (`(x pow 3 + a * x + b:int == &0) (mod p)
     ==> (y == c4 * x pow 4 + c3 * x pow 3 + c2 * x pow 2 + c1 * x + c0) (mod p)
         ==> (y == c3 * x pow 3 + (c2 - a * c4) * x pow 2 +
                   (c1 - b * c4) * x + c0) (mod p)`,
    INTEGER_TAC)
  and lemma_rem = prove
   (`(y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> (y == c2 rem p * x pow 2 + c1 rem p * x + c0 rem p) (mod p)`,
    MATCH_MP_TAC(INTEGER_RULE
     `(c2:int == c2') (mod p) /\ (c1 == c1') (mod p) /\ (c0 == c0') (mod p)
      ==> (y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
          ==> (y:int == c2' * x pow 2 + c1' * x + c0') (mod p)`) THEN
    REWRITE_TAC[INT_CONG_RREM] THEN CONV_TAC INTEGER_RULE)
  and lemma_mulx = prove
   (`((x:int) pow n == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> (x pow (n + 1) == c2 * x pow 3 + c1 * x pow 2 + c0 * x + &0) (mod p)`,
    REWRITE_TAC[INT_POW_ADD] THEN INTEGER_TAC)
  and lemma_sqr = prove
   (`((x:int) pow n == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> (x pow (2 * n) ==
          (c2 pow 2) * x pow 4 + (&2 * c1 * c2) * x pow 3 +
          (c1 pow 2 + &2 * c0 * c2) * x pow 2 +
          (&2 * c0 * c1) * x +
          c0 pow 2) (mod p)`,
    REWRITE_TAC[MULT_2; INT_POW_ADD] THEN
    INTEGER_TAC)
  and lemma_mulc = prove
   (`(y:int == c2 * x pow 2 + c1 * x + c0) (mod p)
     ==> !c. (c * y == (c * c2) * x pow 2 + (c * c1) * x + c * c0) (mod p)`,
    INTEGER_TAC)
  and pth0 = INTEGER_RULE `!p. ((x:int) pow 0 == &0 * x pow 2 + &0 * x + &1)
                               (mod &p)` in
  fun tm primeth ->
    let th = ASSUME tm in
    let rule_3_2 = MATCH_MP(MATCH_MP lemma_3_2 th)
    and rule_4_3 = MATCH_MP(MATCH_MP lemma_4_3 th)
    and rule_mulx = MATCH_MP lemma_mulx
    and rule_mulc = MATCH_MP lemma_mulc
    and rule_sqr = MATCH_MP lemma_sqr
    and rule_rem = MATCH_MP lemma_rem in
    let qtm = rand(concl primeth) in
    let q = dest_numeral qtm in
    let th0 = SPEC qtm pth0 in
    let rec power_rule n =
      if n =/ num_0 then th0 else
      let m = quo_num n num_2 in
      let th1 = power_rule m in
      let th2 = (CONV_RULE INT_REDUCE_CONV o
                 CONV_RULE NUM_REDUCE_CONV o
                 rule_rem o rule_3_2 o rule_4_3 o rule_sqr) th1 in
      if mod_num n num_2 =/ num_0 then th2 else
      (CONV_RULE INT_REDUCE_CONV o
       CONV_RULE NUM_REDUCE_CONV o
       rule_rem o rule_3_2 o rule_mulx) th2 in
    let th1 = DISCH tm (power_rule q) in
    let th2 = MP (MATCH_MP lemma_flt th1) primeth in
    let th3 = MP th2 (EQT_ELIM(INT_REDUCE_CONV(lhand(concl th2)))) in
    let th4 = (CONV_RULE INT_REDUCE_CONV o rule_rem) (UNDISCH th3) in
    let hc = dest_intconst(lhand(lhand(rand(rator(concl th4))))) in
    let th8 =
      if hc =/ num_0 then th4 else
      let th5 = SPEC (mk_intconst(num_modinv q hc)) (rule_mulc th4) in
      let th6 = (CONV_RULE INT_REDUCE_CONV o rule_rem) th5 in
      let th7 = MATCH_MP lemma_tolin (CONJ (ASSUME tm) th6) in
      (CONV_RULE INT_REDUCE_CONV o rule_rem) th7 in
    let lc = dest_intconst(lhand(lhand(rand(rand(rator(concl th8)))))) in
    let th9 = SPEC (mk_intconst(num_modinv q lc)) (rule_mulc th8) in
    let tha = (CONV_RULE INT_REDUCE_CONV o rule_rem) th9 in
    let thb = MATCH_MP lemma_toconst (CONJ (ASSUME tm) tha) in
    let thc = CONV_RULE INT_REDUCE_CONV (REWRITE_RULE[GSYM INT_REM_EQ] thb) in
    NOT_INTRO(DISCH tm thc);;

let EXCLUDE_MODULAR_CUBIC_ROOTS_TAC primeth defths =
  X_GEN_TAC `x:int` THEN
  GEN_REWRITE_TAC ONCE_DEPTH_CONV
   [INT_ARITH `x pow 3 - &3 * x + b:int = x pow 3 + (-- &3) * x + b /\
               x pow 3 + &c = x pow 3 + &0 * x + &c`] THEN
  REWRITE_TAC defths THEN
  W(fun (asl,w) -> ACCEPT_TAC
    (EXCLUDE_MODULAR_CUBIC_ROOTS (rand w)
      (ONCE_REWRITE_RULE defths primeth)));;
