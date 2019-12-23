(* ========================================================================= *)
(* The multiplicative group of integers modulo n.                            *)
(* ========================================================================= *)

needs "Library/grouptheory.ml";;
needs "Library/primitive.ml";;

(* ------------------------------------------------------------------------- *)
(* A trivial general lemma used to dispose of degnerate cases.               *)
(* ------------------------------------------------------------------------- *)

let MULT_EQ_2 = prove
 (`!m n. m * n = 2 <=> m = 1 /\ n = 2 \/ m = 2 /\ n = 1`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * 2 <= p ==> ~(p = 2)`) THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Modulo-n multiplicative inverse, 1 in degenerate cases.                   *)
(* ------------------------------------------------------------------------- *)

let inverse_mod = new_definition
 `inverse_mod n x =
    if n <= 1 then 1
    else @y. y < n /\ (x * y == gcd(n,x)) (mod n)`;;

let INVERSE_MOD_BOUND,INVERSE_MOD_RMUL_GEN = (CONJ_PAIR o prove)
 (`(!n x. inverse_mod n x < n <=> 2 <= n) /\
   (!n x. (x * inverse_mod n x == gcd(n,x)) (mod n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REWRITE_TAC[inverse_mod] THEN
  MAP_EVERY X_GEN_TAC [`n:num`; `x:num`] THEN ASM_CASES_TAC `n <= 1` THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `n <= 1 ==> n = 0 \/ n = 1`)) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[CONG_MOD_0; CONG_MOD_1; GCD_0; MULT_CLAUSES];
    ASM_REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n <= 1)`] THEN
    CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[CONG_SOLVE_LT_EQ] THEN
    REWRITE_TAC[GCD_SYM; DIVIDES_REFL] THEN ASM_ARITH_TAC]);;

let INVERSE_MOD_LMUL_GEN = prove
 (`!n x. (inverse_mod n x * x == gcd(n,x)) (mod n)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[INVERSE_MOD_RMUL_GEN]);;

let INVERSE_MOD_RMUL_EQ = prove
 (`!n x. (x * inverse_mod n x == 1) (mod n) <=> coprime(n,x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [NUMBER_TAC; ALL_TAC] THEN
  REWRITE_TAC[COPRIME_GCD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[INVERSE_MOD_RMUL_GEN]);;

let INVERSE_MOD_LMUL_EQ = prove
 (`!n x. (inverse_mod n x * x == 1) (mod n) <=> coprime(n,x)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[INVERSE_MOD_RMUL_EQ]);;

let INVERSE_MOD_LMUL = prove
 (`!n x. coprime(n,x) ==> (inverse_mod n x * x == 1) (mod n)`,
  REWRITE_TAC[INVERSE_MOD_LMUL_EQ]);;

let INVERSE_MOD_RMUL = prove
 (`!n x. coprime(n,x) ==> (x * inverse_mod n x == 1) (mod n)`,
  REWRITE_TAC[INVERSE_MOD_RMUL_EQ]);;

let INVERSE_MOD_UNIQUE = prove
 (`!n a x.
        (a * x == 1) (mod n) /\ x <= n /\ ~(n = 1 /\ x = 0)
        ==> inverse_mod n a = x`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[CONG_MOD_0; MULT_EQ_1] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x:num = n` THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(a * n == z) (mod n) <=> n divides z`] THEN
    REWRITE_TAC[DIVIDES_ONE] THEN SIMP_TAC[inverse_mod; LE_REFL];
    REPEAT STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE
   `~(n = 1 /\ x = 0) ==> ~(x = n) /\ x <= n ==> ~(n = 1)`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[INVERSE_MOD_BOUND] THEN
  REPEAT(CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a * x == 1) (mod n) /\ (a * y == 1) (mod n) ==> (x == y) (mod n)`) THEN
  ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ] THEN
  UNDISCH_TAC `(a * x == 1) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let INVERSE_MOD_CONG = prove
 (`!n x y. (x == y) (mod n) ==> inverse_mod n x = inverse_mod n y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[inverse_mod] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP CONG_GCD_RIGHT) THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `(x:num == y) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let INVERSE_MOD_INVERSE_MOD_CONG = prove
 (`!n x. coprime(n,x) ==> (inverse_mod n (inverse_mod n x) == x) (mod n)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!x'. (x * x' == 1) (mod n) /\ (x' * x'' == 1) (mod n)
         ==> (x'' == x) (mod n)`) THEN
  EXISTS_TAC `inverse_mod n x` THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[INVERSE_MOD_RMUL_EQ];
    GEN_REWRITE_TAC RAND_CONV [INVERSE_MOD_RMUL_EQ] THEN
    CONV_TAC NUMBER_RULE]);;

let INVERSE_MOD_INVERSE_MOD = prove
 (`!n x. coprime(n,x) /\ 1 <= x /\ x <= n
         ==> inverse_mod n (inverse_mod n x) = x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INVERSE_MOD_UNIQUE THEN
  ASM_SIMP_TAC[INVERSE_MOD_LMUL_EQ; LE_1]);;

let ORDER_INVERSE_MOD = prove
 (`!n a. coprime(n,a) ==> order n (inverse_mod n a) = order n a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[order] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `d:num` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a * b == 1) (mod n) ==> ((a == 1) (mod n) <=> (b == 1) (mod n))`) THEN
  REWRITE_TAC[GSYM MULT_EXP] THEN MATCH_MP_TAC CONG_EXP_1 THEN
  ASM_REWRITE_TAC[INVERSE_MOD_LMUL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Multiplicative group of integers mod n, with degenerate {1} for n <= 1.   *)
(* ------------------------------------------------------------------------- *)

let modmul_group = new_definition
 `modmul_group n =
        if n <= 1 then singleton_group 1
        else group({m | m < n /\ coprime(m,n)},
                   1,inverse_mod n,(\a b. (a * b) MOD n))`;;

let MODMUL_GROUP = prove
 (`(!n. group_carrier(modmul_group n) =
        if n <= 1 then {1} else {m | m < n /\ coprime(m,n)}) /\
   (!n. group_id(modmul_group n) = 1) /\
   (!n. group_inv(modmul_group n) = inverse_mod n) /\
   (!n. group_mul(modmul_group n) =
        if n <= 1 then (\a b. 1) else (\a b. (a * b) MOD n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[modmul_group] THEN
  ASM_CASES_TAC `n <= 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SINGLETON_GROUP] THEN ASM_REWRITE_TAC[FUN_EQ_THM; inverse_mod];
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `~(n <= 1) <=> 2 <= n`])] THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul] THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM(CONJUNCT2 group_tybij)] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `1 < n <=> 2 <= n`] THEN
  REWRITE_TAC[NUMBER_RULE `coprime(1,n)`; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[INVERSE_MOD_BOUND] THEN
    MATCH_MP_TAC(NUMBER_RULE `!m. (a * m == 1) (mod n) ==> coprime(a,n)`) THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[INVERSE_MOD_LMUL_EQ] THEN
    ASM_MESON_TAC[COPRIME_SYM];
    REWRITE_TAC[COPRIME_LMOD; COPRIME_LMUL] THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `2 <= n ==> ~(n = 0)`];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    REWRITE_TAC[MOD_MOD_REFL] THEN REWRITE_TAC[MOD_MULT_MOD2] THEN
    REWRITE_TAC[MULT_ASSOC];
    SIMP_TAC[MULT_CLAUSES; MOD_LT];
    REWRITE_TAC[MOD_UNIQUE; INVERSE_MOD_RMUL_EQ; INVERSE_MOD_LMUL_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> 1 < n`] THEN
    MESON_TAC[COPRIME_SYM]]);;

let FINITE_MODMUL_GROUP = prove
 (`!n. FINITE(group_carrier(modmul_group n))`,
  GEN_TAC THEN REWRITE_TAC[MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_SING] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
  ARITH_TAC);;

let ORDER_MODMUL_GROUP = prove
 (`!n. CARD(group_carrier(modmul_group n)) =
       if n = 0 then 1 else phi n`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MODMUL_GROUP; LE_0; CARD_SING] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[LE_REFL; PHI_1; CARD_SING] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[PHI_ALT]);;

let HAS_SIZE_MODMUL_GROUP = prove
 (`!n. ~(n = 0) ==> group_carrier(modmul_group n) HAS_SIZE phi n`,
  SIMP_TAC[HAS_SIZE; FINITE_MODMUL_GROUP] THEN
  SIMP_TAC[ORDER_MODMUL_GROUP]);;

let ABELIAN_MODMUL_GROUP = prove
 (`!n. abelian_group(modmul_group n)`,
  GEN_TAC THEN REWRITE_TAC[abelian_group; MODMUL_GROUP] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_SYM]);;

let TRIVIAL_MODMUL_GROUP = prove
 (`!n. trivial_group(modmul_group n) <=> n <= 2`,
  GEN_TAC THEN REWRITE_TAC[TRIVIAL_GROUP_HAS_SIZE_1; HAS_SIZE] THEN
  REWRITE_TAC[FINITE_MODMUL_GROUP] THEN
  REWRITE_TAC[ORDER_MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[PHI_1; ARITH] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[PHI_2; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `~(n <= 2) /\ 2 <= p ==> (p = 1 <=> n <= 2)`) THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC PHI_LOWERBOUND_2] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chinese remainder theorem in group-theoretic language.                    *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP = prove
 (`!m n. 2 <= m /\ 2 <= n
         ==> group_homomorphism (modmul_group(m * n),
                                 prod_group (modmul_group m)
                                            (modmul_group n))
                                (\a. (a MOD m),(a MOD n))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; PROD_GROUP; SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[MODMUL_GROUP] THEN
  REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
  ASM_SIMP_TAC[MULT_EQ_0; MULT_EQ_1; IN_ELIM_THM; MOD_LT_EQ; COPRIME_LMOD;
               PAIR_EQ; ARITH_RULE  `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  SIMP_TAC[COPRIME_RMUL; MOD_MOD; ONCE_REWRITE_RULE[MULT_SYM] MOD_MOD] THEN
  REWRITE_TAC[MOD_MULT_MOD2]);;

let GROUP_ISOMORPHISM_PROD_MODMUL_GROUP = prove
 (`!m n. 2 <= m /\ 2 <= n /\ coprime(m,n)
         ==> group_isomorphism (modmul_group(m * n),
                                prod_group (modmul_group m)
                                           (modmul_group n))
                               (\a. (a MOD m),(a MOD n))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE o snd) THEN
  ASM_SIMP_TAC[ORDER_MODMUL_GROUP; FINITE_PROD_GROUP;
               FINITE_MODMUL_GROUP; MULT_EQ_0;
               CONJUNCT1 PROD_GROUP; CARD_CROSS; PHI_MULTIPLICATIVE;
               ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[group_monomorphism] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP] THEN
  ASM_SIMP_TAC[MODMUL_GROUP; MULT_EQ_0; MULT_EQ_1;
               ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`;
               ARITH_RULE `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  REWRITE_TAC[PAIR_EQ; IN_ELIM_THM; GSYM CONG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
  EXISTS_TAC `m * n:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NUMBER_RULE
   `coprime(m:num,n) /\ (x == y) (mod m) /\ (x == y) (mod n)
    ==> (x == y) (mod(m * n))`]);;

let ISOMORPHIC_GROUP_MODMUL_GROUP = prove
 (`!m n. coprime(m,n)
         ==> prod_group (modmul_group m)
                        (modmul_group n)
             isomorphic_group (modmul_group (m * n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[ISOMORPHIC_TRIVIAL_GROUPS]
   `(trivial_group G <=> trivial_group H) /\
    (~trivial_group G /\ ~trivial_group H ==> G isomorphic_group H)
    ==> G isomorphic_group H`) THEN
  REWRITE_TAC[TRIVIAL_PROD_GROUP; TRIVIAL_MODMUL_GROUP] THEN
  POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_SIMP_TAC[COPRIME_0; ARITH] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[COPRIME_0; ARITH] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `m = 1` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ISOMORPHIC_PROD_TRIVIAL_GROUP;
              TRIVIAL_MODMUL_GROUP; ARITH] THEN
  ASM_CASES_TAC `n = 1` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ISOMORPHIC_PROD_TRIVIAL_GROUP;
               TRIVIAL_MODMUL_GROUP; ARITH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; MULT_EQ_1; MULT_EQ_2] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_REFL]; DISCH_THEN(K ALL_TAC)] THEN
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `\a. (a MOD m),(a MOD n)` THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_PROD_MODMUL_GROUP THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GROUP_POW_MODMUL_GROUP = prove
 (`!n a k. group_pow (modmul_group n) a k =
           if n <= 1 then 1 else (a EXP k) MOD n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_pow; MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP] THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    MESON_TAC[MOD_MULT_MOD2; MOD_MOD_REFL; MOD_EXP_MOD]]);;

let GROUP_ELEMENT_ORDER_MODMUL_GROUP = prove
 (`!n a. a IN group_carrier(modmul_group n)
         ==> group_element_order (modmul_group n) a = order n a`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE] THEN
  REWRITE_TAC[GSYM ORDER_DIVIDES] THEN
  X_GEN_TAC `k:num` THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GROUP_POW_MODMUL_GROUP] THEN
  REWRITE_TAC[MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[IN_SING; EXP_ONE; CONG] THEN
  DISCH_THEN(K ALL_TAC) THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Existence of primitive roots in group-theoretic language.                 *)
(* ------------------------------------------------------------------------- *)

let CYCLIC_MODMUL_GROUP = prove
 (`!n. cyclic_group(modmul_group n) <=>
       n = 0 \/ n = 1 \/ n = 2 \/ n = 4 \/
       ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)`,
  GEN_TAC THEN ASM_CASES_TAC `n <= 2` THENL
   [ASM_SIMP_TAC[TRIVIAL_MODMUL_GROUP;
                 TRIVIAL_IMP_CYCLIC_GROUP] THEN
    ASM_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
  SIMP_TAC[CYCLIC_GROUP_ELEMENT_ORDER; FINITE_MODMUL_GROUP] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[GROUP_ELEMENT_ORDER_MODMUL_GROUP] THEN
  MP_TAC(SPEC `n:num` PRIMITIVE_ROOT_EXISTS) THEN
  ASM_SIMP_TAC[ORDER_MODMUL_GROUP; FINITE_MODMUL_GROUP;
               MODMUL_GROUP;
               ARITH_RULE `2 < n ==> ~(n = 0) /\ ~(n = 1) /\ ~(n <= 1)`] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IMP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k MOD n` THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `2 < n ==> ~(n = 0)`] THEN
  MATCH_MP_TAC(TAUT `(~p ==> ~q) /\ q ==> p /\ q`) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN SIMP_TAC[GSYM ORDER_EQ_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[PHI_EQ_0; ARITH_RULE `2 < n ==> ~(n = 0)`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;
