(* ========================================================================= *)
(* Zolotarev-Frobenius characterization of the Jacobi symbol (a/n) for odd   *)
(* n as the sign of the permutation "multiplication by a modulo n".          *)
(* ========================================================================= *)

needs "Library/jacobi.ml";;
needs "Library/permutations.ml";;

(* ------------------------------------------------------------------------- *)
(* The Zolotarev permutation and its most basic properties.                  *)
(* ------------------------------------------------------------------------- *)

let zolotarev = new_definition
 `zolotarev(a,n) = \m. if m < n then (a * m) MOD n else m`;;

let PERMUTES_ZOLOTAREV = prove
 (`!a n. coprime(a,n) ==> (zolotarev(a,n)) permutes {m | m < n}`,
  SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  SIMP_TAC[zolotarev; IN_ELIM_THM; MOD_LT_EQ_LT; GSYM CONG] THEN
  REPEAT STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NUMBER_RULE
   `coprime(a:num,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)`]);;

let PERMUTES_ZOLOTAREV_ALT = prove
 (`!a n. coprime(a,n) ==> (zolotarev(a,n)) permutes {m | 0 < m /\ m < n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PERMUTES_SUPERSET THEN
  EXISTS_TAC `{m:num | m < n}` THEN ASM_SIMP_TAC[PERMUTES_ZOLOTAREV] THEN
  X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
  SIMP_TAC[IMP_CONJ; ARITH_RULE `~(0 < m) <=> m = 0`] THEN
  REWRITE_TAC[zolotarev] THEN ARITH_TAC);;

let PERMUTATION_ZOLOTAREV = prove
 (`!a n. coprime(a,n) ==> permutation (zolotarev(a,n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PERMUTATION_PERMUTES] THEN
  EXISTS_TAC `{m:num | m < n}` THEN
  ASM_SIMP_TAC[PERMUTES_ZOLOTAREV; FINITE_NUMSEG_LT]);;

let ZOLATAREV_MOD = prove
 (`!a n. zolotarev(a MOD n,n) = zolotarev(a,n)`,
  REWRITE_TAC[FUN_EQ_THM; zolotarev] THEN
  MESON_TAC[MOD_MULT_MOD2; MOD_MOD_REFL]);;

let ZOLOTAREV_CONG = prove
 (`!a b n. (a == b) (mod n) ==> zolotarev(a,n) = zolotarev(b,n)`,
  MESON_TAC[CONG; ZOLATAREV_MOD]);;

(* ------------------------------------------------------------------------- *)
(* A variant of the Zolotarev permutation, just permuting the units.         *)
(* This is an independently interesting building-block, because for any      *)
(* modulus >= 3 with a primitive root, the sign of this modified version     *)
(* exactly characterizes quadratic residuosity.                              *)
(* ------------------------------------------------------------------------- *)

let zolotarevu = new_definition
 `zolotarevu(a,n) = \m. if coprime(m,n) /\ m < n then (a * m) MOD n else m`;;

let PERMUTES_ZOLOTAREVU = prove
 (`!a n. coprime(a,n)
         ==> (zolotarevu(a,n)) permutes {m | coprime(m,n) /\ m < n}`,
  ONCE_REWRITE_TAC[SET_RULE
   `{x | P x /\ Q x} = {x | x IN {y | Q y} /\ P x}`] THEN
  SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
  SIMP_TAC[zolotarevu; IN_ELIM_THM; MOD_LT_EQ_LT; GSYM CONG] THEN
  SIMP_TAC[COPRIME_LMOD; COPRIME_LMUL] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[]; ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `n:num` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NUMBER_RULE
   `coprime(a:num,n) /\ (a * x == a * y) (mod n) ==> (x == y) (mod n)`]);;

let PERMUTATION_ZOLOTAREVU = prove
 (`!a n. coprime(a,n) ==> permutation (zolotarevu(a,n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PERMUTATION_PERMUTES] THEN
  EXISTS_TAC `{m:num | m IN {m | m < n} /\ coprime(m,n)}` THEN
  SIMP_TAC[FINITE_NUMSEG_LT; FINITE_RESTRICT] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  ASM_SIMP_TAC[PERMUTES_ZOLOTAREVU; IN_ELIM_THM]);;

let ZOLATAREVU_MOD = prove
 (`!a n. zolotarevu(a MOD n,n) = zolotarevu(a,n)`,
  REWRITE_TAC[FUN_EQ_THM; zolotarevu] THEN
  MESON_TAC[MOD_MULT_MOD2; MOD_MOD_REFL]);;

let ZOLOTAREVU_PRIMITIVE = prove
 (`!a n. 3 <= n /\ coprime(a,n) /\ (?g. order n g = phi n)
         ==> (evenperm(zolotarevu(a,n)) <=> ?x. (x EXP 2 == a) (mod n))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `g:num`; `a:num`]
        PRIMITIVE_ROOT_SURJECTIVE_ALT) THEN
  ASM_REWRITE_TAC[CONG; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:num` THEN ONCE_REWRITE_TAC[GSYM ZOLATAREVU_MOD] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  REWRITE_TAC[GSYM CONG; ZOLATAREVU_MOD] THEN
  ASM_CASES_TAC `coprime(n:num,g)` THENL
   [ALL_TAC; ASM_MESON_TAC[ORDER_EQ_0; COPRIME_SYM; PHI_EQ_0]] THEN
  ASM_SIMP_TAC[QUADRATIC_RESIDUE_MODULO_PRIMITIVE_POWER] THEN
  TRANS_TAC EQ_TRANS
   `evenperm(\i. if i < phi n then (i + k) MOD phi n else i)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[EVENPERM_CYCLIC_N] THEN
    ASM_SIMP_TAC[GSYM NOT_EVEN; EVEN_PHI; PHI_EQ_0]] THEN
  MATCH_MP_TAC EVENPERM_TRANSFER THEN
  MAP_EVERY EXISTS_TAC [`\i. (g EXP i) MOD n`; `{i | i < phi n}`] THEN
  SIMP_TAC[FINITE_NUMSEG_LT; PERMUTES_FINITE_INJECTIVE] THEN
  REWRITE_TAC[IN_ELIM_THM; IMP_CONJ] THEN
  ASM_SIMP_TAC[zolotarevu; MOD_LT_EQ] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM CONG] THEN
    ASM_SIMP_TAC[ORDER_DIVIDES_EXPDIFF] THEN MESON_TAC[CONG_IMP_EQ];
    ARITH_TAC;
    REWRITE_TAC[GSYM CONG; CONG_ADD_RCANCEL_EQ] THEN MESON_TAC[CONG_IMP_EQ];
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN
    ASM_REWRITE_TAC[COPRIME_RMOD; COPRIME_REXP] THEN
    ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    REWRITE_TAC[MOD_MOD_REFL] THEN REWRITE_TAC[MOD_MULT_MOD2] THEN
    REWRITE_TAC[GSYM EXP_ADD; GSYM CONG] THEN
    ASM_SIMP_TAC[ORDER_DIVIDES_EXPDIFF; CONG_RMOD; CONG_REFL] THEN
    REWRITE_TAC[CONG; ADD_SYM];
    ASM_SIMP_TAC[PRIMITIVE_ROOT_IMAGE] THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Hence characterize zolotarev for odd prime powers p^k by induction,       *)
(* splitting the case of p^{k+1} into the units (covered by zolotarevu)      *)
(* and the non-units, which are just the p^k cases multiplied by p.          *)
(* ------------------------------------------------------------------------- *)

let ZOLATAREV_EQ_ZOLATAREVU = prove
 (`!a p. prime p ==> zolotarev(a,p) = zolotarevu(a,p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zolotarev; zolotarevu; FUN_EQ_THM] THEN
  X_GEN_TAC `n:num` THEN ASM_CASES_TAC `n:num < p` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
  REWRITE_TAC[COND_SWAP] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE_STRONG) THEN
  STRIP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MOD_0]);;

let ZOLOTAREV_1 = prove
 (`!a. zolotarev(a,1) = I`,
  REWRITE_TAC[FUN_EQ_THM; I_DEF] THEN REPEAT GEN_TAC THEN
  SIMP_TAC[zolotarev; ARITH_RULE `m < 1 <=> m = 0`; MULT_CLAUSES; MOD_0] THEN
  MESON_TAC[]);;

let JACOBI_EQ_ZOLOTAREV_PRIMEPOW = prove
 (`!a p k.
        prime p /\ ODD p /\ coprime(a,p)
        ==> real_of_int(jacobi(a,p EXP k)) = sign(zolotarev(a,p EXP k))`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `p = 0` THEN ASM_REWRITE_TAC[PRIME_0] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  REWRITE_TAC[JACOBI_REXP; int_pow_th] THEN
  MATCH_MP_TAC num_INDUCTION THEN
  REWRITE_TAC[EXP; ZOLOTAREV_1; real_pow; SIGN_I] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  SUBGOAL_THEN
   `zolotarev (a,p EXP SUC k) =
    zolotarevu(a,p EXP SUC k) o
    (\i. if p divides i then zolotarev(a,p EXP SUC k) i else i)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; zolotarev; zolotarevu] THEN
    X_GEN_TAC `i:num` THEN ASM_CASES_TAC `(p:num) divides i` THEN
    ASM_CASES_TAC `i < p EXP (SUC k)` THEN
    ASM_REWRITE_TAC[COPRIME_LMOD; MOD_LT_EQ; EXP_EQ_0] THEN
    ASM_REWRITE_TAC[COPRIME_REXP; NOT_SUC; COPRIME_LMUL] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] PRIME_COPRIME_EQ];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SIGN_COMPOSE o lhand o snd) THEN
  ASM_SIMP_TAC[PERMUTATION_ZOLOTAREVU; COPRIME_REXP] THEN ANTS_TAC THENL
   [MATCH_MP_TAC PERMUTATION_RESTRICT THEN
    ASM_SIMP_TAC[ETA_AX; PERMUTATION_ZOLOTAREV; COPRIME_REXP] THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[zolotarev] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [TAUT `(p <=> q) <=> (~p <=> ~q)`] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM]
     (GSYM PRIME_COPRIME_EQ)] THEN
    ASM_MESON_TAC[COPRIME_REXP; COPRIME_LMOD; NOT_SUC; COPRIME_LMUL];
    DISCH_THEN SUBST1_TAC] THEN
  BINOP_TAC THENL
   [ASM_SIMP_TAC[JACOBI_PRIME] THEN ONCE_REWRITE_TAC[GSYM COND_SWAP] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM]
     (GSYM PRIME_COPRIME_EQ)] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[sign; int_neg_th; int_of_num_th] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MP_TAC(ISPECL [`p:num`; `a:num`; `SUC k`]
       QUADRATIC_RESIDUE_MODULO_ODD_POWER) THEN
    ASM_REWRITE_TAC[NOT_SUC] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[COPRIME_SYM]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC ZOLOTAREVU_PRIMITIVE THEN
    ASM_REWRITE_TAC[COPRIME_REXP] THEN CONJ_TAC THENL
     [TRANS_TAC LE_TRANS `p EXP 1` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[ODD_PRIME; EXP_1]; ALL_TAC] THEN
      REWRITE_TAC[LE_EXP; NOT_SUC; ARITH_RULE `1 <= SUC k`] THEN
      CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[COND_ID];
      REWRITE_TAC[PRIMITIVE_ROOT_EXISTS] THEN ASM_MESON_TAC[ODD_PRIME]];
    MATCH_MP_TAC SIGN_TRANSFER THEN
    EXISTS_TAC `\x:num. p * x` THEN
    EXISTS_TAC `{i | i < p EXP k}` THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; PERMUTES_ZOLOTAREV; COPRIME_REXP] THEN
    ASM_SIMP_TAC[EQ_MULT_LCANCEL] THEN
    SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL; zolotarev; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; EXP] THEN
      MESON_TAC[MOD_MULT2; MULT_AC];
      X_GEN_TAC `j:num` THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      ASM_MESON_TAC[LT_MULT_LCANCEL; EXP]]]);;

(* ------------------------------------------------------------------------- *)
(* Now extend to all odd moduli via the Chinese Remainder Theorem.           *)
(* ------------------------------------------------------------------------- *)

let JACOBI_EQ_ZOLOTAREV = prove
 (`!a n. ODD n /\ coprime(a,n)
         ==> real_of_int(jacobi(a,n)) = sign(zolotarev(a,n))`,
  GEN_TAC THEN MATCH_MP_TAC INDUCT_COPRIME_ALT THEN
  REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_SIMP_TAC[ODD_EXP; COPRIME_REXP] THEN
    REWRITE_TAC[JACOBI_1; ZOLOTAREV_1; EXP; int_of_num_th; SIGN_I] THEN
    ASM_SIMP_TAC[JACOBI_EQ_ZOLOTAREV_PRIMEPOW]] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[ODD_MULT; COPRIME_RMUL] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[JACOBI_RMUL; int_mul_th] THEN
  REPEAT(FIRST_X_ASSUM SUBST1_TAC) THEN
  TRANS_TAC EQ_TRANS
   `sign(\(i,j). if i IN {i | i < m} /\ j IN {j | j < n}
                 then zolotarev(a,m) i,zolotarev(a,n) j else i,j)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[SIGN_CARTESIAN_PRODUCT; PERMUTES_ZOLOTAREV;
                 FINITE_NUMSEG_LT; ETA_AX] THEN
    BINOP_TAC THEN REWRITE_TAC[sign] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_POW_ONE; REAL_POW_NEG] THEN
    ASM_REWRITE_TAC[CARD_NUMSEG_LT; GSYM NOT_ODD];
    ALL_TAC] THEN
  MATCH_MP_TAC SIGN_TRANSFER THEN
  EXISTS_TAC `\i. i MOD m,i MOD n` THEN
  EXISTS_TAC `{i:num | i < m * n}` THEN
  ASM_SIMP_TAC[FINITE_NUMSEG_LT; PERMUTES_ZOLOTAREV; COPRIME_RMUL] THEN
  ASM_REWRITE_TAC[o_THM; MOD_LT_EQ; IN_ELIM_THM; PAIR_EQ; ] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[PAIR_EQ; GSYM CONG] THEN STRIP_TAC THEN
    MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `m * n:num` THEN
    ASM_SIMP_TAC[CONG_CHINESE];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[zolotarev; MOD_LT_EQ; PAIR_EQ] THEN
    REWRITE_TAC[MOD_MOD; ONCE_REWRITE_RULE[MULT_SYM] MOD_MOD] THEN
    MESON_TAC[MOD_MULT_MOD2; MOD_MOD_REFL];
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    ASM_CASES_TAC `i:num < m /\ j:num < n` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[zolotarev; MOD_LT_EQ; PAIR_EQ] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MP_TAC(ISPECL [`m:num`; `n:num`; `i:num`; `j:num`]
      CHINESE_REMAINDER_UNIQUE) THEN
    ASM_REWRITE_TAC[EXISTS_UNIQUE_DEF] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[IN_IMAGE; PAIR_EQ; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[CONG; MOD_LT] THEN MESON_TAC[]]);;
