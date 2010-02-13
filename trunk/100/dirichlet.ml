(* ========================================================================= *)
(* Dirichlet's theorem.                                                      *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "Library/agm.ml";;
needs "Multivariate/transcendentals.ml";;
needs "Library/pocklington.ml";;
needs "Library/multiplicative.ml";;
needs "Examples/mangoldt.ml";;

prioritize_real();;
prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Rearranging a certain kind of double sum.                                 *)
(* ------------------------------------------------------------------------- *)

let VSUM_VSUM_DIVISORS = prove
 (`!f x. vsum (1..x) (\n. vsum {d | d divides n} (f n)) =
         vsum (1..x) (\n. vsum (1..(x DIV n)) (\k. f (k * n) n))`,
  SIMP_TAC[VSUM; FINITE_DIVISORS; LE_1] THEN
  SIMP_TAC[VSUM; FINITE_NUMSEG; ITERATE_ITERATE_DIVISORS;
           MONOIDAL_VECTOR_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Useful approximation lemmas.                                              *)
(* ------------------------------------------------------------------------- *)

let REAL_EXP_1_LE_4 = prove
 (`exp(&1) <= &4`,
  ONCE_REWRITE_TAC[ARITH_RULE `&1 = &1 / &2 + &1 / &2`; REAL_EXP_ADD] THEN
  REWRITE_TAC[REAL_ARITH `&4 = &2 * &2`; REAL_EXP_ADD] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
  MP_TAC(SPEC `&1 / &2` REAL_EXP_BOUND_LEMMA) THEN REAL_ARITH_TAC);;

let DECREASING_LOG_OVER_N = prove
 (`!n. 4 <= n ==> log(&n + &1) / (&n + &1) <= log(&n) / &n`,
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. clog z / z`; `\z. (Cx(&1) - clog(z)) / z pow 2`;
                 `Cx(&n)`; `Cx(&n + &1)`] COMPLEX_MVT_LINE) THEN
  REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN
  REWRITE_TAC[REAL_ARITH `~(n + &1 <= x /\ x <= n)`] THEN ANTS_TAC THENL
   [X_GEN_TAC `w:complex` THEN STRIP_TAC THEN COMPLEX_DIFF_TAC THEN
    SUBGOAL_THEN `&0 < Re w` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `w = Cx(&0)` THEN ASM_SIMP_TAC[RE_CX; REAL_LT_REFL] THEN
    DISCH_TAC THEN UNDISCH_TAC `~(w = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    DISCH_THEN(X_CHOOSE_THEN `z:complex`
     (CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    SUBGOAL_THEN `&0 < &n /\ &0 < &n + &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_DIV; RE_CX; GSYM CX_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> a - b = x ==> a <= b`) THEN
    REWRITE_TAC[RE_MUL_CX; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `?u. z = Cx(u)` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[REAL; real]; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IM_CX; RE_CX]) THEN
    UNDISCH_THEN `T` (K ALL_TAC) THEN
    SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CX_LOG; GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV; RE_CX;
      real_div; GSYM REAL_MUL_LNEG; REAL_NEG_SUB; GSYM REAL_POW_INV] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[REAL_SUB_LE] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    MP_TAC REAL_EXP_1_LE_4 THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* An ad-hoc fact about complex n'th roots.                                  *)
(* ------------------------------------------------------------------------- *)

let EXISTS_COMPLEX_ROOT_NONTRIVIAL = prove
 (`!a n. 2 <= n ==> ?z. z pow n = a /\ ~(z = Cx(&1))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP(ARITH_RULE `2 <= n ==> ~(n = 0)`)) THEN
  ASM_CASES_TAC  `a = Cx(&0)` THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_POW_ZERO] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `a = Cx(&1)` THENL
   [EXISTS_TAC `cexp(Cx(&2) * Cx pi * ii * Cx(&1 / &n))` THEN
    ASM_SIMP_TAC[COMPLEX_ROOT_UNITY_EQ_1; DIVIDES_ONE;
                 ARITH_RULE `2 <= n ==> ~(n = 1)`; COMPLEX_ROOT_UNITY];
    MATCH_MP_TAC(MESON[]
     `(!x. ~Q x ==> ~P x) /\ (?x. P x) ==> (?x. P x /\ Q x)`) THEN
    ASM_SIMP_TAC[COMPLEX_POW_ONE] THEN EXISTS_TAC `cexp(clog a / Cx(&n))` THEN
    ASM_SIMP_TAC[GSYM CEXP_N; COMPLEX_DIV_LMUL; CX_INJ; REAL_OF_NUM_EQ] THEN
    ASM_SIMP_TAC[CEXP_CLOG]]);;

(* ------------------------------------------------------------------------- *)
(* Definition of a Dirichlet character mod d.                                *)
(* ------------------------------------------------------------------------- *)

let dirichlet_character = new_definition
 `dirichlet_character d (c:num->complex) <=>
        (!n. c(n + d) = c(n)) /\
        (!n. c(n) = Cx(&0) <=> ~coprime(n,d)) /\
        (!m n. c(m * n) = c(m) * c(n))`;;

let DIRICHLET_CHARACTER_PERIODIC = prove
 (`!d c n. dirichlet_character d c ==> c(n + d) = c(n)`,
  SIMP_TAC[dirichlet_character]);;

let DIRICHLET_CHARACTER_EQ_0 = prove
 (`!d c n. dirichlet_character d c ==> (c(n) = Cx(&0) <=> ~coprime(n,d))`,
  SIMP_TAC[dirichlet_character]);;

let DIRICHLET_CHARACTER_MUL = prove
 (`!d c m n. dirichlet_character d c ==> c(m * n) = c(m) * c(n)`,
  SIMP_TAC[dirichlet_character]);;

let DIRICHLET_CHARACTER_EQ_1 = prove
 (`!d c. dirichlet_character d c ==> c(1) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_MUL) THEN
  DISCH_THEN(MP_TAC o repeat (SPEC `1`)) THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_FIELD `a = a * a <=> a = Cx(&0) \/ a = Cx(&1)`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_EQ_0] THEN
  MESON_TAC[COPRIME_1; COPRIME_SYM]);;

let DIRICHLET_CHARACTER_POW = prove
 (`!d c m n. dirichlet_character d c ==> c(m EXP n) = c(m) pow n`,
  REPLICATE_TAC 3 GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[EXP; complex_pow] THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  ASM_REWRITE_TAC[]);;

let DIRICHLET_CHARACTER_PERIODIC_GEN = prove
 (`!d c m n. dirichlet_character d c ==> c(m * d + n) = c(n)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  GEN_TAC THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(mk + d) + n:num = (mk + n) + d`] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC]);;

let DIRICHLET_CHARACTER_CONG = prove
 (`!d c m n.
        dirichlet_character d c /\ (m == n) (mod d) ==> c(m) = c(n)`,
  REWRITE_TAC[CONG_CASES] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_PERIODIC_GEN]);;

let DIRICHLET_CHARACTER_ROOT = prove
 (`!d c n. dirichlet_character d c /\ coprime(d,n)
           ==> c(n) pow phi(d) = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o GSYM o MATCH_MP DIRICHLET_CHARACTER_EQ_1) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_POW th)]) THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN
  EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FERMAT_LITTLE THEN ASM_MESON_TAC[COPRIME_SYM]);;

let DIRICHLET_CHARACTER_NORM = prove
 (`!d c n. dirichlet_character d c
           ==> norm(c n) = if coprime(d,n) then &1 else &0`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[COMPLEX_NORM_ZERO] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COPRIME_SYM]] THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  COPRIME_0; COPRIME_SYM];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`; `n:num`]
    DIRICHLET_CHARACTER_ROOT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
  REWRITE_TAC[COMPLEX_NORM_POW; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`norm((c:num->complex) n)`; `phi d`] REAL_POW_EQ_1_IMP) THEN
  ASM_REWRITE_TAC[REAL_ABS_NORM] THEN
  ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1]);;

(* ------------------------------------------------------------------------- *)
(* The principal character mod d.                                            *)
(* ------------------------------------------------------------------------- *)

let chi_0 = new_definition
 `chi_0 d n = if coprime(n,d) then Cx(&1) else Cx(&0)`;;

let DIRICHLET_CHARACTER_CHI_0 = prove
 (`dirichlet_character d (chi_0 d)`,
  REWRITE_TAC[dirichlet_character; chi_0] THEN
  REWRITE_TAC[NUMBER_RULE `coprime(n + d,d) <=> coprime(n,d)`;
          NUMBER_RULE `coprime(m * n,d) <=> coprime(m,d) /\ coprime(n,d)`] THEN
  CONV_TAC COMPLEX_RING);;

let DIRICHLET_CHARACTER_EQ_PRINCIPAL = prove
 (`!d c. dirichlet_character d c
         ==> (c = chi_0 d <=> !n. coprime(n,d) ==> c(n) = Cx(&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM; chi_0] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]);;

let DIRICHLET_CHARACTER_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?n. coprime(n,d) /\ ~(c n = Cx(&0)) /\ ~(c n = Cx(&1))`,
  MESON_TAC[DIRICHLET_CHARACTER_EQ_PRINCIPAL; DIRICHLET_CHARACTER_EQ_0]);;

let DIRICHLET_CHARACTER_0 = prove
 (`!c. dirichlet_character 0 c <=> c = chi_0 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM; COPRIME_0] THEN
  X_GEN_TAC `n:num` THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_EQ_0;
                COPRIME_0]);;

let DIRICHLET_CHARACTER_1 = prove
 (`!c. dirichlet_character 1 c <=> !n. c n = Cx(&1)`,
  GEN_TAC THEN REWRITE_TAC[dirichlet_character; COPRIME_1] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_REWRITE_TAC[ARITH; COMPLEX_RING
     `x = x * x <=> x = Cx(&0) \/ x = Cx(&1)`] THEN
    DISCH_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `0`)) THEN ASM_REWRITE_TAC[ARITH] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING]);;

let DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(d = 0) /\ ~(d = 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_0; TAUT `~(p /\ ~p)`] THEN
  ASM_CASES_TAC `d = 1` THEN
  ASM_REWRITE_TAC[DIRICHLET_CHARACTER_1; chi_0; FUN_EQ_THM; COPRIME_1] THEN
  CONV_TAC TAUT);;

let DIRICHLET_CHARACTER_ZEROSUM = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..d) c = Cx(&0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_CHARACTER_NONPRINCIPAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC(COMPLEX_RING
   `!x. x * c = c /\ ~(x = Cx(&1)) ==> c = Cx(&0)`) THEN
  EXISTS_TAC `(c:num->complex) m` THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC(MESON[]
   `!t. vsum t f = vsum s f /\ vsum t g = vsum s g /\ vsum t f = vsum t g
        ==> vsum s f = vsum s g`) THEN
  EXISTS_TAC `{n | coprime(n,d) /\ n < d}` THEN
  REPEAT(CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_NUMSEG; LT_IMP_LE; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `r:num` THENL
     [ASM_CASES_TAC `r = 0` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
      ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[COPRIME_0];
      ASM_CASES_TAC `coprime(r,d)` THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `r:num = d` THEN ASM_REWRITE_TAC[LT_REFL] THENL
         [ASM_MESON_TAC[COPRIME_REFL]; ASM_ARITH_TAC];
        REWRITE_TAC[COMPLEX_VEC_0] THEN
        ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]]];
    ALL_TAC]) THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[GSYM(MATCH_MP DIRICHLET_CHARACTER_MUL (CONJUNCT1 th))]) THEN
  SIMP_TAC[VSUM; PHI_FINITE_LEMMA] THEN
  MATCH_MP_TAC ITERATE_OVER_COPRIME THEN SIMP_TAC[MONOIDAL_VECTOR_ADD] THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG]);;

let DIRICHLET_CHARACTER_ZEROSUM_MUL = prove
 (`!d c n. dirichlet_character d c /\ ~(c = chi_0 d)
           ==> vsum(1..d*n) c = Cx(&0)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; VSUM_CLAUSES_NUMSEG] THEN
  REWRITE_TAC[ARITH; COMPLEX_VEC_0] THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
  ASM_SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`; COMPLEX_ADD_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIRICHLET_CHARACTER_ZEROSUM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN NUMBER_TAC);;

let DIRICHLET_CHARACTER_SUM_MOD = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> vsum(1..n) c = vsum(1..(n MOD d)) c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP
    DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= n + 1`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_ZEROSUM_MUL; COMPLEX_ADD_LID] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[VSUM_OFFSET] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP DIRICHLET_CHARACTER_ZEROSUM) THEN
  MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Finiteness of the set of characters (later we could get size =  phi(d)).  *)
(* ------------------------------------------------------------------------- *)

let FINITE_DIRICHLET_CHARACTERS = prove
 (`!d. FINITE {c | dirichlet_character d c}`,
  GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_SIMP_TAC[DIRICHLET_CHARACTER_0; SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[FINITE_RULES];
    ALL_TAC] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\c n. c(n MOD d))
                    {c | (!m. m IN {m | m < d}
                             ==> c(m) IN (Cx(&0) INSERT
                                          {z | z pow (phi d) = Cx(&1)})) /\
                         (!m. ~(m IN {m | m < d})
                              ==> c(m) = Cx(&0))}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_FUNSPACE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; FINITE_INSERT] THEN
    MATCH_MP_TAC FINITE_COMPLEX_ROOTS_UNITY THEN
    ASM_SIMP_TAC[PHI_LOWERBOUND_1_STRONG; LE_1];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `c:num->complex` THEN
  DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INSERT] THEN
  EXISTS_TAC `\n:num. if n < d then c(n) else Cx(&0)` THEN
  ASM_SIMP_TAC[DIVISION; FUN_EQ_THM] THEN CONJ_TAC THEN X_GEN_TAC `m:num` THENL
   [MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN EXISTS_TAC `d:num` THEN
    ASM_MESON_TAC[CONG_MOD; CONG_SYM];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_ROOT; COPRIME_SYM;
                  DIRICHLET_CHARACTER_EQ_0]]);;

(* ------------------------------------------------------------------------- *)
(* Very basic group structure.                                               *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_MUL_CNJ = prove
 (`!d c n. dirichlet_character d c /\ ~(c n = Cx(&0))
           ==> cnj(c n) * c n = Cx(&1) /\ c n * cnj(c n) = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(COMPLEX_FIELD
   `inv z = w /\ ~(z = Cx(&0)) ==> w * z = Cx(&1) /\ z * w = Cx(&1)`) THEN
  ASM_REWRITE_TAC[COMPLEX_INV_CNJ] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM COMPLEX_NORM_NZ]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LT_REFL; COMPLEX_POW_ONE] THEN
  REWRITE_TAC[COMPLEX_DIV_1]);;

let DIRICHLET_CHARACTER_CNJ = prove
 (`!d c. dirichlet_character d c ==> dirichlet_character d (\n. cnj(c n))`,
  SIMP_TAC[dirichlet_character; CNJ_MUL; CNJ_EQ_CX]);;

let DIRICHLET_CHARACTER_GROUPMUL = prove
 (`!d c1 c2. dirichlet_character d c1 /\ dirichlet_character d c2
             ==> dirichlet_character d (\n. c1(n) * c2(n))`,
  SIMP_TAC[dirichlet_character; COMPLEX_ENTIRE] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let DIRICHLET_CHARACTER_GROUPINV = prove
 (`!d c. dirichlet_character d c ==> (\n. cnj(c n) * c n) = chi_0 d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[chi_0; FUN_EQ_THM] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_MUL_CNJ; DIRICHLET_CHARACTER_EQ_0];
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; COMPLEX_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Orthogonality relations, a weak version of one first.                     *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_SUM_OVER_NUMBERS = prove
 (`!d c. dirichlet_character d c
         ==> vsum (1..d) c = if c = chi_0 d then Cx(&(phi d)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_ZEROSUM] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN POP_ASSUM(K ALL_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  REWRITE_TAC[chi_0] THEN
  SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG; GSYM COMPLEX_VEC_0] THEN
  SIMP_TAC[phi; VSUM_CONST; FINITE_RESTRICT; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `coprime(x,d)` THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK = prove
 (`!d n. vsum {c | dirichlet_character d c} (\x. x n) = Cx(&0) \/
         coprime(n,d) /\ !c. dirichlet_character d c ==> c(n) = Cx(&1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `coprime(n,d)` THENL
   [ALL_TAC;
    DISJ1_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_ELIM_THM; COMPLEX_VEC_0; DIRICHLET_CHARACTER_EQ_0]] THEN
  SUBGOAL_THEN
    `!c'. dirichlet_character d c'
          ==> vsum {c | dirichlet_character d c}
                   ((\c. c(n)) o (\c n. c'(n) * c(n))) =
              vsum {c | dirichlet_character d c} (\c. c(n))`
  MP_TAC THENL
   [ALL_TAC;
    SIMP_TAC[o_DEF; FINITE_DIRICHLET_CHARACTERS; VSUM_COMPLEX_LMUL] THEN
    REWRITE_TAC[COMPLEX_RING `a * x = x <=> a = Cx(&1) \/ x = Cx(&0)`] THEN
    ASM_MESON_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_INJECTION THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_GROUPMUL] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(\c n. cnj(c'(n:num)) * c n)`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `coprime(m,d)` THENL
   [ALL_TAC; ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0]] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  MATCH_MP_TAC(COMPLEX_RING
    `a * b = Cx(&1) ==> a * b * x = a * b * y ==> x = y`) THEN
  ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0; DIRICHLET_CHARACTER_MUL_CNJ]);;

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS = prove
 (`!d n. real(vsum {c | dirichlet_character d c} (\c. c n)) /\
         &0 <= Re(vsum {c | dirichlet_character d c} (\c. c n))`,
  MP_TAC DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_CX; RE_CX; REAL_LE_REFL] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_VSUM;
    SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; RE_VSUM] THEN
    MATCH_MP_TAC SUM_POS_LE] THEN
  ASM_SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM; REAL_CX; RE_CX] THEN
  REWRITE_TAC[REAL_POS]);;

(* ------------------------------------------------------------------------- *)
(* A somewhat gruesome lemma about extending a character from a subgroup.    *)
(* ------------------------------------------------------------------------- *)

let CHARACTER_EXTEND_FROM_SUBGROUP = prove
 (`!f h a d.
        h SUBSET {x | x < d /\ coprime(x,d)} /\
        (1 IN h) /\
        (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
        (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
        (!x. x IN h ==> ~(f x = Cx(&0))) /\
        (!x y. x IN h /\ y IN h
                 ==> f((x * y) MOD d) = f(x) * f(y)) /\
        a IN {x | x < d /\ coprime(x,d)} DIFF h
        ==> ?f' h'. (a INSERT h) SUBSET h' /\
                    h' SUBSET {x | x < d /\ coprime(x,d)} /\
                    (!x. x IN h ==> f'(x) = f(x)) /\
                    ~(f' a = Cx(&1)) /\
                    1 IN h' /\
                    (!x y. x IN h' /\ y IN h' ==> ((x * y) MOD d) IN h') /\
                    (!x. x IN h' ==> ?y. y IN h' /\ (x * y == 1) (mod d)) /\
                    (!x. x IN h' ==> ~(f' x = Cx(&0))) /\
                    (!x y. x IN h' /\ y IN h'
                           ==> f'((x * y) MOD d) = f'(x) * f'(y))`,
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF; SUBSET] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 < d` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
  SUBGOAL_THEN `?m x. 0 < m /\ x IN h /\ (a EXP m == x) (mod d)` MP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`phi d`; `1`] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[PHI_LOWERBOUND_1_STRONG; LE_1]; ALL_TAC] THEN
    MATCH_MP_TAC FERMAT_LITTLE THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x s. x IN h ==> ((x EXP s) MOD d) IN h` ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
    INDUCT_TAC THEN ASM_SIMP_TAC[EXP; MOD_LT] THEN
    SUBGOAL_THEN `((x * (x EXP s) MOD d) MOD d) IN h` MP_TAC THEN
    ASM_MESON_TAC[MOD_MULT_RMOD; ASSUME `1 <= d`; LE_1];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `am:num` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `0 < m ==> m = 1 \/ 2 <= m`))
  THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN UNDISCH_TAC `(a EXP 1 == am) (mod d)` THEN
    ASM_SIMP_TAC[EXP_1; GSYM CONG_MOD_LT; MOD_LT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GEN `r:num` o SPEC `r MOD m`) THEN
  ASM_SIMP_TAC[DIVISION; LE_1; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b /\ c) <=> b /\ c ==> ~a`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!r x. x IN h /\ (a EXP r == x) (mod d) ==> m divides r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[DIVIDES_MOD; LE_1] THEN
    REWRITE_TAC[ARITH_RULE `n = 0 <=> ~(0 < n)`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `(a EXP (r MOD m)) MOD d` THEN
    ASM_SIMP_TAC[CONG_RMOD; LE_1; CONG_REFL] THEN
    UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
    DISCH_THEN(MP_TAC o SPEC `(a EXP (m * r DIV m)) MOD d`) THEN ANTS_TAC THENL
     [REWRITE_TAC[GSYM EXP_EXP] THEN
      SUBGOAL_THEN
       `(a EXP m) EXP (r DIV m) MOD d = (am EXP (r DIV m)) MOD d`
       (fun th -> ASM_SIMP_TAC[th]) THEN
      ASM_SIMP_TAC[GSYM CONG; LE_1] THEN
      ASM_SIMP_TAC[CONG_LMOD; CONG_EXP; LE_1];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(a EXP r == x) (mod d)` THEN
    MP_TAC(SPECL [`r:num`; `m:num`] DIVISION) THEN ASM_SIMP_TAC[LE_1] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[EXP_ADD] THEN
    DISCH_THEN(MP_TAC o SPEC `y:num` o MATCH_MP
    (NUMBER_RULE `!a. (x:num == y) (mod n) ==> (a * x == a * y) (mod n)`)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
     `(y * e * a == z) (mod n)
      ==> (e * y == 1) (mod n) ==> (a == z) (mod n)`)) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `a EXP (m * r DIV m) MOD d * y` THEN
      ASM_SIMP_TAC[CONG_MULT; CONG_REFL; CONG_RMOD; LE_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONG; LE_1];
    ALL_TAC] THEN
  MP_TAC(SPECL [`(f:num->complex) am`; `m:num`]
               EXISTS_COMPLEX_ROOT_NONTRIVIAL) THEN ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?g. !x k. x IN h ==> g((x * a EXP k) MOD d) = f(x) * z pow k`
  MP_TAC THENL
   [REWRITE_TAC[MESON[] `(?g. !x a. p x ==> g(f a x) = h a x) <=>
                         (?g. !y x a. p x /\ f a x = y ==> g y = h a x)`] THEN
    REWRITE_TAC[GSYM SKOLEM_THM] THEN
    REWRITE_TAC[MESON[]
     `(!y. ?z. !x k. p x /\ f x k = y ==> z = g x k) <=>
      (!x k x' k'. p x /\ p x' /\ f x k = f x' k' ==> g x k = g x' k')`] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(!x k y j. P x k y j) <=> (!k j x y. P x k y j)`] THEN
    MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:num`; `j:num`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:num`; `y:num`] THEN
    ASM_SIMP_TAC[GSYM CONG; LE_1] THEN STRIP_TAC THEN
    UNDISCH_TAC `k:num <= j` THEN REWRITE_TAC[LE_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC) THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN
    REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `m divides i` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
      DISCH_THEN(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(z * x) MOD d` THEN ASM_SIMP_TAC[CONG_RMOD; LE_1] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `y * a EXP k` THEN
      REWRITE_TAC[COPRIME_LMUL] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(x * a EXP k == y * a EXP (k + i)) (mod d)` THEN
      REWRITE_TAC[EXP_ADD] THEN UNDISCH_TAC `(y * z == 1) (mod d)` THEN
      CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:num` SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f((y * (am EXP r) MOD d) MOD d):complex` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[CONG_MOD_LT] THEN
      MATCH_MP_TAC CONG_TRANS THEN
      EXISTS_TAC `y * (a EXP m) EXP r` THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONG_MULT THEN
        ASM_SIMP_TAC[CONG_MULT; CONG_LMOD; CONG_REFL; LE_1] THEN
        MATCH_MP_TAC CONG_EXP THEN ASM_MESON_TAC[CONG_SYM];
        ALL_TAC] THEN
      MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `a EXP k` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM]; ALL_TAC] THEN
      UNDISCH_TAC `(x * a EXP k == y * a EXP (k + m * r)) (mod d)` THEN
      REWRITE_TAC[EXP_ADD; EXP_EXP] THEN CONV_TAC NUMBER_RULE;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    SPEC_TAC(`r:num`,`s:num`) THEN INDUCT_TAC THEN
    ASM_SIMP_TAC[EXP; MOD_LT; complex_pow; COMPLEX_MUL_RID] THENL
     [UNDISCH_TAC
       `!x y. x IN h /\ y IN h ==> f ((x * y) MOD d):complex = f x * f y` THEN
      DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
      ASM_SIMP_TAC[MULT_CLAUSES; MOD_LT] THEN
      UNDISCH_TAC `!x:num. x IN h ==> ~(f x = Cx (&0))` THEN
      DISCH_THEN(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f((am * (am EXP s) MOD d) MOD d):complex` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_SIMP_TAC[]] THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_RMOD; ASSUME `1 <= d`; LE_1];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:num->complex` THEN
  DISCH_THEN (LABEL_TAC "*") THEN
  EXISTS_TAC `{(x * a EXP k) MOD d | x IN h /\ k IN (:num)}` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; IN_UNIV] THEN
    X_GEN_TAC `x:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MAP_EVERY EXISTS_TAC [`1`; `1`];
      MAP_EVERY EXISTS_TAC [`x:num`; `0`]] THEN
    ASM_SIMP_TAC[EXP_1; MULT_CLAUSES; EXP; MOD_LT];
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:num`; `x:num`; `k:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[DIVISION; LE_1; COPRIME_MOD; COPRIME_LMUL] THEN
    ASM_MESON_TAC[COPRIME_EXP; COPRIME_SYM];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPECL [`x:num`; `0`]) THEN
    ASM_SIMP_TAC[MOD_LT; EXP; MULT_CLAUSES; complex_pow; COMPLEX_MUL_RID];
    REMOVE_THEN "*" (MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_SIMP_TAC[EXP_1; MULT_CLAUSES; MOD_LT; COMPLEX_POW_1] THEN
    UNDISCH_TAC `!x y. x IN h /\ y IN h ==> f ((x * y) MOD d) = f x * f y` THEN
    DISCH_THEN(MP_TAC o SPECL [`1`; `1`]) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; MOD_LT] THEN
    UNDISCH_TAC `~(z = Cx(&1))` THEN CONV_TAC COMPLEX_RING;
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    MAP_EVERY EXISTS_TAC [`1`; `0`] THEN
    ASM_SIMP_TAC[EXP; MULT_CLAUSES; MOD_LT];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`r:num`; `s:num`; `x:num`; `k:num`; `y:num`; `j:num`] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`(x * y) MOD d`; `j + k:num`] THEN
    ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD; LE_1] THEN
    REWRITE_TAC[EXP_ADD; MULT_AC];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:num`; `x:num`; `k:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `!x. x IN h ==> (?y. y IN h /\ (x * y == 1) (mod d))` THEN
    DISCH_THEN(MP_TAC o SPEC `x:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(z * a EXP ((phi d - 1) * k)) MOD d` THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `(x * a EXP k) * (z * a EXP ((phi d - 1) * k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONG_MULT THEN ASM_SIMP_TAC[CONG_MOD; LE_1]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE
     `(x * a) * (z * ak):num = (x * z) * (a * ak)`] THEN
    GEN_REWRITE_TAC (LAND_CONV) [ARITH_RULE `1 = 1 * 1`] THEN
    MATCH_MP_TAC CONG_MULT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM EXP_ADD] THEN
    SUBGOAL_THEN `k + (phi d - 1) * k = phi(d) * k` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `k + a * k = (a + 1) * k`] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[SUB_ADD; PHI_LOWERBOUND_1_STRONG];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM EXP_EXP] THEN SUBST1_TAC(SYM(SPEC `k:num` EXP_ONE)) THEN
    MATCH_MP_TAC CONG_EXP THEN ASM_SIMP_TAC[FERMAT_LITTLE];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_SIMP_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0] THEN
    UNDISCH_TAC `!x:num. x IN h ==> ~(f x = Cx (&0))` THEN
    DISCH_THEN(MP_TAC o SPEC `am:num`) THEN ASM_REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `z pow m = f(am:num)`)) THEN
    REWRITE_TAC[COMPLEX_POW_EQ_0] THEN ASM_SIMP_TAC[LE_1];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`r:num`; `s:num`; `x:num`; `k:num`; `y:num`; `j:num`] THEN
    STRIP_TAC THEN REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `g(((x * y) MOD d * a EXP (k + j)) MOD d):complex` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_LMOD; MOD_MULT_RMOD; LE_1] THEN
      REWRITE_TAC[EXP_ADD; MULT_AC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the key result that we can find a distinguishing character.         *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_DISCRIMINATOR = prove
 (`!d n. 1 < d /\ ~((n == 1) (mod d))
          ==> ?c. dirichlet_character d c /\ ~(c n = Cx(&1))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP LT_IMP_LE) THEN
  ASM_CASES_TAC `coprime(n,d)` THENL
   [ALL_TAC;
    EXISTS_TAC `chi_0 d` THEN
    ASM_REWRITE_TAC[DIRICHLET_CHARACTER_CHI_0; chi_0] THEN
    CONV_TAC COMPLEX_RING] THEN
  MP_TAC(ISPECL [`\n:num. Cx(&1)`; `{1}`; `n MOD d`; `d:num`]
                CHARACTER_EXTEND_FROM_SUBGROUP) THEN
  ASM_SIMP_TAC[IN_SING; IN_ELIM_THM; IN_DIFF] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SUBSET; MULT_CLAUSES; MOD_LT; LE_1; IN_SING;
                 IN_ELIM_THM; DIVISION; COPRIME_MOD; CONG_MOD_LT;
                 COMPLEX_MUL_LID; CX_INJ; REAL_OF_NUM_EQ; ARITH] THEN
    ASM_MESON_TAC[COPRIME_1; COPRIME_SYM; CONG_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f0:num->complex`; `h0:num->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!m. m <= CARD {x | x < d /\ coprime(x,d)}
        ==> ?f h. h SUBSET {x | x < d /\ coprime(x,d)} /\
                 (1 IN h) /\ (n MOD d) IN h /\
                 (!x y. x IN h /\ y IN h ==> ((x * y) MOD d) IN h) /\
                 (!x. x IN h ==> ?y. y IN h /\ (x * y == 1) (mod d)) /\
                 ~(f(n MOD d) = Cx(&1)) /\
                 (!x. x IN h ==> ~(f x = Cx(&0))) /\
                 (!x y. x IN h /\ y IN h
                          ==> f((x * y) MOD d) = f(x) * f(y)) /\
                 m <= CARD h`
  MP_TAC THENL
   [MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
    DISCH_THEN(LABEL_TAC "*") THEN DISCH_TAC THEN
    ASM_CASES_TAC `m = 0` THENL
     [MAP_EVERY EXISTS_TAC [`f0:num->complex`; `h0:num->bool`] THEN
      ASM_REWRITE_TAC[LE_0] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o C MATCH_MP
     (MATCH_MP (ARITH_RULE `~(m = 0) ==> m - 1 < m`) (ASSUME `~(m = 0)`))) THEN
    ASM_SIMP_TAC[ARITH_RULE `x <= n ==> x - 1 <= n`; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:num->complex`; `h:num->bool`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m <= CARD(h:num->bool)` THENL
     [MAP_EVERY EXISTS_TAC [`f:num->complex`; `h:num->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ASSUME `h SUBSET {x | x < d /\ coprime (x,d)}`) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> ~(s = t) ==> ?a. a IN t /\ ~(a IN s)`)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`f:num->complex`; `h:num->bool`; `a:num`; `d:num`]
                CHARACTER_EXTEND_FROM_SUBGROUP) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ff:num->complex` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `hh:num->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD((a:num) INSERT h)` THEN
    SUBGOAL_THEN `FINITE(h:num->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | x IN {x | x < d} /\ coprime(x,d)}` THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[CARD_CLAUSES] THEN
      UNDISCH_TAC `m - 1 <= CARD(h:num->bool)` THEN ARITH_TAC;
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | x IN {x | x < d} /\ coprime(x,d)}` THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `CARD {x | x < d /\ coprime(x,d)}`) THEN
  REWRITE_TAC[LE_REFL] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:num->complex`; `h:num->bool`] THEN
  ASM_CASES_TAC `h = {x | x < d /\ coprime (x,d)}` THENL
   [ALL_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
    REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC CARD_PSUBSET THEN
    ASM_REWRITE_TAC[PSUBSET] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < d}` THEN
    SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG_LT] THEN SET_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `\n. if coprime(n,d) then f(n MOD d) else Cx(&0)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[dirichlet_character] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:num` THENL
   [REWRITE_TAC[NUMBER_RULE `coprime(x + d:num,d) <=> coprime(x,d)`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[GSYM CONG; LE_1] THEN CONV_TAC NUMBER_RULE;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC[COPRIME_MOD; DIVISION; LE_1];
    X_GEN_TAC `y:num` THEN REWRITE_TAC[COPRIME_LMUL] THEN
    MAP_EVERY ASM_CASES_TAC [`coprime(x,d)`; `coprime(y,d)`] THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `f(((x MOD d) * (y MOD d)) MOD d):complex` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN ASM_SIMP_TAC[MOD_MULT_MOD2; LE_1];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[DIVISION; COPRIME_MOD; LE_1]]]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get the full second orthogonality relation.                      *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT = prove
 (`!d n. vsum {c | dirichlet_character d c} (\c. c n) =
                if (n == 1) (mod d)
                then Cx(&(CARD {c | dirichlet_character d c}))
                else Cx(&0)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_REWRITE_TAC[CONG_MOD_0; DIRICHLET_CHARACTER_0; SET_RULE
     `{x | x = a} = {a}`] THEN
    SIMP_TAC[VSUM_CLAUSES; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    REWRITE_TAC[chi_0; COPRIME_0; VECTOR_ADD_RID] THEN REWRITE_TAC[ARITH];
    ALL_TAC] THEN
  ASM_CASES_TAC `d = 1` THENL
   [ASM_REWRITE_TAC[CONG_MOD_1; DIRICHLET_CHARACTER_1] THEN
    REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX] THEN
    ASM_REWRITE_TAC[SET_RULE `{x | x = a} = {a}`] THEN
    SIMP_TAC[VSUM_CLAUSES; CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_ADD_RID; ARITH];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `vsum {c | dirichlet_character d c} (\c. Cx(&1))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; DIRICHLET_CHARACTER_CONG];
      SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; VSUM_CONST] THEN
      REWRITE_TAC[COMPLEX_CMUL; COMPLEX_MUL_RID]];
    MP_TAC(SPECL [`d:num`; `n:num`]
      DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_WEAK) THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_DISCRIMINATOR;
                  ARITH_RULE `~(d = 0) /\ ~(d = 1) ==> 1 < d`]]);;

let DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS = prove
 (`!d n. 1 <= d
         ==> vsum {c | dirichlet_character d c} (\c. c(n)) =
                if (n == 1) (mod d) then Cx(&(phi d)) else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\c n. (c:num->complex) n`; `{c | dirichlet_character d c}`;
                 `1..d`;] VSUM_SWAP) THEN
  SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_INEXPLICIT;
           DIRICHLET_CHARACTER_SUM_OVER_NUMBERS; FINITE_NUMSEG;
           FINITE_DIRICHLET_CHARACTERS; ETA_AX] THEN
  REWRITE_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0] THEN
  REWRITE_TAC[IN_ELIM_THM; DIRICHLET_CHARACTER_CHI_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[GSYM VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `{j | j IN 1..d /\ (j == 1) (mod d)} = {1}`
   (fun th -> SIMP_TAC[th; VSUM_SING]) THEN
  REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `k:num` THEN EQ_TAC THEN ASM_SIMP_TAC[LE_REFL; CONG_REFL] THEN
  ASM_CASES_TAC `d = 1` THEN ASM_SIMP_TAC[CONG_MOD_1; LE_ANTISYM] THEN
  ASM_CASES_TAC `k:num = d` THENL
   [ASM_REWRITE_TAC[NUMBER_RULE `(d == 1) (mod d) <=> d divides 1`] THEN
    ASM_REWRITE_TAC[DIVIDES_ONE];
    STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[LT_LE]]);;

(* ------------------------------------------------------------------------- *)
(* L-series, just at the point s = 1.                                        *)
(* ------------------------------------------------------------------------- *)

let Lfunction_DEF = new_definition
 `Lfunction c = infsum (from 1) (\n. c(n) / Cx(&n))`;;

let BOUNDED_LFUNCTION_PARTIAL_SUMS = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded {vsum (1..n) c | n IN (:num)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(fun th ->
    ONCE_REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_SUM_MOD th]) THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `IMAGE (\n. vsum(1..n) c:complex) (0..d)` THEN
  SIMP_TAC[FINITE_IMP_BOUNDED; FINITE_IMAGE; FINITE_NUMSEG] THEN
  REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV; IN_IMAGE] THEN
  EXISTS_TAC `n MOD d` THEN REWRITE_TAC[IN_NUMSEG; LE_0] THEN
  ASM_MESON_TAC[LT_IMP_LE; DIVISION;
                DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL]);;

let LFUNCTION = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ((\n. c(n) / Cx(&n)) sums (Lfunction c)) (from 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SIMP_TAC[Lfunction_DEF; SUMS_INFSUM] THEN
  REWRITE_TAC[complex_div] THEN MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX THEN
  REPEAT(EXISTS_TAC `1`) THEN FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  REWRITE_TAC[LIM_INV_N; GSYM CX_INV; REAL_CX; RE_CX] THEN
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Other properties of conjugate characters.                                 *)
(* ------------------------------------------------------------------------- *)

let CNJ_CHI_0 = prove
 (`!d n. cnj(chi_0 d n) = chi_0 d n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[chi_0] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[CNJ_CX]);;

let LFUNCTION_CNJ = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> Lfunction (\n. cnj(c n)) = cnj(Lfunction c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[Lfunction_DEF] THEN
  MATCH_MP_TAC INFSUM_UNIQUE THEN
  ONCE_REWRITE_TAC[GSYM CNJ_CX] THEN
  REWRITE_TAC[GSYM CNJ_DIV] THEN
  REWRITE_TAC[SUMS_CNJ; CNJ_CX; GSYM Lfunction_DEF] THEN
  ASM_MESON_TAC[LFUNCTION]);;

(* ------------------------------------------------------------------------- *)
(* Explicit bound on truncating the Lseries.                                 *)
(* ------------------------------------------------------------------------- *)

let LFUNCTION_PARTIAL_SUM = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. 1 <= n
                     ==> norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                          <= B / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:num->complex`; `\n. inv(Cx(&n))`; `1`; `1`]
                SERIES_DIRICHLET_COMPLEX_EXPLICIT) THEN
  REWRITE_TAC[LE_REFL] THEN FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  REWRITE_TAC[LIM_INV_N; GSYM CX_INV; REAL_CX; RE_CX] THEN
  SIMP_TAC[REAL_LE_INV2; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1; LE_ADD] THEN
  REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_INV; REAL_ABS_NUM] THEN
  REWRITE_TAC[CX_INV; GSYM complex_div; GSYM real_div] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\n. vsum(k+1..n) (\n. c(n) / Cx(&n))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP LFUNCTION) THEN
    MP_TAC(ISPECL [`sequentially`; `vsum (1..k) (\n. c n / Cx (&n))`]
                LIM_CONST) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT; sums; FROM_INTER_NUMSEG] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `k + 1` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `k + 1 <= m ==> k <= m`)) THEN
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    ASM_SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= k ==> 1 <= k + 1`] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= k + 1`; REAL_OF_NUM_ADD]]);;

let LFUNCTION_PARTIAL_SUM_STRONG = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ?B. &0 < B /\
                 !n. norm(Lfunction c - vsum(1..n) (\n. c(n) / Cx(&n)))
                         <= B / (&n + &1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LFUNCTION_PARTIAL_SUM) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `max B (norm(Lfunction c))` THEN
  ASM_SIMP_TAC[REAL_LT_MAX] THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[VSUM_CLAUSES_NUMSEG; VECTOR_SUB_RZERO; ARITH] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_SIMP_TAC[LE_1] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* First key bound, when the Lfunction is not zero (as indeed it isn't).     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) -
                vsum(1..x) (\n. c(n) * Cx(log(&n) / &n)) | x IN (:num)}`,
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN
  SIMP_TAC[LOG_MANGOLDT_SUM; real_div; CX_MUL;  GSYM VSUM_CX; FINITE_DIVISORS;
           LE_1; GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; COMPLEX_INV_MUL; CX_MUL; CX_INV] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(ck * cn) * cm * k * n:complex = (ck * k) * (cn * cm * n)`] THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_PARTIAL_SUM_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&18 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `x:num` THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL] THEN
  REWRITE_TAC[COMPLEX_NORM_INV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM real_div] THEN REWRITE_TAC[REAL_MUL_ASSOC] THEN
  REWRITE_TAC[real_abs; MANGOLDT_POS_LE] THEN ASM_CASES_TAC `x = 0` THEN
  ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH; REAL_LE_MUL; REAL_LT_IMP_LE;
               REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..x) (\n. B / &x * mangoldt n)` THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `B / &x * &18 * &x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[REWRITE_RULE[ETA_AX] PSI_BOUND];
      ASM_SIMP_TAC[REAL_FIELD `~(x = &0) ==> B / x * &18 * x = &18 * B`;
                   REAL_OF_NUM_EQ; REAL_LE_REFL]]] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_MUL_RID; REAL_LE_MUL;
               REAL_LE_DIV; REAL_POS; REAL_LT_IMP_LE; MANGOLDT_POS_LE] THEN
  REWRITE_TAC[real_div; REAL_ARITH `a * b * c <= d <=> (a * c) * b <= d`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[MANGOLDT_POS_LE] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B / (&(x DIV n) + &1)` THEN
  ASM_REWRITE_TAC[GSYM complex_div] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
  ONCE_REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  SUBGOAL_THEN `1 <= x` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC);;

let SUMMABLE_CHARACTER_LOG_OVER_N = prove
 (`!c d. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> summable (from 1) (\n. c(n) * Cx(log(&n) / &n))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX THEN
  MAP_EVERY EXISTS_TAC [`4`; `1`] THEN REWRITE_TAC[REAL_CX] THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP BOUNDED_LFUNCTION_PARTIAL_SUMS th]) THEN
  CONJ_TAC THENL
   [SIMP_TAC[DECREASING_LOG_OVER_N; GSYM REAL_OF_NUM_ADD; RE_CX];
    MP_TAC LIM_LOG_OVER_N THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[CX_LOG; CX_DIV; LE_1; REAL_OF_NUM_LT]]);;

let BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> bounded
              { Lfunction(c) *
                vsum(1..x) (\n. c(n) * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o
    MATCH_MP BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT_LEMMA) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_CHARACTER_LOG_OVER_N) THEN
  DISCH_THEN(MP_TAC o MATCH_MP SUMMABLE_IMP_SUMS_BOUNDED) THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_SUMS) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] BOUNDED_SUBSET) THEN
  REWRITE_TAC[SIMPLE_IMAGE; SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_UNIV; IN_ELIM_THM; RIGHT_EXISTS_AND_THM; EXISTS_IN_IMAGE;
              GSYM CONJ_ASSOC] THEN
  X_GEN_TAC `n:num` THEN REPEAT(EXISTS_TAC `n:num`) THEN VECTOR_ARITH_TAC);;

let BOUNDED_DIRICHLET_MANGOLDT_NONZERO = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ ~(Lfunction c = Cx(&0))
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_LFUNCTION_DIRICHLET_MANGOLDT) THEN
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; COMPLEX_NORM_NZ] THEN
  ASM_MESON_TAC[COMPLEX_NORM_NZ; REAL_LT_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Now a bound when the Lfunction is zero (hypothetically).                  *)
(* ------------------------------------------------------------------------- *)

let MANGOLDT_LOG_SUM = prove
 (`!n. 1 <= n
       ==> mangoldt(n) = --(sum {d | d divides n} (\d. mobius(d) * log(&d)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. mangoldt n`; `\n. log(&n)`] MOBIUS_INVERSION) THEN
  ASM_SIMP_TAC[LOG_MANGOLDT_SUM; LE_1] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {d | d divides n} (\x. mobius x * (log(&n) - log(&x)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `d:num` THEN
    REWRITE_TAC[IN_ELIM_THM; DIVIDES_DIV_MULT] THEN
    ABBREV_TAC `q = n DIV d` THEN
    MAP_EVERY ASM_CASES_TAC [`q = 0`; `d = 0`] THEN
    ASM_SIMP_TAC[MULT_CLAUSES; LE_1] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM REAL_OF_NUM_MUL; LOG_MUL; REAL_OF_NUM_LT; LE_1] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_SUB_LDISTRIB; SUM_SUB; FINITE_DIVISORS; LE_1] THEN
    ASM_SIMP_TAC[SUM_RMUL; REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS] THEN
    MATCH_MP_TAC(REAL_ARITH `a = &0 ==> a - b = --b`) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LOG_1] THEN REAL_ARITH_TAC]);;

let BOUNDED_DIRICHLET_MANGOLDT_LEMMA = prove
 (`!d c x.
        dirichlet_character d c /\ ~(c = chi_0 d) /\ 1 <= x
        ==> Cx(log(&x)) + vsum (1..x) (\n. c(n) * Cx(mangoldt n / &n)) =
            vsum (1..x) (\n. c(n) / Cx(&n) *
                             vsum {d | d divides n}
                                  (\d. Cx(mobius(d) * log(&x / &d))))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MANGOLDT_LOG_SUM] THEN
  MATCH_MP_TAC(COMPLEX_RING `c - b = a ==> (a:complex) + b = c`) THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  SIMP_TAC[CX_NEG; CX_DIV; GSYM VSUM_CX; FINITE_NUMSEG; FINITE_DIVISORS;
           LE_1] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH
   `c / d * x - c * --y / d:complex = c / d * (x + y)`] THEN
  SIMP_TAC[GSYM VSUM_ADD; FINITE_DIVISORS; LE_1] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `vsum (1..x)
         (\n. c n / Cx(&n) * vsum {d | d divides n}
               (\d. Cx(mobius d * log(&x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `m:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[CX_MUL; GSYM COMPLEX_ADD_LDISTRIB] THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM CX_ADD; CX_INJ] THEN
    ASM_CASES_TAC `m = 0` THENL
     [ASM_MESON_TAC[DIVIDES_ZERO; LE_1]; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV; REAL_OF_NUM_LT; LE_1] THEN REAL_ARITH_TAC;
    SIMP_TAC[FINITE_DIVISORS; CX_MUL; SUM_RMUL; LE_1; VSUM_CX] THEN
    SIMP_TAC[REWRITE_RULE[ETA_AX] DIVISORSUM_MOBIUS] THEN
    SIMP_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO] THEN
    ASM_SIMP_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0; IN_NUMSEG; LE_REFL] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_EQ_1) THEN
    ASM_SIMP_TAC[COMPLEX_MUL_LID; COMPLEX_DIV_1]]);;

let SUM_LOG_OVER_X_BOUND = prove
 (`!x. abs(sum(1..x) (\n. log(&x / &n) / &x)) <= &4`,
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG; ARITH_EQ; REAL_ABS_NUM; REAL_POS];
    ALL_TAC] THEN
  SIMP_TAC[real_div; SUM_RMUL; REAL_ABS_MUL; REAL_ABS_INV; REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (1..x) (\n. abs(log(&x / &n)))` THEN
  REWRITE_TAC[SUM_ABS_NUMSEG] THEN
  ASM_SIMP_TAC[real_abs; LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               LE_1; REAL_MUL_LID; REAL_OF_NUM_LE; LOG_DIV] THEN
  REWRITE_TAC[SUM_SUB_NUMSEG; GSYM LOG_FACT] THEN
  REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LOG_FACT_BOUNDS) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&2 * l + abs(x) + &1 <= b
    ==> abs(lf - (xl - x + &1)) <= &2 * l
        ==> xl - lf <= b`) THEN
 MATCH_MP_TAC(REAL_ARITH
   `&1 <= x /\ l <= x ==> &2 * l + abs(x) + &1 <= &4 * x`) THEN
  ASM_SIMP_TAC[REAL_OF_NUM_LE; LE_1; LOG_LE_REFL]);;

let BOUNDED_DIRICHLET_MANGOLDT_ZERO = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d) /\ Lfunction c = Cx(&0)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) +
                    Cx(log(&x)) | x IN (:num)}`,
  ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_PARTIAL_SUM_STRONG) THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SIMP_TAC[SET_RULE `{f x | x IN (:num)} = f 0 INSERT {f x | ~(x = 0)}`] THEN
  REWRITE_TAC[BOUNDED_INSERT; ARITH_RULE `~(n = 0) <=> 1 <= n`] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    BOUNDED_DIRICHLET_MANGOLDT_LEMMA) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_DIVISORS; LE_1] THEN
  REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL; complex_div; COMPLEX_INV_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `((ck * cn) * k' * n') * m * l = (cn * m * n') * l * (ck * k')`] THEN
  REWRITE_TAC[GSYM complex_div] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  EXISTS_TAC `&4 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `x:num` THEN DISCH_TAC THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(1..x) (\n. inv(&n) * log(&x / &n) * B / (&(x DIV n) + &1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN CONJ_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
      FIRST_ASSUM(fun t -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM t]) THEN
      COND_CASES_TAC THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_LE_INV_EQ; REAL_POS] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_ABS_NUM] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
      ASM_SIMP_TAC[REAL_FIELD `&1 <= n ==> inv(n) * n = &1`; REAL_OF_NUM_LE;
                   REAL_ABS_MOBIUS];
      SIMP_TAC[CX_LOG; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
      SIMP_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_ARITH `abs x <= x <=> &0 <= x`] THEN
      ASM_SIMP_TAC[LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1;
                   REAL_MUL_LID; REAL_OF_NUM_LE]];
    ALL_TAC] THEN
  SIMP_TAC[real_div; REAL_RING `a * l * B * i:real = ((l * i) * a) * B`] THEN
  REWRITE_TAC[SUM_RMUL] THEN ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(1..x) (\n. log(&x / &n) / &x)` THEN
  ASM_SIMP_TAC[REAL_ARITH `abs x <= a ==> x <= a`; SUM_LOG_OVER_X_BOUND] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[GSYM real_div; LOG_POS; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT;
               LE_1; REAL_MUL_LID; REAL_OF_NUM_LE] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_INV_INV] THEN
  REWRITE_TAC[GSYM REAL_INV_MUL] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LT_DIV; REAL_OF_NUM_LT; LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Now the analogous result for the principal character.                     *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA = prove
 (`!d. 1 <= d
       ==> norm(vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n)))
            <= sum {p | prime p /\ p divides d} (\p. log(&p))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum {p | prime p /\ p divides d}
                  (\p. sum {k | 1 <= k /\ p EXP k <= x}
                           (\k. log(&p) / &p pow k))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_1] THEN
    X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `2 <= p /\ 1 <= p /\ 1 < p` ASSUME_TAC THENL
     [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 < p /\ 1 <= p`];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..x) (\k. log(&p) / &p pow k)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[IN_DIFF; IN_NUMSEG; IN_ELIM_THM; SUBSET; REAL_POW_LE;
                   REAL_POS; REAL_LE_DIV; LOG_POS; REAL_OF_NUM_LE;
                   PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
      ASM_SIMP_TAC[LT_POW2_REFL; LT_IMP_LE; EXP_MONO_LE];
      REWRITE_TAC[real_div; SUM_LMUL] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; LOG_POS_LT; REAL_OF_NUM_LT] THEN
      SIMP_TAC[GSYM REAL_POW_INV; SUM_GP; REAL_INV_EQ_1; REAL_OF_NUM_EQ] THEN
      COND_CASES_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT; REAL_LT_LDIV_EQ;
                   REAL_MUL_LID; REAL_OF_NUM_LT; LE_1] THEN
      REWRITE_TAC[real_pow] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x * y /\ &2 * x <= &1
                                ==> x pow 1 - x * y <= &1 - x`) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS; REAL_LE_MUL] THEN
      REWRITE_TAC[real_div; REAL_MUL_LID] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID; REAL_OF_NUM_LT;
                   REAL_OF_NUM_LE; LE_1]]] THEN
   W(MP_TAC o PART_MATCH (lhs o rand) SUM_SUM_PRODUCT o rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_SPECIAL_DIVISORS; LE_1] THEN
      X_GEN_TAC `p:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `1..x` THEN
      SIMP_TAC[SUBSET; FINITE_NUMSEG; IN_NUMSEG; IN_ELIM_THM] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP k` THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP k` THEN
      ASM_SIMP_TAC[LT_POW2_REFL; LT_IMP_LE; EXP_MONO_LE; PRIME_GE_2];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
    REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[chi_0; COND_RAND; COND_RATOR] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_SUB_LZERO] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NORM_NEG; REAL_ABS_NUM] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THEN
    REWRITE_TAC[mangoldt; COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_ABS_NUM] THEN
    REWRITE_TAC[TAUT `(if a then &0 else if b then x else &0) =
                      (if ~a /\ b then x else &0)`] THEN
    SIMP_TAC[GSYM real_div; GSYM SUM_RESTRICT_SET; FINITE_NUMSEG] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_EQ_GENERAL THEN EXISTS_TAC `\(p,k). p EXP k` THEN
    REWRITE_TAC[EXISTS_UNIQUE; EXISTS_PAIR_THM; FORALL_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_NUMSEG; PAIR_EQ] THEN CONJ_TAC THENL
     [X_GEN_TAC `y:num` THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(coprime(p EXP k,d))` THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW; LE_1] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`q:num`; `j:num`] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC[EQ_PRIME_EXP] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`]  THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[COPRIME_SYM] COPRIME_PRIMEPOW; LE_1] THEN
    REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[EXP_EQ_0; LE_1; PRIME_0]; ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_POW; REAL_ABS_DIV; REAL_ABS_POW;
                REAL_ABS_NUM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y /\ x = y ==> abs x = y`) THEN
    ASM_SIMP_TAC[LOG_POS; REAL_OF_NUM_LE; PRIME_IMP_NZ; LE_1] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `q:num` THEN REWRITE_TAC[] THEN EQ_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `k = SUC(k - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[EXP; DIVIDES_RMUL; DIVIDES_REFL]]]);;

let BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL = prove
 (`!d. 1 <= d
       ==> bounded { vsum(1..x) (\n. chi_0 d n * Cx(mangoldt n / &n)) -
                     Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[bounded; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  EXISTS_TAC
   `abs(sum {p | prime p /\ p divides d} (\p. log(&p))) +
    abs(log(&0)) + &21` THEN
  X_GEN_TAC `x:num` THEN ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[VSUM_CLAUSES_NUMSEG; ARITH; VECTOR_SUB_LZERO] THEN
    REWRITE_TAC[NORM_NEG; COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= a + b ==> x <= a + abs y + b`) THEN
  MATCH_MP_TAC(NORM_ARITH
   `!s'. norm(s') <= p /\ norm(s - s' - l) <= &21
        ==> norm(s - l) <= abs p + &21`) THEN
  EXISTS_TAC `vsum(1..x) (\n. (chi_0 d n - Cx(&1)) * Cx(mangoldt n / &n))` THEN
  ASM_SIMP_TAC[BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL_LEMMA] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_RING `c * x - (c - Cx(&1)) * x = x`] THEN
  SIMP_TAC[GSYM CX_SUB; VSUM_CX; FINITE_NUMSEG; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC MERTENS_LEMMA THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The arithmetic-geometric mean that we want.                               *)
(* ------------------------------------------------------------------------- *)

let SUM_OF_NUMBERS = prove
 (`!n. nsum(0..n) (\i. i) = (n * (n + 1)) DIV 2`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let PRODUCT_POW_NSUM = prove
 (`!s. FINITE s ==> product s (\i. z pow (f i)) = z pow (nsum s f)`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NSUM_CLAUSES; real_pow; REAL_POW_ADD]);;

let PRODUCT_SPECIAL = prove
 (`!z i. product (0..n) (\i. z pow i) = z pow ((n * (n + 1)) DIV 2)`,
  SIMP_TAC[PRODUCT_POW_NSUM; FINITE_NUMSEG; SUM_OF_NUMBERS]);;

let AGM_SPECIAL = prove
 (`!n t. &0 <= t
         ==> (&n + &1) pow 2 * t pow n <= (sum(0..n) (\k. t pow k)) pow 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n + 1`; `\k. (t:real) pow (k - 1)`] AGM) THEN
  ASM_SIMP_TAC[REAL_POW_LE; ARITH_RULE `1 <= n + 1`] THEN
  SUBGOAL_THEN `1..n+1 = 0+1..n+1` SUBST1_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[SUM_OFFSET; PRODUCT_OFFSET; ADD_SUB] THEN
  REWRITE_TAC[PRODUCT_SPECIAL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] REAL_POW_LE2)) THEN
  DISCH_THEN(MP_TAC o SPEC `2`) THEN
  ASM_SIMP_TAC[PRODUCT_POS_LE_NUMSEG; REAL_POW_LE] THEN
  REWRITE_TAC[REAL_POW_POW] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  SUBGOAL_THEN `2 * (n * (n + 1)) DIV 2 = n * (n + 1)` SUBST1_TAC THENL
   [SUBGOAL_THEN `EVEN(n * (n + 1))` MP_TAC THENL
     [REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH_EVEN] THEN CONV_TAC TAUT;
      SIMP_TAC[EVEN_EXISTS; LEFT_IMP_EXISTS_THM; DIV_MULT; ARITH]];
    REWRITE_TAC[GSYM REAL_POW_POW] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_POW_LE2_REV)) THEN
    REWRITE_TAC[ADD_EQ_0; ARITH_EQ; REAL_POW_2; REAL_LE_SQUARE] THEN
    REWRITE_TAC[GSYM REAL_POW_2; GSYM REAL_OF_NUM_ADD] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LE_RDIV_EQ; REAL_POW_LT;
                 REAL_ARITH `&0 < &n + &1`] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* The trickiest part: the nonvanishing of L-series for real character.      *)
(* Proof from Monsky's article (AMM 1993, pp. 861-2).                        *)
(* ------------------------------------------------------------------------- *)

let DIVISORSUM_PRIMEPOW = prove
 (`!f p k. prime p
           ==> sum {m | m divides (p EXP k)} c = sum(0..k) (\i. c(p EXP i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
   `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM NUMSEG_LE] THEN MATCH_MP_TAC SUM_IMAGE THEN
  ASM_SIMP_TAC[IN_ELIM_THM; EQ_EXP; FINITE_NUMSEG_LE] THEN
  ASM_MESON_TAC[PRIME_0; PRIME_1]);;

let DIVISORVSUM_PRIMEPOW = prove
 (`!f p k. prime p
           ==> vsum {m | m divides (p EXP k)} c = vsum(0..k) (\i. c(p EXP i))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; SET_RULE
   `{m | ?i. P i /\ m = f i} = IMAGE f {i | P i}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[GSYM NUMSEG_LE] THEN MATCH_MP_TAC VSUM_IMAGE THEN
  ASM_SIMP_TAC[IN_ELIM_THM; EQ_EXP; FINITE_NUMSEG_LE] THEN
  ASM_MESON_TAC[PRIME_0; PRIME_1]);;

let DIRICHLET_CHARACTER_DIVISORSUM_EQ_1 = prove
 (`!d c p k. dirichlet_character d c /\ prime p /\ p divides d
             ==> vsum {m | m divides (p EXP k)} c = Cx(&1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `vsum {1} c : complex` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[VSUM_SING] THEN ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1]] THEN
  MATCH_MP_TAC VSUM_SUPERSET THEN
  SIMP_TAC[SUBSET; IN_SING; IN_ELIM_THM; DIVIDES_1] THEN
  ASM_SIMP_TAC[DIVIDES_PRIMEPOW; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:num`; `i:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_0 th]) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_REXP] THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[COPRIME_SYM; PRIME_COPRIME_EQ]);;

let DIRICHLET_CHARACTER_REAL_CASES = prove
 (`!d c. dirichlet_character d c /\ (!n. real(c n))
         ==> !n. c n = --Cx(&1) \/ c n = Cx(&0) \/ c n = Cx(&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIRICHLET_CHARACTER_NORM) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN REWRITE_TAC[REAL_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` SUBST1_TAC) THEN
  REWRITE_TAC[COMPLEX_NORM_CX; GSYM CX_NEG; CX_INJ] THEN REAL_ARITH_TAC);;

let DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS = prove
 (`!d c p k. dirichlet_character d c /\ (!n. real(c n)) /\ prime p
             ==> &0 <= Re(vsum {m | m divides (p EXP k)} c)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RE_VSUM; FINITE_DIVISORS; EXP_EQ_0; PRIME_IMP_NZ] THEN
  ASM_SIMP_TAC[DIVISORSUM_PRIMEPOW] THEN
  FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_POW th]) THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] DIRICHLET_CHARACTER_REAL_CASES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM CX_POW; RE_CX; SUM_POS_LE_NUMSEG;
               REAL_POW_LE; REAL_POS] THEN
  MATCH_MP_TAC(REAL_ARITH `(s = if EVEN k then &1 else &0) ==> &0 <= s`) THEN
  SPEC_TAC(`k:num`,`r:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[EVEN; SUM_CLAUSES_NUMSEG] THEN
  ASM_REWRITE_TAC[complex_pow; RE_CX; LE_0] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_POW_NEG; COMPLEX_POW_ONE; COMPLEX_MUL_LNEG;
                  COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG; COMPLEX_MUL_LID;
                  RE_NEG; RE_CX] THEN
  REAL_ARITH_TAC);;

let DIRICHLET_CHARACTER_DIVISORSUM_POS = prove
 (`!d c n. dirichlet_character d c /\ (!n. real(c n)) /\ ~(n = 0)
           ==> &0 <= Re(vsum {m | m divides n} c)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(n = 0) ==> n = 1 \/ 1 < n`))
  THENL
   [ASM_SIMP_TAC[DIVIDES_ONE; SING_GSPEC; VSUM_SING] THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; RE_CX; REAL_POS];
    ALL_TAC] THEN
  UNDISCH_TAC `1 < n` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  MATCH_MP_TAC INDUCT_COPRIME_STRONG THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[DIRICHLET_CHARACTER_DIVISORSUM_PRIMEPOW_POS]] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `\m:num. Re(c m)` REAL_MULTIPLICATIVE_DIVISORSUM) THEN
  REWRITE_TAC[real_multiplicative] THEN ANTS_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
    ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_1; RE_CX; REAL; CX_MUL];
  DISCH_THEN(MP_TAC o SPECL [`a:num`; `b:num`] o CONJUNCT2) THEN
  ASM_SIMP_TAC[GSYM RE_VSUM; FINITE_DIVISORS; MULT_EQ_0;
               ARITH_RULE `1 < n ==> ~(n = 0)`; REAL_LE_MUL]]);;

let lemma = prove
 (`!x n. &0 <= x /\ x <= &1 ==> &1 - &n * x <= (&1 - x) pow n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[real_pow] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - x) * (&1 - &n * x)` THEN
  ASM_SIMP_TAC[REAL_LE_LMUL; REAL_SUB_LE; GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= n * x * x ==> &1 - (n + &1) * x <= (&1 - x) * (&1 - n * x)`) THEN
  SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_LE_SQUARE]);;

let LFUNCTION_NONZERO_REAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d) /\ (!n. real(c n))
         ==> ~(Lfunction c = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
   DIRICHLET_CHARACTER_NONPRINCIPAL_NONTRIVIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!z. norm(z) < &1
        ==> summable (from 1) (\n. c(n) * z pow n / (Cx(&1) - z pow n))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `z = Cx(&0)` THENL
     [MATCH_MP_TAC SUMMABLE_FROM_ELSEWHERE THEN EXISTS_TAC `2` THEN
      MATCH_MP_TAC SUMMABLE_EQ THEN EXISTS_TAC `\n:num. Cx(&0)` THEN
      REWRITE_TAC[GSYM COMPLEX_VEC_0; SUMMABLE_0] THEN
      ASM_SIMP_TAC[COMPLEX_VEC_0; COMPLEX_POW_ZERO; IN_FROM;
                   ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
    EXISTS_TAC `\n. Cx(&2 * norm(z:complex) pow n)` THEN
    REWRITE_TAC[REAL_CX; RE_CX] THEN
    SIMP_TAC[REAL_LE_MUL; REAL_POS; REAL_POW_LE; NORM_POS_LE] THEN
    ASM_SIMP_TAC[CX_MUL; CX_POW; SUMMABLE_COMPLEX_LMUL; COMPLEX_NORM_CX;
                 REAL_ABS_NORM; SUMMABLE_GP] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ABS_POS; REAL_LE_MUL] THEN
    REWRITE_TAC[TAUT `(p ==> (if q then x else T)) <=> p /\ q ==> x`] THEN
    MP_TAC(SPECL [`norm(z:complex)`; `&1 / &2`] REAL_ARCH_POW_INV) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[GE] THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; REAL_ABS_NUM; REAL_ABS_POW] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[complex_div; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN
    SUBST1_TAC(REAL_ARITH `&2 = inv(&1 / &2)`) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(z) <= norm(w) - h ==> h <= norm(w - z)`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `norm(z:complex) pow N` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[COMPLEX_NORM_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  REWRITE_TAC[summable; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:complex->complex` (LABEL_TAC "+")) THEN
  ABBREV_TAC `b = \z n. inv(Cx(&n) * (Cx(&1) - z)) -
                        z pow n / (Cx(&1) - z pow n)` THEN
  SUBGOAL_THEN
   `!z:complex. norm(z) < &1 ==> ((\n. c(n) * b z n) sums --(f z)) (from 1)`
   (LABEL_TAC "*")
  THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "b" THEN
    REWRITE_TAC[COMPLEX_SUB_LDISTRIB; GSYM COMPLEX_SUB_LZERO] THEN
    MATCH_MP_TAC SERIES_SUB THEN ASM_SIMP_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
    REWRITE_TAC[COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
    SUBST1_TAC(COMPLEX_RING `Cx(&0) = Cx(&0) * inv(Cx(&1) - z)`) THEN
    MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION) THEN
    ASM_REWRITE_TAC[complex_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z. norm(z) < &1
                    ==> ((\n. vsum {d | d divides n} (\d. c d) * z pow n) sums
                         f(z)) (from 1)`
  (LABEL_TAC "+") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_DIVISORS; LE_1] THEN
    REWRITE_TAC[VSUM_VSUM_DIVISORS] THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `z:complex`) THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG; sums; FROM_INTER_NUMSEG] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM COMPLEX_SUB_LDISTRIB] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN
    REWRITE_TAC[VSUM_GP; ARITH_RULE `n < 1 <=> n = 0`] THEN
    SIMP_TAC[DIV_EQ_0; LE_1] THEN SIMP_TAC[GSYM NOT_LE] THEN
    SUBGOAL_THEN `!k. 1 <= k ==> ~(z pow k = Cx(&1))` (fun th -> SIMP_TAC[th])
    THENL [ASM_MESON_TAC[COMPLEX_POW_EQ_1; LE_1; REAL_LT_REFL]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_POW_1; complex_div] THEN
    REWRITE_TAC[COMPLEX_RING `(zx * i - (zx - w) * i) = w * i`] THEN
    SIMP_TAC[COMPLEX_POW_POW] THEN MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
    EXISTS_TAC `\x. vsum (1..x)
                       (\n. z pow x * c n *
                            z pow (n - x MOD n) / (Cx(&1) - z pow n))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
      X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[complex_div; COMPLEX_INV_MUL; COMPLEX_MUL_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      ONCE_REWRITE_TAC[COMPLEX_RING `(zx * cn) * zn = cn * zx * zn`] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN
      AP_TERM_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
      MP_TAC(SPECL [`x:num`; `n:num`] DIVISION) THEN ASM_SIMP_TAC[LE_1] THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN
    MATCH_MP_TAC LIM_NULL_COMPARISON_COMPLEX THEN
    EXISTS_TAC `\x. Cx(norm(z) / (&1 - norm z)) * Cx(&x) * z pow x` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `x:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
      REWRITE_TAC[FINITE_NUMSEG; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
                  REAL_ABS_DIV; REAL_ABS_NUM] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_ARITH `a * &x * b = &x * a * b`] THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      FIRST_ASSUM(fun t -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM t]) THEN
      COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LE_DIV; REAL_ABS_POS;
                   NORM_POS_LE; REAL_LE_MUL; REAL_MUL_LID; REAL_ABS_NORM] THEN
      GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      SIMP_TAC[complex_div; real_div; COMPLEX_NORM_MUL; COMPLEX_NORM_INV] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_LE_INV_EQ] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[COMPLEX_NORM_POW] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE] THEN
        MATCH_MP_TAC(ARITH_RULE `m < r ==> 1 <= r - m`) THEN
        ASM_SIMP_TAC[DIVISION; LE_1];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_ARITH `&0 < abs(x - a) <=> ~(a = x)`] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(w) = &1 /\ norm(z) < &1 /\ norm(zn) <= norm(z)
        ==> abs(&1 - norm(z)) <= norm(w - zn)`) THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NUM; COMPLEX_NORM_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC LIM_NULL_COMPLEX_LMUL THEN ASM_SIMP_TAC[LIM_N_TIMES_POWN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(bounded
       { (f:complex->complex)(t) | real t /\ &0 <= Re t /\ norm(t) < &1 })`
  MP_TAC THENL
   [REWRITE_TAC[BOUNDED_POS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_REAL] THEN
    REWRITE_TAC[COMPLEX_NORM_CX; RE_CX; IMP_IMP] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x /\ abs x < &1 <=> &0 <= x /\ x < &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC o
      MATCH_MP PRIME_FACTOR) THEN
    X_CHOOSE_TAC `N:num` (SPEC `&2 * (B + &1)` REAL_ARCH_SIMPLE) THEN
    SUBGOAL_THEN `0 < N` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `t = &1 - inv(&(p EXP N)) / &2` THEN
    SUBGOAL_THEN `&0 <= t /\ t < &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "t" THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 < y /\ y <= &1 ==> &0 <= &1 - y / &2 /\ &1 - y / &2 < &1`) THEN
      ASM_SIMP_TAC[REAL_INV_LE_1; REAL_LT_INV_EQ; REAL_OF_NUM_LE;
                           REAL_OF_NUM_LT; LE_1; EXP_EQ_0; PRIME_IMP_NZ];
      ALL_TAC] THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `Cx t`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN REWRITE_TAC[SERIES_FROM; LIM_SEQUENTIALLY] THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` MP_TAC) THEN
    SUBGOAL_THEN `?n. M <= n /\ 1 <= n /\ p EXP N <= n` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `p EXP N + M + 1` THEN ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `norm (f (Cx t):complex) <= B` THEN
    MATCH_MP_TAC(NORM_ARITH
     `B + &1 <= norm(x) ==> norm(y) <= B ==> ~(dist(x,y) < &1)`) THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= Re z /\ abs(Re z) <= norm z ==> a <= norm z`) THEN
    REWRITE_TAC[COMPLEX_NORM_GE_RE_IM] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX; GSYM CX_POW] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (IMAGE (\k. p EXP k) (0..N))
                    (\x. Re (vsum {d | d divides x} (\d. c d)) * t pow x)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; IN_DIFF; SUBSET; IN_ELIM_THM;
                  FORALL_IN_IMAGE] THEN
      MP_TAC(SPECL [`d:num`; `c:num->complex`]
        DIRICHLET_CHARACTER_DIVISORSUM_POS) THEN
      ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; LE_1; ETA_AX] THEN
      DISCH_THEN(K ALL_TAC) THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p EXP N` THEN
      ASM_SIMP_TAC[LE_EXP; PRIME_IMP_NZ]] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[EQ_EXP] THEN ASM_MESON_TAC[PRIME_0; PRIME_1]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum (0..N) (\k. &1 * &1 / &2)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUM_CONST_NUMSEG; SUB_0; GSYM REAL_OF_NUM_ADD] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`d:num`; `c:num->complex`; `p:num`; `k:num`]
                DIRICHLET_CHARACTER_DIVISORSUM_EQ_1) THEN
      ASM_SIMP_TAC[ETA_AX; RE_CX; REAL_LE_REFL];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`inv(&(p EXP N)) / &2`; `p EXP k`] lemma) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [REWRITE_TAC[real_div; GSYM REAL_INV_MUL; REAL_OF_NUM_MUL] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
      MATCH_MP_TAC REAL_INV_LE_1 THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      ASM_SIMP_TAC[EXP_EQ_0; MULT_EQ_0; ARITH; PRIME_IMP_NZ];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= a ==> a <= x ==> b <= x`) THEN
    MATCH_MP_TAC(REAL_ARITH `x * y <= &1 ==> &1 / &2 <= &1 - x * y / &2`) THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; LE_1;
                 EXP_EQ_0; PRIME_IMP_NZ] THEN
    ASM_REWRITE_TAC[REAL_MUL_LID; REAL_OF_NUM_LE; LE_EXP] THEN
    ASM_MESON_TAC[PRIME_0];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`]
    BOUNDED_LFUNCTION_PARTIAL_SUMS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
  REWRITE_TAC[BOUNDED_POS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MESON[] `(!x a b. x = f a b ==> p a b) <=> (!a b. p a b)`] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN EXISTS_TAC `&2 * B` THEN
  ASM_SIMP_TAC[REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
   `\n. vsum(from 1 INTER (0..n)) (\k. c k * b (z:complex) k :complex)` THEN
  ASM_SIMP_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; GSYM sums] THEN
  REWRITE_TAC[FROM_INTER_NUMSEG] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`c:num->complex`; `(b:complex->num->complex) z`;
                 `B:real`; `1`] SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    SUBGOAL_THEN `(b:complex->num->complex) z 1 = Cx(&1)` SUBST1_TAC THENL
     [EXPAND_TAC "b" THEN
      REWRITE_TAC[COMPLEX_POW_1; COMPLEX_INV_MUL; complex_div] THEN
      REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_INV_1] THEN
      MATCH_MP_TAC COMPLEX_MUL_RINV THEN REWRITE_TAC[COMPLEX_SUB_0] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `norm(Cx(&1)) < &1` THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_LT_REFL; REAL_ABS_NUM];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_NUM; REAL_MUL_RID] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `t:real` SUBST_ALL_TAC o
                GEN_REWRITE_RULE I [REAL_EXISTS]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[RE_CX; COMPLEX_NORM_CX]) THEN
  SUBGOAL_THEN `!n. &0 < sum(0..n) (\m. t pow m)` ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC[LE_0; SUM_CLAUSES_LEFT; real_pow] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    ASM_SIMP_TAC[SUM_POS_LE_NUMSEG; REAL_POW_LE];
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN EXPAND_TAC "b" THEN
  REWRITE_TAC[GSYM CX_SUB; GSYM CX_POW; GSYM CX_DIV; GSYM CX_MUL;
              GSYM CX_INV; REAL_CX; RE_CX]
  THENL
   [ASM_SIMP_TAC[REAL_SUB_POW_L1; REAL_SUB_LE] THEN
    ASM_REWRITE_TAC[real_div; REAL_INV_MUL] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT;
                 LE_1; REAL_ARITH `abs t < &1 ==> &0 < &1 - t`] THEN
    ASM_SIMP_TAC[real_div; REAL_FIELD
     `abs(t) < &1 ==> (x * inv(&1 - t) * y) * (&1 - t) = x * y`] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_OF_NUM_LT; LE_1] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x / y * &n = (&n * x) / y`] THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n-1) (\m. t pow n)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_CONST_NUMSEG; ARITH_RULE `1 <= n ==> n - 1 + 1 = n`;
                   SUB_0; REAL_LE_REFL];
      REWRITE_TAC[REAL_MUL_LID] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_POW_MONO_INV THEN REPEAT CONJ_TAC THEN
      TRY ASM_REAL_ARITH_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_SUB_POW_L1; ARITH_RULE `1 <= n + 1`] THEN
  REWRITE_TAC[ADD_SUB; REAL_INV_MUL; real_div] THEN
  REWRITE_TAC[REAL_ARITH `x * t - y * t * z <= u * t - v * t * w <=>
                          t * (v * w - y * z) <= t * (u - x)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_FIELD
   `&0 < y /\ &0 < z ==> x / y - w / z = (x * z - w * y) / (y * z)`] THEN
  SUBGOAL_THEN `t pow n * sum (0..n) (\m. t pow m) -
                t pow (n + 1) * sum (0..n - 1) (\m. t pow m) = t pow n`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM REAL_POW_ADD] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `(n + 1) + x = n + x + 1`] THEN
    REWRITE_TAC[GSYM(SPEC `1` SUM_OFFSET); SUB_ADD; ADD_CLAUSES] THEN
    SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; GSYM SUM_LMUL; ADD_CLAUSES] THEN
    ASM_SIMP_TAC[SUB_ADD; REAL_POW_ADD] THEN
    REWRITE_TAC[REAL_ARITH `(x + y) - y:real = x`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_MUL; GSYM REAL_OF_NUM_ADD;
               REAL_OF_NUM_LE;
       REAL_FIELD `&1 <= n ==> inv(n) - inv(n + &1) = inv(n * (n + &1))`] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH] THEN CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN
           CONJ_TAC THEN REWRITE_TAC[REAL_LE_INV_EQ]) THEN
    ASM_SIMP_TAC[REAL_POW_LE; SUM_POS_LE_NUMSEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `t:real`] AGM_SPECIAL) THEN
  MP_TAC(SPECL [`n - 1`; `t:real`] AGM_SPECIAL) THEN
  ASM_SIMP_TAC[GSYM REAL_OF_NUM_SUB; REAL_SUB_ADD] THEN
  REWRITE_TAC[IMP_IMP] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
               LE_1; REAL_ARITH `&0 < &n + &1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE
   [TAUT `a /\ b /\ c /\ d ==> e <=> b /\ d ==> a /\ c ==> e`]
   REAL_LE_MUL2)) THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_ARITH `&0 <= &n + &1`] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y /\ a <= b ==> b <= x ==> a <= y`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_POW_2; real_div; REAL_INV_MUL; REAL_POW_MUL] THEN
    REWRITE_TAC[REAL_MUL_AC];
    REWRITE_TAC[GSYM REAL_POW_ADD; REAL_POW_POW] THEN
    MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Deduce nonvanishing of all the nonprincipal characters.                   *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_DIFF_LOGMUL = prove
 (`!f a. bounded {f x - Cx(log(&x)) * a | x IN (:num)}
         ==> (!x. &0 <= Re(f x)) ==> &0 <= Re a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[BOUNDED_POS; SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `exp((B + &1) / --(Re a))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  SUBGOAL_THEN `abs(Re(f n - Cx(log(&n)) * a)) <= B` MP_TAC THENL
   [ASM_MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LE_TRANS]; ALL_TAC] THEN
  REWRITE_TAC[RE_SUB; RE_MUL_CX; REAL_NOT_LE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `B < l * --a /\ &0 <= f ==> B < abs(f - l * a)`) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ; REAL_NEG_GT0] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN
  EXISTS_TAC `log(exp((B + &1) / --Re a))` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[LOG_EXP; REAL_NEG_GT0; REAL_LT_DIV2_EQ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT]]);;

let LFUNCTION_NONZERO_NONPRINCIPAL = prove
 (`!d c. dirichlet_character d c /\ ~(c = chi_0 d)
         ==> ~(Lfunction c = Cx(&0))`,
  let lemma = prove
   (`{a,b,c} SUBSET s
     ==> FINITE s
         ==> !f. sum s f = sum (s DIFF {a,b,c}) f + sum {a,b,c} f`,
    REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_UNION_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]) in
  GEN_TAC THEN ASM_CASES_TAC `d = 0` THENL
   [ASM_MESON_TAC[DIRICHLET_CHARACTER_0]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x c. vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) -
           Cx(log(&x)) *
           (if c = chi_0 d then Cx(&1)
            else if Lfunction c = Cx(&0) then --Cx(&1)
            else Cx(&0))`;
    `(:num)`;
    `{c | dirichlet_character d c}`]
   BOUNDED_SUMS_IMAGES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
    X_GEN_TAC `c:num->complex` THEN
    ASM_CASES_TAC `c = chi_0 d` THEN
    ASM_SIMP_TAC[COMPLEX_MUL_RID; BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL;
                 LE_1] THEN
    ASM_CASES_TAC `Lfunction c = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_RZERO; COMPLEX_MUL_RNEG; COMPLEX_MUL_RZERO;
                    COMPLEX_MUL_RID; COMPLEX_SUB_RNEG] THEN
    ASM_MESON_TAC[BOUNDED_DIRICHLET_MANGOLDT_ZERO;
                  BOUNDED_DIRICHLET_MANGOLDT_NONZERO; LE_1];
    ALL_TAC] THEN
  SIMP_TAC[VSUM_SUB; FINITE_DIRICHLET_CHARACTERS; VSUM_COMPLEX_LMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_DIFF_LOGMUL) THEN
  REWRITE_TAC[IN_UNIV] THEN ANTS_TAC THENL
   [X_GEN_TAC `x:num` THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o funpow 2 rand o snd) THEN
    REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_NUMSEG] THEN
    DISCH_THEN SUBST1_TAC THEN
    SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_DIRICHLET_CHARACTERS] THEN
    SIMP_TAC[RE_VSUM; FINITE_NUMSEG; RE_MUL_CX] THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS_POS;
             REAL_LE_DIV; REAL_POS; MANGOLDT_POS_LE];
    ALL_TAC] THEN
  SIMP_TAC[RE_VSUM; FINITE_DIRICHLET_CHARACTERS] THEN
  REPLICATE_TAC 2 (ONCE_REWRITE_TAC[COND_RAND]) THEN
  REWRITE_TAC[RE_NEG; RE_CX] THEN DISCH_TAC THEN
  X_GEN_TAC `c:num->complex` THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LT]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{chi_0 d,c,(\n. cnj(c n))} SUBSET {c | dirichlet_character d c}`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[DIRICHLET_CHARACTER_CHI_0; DIRICHLET_CHARACTER_CNJ];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `s <= &0 /\ t < &0 ==> s + t < &0`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= --x ==> x <= &0`) THEN
    REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_POS_LE THEN
    SIMP_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_DIFF] THEN
    SIMP_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; IN_INSERT; NOT_IN_EMPTY;
               FINITE_RULES] THEN
  SUBGOAL_THEN `~(chi_0 d = (\n. cnj (c n)))` ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o AP_TERM `(\c n:num. cnj(c n))`) THEN
    REWRITE_TAC[CNJ_CNJ; FUN_EQ_THM; CNJ_CHI_0] THEN
    ASM_REWRITE_TAC[GSYM FUN_EQ_THM; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c = \n:num. cnj(c n))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
    REWRITE_TAC[GSYM REAL_CNJ; FUN_EQ_THM] THEN
    ASM_MESON_TAC[LFUNCTION_NONZERO_REAL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `c:num->complex`] LFUNCTION_CNJ) THEN
  ASM_SIMP_TAC[CNJ_EQ_CX] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Hence derive our boundedness result for all nonprincipal characters.      *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL = prove
 (`!d c.
      dirichlet_character d c /\ ~(c = chi_0 d)
      ==> bounded { vsum(1..x) (\n. c n * Cx(mangoldt n / &n)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_DIRICHLET_MANGOLDT_NONZERO THEN
  EXISTS_TAC `d:num` THEN
  ASM_MESON_TAC[LFUNCTION_NONZERO_NONPRINCIPAL]);;

(* ------------------------------------------------------------------------- *)
(* Hence the main sum result.                                                *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS = prove
 (`!d l. 1 <= d /\ coprime(l,d)
         ==> bounded { vsum {c | dirichlet_character d c}
                            (\c. c(l) *
                                 vsum(1..x) (\n. c n * Cx (mangoldt n / &n))) -
                       Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `!x. Cx(log(&x)) =
                        vsum {c | dirichlet_character d c}
                             (\c. if c = chi_0 d then Cx(log(&x)) else Cx(&0))`
   (fun th -> ONCE_REWRITE_TAC[th])
  THENL
   [SIMP_TAC[VSUM_DELTA; GSYM COMPLEX_VEC_0] THEN
    REWRITE_TAC[IN_ELIM_THM; DIRICHLET_CHARACTER_CHI_0];
    ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_DIRICHLET_CHARACTERS] THEN
  MATCH_MP_TAC BOUNDED_SUMS_IMAGES THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; IN_ELIM_THM] THEN
  X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
  ASM_CASES_TAC `c = chi_0 d` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_DIRICHLET_MANGOLDT_PRINCIPAL) THEN
    ASM_REWRITE_TAC[chi_0; COMPLEX_MUL_LID];
    REWRITE_TAC[COMPLEX_SUB_RZERO] THEN
    MP_TAC(SPECL [`d:num`; `c:num->complex`]
      BOUNDED_DIRICHLET_MANGOLDT_NONPRINCIPAL) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[BOUNDED_POS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
    FIRST_ASSUM(fun th -> SIMP_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
    REAL_ARITH_TAC]);;

let DIRICHLET_MANGOLDT = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> bounded { Cx(&(phi d)) * vsum {n | n IN 1..x /\ (n == k) (mod d)}
                                           (\n. Cx(mangoldt n / &n)) -
                       Cx(log(&x)) | x IN (:num)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?l. (k * l == 1) (mod d)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[CONG_SOLVE]; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `l:num`] BOUNDED_SUM_OVER_DIRICHLET_CHARACTERS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(k * l == 1) (mod d)` THEN
    CONV_TAC NUMBER_RULE;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(!x. x IN s ==> f x = g x) ==> {f x | x IN s} = {g x | x IN s}`) THEN
  X_GEN_TAC `x:num` THEN DISCH_THEN(K ALL_TAC) THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; FINITE_RESTRICT] THEN
  SIMP_TAC[VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_DIRICHLET_CHARACTERS; FINITE_NUMSEG] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
  MP_TAC(GSYM(SPEC `d:num` DIRICHLET_CHARACTER_MUL)) THEN
  SIMP_TAC[IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN
  SIMP_TAC[VSUM_COMPLEX_RMUL; FINITE_DIRICHLET_CHARACTERS] THEN
  ASM_SIMP_TAC[DIRICHLET_CHARACTER_SUM_OVER_CHARACTERS] THEN
  SUBGOAL_THEN `(l * n == 1) (mod d) <=> (n == k) (mod d)` SUBST1_TAC THENL
   [UNDISCH_TAC `(k * l == 1) (mod d)` THEN CONV_TAC NUMBER_RULE;
    COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;

let DIRICHLET_MANGOLDT_EXPLICIT = prove
 (`!d k. 1 <= d /\ coprime (k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {n | n IN 1..x /\ (n == k) (mod d)}
                             (\n. mangoldt n / &n) -
                         log(&x) / &(phi d)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIRICHLET_MANGOLDT) THEN
  REWRITE_TAC[BOUNDED_POS] THEN
  SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV] THEN
  SIMP_TAC[VSUM_CX; FINITE_RESTRICT; FINITE_NUMSEG;
           GSYM CX_SUB; GSYM CX_MUL; COMPLEX_NORM_CX] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B / &(phi d)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; PHI_LOWERBOUND_1_STRONG;
               REAL_LE_RDIV_EQ] THEN
  X_GEN_TAC `n:num` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM REAL_ABS_NUM] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_SUB_LDISTRIB; REAL_DIV_LMUL;
               LE_1; PHI_LOWERBOUND_1_STRONG; REAL_OF_NUM_EQ]);;

let DIRICHLET_STRONG = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> ?B. &0 < B /\
                 !x. abs(sum {p | p IN 1..x /\ prime p /\ (p == k) (mod d)}
                             (\p. log(&p) / &p) -
                         log(&x) / &(phi d)) <= B`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC o
    MATCH_MP DIRICHLET_MANGOLDT_EXPLICIT) THEN
  EXISTS_TAC `B + &3` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:num`) THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x - y) <= a ==> abs(x - z) <= b ==> abs(y - z) <= b + a`) THEN
  MP_TAC(SPECL [`x:num`; `{n | n IN 1..x /\ (n == k) (mod d)}`]
               MERTENS_MANGOLDT_VERSUS_LOG) THEN
  SIMP_TAC[SUBSET; IN_ELIM_THM] THEN REWRITE_TAC[CONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* Ignore the density details and prove the main result.                     *)
(* ------------------------------------------------------------------------- *)

let DIRICHLET = prove
 (`!d k. 1 <= d /\ coprime(k,d)
         ==> INFINITE {p | prime p /\ (p == k) (mod d)}`,
  REWRITE_TAC[INFINITE] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\n:num. n` o MATCH_MP UPPER_BOUND_FINITE_SET) THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN MP_TAC(SPECL [`d:num`; `k:num`] DIRICHLET_STRONG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC
   `max (exp(&(phi d) *
            (&1 + B + sum {p | p IN 1..n /\ prime p /\ (p == k) (mod d)}
                          (\p. log(&p) / &p))))
        (max (&n) (&1))`
   REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[NOT_EXISTS_THM; REAL_MAX_LE; REAL_OF_NUM_LE] THEN
  X_GEN_TAC `m:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) <= b ==> y < &1 + b + x`)) THEN
  ASM_SIMP_TAC[REAL_NOT_LT; REAL_LE_RDIV_EQ; PHI_LOWERBOUND_1_STRONG;
               REAL_OF_NUM_LT; LE_1] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ONCE_REWRITE_TAC[GSYM REAL_EXP_MONO_LE] THEN
  ASM_SIMP_TAC[EXP_LOG; REAL_OF_NUM_LT; LE_1] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x <= a ==> x = y ==> y <= a`)) THEN
  REPLICATE_TAC 4 AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
  GEN_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC);;
