(* ========================================================================= *)
(* Linear forms in many variables, part 1: local counts, the Chinese         *)
(* remainder theorem for tuples, and boxes.                                  *)
(*                                                                           *)
(* For integer coefficients b and a constant b0 the affine form is           *)
(*   lf_form k b b0 z = sum_{i IN k} b i * z i + b0,                         *)
(* and lf_ncount k p B B0 J counts the z in Z_p^k (residues r < p in each    *)
(* coordinate) with p | lf_form k (B j) (B0 j) z for every j IN J.           *)
(* * COUNT_ONE_FORM: a form with a coefficient prime to p has p^(|k| - 1)    *)
(*   zeros mod p; COUNT_TWO_FORMS: two forms with a 2 x 2 minor prime to p   *)
(*   have p^(|k| - 2) common zeros.  With the nondegeneracy predicates       *)
(*   lf_pnz and lf_pind: LF_NCOUNT_EMPTY, LF_NCOUNT_SING, LF_NCOUNT_PAIR and *)
(*   LF_NCOUNT_MONO.                                                         *)
(* * CRT_TUPLE_SUM, DENSITY_CRT: for D j SUBSET P (primes), the number of    *)
(*   x mod prod P with prod(D j) | lf_form (B j) (B0 j) x for all j IN Js is *)
(*   the product over p IN P of lf_ncount at {j | p IN D j}.                 *)
(* * lf_box t a M = prod_{i < t} [a i, a i + M i):  COUNT_RESIDUE_INTERVAL   *)
(*   (an interval of length M meets each class mod D in M / D + O(1)         *)
(*   points), LF_BOX_SUM_RESIDUES and LF_BOX_APPROX (the sum of a D-periodic *)
(*   g over a box is prod_i (M i / D) sum_{Z_D^t} g up to (prod_i (M i / D + *)
(*   1) - prod_i (M i / D)) sum_{Z_D^t} |g|, by PRODUCT_PERTURB).            *)
(* ========================================================================= *)

needs "Sieve/bg_s1.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Cartesian products and the Chinese remainder theorem for tuples.          *)
(* ------------------------------------------------------------------------- *)

let SUM_CARTESIAN_INSERT = prove
 (`!a k (s:K->A->bool) (f:(K->A)->real).
        FINITE k /\ ~(a IN k) /\ (!i. i IN k ==> FINITE(s i)) /\ FINITE(s a)
        ==> sum (cartesian_product (a INSERT k) s) f =
            sum (s a) (\u. sum (cartesian_product k s)
                               (\x. f (\i. if i = a then u else x i)))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CARTESIAN_PRODUCT_INSERT_IMAGE] THEN
  SUBGOAL_THEN `FINITE(cartesian_product k (s:K->A->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; FUN_EQ_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:A`; `x:K->A`; `v:A`; `z:K->A`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:K`) THEN REWRITE_TAC[];
      MATCH_MP_TAC CARTESIAN_PRODUCT_EQ_MEMBERS THEN
      MAP_EVERY EXISTS_TAC [`k:K->bool`; `s:K->A->bool`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:K` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:K`) THEN
      COND_CASES_TAC THEN ASM_MESON_TAC[]];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  MP_TAC(ISPECL
   [`(s:K->A->bool) a`; `\u:A. cartesian_product k (s:K->A->bool)`;
    `\u:A x:K->A. (f:(K->A)->real) (\i. if i = a then u else x i)`]
   SUM_SUM_PRODUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[]);;

let CRT_TUPLE_SUM = prove
 (`!t P (Fp:num->(num->num)->real).
     FINITE P /\ (!p. p IN P ==> prime p) /\
     (!p z z'. p IN P /\ (!i. i < t ==> z i = z' i) ==> Fp p z = Fp p z')
     ==> sum (cartesian_product {i | i < t}
                                (\i. {c | c < nproduct P (\p. p)}))
             (\x. product P (\p. Fp p (\i. x i MOD p))) =
         product P (\p. sum (cartesian_product {i | i < t}
                                               (\i. {r | r < p})) (Fp p))`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LT; EMPTY_GSPEC; CARTESIAN_PRODUCT_EMPTY; SUM_SING] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    X_GEN_TAC `p:num` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[LT];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{i | i < SUC t} = t INSERT {i | i < t}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t IN {i:num | i < t})` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CARTESIAN_INSERT; FINITE_NUMSEG_LT] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (cartesian_product {i | i < t} (\i. {c | c < nproduct P (\p. p)}))
        (\x. product P
               (\p. (\p z. sum {r | r < p}
                       (\r. (Fp:num->(num->num)->real) p
                               (\i. if i = t then r else z i)))
                    p (\i. x i MOD p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MP_TAC(ISPECL [`P:num->bool`;
                   `\p r. (Fp:num->(num->num)->real) p
                             (\i. if i = t then r else x i MOD p)`]
                  CRT_SUM_PRODUCT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `u:num` THEN DISCH_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN
    DISCH_TAC THEN BETA_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
    COND_CASES_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    W(MP_TAC o PART_MATCH (lhand o rand) th o lhand o snd)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `z:num->num`; `z':num->num`] THEN
    STRIP_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN BETA_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Affine forms and their zeros modulo a prime.                              *)
(* ------------------------------------------------------------------------- *)

let PRIME_INT_COPRIME = prove
 (`!p b. prime p /\ ~((&p:int) divides b) ==> coprime(&p,b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&p:int = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`b:int`; `&p:int`] INT_CONG_SOLVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `x:int` INT_OF_NUM_OF_INT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = num_of_int x` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `coprime(&p:int,&r) <=> coprime(&p:int,b)` (SUBST1_TAC o SYM)
  THENL
   [UNDISCH_TAC `((&r:int) == b) (mod &p)` THEN CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM num_coprime] THEN ASM_SIMP_TAC[PRIME_COPRIME_EQ] THEN
  REWRITE_TAC[num_divides] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((&p:int) divides b)` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `((&r:int) == b) (mod &p)` THEN
    UNDISCH_TAC `(&p:int) divides &r` THEN
  CONV_TAC INTEGER_RULE);;

let ONE_VAR_COUNT = prove
 (`!p b c. prime p /\ ~((&p:int) divides b)
           ==> sum {u | u < p} (\u. if (&p:int) divides b * &u + c
                                   then &1 else &0) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&p:int = &0) /\ ~(p = 0)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`p:num`; `b:int`] PRIME_INT_COPRIME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:int. (b * x == --c) (mod &p)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `coprime(&p:int,b)` THEN CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  MP_TAC(SPECL [`x:int`; `&p:int`] INT_CONG_SOLVE_BOUNDS) THEN
  ASM_REWRITE_TAC[INT_ABS_NUM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `y:int` INT_OF_NUM_OF_INT) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `u0 = num_of_int y` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `(u0:num) < p` ASSUME_TAC THENL
   [ASM_MESON_TAC[INT_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u < p ==> ((&p:int) divides b * &u + c <=> u = u0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:num` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(&p:int) divides b * (&u - &u0)` MP_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(&p:int) divides b * &u + c`; `((&u0:int) == x) (mod &p)`;
          `((b:int) * x == --c) (mod &p)`] THEN
        CONV_TAC INTEGER_RULE;
        ALL_TAC] THEN
      ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ] THEN DISCH_TAC THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN MATCH_MP_TAC INT_CONG_IMP_EQ THEN
      EXISTS_TAC `&p:int` THEN CONJ_TAC THENL
       [UNDISCH_TAC `(u:num) < p` THEN UNDISCH_TAC `(u0:num) < p` THEN
        REWRITE_TAC[GSYM INT_OF_NUM_LT] THEN INT_ARITH_TAC;
        UNDISCH_TAC `(&p:int) divides &u - &u0` THEN CONV_TAC INTEGER_RULE];
      DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`((&u0:int) == x) (mod &p)`; `((b:int) * x == --c) (mod &p)`] THEN
      CONV_TAC INTEGER_RULE];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {u:num | u < p} (\u. if u = u0 then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]]);;

let LF_ISUM_EQ = prove
 (`!k (f:A->int) g. FINITE k /\ (!i. i IN k ==> f i = g i)
                    ==> isum k f = isum k g`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES; FORALL_IN_INSERT]);;

let LF_ISUM_ADD = prove
 (`!k (f:A->int) g. FINITE k
                    ==> isum k (\i. f i + g i) = isum k f + isum k g`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES] THEN INT_ARITH_TAC);;

let LF_ISUM_LMUL = prove
 (`!k (f:A->int) c. FINITE k ==> isum k (\i. c * f i) = c * isum k f`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES] THEN INT_ARITH_TAC);;

let LF_ISUM_SUB = prove
 (`!k (f:A->int) g. FINITE k
                    ==> isum k (\i. f i - g i) = isum k f - isum k g`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES] THEN INT_ARITH_TAC);;

let lf_form = new_definition
 `lf_form k (b:num->int) (b0:int) (z:num->num) =
    isum k (\i. b i * &(z i)) + b0`;;

let SUM_CARTESIAN_ONE = prove
 (`!k p. FINITE k
         ==> sum (cartesian_product k (\i:num. {r:num | r < p})) (\x. &1) =
             &p pow CARD k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num->bool`; `\i:num. {r:num | r < p}`;
                 `\i:num r:num. &1`] PRODUCT_SUM_CARTESIAN) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT; PRODUCT_ONE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[PRODUCT_CONST]);;

let LF_FORM_EXTEND = prove
 (`!k a (b:num->int) b0 u (y:num->num).
        FINITE k /\ ~(a IN k)
        ==> lf_form (a INSERT k) b b0 (\i. if i = a then u else y i) =
            b a * &u + lf_form k b b0 y`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[lf_form; ISUM_CLAUSES] THEN
  SUBGOAL_THEN `isum k (\i. (b:num->int) i *
                            &(if i = a then u else (y:num->num) i)) =
                isum k (\i. b i * &(y i))` SUBST1_TAC THENL
   [MATCH_MP_TAC LF_ISUM_EQ THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN
     DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_MESON_TAC[];
    INT_ARITH_TAC]);;

let COUNT_ONE_FORM = prove
 (`!k p (b:num->int) b0 a.
        FINITE k /\ prime p /\ a IN k /\ ~((&p:int) divides b a)
        ==> sum (cartesian_product k (\i. {r | r < p}))
                (\z. if (&p:int) divides lf_form k b b0 z then &1 else &0) =
            &p pow (CARD k - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k = (a:num) INSERT (k DELETE a)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(k DELETE (a:num)) /\ ~(a IN k DELETE a)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CARTESIAN_INSERT; FINITE_NUMSEG_LT; LF_FORM_EXTEND] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[ONE_VAR_COUNT; SUM_CARTESIAN_ONE; CARD_DELETE;
   CARD_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `SUC n - 1 = n`]);;

let LF_FORM_COMB = prove
 (`!k (b:num->int) b0 (b':num->int) b0' c c' (z:num->num).
        FINITE k
        ==> c * lf_form k b' b0' z - c' * lf_form k b b0 z =
            lf_form k (\i. c * b' i - c' * b i) (c * b0' - c' * b0) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lf_form] THEN
  REWRITE_TAC[INT_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[LF_ISUM_SUB; GSYM INT_MUL_ASSOC; LF_ISUM_LMUL] THEN
  INT_ARITH_TAC);;

let COUNT_TWO_FORMS = prove
 (`!k p (b:num->int) b0 (b':num->int) b0' a a'.
        FINITE k /\ prime p /\ a IN k /\ a' IN k /\ ~(a = a') /\
        ~((&p:int) divides b a) /\
        ~((&p:int) divides (b a * b' a' - b a' * b' a))
        ==> sum (cartesian_product k (\i. {r | r < p}))
                (\z. if (&p:int) divides lf_form k b b0 z /\
                        (&p:int) divides lf_form k b' b0' z then &1 else &0) =
            &p pow (CARD k - 2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `bb = \i. (b:num->int) a * b' i - b' a * b i` THEN
  ABBREV_TAC `cc = (b:num->int) a * b0' - b' a * b0` THEN
  SUBGOAL_THEN
   `!z. (&p:int) divides lf_form k b b0 z /\
        (&p:int) divides lf_form k b' b0' z
        <=> (&p:int) divides lf_form k b b0 z /\ (&p:int) divides
          lf_form k bb cc z`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `z:num->num` THEN EXPAND_TAC "bb" THEN EXPAND_TAC "cc" THEN
    ASM_SIMP_TAC[GSYM LF_FORM_COMB] THEN
    ASM_CASES_TAC `(&p:int) divides lf_form k b b0 z` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(&p:int) divides (b:num->int) a * lf_form k b' b0' z` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[PRIME_INT_DIVPROD_EQ]; ALL_TAC] THEN
    UNDISCH_TAC `(&p:int) divides lf_form k b b0 z` THEN
    CONV_TAC INTEGER_RULE;
    ALL_TAC] THEN
  SUBGOAL_THEN `k = (a:num) INSERT (k DELETE a)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(k DELETE (a:num)) /\ ~(a IN k DELETE a) /\
                a' IN k DELETE a`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CARTESIAN_INSERT; FINITE_NUMSEG_LT; LF_FORM_EXTEND] THEN
  SUBGOAL_THEN `(bb:num->int) a = &0` SUBST1_TAC THENL
   [EXPAND_TAC "bb" THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_ADD_LID] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (cartesian_product (k DELETE a) (\i. {r | r < p}))
        (\y. if (&p:int) divides lf_form (k DELETE a) bb cc y then &1
          else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `y:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    ASM_CASES_TAC `(&p:int) divides lf_form (k DELETE a) bb cc y` THEN
    ASM_REWRITE_TAC[SUM_0] THEN ASM_SIMP_TAC[ONE_VAR_COUNT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k DELETE (a:num)`; `p:num`; `bb:num->int`; `cc:int`;
                 `a':num`] COUNT_ONE_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "bb" THEN
    UNDISCH_TAC `~((&p:int) divides ((b:num->int) a * (b':num->int) a' -
                                      b a' * b' a))` THEN
    REWRITE_TAC[INT_MUL_SYM];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE; CARD_CLAUSES] THEN AP_TERM_TAC THEN ARITH_TAC);;

let lf_ncount = new_definition
 `lf_ncount k p (B:num->num->int) (B0:num->int) (J:num->bool) =
    sum (cartesian_product k (\i. {r | r < p}))
        (\z. if (!j. j IN J ==> (&p:int) divides lf_form k (B j) (B0 j) z)
             then &1 else &0)`;;

let lf_pnz = new_definition
 `lf_pnz p k (b:num->int) <=> ?a. a IN k /\ ~((&p:int) divides b a)`;;

let lf_pind = new_definition
 `lf_pind p k (b:num->int) (b':num->int) <=>
    ?a a'. a IN k /\ a' IN k /\ ~(a = a') /\ ~((&p:int) divides b a) /\
           ~((&p:int) divides (b a * b' a' - b a' * b' a))`;;

let LF_NCOUNT_EMPTY = prove
 (`!k p B B0. FINITE k ==> lf_ncount k p B B0 {} = &p pow CARD k`,
  SIMP_TAC[lf_ncount; NOT_IN_EMPTY; SUM_CARTESIAN_ONE]);;

let LF_NCOUNT_SING = prove
 (`!k p B B0 j. FINITE k /\ prime p /\ lf_pnz p k (B j)
                ==> lf_ncount k p B B0 {j} = &p pow (CARD k - 1)`,
  REWRITE_TAC[lf_ncount; lf_pnz; IN_SING; FORALL_UNWIND_THM2] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COUNT_ONE_FORM THEN
  ASM_MESON_TAC[]);;

let LF_NCOUNT_PAIR = prove
 (`!k p B B0 j j'. FINITE k /\ prime p /\ lf_pind p k (B j) (B j')
                   ==> lf_ncount k p B B0 {j,j'} = &p pow (CARD k - 2)`,
  REWRITE_TAC[lf_ncount; lf_pind; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MESON[] `(!x:num. x = a \/ x = b ==> P x) <=> P a /\ P b`] THEN
  MATCH_MP_TAC COUNT_TWO_FORMS THEN ASM_MESON_TAC[]);;

let LF_NCOUNT_POS = prove
 (`!k p B B0 J. &0 <= lf_ncount k p B B0 J`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lf_ncount] THEN MATCH_MP_TAC SUM_POS_LE THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let LF_NCOUNT_MONO = prove
 (`!k p B B0 J J'. FINITE k /\ J SUBSET J'
                   ==> lf_ncount k p B B0 J' <= lf_ncount k p B B0 J`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lf_ncount] THEN MATCH_MP_TAC SUM_LE THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_LE_REFL; REAL_POS] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Products of moduli: the density of a system of congruences.               *)
(* ------------------------------------------------------------------------- *)

let INT_NPRODUCT_DIVIDES = prove
 (`!t n. FINITE t /\ (!p. p IN t ==> prime p)
         ==> ((&(nproduct t (\p. p)):int) divides n <=>
              !p. p IN t ==> (&p:int) divides n)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM INT_DIVIDES_RABS] THEN
  MP_TAC(SPEC `abs n:int` INT_OF_NUM_OF_INT) THEN
  REWRITE_TAC[INT_ABS_POS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM num_divides] THEN
  ASM_SIMP_TAC[GSYM PRIMES_DIVIDE_IFF_NPRODUCT]);;

let LF_FORM_EQ = prove
 (`!k (b:num->int) b0 z z'.
        FINITE k /\ (!i. i IN k ==> z i = z' i)
        ==> lf_form k b b0 z = lf_form k b b0 z'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lf_form] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC LF_ISUM_EQ THEN ASM_SIMP_TAC[]);;

let LF_FORM_MOD = prove
 (`!k p (b:num->int) b0 x.
        FINITE k /\ ~(p = 0)
        ==> ((&p:int) divides lf_form k b b0 x <=>
             (&p:int) divides lf_form k b b0 (\i. x i MOD p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `lf_form k (b:num->int) b0 x - lf_form k b b0 (\i. x i MOD p) =
    &p * isum k (\i. b i * &(x i DIV p))`
  MP_TAC THENL
   [REWRITE_TAC[lf_form; INT_ARITH `(a + c) - (b + c):int = a - b`] THEN
    ASM_SIMP_TAC[GSYM LF_ISUM_SUB; GSYM LF_ISUM_LMUL] THEN
    MATCH_MP_TAC LF_ISUM_EQ THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
    MP_TAC(SPECL [`(x:num->num) i`; `p:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV o
                                          RAND_CONV) [CONJUNCT1 th]) THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
    CONV_TAC INTEGER_RULE]);;

let PRODUCT_INDICATOR = prove
 (`!(P:A->bool) Q. FINITE P
                   ==> product P (\p. if Q p then &1 else &0) =
                       if (!p. p IN P ==> Q p) then &1 else &0`,
  GEN_TAC THEN GEN_TAC THEN SPEC_TAC(`P:A->bool`,`P:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; NOT_IN_EMPTY; FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(Q:A->bool) x` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let DENSITY_CRT = prove
 (`!t P (B:num->num->int) B0 (D:num->num->bool) Js.
        FINITE P /\ (!p. p IN P ==> prime p) /\
        (!j. j IN Js ==> D j SUBSET P)
        ==> sum (cartesian_product {i | i < t}
                                   (\i. {c | c < nproduct P (\p. p)}))
                (\x. if !j. j IN Js
                            ==> (&(nproduct (D j) (\p. p)):int) divides
                                lf_form {i | i < t} (B j) (B0 j) x
                     then &1 else &0) =
            product P (\p. lf_ncount {i | i < t} p B B0
                                  {j | j IN Js /\ p IN D j})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!j. j IN Js ==> FINITE((D:num->num->bool) j) /\
                                (!p. p IN D j ==> prime p)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `!p. p IN P ==> ~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `sum (cartesian_product {i | i < t} (\i. {c | c < nproduct P (\p. p)}))
        (\x. product P
               (\p. (\p z. if !j. j IN {j | j IN Js /\ p IN D j}
                                  ==> (&p:int) divides
                                      lf_form {i | i < t}
                                        ((B:num->num->int) j)
                                        ((B0:num->int) j) z
                           then &1 else &0) p (\i. x i MOD p)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    BETA_TAC THEN ASM_SIMP_TAC[PRODUCT_INDICATOR] THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `!p j. p IN P
            ==> ((&p:int) divides lf_form {i | i < t} ((B:num->num->int) j)
                                         ((B0:num->int) j) (\i. x i MOD p) <=>
                 (&p:int) divides lf_form {i | i < t} (B j) (B0 j) x)`
     (fun th -> ASM_SIMP_TAC[th])
    THENL
     [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC LF_FORM_MOD THEN ASM_SIMP_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_THEN(fun th -> X_GEN_TAC `p:num` THEN DISCH_TAC THEN
        X_GEN_TAC `j:num` THEN STRIP_TAC THEN MP_TAC(SPEC `j:num` th)) THEN
      SUBGOAL_THEN `FINITE((D:num->num->bool) j) /\
                    (!p. p IN D j ==> prime p)` STRIP_ASSUME_TAC
      THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[INT_NPRODUCT_DIVIDES];
      DISCH_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `FINITE((D:num->num->bool) j) /\
                    (!p. p IN D j ==> prime p)` STRIP_ASSUME_TAC
      THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[INT_NPRODUCT_DIVIDES] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:num) IN P` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `p:num` o check (is_forall o concl)) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`t:num`; `P:num->bool`;
    `\p z. if !j. j IN {j | j IN Js /\ p IN (D:num->num->bool) j}
                  ==> (&p:int) divides
                      lf_form {i | i < t} ((B:num->num->int) j) (B0 j) z
           then &1 else &0`] CRT_TUPLE_SUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`p:num`; `z:num->num`; `z':num->num`] THEN
    STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `!j. lf_form {i | i < t} ((B:num->num->int) j)
                            ((B0:num->int) j) z =
                      lf_form {i | i < t} (B j) (B0 j) z'`
    (fun th -> REWRITE_TAC[th]) THEN
    GEN_TAC THEN MATCH_MP_TAC LF_FORM_EQ THEN
    ASM_SIMP_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  REWRITE_TAC[lf_ncount]);;

(* ------------------------------------------------------------------------- *)
(* Residues in intervals and boxes.                                          *)
(* ------------------------------------------------------------------------- *)

let RESIDUE_BLOCK_UNIQUE = prove
 (`!a D x y. a <= x /\ x < a + D /\ a <= y /\ y < a + D /\
             x MOD D = y MOD D ==> x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((x:num) == y) (mod D)` MP_TAC THENL
   [ASM_REWRITE_TAC[CONG]; ALL_TAC] THEN
  REWRITE_TAC[num_congruent] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
    (REWRITE_RULE[IMP_CONJ_ALT] INT_CONG_IMP_EQ)) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN DISCH_THEN MATCH_MP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`(a:num) <= x`; `(x:num) < a + D`; `(a:num) <= y`;
                         `(y:num) < a + D`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_LT;
              GSYM INT_OF_NUM_ADD] THEN INT_ARITH_TAC);;

let CARD_RESIDUE_BLOCK = prove
 (`!a D r. ~(D = 0) /\ r < D
           ==> CARD {x | a <= x /\ x < a + D /\ x MOD D = r} = 1`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {x:num | a <= x /\ x < a + D}` THEN
  SUBGOAL_THEN `FINITE(S:num->bool) /\ CARD S = D` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `S = a..(a + D) - 1` SUBST1_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x. x MOD D) S = {r | r < D}` ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_NUMSEG_LT] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[MOD_LT_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[CARD_NUMSEG_LT] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MESON_TAC[RESIDUE_BLOCK_UNIQUE];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:num) IN IMAGE (\x. x MOD D) S` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{x | a <= x /\ x < a + D /\ x MOD D = r} = {y}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM] THEN
    UNDISCH_TAC `(y:num) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[RESIDUE_BLOCK_UNIQUE];
    REWRITE_TAC[CARD_SING]]);;

let CARD_RESIDUE_BLOCKS = prove
 (`!q a D r. ~(D = 0) /\ r < D
             ==> CARD {x | a <= x /\ x < a + q * D /\ x MOD D = r} = q`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD({}:num->bool)` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      ARITH_TAC;
      REWRITE_TAC[CARD_CLAUSES]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | a <= x /\ x < a + SUC q * D /\ x MOD D = r} =
    {x | a <= x /\ x < a + D /\ x MOD D = r} UNION
    {x | (a + D) <= x /\ x < (a + D) + q * D /\ x MOD D = r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; MULT_CLAUSES] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < a + D}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:num | x < (a + D) + q * D}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
       NOT_IN_EMPTY] THEN
      ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CARD_RESIDUE_BLOCK] THEN ARITH_TAC);;

let CARD_RESIDUE_SHORT = prove
 (`!b s D r. s <= D /\ ~(D = 0) /\ r < D
             ==> CARD {x | b <= x /\ x < b + s /\ x MOD D = r} <= 1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {x | b <= x /\ x < b + D /\ x MOD D = r}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < b + D}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]];
    ASM_SIMP_TAC[CARD_RESIDUE_BLOCK; LE_REFL]]);;

let COUNT_RESIDUE_INTERVAL = prove
 (`!a M D r. ~(D = 0) /\ r < D
             ==> abs(&(CARD {x | a <= x /\ x < a + M /\ x MOD D = r}) -
                     &M / &D) <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`M:num`; `D:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = M DIV D` THEN ABBREV_TAC `s = M MOD D` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | a <= x /\ x < a + M /\ x MOD D = r} =
    {x | a <= x /\ x < a + q * D /\ x MOD D = r} UNION
    {x | (a + q * D) <= x /\ x < (a + q * D) + s /\ x MOD D = r}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CARD_UNION o rand o lhand o
    rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{x:num | x < a + q * D}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:num | x < (a + q * D) + s}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
       NOT_IN_EMPTY] THEN
      ARITH_TAC];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CARD_RESIDUE_BLOCKS] THEN
  MP_TAC(SPECL [`(a:num) + q * D`; `s:num`; `D:num`; `r:num`]
         CARD_RESIDUE_SHORT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
  SPEC_TAC(`CARD {x | a + q * D <= x /\ x < (a + q * D) + s /\ x MOD D = r}`,
           `e:num`) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&(q * D) + &s) / &D = &q + &s / &D /\ &0 <= &s / &D /\
                &s / &D < &1`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &D` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_LT_LDIV_EQ; REAL_MUL_LID;
                 REAL_OF_NUM_LT] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < &D` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&e <= &1` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(&(q * D) + &s) / &D = &q + &s / &D`; `&0 <= &s / &D`;
    `&s / &D < &1`] THEN
  REAL_ARITH_TAC);;

let lf_box = new_definition
 `lf_box t (a:num->num) (M:num->num) =
    cartesian_product {i | i < t} (\i. {x | a i <= x /\ x < a i + M i})`;;

let FINITE_LF_BOX = prove
 (`!t a M. FINITE(lf_box t a M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lf_box] THEN
  MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x:num | x < a(i:num) + M i}` THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[]);;

let SUM_CARTESIAN_CARD = prove
 (`!k (s:num->num->bool).
        FINITE k /\ (!i. i IN k ==> FINITE(s i))
        ==> sum (cartesian_product k s) (\x. &1) =
            product k (\i. &(CARD(s i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num->bool`; `s:num->num->bool`; `\i:num r:num. &1`]
         PRODUCT_SUM_CARTESIAN) THEN
  ASM_REWRITE_TAC[PRODUCT_ONE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC PRODUCT_EQ THEN ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RID]);;

let LF_BOX_SUM_RESIDUES = prove
 (`!t a M D (g:(num->num)->real).
        ~(D = 0) /\
        (!x. x IN lf_box t a M
             ==> g x = g (\i. if i < t then x i MOD D else ARB))
        ==> sum (lf_box t a M) g =
            sum (cartesian_product {i | i < t} (\i. {r | r < D}))
                (\z. g z *
                     product {i | i < t}
                       (\i. &(CARD {x | a i <= x /\ x < a i + M i /\
                                        x MOD D = z i})))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `f = \x:num->num. \i. if i < t then x i MOD D else ARB` THEN
  MP_TAC(ISPECL [`f:(num->num)->(num->num)`; `g:(num->num)->real`;
                 `lf_box t a M`;
                 `cartesian_product {i:num | i < t} (\i. {r:num | r < D})`]
         SUM_GROUP) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_LF_BOX] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; lf_box; cartesian_product;
                IN_ELIM_THM; EXTENSIONAL] THEN
    X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN EXPAND_TAC "f" THEN
    ASM_SIMP_TAC[MOD_LT_EQ];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `z:num->num` THEN DISCH_TAC THEN
  BETA_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {x | x IN lf_box t a M /\ (f:(num->num)->(num->num)) x = z}
                  (\x. (g:(num->num)->real) z)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `x:num->num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num->num` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(f:(num->num)->(num->num)) x = z` THEN EXPAND_TAC "f" THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{x | x IN lf_box t a M /\ (f:(num->num)->(num->num)) x = z} =
    cartesian_product {i | i < t}
      (\i. {x | a i <= x /\ x < a i + M i /\ x MOD D = z i})`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(z:num->num) IN cartesian_product {i:num | i < t}
                                    (\i. {r:num | r < D})` THEN
    EXPAND_TAC "f" THEN
    REWRITE_TAC[lf_box; cartesian_product; EXTENSIONAL; IN_ELIM_THM;
                EXTENSION; FUN_EQ_THM] THEN
    STRIP_TAC THEN X_GEN_TAC `x:num->num` THEN EQ_TAC THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(X_GEN_TAC `i:num`) THEN
    TRY(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    TRY(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    TRY(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    ASM_CASES_TAC `(i:num) < t` THEN ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:num. FINITE {x | a i <= x /\ x < a i + M i /\ x MOD D = z i}`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{x:num | x < a(i:num) + M i}` THEN
    REWRITE_TAC[FINITE_NUMSEG_LT] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{i:num | i < t}`;
                 `\i:num. {x | a i <= x /\ x < a i + M i /\
                              x MOD D = (z:num->num) i}`]
                SUM_CARTESIAN_CARD) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `FINITE(cartesian_product {i:num | i < t}
             (\i. {x | a i <= x /\ x < a i + M i /\
                       x MOD D = (z:num->num) i}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_SYM]);;

let PRODUCT_PERTURB = prove
 (`!k (c:A->real) m.
        FINITE k /\ (!i. i IN k ==> &0 <= m i /\ abs(c i - m i) <= &1)
        ==> abs(product k c - product k m) <=
            product k (\i. m i + &1) - product k m`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`k:A->bool`,`k:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[PRODUCT_CLAUSES; FORALL_IN_INSERT] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `k:A->bool`] THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs(product k (c:A->real)) <= product k (\i. m i + &1)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_ABS] THEN MATCH_MP_TAC PRODUCT_LE THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:A` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= product k (\i. (m:A->real) i + &1) - product k m`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_POS; REAL_LE_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((c:A->real) a - m a) * abs(product k c) +
              m a * abs(product k c - product k m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `abs((c - m) * p) <= x /\ abs(m * (p - q)) <= y /\
      c * p - m * q = (c - m) * p + m * (p - q)
      ==> abs(c * p - m * q) <= x + y`) THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&1 * product k (\i. (m:A->real) i + &1) +
              m a * (product k (\i. m i + &1) - product k m)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; REAL_LE_REFL];
    REAL_ARITH_TAC]);;

let LF_BOX_APPROX = prove
 (`!t a M D (g:(num->num)->real).
        ~(D = 0) /\
        (!x. x IN lf_box t a M
             ==> g x = g (\i. if i < t then x i MOD D else ARB))
        ==> abs(sum (lf_box t a M) g -
                product {i | i < t} (\i. &(M i) / &D) *
                sum (cartesian_product {i | i < t} (\i. {r | r < D})) g)
            <= (product {i | i < t} (\i. &(M i) / &D + &1) -
                product {i | i < t} (\i. &(M i) / &D)) *
               sum (cartesian_product {i | i < t} (\i. {r | r < D}))
                   (\z. abs(g z))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LF_BOX_SUM_RESIDUES] THEN
  ABBREV_TAC `C = cartesian_product {i:num | i < t} (\i. {r:num | r < D})` THEN
  SUBGOAL_THEN `FINITE(C:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM SUM_LMUL; GSYM SUM_SUB] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum C (\z. abs((g:(num->num)->real) z) *
                         (product {i:num | i < t} (\i. &(M i) / &D + &1) -
                          product {i:num | i < t} (\i. &(M i) / &D)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_ABS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:num->num` THEN DISCH_TAC THEN BETA_TAC THEN
    REWRITE_TAC[REAL_ARITH `x * p - m * x:real = x * (p - m)`] THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_ABS_POS] THEN MATCH_MP_TAC PRODUCT_PERTURB THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    MATCH_MP_TAC COUNT_RESIDUE_INTERVAL THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:num->num) IN C` THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[SUM_RMUL; REAL_MUL_SYM; REAL_LE_REFL]]);;
