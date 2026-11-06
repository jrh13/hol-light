(* ========================================================================= *)
(* Additive characters e(x) and Gauss sums.                                  *)
(*                                                                           *)
(* expi x = e(x) = exp(2 pi i x); VSUM_EXPI_RESIDUES evaluates the complete  *)
(* sums sum_{a < q} e(x a / q) for integer x (q or 0).                       *)
(* gauss_sum q c n = sum_{a < q} c(a) e(a n / q), and for a primitive        *)
(* character c mod q:                                                        *)
(*   GAUSS_SUM_SEPARABLE  gauss_sum q c n = cnj(c n) gauss_sum q c 1 (all n) *)
(*   GAUSS_SUM_NORM       |gauss_sum q c 1|^2 = q.                           *)
(*                                                                           *)
(* Method.  For (n,q) = 1 substitute a -> n a on the residues mod q          *)
(* (VSUM_OVER_RESIDUES_MUL).  For (n,q) = g > 1 primitivity gives a unit     *)
(* c0 == 1 (mod q/g) with c(c0) <> 1, and a -> c0 a fixes e(a n / q), so     *)
(* the sum vanishes.  Then tau cnj(tau) = sum_b e(-b/q) gauss_sum q c b =    *)
(* sum_a c(a) sum_b e((a - 1) b / q) = q c(1).                               *)
(* ========================================================================= *)

needs "Sieve/characters.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The additive character e(x).                                              *)
(* ------------------------------------------------------------------------- *)

let expi = new_definition
 `expi x = cexp(Cx(&2 * x * pi) * ii)`;;

let EXPI_ADD = prove
 (`!x y. expi(x + y) = expi x * expi y`,
  REWRITE_TAC[expi; GSYM CEXP_ADD] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_RDISTRIB; GSYM CX_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let EXPI_0 = prove
 (`expi(&0) = Cx(&1)`,
  REWRITE_TAC[expi; REAL_MUL_LZERO; REAL_MUL_RZERO; COMPLEX_MUL_LZERO;
              CEXP_0]);;

let EXPI_INTEGER = prove
 (`!x. integer x ==> expi x = Cx(&1)`,
  REWRITE_TAC[expi; CEXP_INTEGER_2PI]);;

let EXPI_EQ_1 = prove
 (`!x. expi x = Cx(&1) <=> integer x`,
  GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[EXPI_INTEGER] THEN
  REWRITE_TAC[expi; CEXP_EQ_1; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[REAL_NEG_0] THEN DISCH_THEN(X_CHOOSE_THEN `n:real`
    STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x:real = n` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC PI_POS THEN UNDISCH_TAC `&2 * x * pi = &2 * n * pi` THEN
  CONV_TAC REAL_FIELD);;

let NORM_EXPI = prove
 (`!x. norm(expi x) = &1`,
  REWRITE_TAC[expi; NORM_CEXP; RE_MUL_II; IM_CX; REAL_NEG_0; REAL_EXP_0]);;

let CNJ_EXPI = prove
 (`!x. cnj(expi x) = expi(--x)`,
  REWRITE_TAC[expi; CNJ_CEXP; CNJ_MUL; CNJ_CX; CNJ_II] THEN
  GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 * --x * pi = --(&2 * x * pi)`; CX_NEG] THEN
  CONV_TAC COMPLEX_RING);;

let EXPI_NUM_MUL = prove
 (`!n x. expi(&n * x) = expi x pow n`,
  REWRITE_TAC[expi; GSYM CEXP_N] THEN REPEAT GEN_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM CX_MUL; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let EXPI_INTEGER_ADD = prove
 (`!x y. integer y ==> expi(x + y) = expi x`,
  SIMP_TAC[EXPI_ADD; EXPI_INTEGER; COMPLEX_MUL_RID]);;

let VSUM_EXPI_RESIDUES = prove
 (`!q x. ~(q = 0) /\ integer x
         ==> vsum {a | a < q} (\a. expi(x * &a / &q)) =
             if integer(x / &q) then Cx(&q) else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a | a < q} = 0..q-1` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a. expi(x * &a / &q) = expi(x / &q) pow a` (fun th ->
    REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM EXPI_NUM_MUL] THEN AP_TERM_TAC THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VSUM_GP] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[EXPI_INTEGER; GSYM EXPI_EQ_1] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[EXPI_EQ_1]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SUC(q - 1) = q` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM EXPI_NUM_MUL; complex_pow] THEN
  SUBGOAL_THEN `&q * x / &q = x` SUBST1_TAC THENL
   [UNDISCH_TAC `~(q = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ASM_SIMP_TAC[EXPI_INTEGER; COMPLEX_SUB_REFL; complex_div;
                 COMPLEX_MUL_LZERO; REAL_MUL_LZERO; EXPI_0]]);;

let ITERATE_OVER_RESIDUES_MUL = prove
 (`!op (f:num->V) n k.
        monoidal(op) /\ coprime(k,n) /\
        (!x y. (x == y) (mod n) ==> f x = f y)
        ==> iterate op {d | d < n} (\m. f(k * m)) =
            iterate op {d | d < n} f`,
  let lemma = prove
   (`~(n = 0) ==> ((a * x MOD n == b) (mod n) <=> (a * x == b) (mod n))`,
    MESON_TAC[CONG_REFL; CONG_SYM; CONG_TRANS; CONG_MULT; CONG_MOD]) in
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [ASM_SIMP_TAC[LT; SET_RULE `{x:num | F} = {}`; ITERATE_CLAUSES];
    ALL_TAC] THEN
  STRIP_TAC THEN SUBGOAL_THEN `?m. (k * m == 1) (mod n)` CHOOSE_TAC THENL
   [ASM_MESON_TAC[CONG_SOLVE; MULT_SYM; CONG_SYM]; ALL_TAC] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP ITERATE_EQ_GENERAL_INVERSES) THEN
  MAP_EVERY EXISTS_TAC [`\x. (k * x) MOD n`; `\x. (m * x) MOD n`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_SIMP_TAC[CONG_MOD_LT; CONG_LMOD; DIVISION; lemma] THEN
  REPEAT STRIP_TAC THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[CONG_LMOD]) THEN
  UNDISCH_TAC `(k * m == 1) (mod n)` THEN CONV_TAC NUMBER_RULE);;

let VSUM_OVER_RESIDUES_MUL = prove
 (`!(f:num->complex) n k.
        coprime(k,n) /\ (!x y. (x == y) (mod n) ==> f x = f y)
           ==> vsum {d | d < n} (\m. f(k * m)) = vsum {d | d < n} f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {d:num | d < n}` ASSUME_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM] THEN MATCH_MP_TAC ITERATE_OVER_RESIDUES_MUL THEN
  ASM_REWRITE_TAC[MONOIDAL_VECTOR_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Gauss sums.                                                               *)
(* ------------------------------------------------------------------------- *)

let gauss_sum = new_definition
 `gauss_sum q (c:num->complex) n =
    vsum {a | a < q} (\a. c a * expi(&a * &n / &q))`;;

let EXPI_INTEGER_DIFF = prove
 (`!x y. integer(x - y) ==> expi x = expi y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `x = y + (x - y:real)` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ASM_SIMP_TAC[EXPI_INTEGER_ADD]]);;

let CONG_INTEGER_QUOTIENT = prove
 (`!q a b. ~(q = 0) /\ (a == b) (mod q) ==> integer((&a - &b) / &q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[CONG_CASES] THEN
  SUBGOAL_THEN `~(&q = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_EQ]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `t:num` SUBST1_TAC)) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THENL
   [SUBGOAL_THEN `((&t * &q + &b) - &b) / &q = &t` SUBST1_TAC THENL
     [UNDISCH_TAC `~(&q = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC];
    SUBGOAL_THEN `(&a - (&t * &q + &a)) / &q = --(&t)` SUBST1_TAC THENL
     [UNDISCH_TAC `~(&q = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC]] THEN
  SIMP_TAC[INTEGER_CLOSED]);;

let EXPI_CONG = prove
 (`!q a b n. ~(q = 0) /\ (a == b) (mod q)
             ==> expi(&a * &n / &q) = expi(&b * &n / &q)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EXPI_INTEGER_DIFF THEN
  SUBGOAL_THEN `&a * &n / &q - &b * &n / &q = ((&a - &b) / &q) * &n`
  SUBST1_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `integer((&a - &b) / &q)` MP_TAC THENL
   [ASM_SIMP_TAC[CONG_INTEGER_QUOTIENT]; ALL_TAC] THEN
  MESON_TAC[INTEGER_CLOSED]);;

let GAUSS_SUM_COPRIME = prove
 (`!q c n. dirichlet_character q c /\ ~(q = 0) /\ coprime(n,q)
           ==> gauss_sum q c n = cnj(c n) * gauss_sum q c 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\a. (c:num->complex) a * expi(&a * &1 / &q)`;
                 `q:num`; `n:num`] VSUM_OVER_RESIDUES_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BINOP_TAC THENL
     [ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG];
      MATCH_MP_TAC EXPI_CONG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM gauss_sum] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  SUBGOAL_THEN
   `!m. expi(&(n * m) * &1 / &q) = expi(&m * &n / &q)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM gauss_sum; COMPLEX_MUL_ASSOC] THEN
  SUBGOAL_THEN `cnj((c:num->complex) n) * c n = Cx(&1)`
    (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LID]) THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_NORM th]) THEN
  SUBGOAL_THEN `coprime(q:num,n)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[COPRIME_SYM]; REWRITE_TAC[COMPLEX_POW_ONE]]);;

let GAUSS_SUM_NONCOPRIME = prove
 (`!q c n. primitive_character q c /\ ~(q = 0) /\ ~coprime(n,q)
           ==> gauss_sum q c n = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [primitive_character]) THEN
  ABBREV_TAC `g = gcd(n:num,q)` THEN
  SUBGOAL_THEN `g divides n /\ g divides q /\ ~(g = 1) /\ ~(g = 0)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[GCD; GSYM COPRIME_GCD] THEN
    ASM_REWRITE_TAC[GCD_ZERO] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q1 = q DIV g` THEN
  SUBGOAL_THEN `(q1:num) * g = q` ASSUME_TAC THENL
   [EXPAND_TAC "q1" THEN REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q1:num) divides q /\ ~(q1 = q) /\ ~(q1 = 0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
        check (fun th -> rhs(concl th) = `q:num`)) THEN
      CONV_TAC NUMBER_RULE;
      DISCH_TAC THEN UNDISCH_TAC `(q1:num) * g = q` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE `(q:num) * g = q <=> q * g = q * 1`] THEN
      ASM_REWRITE_TAC[EQ_MULT_LCANCEL];
      DISCH_TAC THEN UNDISCH_TAC `(q1:num) * g = q` THEN
      ASM_REWRITE_TAC[MULT_CLAUSES] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q1:num` o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`\a. (c:num->complex) a * expi(&a * &n / &q)`;
                 `q:num`; `c0:num`] VSUM_OVER_RESIDUES_MUL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN BINOP_TAC THENL
     [ASM_MESON_TAC[DIRICHLET_CHARACTER_CONG];
      MATCH_MP_TAC EXPI_CONG THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM gauss_sum] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_MUL th]) THEN
  SUBGOAL_THEN
   `!m. expi(&(c0 * m) * &n / &q) = expi(&m * &n / &q)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC EXPI_INTEGER_DIFF THEN
    SUBGOAL_THEN `integer((&c0 - &1) / &q1) /\ integer(&n / &g)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONG_INTEGER_QUOTIENT THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(g:num) divides n` THEN REWRITE_TAC[divides] THEN
        DISCH_THEN(X_CHOOSE_THEN `v:num` SUBST1_TAC) THEN
        SUBGOAL_THEN `&(g * v) / &g = &v` (fun th ->
          REWRITE_TAC[th; INTEGER_CLOSED]) THEN
        UNDISCH_TAC `~(g = 0)` THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&(c0 * m) * &n / &q - &m * &n / &q =
      &m * ((&c0 - &1) / &q1) * (&n / &g)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        rhs(concl th) = `q:num`)) THEN
      MAP_EVERY UNDISCH_TAC [`~(q1 = 0)`; `~(g = 0)`] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM REAL_OF_NUM_MUL] THEN
      CONV_TAC REAL_FIELD;
      ASM_MESON_TAC[INTEGER_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[GSYM gauss_sum] THEN
  UNDISCH_TAC `~((c:num->complex) c0 = Cx(&1))` THEN
  CONV_TAC COMPLEX_RING);;

let GAUSS_SUM_SEPARABLE = prove
 (`!q c n. primitive_character q c /\ ~(q = 0)
           ==> gauss_sum q c n = cnj(c n) * gauss_sum q c 1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [primitive_character]) THEN
  ASM_CASES_TAC `coprime(n:num,q)` THENL
   [ASM_SIMP_TAC[GAUSS_SUM_COPRIME];
    ASM_SIMP_TAC[GAUSS_SUM_NONCOPRIME] THEN
    SUBGOAL_THEN `(c:num->complex) n = Cx(&0)` SUBST1_TAC THENL
     [ASM_MESON_TAC[DIRICHLET_CHARACTER_EQ_0];
      REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LZERO]]]);;
let INTEGER_QUOTIENT_CONG = prove
 (`!q a b. ~(q = 0) ==> (integer((&a - &b) / &q) <=> (a == b) (mod q))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[CONG_INTEGER_QUOTIENT]] THEN
  REWRITE_TAC[integer; CONG_CASES] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:num`) THEN
  SUBGOAL_THEN `abs(&a - &b) = &m * &q` MP_TAC THENL
   [UNDISCH_TAC `abs((&a - &b) / &q) = &m` THEN
    REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
    UNDISCH_TAC `~(q = 0)` THEN REWRITE_TAC[GSYM REAL_OF_NUM_EQ] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `abs(x - y) = z ==> x = z + y \/ y = z + x`)) THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_EQ] THEN
  MESON_TAC[]);;

let GAUSS_SUM_NORM = prove
 (`!q c. primitive_character q c /\ ~(q = 0)
         ==> norm(gauss_sum q c 1) pow 2 = &q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `gauss_sum q c 1 * cnj(gauss_sum q c 1) = Cx(&q)` MP_TAC THENL
   [ALL_TAC; REWRITE_TAC[COMPLEX_MUL_CNJ; GSYM CX_POW; CX_INJ]] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [gauss_sum] THEN
  SIMP_TAC[CNJ_VSUM; FINITE_NUMSEG_LT; CNJ_MUL; CNJ_EXPI] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN
   `!b. gauss_sum q c 1 * cnj(c b) * expi(--(&b * &1 / &q)) =
        vsum {a | a < q} (\a. c a * expi((&a - &1) * &b / &q))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [COMPLEX_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM GAUSS_SUM_SEPARABLE] THEN
    REWRITE_TAC[gauss_sum] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM EXPI_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\b a. (c:num->complex) a * expi((&a - &1) * &b / &q)`;
                 `{b:num | b < q}`; `{a:num | a < q}`] VSUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[VSUM_COMPLEX_LMUL; FINITE_NUMSEG_LT] THEN
  ASM_SIMP_TAC[VSUM_EXPI_RESIDUES; INTEGER_CLOSED; INTEGER_QUOTIENT_CONG] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [primitive_character]) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
   `vsum {a | a < q} (\a. if a = 1 MOD q then Cx(&q) else vec 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:num` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a == 1) (mod q) <=> a = 1 MOD q` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CONG; MOD_LT]; ALL_TAC] THEN
    COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_VEC_0] THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    SUBGOAL_THEN `(c:num->complex) (1 MOD q) = c 1` SUBST1_TAC THENL
     [MATCH_MP_TAC DIRICHLET_CHARACTER_CONG THEN
      EXISTS_TAC `q:num` THEN ASM_REWRITE_TAC[CONG_LMOD; CONG_REFL];
      FIRST_ASSUM(fun th ->
        REWRITE_TAC[MATCH_MP DIRICHLET_CHARACTER_EQ_1 th]) THEN
      REWRITE_TAC[COMPLEX_MUL_LID]];
    REWRITE_TAC[VSUM_DELTA; IN_ELIM_THM] THEN ASM_REWRITE_TAC[MOD_LT_EQ]]);;

let GAUSS_SUM_CHARACTER_SUM = prove
 (`!q c N (a:num->complex).
     primitive_character q c /\ ~(q = 0)
     ==> gauss_sum q (\n. cnj(c n)) 1 * vsum(1..N) (\n. a n * c n) =
         vsum {b | b < q}
           (\b. cnj(c b) * vsum(1..N) (\n. a n * expi(&n * &b / &q)))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PRIMITIVE_CHARACTER_CNJ) THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `!n. gauss_sum q (\n. cnj(c n)) 1 * a n * (c:num->complex) n =
        a n * gauss_sum q (\n. cnj(c n)) n`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`q:num`; `\n. cnj((c:num->complex) n)`; `n:num`]
      GAUSS_SUM_SEPARABLE) THEN
    ASM_REWRITE_TAC[CNJ_CNJ] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[gauss_sum] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
  MP_TAC(ISPECL
   [`\n b. (a:num->complex) n * cnj((c:num->complex) b) *
           expi(&b * &n / &q)`;
    `1..N`; `{b:num | b < q}`] VSUM_SWAP) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `b:num` THEN DISCH_TAC THEN
  BETA_TAC THEN MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN BETA_TAC THEN
  SUBGOAL_THEN `&b * &n / &q = &n * &b / &q` SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; CONV_TAC COMPLEX_RING]);;
