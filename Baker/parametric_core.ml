(* ========================================================================= *)
(* The parametric core of the Baker method.                                  *)
(*                                                                           *)
(* Purpose: Baker, Transcendental Number Theory, Ch. 3: Lemmas 4-7 and       *)
(* sec. 4 assembled into one parametric contradiction. Given                 *)
(*  - algebraic theta r = cexp(lg r) (r = 1..n) with explicit integer        *)
(*    polynomials of degree d r and height H r, and no nontrivial integer    *)
(*    relation b 1 lg 1 + ... + b n lg n = 0 with all |b r| <= L (only such  *)
(*    small relations are produced by sec. 4, BAKER_INTEGER_RELATION);       *)
(*  - beta j = --(g j theta) / g n theta with intpoly V e G (g j);           *)
(*  - natural number parameters h, L, k (Siegel), R, S, rho, J (Lemma 6),    *)
(*    X7, rhoX (Lemma 7) and reals eps, Bb, Lam, d0, lmin, Gn,               *)
(* satisfying the numeric inequalities stated with the bound functions       *)
(* below, one gets F. Here d0 bounds |beta 0 + sum beta r lg r - lg n| =     *)
(* |Lambda| / |g n|; the numeric layer Baker/param.ml chooses the            *)
(* parameters.                                                               *)
(* Bound functions: baker_ub (size of the auxiliary function F_m on a        *)
(* disc), baker_err (F_m minus its algebraic counterpart), baker_pbound      *)
(* (Siegel height of the coefficients p), baker_nmax (common multiple of     *)
(* l+1..l+h), baker_liou5 / baker_liou7 (Liouville lower bounds of Lemmas    *)
(* 5 and 7) and baker_vb (the gap of the Lemma 6 dichotomy).                 *)
(*                                                                           *)
(* Main results: BAKER_DICHOTOMY (Lemma 5 as a dichotomy: at an integer      *)
(* point l <= Rm the auxiliary function is either <= baker_err or            *)
(* >= baker_vb), BAKER_CORE_PARAMETRIC (the parametric contradiction,        *)
(* used by BAKER_CORE_NUMERIC in Baker/param.ml).                            *)
(*                                                                           *)
(* Uses: Baker/aux_arith.ml (BAKER_LEMMA4_ARITH, BAKER_LEMMA5_ARITH,         *)
(* BAKER_LEMMA7_ARITH, BAKER_ALG_ZERO, CARD_BAKER_INDEX), Baker/extrap.ml    *)
(* (EXTRAPOLATION_INDUCTION, RATIONAL_EXTRAPOLATION_ALL), Baker/bounds.ml    *)
(* (BAKER_AUX_EXP_BOUND, BAKER_APPROX_EXP_BOUND, LIOUVILLE_EXP_LOWER,        *)
(* LIOUVILLE_EXP_LOWER_MONO), Baker/sec4.ml (BAKER_INTEGER_RELATION),        *)
(* Baker/auxiliary.ml (baker_aux, baker_alg and their holomorphy and         *)
(* derivatives), Baker/delta.ml (NUMSEG_COMMON_MULTIPLE,                     *)
(* SHIFTED_COMMON_MULTIPLE_BOUND), Baker/intpoly.ml (intpoly),               *)
(* Library/products.ml (REAL_POW_NSUM), Baker/lemmas.ml (REAL_LE_1_MUL).     *)
(* ========================================================================= *)

needs "Baker/extrap.ml";;
needs "Baker/sec4.ml";;
needs "Baker/bounds.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The bound functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let baker_ub = new_definition
 `baker_ub n h L k P Bb Lam N =
    P * exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
            &(2 * k) * log(&2 * &k * Bb * Lam) + &N * &L * (Lam + &1))`;;

let baker_err = new_definition
 `baker_err n h L k P Bb Lam d0 N =
    P * exp(&h + &(n + 1) * &L + &(L + 2) * &(N + h) +
            &(2 * k) * log(&2 * &k * Bb * Lam) + &N * &L * Lam) *
    (&N * &L * d0 * exp(&N * &L * d0))`;;

let baker_pbound = new_definition
 `baker_pbound n h L k V G (H:num->real) (e:num->num) =
    &(CARD(baker_index h L n)) *
    max (&1)
     ((exp(&36 * &h) pow k * &2 pow ((L + 2) * ((h + 1) + h)) *
       (&k + &1) pow k * (&2 * &L * G) pow k) *
      product V (\r. (&2 * H r) pow
                     ((if r IN 1..n then L * h else 0) + k * e r)))`;;

let baker_nmax = new_definition
 `baker_nmax h R = (exp(&19) * (&R + &h) / &h) pow h`;;

let baker_liou5 = new_definition
 `baker_liou5 n h L k V G (H:num->real) (e:num->num) (d:num->num) P R =
    exp(--(&(nproduct V d) *
           (log(&(nproduct V d)) +
            log(&(CARD(baker_index h L n)) * P *
                (baker_nmax h R pow k * &2 pow ((L + 2) * ((R + 1) + h)) *
                 (&k + &1) pow k * (&2 * &L * G) pow k)) +
            sum V (\r. &((if r IN 1..n then L * R else 0) + k * e r) *
                       log(&(d r + 1) * H r pow 3)))))`;;

let baker_liou7 = new_definition
 `baker_liou7 n h L k (d:num->num) (H:num->real) P X7 lmax =
    exp(--(&(nproduct(1..n) (\r. k * d r)) *
           (log(&(nproduct(1..n) (\r. k * d r))) +
            log(&(CARD(baker_index h L n)) *
                (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))) +
            sum(1..n) (\r. &(L * lmax) * log(&(k * d r + 1) * H r pow 3)))))`;;

let baker_vb = new_definition
 `baker_vb n h L k V G (H:num->real) (e:num->num) (d:num->num) P Bb Lam d0
           lmin Gn R =
    lmin pow k * baker_liou5 n h L k V G H e d P R /
    (baker_nmax h R pow k * Gn pow k) -
    baker_err n h L k P Bb Lam d0 (R + 1)`;;

(* ------------------------------------------------------------------------- *)
(* Lemma 5 in dichotomy form: at an integer point l <= Rm the auxiliary      *)
(* function is either tiny (its algebraic counterpart vanishes) or at least  *)
(* baker_vb (Liouville applied to the nonzero algebraic counterpart).        *)
(* ------------------------------------------------------------------------- *)

let CPRODUCT_LG_POW_LOWER = prove
 (`!n (lg:num->complex) m k lmin.
        1 <= n /\ &0 < lmin /\ lmin <= &1 /\
        (!r. r IN 1..n ==> lmin <= norm(lg r)) /\ nsum(0..n-1) m <= k
        ==> lmin pow k <= norm(cproduct(1..n-1) (\r. lg r pow (m r)))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[NORM_CPRODUCT; FINITE_NUMSEG] THEN
  REWRITE_TAC[COMPLEX_NORM_POW] THEN
  TRANS_TAC REAL_LE_TRANS `lmin pow (nsum(1..n-1) m)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    TRANS_TAC LE_TRANS `nsum(0..n-1) m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NSUM_SUBSET_SIMPLE THEN
    REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_NUMSEG] THEN ARITH_TAC;
    SIMP_TAC[REAL_POW_NSUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC]);;

let NORM_LOWER_FROM_APPROX = prove
 (`!A er (f:complex) u. A <= norm u /\ norm(f - u) <= er ==> A - er <= norm f`,
  NORM_ARITH_TAC);;

let BAKER_DICHOTOMY = prove
 (`!n lg theta V (g:num->(num->complex)->complex) e G a d H beta h L k p P
    Bb Lam d0 lmin Gn Rm l m.
    1 <= n /\ 1 <= L /\ L <= k /\ 1 <= h /\ &1 <= G /\ FINITE V /\
    (1..n) SUBSET V /\
    (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
    (!j. j <= n ==> intpoly V e G (g j)) /\
    ~(g n theta = Cx(&0)) /\ norm(g n theta) <= Gn /\ &1 <= Gn /\
    (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
    (!r. r IN V
         ==> 1 <= d r /\ &1 <= H r /\
             (!j. integer(a r j) /\ abs(a r j) <= H r) /\
             ~(a r (d r) = &0) /\
             vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
    (!x. x IN baker_index h L n ==> integer(p x) /\ abs(p x) <= P) /\
    &1 <= P /\
    &1 <= Bb /\ (!j. j < n ==> norm(beta j) <= Bb) /\
    &1 <= Lam /\ (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
    sum(1..n) (\r. norm(lg r)) <= Lam /\
    &0 < lmin /\ lmin <= &1 /\ (!r. r IN 1..n ==> lmin <= norm(lg r)) /\
    &0 <= d0 /\
    norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) <= d0 /\
    l <= Rm /\ nsum(0..n-1) m <= k
    ==> norm(baker_aux n h L p beta lg m (Cx(&l))) <=
        baker_err n h L k P Bb Lam d0 (Rm + 1) \/
        baker_vb n h L k V G H e d P Bb Lam d0 lmin Gn Rm <=
        norm(baker_aux n h L p beta lg m (Cx(&l)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L:num`; `k:num`;
                 `p:num#num#(num->num)->real`; `beta:num->complex`;
                 `lg:num->complex`; `m:num->num`; `Cx(&l)`; `Rm + 1`;
                 `P:real`; `Bb:real`; `Lam:real`; `d0:real`]
         BAKER_APPROX_EXP_BOUND) THEN
  ASM_SIMP_TAC[REAL_ARITH `&1 <= P ==> &0 <= P`; COMPLEX_NORM_CX;
               REAL_ABS_NUM; REAL_OF_NUM_ADD; REAL_OF_NUM_LE;
               LE_ADD_RCANCEL] THEN
  REWRITE_TAC[GSYM baker_err] THEN DISCH_THEN(LABEL_TAC "approx") THEN
  ASM_CASES_TAC `baker_alg n h L p beta lg m (Cx(&l)) = Cx(&0)` THENL
   [DISJ1_TAC THEN REMOVE_THEN "approx" MP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO];
    DISJ2_TAC] THEN
  MP_TAC(SPECL [`l:num`; `h:num`] SHIFTED_COMMON_MULTIPLE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Nl:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= &Nl /\ &Nl <= baker_nmax h Rm` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= x <=> ~(x = 0)`];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(exp(&19) * (&l + &h) / &h) pow h` THEN
    ASM_REWRITE_TAC[baker_nmax] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    SUBGOAL_THEN `&0 < &h` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_EXP_POS_LE; REAL_POS;
                 REAL_LE_ADD; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_LE_RADD;
                 REAL_OF_NUM_LE; LE_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L:num`; `beta:num->complex`;
                 `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
                 `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
                 `Nl:num`; `l:num`; `m:num->num`;
                 `p:num#num#(num->num)->real`; `P:real`;
                 `a:num->num->real`; `d:num->num`; `H:num->real`]
         BAKER_LEMMA5_ARITH) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `b5 = &(CARD(baker_index h L n)) * P *
         (&Nl pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
          (&(m 0) + &1) pow (m 0) * (&2 * &L * G) pow (nsum(0..n-1) m))` THEN
  SUBGOAL_THEN `(m:num->num) 0 <= k` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `nsum(0..n-1) m` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:num->num`; `0..n-1`; `0`] NSUM_DELETE) THEN
    REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &2 * &L * G` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= y ==> &1 <= &2 * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &(CARD(baker_index h L n))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LE; CARD_BAKER_INDEX] THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= b5` ASSUME_TAC THENL
   [EXPAND_TAC "b5" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:num->bool`; `d:num->num`; `H:num->real`;
                 `\r. (if r IN 1..n then L * l else 0) +
                      nsum(0..n-1) m * (e:num->num) r`;
                 `b5:real`] LIOUVILLE_EXP_LOWER) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`V:num->bool`; `d:num->num`; `H:num->real`; `H:num->real`;
                 `\r. (if r IN 1..n then L * l else 0) +
                      nsum(0..n-1) m * (e:num->num) r`;
                 `\r. (if r IN 1..n then L * Rm else 0) + k * (e:num->num) r`;
                 `b5:real`;
                 `&(CARD(baker_index h L n)) * P *
                  (baker_nmax h Rm pow k *
                   &2 pow ((L + 2) * ((Rm + 1) + h)) *
                   (&k + &1) pow k * (&2 * &L * G) pow k)`]
         LIOUVILLE_EXP_LOWER_MONO) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [EXPAND_TAC "b5" THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `&Nl pow k` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
        CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS; REAL_LE_ADD] THEN CONJ_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `(&(m 0) + &1) pow k` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
          REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE2 THEN
          ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_LE_RADD] THEN REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
                      ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN MATCH_MP_TAC LE_ADD2 THEN
      CONJ_TAC THENL
       [COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL; LE_MULT_LCANCEL];
        ASM_REWRITE_TAC[LE_MULT_RCANCEL]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM baker_liou5] THEN
  DISCH_THEN(LABEL_TAC "mono") THEN DISCH_THEN(LABEL_TAC "lel") THEN
  DISCH_THEN(LABEL_TAC "l5") THEN
  REMOVE_THEN "mono" (fun th1 -> REMOVE_THEN "lel" (fun th2 ->
    REMOVE_THEN "l5" (fun th3 ->
      ASSUME_TAC(MATCH_MP REAL_LE_TRANS
        (CONJ (MATCH_MP REAL_LE_TRANS (CONJ th1 th2)) th3))))) THEN
  SUBGOAL_THEN
   `norm(Cx(&Nl) pow (m 0) *
         (g:num->(num->complex)->complex) n theta pow (nsum(0..n-1) m) *
         baker_alg n h L p beta lg m (Cx(&l))) <=
    (baker_nmax h Rm pow k * Gn pow k) *
    norm(baker_alg n h L p beta lg m (Cx(&l)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX;
                REAL_ABS_NUM; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS; NORM_POS_LE] THEN CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&Nl pow k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS]];
      TRANS_TAC REAL_LE_TRANS `Gn pow (nsum(0..n-1) m)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[NORM_POS_LE];
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lmin pow k <= norm(cproduct(1..n-1) (\r. lg r pow (m r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CPRODUCT_LG_POW_LOWER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[baker_vb] THEN
  SUBGOAL_THEN `&0 < baker_nmax h Rm pow k * Gn pow k` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `baker_liou5 n h L k V G H e d P Rm /
    (baker_nmax h Rm pow k * Gn pow k) <=
    norm(baker_alg n h L p beta lg m (Cx(&l)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `norm(Cx(&Nl) pow (m 0) *
           (g:num->(num->complex)->complex) n theta pow (nsum(0..n-1) m) *
           baker_alg n h L p beta lg m (Cx(&l)))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `lmin pow k *
    (baker_liou5 n h L k V G H e d P Rm /
     (baker_nmax h Rm pow k * Gn pow k)) <=
    norm(cproduct(1..n-1) (\r. (lg:num->complex) r pow (m r)) *
         baker_alg n h L p beta lg m (Cx(&l)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REWRITE_TAC[baker_liou5; REAL_EXP_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC NORM_LOWER_FROM_APPROX THEN
  EXISTS_TAC `cproduct(1..n-1) (\r. (lg:num->complex) r pow (m r)) *
              baker_alg n h L p beta lg m (Cx(&l))` THEN
  ASM_REWRITE_TAC[] THEN REMOVE_THEN "approx" ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The parametric core: Siegel (Lemma 4), extrapolation over integers        *)
(* (Lemmas 5 and 6), extrapolation to the rationals l / k (Lemma 7) and the  *)
(* coincidence of nodes (sec. 4) contradict the linear independence.         *)
(* ------------------------------------------------------------------------- *)

let BAKER_CORE_PARAMETRIC = prove
 (`!n lg theta V (g:num->(num->complex)->complex) e G a d H beta
    h L k R S rho J X7 rhoX eps Bb Lam d0 lmin Gn.
    1 <= n /\ 1 <= L /\ L <= k /\ 1 <= h /\ &1 <= G /\ FINITE V /\
    (1..n) SUBSET V /\
    (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
    (!j. j <= n ==> intpoly V e G (g j)) /\
    ~(g n theta = Cx(&0)) /\ norm(g n theta) <= Gn /\ &1 <= Gn /\
    (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
    (!r. r IN V
         ==> 1 <= d r /\ &1 <= H r /\
             (!j. integer(a r j) /\ abs(a r j) <= H r) /\
             ~(a r (d r) = &0) /\
             vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
    (!b. (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= &L) /\
         vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
         ==> !r. r IN 1..n ==> b r = &0) /\
    &1 <= Bb /\ (!j. j < n ==> norm(beta j) <= Bb) /\
    &1 <= Lam /\ (!r. r IN 1..n ==> norm(lg r) <= Lam) /\
    sum(1..n) (\r. norm(lg r)) <= Lam /\
    &0 < lmin /\ lmin <= &1 /\ (!r. r IN 1..n ==> lmin <= norm(lg r)) /\
    &0 <= d0 /\ d0 <= &1 /\
    norm(beta 0 + vsum(1..n-1) (\r. beta r * lg r) - lg n) <= d0 /\
    2 * nproduct V d * (k + 1) EXP n <= (L + 1) * (L + 1) EXP n /\
    baker_err n h L k (baker_pbound n h L k V G H e) Bb Lam d0 (h + 1)
    <= eps /\
    R 0 = h /\ S 0 = k /\
    (!K. K < J ==> R K <= R(K + 1)) /\
    (!K. K < J ==> 2 * S(K + 1) <= S K) /\
    (!K. K < J ==> 4 * R(K + 1) <= rho K) /\
    (!K. K < J
         ==> baker_err n h L k (baker_pbound n h L k V G H e) Bb Lam d0
                       (R(K + 1) + 1) <= eps) /\
    (!K. K < J
         ==> &0 < baker_vb n h L k V G H e d (baker_pbound n h L k V G H e)
                           Bb Lam d0 lmin Gn (R(K + 1))) /\
    (!K. K < J
         ==> &2 * baker_ub n h L k (baker_pbound n h L k V G H e) Bb Lam
                           (rho K + 1) *
             (&4 * &(R(K + 1)) / &(rho K)) pow (R K * (S(K + 1) + 1)) +
             eps * &2 * &(R K) * &2 pow S(K + 1) * exp(&n) *
             (&(R(K + 1)) * &16 pow R(K + 1)) pow (S(K + 1) + 1)
             <= baker_vb n h L k V G H e d (baker_pbound n h L k V G H e)
                         Bb Lam d0 lmin Gn (R(K + 1)) / &2) /\
    h * (L + 2) * (L + 1) EXP n <= k * X7 /\ X7 <= R J /\ 4 * R J <= rhoX /\
    &k pow (2 * h * (L + 2)) *
    (&2 * baker_ub n h L k (baker_pbound n h L k V G H e) Bb Lam (rhoX + 1) *
     (&4 * &(R J) / &rhoX) pow (R J * (S J + 1)) +
     eps * &2 * &k * &(R J) * (&2 * &k) pow (S J) * exp(&n) *
     (&(R J) * &16 pow (R J)) pow (S J + 1) +
     baker_err n h L k (baker_pbound n h L k V G H e) Bb Lam d0 (X7 + 1))
    < baker_liou7 n h L k d H (baker_pbound n h L k V G H e) X7
                  (h * (L + 2) * (L + 1) EXP n) /\
    &L * Lam < &2 * pi * &k
    ==> F`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `P = baker_pbound n h L k V G H e` THEN
  MP_TAC(SPEC `2 * h` NUMSEG_COMMON_MULTIPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L:num`; `k:num`; `beta:num->complex`;
                 `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
                 `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
                 `N:num`; `a:num->num->real`; `d:num->num`; `H:num->real`]
         BAKER_LEMMA4_ARITH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      free_in `V:num->bool` (concl th) &&
      free_in `a:num->num->real` (concl th))) THEN
    MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num#num#(num->num)->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN baker_index h L n ==> integer(p x) /\ abs(p x) <= P`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:num#num#(num->num)` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num#num#(num->num)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `a <= b ==> b <= c ==> a <= c:real`)) THEN
    EXPAND_TAC "P" THEN REWRITE_TAC[baker_pbound] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> max (&1) x <= max (&1) y`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC PRODUCT_POS_LE THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE THEN
      MATCH_MP_TAC(REAL_ARITH `&1 <= y ==> &0 <= &2 * y`) THEN
      ASM_SIMP_TAC[]] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_POS] THEN
      UNDISCH_TAC `&N <= exp(&18 * &(2 * h))` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_MUL; REAL_MUL_ASSOC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[baker_pbound; CARD_BAKER_INDEX] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= x * y ==> &1 <= x * y`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_POS; REAL_ARITH `&1 <= max (&1) x`] THEN
    REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                MULT_EQ_0; EXP_EQ_0] THEN
    UNDISCH_TAC `1 <= h` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= P /\ (!x. x IN baker_index h L n ==> abs(p x) <= P)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 <= P ==> &0 <= P`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM(MP_TAC o check (fun th ->
        free_in `p:num#num#(num->num)->real` (concl th) &&
        free_in `P:real` (concl th))) THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `f = \m. baker_aux n h L p beta lg m` THEN
  SUBGOAL_THEN
   `(!m. (f:(num->num)->complex->complex) m holomorphic_on (:complex)) /\
    (!m. complex_derivative (f m) =
         \z. vsum(0..n-1) (\i. f (\r. if r = i then m r + 1 else m r) z))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN ASM_SIMP_TAC[BAKER_AUX_HOLOMORPHIC; ETA_AX] THEN
    ASM_SIMP_TAC[BAKER_AUX_DERIVATIVE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m z N. nsum(0..n-1) m <= k /\ norm z + &1 <= &N
            ==> norm((f:(num->num)->complex->complex) m z) <=
                baker_ub n h L k P Bb Lam N`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[baker_ub] THEN
    MATCH_MP_TAC BAKER_AUX_EXP_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `d0:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m z N. nsum(0..n-1) m <= k /\ norm z + &1 <= &N
            ==> norm((f:(num->num)->complex->complex) m z -
                     cproduct(1..n-1) (\r. lg r pow (m r)) *
                     baker_alg n h L p beta lg m z) <=
                baker_err n h L k P Bb Lam d0 N`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "f" THEN REWRITE_TAC[baker_err] THEN
    MATCH_MP_TAC BAKER_APPROX_EXP_BOUND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m l. nsum(0..n-1) m <= S 0 /\ 1 <= l /\ l <= R 0
          ==> norm((f:(num->num)->complex->complex) m (Cx(&l))) <= eps`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num->num`; `Cx(&l)`; `h + 1`]) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_OF_NUM_ADD;
                REAL_OF_NUM_LE; LE_ADD_RCANCEL] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `baker_alg n h L p beta lg m (Cx(&l)) = Cx(&0)`
    SUBST1_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <= c`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!K. K <= J ==> S K <= k /\ h <= R K` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    SUBGOAL_THEN `K < J` ASSUME_TAC THENL
     [UNDISCH_TAC `SUC K <= J` THEN ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
    ANTS_TAC THENL [UNDISCH_TAC `K < J` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD1] THEN
    MP_TAC(ASSUME `K < J`) THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `!K. K < J ==> 2 * S(K + 1) <= S K` THEN
    DISCH_THEN(MP_TAC o SPEC `K:num`) THEN
    UNDISCH_TAC `!K. K < J ==> R K <= R(K + 1)` THEN
    DISCH_THEN(MP_TAC o SPEC `K:num`) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m l. nsum(0..n-1) m <= (S:num->num) J /\ 1 <= l /\ l <= (R:num->num) J
          ==> norm((f:(num->num)->complex->complex) m (Cx(&l))) <= eps`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL
   [`f:(num->num)->complex->complex`; `n:num`; `R:num->num`; `S:num->num`;
    `\K. &((rho:num->num) K)`;
    `\K. baker_ub n h L k P Bb Lam ((rho:num->num) K + 1)`;
    `\K. baker_vb n h L k V G (H:num->real) (e:num->num) (d:num->num) P
                   Bb Lam d0 lmin Gn ((R:num->num)(K + 1)) / &2`;
    `eps:real`; `J:num`] EXTRAPOLATION_INDUCTION) THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `K:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `S(K + 1) <= k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `K + 1` o check (fun th ->
        free_in `k:num` (concl th) && is_forall(concl th) &&
        not (free_in `eps:real` (concl th)))) THEN
      ANTS_TAC THENL [UNDISCH_TAC `K < J` THEN ARITH_TAC; SIMP_TAC[]];
      ALL_TAC] THEN
    (* rewrite with the instances at K of all hypotheses !K. K < J ==> .. *)
    ASSUM_LIST(fun ths -> REWRITE_TAC(REAL_OF_NUM_MUL :: REAL_OF_NUM_LE ::
      mapfilter (fun th -> MP (SPEC `K:num` th) (ASSUME `K < J`)) ths)) THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "baker_ub"
                        with Failure _ -> false)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_LE_REFL] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(S:num->num)(K + 1)` THEN
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL
       [`n:num`; `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
        `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
        `a:num->num->real`; `d:num->num`; `H:num->real`; `beta:num->complex`;
        `h:num`; `L:num`; `k:num`; `p:num#num#(num->num)->real`; `P:real`;
        `Bb:real`; `Lam:real`; `d0:real`; `lmin:real`; `Gn:real`;
        `(R:num->num)(K + 1)`; `l:num`; `m:num->num`] BAKER_DICHOTOMY) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
        EXISTS_TAC `(S:num->num)(K + 1)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXPAND_TAC "f" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `er <= eps /\ &0 < vb
        ==> (x <= er \/ vb <= x) ==> x <= eps \/ vb / &2 < x`) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `h <= (R:num->num) J /\ (S:num->num) J <=
    k` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `J:num` o check (fun th ->
      free_in `k:num` (concl th) && is_forall(concl th) &&
      not (free_in `eps:real` (concl th)))) THEN
    SIMP_TAC[LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l < h * (L + 2) * (L + 1) EXP n
        ==> baker_alg n h L p beta lg (\r. 0) (Cx(&l) / Cx(&k)) = Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `l <= k * X7` ASSUME_TAC THENL
     [MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `h * (L + 2) * (L + 1) EXP n` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `l <= k * (R:num->num) J` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `k * X7` THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`f:(num->num)->complex->complex`; `n:num`; `(R:num->num) J`;
      `(S:num->num) J`; `k:num`; `l:num`; `&rhoX`;
      `baker_ub n h L k P Bb Lam (rhoX + 1)`; `eps:real`]
     RATIONAL_EXTRAPOLATION_ALL) THEN
    SUBGOAL_THEN `1 <= (R:num->num) J /\ 1 <= k` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC LE_TRANS THENL
       [EXISTS_TAC `h:num`; EXISTS_TAC `L:num`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term (fun t -> try fst(dest_const t) = "baker_ub"
                        with Failure _ -> false)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[NSUM_0; LE_0; GSYM REAL_OF_NUM_ADD; REAL_LE_REFL];
      DISCH_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!r. r IN 1..n
          ==> 1 <= (d:num->num) r /\ &1 <= (H:num->real) r /\
              (!j. integer((a:num->num->real) r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)`
    ASSUME_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r:num) IN V` ASSUME_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          concl th = `(1..n) SUBSET (V:num->bool)`)) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `cexp(lg r) = (theta:num->complex) r` SUBST1_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        free_in `V:num->bool` (concl th) &&
        free_in `a:num->num->real` (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!r. r IN 1..n ==> 1 <= k * (d:num->num) r` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `1 * 1 <= x ==> 1 <= x`) THEN
      MATCH_MP_TAC LE_MULT2 THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&1 <= &(CARD(baker_index h L n)) *
            (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))`
    ASSUME_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
      ASM_REWRITE_TAC[] THEN TRY(MATCH_MP_TAC REAL_POW_LE_1) THEN
      REWRITE_TAC[CARD_BAKER_INDEX; REAL_OF_NUM_LE] THEN
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      UNDISCH_TAC `1 <= h` THEN UNDISCH_TAC `1 <= k` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`n:num`; `h:num`; `L:num`; `beta:num->complex`; `lg:num->complex`;
      `p:num#num#(num->num)->real`; `P:real`; `k:num`; `l:num`; `X7:num`;
      `a:num->num->real`; `d:num->num`; `H:num->real`] BAKER_LEMMA7_ARITH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o check (fun th ->
        free_in `a:num->num->real` (concl th) &&
        not (free_in `V:num->bool` (concl th)))) THEN
      MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o check (fun th ->
      is_binary "real_lt" (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "baker_liou7"
                      with Failure _ -> false)) (concl th))) THEN
    MATCH_MP_TAC(REAL_ARITH
     `(a:real) <= b /\ c <= d ==> d < a ==> b <= c ==> F`) THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`1..n`; `\r:num. k * (d:num->num) r`; `H:num->real`;
        `\r:num. L * l`;
        `&(CARD(baker_index h L n)) *
         (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))`]
       LIOUVILLE_EXP_LOWER) THEN
      BETA_TAC THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= c ==> a <= c:real`) THEN
      REWRITE_TAC[baker_liou7] THEN
      MP_TAC(ISPECL
       [`1..n`; `\r:num. k * (d:num->num) r`; `H:num->real`; `H:num->real`;
        `\r:num. L * l`; `\r:num. L * h * (L + 2) * (L + 1) EXP n`;
        `&(CARD(baker_index h L n)) *
         (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))`;
        `&(CARD(baker_index h L n)) *
         (P * &k pow (2 * h * (L + 2)) * &2 pow ((L + 2) * (X7 + h)))`]
       LIOUVILLE_EXP_LOWER_MONO) THEN
      BETA_TAC THEN REWRITE_TAC[FINITE_NUMSEG; REAL_LE_REFL] THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[LE_MULT_LCANCEL; LT_IMP_LE]; DISCH_THEN ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX;
                REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_POS];
                    ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y a b e:real. x <= y + e /\ y <= a + b ==> x <= a + b + e`) THEN
    EXISTS_TAC
     `norm((f:(num->num)->complex->complex) (\r. 0) (Cx(&l) / Cx(&k)))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`\r:num. 0`; `Cx(&l) / Cx(&k)`; `X7 + 1`] o
      check (fun th -> is_forall(concl th) &&
             free_in `f:(num->num)->complex->complex` (concl th) &&
             can (find_term (fun t -> try fst(dest_const t) = "baker_err"
                             with Failure _ -> false)) (concl th))) THEN
    BETA_TAC THEN
    REWRITE_TAC[NSUM_0; LE_0; complex_pow; CPRODUCT_1; COMPLEX_MUL_LID] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM;
                  GSYM REAL_OF_NUM_ADD; REAL_LE_RADD] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; ASSUME `1 <= k`;
               ARITH_RULE `1 <= k ==> 0 < k`] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_ACCEPT_TAC(NORM_ARITH
       `!x y:complex e. norm(x - y) <= e ==> norm y <= norm x + e`)];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `L:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L:num`; `k:num`;
                 `p:num#num#(num->num)->real`; `lg:num->complex`]
         BAKER_INTEGER_RELATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `l:num` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "baker_alg"
                        with Failure _ -> false)) (concl th))) THEN
      ASM_REWRITE_TAC[BAKER_ALG_ZERO] THEN
      REWRITE_TAC[complex_div; COMPLEX_MUL_AC];
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&L * Lam` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[REAL_POS]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(!r. r IN 1..n ==> (b:num->real) r = &0)` THEN
  REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) &&
    type_of(fst(dest_forall(concl th))) = `:num->real`)) THEN
  ASM_SIMP_TAC[]);;
