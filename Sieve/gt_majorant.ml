(* ========================================================================= *)
(* The pseudorandom majorant of the W-tricked primes: the k-linear forms     *)
(* condition and the majorant property.                                      *)
(*                                                                           *)
(* W = gtW w = prod_{p <= w} p, P = gtP w R (the primes in (w, R]),          *)
(* D = gtD w R = {A SUBSET P | prod A <= R}, Y = sum_D selberg_H (1/p) and   *)
(* nu = gtnu W b D P, nu(n) = Y (sum_{A IN D, prod A | W n + b} lambda_A)^2  *)
(* for a residue b (the applications use a reduced residue modulo W).        *)
(* * GT_LINEAR_FORMS_AFFINE: for m >= 1, t >= 2, K and e > 0 there are w0    *)
(*   and R0 such that for w >= w0, R >= R0, R^(10 m) <= M, M^2 <= N with N   *)
(*   prime, every family of at most m integer affine forms psi_j in t        *)
(*   variables, with linear parts bounded by K, none zero and no two         *)
(*   proportional, and residues b_j,                                         *)
(*     |sum_{x IN Z_N^t} prod_j nu_{b_j}(psi_j(x) mod N) / N^t - 1| <= e     *)
(*   (LF_EXPLICIT gives the bound (exp(19^m / w) - 1) + 2^t / R + O(1/R)).   *)
(*   GT_LINEAR_FORMS: linear forms and one residue b.                        *)
(* * GT_NU_PRIME, GT_Y_LOWER, GT_MAJORANT: nu(n) = Y >= (phi(W)/W)           *)
(*   log(R + 1) when W n + b is a prime > R, so c (phi(W)/W) log(W n + b)    *)
(*   <= nu(n) whenever c log(W n + b) <= log(R + 1).                         *)
(*                                                                           *)
(* Method: Selberg's weights in dual variables replace the smooth cutoffs    *)
(* and contour integrals of Goldston-Yildirim and Green-Tao: the local       *)
(* densities of the forms are inverted on the subset lattice                 *)
(* (lf_selberg.ml), the boxes come from the Chinese remainder theorem        *)
(* (lf_local.ml), and Z_N is reduced to boxes by translation                 *)
(* (lf_estimate.ml).  No zeta function or Fourier analysis is used.          *)
(* ========================================================================= *)

needs "Sieve/lf_estimate.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Nondegenerate families of integer forms.                                  *)
(* ------------------------------------------------------------------------- *)

let INT_PRIME_NDIV_MUL = prove
 (`!p a b. prime p /\ ~((&p:int) divides a) /\ ~((&p:int) divides b)
           ==> ~((&p:int) divides a * b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `a:int`] PRIME_INT_COPRIME) THEN
  MP_TAC(SPECL [`p:num`; `b:int`] PRIME_INT_COPRIME) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(&p:int) divides &1` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`coprime(&p:int,a)`; `coprime(&p:int,b)`; `(&p:int) divides a * b`] THEN
    CONV_TAC INTEGER_RULE;
    REWRITE_TAC[GSYM num_divides; DIVIDES_ONE] THEN
    ASM_MESON_TAC[PRIME_1]]);;

let INT_SMALL_NDIV = prove
 (`!p x. ~(x = &0) /\ abs x < &p ==> ~((&p:int) divides x)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
  ASM_REWRITE_TAC[INT_ABS_NUM] THEN ASM_INT_ARITH_TAC);;

let INT_MINOR_BOUND = prove
 (`!a b c d K. abs a <= &K /\ abs b <= &K /\ abs c <= &K /\ abs d <= &K
               ==> abs(a * d - b * c:int) <= &2 * &K * &K`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `abs a * abs d + abs b * abs(c:int)` THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_ABS_MUL] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH
   `(x:int) <= &K * &K /\ y <= &K * &K ==> x + y <= &2 * &K * &K`) THEN
  CONJ_TAC THEN MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_ABS_POS]);;

let LF_FAM_OK_SCALED = prove
 (`!p t K W Js (c:num->num->int).
        prime p /\ ~(p divides W) /\ K < p /\ 2 * K * K < p /\
        (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K) /\
        (!j. j IN Js ==> ?i. i < t /\ ~(c j i = &0)) /\
        (!j j'. j IN Js /\ j' IN Js /\ ~(j = j')
                ==> ?i i'. i < t /\ i' < t /\ ~(i = i') /\ ~(c j i = &0) /\
                           ~(c j i * c j' i' - c j i' * c j' i = &0))
        ==> lf_fam_ok p t Js (\j i. &W * c j i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((&p:int) divides &W)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM num_divides]; ALL_TAC] THEN
  SUBGOAL_THEN `!j i. j IN Js /\ i < t /\ ~((c:num->num->int) j i = &0)
                      ==> ~((&p:int) divides c j i)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INT_SMALL_NDIV THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC `&K:int` THEN
    ASM_SIMP_TAC[INT_OF_NUM_LT];
    ALL_TAC] THEN
  REWRITE_TAC[lf_fam_ok; lf_pnz; lf_pind; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
      check (fun th -> is_forall(concl th) &&
                       not(is_forall(snd(dest_forall(concl th)))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_PRIME_NDIV_MUL THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `j':num`] THEN STRIP_TAC THEN DISJ1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `j':num`] o
    check (fun th -> can (find_term is_exists) (concl th) &&
                     length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `i':num`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`i:num`; `i':num`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_PRIME_NDIV_MUL THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[INT_RING
   `(w * a) * (w * d) - (w * b) * (w * c) = w * w * (a * d - b * c):int`] THEN
  MATCH_MP_TAC INT_PRIME_NDIV_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_PRIME_NDIV_MUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_SMALL_NDIV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC `&2 * &K * &K:int` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_MINOR_BOUND THEN ASM_SIMP_TAC[];
    ASM_REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LT]]);;

(* ------------------------------------------------------------------------- *)
(* The parameters W, P and D.                                                *)
(* ------------------------------------------------------------------------- *)

let gtW = new_definition
 `gtW w = nproduct {p | prime p /\ p <= w} (\p. p)`;;

let gtP = new_definition
 `gtP w R = {p | prime p /\ w < p /\ p <= R}`;;

let gtD = new_definition
 `gtD w R = {A | A SUBSET gtP w R /\ nproduct A (\p. p) <= R}`;;

let GTP_FINITE = prove
 (`!w R. FINITE(gtP w R)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[gtP] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..R` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN ARITH_TAC);;

let GTP_PRIME = prove
 (`!w R p. 2 <= w /\ p IN gtP w R ==> prime p /\ 3 <= p /\ w < p`,
  REWRITE_TAC[gtP; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GTP_COPRIME = prove
 (`!w R p. p IN gtP w R ==> ~(p divides gtW w)`,
  REWRITE_TAC[gtP; gtW; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:num`; `{p:num | prime p /\ p <= w}`]
         PRIME_DIVIDES_NPRODUCT_PRIMES) THEN
  ASM_SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN ASM_ARITH_TAC);;

let GTD_FAMILY = prove
 (`!w R. 1 <= R ==> selberg_family (gtP w R) (gtD w R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[selberg_family; gtD] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM; EMPTY_SUBSET; NPRODUCT_CLAUSES];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`A:num->bool`; `B:num->bool`] THEN STRIP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nproduct A (\p:num. p)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NPRODUCT_SUBSET_LE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; GTP_FINITE]; ALL_TAC] THEN
  X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(p:num) IN gtP w R` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[gtP; IN_ELIM_THM]] THEN
  MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

(* ------------------------------------------------------------------------- *)
(* Estimates for the error terms.                                            *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_ONE_PLUS_LE_EXP = prove
 (`!(f:A->real) s. FINITE s /\ (!x. x IN s ==> &0 <= f x)
                   ==> product s (\x. &1 + f x) <= exp(sum s f)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_EXP_SUM] THEN
  MATCH_MP_TAC PRODUCT_LE THEN ASM_SIMP_TAC[REAL_EXP_LE_X] THEN
  REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
  ASM_SIMP_TAC[]);;

let SUM_INV_SQUARE_FINITE_TAIL = prove
 (`!w s. 1 <= w /\ FINITE s /\ (!n. n IN s ==> w < n)
         ==> sum s (\n. inv(&n pow 2)) <= inv(&w)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [num_FINITE]) THEN
  DISCH_THEN(X_CHOOSE_TAC `L:num`) THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(w+1..L) (\n. inv(&n pow 2))` THEN
  ASM_SIMP_TAC[SUM_INV_SQUARE_TAIL] THEN
  MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
  SIMP_TAC[FINITE_NUMSEG; REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS] THEN
  REWRITE_TAC[SUBSET; IN_NUMSEG] THEN
  ASM_MESON_TAC[ARITH_RULE `w < n ==> w + 1 <= n`]);;

let POW_ONE_PLUS_LE = prove
 (`!x t. &0 <= x /\ x <= &1 ==> (&1 + x) pow t <= &1 + &2 pow t * x`,
  SUBGOAL_THEN
   `!x t. &0 <= x /\ x <= &1 ==> (&1 + x) pow t <= &1 + (&2 pow t - &1) * x`
  (fun th -> REPEAT STRIP_TAC THEN
             MP_TAC(SPECL [`x:real`; `t:num`] th) THEN ASM_REAL_ARITH_TAC) THEN
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[real_pow] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 + x) * (&1 + (&2 pow t - &1) * x)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &2 pow t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2 pow t - &1) * (x * x) <= (&2 pow t - &1) * x` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    REAL_ARITH_TAC]);;

let SELBERG_H_INV_LE_1 = prove
 (`!A. FINITE A /\ (!p. p IN A ==> 2 <= p)
       ==> &0 <= selberg_H (\p. inv(&p)) A /\ selberg_H (\p. inv(&p)) A <= &1`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[selberg_H] THEN
  SUBGOAL_THEN `!p. p IN A ==> inv(&p) / (&1 - inv(&p)) = inv(&p - &1) /\
                               &1 <= &p - &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&2 <= &p` MP_TAC THENL
     [ASM_SIMP_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PRODUCT_POS_LE; MATCH_MP_TAC PRODUCT_LE_1] THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ] THEN X_GEN_TAC `p:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1; REAL_ARITH
   `&1 <= x ==> &0 <= x`]);;

let GT_Y_LE = prove
 (`!w R. 1 <= R ==> sum (gtD w R) (selberg_H (\p. inv(&p))) <= &R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(gtD w R)` ASSUME_TAC THENL
   [MATCH_MP_TAC SELBERG_FAMILY_FINITE THEN EXISTS_TAC `gtP w R` THEN
    ASM_SIMP_TAC[GTD_FAMILY; GTP_FINITE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&(CARD(gtD w R)) * &1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_BOUND THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `A:num->bool` THEN REWRITE_TAC[gtD; IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(SPEC `A:num->bool` SELBERG_H_INV_LE_1) THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; GTP_FINITE]; ALL_TAC] THEN
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:num) IN gtP w R` MP_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[gtP; IN_ELIM_THM]] THEN
      MESON_TAC[PRIME_GE_2];
      SIMP_TAC[]];
    REWRITE_TAC[REAL_MUL_RID; REAL_OF_NUM_LE] THEN
    MATCH_MP_TAC SELBERG_FAMILY_CARD_LE THEN EXISTS_TAC `gtP w R` THEN
    ASM_SIMP_TAC[GTD_FAMILY; GTP_FINITE] THEN
    REWRITE_TAC[gtP; gtD; IN_ELIM_THM] THEN SIMP_TAC[]]);;

let POW_DIFF_REL = prove
 (`!M r t. &0 < M /\ &0 <= r /\ r <= M
           ==> ((M + r) pow t - M pow t) / M pow t <= &2 pow t * (r / M)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(M + r) pow t = M pow t * (&1 + r / M) pow t` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < M` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < M pow t` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `(M pow t * (&1 + r / M) pow t - M pow t) / M pow t =
                (&1 + r / M) pow t - &1` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < M pow t` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= &1 + y ==> x - &1 <= y`) THEN
  MATCH_MP_TAC POW_ONE_PLUS_LE THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ; REAL_MUL_LID]);;

let LF_RATIO = prove
 (`!a R M n. &0 <= a /\ &1 <= R /\ &0 < M /\ R pow n * R <= M
             ==> a * R pow n / M <= a / R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:real) * R pow n / M = (a / R) * ((R pow n * R) / M)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= R`; `&0 < M`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID]]);;

let LF_EMT_BOUND = prove
 (`!t M w R m m'.
        2 <= w /\ 1 <= R /\ 1 <= m /\ m' <= m /\ R EXP (10 * m) <= M
        ==> lf_err t M (gtP w R) (gtD w R) R m' / &M pow t
            <= (exp(&19 pow m / &w) - &1) + &2 pow t / &R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &R /\ &R pow (10 * m) <= &M` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&R pow (10 * m)` THEN
    ASM_SIMP_TAC[REAL_POW_LE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &M pow t` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`w:num`; `R:num`] GTD_FAMILY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&1 <= sum (gtD w R) (selberg_H (\p. inv(&p))) /\
                sum (gtD w R) (selberg_H (\p. inv(&p))) <= &R`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GT_Y_LE] THEN MATCH_MP_TAC SELBERG_G_GE_1 THEN
    EXISTS_TAC `gtP w R` THEN ASM_REWRITE_TAC[GTP_FINITE] THEN
    MP_TAC(SPEC `gtP w R` INV_PRIME_RANGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[GTP_PRIME]; SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Y = sum (gtD w R) (selberg_H (\p. inv(&p)))` THEN
  REWRITE_TAC[lf_err; real_div; REAL_ADD_RDISTRIB] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!x. (&M pow t * x) / &M pow t = x` (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN UNDISCH_TAC `&0 < &M pow t` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x - &1 <= y - &1`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `exp(sum (gtP w R) (\p. &19 pow m' / &p pow 2))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_ONE_PLUS_LE_EXP THEN REWRITE_TAC[GTP_FINITE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; real_div; SUM_LMUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[GTP_FINITE] THEN
      SIMP_TAC[REAL_LE_INV_EQ; REAL_POW_LE; REAL_POS];
      MATCH_MP_TAC SUM_INV_SQUARE_FINITE_TAIL THEN
      REWRITE_TAC[GTP_FINITE] THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[gtP; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&R pow (2 * m') <= &M` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&R pow (10 * m)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
  REWRITE_TAC[GSYM real_div] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&R pow m' * &R pow (2 * m') *
              (&2 pow t * (&R pow (2 * m') / &M))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
       [REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> x <= x + y`) THEN
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC POW_DIFF_REL THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&R pow m' * &R pow (2 * m') * (&2 pow t * (&R pow (2 * m') /
                &M)) = &2 pow t * &R pow (5 * m') / &M`
  SUBST1_TAC THENL
   [REWRITE_TAC[ARITH_RULE `5 * m' = m' + 2 * m' + 2 * m'`; REAL_POW_ADD] THEN
    REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LF_RATIO THEN ASM_SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&R pow (10 * m)` THEN
  ASM_REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let LF_DIV_STEP = prove
 (`!Mt Nt S E Q c3.
        &0 < Mt /\ &0 < Nt /\
        Mt * abs(S - Nt) <= Nt * E + Q * (c3 * (Mt + E) + Mt)
        ==> abs(S / Nt - &1) <= E / Mt + Q / Nt * (c3 * (&1 + E / Mt) + &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs(S / Nt - &1) = (Mt * abs(S - Nt)) / (Mt * Nt)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `S / Nt - &1 = (S - Nt) / Nt` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Nt` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_DIV] THEN
    SUBGOAL_THEN `abs Nt = Nt` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < Nt`; `&0 < Mt`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `E / Mt + Q / Nt * (c3 * (&1 + E / Mt) + &1) =
                (Nt * E + Q * (c3 * (Mt + E) + Mt)) / (Mt * Nt)`
  SUBST1_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < Nt`; `&0 < Mt`] THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_MUL]);;

let LF_Q_BOUND = prove
 (`!m m' t K M N R.
        m' <= m /\ 1 <= t /\ 1 <= R /\ R <= M /\ M * M <= N
        ==> (&m' * &2 * &(t * K * M) * &N pow (t - 1)) / &N pow t
            <= &2 * &m * &t * &K / &R`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `0 < N /\ 0 < R` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC] THEN
    MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `(M:num) * M` THEN
      ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LT_NZ; MULT_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&N pow t = &N * &N pow (t - 1)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &N pow (t - 1) /\ &0 < &N /\ &0 < &R`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&m' * &2 * &(t * K * M) * &N pow (t - 1)) / (&N * &N pow (t - 1)) =
    &(m' * 2 * t * K * M) / &N`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    MAP_EVERY UNDISCH_TAC [`&0 < &N pow (t - 1)`; `&0 < &N`] THEN
    CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `(&2 * &m * &t * &K / &R) * &N = &(2 * m * t * K * N) / &R`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
    UNDISCH_TAC `&0 < &R` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  SUBGOAL_THEN `(m':num) * M * R <= m * N` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(m:num) * M * M` THEN CONJ_TAC THENL
     [REWRITE_TAC[MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
      ASM_SIMP_TAC[LE_MULT2; LE_REFL];
      REWRITE_TAC[GSYM MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
      ASM_REWRITE_TAC[LE_REFL]];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 * (t:num) * (K:num)) * ((m':num) * M * R)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC EQ_IMP_LE THEN REWRITE_TAC[MULT_AC];
   ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 * (t:num) * (K:num)) * ((m:num) * N)` THEN
  ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* The linear forms condition.                                               *)
(* ------------------------------------------------------------------------- *)

let LF_MONO_COMBINE = prove
 (`!a a' q q' c c'.
        &0 <= a /\ a <= a' /\ &0 <= q /\ q <= q' /\ &0 <= c /\ c <= c'
        ==> a + q * (c * (&1 + a) + &1) <= a' + q' * (c' * (&1 + a') + &1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_ADD THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= y + &1`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC]);;

let LF_EXPLICIT = prove
 (`!m t K w (b:num->num) R M N Js (c:num->num->int) (c0:num->int).
        1 <= m /\ 2 <= t /\ 2 <= w /\ 2 * K * K + K < w /\ 1 <= R /\
        t * K < R /\ R EXP (10 * m) <= M /\ M * M <= N /\ prime N /\
        FINITE Js /\ CARD Js <= m /\
        (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K) /\
        (!j. j IN Js ==> ?i. i < t /\ ~(c j i = &0)) /\
        (!j j'. j IN Js /\ j' IN Js /\ ~(j = j')
                ==> ?i i'. i < t /\ i' < t /\ ~(i = i') /\ ~(c j i = &0) /\
                           ~(c j i * c j' i' - c j i' * c j' i = &0))
        ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                    (\x. product Js
                          (\j. gtnu (gtW w) (b j) (gtD w R) (gtP w R)
                                (lf_form {i | i < t} (c j) (c0 j) x rem &N))) /
                &N pow t - &1)
            <= ((exp(&19 pow m / &w) - &1) + &2 pow t / &R) +
               (&2 * &m * &t * &K / &R) *
               (&3 pow m *
                 (&1 + ((exp(&19 pow m / &w) - &1) + &2 pow t / &R)) +
                &1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(R:num) <= M` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `R EXP (10 * m)` THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
    REWRITE_TAC[LE_EXP] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:num) * K * M < N` ASSUME_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `(M:num) * M` THEN
    ASM_REWRITE_TAC[MULT_ASSOC; LT_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:num`; `M:num`; `gtP w R`; `gtD w R`; `R:num`; `gtW w`;
                `b:num->num`; `N:num`; `K:num`; `Js:num->bool`;
                `c:num->num->int`; `c0:num->int`]
         LF_ZN_BOUND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[GTP_FINITE; GTD_FAMILY; GTP_PRIME] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[gtD; IN_ELIM_THM] THEN SIMP_TAC[];
      X_GEN_TAC `p:num` THEN DISCH_TAC THEN MATCH_MP_TAC LF_FAM_OK_SCALED THEN
      EXISTS_TAC `K:num` THEN
      MP_TAC(SPECL [`w:num`; `R:num`; `p:num`] GTP_PRIME) THEN
      MP_TAC(SPECL [`w:num`; `R:num`; `p:num`] GTP_COPRIME) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o
        check (fun th -> is_forall(concl th) &&
                         not(is_forall(snd(dest_forall(concl th)))) &&
                         can (find_term is_exists) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INT_SMALL_NDIV THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INT_LET_TRANS THEN EXISTS_TAC `&K:int` THEN
      ASM_SIMP_TAC[INT_OF_NUM_LT] THEN
      UNDISCH_TAC `(t:num) * K * M < N` THEN UNDISCH_TAC `(R:num) <= M` THEN
      UNDISCH_TAC `(t:num) * K < R` THEN UNDISCH_TAC `2 <= t` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `(K:num) <= a ==> a < N ==> K < N`) THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(t:num) * K` THEN
      CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `(K:num) = 1 * K`] THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `(x:num) = x * 1`] THEN
        REWRITE_TAC[GSYM MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN
        CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < &M pow t /\ &0 < &N pow t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THENL
     [UNDISCH_TAC `(R:num) <= M` THEN UNDISCH_TAC `1 <= R` THEN ARITH_TAC;
      ASM_MESON_TAC[PRIME_IMP_NZ]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LF_DIV_STEP o
    CONJ (ASSUME `&0 < &M pow t`) o CONJ (ASSUME `&0 < &N pow t`)) THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z`) THEN
  MATCH_MP_TAC LF_MONO_COMBINE THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC LF_ERR_POS THEN ASM_SIMP_TAC[GTP_FINITE; GTD_FAMILY] THEN
    ASM_MESON_TAC[GTP_PRIME];
    MATCH_MP_TAC LF_EMT_BOUND THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    SIMP_TAC[REAL_POS; REAL_POW_LE];
    MATCH_MP_TAC LF_Q_BOUND THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let DIV_LE_THIRD = prove
 (`!a e R. &0 < e /\ &0 <= a /\ &0 < R /\ (&3 * a) / e <= R
           ==> a / R <= e / &3`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  UNDISCH_TAC `(&3 * a) / e <= R` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  REAL_ARITH_TAC);;

let LF_FINAL_ARITH = prove
 (`!e e1 e2 e3 c.
        &0 < e /\ &0 <= e1 /\ e1 <= e / &3 /\ e1 <= &1 /\
        &0 <= e2 /\ e2 <= e / &3 /\ e2 <= &1 /\
        &0 <= e3 /\ e3 * (c * &3 + &1) <= e / &3 /\ &0 <= c
        ==> (e1 + e2) + e3 * (c * (&1 + (e1 + e2)) + &1) <= e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `e3 * (c * (&1 + (e1 + e2)) + &1) <= e3 * (c * &3 + &1)`
  MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + &1 <= y + &1`) THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let EXP_MINUS_ONE_BOUND = prove
 (`!x. &0 <= x /\ x <= inv(&2) ==> &0 <= exp x - &1 /\ exp x - &1 <= &2 * x`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    MP_TAC(SPEC `x:real` REAL_EXP_BOUND_LEMMA) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let GT_LINEAR_FORMS_AFFINE = prove
 (`!m t K e.
        1 <= m /\ 2 <= t /\ &0 < e
        ==> ?w0 R0.
              !w (b:num->num) R M N Js (c:num->num->int) (c0:num->int).
                w0 <= w /\ R0 <= R /\ R EXP (10 * m) <= M /\ M * M <= N /\
                prime N /\ FINITE Js /\ CARD Js <= m /\
                (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K) /\
                (!j. j IN Js ==> ?i. i < t /\ ~(c j i = &0)) /\
                (!j j'. j IN Js /\ j' IN Js /\ ~(j = j')
                        ==> ?i i'. i < t /\ i' < t /\ ~(i = i') /\
                                   ~(c j i = &0) /\
                                   ~(c j i * c j' i' - c j i' * c j' i = &0))
                ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                            (\x. product Js
                                  (\j. gtnu (gtW w) (b j) (gtD w R)
                                         (gtP w R)
                                        (lf_form {i | i < t} (c j) (c0 j) x
                                         rem &N))) /
                        &N pow t - &1) <= e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `a1 = &2 * &19 pow m` THEN
  ABBREV_TAC `a3 = (&2 * &m * &t * &K) * (&3 pow m * &3 + &1)` THEN
  SUBGOAL_THEN `&0 <= a1 /\ &0 <= a3 /\ &0 <= &2 pow t /\ &0 <= &19 pow m`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a1"; "a3"] THEN REPEAT CONJ_TAC THEN
    REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_ADD) THEN
           CONJ_TAC) THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPEC `(&3 * a1) / e + &4 * &19 pow m + &(2 * K * K + K) + &2`
         REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `w0:num`) THEN
  MP_TAC(SPEC `(&3 * &2 pow t) / e + &2 pow t + (&3 * a3) / e + &(t * K) + &1`
         REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `R0:num`) THEN
  MAP_EVERY EXISTS_TAC [`w0:num`; `R0:num`] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&3 * a1) / e /\ &0 <= (&3 * &2 pow t) / e /\
                &0 <= (&3 * a3) / e`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&w0 <= &w /\ &R0 <= &R` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= w /\ 2 * K * K + K < w /\ 1 <= R /\ t * K < R`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &w /\ &0 < &R` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `t:num`; `K:num`; `w:num`; `b:num->num`; `R:num`;
                `M:num`; `N:num`; `Js:num->bool`; `c:num->num->int`;
                `c0:num->int`] LF_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= e ==> x <= y ==> x <= e`) THEN
  MATCH_MP_TAC LF_FINAL_ARITH THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &19 pow m / &w /\ &19 pow m / &w <= inv(&2)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&19 pow m / &w` EXP_MINUS_ONE_BOUND) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 * &19 pow m / &w <= e / &3` ASSUME_TAC THENL
   [REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    MATCH_MP_TAC DIV_LE_THIRD THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE];
    MATCH_MP_TAC DIV_LE_THIRD THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_POS];
    SUBGOAL_THEN `(&2 * &m * &t * &K / &R) * (&3 pow m * &3 + &1) = a3 / &R`
    SUBST1_TAC THENL
     [EXPAND_TAC "a3" THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC DIV_LE_THIRD THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    SIMP_TAC[REAL_POW_LE; REAL_POS]]);;

let GT_LINEAR_FORMS = prove
 (`!m t K e.
        1 <= m /\ 2 <= t /\ &0 < e
        ==> ?w0 R0.
              !w b R M N Js (c:num->num->int).
                w0 <= w /\ R0 <= R /\ R EXP (10 * m) <= M /\ M * M <= N /\
                prime N /\ FINITE Js /\ CARD Js <= m /\
                (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K) /\
                (!j. j IN Js ==> ?i. i < t /\ ~(c j i = &0)) /\
                (!j j'. j IN Js /\ j' IN Js /\ ~(j = j')
                        ==> ?i i'. i < t /\ i' < t /\ ~(i = i') /\
                                   ~(c j i = &0) /\
                                   ~(c j i * c j' i' - c j i' * c j' i = &0))
                ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                            (\x. product Js
                                  (\j. gtnu (gtW w) b (gtD w R) (gtP w R)
                                        (lf_form {i | i < t} (c j) (&0) x
                                         rem &N))) /
                        &N pow t - &1) <= e`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:num`; `t:num`; `K:num`; `e:real`]
    GT_LINEAR_FORMS_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`w:num`; `\j:num. (b:num)`; `R:num`; `M:num`; `N:num`; `Js:num->bool`;
    `c:num->num->int`; `\j:num. &0:int`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The majorant property.                                                    *)
(* ------------------------------------------------------------------------- *)

let NPRODUCT_PRIMES_GT_1 = prove
 (`!A. FINITE A /\ (!p. p IN A ==> prime p) /\ ~(A = {})
       ==> 1 < nproduct A (\p. p)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:num` o GEN_REWRITE_RULE I
    [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `p:num` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 < p`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:num. p`; `{p:num}`; `A:num->bool`] NPRODUCT_SUBSET_LE) THEN
  REWRITE_TAC[NPRODUCT_SING] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SING_SUBSET] THEN
  ASM_MESON_TAC[PRIME_GE_2; ARITH_RULE `2 <= p ==> 1 <= p`]);;

let SELBERG_LAMSUM_PRIME = prove
 (`!w R q. 2 <= w /\ 1 <= R /\ prime q /\ R < q
           ==> selberg_lamsum (gtD w R) (gtP w R) (&q) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `gtP w R` INV_PRIME_RANGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[GTP_PRIME]; DISCH_TAC] THEN
  REWRITE_TAC[selberg_lamsum] THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `sum {A:num->bool | A SUBSET gtP w R}
                  (\A. if A = {} then &1 else &0)` THEN
  CONJ_TAC THENL
   [ALL_TAC; REWRITE_TAC[SUM_DELTA; IN_ELIM_THM; EMPTY_SUBSET]] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `A:num->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  ASM_CASES_TAC `A:num->bool = {}` THENL
   [ASM_REWRITE_TAC[NPRODUCT_CLAUSES; INTEGER_RULE `!x:int. &1 divides x`] THEN
    MATCH_MP_TAC SELBERG_WEIGHT_EMPTY THEN EXISTS_TAC `gtP w R` THEN
    ASM_SIMP_TAC[GTP_FINITE; GTD_FAMILY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC SELBERG_WEIGHT_SUPPORT THEN EXISTS_TAC `gtP w R` THEN
  ASM_SIMP_TAC[GTD_FAMILY] THEN REWRITE_TAC[gtD; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 < nproduct A (\p:num. p)` ASSUME_TAC THENL
   [MATCH_MP_TAC NPRODUCT_PRIMES_GT_1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; GTP_FINITE]; ALL_TAC] THEN
    UNDISCH_TAC `A SUBSET gtP w R` THEN REWRITE_TAC[gtP; SUBSET;
     IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(&(nproduct A (\p:num. p)):int) divides &q` THEN
  REWRITE_TAC[GSYM num_divides] THEN
  UNDISCH_TAC `prime q` THEN REWRITE_TAC[PRIME_ALT] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let GT_NU_PRIME = prove
 (`!w b R n.
        2 <= w /\ 1 <= R /\ prime(gtW w * n + b) /\ R < gtW w * n + b
        ==> gtnu (gtW w) b (gtD w R) (gtP w R) (&n) =
            sum (gtD w R) (selberg_H (\p. inv(&p)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[gtnu] THEN
  REWRITE_TAC[INT_OF_NUM_MUL; INT_OF_NUM_ADD] THEN
  ASM_SIMP_TAC[SELBERG_LAMSUM_PRIME] THEN REAL_ARITH_TAC);;

let GTW_POS = prove
 (`!w. 1 <= gtW w`,
  GEN_TAC THEN REWRITE_TAC[gtW; ARITH_RULE `1 <= n <=> 0 < n`] THEN
  MATCH_MP_TAC NPRODUCT_POS_LT THEN
  SIMP_TAC[FINITE_ATMOST; IN_ELIM_THM] THEN MESON_TAC[PRIME_IMP_NZ; LT_NZ]);;

let GT_Y_LOWER = prove
 (`!w R. 1 <= R
         ==> &(phi(gtW w)) / &(gtW w) * log(&R + &1) <=
             sum (gtD w R) (selberg_H (\p. inv(&p)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`gtW w`; `&R + &1`] SELBERG_G_ONE_LOWER) THEN
  REWRITE_TAC[GTW_POS] THEN ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `y = z ==> x <= y ==> x <= z`) THEN
  SUBGOAL_THEN `{p | prime p /\ &p < &R + &1 /\ ~(p divides gtW w)} = gtP w R`
  SUBST1_TAC THENL
   [REWRITE_TAC[gtP; gtW; EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `p:num` THEN
    ASM_CASES_TAC `prime p` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRIME_DIVIDES_NPRODUCT_PRIMES; FINITE_ATMOST;
     IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[selberg_G] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[gtD; EXTENSION; IN_ELIM_THM] THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT;
              ARITH_RULE `!n R. n < R + 1 <=> n <= R`]);;

let GT_MAJORANT = prove
 (`!w b R n c.
        2 <= w /\ 1 <= R /\ prime(gtW w * n + b) /\ R < gtW w * n + b /\
        &0 <= c /\ c * log(&(gtW w * n + b)) <= log(&R + &1)
        ==> c * (&(phi(gtW w)) / &(gtW w) * log(&(gtW w * n + b))) <=
            gtnu (gtW w) b (gtD w R) (gtP w R) (&n)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GT_NU_PRIME] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&(phi(gtW w)) / &(gtW w) * log(&R + &1)` THEN
  ASM_SIMP_TAC[GT_Y_LOWER] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `c * (a * b) = a * (c * b:real)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS]);;
