(* ========================================================================= *)
(* Transference on Z_N and the relative Szemeredi theorem (Zhao, "An         *)
(* arithmetic transference proof of a relative Szemeredi theorem", Sections  *)
(* 3-5), for N prime, from Szemeredi's theorem in Z_N (WEIGHTED_SZEMEREDI    *)
(* of Library/szemeredi.ml).                                                 *)
(*                                                                           *)
(* The edge forms are zn_psi k N j x = sum_{i /= j} (i - j) x_i mod N, so    *)
(* zn_psi j x = (zn_A x + j zn_D x) mod N (ZN_PSI_AP), and ZN_HCOUNT_AP: the *)
(* count of the system f o zn_psi is E_{a,d} prod_{j<k} f((a + j d) mod N).  *)
(* * The test class: plain-sum duals zn_dual u y = N E_x [zn_sig x = y]      *)
(*   prod_{i /= 0} u_i x, zn_sig x = sum_{i /= 0} x_i mod N.  ZN_DUAL_MUL: a *)
(*   product of two duals is an average over the kernel of zn_sig of duals   *)
(*   (translations zn_add), hence ZN_DUAL_PRODUCT_BOUND for products of any  *)
(*   number of duals; ZN_DUAL_SINGLE: |E (nu - 1) zn_dual u|^(2^(k-1)) <=    *)
(*   2^|lf_index k| eta, by GOWERS_CS after the dilation zn_dil turning      *)
(*   zn_sig into zn_psi 0, and LF_PRODUCT_EXPAND.                            *)
(* * ZN_DENSE_MODEL: DENSE_MODEL for the duals of the indicator families     *)
(*   zn_ind A, A IN zn_S0 k N, extended to all [0, 1] families by            *)
(*   DISC_REDUCE.                                                            *)
(* * EDGE_TRANSFER: the coordinate change zn_map (inverse coefficients       *)
(*   zn_inverse mod N, coordinates 0 and j exchanged) turns zn_psi j into    *)
(*   zn_sig; ZN_DISCREPANCY: zn_hdisc for every edge form, and |E f - E ft|  *)
(*   <= e.                                                                   *)
(* * ZN_RELATIVE_AP: for 2 <= k and gamma > 0 there is eta > 0 such that     *)
(*   for every prime N >= k, nu o zn_psi satisfying lf_cond with error eta   *)
(*   and 0 <= f <= nu on Z_N there is ft : Z_N -> [0, 1] with |E f - E ft|   *)
(*   <= gamma and                                                            *)
(*     |E_{a,d} prod_j f(a + j d) - E_{a,d} prod_j ft(a + j d)| <= gamma     *)
(*   (GT_COUNTING_LEMMA for f o zn_psi, ft o zn_psi and nu o zn_psi).        *)
(* * lf_hyp N nu t m K eta is the linear forms condition in the form of      *)
(*   GT_LINEAR_FORMS (gt_majorant.ml): integer forms in t variables, at      *)
(*   most m of them, coefficients bounded by K, none zero, no two            *)
(*   proportional.  LF_COND_FROM_HYP (t = 2k, m = |lf_index k|, K = k; the   *)
(*   doubled forms zn_coef, their residues zn_dcoef, LF_FORM_ZN_LIN,         *)
(*   ZN_MEAN2_ZTUP2, ZN_COEF_INDEP) and ZN_TRANSFERENCE: ZN_RELATIVE_AP      *)
(*   under lf_hyp.                                                           *)
(* * RELATIVE_SZEMEREDI (Green-Tao): if 0 <= f <= nu on Z_N, N prime and     *)
(*   large, E f >= delta and nu satisfies lf_hyp with error eta, then        *)
(*   E_{a,d} prod_{j<k} f(a + j d) >= c(k, delta) > 0: ZN_TRANSFERENCE       *)
(*   gives ft : Z_N -> [0, 1] with almost the same mean and count, and       *)
(*   WEIGHTED_SZEMEREDI bounds the count of ft from below.                   *)
(* ========================================================================= *)

needs "Sieve/gt_counting.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Linear forms, translations and fibres on Z_N^k.                           *)
(* ------------------------------------------------------------------------- *)

let FMEAN_INJ = prove
 (`!k N (Tm:(num->num)->(num->num)) (F1:(num->num)->real).
        (!x. x IN zn_tup k N ==> Tm x IN zn_tup k N) /\
        (!x y. x IN zn_tup k N /\ y IN zn_tup k N /\ Tm x = Tm y ==> x = y)
        ==> fmean (zn_tup k N) (\x. F1(Tm x)) = fmean (zn_tup k N) F1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (Tm:(num->num)->(num->num)) (zn_tup k N) = zn_tup k N`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[FINITE_ZN_TUP];
    ALL_TAC] THEN
  REWRITE_TAC[fmean] THEN
  SUBGOAL_THEN `sum (zn_tup k N) (F1:(num->num)->real) =
                sum (IMAGE Tm (zn_tup k N)) F1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o rand o snd) THEN
  ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let zn_lin = new_definition
 `zn_lin N (c:num->num) s (x:num->num) = nsum s (\i. c i * x i) MOD N`;;

let ZN_LIN_LT = prove
 (`!N c s x. ~(N = 0) ==> zn_lin N c s x < N`,
  SIMP_TAC[zn_lin; MOD_LT_EQ]);;

let zn_add = new_definition
 `zn_add k N (x:num->num) w = \i. if i < k then (x i + w i) MOD N else ARB`;;

let ZN_ADD_IN_TUP = prove
 (`!k N x w. 1 <= N ==> zn_add k N x w IN zn_tup k N`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ZN_TUP; zn_add] THEN
  SIMP_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC);;

let ZN_LIN_ADD = prove
 (`!k N c s x w.
        FINITE s /\ s SUBSET {i | i < k}
        ==> zn_lin N c s (zn_add k N x w) =
            (zn_lin N c s x + zn_lin N c s w) MOD N`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_lin; MOD_ADD_MOD] THEN
  ASM_SIMP_TAC[GSYM NSUM_ADD; GSYM CONG] THEN MATCH_MP_TAC CONG_NSUM THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `i:num < k` (fun th -> REWRITE_TAC[zn_add; th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `(a:num == x + w) (mod n) ==> (c * a == c * x + c * w) (mod n)`) THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;

let FMEAN_FIBRE = prove
 (`!k N (sg:(num->num)->num) (F1:num->real) G.
        1 <= N /\ (!x. x IN zn_tup k N ==> sg x < N)
        ==> fmean (zn_tup k N) (\x. F1(sg x) * G x) =
            fmean {y | y < N}
              (\y. F1 y * (&N * fmean (zn_tup k N)
                                 (\x. if sg x = y then G x else &0)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum (zn_tup k N) (\x. (F1:num->real)(sg x) * G x) =
    sum {y | y < N}
      (\y. F1 y * sum (zn_tup k N) (\x. if sg x = y then G x else &0))`
  ASSUME_TAC THENL
   [SIMP_TAC[GSYM SUM_LMUL] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o rand o snd) THEN
    REWRITE_TAC[FINITE_ZN_TUP; FINITE_NUMSEG_LT] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    REWRITE_TAC[COND_RAND; REAL_MUL_RZERO] THEN
    ONCE_REWRITE_TAC[MESON[] `(if (sg:num) = y then (a:real) else b) =
                               (if y = sg then a else b)`] THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[SUM_DELTA; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[fmean; CARD_ZN_TUP; CARD_NUMSEG_LT] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_RING
   `!f n s q:real. f * (n * (s * q)) = (n * q) * (f * s)`] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_FIELD
   `!X P n:real. ~(n = &0) ==> X * inv P = ((n * inv P) * X) * inv n`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Plain-sum duals and their products.                                       *)
(* ------------------------------------------------------------------------- *)

let zn_sig = new_definition
 `zn_sig k N x = zn_lin N (\i. 1) ({l | l < k} DELETE 0) x`;;

let zn_fam = new_definition
 `zn_fam k N (u:num->(num->num)->real) <=>
    !i. i < k /\ ~(i = 0)
        ==> zn_depon ({l | l < k} DIFF {i, 0}) (u i) /\
            !x. x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1`;;

let zn_dual = new_definition
 `zn_dual k N (u:num->(num->num)->real) y =
    &N * fmean (zn_tup k N)
           (\x. if zn_sig k N x = y
                then product ({l | l < k} DELETE 0) (\i. u i x) else &0)`;;

let ZN_SIG_UPD1 = prove
 (`!k N x r. 1 < k
             ==> zn_sig k N (zn_upd x 1 r) =
                 (nsum (({l | l < k} DELETE 0) DELETE 1) (\i. x i) + r)
                 MOD N`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_sig; zn_lin; MULT_CLAUSES] THEN
  SUBGOAL_THEN `FINITE({l:num | l < k} DELETE 0) /\
                1 IN {l:num | l < k} DELETE 0`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP NSUM_DELETE th)]) THENL
   [ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; IN_DELETE; IN_ELIM_THM;
                 ARITH_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[ZN_UPD_AT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[IN_DELETE; zn_upd]);;

let FIBRE_MEAN = prove
 (`!k N y. 1 < k /\ 1 <= N /\ y < N
           ==> fmean (zn_tup k N) (\x. if zn_sig k N x = y then &1 else &0) =
               inv(&N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `1`;
                 `\x. if zn_sig k N x = y then &1 else &0`]
                   ZN_TUP_FMEAN_COORD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[ZN_SIG_UPD1] THEN
  REWRITE_TAC[GEN `c:num` (BETA_RULE (ISPECL
   [`N:num`; `c:num`; `\r:num. if r = y then &1 else &0`]
   FMEAN_SHIFT_MOD))] THEN
  SUBGOAL_THEN
   `fmean {r | r < N} (\r. if r = y then &1 else &0) = inv(&N)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[fmean; SUM_DELTA; IN_ELIM_THM; CARD_NUMSEG_LT] THEN
    REWRITE_TAC[real_div; REAL_MUL_LID];
    MATCH_MP_TAC FMEAN_CONST THEN
    ASM_SIMP_TAC[FINITE_ZN_TUP; ZN_TUP_NONEMPTY]]);;

let ZN_DUAL_BOUNDS = prove
 (`!k N (u:num->(num->num)->real) y.
        zn_fam k N u /\ 1 < k /\ 1 <= N /\ y < N
        ==> &0 <= zn_dual k N u y /\ zn_dual k N u y <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_fam] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. x IN zn_tup k N
        ==> &0 <= product ({l | l < k} DELETE 0) (\i. u i x) /\
            product ({l | l < k} DELETE 0) (\i. u i x) <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE; MATCH_MP_TAC PRODUCT_LE_1] THEN
    ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; IN_DELETE; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[zn_dual] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC FMEAN_POS THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&N * fmean (zn_tup k N)
    (\x. if zn_sig k N x = y then &1 else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
    ASM_SIMP_TAC[FIBRE_MEAN] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC]);;

let ZN_DUAL_FIBRE = prove
 (`!k N (F1:num->real) (u:num->(num->num)->real).
        1 <= N
        ==> fmean (zn_tup k N)
              (\x. F1(zn_sig k N x) * product ({l | l < k} DELETE 0)
                (\i. u i x)) =
            fmean {y | y < N} (\y. F1 y * zn_dual k N u y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dual] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `zn_sig k N`; `F1:num->real`;
                 `\x. product ({l | l < k} DELETE 0)
                        (\i. (u:num->(num->num)->real) i x)`] FMEAN_FIBRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_sig] THEN MATCH_MP_TAC ZN_LIN_LT THEN
  ASM_ARITH_TAC);;

let ZN_ADD_INJ = prove
 (`!k N x w w'. w IN zn_tup k N /\ w' IN zn_tup k N /\
                zn_add k N x w = zn_add k N x w' ==> w = w'`,
  REWRITE_TAC[IN_ZN_TUP; zn_add; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x':num) < k` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(NUMBER_RULE
   `!c x y n. (c + x:num == c + y) (mod n) ==> (x == y) (mod n)`) THEN
  EXISTS_TAC `(x:num->num) x'` THEN REWRITE_TAC[CONG] THEN
  ASM_MESON_TAC[]);;

let ZN_SIG_ADD = prove
 (`!k N x w. zn_sig k N (zn_add k N x w) =
             (zn_sig k N x + zn_sig k N w) MOD N`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_sig] THEN MATCH_MP_TAC ZN_LIN_ADD THEN
  SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; DELETE_SUBSET]);;

let MOD_ADD_EQ_SELF = prove
 (`!N y s. y < N /\ s < N ==> ((y + s) MOD N = y <=> s = 0)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(NUMBER_RULE
     `!y s n. (y + s:num == y) (mod n) ==> (s == 0) (mod n)`) THEN
    EXISTS_TAC `y:num` THEN ASM_SIMP_TAC[CONG; MOD_LT];
    SIMP_TAC[ADD_CLAUSES] THEN ASM_SIMP_TAC[MOD_LT]]);;

let ZN_DUAL_MUL = prove
 (`!k N (u:num->(num->num)->real) u' y.
        1 <= N /\ y < N
        ==> zn_dual k N u y * zn_dual k N u' y =
            fmean (zn_tup k N)
              (\w. (if zn_sig k N w = 0 then &N else &0) *
                   zn_dual k N (\i x. u i x * u' i (zn_add k N x w)) y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dual] THEN
  ABBREV_TAC `J0 = {l:num | l < k} DELETE 0` THEN
  SUBGOAL_THEN `FINITE(J0:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "J0" THEN SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN zn_tup k N
        ==> fmean (zn_tup k N)
              (\x'. if zn_sig k N x' = y
                    then product J0 (\i. (u':num->(num->num)->real) i x')
                    else &0) =
            fmean (zn_tup k N)
              (\w. if zn_sig k N (zn_add k N x w) = y
                   then product J0 (\i. u' i (zn_add k N x w)) else &0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `zn_add k N x`;
                   `\x'. if zn_sig k N x' = y
                         then product J0 (\i. (u':num->(num->num)->real) i x')
                         else &0`] FMEAN_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[ZN_ADD_IN_TUP] THEN MESON_TAC[ZN_ADD_INJ];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_RING `((n:real) * a) * (n * b) = (n * n) * (a * b)`] THEN
  REWRITE_TAC[GSYM FMEAN_RMUL] THEN
  SUBGOAL_THEN
   `fmean (zn_tup k N)
      (\x. (if zn_sig k N x = y then product J0 (\i. u i x) else &0) *
           fmean (zn_tup k N)
             (\x'. if zn_sig k N x' = y
                   then product J0 (\i. (u':num->(num->num)->real) i x')
                   else &0)) =
    fmean (zn_tup k N)
      (\x. fmean (zn_tup k N)
             (\w. (if zn_sig k N x = y then product J0 (\i. u i x) else &0) *
                  (if zn_sig k N (zn_add k N x w) = y
                   then product J0 (\i. u' i (zn_add k N x w)) else &0)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[FMEAN_LMUL];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FMEAN_SWAP o rand o lhand o snd) THEN
  REWRITE_TAC[FINITE_ZN_TUP] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM FMEAN_LMUL] THEN MATCH_MP_TAC FMEAN_EQ THEN
  X_GEN_TAC `w:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `zn_sig k N w < N` ASSUME_TAC THENL
   [REWRITE_TAC[zn_sig] THEN MATCH_MP_TAC ZN_LIN_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ZN_SIG_ADD] THEN MATCH_MP_TAC FMEAN_EQ THEN
  X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `zn_sig k N x < N` ASSUME_TAC THENL
   [REWRITE_TAC[zn_sig] THEN MATCH_MP_TAC ZN_LIN_LT THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `zn_sig k N w = 0` THEN ASM_CASES_TAC `zn_sig k N x = y` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; MOD_LT; MOD_ADD_EQ_SELF; REAL_MUL_LZERO;
               REAL_MUL_RZERO; PRODUCT_MUL] THEN
  REWRITE_TAC[REAL_MUL_ASSOC]);;

let ZN_FAM_PROD = prove
 (`!k N (u:num->(num->num)->real) u' w.
        1 <= N /\ zn_fam k N u /\ zn_fam k N u'
        ==> zn_fam k N (\i x. u i x * u' i (zn_add k N x w))`,
  REWRITE_TAC[zn_fam] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `zn_depon ({l | l < k} DIFF {i, 0}) ((u:num->(num->num)->real) i) /\
    zn_depon ({l | l < k} DIFF {i, 0}) ((u':num->(num->num)->real) i) /\
    (!x. x IN zn_tup k N
         ==> &0 <= u i x /\ u i x <= &1 /\ &0 <= u' i x /\ u' i x <= &1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[zn_depon] THEN MAP_EVERY X_GEN_TAC [`x:num->num`;
    `y:num->num`] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `!l. l IN {l | l < k} DIFF {i, 0} ==> zn_add k N x w l = zn_add k N y w l`
    ASSUME_TAC THENL
     [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `l:num < k /\ (x:num->num) l = y l` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]; ALL_TAC] THEN
      ASM_REWRITE_TAC[zn_add];
      ALL_TAC] THEN
    BINOP_TAC THENL
     [UNDISCH_TAC
       `zn_depon ({l | l < k} DIFF {i, 0}) ((u:num->(num->num)->real) i)`;
      UNDISCH_TAC
       `zn_depon ({l | l < k} DIFF {i, 0})
          ((u':num->(num->num)->real) i)`] THEN
    REWRITE_TAC[zn_depon] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `zn_add k N x w IN zn_tup k N` ASSUME_TAC THENL
     [ASM_SIMP_TAC[ZN_ADD_IN_TUP]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * &1` THEN
      CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[]]]);;

let ZN_FAM_ONE = prove
 (`!k N. zn_fam k N (\i x. &1)`,
  REWRITE_TAC[zn_fam; ZN_DEPON_CONST; REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[zn_depon]);;

let ZN_DUAL_ONE = prove
 (`!k N y. 1 < k /\ 1 <= N /\ y < N ==> zn_dual k N (\i x. &1) y = &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dual; PRODUCT_ONE] THEN
  ASM_SIMP_TAC[FIBRE_MEAN] THEN MATCH_MP_TAC REAL_MUL_RINV THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC);;

let ZWEIGHT_MEAN = prove
 (`!k N. 1 < k /\ 1 <= N
         ==> fmean (zn_tup k N)
               (\w. if zn_sig k N w = 0 then &N else &0) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!w. (if zn_sig k N w = 0 then &N else &0) =
                    &N * (if zn_sig k N w = 0 then &1 else &0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[FMEAN_LMUL] THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `0`] FIBRE_MEAN) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC REAL_MUL_RINV THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
  ASM_ARITH_TAC);;

let PRODUCT_LT_SUC = prove
 (`!n (f:num->real).
        product {t | t < SUC n} f = f n * product {t | t < n} f`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{t | t < SUC n} = n INSERT {t | t < n}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ARITH_TAC;
    SIMP_TAC[PRODUCT_CLAUSES; FINITE_NUMSEG_LT; IN_ELIM_THM; LT_REFL]]);;

let ZN_DUAL_PRODUCT_BOUND = prove
 (`!k N (G:num->real) B.
        1 < k /\ 1 <= N /\
        (!u. zn_fam k N u
             ==> abs(fmean {y | y < N} (\y. G y * zn_dual k N u y)) <= B)
        ==> !d us. (!t. t < (d:num) ==> zn_fam k N (us t))
                   ==> abs(fmean {y | y < N}
                             (\y. G y * product {t | t < d}
                                          (\t. zn_dual k N (us t) y))) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!d us. (!t. t < SUC d ==> zn_fam k N (us t))
           ==> abs(fmean {y | y < N}
                     (\y. G y * product {t | t < SUC d}
                                  (\t. zn_dual k N (us t) y))) <= B`
  ASSUME_TAC THENL
   [INDUCT_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[PRODUCT_LT_SUC] THEN
      REWRITE_TAC[LT; EMPTY_GSPEC; PRODUCT_CLAUSES; REAL_MUL_RID] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ARITH_TAC;
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[PRODUCT_LT_SUC] THEN REWRITE_TAC[PRODUCT_LT_SUC] THEN
    ABBREV_TAC
     `mg = \w i x. (us:num->num->(num->num)->real) d i x *
                   us (SUC d) i (zn_add k N x w)` THEN
    SUBGOAL_THEN
     `!y. y IN {y | y < N}
          ==> G y * zn_dual k N (us (SUC d)) y *
                    zn_dual k N (us d) y *
                    product {t | t < d} (\t. zn_dual k N (us t) y) =
              fmean (zn_tup k N)
                (\w. (if zn_sig k N w = 0 then &N else &0) *
                     (G y * product {t | t < SUC d}
                       (\t. zn_dual k N
                              (if t < d then us t else mg w) y)))`
    ASSUME_TAC THENL
     [X_GEN_TAC `y:num` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[PRODUCT_LT_SUC; LT_REFL] THEN
      SUBGOAL_THEN
       `!w. product {t | t < d}
              (\t. zn_dual k N (if t < d then us t else (mg:(num->num)->num->
                   (num->num)->real) w) y) =
            product {t | t < d}
              (\t. zn_dual k N ((us:num->num->(num->num)->real) t) y)`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`k:num`; `N:num`; `(us:num->num->(num->num)->real) d`;
                     `(us:num->num->(num->num)->real) (SUC d)`; `y:num`]
                    ZN_DUAL_MUL) THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "mg" THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN
      REWRITE_TAC[REAL_RING `(g:real) * b * a * p = (a * b) * (g * p)`] THEN
      ASM_REWRITE_TAC[GSYM FMEAN_RMUL] THEN
      MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      REWRITE_TAC[REAL_MUL_AC];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `abs(fmean (zn_tup k N)
       (\w. (if zn_sig k N w = 0 then &N else &0) *
            fmean {y | y < N}
              (\y. G y * product {t | t < SUC d}
                     (\t. zn_dual k N (if t < d then us t else
                         (mg:(num->num)->num->(num->num)->real) w) y))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC
       `fmean {y | y < N}
         (\y. fmean (zn_tup k N)
           (\w. (if zn_sig k N w = 0 then &N else &0) *
                (G y * product {t | t < SUC d}
                   (\t. zn_dual k N (if t < d then us t else
                         (mg:(num->num)->num->(num->num)->real) w) y))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        W(MP_TAC o PART_MATCH (lhand o rand) FMEAN_SWAP o lhand o snd) THEN
        REWRITE_TAC[FINITE_ZN_TUP; FINITE_NUMSEG_LT] THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FMEAN_LMUL]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `fmean (zn_tup k N) (\w. (if zn_sig k N w = 0 then &N else &0) * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `fmean (zn_tup k N)
         (\w. abs((if zn_sig k N w = 0 then &N else &0) *
            fmean {y | y < N}
              (\y. G y * product {t | t < SUC d}
                     (\t. zn_dual k N (if t < d then us t else
                         (mg:(num->num)->num->(num->num)->real) w) y))))` THEN
      SIMP_TAC[FMEAN_ABS_LE; FINITE_ZN_TUP] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      X_GEN_TAC `w:num->num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      CONJ_TAC THENL [COND_CASES_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC
        `\t. if t < d then (us:num->num->(num->num)->real) t
             else (mg:(num->num)->num->(num->num)->real) w`) THEN
      REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `t:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        EXPAND_TAC "mg" THEN REWRITE_TAC[] THEN MATCH_MP_TAC ZN_FAM_PROD THEN
        ASM_REWRITE_TAC[ETA_AX] THEN CONJ_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC];
      REWRITE_TAC[FMEAN_RMUL] THEN ASM_SIMP_TAC[ZWEIGHT_MEAN] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[LT; EMPTY_GSPEC; PRODUCT_CLAUSES; REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC
     `abs(fmean {y | y < N} (\y. G y * zn_dual k N (\i x. &1) y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC FMEAN_EQ THEN
      ASM_SIMP_TAC[IN_ELIM_THM; ZN_DUAL_ONE; REAL_MUL_RID];
      FIRST_X_ASSUM(MATCH_MP_TAC o CONJUNCT2 o CONJ (ASSUME `1 <= N`)) THEN
      REWRITE_TAC[ZN_FAM_ONE]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Correlations of nu - 1 with the duals.                                    *)
(* ------------------------------------------------------------------------- *)

let zn_psi = new_definition
 `zn_psi k N j x = zn_lin N (\i. (i + N - j) MOD N) ({l | l < k} DELETE j) x`;;

let zn_dil = new_definition
 `zn_dil k N (x:num->num) =
    \i. if i = 0 then x 0 else if i < k then (i * x i) MOD N else ARB`;;

let ZN_DIL_IN_TUP = prove
 (`!k N x. 1 <= N /\ x IN zn_tup k N ==> zn_dil k N x IN zn_tup k N`,
  REWRITE_TAC[IN_ZN_TUP; zn_dil] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

let ZN_DIL_INJ = prove
 (`!k N x y. prime N /\ k <= N /\ x IN zn_tup k N /\ y IN zn_tup k N /\
             zn_dil k N x = zn_dil k N y ==> x = y`,
  REWRITE_TAC[IN_ZN_TUP; zn_dil; FUN_EQ_THM] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(x':num) < k` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `x':num = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `x':num`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x':num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN EXISTS_TAC `x':num` THEN
  ASM_REWRITE_TAC[CONG] THEN
  MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ZN_DIL_MIX = prove
 (`!k N W x0 x1. zn_mix W (zn_dil k N x0) (zn_dil k N x1) =
                 zn_dil k N (zn_mix W x0 x1)`,
  REWRITE_TAC[zn_mix; zn_dil; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let ZN_SIG_DIL = prove
 (`!k N x. zn_sig k N (zn_dil k N x) = zn_psi k N 0 x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_sig; zn_psi; zn_lin; GSYM CONG] THEN
  MATCH_MP_TAC CONG_NSUM THEN SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[zn_dil; MULT_CLAUSES; SUB_0; CONG_LMOD] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `(i + N) * (x:num->num) i` THEN
  CONJ_TAC THENL
   [CONV_TAC NUMBER_RULE;
    MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
    ONCE_REWRITE_TAC[CONG_SYM] THEN REWRITE_TAC[CONG_MOD]]);;

let ZN_MEAN2_INJ = prove
 (`!k N (Tm:(num->num)->(num->num)) (F2:(num->num)->(num->num)->real).
        (!x. x IN zn_tup k N ==> Tm x IN zn_tup k N) /\
        (!x y. x IN zn_tup k N /\ y IN zn_tup k N /\ Tm x = Tm y ==> x = y)
        ==> zn_mean2 k N (\x0 x1. F2 (Tm x0) (Tm x1)) = zn_mean2 k N F2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_mean2] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `Tm:(num->num)->(num->num)`;
                 `\x0. fmean (zn_tup k N)
                         (\x1. (F2:(num->num)->(num->num)->real) x0 x1)`]
                FMEAN_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC FMEAN_EQ THEN X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `Tm:(num->num)->(num->num)`;
                 `\x1. (F2:(num->num)->(num->num)->real) (Tm (x:num->num)) x1`]
                FMEAN_INJ) THEN
  ASM_REWRITE_TAC[]);;

let PRODUCT_IMAGE_PAIR2 = prove
 (`!s (j0:num) (f:num#(num->bool)->real).
        product (IMAGE (\W. (j0,W)) s) f = product s (\W. f (j0,W))`,
  REPEAT GEN_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]);;

let ZN_DUAL_SINGLE = prove
 (`!k N (nu:num->real) eta (u:num->(num->num)->real).
        prime N /\ 1 < k /\ k <= N /\
        lf_cond k N (\j x. nu(zn_psi k N j x)) eta /\ zn_fam k N u
        ==> abs(fmean {y | y < N} (\y. (nu y - &1) * zn_dual k N u y))
              pow (2 EXP (k - 1))
            <= &2 pow CARD(lf_index k) * eta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= eta` ASSUME_TAC THENL
   [ASM_MESON_TAC[LF_COND_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE({l:num | l < k} DELETE 0) /\
    ({l:num | l < k} DELETE 0) SUBSET {i | i < k} /\
    ~({l:num | l < k} DELETE 0 = {}) /\
    CARD({l:num | l < k} DELETE 0) = k - 1`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT; DELETE_SUBSET; CARD_DELETE;
             CARD_NUMSEG_LT; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 < k ==> 0 < k`] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DELETE; IN_ELIM_THM] THEN
    EXISTS_TAC `1` THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `J0 = {l:num | l < k} DELETE 0` THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `\y:num. (nu:num->real) y - &1`;
                 `u:num->(num->num)->real`] ZN_DUAL_FIBRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `zn_mean2 k N (\x0 x1. product {W | W SUBSET J0}
                       (\W. (nu:num->real)(zn_sig k N (zn_mix W x0 x1))
                              - &1))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
      [SYM th]) THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `J0:num->bool`;
                   `\x. (nu:num->real)(zn_sig k N x) - &1`;
                   `u:num->(num->num)->real`] GOWERS_CS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `zn_fam k N (u:num->(num->num)->real)` THEN
    REWRITE_TAC[zn_fam] THEN EXPAND_TAC "J0" THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC ZN_DEPON_UPD THEN
      EXISTS_TAC `{l:num | l < k} DIFF {i, 0}` THEN
      ASM_SIMP_TAC[IN_DIFF; IN_INSERT];
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zn_mean2 k N (\x0 x1. product {W | W SUBSET J0}
                     (\W. (nu:num->real)(zn_sig k N (zn_mix W x0 x1)) - &1)) =
    zn_mean2 k N (\x0 x1. product {W | W SUBSET J0}
                     (\W. nu(zn_psi k N 0 (zn_mix W x0 x1)) - &1))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`k:num`; `N:num`; `zn_dil k N`;
                   `\x0 x1. product {W | W SUBSET J0}
                       (\W. (nu:num->real)(zn_sig k N (zn_mix W x0 x1)) - &1)`]
                  ZN_MEAN2_INJ) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ZN_DIL_IN_TUP] THEN ASM_MESON_TAC[ZN_DIL_INJ]; ALL_TAC] THEN
    REWRITE_TAC[ZN_DIL_MIX; ZN_SIG_DIL] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\W. (0,W)) {W:num->bool | W SUBSET J0} SUBSET lf_index k`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    X_GEN_TAC `W:num->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; lf_index; IN_ELIM_PAIR_THM] THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_ARITH_TAC; EXPAND_TAC "J0" THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {W:num->bool | W SUBSET J0} <= CARD(lf_index k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD(IMAGE (\W. (0,W)) {W:num->bool | W SUBSET J0})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_SIMP_TAC[FINITE_POWERSET] THEN
      REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[];
      MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_LF_INDEX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `\j x. (nu:num->real)(zn_psi k N j x)`;
                 `eta:real`; `IMAGE (\W. (0,W)) {W:num->bool | W SUBSET J0}`;
                 `\p:num#(num->bool). --(&1)`; `\p:num#(num->bool). &1`]
                LF_PRODUCT_EXPAND) THEN
  ASM_REWRITE_TAC[PRODUCT_IMAGE_PAIR2; FST; SND; REAL_MUL_LID] THEN
  REWRITE_TAC[REAL_ARITH `--(&1) + x = x - &1`; REAL_ABS_NEG;
              REAL_ABS_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[PRODUCT_CONST; FINITE_POWERSET; REAL_POW_ZERO; CARD_POWERSET;
               EXP_EQ_0; ARITH_EQ; REAL_SUB_RZERO] THEN
  MATCH_MP_TAC(REAL_ARITH `b <= c ==> abs x <= b ==> x <= c`) THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  UNDISCH_TAC `CARD {W:num->bool | W SUBSET J0} <= CARD(lf_index k)` THEN
  ASM_SIMP_TAC[CARD_POWERSET]);;

(* ------------------------------------------------------------------------- *)
(* The dense model on Z_N.                                                   *)
(* ------------------------------------------------------------------------- *)

let zn_restr = new_definition
 `zn_restr (e:num->bool) (x:num->num) = \l. if l IN e then x l else ARB`;;

let zn_slice = new_definition
 `zn_slice k N i =
    cartesian_product ({l | l < k} DIFF {i, 0}) (\l. {r:num | r < N})`;;

let zn_S0 = new_definition
 `zn_S0 k N = cartesian_product ({l | l < k} DELETE 0)
                              (\i. {A | A SUBSET zn_slice k N i})`;;

let zn_ind = new_definition
 `zn_ind k (A:num->(num->num)->bool) =
    \i x. if zn_restr ({l | l < k} DIFF {i, 0}) x IN A i then &1 else &0`;;

let ZN_FAM_IND = prove
 (`!k N A. zn_fam k N (zn_ind k A)`,
  REWRITE_TAC[zn_fam; zn_ind] THEN REPEAT STRIP_TAC THENL
   [REWRITE_TAC[zn_depon] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `zn_restr ({l | l < k} DIFF {i, 0}) x =
                  zn_restr ({l | l < k} DIFF {i, 0}) y`
    (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[zn_restr; FUN_EQ_THM] THEN ASM_MESON_TAC[];
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

let FINITE_ZN_S0 = prove
 (`!k N. FINITE(zn_S0 k N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_S0] THEN
  MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
  SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_POWERSET THEN REWRITE_TAC[zn_slice] THEN
  MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
  SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG_LT]);;

let ZN_S0_NONEMPTY = prove
 (`!k N. ~(zn_S0 k N = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  EXISTS_TAC `\i. if i IN {l | l < k} DELETE 0 then {}:(num->num)->bool
                  else ARB` THEN
  REWRITE_TAC[zn_S0; cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  SIMP_TAC[EMPTY_SUBSET]);;

let ZN_DUAL_EQ = prove
 (`!k N (u:num->(num->num)->real) v y.
        (!i x. i IN {l | l < k} DELETE 0 /\ x IN zn_tup k N ==> u i x = v i x)
        ==> zn_dual k N u y = zn_dual k N v y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_dual] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC PRODUCT_EQ THEN
  ASM_SIMP_TAC[]);;

let ZN_IND_AGREE = prove
 (`!k N (b:num->(num->num)->real).
        (!i. i IN {l | l < k} DELETE 0
             ==> zn_depon ({l | l < k} DIFF {i, 0}) (b i) /\
                 !x. b i x = &0 \/ b i x = &1)
        ==> ?A. A IN zn_S0 k N /\
                !i x. i IN {l | l < k} DELETE 0 /\ x IN zn_tup k N
                      ==> b i x = zn_ind k A i x`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `\i. if i IN {l | l < k} DELETE 0
        then {zn_restr ({l | l < k} DIFF {i, 0}) x | x | x IN zn_tup k N /\
                                                     b i x = &1}
        else ARB` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[zn_S0; cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
    SIMP_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; zn_slice] THEN
    REWRITE_TAC[cartesian_product; IN_ELIM_THM; EXTENSIONAL; zn_restr] THEN
    REWRITE_TAC[IN_ZN_TUP] THEN SIMP_TAC[IN_DIFF; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `x:num->num`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[zn_ind] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[zn_depon] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o SPEC `x:num->num`) THEN
  ASM_REWRITE_TAC[] THENL
   [COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x':num->num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(b:num->(num->num)->real) i x = b i x'` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o C AP_THM `l:num`) THEN
      ASM_REWRITE_TAC[zn_restr];
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let ZN_DENSE_MODEL = prove
 (`!k e. 1 < k /\ &0 < e /\ e <= &1
         ==> ?eta. &0 < eta /\
               !N (nu:num->real) f.
                 prime N /\ k <= N /\
                 lf_cond k N (\j x. nu(zn_psi k N j x)) eta /\
                 (!y. y < N ==> &0 <= f y /\ f y <= nu y)
                 ==> ?ft. (!y. &0 <= ft y /\ ft y <= &1) /\
                          !u. zn_fam k N u
                              ==> abs(fmean (zn_tup k N)
                                    (\x. (f(zn_sig k N x) - ft(zn_sig k N x)) *
                                         product ({l | l < k} DELETE 0)
                                                 (\i. u i x))) <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(INST_TYPE [`:num`,`:A`; `:num#(num->(num->num)->bool)`,`:B`]
          (SPEC `e:real` DENSE_MODEL)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:num` (X_CHOOSE_THEN `e':real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `e' pow (2 EXP (k - 1)) / &2 pow CARD(lf_index k)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN
    ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; ARITH];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `nu:num->real`; `f:num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. zn_fam k N u
        ==> abs(fmean {y | y < N} (\y. (nu y - &1) * zn_dual k N u y)) <= e'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN
    EXISTS_TAC `2 EXP (k - 1)` THEN
    ASM_SIMP_TAC[EXP_EQ_0; ARITH_EQ; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&2 pow CARD(lf_index k) *
                (e' pow (2 EXP (k - 1)) / &2 pow CARD(lf_index k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ZN_DUAL_SINGLE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
      REWRITE_TAC[REAL_POW_EQ_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `\y:num. (nu:num->real) y - &1`;
                 `e':real`] ZN_DUAL_PRODUCT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`{y:num | y < N}`; `{c:num | c < 2} CROSS zn_S0 k N`;
    `\(s:num#(num->(num->num)->bool)) (y:num).
        (if FST s = 0 then &1 else --(&1)) * zn_dual k N (zn_ind k (SND s)) y`;
    `nu:num->real`; `f:num->real`]) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FINITE_NUMSEG_LT];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `0` THEN ASM_ARITH_TAC;
      SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT; FINITE_ZN_S0];
      REWRITE_TAC[CROSS_EQ_EMPTY; ZN_S0_NONEMPTY] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `0` THEN ARITH_TAC;
      REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; FST; SND] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
      MP_TAC(ISPECL [`k:num`; `N:num`; `zn_ind k p2`; `x:num`]
               ZN_DUAL_BOUNDS) THEN
      ASM_REWRITE_TAC[ZN_FAM_IND] THEN
      COND_CASES_TAC THEN REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM] THEN
      REAL_ARITH_TAC;
      ASM_SIMP_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`d:num`; `sq:num->num#(num->(num->num)->bool)`] THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM] THEN STRIP_TAC THEN
    SIMP_TAC[PRODUCT_MUL; FINITE_NUMSEG_LT] THEN
    ABBREV_TAC
     `sg = product {j | j < d}
             (\j. if FST((sq:num->num#(num->(num->num)->bool)) j) = 0
                  then &1 else --(&1))` THEN
    SUBGOAL_THEN `abs sg = &1` ASSUME_TAC THENL
     [EXPAND_TAC "sg" THEN SIMP_TAC[GSYM PRODUCT_ABS; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[COND_RAND; REAL_ABS_NEG; REAL_ABS_NUM; COND_ID] THEN
      REWRITE_TAC[PRODUCT_ONE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `fmean {y | y < N}
        (\x. ((nu:num->real) x - &1) *
             sg * product {j | j < d}
                    (\j. zn_dual k N
                           (zn_ind k (SND((sq:num->num#(num->(num->num)
                                                  ->bool)) j))) x)) =
      sg * fmean {y | y < N}
        (\x. (nu x - &1) *
             product {j | j < d}
               (\j. zn_dual k N (zn_ind k (SND(sq j))) x))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM FMEAN_LMUL] THEN MATCH_MP_TAC FMEAN_EQ THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_MUL_AC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_MUL_LID] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`d:num`;
      `\j. zn_ind k (SND((sq:num->num#(num->(num->num)->bool)) j))`]) THEN
    REWRITE_TAC[ZN_FAM_IND];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ft:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ft:num->real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!A. A IN zn_S0 k N
        ==> abs(fmean {y | y < N}
                  (\y. (f y - ft y) * zn_dual k N (zn_ind k A) y)) <= e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `(0,A):num#(num->(num->num)->bool)` th) THEN
      MP_TAC(SPEC `(1,A):num#(num->(num->num)->bool)` th)) THEN
    ASM_REWRITE_TAC[IN_CROSS; IN_ELIM_THM; FST; SND; ARITH] THEN
    REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_LID; REAL_MUL_RNEG] THEN
    REWRITE_TAC[fmean; SUM_NEG; real_div; REAL_MUL_LNEG] THEN
    MATCH_ACCEPT_TAC(REAL_ARITH
     `!a e:real. --a <= e ==> a <= e ==> abs a <= e`);
    ALL_TAC] THEN
  X_GEN_TAC `u:num->(num->num)->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`;
                 `\x. (f:num->real)(zn_sig k N x) - ft(zn_sig k N x)`;
                 `{l:num | l < k} DELETE 0`;
                 `\i. {l:num | l < k} DIFF {i, 0}`; `e:real`] DISC_REDUCE) THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN ANTS_TAC THENL
   [X_GEN_TAC `b:num->(num->num)->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `b:num->(num->num)->real`]
                  ZN_IND_AGREE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `A:num->(num->num)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `\y. (f:num->real) y - ft y`;
                   `b:num->(num->num)->real`] ZN_DUAL_FIBRE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(fmean {y | y < N}
                      (\y. (f y - ft y) * zn_dual k N (zn_ind k A) y))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC ZN_DUAL_EQ THEN ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `zn_fam k N (u:num->(num->num)->real)` THEN
    REWRITE_TAC[zn_fam; IN_DELETE; IN_ELIM_THM] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* From the plain sum to the edge forms.                                     *)
(* ------------------------------------------------------------------------- *)

let zn_inverse = new_definition
 `zn_inverse N a = @d. d < N /\ (a * d == 1) (mod N)`;;

let ZN_INVERSE = prove
 (`!N a. prime N /\ coprime(a,N)
         ==> zn_inverse N a < N /\ (a * zn_inverse N a == 1) (mod N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[zn_inverse] THEN
  CONV_TAC SELECT_CONV THEN
  MP_TAC(SPECL [`a:num`; `1`; `N:num`] CONG_SOLVE_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PRIME_0];
    REWRITE_TAC[EXISTS_UNIQUE] THEN MESON_TAC[]]);;

let zn_swap = new_definition
 `zn_swap j i = if i = 0 then j else if i = j then 0 else i`;;

let ZN_SWAP_SWAP = prove
 (`!j i. zn_swap j (zn_swap j i) = i`,
  REWRITE_TAC[zn_swap] THEN ARITH_TAC);;

let ZN_SWAP_LT = prove
 (`!j i k. j < k /\ i < k ==> zn_swap j i < k`,
  REWRITE_TAC[zn_swap] THEN ARITH_TAC);;

let zn_map = new_definition
 `zn_map k N j (x:num->num) =
    \l. if l < k
        then (if l = j then x 0
              else (zn_inverse N ((l + N - j) MOD N) * x (zn_swap j l)) MOD N)
        else ARB`;;

let ZCOEF_COPRIME = prove
 (`!N j l. prime N /\ j < N /\ l < N /\ ~(l = j)
           ==> coprime((l + N - j) MOD N,N)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  SUBGOAL_THEN `~((l + N - j) MOD N = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOD_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
    ASM_CASES_TAC `q = 0` THENL
     [UNDISCH_TAC `l + N - j = (q:num) * N` THEN
       ASM_REWRITE_TAC[MULT_CLAUSES] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `q = 1` THENL
     [UNDISCH_TAC `l + N - j = (q:num) * N` THEN
       ASM_REWRITE_TAC[MULT_CLAUSES] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `2 * N <= (q:num) * N` MP_TAC THENL
     [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC PRIME_COPRIME_LT THEN ASM_SIMP_TAC[MOD_LT_EQ] THEN
  ASM_ARITH_TAC);;

let ZN_SWAP_IMAGE = prove
 (`!j k. j < k
         ==> IMAGE (zn_swap j) ({l | l < k} DELETE 0) = {l | l < k} DELETE j /\
             IMAGE (zn_swap j) ({l | l < k} DELETE j) = {l | l < k} DELETE 0`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THEN STRIP_TAC THEN
  TRY(EXISTS_TAC `zn_swap j x` THEN REWRITE_TAC[ZN_SWAP_SWAP]) THEN
  ASM_REWRITE_TAC[zn_swap] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC);;

let ZN_INVERSE_COPRIME = prove
 (`!N a. prime N /\ coprime(a,N) ==> coprime(zn_inverse N a,N)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `a:num`] ZN_INVERSE) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUMBER_RULE);;

let ZN_MAP_IN_TUP = prove
 (`!k N j x. 1 <= N /\ j < k /\ x IN zn_tup k N
             ==> zn_map k N j x IN zn_tup k N`,
  REWRITE_TAC[IN_ZN_TUP; zn_map] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[MOD_LT_EQ] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC);;

let ZN_MAP_INJ = prove
 (`!k N j x y. prime N /\ k <= N /\ j < k /\
               x IN zn_tup k N /\ y IN zn_tup k N /\
               zn_map k N j x = zn_map k N j y ==> x = y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i:num < k` THENL
   [ALL_TAC; ASM_MESON_TAC[IN_ZN_TUP]] THEN
  ASM_CASES_TAC `i = 0` THENL
   [FIRST_X_ASSUM(MP_TAC o C AP_THM `j:num`) THEN
    ASM_REWRITE_TAC[zn_map];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `zn_swap j i`) THEN
  SUBGOAL_THEN
    `zn_swap j i < k /\ ~(zn_swap j i = j) /\ zn_swap j (zn_swap j i) = i`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ZN_SWAP_LT; ZN_SWAP_SWAP] THEN REWRITE_TAC[zn_swap] THEN
    REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[zn_map] THEN DISCH_TAC THEN
  MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
  REPEAT CONJ_TAC THENL [ASM_MESON_TAC[IN_ZN_TUP]; ASM_MESON_TAC[IN_ZN_TUP];
                         ALL_TAC] THEN
  MATCH_MP_TAC CONG_MULT_LCANCEL THEN
  EXISTS_TAC `zn_inverse N ((zn_swap j i + N - j) MOD N)` THEN
  ASM_REWRITE_TAC[CONG] THEN MATCH_MP_TAC ZN_INVERSE_COPRIME THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZCOEF_COPRIME THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let ZN_PSI_MAP = prove
 (`!k N j x. prime N /\ k <= N /\ j < k /\ x IN zn_tup k N
             ==> zn_psi k N j (zn_map k N j x) = zn_sig k N x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_psi; zn_sig; zn_lin; MULT_CLAUSES] THEN
  SUBGOAL_THEN
   `nsum ({l | l < k} DELETE 0) (\i. (x:num->num) i) =
    nsum ({l | l < k} DELETE j) (\l. x(zn_swap j l))`
  SUBST1_TAC THENL
   [MP_TAC(SPECL [`j:num`; `k:num`] ZN_SWAP_IMAGE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
      [GSYM(CONJUNCT2 th)]) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) NSUM_IMAGE o lhand o snd) THEN
    ANTS_TAC THENL [MESON_TAC[ZN_SWAP_SWAP]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM CONG] THEN MATCH_MP_TAC CONG_NSUM THEN
  SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `l:num` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[zn_map] THEN
  MP_TAC(SPECL [`N:num`; `(l + N - j) MOD N`] ZN_INVERSE) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZCOEF_COPRIME THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SPEC_TAC(`zn_inverse N ((l + N - j) MOD N)`,`d:num`) THEN
  SPEC_TAC(`(l + N - j) MOD N`,`c:num`) THEN
  SPEC_TAC(`(x:num->num)(zn_swap j l)`,`z:num`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `c * d * z:num` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL; CONG_LMOD];
    UNDISCH_TAC `(c * d == 1) (mod N)` THEN CONV_TAC NUMBER_RULE]);;

let EDGE_TRANSFER = prove
 (`!k N j (u:num->(num->num)->real) (F1:num->real).
        prime N /\ k <= N /\ j < k /\
        (!i. i < k /\ ~(i = j)
             ==> zn_depon ({l | l < k} DIFF {i, j}) (u i) /\
                 !x. x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1)
        ==> zn_fam k N (\i x. u (zn_swap j i) (zn_map k N j x)) /\
            fmean (zn_tup k N)
              (\x. F1(zn_psi k N j x) *
                   product ({l | l < k} DELETE j) (\i. u i x)) =
            fmean (zn_tup k N)
              (\x. F1(zn_sig k N x) *
                   product ({l | l < k} DELETE 0)
                     (\i. u (zn_swap j i) (zn_map k N j x)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[zn_fam] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `zn_swap j i < k /\ ~(zn_swap j i = j)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[ZN_SWAP_LT] THEN REWRITE_TAC[zn_swap] THEN
      REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `zn_swap j i`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[zn_depon] THEN MAP_EVERY X_GEN_TAC [`x:num->num`;
      `y:num->num`] THEN
      DISCH_TAC THEN UNDISCH_TAC
       `zn_depon ({l | l < k} DIFF {zn_swap j i, j}) ((u:num->(num->num)->real)
                                               (zn_swap j i))` THEN
      REWRITE_TAC[zn_depon] THEN DISCH_THEN MATCH_MP_TAC THEN
      X_GEN_TAC `l:num` THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY;
       DE_MORGAN_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[zn_map] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC[ZN_SWAP_LT] THEN
      UNDISCH_TAC `~(l = zn_swap j i)` THEN UNDISCH_TAC `~(l:num = j)` THEN
      REWRITE_TAC[zn_swap] THEN REPEAT COND_CASES_TAC THEN ASM_ARITH_TAC;
      X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[ZN_MAP_IN_TUP]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `zn_map k N j`;
                 `\x. (F1:num->real)(zn_psi k N j x) *
                      product ({l | l < k} DELETE j)
                        (\i. (u:num->(num->num)->real) i x)`] FMEAN_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ZN_MAP_IN_TUP] THEN ASM_MESON_TAC[ZN_MAP_INJ]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FMEAN_EQ THEN
  X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ZN_PSI_MAP] THEN AP_TERM_TAC THEN
  MP_TAC(SPECL [`j:num`; `k:num`] ZN_SWAP_IMAGE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
    [GSYM(CONJUNCT1 th)]) THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [MESON_TAC[ZN_SWAP_SWAP]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]);;

let ZN_DISCREPANCY = prove
 (`!k e. 1 < k /\ &0 < e /\ e <= &1
         ==> ?eta. &0 < eta /\
               !N (nu:num->real) f.
                 prime N /\ k <= N /\
                 lf_cond k N (\j x. nu(zn_psi k N j x)) eta /\
                 (!y. y < N ==> &0 <= f y /\ f y <= nu y)
                 ==> ?ft. (!y. &0 <= ft y /\ ft y <= &1) /\
                          (!j. j < k
                               ==> zn_hdisc k N j (\x. f(zn_psi k N j x))
                                               (\x. ft(zn_psi k N j x)) e) /\
                          abs(fmean {y | y < N} f - fmean {y | y < N} ft)
                          <= e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `e:real`] ZN_DENSE_MODEL) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `eta:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `nu:num->real`; `f:num->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `nu:num->real`; `f:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `ft:num->real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `1 <= N` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[zn_hdisc] THEN
    X_GEN_TAC `u:num->(num->num)->real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:num`; `N:num`; `j:num`; `u:num->(num->num)->real`;
                   `\y. (f:num->real) y - ft y`] EDGE_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\i:num x:num->num. &1`) THEN
  REWRITE_TAC[ZN_FAM_ONE] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `\y. (f:num->real) y - ft y`;
                 `\i:num x:num->num. &1`] ZN_DUAL_FIBRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> abs a <= e ==> abs b <= e`) THEN
  SIMP_TAC[GSYM FMEAN_SUB; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC FMEAN_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM; ZN_DUAL_ONE] THEN
  REWRITE_TAC[REAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* The progression count.                                                    *)
(* ------------------------------------------------------------------------- *)

let zn_A = new_definition `zn_A k N x = zn_lin N (\i. i) {l | l < k} x`;;

let zn_S = new_definition `zn_S k N x = zn_lin N (\i. 1) {l | l < k} x`;;

let zn_D = new_definition `zn_D k N x = (N - zn_S k N x) MOD N`;;

let ZN_PSI_CONG = prove
 (`!k N j x. j < k /\ k <= N
             ==> (zn_psi k N j x + j * zn_S k N x == zn_A k N x) (mod N)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[zn_psi; zn_S; zn_A; zn_lin; MULT_CLAUSES] THEN
  MATCH_MP_TAC CONG_TRANS THEN
  EXISTS_TAC `nsum ({l | l < k} DELETE j) (\i. ((i + N - j) MOD N) * x i) +
              j * nsum {l | l < k} (\i. (x:num->num) i)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_LMOD; CONG_REFL] THEN
    MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL; CONG_LMOD];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN REWRITE_TAC[CONG_LMOD] THEN
  ONCE_REWRITE_TAC[CONG_SYM] THEN
  SUBGOAL_THEN `FINITE {l:num | l < k} /\ j IN {l:num | l < k}`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP NSUM_DELETE th)]) THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM NSUM_LMUL] THEN
  REWRITE_TAC[ARITH_RULE `a + b + c = b + (a + c:num)`] THEN
  SIMP_TAC[GSYM NSUM_ADD; FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL] THEN
  MATCH_MP_TAC CONG_NSUM THEN SIMP_TAC[FINITE_DELETE; FINITE_NUMSEG_LT] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
  MATCH_MP_TAC CONG_MULT THEN REWRITE_TAC[CONG_REFL] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `((i:num) + N - j) + j` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL; CONG_LMOD];
    SUBGOAL_THEN `((i:num) + N - j) + j = i + N` SUBST1_TAC THENL
     [ASM_ARITH_TAC; CONV_TAC NUMBER_RULE]]);;

let ZN_PSI_AP = prove
 (`!k N j x. ~(N = 0) /\ j < k /\ k <= N
             ==> zn_psi k N j x = (zn_A k N x + j * zn_D k N x) MOD N`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
  EXISTS_TAC `N:num` THEN ASM_SIMP_TAC[MOD_LT_EQ; zn_psi; ZN_LIN_LT] THEN
  REWRITE_TAC[CONG_RMOD; GSYM zn_psi] THEN
  ONCE_REWRITE_TAC[GSYM(SPEC `j * zn_S k N x` CONG_ADD_RCANCEL_EQ)] THEN
  MATCH_MP_TAC CONG_TRANS THEN EXISTS_TAC `zn_A k N x` THEN
  ASM_SIMP_TAC[ZN_PSI_CONG] THEN
  REWRITE_TAC[GSYM ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
  SUBGOAL_THEN `(zn_D k N x + zn_S k N x == 0) (mod N)` MP_TAC THENL
   [REWRITE_TAC[zn_D] THEN MATCH_MP_TAC CONG_TRANS THEN
    EXISTS_TAC `(N - zn_S k N x) + zn_S k N x` THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONG_ADD THEN REWRITE_TAC[CONG_REFL; CONG_LMOD];
      ALL_TAC] THEN
    SUBGOAL_THEN `zn_S k N x < N` MP_TAC THENL
     [ASM_SIMP_TAC[zn_S; ZN_LIN_LT]; ALL_TAC] THEN
    SIMP_TAC[ARITH_RULE `(s:num) < n ==> n - s + s = n`] THEN
    DISCH_TAC THEN CONV_TAC NUMBER_RULE;
    MATCH_ACCEPT_TAC(NUMBER_RULE
     `!a b j n. (b:num == 0) (mod n) ==> (a == a + j * b) (mod n)`)]);;

let zn_ab = new_definition
 `zn_ab k N x = \i. if i = 0 then zn_D k N x else if i = 1 then zn_A k N x
   else x i`;;

let NSUM_LT_SPLIT2 = prove
 (`!k (f:num->num).
        2 <= k
        ==> nsum {l | l < k} f = f 0 + f 1 + nsum {l | 2 <= l /\ l < k} f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{l:num | l < k} = 0 INSERT 1 INSERT {l | 2 <= l /\ l < k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {l:num | 2 <= l /\ l < k}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{l:num | l < k}` THEN
    SIMP_TAC[FINITE_NUMSEG_LT; SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CLAUSES; FINITE_INSERT; IN_INSERT; IN_ELIM_THM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_ASSOC]);;

let ZN_AB_IN_TUP = prove
 (`!k N x. 2 <= k /\ ~(N = 0) /\ x IN zn_tup k N
           ==> zn_ab k N x IN zn_tup k N`,
  REWRITE_TAC[IN_ZN_TUP; zn_ab] THEN REPEAT STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN
  ASM_SIMP_TAC[zn_D; zn_A; ZN_LIN_LT; MOD_LT_EQ] THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC);;

let ZD_INJ = prove
 (`!N a b. a < N /\ b < N /\ (N - a) MOD N = (N - b) MOD N ==> a = b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(N - a) MOD N = (N - b) MOD N` THEN REWRITE_TAC[GSYM CONG] THEN
  ONCE_REWRITE_TAC[GSYM(SPEC `a + b:num` CONG_ADD_RCANCEL_EQ)] THEN
  ASM_SIMP_TAC[ARITH_RULE `a:num < n /\ b < n
                ==> n - a + a + b = n + b /\ n - b + a + b = n + a`] THEN
  CONV_TAC NUMBER_RULE);;

let ZN_S_CANCEL0 = prove
 (`!k N x y. 2 <= k /\ x 0 < N /\ y 0 < N /\ x 1 = y 1 /\
             (!i. 2 <= i /\ i < k ==> x i = y i) /\ zn_S k N x = zn_S k N y
             ==> x 0 = y 0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `zn_S k N x = zn_S k N y` THEN
  ASM_SIMP_TAC[zn_S; zn_lin; NSUM_LT_SPLIT2; MULT_CLAUSES] THEN
  SUBGOAL_THEN
   `nsum {l | 2 <= l /\ l < k} (\i. (x:num->num) i) =
    nsum {l | 2 <= l /\ l < k} (\i. y i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONG; GSYM ADD_ASSOC; CONG_ADD_RCANCEL_EQ] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
  ASM_REWRITE_TAC[]);;

let ZN_A_CANCEL1 = prove
 (`!k N x y. 2 <= k /\ x 1 < N /\ y 1 < N /\
             (!i. 2 <= i /\ i < k ==> x i = y i) /\ zn_A k N x = zn_A k N y
             ==> x 1 = y 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `zn_A k N x = zn_A k N y` THEN
  ASM_SIMP_TAC[zn_A; zn_lin; NSUM_LT_SPLIT2; MULT_CLAUSES; ADD_CLAUSES] THEN
  SUBGOAL_THEN
   `nsum {l | 2 <= l /\ l < k} (\i. i * (x:num->num) i) =
    nsum {l | 2 <= l /\ l < k} (\i. i * y i)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM CONG; CONG_ADD_RCANCEL_EQ] THEN
  DISCH_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN EXISTS_TAC `N:num` THEN
  ASM_REWRITE_TAC[]);;

let ZN_AB_INJ = prove
 (`!k N x y. 2 <= k /\ ~(N = 0) /\ x IN zn_tup k N /\ y IN zn_tup k N /\
             zn_ab k N x = zn_ab k N y ==> x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!i. ~(i = 0) /\ ~(i = 1) ==> (x:num->num) i = y i`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o C AP_THM `i:num`) THEN
    REWRITE_TAC[zn_ab] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `zn_A k N x = zn_A k N y /\ zn_D k N x = zn_D k N y`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o C AP_THM `1`) THEN REWRITE_TAC[zn_ab; ARITH_EQ];
      FIRST_ASSUM(MP_TAC o C AP_THM `0`) THEN REWRITE_TAC[zn_ab]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->num) 0 < N /\ y 0 < N /\ x 1 < N /\ y 1 < N`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(x:num->num) IN zn_tup k N`; `(y:num->num) IN zn_tup k N`;
      `2 <= k`] THEN
    REWRITE_TAC[IN_ZN_TUP] THEN
    MESON_TAC[ARITH_RULE `2 <= k ==> 0 < k /\ 1 < k`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 2 <= i /\ i < k ==> (x:num->num) i = y i` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->num) 1 = y 1` ASSUME_TAC THENL
   [MATCH_MP_TAC ZN_A_CANCEL1 THEN MAP_EVERY EXISTS_TAC [`k:num`; `N:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->num) 0 = y 0` ASSUME_TAC THENL
   [MATCH_MP_TAC ZN_S_CANCEL0 THEN MAP_EVERY EXISTS_TAC [`k:num`; `N:num`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ZD_INJ THEN EXISTS_TAC `N:num` THEN
    ASM_SIMP_TAC[zn_S; ZN_LIN_LT] THEN ASM_REWRITE_TAC[GSYM zn_S; GSYM zn_D];
    ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = 1` THEN ASM_SIMP_TAC[]);;

let FMEAN_TWO_COORDS = prove
 (`!k N (G:num->num->real).
        2 <= k /\ 1 <= N
        ==> fmean (zn_tup k N) (\x. G (x 1) (x 0)) =
            fmean {a | a < N} (\a. fmean {d | d < N} (\d. G a d))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `0`;
   `\x:num->num. (G:num->num->real) (x 1) (x 0)`]
                ZN_TUP_FMEAN_COORD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[zn_upd; ARITH_EQ] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `1`;
                 `\x:num->num. fmean {r | r < N}
                   (\r. (G:num->num->real) (x 1) r)`]
                ZN_TUP_FMEAN_COORD) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ZN_UPD_AT] THEN MATCH_MP_TAC FMEAN_CONST THEN
  ASM_SIMP_TAC[FINITE_ZN_TUP; ZN_TUP_NONEMPTY]);;

let ZN_HCOUNT_AP = prove
 (`!k N (f:num->real).
        2 <= k /\ k <= N /\ ~(N = 0)
        ==> zn_hcount k N (\j x. f(zn_psi k N j x)) =
            fmean {a | a < N}
              (\a. fmean {d | d < N}
                     (\d. product {j | j < k} (\j. f((a + j * d) MOD N))))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_hcount] THEN
  SUBGOAL_THEN
   `fmean (zn_tup k N) (\x. product {j | j < k} (\j. f(zn_psi k N j x))) =
    fmean (zn_tup k N)
      (\x. (\a d. product {j | j < k} (\j. (f:num->real)((a + j * d) MOD N)))
           (zn_ab k N x 1) (zn_ab k N x 0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC FMEAN_EQ THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[zn_ab; ARITH_EQ] THEN MATCH_MP_TAC PRODUCT_EQ THEN
    SIMP_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[ZN_PSI_AP] THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC ZN_PSI_AP THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `zn_ab k N`;
                 `\y:num->num. (\a d. product {j | j < k}
                     (\j. (f:num->real)((a + j * d) MOD N))) (y 1) (y 0)`]
                FMEAN_INJ) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ZN_AB_IN_TUP] THEN ASM_MESON_TAC[ZN_AB_INJ]; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`k:num`; `N:num`;
                 `\a d. product {j | j < k}
                     (\j. (f:num->real)((a + j * d) MOD N))`]
                FMEAN_TWO_COORDS) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The relative AP theorem on Z_N.                                           *)
(* ------------------------------------------------------------------------- *)

let ZN_DEPON_PSI = prove
 (`!k N j (F1:num->real).
        zn_depon ({l | l < k} DELETE j) (\x. F1(zn_psi k N j x))`,
  REWRITE_TAC[zn_depon; zn_psi; zn_lin] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC NSUM_EQ THEN
  ASM_SIMP_TAC[]);;

let ZN_RELATIVE_AP = prove
 (`!k gam.
        2 <= k /\ &0 < gam
        ==> ?eta. &0 < eta /\
              !N (nu:num->real) f.
                prime N /\ k <= N /\
                lf_cond k N (\j x. nu(zn_psi k N j x)) eta /\
                (!y. y < N ==> &0 <= f y /\ f y <= nu y)
                ==> ?ft. (!y. &0 <= ft y /\ ft y <= &1) /\
                         abs(fmean {y | y < N} f - fmean {y | y < N} ft)
                         <= gam /\
                         abs(fmean {a | a < N}
                               (\a. fmean {d | d < N}
                                  (\d. product {j | j < k}
                                         (\j. f((a + j * d) MOD N)))) -
                             fmean {a | a < N}
                               (\a. fmean {d | d < N}
                                  (\d. product {j | j < k}
                                         (\j. ft((a + j * d) MOD N)))))
                         <= gam`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `k:num`; `gam:real`] GT_COUNTING_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (X_CHOOSE_THEN `n1:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`k:num`; `min e1 (min gam (&1))`] ZN_DISCREPANCY) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC ORELSE ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n2:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min n1 n2` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `nu:num->real`; `f:num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `~(N = 0) /\ 1 <= N` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `nu:num->real`; `f:num->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LF_COND_MONO THEN
    EXISTS_TAC `min n1 n2` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ft:num->real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `!x e g:real. x <= min e (min g (&1)) ==> x <= g`) THEN
    EXISTS_TAC `e1:real` THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM ZN_HCOUNT_AP] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `{j:num | j < k}` THEN
  EXISTS_TAC `\j x. (nu:num->real)(zn_psi k N j x)` THEN
  REWRITE_TAC[zn_hsys; CARD_NUMSEG_LT; SUBSET_REFL; IN_ELIM_THM] THEN
  ASM_REWRITE_TAC[ZN_DEPON_PSI] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LF_COND_MONO THEN EXISTS_TAC `min n1 n2` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ZN_HDISC_MONO THEN EXISTS_TAC `min e1 (min gam (&1))` THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `zn_psi k N j x < N` ASSUME_TAC THENL
     [ASM_SIMP_TAC[zn_psi; ZN_LIN_LT]; ASM_SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* The linear forms condition from integer forms.                            *)
(* ------------------------------------------------------------------------- *)

let INT_OF_NUM_NSUM = prove
 (`!(f:A->num) s. FINITE s ==> &(nsum s f) = isum s (\i. &(f i))`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[NSUM_CLAUSES; ISUM_CLAUSES; GSYM INT_OF_NUM_ADD]);;

let INT_CONG_ISUM = prove
 (`!n (f:A->int) g s.
        FINITE s /\ (!i. i IN s ==> (f i == g i) (mod n))
        ==> (isum s f == isum s g) (mod n)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[ISUM_CLAUSES; IN_INSERT] THEN
  CONJ_TAC THENL [CONV_TAC INTEGER_RULE; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!a b a' b' n:int. (a == a') (mod n) /\ (b == b') (mod n)
                      ==> (a + b == a' + b') (mod n)`) THEN
  ASM_MESON_TAC[]);;

let LF_FORM_ZN_LIN = prove
 (`!s (c:num->int) d N x.
        FINITE s /\ ~(N = 0) /\ (!i. i IN s ==> (c i == &(d i)) (mod &N))
        ==> num_of_int(lf_form s c (&0) x rem &N) = zn_lin N d s x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_lin] THEN
  MATCH_MP_TAC(MESON[NUM_OF_INT_OF_NUM] `a = &b ==> num_of_int a = b`) THEN
  REWRITE_TAC[GSYM INT_OF_NUM_REM; INT_REM_EQ] THEN
  ASM_SIMP_TAC[INT_OF_NUM_NSUM; lf_form; INT_ADD_RID; GSYM INT_OF_NUM_MUL] THEN
  MATCH_MP_TAC INT_CONG_ISUM THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!c d x n:int. (c == d) (mod n) ==> (c * x == d * x) (mod n)`) THEN
  ASM_SIMP_TAC[]);;

let NSUM_LT_DOUBLE = prove
 (`!k (g:num->num).
        nsum {i | i < 2 * k} g =
        nsum {i | i < k} g + nsum {i | i < k} (\i. g(k + i))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{i | i < 2 * k} = {i | i < k} UNION IMAGE (\i. k + i)
    {i | i < k}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `i:num` THEN EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `i:num < k` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `i - k:num` THEN ASM_ARITH_TAC;
      STRIP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_NUMSEG_LT; FINITE_IMAGE] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) NSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL [ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF]);;

let zn_lo = new_definition
 `zn_lo k (z:num->num) = \i. if i < k then z i else ARB`;;

let zn_hi = new_definition
 `zn_hi k (z:num->num) = \i. if i < k then z (k + i) else ARB`;;

let zn_dcoef = new_definition
 `zn_dcoef k N j (W:num->bool) =
    \i. if i < k then (if i = j \/ i IN W then 0 else (i + N - j) MOD N)
        else if i < 2 * k /\ ~(i - k = j) /\ (i - k) IN W
             then ((i - k) + N - j) MOD N else 0`;;

let zn_coef = new_definition
 `zn_coef k j (W:num->bool) =
    \i. if i < k then (if i = j \/ i IN W then &0 else &i - &j)
        else if i < 2 * k /\ ~(i - k = j) /\ (i - k) IN W
             then &(i - k) - &j else (&0:int)`;;

let ZN_PSI_MIX_LIN = prove
 (`!k N j W z.
        j < k
        ==> zn_psi k N j (zn_mix W (zn_lo k z) (zn_hi k z)) =
            zn_lin N (zn_dcoef k N j W) {i | i < 2 * k} z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_psi; zn_lin; NSUM_LT_DOUBLE] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[GSYM NSUM_ADD; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `FINITE {l:num | l < k} /\ j IN {l:num | l < k}`
  (fun th -> REWRITE_TAC[GSYM(MATCH_MP NSUM_DELETE th)]) THENL
   [ASM_REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[zn_dcoef; ADD_SUB2; ARITH_RULE `~(k + i < k:num)`] THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `i < k ==> k + i < 2 * k`] THEN
  REWRITE_TAC[zn_mix; zn_lo; zn_hi] THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

let INT_CONG_SUBMOD = prove
 (`!a j N. j <= N ==> (&a - &j:int == &((a + N - j) MOD N)) (mod &N)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `!x y z n:int. (x == y) (mod n) /\ (z == y) (mod n) ==> (x == z)
     (mod n)`) THEN
  EXISTS_TAC `&(a + N - j):int` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_SUB] THEN
    CONV_TAC INTEGER_RULE;
    REWRITE_TAC[GSYM num_congruent; CONG_LMOD; CONG_REFL]]);;

let ZN_COEF_CONG = prove
 (`!k N j W i. j < k /\ k <= N
               ==> (zn_coef k j W i == &(zn_dcoef k N j W i)) (mod &N)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_coef; zn_dcoef] THEN
  ASM_CASES_TAC `i:num < k` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN REWRITE_TAC[INTEGER_RULE `(x:int == x) (mod n)`] THEN
  MATCH_MP_TAC INT_CONG_SUBMOD THEN ASM_ARITH_TAC);;

let zn_cat = new_definition
 `zn_cat k (x0:num->num) x1 =
    \i. if i < k then x0 i else if i < 2 * k then x1 (i - k) else ARB`;;

let ZN_MEAN2_ZTUP2 = prove
 (`!k N (F2:(num->num)->(num->num)->real).
        zn_mean2 k N F2 =
        fmean (zn_tup (2 * k) N) (\z. F2 (zn_lo k z) (zn_hi k z))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_mean2; fmean; CARD_ZN_TUP] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_ZN_TUP] THEN
  SUBGOAL_THEN
   `sum (zn_tup (2 * k) N) (\z. F2 (zn_lo k z) (zn_hi k z)) =
    sum {x0,x1 | x0 IN zn_tup k N /\ x1 IN zn_tup k N}
        (\(x0,x1). (F2:(num->num)->(num->num)->real) x0 x1)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_GENERAL THEN
    EXISTS_TAC `\z:num->num. (zn_lo k z,zn_hi k z)` THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN STRIP_TAC THEN
      REWRITE_TAC[EXISTS_UNIQUE] THEN EXISTS_TAC `zn_cat k x0 x1` THEN
      REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `(x0:num->num) IN zn_tup k N` THEN
        UNDISCH_TAC `(x1:num->num) IN zn_tup k N` THEN
        REWRITE_TAC[IN_ZN_TUP; zn_cat] THEN REPEAT STRIP_TAC THEN
        REPEAT COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
        TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM_ARITH_TAC;
        UNDISCH_TAC `(x0:num->num) IN zn_tup k N` THEN
        REWRITE_TAC[IN_ZN_TUP; zn_cat; zn_lo; FUN_EQ_THM] THEN
        MESON_TAC[];
        UNDISCH_TAC `(x1:num->num) IN zn_tup k N` THEN
        REWRITE_TAC[IN_ZN_TUP; zn_cat; zn_hi; FUN_EQ_THM] THEN
        REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
        ASM_SIMP_TAC[ARITH_RULE `~(k + i < k:num)`; ADD_SUB2;
                     ARITH_RULE `i < k ==> k + i < 2 * k`];
        X_GEN_TAC `z:num->num` THEN REWRITE_TAC[IN_ZN_TUP] THEN STRIP_TAC THEN
        REWRITE_TAC[FUN_EQ_THM; zn_cat] THEN X_GEN_TAC `i:num` THEN
        ASM_CASES_TAC `i:num < k` THEN ASM_REWRITE_TAC[] THENL
         [UNDISCH_TAC `zn_lo k z = (x0:num->num)` THEN
          REWRITE_TAC[FUN_EQ_THM; zn_lo] THEN
          DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        COND_CASES_TAC THENL
         [UNDISCH_TAC `zn_hi k z = (x1:num->num)` THEN
          REWRITE_TAC[FUN_EQ_THM; zn_hi] THEN
          DISCH_THEN(MP_TAC o SPEC `i - k:num`) THEN
          ASM_SIMP_TAC[ARITH_RULE `~(i < k) /\ i < 2 * k ==> i - k < k`] THEN
          ASM_SIMP_TAC[ARITH_RULE `!i k. ~(i < k) ==> k + i - k = i:num`];
          ASM_SIMP_TAC[]]];
      X_GEN_TAC `z:num->num` THEN REWRITE_TAC[IN_ZN_TUP; zn_lo; zn_hi] THEN
      STRIP_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `2 * k = k + k`; REAL_POW_ADD; REAL_INV_MUL] THEN
  REWRITE_TAC[REAL_MUL_AC]);;

let ZN_COEF_BOUND = prove
 (`!k j W i. j < k /\ i < 2 * k ==> abs(zn_coef k j W i) <= &k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_coef] THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[INT_ABS_NUM; INT_POS] THEN
  MATCH_MP_TAC(INT_ARITH
   `!a j k. &a:int < &k /\ &j:int < &k /\ &0:int <= &a /\ &0:int <= &j
            ==> abs(&a - &j:int) <= &k`) THEN
  REWRITE_TAC[INT_POS; INT_OF_NUM_LT] THEN ASM_ARITH_TAC);;

let ZN_COEF_AT = prove
 (`!k j W l. l < k /\ ~(l = j)
             ==> zn_coef k j W (if l IN W then k + l else l) = &l - &j /\
                 zn_coef k j W (if l IN W then l else k + l) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(l:num) IN W` THEN ASM_REWRITE_TAC[zn_coef] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(k + l < k:num)`; ADD_SUB2] THEN
  ASM_SIMP_TAC[ARITH_RULE `l < k ==> k + l < 2 * k`]);;

let ZN_COEF_SELF = prove
 (`!k j W. j < k ==> zn_coef k j W j = &0 /\ zn_coef k j W (k + j) = &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_coef] THEN
  ASM_REWRITE_TAC[ARITH_RULE `~(k + l < k:num)`; ADD_SUB2]);;

let ZN_COEF_NONZERO = prove
 (`!k j W. 2 <= k /\ j < k ==> ?i. i < 2 * k /\ ~(zn_coef k j W i = &0)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `l = if j = 0 then 1 else (0:num)` THEN
  SUBGOAL_THEN `(l:num) < k /\ ~(l = j)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN COND_CASES_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `if (l:num) IN W then k + l else l` THEN
  ASM_SIMP_TAC[ZN_COEF_AT; INT_SUB_0; INT_OF_NUM_EQ] THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

let ZN_COEF_INDEP = prove
 (`!k j W j' W'.
        j < k /\ W SUBSET {l | l < k} DELETE j /\
        j' < k /\ W' SUBSET {l | l < k} DELETE j' /\
        ~((j,W) = (j',W'))
        ==> ?i i'. i < 2 * k /\ i' < 2 * k /\ ~(i = i') /\
                   ~(zn_coef k j W i = &0) /\
                   ~(zn_coef k j W i * zn_coef k j' W' i' -
                     zn_coef k j W i' * zn_coef k j' W' i = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `j:num = j'` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `?l:num. ~(l IN W <=> l IN W')` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((j':num,W:num->bool) = (j',W'))` THEN
      REWRITE_TAC[PAIR_EQ; EXTENSION] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `l:num < k /\ ~(l = j')` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(SPECL [`k:num`; `j':num`; `W:num->bool`; `l:num`] ZN_COEF_AT) THEN
    MP_TAC(SPECL [`k:num`; `j':num`; `W':num->bool`; `l:num`] ZN_COEF_AT) THEN
    ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `(l:num) IN W` THENL
     [SUBGOAL_THEN `~((l:num) IN W')` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`k + l:num`; `l:num`];
      SUBGOAL_THEN `(l:num) IN W'` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`l:num`; `k + l:num`]] THEN
    ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_SUB_RZERO; INT_ENTIRE;
                    INT_SUB_0; INT_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`if (j':num) IN W then k + j' else j'`;
    `if (j:num) IN W' then k + j else j`] THEN
  ASM_CASES_TAC `(j':num) IN W` THEN ASM_CASES_TAC `(j:num) IN W'` THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_ARITH_TAC THEN
  MP_TAC(SPECL [`k:num`; `j:num`; `W:num->bool`; `j':num`] ZN_COEF_AT) THEN
  MP_TAC(SPECL [`k:num`; `j':num`; `W':num->bool`; `j:num`] ZN_COEF_AT) THEN
  MP_TAC(SPECL [`k:num`; `j':num`; `W':num->bool`] ZN_COEF_SELF) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO; INT_SUB_RZERO; INT_ENTIRE;
              INT_SUB_0; INT_OF_NUM_EQ] THEN
  ASM_ARITH_TAC);;

let lf_hyp = new_definition
 `lf_hyp N (nu:num->real) t m K eta <=>
    !Js (c:num->num->int).
      FINITE Js /\ CARD Js <= m /\
      (!j i. j IN Js /\ i < t ==> abs(c j i) <= &K) /\
      (!j. j IN Js ==> ?i. i < t /\ ~(c j i = &0)) /\
      (!j j'. j IN Js /\ j' IN Js /\ ~(j = j')
              ==> ?i i'. i < t /\ i' < t /\ ~(i = i') /\ ~(c j i = &0) /\
                         ~(c j i * c j' i' - c j i' * c j' i = &0))
      ==> abs(sum (cartesian_product {i | i < t} (\i. {r | r < N}))
                  (\x. product Js
                         (\j. nu(num_of_int(lf_form {i | i < t} (c j) (&0) x
                                            rem &N)))) / &N pow t - &1)
          <= eta`;;

let LF_COND_FROM_HYP = prove
 (`!k N (nu:num->real) eta.
        2 <= k /\ k <= N /\
        lf_hyp N nu (2 * k) (CARD(lf_index k)) k eta
        ==> lf_cond k N (\j x. nu(zn_psi k N j x)) eta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(N = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lf_cond] THEN X_GEN_TAC `S:num#(num->bool)->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FINITE(S:num#(num->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_LF_INDEX]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_INDEX_NUMBERS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `Js:num->bool` (X_CHOOSE_THEN
    `sg:num->num#(num->bool)` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!m. m IN Js ==> FST((sg:num->num#(num->bool)) m) < k /\
                    SND(sg m) SUBSET {l | l < k} DELETE FST(sg m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(sg:num->num#(num->bool)) m IN lf_index k` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SPEC_TAC(`(sg:num->num#(num->bool)) m`,`p:num#(num->bool)`) THEN
    REWRITE_TAC[FORALL_PAIR_THM; lf_index; IN_ELIM_PAIR_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`Js:num->bool`;
    `\m. zn_coef k (FST((sg:num->num#(num->bool)) m)) (SND(sg m))`] o
   GEN_REWRITE_RULE I [lf_hyp]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD(S:num#(num->bool)->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC EQ_IMP_LE THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_LF_INDEX]];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ZN_COEF_BOUND THEN ASM_SIMP_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC ZN_COEF_NONZERO THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`m:num`; `m':num`] THEN STRIP_TAC THEN
      MATCH_MP_TAC ZN_COEF_INDEP THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[GSYM PAIR_EQ; PAIR] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> abs(a - &1) <= e ==> abs(b - &1)
    <= e`) THEN
  REWRITE_TAC[ZN_MEAN2_ZTUP2; fmean; CARD_ZN_TUP] THEN REWRITE_TAC[zn_tup] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `z:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o rand o snd) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC PRODUCT_EQ THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(sg:num->num#(num->bool)) m`,`p:num#(num->bool)`) THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `W:num->bool`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ZN_PSI_MIX_LIN] THEN
  MATCH_MP_TAC LF_FORM_ZN_LIN THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ZN_COEF_CONG THEN ASM_REWRITE_TAC[]);;

let ZN_TRANSFERENCE = prove
 (`!k gam.
        2 <= k /\ &0 < gam
        ==> ?eta. &0 < eta /\
              !N (nu:num->real) f.
                prime N /\ k <= N /\
                lf_hyp N nu (2 * k) (CARD(lf_index k)) k eta /\
                (!y. y < N ==> &0 <= f y /\ f y <= nu y)
                ==> ?ft. (!y. &0 <= ft y /\ ft y <= &1) /\
                         abs(fmean {y | y < N} f - fmean {y | y < N} ft)
                         <= gam /\
                         abs(fmean {a | a < N}
                               (\a. fmean {d | d < N}
                                  (\d. product {j | j < k}
                                         (\j. f((a + j * d) MOD N)))) -
                             fmean {a | a < N}
                               (\a. fmean {d | d < N}
                                  (\d. product {j | j < k}
                                         (\j. ft((a + j * d) MOD N)))))
                         <= gam`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `gam:real`] ZN_RELATIVE_AP) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `eta:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `nu:num->real` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LF_COND_FROM_HYP THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The relative Szemeredi theorem.                                           *)
(* ------------------------------------------------------------------------- *)

let RELATIVE_SZEMEREDI = prove
 (`!k delta.
        2 <= k /\ &0 < delta
        ==> ?c eta N0.
              &0 < c /\ &0 < eta /\
              !N (nu:num->real) f.
                N0 <= N /\ prime N /\
                lf_hyp N nu (2 * k) (CARD(lf_index k)) k eta /\
                (!y. y < N ==> &0 <= f y /\ f y <= nu y) /\
                delta <= fmean {y | y < N} f
                ==> c <= fmean {a | a < N}
                           (\a. fmean {d | d < N}
                                  (\d. product {j | j < k}
                                         (\j. f((a + j * d) MOD N))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `k:num` WEIGHTED_SZEMEREDI) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[weighted_szemeredi] THEN
  DISCH_THEN(MP_TAC o SPEC `delta / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `csz:real` (X_CHOOSE_THEN `N1:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "wsz")))) THEN
  MP_TAC(SPECL [`k:num`; `min (delta / &2) (csz / &2)`] ZN_TRANSFERENCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "transfer"))) THEN
  MAP_EVERY EXISTS_TAC [`csz / &2`; `eta:real`; `N1 + k:num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`N:num`; `nu:num->real`; `f:num->real`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "transfer" (MP_TAC o SPECL
   [`N:num`; `nu:num->real`; `f:num->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ft:num->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `ef = fmean {y | y < N} (f:num->real)` THEN
  ABBREV_TAC `eft = fmean {y:num | y < N} ft` THEN
  ABBREV_TAC
   `apf = fmean {a | a < N}
            (\a. fmean {d | d < N}
                   (\d. product {j | j < k} (\j. (f:num->real)((a + j * d)
                     MOD N))))` THEN
  ABBREV_TAC
   `apft = fmean {a | a < N}
             (\a. fmean {d | d < N}
                    (\d. product {j | j < k} (\j. ft((a + j * d)
                      MOD N))))` THEN
  REMOVE_THEN "wsz" (MP_TAC o SPECL [`N:num`; `ft:num->real`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`abs(ef - eft) <= min (delta / &2) (csz / &2)`; `delta <= ef`] THEN
    REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs(apf - apft) <= min (delta / &2) (csz / &2)`; `csz <= apft`] THEN
  REAL_ARITH_TAC);;
