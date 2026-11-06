(* ========================================================================= *)
(* The weighted hypergraph framework on the simplex for the Green-Tao        *)
(* counting lemma (Conlon, Fox and Zhao, "A relative Szemeredi theorem").    *)
(*                                                                           *)
(* Points of Z_N^k are the x IN zn_tup k N (coordinates r < N for i < k and  *)
(* ARB beyond).  For W SUBSET {i | i < k}, zn_mix W x0 x1 takes the          *)
(* coordinates in W from x1 and the others from x0 (the 2-blow-up); zn_upd x *)
(* j r replaces x j by r; zn_depon e g says that g depends only on the       *)
(* coordinates in e; zn_mean2 k N g2 is the mean of g2 over pairs (x0, x1).  *)
(* * Cauchy-Schwarz doubling of a coordinate j: WCS_DOUBLING (weighted),     *)
(*   BCS_DOUBLING (weights in [0, 1]), from ZN_MEAN2_WEIGHTED_CS and the     *)
(*   identities ZN_MEAN2_AVG_IDENTITY, ZN_MEAN2_SQUARE_IDENTITY.             *)
(* * GOWERS_CS (CFZ Lemma 6.2): if each u_i (i IN e) takes values in         *)
(*   [0, 1] and does not depend on coordinate i, then                        *)
(*     |E_x g x prod_{i IN e} u_i x|^(2^|e|)                                 *)
(*       <= E_{x0,x1} prod_{W SUBSET e} g(zn_mix W x0 x1)                    *)
(*   (|e| doubling steps, GCS_STEP and GCS_INDUCT); ZN_MIX_MEAN2.            *)
(* * Reduction to indicators: BANG_BANG and DISC_REDUCE (a bound for         *)
(*   {0,1}-valued families depending on given coordinates extends to         *)
(*   [0,1]-valued ones, by multilinearity).                                  *)
(* * zn_hcount k N G = E_x prod_{j<k} G j x, edge j depending on the         *)
(*   coordinates i /= j; zn_hdisc k N j g h eps: |E_x (g - h) x prod_{i /=   *)
(*   j} u_i x| <= eps for all u_i in [0, 1] depending on J - {i, j}.         *)
(*   DENSE_COUNT (CFZ Lemma 6.1): if g j, h j take values in [0, 1] and      *)
(*   zn_hdisc holds for every j then |zn_hcount g - zn_hcount h| <= k eps    *)
(*   (telescoping through the hybrids, TELESCOPE_STEP, DENSE_TELESCOPE).     *)
(* ========================================================================= *)

needs "Sieve/gt_dense_model.ml";;
needs "Sieve/lf_local.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Points of Z_N^k, the 2-blow-up and averages over one coordinate.          *)
(* ------------------------------------------------------------------------- *)

let zn_tup = new_definition
 `zn_tup k N = cartesian_product {i:num | i < k} (\i. {r:num | r < N})`;;

let zn_mix = new_definition
 `zn_mix (W:num->bool) (x0:num->num) x1 = \i. if i IN W then x1 i else x0 i`;;

let zn_upd = new_definition
 `zn_upd (x:num->num) j r = \i. if i = j then r else x i`;;

let zn_depon = new_definition
 `zn_depon (e:num->bool) (g:(num->num)->real) <=>
    !x y. (!i. i IN e ==> x i = y i) ==> g x = g y`;;

let FINITE_ZN_TUP = prove
 (`!k N. FINITE(zn_tup k N)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[zn_tup] THEN
  MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
  REWRITE_TAC[FINITE_NUMSEG_LT]);;

let IN_ZN_TUP = prove
 (`!k N x. x IN zn_tup k N <=>
           (!i. i < k ==> x i < N) /\ (!i. ~(i < k) ==> x i = ARB)`,
  REWRITE_TAC[zn_tup; cartesian_product; IN_ELIM_THM; EXTENSIONAL] THEN
  MESON_TAC[]);;

let CARD_ZN_TUP = prove
 (`!k N. &(CARD(zn_tup k N)) = &N pow k`,
  REPEAT GEN_TAC THEN SIMP_TAC[CARD_EQ_SUM; FINITE_ZN_TUP] THEN
  REWRITE_TAC[zn_tup] THEN
  SIMP_TAC[SUM_CARTESIAN_ONE; FINITE_NUMSEG_LT; CARD_NUMSEG_LT]);;

let ZN_TUP_NONEMPTY = prove
 (`!k N. 1 <= N ==> ~(zn_tup k N = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\i. if i < k then 0 else ARB) IN zn_tup k N` MP_TAC THENL
   [REWRITE_TAC[IN_ZN_TUP] THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[NOT_IN_EMPTY]]);;

let ZN_MIX_IN_TUP = prove
 (`!k N W x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N
                 ==> zn_mix W x0 x1 IN zn_tup k N`,
  REWRITE_TAC[IN_ZN_TUP; zn_mix] THEN MESON_TAC[]);;

let ZN_UPD_IN_TUP = prove
 (`!k N x j r. x IN zn_tup k N /\ j < k /\ r < N
               ==> zn_upd x j r IN zn_tup k N`,
  REWRITE_TAC[IN_ZN_TUP; zn_upd] THEN MESON_TAC[]);;

let ZN_TUP_SUM_COORD = prove
 (`!k N j (g:(num->num)->real).
        j < k
        ==> sum (zn_tup k N) (\x. sum {r | r < N} (\r. g(zn_upd x j r))) =
            &N * sum (zn_tup k N) g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{i:num | i < k} = j INSERT ({i | i < k} DELETE j)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[zn_tup] THEN FIRST_ASSUM(SUBST1_TAC) THEN
  SIMP_TAC[SUM_CARTESIAN_INSERT; FINITE_DELETE; FINITE_NUMSEG_LT;
           IN_DELETE] THEN
  SUBGOAL_THEN
   `!u y r. zn_upd (\i. if i = j then u else y i) j r =
            (\i. if i = j then r else y i)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[zn_upd; FUN_EQ_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_SWAP o lhand o snd) THEN
  SIMP_TAC[FINITE_NUMSEG_LT; FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_DELETE]);;

let SUM_WEIGHTED_CS_ALT = prove
 (`!(s:A->bool) a y.
        FINITE s /\ (!x. x IN s ==> &0 <= y x)
        ==> sum s (\x. a x * y x) pow 2 <=
            sum s (\x. a x pow 2 * y x) * sum s y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`y:A->real`; `a:A->real`; `s:A->bool`] SUM_WEIGHTED_CS) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(MESON[REAL_MUL_SYM]
   `!a a' b b' c:real. a = a' /\ b = b'
                       ==> a pow 2 <= c * b ==> a' pow 2 <= b' * c`) THEN
  CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[REAL_MUL_SYM]);;

let ZN_TUP_FMEAN_COORD = prove
 (`!k N j (g:(num->num)->real).
        j < k /\ 1 <= N
        ==> fmean (zn_tup k N) g =
            fmean (zn_tup k N) (\x. fmean {r | r < N} (\r. g(zn_upd x j r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; CARD_NUMSEG_LT] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN
  ASM_SIMP_TAC[REWRITE_RULE[real_div] ZN_TUP_SUM_COORD; GSYM SUM_RMUL] THEN
  ASM_SIMP_TAC[ZN_TUP_SUM_COORD; SUM_RMUL] THEN
  SUBGOAL_THEN `~(&N = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; CONV_TAC REAL_FIELD]);;

let ZN_UPD_UPD = prove
 (`!x j r r'. zn_upd (zn_upd x j r) j r' = zn_upd x j r'`,
  REWRITE_TAC[zn_upd; FUN_EQ_THM] THEN MESON_TAC[]);;

let ZN_MIX_SING = prove
 (`!j x0 x1. zn_mix {j} x0 x1 = zn_upd x0 j (x1 j)`,
  REWRITE_TAC[zn_mix; zn_upd; FUN_EQ_THM; IN_SING] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pairs of points and Cauchy-Schwarz doubling.                              *)
(* ------------------------------------------------------------------------- *)

let FMEAN_SWAP = prove
 (`!(X:A->bool) (Y:B->bool) g.
        FINITE X /\ FINITE Y
        ==> fmean X (\x. fmean Y (\y. g x y)) =
            fmean Y (\y. fmean X (\x. g x y))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fmean; real_div; SUM_RMUL; ETA_AX] THEN
  MP_TAC(ISPECL [`g:A->B->real`; `X:A->bool`; `Y:B->bool`] SUM_SWAP) THEN
  ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!a b c:real. (a * b) * c = (a * c) * b`));;

let FMEAN_RMUL = prove
 (`!(X:A->bool) c g. fmean X (\x. g x * c) = fmean X g * c`,
  REWRITE_TAC[fmean; SUM_RMUL] THEN REAL_ARITH_TAC);;

let FMEAN_SQUARE = prove
 (`!(X:A->bool) g.
        fmean X g pow 2 = fmean X (\x. fmean X (\x'. g x * g x'))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM FMEAN_RMUL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[GSYM FMEAN_LMUL]);;

let zn_mean2 = new_definition
 `zn_mean2 k N (g2:(num->num)->(num->num)->real) =
    fmean (zn_tup k N) (\x0. fmean (zn_tup k N) (\x1. g2 x0 x1))`;;

let ZN_MEAN2_WEIGHTED_CS = prove
 (`!k N a y.
        (!x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N ==> &0 <= y x0 x1)
        ==> zn_mean2 k N (\x0 x1. a x0 x1 * y x0 x1) pow 2 <=
            zn_mean2 k N (\x0 x1. a x0 x1 pow 2 * y x0 x1) * zn_mean2 k N y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_mean2; fmean] THEN
  REWRITE_TAC[real_div; SUM_RMUL] THEN
  ABBREV_TAC `c = inv(&(CARD(zn_tup k N)))` THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_ZN_TUP] THEN
  ABBREV_TAC `Pz = {(x0:num->num,x1:num->num) | x0 IN zn_tup k N /\
                                                 x1 IN zn_tup k N}` THEN
  SUBGOAL_THEN `FINITE(Pz:(num->num)#(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Pz" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    REWRITE_TAC[FINITE_ZN_TUP];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Pz:(num->num)#(num->num)->bool`;
                 `\p:(num->num)#(num->num). a (FST p) (SND p):real`;
                 `\p:(num->num)#(num->num). y (FST p) (SND p):real`]
         SUM_WEIGHTED_CS_ALT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Pz" THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!h:(num->num)->(num->num)->real.
       sum Pz (\(x0,x1). h x0 x1) = sum Pz (\p. h (FST p) (SND p))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c` MP_TAC THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS]; ALL_TAC] THEN
  SPEC_TAC(`sum Pz (\p:(num->num)#(num->num). a (FST p) (SND p) *
                                              y (FST p) (SND
                                                p))`,`u:real`) THEN
  SPEC_TAC(`sum Pz (\p:(num->num)#(num->num). a (FST p) (SND p) pow 2 *
                                              y (FST p) (SND
                                                p))`,`v:real`) THEN
  SPEC_TAC(`sum Pz (\p:(num->num)#(num->num). y (FST p) (SND p):real)`,
           `w:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `((u:real) * c * c) pow 2 = (c pow 4) * u pow 2 /\
                (v:real) * c * c * w * c * c = (c pow 4) * (v * w)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE]);;

let ZN_MEAN2_AVG_IDENTITY = prove
 (`!k N j (A:(num->num)->(num->num)->real) Y.
        j < k /\ 1 <= N /\ (!x0 x1 r. Y (zn_upd x0 j r) x1 = Y x0 x1)
        ==> zn_mean2 k N (\x0 x1. A x0 x1 * Y x0 x1) =
            zn_mean2 k N
              (\x0 x1. fmean {r | r < N} (\r. A (zn_upd x0 j r) x1) *
                            Y x0 x1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_mean2] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ZN_TUP_FMEAN_COORD o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN ASM_REWRITE_TAC[] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FMEAN_SWAP o lhand o snd) THEN
  REWRITE_TAC[FINITE_ZN_TUP; FINITE_NUMSEG_LT] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[FMEAN_RMUL]);;

let ZN_MEAN2_SQUARE_IDENTITY = prove
 (`!k N j (A:(num->num)->(num->num)->real) Y.
        j < k /\ 1 <= N /\
        (!x0 x1 r. A x0 (zn_upd x1 j r) = A x0 x1) /\
        (!x0 x1 r. Y (zn_upd x0 j r) x1 = Y x0 x1) /\
        (!x0 x1 r. Y x0 (zn_upd x1 j r) = Y x0 x1)
        ==> zn_mean2 k N
              (\x0 x1. fmean {r | r < N} (\r. A (zn_upd x0 j r) x1) pow 2 *
                            Y x0 x1) =
            zn_mean2 k N
              (\x0 x1. A x0 x1 * A (zn_mix {j} x0 x1) x1 * Y x0 x1)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Zr = {r:num | r < N}` THEN
  SUBGOAL_THEN `FINITE(Zr:num->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Zr" THEN REWRITE_TAC[FINITE_NUMSEG_LT]; ALL_TAC] THEN
  REWRITE_TAC[zn_mean2; ZN_MIX_SING] THEN
  SUBGOAL_THEN
   `!x0. fmean (zn_tup k N)
           (\x1. (A:(num->num)->(num->num)->real) x0 x1 *
                 A (zn_upd x0 j (x1 j)) x1 * Y x0 x1) =
         fmean (zn_tup k N)
           (\x1. fmean Zr (\r'. A x0 x1 * A (zn_upd x0 j r') x1 * Y x0 x1))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) ZN_TUP_FMEAN_COORD o lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[zn_upd];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ZN_TUP_FMEAN_COORD o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[ZN_UPD_UPD] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  REWRITE_TAC[FMEAN_SQUARE; GSYM FMEAN_RMUL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FMEAN_SWAP o rand o snd) THEN
  ASM_REWRITE_TAC[FINITE_ZN_TUP] THEN DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_TERM_TAC THEN ABS_TAC THEN REAL_ARITH_TAC);;

let WCS_DOUBLING = prove
 (`!k N j (A:(num->num)->(num->num)->real) Y.
        j < k /\ 1 <= N /\
        (!x0 x1 r. A x0 (zn_upd x1 j r) = A x0 x1) /\
        (!x0 x1 r. Y (zn_upd x0 j r) x1 = Y x0 x1) /\
        (!x0 x1 r. Y x0 (zn_upd x1 j r) = Y x0 x1) /\
        (!x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N ==> &0 <= Y x0 x1)
        ==> zn_mean2 k N (\x0 x1. A x0 x1 * Y x0 x1) pow 2 <=
            zn_mean2 k N
              (\x0 x1. A x0 x1 * A (zn_mix {j} x0 x1) x1 * Y x0 x1) *
            zn_mean2 k N Y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `j:num`; `A:(num->num)->(num->num)->real`;
                `Y:(num->num)->(num->num)->real`] ZN_MEAN2_AVG_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `j:num`; `A:(num->num)->(num->num)->real`;
                `Y:(num->num)->(num->num)->real`]
                  ZN_MEAN2_SQUARE_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC ZN_MEAN2_WEIGHTED_CS THEN ASM_REWRITE_TAC[]);;

let BCS_DOUBLING = prove
 (`!k N j (A:(num->num)->(num->num)->real) Y.
        j < k /\ 1 <= N /\
        (!x0 x1 r. A x0 (zn_upd x1 j r) = A x0 x1) /\
        (!x0 x1 r. Y (zn_upd x0 j r) x1 = Y x0 x1) /\
        (!x0 x1 r. Y x0 (zn_upd x1 j r) = Y x0 x1) /\
        (!x0 x1. x0 IN zn_tup k N /\ x1 IN zn_tup k N
                 ==> &0 <= Y x0 x1 /\ Y x0 x1 <= &1)
        ==> zn_mean2 k N (\x0 x1. A x0 x1 * Y x0 x1) pow 2 <=
            zn_mean2 k N (\x0 x1. A x0 x1 * A (zn_mix {j} x0 x1) x1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `j:num`; `A:(num->num)->(num->num)->real`;
                `\(x0:num->num) (x1:num->num). &1`]
                  ZN_MEAN2_SQUARE_IDENTITY) THEN
  ASM_REWRITE_TAC[REAL_MUL_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `j:num`; `A:(num->num)->(num->num)->real`;
                `Y:(num->num)->(num->num)->real`] ZN_MEAN2_AVG_IDENTITY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `a = \x0 x1. fmean {r | r < N}
                    (\r. (A:(num->num)->(num->num)->real)
                      (zn_upd x0 j r) x1)` THEN
  SUBGOAL_THEN
   `!x0 x1. fmean {r | r < N}
              (\r. (A:(num->num)->(num->num)->real) (zn_upd x0 j r) x1) =
            a x0 x1`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `zn_mean2 k N (\x0 x1. (a:(num->num)->(num->num)->real) x0 x1 pow 2 *
                              Y x0 x1) * zn_mean2 k N Y` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ZN_MEAN2_WEIGHTED_CS THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= zn_mean2 k N (\x0 x1. (a:(num->num)->(num->num)->real) x0 x1 pow 2 *
                          Y x0 x1) /\
    zn_mean2 k N (\x0 x1. a x0 x1 pow 2 * Y x0 x1) <=
    zn_mean2 k N (\x0 x1. a x0 x1 pow 2) /\
    zn_mean2 k N Y <= &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[zn_mean2] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean (zn_tup k N) (\x0:num->num. &0)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[FMEAN_CONST; FINITE_ZN_TUP; ZN_TUP_NONEMPTY;
                     REAL_LE_REFL];
        ALL_TAC] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      X_GEN_TAC `x0:num->num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean (zn_tup k N) (\x1:num->num. &0)` THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[FMEAN_CONST; FINITE_ZN_TUP; ZN_TUP_NONEMPTY;
                     REAL_LE_REFL];
        ALL_TAC] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      X_GEN_TAC `x0:num->num` THEN DISCH_TAC THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      X_GEN_TAC `x1:num->num` THEN DISCH_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_POW_2];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean (zn_tup k N) (\x0:num->num. &1)` THEN CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[FMEAN_CONST; FINITE_ZN_TUP; ZN_TUP_NONEMPTY;
         REAL_LE_REFL]] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      X_GEN_TAC `x0:num->num` THEN DISCH_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `fmean (zn_tup k N) (\x1:num->num. &1)` THEN CONJ_TAC THENL
       [ALL_TAC;
        ASM_SIMP_TAC[FMEAN_CONST; FINITE_ZN_TUP; ZN_TUP_NONEMPTY;
         REAL_LE_REFL]] THEN
      MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
    `zn_mean2 k N (\x0 x1. (a:(num->num)->(num->num)->real) x0 x1 pow 2 *
                              Y x0 x1) * &1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[REAL_MUL_RID]]);;

(* ------------------------------------------------------------------------- *)
(* The Gowers-Cauchy-Schwarz inequality.                                     *)
(* ------------------------------------------------------------------------- *)

let PRODUCT_SUBSETS_INSERT = prove
 (`!(g:(A->bool)->real) a t.
        FINITE t /\ ~(a IN t)
        ==> product {s | s SUBSET (a INSERT t)} g =
            product {s | s SUBSET t} g *
            product {s | s SUBSET t} (\s. g (a INSERT s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[POWERSET_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_UNION o lhand o snd) THEN
  ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE] THEN ANTS_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_IMAGE; IN_ELIM_THM;
                NOT_IN_EMPTY] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PRODUCT_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let ZN_MIX_INSERT_SING = prove
 (`!j W x0 x1. zn_mix W (zn_mix {j} x0 x1) x1 = zn_mix (j INSERT W) x0 x1`,
  REWRITE_TAC[zn_mix; FUN_EQ_THM; IN_INSERT; IN_SING] THEN MESON_TAC[]);;

let zn_gcsq = new_definition
 `zn_gcsq e d (g:(num->num)->real) (u:num->(num->num)->real) x0 x1 =
    product {W | W SUBSET d} (\W. g(zn_mix W x0 x1)) *
    product (e DIFF d)
      (\i. product {W | W SUBSET d} (\W. u i (zn_mix W x0 x1)))`;;

let GCS_STEP = prove
 (`!k N e d j (g:(num->num)->real) u.
        1 <= N /\ e SUBSET {i | i < k} /\ d SUBSET e /\ j IN e /\
        ~(j IN d) /\
        (!i x r. i IN e ==> u i (zn_upd x i r) = u i x) /\
        (!i x. i IN e /\ x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1)
        ==> zn_mean2 k N (zn_gcsq e d g u) pow 2 <=
            zn_mean2 k N (zn_gcsq e (j INSERT d) g u)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(e:num->bool) /\ FINITE(d:num->bool) /\ (j:num) < k`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < k}` THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < k}` THEN
      REWRITE_TAC[FINITE_NUMSEG_LT] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC
   `A = \x0 x1. product {W | W SUBSET d} (\W. (g:(num->num)->real)
                                                (zn_mix W x0 x1)) *
                product (e DIFF (j INSERT d))
                 (\i. product {W | W SUBSET d}
                       (\W. (u:num->(num->num)->real) i
                              (zn_mix W x0 x1)))` THEN
  ABBREV_TAC
   `Y = \x0 x1. product {W | W SUBSET d}
                  (\W. (u:num->(num->num)->real) j (zn_mix W x0 x1))` THEN
  SUBGOAL_THEN `zn_gcsq e d (g:(num->num)->real) u =
                (\x0 x1. (A:(num->num)->(num->num)->real) x0 x1 * Y x0 x1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; zn_gcsq] THEN
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN
    MAP_EVERY EXPAND_TAC ["A"; "Y"] THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:num->bool) DIFF d = j INSERT (e DIFF (j INSERT d))`
    SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DIFF; IN_DIFF; IN_INSERT] THEN
    MATCH_ACCEPT_TAC(REAL_ARITH `!a b c:real. a * b * c = (a * c) * b`);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `zn_gcsq e (j INSERT d) (g:(num->num)->real) u =
    (\x0 x1. (A:(num->num)->(num->num)->real) x0 x1 * A (zn_mix {j} x0 x1) x1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; zn_gcsq] THEN
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[ZN_MIX_INSERT_SING] THEN
    ASM_SIMP_TAC[PRODUCT_SUBSETS_INSERT; PRODUCT_MUL; FINITE_DIFF] THEN
    MATCH_ACCEPT_TAC(REAL_ARITH
     `!a b c d:real. (a * b) * (c * d) = (a * c) * (b * d)`);
    ALL_TAC] THEN
  MATCH_MP_TAC BCS_DOUBLING THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`; `r:num`] THEN
    EXPAND_TAC "A" THEN REWRITE_TAC[] THEN BINOP_TAC THEN
    TRY(MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        REWRITE_TAC[]) THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `W:num->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[zn_mix; zn_upd; FUN_EQ_THM] THEN
    X_GEN_TAC `l:num` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`; `r:num`] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `W:num->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `zn_mix W (zn_upd x0 j r) x1 = zn_upd (zn_mix W x0 x1) j r`
    SUBST1_TAC THENL
     [REWRITE_TAC[zn_mix; zn_upd; FUN_EQ_THM] THEN X_GEN_TAC `l:num` THEN
      REPEAT COND_CASES_TAC THEN ASM SET_TAC[];
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`; `r:num`] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `W:num->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN REWRITE_TAC[zn_mix; zn_upd; FUN_EQ_THM] THEN
    X_GEN_TAC `l:num` THEN REPEAT COND_CASES_TAC THEN ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`x0:num->num`; `x1:num->num`] THEN STRIP_TAC THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_POS_LE; MATCH_MP_TAC PRODUCT_LE_1] THEN
    ASM_SIMP_TAC[FINITE_POWERSET] THEN
    X_GEN_TAC `W:num->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `zn_mix W x0 x1`] o
      check (fun th -> can (find_term ((=) `&1`)) (concl th) &&
                       is_forall(concl th))) THEN
    ASM_SIMP_TAC[ZN_MIX_IN_TUP] THEN REAL_ARITH_TAC]);;

let GCS_INDUCT = prove
 (`!k N e (g:(num->num)->real) u.
        1 <= N /\ e SUBSET {i | i < k} /\
        (!i x r. i IN e ==> u i (zn_upd x i r) = u i x) /\
        (!i x. i IN e /\ x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1)
        ==> !d. d SUBSET e /\ ~(d = {})
                ==> abs(zn_mean2 k N (zn_gcsq e {} g u)) pow (2 EXP CARD d) <=
                    zn_mean2 k N (zn_gcsq e d g u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(e:num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{i:num | i < k}` THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!d. FINITE d ==> d SUBSET e /\ ~(d = {})
        ==> abs(zn_mean2 k N (zn_gcsq e {} (g:(num->num)->real) u)) pow
            (2 EXP CARD d) <= zn_mean2 k N (zn_gcsq e d g u)`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `d:num->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:num->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[FINITE_SUBSET]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  MAP_EVERY X_GEN_TAC [`j:num`; `d:num->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; EXP] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `zn_mean2 k N (zn_gcsq e d (g:(num->num)->real) u) pow 2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC GCS_STEP THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `d:num->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; EXP; MULT_CLAUSES; REAL_POW2_ABS] THEN
    REWRITE_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `2 * n = n * 2`] THEN
    REWRITE_TAC[GSYM REAL_POW_POW] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_POW_LE THEN REWRITE_TAC[REAL_ABS_POS]);;

let GOWERS_CS = prove
 (`!k N e (g:(num->num)->real) u.
        1 <= N /\ e SUBSET {i | i < k} /\ ~(e = {}) /\
        (!i x r. i IN e ==> u i (zn_upd x i r) = u i x) /\
        (!i x. i IN e /\ x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1)
        ==> abs(fmean (zn_tup k N) (\x. g x * product e (\i. u i x)))
            pow (2 EXP CARD e) <=
            zn_mean2 k N
              (\x0 x1. product {W | W SUBSET e} (\W. g(zn_mix W x0 x1)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `e:num->bool`; `g:(num->num)->real`;
                `u:num->(num->num)->real`] GCS_INDUCT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:num->bool`) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b /\ c = d ==> a <= c ==> b <= d`) THEN
  CONJ_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[zn_mean2; zn_gcsq; SUBSET_EMPTY; SING_GSPEC; PRODUCT_SING;
     DIFF_EMPTY] THEN
    SUBGOAL_THEN `!x0 x1:num->num. zn_mix {} x0 x1 = x0`
    (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[zn_mix; NOT_IN_EMPTY; FUN_EQ_THM]; ALL_TAC] THEN
    AP_TERM_TAC THEN ABS_TAC THEN
    ASM_SIMP_TAC[FMEAN_CONST; FINITE_ZN_TUP; ZN_TUP_NONEMPTY];
    REWRITE_TAC[zn_mean2; zn_gcsq; DIFF_EQ_EMPTY; PRODUCT_CLAUSES;
                REAL_MUL_RID]]);;

let ZN_MIX_MEAN2 = prove
 (`!k N W (g:(num->num)->real).
        1 <= N ==> zn_mean2 k N (\x0 x1. g(zn_mix W x0 x1)) =
        fmean (zn_tup k N) g`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[zn_mean2; fmean; CARD_ZN_TUP; real_div] THEN
  REWRITE_TAC[SUM_RMUL] THEN
  ABBREV_TAC `Z = zn_tup k N` THEN
  SUBGOAL_THEN `FINITE(Z:(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[FINITE_ZN_TUP]; ALL_TAC] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; ASSUME `FINITE(Z:(num->num)->bool)`] THEN
  SUBGOAL_THEN
   `sum {(x0,x1) | x0 IN Z /\ x1 IN Z} (\(x0,x1). g (zn_mix W x0 x1)) =
    sum {(x0,x1) | x0 IN Z /\ x1 IN Z} (\(x0:num->num,x1:num->num). g x0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ_GENERAL_INVERSES THEN
    MAP_EVERY EXISTS_TAC
     [`\(x0:num->num,x1:num->num). (zn_mix W x0 x1, zn_mix W x1 x0)`;
      `\(x0:num->num,x1:num->num). (zn_mix W x0 x1, zn_mix W x1 x0)`] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
    SUBGOAL_THEN
      `!x0 x1:num->num. zn_mix W (zn_mix W x0 x1) (zn_mix W x1 x0) = x0`
    ASSUME_TAC THENL
     [REWRITE_TAC[zn_mix; FUN_EQ_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Z" THEN
    MESON_TAC[ZN_MIX_IN_TUP];
    ALL_TAC] THEN
  SIMP_TAC[GSYM SUM_SUM_PRODUCT; ASSUME `FINITE(Z:(num->num)->bool)`] THEN
  ASM_SIMP_TAC[SUM_CONST] THEN
  EXPAND_TAC "Z" THEN REWRITE_TAC[CARD_ZN_TUP; SUM_LMUL] THEN
  SUBGOAL_THEN `~(&N pow k = &0)` MP_TAC THENL
   [REWRITE_TAC[REAL_POW_EQ_0; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Reduction to indicator functions.                                         *)
(* ------------------------------------------------------------------------- *)

let FMEAN_PROJECT = prove
 (`!k N D (v:(num->num)->real) G.
        1 <= N /\ zn_depon D v
        ==> fmean (zn_tup k N) (\x. v x * G x) =
            fmean (zn_tup k N)
              (\x. v x *
                   fmean (zn_tup k N) (\y. G(zn_mix ((:num) DIFF D) x y)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `(:num) DIFF D`;
                `\x:num->num. (v:(num->num)->real) x * G x`] ZN_MIX_MEAN2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[zn_mean2; GSYM FMEAN_LMUL] THEN
  AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [zn_depon]) THEN
  REWRITE_TAC[zn_mix; IN_DIFF; IN_UNIV] THEN MESON_TAC[]);;

let BANG_BANG = prove
 (`!k N D (u:(num->num)->real) G.
        1 <= N /\ zn_depon D u /\
        (!x. x IN zn_tup k N ==> &0 <= u x /\ u x <= &1)
        ==> ?bp bm. zn_depon D bp /\ zn_depon D bm /\
                    (!x. bp x = &0 \/ bp x = &1) /\
                    (!x. bm x = &0 \/ bm x = &1) /\
                    fmean (zn_tup k N) (\x. bm x * G x) <=
                    fmean (zn_tup k N) (\x. u x * G x) /\
                    fmean (zn_tup k N) (\x. u x * G x) <=
                    fmean (zn_tup k N) (\x. bp x * G x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Gb = \x. fmean (zn_tup k N)
                         (\y. (G:(num->num)->real)
                           (zn_mix ((:num) DIFF D) x y))` THEN
  SUBGOAL_THEN `zn_depon D (Gb:(num->num)->real)` ASSUME_TAC THENL
   [REWRITE_TAC[zn_depon] THEN REPEAT STRIP_TAC THEN EXPAND_TAC "Gb" THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[zn_mix; IN_DIFF; IN_UNIV; FUN_EQ_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\x. if &0 < (Gb:(num->num)->real) x then &1 else &0`;
    `\x. if (Gb:(num->num)->real) x < &0 then &1 else &0`] THEN
  SUBGOAL_THEN
   `zn_depon D (\x. if &0 < (Gb:(num->num)->real) x then &1 else &0) /\
    zn_depon D (\x. if (Gb:(num->num)->real) x < &0 then &1 else &0)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `zn_depon D (Gb:(num->num)->real)` THEN
    REWRITE_TAC[zn_depon] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `D:num->bool`; `u:(num->num)->real`;
                 `G:(num->num)->real`] FMEAN_PROJECT) THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `D:num->bool`;
                 `\x. if &0 < (Gb:(num->num)->real) x then &1 else &0`;
                 `G:(num->num)->real`] FMEAN_PROJECT) THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `D:num->bool`;
                 `\x. if (Gb:(num->num)->real) x < &0 then &1 else &0`;
                 `G:(num->num)->real`] FMEAN_PROJECT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. fmean (zn_tup k N)
          (\y. (G:(num->num)->real) (zn_mix ((:num) DIFF D) x y)) = Gb x`
  (fun th -> REWRITE_TAC[th]) THENL
   [EXPAND_TAC "Gb" THEN REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  CONJ_TAC THEN MATCH_MP_TAC FMEAN_LE THEN REWRITE_TAC[FINITE_ZN_TUP] THEN
  X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!x. x IN zn_tup k N ==> &0 <= (u:(num->num)->real) x /\ u x <= &1` THEN
  DISCH_THEN(MP_TAC o SPEC `x:num->num`) THEN ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`(Gb:(num->num)->real) x`,`b:real`) THEN
  SPEC_TAC(`(u:(num->num)->real) x`,`a:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID] THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ a * --b <= &1 * --b ==> b <=
     a * b`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `a * b <= &1 * b ==> a * b <= b`) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[REAL_ARITH `a * b <= &0 <=> &0 <= a * --b`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]);;

let FMEAN_PRODUCT_FACTOR = prove
 (`!k N (e:num->bool) i (H:(num->num)->real) (u:num->(num->num)->real).
        FINITE e /\ i IN e
        ==> fmean (zn_tup k N) (\x. H x * product e (\l. u l x)) =
            fmean (zn_tup k N)
              (\x. u i x * (H x * product (e DELETE i) (\l. u l x)))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
  SUBGOAL_THEN `e = (i:num) INSERT (e DELETE i)` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
    [th]) THEN
  ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE] THEN
  REAL_ARITH_TAC);;

let DISC_REDUCE = prove
 (`!k N (H:(num->num)->real) e (Dd:num->num->bool) eps.
        1 <= N /\ FINITE e /\
        (!b. (!i. i IN e ==> zn_depon (Dd i) (b i) /\
                             !x. b i x = &0 \/ b i x = &1)
             ==> abs(fmean (zn_tup k N) (\x. H x * product e (\i. b i x)))
                 <= eps)
        ==> !u. (!i. i IN e
                     ==> zn_depon (Dd i) (u i) /\
                         !x. x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1)
                ==> abs(fmean (zn_tup k N) (\x. H x * product e (\i. u i x)))
                    <= eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!S. FINITE S
        ==> S SUBSET (e:num->bool)
            ==> !u:num->(num->num)->real.
                    (!i. i IN e ==> zn_depon ((Dd:num->num->bool) i) (u i)) /\
                    (!i. i IN e /\ ~(i IN S)
                         ==> !x. u i x = &0 \/ u i x = &1) /\
                    (!i. i IN S
                         ==> !x. x IN zn_tup k N
                                 ==> &0 <= u i x /\ u i x <= &1)
                    ==> abs(fmean (zn_tup k N)
                                  (\x. (H:(num->num)->real) x *
                                       product e (\i. u i x))) <= eps`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPEC `e:num->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `u:num->(num->num)->real` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MATCH_MP_TAC th) THEN
    ASM_SIMP_TAC[TAUT `(p /\ ~p ==> q) <=> T`]] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[NOT_IN_EMPTY; EMPTY_SUBSET] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `S:num->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  X_GEN_TAC `u:num->(num->num)->real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[FMEAN_PRODUCT_FACTOR] THEN
  MP_TAC(ISPECL [`k:num`; `N:num`; `(Dd:num->num->bool) i`;
                 `(u:num->(num->num)->real) i`;
                 `\x. (H:(num->num)->real) x *
                      product (e DELETE i)
                        (\l. (u:num->(num->num)->real) l x)`]
         BANG_BANG) THEN
  ASM_SIMP_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `bp:(num->num)->real`
    (X_CHOOSE_THEN `bm:(num->num)->real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!b. zn_depon ((Dd:num->num->bool) i) b /\ (!x. b x = &0 \/ b x = &1)
        ==> abs(fmean (zn_tup k N)
                 (\x. b x * (H x * product (e DELETE i)
                                   (\l. (u:num->(num->num)->real) l x))))
            <= eps`
  ASSUME_TAC THENL
   [X_GEN_TAC `b:(num->num)->real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `\l:num. if l = i then (b:(num->num)->real)
             else (u:num->(num->num)->real) l`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN X_GEN_TAC `l:num` THEN
      ASM_CASES_TAC `l:num = i` THEN ASM_SIMP_TAC[] THEN
      ASM_MESON_TAC[IN_INSERT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FMEAN_PRODUCT_FACTOR] THEN
    MATCH_MP_TAC(REAL_ARITH `a = b ==> abs a <= e ==> abs b <= e`) THEN
    AP_TERM_TAC THEN ABS_TAC THEN REWRITE_TAC[] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
    REWRITE_TAC[IN_DELETE] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c e:real. b <= a /\ a <= c /\ abs b <= e /\ abs c <= e
                   ==> abs a <= e`) THEN
  MAP_EVERY EXISTS_TAC
   [`fmean (zn_tup k N)
      (\x. (bm:(num->num)->real) x *
           (H x * product (e DELETE i) (\l. (u:num->(num->num)->real) l x)))`;
    `fmean (zn_tup k N)
      (\x. (bp:(num->num)->real) x *
           (H x * product (e DELETE i) (\l. (u:num->(num->num)->real) l x)))`]
  THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Counts, discrepancy and the dense counting lemma.                         *)
(* ------------------------------------------------------------------------- *)

let zn_hcount = new_definition
 `zn_hcount k N (G:num->(num->num)->real) =
    fmean (zn_tup k N) (\x. product {j | j < k} (\j. G j x))`;;

let zn_hdisc = new_definition
 `zn_hdisc k N j (g:(num->num)->real) h eps <=>
    !u. (!i. i < k /\ ~(i = j)
             ==> zn_depon ({l | l < k} DIFF {i, j}) (u i) /\
                 !x. x IN zn_tup k N ==> &0 <= u i x /\ u i x <= &1)
        ==> abs(fmean (zn_tup k N)
                  (\x. (g x - h x) *
                       product ({l | l < k} DELETE j) (\i. u i x)))
            <= eps`;;

let FMEAN_ZN_UPD_SWAP = prove
 (`!k N j (F1:(num->num)->real).
        j < k /\ 1 <= N
        ==> fmean (zn_tup k N) F1 =
            fmean {r | r < N} (\r. fmean (zn_tup k N) (\x. F1(zn_upd x j r)))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) ZN_TUP_FMEAN_COORD o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FMEAN_SWAP THEN REWRITE_TAC[FINITE_ZN_TUP; FINITE_NUMSEG_LT]);;

let FMEAN_ABS_BOUND = prove
 (`!(X:A->bool) f b. FINITE X /\ ~(X = {}) /\ (!x. x IN X ==> abs(f x) <= b)
                     ==> abs(fmean X f) <= b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `fmean X (\x:A. abs(f x))` THEN ASM_SIMP_TAC[FMEAN_ABS_LE] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `fmean X (\x:A. b)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FMEAN_LE THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[FMEAN_CONST; REAL_LE_REFL]]);;

let ZN_DEPON_UPD = prove
 (`!e (g:(num->num)->real) j r x. zn_depon e g /\ ~(j IN e) ==>
   g(zn_upd x j r) = g x`,
  REWRITE_TAC[zn_depon; zn_upd] THEN MESON_TAC[]);;

let TELESCOPE_STEP = prove
 (`!k N j (g:(num->num)->real) h w eps.
        j < k /\ 1 <= N /\ zn_hdisc k N j g h eps /\
        zn_depon ({l | l < k} DELETE j) g /\
        zn_depon ({l | l < k} DELETE j) h /\
        (!l. l < k /\ ~(l = j)
             ==> zn_depon ({m | m < k} DELETE l) (w l) /\
                 !x. x IN zn_tup k N ==> &0 <= w l x /\ w l x <= &1)
        ==> abs(fmean (zn_tup k N)
                  (\x. (g x - h x) *
                       product ({l | l < k} DELETE j) (\l. w l x)))
            <= eps`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) FMEAN_ZN_UPD_SWAP o
    rand o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC FMEAN_ABS_BOUND THEN
  REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x. (g:(num->num)->real) (zn_upd x j r) = g x /\
        (h:(num->num)->real) (zn_upd x j r) = h x`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC ZN_DEPON_UPD THEN
    EXISTS_TAC `{l:num | l < k} DELETE j` THEN
    ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [zn_hdisc]) THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[zn_depon] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:num->num`; `y:num->num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[zn_upd; IN_DELETE; IN_ELIM_THM] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_SIMP_TAC[ZN_UPD_IN_TUP]]);;

let zn_hybrid = new_definition
 `zn_hybrid k (g:num->(num->num)->real) h Tt x =
    product {j | j < k} (\j. if j IN Tt then h j x else g j x)`;;

let ZN_HYBRID_STEP = prove
 (`!k (g:num->(num->num)->real) h Tt j x.
        j < k /\ ~(j IN Tt)
        ==> zn_hybrid k g h Tt x - zn_hybrid k g h (j INSERT Tt) x =
            (g j x - h j x) *
            product ({l | l < k} DELETE j)
                    (\l. if l IN Tt then h l x else g l x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[zn_hybrid] THEN
  SUBGOAL_THEN `(j:num) IN {l | l < k}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM(MATCH_MP (SPEC_ALL PRODUCT_DELETE)
    (CONJ (SPEC `k:num` FINITE_NUMSEG_LT)
          (ASSUME `(j:num) IN {l | l < k}`)))] THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  SUBGOAL_THEN
   `product ({l | l < k} DELETE j)
      (\l. if l = j \/ l IN Tt then (h:num->(num->num)->real) l x
           else g l x) =
    product ({l | l < k} DELETE j) (\l. if l IN Tt then h l x else g l x)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  MATCH_ACCEPT_TAC(REAL_ARITH `!a b c:real. a * c - b * c = (a - b) * c`));;

let DENSE_TELESCOPE = prove
 (`!k N (g:num->(num->num)->real) h eps.
        1 <= N /\
        (!j. j < k
             ==> zn_depon ({l | l < k} DELETE j) (g j) /\
                 zn_depon ({l | l < k} DELETE j) (h j) /\
                 zn_hdisc k N j (g j) (h j) eps /\
                 !x. x IN zn_tup k N ==> &0 <= h j x /\ h j x <= &1)
        ==> !Tt. Tt SUBSET {j | j < k} /\
                 (!j x. j < k /\ ~(j IN Tt) /\ x IN zn_tup k N
                        ==> &0 <= g j x /\ g j x <= &1)
                 ==> abs(fmean (zn_tup k N) (zn_hybrid k g h Tt) -
                         fmean (zn_tup k N) (zn_hybrid k g h {j | j < k}))
                     <= &(CARD({j | j < k} DIFF Tt)) * eps`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n Tt. CARD({j | j < k} DIFF Tt) = n
           ==> Tt SUBSET {j | j < k} /\
               (!j x. j < k /\ ~(j IN Tt) /\ x IN zn_tup k N
                      ==> &0 <= (g:num->(num->num)->real) j x /\ g j x <= &1)
               ==> abs(fmean (zn_tup k N) (zn_hybrid k g h Tt) -
                       fmean (zn_tup k N) (zn_hybrid k g h {j | j < k}))
                   <= &n * eps`
  (fun th -> MESON_TAC[th]) THEN
  INDUCT_TAC THEN X_GEN_TAC `Tt:num->bool` THENL
   [SIMP_TAC[CARD_EQ_0; FINITE_DIFF; FINITE_NUMSEG_LT] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `Tt = {j:num | j < k}` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0; REAL_MUL_LZERO;
                                 REAL_LE_REFL]];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?j. j < k /\ ~((j:num) IN Tt)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~({j:num | j < k} DIFF Tt = {}) ==> ?j. j < k /\ ~(j IN Tt)`) THEN
    DISCH_TAC THEN UNDISCH_TAC `CARD({j:num | j < k} DIFF Tt) = SUC n` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(j:num) INSERT Tt`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `{l:num | l < k} DIFF (j INSERT Tt) =
                  ({l | l < k} DIFF Tt) DELETE j` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; FINITE_NUMSEG_LT; IN_DIFF;
                 IN_ELIM_THM] THEN ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!a b c n e:real. abs(a - b) <= e
                     ==> abs(b - c) <= n * e ==> abs(a - c) <=
                       (n + &1) * e`) THEN
  ASM_SIMP_TAC[GSYM FMEAN_SUB; FINITE_ZN_TUP; ZN_HYBRID_STEP] THEN
  MATCH_MP_TAC TELESCOPE_STEP THEN REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[] THEN
  X_GEN_TAC `l:num` THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_CASES_TAC `(l:num) IN Tt` THEN ASM_SIMP_TAC[ETA_AX];
    X_GEN_TAC `x:num->num` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[]]);;

let DENSE_COUNT = prove
 (`!k N (g:num->(num->num)->real) h eps.
        1 <= N /\
        (!j. j < k
             ==> zn_depon ({l | l < k} DELETE j) (g j) /\
                 zn_depon ({l | l < k} DELETE j) (h j) /\
                 zn_hdisc k N j (g j) (h j) eps /\
                 (!x. x IN zn_tup k N ==> &0 <= h j x /\ h j x <= &1) /\
                 (!x. x IN zn_tup k N ==> &0 <= g j x /\ g j x <= &1))
        ==> abs(zn_hcount k N g - zn_hcount k N h) <= &k * eps`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `N:num`; `g:num->(num->num)->real`;
                `h:num->(num->num)->real`; `eps:real`] DENSE_TELESCOPE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `{}:num->bool`) THEN
  REWRITE_TAC[EMPTY_SUBSET; NOT_IN_EMPTY; DIFF_EMPTY; CARD_NUMSEG_LT] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> a <= e ==> b <= e`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[zn_hcount] THEN BINOP_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; zn_hybrid; NOT_IN_EMPTY; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN SIMP_TAC[IN_ELIM_THM]);;
