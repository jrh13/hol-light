(* ========================================================================= *)
(* The hyperelliptic equation: three simple roots give finitely many x.      *)
(*                                                                           *)
(* Purpose: if d_i (x - z_i) is the square of an integer polynomial          *)
(* expression in z_i for i = 1, 2, 3 (z_1, z_2, z_3 distinct algebraic       *)
(* integers, d_i from finite sets of non-zero algebraic integers), then x    *)
(* lies in a finite set (Baker 1969; the core of the hyperelliptic theorem). *)
(* Route (one unit equation): with rho_i^2 = d_i and d_i (x - z_i) = xi_i^2, *)
(* the factor lam_ij = rho_j xi_i - rho_i xi_j has the partner mu_ij = rho_j *)
(* xi_i + rho_i xi_j with the fixed product lam_ij mu_ij = d_i d_j (z_j -    *)
(* z_i), hence bounded norm (NF_BOUNDED_NORM_FINITE); the Siegel identity    *)
(* rho_3 lam_12 + rho_1 lam_23 + rho_2 lam_31 = 0 and NF_UNIT_EQUATION leave *)
(* finitely many ratios lam_12 / lam_31, and x is an explicit rational       *)
(* function of that ratio (HYPERELL_RECOVER).                                *)
(*                                                                           *)
(* Main results: HYPERELL_THREE_ROOTS, HYPERELL_TR_CORE (the same for data   *)
(* in one fixed order), HYPERELL_RECOVER; helper names HYPERELL_*.           *)
(*                                                                           *)
(* Uses: Baker/superell_roots.ml (NF_SIEGEL_RATIO_FINITE,                    *)
(* NF_ORDER_FACTOR_NORMS and the m-independent SUPERELL_TR helpers),         *)
(* Baker/nf_order.ml (NF_ORDER_ADD, NF_ORDER_EQ), Baker/nf_defs.ml           *)
(* (NF_DATA_1_IN), Baker/algint.ml (ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER). *)
(* ========================================================================= *)

needs "Baker/superell_roots.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Recovering x from the ratio t = (beta1 - beta2) / (beta1 - beta3) of      *)
(* differences of square roots beta_i of x - z_i.                            *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_RECOVER_BETA = prove
 (`!z1 z2 z3 b1 b2 b3 x t:complex.
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     b1 pow 2 = x - z1 /\ b2 pow 2 = x - z2 /\ b3 pow 2 = x - z3 /\
     t = (b1 - b2) / (b1 - b3)
     ==> x = z1 + ((z2 - z1 - t * (z3 - z1)) / (t - t pow 2) + z3 - z1)
                  pow 2 /
                 (Cx(&4) * ((z2 - z1 - t * (z3 - z1)) / (t - t pow 2)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(b1 - b2 = Cx(&0)) /\ ~(b1 - b3 = Cx(&0)) /\
                ~(b2 - b3 = Cx(&0))` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(z1 = z2:complex)`; UNDISCH_TAC `~(z1 = z3:complex)`;
      UNDISCH_TAC `~(z2 = z3:complex)`] THEN
    REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(b1:complex) pow 2 = x - z1`; `(b2:complex) pow 2 = x - z2`;
      `(b3:complex) pow 2 = x - z3`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z2:complex) - z1 = (b1 - b2) * (b1 + b2) /\
                (z3:complex) - z1 = (b1 - b3) * (b1 + b3) /\
                (x:complex) = z1 + b1 pow 2`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY UNDISCH_TAC
     [`(b1:complex) pow 2 = x - z1`; `(b2:complex) pow 2 = x - z2`;
      `(b3:complex) pow 2 = x - z3`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> lhs(concl th) = `t:complex`)) THEN
  SUBGOAL_THEN
   `((b1 - b2) * (b1 + b2) - (b1 - b2) / (b1 - b3) * (b1 - b3) * (b1 + b3)) /
    ((b1 - b2) / (b1 - b3) - ((b1 - b2) / (b1 - b3)) pow 2) =
    (b1 - b3:complex) pow 2`
  SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(b1 - b2) * (b1 + b2) - (b1 - b2) / (b1 - b3) * (b1 - b3) * (b1 + b3) =
      (b1 - b2) * (b2 - b3:complex) /\
      (b1 - b2) / (b1 - b3) - ((b1 - b2) / (b1 - b3)) pow 2 =
      ((b1 - b2) * (b2 - b3)) / (b1 - b3) pow 2`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN UNDISCH_TAC `~(b1 - b3 = Cx(&0))` THEN
      CONV_TAC COMPLEX_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((b1 - b2) * (b2 - b3) = Cx(&0))` MP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_ENTIRE]; ALL_TAC] THEN
    UNDISCH_TAC `~(b1 - b3 = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  UNDISCH_TAC `~(b1 - b3 = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let HYPERELL_RECOVER = prove
 (`!z1 z2 z3 rho1 rho2 rho3 xi1 xi2 xi3 x:complex.
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     ~(rho1 = Cx(&0)) /\ ~(rho2 = Cx(&0)) /\ ~(rho3 = Cx(&0)) /\
     rho1 pow 2 * (x - z1) = xi1 pow 2 /\
     rho2 pow 2 * (x - z2) = xi2 pow 2 /\
     rho3 pow 2 * (x - z3) = xi3 pow 2
     ==> x = (let t = --(rho3 / rho2) *
                      ((rho2 * xi1 - rho1 * xi2) / (rho1 * xi3 - rho3 * xi1)) in
              let W = (z2 - z1 - t * (z3 - z1)) / (t - t pow 2) in
              z1 + (W + z3 - z1) pow 2 / (Cx(&4) * W))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MATCH_MP_TAC HYPERELL_RECOVER_BETA THEN
  MAP_EVERY EXISTS_TAC [`xi1 / rho1:complex`; `xi2 / rho2:complex`;
                        `xi3 / rho3:complex`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:complex) - z1 = (xi1 / rho1) pow 2 /\
                (x:complex) - z2 = (xi2 / rho2) pow 2 /\
                (x:complex) - z3 = (xi3 / rho3) pow 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_DIV] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
      [SYM th] THEN ASSUME_TAC th) THEN
    (SUBGOAL_THEN `~((rho1:complex) pow 2 = Cx(&0)) /\
                   ~((rho2:complex) pow 2 = Cx(&0)) /\
                   ~((rho3:complex) pow 2 = Cx(&0))` MP_TAC THENL
     [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0] THEN ARITH_TAC; ALL_TAC]) THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((xi1:complex) / rho1 - xi3 / rho3 = Cx(&0))` MP_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(z1 = z3:complex)` THEN REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(x:complex) - z1 = (xi1 / rho1) pow 2`;
                           `(x:complex) - z3 = (xi3 / rho3) pow 2`] THEN
    POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`~(rho1 = Cx(&0))`; `~(rho2 = Cx(&0))`;
                         `~(rho3 = Cx(&0))`] THEN
  CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The factors lam = D^M (Rj Xi - Ri Xj) of one pair of roots: order         *)
(* elements whose norm is bounded by that of the fixed element               *)
(* G = D^(2M) Ri^2 Rj^2 (Zj - Zi), since lam mu = G for the partner          *)
(* mu = D^M (Rj Xi + Ri Xj).                                                 *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_TR_DPOW_ADD = prove
 (`!n r D N (a:num->complex) b.
        nf_order n r (\k. Cx D pow N * a k) /\
        nf_order n r (\k. Cx D pow N * b k)
        ==> nf_order n r (\k. Cx D pow N * (a k + b k))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NF_ORDER_EQ THEN
  EXISTS_TAC `\k. Cx D pow N * (a:num->complex) k + Cx D pow N * b k` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`;
                   `\k. Cx D pow N * (a:num->complex) k`;
                   `\k. Cx D pow N * (b:num->complex) k`] NF_ORDER_ADD) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_ADD_LDISTRIB]]);;

let HYPERELL_TR_XORDER = prove
 (`!n r D (Z:num->complex) R (q:num->real) m M.
        integer D /\ nf_order n r (\k. Cx D * Z k) /\
        nf_order n r (\k. Cx D * R k) /\ (!i. integer(q i)) /\ m + 1 <= M
        ==> nf_order n r
             (\k. Cx D pow M * (R k * vsum(0..m-1) (\l. Cx(q l) * Z k pow l)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUPERELL_TR_DPOW_MONO THEN
  EXISTS_TAC `1 + (m - 1)` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN
    ASM_REWRITE_TAC[COMPLEX_POW_1] THEN
    MATCH_MP_TAC SUPERELL_TR_DPOW_POLY THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `m + 1 <= M` THEN ARITH_TAC]);;

let HYPERELL_TR_PAIR = prove
 (`!n c r D (Zi:num->complex) Zj Ri Rj (qi:num->real) qj ni nj M x
    (lam:num->complex) (G:num->complex).
     nf_data n c r /\ integer D /\ ~(D = &0) /\ ~(Zi 1 = Zj 1) /\
     ~(Ri 1 = Cx(&0)) /\ ~(Rj 1 = Cx(&0)) /\
     nf_order n r (\k. Cx D * Zi k) /\ nf_order n r (\k. Cx D * Zj k) /\
     nf_order n r (\k. Cx D * Ri k) /\ nf_order n r (\k. Cx D * Rj k) /\
     (!i. integer(qi i)) /\ (!i. integer(qj i)) /\ ni + nj + 3 <= M /\
     Ri 1 pow 2 * (x - Zi 1) =
     vsum(0..ni-1) (\l. Cx(qi l) * Zi 1 pow l) pow 2 /\
     Rj 1 pow 2 * (x - Zj 1) =
     vsum(0..nj-1) (\l. Cx(qj l) * Zj 1 pow l) pow 2
     ==> (!k. lam k =
              Cx D pow M *
              (Rj k * vsum(0..ni-1) (\l. Cx(qi l) * Zi k pow l) -
               Ri k * vsum(0..nj-1) (\l. Cx(qj l) * Zj k pow l))) /\
         (!k. G k = Cx D pow (M + M) * Ri k pow 2 * Rj k pow 2 *
                    (Zj k - Zi k))
         ==> nf_order n r lam /\ ~(cproduct(1..n) lam = Cx(&0)) /\
             norm(cproduct(1..n) lam) <= norm(cproduct(1..n) G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lam") (LABEL_TAC "G")) THEN
  SUBGOAL_THEN
   `nf_order n r
     (\k. Cx D pow M *
          ((Rj:num->complex) k *
           vsum(0..ni-1) (\l. Cx(qi l) * (Zi:num->complex) k pow l))) /\
    nf_order n r
     (\k. Cx D pow M *
          ((Ri:num->complex) k *
           vsum(0..nj-1) (\l. Cx(qj l) * (Zj:num->complex) k pow l)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HYPERELL_TR_XORDER THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ni + nj + 3 <= M` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (lam:num->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC NF_ORDER_EQ THEN
    EXISTS_TAC
     `\k. Cx D pow M *
          ((Rj:num->complex) k *
           vsum(0..ni-1) (\l. Cx(qi l) * (Zi:num->complex) k pow l) -
           (Ri:num->complex) k *
           vsum(0..nj-1) (\l. Cx(qj l) * (Zj:num->complex) k pow l))` THEN
    USE_THEN "lam" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUPERELL_TR_DPOW_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (G:num->complex)` ASSUME_TAC THENL
   [MATCH_MP_TAC NF_ORDER_EQ THEN
    EXISTS_TAC
     `\k. Cx D pow (M + M) * (Ri:num->complex) k pow 2 *
          (Rj:num->complex) k pow 2 * ((Zj:num->complex) k - Zi k)` THEN
    USE_THEN "G" (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUPERELL_TR_DPOW_MONO THEN EXISTS_TAC `2 + 2 + 1` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUPERELL_TR_DPOW_POW1 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUPERELL_TR_DPOW_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUPERELL_TR_DPOW_POW1 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC SUPERELL_TR_DPOW_SUB THEN ASM_REWRITE_TAC[COMPLEX_POW_1];
      UNDISCH_TAC `ni + nj + 3 <= M` THEN ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC
   `mu = \k. Cx D pow M *
             ((Rj:num->complex) k *
              vsum(0..ni-1) (\l. Cx(qi l) * (Zi:num->complex) k pow l) +
              (Ri:num->complex) k *
              vsum(0..nj-1) (\l. Cx(qj l) * (Zj:num->complex) k pow l))` THEN
  SUBGOAL_THEN `nf_order n r (mu:num->complex)` ASSUME_TAC THENL
   [EXPAND_TAC "mu" THEN MATCH_MP_TAC HYPERELL_TR_DPOW_ADD THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(lam:num->complex) 1 * (mu:num->complex) 1 = G 1`
  ASSUME_TAC THENL
   [USE_THEN "lam" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "G" (fun th -> REWRITE_TAC[th]) THEN
    EXPAND_TAC "mu" THEN REWRITE_TAC[COMPLEX_POW_ADD] THEN
    UNDISCH_TAC
     `(Ri:num->complex) 1 pow 2 * ((x:complex) - (Zi:num->complex) 1) =
      vsum(0..ni-1) (\l. Cx(qi l) * Zi 1 pow l) pow 2` THEN
    UNDISCH_TAC
     `(Rj:num->complex) 1 pow 2 * ((x:complex) - (Zj:num->complex) 1) =
      vsum(0..nj-1) (\l. Cx(qj l) * Zj 1 pow l) pow 2` THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((G:num->complex) 1 = Cx(&0))` ASSUME_TAC THENL
   [USE_THEN "G" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; COMPLEX_SUB_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                 `\j:num. if j = 0 then (lam:num->complex) else mu`;
                 `{0,1}`; `G:num->complex`] NF_ORDER_FACTOR_NORMS) THEN
  SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
           CPRODUCT_CLAUSES; IN_INSERT; ARITH_EQ; CPRODUCT_SING] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The core: for fixed field data (conjugate vectors of z1, z2, z3 and of    *)
(* rho1, rho2, rho3 in one number field), the set of x is finite.            *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_TR_CORE = prove
 (`!n c r D z1 z2 z3 rho1 rho2 rho3 (Z1:num->complex) Z2 Z3 R1 R2 R3
    n1 n2 n3.
     nf_data n c r /\ integer D /\ ~(D = &0) /\
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     ~(rho1 = Cx(&0)) /\ ~(rho2 = Cx(&0)) /\ ~(rho3 = Cx(&0)) /\
     nf_order n r (\k. Cx D * Z1 k) /\ nf_order n r (\k. Cx D * Z2 k) /\
     nf_order n r (\k. Cx D * Z3 k) /\ nf_order n r (\k. Cx D * R1 k) /\
     nf_order n r (\k. Cx D * R2 k) /\ nf_order n r (\k. Cx D * R3 k) /\
     Z1 1 = z1 /\ Z2 1 = z2 /\ Z3 1 = z3 /\
     R1 1 = rho1 /\ R2 1 = rho2 /\ R3 1 = rho3
     ==> FINITE {x | ?q1 q2 q3.
                       (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                       (!i. integer(q3 i)) /\
                       rho1 pow 2 * (x - z1) =
                       vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow 2 /\
                       rho2 pow 2 * (x - z2) =
                       vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow 2 /\
                       rho3 pow 2 * (x - z3) =
                       vsum(0..n3-1) (\i. Cx(q3 i) * z3 pow i) pow 2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  ABBREV_TAC `M = n1 + n2 + n3 + 3` THEN
  SUBGOAL_THEN `n1 + n2 + 3 <= M /\ n2 + n3 + 3 <= M /\ n3 + n1 + 3 <= M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `G12 = \k. Cx D pow (M + M) * R1 k pow 2 * R2 k pow 2 *
              ((Z2:num->complex) k - Z1 k)` THEN
  ABBREV_TAC
   `G23 = \k. Cx D pow (M + M) * R2 k pow 2 * R3 k pow 2 *
              ((Z3:num->complex) k - Z2 k)` THEN
  ABBREV_TAC
   `G31 = \k. Cx D pow (M + M) * R3 k pow 2 * R1 k pow 2 *
              ((Z1:num->complex) k - Z3 k)` THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
     `\k. Cx D * (R3:num->complex) k`; `\k. Cx D * (R1:num->complex) k`;
     `\k. Cx D * (R2:num->complex) k`;
     `norm(cproduct(1..n) (G12:num->complex)) +
      norm(cproduct(1..n) (G23:num->complex)) +
      norm(cproduct(1..n) (G31:num->complex))`] NF_SIEGEL_RATIO_FINITE) THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `TT:complex->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "TT"))) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\y. let t = --(rho3 / rho2) * y in
               let W = (z2 - z1 - t * (z3 - z1)) / (t - t pow 2) in
               z1 + (W + z3 - z1) pow 2 / (Cx(&4) * W))
          (TT:complex->bool)` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
  X_GEN_TAC `x:complex` THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:num->real` (X_CHOOSE_THEN `q2:num->real`
    (X_CHOOSE_THEN `q3:num->real` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `xi1 = vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i)` THEN
  ABBREV_TAC `xi2 = vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i)` THEN
  ABBREV_TAC `xi3 = vsum(0..n3-1) (\i. Cx(q3 i) * z3 pow i)` THEN
  ABBREV_TAC
   `lam12 = \k. Cx D pow M *
                ((R2:num->complex) k *
                 vsum(0..n1-1) (\l. Cx(q1 l) * (Z1:num->complex) k pow l) -
                 (R1:num->complex) k *
                 vsum(0..n2-1) (\l. Cx(q2 l) * (Z2:num->complex) k pow l))` THEN
  ABBREV_TAC
   `lam23 = \k. Cx D pow M *
                ((R3:num->complex) k *
                 vsum(0..n2-1) (\l. Cx(q2 l) * (Z2:num->complex) k pow l) -
                 (R2:num->complex) k *
                 vsum(0..n3-1) (\l. Cx(q3 l) * (Z3:num->complex) k pow l))` THEN
  ABBREV_TAC
   `lam31 = \k. Cx D pow M *
                ((R1:num->complex) k *
                 vsum(0..n3-1) (\l. Cx(q3 l) * (Z3:num->complex) k pow l) -
                 (R3:num->complex) k *
                 vsum(0..n1-1) (\l. Cx(q1 l) * (Z1:num->complex) k pow l))` THEN
  MAP_EVERY (fun (za,zb,ra,rb,qa,qb,na,nb,lam,g) ->
    MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `D:real`;
                   za; zb; ra; rb; qa; qb; na; nb; `M:num`; `x:complex`;
                   lam; g] HYPERELL_TR_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [EXPAND_TAC (fst(dest_var lam)) THEN REWRITE_TAC[];
        EXPAND_TAC (fst(dest_var g)) THEN REWRITE_TAC[]];
      STRIP_TAC])
   [`Z1:num->complex`,`Z2:num->complex`,`R1:num->complex`,`R2:num->complex`,
    `q1:num->real`,`q2:num->real`,`n1:num`,`n2:num`,
    `lam12:num->complex`,`G12:num->complex`;
    `Z2:num->complex`,`Z3:num->complex`,`R2:num->complex`,`R3:num->complex`,
    `q2:num->real`,`q3:num->real`,`n2:num`,`n3:num`,
    `lam23:num->complex`,`G23:num->complex`;
    `Z3:num->complex`,`Z1:num->complex`,`R3:num->complex`,`R1:num->complex`,
    `q3:num->real`,`q1:num->real`,`n3:num`,`n1:num`,
    `lam31:num->complex`,`G31:num->complex`] THEN
  MAP_EVERY (fun t -> ASSUME_TAC(ISPEC t NORM_POS_LE))
   [`cproduct(1..n) (G12:num->complex)`; `cproduct(1..n) (G23:num->complex)`;
    `cproduct(1..n) (G31:num->complex)`] THEN
  USE_THEN "TT" (MP_TAC o SPECL [`lam12:num->complex`; `lam23:num->complex`;
                                 `lam31:num->complex`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
      X_GEN_TAC `k:num` THEN DISCH_TAC THEN
      MAP_EVERY EXPAND_TAC ["lam12"; "lam23"; "lam31"] THEN
      CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lam12:num->complex) 1 = Cx D pow M * (rho2 * xi1 - rho1 * xi2) /\
    (lam31:num->complex) 1 = Cx D pow M * (rho1 * xi3 - rho3 * xi1)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lam12"; "lam31"] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `((rho2:complex) * xi1 - rho1 * xi2) /
              (rho1 * xi3 - rho3 * xi1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HYPERELL_RECOVER THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `((rho2:complex) * xi1 - rho1 * xi2) / (rho1 * xi3 - rho3 * xi1) =
      (Cx D pow M * (rho2 * xi1 - rho1 * xi2)) /
      (Cx D pow M * (rho1 * xi3 - rho3 * xi1))`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `~(Cx D pow M = Cx(&0))` MP_TAC THENL
       [ASM_REWRITE_TAC[COMPLEX_POW_EQ_0; CX_INJ]; CONV_TAC COMPLEX_FIELD];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Fixed d1, d2, d3: choose square roots rho_i and a common field            *)
(* (SUPERELL_TR_PRIMITIVE).                                                  *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_THREE_ROOTS_FIXED = prove
 (`!z1 z2 z3 d1 d2 d3 n1 n2 n3.
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     algebraic_integer z1 /\ algebraic_integer z2 /\ algebraic_integer z3 /\
     algebraic_integer d1 /\ ~(d1 = Cx(&0)) /\
     algebraic_integer d2 /\ ~(d2 = Cx(&0)) /\
     algebraic_integer d3 /\ ~(d3 = Cx(&0))
     ==> FINITE {x | ?q1 q2 q3.
                       (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                       (!i. integer(q3 i)) /\
                       d1 * (x - z1) =
                       vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow 2 /\
                       d2 * (x - z2) =
                       vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow 2 /\
                       d3 * (x - z3) =
                       vsum(0..n3-1) (\i. Cx(q3 i) * z3 pow i) pow 2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d1:complex`; `2`] SUPERELL_TR_ROOT_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d2:complex`; `2`] SUPERELL_TR_ROOT_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho2:complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d3:complex`; `2`] SUPERELL_TR_ROOT_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho3:complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `{z1:complex, z2, z3, rho1, rho2, rho3}`
    SUPERELL_TR_PRIMITIVE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT;
                NOT_IN_EMPTY] THEN
    ASM_SIMP_TAC[ALGEBRAIC_INTEGER_IMP_ALGEBRAIC_NUMBER];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
   (X_CHOOSE_THEN `r:num->complex` (X_CHOOSE_THEN `D:real`
     (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Z")))))))) THEN
  USE_THEN "Z" (MP_TAC o SPEC `z1:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z1:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `z2:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z2:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `z3:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z3:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `rho1:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `R1:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `rho2:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `R2:num->complex` STRIP_ASSUME_TAC) THEN
  USE_THEN "Z" (MP_TAC o SPEC `rho3:complex`) THEN REWRITE_TAC[IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `R3:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `c:num->real`; `r:num->complex`; `D:real`;
                 `z1:complex`; `z2:complex`; `z3:complex`;
                 `rho1:complex`; `rho2:complex`; `rho3:complex`;
                 `Z1:num->complex`; `Z2:num->complex`; `Z3:num->complex`;
                 `R1:num->complex`; `R2:num->complex`; `R3:num->complex`;
                 `n1:num`; `n2:num`; `n3:num`]
    HYPERELL_TR_CORE) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The export: finite union over the finitely many (d1, d2, d3).             *)
(* ------------------------------------------------------------------------- *)

let HYPERELL_THREE_ROOTS = prove
 (`!z1 z2 z3 (DD1:complex->bool) DD2 DD3 n1 n2 n3.
     ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
     algebraic_integer z1 /\ algebraic_integer z2 /\ algebraic_integer z3 /\
     FINITE DD1 /\ FINITE DD2 /\ FINITE DD3 /\
     (!d. d IN DD1 ==> algebraic_integer d /\ ~(d = Cx(&0))) /\
     (!d. d IN DD2 ==> algebraic_integer d /\ ~(d = Cx(&0))) /\
     (!d. d IN DD3 ==> algebraic_integer d /\ ~(d = Cx(&0)))
     ==> FINITE {x | ?d1 d2 d3 q1 q2 q3.
                       d1 IN DD1 /\ d2 IN DD2 /\ d3 IN DD3 /\
                       (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                       (!i. integer(q3 i)) /\
                       d1 * (x - z1) =
                       vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow 2 /\
                       d2 * (x - z2) =
                       vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow 2 /\
                       d3 * (x - z3) =
                       vsum(0..n3-1) (\i. Cx(q3 i) * z3 pow i) pow 2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `UNIONS
     (IMAGE (\p. {x | ?q1 q2 q3.
                        (!i. integer(q1 i)) /\ (!i. integer(q2 i)) /\
                        (!i. integer(q3 i)) /\
                        FST p * (x - z1) =
                        vsum(0..n1-1) (\i. Cx(q1 i) * z1 pow i) pow 2 /\
                        FST(SND p) * (x - z2) =
                        vsum(0..n2-1) (\i. Cx(q2 i) * z2 pow i) pow 2 /\
                        SND(SND p) * (x - z3) =
                        vsum(0..n3-1) (\i. Cx(q3 i) * z3 pow i) pow 2})
            ((DD1:complex->bool) CROSS (DD2:complex->bool) CROSS
             (DD3:complex->bool)))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[FINITE_CROSS];
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
      MAP_EVERY X_GEN_TAC [`d1:complex`; `d2:complex`; `d3:complex`] THEN
      STRIP_TAC THEN MATCH_MP_TAC HYPERELL_THREE_ROOTS_FIXED THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_PAIR_THM;
                IN_CROSS] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]);;
