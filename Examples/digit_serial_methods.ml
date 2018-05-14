(* ========================================================================= *)
(* HOL Light formalizations of some of the main theorems from the paper      *)
(* by Warren Ferguson, Jesse Bingham, Levent Erkok, John Harrison and        *)
(* Joe Leslie-Hurd: "Digit Serial Methods with Applications to               *)
(* Division and Square Root", IEEE Transactions on Computers, vol. 67,       *)
(* issue 3, pp. 449-456, 2017.                                               *)
(* ========================================================================= *)

(*** This dependency is just for some convex function basics.    ***)
(*** It is a bit extravagent for the small amount actually used. ***)

needs "Multivariate/realanalysis.ml";;

(* ------------------------------------------------------------------------- *)
(* The main proxy theorem.                                                   *)
(* ------------------------------------------------------------------------- *)

let THEOREM_V_1 = prove
 (`!(V:real) (beta:num->real) (omega:num->real) (DSF:num->real->real)
    (B:num->real) (H:num->real) (v:num->real) (Tl:num->real) (Tp:num->real)
    (PSI:num->real#real->real) (psi:num->real#real->real)
    (tau:num->real->real) (taup:num->real->real).

        // Environmental assumptions including nondecreasing property
        &0 <= V /\
        (!i. i >= 0 ==> beta i > &0) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        (!i. i >= 0 ==> abs (psi i (V,Tl i)) <= PSI i (V,abs(Tl i))) /\
        (!i x y. &0 <= x /\ x <= y ==> PSI i (V,x) <= PSI i (V,y)) /\

        (!u. tau 0 u = u) /\
        (!i u. tau (i + 1) u =
               beta (i + 1) * PSI i (u,tau i u) * tau i u + omega (i + 1)) /\
        (!i u. taup i u = (&1 + PSI i (u,tau i u)) * tau i u) /\

        // Computing recursively
        B 0 = &1 /\ H 0 = &0 /\ Tl 0 = V /\

        (!i. Tp i = (&1 + psi i (V,Tl i)) * Tl i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. Tl (i + 1) = beta (i + 1) * Tl i - v (i + 1))

        // Conclude loop invariant and bounds.
        ==> (!i. V = H i + Tl i / B i) /\
            (!i. i >= 0 ==> abs(Tl i) <= tau i V) /\
            (!i. i >= 0 ==> abs(Tp i) <= taup i V)`,

  REPEAT GEN_TAC THEN REWRITE_TAC[GE; real_gt; real_gt; LE_0] THEN
  STRIP_TAC THEN

  (*** Lemma: all the B_i are strictly positive, by induction ***)

  SUBGOAL_THEN `!i:num. &0 < B i` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC[REAL_LT_01; ADD1; REAL_LT_MUL];
    ALL_TAC] THEN

  (*** Handle the tau_p clause first, assuming the other two ***)

  MATCH_MP_TAC(TAUT `(p /\ q ==> r) /\ p /\ q ==> p /\ q /\ r`) THEN
  CONJ_TAC THENL
   [DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL] THEN GEN_TAC THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> abs(&1 + x) <= &1 + a`) THEN
    TRANS_TAC REAL_LE_TRANS `(PSI:num->real#real->real) i (V,abs(Tl i))` THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[REAL_ABS_POS];
    ALL_TAC] THEN

  (*** Start main induction and dispose of base case ***)

  REWRITE_TAC[AND_FORALL_THM] THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[] THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN

  (*** Prove the step case of the loop invariant ***)
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[ADD1] THEN
    SUBGOAL_THEN `&0 < beta (i + 1) /\ &0 < B i` MP_TAC THENL
     [ASM_REWRITE_TAC[]; CONV_TAC REAL_FIELD];
    ALL_TAC] THEN

  (*** Massage the goal a little then chain through the inequalities ***)

  FIRST_X_ASSUM(CONJUNCTS_THEN (ASSUME_TAC o GSYM)) THEN
  REWRITE_TAC[ADD1] THEN

  TRANS_TAC REAL_LE_TRANS
   `abs(-- beta (i + 1)  * psi i (V:real,Tl i) * Tl i +
        (beta (i + 1) * Tp i - DSF (i + 1) (beta (i + 1) * Tp i)))` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN

  TRANS_TAC REAL_LE_TRANS
   `beta (i + 1) * abs(psi i (V:real,Tl i)) * abs(Tl i) + omega(i + 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `abs(x) <= a /\ abs(y) <= b ==> abs(x + y) <= a + b`) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= i + 1`] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NEG] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`; REAL_LE_REFL];
    ALL_TAC] THEN

  ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_LE_RADD] THEN
  ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
  TRANS_TAC REAL_LE_TRANS `(PSI:num->real#real->real) i (V,abs(Tl i))` THEN
  ASM_SIMP_TAC[] THEN ASM_MESON_TAC[REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Restricted posynomials (definition V.2)                                   *)
(* ------------------------------------------------------------------------- *)

let posynomial = new_definition
 `posynomial p <=>
  ?c (n:num->real) k.
        (!i. 1 <= i /\ i <= k ==> c i > &0 /\ integer(n i)) /\
        (!v. &0 < v ==> sum (1..k) (\i. c i * v rpow (n i)) = p v)`;;

let POSYNOMIAL_0 = prove
 (`posynomial (\v. &0)`,
  REWRITE_TAC[posynomial] THEN
  MAP_EVERY EXISTS_TAC [`(\i. &1):num->real`; `(\i. &0):num->real`; `0`] THEN
  REWRITE_TAC[SUM_CLAUSES_NUMSEG] THEN ARITH_TAC);;

let POSYNOMIAL_1 = prove
 (`posynomial (\v. &1)`,
  REWRITE_TAC[posynomial] THEN
  MAP_EVERY EXISTS_TAC [`(\i. &1):num->real`; `(\i. &0):num->real`; `1`] THEN
  REWRITE_TAC[INTEGER_CLOSED; SUM_SING_NUMSEG; RPOW_POW] THEN REAL_ARITH_TAC);;

let POSYNOMIAL_CMUL = prove
 (`!p c. posynomial p /\ &0 < c ==> posynomial(\v. c * p(v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[posynomial] THEN DISCH_THEN(X_CHOOSE_THEN `d:num->real`
   (fun th -> EXISTS_TAC `(\i. c * d i):num->real` THEN MP_TAC th)) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  SIMP_TAC[SUM_LMUL; GSYM REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[real_gt; REAL_LT_MUL]);;

let POSYNOMIAL_CONST = prove
 (`!c. &0 <= c ==> posynomial (\v. c)`,
  REWRITE_TAC[REAL_ARITH `&0 <= c <=> c = &0 \/ &0 < c`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[POSYNOMIAL_0] THEN
  GEN_REWRITE_TAC (RAND_CONV o ABS_CONV) [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC POSYNOMIAL_CMUL THEN
  ASM_REWRITE_TAC[POSYNOMIAL_1]);;

let POSYNOMIAL_VPOWMUL = prove
 (`!p n. posynomial p /\ integer n ==> posynomial(\v. p(v) * v rpow n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[posynomial] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:num->real` THEN
  GEN_REWRITE_TAC BINOP_CONV [SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `nn:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(\i. nn i + n):num->real` THEN
  ASM_SIMP_TAC[RPOW_ADD; REAL_MUL_ASSOC; SUM_RMUL; INTEGER_CLOSED]);;

let POSYNOMIAL_VMUL = prove
 (`!p. posynomial p ==> posynomial(\v. p(v) * v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real->real`; `&1:real`] POSYNOMIAL_VPOWMUL) THEN
  ASM_REWRITE_TAC[RPOW_POW; REAL_POW_1; INTEGER_CLOSED]);;

let POSYNOMIAL_VDIV = prove
 (`!p. posynomial p ==> posynomial(\v. p(v) / v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:real->real`; `-- &1:real`] POSYNOMIAL_VPOWMUL) THEN
  ASM_SIMP_TAC[RPOW_POW; real_div; RPOW_NEG; REAL_POW_1; INTEGER_CLOSED]);;

let POSYNOMIAL_V = prove
 (`posynomial(\v. v)`,
  GEN_REWRITE_TAC (RAND_CONV o ABS_CONV) [GSYM REAL_MUL_LID] THEN
  MATCH_MP_TAC POSYNOMIAL_VMUL THEN REWRITE_TAC[POSYNOMIAL_1]);;

let POSYNOMIAL_ADD = prove
 (`!p q. posynomial p /\ posynomial q ==> posynomial(\v. p v + q v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[posynomial; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `n1:num->real`; `m:num`] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`c2:num->real`; `n2:num->real`; `n:num`] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `\i. if i <= m then (c1:num->real) i else c2 (i - m)` THEN
  EXISTS_TAC `\i. if i <= m then (n1:num->real) i else n2 (i - m)` THEN
  EXISTS_TAC `m + n:num` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[ARITH_RULE
     `~(i:num <= m) /\ i <= m + n ==> 1 <= i - m /\ i - m <= n`];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[MESON[] `(if p then f else g) (if p then x else y) =
        if p then f x else g y`] THEN
    SIMP_TAC[SUM_CASES; FINITE_NUMSEG; IN_NUMSEG;
      ARITH_RULE `(1 <= i /\ i <= m + n) /\ i <= m <=> 1 <= i /\ i <= m`;
      ARITH_RULE `(1 <= i /\ i <= m + n) /\ ~(i <= m) <=>
                  1 + m <= i /\ i <= n + m`] THEN
    REWRITE_TAC[GSYM numseg; SUM_OFFSET; ADD_SUB] THEN ASM_SIMP_TAC[]]);;

let POSYNOMIAL_SUM = prove
 (`!k:A->bool p.
        FINITE k /\ (!i. i IN k ==> posynomial(\v. p v i))
        ==> posynomial (\v. sum k (p v))`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; POSYNOMIAL_0; POSYNOMIAL_ADD; FORALL_IN_INSERT;
            ETA_AX]);;

let POSYNOMIAL_MUL = prove
 (`!p q. posynomial p /\ posynomial q ==> posynomial(\v. p v * q v)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV)
   [CONV_RULE (RAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) (SPEC_ALL posynomial)] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[posynomial] THEN
  REWRITE_TAC[GSYM posynomial] THEN
  SIMP_TAC[SUM_SUM_PRODUCT; FINITE_NUMSEG; REAL_MUL_SUM] THEN
  MATCH_MP_TAC POSYNOMIAL_SUM THEN
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT; FINITE_NUMSEG; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(c * x) * (d * y):real = (c * d) * (x * y)`] THEN
  SIMP_TAC[posynomial; GSYM RPOW_ADD] THEN REWRITE_TAC[GSYM posynomial] THEN
  MATCH_MP_TAC POSYNOMIAL_VPOWMUL THEN ASM_SIMP_TAC[INTEGER_CLOSED] THEN
  ONCE_REWRITE_TAC[GSYM REAL_MUL_RID] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[real_gt]) THEN
  MATCH_MP_TAC POSYNOMIAL_CMUL THEN
  ASM_SIMP_TAC[REAL_LT_MUL; POSYNOMIAL_1]);;

let REAL_CONVEX_ON_POSYNOMIAL = prove
 (`!p. posynomial p ==> p real_convex_on {x | x > &0}`,
  GEN_TAC THEN REWRITE_TAC[posynomial; LEFT_IMP_EXISTS_THM; real_gt] THEN
  MAP_EVERY X_GEN_TAC [`c:num->real`; `n:num->real`; `m:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
   [SET_RULE `&0 < v <=> v IN {x | &0 < x}`] THEN
  MATCH_MP_TAC(MESON[REAL_CONVEX_ON_EQ]
   `is_realinterval s /\ f real_convex_on s
    ==> (!x. x IN s ==> f x = g x) ==> g real_convex_on s`) THEN
  REWRITE_TAC[IS_REALINTERVAL_CLAUSES] THEN
  MATCH_MP_TAC REAL_CONVEX_ON_SUM THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN MATCH_MP_TAC REAL_CONVEX_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  MATCH_MP_TAC REAL_CONVEX_ON_RPOW_INTEGER THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The corollary.                                                            *)
(* ------------------------------------------------------------------------- *)

let COROLLARY_V_3 = prove
 (`!(V:real) (beta:num->real) (omega:num->real) (DSF:num->real->real)
    (B:num->real) (H:num->real) (v:num->real) (Tl:num->real) (Tp:num->real)
    (PSI:num->real#real->real) (psi:num->real#real->real)
    (tau:num->real->real) (taup:num->real->real).

        // Environmental assumptions including nondecreasing property
        &0 < V /\
        (!i. i >= 0 ==> beta i > &0) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        (!i. i >= 0 ==> abs (psi i (V,Tl i)) <= PSI i (V,abs(Tl i))) /\
        (!i x y. &0 <= x /\ x <= y ==> PSI i (V,x) <= PSI i (V,y)) /\

        (!u. tau 0 u = u) /\
        (!i u. tau (i + 1) u =
               beta (i + 1) * PSI i (u,tau i u) * tau i u + omega (i + 1)) /\
        (!i u. taup i u = (&1 + PSI i (u,tau i u)) * tau i u) /\

        // Computing recursively
        B 0 = &1 /\ H 0 = &0 /\ Tl 0 = V /\

        (!i. Tp i = (&1 + psi i (V,Tl i)) * Tl i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. Tl (i + 1) = beta (i + 1) * Tl i - v (i + 1)) /\

        // The extra posynomial-related assumption
        (!i p. i >= 0 /\ posynomial p
               ==> posynomial (\v. PSI i (v,p v)))

        // Hence conclude our bounds
        ==> !a b. real_interval[a,b] SUBSET {x | x > &0}
                  ==> !i u. u IN real_interval[a,b]
                            ==> tau i u <= max (tau i a) (tau i b) /\
                                taup i u <= max (taup i a) (taup i b)`,
  REWRITE_TAC[real_gt; real_ge; GT; GE; LE_0] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `!i:num. posynomial (tau i)` ASSUME_TAC THENL
   [INDUCT_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    ASM_REWRITE_TAC[ADD1; POSYNOMIAL_V] THEN
    MATCH_MP_TAC POSYNOMIAL_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC POSYNOMIAL_CMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POSYNOMIAL_MUL THEN ASM_SIMP_TAC[ETA_AX];
      MATCH_MP_TAC POSYNOMIAL_CONST THEN
      ASM_MESON_TAC[REAL_LE_TRANS; REAL_ABS_POS; ARITH_RULE `1 <= i + 1`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i:num. posynomial (taup i)` ASSUME_TAC THENL
   [INDUCT_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[ADD1] THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POSYNOMIAL_MUL THEN REWRITE_TAC[ETA_AX] THEN
    (CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_ACCEPT_TAC]) THEN
    MATCH_MP_TAC POSYNOMIAL_ADD THEN REWRITE_TAC[POSYNOMIAL_1] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[ETA_AX] THEN
    FIRST_X_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_CONVEX_LOWER_REAL_INTERVAL THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
        REAL_CONVEX_ON_SUBSET)) THEN
  REWRITE_TAC[GSYM real_gt] THEN MATCH_MP_TAC REAL_CONVEX_ON_POSYNOMIAL THEN
  FIRST_X_ASSUM MATCH_ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Add the other clauses to the corollary.                                   *)
(* ------------------------------------------------------------------------- *)

let FULL_COROLLARY = prove
 (`!(V:real) (beta:num->real) (omega:num->real) (DSF:num->real->real)
    (B:num->real) (H:num->real) (v:num->real) (Tl:num->real) (Tp:num->real)
    (PSI:num->real#real->real) (psi:num->real#real->real)
    (tau:num->real->real) (taup:num->real->real).

        // Not stated explicitly in the theorem itself but higher up.
        &0 < V /\

        // Environmental assumptions including nondecreasing property
        (!i. i >= 0 ==> beta i > &0) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        (!i. i >= 0 ==> abs (psi i (V,Tl i)) <= PSI i (V,abs(Tl i))) /\
        (!i x y. &0 <= x /\ x <= y ==> PSI i (V,x) <= PSI i (V,y)) /\

        (!u. tau 0 u = u) /\
        (!i u. tau (i + 1) u =
               beta (i + 1) * PSI i (u,tau i u) * tau i u + omega (i + 1)) /\
        (!i u. taup i u = (&1 + PSI i (u,tau i u)) * tau i u) /\

        // Computing recursively
        B 0 = &1 /\ H 0 = &0 /\ Tl 0 = V /\

        (!i. Tp i = (&1 + psi i (V,Tl i)) * Tl i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. Tl (i + 1) = beta (i + 1) * Tl i - v (i + 1)) /\

        // The extra posynomial-related assumption
        (!i p. i >= 0 /\ posynomial p
               ==> posynomial (\v. PSI i (v,p v)))

        // Hence conclude invariant and all bounds.
        ==> (!i. V = H i + Tl i / B i) /\
            (!i. abs(Tl i) <= tau i V) /\
            (!i. abs(Tp i) <= taup i V) /\
            (!a b. real_interval[a,b] SUBSET {x | x > &0}
                   ==> !i u. u IN real_interval[a,b]
                             ==> tau i u <= max (tau i a) (tau i b) /\
                                 taup i u <= max (taup i a) (taup i b))`,
  REWRITE_TAC[real_gt; real_ge; GT; GE; LE_0] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> (p /\ q /\ r) /\ s`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[GE; LE_0] THEOREM_V_1) THEN
    MAP_EVERY EXISTS_TAC
     [`beta:num->real`; `omega:num->real`; `DSF:num->real->real`;
      `v:num->real`; `PSI:num->real#real->real`;
      `psi:num->real#real->real`] THEN
    ASM_REWRITE_TAC[real_gt];

    MATCH_MP_TAC(REWRITE_RULE[real_gt] COROLLARY_V_3) THEN
    MAP_EVERY EXISTS_TAC
     [`V:real`; `beta:num->real`; `omega:num->real`; `DSF:num->real->real`;
      `B:num->real`; `H:num->real`; `v:num->real`; `Tl:num->real`;
      `Tp:num->real`;
      `PSI:num->real#real->real`; `psi:num->real#real->real`] THEN
    ASM_REWRITE_TAC[GE; LE_0]]);;

(* ------------------------------------------------------------------------- *)
(* Instantiations for division and square root.                              *)
(* ------------------------------------------------------------------------- *)

let BOUND_THEOREM_DIV = prove
 (`!beta Sigma omega B DSF H R Tp X Y g sigma v.
        (!i. i >= 0 ==> beta i > &0) /\
        &1 / &2 <= X /\ X < &1 /\
        &1 <= Y /\ Y < &2 /\
        (!y. &1 <= y /\ y < &2
             ==> g y = (&1 + sigma y) / y /\ abs(sigma y) <= Sigma) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        B 0 = &1 /\ H 0 = &0 /\ R 0 = X /\
        (!i. Tp i = g(Y) * R i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. R (i + 1) = beta (i + 1) * R i -  v(i + 1) * Y)
        ==> ?tau. (!u. tau 0 u = u) /\
                  (!i u. tau (i + 1) u =
                         beta (i + 1) * Sigma * tau i u + omega (i + 1)) /\
                  (!i. abs(X / Y - H i)
                       <= max (tau i (&1 / &4)) (tau i (&1)) / B i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GE; LE_0; real_gt] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Sigma` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1:real`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. &0 < (B:num->real) i` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL; ADD1; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X /\ &0 < Y` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X / Y` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LT_DIV]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`PSI:num->real#real->real = \i (u,t). Sigma`;
    `psi:num->real#real->real = \i (u,t). sigma(Y:real)`] THEN
  (X_CHOOSE_THEN `tau:num->real->real`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ADD1]) o
   prove_recursive_functions_exist num_RECURSION)
    `(!u:real. tau 0 u = u) /\
     (!i u. tau (SUC i) u =
            beta (i + 1) * PSI i (u,tau i u) * tau i u + omega (i + 1))` THEN
  (X_CHOOSE_THEN `Tl:num->real`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ADD1]) o
   prove_recursive_functions_exist num_RECURSION)
    `Tl 0 :real = X / Y /\
    !i. Tl (SUC i) = beta (i + 1) * Tl i - v (i + 1)` THEN
  ABBREV_TAC
   `taup:num->real->real = \i u. (&1 + PSI i (u,tau i u)) * tau i u` THEN
  MP_TAC(ISPECL
   [`X / Y:real`;
    `beta:num->real`;
    `omega:num->real`;
    `DSF:num->real->real`;
    `B:num->real`;
    `H:num->real`;
    `v:num->real`;
    `Tl:num->real`;
    `Tp:num->real`;
    `PSI:num->real#real->real`;
    `psi:num->real#real->real`;
    `tau:num->real->real`;
    `taup:num->real->real`]
    FULL_COROLLARY) THEN
  REWRITE_TAC[GE; LE_0; real_gt] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN MAP_EVERY EXPAND_TAC ["PSI"; "psi"] THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN NO_TAC;
      EXPAND_TAC "PSI" THEN REWRITE_TAC[REAL_LE_REFL] THEN NO_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN NO_TAC;
      EXPAND_TAC "taup" THEN REWRITE_TAC[] THEN NO_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[REAL_ARITH `a / b * c:real = a * c / b`] THEN
      AP_TERM_TAC THEN ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN
      SPEC_TAC(`i:num`,`j:num`) THEN
      INDUCT_TAC THEN ASM_SIMP_TAC[ADD1; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      EXPAND_TAC "PSI" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[POSYNOMIAL_CONST] THEN NO_TAC];
    STRIP_TAC THEN EXISTS_TAC `tau:num->real->real` THEN
    ASM_REWRITE_TAC[REAL_ADD_SUB] THEN CONJ_TAC THENL
     [EXPAND_TAC "PSI" THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_DIV2_EQ;
                 REAL_ARITH `&0 < b ==> abs b = b`] THEN
    X_GEN_TAC `i:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1 / &4`; `&1`]) THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `X / Y:real`]) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS]] THEN
    REWRITE_TAC[REAL_ARITH
     `&1 / &4 <= X / Y /\ X / Y <= &1 <=>
      &1 / &2 * inv(&2) <= X * inv Y /\ X * inv Y <= &1 * inv(&1)`] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_INV2) THEN
    REWRITE_TAC[REAL_LE_INV_EQ] THEN ASM_REAL_ARITH_TAC]);;

let BOUND_THEOREM_SQRT = prove
 (`!beta Sigma omega B DSF H R Tp X g sigma v.
        (!i. i >= 0 ==> beta i > &0) /\
        &1 / &4 <= X /\ X < &1 /\
        (!x. &1 / &4 <= x /\ x < &1
             ==> g x = (&1 + sigma x) / sqrt x /\
                 abs(sigma x) <= Sigma) /\
        (!i. i >= 1 ==> (!x. abs (x - DSF i x) <= omega i)) /\
        B 0 = &1 /\ H 0 = &0 /\ R 0 = X / &2 /\
        (!i. Tp i = (if i = 0 then &2 else &1) * g(X) * R i) /\
        (!i. v (i + 1) = DSF (i + 1) (beta (i + 1) * Tp i)) /\
        (!i. B (i + 1) = beta (i + 1) * B i) /\
        (!i. H (i + 1) = H i + v (i + 1) / B (i + 1)) /\
        (!i. R (i + 1) =
             beta (i + 1) * R i -  v(i + 1) * (H(i + 1) + H i) / &2)
        ==> ?tau.
                  (!u. tau 0 u = u) /\
                  (!i u. tau (i + 1) u =
                         beta (i + 1) *
                         (if i = 0 then Sigma
                          else Sigma + (&1 + Sigma) * tau i u / (&2 * u * B i))
                          * tau i u +
                         omega (i + 1)) /\
                  (!i. abs(sqrt X - H i)
                       <= max (tau i (&1 / &2)) (tau i (&1)) / B i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GE; LE_0; real_gt] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= Sigma` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &2`) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. &0 < (B:num->real) i` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_SIMP_TAC[REAL_LT_MUL; ADD1; REAL_LT_01]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < X` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sqrt X` ASSUME_TAC THENL
   [ASM_MESON_TAC[SQRT_POS_LT]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`PSI:num->real#real->real = \i (u,t).
        if i = 0 then Sigma
        else Sigma + (&1 + Sigma) * t / (&2 * u * B i)`;
    `psi:num->real#real->real = \i (u,t).
        if i = 0 then sigma(X)
        else (&1 + sigma(X:real)) * (&1 - t / (&2 * u * B i)) - &1`] THEN
  (X_CHOOSE_THEN `tau:num->real->real`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ADD1]) o
   prove_recursive_functions_exist num_RECURSION)
    `(!u:real. tau 0 u = u) /\
     (!i u. tau (SUC i) u =
            beta (i + 1) * PSI i (u,tau i u) * tau i u + omega (i + 1))` THEN
  (X_CHOOSE_THEN `Tl:num->real`
    (STRIP_ASSUME_TAC o REWRITE_RULE[ADD1]) o
   prove_recursive_functions_exist num_RECURSION)
    `Tl 0 = sqrt(X) /\
    !i. Tl (SUC i) = beta (i + 1) * Tl i - v (i + 1)` THEN
  ABBREV_TAC
   `taup:num->real->real = \i u. (&1 + PSI i (u,tau i u)) * tau i u` THEN
  MP_TAC(ISPECL
   [`sqrt X`;
    `beta:num->real`;
    `omega:num->real`;
    `DSF:num->real->real`;
    `B:num->real`;
    `H:num->real`;
    `v:num->real`;
    `Tl:num->real`;
    `Tp:num->real`;
    `PSI:num->real#real->real`;
    `psi:num->real#real->real`;
    `tau:num->real->real`;
    `taup:num->real->real`]
    FULL_COROLLARY) THEN
  REWRITE_TAC[GE; LE_0; real_gt] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN MAP_EVERY EXPAND_TAC ["PSI"; "psi"] THEN
      REWRITE_TAC[] THEN ASM_CASES_TAC `i = 0` THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs x <= a /\ abs((&1 + x) * y) <= b
        ==> abs((&1 + x) * (&1 - y) - &1) <= a + b`) THEN
      ASM_SIMP_TAC[REAL_ABS_MUL] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS] THEN
      ASM_SIMP_TAC[REAL_ARITH `abs x <= a ==> abs(&1 + x) <= &1 + a`] THEN
      REWRITE_TAC[REAL_ABS_DIV] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < x ==> abs(&2 * x) = &2 * x`) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `x:real`; `y:real`] THEN STRIP_TAC THEN
      EXPAND_TAC "PSI" THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_LMUL_EQ; REAL_LE_DIV2_EQ;
                   REAL_ARITH `&0 <= s ==> &0 < &1 + s`; REAL_LT_MUL;
                   REAL_ARITH `&0 < &2 * x <=> &0 < x`] THEN
      REAL_ARITH_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      ASM_REWRITE_TAC[] THEN NO_TAC;
      EXPAND_TAC "taup" THEN REWRITE_TAC[] THEN NO_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      X_GEN_TAC `i:num` THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `i = 0` THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[REAL_DIV_SQRT; REAL_LT_IMP_LE; REAL_ARITH
         `&2 * c / s * x / &2 = c * x / s`];
        ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_LID; REAL_ARITH `&1 + x - &1 = x`] THEN
      ASM_SIMP_TAC[] THEN REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC(REAL_FIELD
       `&0 < b /\ &0 < s /\ r = (s - t / b / &2) * t
        ==> inv s * r = (&1 - t * inv(&2 * s * b)) * t`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `!j:num. Tl j / B j = sqrt X - H j`
      ASSUME_TAC THENL
       [INDUCT_TAC THEN ASM_REWRITE_TAC[REAL_SUB_RZERO; REAL_DIV_1; ADD1] THEN
        UNDISCH_TAC `Tl(j:num) / B j = sqrt X - H j` THEN
        SUBGOAL_THEN `&0 < beta(j + 1) /\ &0 < B j` MP_TAC THENL
         [ASM_REWRITE_TAC[]; CONV_TAC REAL_FIELD];
        ASM_REWRITE_TAC[REAL_ARITH `s - (s - h) / &2 = (s + h) / &2`]] THEN
      MATCH_MP_TAC(REAL_FIELD
       `!b. &0 < b /\ x / b = y / &2 * z / b ==> x = y / &2 * z`) THEN
      EXISTS_TAC `(B:num->real) i` THEN ASM_REWRITE_TAC[REAL_ARITH
       `(x + h) / &2 * (x - h) = (x pow 2 - h pow 2) / &2`] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE] THEN
      ASM_SIMP_TAC[REAL_EQ_LDIV_EQ] THEN
      SPEC_TAC(`i:num`,`j:num`) THEN
      MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; REWRITE_TAC[ADD1]] THEN
      ONCE_REWRITE_TAC[ASSUME
      `!i. R (i + 1) =
           beta (i + 1) * R i - v (i + 1) * (H (i + 1) + H i) / &2`] THEN
      X_GEN_TAC `j:num` THEN SIMP_TAC[] THEN
      REWRITE_TAC[ASSUME
       `!i. H (i + 1):real = H i + v (i + 1) / B (i + 1)`] THEN
      REWRITE_TAC[ASSUME `!i. B (i + 1):real = beta (i + 1) * B i`] THEN
      SUBGOAL_THEN `&0 < beta(j + 1) /\ &0 < B j` MP_TAC THENL
       [ASM_REWRITE_TAC[]; CONV_TAC REAL_FIELD];
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      FIRST_X_ASSUM MATCH_ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`i:num`; `p:real->real`] THEN DISCH_TAC THEN
      EXPAND_TAC "PSI" THEN REWRITE_TAC[] THEN
      ASM_CASES_TAC `i = 0` THEN ASM_SIMP_TAC[POSYNOMIAL_CONST] THEN
      MATCH_MP_TAC POSYNOMIAL_ADD THEN
      ASM_SIMP_TAC[POSYNOMIAL_CONST] THEN
      MATCH_MP_TAC POSYNOMIAL_MUL THEN
      ASM_SIMP_TAC[POSYNOMIAL_CONST; REAL_ARITH
       `&0 <= s ==> &0 <= &1 + s`] THEN
      REWRITE_TAC[real_div; REAL_INV_MUL] THEN REWRITE_TAC[ REAL_ARITH
       `x * inv(&2) * inv y * z = (inv(&2) * z) * x / y`] THEN
      MATCH_MP_TAC POSYNOMIAL_CMUL THEN
      ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH
       `&0 < inv(&2) * x <=> &0 < x`] THEN
      MATCH_MP_TAC POSYNOMIAL_VDIV THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN EXISTS_TAC `tau:num->real->real` THEN
    ASM_REWRITE_TAC[REAL_ADD_SUB] THEN CONJ_TAC THENL
     [EXPAND_TAC "PSI" THEN REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_DIV2_EQ;
                 REAL_ARITH `&0 < b ==> abs b = b`] THEN
    X_GEN_TAC `i:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1 / &2`; `&1`]) THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `sqrt X`]) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LE_TRANS]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RSQRT; MATCH_MP_TAC REAL_LE_LSQRT] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Automatically instantiate the theorems and derive error bounds.           *)
(*                                                                           *)
(* th = theorem to instantiate (BOUND_THEOREM_DIV or BOUND_THEOREM_SQRT)     *)
(* beta, sigma, omega = HOL term instantiations for corresponding parameters *)
(* n = number of iterations: result will provide bounds for H_0, ..., H_n    *)
(* d = number of fraction digits in resulting digit bounds                   *)
(* ------------------------------------------------------------------------- *)

let BOUNDS_INSTATIATION =
  let pth = prove
     (`x <= a / b ==> &0 <= b ==> !a'. a <= a' ==> x <= a' / b`,
      REPEAT STRIP_TAC THEN TRANS_TAC REAL_LE_TRANS `a / b:real` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[real_div] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ]) in
  let rec calc rews (thb,ths) n =
    if n = 0 then [thb] else
    let oths = calc rews (thb,ths) (n - 1) in
    let th1 = CONV_RULE NUM_REDUCE_CONV (SPEC(mk_small_numeral(n - 1)) ths) in
    let th2 = GEN_REWRITE_RULE TOP_DEPTH_CONV (hd oths::rews) th1 in
    let th3 = CONV_RULE REAL_RAT_REDUCE_CONV th2 in
    th3::oths in
  fun th beta sigma omega n d ->
    let ith = BETA_RULE (SPECL [beta; sigma; omega] th) in
    let avs,itm = strip_forall(concl ith) in
    let hth = ASSUME (rand(lhand itm)) in
    let eth = MP (SPECL avs ith) (CONJ (REAL_ARITH(lhand(lhand itm))) hth) in
    let ev,ebod = dest_exists(concl eth) in
    let [th0;th1;bth] = CONJUNCTS(ASSUME ebod) in
    let (th_b,th_s) =
      let hths = CONJUNCTS hth in
      el (if th = BOUND_THEOREM_DIV then 6 else 4) hths,
      el (if th = BOUND_THEOREM_DIV then 11 else 9) hths in
    let bths = calc [] (th_b,th_s) n in
    let tths_lo =
      calc bths (SPEC (if th = BOUND_THEOREM_DIV then `&1 / &4` else `&1 / &2`)
                 th0,
            SPEC (if th = BOUND_THEOREM_DIV then `&1 / &4` else `&1 / &2`)
                 (GEN_REWRITE_RULE I [SWAP_FORALL_THM] th1)) n
    and tths_hi =
      calc bths (SPEC `&1:real` th0,
            SPEC `&1:real` (GEN_REWRITE_RULE I [SWAP_FORALL_THM] th1)) n in
    let aths = map
     (CONV_RULE REAL_RAT_REDUCE_CONV o
      REWRITE_RULE(tths_lo@tths_hi) o
      C SPEC bth o mk_small_numeral) (0--n) in
    let weaken th =
      let th1 = MATCH_MP pth th in
      let th2 = GEN_REWRITE_CONV RAND_CONV bths (lhand(concl th1)) in
      let th3 = CONV_RULE(RAND_CONV REAL_RAT_REDUCE_CONV) th2 in
      let th4 = MP th1 (EQT_ELIM th3) in
      let rr = rat_of_term(lhand(lhand(snd(dest_forall(concl th4))))) in
      let yy = pow10 d in
      let xx = ceiling_num(yy */ rr) in
      let th5 = SPECL [mk_numeral xx; mk_numeral yy] DECIMAL in
      let th6 = SPEC (lhand(concl th5)) th4 in
      MP th6 (EQT_ELIM(REAL_RAT_REDUCE_CONV(lhand(concl th6)))) in
    let ath = end_itlist CONJ (map weaken aths) in
    GENL avs (DISCH_ALL (CHOOSE(ev,eth) ath));;

(* ------------------------------------------------------------------------- *)
(* A slightly larger / more complicated example as a stress-test.            *)
(* ------------------------------------------------------------------------- *)

BOUNDS_INSTATIATION BOUND_THEOREM_SQRT
 `(\i. if i = 2 then &32 else if i = 5 then &64 else &128):num->real`
 `inv(&2 pow 8):real`
 `(\i. if i = 0 then &1 / &2 else &9 / &16):num->real`
 7 6;;

(* ------------------------------------------------------------------------- *)
(* The actual examples in the table.                                         *)
(* ------------------------------------------------------------------------- *)

let TABLE_PART_1 = BOUNDS_INSTATIATION BOUND_THEOREM_DIV
 `(\i. &128):num->real`
 `inv(&2 pow 9):real`
 `(\i. &5 / &8):num->real`
 4 4;;

let TABLE_PART_2 = BOUNDS_INSTATIATION BOUND_THEOREM_DIV
 `(\i. if i = 2 then &32 else &128):num->real`
 `inv(&2 pow 9):real`
 `(\i. &5 / &8):num->real`
 4 4;;

let TABLE_PART_3 = BOUNDS_INSTATIATION BOUND_THEOREM_SQRT
 `(\i. &128):num->real`
 `inv(&2 pow 9):real`
 `(\i. &5 / &8):num->real`
 4 4;;

let TABLE_PART_4 = BOUNDS_INSTATIATION BOUND_THEOREM_SQRT
 `(\i. if i = 2 then &32 else &128):num->real`
 `inv(&2 pow 9):real`
 `(\i. &5 / &8):num->real`
 4 4;;
