(* ========================================================================= *)
(* Degrees and heights at a point with m extra algebraic coordinates.        *)
(*                                                                           *)
(* Purpose: besides theta 1, ..., theta n (degrees d r, heights H r) the     *)
(* point theta has the coordinates theta r, r IN n + 1..n + m, of degrees    *)
(* dx r <= Dx and heights <= B. On the whole range 1..n + m the merged       *)
(* degrees and heights are dt r = (if r <= n then d r else dx r) and         *)
(* Ht r = (if r <= n then H r else B). With E = nsum(n + 1..n + m) e,        *)
(* Dm = nproduct(1..n) d Dx^m and                                            *)
(*   S = sum(1..n) e r log((d r + 1) H r^3) + E (log(Dx + 1) + 3 log B),     *)
(* BAKER_EXTRA_BOUNDS gives, for integer polynomials g j (j <= n) in the     *)
(* n + m variables with exponents e r and coefficient sum G0:                *)
(*   - nproduct(1..n + m) dt <= Dm;                                          *)
(*   - norm(g j theta) <= G0 prod(1..n) (1 + d r H r)^e r ((1 + Dx) B)^E;    *)
(*   - exp(--(Dm (log Dm + log G0 + S))) <= norm(g n theta) when g n theta   *)
(*     is nonzero (the Liouville bound with Dm and S in place of the exact   *)
(*     degree product and height sum);                                       *)
(*   - sum(1..n + m) e r log((dt r + 1) Ht r^3) <= S.                        *)
(*                                                                           *)
(* Main results: BAKER_EXTRA_BOUNDS; its parts BAKER_EXTRA_MERGE,            *)
(*   INTPOLY_LIOUVILLE_EXP_MONO, LIOUVILLE_EXP_ENLARGE.                      *)
(*                                                                           *)
(* Uses: Library/products.ml (REAL_POW_NSUM), Baker/intpoly.ml               *)
(*   (INTPOLY_BOUND), Baker/liouville_inequality.ml                          *)
(*   (INTEGER_POLY_ROOT_BOUND, INTPOLY_LIOUVILLE), Baker/lemmas.ml           *)
(*   (REAL_LE_1_MUL), Baker/bounds.ml (LIOUVILLE_EXP_LOWER).                 *)
(* ========================================================================= *)

needs "Baker/bounds.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Splitting products and sums over 1..n + m at n.                           *)
(* ------------------------------------------------------------------------- *)

let BAKER_EXTRA_NPRODUCT_LE = prove
 (`!n m (d:num->num) (dx:num->num) Dx.
        (!r. r IN (n + 1)..(n + m) ==> dx r <= Dx)
        ==> nproduct (1..(n + m)) (\r. if r <= n then d r else dx r) <=
            nproduct(1..n) d * Dx EXP m`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\r. if r <= n then (d:num->num) r else dx r`;
                 `1`; `n:num`; `m:num`] NPRODUCT_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN MATCH_MP_TAC NPRODUCT_EQ_NUMSEG THEN
    SIMP_TAC[];
    TRANS_TAC LE_TRANS `nproduct((n + 1)..(n + m)) (\r. Dx)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE `n + 1 <= i ==> ~(i <= n)`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
      REWRITE_TAC[NPRODUCT_CONST_NUMSEG] THEN MATCH_MP_TAC EQ_IMP_LE THEN
      AP_TERM_TAC THEN ARITH_TAC]]);;

let PRODUCT_POW_COND_SPLIT = prove
 (`!n m (f:num->real) c (e:num->num).
        product(1..(n + m)) (\r. (if r <= n then f r else c) pow e r) =
        product(1..n) (\r. f r pow e r) * c pow (nsum((n + 1)..(n + m)) e)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`\r. (if r <= n then (f:num->real) r else c) pow
                      (e:num->num) r`;
                 `1`; `n:num`; `m:num`] PRODUCT_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN SIMP_TAC[];
    SIMP_TAC[REAL_POW_NSUM; FINITE_NUMSEG] THEN
    MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `n + 1 <= i ==> ~(i <= n)`]]);;

let BAKER_EXTRA_LOGSUM_LE = prove
 (`!n m (d:num->num) (dx:num->num) (H:num->real) (e:num->num) Dx B.
        &0 < B /\ (!r. r IN (n + 1)..(n + m) ==> dx r <= Dx)
        ==> sum(1..(n + m))
              (\r. &(e r) * log(&((if r <= n then d r else dx r) + 1) *
                                (if r <= n then H r else B) pow 3))
            <= sum(1..n) (\r. &(e r) * log(&(d r + 1) * H r pow 3)) +
               &(nsum((n + 1)..(n + m)) e) * (log(&Dx + &1) + &3 * log B)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\r. &((e:num->num) r) *
         log(&((if r <= n then (d:num->num) r else dx r) + 1) *
             (if r <= n then (H:num->real) r else B) pow 3)`;
    `1`; `n:num`; `m:num`] SUM_ADD_SPLIT) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n + 1`] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `x = x' /\ y <= y' ==> x + y <= x' + y':real`) THEN
  CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[ARITH_RULE `n + 1 <= i ==> ~(i <= n)`] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
  SUBGOAL_THEN `(dx:num->num) i <= Dx` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT; REAL_OF_NUM_LT;
               ARITH_RULE `0 < n + 1`] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> x + z <= y + z:real`) THEN
  MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The Liouville lower bound in exp form, with an upper bound D for the      *)
(* degree product and an upper bound S for the height sum.                   *)
(* ------------------------------------------------------------------------- *)

let LIOUVILLE_EXP_ENLARGE = prove
 (`!D0 D b S0 S.
        1 <= D0 /\ D0 <= D /\ &1 <= b /\ &0 <= S0 /\ S0 <= S
        ==> exp(--(&D * (log(&D) + log b + S))) <=
            exp(--(&D0 * (log(&D0) + log b + S0)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `&1 <= (&D0:real) /\ (&D0:real) <= &D` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log(&D0) /\ log(&D0) <= log(&D) /\ &0 <= log b`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC);;

let INTPOLY_LIOUVILLE_EXP_MONO = prove
 (`!v nn b g (theta:num->complex) (a:num->num->real) d h D S.
        FINITE v /\ intpoly v nn b g /\ &1 <= b /\
        (!r. r IN v
             ==> 1 <= d r /\ &1 <= h r /\
                 (!j. integer(a r j) /\ abs(a r j) <= h r) /\
                 ~(a r (d r) = &0) /\
                 vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
        nproduct v d <= D /\
        sum v (\r. &(nn r) * log(&(d r + 1) * h r pow 3)) <= S /\
        ~(g theta = Cx(&0))
        ==> exp(--(&D * (log(&D) + log b + S))) <= norm(g theta)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`v:num->bool`; `nn:num->num`; `b:real`;
                `g:(num->complex)->complex`; `theta:num->complex`;
                `a:num->num->real`; `d:num->num`; `h:num->real`]
         INTPOLY_LIOUVILLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y <= z ==> x <= z:real`) THEN
  TRANS_TAC REAL_LE_TRANS
   `exp(--(&(nproduct v (d:num->num)) *
           (log(&(nproduct v d)) + log b +
            sum (v:num->bool)
                (\r. &((nn:num->num) r) *
                     log(&(d r + 1) * (h:num->real) r pow 3)))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC LIOUVILLE_EXP_ENLARGE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `1 <= x <=> 0 < x`] THEN
      MATCH_MP_TAC NPRODUCT_POS_LT THEN
      ASM_MESON_TAC[ARITH_RULE `1 <= x ==> 0 < x`];
      MATCH_MP_TAC SUM_POS_LE THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_LE_1_MUL THEN
      ASM_SIMP_TAC[REAL_POW_LE_1; REAL_OF_NUM_LE] THEN ARITH_TAC];
    MATCH_MP_TAC LIOUVILLE_EXP_LOWER THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The merged family: degrees, heights, vanishing integer polynomials        *)
(* and root bounds of theta r for r IN 1..n + m.                             *)
(* ------------------------------------------------------------------------- *)

let BAKER_EXTRA_MERGE = prove
 (`!n m (a:num->num->real) (d:num->num) (H:num->real) Dx B
    (theta:num->complex) (dx:num->num) (ax:num->num->real).
     &1 <= B /\
     (!r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
     (!r. r IN (n + 1)..(n + m)
          ==> 1 <= dx r /\ dx r <= Dx /\
              (!j. integer(ax r j) /\ abs(ax r j) <= B) /\
              ~(ax r (dx r) = &0) /\
              vsum(0..dx r) (\j. Cx(ax r j) * theta r pow j) = Cx(&0))
     ==> (!r. r IN 1..(n + m)
              ==> 1 <= (if r <= n then d r else dx r) /\
                  &1 <= (if r <= n then H r else B) /\
                  (!j. integer((if r <= n then a r else ax r) j) /\
                       abs((if r <= n then a r else ax r) j) <=
                       (if r <= n then H r else B)) /\
                  ~((if r <= n then a r else ax r)
                    (if r <= n then d r else dx r) = &0) /\
                  vsum(0..(if r <= n then d r else dx r))
                    (\j. Cx((if r <= n then a r else ax r) j) *
                         theta r pow j) = Cx(&0)) /\
         (!r. r IN 1..(n + m)
              ==> norm(theta r) <=
                  (if r <= n then &1 + &(d r) * H r else (&1 + &Dx) * B) /\
                  &1 <=
                  (if r <= n then &1 + &(d r) * H r else (&1 + &Dx) * B)) /\
         (!r. r IN (n + 1)..(n + m) ==> dx r <= Dx)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "lo") (LABEL_TAC "hi"))) THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THENL
   [ASM_CASES_TAC `r <= n` THEN ASM_REWRITE_TAC[] THENL
     [REMOVE_THEN "lo" (MP_TAC o SPEC `r:num`);
      REMOVE_THEN "hi" (MP_TAC o SPEC `r:num`)] THEN
    (ANTS_TAC THENL
      [UNDISCH_TAC `r IN 1..(n + m)` THEN REWRITE_TAC[IN_NUMSEG] THEN
       ASM_ARITH_TAC;
       STRIP_TAC THEN ASM_REWRITE_TAC[]]);
    ASM_CASES_TAC `r <= n` THEN ASM_REWRITE_TAC[] THENL
     [REMOVE_THEN "lo" (MP_TAC o SPEC `r:num`);
      REMOVE_THEN "hi" (MP_TAC o SPEC `r:num`)] THEN
    (ANTS_TAC THENL
      [UNDISCH_TAC `r IN 1..(n + m)` THEN REWRITE_TAC[IN_NUMSEG] THEN
       ASM_ARITH_TAC;
       STRIP_TAC]) THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC INTEGER_POLY_ROOT_BOUND THEN
        EXISTS_TAC `(a:num->num->real) r` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN
       `norm((theta:num->complex) r) <= &1 + &((dx:num->num) r) * B`
      ASSUME_TAC THENL
       [MATCH_MP_TAC INTEGER_POLY_ROOT_BOUND THEN
        EXISTS_TAC `(ax:num->num->real) r` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&((dx:num->num) r) * B <= &Dx * B /\ &0 <= &Dx * B`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
          ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    REMOVE_THEN "hi" (MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The bounds for the point theta with m extra coordinates.                  *)
(* ------------------------------------------------------------------------- *)

let BAKER_EXTRA_BOUNDS = prove
 (`!n m (a:num->num->real) (d:num->num) (H:num->real) (e:num->num) G0 Dx
    B (theta:num->complex) (g:num->(num->complex)->complex)
    (dx:num->num) (ax:num->num->real).
     1 <= n /\ 1 <= Dx /\ &1 <= G0 /\ &2 <= B /\
     (!r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
     (!r. r IN (n + 1)..(n + m)
          ==> 1 <= dx r /\ dx r <= Dx /\
              (!j. integer(ax r j) /\ abs(ax r j) <= B) /\
              ~(ax r (dx r) = &0) /\
              vsum(0..dx r) (\j. Cx(ax r j) * theta r pow j) = Cx(&0)) /\
     (!j. j <= n ==> intpoly (1..(n + m)) e G0 (g j)) /\
     ~(g n theta = Cx(&0))
     ==> nproduct (1..(n + m)) (\r. if r <= n then d r else dx r) <=
         nproduct(1..n) d * Dx EXP m /\
         (!j. j <= n
              ==> norm(g j theta) <=
                  G0 * product(1..n) (\r. (&1 + &(d r) * H r) pow e r) *
                  ((&1 + &Dx) * B) pow (nsum((n + 1)..(n + m)) e)) /\
         exp(--(&(nproduct(1..n) d * Dx EXP m) *
                (log(&(nproduct(1..n) d * Dx EXP m)) + log G0 +
                 sum(1..n) (\r. &(e r) * log(&(d r + 1) * H r pow 3)) +
                 &(nsum((n + 1)..(n + m)) e) * (log(&Dx + &1) + &3 * log B))))
         <= norm(g n theta) /\
         sum(1..(n + m))
            (\r. &(e r) * log(&((if r <= n then d r else dx r) + 1) *
                              (if r <= n then H r else B) pow 3))
         <= sum(1..n) (\r. &(e r) * log(&(d r + 1) * H r pow 3)) +
            &(nsum((n + 1)..(n + m)) e) * (log(&Dx + &1) + &3 * log B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `m:num`; `a:num->num->real`; `d:num->num`;
                `H:num->real`; `Dx:num`; `B:real`; `theta:num->complex`;
                `dx:num->num`; `ax:num->num->real`] BAKER_EXTRA_MERGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`n:num`; `m:num`; `d:num->num`; `dx:num->num`; `Dx:num`]
    BAKER_EXTRA_NPRODUCT_LE) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`n:num`; `m:num`; `d:num->num`; `dx:num->num`; `H:num->real`;
                `e:num->num`; `Dx:num`; `B:real`] BAKER_EXTRA_LOGSUM_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBST1_TAC(SYM(BETA_RULE(SPECL
     [`n:num`; `m:num`; `\r. &1 + &((d:num->num) r) * (H:num->real) r`;
      `(&1 + &Dx) * (B:real)`; `e:num->num`] PRODUCT_POW_COND_SPLIT))) THEN
    MATCH_MP_TAC(BETA_RULE(SPECL
     [`1..(n + m)`; `e:num->num`; `G0:real`;
      `(g:num->(num->complex)->complex) j`; `theta:num->complex`;
      `\r. if r <= n then &1 + &((d:num->num) r) * (H:num->real) r
           else (&1 + &Dx) * (B:real)`] INTPOLY_BOUND)) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC(BETA_RULE(SPECL
     [`1..(n + m)`; `e:num->num`; `G0:real`;
      `(g:num->(num->complex)->complex) n`; `theta:num->complex`;
      `\r. if r <= n then (a:num->num->real) r else ax r`;
      `\r. if r <= n then (d:num->num) r else dx r`;
      `\r. if r <= n then (H:num->real) r else B`;
      `nproduct(1..n) (d:num->num) * Dx EXP m`;
      `sum(1..n) (\r. &((e:num->num) r) *
                      log(&((d:num->num) r + 1) * (H:num->real) r pow 3)) +
       &(nsum((n + 1)..(n + m)) e) * (log(&Dx + &1) + &3 * log B)`]
     INTPOLY_LIOUVILLE_EXP_MONO)) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL];
    FIRST_ASSUM ACCEPT_TAC]);;
