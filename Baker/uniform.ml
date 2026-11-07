(* ========================================================================= *)
(* Uniform lower bounds for arbitrary (possibly dependent) logarithms.       *)
(*                                                                           *)
(* Purpose: lower bounds for linear forms in logarithms of algebraic numbers *)
(* of bounded size, uniform in the data and without any independence         *)
(* hypothesis on the logarithms: the uniform core for algebraic              *)
(* coefficients BAKER_CORE_UNIFORM_ALGCOEFF (the base of the uniform bound   *)
(* BAKER_UNIFORM_ALGCOEFF of Baker/sharp_uniform.ml, hence of the two        *)
(* descents of Sharpening I: Baker, Acta Arith. 21 (1972) 117-129, and its   *)
(* version with algebraic coefficients, Baker 1973), its integer case        *)
(* BAKER_CORE_UNIFORM_INTEGER, and the uniform bounds BAKER_UNIFORM_INTEGER  *)
(* and BAKER_UNIFORM_RATIONAL for integer coefficients; this file is also    *)
(* part of the core loader Baker/make_core.ml.                               *)
(*                                                                           *)
(* sharpc_coefdata n bb ab db Hb: the coefficients bb r (r = 1..n) are roots *)
(* of the integer polynomials ab r of degree db r >= 1 with coefficients of  *)
(* absolute value at most Hb (the classical height data of the coefficients  *)
(* of a linear form). baker_logdata n lg a d H Mb Dmax: cexp(lg r) (r =      *)
(* 1..n) are roots of the integer polynomials a r of degree d r and height   *)
(* H r, the degree product is <= Dmax, each lg r is 0 or >= exp(-Mb) in      *)
(* size, sum |lg r| <= Mb and sum log((d r + 1) H r^3) <= Mb; the data are   *)
(* invariant under permutations of 1..n and pass to 1..n-1.                  *)
(*                                                                           *)
(* Main results:                                                             *)
(*  - BAKER_CORE_UNIFORM_ALGCOEFF: for fixed N, Dmax and Dx there are c,     *)
(*    kappa, cr, kr such that for all data baker_logdata N lg a d H Mb Dmax  *)
(*    without a small integer relation sum cc r lg r = 0 (|cc r| <= max 1    *)
(*    (cr Mb^kr), not all 0) and all coefficients of degree at most Dx and   *)
(*    height at most B >= 2, Lambda = bb 1 lg 1 + ... + bb N lg N = 0 or     *)
(*    |Lambda| >= exp(-(c Mb^kappa log B)): BAKER_CORE_UNIFORM of            *)
(*    Baker/explicit.ml with the coefficients as N extra algebraic           *)
(*    variables, after a transposition that puts a nonzero coefficient last. *)
(*  - BAKER_CORE_UNIFORM_INTEGER: its case of integer coefficients, which    *)
(*    are coefficient data of degree 1 and height B                          *)
(*    (SHARPC_COEFDATA_INTEGER: b r is the root of X - b r).                 *)
(*  - BAKER_UNIFORM_INTEGER: the same bound for integer coefficients without *)
(*    the relation hypothesis, by induction on n: a small relation           *)
(*    eliminates one logarithm (SHARPC_VSUM_ELIMINATE_LAST, for complex      *)
(*    coefficients bb r, also used by Baker/sharp_uniform.ml;                *)
(*    RELATION_ABSORB), else the core applies.                               *)
(*  - BAKER_UNIFORM_RATIONAL: the case of positive rationals u r / v r with  *)
(*    u r, v r <= exp(g0) and real logarithms: |sum b r log(u r / v r)| >=   *)
(*    exp(-(c g0^kappa log B)) unless the sum is 0; LOG_RATIO_LOWER and      *)
(*    LOG_RATIO_UPPER.                                                       *)
(*                                                                           *)
(* Uses: Baker/explicit.ml (BAKER_CORE_UNIFORM), Baker/intpoly.ml            *)
(* (INTPOLY_CONST, INTPOLY_VAR), Baker/estimates.ml (LOG_LE_SELF),           *)
(* Baker/lemmas.ml (LOG_2_LE_1, REAL_LE_1_MUL, CEXP_LOG_RATIO);              *)
(* Library/permutations.ml (swap, PERMUTES_SWAP, SWAP_IDEMPOTENT).           *)
(* ========================================================================= *)

needs "Baker/explicit.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The classical height data of the coefficients of a linear form; integer   *)
(* coefficients are such data of degree 1.                                   *)
(* ------------------------------------------------------------------------- *)

let sharpc_coefdata = new_definition
 `sharpc_coefdata n (bb:num->complex) (ab:num->num->real) (db:num->num)
                  (Hb:real) <=>
    !r. r IN 1..n
        ==> 1 <= db r /\ (!j. integer(ab r j) /\ abs(ab r j) <= Hb) /\
            ~(ab r (db r) = &0) /\
            vsum(0..db r) (\j. Cx(ab r j) * bb r pow j) = Cx(&0)`;;

let SHARPC_COEFDATA_INTEGER = prove
 (`!n (b:num->real) B.
        &1 <= B /\ (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= B)
        ==> sharpc_coefdata n (\r. Cx(b r))
              (\r j. if j = 0 then --(b r) else if j = 1 then &1 else &0)
              (\r. 1) B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[sharpc_coefdata] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN REWRITE_TAC[LE_REFL; ARITH_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[INTEGER_NEG; INTEGER_CLOSED; REAL_ABS_NEG; REAL_ABS_NUM] THEN
    ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[ONE] THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; LE_0; NOT_SUC; complex_pow] THEN
    REWRITE_TAC[GSYM ONE; CX_NEG] THEN CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Size data of a family of logarithms, invariant under permutations.        *)
(* ------------------------------------------------------------------------- *)

let baker_logdata = new_definition
 `baker_logdata n (lg:num->complex) (a:num->num->real) (d:num->num)
                (H:num->real) Mb Dmax <=>
    nproduct(1..n) d <= Dmax /\
    (!r. r IN 1..n
         ==> 1 <= d r /\ &1 <= H r /\
             (!j. integer(a r j) /\ abs(a r j) <= H r) /\
             ~(a r (d r) = &0) /\
             vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0) /\
             (lg r = Cx(&0) \/ exp(--Mb) <= norm(lg r))) /\
    sum(1..n) (\r. norm(lg r)) <= Mb /\
    sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= Mb`;;

let NPRODUCT_PERMUTE = prove
 (`!(f:A->num) p s. p permutes s ==> nproduct s f = nproduct s (f o p)`,
  REWRITE_TAC[nproduct] THEN MATCH_MP_TAC ITERATE_PERMUTE THEN
  REWRITE_TAC[MONOIDAL_MUL]);;

let VSUM_PERMUTE = prove
 (`!f:A->real^N p s. p permutes s ==> vsum s f = vsum s (f o p)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_BIJECTION THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP PERMUTES_IN_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:A` o CONJUNCT2 o
    GEN_REWRITE_RULE I [permutes]) THEN
  REWRITE_TAC[EXISTS_UNIQUE] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_MESON_TAC[]);;

let BAKER_LOGDATA_PERMUTES = prove
 (`!n lg a d H Mb Dmax p.
     p permutes 1..n /\ baker_logdata n lg a d H Mb Dmax
     ==> baker_logdata n (lg o p) (a o p) (d o p) (H o p) Mb Dmax`,
  REPEAT GEN_TAC THEN REWRITE_TAC[baker_logdata] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`d:num->num`; `p:num->num`; `1..n`] NPRODUCT_PERMUTE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    MP_TAC(ISPECL [`\r. norm((lg:num->complex) r)`; `p:num->num`; `1..n`]
                  SUM_PERMUTE) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`\r. log(&((d:num->num) r + 1) * (H:num->real) r pow 3)`;
                   `p:num->num`; `1..n`] SUM_PERMUTE) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[]]);;

let BAKER_LOGDATA_RESTRICT = prove
 (`!n lg a d H Mb Dmax.
     baker_logdata (SUC n) lg a d H Mb Dmax
     ==> baker_logdata n lg a d H Mb Dmax`,
  REPEAT GEN_TAC THEN REWRITE_TAC[baker_logdata] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> r IN 1..SUC n` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `SUC n` o check (fun th ->
    is_forall(concl th) && free_in `a:num->num->real` (concl th))) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)] THEN
  REPEAT CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `nproduct(1..SUC n) d` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NPRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `x = x * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ASM_MESON_TAC[];
    TRANS_TAC REAL_LE_TRANS `sum(1..SUC n) (\r. norm((lg:num->complex) r))` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[REAL_LE_ADDR; NORM_POS_LE];
    TRANS_TAC REAL_LE_TRANS
     `sum(1..SUC n)
        (\r. log(&((d:num->num) r + 1) * (H:num->real) r pow 3))` THEN
    ASM_REWRITE_TAC[SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    REWRITE_TAC[REAL_LE_ADDR] THEN MATCH_MP_TAC LOG_POS THEN
    MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Bookkeeping of the exponents.                                             *)
(* ------------------------------------------------------------------------- *)

let EXP_BOUND_MONO = prove
 (`!c c' k k' Mb lb x.
     c <= c' /\ &0 <= c' /\ k <= k' /\ &1 <= Mb /\ &0 <= lb /\
     exp(--(c * Mb pow k * lb)) <= x
     ==> exp(--(c' * Mb pow k' * lb)) <= x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REAL_ARITH `(a:real) <= x ==> b <= a ==> b <= x`)) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `&1 <= Mb pow k /\ Mb pow k <= Mb pow k'` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `&0 <= c` THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= --c * Mb pow k /\ &0 <= c' * Mb pow k'` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;

let RELATION_ABSORB = prove
 (`!c1 k1 X0 kr Mb B X x.
     &0 <= c1 /\ &1 <= X0 /\ &1 <= Mb /\ &2 <= B /\ &1 <= X /\
     X <= X0 * Mb pow kr /\
     exp(--(c1 * Mb pow k1 * log(&2 * X * B))) <= X * x
     ==> exp(--(((c1 + &1) * (&2 + &2 * log X0 + &2 * &kr)) *
                Mb pow (k1 + 1) * log B)) <= x`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K3 = &2 + &2 * log X0 + &2 * &kr` THEN
  SUBGOAL_THEN `&1 / &2 <= log B /\ log(&2) <= log B` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `(a:real) <= b /\ b <= c ==> a <= c /\ b <= c`) THEN
    REWRITE_TAC[CONJUNCT1 LOG_2_BOUNDS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log X0 /\ &0 <= log X` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `log X <= log X0 + &kr * Mb` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `log(X0 * Mb pow kr)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < X0 /\ &0 < Mb pow kr` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_POW_LT THEN
                      ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_ARITH `&1 <= (x:real) ==> &0 < x`] THEN
    REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_LE_SELF THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2 * X * B) = log(&2) + log X + log B` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `&0 < X /\ &0 < B` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_MUL; REAL_LT_MUL; REAL_ARITH `&0 < &2:real`];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) + log X + log B <= K3 * Mb * log B` ASSUME_TAC THENL
   [SUBGOAL_THEN `log B <= Mb * log B /\ log X0 <= log X0 * (&2 * Mb * log B) /\
                  &kr * Mb <= (&kr * Mb) * (&2 * log B)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `log B <= Mb * log B` MP_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    EXPAND_TAC "K3" THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`log B <= Mb * log B`; `log X0 <= log X0 * (&2 * Mb * log B)`;
      `&kr * Mb <= (&kr * Mb) * (&2 * log B)`; `log X <= log X0 + &kr * Mb`;
      `log(&2) <= log B`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= Mb pow k1 /\ Mb pow (k1 + 1) = Mb pow k1 * Mb`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
                    REWRITE_TAC[REAL_POW_ADD; REAL_POW_1]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K3 * Mb * log B` ASSUME_TAC THENL
   [MP_TAC(CONJUNCT1 LOG_2_BOUNDS) THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`log(&2) + log X + log B <= K3 * Mb * log B`; `&0 <= log X`;
      `&1 / &2 <= log B`; `log(&2) <= log B`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c1 * Mb pow k1 * (log(&2) + log X + log B) + log X <=
    ((c1 + &1) * K3) * Mb pow (k1 + 1) * log B`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `c1 * Mb pow k1 * (log(&2) + log X + log B) <=
      c1 * Mb pow k1 * (K3 * Mb * log B) /\
      log X <= Mb pow k1 * (K3 * Mb * log B)`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        TRANS_TAC REAL_LE_TRANS `K3 * Mb * log B` THEN CONJ_TAC THENL
         [MP_TAC(CONJUNCT1 LOG_2_BOUNDS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `exp(--(c1 * Mb pow k1 * (log(&2) + log X + log B) + log X))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--(c1 * Mb pow k1 * (log(&2) + log X + log B) + log X)) =
    exp(--(c1 * Mb pow k1 * (log(&2) + log X + log B))) / X`
  SUBST1_TAC THENL
   [REWRITE_TAC[REAL_NEG_ADD; REAL_EXP_ADD; real_div] THEN AP_TERM_TAC THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN AP_TERM_TAC THEN MATCH_MP_TAC EXP_LOG THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= (x:real) ==> &0 < x`] THEN
  ASM_REAL_ARITH_TAC);;

let SHARPC_VSUM_ELIMINATE_LAST = prove
 (`!n (lg:num->complex) (bb:num->complex) (c:num->real).
     vsum(1..SUC n) (\r. Cx(c r) * lg r) = Cx(&0)
     ==> Cx(c(SUC n)) * vsum(1..SUC n) (\r. bb r * lg r) =
         vsum(1..n) (\r. (Cx(c(SUC n)) * bb r - Cx(c r) * bb(SUC n)) *
                         lg r)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `vsum(1..n) (\r. (Cx(c(SUC n)) * bb r - Cx(c r) * bb(SUC n)) *
                    (lg:num->complex) r) =
    vsum(1..n) (\r. Cx(c(SUC n)) * (bb r * lg r) -
                    bb(SUC n) * (Cx(c r) * lg r))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[VSUM_SUB; FINITE_NUMSEG; VSUM_COMPLEX_LMUL] THEN
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* The uniform core for algebraic coefficients without small integer         *)
(* relations: the coefficients become extra algebraic variables, a nonzero   *)
(* coefficient is moved to the last place by a transposition. Integer        *)
(* coefficients are the case of degree 1.                                    *)
(* ------------------------------------------------------------------------- *)

let BAKER_CORE_UNIFORM_ALGCOEFF = prove
 (`!N Dmax Dx.
     1 <= N /\ 1 <= Dmax /\ 1 <= Dx
     ==> ?c kappa cr kr.
           !Mb (lg:num->complex) (a:num->num->real) (d:num->num)
            (H:num->real) (bb:num->complex) (ab:num->num->real)
            (db:num->num) B.
             &1 <= Mb /\ &2 <= B /\ baker_logdata N lg a d H Mb Dmax /\
             sharpc_coefdata N bb ab db B /\
             (!r. r IN 1..N ==> db r <= Dx) /\
             ~(vsum(1..N) (\r. bb r * lg r) = Cx(&0)) /\
             (!cc. (!r. r IN 1..N
                        ==> integer(cc r) /\
                            abs(cc r) <= max (&1) (cr * Mb pow kr)) /\
                   vsum(1..N) (\r. Cx(cc r) * lg r) = Cx(&0)
                   ==> !r. r IN 1..N ==> cc r = &0)
             ==> exp(--(c * Mb pow kappa * log B)) <=
                 norm(vsum(1..N) (\r. bb r * lg r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `N:num`; `\r:num. 1`; `&1`; `Dx:num`; `Dmax:num`]
               BAKER_CORE_UNIFORM) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `kappa:num`
    (X_CHOOSE_THEN `cr:real` (X_CHOOSE_TAC `kr:num`)))) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `kappa:num`; `cr:real`; `kr:num`] THEN
  MAP_EVERY X_GEN_TAC [`Mb:real`; `lg:num->complex`; `a:num->num->real`;
                       `d:num->num`; `H:num->real`; `bb:num->complex`;
                       `ab:num->num->real`; `db:num->num`; `B:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN 1..N ==> ~((lg:num->complex) r = Cx(&0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:num` THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\r:num. if r = s then &1 else &0` o
      check (fun th -> is_forall(concl th) &&
                       type_of(fst(dest_forall(concl th))) = `:num->real`)) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [X_GEN_TAC `r:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
        REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
        REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN BETA_TAC THEN
        COND_CASES_TAC THEN
        ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]];
      DISCH_THEN(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t. t IN 1..N /\ ~((bb:num->complex) t = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC
     `~(vsum(1..N) (\r. (bb:num->complex) r * (lg:num->complex) r) =
        Cx(&0))` THEN
    REWRITE_TAC[] THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    BETA_TAC THEN
    SUBGOAL_THEN `(bb:num->complex) r = Cx(&0)`
     (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
    UNDISCH_TAC `r IN 1..N` THEN
    UNDISCH_TAC `~(?t. t IN 1..N /\ ~((bb:num->complex) t = Cx(&0)))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `p = swap(t:num,N)` THEN
  SUBGOAL_THEN `(p:num->num) permutes 1..N /\ p N = t /\ (!r. p(p r) = r)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_SWAP THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[swap] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN 1..N ==> (p:num->num) r IN 1..N` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_IN_IMAGE th]);
    ALL_TAC] THEN
  MP_TAC(SPECL [`N:num`; `lg:num->complex`; `a:num->num->real`;
                `d:num->num`; `H:num->real`; `Mb:real`; `Dmax:num`;
                `p:num->num`] BAKER_LOGDATA_PERMUTES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[baker_logdata; o_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum(1..N) (\r. (bb:num->complex) r * (lg:num->complex) r) =
    vsum(1..N) (\r. bb(p r) * lg(p r))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`\r. (bb:num->complex) r * (lg:num->complex) r`;
                   `p:num->num`; `1..N`] VSUM_PERMUTE) THEN
    ASM_REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`Mb:real`; `(lg:num->complex) o (p:num->num)`;
    `(a:num->num->real) o (p:num->num)`;
    `(d:num->num) o (p:num->num)`; `(H:num->real) o (p:num->num)`; `B:real`;
    `\r. if r <= N then cexp((lg:num->complex)(p r))
         else (bb:num->complex)(p(r - N))`;
    `\j (x:num->complex). if j = 0 then Cx(&0) else x(N + j)`;
    `\r. (db:num->num)((p:num->num)(r - N))`;
    `\r. (ab:num->num->real)((p:num->num)(r - N))`] o
    check (fun th -> is_forall(concl th) &&
                     can (find_term ((=) `kappa:num`)) (concl th))) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `b0:num->real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `\r. (b0:num->real)((p:num->num) r)` o
        check (fun th -> is_forall(concl th) &&
                     type_of(fst(dest_forall(concl th))) = `:num->real`)) THEN
      BETA_TAC THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `(p:num->num) r` o check (fun th ->
            is_forall(concl th) && free_in `b0:num->real` (concl th))) THEN
          ASM_SIMP_TAC[REAL_LE_MAX];
          MP_TAC(ISPECL
           [`\r. Cx((b0:num->real)((p:num->num) r)) * (lg:num->complex) r`;
            `p:num->num`; `1..N`] VSUM_PERMUTE) THEN
          ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN SUBST1_TAC THEN
          ASM_REWRITE_TAC[]];
        DISCH_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(p:num->num) r`) THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [SIMP_TAC[IN_NUMSEG]; ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(r <= N) /\ r - N IN 1..N` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(p:num->num)(r - N) IN 1..N` ASSUME_TAC THENL
       [MATCH_MP_TAC(ASSUME `!r. r IN 1..N ==> (p:num->num) r IN 1..N`) THEN
        FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP (ASSUME `!r. r IN 1..N ==> (db:num->num) r <= Dx`)
                      (ASSUME `(p:num->num)(r - N) IN 1..N`)) THEN
      MP_TAC(MATCH_MP (REWRITE_RULE[sharpc_coefdata]
                         (ASSUME `sharpc_coefdata N bb ab db B`))
                      (ASSUME `(p:num->num)(r - N) IN 1..N`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN ASM_CASES_TAC `j = 0` THEN
      ASM_REWRITE_TAC[] THENL
       [MATCH_MP_TAC INTPOLY_CONST THEN REWRITE_TAC[INTEGER_CLOSED] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC INTPOLY_VAR THEN
        REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_REFL; REAL_LE_REFL] THEN
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(N = 0) /\ ~(N + N <= N) /\ (N + N) - N = N`
    STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> e <= x ==> e <= y`) THEN
  AP_TERM_TAC THEN REWRITE_TAC[COMPLEX_ADD_LID] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0) /\ ~(N + r <= N) /\ (N + r) - N = r`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let BAKER_CORE_UNIFORM_INTEGER = prove
 (`!N Dmax.
     1 <= N /\ 1 <= Dmax
     ==> ?c kappa cr kr.
           !Mb (lg:num->complex) (a:num->num->real) (d:num->num)
            (H:num->real) (b:num->real) B.
             &1 <= Mb /\ &2 <= B /\ baker_logdata N lg a d H Mb Dmax /\
             (!r. r IN 1..N ==> integer(b r) /\ abs(b r) <= B) /\
             ~(vsum(1..N) (\r. Cx(b r) * lg r) = Cx(&0)) /\
             (!cc. (!r. r IN 1..N
                        ==> integer(cc r) /\
                            abs(cc r) <= max (&1) (cr * Mb pow kr)) /\
                   vsum(1..N) (\r. Cx(cc r) * lg r) = Cx(&0)
                   ==> !r. r IN 1..N ==> cc r = &0)
             ==> exp(--(c * Mb pow kappa * log B)) <=
                 norm(vsum(1..N) (\r. Cx(b r) * lg r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`N:num`; `Dmax:num`; `1`] BAKER_CORE_UNIFORM_ALGCOEFF) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `kappa:num`
   (X_CHOOSE_THEN `cr:real` (X_CHOOSE_TAC `kr:num`)))) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `kappa:num`; `cr:real`; `kr:num`] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`Mb:real`; `lg:num->complex`; `a:num->num->real`; `d:num->num`;
    `H:num->real`; `\r. Cx((b:num->real) r)`;
    `\r j. if j = 0 then --((b:num->real) r) else if j = 1 then &1 else &0`;
    `\r:num. 1`; `B:real`]) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SHARPC_COEFDATA_INTEGER THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The uniform bound for arbitrary (possibly dependent) logarithms and       *)
(* homogeneous integer forms, by induction on the number of logarithms: a    *)
(* small relation eliminates one logarithm (after a transposition), else the *)
(* uniform core applies.                                                     *)
(* ------------------------------------------------------------------------- *)

let BAKER_UNIFORM_INTEGER = prove
 (`!n Dmax.
     1 <= Dmax
     ==> ?c kappa.
           !Mb (lg:num->complex) (a:num->num->real) (d:num->num)
            (H:num->real) (b:num->real) B.
             &1 <= Mb /\ &2 <= B /\ baker_logdata n lg a d H Mb Dmax /\
             (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= B) /\
             ~(vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0))
             ==> exp(--(c * Mb pow kappa * log B)) <=
                 norm(vsum(1..n) (\r. Cx(b r) * lg r))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_EQ; VSUM_CLAUSES; COMPLEX_VEC_0];
    ALL_TAC] THEN
  X_GEN_TAC `Dmax:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Dmax:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_TAC `k1:num`)) THEN
  MP_TAC(SPECL [`SUC n`; `Dmax:num`] BAKER_CORE_UNIFORM_INTEGER) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `k2:num`
    (X_CHOOSE_THEN `cr:real` (X_CHOOSE_TAC `kr:num`)))) THEN
  EXISTS_TAC `max (max c2 (&0)) ((max c1 (&0) + &1) *
                (&2 + &2 * log(max (&1) cr) + &2 * &kr))` THEN
  EXISTS_TAC `MAX k2 (k1 + 1)` THEN
  MAP_EVERY X_GEN_TAC [`Mb:real`; `lg:num->complex`; `a:num->num->real`;
                       `d:num->num`; `H:num->real`; `b:num->real`;
                       `B:real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log B` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC
   `?cc:num->real.
      (!r. r IN 1..SUC n
           ==> integer(cc r) /\ abs(cc r) <= max (&1) (cr * Mb pow kr)) /\
      ~(!r. r IN 1..SUC n ==> cc r = &0) /\
      vsum(1..SUC n) (\r. Cx(cc r) * (lg:num->complex) r) = Cx(&0)`
  THENL
   [ALL_TAC;
    MATCH_MP_TAC EXP_BOUND_MONO THEN
    MAP_EVERY EXISTS_TAC [`c2:real`; `k2:num`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC; REAL_ARITH_TAC; ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `c2:real` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cc:num->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    is_neg(concl th) && is_forall(rand(concl th)))) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `X = max (&1) (cr * Mb pow kr)` THEN
  SUBGOAL_THEN `&1 <= X /\ X <= max (&1) cr * Mb pow kr` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBGOAL_THEN `&1 <= Mb pow kr` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_MAX_LE] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `p = swap(t:num,SUC n)` THEN
  SUBGOAL_THEN
   `(p:num->num) permutes 1..SUC n /\ p(SUC n) = t /\ (!r. p(p r) = r)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PERMUTES_SWAP THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
      ARITH_TAC;
      REWRITE_TAC[swap] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN 1..SUC n ==> (p:num->num) r IN 1..SUC n`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_IN_IMAGE th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `baker_logdata n ((lg:num->complex) o (p:num->num)) ((a:num->num->real) o p)
                  ((d:num->num) o p) ((H:num->real) o p) Mb Dmax`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_LOGDATA_RESTRICT THEN
    MATCH_MP_TAC BAKER_LOGDATA_PERMUTES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(1..SUC n) (\r. Cx((b:num->real) r) * (lg:num->complex) r) =
    vsum(1..SUC n) (\r. Cx(b((p:num->num) r)) * lg(p r)) /\
    vsum(1..SUC n) (\r. Cx((cc:num->real)(p r)) * lg(p r)) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\r. Cx((b:num->real) r) * (lg:num->complex) r`;
                     `p:num->num`; `1..SUC n`] VSUM_PERMUTE) THEN
      ASM_REWRITE_TAC[o_DEF];
      MP_TAC(ISPECL [`\r. Cx((cc:num->real) r) * (lg:num->complex) r`;
                     `p:num->num`; `1..SUC n`] VSUM_PERMUTE) THEN
      ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `\r. (lg:num->complex)((p:num->num) r)`;
                 `\r. Cx((b:num->real)((p:num->num) r))`;
                 `\r. (cc:num->real)((p:num->num) r)`]
                SHARPC_VSUM_ELIMINATE_LAST) THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`Mb:real`; `(lg:num->complex) o (p:num->num)`;
    `(a:num->num->real) o (p:num->num)`;
    `(d:num->num) o (p:num->num)`; `(H:num->real) o (p:num->num)`;
    `\r. (cc:num->real) t * b((p:num->num) r) - cc(p r) * b t`;
    `&2 * X * B`] o
    check (fun th -> is_forall(concl th) && free_in `c1:real` (concl th))) THEN
  ASM_REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `&1 <= X * B` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:num->num) r IN 1..SUC n` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `r IN 1..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN
       `integer((cc:num->real) t) /\ abs(cc t) <= X /\
        integer(cc((p:num->num) r)) /\ abs(cc(p r)) <= X /\
        integer((b:num->real) t) /\ abs(b t) <= B /\
        integer(b(p r)) /\ abs(b(p r)) <= B`
      STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`!r. r IN 1..SUC n ==> integer((cc:num->real) r) /\ abs(cc r) <= X`;
          `!r. r IN 1..SUC n ==> integer((b:num->real) r) /\ abs(b r) <= B`;
          `t IN 1..SUC n`; `(p:num->num) r IN 1..SUC n`] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL [ASM_SIMP_TAC[INTEGER_CLOSED]; ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x:real) <= X * B /\ abs(y) <= X * B
        ==> abs(x - y) <= &2 * X * B`) THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS];
      FIRST_ASSUM(fun th ->
        if is_eq(concl th) &&
           can (term_match [] `Cx(c:real) * (x:complex)`) (lhand(concl th))
        then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; DE_MORGAN_THM] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `norm(vsum(1..n) (\r. Cx((cc:num->real) t * b((p:num->num) r) -
                            cc(p r) * b t) * (lg:num->complex)(p r))) <=
    X * norm(vsum(1..SUC n) (\r. Cx(b r) * lg r))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_eq(concl th) &&
         can (term_match [] `Cx(c:real) * (x:complex)`) (lhand(concl th))
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[ASSUME
     `vsum(1..SUC n) (\r. Cx((b:num->real) r) * (lg:num->complex) r) =
      vsum(1..SUC n) (\r. Cx(b((p:num->num) r)) * lg(p r))`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EXP_BOUND_MONO THEN
  MAP_EVERY EXISTS_TAC
   [`(max c1 (&0) + &1) * (&2 + &2 * log(max (&1) cr) + &2 * &kr)`;
    `k1 + 1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC; ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RELATION_ABSORB THEN EXISTS_TAC `X:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EXP_BOUND_MONO THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `k1:num`] THEN
  ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN
    SUBGOAL_THEN `&1 <= X * B` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ASM_MESON_TAC[REAL_LE_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* The uniform bound for logarithms of positive rationals.                   *)
(* ------------------------------------------------------------------------- *)

let LOG_RATIO_LOWER = prove
 (`!u v. 1 <= u /\ 1 <= v /\ ~(u = v)
         ==> inv(&(MAX u v)) <= abs(log(&u / &v))`,
  SUBGOAL_THEN `!u v. 1 <= v /\ v < u ==> inv(&u) <= log(&u / &v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `&0 < &u /\ &0 < &v /\ &v + &1 <= &u` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `--log(&u / &v)` REAL_EXP_LE_X) THEN
    REWRITE_TAC[REAL_EXP_NEG] THEN
    SUBGOAL_THEN `exp(log(&u / &v)) = &u / &v` SUBST1_TAC THENL
     [MATCH_MP_TAC EXP_LOG THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    REWRITE_TAC[REAL_INV_DIV] THEN
    SUBGOAL_THEN `inv(&u) + &v / &u <= &1` MP_TAC THENL
     [SUBGOAL_THEN `inv(&u) + &v / &u = (&1 + &v) / &u` SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < &u` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ARITH_RULE `v < u \/ u < (v:num) \/ u = v`) THEN STRIP_TAC THENL
   [SUBGOAL_THEN `MAX u v = u` SUBST1_TAC THENL
     [REWRITE_TAC[MAX] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `log(&u / &v)` THEN ASM_SIMP_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC;
    ASM_ARITH_TAC] THEN
  SUBGOAL_THEN `MAX u v = v` SUBST1_TAC THENL
   [REWRITE_TAC[MAX] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&u / &v) = --log(&v / &u)` SUBST1_TAC THENL
   [SUBGOAL_THEN `&0 < &u /\ &0 < &v` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_DIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `log(&v / &u)` THEN ASM_SIMP_TAC[] THEN
  REAL_ARITH_TAC);;

let LOG_RATIO_UPPER = prove
 (`!u v. 1 <= u /\ 1 <= v ==> abs(log(&u / &v)) <= log(&(MAX u v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &u /\ &0 < &v` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_DIV] THEN
  SUBGOAL_THEN `&0 <= log(&u) /\ &0 <= log(&v) /\
                log(&u) <= log(&(MAX u v)) /\ log(&v) <= log(&(MAX u v))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC LOG_POS) THEN
    TRY(MATCH_MP_TAC LOG_MONO_LE_IMP) THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    REAL_ARITH_TAC]);;

let BAKER_LOGDATA_RATIONAL = prove
 (`!n (u:num->num) (v:num->num) g0.
     &1 <= g0 /\
     (!r. r IN 1..n
          ==> 1 <= u r /\ 1 <= v r /\ &(u r) <= exp g0 /\ &(v r) <= exp g0)
     ==> baker_logdata n (\r. Cx(log(&(u r) / &(v r))))
                         (\r j. if j = 0 then --(&(u r))
                                else if j = 1 then &(v r) else &0)
                         (\r. 1) (\r. &(MAX (u r) (v r)))
                         (&(5 * (n + 1)) * g0) 1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_logdata] THEN
  SUBGOAL_THEN
   `!r. r IN 1..n ==> log(&(MAX ((u:num->num) r) ((v:num->num) r))) <= g0`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBST1_TAC(SYM(SPEC `g0:real` LOG_EXP)) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN
    REWRITE_TAC[REAL_OF_NUM_LT; MAX] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &n * g0 /\ &n * g0 <= &(5 * (n + 1)) * g0 /\
                g0 <= &(5 * (n + 1)) * g0`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NPRODUCT_CONST_NUMSEG; EXP_ONE; LE_REFL];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `1 <= (u:num->num) r /\ 1 <= (v:num->num) r /\
                  &(u r) <= exp g0 /\ &(v r) <= exp g0`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[LE_REFL; ARITH_EQ] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      REWRITE_TAC[INTEGER_CLOSED; INTEGER_NEG; REAL_ABS_NEG; REAL_ABS_NUM;
                  REAL_OF_NUM_LE] THEN ARITH_TAC;
      REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; ADD_CLAUSES; VSUM_SING_NUMSEG] THEN
      ASM_SIMP_TAC[CEXP_LOG_RATIO; ARITH_EQ; complex_pow; COMPLEX_POW_1] THEN
      REWRITE_TAC[CX_NEG; CX_DIV] THEN
      SUBGOAL_THEN `~(Cx(&((v:num->num) r)) = Cx(&0))` MP_TAC THENL
       [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
        CONV_TAC COMPLEX_FIELD];
      ASM_CASES_TAC `(u:num->num) r = v r` THENL
       [DISJ1_TAC THEN ASM_REWRITE_TAC[CX_INJ] THEN
        SUBGOAL_THEN `~(&((v:num->num) r) = &0)` MP_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
          SIMP_TAC[REAL_DIV_REFL; LOG_1]];
        DISJ2_TAC THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
        TRANS_TAC REAL_LE_TRANS `inv(&(MAX ((u:num->num) r) (v r)))` THEN
        ASM_SIMP_TAC[LOG_RATIO_LOWER] THEN
        SUBGOAL_THEN `&0 < &(MAX ((u:num->num) r) (v r))` ASSUME_TAC THENL
         [REWRITE_TAC[REAL_OF_NUM_LT; MAX] THEN COND_CASES_TAC THEN
          ASM_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `inv(&(MAX ((u:num->num) r) (v r))) =
                      exp(--log(&(MAX (u r) (v r))))`
        SUBST1_TAC THENL
         [ASM_SIMP_TAC[REAL_EXP_NEG; EXP_LOG]; ALL_TAC] THEN
        REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
        TRANS_TAC REAL_LE_TRANS `g0:real` THEN ASM_SIMP_TAC[]]];
    TRANS_TAC REAL_LE_TRANS `&n * g0` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
     [ARITH_RULE `n = (n + 1) - 1`] THEN
    REWRITE_TAC[GSYM SUM_CONST_NUMSEG] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN
    TRANS_TAC REAL_LE_TRANS
     `log(&(MAX ((u:num->num) r) ((v:num->num) r)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_RATIO_UPPER THEN ASM_MESON_TAC[IN_NUMSEG];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG]];
    TRANS_TAC REAL_LE_TRANS `sum(1..n) (\r. &4 * g0)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      BETA_TAC THEN REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
      SUBGOAL_THEN `&0 < &(MAX ((u:num->num) r) ((v:num->num) r))`
      ASSUME_TAC THENL
       [SUBGOAL_THEN `1 <= (u:num->num) r` MP_TAC THENL
         [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
        REWRITE_TAC[REAL_OF_NUM_LT; MAX] THEN COND_CASES_TAC THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[LOG_MUL; LOG_POW; REAL_POW_LT;
                   REAL_ARITH `&0 < &2:real`] THEN
      SUBGOAL_THEN
       `log(&(MAX ((u:num->num) r) ((v:num->num) r))) <= g0`
      MP_TAC THENL [ASM_MESON_TAC[IN_NUMSEG]; ALL_TAC] THEN
      MP_TAC LOG_2_LE_1 THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC]]]);;

let BAKER_UNIFORM_RATIONAL = prove
 (`!n. ?c kappa.
     !(u:num->num) (v:num->num) (b:num->real) B g0.
       &1 <= g0 /\ &2 <= B /\
       (!r. r IN 1..n
            ==> 1 <= u r /\ 1 <= v r /\ &(u r) <= exp g0 /\ &(v r) <= exp g0) /\
       (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= B) /\
       ~(sum(1..n) (\r. b r * log(&(u r) / &(v r))) = &0)
       ==> exp(--(c * g0 pow kappa * log B)) <=
           abs(sum(1..n) (\r. b r * log(&(u r) / &(v r))))`,
  GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `1`] BAKER_UNIFORM_INTEGER) THEN
  REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_TAC `kappa:num`)) THEN
  EXISTS_TAC `c * &(5 * (n + 1)) pow kappa` THEN EXISTS_TAC `kappa:num` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`&(5 * (n + 1)) * g0`;
    `\r. Cx(log(&((u:num->num) r) / &((v:num->num) r)))`;
    `\r j. if j = 0 then --(&((u:num->num) r))
           else if j = 1 then &((v:num->num) r) else &0`;
    `\r:num. 1`;
    `\r. &(MAX ((u:num->num) r) ((v:num->num) r))`;
    `b:num->real`; `B:real`]) THEN
  SUBGOAL_THEN
   `vsum(1..n) (\r. Cx((b:num->real) r) *
                    Cx(log(&((u:num->num) r) / &((v:num->num) r)))) =
    Cx(sum(1..n) (\r. b r * log(&(u r) / &(v r))))`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM VSUM_CX; CX_MUL]; ALL_TAC] THEN
  ASM_SIMP_TAC[BAKER_LOGDATA_RATIONAL; CX_INJ; COMPLEX_NORM_CX] THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ARITH_TAC;
    REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC]]);;
