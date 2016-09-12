(* ========================================================================= *)
(* Naive quantifier elimination for complex numbers.                         *)
(* ========================================================================= *)

needs "Complex/fundamental.ml";;

let NULLSTELLENSATZ_LEMMA = prove
 (`!n p q. (!x. (poly p x = Cx(&0)) ==> (poly q x = Cx(&0))) /\
           (degree p = n) /\ ~(n = 0)
           ==> p divides (q exp n)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:complex list`; `q:complex list`] THEN
  ASM_CASES_TAC `?a. poly p a = Cx(&0)` THENL
   [ALL_TAC;
    DISCH_THEN(K ALL_TAC) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP
     (ONCE_REWRITE_RULE[TAUT `a ==> b <=> ~b ==> ~a`]
                       FUNDAMENTAL_THEOREM_OF_ALGEBRA_ALT)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:complex`; `zeros:complex list`] THEN
    STRIP_TAC THEN REWRITE_TAC[divides] THEN
    EXISTS_TAC `[inv(k)] ** q exp n` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN X_GEN_TAC `z:complex` THEN
    ASM_SIMP_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_RINV; COMPLEX_MUL_LID;
                 poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; POLY_0]] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:complex` MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  GEN_REWRITE_TAC LAND_CONV [ORDER_ROOT] THEN
  ASM_CASES_TAC `poly p = poly []` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[DEGREE_ZERO] THEN MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p:complex list`; `a:complex`; `order a p`] ORDER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:complex` o MATCH_MP ORDER_DEGREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:complex`) THEN
  REWRITE_TAC[ASSUME `poly p a = Cx(&0)`] THEN
  REWRITE_TAC[POLY_LINEAR_DIVIDES] THEN
  ASM_CASES_TAC `q:complex list = []` THENL
   [DISCH_TAC THEN MATCH_MP_TAC POLY_DIVIDES_ZERO THEN
    UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[poly_exp] THEN DISCH_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL; COMPLEX_MUL_LZERO; poly];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:complex list` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `[--a; Cx (&1)] exp (order a p) divides p` THEN
  GEN_REWRITE_TAC LAND_CONV [divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:complex list` ASSUME_TAC) THEN
  SUBGOAL_THEN `~(poly s = poly [])` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(poly p = poly [])` THEN
    ASM_REWRITE_TAC[POLY_ENTIRE]; ALL_TAC] THEN
  ASM_CASES_TAC `degree s = 0` THENL
   [SUBGOAL_THEN `?k. ~(k = Cx(&0)) /\ (poly s = poly [k])` MP_TAC THENL
     [EXISTS_TAC `LAST(normalize s)` THEN
      ASM_SIMP_TAC[NORMAL_NORMALIZE; GSYM POLY_NORMALIZE_ZERO] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM POLY_NORMALIZE] THEN
      UNDISCH_TAC `degree s = 0` THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
        [POLY_NORMALIZE_ZERO]) THEN
      REWRITE_TAC[degree] THEN
      SPEC_TAC(`normalize s`,`s:complex list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
      REWRITE_TAC[LENGTH; PRE; poly; LAST] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:complex` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[divides] THEN
    EXISTS_TAC `[inv(k)] ** [--a; Cx (&1)] exp (n - order a p) ** r exp n` THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_EXP; COMPLEX_POW_MUL] THEN
    X_GEN_TAC `z:complex` THEN
    ONCE_REWRITE_TAC[AC COMPLEX_MUL_AC
     `(a * b) * c * d * e = ((d * a) * (c * b)) * e`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN ASM_SIMP_TAC[SUB_ADD] THEN
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID; COMPLEX_MUL_RID] THEN
    ASM_SIMP_TAC[COMPLEX_MUL_LINV; COMPLEX_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `degree s < n` ASSUME_TAC THENL
   [EXPAND_TAC "n" THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP DEGREE_WELLDEF) THEN
    REWRITE_TAC[LINEAR_POW_MUL_DEGREE] THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(order a p = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `degree s`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:complex list`; `r:complex list`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!x. (poly p x = Cx(&0)) ==> (poly([--a; Cx (&1)] ** r) x = Cx(&0))` THEN
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[POLY_MUL; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_ENTIRE] THEN
    MATCH_MP_TAC(TAUT `~a ==> (a \/ b ==> b)`) THEN
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    REWRITE_TAC[SIMPLE_COMPLEX_ARITH
     `(--a + z * Cx(&1) = Cx(&0)) <=> (z = a)`] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `poly s a = Cx (&0)` THEN
    ASM_REWRITE_TAC[POLY_LINEAR_DIVIDES; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:complex list` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `~([--a; Cx (&1)] exp SUC (order a p) divides p)` THEN
    REWRITE_TAC[divides] THEN
    EXISTS_TAC `u:complex list` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[POLY_MUL; poly_exp; COMPLEX_MUL_AC; FUN_EQ_THM];
    ALL_TAC] THEN
  REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:complex list` ASSUME_TAC) THEN
  EXISTS_TAC
   `u ** [--a; Cx(&1)] exp (n - order a p) ** r exp (n - degree s)` THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; POLY_MUL; POLY_EXP; COMPLEX_POW_MUL] THEN
  X_GEN_TAC `z:complex` THEN
  ONCE_REWRITE_TAC[AC COMPLEX_MUL_AC
   `(ap * s) * u * anp * rns = (anp * ap) * rns * s * u`] THEN
  REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN
  ASM_SIMP_TAC[SUB_ADD] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM POLY_MUL] THEN
  SUBST1_TAC(SYM(ASSUME `poly (r exp degree s) = poly (s ** u)`)) THEN
  REWRITE_TAC[POLY_EXP; GSYM COMPLEX_POW_ADD] THEN
  ASM_SIMP_TAC[SUB_ADD; LT_IMP_LE]);;

let NULLSTELLENSATZ_UNIVARIATE = prove
 (`!p q. (!x. (poly p x = Cx(&0)) ==> (poly q x = Cx(&0))) <=>
         p divides (q exp (degree p)) \/
         ((poly p = poly []) /\ (poly q = poly []))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `poly p = poly []` THENL
   [ASM_REWRITE_TAC[poly] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP DEGREE_WELLDEF) THEN
    REWRITE_TAC[degree; normalize; LENGTH; ARITH; poly_exp] THEN
    ASM_REWRITE_TAC[divides; FUN_EQ_THM; POLY_MUL; poly;
                    COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH]; ALL_TAC] THEN
  ASM_CASES_TAC `degree p = 0` THENL
   [ALL_TAC;
    MP_TAC(SPECL [`degree p`; `p:complex list`; `q:complex list`]
                 NULLSTELLENSATZ_LEMMA) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EQ_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      X_GEN_TAC `z:complex` THEN DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[divides; FUN_EQ_THM; POLY_MUL] THEN
    DISCH_THEN(CHOOSE_THEN (MP_TAC o SPEC `z:complex`)) THEN
    ASM_REWRITE_TAC[POLY_EXP; COMPLEX_MUL_LZERO; COMPLEX_POW_EQ_0]] THEN
  ASM_REWRITE_TAC[poly_exp] THEN
  SUBGOAL_THEN `?k. ~(k = Cx(&0)) /\ (poly p = poly [k])` MP_TAC THENL
   [SUBST1_TAC(SYM(SPEC `p:complex list` POLY_NORMALIZE)) THEN
    EXISTS_TAC `LAST(normalize p)` THEN
    ASM_SIMP_TAC[NORMAL_NORMALIZE; GSYM POLY_NORMALIZE_ZERO] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM POLY_NORMALIZE] THEN
    UNDISCH_TAC `degree p = 0` THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
      [POLY_NORMALIZE_ZERO]) THEN
    REWRITE_TAC[degree] THEN
    SPEC_TAC(`normalize p`,`p:complex list`) THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
    REWRITE_TAC[LENGTH; PRE; poly; LAST] THEN
    SIMP_TAC[LENGTH_EQ_NIL; POLY_NORMALIZE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:complex` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[divides; poly; FUN_EQ_THM; POLY_MUL] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  EXISTS_TAC `[inv(k)]` THEN
  ASM_REWRITE_TAC[divides; poly; FUN_EQ_THM; POLY_MUL] THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  ASM_SIMP_TAC[COMPLEX_MUL_RINV]);;

(* ------------------------------------------------------------------------- *)
(* Useful lemma I should have proved ages ago.                               *)
(* ------------------------------------------------------------------------- *)

let CONSTANT_DEGREE = prove
 (`!p. constant(poly p) <=> (degree p = 0)`,
  GEN_TAC THEN REWRITE_TAC[constant] THEN EQ_TAC THENL
   [DISCH_THEN(ASSUME_TAC o GSYM o SPEC `Cx(&0)`) THEN
    SUBGOAL_THEN `degree [poly p (Cx(&0))] = 0` MP_TAC THENL
     [REWRITE_TAC[degree; normalize] THEN
      COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `(x = y) ==> (x = 0) ==> (y = 0)`) THEN
    MATCH_MP_TAC DEGREE_WELLDEF THEN
    REWRITE_TAC[FUN_EQ_THM; poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    FIRST_ASSUM(ACCEPT_TAC o GSYM);
    ONCE_REWRITE_TAC[GSYM POLY_NORMALIZE] THEN REWRITE_TAC[degree] THEN
    SPEC_TAC(`normalize p`,`l:complex list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[poly] THEN
    SIMP_TAC[LENGTH; PRE; LENGTH_EQ_NIL; poly; COMPLEX_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* It would be nicer to prove this without using algebraic closure...        *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_DEGREE_LEMMA = prove
 (`!n p q. (degree(p) = n)
           ==> n <= degree(p ** q) \/ (poly(p ** q) = poly [])`,
  INDUCT_TAC THEN REWRITE_TAC[LE_0] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `p:complex list` FUNDAMENTAL_THEOREM_OF_ALGEBRA) THEN
  ASM_REWRITE_TAC[CONSTANT_DEGREE; NOT_SUC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:complex` MP_TAC) THEN
  GEN_REWRITE_TAC LAND_CONV [POLY_LINEAR_DIVIDES] THEN
  DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC MP_TAC) THENL
   [REWRITE_TAC[POLY_MUL; poly; COMPLEX_MUL_LZERO; FUN_EQ_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:complex list` SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `poly (([--a; Cx (&1)] ** r) ** q) =
                poly ([--a; Cx (&1)] ** (r ** q))`
  ASSUME_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; POLY_MUL; COMPLEX_MUL_ASSOC]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DEGREE_WELLDEF) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`r ** q`; `--a`] LINEAR_MUL_DEGREE) THEN
  ASM_CASES_TAC `poly (r ** q) = poly []` THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN
    ONCE_REWRITE_TAC[POLY_MUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `n <= degree(r ** q) \/ (poly(r ** q) = poly [])` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[ARITH_RULE `SUC n <= m + 1 <=> n <= m`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN
    ONCE_REWRITE_TAC[POLY_MUL] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO]] THEN
  MP_TAC(SPECL [`r:complex list`; `--a`] LINEAR_MUL_DEGREE) THEN ANTS_TAC THENL
   [UNDISCH_TAC `~(poly (r ** q) = poly [])` THEN
    REWRITE_TAC[TAUT `~b ==> ~a <=> a ==> b`] THEN
    SIMP_TAC[poly; FUN_EQ_THM; POLY_MUL; COMPLEX_ENTIRE]; ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `degree r + 1 = SUC n` THEN ARITH_TAC);;

let DIVIDES_DEGREE = prove
 (`!p q. p divides q ==> degree(p) <= degree(q) \/ (poly q = poly [])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `r:complex list` THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP DEGREE_WELLDEF) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[DIVIDES_DEGREE_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on multivariate polynomials.                        *)
(* ------------------------------------------------------------------------- *)

let MPOLY_BASE_CONV =
  let pth_0 = prove
   (`Cx(&0) = poly [] x`,
    REWRITE_TAC[poly])
  and pth_1 = prove
   (`c = poly [c] x`,
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID])
  and pth_var = prove
   (`x = poly [Cx(&0); Cx(&1)] x`,
    REWRITE_TAC[poly; COMPLEX_ADD_LID; COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC[COMPLEX_ADD_RID; COMPLEX_MUL_RID])
  and zero_tm = `Cx(&0)`
  and c_tm = `c:complex`
  and x_tm = `x:complex` in
  let rec MPOLY_BASE_CONV avs tm =
    if avs = [] then REFL tm
    else if tm = zero_tm then INST [hd avs,x_tm] pth_0
    else if tm = hd avs then
      let th1 = INST [tm,x_tm] pth_var in
      let th2 =
        (LAND_CONV
          (COMB2_CONV (RAND_CONV (MPOLY_BASE_CONV (tl avs)))
                      (LAND_CONV (MPOLY_BASE_CONV (tl avs)))))
        (rand(concl th1)) in
      TRANS th1 th2
    else
      let th1 = MPOLY_BASE_CONV (tl avs) tm in
      let th2 = INST [hd avs,x_tm; rand(concl th1),c_tm] pth_1 in
      TRANS th1 th2 in
  MPOLY_BASE_CONV;;

let MPOLY_NORM_CONV =
  let pth_0 = prove
   (`poly [Cx(&0)] x = poly [] x`,
    REWRITE_TAC[poly; COMPLEX_ADD_RID; COMPLEX_MUL_RZERO])
  and pth_1 = prove
   (`poly [poly [] y] x = poly [] x`,
    REWRITE_TAC[poly; COMPLEX_ADD_RID; COMPLEX_MUL_RZERO]) in
  let conv_fwd = REWR_CONV(CONJUNCT2 poly)
  and conv_bck = REWR_CONV(GSYM(CONJUNCT2 poly))
  and conv_0 = GEN_REWRITE_CONV I [pth_0]
  and conv_1 = GEN_REWRITE_CONV I [pth_1] in
  let rec NORM0_CONV tm =
   (conv_0 ORELSEC
    (conv_fwd THENC RAND_CONV(RAND_CONV NORM0_CONV) THENC conv_bck THENC
     TRY_CONV NORM0_CONV)) tm
  and NORM1_CONV tm =
   (conv_1 ORELSEC
    (conv_fwd THENC RAND_CONV(RAND_CONV NORM1_CONV) THENC conv_bck THENC
     TRY_CONV NORM1_CONV)) tm in
  fun avs -> TRY_CONV(if avs = [] then NORM0_CONV else NORM1_CONV);;

let MPOLY_ADD_CONV,MPOLY_TADD_CONV =
  let add_conv0 = GEN_REWRITE_CONV I (butlast (CONJUNCTS POLY_ADD_CLAUSES))
  and add_conv1 = GEN_REWRITE_CONV I [last (CONJUNCTS POLY_ADD_CLAUSES)]
  and add_conv = REWR_CONV(GSYM POLY_ADD) in
  let rec MPOLY_ADD_CONV avs tm =
    if avs = [] then COMPLEX_RAT_ADD_CONV tm else
    (add_conv THENC LAND_CONV(MPOLY_TADD_CONV avs) THENC
     MPOLY_NORM_CONV (tl avs)) tm
  and MPOLY_TADD_CONV avs tm =
    (add_conv0 ORELSEC
      (add_conv1 THENC
       LAND_CONV (MPOLY_ADD_CONV (tl avs)) THENC
       RAND_CONV (MPOLY_TADD_CONV avs))) tm in
  MPOLY_ADD_CONV,MPOLY_TADD_CONV;;

let MPOLY_CMUL_CONV,MPOLY_TCMUL_CONV,MPOLY_MUL_CONV,MPOLY_TMUL_CONV =
  let cmul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 poly_cmul]
    and cmul_conv1 = GEN_REWRITE_CONV I [CONJUNCT2 poly_cmul]
    and cmul_conv = REWR_CONV(GSYM POLY_CMUL)
    and mul_conv0 = GEN_REWRITE_CONV I [CONJUNCT1 POLY_MUL_CLAUSES]
    and mul_conv1 = GEN_REWRITE_CONV I [CONJUNCT1(CONJUNCT2 POLY_MUL_CLAUSES)]
    and mul_conv2 = GEN_REWRITE_CONV I [CONJUNCT2(CONJUNCT2 POLY_MUL_CLAUSES)]
    and mul_conv = REWR_CONV(GSYM POLY_MUL) in
  let rec MPOLY_CMUL_CONV avs tm =
    (cmul_conv THENC LAND_CONV(MPOLY_TCMUL_CONV avs)) tm
  and MPOLY_TCMUL_CONV avs tm =
    (cmul_conv0 ORELSEC
      (cmul_conv1 THENC
       LAND_CONV (MPOLY_MUL_CONV (tl avs)) THENC
       RAND_CONV (MPOLY_TCMUL_CONV avs))) tm
  and MPOLY_MUL_CONV avs tm =
    if avs = [] then COMPLEX_RAT_MUL_CONV tm else
    (mul_conv THENC LAND_CONV(MPOLY_TMUL_CONV avs)) tm
  and MPOLY_TMUL_CONV avs tm =
    (mul_conv0 ORELSEC
     (mul_conv1 THENC MPOLY_TCMUL_CONV avs) ORELSEC
     (mul_conv2 THENC
      COMB2_CONV (RAND_CONV(MPOLY_TCMUL_CONV avs))
                 (COMB2_CONV (RAND_CONV(MPOLY_BASE_CONV (tl avs)))
                             (MPOLY_TMUL_CONV avs)) THENC
      MPOLY_TADD_CONV avs)) tm in
  MPOLY_CMUL_CONV,MPOLY_TCMUL_CONV,MPOLY_MUL_CONV,MPOLY_TMUL_CONV;;

let MPOLY_SUB_CONV =
  let pth = prove
   (`(poly p x - poly q x) = (poly p x + Cx(--(&1)) * poly q x)`,
    SIMPLE_COMPLEX_ARITH_TAC) in
  let APPLY_PTH_CONV = REWR_CONV pth in
  fun avs ->
     APPLY_PTH_CONV THENC
     RAND_CONV(LAND_CONV (MPOLY_BASE_CONV (tl avs)) THENC
               MPOLY_CMUL_CONV avs) THENC
     MPOLY_ADD_CONV avs;;

let MPOLY_POW_CONV =
  let cnv_0 = GEN_REWRITE_CONV I [CONJUNCT1 complex_pow]
  and cnv_1 = GEN_REWRITE_CONV I [CONJUNCT2 complex_pow] in
  let rec MPOLY_POW_CONV avs tm =
    try (cnv_0 THENC MPOLY_BASE_CONV avs) tm with Failure _ ->
    (RAND_CONV num_CONV THENC
     cnv_1 THENC (RAND_CONV (MPOLY_POW_CONV avs)) THENC
     MPOLY_MUL_CONV avs) tm in
  MPOLY_POW_CONV;;

(* ------------------------------------------------------------------------- *)
(* Recursive conversion to polynomial form.                                  *)
(* ------------------------------------------------------------------------- *)

let POLYNATE_CONV =
  let ELIM_SUB_CONV = REWR_CONV
    (SIMPLE_COMPLEX_ARITH `x - y = x + Cx(--(&1)) * y`)
  and ELIM_NEG_CONV = REWR_CONV
    (SIMPLE_COMPLEX_ARITH `--x = Cx(--(&1)) * x`)
  and ELIM_POW_0_CONV = GEN_REWRITE_CONV I [CONJUNCT1 complex_pow]
  and ELIM_POW_1_CONV =
    RAND_CONV num_CONV THENC GEN_REWRITE_CONV I [CONJUNCT2 complex_pow] in
  let rec ELIM_POW_CONV tm =
    (ELIM_POW_0_CONV ORELSEC (ELIM_POW_1_CONV THENC RAND_CONV ELIM_POW_CONV))
    tm in
  let polynet = itlist (uncurry net_of_conv)
    [`x pow n`,(fun cnv avs -> LAND_CONV (cnv avs) THENC MPOLY_POW_CONV avs);
     `x * y`,(fun cnv avs -> BINOP_CONV (cnv avs) THENC MPOLY_MUL_CONV avs);
     `x + y`,(fun cnv avs -> BINOP_CONV (cnv avs) THENC MPOLY_ADD_CONV avs);
     `x - y`,(fun cnv avs -> BINOP_CONV (cnv avs) THENC MPOLY_SUB_CONV avs);
     `--x`,(fun cnv avs -> ELIM_NEG_CONV THENC (cnv avs))]
    empty_net in
  let rec POLYNATE_CONV avs tm =
    try snd(hd(lookup tm polynet)) POLYNATE_CONV avs tm
    with Failure _ -> MPOLY_BASE_CONV avs tm in
  POLYNATE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Cancellation conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

let POLY_PAD_RULE =
  let pth = prove
   (`(poly p x = Cx(&0)) ==> (poly (CONS (Cx(&0)) p) x = Cx(&0))`,
    SIMP_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID]) in
  let MATCH_pth = MATCH_MP pth in
  fun avs th ->
     let th1 = MATCH_pth th in
     CONV_RULE(funpow 3 LAND_CONV (MPOLY_BASE_CONV (tl avs))) th1;;

let POLY_CANCEL_EQ_CONV =
  let pth_1 = prove
   (`(p = Cx(&0)) /\ ~(a = Cx(&0))
     ==> !q b. (q = Cx(&0)) <=> (a * q - b * p = Cx(&0))`,
    SIMP_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_RZERO; COMPLEX_ENTIRE]) in
  let MATCH_CANCEL_THM = MATCH_MP pth_1 in
  let rec POLY_CANCEL_EQ_CONV avs n ath eth tm =
    let m = length(dest_list(lhand(lhand tm))) in
    if m < n then REFL tm else
    let th1 = funpow (m - n) (POLY_PAD_RULE avs) eth in
    let th2 = MATCH_CANCEL_THM (CONJ th1 ath) in
    let th3 = SPECL [lhs tm; last(dest_list(lhand(lhs tm)))] th2 in
    let th4 = CONV_RULE(RAND_CONV(LAND_CONV
                (BINOP_CONV(MPOLY_CMUL_CONV avs)))) th3 in
    let th5 = CONV_RULE(RAND_CONV(LAND_CONV (MPOLY_SUB_CONV avs))) th4 in
    TRANS th5 (POLY_CANCEL_EQ_CONV avs n ath eth (rand(concl th5))) in
  POLY_CANCEL_EQ_CONV;;

let RESOLVE_EQ_RAW =
  let pth = prove
   (`(poly [] x = Cx(&0)) /\
     (poly [c] x = c)`,
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]) in
  let REWRITE_pth = GEN_REWRITE_CONV LAND_CONV [pth] in
  let rec RESOLVE_EQ asm tm =
    try EQT_INTRO(find (fun th -> concl th = tm) asm) with Failure _ ->
    let tm' = mk_neg tm in
    try EQF_INTRO(find (fun th -> concl th = tm') asm) with Failure _ ->
    try let th1 = REWRITE_pth tm in
        TRANS th1 (RESOLVE_EQ asm (rand(concl th1)))
    with Failure _ -> COMPLEX_RAT_EQ_CONV tm in
  RESOLVE_EQ;;

let RESOLVE_EQ asm tm =
  let th = RESOLVE_EQ_RAW asm tm in
  try EQF_ELIM th with Failure _ -> EQT_ELIM th;;

let RESOLVE_EQ_THEN =
  let MATCH_pth = MATCH_MP
  (TAUT `(p ==> (q <=> q1)) /\ (~p ==> (q <=> q2))
         ==> (q <=> (p /\ q1 \/ ~p /\ q2))`) in
  fun asm tm yfn nfn  ->
    try let th = RESOLVE_EQ asm tm in
        if is_neg(concl th) then nfn (th::asm) th else yfn (th::asm) th
    with Failure _ ->
        let tm' = mk_neg tm in
        let yth = DISCH tm (yfn (ASSUME tm :: asm) (ASSUME tm))
        and nth = DISCH tm' (nfn (ASSUME tm' :: asm) (ASSUME tm')) in
    MATCH_pth (CONJ yth nth);;

let POLY_CANCEL_ENE_CONV avs n ath eth tm =
  if is_neg tm then RAND_CONV(POLY_CANCEL_EQ_CONV avs n ath eth) tm
  else POLY_CANCEL_EQ_CONV avs n ath eth tm;;

let RESOLVE_NE =
  let NEGATE_NEGATE_RULE = GEN_REWRITE_RULE I [TAUT `p <=> (~p <=> F)`] in
  fun asm tm ->
    try let th = RESOLVE_EQ asm (rand tm) in
        if is_neg(concl th) then EQT_INTRO th
        else NEGATE_NEGATE_RULE th
    with Failure _ -> REFL tm;;

(* ------------------------------------------------------------------------- *)
(* Conversion for division of polynomials.                                   *)
(* ------------------------------------------------------------------------- *)

let LAST_CONV = GEN_REWRITE_CONV REPEATC [LAST_CLAUSES];;

let LENGTH_CONV =
  let cnv_0 = GEN_REWRITE_CONV I [CONJUNCT1 LENGTH]
  and cnv_1 = GEN_REWRITE_CONV I [CONJUNCT2 LENGTH] in
  let rec LENGTH_CONV tm =
    try cnv_0 tm with Failure _ ->
    (cnv_1 THENC RAND_CONV LENGTH_CONV THENC NUM_SUC_CONV) tm in
  LENGTH_CONV;;

let EXPAND_EX_BETA_CONV =
  let pth = prove(`EX P [c] = P c`,REWRITE_TAC[EX]) in
  let cnv_0 = GEN_REWRITE_CONV I [CONJUNCT1 EX]
  and cnv_1 = GEN_REWRITE_CONV I [pth]
  and cnv_2 = GEN_REWRITE_CONV I [CONJUNCT2 EX] in
  let rec EXPAND_EX_BETA_CONV tm =
    try (cnv_1 THENC BETA_CONV) tm with Failure _ -> try
        (cnv_2 THENC COMB2_CONV (RAND_CONV BETA_CONV)
                                EXPAND_EX_BETA_CONV) tm
    with Failure _ -> cnv_0 tm in
  EXPAND_EX_BETA_CONV;;

let POLY_DIVIDES_PAD_RULE =
  let pth = prove
   (`p divides q ==> p divides (CONS (Cx(&0)) q)`,
    REWRITE_TAC[divides; FUN_EQ_THM; POLY_MUL; poly; COMPLEX_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:complex list` ASSUME_TAC) THEN
    EXISTS_TAC `[Cx(&0); Cx(&1)] ** r` THEN
    ASM_REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_ADD_RID;
                    COMPLEX_MUL_RID; POLY_MUL] THEN
    REWRITE_TAC[COMPLEX_MUL_AC]) in
  let APPLY_pth = MATCH_MP pth in
  fun avs n tm ->
    funpow n
     (CONV_RULE(RAND_CONV(LAND_CONV(MPOLY_BASE_CONV (tl avs)))) o APPLY_pth)
     (SPEC tm POLY_DIVIDES_REFL);;

let POLY_DIVIDES_PAD_CONST_RULE =
  let pth = prove
   (`p divides q ==> !a. p divides (a ## q)`,
    REWRITE_TAC[FUN_EQ_THM; divides; POLY_CMUL; POLY_MUL] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:complex list` ASSUME_TAC) THEN
    X_GEN_TAC `a:complex` THEN EXISTS_TAC `[a] ** r` THEN
    ASM_REWRITE_TAC[POLY_MUL; poly] THEN SIMPLE_COMPLEX_ARITH_TAC) in
  let APPLY_pth = MATCH_MP pth in
  fun avs n a tm ->
    let th1 = POLY_DIVIDES_PAD_RULE avs n tm in
    let th2 = SPEC a (APPLY_pth th1) in
    CONV_RULE(RAND_CONV(MPOLY_TCMUL_CONV avs)) th2;;

let EXPAND_EX_BETA_RESOLVE_CONV asm tm =
  let th1 = EXPAND_EX_BETA_CONV tm in
  let djs = disjuncts(rand(concl th1)) in
  let th2 = end_itlist MK_DISJ (map (RESOLVE_NE asm) djs) in
  TRANS th1 th2;;

let POLY_DIVIDES_CONV =
  let pth_0 = prove
   (`LENGTH q < LENGTH p
     ==> ~(LAST p = Cx(&0))
         ==> (p divides q <=> ~(EX (\c. ~(c = Cx(&0))) q))`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[NOT_EX; GSYM POLY_ZERO] THEN EQ_TAC THENL
     [ALL_TAC;
      SIMP_TAC[divides; POLY_MUL; FUN_EQ_THM] THEN
      DISCH_TAC THEN EXISTS_TAC `[]:complex list` THEN
      REWRITE_TAC[poly; COMPLEX_MUL_RZERO]] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_DEGREE) THEN
    MATCH_MP_TAC(TAUT `(~b ==> ~a) ==> (a \/ b ==> b)`) THEN
    DISCH_TAC THEN REWRITE_TAC[NOT_LE] THEN ASM_SIMP_TAC[NORMAL_DEGREE] THEN
    REWRITE_TAC[degree] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
     `lq < lp ==> ~(lq = 0) /\ dq <= lq - 1 ==> dq < lp - 1`)) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    MATCH_MP_TAC(ARITH_RULE `m <= n ==> PRE m <= n - 1`) THEN
    REWRITE_TAC[LENGTH_NORMALIZE_LE]) in
  let APPLY_pth0 = PART_MATCH (lhand o rand o rand) pth_0 in
  let pth_1 = prove
   (`~(a = Cx(&0))
     ==> p divides p'
         ==> (!x. a * poly q x - poly p' x = poly r x)
             ==> (p divides q <=> p divides r)`,
    DISCH_TAC THEN REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `t:complex list` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; POLY_MUL] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `s:complex list` MP_TAC) THENL
     [DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
      EXISTS_TAC `a ## s ++ --(Cx(&1)) ## t` THEN
      REWRITE_TAC[POLY_MUL; POLY_ADD; POLY_CMUL] THEN
      REWRITE_TAC[poly] THEN SIMPLE_COMPLEX_ARITH_TAC;
      REWRITE_TAC[POLY_MUL] THEN DISCH_TAC THEN
      EXISTS_TAC `[inv(a)] ** (t ++ s)` THEN
      X_GEN_TAC `z:complex` THEN
      ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
      REWRITE_TAC[POLY_MUL; POLY_ADD; GSYM COMPLEX_MUL_ASSOC] THEN
      REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
      SUBGOAL_THEN `a * poly q z = (poly t z + poly s z) * poly p z`
      MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `z:complex`) THEN SIMPLE_COMPLEX_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `( * ) (inv a)`) THEN
      ASM_SIMP_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_LINV; COMPLEX_MUL_LID]]) in
  let MATCH_pth1 = MATCH_MP pth_1 in
  let rec DIVIDE_STEP_CONV avs sfn n tm =
    let m = length(dest_list(rand tm)) in
    if m < n then REFL tm else
    let th1 = POLY_DIVIDES_PAD_CONST_RULE avs (m - n)
                 (last(dest_list(rand tm))) (lhand tm) in
    let th2 = MATCH_MP (sfn tm) th1 in
    let av,bod = dest_forall(lhand(concl th2)) in
    let tm1 = vsubst [hd avs,av] (lhand bod) in
    let th3 = (LAND_CONV (MPOLY_CMUL_CONV avs) THENC MPOLY_SUB_CONV avs) tm1 in
    let th4 = MATCH_MP th2 (GEN (hd avs) th3) in
    TRANS th4 (DIVIDE_STEP_CONV avs sfn n (rand(concl th4))) in
  let zero_tm = `Cx(&0)` in
  fun asm avs tm ->
    let ath = RESOLVE_EQ asm (mk_eq(last(dest_list(lhand tm)),zero_tm)) in
    let sfn = PART_MATCH (lhand o rand o rand) (MATCH_pth1 ath)
    and n = length(dest_list(lhand tm)) in
    let th1 = DIVIDE_STEP_CONV avs sfn n tm in
    let th2 = APPLY_pth0 (rand(concl th1)) in
    let th3 = (BINOP_CONV LENGTH_CONV THENC NUM_LT_CONV) (lhand(concl th2)) in
    let th4 = MP th2 (EQT_ELIM th3) in
    let th5 = CONV_RULE(LAND_CONV(RAND_CONV(LAND_CONV LAST_CONV))) th4 in
    let th6 = TRANS th1 (MP th5 ath) in
    CONV_RULE(RAND_CONV(RAND_CONV(EXPAND_EX_BETA_RESOLVE_CONV asm))) th6;;

(* ------------------------------------------------------------------------- *)
(* Apply basic Nullstellensatz principle.                                    *)
(* ------------------------------------------------------------------------- *)

let BASIC_QUELIM_CONV =
  let pth_1 = prove
   (`((?x. (poly p x = Cx(&0)) /\ ~(poly [] x = Cx(&0))) <=> F) /\
     ((?x. ~(poly [] x = Cx(&0))) <=> F) /\
     ((?x. ~(poly [c] x = Cx(&0))) <=> ~(c = Cx(&0))) /\
     ((?x. (poly [] x = Cx(&0))) <=> T) /\
     ((?x. (poly [c] x = Cx(&0))) <=> (c = Cx(&0)))`,
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]) in
  let APPLY_pth1 = GEN_REWRITE_CONV I [pth_1] in
  let pth_2 = prove
   (`~(LAST(CONS a (CONS b p)) = Cx(&0))
     ==> ((?x. poly (CONS a (CONS b p)) x = Cx(&0)) <=> T)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `CONS (a:complex) (CONS b p)`
             FUNDAMENTAL_THEOREM_OF_ALGEBRA_ALT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[NOT_EXISTS_THM; CONS_11] THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(ALL (\c. c = Cx(&0)) (CONS b p))`
     (fun th -> MP_TAC th THEN ASM_REWRITE_TAC[]) THEN
    UNDISCH_TAC `~(LAST (CONS a (CONS b p)) = Cx (&0))` THEN
    ONCE_REWRITE_TAC[LAST] THEN REWRITE_TAC[NOT_CONS_NIL] THEN
    REWRITE_TAC[TAUT `~a ==> ~b <=> b ==> a`] THEN
    SPEC_TAC(`p:complex list`,`p:complex list`) THEN
    LIST_INDUCT_TAC THEN ONCE_REWRITE_TAC[LAST] THEN
    REWRITE_TAC[ALL; NOT_CONS_NIL] THEN
    STRIP_TAC THEN FIRST_ASSUM(UNDISCH_TAC o check is_imp o concl) THEN
    REWRITE_TAC[LAST] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ALL]) in
  let APPLY_pth2 = PART_MATCH (lhand o rand) pth_2 in
  let pth_2b = prove
   (`(?x. ~(poly p x = Cx(&0))) <=> EX (\c. ~(c = Cx(&0))) p`,
    REWRITE_TAC[GSYM NOT_FORALL_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(~a <=> b) <=> (a <=> ~b)`] THEN
    REWRITE_TAC[NOT_EX; GSYM POLY_ZERO; poly; FUN_EQ_THM]) in
  let APPLY_pth2b = GEN_REWRITE_CONV I [pth_2b] in
  let pth_3 = prove
   (`~(LAST(CONS a p) = Cx(&0))
     ==> ((?x. (poly (CONS a p) x = Cx(&0)) /\ ~(poly q x = Cx(&0))) <=>
          ~((CONS a p) divides (q exp (LENGTH p))))`,
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`CONS (a:complex) p`; `q:complex list`]
                 NULLSTELLENSATZ_UNIVARIATE) THEN
    ASM_SIMP_TAC[degree; NORMALIZE_EQ; LENGTH; PRE] THEN
    SUBGOAL_THEN `~(poly (CONS a p) = poly [])`
     (fun th -> REWRITE_TAC[th] THEN MESON_TAC[]) THEN
    REWRITE_TAC[POLY_ZERO] THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`p:complex list`,`p:complex list`) THEN
    REWRITE_TAC[LAST] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; ALL; NOT_CONS_NIL] THEN
    POP_ASSUM MP_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[ALL] THEN
    CONV_TAC TAUT) in
  let APPLY_pth3 = PART_MATCH (lhand o rand) pth_3 in
  let POLY_EXP_DIVIDES_CONV =
    let pth_4 = prove
     (`(!x. (poly (q exp n) x = poly r x))
       ==> (p divides (q exp n) <=> p divides r)`,
      SIMP_TAC[divides; POLY_EXP; FUN_EQ_THM]) in
    let APPLY_pth4 = MATCH_MP pth_4
    and poly_tm = `poly`
    and REWR_POLY_EXP_CONV = REWR_CONV POLY_EXP in
    let POLY_EXP_DIVIDES_CONV avs tm =
      let tm1 = mk_comb(mk_comb(poly_tm,rand tm),hd avs) in
      let th1 = REWR_POLY_EXP_CONV tm1 in
      let th2 = TRANS th1 (MPOLY_POW_CONV avs (rand(concl th1))) in
      PART_MATCH lhand (APPLY_pth4 (GEN (hd avs) th2)) tm in
    POLY_EXP_DIVIDES_CONV in
  fun asm avs tm ->
    try APPLY_pth1 tm with Failure _ ->
    try let th1 = APPLY_pth2 tm in
        let th2 = CONV_RULE(LAND_CONV(RAND_CONV(LAND_CONV LAST_CONV))) th1 in
        let th3 = try MATCH_MP th2 (RESOLVE_EQ asm (rand(lhand(concl th2))))
                  with Failure _ -> failwith "Sanity failure (2a)" in
        th3
    with Failure _ -> try
        let th1 = APPLY_pth2b tm in
        TRANS th1 (EXPAND_EX_BETA_RESOLVE_CONV asm (rand(concl th1)))
    with Failure _ ->
        let th1 = APPLY_pth3 tm in
        let th2 = CONV_RULE(LAND_CONV(RAND_CONV(LAND_CONV LAST_CONV))) th1 in
        let th3 = try MATCH_MP th2 (RESOLVE_EQ asm (rand(lhand(concl th2))))
                  with Failure _ -> failwith "Sanity failure (2b)" in
        let th4 = CONV_RULE (funpow 4 RAND_CONV LENGTH_CONV) th3 in
        let th5 =
           CONV_RULE(RAND_CONV(RAND_CONV(POLY_EXP_DIVIDES_CONV avs))) th4 in
        CONV_RULE(RAND_CONV(RAND_CONV(POLY_DIVIDES_CONV asm avs))) th5;;

(* ------------------------------------------------------------------------- *)
(* Put into canonical form by multiplying inequalities.                      *)
(* ------------------------------------------------------------------------- *)

let POLY_NE_MULT_CONV =
  let pth = prove
   (`~(poly p x = Cx(&0)) /\ ~(poly q x = Cx(&0)) <=>
     ~(poly p x * poly q x = Cx(&0))`,
    REWRITE_TAC[COMPLEX_ENTIRE; DE_MORGAN_THM]) in
  let APPLY_pth = REWR_CONV pth in
  let rec POLY_NE_MULT_CONV avs tm =
    if not(is_conj tm) then REFL tm else
    let l,r = dest_conj tm in
    let th1 = MK_COMB(AP_TERM (rator(rator tm)) (POLY_NE_MULT_CONV avs l),
                      POLY_NE_MULT_CONV avs r) in
    let th2 = TRANS th1 (APPLY_pth (rand(concl th1))) in
    CONV_RULE(RAND_CONV(RAND_CONV(LAND_CONV(MPOLY_MUL_CONV avs)))) th2 in
  POLY_NE_MULT_CONV;;

let CORE_QUELIM_CONV =
  let CONJ_AC_RULE = AC CONJ_ACI in
  let CORE_QUELIM_CONV asm avs tm =
    let ev,bod = dest_exists tm in
    let cjs = conjuncts bod in
    let eqs,neqs = partition is_eq cjs in
    if eqs = [] then
      let th1 = MK_EXISTS ev (POLY_NE_MULT_CONV avs bod) in
      TRANS th1 (BASIC_QUELIM_CONV asm avs (rand(concl th1)))
    else if length eqs > 1 then failwith "CORE_QUELIM_CONV: Sanity failure"
    else if neqs = [] then BASIC_QUELIM_CONV asm avs tm else
    let tm1 = mk_conj(hd eqs,list_mk_conj neqs) in
    let th1 = CONJ_AC_RULE(mk_eq(bod,tm1)) in
    let th2 = CONV_RULE(funpow 2 RAND_CONV(POLY_NE_MULT_CONV avs)) th1 in
    let th3 = MK_EXISTS ev th2 in
    TRANS th3 (BASIC_QUELIM_CONV asm avs (rand(concl th3))) in
  CORE_QUELIM_CONV;;

(* ------------------------------------------------------------------------- *)
(* Main elimination coversion (for a single quantifier).                     *)
(* ------------------------------------------------------------------------- *)

let RESOLVE_EQ_NE =
  let DNE_RULE = GEN_REWRITE_RULE I
   [TAUT `((p <=> T) <=> (~p <=> F)) /\ ((p <=> F) <=> (~p <=> T))`] in
  fun asm tm ->
    if is_neg tm then DNE_RULE(RESOLVE_EQ_RAW asm (rand tm))
    else RESOLVE_EQ_RAW asm tm;;

let COMPLEX_QUELIM_CONV =
  let pth_0 = prove
   (`((poly [] x = Cx(&0)) <=> T) /\
     ((poly [] x = Cx(&0)) /\ p <=> p)`,
    REWRITE_TAC[poly])
  and pth_1 = prove
   (`(~(poly [] x = Cx(&0)) <=> F) /\
     (~(poly [] x = Cx(&0)) /\ p <=> F)`,
    REWRITE_TAC[poly])
  and pth_2 = prove
   (`(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)`,
    CONV_TAC TAUT)
  and zero_tm = `Cx(&0)`
  and true_tm = `T` in
  let ELIM_ZERO_RULE = GEN_REWRITE_RULE RAND_CONV [pth_0]
  and ELIM_NONZERO_RULE = GEN_REWRITE_RULE RAND_CONV [pth_1]
  and INCORP_ASSUM_THM = MATCH_MP pth_2
  and CONJ_AC_RULE = AC CONJ_ACI in
  let POLY_CONST_CONV =
    let pth = prove
     (`((poly [c] x = y) <=> (c = y)) /\
       (~(poly [c] x = y) <=> ~(c = y))`,
      REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]) in
    TRY_CONV(GEN_REWRITE_CONV I [pth]) in
  let EXISTS_TRIV_CONV = REWR_CONV EXISTS_SIMP
  and EXISTS_PUSH_CONV = REWR_CONV RIGHT_EXISTS_AND_THM
  and AND_SIMP_CONV = GEN_REWRITE_CONV DEPTH_CONV
    [TAUT `(p /\ F <=> F) /\ (p /\ T <=> p) /\
           (F /\ p <=> F) /\ (T /\ p <=> p)`]
  and RESOLVE_OR_CONST_CONV asm tm =
    try RESOLVE_EQ_NE asm tm with Failure _ -> POLY_CONST_CONV tm
  and false_tm = `F` in
  let rec COMPLEX_QUELIM_CONV asm avs tm =
    let ev,bod = dest_exists tm in
    let cjs = conjuncts bod in
    let cjs_set = setify cjs in
    if length cjs_set < length cjs then
      let th1 = CONJ_AC_RULE(mk_eq(bod,list_mk_conj cjs_set)) in
      let th2 = MK_EXISTS ev th1 in
      TRANS th2 (COMPLEX_QUELIM_CONV asm avs (rand(concl th2)))
    else
    let eqs,neqs = partition is_eq cjs in
    let lens = map (length o dest_list o lhand o lhs) eqs
    and nens = map (length o dest_list o lhand o lhs o rand) neqs in
    try let zeq = el (index 0 lens) eqs in
        if cjs = [zeq] then BASIC_QUELIM_CONV asm avs tm else
        let cjs' = zeq::(subtract cjs [zeq]) in
        let th1 = ELIM_ZERO_RULE(CONJ_AC_RULE(mk_eq(bod,list_mk_conj cjs'))) in
        let th2 = MK_EXISTS ev th1 in
        TRANS th2 (COMPLEX_QUELIM_CONV asm avs (rand(concl th2)))
    with Failure _ -> try
        let zne = el (index 0 nens) neqs in
        if cjs = [zne] then BASIC_QUELIM_CONV asm avs tm else
        let cjs' = zne::(subtract cjs [zne]) in
        let th1 = ELIM_NONZERO_RULE
          (CONJ_AC_RULE(mk_eq(bod,list_mk_conj cjs'))) in
        CONV_RULE (RAND_CONV EXISTS_TRIV_CONV) (MK_EXISTS ev th1)
    with Failure _ -> try
        let ones = map snd (filter (fun (n,_) -> n = 1)
                                   (zip lens eqs @ zip nens neqs)) in
        if ones = [] then failwith "" else
        let cjs' = subtract cjs ones in
        if cjs' = [] then
          let th1 = MK_EXISTS ev (SUBS_CONV(map POLY_CONST_CONV cjs) bod) in
          TRANS th1 (EXISTS_TRIV_CONV (rand(concl th1)))
        else
          let tha = SUBS_CONV (map (RESOLVE_OR_CONST_CONV asm) ones)
                              (list_mk_conj ones) in
          let thb = CONV_RULE (RAND_CONV AND_SIMP_CONV) tha in
          if rand(concl thb) = false_tm then
            let thc = MK_CONJ thb (REFL(list_mk_conj cjs')) in
            let thd = CONV_RULE(RAND_CONV AND_SIMP_CONV) thc in
            let the = CONJ_AC_RULE(mk_eq(bod,lhand(concl thd))) in
            let thf = MK_EXISTS ev (TRANS the thd) in
            CONV_RULE(RAND_CONV EXISTS_TRIV_CONV) thf
          else
            let thc = MK_CONJ thb (REFL(list_mk_conj cjs')) in
            let thd = CONJ_AC_RULE(mk_eq(bod,lhand(concl thc))) in
            let the =  MK_EXISTS ev (TRANS thd thc) in
            let th4 = TRANS  the(EXISTS_PUSH_CONV(rand(concl the))) in
            let tm4 = rand(concl th4) in
            let th5 = COMPLEX_QUELIM_CONV asm avs (rand tm4) in
            TRANS th4 (AP_TERM (rator tm4) th5)
    with Failure _ ->
    if eqs = [] ||
       (length eqs = 1 &
        (let ceq = mk_eq(last(dest_list(lhand(lhs(hd eqs)))),zero_tm) in
         try concl(RESOLVE_EQ asm ceq) = mk_neg ceq with Failure _ -> false) &
        (let h = hd lens in forall (fun n -> n < h) nens))
    then
      CORE_QUELIM_CONV asm avs tm
    else
      let n = end_itlist min lens in
      let eq = el (index n lens) eqs in
      let pol = lhand(lhand eq) in
      let atm = last(dest_list pol) in
      let zeq = mk_eq(atm,zero_tm) in
      RESOLVE_EQ_THEN asm zeq
       (fun asm' yth ->
          let th0 = TRANS yth (MPOLY_BASE_CONV (tl avs) zero_tm) in
          let th1 =
            GEN_REWRITE_CONV
             (LAND_CONV o LAND_CONV o funpow (n - 1) RAND_CONV o LAND_CONV)
             [th0] eq in
          let th2 = LAND_CONV(MPOLY_NORM_CONV avs) (rand(concl th1)) in
          let th3 = MK_EXISTS ev (SUBS_CONV[TRANS th1 th2] bod) in
          TRANS th3 (COMPLEX_QUELIM_CONV asm' avs (rand(concl th3))))
       (fun asm' nth ->
          let oth = subtract cjs [eq] in
          if oth = [] then COMPLEX_QUELIM_CONV asm' avs tm else
          let eth = ASSUME eq in
          let ths = map (POLY_CANCEL_ENE_CONV avs n nth eth) oth in
          let th1 = DISCH eq (end_itlist MK_CONJ ths) in
          let th2 = INCORP_ASSUM_THM th1 in
          let th3 = TRANS (CONJ_AC_RULE(mk_eq(bod,lhand(concl th2)))) th2 in
          let th4 = MK_EXISTS ev th3 in
          TRANS th4 (COMPLEX_QUELIM_CONV asm' avs (rand(concl th4)))) in
  fun asm avs -> time(COMPLEX_QUELIM_CONV asm avs);;

(* ------------------------------------------------------------------------- *)
(* NNF conversion doing "conditionals" ~(p /\ q \/ ~p /\ r) intelligently.   *)
(* ------------------------------------------------------------------------- *)

let NNF_COND_CONV =
  let NOT_EXISTS_UNIQUE_THM = prove
   (`~(?!x. P x) <=> (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')`,
    REWRITE_TAC[EXISTS_UNIQUE_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; CONJ_ASSOC]) in
  let tauts =
    [TAUT `~(~p) <=> p`;
     TAUT `~(p /\ q) <=> ~p \/ ~q`;
     TAUT `~(p \/ q) <=> ~p /\ ~q`;
     TAUT `~(p ==> q) <=> p /\ ~q`;
     TAUT `p ==> q <=> ~p \/ q`;
     NOT_FORALL_THM;
     NOT_EXISTS_THM;
     EXISTS_UNIQUE_THM;
     NOT_EXISTS_UNIQUE_THM;
     TAUT `~(p <=> q) <=> (p /\ ~q) \/ (~p /\ q)`;
     TAUT `(p <=> q) <=> (p /\ q) \/ (~p /\ ~q)`;
     TAUT `~(p /\ q \/ ~p /\ r) <=> p /\ ~q \/ ~p /\ ~r`] in
  GEN_REWRITE_CONV TOP_SWEEP_CONV tauts;;

(* ------------------------------------------------------------------------- *)
(* Overall procedure for multiple quantifiers in any first order formula.    *)
(* ------------------------------------------------------------------------- *)

let FULL_COMPLEX_QUELIM_CONV =
  let ELIM_FORALL_CONV =
    let pth = prove(`(!x. P x) <=> ~(?x. ~(P x))`,MESON_TAC[]) in
    REWR_CONV pth in
  let ELIM_EQ_CONV =
    let pth = SIMPLE_COMPLEX_ARITH `(x = y) <=> (x - y = Cx(&0))`
    and zero_tm = `Cx(&0)` in
    let REWR_pth = REWR_CONV pth in
    fun avs tm ->
      if rand tm = zero_tm then LAND_CONV(POLYNATE_CONV avs) tm
      else (REWR_pth THENC LAND_CONV(POLYNATE_CONV avs)) tm in
  let SIMP_DNF_CONV =
    GEN_REWRITE_CONV TOP_DEPTH_CONV (basic_rewrites()) THENC
    NNF_COND_CONV THENC DNF_CONV in
  let DISTRIB_EXISTS_CONV = GEN_REWRITE_CONV I [EXISTS_OR_THM] in
  let TRIV_EXISTS_CONV = GEN_REWRITE_CONV I [EXISTS_SIMP] in
  let complex_ty = `:complex` in
  let FINAL_SIMP_CONV =
    GEN_REWRITE_CONV DEPTH_CONV [CX_INJ] THENC
    REAL_RAT_REDUCE_CONV THENC
    GEN_REWRITE_CONV TOP_DEPTH_CONV (basic_rewrites()) in
  let rec FULL_COMPLEX_QUELIM_CONV avs tm =
     if is_forall tm then
        let th1 = ELIM_FORALL_CONV tm in
        let th2 = FULL_COMPLEX_QUELIM_CONV avs (rand(concl th1)) in
        TRANS th1 th2
     else if is_neg tm then
        AP_TERM (rator tm) (FULL_COMPLEX_QUELIM_CONV avs (rand tm))
     else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
        let lop,r = dest_comb tm in
        let op,l = dest_comb lop in
        let thl = FULL_COMPLEX_QUELIM_CONV avs l
        and thr = FULL_COMPLEX_QUELIM_CONV avs r in
        MK_COMB(AP_TERM(rator(rator tm)) thl,thr)
     else if is_exists tm then
        let ev,bod = dest_exists tm in
        let th0 = FULL_COMPLEX_QUELIM_CONV (ev::avs) bod in
        let th1 = MK_EXISTS ev (CONV_RULE(RAND_CONV SIMP_DNF_CONV) th0) in
        TRANS th1 (DISTRIB_AND_COMPLEX_QUELIM_CONV (ev::avs) (rand(concl th1)))
     else if is_eq tm then
        ELIM_EQ_CONV avs tm
     else failwith "unexpected type of formula"
  and DISTRIB_AND_COMPLEX_QUELIM_CONV avs tm =
    try TRIV_EXISTS_CONV tm
    with Failure _ -> try
        (DISTRIB_EXISTS_CONV THENC
         BINOP_CONV (DISTRIB_AND_COMPLEX_QUELIM_CONV avs)) tm
    with Failure _ -> COMPLEX_QUELIM_CONV [] avs tm in
  fun tm ->
        let avs = filter (fun t -> type_of t = complex_ty) (frees tm) in
        (FULL_COMPLEX_QUELIM_CONV avs THENC FINAL_SIMP_CONV) tm;;
