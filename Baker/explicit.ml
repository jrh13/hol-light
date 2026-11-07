(* ========================================================================= *)
(* The core lower bound: explicit, existential and uniform versions.         *)
(*                                                                           *)
(* Purpose: the core lower bound of Baker, Transcendental Number Theory, Ch. *)
(* 3, Thm 3.1, for fixed data: cexp(lg r) are roots of integer polynomials   *)
(* (degrees d r, heights H r), there are m extra variables of degree <= Dx   *)
(* and height <= B, and the coefficients g 0, ..., g n are integer           *)
(* polynomials (intpoly) of degrees e and coefficient bound G0. The          *)
(* parametric core is applied with q fixed (huge, depending on the data) and *)
(* h of the size of log B. First with explicit choices: all sizes of the     *)
(* data bounded by one parameter Mb and an exponent that is polynomial in Mb *)
(* (the base of the descent of Sharpening I, Acta Arith. 21 (1972) 117-129). *)
(* The definitions baker_qreq n Dm M (lower bound for q) and                 *)
(* baker_cexp n Dm E Ex G0 Dx Mb q (lower bound for C) are explicit          *)
(* functions of the data.                                                    *)
(*                                                                           *)
(* Main results: BAKER_CORE_EXPLICIT (if Mb bounds sum |lg r|, log(1/|lg r|) *)
(*   and sum log((d r + 1) H r^3), the logarithms have no nontrivial integer *)
(*   relation with coefficients <= baker_Lpar, q >= baker_qreq and C >=      *)
(*   baker_cexp, where Dm = Dmax Dx^m, then                                  *)
(*        B^-C <= |g 0 theta + sum g r theta lg r|);                         *)
(*   BAKER_CORE_EXISTS (logarithms without any nontrivial integer relation:  *)
(*   there is C such that for all B >= 2 and all values theta of the extra   *)
(*   variables that are roots of integer polynomials of degree <= Dx and     *)
(*   height <= B, if g n theta <> 0 then B^-C <= |g 0 theta + g 1 theta lg 1 *)
(*   + ... + g n theta lg n|; a corollary of BAKER_CORE_EXPLICIT with Mb, q  *)
(*   and C chosen by REAL_ARCH_SIMPLE); BAKER_CORE_UNIFORM (for fixed n, m,  *)
(*   e, G0, Dx, Dmax there are c, kappa, cr, kr such that for all data of    *)
(*   size <= Mb whose logarithms have no nontrivial integer relation with    *)
(*   coefficients <= cr Mb^kr                                                *)
(*        exp(-(c Mb^kappa log B)) <= |g 0 theta + sum g r theta lg r|);     *)
(*   BAKER_QREQ_POLY and BAKER_CEXP_POLY (polynomial growth in Mb).          *)
(*                                                                           *)
(* Uses: Baker/numeric_dmax.ml (BAKER_CORE_NUMERIC_DMAX, REAL_NUM_CEIL,      *)
(*   SMALL_INDEPENDENT_MONO), Baker/heights.ml (BAKER_EXTRA_BOUNDS),         *)
(*   Baker/param.ml (the parameters baker_c, baker_J, baker_e1, baker_kpar,  *)
(*   baker_Lpar), Baker/intpoly.ml (intpoly), Baker/estimates.ml             *)
(*   (LOG_LE_SELF), Baker/bounds.ml (PRODUCT_GE_1), Baker/lemmas.ml          *)
(*   (REAL_LE_1_MUL, LOG_2_LE_1).                                            *)
(* ========================================================================= *)

needs "Baker/heights.ml";;
needs "Baker/numeric_dmax.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The explicit parameters.                                                  *)
(* ------------------------------------------------------------------------- *)

let baker_qreq = new_definition
 `baker_qreq n Dm M =
    max (exp(&112))
     (max (&2176 * M pow 3 * &2 pow (baker_J n Dm))
          (&(baker_c Dm * (n + 1)) * (&8 * M + &75) * (&6 * M) pow (n + 3) *
           &2 pow (baker_J n Dm + 1)))`;;

let baker_cexp = new_definition
 `baker_cexp n Dm E Ex G0 Dx Mb q =
    &q pow (baker_e1 n Dm + 1) *
    (&2 * ((&4 * Mb + &n + &Dm + &2) + log(&(baker_kpar n Dm q)) + log G0 +
           &1 + (log G0 + &E * Mb + &Ex * log(&1 + &Dx)) +
           &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1)) +
           &E * Mb + &Ex * log(&Dx + &1)) +
     (&Ex + &3 * &Dm * &Ex + &3 * &Ex)) +
    &3 * &Dm * &Ex + &2 * &q pow (baker_e1 n Dm + 1) +
    &2 * (&Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1)))`;;

let LOG_CA_LE_SA = prove
 (`!n (e:num->num) (d:num->num) (H:num->real).
     (!r. r IN 1..n ==> 1 <= d r /\ &1 <= H r)
     ==> log(product(1..n) (\r. (&1 + &(d r) * H r) pow e r)) <=
         sum(1..n) (\r. &(e r) * log(&(d r + 1) * H r pow 3))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN 1..n ==> &0 < (&1 + &(d r) * (H:num->real) r) pow e r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LT THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  BETA_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `(H:num->real) r`)) (concl th) &&
    not (can (find_term ((=) `(e:num->num) r`)) (concl th)))) THEN
  ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 + &(d r) * (H:num->real) r` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < &1 + x`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC LOG_MONO_LE_IMP THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(H:num->real) r <= H r pow 3` MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC REAL_LE_TRANS `&(d r + 1) * (H:num->real) r` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]]);;

(* ------------------------------------------------------------------------- *)
(* The core with explicit parameters.                                        *)
(* ------------------------------------------------------------------------- *)

let BAKER_CORE_EXPLICIT = prove
 (`!n m lg (a:num->num->real) (d:num->num) (H:num->real) (e:num->num) G0 Dx
    Dmax Mb q C.
     1 <= n /\ 1 <= Dx /\ &1 <= G0 /\ &1 <= Mb /\ nproduct(1..n) d <= Dmax /\
     (!r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)) /\
     (!b. (!r. r IN 1..n
               ==> integer(b r) /\
                   abs(b r) <= &(baker_Lpar n (Dmax * Dx EXP m) q)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0) /\
     (!r. r IN 1..n ==> exp(--Mb) <= norm(lg r)) /\
     sum(1..n) (\r. norm(lg r)) <= Mb /\
     sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= Mb /\
     baker_qreq n (Dmax * Dx EXP m) (&4 * Mb + &n + &(Dmax * Dx EXP m) + &2)
     <= &q /\
     baker_cexp n (Dmax * Dx EXP m) (nsum(1..n) e) (nsum((n + 1)..(n + m)) e)
                G0 Dx Mb q <= &C
     ==> !B (theta:num->complex) (g:num->(num->complex)->complex)
               (dx:num->num) (ax:num->num->real).
           &2 <= B /\
           (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
           (!r. r IN (n + 1)..(n + m)
                ==> 1 <= dx r /\ dx r <= Dx /\
                    (!j. integer(ax r j) /\ abs(ax r j) <= B) /\
                    ~(ax r (dx r) = &0) /\
                    vsum(0..dx r) (\j. Cx(ax r j) * theta r pow j) = Cx(&0)) /\
           (!j. j <= n ==> intpoly (1..(n + m)) e G0 (g j)) /\
           ~(g n theta = Cx(&0))
           ==> inv(B pow C) <=
               norm(g 0 theta + vsum(1..n) (\r. g r theta * lg r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `lmin = exp(--Mb)` THEN
  SUBGOAL_THEN `&0 < lmin /\ lmin <= &1 /\ log(inv lmin) = Mb`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lmin" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[REAL_EXP_POS_LT];
      SUBGOAL_THEN `exp(--Mb) <= exp(&0)` MP_TAC THENL
       [REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_EXP_0]];
      REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV; LOG_EXP]];
    ALL_TAC] THEN
  ABBREV_TAC `Lam = &1 + sum(1..n) (\r. norm((lg:num->complex) r))` THEN
  ABBREV_TAC `Dm = Dmax * Dx EXP m` THEN
  ABBREV_TAC `E = nsum(1..n) (e:num->num)` THEN
  ABBREV_TAC `SA = sum(1..n) (\r. &(e r) * log(&(d r + 1) * H r pow 3))` THEN
  ABBREV_TAC `cH = sum(1..n) (\r. log(&(d r + 1) * (H:num->real) r pow 3))` THEN
  ABBREV_TAC `Ex = nsum((n + 1)..(n + m)) (e:num->num)` THEN
  ABBREV_TAC `CA = product(1..n) (\r. (&1 + &(d r) * H r) pow e r)` THEN
  SUBGOAL_THEN `&0 <= SA /\ &0 <= cH /\ &1 <= CA /\ &0 <= log(inv lmin)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "SA" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC LOG_POS THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        is_forall(concl th) && free_in `a:num->num->real` (concl th) &&
        free_in `lg:num->complex` (concl th))) THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_1_MUL THEN
      CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "cH" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      X_GEN_TAC `r:num` THEN STRIP_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC LOG_POS THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        is_forall(concl th) && free_in `a:num->num->real` (concl th) &&
        free_in `lg:num->complex` (concl th))) THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_1_MUL THEN
      CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "CA" THEN MATCH_MP_TAC PRODUCT_GE_1 THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      BETA_TAC THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        is_forall(concl th) && free_in `a:num->num->real` (concl th) &&
        free_in `lg:num->complex` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_INV_1_LE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `M = &4 * Mb + &n + &Dm + &2` THEN
  SUBGOAL_THEN `1 <= nproduct(1..n) (d:num->num)` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> 0 < x`] THEN
    MATCH_MP_TAC NPRODUCT_POS_LT THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= x ==> 0 < x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `nproduct(1..n) (d:num->num) * Dx EXP m <= Dm /\
    1 <= nproduct(1..n) (d:num->num) * Dx EXP m`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Dm" THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= Dm` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(cH:real) <= Mb /\ SA <= &E * Mb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `&E * cH` THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS]] THEN
    MAP_EVERY EXPAND_TAC ["SA"; "E"; "cH"] THEN
    REWRITE_TAC[REAL_OF_NUM_SUM_NUMSEG] THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    BETA_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MP_TAC(ISPECL [`\r. log(&(d r + 1) * (H:num->real) r pow 3)`; `1..n`;
                   `r:num`] SUM_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> y = s - x ==> x <= s`) THEN
    MATCH_MP_TAC SUM_POS_LE THEN REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_DELETE; IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC LOG_POS THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
      is_forall(concl th) && free_in `a:num->num->real` (concl th) &&
      free_in `lg:num->complex` (concl th))) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_1_MUL THEN
    CONJ_TAC THENL [REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= M /\ &0 <= M /\ &n <= M /\ &Dm <= M /\ Lam <= M /\
                cH <= M /\ log(inv lmin) <= M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN
    SUBGOAL_THEN `Lam <= &1 + (Mb:real)` MP_TAC THENL
     [EXPAND_TAC "Lam" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ASSUME `(cH:real) <= Mb`) THEN
    MP_TAC(ASSUME `log(inv lmin) = Mb`) THEN
    MP_TAC(ASSUME `&1 <= (Mb:real)`) THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
    MP_TAC(SPEC `Dm:num` REAL_POS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term (fun t -> try fst(dest_const t) = "baker_qreq"
                             with Failure _ -> false)) (concl th))) THEN
  ASM_REWRITE_TAC[baker_qreq] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_MAX_LE]) THEN
  SUBGOAL_THEN `&112 <= log(&q)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(SPEC `&112` LOG_EXP)) THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[REAL_EXP_POS_LT];
    ALL_TAC] THEN
  ABBREV_TAC `Q = &q pow (baker_e1 n Dm + 1)` THEN
  ABBREV_TAC `AG = log G0 + log CA + &Ex * log(&1 + &Dx)` THEN
  ABBREV_TAC
   `cL = &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1))` THEN
  ABBREV_TAC `AGb = log G0 + &E * Mb + &Ex * log(&1 + &Dx)` THEN
  SUBGOAL_THEN `&0 <= &E * Mb /\ (AG:real) <= AGb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["AG"; "AGb"] THEN
    MATCH_MP_TAC(REAL_ARITH `(x:real) <= y ==> g + x + z <= g + y + z`) THEN
    TRANS_TAC REAL_LE_TRANS `SA:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["CA"; "SA"] THEN MATCH_MP_TAC LOG_CA_LE_SA THEN
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
      is_forall(concl th) && free_in `a:num->num->real` (concl th) &&
      free_in `lg:num->complex` (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0 <= log(&(baker_kpar n Dm q)) /\ &0 <= log G0 /\
                 &0 <= &Ex * log(&Dx + &1)) /\ &0 <= AG /\ &0 <= cL`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC LOG_POS THEN REWRITE_TAC[REAL_OF_NUM_LE; baker_kpar] THEN
        REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
        SUBGOAL_THEN `&2176 <= &q` MP_TAC THENL
         [MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `&2176 * M pow 3 * &2 pow baker_J n Dm` THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &2176 <= &2176 * x`) THEN
          MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC THEN
          MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC];
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC];
      STRIP_TAC THEN CONJ_TAC THENL
       [EXPAND_TAC "AG" THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
          MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC];
        EXPAND_TAC "cL" THEN MATCH_MP_TAC REAL_LE_MUL THEN
        REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 <= d ==> &0 <= a + b + c +
           d`) THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE]]];
    ALL_TAC] THEN
  ABBREV_TAC `K0 = M + log(&(baker_kpar n Dm q)) + log G0 + &1 +
                   AGb + cL + &E * Mb + &Ex * log(&Dx + &1)` THEN
  ABBREV_TAC `K1 = &Ex + &3 * &Dm * &Ex + &3 * &Ex` THEN
  ABBREV_TAC `ch = &2 * K0 + K1` THEN
  SUBGOAL_THEN `Q * ch + &3 * &Dm * &Ex + &2 * Q + &2 * cL <= &C`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> try fst(dest_const t) = "baker_cexp"
                               with Failure _ -> false)) (concl th))) THEN
    REWRITE_TAC[baker_cexp] THEN
    MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> x <= c ==> y <= c`) THEN
    MAP_EVERY EXPAND_TAC ["ch"; "K0"; "K1"; "Q"; "cL"; "AGb"; "M";
                          "Dm"; "E"; "Ex"] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`B:real`; `theta:num->complex`;
                       `g:num->(num->complex)->complex`; `dx:num->num`;
                       `ax:num->num->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `&0 < B /\ &1 <= B /\ &1 / &2 <= log B /\ &0 <= log B`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[REAL_ARITH `&2 <= B ==> &0 < B /\ &1 <= B`; ASSUME `&2 <= B`] THEN
    MATCH_MP_TAC(REAL_ARITH `&1 / &2 <= y ==> &1 / &2 <= y /\ &0 <= y`) THEN
    TRANS_TAC REAL_LE_TRANS `log(&2)` THEN
      REWRITE_TAC[CONJUNCT1 LOG_2_BOUNDS] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `m:num`; `a:num->num->real`; `d:num->num`;
                 `H:num->real`; `e:num->num`; `G0:real`; `Dx:num`; `B:real`;
                 `theta:num->complex`; `g:num->(num->complex)->complex`;
                 `dx:num->num`; `ax:num->num->real`] BAKER_EXTRA_BOUNDS) THEN
  ANTS_TAC THENL
   [SIMP_TAC[ASSUME `!r. r IN 1..n ==> theta r = cexp(lg r)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= G0 * CA * ((&1 + &Dx) * B) pow Ex` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `log(G0 * CA * ((&1 + &Dx) * B) pow Ex) = AG + &Ex * log B`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < G0 /\ &0 < CA /\ &0 < &1 + &Dx /\ &0 < (&1 + &Dx) * B /\
                  &0 < ((&1 + &Dx) * B) pow Ex /\
                  &0 < CA * ((&1 + &Dx) * B) pow Ex`
     (fun th -> SIMP_TAC[LOG_MUL; LOG_POW; th; ASSUME `&0 < B`]) THENL
     [REPEAT CONJ_TAC THEN
      TRY(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LT) THEN
      TRY(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "AG" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Gn = G0 * CA * ((&1 + &Dx) * B) pow Ex` THEN
  ABBREV_TAC `LB = exp(--(cL + &3 * &Dm * &Ex * log B))` THEN
  SUBGOAL_THEN `LB <= norm((g:num->(num->complex)->complex) n theta) /\ &0 < LB`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "LB" THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `(a:real) <= x ==> b <= a ==> b <= x`) o check (fun th ->
      is_binary "real_le" (concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "exp"
                               with Failure _ -> false)) (lhand(concl th)) &&
      can (find_term ((=) `(g:num->(num->complex)->complex) n theta`))
          (concl th))) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    SUBGOAL_THEN
     `cL + &3 * &Dm * &Ex * log B =
      &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * (log(&Dx + &1) + &3 * log B))`
    SUBST1_TAC THENL [EXPAND_TAC "cL" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `&0 <= &Ex * (log(&Dx + &1) + &3 * log B) /\
                  &0 <= log(&(nproduct(1..n) (d:num->num) * Dx EXP m)) /\
                  log(&(nproduct(1..n) (d:num->num) * Dx EXP m)) <=
                  log(&Dm)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> &0 <= a + &3 * b`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
        MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
        MATCH_MP_TAC LOG_MONO_LE_IMP THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ASSUME `&0 <= SA`) THEN MP_TAC(ASSUME `SA <= &E * Mb`) THEN
    MP_TAC(ASSUME `&0 <= log G0`) THEN
    MP_TAC(ASSUME `&0 <= &Ex * (log(&Dx + &1) + &3 * log B)`) THEN
    MP_TAC(ASSUME `&0 <= log(&(nproduct(1..n) (d:num->num) * Dx EXP m))`) THEN
    MP_TAC(ASSUME `log(&(nproduct(1..n) (d:num->num) * Dx EXP m)) <=
                   log(&Dm)`) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bb = &1 + Gn * exp(cL + &3 * &Dm * &Ex * log B)` THEN
  SUBGOAL_THEN
   `&1 <= Bb /\
    !j. j < n ==> norm(--((g:num->(num->complex)->complex) j theta) /
                       g n theta) <= Bb`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Bb" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_DIV; NORM_NEG; real_div] THEN
    EXPAND_TAC "Bb" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= &1 + y`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[NORM_POS_LE] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "product"
                        with Failure _ -> false)) (concl th) = false &&
        can (find_term ((=) `Gn:real`)) (concl th))) THEN
      UNDISCH_TAC `j < n` THEN ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[NORM_POS_LE];
      TRANS_TAC REAL_LE_TRANS `inv LB` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "LB" THEN REWRITE_TAC[REAL_EXP_NEG; REAL_INV_INV] THEN
        REWRITE_TAC[REAL_LE_REFL]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K0 /\ &1 <= K0 /\ &0 <= K1` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &Dm * &Ex` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`&1 <= M`; `&0 <= log(&(baker_kpar n Dm q))`; `&0 <= log G0`;
      `&0 <= AG`; `&0 <= cL`; `&0 <= SA`; `&0 <= &Ex * log(&Dx + &1)`;
      `(AG:real) <= AGb`; `SA <= &E * Mb`; `&0 <= &E * Mb`] THEN
    MAP_EVERY EXPAND_TAC ["K0"; "K1"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `ch * log B` REAL_NUM_CEIL) THEN ANTS_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN EXPAND_TAC "ch" THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `h:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `K0 + K1 * log B <= &h` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `ch * log B` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`K0:real`; `&1 / &2`; `log B`] REAL_LE_LMUL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ch" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `K1 * log B = &Ex * log B + &3 * (&Dm * &Ex * log B) + &3 * (&Ex * log B) /\
    &0 <= &Ex * log B /\ &0 <= &Dm * &Ex * log B`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `log Bb <= &1 + log Gn + cL + &3 * &Dm * &Ex * log B`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= exp(cL + &3 * &Dm * &Ex * log B)` ASSUME_TAC THENL
     [MP_TAC(SPEC `cL + &3 * &Dm * &Ex * log B` REAL_EXP_LE_X) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 <= Gn * exp(cL + &3 * &Dm * &Ex * log B)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `log(&2 * (Gn * exp(cL + &3 * &Dm * &Ex *
      log B)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP THEN EXPAND_TAC "Bb" THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < Gn /\ &0 < exp(cL + &3 * &Dm * &Ex * log B)`
     (fun th -> SIMP_TAC[LOG_MUL; REAL_LT_MUL; LOG_EXP; th;
                         REAL_ARITH `&0 < &2`]) THENL
     [REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC LOG_2_LE_1 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `norm(--((g:num->(num->complex)->complex) 0 theta) / g n theta +
         vsum(1..n-1) (\r. --(g r theta) / g n theta * (lg:num->complex) r) -
         lg n) = norm((g:num->(num->complex)->complex) 0 theta +
           vsum(1..n) (\r. g r theta * (lg:num->complex) r)) / norm(g n theta)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `--((g:num->(num->complex)->complex) 0 theta) / g n theta +
      vsum(1..n-1) (\r. --(g r theta) / g n theta * (lg:num->complex) r) -
      lg n = --(g 0 theta + vsum(1..n) (\r. g r theta * lg r)) / g n theta`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `vsum(1..n-1) (\r. --((g:num->(num->complex)->complex) r theta) /
         g n theta * (lg:num->complex) r) =
        vsum(1..n-1) (\r. g r theta * lg r) * --inv(g n theta)`
      SUBST1_TAC THENL
       [SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
        MATCH_MP_TAC VSUM_EQ THEN REPEAT STRIP_TAC THEN BETA_TAC THEN
        REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`\r. (g:num->(num->complex)->complex) r theta *
        (lg:num->complex) r`; `1`; `n:num`]
                    VSUM_CLAUSES_RIGHT) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `1 <= n` THEN ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      BETA_TAC THEN
      UNDISCH_TAC `~((g:num->(num->complex)->complex) n theta = Cx(&0))` THEN
        CONV_TAC COMPLEX_FIELD;
      REWRITE_TAC[COMPLEX_NORM_DIV; NORM_NEG]];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm((g:num->(num->complex)->complex) 0 theta +
    vsum(1..n) (\r. g r theta * (lg:num->complex) r)) /
    norm((g:num->(num->complex)->complex) n theta) <= exp(--(Q *
    &h))` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= Q /\ &0 <= &2 * Q + &2 * cL` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= x /\ &0 <= &2 * x +
        &2 * y`) THEN
      CONJ_TAC THENL [SIMP_TAC[REAL_POW_LE; REAL_POS]; FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `inv(B pow C) * inv LB` THEN CONJ_TAC THENL
     [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
      REWRITE_TAC[NORM_POS_LE] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_INV THEN REWRITE_TAC[NORM_POS_LE];
        MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `inv(B pow C) * inv LB =
                  exp(--(&C * log B) + (cL + &3 * &Dm * &Ex * log B))`
    SUBST1_TAC THENL
     [EXPAND_TAC "LB" THEN
      REWRITE_TAC[REAL_EXP_ADD; REAL_EXP_NEG; REAL_INV_INV] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[REAL_EXP_N; EXP_LOG; ASSUME `&0 < B`];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    SUBGOAL_THEN `Q * &h <= Q * (ch * log B + &1)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(Q * ch + &3 * &Dm * &Ex + &2 * Q + &2 * cL) * log B <=
                  &C * log B` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(&2 * Q + &2 * cL) * (&1 / &2) <=
                  (&2 * Q + &2 * cL) * log B` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`n:num`; `lg:num->complex`; `theta:num->complex`; `1..(n + m)`;
    `g:num->(num->complex)->complex`; `e:num->num`; `G0:real`;
    `\r. if r <= n then (a:num->num->real) r else ax r`;
    `\r. if r <= n then (d:num->num) r else dx r`;
    `\r. if r <= n then (H:num->real) r else B`;
    `\j. --((g:num->(num->complex)->complex) j theta) / g n theta`;
    `Bb:real`; `Lam:real`; `norm((g:num->(num->complex)->complex) 0 theta +
      vsum(1..n) (\r. g r theta * (lg:num->complex) r)) /
      norm((g:num->(num->complex)->complex) n theta)`; `lmin:real`;
    `Gn:real`; `M:real`; `q:num`; `h:num`; `Dm:num`]
   BAKER_CORE_NUMERIC_DMAX) THEN
  BETA_TAC THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  SUBGOAL_THEN `!x. x <= K0 + K1 * log B ==> x <= &h` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH `(b:real) <= c ==> a <= b ==> a <=
     c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= K1 * log B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `M <= K0 /\ log(&(baker_kpar n Dm q)) <= K0 /\ log G0 <= K0 /\
    &1 + AG + cL <= K0 /\ SA + &Ex * log(&Dx + &1) <= K0 /\ &1 <= K0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`&1 <= M`; `&0 <= log(&(baker_kpar n Dm q))`; `&0 <= log G0`;
      `&0 <= AG`; `&0 <= cL`; `&0 <= SA`; `&0 <= &Ex * log(&Dx + &1)`;
      `(AG:real) <= AGb`; `SA <= &E * Mb`; `&0 <= &E * Mb`] THEN
    EXPAND_TAC "K0" THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `K1 * log B = &Ex * log B + &3 * (&Dm * &Ex * log B) + &3 * (&Ex * log B)`
  ASSUME_TAC THENL
   [EXPAND_TAC "K1" THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC;
    ASM_SIMP_TAC[LE_REFL];
    REPEAT STRIP_TAC THEN
      UNDISCH_TAC `~((g:num->(num->complex)->complex) n theta = Cx(&0))` THEN
    CONV_TAC COMPLEX_FIELD;
    X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `r <= n` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `(r:num) IN 1..n` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
      SUBGOAL_THEN `(theta:num->complex) r = cexp((lg:num->complex) r)`
      SUBST1_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && free_in `theta:num->complex` (concl th) &&
          free_in `lg:num->complex` (concl th) &&
          not(free_in `a:num->num->real` (concl th)))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && free_in `a:num->num->real` (concl th) &&
        free_in `lg:num->complex` (concl th))) THEN
      ASM_REWRITE_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        is_forall(concl th) && free_in `ax:num->num->real` (concl th))) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_NUMSEG] THEN
        MAP_EVERY UNDISCH_TAC [`~(r <= n)`; `r <= n + m`] THEN ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    EXPAND_TAC "Lam" THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
    MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN EXPAND_TAC "Lam" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= &1 + y`) THEN
    MP_TAC(ISPECL [`\r. norm((lg:num->complex) r)`; `1..n`; `r:num`]
                  SUM_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN BETA_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> y = s - x ==> x <= s`) THEN
    MATCH_MP_TAC SUM_POS_LE THEN
    REWRITE_TAC[FINITE_DELETE; FINITE_NUMSEG; NORM_POS_LE];
    EXPAND_TAC "Lam" THEN REAL_ARITH_TAC;
    TRANS_TAC LE_TRANS `nproduct(1..n) (d:num->num) * Dx EXP m` THEN
    ASM_REWRITE_TAC[];
    TRANS_TAC REAL_LE_TRANS `cH:real` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "cH" THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[];
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ASSUME `&1 <= K0`) THEN MP_TAC(ASSUME `&0 <= K1 * log B`) THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ASSUME `(M:real) <= K0`) THEN MP_TAC(ASSUME `&0 <= K1 * log B`) THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ASSUME `log(&(baker_kpar n Dm q)) <= K0`) THEN
    MP_TAC(ASSUME `&0 <= K1 * log B`) THEN REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ASSUME `log G0 <= K0`) THEN MP_TAC(ASSUME `&0 <= K1 * log B`) THEN
    REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ASSUME `log Bb <= &1 + log Gn + cL + &3 * &Dm * &Ex * log B`) THEN
    MP_TAC(ASSUME `log Gn = AG + &Ex * log B`) THEN
    MP_TAC(ASSUME `&1 + AG + cL <= K0`) THEN
    MP_TAC(ASSUME `K1 * log B = &Ex * log B + &3 * (&Dm * &Ex * log B) +
                                &3 * (&Ex * log B)`) THEN
    MP_TAC(ASSUME `&0 <= &Ex * log B`) THEN REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN
    MP_TAC(ASSUME `&1 + AG + cL <= K0`) THEN
    MP_TAC(ASSUME `&0 <= cL`) THEN
    MP_TAC(ASSUME `K1 * log B = &Ex * log B + &3 * (&Dm * &Ex * log B) +
                                &3 * (&Ex * log B)`) THEN
    MP_TAC(ASSUME `&0 <= &Ex * log B`) THEN
    MP_TAC(ASSUME `&0 <= &Dm * &Ex * log B`) THEN REAL_ARITH_TAC;
    FIRST_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `SA + &Ex * (log(&Dx + &1) + &3 * log B)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `SA + &Ex * log(&Dx + &1) <= K0`) THEN
    MP_TAC(ASSUME `K1 * log B = &Ex * log B + &3 * (&Dm * &Ex * log B) +
                                &3 * (&Ex * log B)`) THEN
    MP_TAC(ASSUME `&0 <= &Ex * log B`) THEN
    MP_TAC(ASSUME `&0 <= &Dm * &Ex * log B`) THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* The core lower bound with an existential exponent: for logarithms         *)
(* without any nontrivial integer relation, choose Mb, q and C in            *)
(* BAKER_CORE_EXPLICIT.                                                      *)
(* ------------------------------------------------------------------------- *)

let INDEPENDENT_IMP_SMALL = prove
 (`!n (lg:num->complex) X.
     (!b. (!r. r IN 1..n ==> integer(b r)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0)
     ==> !b. (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= X) /\
             vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
             ==> !r. r IN 1..n ==> b r = &0`,
  MESON_TAC[]);;

let LOGS_NONZERO_OF_INDEPENDENT = prove
 (`!n (lg:num->complex).
     (!b. (!r. r IN 1..n ==> integer(b r)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0)
     ==> !r. r IN 1..n ==> ~(lg r = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `s:num` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o BETA_RULE o SPEC `\r:num. if r =
    s then &1 else &0`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
      REWRITE_TAC[INTEGER_CLOSED];
      REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]];
    DISCH_THEN(MP_TAC o SPEC `s:num`) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

let LMIN_EXISTS = prove
 (`!n (lg:num->complex).
     1 <= n /\ (!r. r IN 1..n ==> ~(lg r = Cx(&0)))
     ==> ?lmin. &0 < lmin /\ lmin <= &1 /\
                !r. r IN 1..n ==> lmin <= norm(lg r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\r. norm((lg:num->complex) r)) (1..n)` INF_FINITE) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
           FORALL_IN_IMAGE; IN_IMAGE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r0:num` STRIP_ASSUME_TAC)
                             ASSUME_TAC) THEN
  EXISTS_TAC
   `min (&1) (inf (IMAGE (\r. norm((lg:num->complex) r)) (1..n)))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ASM_SIMP_TAC[NORM_POS_LT; COMPLEX_VEC_0]];
    REAL_ARITH_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> min (&1) y <= z`) THEN
    ASM_SIMP_TAC[]]);;

let BAKER_CORE_EXISTS = prove
 (`!n m lg (a:num->num->real) (d:num->num) (H:num->real) (e:num->num) G0 Dx.
     1 <= n /\ 1 <= Dx /\ &1 <= G0 /\
     (!r. r IN 1..n
          ==> 1 <= d r /\ &1 <= H r /\
              (!j. integer(a r j) /\ abs(a r j) <= H r) /\
              ~(a r (d r) = &0) /\
              vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)) /\
     (!b. (!r. r IN 1..n ==> integer(b r)) /\
          vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
          ==> !r. r IN 1..n ==> b r = &0)
     ==> ?C. !B (theta:num->complex) (g:num->(num->complex)->complex)
               (dx:num->num) (ax:num->num->real).
           &2 <= B /\
           (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
           (!r. r IN (n + 1)..(n + m)
                ==> 1 <= dx r /\ dx r <= Dx /\
                    (!j. integer(ax r j) /\ abs(ax r j) <= B) /\
                    ~(ax r (dx r) = &0) /\
                    vsum(0..dx r) (\j. Cx(ax r j) * theta r pow j) = Cx(&0)) /\
           (!j. j <= n ==> intpoly (1..(n + m)) e G0 (g j)) /\
           ~(g n theta = Cx(&0))
           ==> inv(B pow C) <=
               norm(g 0 theta + vsum(1..n) (\r. g r theta * lg r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `lg:num->complex`] LOGS_NONZERO_OF_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `lg:num->complex`] LMIN_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lmin:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `cH = sum(1..n) (\r. log(&(d r + 1) * (H:num->real) r pow 3))` THEN
  ABBREV_TAC `Lam = sum(1..n) (\r. norm((lg:num->complex) r))` THEN
  SUBGOAL_THEN `&0 <= cH /\ &0 <= Lam /\ &0 <= log(inv lmin)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "cH" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN BETA_TAC THEN
      MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_LE_1_MUL THEN
      REWRITE_TAC[REAL_OF_NUM_LE; ARITH_RULE `1 <= x + 1`] THEN
      MATCH_MP_TAC REAL_POW_LE_1 THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        is_forall(concl th) && free_in `a:num->num->real` (concl th))) THEN
      ASM_REWRITE_TAC[IN_NUMSEG] THEN SIMP_TAC[];
      EXPAND_TAC "Lam" THEN MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN
      REWRITE_TAC[NORM_POS_LE];
      MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_INV_1_LE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `Mb = &1 + Lam + cH + log(inv lmin)` THEN
  ABBREV_TAC `Dm = nproduct(1..n) d * Dx EXP m` THEN
  MP_TAC(SPEC `baker_qreq n Dm (&4 * Mb + &n + &Dm + &2)` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `q:num`) THEN
  MP_TAC(SPEC `baker_cexp n Dm (nsum(1..n) e) (nsum((n + 1)..(n + m)) e)
                          G0 Dx Mb q` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `C:num`) THEN EXISTS_TAC `C:num` THEN
  MATCH_MP_TAC(SPECL
   [`n:num`; `m:num`; `lg:num->complex`; `a:num->num->real`; `d:num->num`;
    `H:num->real`; `e:num->num`; `G0:real`; `Dx:num`;
    `nproduct(1..n) (d:num->num)`; `Mb:real`; `q:num`; `C:num`]
   BAKER_CORE_EXPLICIT) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Mb" THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC INDEPENDENT_IMP_SMALL THEN FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `lmin:real` THEN CONJ_TAC THENL
     [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV
     [GSYM(MATCH_MP EXP_LOG (ASSUME `&0 < lmin`))] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    MP_TAC(MATCH_MP LOG_INV (ASSUME `&0 < lmin`)) THEN
    EXPAND_TAC "Mb" THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "Mb" THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "Mb" THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial growth of the explicit parameters in Mb.                       *)
(* ------------------------------------------------------------------------- *)

let BAKER_QREQ_POLY = prove
 (`!n Dm M. &1 <= M
            ==> baker_qreq n Dm M <=
                (exp(&112) + &2176 * &2 pow (baker_J n Dm) +
                 &(baker_c Dm * (n + 1)) * &83 * &6 pow (n + 3) *
                 &2 pow (baker_J n Dm + 1)) * M pow (n + 4)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_qreq] THEN
  ABBREV_TAC `J = baker_J n Dm` THEN ABBREV_TAC `cc = baker_c Dm` THEN
  SUBGOAL_THEN `&1 <= M pow (n + 4) /\ &1 <= M pow 3 /\
                M pow 3 <= M pow (n + 4) /\
                M pow (n + 3) * M <= M pow (n + 4)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
      REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ADD1; ARITH_RULE
       `(n + 3) + 1 = n + 4`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM(CONJUNCT2 real_pow); ADD1; ARITH_RULE
       `(n + 3) + 1 = n + 4`; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 pow J /\
                &0 <= &cc * &(n + 1) * &6 pow (n + 3) * &2 pow (J + 1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_MAX_LE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `exp(&112) * M pow (n + 4)` THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= b /\ &0 <= c ==> a <= a + b + c`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
          REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
          REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
          REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2176 * &2 pow J) * M pow (n + 4)` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[REAL_ARITH `&2176 * a * b = (&2176 * b) * a`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= c ==> b <= a + b + c`) THEN
        REWRITE_TAC[REAL_EXP_POS_LE; GSYM REAL_OF_NUM_MUL] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
        REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]];
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&(cc * (n + 1)) * &83 * &6 pow (n + 3) * &2 pow (J + 1)) *
                M pow (n + 4)` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `&(cc * (n + 1)) * (&8 * M + &75) * (&6 * M) pow (n + 3) *
        &2 pow (J + 1) =
        (&(cc * (n + 1)) * &6 pow (n + 3) * &2 pow (J + 1)) *
        ((&8 * M + &75) * M pow (n + 3))`
      SUBST1_TAC THENL [REWRITE_TAC[REAL_POW_MUL] THEN REAL_ARITH_TAC;
                        ALL_TAC] THEN
      SUBGOAL_THEN
       `(&(cc * (n + 1)) * &83 * &6 pow (n + 3) * &2 pow (J + 1)) *
        M pow (n + 4) =
        (&(cc * (n + 1)) * &6 pow (n + 3) * &2 pow (J + 1)) *
        (&83 * M pow (n + 4))`
      SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
        REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
        REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `(&83 * M) * M pow (n + 3)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
        MP_TAC(ASSUME `M pow (n + 3) * M <= M pow (n + 4)`) THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b ==> c <= a + b + c`) THEN
        REWRITE_TAC[REAL_EXP_POS_LE] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC]]]);;

let BAKER_CEXP_POLY = prove
 (`!n Dm E Ex G0 Dx Bq.
     1 <= Dm /\ &1 <= G0 /\ &0 <= Bq
     ==> ?c. !Mb q. &1 <= Mb /\ 1 <= q /\ &q <= Bq * Mb pow (n + 4)
                    ==> baker_cexp n Dm E Ex G0 Dx Mb q + &1 <=
                        c * Mb pow ((n + 4) * (baker_e1 n Dm + 2))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e1 = baker_e1 n Dm` THEN
  ABBREV_TAC `kk = baker_c Dm * (n + 1)` THEN
  ABBREV_TAC `A = &n + &Dm + &2 + log G0 + &1 + log G0 +
                  &Ex * log(&1 + &Dx) +
                  &Dm * (log(&Dm) + log G0 + &Ex * log(&Dx + &1)) +
                  &Ex * log(&Dx + &1)` THEN
  ABBREV_TAC `Bc = &4 + &E + &Dm * &E + &E` THEN
  ABBREV_TAC `Lc0 = &Dm * (log(&Dm) + log G0 + &Ex * log(&Dx + &1))` THEN
  ABBREV_TAC `K1 = &Ex + &3 * &Dm * &Ex + &3 * &Ex` THEN
  ABBREV_TAC `Kc = A + Bc + &kk * Bq` THEN
  ABBREV_TAC `Lc = Lc0 + &Dm * &E` THEN
  SUBGOAL_THEN `&0 <= A /\ &0 <= Bc /\ &0 <= Lc0 /\ &0 <= K1 /\ &0 <= Kc /\
                &0 <= Lc /\ &0 <= Bq pow (e1 + 1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= log G0 /\ &0 <= log(&Dm) /\ &0 <= log(&1 + &Dx) /\
                  &0 <= log(&Dx + &1)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &Ex * log(&1 + &Dx) /\ &0 <= &Ex * log(&Dx + &1) /\
                  &0 <= &Dm * &E /\ &0 <= &kk * Bq`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_POS];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= Lc0` ASSUME_TAC THENL
     [EXPAND_TAC "Lc0" THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &Dm * &Ex` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= A /\ &0 <= Bc` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A"; "Bc"] THEN
      MP_TAC(ASSUME `&0 <= Lc0`) THEN EXPAND_TAC "Lc0" THEN
      MP_TAC(SPEC `n:num` REAL_POS) THEN MP_TAC(SPEC `Dm:num` REAL_POS) THEN
      MP_TAC(SPEC `E:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [EXPAND_TAC "K1" THEN MP_TAC(SPEC `Ex:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Kc" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "Lc" THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `Bq pow (e1 + 1) * (&2 * Kc + K1) + &3 * &Dm * &Ex +
              &2 * Bq pow (e1 + 1) + &2 * Lc + &1` THEN
  MAP_EVERY X_GEN_TAC [`Mb:real`; `q:num`] THEN STRIP_TAC THEN
  ABBREV_TAC `P = Mb pow (n + 4)` THEN
  ABBREV_TAC `Qx = Mb pow ((n + 4) * (e1 + 1))` THEN
  SUBGOAL_THEN `Mb pow ((n + 4) * (e1 + 2)) = Qx * P` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Qx"; "P"] THEN REWRITE_TAC[GSYM REAL_POW_ADD] THEN
    AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= P /\ &1 <= Qx /\ Mb <= (P:real)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["P"; "Qx"] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&q pow (e1 + 1) <= Bq pow (e1 + 1) * Qx` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(Bq * P) pow (e1 + 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
      MAP_EVERY EXPAND_TAC ["Qx"; "P"] THEN
      REWRITE_TAC[REAL_POW_MUL; REAL_POW_POW; REAL_LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(&(baker_kpar n Dm q)) <= &kk * Bq * P` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[baker_kpar; GSYM REAL_OF_NUM_POW] THEN
    SUBGOAL_THEN `&0 < &q` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[LOG_POW] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    REWRITE_TAC[REAL_POS] THEN TRANS_TAC REAL_LE_TRANS `&q` THEN
    ASM_SIMP_TAC[LOG_LE_SELF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 * Mb + &n + &Dm + &2) + log(&(baker_kpar n Dm q)) + log G0 + &1 +
    (log G0 + &E * Mb + &Ex * log(&1 + &Dx)) +
    &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1)) +
    &E * Mb + &Ex * log(&Dx + &1) <= Kc * P`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(A:real) <= A * P /\ (Bc:real) * Mb <= Bc * P`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ASSUME `log(&(baker_kpar n Dm q)) <= &kk * Bq * P`) THEN
    MP_TAC(ASSUME `(A:real) <= A * P`) THEN
    MP_TAC(ASSUME `(Bc:real) * Mb <= Bc * P`) THEN
    MAP_EVERY EXPAND_TAC ["Kc"; "A"; "Bc"; "Lc0"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1)) <= Lc * P`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(Lc0:real) <= Lc0 * P /\ (&Dm * &E) * Mb <= (&Dm * &E) * P`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS]];
      ALL_TAC] THEN
    MP_TAC(ASSUME `(Lc0:real) <= Lc0 * P`) THEN
    MP_TAC(ASSUME `(&Dm * &E) * Mb <= (&Dm * &E) * P`) THEN
    MAP_EVERY EXPAND_TAC ["Lc"; "Lc0"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `K0 = (&4 * Mb + &n + &Dm + &2) + log(&(baker_kpar n Dm q)) + log G0 +
         &1 + (log G0 + &E * Mb + &Ex * log(&1 + &Dx)) +
         &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1)) +
         &E * Mb + &Ex * log(&Dx + &1)` THEN
  ABBREV_TAC
   `cL = &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1))` THEN
  ABBREV_TAC `Q = &q pow (e1 + 1)` THEN
  SUBGOAL_THEN
   `baker_cexp n Dm E Ex G0 Dx Mb q =
    Q * (&2 * K0 + K1) + &3 * &Dm * &Ex + &2 * Q + &2 * cL`
  SUBST1_TAC THENL
   [REWRITE_TAC[baker_cexp] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXPAND_TAC ["Q"; "K0"; "K1"; "cL"] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Q /\ &0 <= K0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [EXPAND_TAC "Q" THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
                    ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= log(&(baker_kpar n Dm q)) /\ &0 <= log G0 /\
                  &0 <= log(&1 + &Dx) /\ &0 <= log(&Dx + &1) /\ &0 <= log(&Dm)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN TRY REAL_ARITH_TAC THEN
      ASM_REWRITE_TAC[baker_kpar; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                      EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= &E * Mb /\ &0 <= &Ex * log(&1 + &Dx) /\
                  &0 <= &Ex * log(&Dx + &1)` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= cL` ASSUME_TAC THENL
     [EXPAND_TAC "cL" THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "K0" THEN MP_TAC(SPEC `n:num` REAL_POS) THEN
    MP_TAC(SPEC `Dm:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Q * (&2 * K0 + K1) <= (Bq pow (e1 + 1) * (&2 * Kc + K1)) * (Qx * P)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `(Bq pow (e1 + 1) * Qx) * ((&2 * Kc + K1) * P)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(K1:real) <= K1 * P` MP_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
        MP_TAC(ASSUME `(K0:real) <= Kc * P`) THEN REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * Q <= (&2 * Bq pow (e1 + 1)) * (Qx * P) /\
    &3 * &Dm * &Ex <= (&3 * &Dm * &Ex) * (Qx * P) /\
    &2 * cL <= (&2 * Lc) * (Qx * P) /\ &1 <= &1 * (Qx * P)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&1 <= Qx * P /\ (Qx:real) <= Qx * P /\ (P:real) <= Qx * P`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[];
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `Bq pow (e1 + 1) * Qx <= Bq pow (e1 + 1) * (Qx * P)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ASSUME `(Q:real) <= Bq pow (e1 + 1) * Qx`) THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS];
      SUBGOAL_THEN `(Lc:real) * P <= Lc * (Qx * P)` MP_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ASSUME `(cL:real) <= Lc * P`) THEN REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t))
   [`Q * (&2 * K0 + K1) <= (Bq pow (e1 + 1) * (&2 * Kc + K1)) * (Qx * P)`;
    `&2 * Q <= (&2 * Bq pow (e1 + 1)) * (Qx * P)`;
    `&3 * &Dm * &Ex <= (&3 * &Dm * &Ex) * (Qx * P)`;
    `&2 * cL <= (&2 * Lc) * (Qx * P)`; `&1 <= &1 * (Qx * P)`] THEN
  REAL_ARITH_TAC);;

let BAKER_CEXP_POS = prove
 (`!n Dm E Ex G0 Dx Mb q.
     1 <= Dm /\ &1 <= G0 /\ &0 <= Mb /\ 1 <= q
     ==> &0 <= baker_cexp n Dm E Ex G0 Dx Mb q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_cexp] THEN
  SUBGOAL_THEN `&0 <= log(&(baker_kpar n Dm q)) /\ &0 <= log G0 /\
                &0 <= log(&1 + &Dx) /\ &0 <= log(&Dx + &1) /\ &0 <= log(&Dm)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC LOG_POS THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN TRY REAL_ARITH_TAC THEN
    ASM_REWRITE_TAC[baker_kpar; ARITH_RULE `1 <= x <=> ~(x = 0)`;
                    EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &E * Mb /\ &0 <= &Ex * log(&1 + &Dx) /\
                &0 <= &Ex * log(&Dx + &1) /\ &0 <= &Dm * &Ex`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  ABBREV_TAC `Q = &q pow (baker_e1 n Dm + 1)` THEN
  ABBREV_TAC
   `cL = &Dm * (log(&Dm) + log G0 + &E * Mb + &Ex * log(&Dx + &1))` THEN
  SUBGOAL_THEN `&0 <= Q /\ &0 <= cL` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "Q" THEN SIMP_TAC[REAL_POW_LE; REAL_POS];
      EXPAND_TAC "cL" THEN MATCH_MP_TAC REAL_LE_MUL THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= Q * x /\ &0 <= y /\ &0 <= Q /\ &0 <= cL
    ==> &0 <= Q * x + y + &2 * Q + &2 * cL`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `n:num` REAL_POS) THEN MP_TAC(SPEC `Dm:num` REAL_POS) THEN
    MP_TAC(SPEC `Ex:num` REAL_POS) THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The uniform bound.                                                        *)
(* ------------------------------------------------------------------------- *)

let BAKER_CORE_UNIFORM = prove
 (`!n m (e:num->num) G0 Dx Dmax.
     1 <= n /\ 1 <= Dx /\ &1 <= G0 /\ 1 <= Dmax
     ==> ?c kappa cr kr.
           !Mb lg (a:num->num->real) (d:num->num) (H:num->real) B
            (theta:num->complex) (g:num->(num->complex)->complex)
            (dx:num->num) (ax:num->num->real).
             &1 <= Mb /\ nproduct(1..n) d <= Dmax /\
             (!r. r IN 1..n
                  ==> 1 <= d r /\ &1 <= H r /\
                      (!j. integer(a r j) /\ abs(a r j) <= H r) /\
                      ~(a r (d r) = &0) /\
                      vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) =
                      Cx(&0)) /\
             (!b. (!r. r IN 1..n
                       ==> integer(b r) /\ abs(b r) <= cr * Mb pow kr) /\
                  vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
                  ==> !r. r IN 1..n ==> b r = &0) /\
             (!r. r IN 1..n ==> exp(--Mb) <= norm(lg r)) /\
             sum(1..n) (\r. norm(lg r)) <= Mb /\
             sum(1..n) (\r. log(&(d r + 1) * H r pow 3)) <= Mb /\
             &2 <= B /\
             (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
             (!r. r IN (n + 1)..(n + m)
                  ==> 1 <= dx r /\ dx r <= Dx /\
                      (!j. integer(ax r j) /\ abs(ax r j) <= B) /\
                      ~(ax r (dx r) = &0) /\
                      vsum(0..dx r) (\j. Cx(ax r j) * theta r pow j) =
                      Cx(&0)) /\
             (!j. j <= n ==> intpoly (1..(n + m)) e G0 (g j)) /\
             ~(g n theta = Cx(&0))
             ==> exp(--(c * Mb pow kappa * log B)) <=
                 norm(g 0 theta + vsum(1..n) (\r. g r theta * lg r))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Dm = Dmax * Dx EXP m` THEN
  SUBGOAL_THEN `1 <= Dm` ASSUME_TAC THENL
   [EXPAND_TAC "Dm" THEN
    REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `Aq = exp(&112) + &2176 * &2 pow (baker_J n Dm) +
         &(baker_c Dm * (n + 1)) * &83 * &6 pow (n + 3) *
         &2 pow (baker_J n Dm + 1)` THEN
  SUBGOAL_THEN `&0 <= Aq` ASSUME_TAC THENL
   [EXPAND_TAC "Aq" THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c ==> &0 <= a + b + c`) THEN
    REWRITE_TAC[REAL_EXP_POS_LE] THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `Bq = (Aq + &1) * (&n + &Dm + &6) pow (n + 4)` THEN
  SUBGOAL_THEN `&0 <= Bq` ASSUME_TAC THENL
   [EXPAND_TAC "Bq" THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `Dm:num`; `nsum(1..n) (e:num->num)`;
                `nsum((n + 1)..(n + m)) (e:num->num)`; `G0:real`; `Dx:num`;
                `Bq:real`] BAKER_CEXP_POLY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c:real`) THEN
  MAP_EVERY EXISTS_TAC
   [`c:real`; `(n + 4) * (baker_e1 n Dm + 2)`;
    `&2 * &Dm * Bq pow (baker_c Dm * n)`; `(n + 4) * (baker_c Dm * n)`] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `M = &4 * Mb + &n + &Dm + &2` THEN
  SUBGOAL_THEN `&1 <= M /\ M <= (&n + &Dm + &6) * Mb` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN CONJ_TAC THENL
     [MP_TAC(SPEC `n:num` REAL_POS) THEN MP_TAC(SPEC `Dm:num` REAL_POS) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&n <= &n * Mb /\ &Dm <= &Dm * Mb` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_POS];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= baker_qreq n Dm M` ASSUME_TAC THENL
   [REWRITE_TAC[baker_qreq] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= x ==> a <= max x y`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + &112` THEN
    REWRITE_TAC[REAL_EXP_LE_X] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `baker_qreq n Dm M` REAL_NUM_CEIL) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= q /\ &q <= Bq * Mb pow (n + 4)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `Dm:num`; `M:real`] BAKER_QREQ_POLY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 <= M pow (n + 4) /\
                  M pow (n + 4) <= ((&n + &Dm + &6) * Mb) pow (n + 4)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE_1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS `(Aq + &1) * M pow (n + 4)` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `baker_qreq n Dm M <= Aq * M pow (n + 4)`) THEN
      MP_TAC(ASSUME `&q < baker_qreq n Dm M + &1`) THEN
      MP_TAC(ASSUME `&1 <= M pow (n + 4)`) THEN REAL_ARITH_TAC;
      EXPAND_TAC "Bq" THEN REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[GSYM REAL_POW_MUL]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Mb:real`; `q:num`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= baker_cexp n Dm (nsum(1..n) e) (nsum((n + 1)..(n + m)) e) G0 Dx Mb q`
  ASSUME_TAC THENL
   [MATCH_MP_TAC BAKER_CEXP_POS THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC
   `baker_cexp n Dm (nsum(1..n) e) (nsum((n + 1)..(n + m)) e) G0 Dx Mb q`
   REAL_NUM_CEIL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `C:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!b. (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= &(baker_Lpar n Dm q)) /\
        vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)
        ==> !r. r IN 1..n ==> b r = &0`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SMALL_INDEPENDENT_MONO THEN
    EXISTS_TAC `(&2 * &Dm * Bq pow (baker_c Dm * n)) *
                Mb pow ((n + 4) * (baker_c Dm * n))` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[baker_Lpar; GSYM REAL_OF_NUM_MUL; GSYM REAL_OF_NUM_POW;
                GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    SUBGOAL_THEN `Mb pow ((n + 4) * (baker_c Dm * n)) =
                  (Mb pow (n + 4)) pow (baker_c Dm * n)` SUBST1_TAC THENL
     [REWRITE_TAC[REAL_POW_POW]; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_POW_MUL] THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `m:num`; `lg:num->complex`; `a:num->num->real`;
                `d:num->num`; `H:num->real`; `e:num->num`; `G0:real`;
                `Dx:num`; `Dmax:num`; `Mb:real`; `q:num`; `C:num`]
               BAKER_CORE_EXPLICIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`B:real`; `theta:num->complex`;
    `g:num->(num->complex)->complex`; `dx:num->num`; `ax:num->num->real`]) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= x ==> a <= x`) THEN
  SUBGOAL_THEN `&0 < B /\ &0 <= log B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC LOG_POS THEN
                    ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `inv(B pow C) = exp(--(&C * log B))` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_EXP_NEG] THEN AP_TERM_TAC THEN
    SIMP_TAC[REAL_EXP_N; EXP_LOG; ASSUME `&0 < B`];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;
