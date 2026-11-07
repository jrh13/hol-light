(* ========================================================================= *)
(* Sharpening I: uniform lower bounds for logarithms of bounded size with    *)
(* algebraic coefficients (the base case of both descents).                  *)
(*                                                                           *)
(* Purpose: for fixed n, Dmax and Dx there are c, kappa such that for all    *)
(* data baker_logdata n lg a d H Mb Dmax (alphas cexp(lg r) with degree      *)
(* product at most Dmax, each lg r zero or of size at least exp(-Mb), sizes  *)
(* and heights bounded by Mb) and all algebraic coefficients bb r of degree  *)
(* at most Dx and height at most B >= 2 (sharpc_coefdata n bb ab db B), the  *)
(* linear form Lambda = bb 1 lg 1 + ... + bb n lg n is 0 or                  *)
(* |Lambda| >= exp(-c Mb^kappa log B) (BAKER_UNIFORM_ALGCOEFF), without any  *)
(* independence hypothesis on the logarithms. This is the uniform base of    *)
(* both endings of Sharpening I: SHARPC_UNIFORM_ALG is the base case         *)
(* log A <= c7 g0^k7 of the descent of Baker/sharpc_descent.ml (it replaces  *)
(* the pigeonhole ending of Baker, A central theorem in transcendence        *)
(* theory (1973), sec. 4, which is not uniform in the data), and its integer *)
(* case SHARP_UNIFORM_ALG is the base case of the descent of                 *)
(* Baker/sharp_descent.ml (a vanishing last coefficient, or                  *)
(* log A <= 16 D^2 (n+1) g0).                                                *)
(*                                                                           *)
(* Method: induction on n with the degree bound Dx inside the induction      *)
(* statement, as BAKER_UNIFORM_INTEGER of Baker/uniform.ml. Without a small  *)
(* integer relation sum cc r lg r = 0 (|cc r| <= max 1 (cr Mb^kr), not all   *)
(* 0) the uniform core BAKER_CORE_UNIFORM_ALGCOEFF of Baker/uniform.ml       *)
(* applies. Otherwise a transposition puts an index with cc k <> 0 last, and *)
(* cc_n Lambda = sum_(r<n) (cc_n bb r - cc_r bb n) lg r                      *)
(* (SHARPC_VSUM_ELIMINATE_LAST of Baker/uniform.ml). The new coefficients    *)
(* lie in Q(bb r, bb n), of degree at most Dx^2                              *)
(* (COMPLEX_SUBFIELD_GENERATED_DEGREE), with denominator at most B^2 and     *)
(* conjugates at most 2 X (1 + Dx B) (sharp_nfbound: SHARP_NFBOUND_ROOT and  *)
(* SHARPC_NFBOUND_INT_LINEAR), hence they are roots of integer polynomials   *)
(* of degree at most Dx^2 and height at most (2 X B)^((Dx + 3) Dx^2)         *)
(* (COMPLEX_SUBFIELD_ELEMENT_POLY, SHARPC_ELIM_COEFF_POLY); the induction    *)
(* hypothesis at degree Dx^2 and RELATION_ABSORB give the bound. Vanishing   *)
(* terms need no separate case: lg r = 0 gives the small relation cc =       *)
(* delta_r, and the core requires only one nonzero coefficient. Then         *)
(* SHARPC_UNIFORM_ALG: the bound exp(-c G^k log B) for principal logarithms  *)
(* of algebraic numbers of degree at most D and classical height at most exp *)
(* G (sharp_algdata), with coefficients of degree at most D, through         *)
(* SHARPC_ALGDATA_LOGDATA (baker_logdata with Mb = M G, by                   *)
(* SHARP_LOG_ALG_SIZE); SHARP_UNIFORM_ALG is its case of integer             *)
(* coefficients, which are coefficient data of degree 1                      *)
(* (SHARPC_COEFDATA_INTEGER).                                                *)
(*                                                                           *)
(* Main results: BAKER_UNIFORM_ALGCOEFF, SHARPC_UNIFORM_ALG,                 *)
(* SHARP_UNIFORM_ALG; SHARPC_ELIM_COEFF_POLY, SHARPC_ALGDATA_LOGDATA,        *)
(* SHARPC_NFBOUND_ADD, SHARPC_NFBOUND_INT_CMUL, SHARPC_NFBOUND_INT_LINEAR,   *)
(* SHARPC_ELIM_HEIGHT_ARITH, SHARPC_ELIM_RADIUS_ARITH,                       *)
(* SHARPC_ELIM_POW_ARITH.                                                    *)
(*                                                                           *)
(* Uses: Baker/uniform.ml (sharpc_coefdata, SHARPC_COEFDATA_INTEGER,         *)
(* baker_logdata, BAKER_LOGDATA_PERMUTES, BAKER_LOGDATA_RESTRICT,            *)
(* VSUM_PERMUTE, EXP_BOUND_MONO, RELATION_ABSORB,                            *)
(* SHARPC_VSUM_ELIMINATE_LAST, BAKER_CORE_UNIFORM_ALGCOEFF),                 *)
(* Baker/sharp_defs.ml (sharp_algdata, sharp_nfbound), Baker/sharp_tools.ml  *)
(* (SHARP_NFBOUND_EMBEDDING, SHARP_NFBOUND_ROOT, SHARP_NFBOUND_MONO,         *)
(* SHARP_LOG_ALG_SIZE, COMPLEX_SUBFIELD_ELEMENT_POLY,                        *)
(* COMPLEX_SUBFIELD_GENERATED_DEGREE, COMPLEX_EMBEDDING_CMUL_INTEGER),       *)
(* Baker/ant_bridge_complex.ml (BRIDGE_NF_SUBFIELD_CLOSED,                   *)
(* BRIDGE_NF_SUBFIELD_RATIONAL), Baker/algint.ml (ALGEBRAIC_INTEGER_ADD,     *)
(* ALGEBRAIC_INTEGER_MUL, ALGEBRAIC_INTEGER_INTEGER), Baker/bridge.ml        *)
(* (EXPLICIT_IMP_ALGEBRAIC_NUMBER), Baker/lemmas.ml (REAL_LE_1_MUL);         *)
(* Library/fieldtheory.ml (SUBFIELD_GENERATED_INC_GEN),                      *)
(* Library/permutations.ml (swap, PERMUTES_SWAP, SWAP_IDEMPOTENT).           *)
(* ========================================================================= *)

needs "Baker/sharp_tools.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Part 1. Integer linear combinations of elements with bounded              *)
(* denominator and conjugates (sharp_nfbound).                               *)
(* ------------------------------------------------------------------------- *)

let SHARPC_NFBOUND_ADD = prove
 (`!s x y d1 d2 R1 R2.
        sharp_nfbound s x d1 R1 /\ sharp_nfbound s y d2 R2
        ==> sharp_nfbound s (x + y) (d1 * d2) (R1 + R2)`,
  REWRITE_TAC[sharp_nfbound] THEN REPEAT STRIP_TAC THENL
   [ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_CLOSED];
    ASM_SIMP_TAC[INTEGER_MUL];
    ASM_SIMP_TAC[REAL_LE_1_MUL];
    SUBGOAL_THEN
     `Cx(d1 * d2) * (x + y) = Cx d2 * (Cx d1 * x) + Cx d1 * (Cx d2 * y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[CX_MUL] THEN CONV_TAC COMPLEX_RING;
      MATCH_MP_TAC ALGEBRAIC_INTEGER_ADD THEN CONJ_TAC THEN
      MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN
      ASM_SIMP_TAC[ALGEBRAIC_INTEGER_INTEGER]];
    FIRST_ASSUM(MP_TAC o MATCH_MP SHARP_NFBOUND_EMBEDDING) THEN
    DISCH_THEN(fun th -> ASM_SIMP_TAC[th]) THEN
    TRANS_TAC REAL_LE_TRANS
     `norm((g:complex->complex) x) + norm((g:complex->complex) y)` THEN
    REWRITE_TAC[NORM_TRIANGLE] THEN MATCH_MP_TAC REAL_LE_ADD2 THEN
    ASM_SIMP_TAC[]]);;

let SHARPC_NFBOUND_INT_CMUL = prove
 (`!s x d R c.
        sharp_nfbound s x d R /\ integer c
        ==> sharp_nfbound s (Cx c * x) d (abs c * R)`,
  REWRITE_TAC[sharp_nfbound] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2 BRIDGE_NF_SUBFIELD_CLOSED)) THEN
    ASM_SIMP_TAC[BRIDGE_NF_SUBFIELD_RATIONAL; RATIONAL_INTEGER];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `Cx d * Cx c * x = Cx c * (Cx d * x)` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING;
      MATCH_MP_TAC ALGEBRAIC_INTEGER_MUL THEN
      ASM_SIMP_TAC[ALGEBRAIC_INTEGER_INTEGER]];
    MP_TAC(ISPECL [`s:complex->bool`; `g:complex->complex`; `c:real`;
                   `x:complex`] COMPLEX_EMBEDDING_CMUL_INTEGER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_ABS_POS]]);;

let SHARPC_NFBOUND_INT_LINEAR = prove
 (`!s x y d1 d2 R1 R2 c1 c2.
        sharp_nfbound s x d1 R1 /\ sharp_nfbound s y d2 R2 /\
        integer c1 /\ integer c2
        ==> sharp_nfbound s (Cx c1 * x - Cx c2 * y) (d1 * d2)
                          (abs c1 * R1 + abs c2 * R2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `Cx c1 * x - Cx c2 * y = Cx c1 * x + Cx(--c2) * y`
  SUBST1_TAC THENL
   [REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBST1_TAC(SYM(SPEC `c2:real` REAL_ABS_NEG)) THEN
  MATCH_MP_TAC SHARPC_NFBOUND_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC SHARPC_NFBOUND_INT_CMUL THEN
  ASM_SIMP_TAC[INTEGER_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Part 2. The coefficients after the elimination of a small relation:       *)
(* c1 x - c2 y for roots x, y of integer polynomials of degree at most       *)
(* Dx and height at most B and integers |c1|, |c2| <= X is a root of an      *)
(* integer polynomial of degree at most Dx^2 and height at most              *)
(* (2 X B)^((Dx + 3) Dx^2); the elimination identity.                        *)
(* ------------------------------------------------------------------------- *)

let SHARPC_ELIM_HEIGHT_ARITH = prove
 (`!X B Dx.
        &1 <= X /\ &1 <= B
        ==> &4 * X * B pow 2 * (&1 + &Dx * B) <= (&2 * X * B) pow (Dx + 3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_POW_ADD] THEN
  SUBGOAL_THEN `&1 <= X * B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + &Dx <= (&2 * X * B) pow Dx` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&2 pow Dx` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
      MP_TAC(SPEC `Dx:num` LT_POW2_REFL) THEN ARITH_TAC;
      MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&4 * X * B pow 3 <= (&2 * X * B) pow 3` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_MUL] THEN
    SUBGOAL_THEN `X <= X pow 3 /\ &0 <= B pow 3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `X * B pow 3 <= X pow 3 * B pow 3 /\ &0 <= X * B pow 3`
    MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `X * B pow 2 <= X * B pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `(&1 + &Dx) * (&4 * X * B pow 3)` THEN
  CONJ_TAC THENL
   [MP_TAC(ASSUME `X * B pow 2 <= X * B pow 3`) THEN REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC]);;

let SHARPC_ELIM_RADIUS_ARITH = prove
 (`!X B Dx dx dy c1 c2.
        dx <= Dx /\ dy <= Dx /\ abs c1 <= X /\ abs c2 <= X /\
        &1 <= X /\ &1 <= B
        ==> abs c1 * (&1 + &dx * B) + abs c2 * (&1 + &dy * B) <=
            &2 * X * (&1 + &Dx * B) /\
            &1 <= &2 * X * (&1 + &Dx * B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &Dx * B /\ &dx * B <= &Dx * B /\ &dy * B <= &Dx * B /\
                &0 <= &dx * B /\ &0 <= &dy * B`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
        ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `a <= X * D /\ b <= X * D ==> a + b <= &2 * X * D`) THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN ASM_REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC]);;

let SHARPC_ELIM_POW_ARITH = prove
 (`!X B Dx den dz.
        &1 <= X /\ &1 <= B /\ &1 <= den /\ den <= B pow 2 /\ dz <= Dx EXP 2
        ==> (&2 * den * &2 * X * (&1 + &Dx * B)) pow dz <=
            (&2 * X * B) pow ((Dx + 3) * Dx EXP 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &Dx * B` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&2 * X * B) pow (Dx + 3)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE_1 THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * den * &2 * X * (&1 + &Dx * B) <= (&2 * X * B) pow (Dx + 3)`
  ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `&4 * X * B pow 2 * (&1 + &Dx * B)` THEN
    ASM_SIMP_TAC[SHARPC_ELIM_HEIGHT_ARITH] THEN
    TRANS_TAC REAL_LE_TRANS `&2 * B pow 2 * &2 * X * (&1 + &Dx * B)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `((&2 * X * B) pow (Dx + 3)) pow dz` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_POW_POW] THEN MATCH_MP_TAC REAL_POW_MONO THEN
    ASM_REWRITE_TAC[]]);;

let SHARPC_ELIM_COEFF_POLY = prove
 (`!x y (ax:num->real) (ay:num->real) dx dy c1 c2 B X Dx.
        1 <= dx /\ dx <= Dx /\ 1 <= dy /\ dy <= Dx /\
        (!j. integer(ax j) /\ abs(ax j) <= B) /\ ~(ax dx = &0) /\
        vsum(0..dx) (\j. Cx(ax j) * x pow j) = Cx(&0) /\
        (!j. integer(ay j) /\ abs(ay j) <= B) /\ ~(ay dy = &0) /\
        vsum(0..dy) (\j. Cx(ay j) * y pow j) = Cx(&0) /\
        integer c1 /\ abs c1 <= X /\ integer c2 /\ abs c2 <= X /\ &1 <= X
        ==> ?dz (az:num->real).
              1 <= dz /\ dz <= Dx EXP 2 /\
              (!j. integer(az j) /\
                   abs(az j) <= (&2 * X * B) pow ((Dx + 3) * Dx EXP 2)) /\
              ~(az dz = &0) /\
              vsum(0..dz) (\j. Cx(az j) * (Cx c1 * x - Cx c2 * y) pow j) =
              Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= B` ASSUME_TAC THENL
   [TRANS_TAC REAL_LE_TRANS `abs((ax:num->real) dx)` THEN
    ASM_SIMP_TAC[REAL_ABS_INTEGER_LEMMA];
    ALL_TAC] THEN
  ABBREV_TAC `s = IMAGE (\i. if i = 1 then x else y:complex) (1..2)` THEN
  SUBGOAL_THEN
   `FINITE (s:complex->bool) /\ (!z. z IN s ==> algebraic_number z) /\
    x IN ring_carrier(subfield_generated complex_ring s) /\
    y IN ring_carrier(subfield_generated complex_ring s)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN MATCH_MP_TAC EXPLICIT_IMP_ALGEBRAIC_NUMBER THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV; IN_IMAGE] THEN
      EXISTS_TAC `1` THEN SIMP_TAC[IN_NUMSEG; ARITH];
      MATCH_MP_TAC SUBFIELD_GENERATED_INC_GEN THEN
      REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV; IN_IMAGE] THEN
      EXISTS_TAC `2` THEN SIMP_TAC[IN_NUMSEG; ARITH]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `extension_degree (subfield_generated complex_ring {Cx(&0)},
                      subfield_generated complex_ring s) I <= Dx EXP 2`
  ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS `nproduct(1..2) (\i. if i = 1 then dx else dy)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "s" THEN MATCH_MP_TAC COMPLEX_SUBFIELD_GENERATED_DEGREE THEN
      EXISTS_TAC `\i. if i = 1 then (ax:num->real) else ay` THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[];
      TRANS_TAC LE_TRANS `nproduct(1..2) (\i:num. Dx)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
        BETA_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[NPRODUCT_CONST_NUMSEG; ADD_SUB; LE_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:complex->bool`; `x:complex`; `ax:num->real`; `dx:num`;
                 `B:real`] SHARP_NFBOUND_ROOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `y:complex`; `ay:num->real`; `dy:num`;
                 `B:real`] SHARP_NFBOUND_ROOT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `x:complex`; `y:complex`;
                 `abs((ax:num->real) dx)`; `abs((ay:num->real) dy)`;
                 `&1 + &dx * B`; `&1 + &dy * B`; `c1:real`; `c2:real`]
    SHARPC_NFBOUND_INT_LINEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`X:real`; `B:real`; `Dx:num`; `dx:num`; `dy:num`;
                `c1:real`; `c2:real`] SHARPC_ELIM_RADIUS_ARITH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `sharp_nfbound s (Cx c1 * x - Cx c2 * y)
      (abs((ax:num->real) dx) * abs((ay:num->real) dy))
      (&2 * X * (&1 + &Dx * B))`
  MP_TAC THENL
   [MATCH_MP_TAC SHARP_NFBOUND_MONO THEN
    EXISTS_TAC `abs c1 * (&1 + &dx * B) + abs c2 * (&1 + &dy * B)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[sharp_nfbound] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `Cx c1 * x - Cx c2 * y`;
                 `abs((ax:num->real) dx) * abs((ay:num->real) dy)`;
                 `&2 * X * (&1 + &Dx * B)`] COMPLEX_SUBFIELD_ELEMENT_POLY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dz:num` (X_CHOOSE_THEN `az:num->real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `dz <= Dx EXP 2` ASSUME_TAC THENL
   [TRANS_TAC LE_TRANS
     `extension_degree (subfield_generated complex_ring {Cx(&0)},
                        subfield_generated complex_ring s) I` THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`dz:num`; `az:num->real`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
  TRANS_TAC REAL_LE_TRANS
   `(&2 * (abs((ax:num->real) dx) * abs((ay:num->real) dy)) *
     &2 * X * (&1 + &Dx * B)) pow dz` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SHARPC_ELIM_POW_ARITH THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Part 3. The uniform bound for algebraic coefficients, by induction on     *)
(* the number of logarithms (all degree bounds Dx at once): a small          *)
(* relation eliminates one logarithm, else the core applies.                 *)
(* ------------------------------------------------------------------------- *)

let BAKER_UNIFORM_ALGCOEFF = prove
 (`!n Dmax Dx.
     1 <= Dmax /\ 1 <= Dx
     ==> ?c kappa.
           !Mb (lg:num->complex) (a:num->num->real) (d:num->num)
            (H:num->real) (bb:num->complex) (ab:num->num->real)
            (db:num->num) B.
             &1 <= Mb /\ &2 <= B /\ baker_logdata n lg a d H Mb Dmax /\
             sharpc_coefdata n bb ab db B /\
             (!r. r IN 1..n ==> db r <= Dx) /\
             ~(vsum(1..n) (\r. bb r * lg r) = Cx(&0))
             ==> exp(--(c * Mb pow kappa * log B)) <=
                 norm(vsum(1..n) (\r. bb r * lg r))`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`&0`; `0`] THEN
    REWRITE_TAC[NUMSEG_CLAUSES; ARITH_EQ; VSUM_CLAUSES; COMPLEX_VEC_0];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Dmax:num`; `Dx:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= Dx EXP 2 /\ 1 <= (Dx + 3) * Dx EXP 2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`Dmax:num`; `Dx EXP 2`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_TAC `k1:num`)) THEN
  MP_TAC(SPECL [`SUC n`; `Dmax:num`; `Dx:num`]
    BAKER_CORE_UNIFORM_ALGCOEFF) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real` (X_CHOOSE_THEN `k2:num`
    (X_CHOOSE_THEN `cr:real` (X_CHOOSE_TAC `kr:num`)))) THEN
  EXISTS_TAC `max (max c2 (&0))
                  ((max c1 (&0) * &((Dx + 3) * Dx EXP 2) + &1) *
                   (&2 + &2 * log(max (&1) cr) + &2 * &kr))` THEN
  EXISTS_TAC `MAX k2 (k1 + 1)` THEN
  MAP_EVERY X_GEN_TAC [`Mb:real`; `lg:num->complex`; `a:num->num->real`;
                       `d:num->num`; `H:num->real`; `bb:num->complex`;
                       `ab:num->num->real`; `db:num->num`; `B:real`] THEN
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
      FIRST_X_ASSUM(MP_TAC o SPECL
       [`Mb:real`; `lg:num->complex`; `a:num->num->real`; `d:num->num`;
        `H:num->real`; `bb:num->complex`; `ab:num->num->real`;
        `db:num->num`; `B:real`] o check (fun th ->
        is_forall(concl th) && free_in `c2:real` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM(MP_TAC o check (fun th ->
        is_neg(concl th) && is_exists(rand(concl th)))) THEN
      MESON_TAC[]]] THEN
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
  SUBGOAL_THEN `&1 <= &2 * X * B /\ &0 < &2 * X * B` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &1 <= x /\ &0 < x`) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_1_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
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
   `vsum(1..SUC n) (\r. (bb:num->complex) r * (lg:num->complex) r) =
    vsum(1..SUC n) (\r. bb((p:num->num) r) * lg(p r)) /\
    vsum(1..SUC n) (\r. Cx((cc:num->real)(p r)) * lg(p r)) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`\r. (bb:num->complex) r * (lg:num->complex) r`;
                     `p:num->num`; `1..SUC n`] VSUM_PERMUTE) THEN
      ASM_REWRITE_TAC[o_DEF];
      MP_TAC(ISPECL [`\r. Cx((cc:num->real) r) * (lg:num->complex) r`;
                     `p:num->num`; `1..SUC n`] VSUM_PERMUTE) THEN
      ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `\r. (lg:num->complex)((p:num->num) r)`;
                 `\r. (bb:num->complex)((p:num->num) r)`;
                 `\r. (cc:num->real)((p:num->num) r)`]
                SHARPC_VSUM_ELIMINATE_LAST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!r. r IN 1..n
        ==> ?dz (az:num->real).
              1 <= dz /\ dz <= Dx EXP 2 /\
              (!j. integer(az j) /\
                   abs(az j) <= (&2 * X * B) pow ((Dx + 3) * Dx EXP 2)) /\
              ~(az dz = &0) /\
              vsum(0..dz) (\j. Cx(az j) *
                 (Cx((cc:num->real) t) * (bb:num->complex)((p:num->num) r) -
                  Cx(cc(p r)) * bb t) pow j) = Cx(&0)`
  MP_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:num->num) r IN 1..SUC n` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `r IN 1..n` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC SHARPC_ELIM_COEFF_POLY THEN
    MAP_EVERY EXISTS_TAC
     [`(ab:num->num->real)((p:num->num) r)`; `(ab:num->num->real) t`;
      `(db:num->num)((p:num->num) r)`; `(db:num->num) t`] THEN
    SUBGOAL_THEN
     `(db:num->num)((p:num->num) r) <= Dx /\ db t <= Dx /\
      integer((cc:num->real) t) /\ abs(cc t) <= X /\
      integer(cc(p r)) /\ abs(cc(p r)) <= X`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`!r. r IN 1..SUC n ==> integer((cc:num->real) r) /\ abs(cc r) <= X`;
        `!r. r IN 1..SUC n ==> (db:num->num) r <= Dx`;
        `t IN 1..SUC n`; `(p:num->num) r IN 1..SUC n`] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `sharpc_coefdata (SUC n) bb ab db B` THEN
    REWRITE_TAC[sharpc_coefdata] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `t:num` th) THEN
                         MP_TAC(SPEC `(p:num->num) r` th)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `dz:num->num`
    (X_CHOOSE_TAC `az:num->num->real`)) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`Mb:real`; `(lg:num->complex) o (p:num->num)`;
    `(a:num->num->real) o (p:num->num)`;
    `(d:num->num) o (p:num->num)`; `(H:num->real) o (p:num->num)`;
    `\r. Cx((cc:num->real) t) * (bb:num->complex)((p:num->num) r) -
         Cx(cc(p r)) * bb t`;
    `az:num->num->real`; `dz:num->num`;
    `(&2 * X * B) pow ((Dx + 3) * Dx EXP 2)`] o
    check (fun th -> is_forall(concl th) && free_in `c1:real` (concl th))) THEN
  REWRITE_TAC[o_THM] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `&2 * X * B` THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&1 <= x ==> &2 <= &2 * x`) THEN
        MATCH_MP_TAC REAL_LE_1_MUL THEN ASM_REAL_ARITH_TAC;
        GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[sharpc_coefdata] THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        free_in `az:num->num->real` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        free_in `az:num->num->real` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_ASSUM(fun th ->
        if is_eq(concl th) &&
           can (term_match [] `Cx(c:real) * (x:complex)`) (lhand(concl th))
        then REWRITE_TAC[GSYM th] else NO_TAC) THEN
      REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; DE_MORGAN_THM] THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM(ASSUME
       `vsum(1..SUC n) (\r. (bb:num->complex) r * (lg:num->complex) r) =
        vsum(1..SUC n) (\r. bb((p:num->num) r) * lg(p r))`)] THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `norm(vsum(1..n) (\r. (Cx((cc:num->real) t) *
                          (bb:num->complex)((p:num->num) r) -
                          Cx(cc(p r)) * bb t) * (lg:num->complex)(p r))) <=
    X * norm(vsum(1..SUC n) (\r. bb r * lg r))`
  ASSUME_TAC THENL
   [FIRST_ASSUM(fun th ->
      if is_eq(concl th) &&
         can (term_match [] `Cx(c:real) * (x:complex)`) (lhand(concl th))
      then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[ASSUME
     `vsum(1..SUC n) (\r. (bb:num->complex) r * (lg:num->complex) r) =
      vsum(1..SUC n) (\r. bb((p:num->num) r) * lg(p r))`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EXP_BOUND_MONO THEN
  MAP_EVERY EXISTS_TAC
   [`(max c1 (&0) * &((Dx + 3) * Dx EXP 2) + &1) *
     (&2 + &2 * log(max (&1) cr) + &2 * &kr)`;
    `k1 + 1`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC; ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC RELATION_ABSORB THEN EXISTS_TAC `X:real` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(max c1 (&0) * &((Dx + 3) * Dx EXP 2)) * Mb pow k1 * log(&2 * X * B) =
    max c1 (&0) * Mb pow k1 * log((&2 * X * B) pow ((Dx + 3) * Dx EXP 2))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[LOG_POW] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EXP_BOUND_MONO THEN
  MAP_EVERY EXISTS_TAC [`c1:real`; `k1:num`] THEN
  ASM_REWRITE_TAC[LE_REFL] THEN REPEAT CONJ_TAC THENL
   [REAL_ARITH_TAC; REAL_ARITH_TAC;
    MATCH_MP_TAC LOG_POS THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    ASM_REWRITE_TAC[];
    TRANS_TAC REAL_LE_TRANS
     `norm(vsum(1..n) (\r. (Cx((cc:num->real) t) *
                            (bb:num->complex)((p:num->num) r) -
                            Cx(cc(p r)) * bb t) * (lg:num->complex)(p r)))` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `norm(vsum(1..n) (\r. (Cx((cc:num->real) t) *
                            (bb:num->complex)((p:num->num) r) -
                            Cx(cc(p r)) * bb t) * (lg:num->complex)(p r))) <=
      X * norm(vsum(1..SUC n) (\r. bb r * lg r))` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4. Principal logarithms of algebraic numbers with classical          *)
(* heights at most exp G: the size data, the uniform bound, and its case of  *)
(* integer coefficients.                                                     *)
(* ------------------------------------------------------------------------- *)

let SHARPC_ALGDATA_LOGDATA = prove
 (`!m D (lg:num->complex) (a:num->num->real) (dd:num->num) (H:num->real) G.
        1 <= D /\ &1 <= G /\ sharp_algdata m lg a dd H /\
        (!r. r IN 1..m
             ==> dd r <= D /\ H r <= exp G /\
                 --pi < Im(lg r) /\ Im(lg r) <= pi)
        ==> baker_logdata m lg a dd H
              ((&((D + 2) * (D + 3)) + &m * &(D + 5) + &m * &(D + 3) + &1) *
               G) (D EXP m)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `M = &((D + 2) * (D + 3)) + &m * &(D + 5) + &m * &(D + 3) + &1` THEN
  SUBGOAL_THEN
   `&0 <= &m * &(D + 5) * G /\ &0 <= &m * &(D + 3) * G /\
    &0 <= &((D + 2) * (D + 3)) * G`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[sharp_algdata]) THEN
  REWRITE_TAC[baker_logdata] THEN REPEAT CONJ_TAC THENL
   [TRANS_TAC LE_TRANS `nproduct(1..m) (\r:num. D)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NPRODUCT_LE_NUMSEG THEN REPEAT STRIP_TAC THEN
      REWRITE_TAC[] THEN ASM_MESON_TAC[IN_NUMSEG];
      REWRITE_TAC[NPRODUCT_CONST_NUMSEG; ADD_SUB; LE_REFL]];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
      free_in `dd:num->num` (concl th) && free_in `G:real` (concl th))) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
      free_in `a:num->num->real` (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`(lg:num->complex) r`; `(a:num->num->real) r`;
                  `(dd:num->num) r`; `(H:num->real) r`; `G:real`; `D:num`]
      SHARP_LOG_ALG_SIZE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISJ2_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `(x:real) <= y ==> a <= x ==> a <= y`)) THEN
    REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
    EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC;
    TRANS_TAC REAL_LE_TRANS `sum(1..m) (\r:num. &(D + 5) * G)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r:num) IN 1..m` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        free_in `dd:num->num` (concl th) && free_in `G:real` (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        free_in `a:num->num->real` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      MP_TAC(SPECL [`(lg:num->complex) r`; `(a:num->num->real) r`;
                    `(dd:num->num) r`; `(H:num->real) r`; `G:real`; `D:num`]
        SHARP_LOG_ALG_SIZE) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN EXPAND_TAC "M" THEN
      ASM_REAL_ARITH_TAC];
    TRANS_TAC REAL_LE_TRANS `sum(1..m) (\r:num. &(D + 3) * G)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r:num) IN 1..m` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_NUMSEG]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        free_in `dd:num->num` (concl th) && free_in `G:real` (concl th))) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        free_in `a:num->num->real` (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `&1 + &((dd:num->num) r) <= exp(&D)` ASSUME_TAC THENL
       [TRANS_TAC REAL_LE_TRANS `&1 + &D` THEN
        REWRITE_TAC[REAL_EXP_LE_X; REAL_LE_LADD; REAL_OF_NUM_LE] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= (H:num->real) r` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `log(exp(&D + &3 * G))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC LOG_MONO_LE_IMP THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LT_MUL THEN
          REWRITE_TAC[REAL_OF_NUM_LT; ARITH_RULE `0 < n + 1`] THEN
          MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[REAL_EXP_ADD; GSYM REAL_OF_NUM_ADD] THEN
        MATCH_MP_TAC REAL_LE_MUL2 THEN
        REPEAT CONJ_TAC THENL
         [REAL_ARITH_TAC;
          ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_LE THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[REAL_EXP_N] THEN
          MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]];
        REWRITE_TAC[LOG_EXP; GSYM REAL_OF_NUM_ADD] THEN
        SUBGOAL_THEN `&D <= &D * G` MP_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
          REAL_ARITH_TAC]];
      REWRITE_TAC[SUM_CONST_NUMSEG; ADD_SUB] THEN EXPAND_TAC "M" THEN
      ASM_REAL_ARITH_TAC]]);;

let SHARPC_UNIFORM_ALG = prove
 (`!m D. 1 <= D
         ==> ?c k. !(lg:num->complex) (a:num->num->real) (dd:num->num)
                    (H:num->real) (bb:num->complex) (ab:num->num->real)
                    (db:num->num) B G.
               &1 <= G /\ &2 <= B /\ sharp_algdata m lg a dd H /\
               sharpc_coefdata m bb ab db B /\
               (!r. r IN 1..m
                    ==> dd r <= D /\ db r <= D /\ H r <= exp G /\
                        --pi < Im(lg r) /\ Im(lg r) <= pi) /\
               ~(vsum(1..m) (\r. bb r * lg r) = Cx(&0))
               ==> exp(--(c * G pow k * log B)) <=
                   norm(vsum(1..m) (\r. bb r * lg r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `D EXP m`; `D:num`] BAKER_UNIFORM_ALGCOEFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_TAC `kappa:num`)) THEN
  ABBREV_TAC
   `M = &((D + 2) * (D + 3)) + &m * &(D + 5) + &m * &(D + 3) + &1` THEN
  EXISTS_TAC `c * M pow kappa` THEN EXISTS_TAC `kappa:num` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`M * G:real`; `lg:num->complex`; `a:num->num->real`; `dd:num->num`;
    `H:num->real`; `bb:num->complex`; `ab:num->num->real`; `db:num->num`;
    `B:real`]) THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `&0 <= &m * &(D + 5) * G /\ &0 <= &m * &(D + 3) * G /\
      &0 <= &((D + 2) * (D + 3)) * G`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "M" THEN ASM_REAL_ARITH_TAC;
    EXPAND_TAC "M" THEN MATCH_MP_TAC SHARPC_ALGDATA_LOGDATA THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[]]);;

let SHARP_UNIFORM_ALG = prove
 (`!m D. 1 <= D
         ==> ?c k. !(lg:num->complex) (a:num->num->real) (dd:num->num)
                    (H:num->real) (bb:num->real) B G.
               &1 <= G /\ &2 <= B /\ sharp_algdata m lg a dd H /\
               (!r. r IN 1..m
                    ==> dd r <= D /\ H r <= exp G /\
                        --pi < Im(lg r) /\ Im(lg r) <= pi /\
                        integer(bb r) /\ abs(bb r) <= B) /\
               ~(vsum(1..m) (\r. Cx(bb r) * lg r) = Cx(&0))
               ==> exp(--(c * G pow k * log B)) <=
                   norm(vsum(1..m) (\r. Cx(bb r) * lg r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`m:num`; `D:num`] SHARPC_UNIFORM_ALG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_TAC `k:num`)) THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `k:num`] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`lg:num->complex`; `a:num->num->real`; `dd:num->num`; `H:num->real`;
    `\r. Cx((bb:num->real) r)`;
    `\r j. if j = 0 then --((bb:num->real) r) else if j = 1 then &1 else &0`;
    `\r:num. 1`; `B:real`; `G:real`]) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  MATCH_MP_TAC SHARPC_COEFDATA_INTEGER THEN ASM_SIMP_TAC[] THEN
  ASM_REAL_ARITH_TAC);;
