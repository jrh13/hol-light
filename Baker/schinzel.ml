(* ========================================================================= *)
(* Tools for the Schinzel-Tijdeman theorem: exponent bounds and integer      *)
(* polynomials.                                                              *)
(*                                                                           *)
(* Purpose: lemmas from the proof of the reducible case of the               *)
(* Schinzel-Tijdeman theorem by two rational logarithms (its theorems        *)
(* SCHINZEL_TIJDEMAN_REDUCIBLE, SCHINZEL_TIJDEMAN_FINITE_REDUCIBLE and       *)
(* SCHINZEL_TIJDEMAN_REDUCIBLE_MULT are corollaries of SCHINZEL_TIJDEMAN and *)
(* SCHINZEL_TIJDEMAN_FINITE in Baker/schinzel_general.ml), used by the       *)
(* general theorem and by Baker/prime_factors.ml: for X in a finite set the  *)
(* exponent m of c y^m = f(X) with abs y >= 2 is bounded                     *)
(* (SCHINZEL_TIJDEMAN_FINITE_X), m log 2 <= log abs(c y^m)                   *)
(* (SCHINZEL_TIJDEMAN_LOG_LOWER), integer polynomials take integer values at *)
(* integers (SCHINZEL_TIJDEMAN_INTEGER_POLY), a factorization of an integer  *)
(* polynomial over C gives one over R (SCHINZEL_TIJDEMAN_REAL_FACTOR), and   *)
(* the monic scaling X = a_N x, c = a_N^(N-1): an exponent bound for the     *)
(* monic equation gives one for y^m = f(x)                                   *)
(* (SCHINZEL_TIJDEMAN_MONIC_SCALING).                                        *)
(*                                                                           *)
(* Main results: SCHINZEL_TIJDEMAN_MONIC_SCALING,                            *)
(* SCHINZEL_TIJDEMAN_FINITE_X, SCHINZEL_TIJDEMAN_LOG_LOWER,                  *)
(* SCHINZEL_TIJDEMAN_INTEGER_POLY, SCHINZEL_TIJDEMAN_REAL_FACTOR.            *)
(*                                                                           *)
(* Uses: Baker/schinzel_sunit.ml (NF_DESCENT_VSUM_CX), Baker/superell.ml     *)
(* (SUPERELL_MONIC_VALUE). Used by Baker/prime_factors.ml (section 19) and   *)
(* Baker/schinzel_general.ml (section 20).                                   *)
(* ========================================================================= *)

needs "Baker/superell.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Finitely many X: a bounded exponent; the lower bound m log 2 for log      *)
(* abs(c y^m).                                                               *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_FINITE_X = prove
 (`!(f:real->real) c S.
     FINITE S /\ integer c /\ ~(c = &0)
     ==> ?M. !X y m. X IN S /\ &2 <= abs y /\ c * y pow m = f X ==> m <= M`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `sum S (\X. abs((f:real->real) X))` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `M:num`) THEN EXISTS_TAC `M:num` THEN
  MAP_EVERY X_GEN_TAC [`X:real`; `y:real`; `m:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs((f:real->real) X) <= &M` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\X. abs((f:real->real) X)`; `&M`; `S:real->bool`]
      SUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[REAL_ABS_POS] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 pow m <= abs y pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (abs c - &1) * abs y pow m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_ABS_POW] THEN
    SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    UNDISCH_TAC `&1 <= abs c` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&m < &2 pow m` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_LT; LT_POW2_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((f:real->real) X) = abs c * abs y pow m` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`abs((f:real->real) X) <= &M`; `&2 pow m <= abs y pow m`;
    `&0 <= (abs c - &1) * abs y pow m`; `&m < &2 pow m`] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let SCHINZEL_TIJDEMAN_LOG_LOWER = prove
 (`!c y m. integer c /\ ~(c = &0) /\ &2 <= abs y
           ==> &m * log(&2) <= log(abs(c * y pow m))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= abs c` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs c /\ &0 < abs y` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&1 <= abs c`; `&2 <= abs y`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_POW; LOG_MUL; REAL_POW_LT; LOG_POW] THEN
  SUBGOAL_THEN `&0 <= log(abs c) /\ log(&2) <= log(abs y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&m`; `log(&2)`; `log(abs y)`] REAL_LE_LMUL) THEN
  ASM_REWRITE_TAC[REAL_POS] THEN
  UNDISCH_TAC `&0 <= log(abs c)` THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer polynomials: integer values at integers, and real factorizations  *)
(* from complex ones.                                                        *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_INTEGER_POLY = prove
 (`!n (c:num->real) x.
     (!i. integer(c i)) /\ integer x
     ==> integer(sum(0..n) (\i. c i * x pow i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGER_SUM THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC INTEGER_MUL THEN ASM_SIMP_TAC[INTEGER_POW]);;

let SCHINZEL_TIJDEMAN_REAL_FACTOR = prove
 (`!N (a:num->real) n (g:num->real) M (h:num->real).
     (!z. vsum(0..N) (\i. Cx(a i) * z pow i) =
          vsum(0..n) (\i. Cx(g i) * z pow i) *
          vsum(0..M) (\i. Cx(h i) * z pow i))
     ==> !x. sum(0..N) (\i. a i * x pow i) =
             sum(0..n) (\i. g i * x pow i) * sum(0..M) (\i. h i * x pow i)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  REWRITE_TAC[CX_MUL; GSYM NF_DESCENT_VSUM_CX] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The monic scaling X = a_N x, c = a_N^(N-1) (the constant c does not       *)
(* depend on m): an exponent bound for the monic equation gives one for y^m  *)
(* = f(x).                                                                   *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_MONIC_SCALING = prove
 (`!N (a:num->real) M.
     1 <= N /\
     (!X y m. integer X /\ integer y /\ &2 <= abs y /\
              a N pow (N - 1) * y pow m =
              sum(0..N) (\i. (if i = N then &1
                              else a i * a N pow (N - 1 - i)) * X pow i)
              ==> m <= M) /\
     (!i. integer(a i))
     ==> !x y m. integer x /\ integer y /\ &2 <= abs y /\
                 y pow m = sum(0..N) (\i. a i * x pow i)
                 ==> m <= M`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "M")
    ASSUME_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`; `m:num`] THEN STRIP_TAC THEN
  REMOVE_THEN "M" MATCH_MP_TAC THEN EXISTS_TAC `(a:num->real) N * x` THEN
  EXISTS_TAC `y:real` THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [MATCH_MP_TAC INTEGER_MUL THEN CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    MP_TAC(SPECL [`N:num`; `a:num->real`; `x:real`] SUPERELL_MONIC_VALUE) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;
