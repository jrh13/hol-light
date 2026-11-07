(* ========================================================================= *)
(* Tools for the Schinzel-Tijdeman theorem: the multiplicity split and the   *)
(* root data of an integer polynomial.                                       *)
(*                                                                           *)
(* Purpose: lemmas for roots of any multiplicity from the proof of the       *)
(* reducible case (SCHINZEL_TIJDEMAN_REDUCIBLE_MULT is a corollary in        *)
(* Baker/schinzel_general.ml), used by the general theorem and by            *)
(* Baker/prime_factors.ml: an integer polynomial F, not identically zero,    *)
(* vanishing at the root r 1 of nf_data n g r is g^k H with k >= 1 and       *)
(* H(r 1) <> 0 (SCHINZEL_TIJDEMAN_MULT_SPLIT; repeated division by the monic *)
(* g, SCHINZEL_TIJDEMAN_MULT_DIVIDES of Baker/descent.ml, terminating by     *)
(* degree); for a monic integer polynomial and a root Z this gives the root  *)
(* data nf_data n g r with r 1 = Z (SCHINZEL_TIJDEMAN_MULT_ROOT_DATA, the    *)
(* minimal polynomial from NF_DATA_EXISTS); a polynomial with a root has     *)
(* degree >= 1 (SCHINZEL_TIJDEMAN_MULT_DEGREE_POS); and                      *)
(* log abs F(X) <= N log abs X + C for monic F of degree N and large abs X   *)
(* (SCHINZEL_TIJDEMAN_MULT_F_BOUND).                                         *)
(*                                                                           *)
(* Main results: SCHINZEL_TIJDEMAN_MULT_SPLIT,                               *)
(* SCHINZEL_TIJDEMAN_MULT_ROOT_DATA, SCHINZEL_TIJDEMAN_MULT_F_BOUND,         *)
(* SCHINZEL_TIJDEMAN_MULT_DEGREE_POS.                                        *)
(*                                                                           *)
(* Uses: Baker/schinzel_poly.ml (POLY_MONIC_LOG_ASYMPTOTIC),                 *)
(* Baker/descent.ml (SCHINZEL_TIJDEMAN_MULT_DIVIDES),                        *)
(* Baker/schinzel_sunit.ml (NF_DESCENT_VSUM_CX), Baker/nf_order.ml           *)
(* (NF_DATA), Baker/nf_fields.ml (NF_DATA_EXISTS), Baker/algint.ml           *)
(* (ALGEBRAIC_INTEGER_EXPLICIT). Used by Baker/prime_factors.ml (section 19) *)
(* and Baker/schinzel_general.ml (section 20).                               *)
(* ========================================================================= *)

needs "Baker/descent.ml";;
needs "Baker/nf_fields.ml";;
needs "Baker/schinzel_poly.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The multiplicity split: an integer polynomial F, not identically zero,    *)
(* vanishing at r 1 is g^k H with k >= 1, H an integer polynomial and H(r 1) *)
(* <> 0 (g the defining polynomial of nf_data n g r; the division step is    *)
(* SCHINZEL_TIJDEMAN_MULT_DIVIDES of Baker/descent.ml); the root data of a   *)
(* monic integer polynomial at a root Z.                                     *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_MULT_SPLIT = prove
 (`!n c r N (a:num->real).
     nf_data n c r /\ (!i. integer(a i)) /\
     vsum(0..N) (\i. Cx(a i) * r 1 pow i) = Cx(&0) /\
     ~(!z. vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0))
     ==> ?k M (h:num->real).
           1 <= k /\ (!i. integer(h i)) /\
           (!z. vsum(0..N) (\i. Cx(a i) * z pow i) =
                vsum(0..n) (\i. Cx(c i) * z pow i) pow k *
                vsum(0..M) (\i. Cx(h i) * z pow i)) /\
           ~(vsum(0..M) (\i. Cx(h i) * r 1 pow i) = Cx(&0))`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`a:num->real`,`a:num->real`) THEN
  SPEC_TAC(`N:num`,`N:num`) THEN
  MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `N:num` THEN DISCH_THEN(LABEL_TAC "ind") THEN
  X_GEN_TAC `a:num->real` THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP SCHINZEL_TIJDEMAN_MULT_DIVIDES th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "fq")))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  ASM_CASES_TAC
   `vsum(0..N-n) (\i. Cx(q i) * (r:num->complex) 1 pow i) = Cx(&0)`
  THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`1`; `N - n:num`; `q:num->real`] THEN
    REWRITE_TAC[LE_REFL; COMPLEX_POW_1] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [USE_THEN "fq" ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]] THEN
  SUBGOAL_THEN `~(!z. vsum(0..N-n) (\i. Cx(q i) * z pow i) = Cx(&0))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(!z. vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0))` THEN
    REWRITE_TAC[] THEN X_GEN_TAC `z:complex` THEN
    USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO];
    ALL_TAC] THEN
  REMOVE_THEN "ind" (MP_TAC o SPEC `N - n:num`) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`1 <= n`; `n <= N`] THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `q:num->real`) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `M:num`
    (X_CHOOSE_THEN `h:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fh")
        ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`SUC k`; `M:num`; `h:num->real`] THEN
  REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `z:complex` THEN USE_THEN "fq" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "fh" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_ASSOC];
    FIRST_ASSUM ACCEPT_TAC]);;

let SCHINZEL_TIJDEMAN_MULT_DEGREE_POS = prove
 (`!N (a:num->real) (z:complex).
     ~(a N = &0) /\ vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) ==> 1 <= N`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ARITH_RULE `1 <= N <=> ~(N = 0)`] THEN
  ASM_CASES_TAC `N = 0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_RID; CX_INJ] THEN
  CONV_TAC TAUT);;

let SCHINZEL_TIJDEMAN_MULT_ROOT_DATA = prove
 (`!N (a:num->real) Z.
     (!i. integer(a i)) /\ a N = &1 /\
     vsum(0..N) (\i. Cx(a i) * Z pow i) = Cx(&0)
     ==> ?n g r k M h. nf_data n g r /\ r 1 = Z /\ 1 <= k /\
                       (!i. integer(h i)) /\
                       (!x. sum(0..N) (\i. a i * x pow i) =
                            sum(0..n) (\i. g i * x pow i) pow k *
                            sum(0..M) (\i. h i * x pow i)) /\
                       ~(vsum(0..M) (\i. Cx(h i) * Z pow i) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `algebraic_integer Z` MP_TAC THENL
   [REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `a:num->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `g:num->real`
    (X_CHOOSE_THEN `r:num->complex` (CONJUNCTS_THEN2 ASSUME_TAC
      (SUBST_ALL_TAC o SYM)))) o MATCH_MP NF_DATA_EXISTS) THEN
  MP_TAC(SPECL [`n:num`; `g:num->real`; `r:num->complex`; `N:num`;
                `a:num->real`] SCHINZEL_TIJDEMAN_MULT_SPLIT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MP_TAC(ISPECL [`N:num`; `\i. Cx((a:num->real) i)`]
      COMPLEX_POLYFUN_EQ_0) THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL; CX_INJ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `M:num`
    (X_CHOOSE_THEN `h:num->real` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "fac")
        ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `g:num->real`; `r:num->complex`; `k:num`;
                        `M:num`; `h:num->real`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY REFL_TAC THEN
  X_GEN_TAC `x:real` THEN ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  REWRITE_TAC[CX_MUL; CX_POW; GSYM NF_DESCENT_VSUM_CX] THEN
  USE_THEN "fac" (fun th -> REWRITE_TAC[th]));;

(* ------------------------------------------------------------------------- *)
(* The bound log abs F(X) <= N log abs X + C for a monic integer polynomial  *)
(* F of degree N and large abs X (from the asymptotics                       *)
(* POLY_MONIC_LOG_ASYMPTOTIC).                                               *)
(* ------------------------------------------------------------------------- *)

let SCHINZEL_TIJDEMAN_MULT_F_BOUND = prove
 (`!N (a:num->real).
     1 <= N /\ a N = &1
     ==> ?X0 C. !X. integer X /\ X0 <= abs X /\
                    ~(sum(0..N) (\i. a i * X pow i) = &0)
                    ==> log(abs(sum(0..N) (\i. a i * X pow i))) <=
                        &N * log(abs X) + C`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLY_MONIC_LOG_ASYMPTOTIC) THEN
  DISCH_THEN(X_CHOOSE_THEN `X0:real` (X_CHOOSE_THEN `C:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "as"))))) THEN
  MAP_EVERY EXISTS_TAC [`X0:real`; `C:real`] THEN
  X_GEN_TAC `X:real` THEN STRIP_TAC THEN
  REMOVE_THEN "as" (MP_TAC o SPEC `X:real`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `C / abs X <= C` MP_TAC THENL
   [SUBGOAL_THEN `&1 <= abs(X:real)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`&1 <= X0`; `X0 <= abs(X:real)`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&1 <= x ==> &0 < x`;
             ASSUME `&1 <= abs(X:real)`] THEN
    MP_TAC(SPECL [`C:real`; `abs X - &1`] REAL_LE_MUL) THEN
    MAP_EVERY UNDISCH_TAC [`&1 <= abs(X:real)`; `&0 <= C`] THEN
    REAL_ARITH_TAC;
    REAL_ARITH_TAC]);;
