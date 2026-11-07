(* ========================================================================= *)
(* Sharpening I: the headline forms.                                         *)
(*                                                                           *)
(* Purpose: Baker, A sharpening of the bounds for linear forms in            *)
(* logarithms I (Acta Arith. 21, 1972), Theorem, in the classical-height     *)
(* data format of the Baker core: non-zero algebraic numbers al r (r =       *)
(* 1..n), roots of integer polynomials a r of degree dd r <= d, the first    *)
(* n - 1 of height at most exp g0 and the last of height at most A,          *)
(* principal logarithms clog and integer coefficients of size at most B:     *)
(* Lambda = 0 or |Lambda| >= exp(-C g0^K log A log B), with C and K          *)
(* depending only on n and d. The real form for positive real algebraic      *)
(* numbers, and the form for a fixed number field used by the                *)
(* Schinzel-Tijdeman theorem: fixed numbers al j of a number field           *)
(* F = Q(s), one variable number x of F given by an integer denominator      *)
(* den <= A and conjugates of modulus at most A.                             *)
(*                                                                           *)
(* Main results:                                                             *)
(*  - SHARP_ALGDATA_CLOG, SHARP_VSUM_CLOG_REAL: the principal logarithm step *)
(*    of the headline forms, shared with Baker/sharpc_main.ml: lg r =        *)
(*    clog(al r) for non-zero roots al r of integer polynomials gives the    *)
(*    height data sharp_algdata of the core, with imaginary parts in         *)
(*    (-pi, pi] (CEXP_CLOG, CLOG_WORKS); for positive reals x r the linear   *)
(*    form in the clog(Cx(x r)) is Cx of the real one (CX_LOG, VSUM_CX).     *)
(*  - BAKER_SHARPENING: SHARP_BAKER_ALGEBRAIC with lg r = clog(al r).        *)
(*  - BAKER_SHARPENING_REAL: al r = Cx(x r), the polynomial equations and    *)
(*    the linear form through Cx.                                            *)
(*  - SHARP_BAKER_NUMBER_FIELD: BAKER_SHARPENING for N + 1 numbers: the      *)
(*    fixed ones with any integer polynomials                                *)
(*    (ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT; elements of F are algebraic,        *)
(*    COMPLEX_SUBFIELD_GENERATED_ALGEBRAIC), g0 from their heights, the      *)
(*    degree bound D + their degrees; the variable x through                 *)
(*    COMPLEX_SUBFIELD_ELEMENT_POLY with b = den and R = A, so its height is *)
(*    at most A1 = (2 A^2)^D and log A1 <= 3 D log A (A >= e,                *)
(*    SHARP_NF_HEIGHT_LOG_BOUND); the constant C = 3 D |C0| g0^K0.           *)
(*                                                                           *)
(* Uses: Baker/sharp_descent.ml (SHARP_BAKER_ALGEBRAIC),                     *)
(* Baker/sharp_defs.ml (sharp_bound_property_alg, sharp_algdata),            *)
(* Baker/sharp_tools.ml (COMPLEX_SUBFIELD_ELEMENT_POLY,                      *)
(* COMPLEX_SUBFIELD_GENERATED_ALGEBRAIC), Baker/bridge.ml                    *)
(* (ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT), Multivariate/transcendentals.ml       *)
(* (CLOG_WORKS, CEXP_CLOG, CX_LOG).                                          *)
(*                                                                           *)
(* The rational case SHARP_BAKER_RATIONAL (BAKER_SHARPENING_REAL with d = 1) *)
(* is in Baker/tijdeman.ml (section 8).                                      *)
(* ========================================================================= *)

needs "Baker/sharp_descent.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The principal logarithm step of the headline forms (shared with           *)
(* Baker/sharpc_main.ml): principal logarithms of non-zero roots of integer  *)
(* polynomials give the height data of the core, with imaginary parts in     *)
(* (-pi, pi]; for positive reals they are the real logarithms.               *)
(* ------------------------------------------------------------------------- *)

let SHARP_ALGDATA_CLOG = prove
 (`!n (al:num->complex) (a:num->num->real) (dd:num->num) A g0.
        &1 <= g0 /\ exp(&1) <= A /\
        (!r. r IN 1..n
             ==> ~(al r = Cx(&0)) /\ 1 <= dd r /\ (!j. integer(a r j)) /\
                 ~(a r (dd r) = &0) /\
                 vsum(0..dd r) (\j. Cx(a r j) * al r pow j) = Cx(&0)) /\
        (!r j. r IN 1..n-1 ==> abs(a r j) <= exp g0) /\
        (!j. abs(a n j) <= A)
        ==> sharp_algdata n (\r. clog(al r)) a dd
              (\r. if r = n then A else exp g0) /\
            (!r. r IN 1..n
                 ==> --pi < Im(clog(al r)) /\ Im(clog(al r)) <= pi)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "rf") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `&1 <= A /\ &1 <= exp g0` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN
    MP_TAC(SPEC `g0:real` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[sharp_algdata] THEN
  CONJ_TAC THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  USE_THEN "rf" (fun th -> MP_TAC(MP (SPEC `r:num` th)
                                       (ASSUME `r IN 1..n`))) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[CLOG_WORKS; CEXP_CLOG] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `j:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `r IN 1..n` THEN UNDISCH_TAC `~(r:num = n)` THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

let SHARP_VSUM_CLOG_REAL = prove
 (`!n (x:num->real) (b:num->real).
        (!r. r IN 1..n ==> &0 < x r)
        ==> vsum(1..n) (\r. Cx(b r) * clog(Cx(x r))) =
            Cx(sum(1..n) (\r. b r * log(x r)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM VSUM_CX] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[CX_MUL] THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC CX_LOG THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The uniform complex form.                                                 *)
(* ------------------------------------------------------------------------- *)

let BAKER_SHARPENING = prove
 (`!n d. 1 <= n
         ==> ?C K. !(al:num->complex) (a:num->num->real) (dd:num->num)
                    (bb:num->real) A B g0.
                     &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
                     (!r. r IN 1..n
                          ==> ~(al r = Cx(&0)) /\ 1 <= dd r /\ dd r <= d /\
                              (!j. integer(a r j)) /\ ~(a r (dd r) = &0) /\
                              vsum(0..dd r) (\j. Cx(a r j) * al r pow j) =
                              Cx(&0) /\
                              integer(bb r) /\ abs(bb r) <= B) /\
                     (!r j. r IN 1..n-1 ==> abs(a r j) <= exp g0) /\
                     (!j. abs(a n j) <= A) /\
                     ~(vsum(1..n) (\r. Cx(bb r) * clog(al r)) = Cx(&0))
                     ==> exp(--(C * g0 pow K * log A * log B)) <=
                         norm(vsum(1..n) (\r. Cx(bb r) * clog(al r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `d:num`] SHARP_BAKER_ALGEBRAIC) THEN
  ASM_REWRITE_TAC[sharp_bound_property_alg] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`al:num->complex`; `a:num->num->real`; `dd:num->num`; `bb:num->real`;
    `A:real`; `B:real`; `g0:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `al:num->complex`; `a:num->num->real`;
                `dd:num->num`; `A:real`; `g0:real`] SHARP_ALGDATA_CLOG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. clog((al:num->complex) r)`; `a:num->num->real`; `dd:num->num`;
    `bb:num->real`; `A:real`; `B:real`; `g0:real`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The real form: positive real algebraic numbers and real logarithms.       *)
(* ------------------------------------------------------------------------- *)

let BAKER_SHARPENING_REAL = prove
 (`!n d. 1 <= n
         ==> ?C K. !(x:num->real) (a:num->num->real) (dd:num->num)
                    (bb:num->real) A B g0.
                     &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
                     (!r. r IN 1..n
                          ==> &0 < x r /\ 1 <= dd r /\ dd r <= d /\
                              (!j. integer(a r j)) /\ ~(a r (dd r) = &0) /\
                              sum(0..dd r) (\j. a r j * x r pow j) = &0 /\
                              integer(bb r) /\ abs(bb r) <= B) /\
                     (!r j. r IN 1..n-1 ==> abs(a r j) <= exp g0) /\
                     (!j. abs(a n j) <= A) /\
                     ~(sum(1..n) (\r. bb r * log(x r)) = &0)
                     ==> exp(--(C * g0 pow K * log A * log B)) <=
                         abs(sum(1..n) (\r. bb r * log(x r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `d:num`] BAKER_SHARPENING) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`x:num->real`; `a:num->num->real`; `dd:num->num`; `bb:num->real`;
    `A:real`; `B:real`; `g0:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `bb:num->real`]
    SHARP_VSUM_CLOG_REAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. Cx((x:num->real) r)`; `a:num->num->real`; `dd:num->num`;
    `bb:num->real`; `A:real`; `B:real`; `g0:real`]) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CX_INJ; GSYM CX_POW; GSYM CX_MUL; VSUM_CX; REAL_LT_IMP_NZ]);;

(* ------------------------------------------------------------------------- *)
(* The form for a fixed number field (used by Schinzel-Tijdeman).            *)
(* ------------------------------------------------------------------------- *)

(* The height A1 = (2 A^2)^D of the variable number: log A1 <= 3 D log A.    *)

let SHARP_NF_HEIGHT_LOG_BOUND = prove
 (`!A D. exp(&1) <= A /\ 1 <= D
         ==> exp(&1) <= (&2 * A pow 2) pow D /\
             &0 <= log((&2 * A pow 2) pow D) /\
             log((&2 * A pow 2) pow D) <= &3 * &D * log A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 <= A` ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `A <= &2 * A pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= A /\ &1 * A <= A * A ==> A <= &2 * A * A`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * A pow 2 <= (&2 * A pow 2) pow D` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `log(&2) <= log A /\ &0 <= log(&2)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_MONO_LE_IMP; MATCH_MP_TAC LOG_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOG_POW; LOG_MUL; REAL_LT_MUL; REAL_POW_LT;
               REAL_ARITH `&0 < &2`] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 <= x + &2 * y`) THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH `&3 * x * y = x * &3 * y`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
    ASM_REAL_ARITH_TAC]);;

let SHARP_BAKER_NUMBER_FIELD = prove
 (`!s N (al:num->complex).
        FINITE s /\ (!z. z IN s ==> algebraic_number z) /\
        (!j. j IN 1..N
             ==> al j IN ring_carrier(subfield_generated complex_ring s) /\
                 ~(al j = Cx(&0)))
        ==> ?C. !x den (bb:num->real) b A B.
                  x IN ring_carrier(subfield_generated complex_ring s) /\
                  ~(x = Cx(&0)) /\
                  integer den /\ &1 <= den /\ den <= A /\
                  algebraic_integer(Cx den * x) /\
                  (!g. g IN
                       complex_embeddings(subfield_generated complex_ring s)
                       ==> norm(g x) <= A) /\
                  exp(&1) <= A /\ &2 <= B /\
                  (!j. j IN 1..N ==> integer(bb j) /\ abs(bb j) <= B) /\
                  integer b /\ abs b <= B /\
                  ~(vsum(1..N) (\j. Cx(bb j) * clog(al j)) + Cx b * clog x =
                    Cx(&0))
                  ==> exp(--(C * log A * log B)) <=
                      norm(vsum(1..N) (\j. Cx(bb j) * clog(al j)) +
                           Cx b * clog x)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `D = extension_degree (subfield_generated complex_ring {Cx(&0)},
                          subfield_generated complex_ring s) I` THEN
  SUBGOAL_THEN
   `?dd (aa:num->num->real) HH.
      !j. j IN 1..N
          ==> 1 <= dd j /\ (!i. integer(aa j i) /\ abs(aa j i) <= HH j) /\
              ~(aa j (dd j) = &0) /\
              vsum(0..dd j) (\i. Cx(aa j i) * al j pow i) = Cx(&0)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC ALGEBRAIC_NUMBER_EXPLICIT_HEIGHT THEN
    MATCH_MP_TAC COMPLEX_SUBFIELD_GENERATED_ALGEBRAIC THEN
    EXISTS_TAC `s:complex->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `g0 = &1 + sum(1..N) (\j. log(max (&1) (HH j)))` THEN
  SUBGOAL_THEN
   `&1 <= g0 /\
    !j i. j IN 1..N ==> abs((aa:num->num->real) j i) <= exp g0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!j. j IN 1..N ==> &0 <= log(max (&1) (HH j))`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC LOG_POS THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "g0" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &1 <= &1 + x`) THEN
      MATCH_MP_TAC SUM_POS_LE_NUMSEG THEN ASM_SIMP_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `i:num`] THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS `max (&1) (HH(j:num))` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
        can (find_term ((=) `HH:num->real`)) (concl th) &&
        can (find_term ((=) `dd:num->num`)) (concl th))) THEN
      ASM_SIMP_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1 o
        CONJUNCT2) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPEC `max (&1) (HH(j:num))` EXP_LOG) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN EXPAND_TAC "g0" THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= &1 + y`) THEN
    MP_TAC(ISPECL [`\j:num. log(max (&1) ((HH:num->real) j))`;
                   `sum(1..N) (\j. log(max (&1) ((HH:num->real) j)))`;
                   `1..N`] SUM_POS_BOUND) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; REAL_LE_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`SUC N`; `D + nsum(1..N) dd`] BAKER_SHARPENING) THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC N`; SUC_SUB1] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real` (X_CHOOSE_THEN `K0:num`
    (LABEL_TAC "bs"))) THEN
  EXISTS_TAC `&3 * &D * abs C0 * g0 pow K0` THEN
  MAP_EVERY X_GEN_TAC
   [`x:complex`; `den:real`; `bb:num->real`; `b:real`; `A:real`; `B:real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:complex->bool`; `x:complex`; `den:real`; `A:real`]
    COMPLEX_SUBFIELD_ELEMENT_POLY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `dx:num` (X_CHOOSE_THEN `ax:num->real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`A:real`; `D:num`] SHARP_NF_HEIGHT_LOG_BOUND) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[LE_TRANS]; STRIP_TAC] THEN
  USE_THEN "bs" (MP_TAC o SPECL
   [`\r. if r = SUC N then x else (al:num->complex) r`;
    `\r. if r = SUC N then ax else (aa:num->num->real) r`;
    `\r. if r = SUC N then dx else (dd:num->num) r`;
    `\r. if r = SUC N then b else (bb:num->real) r`;
    `(&2 * A pow 2) pow D`; `B:real`; `g0:real`]) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum(1..SUC N) (\r. Cx(if r = SUC N then b else bb r) *
                        clog(if r = SUC N then x else al r)) =
    vsum(1..N) (\j. Cx(bb j) * clog(al j)) + Cx b * clog x`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC N`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    SIMP_TAC[ARITH_RULE `i <= N ==> ~(i = SUC N)`];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      ASM_CASES_TAC `r = SUC N` THEN ASM_REWRITE_TAC[] THENL
       [ASM_SIMP_TAC[ARITH_RULE `dx <= D ==> dx <= D + n`]; ALL_TAC] THEN
      SUBGOAL_THEN `r IN 1..N` ASSUME_TAC THENL
       [UNDISCH_TAC `r IN 1..SUC N` THEN UNDISCH_TAC `~(r = SUC N)` THEN
        REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(dd:num->num) r <= nsum(1..N) dd` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`dd:num->num`; `nsum(1..N) dd`; `1..N`]
          NSUM_POS_BOUND) THEN
        REWRITE_TAC[FINITE_NUMSEG; LE_REFL] THEN
        DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ASM_SIMP_TAC[ARITH_RULE `d <= n ==> d <= D + n`]];
      MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(r = SUC N)` (fun th -> ASM_SIMP_TAC[th]) THEN
      UNDISCH_TAC `r IN 1..N` THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      X_GEN_TAC `j:num` THEN
      TRANS_TAC REAL_LE_TRANS `(&2 * den * A) pow dx` THEN
      ASM_REWRITE_TAC[] THEN
      TRANS_TAC REAL_LE_TRANS `(&2 * A pow 2) pow dx` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_LE2 THEN CONJ_TAC THENL
         [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
          ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_POW_2; GSYM REAL_MUL_ASSOC] THEN
          MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN
        MP_TAC(SPECL [`2`; `A:real`] REAL_POW_LE_1) THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `(a:real) <= b ==> b <= c ==> a <= c`) THEN
  REWRITE_TAC[REAL_EXP_MONO_LE; REAL_LE_NEG2] THEN
  SUBGOAL_THEN `&0 <= g0 pow K0 /\ &0 <= log B` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_POW_LE; MATCH_MP_TAC LOG_POS] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `abs C0 * g0 pow K0 * log((&2 * A pow 2) pow D) * log B` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[REAL_ABS_LE] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(abs C0 * g0 pow K0 * log B) * log((&2 * A pow 2) pow D) <=
    (abs C0 * g0 pow K0 * log B) * (&3 * &D * log A)
    ==> abs C0 * g0 pow K0 * log((&2 * A pow 2) pow D) * log B <=
        (&3 * &D * abs C0 * g0 pow K0) * log A * log B`) THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[REAL_ABS_POS]);;
