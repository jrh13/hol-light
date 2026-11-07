(* ========================================================================= *)
(* Sharpening I with algebraic coefficients: the headline forms.             *)
(*                                                                           *)
(* Purpose: Baker, A sharpening of the bounds for linear forms in            *)
(* logarithms I (Acta Arith. 21, 1972), with ALGEBRAIC coefficients (Baker,  *)
(* A central theorem in transcendence theory, 1973, Theorem; Transcendental  *)
(* Number Theory, p. 23), uniform in the data, in the classical-height data  *)
(* format of the Baker core: non-zero algebraic numbers al r (r = 1..n),     *)
(* roots of integer polynomials a r of degree dd r <= d, the first n - 1 of  *)
(* height at most exp g0 and the last of height at most A, principal         *)
(* logarithms clog, and algebraic coefficients bt r, roots of integer        *)
(* polynomials ab r of degree db r <= d and height at most B:                *)
(*   Lambda = 0 or |Lambda| >= exp(-C g0^K log A log(B log A)),              *)
(* with C and K depending only on n and d (the log log A comes from the      *)
(* factorial denominators of Delta(x; m) at algebraic x). The linear form    *)
(* b1 log eps + b2 log xi + beta3 log(-1) of the class number two problem    *)
(* (Baker/make.ml section 22) is the case n = 3, d = 2. Also the real form   *)
(* for positive real algebraic numbers and real algebraic coefficients.      *)
(*                                                                           *)
(* Main results:                                                             *)
(*  - BAKER_SHARPENING_ALGEBRAIC_COEFFS: SHARPC_BAKER with lg r =            *)
(*    clog(al r), by the principal logarithm step SHARP_ALGDATA_CLOG of      *)
(*    Baker/sharp_main.ml (principal logarithms have imaginary part in       *)
(*    (-pi, pi]).                                                            *)
(*  - SHARPC_SHARPENING_REAL: al r = Cx(x r) and coefficients Cx(bt r),      *)
(*    clog(Cx(x r)) = Cx(log(x r)) (SHARP_VSUM_CLOG_REAL), the polynomial    *)
(*    equations and the linear form through Cx (CX_MUL, CX_POW, VSUM_CX).    *)
(*                                                                           *)
(* Uses: Baker/sharpc_descent.ml (SHARPC_BAKER), Baker/sharp_main.ml         *)
(* (SHARP_ALGDATA_CLOG, SHARP_VSUM_CLOG_REAL), Baker/sharp_defs.ml           *)
(* (sharpc_bound_property), Baker/uniform.ml (sharpc_coefdata).              *)
(* ========================================================================= *)

needs "Baker/sharp_main.ml";;
needs "Baker/sharpc_descent.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The uniform complex form.                                                 *)
(* ------------------------------------------------------------------------- *)

let BAKER_SHARPENING_ALGEBRAIC_COEFFS = prove
 (`!n d. 1 <= n
         ==> ?C K. !(al:num->complex) (a:num->num->real) (dd:num->num)
                    (bt:num->complex) (ab:num->num->real) (db:num->num)
                    A B g0.
                     &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
                     (!r. r IN 1..n
                          ==> ~(al r = Cx(&0)) /\ 1 <= dd r /\ dd r <= d /\
                              (!j. integer(a r j)) /\ ~(a r (dd r) = &0) /\
                              vsum(0..dd r) (\j. Cx(a r j) * al r pow j) =
                              Cx(&0) /\
                              1 <= db r /\ db r <= d /\
                              (!j. integer(ab r j) /\ abs(ab r j) <= B) /\
                              ~(ab r (db r) = &0) /\
                              vsum(0..db r) (\j. Cx(ab r j) * bt r pow j) =
                              Cx(&0)) /\
                     (!r j. r IN 1..n-1 ==> abs(a r j) <= exp g0) /\
                     (!j. abs(a n j) <= A) /\
                     ~(vsum(1..n) (\r. bt r * clog(al r)) = Cx(&0))
                     ==> exp(--(C * g0 pow K * log A * log(B * log A))) <=
                         norm(vsum(1..n) (\r. bt r * clog(al r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `d:num`] SHARPC_BAKER) THEN
  ASM_REWRITE_TAC[sharpc_bound_property; sharpc_coefdata] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`al:num->complex`; `a:num->num->real`; `dd:num->num`;
    `bt:num->complex`; `ab:num->num->real`; `db:num->num`;
    `A:real`; `B:real`; `g0:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `al:num->complex`; `a:num->num->real`;
                `dd:num->num`; `A:real`; `g0:real`] SHARP_ALGDATA_CLOG) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. clog((al:num->complex) r)`; `a:num->num->real`; `dd:num->num`;
    `bt:num->complex`; `ab:num->num->real`; `db:num->num`;
    `A:real`; `B:real`; `g0:real`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The real form: positive real algebraic numbers, real logarithms and real  *)
(* algebraic coefficients.                                                   *)
(* ------------------------------------------------------------------------- *)

let SHARPC_SHARPENING_REAL = prove
 (`!n d. 1 <= n
         ==> ?C K. !(x:num->real) (a:num->num->real) (dd:num->num)
                    (bt:num->real) (ab:num->num->real) (db:num->num)
                    A B g0.
                     &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
                     (!r. r IN 1..n
                          ==> &0 < x r /\ 1 <= dd r /\ dd r <= d /\
                              (!j. integer(a r j)) /\ ~(a r (dd r) = &0) /\
                              sum(0..dd r) (\j. a r j * x r pow j) = &0 /\
                              1 <= db r /\ db r <= d /\
                              (!j. integer(ab r j) /\ abs(ab r j) <= B) /\
                              ~(ab r (db r) = &0) /\
                              sum(0..db r) (\j. ab r j * bt r pow j) = &0) /\
                     (!r j. r IN 1..n-1 ==> abs(a r j) <= exp g0) /\
                     (!j. abs(a n j) <= A) /\
                     ~(sum(1..n) (\r. bt r * log(x r)) = &0)
                     ==> exp(--(C * g0 pow K * log A * log(B * log A))) <=
                         abs(sum(1..n) (\r. bt r * log(x r)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `d:num`] BAKER_SHARPENING_ALGEBRAIC_COEFFS) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`x:num->real`; `a:num->num->real`; `dd:num->num`; `bt:num->real`;
    `ab:num->num->real`; `db:num->num`; `A:real`; `B:real`; `g0:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `x:num->real`; `bt:num->real`]
    SHARP_VSUM_CLOG_REAL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r. Cx((x:num->real) r)`; `a:num->num->real`; `dd:num->num`;
    `\r. Cx((bt:num->real) r)`; `ab:num->num->real`; `db:num->num`;
    `A:real`; `B:real`; `g0:real`]) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[CX_INJ; GSYM CX_POW; GSYM CX_MUL; VSUM_CX; REAL_LT_IMP_NZ]);;
