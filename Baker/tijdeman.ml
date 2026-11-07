(* ========================================================================= *)
(* Tijdeman Theorem 2 for rationals and the Catalan exponent bound.          *)
(*                                                                           *)
(* Purpose: Tijdeman (Acta Arith 29 (1976), Thm 2) for positive rationals,   *)
(* i.e. Baker, Sharpening I with explicit dependence on the heights exp(g0)  *)
(* and A, as the case d = 1 of BAKER_SHARPENING_REAL (u / v is the root of   *)
(* the integer polynomial v X - u), and the unconditional bound for the      *)
(* exponents of the Catalan equation x^p - y^q = 1 (Tijdeman 1976, sec 5).   *)
(*                                                                           *)
(* Main results: SHARP_BAKER_RATIONAL (?C K. sharp_bound_property n C K),    *)
(*   TIJDEMAN_LINEAR_FORMS_RATIONAL (the same, unfolded),                    *)
(*   CATALAN_EXPONENT_BOUND (?M. for distinct odd primes p, q and            *)
(*   x, y >= 2, x^p = y^q + 1 ==> p <= M /\ q <= M),                         *)
(*   CATALAN_ODD_PRIME_FACTORS_BOUNDED (the odd prime factors of the         *)
(*   exponents of x^m = y^n + 1 are bounded).                                *)
(*                                                                           *)
(* Uses: Baker/sharp_main.ml (BAKER_SHARPENING_REAL), Baker/catalan.ml       *)
(*   (sharp_bound_property and the conditional bounds).                      *)
(* ========================================================================= *)

needs "Baker/sharp_main.ml";;
needs "Baker/catalan.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Tijdeman Theorem 2 for positive rationals is the case d = 1 of Baker,     *)
(* Sharpening I for algebraic numbers (BAKER_SHARPENING_REAL): u / v is the  *)
(* root of the integer polynomial v X - u of degree 1, whose coefficients    *)
(* are bounded by the height bounds exp(g0) and A of u and v.                *)
(* ------------------------------------------------------------------------- *)

let SHARP_BAKER_RATIONAL = prove
 (`!n. 1 <= n ==> ?C K. sharp_bound_property n C K`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `1`] BAKER_SHARPENING_REAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` (X_CHOOSE_TAC `K:num`)) THEN
  MAP_EVERY EXISTS_TAC [`C:real`; `K:num`] THEN
  REWRITE_TAC[sharp_bound_property] THEN
  MAP_EVERY X_GEN_TAC
   [`u:num->num`; `v:num->num`; `bb:num->real`;
    `A:real`; `B:real`; `g0:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`\r:num. &(u r) / &(v r)`;
    `\(r:num) (j:num). if j = 0 then --(&(u r)) else if j = 1 then &(v r)
                       else &0`;
    `\r:num. 1`; `bb:num->real`; `A:real`; `B:real`; `g0:real`]) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[LE_REFL] THEN
  SUBGOAL_THEN `&0 <= exp g0 /\ &0 <= A` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LE] THEN
    MP_TAC(SPEC `&1` REAL_EXP_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `1 <= (u:num->num) r /\ 1 <= (v:num->num) r /\
                  integer((bb:num->real) r) /\ abs(bb r) <= B`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[ARITH] THEN
    SUBGOAL_THEN `&1 <= &((u:num->num) r) /\ &1 <= &((v:num->num) r)`
      STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      GEN_TAC THEN REPEAT COND_CASES_TAC THEN
      SIMP_TAC[INTEGER_CLOSED];
      ASM_REAL_ARITH_TAC;
      SIMP_TAC[SUM_CLAUSES_LEFT; LE_0; ARITH; SUM_TRIV_NUMSEG] THEN
      REWRITE_TAC[real_pow; REAL_POW_1; ARITH] THEN
      UNDISCH_TAC `&1 <= &((v:num->num) r)` THEN CONV_TAC REAL_FIELD];
    MAP_EVERY X_GEN_TAC [`r:num`; `j:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&((u:num->num) r) <= exp g0 /\ &((v:num->num) r) <= exp g0`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_ABS_0];
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_NUM; REAL_ABS_0]]);;

let TIJDEMAN_LINEAR_FORMS_RATIONAL = prove
 (`!n. 1 <= n
       ==> ?C K. !(u:num->num) (v:num->num) (bb:num->real) A B g0.
                   &1 <= g0 /\ exp(&1) <= A /\ &2 <= B /\
                   (!r. r IN 1..n ==> 1 <= u r /\ 1 <= v r /\
                                      integer(bb r) /\ abs(bb r) <= B) /\
                   (!r. r IN 1..n-1 ==> &(u r) <= exp g0 /\ &(v r) <= exp g0) /\
                   &(u n) <= A /\ &(v n) <= A /\
                   ~(sum(1..n) (\r. bb r * log(&(u r) / &(v r))) = &0)
                   ==> exp(--(C * g0 pow K * log A * log B)) <=
                       abs(sum(1..n) (\r. bb r * log(&(u r) / &(v r))))`,
  REWRITE_TAC[GSYM sharp_bound_property; SHARP_BAKER_RATIONAL]);;

let CATALAN_EXPONENT_BOUND = prove
 (`?M. !p q x y. prime p /\ prime q /\ ODD p /\ ODD q /\ ~(p = q) /\
                 2 <= x /\ 2 <= y /\ x EXP p = y EXP q + 1
                 ==> p <= M /\ q <= M`,
  MP_TAC(SPEC `2` SHARP_BAKER_RATIONAL) THEN
  MP_TAC(SPEC `3` SHARP_BAKER_RATIONAL) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real` (X_CHOOSE_TAC `K3:num`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (X_CHOOSE_TAC `K2:num`)) THEN
  MATCH_MP_TAC CATALAN_EXPONENT_BOUND_CONDITIONAL THEN
  MAP_EVERY EXISTS_TAC [`C2:real`; `K2:num`; `C3:real`; `K3:num`] THEN
  ASM_REWRITE_TAC[]);;

let CATALAN_ODD_PRIME_FACTORS_BOUNDED = prove
 (`?M. !m n x y p q.
         2 <= m /\ 2 <= n /\ 2 <= x /\ 2 <= y /\ x EXP m = y EXP n + 1 /\
         prime p /\ ODD p /\ p divides m /\ prime q /\ ODD q /\ q divides n
         ==> p <= M /\ q <= M`,
  MP_TAC(SPEC `2` SHARP_BAKER_RATIONAL) THEN
  MP_TAC(SPEC `3` SHARP_BAKER_RATIONAL) THEN REWRITE_TAC[ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real` (X_CHOOSE_TAC `K3:num`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real` (X_CHOOSE_TAC `K2:num`)) THEN
  MATCH_MP_TAC CATALAN_ODD_PRIME_FACTORS_CONDITIONAL THEN
  MAP_EVERY EXISTS_TAC [`C2:real`; `K2:num`; `C3:real`; `K3:num`] THEN
  ASM_REWRITE_TAC[]);;
