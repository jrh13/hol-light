(* ========================================================================= *)
(* Fermat Last Theorem for the exponent 3 (Euler), by descent in the ring    *)
(* of Eisenstein integers.                                                   *)
(*                                                                           *)
(* Purpose: x^3 + y^3 = z^3 in integers forces x y z = 0 (FLT3_INT), and     *)
(* over the natural numbers x = 0 or y = 0 (FLT3); in the Eisenstein         *)
(* integers, alpha^3 + beta^3 + eps gm^3 = 0 has no solution with alpha,     *)
(* beta, gm nonzero and pairwise coprime, eps a unit (FLT3_EISENSTEIN,       *)
(* FLT3_EISENSTEIN_CUBES).                                                   *)
(*                                                                           *)
(* Method (the classical proof in the Eisenstein integers, Hardy-Wright Thm. *)
(* 228, Ireland-Rosen 17.8): the ring O = imag_quadratic_integers 3 of       *)
(* integers of Q(sqrt(-3)) is Z[r] with r = quad_omega 3 = (1 + sqrt(-3))/2, *)
(* r^2 = r - 1, r^3 = -1; w = r - 1 is a primitive cube root of unity, w^2 = *)
(* -r; O is a UFD (Euclidean: IMAG_QUADRATIC_INTEGERS_UFD). The element L =  *)
(* 2 - r = 1 - w has norm 3 and is prime, 3 = r L^2, and every element is    *)
(* congruent to 0, 1 or -1 modulo L (FLT3_RESIDUE); hence x^3 = x mod L and, *)
(* for L not dividing x, x^3 = +-1 mod L^3 (FLT3_CUBE_RESIDUE), even mod L^4 *)
(* (FLT3_CUBE_RESIDUE4). Descent (FLT3_DESCENT): there are no xi, eta, gm    *)
(* in O, unit eps and n >= 1 with xi, eta coprime, L dividing neither eta    *)
(* nor gm, and xi^3 + eta^3 = eps L^(3n) gm^3. Replacing eta by w eta        *)
(* or w^2 eta one gets L^2 | xi + eta (FLT3_ROTATE); then a1 = (xi + eta)/L, *)
(* a2 = a1 - eta, a3 = a1 - r eta are pairwise coprime, L | a1, L divides    *)
(* neither a2 nor a3, a1 + w a2 + w^2 a3 = 0 and a1 a2 a3 = eps L^(3(n-1))   *)
(* gm^3 (FLT3_STEP_SETUP). So n >= 2, a1 = L^(3(n-1)) b1 and b1, a2, a3      *)
(* are units times cubes t1^3, t2^3, t3^3 (UFD_COPRIME_MUL_POW); the         *)
(* relation t2^3 + e1 t3^3 = e2 L^(3(n-1)) t1^3 with units e1, e2 and the    *)
(* cube residues mod L^3 give e1 = +-1 (a norm bound), hence a solution with *)
(* n - 1 (FLT3_STEP). In O: if L divides none of alpha, beta, gm the cube    *)
(* residues mod L^4 exclude a solution, otherwise the L-adic split           *)
(* (FLT3_LAMBDA_SPLIT) reduces to the descent. For integers: after dividing  *)
(* by gcd(x,y), if 3 divides none of x, y, z then cubes are +-1 mod 9        *)
(* (FLT3_INT_CASE1); otherwise, by symmetry, 3 | z = 3^k z0 and z^3 = r^(3k) *)
(* L^(6k) z0^3, which the descent excludes (FLT3_INT_CASE2).                 *)
(*                                                                           *)
(* Main results: FLT3_INT, FLT3, FLT3_EISENSTEIN, FLT3_EISENSTEIN_CUBES;     *)
(* also FLT3_DESCENT. Helper names with prefix FLT3.                         *)
(*                                                                           *)
(* Uses: Baker/quadint_ant.ml (IMAG_QUADRATIC_INTEGERS_CLAUSES,              *)
(* IMAG_QUADRATIC_INTEGERS_SUB_POW) and Baker/quadint_ring.ml (the           *)
(* IMAG_QUADRATIC_INTEGERS and QUAD_OMEGA lemmas,                            *)
(* IMAG_QUADRATIC_INTEGERS_UFD), ANT/ufd.ml (UFD_COPRIME_MUL_POW),           *)
(* Library/ringtheory.ml (RING_COPRIME_DIVISORS, RING_COPRIME_LPOW,          *)
(* RING_ASSOCIATES_COPRIME and the ring lemmas), Library/floor.ml            *)
(* (INTEGER_ROUND), Library/prime.ml (PRIME_POWER_MULT).                     *)
(* ========================================================================= *)

needs "ANT/ufd.ml";;
needs "Baker/quadint_ring.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The ring O = Z[r] of Eisenstein integers, r = (1 + sqrt(-3))/2: UFD,      *)
(* carrier, closure, units.                                                  *)
(* ------------------------------------------------------------------------- *)

let FLT3_SQUAREFREE = prove
 (`squarefree 3`,
  MATCH_MP_TAC PRIME_IMP_SQUAREFREE THEN CONV_TAC PRIME_CONV);;

let FLT3_UFD = prove
 (`UFD(imag_quadratic_integers 3)`,
  MATCH_MP_TAC IMAG_QUADRATIC_INTEGERS_UFD THEN REWRITE_TAC[IN_INSERT]);;

let FLT3_OMEGA_SQUARE = prove
 (`quad_omega 3 pow 2 = quad_omega 3 - Cx(&1)`,
  REWRITE_TAC[QUAD_OMEGA_SQUARE] THEN CONV_TAC NUM_REDUCE_CONV);;

let FLT3_IN = prove
 (`!z. z IN ring_carrier(imag_quadratic_integers 3) <=>
       ?a b. integer a /\ integer b /\ z = Cx a + Cx b * quad_omega 3`,
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_IN; FLT3_SQUAREFREE]);;

let FLT3_CLOSED = prove
 (`(!x. integer x ==> Cx x IN ring_carrier(imag_quadratic_integers 3)) /\
   (!n. Cx(&n) IN ring_carrier(imag_quadratic_integers 3)) /\
   quad_omega 3 IN ring_carrier(imag_quadratic_integers 3) /\
   (!x y. x IN ring_carrier(imag_quadratic_integers 3) /\
          y IN ring_carrier(imag_quadratic_integers 3)
          ==> x + y IN ring_carrier(imag_quadratic_integers 3)) /\
   (!x y. x IN ring_carrier(imag_quadratic_integers 3) /\
          y IN ring_carrier(imag_quadratic_integers 3)
          ==> x - y IN ring_carrier(imag_quadratic_integers 3)) /\
   (!x y. x IN ring_carrier(imag_quadratic_integers 3) /\
          y IN ring_carrier(imag_quadratic_integers 3)
          ==> x * y IN ring_carrier(imag_quadratic_integers 3)) /\
   (!x. x IN ring_carrier(imag_quadratic_integers 3)
        ==> --x IN ring_carrier(imag_quadratic_integers 3)) /\
   (!x n. x IN ring_carrier(imag_quadratic_integers 3)
          ==> x pow n IN ring_carrier(imag_quadratic_integers 3))`,
  MP_TAC(SPEC `3` IMAG_QUADRATIC_INTEGERS_CLOSED) THEN
  SIMP_TAC[INTEGER_CLOSED]);;

let FLT3_LAMBDA_IN = prove
 (`Cx(&2) - quad_omega 3 IN ring_carrier(imag_quadratic_integers 3)`,
  SIMP_TAC[FLT3_CLOSED]);;

(* Membership in the carrier (and integrality) by the closure rules. The    *)
(* simplifier gives up on deeply nested side conditions, so this tactic      *)
(* applies the closure rules one by one; it fails unless it solves the goal. *)

let FLT3_CARRIER_TAC : tactic =
  let cths = CONJUNCTS FLT3_CLOSED and iths = CONJUNCTS INTEGER_CLOSED in
  let acc = [FLT3_LAMBDA_IN; el 1 cths; el 2 cths; el 0 iths] in
  let mps = tl(tl(tl cths)) @ [el 0 cths] @ tl iths in
  REPEAT(CONJ_TAC ORELSE FIRST_ASSUM ACCEPT_TAC ORELSE
         FIRST(map MATCH_ACCEPT_TAC acc) ORELSE
         FIRST(map MATCH_MP_TAC mps)) THEN NO_TAC;;

let FLT3_THREE = prove
 (`Cx(&3) = quad_omega 3 * (Cx(&2) - quad_omega 3) pow 2`,
  MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING);;

let FLT3_LAMBDA_NORM = prove
 (`norm(Cx(&2) - quad_omega 3) pow 2 = &3`,
  MP_TAC(SPECL [`3`; `&2`; `-- &1`] QUAD_OMEGA_NORM) THEN
  REWRITE_TAC[CX_NEG] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_LID; GSYM complex_sub] THEN
  DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

let FLT3_LAMBDA_NZ = prove
 (`~(Cx(&2) - quad_omega 3 = Cx(&0))`,
  DISCH_TAC THEN MP_TAC FLT3_LAMBDA_NORM THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN REAL_ARITH_TAC);;

let FLT3_MULT_EQ_3 = prove
 (`!m n. m * n = 3 ==> m = 1 \/ n = 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`1`; `m:num`; `n:num`; `3`] PRIME_POWER_MULT) THEN
  ASM_REWRITE_TAC[EXP_1; PRIME_3; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  UNDISCH_TAC `m * n = 3` THEN ASM_REWRITE_TAC[GSYM EXP_ADD; EXP_EQ_1] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM EXP_1] THEN
  REWRITE_TAC[EQ_EXP] THEN ARITH_TAC);;

let FLT3_NORM_EQ_1 = prove
 (`!z:complex. norm z pow 2 = &1 <=> norm z = &1`,
  GEN_TAC THEN EQ_TAC THENL
   [MP_TAC(SPECL [`norm(z:complex)`; `2`] REAL_POW_EQ_1_IMP) THEN
    REWRITE_TAC[ARITH_EQ] THEN
    SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> abs x = x`];
    SIMP_TAC[REAL_POW_ONE]]);;

let FLT3_LAMBDA_PRIME = prove
 (`ring_prime (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)`,
  SIMP_TAC[GSYM UFD_IRREDUCIBLE_EQ_PRIME; FLT3_UFD] THEN
  REWRITE_TAC[ring_irreducible; IMAG_QUADRATIC_INTEGERS_CLAUSES;
              IMAG_QUADRATIC_INTEGERS_UNIT; FLT3_LAMBDA_IN;
              FLT3_LAMBDA_NZ; GSYM FLT3_NORM_EQ_1; FLT3_LAMBDA_NORM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MAP_EVERY X_GEN_TAC [`a:complex`; `b:complex`] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`3`; `a:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  MP_TAC(SPECL [`3`; `b:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  MP_TAC FLT3_LAMBDA_NORM THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check ((=) `a * b = Cx(&2) - quad_omega 3` o concl)) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL; REAL_OF_NUM_MUL;
                  REAL_OF_NUM_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FLT3_MULT_EQ_3) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let FLT3_LAMBDA_NOT_UNIT = prove
 (`~ring_unit (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)`,
  MP_TAC FLT3_LAMBDA_PRIME THEN SIMP_TAC[ring_prime]);;

let FLT3_UNIT_NZ = prove
 (`!u. ring_unit (imag_quadratic_integers 3) u ==> ~(u = Cx(&0))`,
  SIMP_TAC[IMAG_QUADRATIC_INTEGERS_UNIT_INV]);;

let FLT3_UNIT_MUL = prove
 (`!u v. ring_unit (imag_quadratic_integers 3) u /\
         ring_unit (imag_quadratic_integers 3) v
         ==> ring_unit (imag_quadratic_integers 3) (u * v)`,
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_MUL) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES]);;

let FLT3_UNIT_NEG = prove
 (`!u. ring_unit (imag_quadratic_integers 3) u
       ==> ring_unit (imag_quadratic_integers 3) (--u)`,
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_NEG) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES]);;

let FLT3_UNIT_POW = prove
 (`!u n. ring_unit (imag_quadratic_integers 3) u
         ==> ring_unit (imag_quadratic_integers 3) (u pow n)`,
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_POW) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_SUB_POW]);;

let FLT3_UNIT_INV = prove
 (`!u. ring_unit (imag_quadratic_integers 3) u
       ==> ring_unit (imag_quadratic_integers 3) (inv u)`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_UNIT; COMPLEX_NORM_INV] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[IMAG_QUADRATIC_INTEGERS_UNIT_INV];
    ASM_MESON_TAC[IMAG_QUADRATIC_INTEGERS_UNIT; REAL_INV_1]]);;

let FLT3_UNIT_DIV = prove
 (`!u v. ring_unit (imag_quadratic_integers 3) u /\
         ring_unit (imag_quadratic_integers 3) v
         ==> ring_unit (imag_quadratic_integers 3) (u / v)`,
  SIMP_TAC[complex_div; FLT3_UNIT_MUL; FLT3_UNIT_INV]);;

let FLT3_UNIT_OMEGA = prove
 (`ring_unit (imag_quadratic_integers 3) (quad_omega 3) /\
   ring_unit (imag_quadratic_integers 3) (quad_omega 3 - Cx(&1))`,
  REWRITE_TAC[ring_unit; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  SIMP_TAC[FLT3_CLOSED] THEN CONJ_TAC THENL
   [EXISTS_TAC `Cx(&1) - quad_omega 3`; EXISTS_TAC `--quad_omega 3`] THEN
  SIMP_TAC[FLT3_CLOSED] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Residues modulo L = 2 - r: every element is 0, 1 or -1 mod L, so          *)
(* x^3 = x mod L, and x^3 = +-1 mod L^3 when L does not divide x.            *)
(* ------------------------------------------------------------------------- *)

let FLT3_INTEGER_MOD3 = prove
 (`!t. integer t
       ==> ?k s. integer k /\ (s = &0 \/ s = &1 \/ s = -- &1) /\
                 t = &3 * k + s`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC (SPEC `t / &3` INTEGER_ROUND) THEN
  MAP_EVERY EXISTS_TAC [`k:real`; `t - &3 * k`] THEN
  ASM_REWRITE_TAC[REAL_ARITH `t = &3 * k + (t - &3 * k:real)`] THEN
  MAP_EVERY (MP_TAC o C SPEC REAL_ABS_INTEGER_LEMMA)
   [`t - &3 * k:real`; `t - &3 * k - &1:real`; `t - &3 * k + &1:real`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN ASM_REAL_ARITH_TAC);;

let FLT3_INTEGER_PM = prove
 (`!s. (s = &0 \/ s = &1 \/ s = -- &1) ==> integer s`,
  GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[INTEGER_CLOSED]);;

let FLT3_RESIDUE = prove
 (`!x. x IN ring_carrier(imag_quadratic_integers 3)
       ==> ?s. (s = &0 \/ s = &1 \/ s = -- &1) /\
               ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) (x - Cx s)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FLT3_IN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPEC `a - b:real` FLT3_INTEGER_MOD3) THEN
  ASM_SIMP_TAC[INTEGER_SUB] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` (X_CHOOSE_THEN `s:real`
    (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC))) THEN
  EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLT3_INTEGER_PM) THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  EXISTS_TAC `Cx k * quad_omega 3 * (Cx(&2) - quad_omega 3) +
              Cx b * (quad_omega 3 * (Cx(&2) - quad_omega 3) - Cx(&1))` THEN
  CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `Cx` o
    check ((=) `a - b = &3 * k + s` o concl)) THEN
  REWRITE_TAC[CX_SUB; CX_ADD; CX_MUL] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
  CONV_TAC COMPLEX_RING);;

let FLT3_CUBE_SELF = prove
 (`!x. x IN ring_carrier(imag_quadratic_integers 3)
       ==> ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
             (x pow 3 - x)`,
  GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FLT3_RESIDUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLT3_INTEGER_PM) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:complex` STRIP_ASSUME_TAC))) THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  EXISTS_TAC `c * (x pow 2 + x * Cx s + Cx s pow 2 - Cx(&1))` THEN
  CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
  UNDISCH_TAC `x - Cx s = (Cx(&2) - quad_omega 3) * c` THEN
  UNDISCH_TAC `s = &0 \/ s = &1 \/ s = -- &1` THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING);;

let FLT3_CUBE_RESIDUE = prove
 (`!x. x IN ring_carrier(imag_quadratic_integers 3) /\
       ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) x
       ==> ?s. (s = &1 \/ s = -- &1) /\
               ring_divides (imag_quadratic_integers 3)
                 ((Cx(&2) - quad_omega 3) pow 3) (x pow 3 - Cx s)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FLT3_RESIDUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_RZERO]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLT3_INTEGER_PM) THEN
  SUBGOAL_THEN `s = &1 \/ s = -- &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:complex` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  EXISTS_TAC `quad_omega 3 * t +
              quad_omega 3 * Cx s * (Cx(&2) - quad_omega 3) * t pow 2 +
              t pow 3` THEN
  CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
  UNDISCH_TAC `x - Cx s = (Cx(&2) - quad_omega 3) * t` THEN
  UNDISCH_TAC `s = &1 \/ s = -- &1` THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CX_NEG] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Norms: nonzero elements have norm >= 1, divisors have smaller norm, and   *)
(* a unit e with L^2 | s + e t (s, t = +-1) is +-1, since |L^2| = 3 > 2.     *)
(* ------------------------------------------------------------------------- *)

let FLT3_NORM_GE_1 = prove
 (`!z. z IN ring_carrier(imag_quadratic_integers 3) /\ ~(z = Cx(&0))
       ==> &1 <= norm z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`3`; `z:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[NORM_POS_LE; ARITH_EQ; REAL_POW_ONE; REAL_OF_NUM_LE] THEN
  ASM_CASES_TAC `n = 0` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  UNDISCH_TAC `norm(z:complex) pow 2 = &n` THEN
  ASM_REWRITE_TAC[REAL_POW_EQ_0; COMPLEX_NORM_ZERO; ARITH_EQ]);;

let FLT3_DIVIDES_NORM_LE = prove
 (`!a b. ring_divides (imag_quadratic_integers 3) a b /\ ~(b = Cx(&0))
         ==> norm a <= norm b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `c:complex`
     STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC FLT3_NORM_GE_1 THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN UNDISCH_TAC `~(a * c = Cx(&0))` THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_RZERO]);;

let FLT3_LAMBDA_SQUARE_NORM = prove
 (`norm((Cx(&2) - quad_omega 3) pow 2) = &3`,
  REWRITE_TAC[COMPLEX_NORM_POW; FLT3_LAMBDA_NORM]);;

let FLT3_UNIT_PM1_ZERO = prove
 (`!e s t. ring_unit (imag_quadratic_integers 3) e /\
           (s = &1 \/ s = -- &1) /\ (t = &1 \/ t = -- &1) /\
           ring_divides (imag_quadratic_integers 3)
             ((Cx(&2) - quad_omega 3) pow 2) (Cx s + e * Cx t)
           ==> Cx s + e * Cx t = Cx(&0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL [`(Cx(&2) - quad_omega 3) pow 2`; `Cx s + e * Cx t`]
    FLT3_DIVIDES_NORM_LE) THEN
  ASM_REWRITE_TAC[REAL_NOT_LE; FLT3_LAMBDA_SQUARE_NORM] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(Cx s) + norm(e * Cx t)` THEN
  REWRITE_TAC[NORM_TRIANGLE; COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  FIRST_ASSUM(SUBST1_TAC o CONJUNCT2 o
    GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_UNIT]) THEN
  MAP_EVERY UNDISCH_TAC [`s = &1 \/ s = -- &1`; `t = &1 \/ t = -- &1`] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN REAL_ARITH_TAC);;

let FLT3_UNIT_PM1 = prove
 (`!e s t. ring_unit (imag_quadratic_integers 3) e /\
           (s = &1 \/ s = -- &1) /\ (t = &1 \/ t = -- &1) /\
           ring_divides (imag_quadratic_integers 3)
             ((Cx(&2) - quad_omega 3) pow 2) (Cx s + e * Cx t)
           ==> e = Cx(&1) \/ e = --Cx(&1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FLT3_UNIT_PM1_ZERO) THEN
  FIRST_X_ASSUM(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MAP_EVERY UNDISCH_TAC [`s = &1 \/ s = -- &1`; `t = &1 \/ t = -- &1`] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING);;

let FLT3_UNIT_PM = prove
 (`!s. (s = &1 \/ s = -- &1)
       ==> ring_unit (imag_quadratic_integers 3) (Cx s)`,
  GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CX_NEG] THEN TRY(MATCH_MP_TAC FLT3_UNIT_NEG) THEN
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_1) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES]);;

let FLT3_LAMBDA_NOT_DIVIDES_UNIT = prove
 (`!u. ring_unit (imag_quadratic_integers 3) u
       ==> ~ring_divides (imag_quadratic_integers 3)
              (Cx(&2) - quad_omega 3) u`,
  MESON_TAC[RING_UNIT_DIVISOR; FLT3_LAMBDA_NOT_UNIT]);;

(* ------------------------------------------------------------------------- *)
(* Divisibility and coprimality helpers.                                     *)
(* ------------------------------------------------------------------------- *)

let FLT3_COPRIME_PRIME_POW = prove
 (`!r p x:A n.
        UFD r /\ ring_prime r p /\ x IN ring_carrier r /\
        ~ring_divides r p x
        ==> ring_coprime r (ring_pow r p n,x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RING_COPRIME_LPOW THEN
  ASM_SIMP_TAC[RING_PRIME_IN_CARRIER; INTEGRAL_DOMAIN_PRIME_COPRIME_EQ;
               UFD_IMP_INTEGRAL_DOMAIN]);;

let FLT3_DIVIDES_LINEAR = prove
 (`!d a b u v.
        ring_divides (imag_quadratic_integers 3) d a /\
        ring_divides (imag_quadratic_integers 3) d b /\
        u IN ring_carrier(imag_quadratic_integers 3) /\
        v IN ring_carrier(imag_quadratic_integers 3)
        ==> ring_divides (imag_quadratic_integers 3) d (u * a + v * b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_ADD) THEN
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_LMUL) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN ASM_MESON_TAC[]);;

let FLT3_COPRIME_COMB = prove
 (`!x y a b u v u' v'.
        ring_coprime (imag_quadratic_integers 3) (x,y) /\
        a IN ring_carrier(imag_quadratic_integers 3) /\
        b IN ring_carrier(imag_quadratic_integers 3) /\
        u IN ring_carrier(imag_quadratic_integers 3) /\
        v IN ring_carrier(imag_quadratic_integers 3) /\
        u' IN ring_carrier(imag_quadratic_integers 3) /\
        v' IN ring_carrier(imag_quadratic_integers 3) /\
        x = u * a + v * b /\ y = u' * a + v' * b
        ==> ring_coprime (imag_quadratic_integers 3) (a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ring_coprime] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `d:complex` THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[FLT3_DIVIDES_LINEAR]);;

let FLT3_COPRIME_RMUL = prove
 (`!a b c. a IN ring_carrier(imag_quadratic_integers 3) /\
           b IN ring_carrier(imag_quadratic_integers 3) /\
           c IN ring_carrier(imag_quadratic_integers 3)
           ==> (ring_coprime (imag_quadratic_integers 3) (a,b * c) <=>
                ring_coprime (imag_quadratic_integers 3) (a,b) /\
                ring_coprime (imag_quadratic_integers 3) (a,c))`,
  MP_TAC(ISPEC `imag_quadratic_integers 3` RING_COPRIME_RMUL) THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES; FLT3_UFD]);;

let FLT3_UNIT_MUL_CUBE = prove
 (`!a b c u.
        a IN ring_carrier(imag_quadratic_integers 3) /\
        b IN ring_carrier(imag_quadratic_integers 3) /\
        c IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) u /\
        ring_coprime (imag_quadratic_integers 3) (a,b) /\
        a * b = u * c pow 3
        ==> ?v t. ring_unit (imag_quadratic_integers 3) v /\
                  t IN ring_carrier(imag_quadratic_integers 3) /\
                  a = v * t pow 3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLT3_UNIT_NZ) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLT3_UNIT_INV) THEN
  MP_TAC(ISPECL [`imag_quadratic_integers 3`; `a:complex`;
                 `inv u * b:complex`; `c:complex`; `3`]
    UFD_COPRIME_MUL_POW) THEN
  REWRITE_TAC[FLT3_UFD; IMAG_QUADRATIC_INTEGERS_CLAUSES;
              IMAG_QUADRATIC_INTEGERS_SUB_POW] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `inv u IN ring_carrier(imag_quadratic_integers 3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FLT3_CARRIER_TAC;
    MP_TAC(ISPECL [`imag_quadratic_integers 3`; `a:complex`; `b:complex`;
                   `a:complex`; `inv u * b:complex`]
      RING_ASSOCIATES_COPRIME) THEN
    MP_TAC(ISPECL [`imag_quadratic_integers 3`; `b:complex`; `inv u:complex`]
      RING_ASSOCIATES_LMUL) THEN
    ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES; RING_ASSOCIATES_REFL] THEN
    SIMP_TAC[];
    UNDISCH_TAC `(a:complex) * b = u * c pow 3` THEN
    UNDISCH_TAC `~(u = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD]);;

let FLT3_LAMBDA_DIVIDES_CUBE = prove
 (`!u x. ring_unit (imag_quadratic_integers 3) u /\
         x IN ring_carrier(imag_quadratic_integers 3) /\
         ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
           (u * x pow 3)
         ==> ring_divides (imag_quadratic_integers 3)
               (Cx(&2) - quad_omega 3) x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`imag_quadratic_integers 3`; `Cx(&2) - quad_omega 3`]
    RING_PRIME_DIVIDES_MUL) THEN
  REWRITE_TAC[FLT3_LAMBDA_PRIME; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `x * x IN ring_carrier(imag_quadratic_integers 3) /\
                x * x * x IN ring_carrier(imag_quadratic_integers 3) /\
                u IN ring_carrier(imag_quadratic_integers 3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; ASM_MESON_TAC[RING_UNIT_IN_CARRIER]];
    ALL_TAC] THEN
  UNDISCH_TAC `ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) (u * x pow 3)` THEN
  REWRITE_TAC[COMPLEX_RING `(x:complex) pow 3 = x * x * x`] THEN
  ASM_SIMP_TAC[] THEN
  MESON_TAC[FLT3_LAMBDA_NOT_UNIT; RING_UNIT_DIVISOR;
            ASSUME `ring_unit (imag_quadratic_integers 3) u`]);;

(* ------------------------------------------------------------------------- *)
(* The descent. First, replacing eta by w eta or w^2 eta (w = r - 1,         *)
(* w^2 = -r) one may assume L^2 | xi + eta.                                  *)
(* ------------------------------------------------------------------------- *)

let FLT3_ROTATE = prove
 (`!xi eta.
        xi IN ring_carrier(imag_quadratic_integers 3) /\
        eta IN ring_carrier(imag_quadratic_integers 3) /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) eta /\
        ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
          (xi pow 3 + eta pow 3)
        ==> ring_divides (imag_quadratic_integers 3)
              ((Cx(&2) - quad_omega 3) pow 2) (xi + eta) \/
            ring_divides (imag_quadratic_integers 3)
              ((Cx(&2) - quad_omega 3) pow 2)
              (xi + (quad_omega 3 - Cx(&1)) * eta) \/
            ring_divides (imag_quadratic_integers 3)
              ((Cx(&2) - quad_omega 3) pow 2) (xi - quad_omega 3 * eta)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
      (xi + eta)`
  MP_TAC THENL
   [MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_SUB) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_SUB_POW] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(xi:complex) + eta =
                  ((xi pow 3 + eta pow 3) - (xi pow 3 - xi)) -
                  (eta pow 3 - eta)` SUBST1_TAC THENL
     [CONV_TAC COMPLEX_RING; ASM_MESON_TAC[FLT3_CUBE_SELF]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  MP_TAC(MATCH_MP FLT3_RESIDUE
   (ASSUME `a IN ring_carrier(imag_quadratic_integers 3)`)) THEN
  MP_TAC(MATCH_MP FLT3_RESIDUE
   (ASSUME `eta IN ring_carrier(imag_quadratic_integers 3)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `se:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `se = &0` THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_RZERO]; ALL_TAC] THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN(X_CHOOSE_THEN `sa:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `sa = &0 \/ sa = se \/ sa = --se` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`sa = &0 \/ sa = &1 \/ sa = -- &1`; `se = &0 \/ se = &1 \/ se = -- &1`;
      `~(se = &0)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Cx(&2) - quad_omega 3) pow 2 IN
                ring_carrier(imag_quadratic_integers 3)` ASSUME_TAC THENL
   [FLT3_CARRIER_TAC; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [DISJ1_TAC; DISJ2_TAC THEN DISJ1_TAC; DISJ2_TAC THEN DISJ2_TAC] THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THENL
   [EXISTS_TAC `c1:complex`;
    EXISTS_TAC `c1 - c2:complex`;
    EXISTS_TAC `c1 + c2 - quad_omega 3 * eta`] THEN
  (CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
  REWRITE_TAC[CX_NEG] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
  CONV_TAC COMPLEX_RING);;

(* With L^2 | xi + eta: a1 = (xi + eta)/L, a2 = a1 - eta, a3 = a1 - r eta    *)
(* (so L a2 = xi + w eta, L a3 = xi + w^2 eta) are pairwise coprime, L | a1, *)
(* L divides neither a2 nor a3, a1 + w a2 + w^2 a3 = 0, and their product    *)
(* is eps L^(3(n-1)) gm^3.                                                   *)

let FLT3_STEP_SETUP = prove
 (`!n xi eta gm eps.
        1 <= n /\
        xi IN ring_carrier(imag_quadratic_integers 3) /\
        eta IN ring_carrier(imag_quadratic_integers 3) /\
        ring_coprime (imag_quadratic_integers 3) (xi,eta) /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) eta /\
        ring_divides (imag_quadratic_integers 3)
          ((Cx(&2) - quad_omega 3) pow 2) (xi + eta) /\
        xi pow 3 + eta pow 3 =
        eps * (Cx(&2) - quad_omega 3) pow (3 * n) * gm pow 3
        ==> ?a1 a2 a3.
              a1 IN ring_carrier(imag_quadratic_integers 3) /\
              a2 IN ring_carrier(imag_quadratic_integers 3) /\
              a3 IN ring_carrier(imag_quadratic_integers 3) /\
              ring_coprime (imag_quadratic_integers 3) (a1,a2) /\
              ring_coprime (imag_quadratic_integers 3) (a1,a3) /\
              ring_coprime (imag_quadratic_integers 3) (a2,a3) /\
              ring_divides (imag_quadratic_integers 3)
                (Cx(&2) - quad_omega 3) a1 /\
              ~ring_divides (imag_quadratic_integers 3)
                (Cx(&2) - quad_omega 3) a2 /\
              ~ring_divides (imag_quadratic_integers 3)
                (Cx(&2) - quad_omega 3) a3 /\
              a1 + (quad_omega 3 - Cx(&1)) * a2 - quad_omega 3 * a3 =
              Cx(&0) /\
              a1 * a2 * a3 =
              eps * (Cx(&2) - quad_omega 3) pow (3 * (n - 1)) * gm pow 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES] o
    check (fun th -> rand(concl th) = `xi + eta:complex`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  MAP_EVERY EXISTS_TAC
   [`(Cx(&2) - quad_omega 3) * c`;
    `(Cx(&2) - quad_omega 3) * c - eta`;
    `(Cx(&2) - quad_omega 3) * c - quad_omega 3 * eta`] THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FLT3_COPRIME_COMB THEN
    MAP_EVERY EXISTS_TAC
     [`xi:complex`; `eta:complex`; `(Cx(&2) - quad_omega 3) - Cx(&1)`;
      `Cx(&1)`; `Cx(&1)`; `--Cx(&1)`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    UNDISCH_TAC `(xi:complex) + eta = (Cx(&2) - quad_omega 3) pow 2 * c` THEN
    MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FLT3_COPRIME_COMB THEN
    MAP_EVERY EXISTS_TAC
     [`xi:complex`; `eta:complex`; `Cx(&1)`; `Cx(&1) - quad_omega 3`;
      `Cx(&1) - quad_omega 3`; `quad_omega 3 - Cx(&1)`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    UNDISCH_TAC `(xi:complex) + eta = (Cx(&2) - quad_omega 3) pow 2 * c` THEN
    MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FLT3_COPRIME_COMB THEN
    MAP_EVERY EXISTS_TAC
     [`xi:complex`; `eta:complex`;
      `(Cx(&2) - quad_omega 3) * (Cx(&1) - quad_omega 3) + quad_omega 3`;
      `(Cx(&2) - quad_omega 3) * quad_omega 3 - quad_omega 3`;
      `--quad_omega 3`; `quad_omega 3`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    UNDISCH_TAC `(xi:complex) + eta = (Cx(&2) - quad_omega 3) pow 2 * c` THEN
    MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `c:complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) eta` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`imag_quadratic_integers 3`;
                   `(Cx(&2) - quad_omega 3) * c`;
                   `(Cx(&2) - quad_omega 3) * c - eta`;
                   `Cx(&2) - quad_omega 3`] RING_DIVIDES_SUB) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_SUB_POW;
                COMPLEX_RING `(a:complex) - (a - b) = b`] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `c:complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) eta` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`imag_quadratic_integers 3`;
                   `(Cx(&2) - quad_omega 3) * c`;
                   `(Cx(&2) - quad_omega 3) * c - quad_omega 3 * eta`;
                   `Cx(&2) - quad_omega 3`] RING_DIVIDES_SUB) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_SUB_POW;
                COMPLEX_RING `(a:complex) - (a - b) = b`] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
      REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
      EXISTS_TAC `c:complex` THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN `eta = (Cx(&1) - quad_omega 3) * quad_omega 3 * eta`
    SUBST1_TAC THENL
     [MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
    MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_LMUL) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN FLT3_CARRIER_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Cx(&2) - quad_omega 3) pow 3 *
    ((Cx(&2) - quad_omega 3) * c) *
    ((Cx(&2) - quad_omega 3) * c - eta) *
    ((Cx(&2) - quad_omega 3) * c - quad_omega 3 * eta) =
    (Cx(&2) - quad_omega 3) pow 3 *
    eps * (Cx(&2) - quad_omega 3) pow (3 * (n - 1)) * gm pow 3`
  MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(xi:complex) pow 3 + eta pow 3` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `(xi:complex) + eta = (Cx(&2) - quad_omega 3) pow 2 * c` THEN
      MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING;
      FIRST_X_ASSUM(SUBST1_TAC o
        check ((=) `(xi:complex) pow 3 + eta pow 3` o lhs o concl)) THEN
      SUBGOAL_THEN `3 * n = 3 + 3 * (n - 1)` SUBST1_TAC THENL
       [UNDISCH_TAC `1 <= n` THEN ARITH_TAC;
        REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING]];
    REWRITE_TAC[COMPLEX_EQ_MUL_LCANCEL; COMPLEX_POW_EQ_0; FLT3_LAMBDA_NZ]]);;

let FLT3_DIVIDES_UNIT_CUBE = prove
 (`!u t. u IN ring_carrier(imag_quadratic_integers 3) /\
         t IN ring_carrier(imag_quadratic_integers 3)
         ==> ring_divides (imag_quadratic_integers 3) t (u * t pow 3)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  EXISTS_TAC `u * (t:complex) pow 2` THEN
  CONJ_TAC THENL [FLT3_CARRIER_TAC; CONV_TAC COMPLEX_RING]);;

(* From the setup: n - 1 >= 1, a1 = L^(3(n-1)) b1, and b1, a2, a3 are units  *)
(* times cubes, by unique factorization.                                     *)

let FLT3_STEP_CUBES = prove
 (`!m a1 a2 a3 gm eps.
        a1 IN ring_carrier(imag_quadratic_integers 3) /\
        a2 IN ring_carrier(imag_quadratic_integers 3) /\
        a3 IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ring_coprime (imag_quadratic_integers 3) (a1,a2) /\
        ring_coprime (imag_quadratic_integers 3) (a1,a3) /\
        ring_coprime (imag_quadratic_integers 3) (a2,a3) /\
        ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) a1 /\
        ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) a2 /\
        ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) a3 /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) gm /\
        a1 + (quad_omega 3 - Cx(&1)) * a2 - quad_omega 3 * a3 = Cx(&0) /\
        a1 * a2 * a3 = eps * (Cx(&2) - quad_omega 3) pow (3 * m) * gm pow 3
        ==> 1 <= m /\
            ?u1 u2 u3 t1 t2 t3.
              ring_unit (imag_quadratic_integers 3) u1 /\
              ring_unit (imag_quadratic_integers 3) u2 /\
              ring_unit (imag_quadratic_integers 3) u3 /\
              t1 IN ring_carrier(imag_quadratic_integers 3) /\
              t2 IN ring_carrier(imag_quadratic_integers 3) /\
              t3 IN ring_carrier(imag_quadratic_integers 3) /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) t1 /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) t2 /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) t3 /\
              ring_coprime (imag_quadratic_integers 3) (t2,t3) /\
              (Cx(&2) - quad_omega 3) pow (3 * m) * u1 * t1 pow 3 +
              (quad_omega 3 - Cx(&1)) * u2 * t2 pow 3 -
              quad_omega 3 * u3 * t3 pow 3 = Cx(&0)`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `eps IN ring_carrier(imag_quadratic_integers 3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `a2 * a3 IN ring_carrier(imag_quadratic_integers 3)`
  ASSUME_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
      (a2 * a3)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`imag_quadratic_integers 3`; `Cx(&2) - quad_omega 3`;
                   `a2:complex`; `a3:complex`] RING_PRIME_DIVIDES_MUL) THEN
    ASM_REWRITE_TAC[FLT3_LAMBDA_PRIME; IMAG_QUADRATIC_INTEGERS_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) gm` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FLT3_LAMBDA_DIVIDES_CUBE THEN
    EXISTS_TAC `eps:complex` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `a1 * a2 * a3 =
      eps * (Cx(&2) - quad_omega 3) pow (3 * m) * gm pow 3` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; complex_pow; COMPLEX_MUL_LID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_RMUL) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (imag_quadratic_integers 3)
      ((Cx(&2) - quad_omega 3) pow (3 * m)) a1`
  MP_TAC THENL
   [MP_TAC(ISPECL [`imag_quadratic_integers 3`; `a1:complex`;
                   `a2 * a3:complex`;
                   `(Cx(&2) - quad_omega 3) pow (3 * m)`]
      RING_COPRIME_DIVPROD_RIGHT) THEN
    REWRITE_TAC[FLT3_UFD; IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
      REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
      EXISTS_TAC `eps * (gm:complex) pow 3` THEN
      CONJ_TAC THENL [FLT3_CARRIER_TAC; CONV_TAC COMPLEX_RING];
      ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN
      MP_TAC(ISPECL [`imag_quadratic_integers 3`; `Cx(&2) - quad_omega 3`;
                     `a2 * a3:complex`; `3 * m`] FLT3_COPRIME_PRIME_POW) THEN
      ASM_REWRITE_TAC[FLT3_UFD; FLT3_LAMBDA_PRIME;
                      IMAG_QUADRATIC_INTEGERS_SUB_POW]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]) THEN
  DISCH_THEN(X_CHOOSE_THEN `b1:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `(b1:complex) * a2 * a3 = eps * gm pow 3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(Cx(&2) - quad_omega 3) pow (3 * m)`;
                   `(b1:complex) * a2 * a3`; `eps * (gm:complex) pow 3`]
      COMPLEX_EQ_MUL_LCANCEL) THEN
    REWRITE_TAC[COMPLEX_POW_EQ_0; FLT3_LAMBDA_NZ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `a1 * a2 * a3 =
      eps * (Cx(&2) - quad_omega 3) pow (3 * m) * gm pow 3` THEN
    UNDISCH_TAC `a1 = (Cx(&2) - quad_omega 3) pow (3 * m) * b1` THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) b1`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) gm` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC FLT3_LAMBDA_DIVIDES_CUBE THEN
    EXISTS_TAC `eps:complex` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check ((=) `(b1:complex) * a2 * a3` o lhs o concl)) THEN
    MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_RMUL) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (imag_quadratic_integers 3) b1 a1`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `(Cx(&2) - quad_omega 3) pow (3 * m)` THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_coprime (imag_quadratic_integers 3) (b1,a2) /\
    ring_coprime (imag_quadratic_integers 3) (b1,a3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RING_COPRIME_DIVISORS THENL
     [MAP_EVERY EXISTS_TAC [`a1:complex`; `a2:complex`];
      MAP_EVERY EXISTS_TAC [`a1:complex`; `a3:complex`]] THEN
    ASM_REWRITE_TAC[RING_DIVIDES_REFL];
    ALL_TAC] THEN
  MP_TAC(SPECL [`b1:complex`; `a2 * a3:complex`; `gm:complex`;
                `eps:complex`] FLT3_UNIT_MUL_CUBE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FLT3_COPRIME_RMUL];
    DISCH_THEN(X_CHOOSE_THEN `u1:complex` (X_CHOOSE_THEN `t1:complex`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (ASSUME_TAC o SYM)))))] THEN
  MP_TAC(SPECL [`a2:complex`; `b1 * a3:complex`; `gm:complex`;
                `eps:complex`] FLT3_UNIT_MUL_CUBE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FLT3_COPRIME_RMUL] THEN
    ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b1:complex) * a2 * a3 = eps * gm pow 3` THEN
    CONV_TAC COMPLEX_RING;
    DISCH_THEN(X_CHOOSE_THEN `u2:complex` (X_CHOOSE_THEN `t2:complex`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (ASSUME_TAC o SYM)))))] THEN
  MP_TAC(SPECL [`a3:complex`; `b1 * a2:complex`; `gm:complex`;
                `eps:complex`] FLT3_UNIT_MUL_CUBE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[FLT3_COPRIME_RMUL] THEN
    ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b1:complex) * a2 * a3 = eps * gm pow 3` THEN
    CONV_TAC COMPLEX_RING;
    DISCH_THEN(X_CHOOSE_THEN `u3:complex` (X_CHOOSE_THEN `t3:complex`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (ASSUME_TAC o SYM)))))] THEN
  SUBGOAL_THEN
   `u1 IN ring_carrier(imag_quadratic_integers 3) /\
    u2 IN ring_carrier(imag_quadratic_integers 3) /\
    u3 IN ring_carrier(imag_quadratic_integers 3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_divides (imag_quadratic_integers 3) t1 b1 /\
    ring_divides (imag_quadratic_integers 3) t2 a2 /\
    ring_divides (imag_quadratic_integers 3) t3 a3`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "b1"; EXPAND_TAC "a2"; EXPAND_TAC "a3"] THEN
    MATCH_MP_TAC FLT3_DIVIDES_UNIT_CUBE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`u1:complex`; `u2:complex`; `u3:complex`;
    `t1:complex`; `t2:complex`; `t3:complex`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) b1` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_DIVIDES_TRANS THEN
    EXISTS_TAC `t1:complex` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) a2` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_DIVIDES_TRANS THEN
    EXISTS_TAC `t2:complex` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) a3` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_DIVIDES_TRANS THEN
    EXISTS_TAC `t3:complex` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC RING_COPRIME_DIVISORS THEN
    MAP_EVERY EXISTS_TAC [`a2:complex`; `a3:complex`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`a1 + (quad_omega 3 - Cx(&1)) * a2 - quad_omega 3 * a3 = Cx(&0)`;
      `a1 = (Cx(&2) - quad_omega 3) pow (3 * m) * b1`;
      `u1 * (t1:complex) pow 3 = b1`; `u2 * (t2:complex) pow 3 = a2`;
      `u3 * (t3:complex) pow 3 = a3`] THEN
    CONV_TAC COMPLEX_RING]);;

(* The relation L^(3m) u1 t1^3 + w u2 t2^3 + w^2 u3 t3^3 = 0 divided by      *)
(* w u2: t2^3 + e1 t3^3 = e2 L^(3m) t1^3 with units e1, e2.                  *)

let FLT3_STEP_UNITS = prove
 (`!m u1 u2 u3 t1 t2 t3.
        ring_unit (imag_quadratic_integers 3) u1 /\
        ring_unit (imag_quadratic_integers 3) u2 /\
        ring_unit (imag_quadratic_integers 3) u3 /\
        (Cx(&2) - quad_omega 3) pow (3 * m) * u1 * t1 pow 3 +
        (quad_omega 3 - Cx(&1)) * u2 * t2 pow 3 -
        quad_omega 3 * u3 * t3 pow 3 = Cx(&0)
        ==> ?e1 e2. ring_unit (imag_quadratic_integers 3) e1 /\
                    ring_unit (imag_quadratic_integers 3) e2 /\
                    t2 pow 3 + e1 * t3 pow 3 =
                    e2 * (Cx(&2) - quad_omega 3) pow (3 * m) * t1 pow 3`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`--(quad_omega 3 * u3) / ((quad_omega 3 - Cx(&1)) * u2)`;
    `--u1 / ((quad_omega 3 - Cx(&1)) * u2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FLT3_UNIT_DIV THEN
    ASM_SIMP_TAC[FLT3_UNIT_NEG; FLT3_UNIT_MUL; FLT3_UNIT_OMEGA];
    MATCH_MP_TAC FLT3_UNIT_DIV THEN
    ASM_SIMP_TAC[FLT3_UNIT_NEG; FLT3_UNIT_MUL; FLT3_UNIT_OMEGA];
    SUBGOAL_THEN `~((quad_omega 3 - Cx(&1)) * u2 = Cx(&0))` MP_TAC THENL
     [MATCH_MP_TAC FLT3_UNIT_NZ THEN
      ASM_SIMP_TAC[FLT3_UNIT_MUL; FLT3_UNIT_OMEGA];
      UNDISCH_TAC
       `(Cx(&2) - quad_omega 3) pow (3 * m) * u1 * t1 pow 3 +
        (quad_omega 3 - Cx(&1)) * u2 * t2 pow 3 -
        quad_omega 3 * u3 * t3 pow 3 = Cx(&0)` THEN
      CONV_TAC COMPLEX_FIELD]]);;

(* With e1 = +-1 (by the cube residues mod L^3, as m >= 1), (t2, e1 t3, t1)  *)
(* is a solution with exponent m.                                            *)

let FLT3_STEP_FINISH = prove
 (`!m e1 e2 t1 t2 t3.
        1 <= m /\
        ring_unit (imag_quadratic_integers 3) e1 /\
        ring_unit (imag_quadratic_integers 3) e2 /\
        t1 IN ring_carrier(imag_quadratic_integers 3) /\
        t2 IN ring_carrier(imag_quadratic_integers 3) /\
        t3 IN ring_carrier(imag_quadratic_integers 3) /\
        ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) t1 /\
        ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) t2 /\
        ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) t3 /\
        ring_coprime (imag_quadratic_integers 3) (t2,t3) /\
        t2 pow 3 + e1 * t3 pow 3 =
        e2 * (Cx(&2) - quad_omega 3) pow (3 * m) * t1 pow 3
        ==> ?xi eta gm eps.
              xi IN ring_carrier(imag_quadratic_integers 3) /\
              eta IN ring_carrier(imag_quadratic_integers 3) /\
              gm IN ring_carrier(imag_quadratic_integers 3) /\
              ring_unit (imag_quadratic_integers 3) eps /\
              ring_coprime (imag_quadratic_integers 3) (xi,eta) /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) eta /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) gm /\
              xi pow 3 + eta pow 3 =
              eps * (Cx(&2) - quad_omega 3) pow (3 * m) * gm pow 3`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `e1 IN ring_carrier(imag_quadratic_integers 3) /\
                e2 IN ring_carrier(imag_quadratic_integers 3)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN `e1 = Cx(&1) \/ e1 = --Cx(&1)` ASSUME_TAC THENL
   [MP_TAC(SPEC `t2:complex` FLT3_CUBE_RESIDUE) THEN
    MP_TAC(SPEC `t3:complex` FLT3_CUBE_RESIDUE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k3:complex` STRIP_ASSUME_TAC o
      CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]))) THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:complex` STRIP_ASSUME_TAC o
      CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC FLT3_UNIT_PM1 THEN
    MAP_EVERY EXISTS_TAC [`s2:real`; `s3:real`] THEN
    ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    SUBGOAL_THEN `integer s2 /\ integer s3` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FLT3_INTEGER_PM]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `(Cx(&2) - quad_omega 3) *
                (e2 * (Cx(&2) - quad_omega 3) pow (3 * (m - 1)) * t1 pow 3 -
                 k2 - e1 * k3)` THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `3 * m = 3 + 3 * (m - 1)` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `1 <= m` THEN ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`t2 pow 3 + e1 * t3 pow 3 =
       e2 * (Cx(&2) - quad_omega 3) pow (3 + 3 * (m - 1)) * t1 pow 3`;
      `t2 pow 3 - Cx s2 = (Cx(&2) - quad_omega 3) pow 3 * k2`;
      `t3 pow 3 - Cx s3 = (Cx(&2) - quad_omega 3) pow 3 * k3`] THEN
    REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 * e1 = Cx(&1) /\ e1 pow 3 = e1` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_divides (imag_quadratic_integers 3) (e1 * t3) t3`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `e1:complex` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `e1 * e1 = Cx(&1)` THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`t2:complex`; `e1 * t3:complex`; `t1:complex`; `e2:complex`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FLT3_CARRIER_TAC;
    MATCH_MP_TAC RING_COPRIME_DIVISORS THEN
    MAP_EVERY EXISTS_TAC [`t2:complex`; `t3:complex`] THEN
    ASM_REWRITE_TAC[RING_DIVIDES_REFL];
    DISCH_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) t3` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC RING_DIVIDES_TRANS THEN
    EXISTS_TAC `e1 * t3:complex` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `t2 pow 3 + e1 * t3 pow 3 =
                 e2 * (Cx(&2) - quad_omega 3) pow (3 * m) * t1 pow 3` THEN
    UNDISCH_TAC `(e1:complex) pow 3 = e1` THEN CONV_TAC COMPLEX_RING]);;

(* One descent step: a solution with exponent n and L^2 | xi + eta gives     *)
(* n >= 2 and a solution with exponent n - 1.                                *)

let FLT3_STEP = prove
 (`!n xi eta gm eps.
        1 <= n /\
        xi IN ring_carrier(imag_quadratic_integers 3) /\
        eta IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ring_coprime (imag_quadratic_integers 3) (xi,eta) /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) eta /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) gm /\
        ring_divides (imag_quadratic_integers 3)
          ((Cx(&2) - quad_omega 3) pow 2) (xi + eta) /\
        xi pow 3 + eta pow 3 =
        eps * (Cx(&2) - quad_omega 3) pow (3 * n) * gm pow 3
        ==> 2 <= n /\
            ?xi' eta' gm' eps'.
              xi' IN ring_carrier(imag_quadratic_integers 3) /\
              eta' IN ring_carrier(imag_quadratic_integers 3) /\
              gm' IN ring_carrier(imag_quadratic_integers 3) /\
              ring_unit (imag_quadratic_integers 3) eps' /\
              ring_coprime (imag_quadratic_integers 3) (xi',eta') /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) eta' /\
              ~ring_divides (imag_quadratic_integers 3)
                 (Cx(&2) - quad_omega 3) gm' /\
              xi' pow 3 + eta' pow 3 =
              eps' * (Cx(&2) - quad_omega 3) pow (3 * (n - 1)) * gm' pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `xi:complex`; `eta:complex`; `gm:complex`;
                `eps:complex`] FLT3_STEP_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:complex` (X_CHOOSE_THEN `a2:complex`
    (X_CHOOSE_THEN `a3:complex` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPECL [`n - 1`; `a1:complex`; `a2:complex`; `a3:complex`;
                `gm:complex`; `eps:complex`] FLT3_STEP_CUBES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `u1:complex` (X_CHOOSE_THEN `u2:complex`
     (X_CHOOSE_THEN `u3:complex` (X_CHOOSE_THEN `t1:complex`
       (X_CHOOSE_THEN `t2:complex` (X_CHOOSE_THEN `t3:complex`
         STRIP_ASSUME_TAC))))))) THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n - 1`; `u1:complex`; `u2:complex`; `u3:complex`;
                `t1:complex`; `t2:complex`; `t3:complex`] FLT3_STEP_UNITS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:complex` (X_CHOOSE_THEN `e2:complex`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC FLT3_STEP_FINISH THEN
  MAP_EVERY EXISTS_TAC [`e1:complex`; `e2:complex`; `t1:complex`;
                        `t2:complex`; `t3:complex`] THEN
  ASM_REWRITE_TAC[]);;

(* The descent: no solution for any n >= 1.                                  *)

let FLT3_DESCENT = prove
 (`!n xi eta gm eps.
        1 <= n /\
        xi IN ring_carrier(imag_quadratic_integers 3) /\
        eta IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ring_coprime (imag_quadratic_integers 3) (xi,eta) /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) eta /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) gm
        ==> ~(xi pow 3 + eta pow 3 =
              eps * (Cx(&2) - quad_omega 3) pow (3 * n) * gm pow 3)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
      (xi pow 3 + eta pow 3)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    SUBGOAL_THEN `eps IN ring_carrier(imag_quadratic_integers 3)`
    ASSUME_TAC THENL [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `eps * (Cx(&2) - quad_omega 3) pow (3 * n - 1) *
                (gm:complex) pow 3` THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `3 * n = SUC(3 * n - 1)` SUBST1_TAC THENL
     [UNDISCH_TAC `1 <= n` THEN ARITH_TAC;
      REWRITE_TAC[complex_pow; SUC_SUB1] THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?v. ring_unit (imag_quadratic_integers 3) v /\ v pow 3 = Cx(&1) /\
        ring_divides (imag_quadratic_integers 3)
          ((Cx(&2) - quad_omega 3) pow 2) (xi + v * eta)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPECL [`xi:complex`; `eta:complex`] FLT3_ROTATE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `Cx(&1)` THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_POW_ONE] THEN
      MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_1) THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES];
      EXISTS_TAC `quad_omega 3 - Cx(&1)` THEN
      ASM_REWRITE_TAC[FLT3_UNIT_OMEGA] THEN
      MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING;
      EXISTS_TAC `--quad_omega 3` THEN
      ASM_SIMP_TAC[FLT3_UNIT_NEG; FLT3_UNIT_OMEGA; COMPLEX_MUL_LNEG;
                   GSYM complex_sub] THEN
      MP_TAC FLT3_OMEGA_SQUARE THEN CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  SUBGOAL_THEN `v IN ring_carrier(imag_quadratic_integers 3) /\
                inv v IN ring_carrier(imag_quadratic_integers 3) /\
                ~(v = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IMAG_QUADRATIC_INTEGERS_UNIT_INV]; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `xi:complex`; `v * eta:complex`; `gm:complex`;
                `eps:complex`] FLT3_STEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FLT3_CARRIER_TAC;
      MATCH_MP_TAC RING_COPRIME_DIVISORS THEN
      MAP_EVERY EXISTS_TAC [`xi:complex`; `eta:complex`] THEN
      ASM_REWRITE_TAC[RING_DIVIDES_REFL] THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
      REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
      EXISTS_TAC `inv v:complex` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(v = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
      DISCH_TAC THEN
      UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                     (Cx(&2) - quad_omega 3) eta` THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `eta = inv v * v * (eta:complex)` SUBST1_TAC THENL
       [UNDISCH_TAC `~(v = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD;
        ALL_TAC] THEN
      MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_LMUL) THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `xi pow 3 + eta pow 3 =
        eps * (Cx(&2) - quad_omega 3) pow (3 * n) * gm pow 3` THEN
      UNDISCH_TAC `(v:complex) pow 3 = Cx(&1)` THEN
      CONV_TAC COMPLEX_RING];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `xi':complex` (X_CHOOSE_THEN `eta':complex`
     (X_CHOOSE_THEN `gm':complex` (X_CHOOSE_THEN `eps':complex`
       STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`xi':complex`; `eta':complex`;
                             `gm':complex`; `eps':complex`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The theorem in the Eisenstein integers (Hardy-Wright Thm. 228 with a      *)
(* unit): alpha^3 + beta^3 + eps gm^3 = 0 has no solution with alpha,        *)
(* beta, gm nonzero and pairwise coprime, eps a unit. If L divides none      *)
(* of them, cubes are +-1 mod L^4 (FLT3_CUBE_RESIDUE4); otherwise L divides  *)
(* exactly one, and after the L-adic split (FLT3_LAMBDA_SPLIT) the descent   *)
(* applies (for L | alpha first eps = +-1 by the cube residues mod L^3).     *)
(* ------------------------------------------------------------------------- *)

let FLT3_CUBE_RESIDUE4 = prove
 (`!x. x IN ring_carrier(imag_quadratic_integers 3) /\
       ~ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) x
       ==> ?s. (s = &1 \/ s = -- &1) /\
               ring_divides (imag_quadratic_integers 3)
                 ((Cx(&2) - quad_omega 3) pow 4) (x pow 3 - Cx s)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FLT3_RESIDUE) THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_CASES_TAC `s = &0` THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_RZERO]; ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP FLT3_INTEGER_PM) THEN
  SUBGOAL_THEN `s = &1 \/ s = -- &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o
    GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:complex` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC `t:complex` FLT3_CUBE_SELF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o
    GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]) THEN
  DISCH_THEN(X_CHOOSE_THEN `c:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  EXISTS_TAC `s:real` THEN
  ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  EXISTS_TAC `c + (quad_omega 3 * (Cx(&2) - quad_omega 3) - Cx(&1)) * t +
              quad_omega 3 * Cx s * t pow 2` THEN
  CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
  UNDISCH_TAC `x - Cx s = (Cx(&2) - quad_omega 3) * t` THEN
  UNDISCH_TAC `(t:complex) pow 3 - t = (Cx(&2) - quad_omega 3) * c` THEN
  UNDISCH_TAC `s = &1 \/ s = -- &1` THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[CX_NEG] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
  CONV_TAC COMPLEX_RING);;

let FLT3_LAMBDA_SPLIT = prove
 (`!z. z IN ring_carrier(imag_quadratic_integers 3) /\ ~(z = Cx(&0))
       ==> ?m g. g IN ring_carrier(imag_quadratic_integers 3) /\
                 ~ring_divides (imag_quadratic_integers 3)
                    (Cx(&2) - quad_omega 3) g /\
                 z = (Cx(&2) - quad_omega 3) pow m * g`,
  SUBGOAL_THEN
   `!n z. z IN ring_carrier(imag_quadratic_integers 3) /\ ~(z = Cx(&0)) /\
          norm z pow 2 = &n
          ==> ?m g. g IN ring_carrier(imag_quadratic_integers 3) /\
                    ~ring_divides (imag_quadratic_integers 3)
                       (Cx(&2) - quad_omega 3) g /\
                    z = (Cx(&2) - quad_omega 3) pow m * g`
   (fun th -> REPEAT STRIP_TAC THEN
              MP_TAC(SPECL [`3`; `z:complex`]
                IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
              ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
              MATCH_MP_TAC th THEN EXISTS_TAC `n:num` THEN
              ASM_REWRITE_TAC[]) THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
  ASM_CASES_TAC
   `ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) z`
  THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`0`; `z:complex`] THEN
    ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_LID]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [IMAG_QUADRATIC_INTEGERS_DIVIDES]) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:complex` STRIP_ASSUME_TAC o
    CONJUNCT2 o CONJUNCT2) THEN
  SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(z = Cx(&0))` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO];
    ALL_TAC] THEN
  MP_TAC(SPECL [`3`; `w:complex`] IMAG_QUADRATIC_INTEGERS_NORM_POW_2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  SUBGOAL_THEN `n = 3 * k /\ ~(k = 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `norm(z:complex) pow 2 = &n` THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_MUL; FLT3_LAMBDA_NORM] THEN
      REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN ARITH_TAC;
      DISCH_TAC THEN UNDISCH_TAC `norm(w:complex) pow 2 = &k` THEN
      ASM_REWRITE_TAC[REAL_POW_EQ_0; COMPLEX_NORM_ZERO; ARITH_EQ]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `w:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `g:complex`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`SUC m`; `g:complex`] THEN
  ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_ASSOC]);;

let FLT3_COPRIME_LAMBDA = prove
 (`!a b. ring_coprime (imag_quadratic_integers 3) (a,b) /\
         ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) a
         ==> ~ring_divides (imag_quadratic_integers 3)
                (Cx(&2) - quad_omega 3) b`,
  REWRITE_TAC[ring_coprime] THEN MESON_TAC[FLT3_LAMBDA_NOT_UNIT]);;

let FLT3_EISENSTEIN_CASE1 = prove
 (`!alpha beta gm eps.
        alpha IN ring_carrier(imag_quadratic_integers 3) /\
        beta IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) alpha /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) beta /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) gm
        ==> ~(alpha pow 3 + beta pow 3 + eps * gm pow 3 = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_TAC THEN
  MAP_EVERY (fun (v,s,k) ->
    MP_TAC(SPEC v FLT3_CUBE_RESIDUE4) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN s (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]))) THEN
    DISCH_THEN(X_CHOOSE_THEN k STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2))
   [`alpha:complex`,`s1:real`,`k1:complex`;
    `beta:complex`,`s2:real`,`k2:complex`;
    `gm:complex`,`s3:real`,`k3:complex`] THEN
  SUBGOAL_THEN `eps IN ring_carrier(imag_quadratic_integers 3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx s1 + Cx s2 + eps * Cx s3 =
    (Cx(&2) - quad_omega 3) pow 4 * --(k1 + k2 + eps * k3)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`alpha pow 3 + beta pow 3 + eps * gm pow 3 = Cx(&0)`;
      `alpha pow 3 - Cx s1 = (Cx(&2) - quad_omega 3) pow 4 * k1`;
      `beta pow 3 - Cx s2 = (Cx(&2) - quad_omega 3) pow 4 * k2`;
      `gm pow 3 - Cx s3 = (Cx(&2) - quad_omega 3) pow 4 * k3`] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  ASM_CASES_TAC `s2 = --s1` THENL
   [MP_TAC(SPEC `eps * Cx s3` FLT3_LAMBDA_NOT_DIVIDES_UNIT) THEN
    ASM_SIMP_TAC[FLT3_UNIT_MUL; FLT3_UNIT_PM] THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    SUBGOAL_THEN `integer s3` ASSUME_TAC THENL
     [ASM_MESON_TAC[FLT3_INTEGER_PM]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `(Cx(&2) - quad_omega 3) pow 3 * --(k1 + k2 + eps * k3)` THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    UNDISCH_TAC `Cx s1 + Cx s2 + eps * Cx s3 =
                 (Cx(&2) - quad_omega 3) pow 4 * --(k1 + k2 + eps * k3)` THEN
    ASM_REWRITE_TAC[CX_NEG] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `s2:real = s1` SUBST_ALL_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`s1 = &1 \/ s1 = -- &1`; `s2 = &1 \/ s2 = -- &1`; `~(s2 = --s1)`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`eps:complex`; `--s1:real`; `s3:real`] FLT3_UNIT_PM1_ZERO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_ARITH `--x = &1 \/ --x = -- &1 <=>
                                x = -- &1 \/ x = &1`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    SUBGOAL_THEN `integer s1 /\ integer s3` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FLT3_INTEGER_PM]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `(Cx(&2) - quad_omega 3) pow 2 * --(k1 + k2 + eps * k3) -
                quad_omega 3 * Cx s1` THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    UNDISCH_TAC `Cx s1 + Cx s1 + eps * Cx s3 =
                 (Cx(&2) - quad_omega 3) pow 4 * --(k1 + k2 + eps * k3)` THEN
    REWRITE_TAC[CX_NEG] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC] THEN
  MP_TAC(SPEC `quad_omega 3 * Cx s1` FLT3_LAMBDA_NOT_DIVIDES_UNIT) THEN
  ASM_SIMP_TAC[FLT3_UNIT_MUL; FLT3_UNIT_PM; FLT3_UNIT_OMEGA] THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  SUBGOAL_THEN `integer s1` ASSUME_TAC THENL
   [ASM_MESON_TAC[FLT3_INTEGER_PM]; ALL_TAC] THEN
  REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
  EXISTS_TAC `(Cx(&2) - quad_omega 3) * --(k1 + k2 + eps * k3)` THEN
  CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`(Cx(&2) - quad_omega 3) pow 2`;
                `quad_omega 3 * Cx s1`;
                `(Cx(&2) - quad_omega 3) * (Cx(&2) - quad_omega 3) *
                 --(k1 + k2 + eps * k3)`] COMPLEX_EQ_MUL_LCANCEL) THEN
  REWRITE_TAC[COMPLEX_POW_EQ_0; FLT3_LAMBDA_NZ; ARITH_EQ] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY UNDISCH_TAC
   [`Cx s1 + Cx s1 + eps * Cx s3 =
     (Cx(&2) - quad_omega 3) pow 4 * --(k1 + k2 + eps * k3)`;
    `Cx(--s1) + eps * Cx s3 = Cx(&0)`] THEN
  REWRITE_TAC[CX_NEG] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
  CONV_TAC COMPLEX_RING);;

let FLT3_EISENSTEIN_CASE2 = prove
 (`!alpha beta gm eps.
        alpha IN ring_carrier(imag_quadratic_integers 3) /\
        beta IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ~(gm = Cx(&0)) /\
        ring_coprime (imag_quadratic_integers 3) (alpha,beta) /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) beta /\
        ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) gm
        ==> ~(alpha pow 3 + beta pow 3 + eps * gm pow 3 = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPEC `gm:complex` FLT3_LAMBDA_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `g:complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST_ALL_TAC)))) THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) g` THEN
    UNDISCH_TAC `ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3)
                   ((Cx(&2) - quad_omega 3) pow 0 * g)` THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `alpha:complex`; `beta:complex`; `g:complex`;
                `--eps:complex`] FLT3_DESCENT) THEN
  ASM_SIMP_TAC[FLT3_UNIT_NEG] THEN ANTS_TAC THENL
   [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> ~q`) THEN
  SUBGOAL_THEN
   `((Cx(&2) - quad_omega 3) pow m * g) pow 3 =
    (Cx(&2) - quad_omega 3) pow (3 * m) * g pow 3`
  SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_POW] THEN REWRITE_TAC[MULT_SYM];
    CONV_TAC COMPLEX_RING]);;

let FLT3_EISENSTEIN_CASE3 = prove
 (`!alpha beta gm eps.
        alpha IN ring_carrier(imag_quadratic_integers 3) /\
        beta IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ~(alpha = Cx(&0)) /\
        ring_coprime (imag_quadratic_integers 3) (beta,gm) /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) beta /\
        ~ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) gm /\
        ring_divides (imag_quadratic_integers 3)
           (Cx(&2) - quad_omega 3) alpha
        ==> ~(alpha pow 3 + beta pow 3 + eps * gm pow 3 = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `alpha:complex` FLT3_LAMBDA_SPLIT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `a:complex`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      SUBST_ALL_TAC)))) THEN
  SUBGOAL_THEN `~(m = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3) a` THEN
    UNDISCH_TAC `ring_divides (imag_quadratic_integers 3)
                   (Cx(&2) - quad_omega 3)
                   ((Cx(&2) - quad_omega 3) pow 0 * a)` THEN
    REWRITE_TAC[complex_pow; COMPLEX_MUL_LID] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `eps IN ring_carrier(imag_quadratic_integers 3)`
  ASSUME_TAC THENL [ASM_MESON_TAC[RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  MAP_EVERY (fun (v,s,k) ->
    MP_TAC(SPEC v FLT3_CUBE_RESIDUE) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN s (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o GEN_REWRITE_RULE I [IMAG_QUADRATIC_INTEGERS_DIVIDES]))) THEN
    DISCH_THEN(X_CHOOSE_THEN k STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2))
   [`beta:complex`,`s2:real`,`k2:complex`;
    `gm:complex`,`s3:real`,`k3:complex`] THEN
  MP_TAC(SPECL [`eps:complex`; `s2:real`; `s3:real`] FLT3_UNIT_PM1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
    SUBGOAL_THEN `integer s2 /\ integer s3` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FLT3_INTEGER_PM]; ALL_TAC] THEN
    REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
    EXISTS_TAC `--((Cx(&2) - quad_omega 3) pow (3 * m - 2) * a pow 3) -
                (Cx(&2) - quad_omega 3) * (k2 + eps * k3)` THEN
    CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `((Cx(&2) - quad_omega 3) pow m * a) pow 3 =
      (Cx(&2) - quad_omega 3) pow 2 *
      (Cx(&2) - quad_omega 3) pow (3 * m - 2) * a pow 3`
    MP_TAC THENL
     [REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_POW; COMPLEX_MUL_ASSOC;
                  GSYM COMPLEX_POW_ADD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`((Cx(&2) - quad_omega 3) pow m * a) pow 3 + beta pow 3 +
       eps * gm pow 3 = Cx(&0)`;
      `beta pow 3 - Cx s2 = (Cx(&2) - quad_omega 3) pow 3 * k2`;
      `gm pow 3 - Cx s3 = (Cx(&2) - quad_omega 3) pow 3 * k3`] THEN
    CONV_TAC COMPLEX_RING;
    DISCH_TAC] THEN
  SUBGOAL_THEN `eps * eps = Cx(&1) /\ eps pow 3 = eps` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`m:num`; `beta:complex`; `eps * gm:complex`; `a:complex`;
                `--Cx(&1)`] FLT3_DESCENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(m = 0)` THEN ARITH_TAC;
      FLT3_CARRIER_TAC;
      MATCH_MP_TAC FLT3_UNIT_NEG THEN
      MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_1) THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES];
      MATCH_MP_TAC RING_COPRIME_DIVISORS THEN
      MAP_EVERY EXISTS_TAC [`beta:complex`; `gm:complex`] THEN
      ASM_REWRITE_TAC[RING_DIVIDES_REFL] THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
      REPEAT(CONJ_TAC THENL [FLT3_CARRIER_TAC; ALL_TAC]) THEN
      EXISTS_TAC `eps:complex` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(eps:complex) * eps = Cx(&1)` THEN CONV_TAC COMPLEX_RING;
      DISCH_TAC THEN
      UNDISCH_TAC `~ring_divides (imag_quadratic_integers 3)
                     (Cx(&2) - quad_omega 3) gm` THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `gm = eps * eps * (gm:complex)` SUBST1_TAC THENL
       [UNDISCH_TAC `(eps:complex) * eps = Cx(&1)` THEN CONV_TAC COMPLEX_RING;
        ALL_TAC] THEN
      MP_TAC(ISPEC `imag_quadratic_integers 3` RING_DIVIDES_LMUL) THEN
      REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((Cx(&2) - quad_omega 3) pow m * a) pow 3 =
    (Cx(&2) - quad_omega 3) pow (3 * m) * a pow 3`
  MP_TAC THENL
   [REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_POW] THEN
    REWRITE_TAC[MULT_SYM];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`((Cx(&2) - quad_omega 3) pow m * a) pow 3 + beta pow 3 +
     eps * gm pow 3 = Cx(&0)`;
    `(eps:complex) pow 3 = eps`] THEN
  CONV_TAC COMPLEX_RING);;

let FLT3_EISENSTEIN = prove
 (`!alpha beta gm eps.
        alpha IN ring_carrier(imag_quadratic_integers 3) /\
        beta IN ring_carrier(imag_quadratic_integers 3) /\
        gm IN ring_carrier(imag_quadratic_integers 3) /\
        ring_unit (imag_quadratic_integers 3) eps /\
        ~(alpha = Cx(&0)) /\ ~(beta = Cx(&0)) /\ ~(gm = Cx(&0)) /\
        ring_coprime (imag_quadratic_integers 3) (alpha,beta) /\
        ring_coprime (imag_quadratic_integers 3) (alpha,gm) /\
        ring_coprime (imag_quadratic_integers 3) (beta,gm)
        ==> ~(alpha pow 3 + beta pow 3 + eps * gm pow 3 = Cx(&0))`,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_CASES_TAC
   `ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) gm`
  THENL
   [MATCH_MP_TAC FLT3_EISENSTEIN_CASE2 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FLT3_COPRIME_LAMBDA THEN EXISTS_TAC `gm:complex` THEN
    ONCE_REWRITE_TAC[RING_COPRIME_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) alpha`
  THENL
   [MATCH_MP_TAC FLT3_EISENSTEIN_CASE3 THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FLT3_COPRIME_LAMBDA THEN EXISTS_TAC `alpha:complex` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3) beta`
  THENL
   [ONCE_REWRITE_TAC[COMPLEX_RING
     `(a:complex) pow 3 + b pow 3 + c = b pow 3 + a pow 3 + c`] THEN
    MATCH_MP_TAC FLT3_EISENSTEIN_CASE3 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FLT3_EISENSTEIN_CASE1 THEN ASM_REWRITE_TAC[]]);;

let FLT3_EISENSTEIN_CUBES = prove
 (`!x y z.
        x IN ring_carrier(imag_quadratic_integers 3) /\
        y IN ring_carrier(imag_quadratic_integers 3) /\
        z IN ring_carrier(imag_quadratic_integers 3) /\
        ~(x = Cx(&0)) /\ ~(y = Cx(&0)) /\ ~(z = Cx(&0)) /\
        ring_coprime (imag_quadratic_integers 3) (x,y) /\
        ring_coprime (imag_quadratic_integers 3) (x,z) /\
        ring_coprime (imag_quadratic_integers 3) (y,z)
        ==> ~(x pow 3 + y pow 3 = z pow 3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`x:complex`; `y:complex`; `z:complex`; `--Cx(&1)`]
    FLT3_EISENSTEIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FLT3_UNIT_NEG THEN
    MP_TAC(ISPEC `imag_quadratic_integers 3` RING_UNIT_1) THEN
    REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES];
    REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:complex) pow 3 + y pow 3 = z pow 3` THEN
    CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Integers: cubes modulo 9, the 3-adic decomposition, divisibility of       *)
(* cubes, and the passage to the Eisenstein integers.                        *)
(* ------------------------------------------------------------------------- *)

let FLT3_INT_CUBE_MOD9 = prove
 (`!x:int. ~(&3 divides x)
           ==> ?q s. (s = &1 \/ s = -- &1) /\ x pow 3 = &9 * q + s`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:int`; `&3:int`] INT_DIVISION) THEN
  REWRITE_TAC[INT_OF_NUM_EQ; ARITH_EQ; INT_ABS_NUM] THEN
  ABBREV_TAC `q = x div &3` THEN ABBREV_TAC `j = x rem &3` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `j = &1 \/ j = &2:int` MP_TAC THENL
   [MATCH_MP_TAC(INT_ARITH
     `&0 <= j /\ j < &3 /\ ~(j = &0) ==> j = &1 \/ j = &2:int`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(&3 divides x)` THEN REWRITE_TAC[int_divides] THEN
    EXISTS_TAC `q:int` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check ((=) `x:int` o lhs o concl)) THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXISTS_TAC [`&3 * q pow 3 + &3 * q pow 2 + q:int`; `&1:int`];
    MAP_EVERY EXISTS_TAC [`&3 * q pow 3 + &6 * q pow 2 + &4 * q + &1:int`;
                          `-- &1:int`]] THEN
  REWRITE_TAC[] THEN CONV_TAC INT_RING);;

let FLT3_INT_NOT_3_DIVIDES_PM1 = prove
 (`!s:int. (s = &1 \/ s = -- &1) ==> ~(&3 divides s)`,
  GEN_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN INT_ARITH_TAC);;

let FLT3_INT_3_DIVIDES_CUBE = prove
 (`!x:int. &3 divides x pow 3 ==> &3 divides x`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FLT3_INT_CUBE_MOD9) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:int` (X_CHOOSE_THEN `s:int`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `s:int` FLT3_INT_NOT_3_DIVIDES_PM1) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&3 divides &9 * q + s` THEN REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:int`) THEN EXISTS_TAC `t - &3 * q:int` THEN
  UNDISCH_TAC `&9 * q + s = &3 * t:int` THEN INT_ARITH_TAC);;

let FLT3_INT_CASE1 = prove
 (`!x y z:int. ~(&3 divides x) /\ ~(&3 divides y) /\ ~(&3 divides z)
               ==> ~(x pow 3 + y pow 3 = z pow 3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN
    (MP_TAC o MATCH_MP FLT3_INT_CUBE_MOD9)) THEN
  DISCH_THEN(X_CHOOSE_THEN `q3:int` (X_CHOOSE_THEN `s3:int`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:int` (X_CHOOSE_THEN `s2:int`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:int` (X_CHOOSE_THEN `s1:int`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(q1 + q2) - q3 <= -- &1 \/ (q1 + q2) - q3 = &0 \/
                &1 <= (q1 + q2) - q3:int` MP_TAC THENL
   [INT_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`s1 = &1 \/ s1 = -- &1:int`; `s2 = &1 \/ s2 = -- &1:int`;
    `s3 = &1 \/ s3 = -- &1:int`;
    `(&9 * q1 + s1) + &9 * q2 + s2 = &9 * q3 + s3:int`] THEN
  INT_ARITH_TAC);;

let FLT3_INT_3ADIC = prove
 (`!z:int. ~(z = &0) ==> ?k z0. z = &3 pow k * z0 /\ ~(&3 divides z0)`,
  MATCH_MP_TAC WF_INT_MEASURE THEN EXISTS_TAC `abs:int->int` THEN
  REWRITE_TAC[INT_ABS_POS] THEN X_GEN_TAC `z:int` THEN
  DISCH_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `&3 divides z` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:int` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [int_divides]) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:int`) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INT_ENTIRE; INT_OF_NUM_EQ; ARITH_EQ]) THEN
    ASM_REWRITE_TAC[INT_ABS_MUL; INT_ABS_NUM] THEN ANTS_TAC THENL
     [UNDISCH_TAC `~(w:int = &0)` THEN INT_ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `z0:int`
        STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`SUC k`; `z0:int`] THEN
      ASM_REWRITE_TAC[INT_POW; INT_MUL_ASSOC]];
    MAP_EVERY EXISTS_TAC [`0`; `z:int`] THEN
    ASM_REWRITE_TAC[INT_POW; INT_MUL_LID]]);;

let FLT3_INT_DIVIDES_CUBE = prove
 (`!a b:int. a pow 3 divides b pow 3 ==> a divides b`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM INT_DIVIDES_LABS] THEN
  ONCE_REWRITE_TAC[GSYM INT_DIVIDES_RABS] THEN
  REWRITE_TAC[INT_ABS_POW] THEN
  MP_TAC(SPECL [`3`; `num_of_int(abs a)`; `num_of_int(abs b)`]
    DIVIDES_EXP2_REV) THEN
  REWRITE_TAC[num_divides; GSYM INT_OF_NUM_POW; ARITH_EQ] THEN
  SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS]);;

let FLT3_INT_IN = prove
 (`!x:int. Cx(real_of_int x) IN ring_carrier(imag_quadratic_integers 3)`,
  SIMP_TAC[FLT3_CLOSED; INTEGER_REAL_OF_INT]);;

let FLT3_INT_LAMBDA_DIVIDES = prove
 (`!m:int. ring_divides (imag_quadratic_integers 3) (Cx(&2) - quad_omega 3)
             (Cx(real_of_int m))
           ==> &3 divides m`,
  GEN_TAC THEN REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_DIVIDES] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:complex` MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[FLT3_IN; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real`; `q:real`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(SPECL [`3`; `real_of_int m`; `&0`; `&2 * p + q`; `q - p:real`]
    QUAD_OMEGA_COORDS) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `Cx(real_of_int m) = (Cx(&2) - quad_omega 3) * c` THEN
    UNDISCH_TAC `c = Cx p + Cx q * quad_omega 3` THEN
    REWRITE_TAC[CX_ADD; CX_SUB; CX_MUL] THEN MP_TAC FLT3_OMEGA_SQUARE THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  REWRITE_TAC[int_divides] THEN EXISTS_TAC `int_of_real p` THEN
  REWRITE_TAC[int_eq; int_mul_th; int_of_num_th] THEN
  SUBST1_TAC(GEN_REWRITE_RULE I [int_rep] (ASSUME `integer p`)) THEN
  UNDISCH_TAC `q - p = &0` THEN UNDISCH_TAC `real_of_int m = &2 * p + q` THEN
  REAL_ARITH_TAC);;

let FLT3_INT_COPRIME = prove
 (`!x y:int. coprime(x,y)
             ==> ring_coprime (imag_quadratic_integers 3)
                   (Cx(real_of_int x),Cx(real_of_int y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[int_coprime; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:int`; `v:int`] THEN DISCH_TAC THEN
  REWRITE_TAC[ring_coprime; FLT3_INT_IN] THEN X_GEN_TAC `d:complex` THEN
  STRIP_TAC THEN REWRITE_TAC[GSYM RING_DIVIDES_ONE] THEN
  REWRITE_TAC[IMAG_QUADRATIC_INTEGERS_CLAUSES] THEN
  SUBGOAL_THEN `Cx(&1) = Cx(real_of_int u) * Cx(real_of_int x) +
                         Cx(real_of_int v) * Cx(real_of_int y)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `real_of_int`) THEN
    REWRITE_TAC[int_add_th; int_mul_th; int_of_num_th] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; CX_INJ] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC FLT3_DIVIDES_LINEAR THEN ASM_REWRITE_TAC[FLT3_INT_IN]]);;

(* If 3 | z and x, y are coprime, then z = 3^k z0 gives                      *)
(* x^3 + y^3 = r^(3k) L^(3(2k)) z0^3 in O, excluded by the descent.          *)

let FLT3_INT_CASE2 = prove
 (`!x y z:int. coprime(x,y) /\ &3 divides z /\ x pow 3 + y pow 3 = z pow 3
               ==> z = &0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(&3 divides y)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&3 divides x` ASSUME_TAC THENL
     [MATCH_MP_TAC FLT3_INT_3_DIVIDES_CUBE THEN
      SUBGOAL_THEN `(x:int) pow 3 = z pow 3 - y pow 3` SUBST1_TAC THENL
       [UNDISCH_TAC `(x:int) pow 3 + y pow 3 = z pow 3` THEN INT_ARITH_TAC;
        MATCH_MP_TAC(INTEGER_RULE
         `!d y z:int. d divides z /\ d divides y
                      ==> d divides (z pow 3 - y pow 3)`) THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(SPEC `&1:int` FLT3_INT_NOT_3_DIVIDES_PM1) THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(INTEGER_RULE
       `!x y d:int. coprime(x,y) /\ d divides x /\ d divides y
                    ==> d divides &1`) THEN
      MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(SPEC `z:int` FLT3_INT_3ADIC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `z0:int`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(&3 divides z0)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `&3 divides z` THEN ASM_REWRITE_TAC[INT_POW; INT_MUL_LID];
    ALL_TAC] THEN
  MP_TAC(SPECL [`2 * k`; `Cx(real_of_int x)`; `Cx(real_of_int y)`;
                `Cx(real_of_int z0)`; `quad_omega 3 pow (3 * k)`]
    FLT3_DESCENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FLT3_INT_IN] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC;
      MATCH_MP_TAC FLT3_UNIT_POW THEN REWRITE_TAC[FLT3_UNIT_OMEGA];
      MATCH_MP_TAC FLT3_INT_COPRIME THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[FLT3_INT_LAMBDA_DIVIDES];
      ASM_MESON_TAC[FLT3_INT_LAMBDA_DIVIDES]];
    REWRITE_TAC[]] THEN
  SUBGOAL_THEN `Cx(real_of_int x) pow 3 + Cx(real_of_int y) pow 3 =
                Cx(real_of_int z) pow 3`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM CX_POW; GSYM CX_ADD; CX_INJ; GSYM int_pow_th;
                GSYM int_add_th; GSYM int_eq] THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Cx(real_of_int z) =
                (quad_omega 3 * (Cx(&2) - quad_omega 3) pow 2) pow k *
                Cx(real_of_int z0)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[int_mul_th; int_pow_th; int_of_num_th; CX_MUL; CX_POW;
                    GSYM FLT3_THREE];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_POW_POW] THEN
  REWRITE_TAC[MULT_AC; COMPLEX_MUL_AC]);;

let FLT3_INT_COPRIME_CASE = prove
 (`!x y z:int. coprime(x,y) /\ x pow 3 + y pow 3 = z pow 3
               ==> x * y * z = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&3 divides z` THENL
   [SUBGOAL_THEN `z = &0:int` SUBST1_TAC THENL
     [MATCH_MP_TAC FLT3_INT_CASE2 THEN
      MAP_EVERY EXISTS_TAC [`x:int`; `y:int`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[INT_MUL_RZERO]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&3 divides x` THENL
   [SUBGOAL_THEN `--x = &0:int` MP_TAC THENL
     [MATCH_MP_TAC FLT3_INT_CASE2 THEN
      MAP_EVERY EXISTS_TAC [`y:int`; `--z:int`] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(INTEGER_RULE
         `!x y z:int. coprime(x,y) /\ x pow 3 + y pow 3 = z pow 3
                      ==> coprime(y,--z)`) THEN
        EXISTS_TAC `x:int` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[INTEGER_RULE
          `!d x:int. d divides --x <=> d divides x`];
        UNDISCH_TAC `(x:int) pow 3 + y pow 3 = z pow 3` THEN
        CONV_TAC INT_RING];
      REWRITE_TAC[INT_NEG_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_MUL_LZERO]];
    ALL_TAC] THEN
  ASM_CASES_TAC `&3 divides y` THENL
   [SUBGOAL_THEN `--y = &0:int` MP_TAC THENL
     [MATCH_MP_TAC FLT3_INT_CASE2 THEN
      MAP_EVERY EXISTS_TAC [`x:int`; `--z:int`] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(INTEGER_RULE
         `!x y z:int. coprime(x,y) /\ x pow 3 + y pow 3 = z pow 3
                      ==> coprime(x,--z)`) THEN
        EXISTS_TAC `y:int` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[INTEGER_RULE
          `!d x:int. d divides --x <=> d divides x`];
        UNDISCH_TAC `(x:int) pow 3 + y pow 3 = z pow 3` THEN
        CONV_TAC INT_RING];
      REWRITE_TAC[INT_NEG_EQ_0] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:int`; `y:int`; `z:int`] FLT3_INT_CASE1) THEN
  ASM_REWRITE_TAC[]);;

let FLT3_INT_GCD_SPLIT = prove
 (`!x y:int. ~(x = &0 /\ y = &0)
             ==> ?g x1 y1. ~(g = &0) /\ x = g * x1 /\ y = g * y1 /\
                           coprime(x1,y1)`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `gcd(x:int,y)` THEN
  MP_TAC(SPECL [`x:int`; `y:int`] (INTEGER_RULE
   `!x y:int. ~(gcd(x,y) = &0)
              ==> ?x1 y1. x = gcd(x,y) * x1 /\ y = gcd(x,y) * y1 /\
                          coprime(x1,y1)`)) THEN
  ASM_REWRITE_TAC[INTEGER_RULE
   `!x y:int. gcd(x,y) = &0 <=> x = &0 /\ y = &0`]);;

(* ------------------------------------------------------------------------- *)
(* Fermat Last Theorem for the exponent 3.                                   *)
(* ------------------------------------------------------------------------- *)

let FLT3_INT = prove
 (`!x y z:int. x pow 3 + y pow 3 = z pow 3 ==> x * y * z = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `(x:int) = &0 /\ (y:int) = &0` THENL
   [ASM_REWRITE_TAC[INT_MUL_LZERO; INT_MUL_RZERO]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP FLT3_INT_GCD_SPLIT) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int` (X_CHOOSE_THEN `x1:int`
    (X_CHOOSE_THEN `y1:int` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 SUBST_ALL_TAC
        (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(g:int) divides z` MP_TAC THENL
   [MATCH_MP_TAC FLT3_INT_DIVIDES_CUBE THEN REWRITE_TAC[int_divides] THEN
    EXISTS_TAC `(x1:int) pow 3 + y1 pow 3` THEN
    UNDISCH_TAC `(g * x1) pow 3 + (g * y1) pow 3 = (z:int) pow 3` THEN
    CONV_TAC INT_RING;
    ALL_TAC] THEN
  REWRITE_TAC[int_divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:int` SUBST_ALL_TAC) THEN
  MP_TAC(SPECL [`x1:int`; `y1:int`; `z1:int`] FLT3_INT_COPRIME_CASE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(g * x1) pow 3 + (g * y1) pow 3 = (g * z1:int) pow 3`;
      `~(g:int = &0)`] THEN
    CONV_TAC INT_RING;
    CONV_TAC INT_RING]);;

let FLT3 = prove
 (`!x y z. x EXP 3 + y EXP 3 = z EXP 3 ==> x = 0 \/ y = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&x:int`; `&y:int`; `&z:int`] FLT3_INT) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_ADD; INT_OF_NUM_MUL;
                  INT_OF_NUM_EQ; MULT_EQ_0] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `x EXP 3 + y EXP 3 = z EXP 3` THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ADD_EQ_0; EXP_EQ_0] THEN
  ARITH_TAC);;
