(* ========================================================================= *)
(* Integral points on elliptic curves (Baker 1968, the elliptic equation;    *)
(* Siegel 1929 for genus 1 in Weierstrass form; Baker, Transcendental Number *)
(* Theory, Ch. 4 sec. 3).                                                    *)
(*                                                                           *)
(* Purpose: the equation y^2 = a x^3 + b x^2 + c x + d with integer          *)
(* coefficients, a <> 0 and non-zero discriminant, the short Weierstrass     *)
(* equation y^2 = x^3 + a x + b with 4 a^3 + 27 b^2 <> 0, and the general    *)
(* Weierstrass equation y^2 + a1 x y + a3 y = x^3 + a2 x^2 + a4 x + a6 with  *)
(* non-zero discriminant Delta have only finitely many integral points.      *)
(* MORDELL (Baker/mordell.ml) is the case a = 0 of the short form.           *)
(*                                                                           *)
(* Method: algebra on top of HYPERELLIPTIC (three distinct simple roots).    *)
(* CUBIC_SIMPLE_ROOTS: by CUBIC_VIETA the cubic is a (z - t1) (z - t2) (z -  *)
(* t3) over C; its discriminant is a^4 ((t1 - t2) (t1 - t3) (t2 - t3))^2 and *)
(* its derivative at t1 is a (t1 - t2) (t1 - t3) (ELLIPTIC_CUBIC_DISC), so   *)
(* the three roots are distinct and simple. ELLIPTIC_CUBIC_INTEGRAL_POINTS:  *)
(* HYPERELLIPTIC with N = 3 and the coefficients d, c, b, a                  *)
(* (ELLIPTIC_CUBIC_SUMS expands the sums). ELLIPTIC_INTEGRAL_POINTS: the     *)
(* case (1, 0, a, b), discriminant -(4 a^3 + 27 b^2).                        *)
(* WEIERSTRASS_INTEGRAL_POINTS: completing the square, (2 y + a1 x + a3)^2 = *)
(* 4 x^3 + b2 x^2 + 2 b4 x + b6 on the curve, and the discriminant of this   *)
(* cubic is 16 Delta (ELLIPTIC_WEIERSTRASS); the curve lies in the image of  *)
(* the integral points of the cubic under (x, Y) |-> (x, (Y - a1 x - a3)/2). *)
(*                                                                           *)
(* Main results: CUBIC_SIMPLE_ROOTS, ELLIPTIC_CUBIC_INTEGRAL_POINTS,         *)
(* ELLIPTIC_INTEGRAL_POINTS, WEIERSTRASS_INTEGRAL_POINTS; helper names       *)
(* ELLIPTIC_*.                                                               *)
(*                                                                           *)
(* Uses: Baker/hyperell.ml (HYPERELLIPTIC), Baker/cubic_reduction.ml         *)
(* (CUBIC_VIETA); library EXPAND_SUM_CONV, EXPAND_VSUM_CONV.                 *)
(* ========================================================================= *)

needs "Baker/cubic_reduction.ml";;
needs "Baker/hyperell.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Algebraic identities: the cubic in terms of its roots, and the            *)
(* discriminants of the short and the general Weierstrass equations.         *)
(* ------------------------------------------------------------------------- *)

let ELLIPTIC_CUBIC_DISC = prove
 (`!a b c d t1 t2 t3:complex.
     b = --(a * (t1 + t2 + t3)) /\
     c = a * (t1 * t2 + t1 * t3 + t2 * t3) /\
     d = --(a * t1 * t2 * t3)
     ==> b pow 2 * c pow 2 - Cx(&4) * a * c pow 3 - Cx(&4) * b pow 3 * d -
         Cx(&27) * a pow 2 * d pow 2 + Cx(&18) * a * b * c * d =
         a pow 4 * ((t1 - t2) * (t1 - t3) * (t2 - t3)) pow 2 /\
         (!z. a * z pow 3 + b * z pow 2 + c * z + d =
              a * (z - t1) * (z - t2) * (z - t3)) /\
         Cx(&3) * a * t1 pow 2 + Cx(&2) * b * t1 + c =
         a * (t1 - t2) * (t1 - t3) /\
         Cx(&3) * a * t2 pow 2 + Cx(&2) * b * t2 + c =
         a * (t2 - t1) * (t2 - t3) /\
         Cx(&3) * a * t3 pow 2 + Cx(&2) * b * t3 + c =
         a * (t3 - t1) * (t3 - t2)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THEN
  REPEAT CONJ_TAC THEN TRY GEN_TAC THEN CONV_TAC COMPLEX_RING);;

let ELLIPTIC_SHORT_WEIERSTRASS = prove
 (`!a b:real.
     &0 pow 2 * a pow 2 - &4 * &1 * a pow 3 - &4 * &0 pow 3 * b -
     &27 * &1 pow 2 * b pow 2 + &18 * &1 * &0 * a * b =
     --(&4 * a pow 3 + &27 * b pow 2) /\
     (let b2 = &0 pow 2 + &4 * &0
      and b4 = &2 * a + &0 * &0
      and b6 = &0 pow 2 + &4 * b
      and b8 = &0 pow 2 * b + &4 * &0 * b - &0 * &0 * a +
               &0 * &0 pow 2 - a pow 2 in
      &9 * b2 * b4 * b6 - b2 pow 2 * b8 - &8 * b4 pow 3 - &27 * b6 pow 2) =
     --(&16) * (&4 * a pow 3 + &27 * b pow 2)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  CONJ_TAC THEN CONV_TAC REAL_RING);;

let ELLIPTIC_WEIERSTRASS = prove
 (`!a1 a2 a3 a4 a6 x y:real.
     let b2 = a1 pow 2 + &4 * a2
     and b4 = &2 * a4 + a1 * a3
     and b6 = a3 pow 2 + &4 * a6
     and b8 = a1 pow 2 * a6 + &4 * a2 * a6 - a1 * a3 * a4 +
              a2 * a3 pow 2 - a4 pow 2 in
     (&2 * y + a1 * x + a3) pow 2 -
     (&4 * x pow 3 + b2 * x pow 2 + &2 * b4 * x + b6) =
     &4 * ((y pow 2 + a1 * x * y + a3 * y) -
           (x pow 3 + a2 * x pow 2 + a4 * x + a6)) /\
     &4 * b8 = b2 * b6 - b4 pow 2 /\
     b2 pow 2 * (&2 * b4) pow 2 - &4 * &4 * (&2 * b4) pow 3 -
     &4 * b2 pow 3 * b6 - &27 * &4 pow 2 * b6 pow 2 +
     &18 * &4 * b2 * (&2 * b4) * b6 =
     &16 * (&9 * b2 * b4 * b6 - b2 pow 2 * b8 - &8 * b4 pow 3 -
            &27 * b6 pow 2)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REPEAT CONJ_TAC THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* A cubic with non-zero discriminant has three distinct simple roots.       *)
(* ------------------------------------------------------------------------- *)

let CUBIC_SIMPLE_ROOTS = prove
 (`!a b c d.
     ~(a = &0) /\
     ~(b pow 2 * c pow 2 - &4 * a * c pow 3 - &4 * b pow 3 * d -
       &27 * a pow 2 * d pow 2 + &18 * a * b * c * d = &0)
     ==> ?z1 z2 z3.
           ~(z1 = z2) /\ ~(z1 = z3) /\ ~(z2 = z3) /\
           !z. z IN {z1, z2, z3}
               ==> Cx a * z pow 3 + Cx b * z pow 2 + Cx c * z + Cx d =
                   Cx(&0) /\
                   ~(Cx(&3 * a) * z pow 2 + Cx(&2 * b) * z + Cx c = Cx(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(SPECL [`Cx a`; `Cx b`; `Cx c`; `Cx d`] CUBIC_VIETA) THEN
  ASM_REWRITE_TAC[CX_INJ; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t1:complex`; `t2:complex`; `t3:complex`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP ELLIPTIC_CUBIC_DISC) THEN
  REWRITE_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
  REWRITE_TAC[CX_SUB; CX_ADD; CX_MUL; CX_POW] THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; COMPLEX_SUB_0; CX_INJ;
                  ARITH_EQ; DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t1:complex`; `t2:complex`; `t3:complex`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:complex` THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_SUB_0; CX_INJ] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The equation y^2 = a x^3 + b x^2 + c x + d (Baker 1968).                  *)
(* ------------------------------------------------------------------------- *)

let ELLIPTIC_CUBIC_SUMS = prove
 (`!(A:num->real) a b c d.
     A 0 = d /\ A 1 = c /\ A 2 = b /\ A 3 = a
     ==> (!x. sum(0..3) (\i. A i * x pow i) =
              a * x pow 3 + b * x pow 2 + c * x + d) /\
         (!z. vsum(0..3) (\i. Cx(A i) * z pow i) =
              Cx a * z pow 3 + Cx b * z pow 2 + Cx c * z + Cx d) /\
         (!z. vsum(1..3) (\i. Cx(&i * A i) * z pow (i - 1)) =
              Cx(&3 * a) * z pow 2 + Cx(&2 * b) * z + Cx c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN GEN_TAC THEN
  CONV_TAC(LAND_CONV(EXPAND_SUM_CONV ORELSEC EXPAND_VSUM_CONV)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[CX_MUL] THEN
  CONV_TAC(REAL_RING ORELSEC COMPLEX_RING));;

let ELLIPTIC_CUBIC_INTEGRAL_POINTS = prove
 (`!a b c d.
     integer a /\ integer b /\ integer c /\ integer d /\ ~(a = &0) /\
     ~(b pow 2 * c pow 2 - &4 * a * c pow 3 - &4 * b pow 3 * d -
       &27 * a pow 2 * d pow 2 + &18 * a * b * c * d = &0)
     ==> FINITE {(x,y) | integer x /\ integer y /\
                         y pow 2 = a * x pow 3 + b * x pow 2 + c * x + d}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`] CUBIC_SIMPLE_ROOTS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`z1:complex`; `z2:complex`; `z3:complex`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `z1:complex` th) THEN
                          MP_TAC(SPEC `z2:complex` th) THEN
                          MP_TAC(SPEC `z3:complex` th)) THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?A:num->real. (!i. integer(A i)) /\
                              A 0 = d /\ A 1 = c /\ A 2 = b /\ A 3 = a`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\i. if i = 0 then d else if i = 1 then c
                    else if i = 2 then b else a:real` THEN
    BETA_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN
    GEN_TAC THEN REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`A:num->real`; `a:real`; `b:real`; `c:real`; `d:real`]
         ELLIPTIC_CUBIC_SUMS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `A:num->real`; `z1:complex`; `z2:complex`;
                 `z3:complex`] HYPERELLIPTIC) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The short Weierstrass equation y^2 = x^3 + a x + b.                       *)
(* ------------------------------------------------------------------------- *)

let ELLIPTIC_INTEGRAL_POINTS = prove
 (`!a b. integer a /\ integer b /\ ~(&4 * a pow 3 + &27 * b pow 2 = &0)
        ==> FINITE {(x,y) | integer x /\ integer y /\
                            y pow 2 = x pow 3 + a * x + b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`&1`; `&0`; `a:real`; `b:real`]
         ELLIPTIC_CUBIC_INTEGRAL_POINTS) THEN
  ASM_REWRITE_TAC[ELLIPTIC_SHORT_WEIERSTRASS; REAL_NEG_EQ_0; INTEGER_CLOSED;
                  REAL_OF_NUM_EQ; ARITH_EQ] THEN
  REWRITE_TAC[REAL_MUL_LID; REAL_MUL_LZERO; REAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* The general Weierstrass equation (b2, b4, b6, b8 and Delta as in Tate     *)
(* and Silverman, Ch. III.1).                                                *)
(* ------------------------------------------------------------------------- *)

let WEIERSTRASS_INTEGRAL_POINTS = prove
 (`!a1 a2 a3 a4 a6.
     integer a1 /\ integer a2 /\ integer a3 /\ integer a4 /\ integer a6 /\
     ~(let b2 = a1 pow 2 + &4 * a2
       and b4 = &2 * a4 + a1 * a3
       and b6 = a3 pow 2 + &4 * a6
       and b8 = a1 pow 2 * a6 + &4 * a2 * a6 - a1 * a3 * a4 +
                a2 * a3 pow 2 - a4 pow 2 in
       &9 * b2 * b4 * b6 - b2 pow 2 * b8 - &8 * b4 pow 3 -
       &27 * b6 pow 2 = &0)
     ==> FINITE {(x,y) | integer x /\ integer y /\
                         y pow 2 + a1 * x * y + a3 * y =
                         x pow 3 + a2 * x pow 2 + a4 * x + a6}`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`&4`; `a1 pow 2 + &4 * a2`; `&2 * (&2 * a4 + a1 * a3)`;
                `a3 pow 2 + &4 * a6`] ELLIPTIC_CUBIC_INTEGRAL_POINTS) THEN
  MP_TAC(SPECL [`a1:real`; `a2:real`; `a3:real`; `a4:real`; `a6:real`;
                `&0`; `&0`] ELLIPTIC_WEIERSTRASS) THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2(CONJUNCT2 th)]) THEN
  ASM_SIMP_TAC[INTEGER_CLOSED; REAL_ENTIRE; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_THEN(MP_TAC o
    ISPEC `\p:real#real. FST p,(SND p - a1 * FST p - a3) / &2` o
    MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_IMAGE;
              EXISTS_PAIR_THM; PAIR_EQ] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`x:real`; `&2 * y + a1 * x + a3`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN CONJ_TAC THENL
   [REAL_ARITH_TAC;
    MP_TAC(SPECL [`a1:real`; `a2:real`; `a3:real`; `a4:real`; `a6:real`;
                  `x:real`; `y:real`] ELLIPTIC_WEIERSTRASS) THEN
    CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[REAL_SUB_REFL] THEN
    REAL_ARITH_TAC]);;
