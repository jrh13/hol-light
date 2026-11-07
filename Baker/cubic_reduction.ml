(* ========================================================================= *)
(* Reduction theory of binary cubic forms (Hermite reduction).               *)
(*                                                                           *)
(* Purpose: for fixed D <> 0 there is a finite set Phi of integer cubic      *)
(* forms such that every integer cubic form                                  *)
(*   F(u,v) = a u^3 + b u^2 v + c u v^2 + d v^3                              *)
(* of discriminant D without non-trivial integer zero is                     *)
(* SL2(Z)-equivalent to a form of Phi. Route: complex roots t1 t2 t3 of      *)
(* a t^3 + b t^2 + c t + d (Vieta); weights                                  *)
(* lam_i = |t_j - t_k| / (|t_i - t_j| |t_i - t_k|) and the form              *)
(* Q(u,v) = sum lam_i |u - t_i v|^2 = A u^2 + B u v + C v^2 with             *)
(* 4 A C - B^2 = 12 and sqrt|D| Q^3 >= 27 F^2 (AM-GM); the identity          *)
(* sum lam_i Im t_i = 0 from the invariance of a sum over the root set       *)
(* under complex conjugation; reduction of real positive definite binary     *)
(* quadratic forms by minimising over first columns of SL2(Z) matrices;      *)
(* explicit coefficient bounds M = 2 + 6 |D| for the reduced form.           *)
(*                                                                           *)
(* Main results: CUBIC_FORM_REDUCTION, CUBIC_HERMITE_FORM (the balanced      *)
(* quadratic form), CUBIC_QF_REDUCE (reduction of quadratic forms).          *)
(*                                                                           *)
(* Uses: Baker/algebraic.ml (COMPLEX_POLYFUN_FACTOR), Baker/lemmas.ml        *)
(* (FINITE_ARGMIN).                                                          *)
(* ========================================================================= *)

needs "Baker/algebraic.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Complex roots of a cubic (Vieta) and conjugation of the root set.         *)
(* ------------------------------------------------------------------------- *)

let CUBIC_VSUM_CPRODUCT_3 = prove
 (`!f g:num->complex. vsum(0..3) f = f 0 + f 1 + f 2 + f 3 /\
                      cproduct(1..3) g = g 1 * g 2 * g 3`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[num_CONV `3`; num_CONV `2`; num_CONV `1`;
              VSUM_CLAUSES_NUMSEG; CPRODUCT_CLAUSES_NUMSEG; LE_0; LE_SUC;
              LE_REFL; NOT_SUC] THEN
  REWRITE_TAC[GSYM ONE; COMPLEX_MUL_LID] THEN
  REWRITE_TAC[GSYM COMPLEX_ADD_ASSOC; GSYM COMPLEX_MUL_ASSOC]);;

let CUBIC_VIETA = prove
 (`!a b c d:complex.
        ~(a = Cx(&0))
        ==> ?t1 t2 t3. b = --(a * (t1 + t2 + t3)) /\
                       c = a * (t1 * t2 + t1 * t3 + t2 * t3) /\
                       d = --(a * t1 * t2 * t3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `\i. if i = 0 then d else if i = 1 then c
                          else if i = 2 then b else a:complex`]
         COMPLEX_POLYFUN_FACTOR) THEN
  ASM_REWRITE_TAC[ARITH; CUBIC_VSUM_CPRODUCT_3] THEN
  DISCH_THEN(X_CHOOSE_TAC `r:num->complex`) THEN
  MAP_EVERY EXISTS_TAC
   [`(r:num->complex) 1`; `(r:num->complex) 2`; `(r:num->complex) 3`] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `Cx(&0)` th) THEN
                          MP_TAC(SPEC `Cx(&1)` th) THEN
                          MP_TAC(SPEC `--Cx(&1)` th)) THEN
  CONV_TAC COMPLEX_RING);;

let CUBIC_SUM_CNJ_IM = prove
 (`!s (g:complex->real).
        FINITE s /\ (!z. z IN s ==> cnj z IN s) /\ (!z. g(cnj z) = g z)
        ==> sum s (\z. g z * Im z) = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE cnj s = s` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `w:complex` THEN
    EQ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN EXISTS_TAC `cnj w` THEN ASM_SIMP_TAC[CNJ_CNJ];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cnj`; `\z. (g:complex->real) z * Im z`;
                 `s:complex->bool`] SUM_IMAGE) THEN
  ANTS_TAC THENL [MESON_TAC[CNJ_INJ]; ALL_TAC] THEN
  ASM_REWRITE_TAC[o_DEF; IM_CNJ] THEN
  REWRITE_TAC[REAL_MUL_RNEG; SUM_NEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `!x:real. x = --x ==> x = &0`) THEN
  FIRST_ASSUM ACCEPT_TAC);;

let CUBIC_SUM_3 = prove
 (`!t1 t2 t3:A.
        ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)
        ==> !f. sum {t1,t2,t3} f = f t1 + f t2 + f t3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  SIMP_TAC[SUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ADD_RID]);;

let CUBIC_ROOTS_CNJ = prove
 (`!a b c d t1 t2 t3 z.
        ~(a = &0) /\
        (!z. Cx a * z pow 3 + Cx b * z pow 2 + Cx c * z + Cx d =
             Cx a * (z - t1) * (z - t2) * (z - t3)) /\
        z IN {t1,t2,t3}
        ==> cnj z IN {t1,t2,t3}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `Cx a * cnj z pow 3 + Cx b * cnj z pow 2 + Cx c * cnj z + Cx d = Cx(&0)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `Cx a * cnj z pow 3 + Cx b * cnj z pow 2 + Cx c * cnj z + Cx d =
      cnj(Cx a * z pow 3 + Cx b * z pow 2 + Cx c * z + Cx d)`
    SUBST1_TAC THENL
     [REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_POW; CNJ_CX]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[IN_INSERT;
      NOT_IN_EMPTY]) THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO;
      COMPLEX_MUL_RZERO; CNJ_CX];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; CX_INJ; COMPLEX_SUB_0] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]]);;

let CUBIC_ROOTS_IM_WEIGHTED = prove
 (`!a b c d t1 t2 t3.
        ~(a = &0) /\
        Cx b = --(Cx a * (t1 + t2 + t3)) /\
        Cx c = Cx a * (t1 * t2 + t1 * t3 + t2 * t3) /\
        Cx d = --(Cx a * t1 * t2 * t3) /\
        ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)
        ==> Im t1 / (norm(t1 - t2) * norm(t1 - t3)) pow 2 +
            Im t2 / (norm(t1 - t2) * norm(t2 - t3)) pow 2 +
            Im t3 / (norm(t1 - t3) * norm(t2 - t3)) pow 2 = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{t1:complex,t2,t3}`;
    `\z. inv(norm(Cx(&3 * a) * z pow 2 + Cx(&2 * b) * z + Cx c) pow 2)`]
   CUBIC_SUM_CNJ_IM) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN CONJ_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      MATCH_MP_TAC CUBIC_ROOTS_CNJ THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `b:real`; `c:real`; `d:real`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
      X_GEN_TAC `z:complex` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `Cx(&3 * a) * cnj z pow 2 + Cx(&2 * b) * cnj z + Cx c =
        cnj(Cx(&3 * a) * z pow 2 + Cx(&2 * b) * z + Cx c)`
      SUBST1_TAC THENL
       [REWRITE_TAC[CNJ_ADD; CNJ_MUL; CNJ_POW; CNJ_CX];
        REWRITE_TAC[COMPLEX_NORM_CNJ]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:complex`; `t2:complex`; `t3:complex`] CUBIC_SUM_3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  SUBGOAL_THEN
   `Cx(&3 * a) * t1 pow 2 + Cx(&2 * b) * t1 + Cx c =
    Cx a * (t1 - t2) * (t1 - t3) /\
    Cx(&3 * a) * t2 pow 2 + Cx(&2 * b) * t2 + Cx c =
    Cx a * (t2 - t1) * (t2 - t3) /\
    Cx(&3 * a) * t3 pow 2 + Cx(&2 * b) * t3 + Cx c =
    Cx a * (t3 - t1) * (t3 - t2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[CX_MUL] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  SUBGOAL_THEN `&0 < abs a /\ &0 < norm(t1 - t2) /\ &0 < norm(t1 - t3) /\
                &0 < norm(t2 - t3)` MP_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ; REAL_ARITH
     `&0 < abs x <=> ~(x = &0)`];
    ALL_TAC] THEN
  REWRITE_TAC[NORM_SUB] THEN CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* The balanced Hermite quadratic form of a real cubic form.                 *)
(* ------------------------------------------------------------------------- *)

let CUBIC_AM_GM_3 = prove
 (`!x y z. &0 <= x /\ &0 <= y /\ &0 <= z
           ==> &27 * x * y * z <= (x + y + z) pow 3`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!e. &0 <= e /\ p - q = e ==> (q:real) <= p`) THEN
  EXISTS_TAC
   `(x + y + z) * ((x - y) pow 2 + (y - z) pow 2 + (z - x) pow 2) / &2 +
    &3 * (x * (y - z) pow 2 + y * (z - x) pow 2 + z * (x - y) pow 2)` THEN
  CONJ_TAC THENL [ALL_TAC; REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      REWRITE_TAC[] THEN
      REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_LE_POW_2]];
    MATCH_MP_TAC REAL_LE_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[] THEN
    REPEAT(MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_LE_POW_2]]);;

let CUBIC_HERMITE_ALGEBRA_0 = prove
 (`!a l1 l2 l3 x1 y1 x2 y2 x3 y3 s.
        &0 < l1 /\ &0 < l2 /\ &0 < l3 /\
        l1 * l2 * ((x1 - x2) pow 2 + (y1 - y2) pow 2) = &1 /\
        l1 * l3 * ((x1 - x3) pow 2 + (y1 - y3) pow 2) = &1 /\
        l2 * l3 * ((x2 - x3) pow 2 + (y2 - y3) pow 2) = &1 /\
        l1 * y1 + l2 * y2 + l3 * y3 = &0 /\
        &0 <= s /\ s * l1 * l2 * l3 = a pow 2
        ==> &0 < l1 + l2 + l3 /\
            &4 * (l1 + l2 + l3) *
                 (l1 * (x1 pow 2 + y1 pow 2) + l2 * (x2 pow 2 + y2 pow 2) +
                  l3 * (x3 pow 2 + y3 pow 2)) -
            (--(&2 * (l1 * x1 + l2 * x2 + l3 * x3))) pow 2 = &12 /\
            !u v. &27 * a pow 2 *
                  ((u - x1 * v) pow 2 + (y1 * v) pow 2) *
                  ((u - x2 * v) pow 2 + (y2 * v) pow 2) *
                  ((u - x3 * v) pow 2 + (y3 * v) pow 2)
                  <= s * ((l1 + l2 + l3) * u pow 2 +
                          --(&2 * (l1 * x1 + l2 * x2 + l3 * x3)) * u * v +
                          (l1 * (x1 pow 2 + y1 pow 2) +
                           l2 * (x2 pow 2 + y2 pow 2) +
                           l3 * (x3 pow 2 + y3 pow 2)) * v pow 2) pow 3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `&4 * (l1 + l2 + l3) *
          (l1 * (x1 pow 2 + y1 pow 2) + l2 * (x2 pow 2 + y2 pow 2) +
           l3 * (x3 pow 2 + y3 pow 2)) -
      (--(&2 * (l1 * x1 + l2 * x2 + l3 * x3))) pow 2 =
      &4 * (l1 * l2 * ((x1 - x2) pow 2 + (y1 - y2) pow 2) +
            l1 * l3 * ((x1 - x3) pow 2 + (y1 - y3) pow 2) +
            l2 * l3 * ((x2 - x3) pow 2 + (y2 - y3) pow 2) +
            (l1 * y1 + l2 * y2 + l3 * y3) pow 2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(l1 + l2 + l3) * u pow 2 +
      --(&2 * (l1 * x1 + l2 * x2 + l3 * x3)) * u * v +
      (l1 * (x1 pow 2 + y1 pow 2) + l2 * (x2 pow 2 + y2 pow 2) +
       l3 * (x3 pow 2 + y3 pow 2)) * v pow 2 =
      l1 * ((u - x1 * v) pow 2 + (y1 * v) pow 2) +
      l2 * ((u - x2 * v) pow 2 + (y2 * v) pow 2) +
      l3 * ((u - x3 * v) pow 2 + (y3 * v) pow 2)`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (u - x1 * v) pow 2 + (y1 * v) pow 2 /\
                  &0 <= (u - x2 * v) pow 2 + (y2 * v) pow 2 /\
                  &0 <= (u - x3 * v) pow 2 + (y3 * v) pow 2`
    MP_TAC THENL [SIMP_TAC[REAL_LE_ADD; REAL_LE_POW_2]; ALL_TAC] THEN
    SPEC_TAC(`(u - x1 * v) pow 2 + (y1 * v) pow 2`,`X1:real`) THEN
    SPEC_TAC(`(u - x2 * v) pow 2 + (y2 * v) pow 2`,`X2:real`) THEN
    SPEC_TAC(`(u - x3 * v) pow 2 + (y3 * v) pow 2`,`X3:real`) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`l1 * X1:real`; `l2 * X2:real`; `l3 * X3:real`]
      CUBIC_AM_GM_3) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_LMUL o CONJ
      (ASSUME `&0 <= s`)) THEN
    MATCH_MP_TAC(REAL_ARITH `(x:real) = y ==> x <= z ==> y <= z`) THEN
    UNDISCH_TAC `s * l1 * l2 * l3 = a pow 2` THEN CONV_TAC REAL_RING]);;

let CUBIC_HERMITE_FORM = prove
 (`!a b c d.
        ~(a = &0) /\
        ~(b pow 2 * c pow 2 - &4 * a * c pow 3 - &4 * b pow 3 * d -
          &27 * a pow 2 * d pow 2 + &18 * a * b * c * d = &0)
        ==> ?A B C.
              &0 < A /\ &4 * A * C - B pow 2 = &12 /\
              !u v. &27 * (a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
                           d * v pow 3) pow 2
                    <= sqrt(abs(b pow 2 * c pow 2 - &4 * a * c pow 3 -
                                &4 * b pow 3 * d - &27 * a pow 2 * d pow 2 +
                                &18 * a * b * c * d)) *
                       (A * u pow 2 + B * u * v + C * v pow 2) pow 3`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `D = b pow 2 * c pow 2 - &4 * a * c pow 3 - &4 * b pow 3 * d -
                  &27 * a pow 2 * d pow 2 + &18 * a * b * c * d` THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`Cx a`; `Cx b`; `Cx c`; `Cx d`] CUBIC_VIETA) THEN
  ASM_REWRITE_TAC[CX_INJ] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:complex` (X_CHOOSE_THEN `t2:complex`
    (X_CHOOSE_THEN `t3:complex` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `Cx D = Cx a pow 4 * ((t1 - t2) * (t1 - t3) * (t2 - t3)) pow 2`
  ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN
    REWRITE_TAC[CX_SUB; CX_ADD; CX_MUL; CX_POW] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t1:complex = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~(D = &0)` THEN
    REWRITE_TAC[GSYM CX_INJ] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(t1 - t2) /\ &0 < norm(t1 - t3) /\
                &0 < norm(t2 - t3)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `sqrt(abs D) = a pow 2 * norm(t1 - t2) * norm(t1 - t3) * norm(t2 - t3)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SQRT_UNIQUE THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:complex->real` o
      check (fun th -> is_eq(concl th) &&
                       lhand(concl th) = `Cx D`)) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[REAL_ARITH `abs a pow 4 = (abs a pow 2) pow 2`] THEN
    REWRITE_TAC[REAL_POW2_ABS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. (a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 + d * v pow 3)
          pow 2 =
          a pow 2 *
          ((u - Re t1 * v) pow 2 + (Im t1 * v) pow 2) *
          ((u - Re t2 * v) pow 2 + (Im t2 * v) pow 2) *
          ((u - Re t3 * v) pow 2 + (Im t3 * v) pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `Cx(a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 + d * v pow 3) =
      Cx a * (Cx u - t1 * Cx v) * (Cx u - t2 * Cx v) * (Cx u - t3 * Cx v)`
    MP_TAC THENL
     [REWRITE_TAC[CX_ADD; CX_MUL; CX_POW] THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX; COMPLEX_NORM_MUL] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\x:real. x pow 2`) THEN
    REWRITE_TAC[REAL_POW2_ABS; REAL_POW_MUL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_SQNORM; RE_SUB; IM_SUB; RE_CX; IM_CX; RE_MUL_CX;
                IM_MUL_CX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`;
                `t1:complex`; `t2:complex`; `t3:complex`]
       CUBIC_ROOTS_IM_WEIGHTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL
   [`a:real`;
    `norm(t2 - t3:complex) / (norm(t1 - t2:complex) * norm(t1 - t3:complex))`;
    `norm(t1 - t3:complex) / (norm(t1 - t2:complex) * norm(t2 - t3:complex))`;
    `norm(t1 - t2:complex) / (norm(t1 - t3:complex) * norm(t2 - t3:complex))`;
    `Re t1`; `Im t1`; `Re t2`; `Im t2`; `Re t3`; `Im t3`;
    `a pow 2 * norm(t1 - t2:complex) * norm(t1 - t3:complex) *
     norm(t2 - t3:complex)`] CUBIC_HERMITE_ALGEBRA_0) THEN
  SUBGOAL_THEN
   `(Re t1 - Re t2) pow 2 + (Im t1 - Im t2) pow 2 = norm(t1 - t2) pow 2 /\
    (Re t1 - Re t3) pow 2 + (Im t1 - Im t3) pow 2 = norm(t1 - t3) pow 2 /\
    (Re t2 - Re t3) pow 2 + (Im t2 - Im t3) pow 2 = norm(t2 - t3) pow 2`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[COMPLEX_SQNORM; RE_SUB; IM_SUB]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < norm(t1 - t2)` THEN
      UNDISCH_TAC `&0 < norm(t1 - t3)` THEN
      UNDISCH_TAC `&0 < norm(t2 - t3)` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < norm(t1 - t2)` THEN
      UNDISCH_TAC `&0 < norm(t1 - t3)` THEN
      UNDISCH_TAC `&0 < norm(t2 - t3)` THEN CONV_TAC REAL_FIELD;
      UNDISCH_TAC `&0 < norm(t1 - t2)` THEN
      UNDISCH_TAC `&0 < norm(t1 - t3)` THEN
      UNDISCH_TAC `&0 < norm(t2 - t3)` THEN CONV_TAC REAL_FIELD;
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
         rand(concl th) = `&0` && is_binop `(+):real->real->real`
         (lhand(concl th)))) THEN
      UNDISCH_TAC `&0 < norm(t1 - t2)` THEN
      UNDISCH_TAC `&0 < norm(t1 - t3)` THEN
      UNDISCH_TAC `&0 < norm(t2 - t3)` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
      UNDISCH_TAC `&0 < norm(t1 - t2)` THEN
      UNDISCH_TAC `&0 < norm(t1 - t3)` THEN
      UNDISCH_TAC `&0 < norm(t2 - t3)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`norm(t2 - t3:complex) / (norm(t1 - t2:complex) * norm(t1 - t3:complex)) +
     norm(t1 - t3:complex) / (norm(t1 - t2:complex) * norm(t2 - t3:complex)) +
     norm(t1 - t2:complex) / (norm(t1 - t3:complex) * norm(t2 - t3:complex))`;
    `--(&2 *
        (norm(t2 - t3:complex) / (norm(t1 - t2:complex) *
                                  norm(t1 - t3:complex)) * Re t1 +
         norm(t1 - t3:complex) / (norm(t1 - t2:complex) *
                                  norm(t2 - t3:complex)) * Re t2 +
         norm(t1 - t2:complex) / (norm(t1 - t3:complex) *
                                  norm(t2 - t3:complex)) * Re t3))`;
    `norm(t2 - t3:complex) / (norm(t1 - t2:complex) * norm(t1 - t3:complex)) *
     (Re t1 pow 2 + Im t1 pow 2) +
     norm(t1 - t3:complex) / (norm(t1 - t2:complex) * norm(t2 - t3:complex)) *
     (Re t2 pow 2 + Im t2 pow 2) +
     norm(t1 - t2:complex) / (norm(t1 - t3:complex) * norm(t2 - t3:complex)) *
     (Re t3 pow 2 + Im t3 pow 2)`] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Reduction of real positive definite binary quadratic forms: a basis       *)
(* (p,r), (q,s) of Z^2 of determinant 1 with |B1| <= A1 <= C1.               *)
(* ------------------------------------------------------------------------- *)

let CUBIC_QF_POS = prove
 (`!A B C x y.
        &0 < A /\ &0 < &4 * A * C - B pow 2 /\ ~(x = &0 /\ y = &0)
        ==> &0 < A * x pow 2 + B * x * y + C * y pow 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &4 * A * (A * x pow 2 + B * x * y + C * y pow 2)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `&4 * A * (A * x pow 2 + B * x * y + C * y pow 2) =
      (&2 * A * x + B * y) pow 2 + (&4 * A * C - B pow 2) * y pow 2`
    SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `y = &0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `~(x = &0)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID; REAL_POW_ZERO; ARITH_EQ;
                  REAL_LT_POW_2] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 < b ==> &0 < a + b`) THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_REWRITE_TAC[REAL_LT_POW_2]];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_ARITH `&0 < A ==> &0 < &4 * A`]]);;

let CUBIC_ABS_LE_1_SQ = prove
 (`!x. abs x <= &1 + x pow 2`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  MP_TAC(SPEC `abs x - &1 / &2` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let CUBIC_QF_BOUND = prove
 (`!A B C x y.
        &0 < A /\ &0 < &4 * A * C - B pow 2 /\
        A * x pow 2 + B * x * y + C * y pow 2 <= A
        ==> abs x <= &1 + (&4 * A * (A + C)) / (&4 * A * C - B pow 2) /\
            abs y <= &1 + (&4 * A * (A + C)) / (&4 * A * C - B pow 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < C` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < A * C` MP_TAC THENL
     [MP_TAC(SPEC `B:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LT_MUL_EQ]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 * A * C - B pow 2) * (x pow 2 + y pow 2) <= &4 * A * (A + C)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&4 * (A + C) * (A * x pow 2 + B * x * y + C * y pow 2)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!p q z w:real. &0 <= p /\ &0 <= q /\ z = p + q + w ==> w <= z`) THEN
      MAP_EVERY EXISTS_TAC
       [`(&2 * A * x + B * y) pow 2`; `(B * x + &2 * C * y) pow 2`] THEN
      REWRITE_TAC[REAL_LE_POW_2] THEN REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[REAL_ARITH `&4 * A * (A + C) = &4 * (A + C) * A`] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `x pow 2 <= (&4 * A * (A + C)) / (&4 * A * C - B pow 2) /\
    y pow 2 <= (&4 * A * (A + C)) / (&4 * A * C - B pow 2)`
  MP_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN CONJ_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&4 * A * C - B pow 2) * (x pow 2 + y pow 2)` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_MUL_SYM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
    MP_TAC(SPEC `y:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` CUBIC_ABS_LE_1_SQ) THEN
  MP_TAC(SPEC `y:real` CUBIC_ABS_LE_1_SQ) THEN REAL_ARITH_TAC);;

let CUBIC_QF_REDUCE = prove
 (`!A B C.
        &0 < A /\ &0 < &4 * A * C - B pow 2
        ==> ?p q r s.
              integer p /\ integer q /\ integer r /\ integer s /\
              p * s - q * r = &1 /\
              abs(&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s)
              <= A * p pow 2 + B * p * r + C * r pow 2 /\
              A * p pow 2 + B * p * r + C * r pow 2
              <= A * q pow 2 + B * q * s + C * s pow 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `K = &1 + (&4 * A * (A + C)) / (&4 * A * C - B pow 2)` THEN
  MP_TAC(ISPECL
   [`{(x,y) | integer x /\ integer y /\
              (?z w. integer z /\ integer w /\ x * w - z * y = &1) /\
              A * x pow 2 + B * x * y + C * y pow 2 <= A}`;
    `\z:real#real. A * FST z pow 2 + B * FST z * SND z + C * SND z pow 2`]
   FINITE_ARGMIN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x | integer x /\ abs x <= K} CROSS
                  {y | integer y /\ abs y <= K}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_CROSS THEN
        REWRITE_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG];
        REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_CROSS;
                    IN_ELIM_THM] THEN
        MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN
        MATCH_MP_TAC CUBIC_QF_BOUND THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(&1, &0)` THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM; INTEGER_CLOSED] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`&0`; `&1`] THEN
        REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
        REAL_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_PAIR_THM; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `r:real` MP_TAC)) THEN
  REWRITE_TAC[FST; SND] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `q0:real` (X_CHOOSE_THEN `s0:real`
      STRIP_ASSUME_TAC)) ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!x y z w. integer x /\ integer y /\ integer z /\ integer w /\
              x * w - z * y = &1
              ==> A * p pow 2 + B * p * r + C * r pow 2 <=
                  A * x pow 2 + B * x * y + C * y pow 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `A * x pow 2 + B * x * y + C * y pow 2 <= A` THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `A' = A * p pow 2 + B * p * r + C * r pow 2` THEN
  SUBGOAL_THEN `&0 < A'` ASSUME_TAC THENL
   [EXPAND_TAC "A'" THEN MATCH_MP_TAC CUBIC_QF_POS THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p * s0 - q0 * r = &1` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC
   `B0 = &2 * A * p * q0 + B * (p * s0 + q0 * r) + &2 * C * r * s0` THEN
  ABBREV_TAC `k = floor((A' - B0) / (&2 * A'))` THEN
  SUBGOAL_THEN `integer k /\ k * (&2 * A') <= A' - B0 /\
                A' - B0 < (k + &1) * (&2 * A')`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `(A' - B0) / (&2 * A')` FLOOR) THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LT_LDIV_EQ;
                 REAL_ARITH `&0 < A' ==> &0 < &2 * A'`];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`p:real`; `q0 + k * p:real`; `r:real`; `s0 + k * r:real`] THEN
  ASM_SIMP_TAC[INTEGER_CLOSED] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `p * s0 - q0 * r = &1` THEN REAL_ARITH_TAC;
    SUBGOAL_THEN
     `&2 * A * p * (q0 + k * p) + B * (p * (s0 + k * r) + (q0 + k * p) * r) +
      &2 * C * r * (s0 + k * r) = B0 + &2 * k * A'`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["B0"; "A'"] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_BOUNDS] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`--p:real`; `--r:real`] THEN
    ASM_SIMP_TAC[INTEGER_CLOSED] THEN
    UNDISCH_TAC `p * s0 - q0 * r = &1` THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Explicit coefficient bounds for the reduced form.                         *)
(* ------------------------------------------------------------------------- *)

let CUBIC_VALUE_BOUND = prove
 (`!S D C V w.
        &0 <= S /\ S pow 2 = abs D /\ &0 <= V /\ V <= &3 * C /\
        &27 * C pow 3 <= &64 * S /\ &27 * w pow 2 <= S * V pow 3
        ==> abs w <= &1 + &3 * abs D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `V pow 3 <= (&3 * C) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `S * V pow 3 <= S * (&3 * C) pow 3` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `S * &27 * C pow 3 <= S * &64 * S` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `w pow 2 <= &3 * abs D` ASSUME_TAC THENL
   [MP_TAC(SPEC `D:real` REAL_ABS_POS) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `w:real` CUBIC_ABS_LE_1_SQ) THEN ASM_REAL_ARITH_TAC);;

let CUBIC_BOUNDS_ALGEBRA = prove
 (`!S D A B C w1 w2 w3 w4.
        &0 <= S /\ S pow 2 = abs D /\
        abs B <= A /\ A <= C /\ &4 * A * C - B pow 2 = &12 /\
        &1 <= w1 pow 2 /\
        &27 * w1 pow 2 <= S * A pow 3 /\
        &27 * w2 pow 2 <= S * C pow 3 /\
        &27 * w3 pow 2 <= S * (A + B + C) pow 3 /\
        &27 * w4 pow 2 <= S * (A - B + C) pow 3
        ==> abs w1 <= &1 + &3 * abs D /\ abs w2 <= &1 + &3 * abs D /\
            abs w3 <= &1 + &3 * abs D /\ abs w4 <= &1 + &3 * abs D`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < A` ASSUME_TAC THENL
   [ASM_CASES_TAC `A = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `B = &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `&4 * A * C - B pow 2 = &12` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `B pow 2 <= A pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real) * A <= A * C` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= A * C /\ A * C <= &4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `B pow 2 <= A pow 2` THEN
      UNDISCH_TAC `(A:real) * A <= A * C` THEN
      UNDISCH_TAC `&4 * A * C - B pow 2 = &12` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&27 * C pow 3 <= &64 * S` ASSUME_TAC THENL
   [SUBGOAL_THEN `&27 * C pow 3 <= (S * A pow 3) * C pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `(A * C) pow 3 <= &4 pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `S * (A * C) pow 3 <= S * &4 pow 3` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `&27 * C pow 3 <= (S * A pow 3) * C pow 3` THEN
    UNDISCH_TAC `S * (A * C) pow 3 <= S * &4 pow 3` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC CUBIC_VALUE_BOUND THEN
  MAP_EVERY EXISTS_TAC [`S:real`; `C:real`] THENL
   [EXISTS_TAC `A:real`; EXISTS_TAC `C:real`;
    EXISTS_TAC `A + B + C:real`; EXISTS_TAC `A - B + C:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let CUBIC_SUBST_INTEGER = prove
 (`!a b c d p q r s.
        integer a /\ integer b /\ integer c /\ integer d /\
        integer p /\ integer q /\ integer r /\ integer s
        ==> integer(a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 +
                    d * r pow 3) /\
            integer(&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
                    c * (&2 * p * r * s + q * r pow 2) +
                    &3 * d * r pow 2 * s) /\
            integer(&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
                    c * (p * s pow 2 + &2 * q * r * s) +
                    &3 * d * r * s pow 2) /\
            integer(a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 +
                    d * s pow 3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST [CONJ_TAC; MATCH_MP_TAC INTEGER_ADD;
                MATCH_MP_TAC INTEGER_MUL; MATCH_MP_TAC INTEGER_POW]) THEN
  ASM_REWRITE_TAC[INTEGER_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* The reduced form: an SL2(Z) transform with explicitly bounded integer     *)
(* coefficients.                                                             *)
(* ------------------------------------------------------------------------- *)

let CUBIC_REDUCED_BOUNDS = prove
 (`!D a b c d.
        ~(D = &0) /\
        integer a /\ integer b /\ integer c /\ integer d /\
        b pow 2 * c pow 2 - &4 * a * c pow 3 - &4 * b pow 3 * d -
        &27 * a pow 2 * d pow 2 + &18 * a * b * c * d = D /\
        (!u v. integer u /\ integer v /\
               a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
               d * v pow 3 = &0
               ==> u = &0 /\ v = &0)
        ==> ?p q r s.
              integer p /\ integer q /\ integer r /\ integer s /\
              p * s - q * r = &1 /\
              abs(a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 +
                  d * r pow 3) <= &2 + &6 * abs D /\
              abs(&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
                  c * (&2 * p * r * s + q * r pow 2) +
                  &3 * d * r pow 2 * s) <= &2 + &6 * abs D /\
              abs(&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
                  c * (p * s pow 2 + &2 * q * r * s) +
                  &3 * d * r * s pow 2) <= &2 + &6 * abs D /\
              abs(a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 +
                  d * s pow 3) <= &2 + &6 * abs D`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (LABEL_TAC "Z"))))))) THEN
  SUBGOAL_THEN `~(a = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN REMOVE_THEN "Z" (MP_TAC o SPECL [`&1`; `&0`]) THEN
    ASM_REWRITE_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`]
    CUBIC_HERMITE_FORM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real` (X_CHOOSE_THEN `B:real`
   (X_CHOOSE_THEN `C:real` (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "IQ")))))) THEN
  MP_TAC(SPECL [`A:real`; `B:real`; `C:real`] CUBIC_QF_REDUCE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3 = &0)`
  ASSUME_TAC THENL
   [DISCH_TAC THEN REMOVE_THEN "Z" (MP_TAC o SPECL [`p:real`; `r:real`]) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `p * s - q * r = &1` THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`;
                `p:real`; `q:real`; `r:real`; `s:real`]
    CUBIC_SUBST_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  USE_THEN "IQ" (fun th ->
    MP_TAC(SPECL [`p:real`; `r:real`] th) THEN
    MP_TAC(SPECL [`q:real`; `s:real`] th) THEN
    MP_TAC(SPECL [`p + q:real`; `r + s:real`] th) THEN
    MP_TAC(SPECL [`p - q:real`; `r - s:real`] th)) THEN
  SUBGOAL_THEN
   `a * (p + q) pow 3 + b * (p + q) pow 2 * (r + s) +
    c * (p + q) * (r + s) pow 2 + d * (r + s) pow 3 =
    (a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3) +
    (&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
     c * (&2 * p * r * s + q * r pow 2) + &3 * d * r pow 2 * s) +
    (&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
     c * (p * s pow 2 + &2 * q * r * s) + &3 * d * r * s pow 2) +
    (a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 + d * s pow 3) /\
    a * (p - q) pow 3 + b * (p - q) pow 2 * (r - s) +
    c * (p - q) * (r - s) pow 2 + d * (r - s) pow 3 =
    (a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3) -
    (&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
     c * (&2 * p * r * s + q * r pow 2) + &3 * d * r pow 2 * s) +
    (&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
     c * (p * s pow 2 + &2 * q * r * s) + &3 * d * r * s pow 2) -
    (a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 + d * s pow 3) /\
    A * (p + q) pow 2 + B * (p + q) * (r + s) + C * (r + s) pow 2 =
    (A * p pow 2 + B * p * r + C * r pow 2) +
    (&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s) +
    (A * q pow 2 + B * q * s + C * s pow 2) /\
    A * (p - q) pow 2 + B * (p - q) * (r - s) + C * (r - s) pow 2 =
    (A * p pow 2 + B * p * r + C * r pow 2) -
    (&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s) +
    (A * q pow 2 + B * q * s + C * s pow 2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT CONJ_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&4 * (A * p pow 2 + B * p * r + C * r pow 2) *
         (A * q pow 2 + B * q * s + C * s pow 2) -
    (&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s) pow 2 = &12`
  MP_TAC THENL
   [UNDISCH_TAC `p * s - q * r = &1` THEN
    UNDISCH_TAC `&4 * A * C - B pow 2 = &12` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  UNDISCH_TAC
   `integer(a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3)` THEN
  UNDISCH_TAC
   `~(a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3 = &0)` THEN
  UNDISCH_TAC
   `abs(&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s)
    <= A * p pow 2 + B * p * r + C * r pow 2` THEN
  UNDISCH_TAC
   `A * p pow 2 + B * p * r + C * r pow 2
    <= A * q pow 2 + B * q * s + C * s pow 2` THEN
  SPEC_TAC(`a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3`,
           `a1:real`) THEN
  SPEC_TAC(`&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
            c * (&2 * p * r * s + q * r pow 2) + &3 * d * r pow 2 * s`,
           `b1:real`) THEN
  SPEC_TAC(`&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
            c * (p * s pow 2 + &2 * q * r * s) + &3 * d * r * s pow 2`,
           `c1:real`) THEN
  SPEC_TAC(`a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 + d * s pow 3`,
           `d1:real`) THEN
  SPEC_TAC(`A * p pow 2 + B * p * r + C * r pow 2`, `A1:real`) THEN
  SPEC_TAC(`&2 * A * p * q + B * (p * s + q * r) + &2 * C * r * s`,
           `B1:real`) THEN
  SPEC_TAC(`A * q pow 2 + B * q * s + C * s pow 2`, `C1:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`sqrt(abs D)`; `D:real`; `A1:real`; `B1:real`; `C1:real`;
                `a1:real`; `d1:real`; `a1 + b1 + c1 + d1:real`;
                `a1 - b1 + c1 - d1:real`] CUBIC_BOUNDS_ALGEBRA) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MATCH_MP_TAC SQRT_POS_LE THEN REWRITE_TAC[REAL_ABS_POS];
      MATCH_MP_TAC SQRT_POW_2 THEN REWRITE_TAC[REAL_ABS_POS];
      MP_TAC(SPEC `a1:real` REAL_ABS_INTEGER_LEMMA) THEN
      ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM(SPEC `2` REAL_POW_ONE)] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Main theorem: Phi = integer forms with coefficients bounded by 2 + 6 |D|. *)
(* F = F1 o gamma with F1 = F o (p q; r s) reduced and gamma the inverse     *)
(* matrix (s -q; -r p).                                                      *)
(* ------------------------------------------------------------------------- *)

let CUBIC_FORM_SUBST = prove
 (`!a b c d p q r s u v.
        a * (p * u + q * v) pow 3 +
        b * (p * u + q * v) pow 2 * (r * u + s * v) +
        c * (p * u + q * v) * (r * u + s * v) pow 2 +
        d * (r * u + s * v) pow 3 =
        (a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3) *
        u pow 3 +
        (&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
         c * (&2 * p * r * s + q * r pow 2) + &3 * d * r pow 2 * s) *
        u pow 2 * v +
        (&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
         c * (p * s pow 2 + &2 * q * r * s) + &3 * d * r * s pow 2) *
        u * v pow 2 +
        (a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 + d * s pow 3) *
        v pow 3`,
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

let CUBIC_FORM_REDUCTION = prove
 (`!D. ~(D = &0)
       ==> ?Phi. FINITE Phi /\
                 (!a1 b1 c1 d1. (a1,b1,c1,d1) IN Phi
                                ==> integer a1 /\ integer b1 /\
                                    integer c1 /\ integer d1) /\
                 !a b c d.
                   integer a /\ integer b /\ integer c /\ integer d /\
                   b pow 2 * c pow 2 - &4 * a * c pow 3 - &4 * b pow 3 * d -
                   &27 * a pow 2 * d pow 2 + &18 * a * b * c * d = D /\
                   (!u v. integer u /\ integer v /\
                          a * u pow 3 + b * u pow 2 * v + c * u * v pow 2 +
                          d * v pow 3 = &0
                          ==> u = &0 /\ v = &0)
                   ==> ?a1 b1 c1 d1 p q r s.
                         (a1,b1,c1,d1) IN Phi /\
                         integer p /\ integer q /\ integer r /\ integer s /\
                         p * s - q * r = &1 /\
                         !u v. a * u pow 3 + b * u pow 2 * v +
                               c * u * v pow 2 + d * v pow 3 =
                               a1 * (p * u + q * v) pow 3 +
                               b1 * (p * u + q * v) pow 2 * (r * u + s * v) +
                               c1 * (p * u + q * v) * (r * u + s * v) pow 2 +
                               d1 * (r * u + s * v) pow 3`,
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC
   `{x | integer x /\ abs x <= &2 + &6 * abs D} CROSS
    ({x | integer x /\ abs x <= &2 + &6 * abs D} CROSS
     ({x | integer x /\ abs x <= &2 + &6 * abs D} CROSS
      {x | integer x /\ abs x <= &2 + &6 * abs D}))` THEN
  REPEAT CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC FINITE_CROSS THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG];
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`; `d:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`D:real`; `a:real`; `b:real`; `c:real`; `d:real`]
    CUBIC_REDUCED_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real`
   (X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`;
                `p:real`; `q:real`; `r:real`; `s:real`]
    CUBIC_SUBST_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`a * p pow 3 + b * p pow 2 * r + c * p * r pow 2 + d * r pow 3`;
    `&3 * a * p pow 2 * q + b * (p pow 2 * s + &2 * p * q * r) +
     c * (&2 * p * r * s + q * r pow 2) + &3 * d * r pow 2 * s`;
    `&3 * a * p * q pow 2 + b * (&2 * p * q * s + q pow 2 * r) +
     c * (p * s pow 2 + &2 * q * r * s) + &3 * d * r * s pow 2`;
    `a * q pow 3 + b * q pow 2 * s + c * q * s pow 2 + d * s pow 3`;
    `s:real`; `--q:real`; `--r:real`; `p:real`] THEN
  ASM_REWRITE_TAC[IN_CROSS; IN_ELIM_THM; INTEGER_NEG] THEN CONJ_TAC THENL
   [UNDISCH_TAC `p * s - q * r = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real`; `v:real`] THEN
  SUBGOAL_THEN
   `p * (s * u + --q * v) + q * (--r * u + p * v) = u /\
    r * (s * u + --q * v) + s * (--r * u + p * v) = v`
  ASSUME_TAC THENL
   [UNDISCH_TAC `p * s - q * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`a:real`; `b:real`; `c:real`; `d:real`;
                `p:real`; `q:real`; `r:real`; `s:real`;
                `s * u + --q * v:real`; `--r * u + p * v:real`]
    CUBIC_FORM_SUBST) THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]));;
