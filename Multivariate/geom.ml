(* ========================================================================= *)
(* Some geometric notions in real^N.                                         *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* Pythagoras's theorem is almost immediate.                                 *)
(* ------------------------------------------------------------------------- *)

let PYTHAGORAS = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`,
  REWRITE_TAC[NORM_POW_2; orthogonal; DOT_LSUB; DOT_RSUB; DOT_SYM] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Angle between vectors (always 0 <= angle <= pi).                          *)
(* ------------------------------------------------------------------------- *)

let vector_angle = new_definition
 `vector_angle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`;;

let VECTOR_ANGLE_LINEAR_IMAGE_EQ = prove
 (`!f x y. linear f /\ (!x. norm(f x) = norm x)
           ==> (vector_angle (f x) (f y) = vector_angle x y)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[vector_angle; GSYM NORM_EQ_0] THEN
  ASM_MESON_TAC[PRESERVES_NORM_PRESERVES_DOT]);;

add_linear_invariants [VECTOR_ANGLE_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Basic properties of vector angles.                                        *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ANGLE_REFL = prove
 (`!x. vector_angle x x = if x = vec 0 then pi / &2 else &0`,
  GEN_TAC THEN REWRITE_TAC[vector_angle; DISJ_ACI] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POW_2; REAL_POW_2] THEN
  ASM_SIMP_TAC[REAL_DIV_REFL; REAL_ENTIRE; NORM_EQ_0; ACS_1]);;

let VECTOR_ANGLE_SYM = prove
 (`!x y. vector_angle x y = vector_angle y x`,
  REWRITE_TAC[vector_angle; DISJ_SYM; DOT_SYM; REAL_MUL_SYM]);;

let VECTOR_ANGLE_LMUL = prove
 (`!a x y:real^N.
        vector_angle (a % x) y =
                if a = &0 then pi / &2
                else if &0 <= a then vector_angle x y
                else pi - vector_angle x y`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[vector_angle; VECTOR_MUL_EQ_0] THEN
  ASM_CASES_TAC `x:real^N = vec 0 \/ y:real^N = vec 0` THEN
  ASM_REWRITE_TAC[] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; DOT_LMUL; real_div; REAL_INV_MUL; real_abs] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[REAL_INV_NEG; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(a = &0) ==> (a * x) * (inv a * y) * z = x * y * z`] THEN
  MATCH_MP_TAC ACS_NEG THEN
  REWRITE_TAC[GSYM REAL_ABS_BOUNDS; GSYM REAL_INV_MUL] THEN
  REWRITE_TAC[GSYM real_div; NORM_CAUCHY_SCHWARZ_DIV]);;

let VECTOR_ANGLE_RMUL = prove
 (`!a x y:real^N.
        vector_angle x (a % y) =
                if a = &0 then pi / &2
                else if &0 <= a then vector_angle x y
                else pi - vector_angle x y`,
  ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN
  REWRITE_TAC[VECTOR_ANGLE_LMUL]);;

let VECTOR_ANGLE_LNEG = prove
 (`!x y. vector_angle (--x) y = pi - vector_angle x y`,
  REWRITE_TAC[VECTOR_ARITH `--x = -- &1 % x`; VECTOR_ANGLE_LMUL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let VECTOR_ANGLE_RNEG = prove
 (`!x y. vector_angle x (--y) = pi - vector_angle x y`,
  ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN REWRITE_TAC[VECTOR_ANGLE_LNEG]);;

let VECTOR_ANGLE_NEG2 = prove
 (`!x y. vector_angle (--x) (--y) = vector_angle x y`,
  REWRITE_TAC[VECTOR_ANGLE_LNEG; VECTOR_ANGLE_RNEG] THEN REAL_ARITH_TAC);;

let SIN_VECTOR_ANGLE_LMUL = prove
 (`!a x y:real^N.
        sin(vector_angle (a % x) y) =
        if a = &0 then &1 else sin(vector_angle x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_ANGLE_LMUL] THEN
  ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[SIN_PI2] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI] THEN
  REAL_ARITH_TAC);;

let SIN_VECTOR_ANGLE_RMUL = prove
 (`!a x y:real^N.
        sin(vector_angle x (a % y)) =
        if a = &0 then &1 else sin(vector_angle x y)`,
  ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN
  REWRITE_TAC[SIN_VECTOR_ANGLE_LMUL]);;

let VECTOR_ANGLE = prove
 (`!x y:real^N. x dot y = norm(x) * norm(y) * cos(vector_angle x y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_angle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_LZERO; NORM_0; REAL_MUL_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN
  ASM_REWRITE_TAC[DOT_RZERO; NORM_0; REAL_MUL_LZERO; REAL_MUL_RZERO] THEN
  ONCE_REWRITE_TAC[AC REAL_MUL_AC `a * b * c:real = c * a * b`] THEN
  ASM_SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT] THEN
  MATCH_MP_TAC(GSYM COS_ACS) THEN
  ASM_REWRITE_TAC[REAL_BOUNDS_LE; NORM_CAUCHY_SCHWARZ_DIV]);;

let VECTOR_ANGLE_RANGE = prove
 (`!x y:real^N. &0 <= vector_angle x y /\ vector_angle x y <= pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[vector_angle] THEN COND_CASES_TAC THENL
   [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN MATCH_MP_TAC ACS_BOUNDS THEN
  ASM_REWRITE_TAC[REAL_BOUNDS_LE; NORM_CAUCHY_SCHWARZ_DIV]);;

let ORTHOGONAL_VECTOR_ANGLE = prove
 (`!x y:real^N. orthogonal x y <=> vector_angle x y = pi / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[orthogonal; vector_angle] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_LZERO] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
  EQ_TAC THENL
   [SIMP_TAC[real_div; REAL_MUL_LZERO] THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM real_div; GSYM COS_PI2] THEN
    MATCH_MP_TAC ACS_COS THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o AP_TERM `cos`) THEN
    SIMP_TAC[COS_ACS; REAL_BOUNDS_LE; NORM_CAUCHY_SCHWARZ_DIV; COS_PI2] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_LT_MUL; NORM_POS_LT; REAL_MUL_LZERO]]);;

let VECTOR_ANGLE_EQ_0 = prove
 (`!x y:real^N. vector_angle x y = &0 <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\ norm(x) % y = norm(y) % x`,
  REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC [`x:real^N = vec 0`; `y:real^N = vec 0`] THEN
  ASM_SIMP_TAC[vector_angle; PI_NZ; REAL_ARITH `x / &2 = &0 <=> x = &0`] THEN
  REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQ] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM REAL_MUL_LID] THEN
  ASM_SIMP_TAC[GSYM REAL_EQ_LDIV_EQ; NORM_POS_LT; REAL_LT_MUL] THEN
  MESON_TAC[ACS_1; COS_ACS; REAL_BOUNDS_LE; NORM_CAUCHY_SCHWARZ_DIV; COS_0]);;

let VECTOR_ANGLE_EQ_PI = prove
 (`!x y:real^N. vector_angle x y = pi <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\
                norm(x) % y + norm(y) % x = vec 0`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `--y:real^N`] VECTOR_ANGLE_EQ_0) THEN
  SIMP_TAC[VECTOR_ANGLE_RNEG; REAL_ARITH `pi - x = &0 <=> x = pi`] THEN
  STRIP_TAC THEN
  REWRITE_TAC[NORM_NEG; VECTOR_ARITH `--x = vec 0 <=> x = vec 0`] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN VECTOR_ARITH_TAC);;

let VECTOR_ANGLE_EQ_0_DIST = prove
 (`!x y:real^N. vector_angle x y = &0 <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\ norm(x + y) = norm x + norm y`,
  REWRITE_TAC[VECTOR_ANGLE_EQ_0; GSYM NORM_TRIANGLE_EQ]);;

let VECTOR_ANGLE_EQ_PI_DIST = prove
 (`!x y:real^N. vector_angle x y = pi <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\ norm(x - y) = norm x + norm y`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `--y:real^N`] VECTOR_ANGLE_EQ_0_DIST) THEN
  SIMP_TAC[VECTOR_ANGLE_RNEG; REAL_ARITH `pi - x = &0 <=> x = pi`] THEN
  STRIP_TAC THEN REWRITE_TAC[NORM_NEG] THEN NORM_ARITH_TAC);;

let SIN_VECTOR_ANGLE_POS = prove
 (`!v w. &0 <= sin(vector_angle v w)`,
  SIMP_TAC[SIN_POS_PI_LE; VECTOR_ANGLE_RANGE]);;

let SIN_VECTOR_ANGLE_EQ_0 = prove
 (`!x y. sin(vector_angle x y) = &0 <=>
           vector_angle x y = &0 \/ vector_angle x y = pi`,
  MESON_TAC[SIN_POS_PI; VECTOR_ANGLE_RANGE; REAL_LT_LE; SIN_0; SIN_PI]);;

let ASN_SIN_VECTOR_ANGLE = prove
 (`!x y:real^N.
        asn(sin(vector_angle x y)) =
          if vector_angle x y <= pi / &2 then vector_angle x y
          else pi - vector_angle x y`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `asn(sin(pi - vector_angle (x:real^N) y))` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI] THEN
      REAL_ARITH_TAC;
      ALL_TAC]] THEN
  MATCH_MP_TAC ASN_SIN THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`] VECTOR_ANGLE_RANGE) THEN
  ASM_REAL_ARITH_TAC);;

let SIN_VECTOR_ANGLE_EQ = prove
 (`!x y w z.
        sin(vector_angle x y) = sin(vector_angle w z) <=>
            vector_angle x y = vector_angle w z \/
            vector_angle x y = pi - vector_angle w z`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI] THENL
   [ALL_TAC; REAL_ARITH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `asn`) THEN
  REWRITE_TAC[ASN_SIN_VECTOR_ANGLE] THEN REAL_ARITH_TAC);;

let CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE = prove
 (`!f:real^M->real^N g x s.
     ~(f x = vec 0) /\ ~(g x = vec 0) /\
     f continuous (at x within s) /\
     g continuous (at x within s)
     ==> (\x. Cx(vector_angle (f x) (g x))) continuous (at x within s)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `trivial_limit(at (x:real^M) within s)` THEN
  ASM_SIMP_TAC[CONTINUOUS_TRIVIAL_LIMIT; vector_angle] THEN
  SUBGOAL_THEN
   `(cacs o (\x. Cx(((f x:real^N) dot g x) / (norm(f x) * norm(g x)))))
    continuous (at (x:real^M) within s)`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN CONJ_TAC THENL
     [REWRITE_TAC[CX_DIV; CX_MUL] THEN REWRITE_TAC[WITHIN_UNIV] THEN
      MATCH_MP_TAC CONTINUOUS_COMPLEX_DIV THEN
      ASM_SIMP_TAC[NETLIMIT_WITHIN; COMPLEX_ENTIRE; CX_INJ; NORM_EQ_0] THEN
      REWRITE_TAC[CONTINUOUS_CX_LIFT; GSYM CX_MUL; LIFT_CMUL] THEN
      ASM_SIMP_TAC[CONTINUOUS_LIFT_DOT2] THEN
      MATCH_MP_TAC CONTINUOUS_MUL THEN
      ASM_SIMP_TAC[CONTINUOUS_LIFT_NORM_COMPOSE; o_DEF];
      MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
      EXISTS_TAC `{z | real z /\ abs(Re z) <= &1}` THEN
      REWRITE_TAC[CONTINUOUS_WITHIN_CACS_REAL] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
      REWRITE_TAC[REAL_CX; RE_CX; NORM_CAUCHY_SCHWARZ_DIV]];
    ASM_SIMP_TAC[CONTINUOUS_WITHIN; CX_ACS; o_DEF;
                 NORM_CAUCHY_SCHWARZ_DIV] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM_EVENTUALLY) THEN
    SUBGOAL_THEN
      `eventually (\y. ~((f:real^M->real^N) y = vec 0) /\
                       ~((g:real^M->real^N) y = vec 0))
                  (at x within s)`
    MP_TAC THENL
     [REWRITE_TAC[EVENTUALLY_AND] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(f:real^M->real^N) continuous (at x within s)`;
        UNDISCH_TAC `(g:real^M->real^N) continuous (at x within s)`] THEN
      REWRITE_TAC[CONTINUOUS_WITHIN; tendsto] THENL
       [DISCH_THEN(MP_TAC o SPEC `norm((f:real^M->real^N) x)`);
        DISCH_THEN(MP_TAC o SPEC `norm((g:real^M->real^N) x)`)] THEN
      ASM_REWRITE_TAC[NORM_POS_LT] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      REWRITE_TAC[] THEN CONV_TAC NORM_ARITH;
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      SIMP_TAC[CX_ACS; NORM_CAUCHY_SCHWARZ_DIV]]]);;

let CONTINUOUS_AT_CX_VECTOR_ANGLE = prove
 (`!c x:real^N. ~(x = vec 0) ==> (Cx o vector_angle c) continuous (at x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[o_DEF; vector_angle] THEN
  ASM_CASES_TAC `c:real^N = vec 0` THEN ASM_REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. cacs(Cx((c dot x) / (norm c * norm x)))`;
                        `norm(x:real^N)`] THEN
  ASM_REWRITE_TAC[NORM_POS_LT] THEN CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[NORM_ARITH `~(dist(vec 0,x) < norm x)`]; ALL_TAC] THEN
    MATCH_MP_TAC(GSYM CX_ACS) THEN REWRITE_TAC[NORM_CAUCHY_SCHWARZ_DIV];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_WITHIN_COMPOSE) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[CX_DIV; CX_MUL] THEN REWRITE_TAC[WITHIN_UNIV] THEN
    MATCH_MP_TAC CONTINUOUS_COMPLEX_DIV THEN
    ASM_REWRITE_TAC[NETLIMIT_AT; COMPLEX_ENTIRE; CX_INJ; NORM_EQ_0] THEN
    SIMP_TAC[CONTINUOUS_COMPLEX_MUL; CONTINUOUS_CONST;
             CONTINUOUS_AT_CX_NORM; CONTINUOUS_AT_CX_DOT];
    MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
    EXISTS_TAC `{z | real z /\ abs(Re z) <= &1}` THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_CACS_REAL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_CX; RE_CX; NORM_CAUCHY_SCHWARZ_DIV]]);;

let CONTINUOUS_WITHIN_CX_VECTOR_ANGLE = prove
 (`!c x:real^N s.
     ~(x = vec 0) ==> (Cx o vector_angle c) continuous (at x within s)`,
  SIMP_TAC[CONTINUOUS_AT_WITHIN; CONTINUOUS_AT_CX_VECTOR_ANGLE]);;

let REAL_CONTINUOUS_AT_VECTOR_ANGLE = prove
 (`!c x:real^N. ~(x = vec 0) ==> (vector_angle c) real_continuous (at x)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS; CONTINUOUS_AT_CX_VECTOR_ANGLE]);;

let REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE = prove
 (`!c s x:real^N. ~(x = vec 0)
                  ==> (vector_angle c) real_continuous (at x within s)`,
  REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS; CONTINUOUS_WITHIN_CX_VECTOR_ANGLE]);;

let CONTINUOUS_ON_CX_VECTOR_ANGLE = prove
 (`!s. ~(vec 0 IN s) ==> (Cx o vector_angle c) continuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  ASM_MESON_TAC[CONTINUOUS_WITHIN_CX_VECTOR_ANGLE]);;

let VECTOR_ANGLE_EQ = prove
 (`!u v x y. ~(u = vec 0) /\  ~(v = vec 0) /\ ~(x = vec 0) /\ ~(y = vec 0)
             ==> (vector_angle u v = vector_angle x y <=>
                        (x dot y) * norm(u) * norm(v) =
                        (u dot v) * norm(x) * norm(y))`,
  SIMP_TAC[vector_angle; NORM_EQ_0; REAL_FIELD
   `~(u = &0) /\ ~(v = &0) /\ ~(x = &0) /\ ~(y = &0)
    ==> (a * u * v = b * x * y <=> a / (x * y) = b / (u * v))`] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN
  DISCH_THEN(MP_TAC o AP_TERM `cos`) THEN
  SIMP_TAC[COS_ACS; NORM_CAUCHY_SCHWARZ_DIV; REAL_BOUNDS_LE]);;

let COS_VECTOR_ANGLE_EQ = prove
 (`!u v x y.
        cos(vector_angle u v) = cos(vector_angle x y) <=>
        vector_angle u v = vector_angle x y`,
  MESON_TAC[ACS_COS; VECTOR_ANGLE_RANGE]);;

let COLLINEAR_VECTOR_ANGLE = prove
 (`!x y. ~(x = vec 0) /\ ~(y = vec 0)
         ==> (collinear {vec 0,x,y} <=>
                vector_angle x y = &0 \/ vector_angle x y = pi)`,
  REWRITE_TAC[GSYM NORM_CAUCHY_SCHWARZ_EQUAL; NORM_CAUCHY_SCHWARZ_ABS_EQ;
              VECTOR_ANGLE_EQ_0; VECTOR_ANGLE_EQ_PI] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN BINOP_TAC THEN
  VECTOR_ARITH_TAC);;

let COLLINEAR_SIN_VECTOR_ANGLE = prove
 (`!x y. ~(x = vec 0) /\ ~(y = vec 0)
         ==> (collinear {vec 0,x,y} <=> sin(vector_angle x y) = &0)`,
  REWRITE_TAC[SIN_VECTOR_ANGLE_EQ_0; COLLINEAR_VECTOR_ANGLE]);;

let COLLINEAR_SIN_VECTOR_ANGLE_IMP = prove
 (`!x y. sin(vector_angle x y) = &0
         ==> ~(x = vec 0) /\ ~(y = vec 0) /\ collinear {vec 0,x,y}`,
  MESON_TAC[COLLINEAR_SIN_VECTOR_ANGLE; SIN_VECTOR_ANGLE_EQ_0;
            VECTOR_ANGLE_EQ_0_DIST; VECTOR_ANGLE_EQ_PI_DIST]);;

let VECTOR_ANGLE_EQ_0_RIGHT = prove
 (`!x y z:real^N. vector_angle x y = &0
                  ==> (vector_angle x z = vector_angle y z)`,
  REWRITE_TAC[VECTOR_ANGLE_EQ_0] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vector_angle (norm(x:real^N) % y) (z:real^N)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[VECTOR_ANGLE_LMUL; NORM_EQ_0; NORM_POS_LE];
    REWRITE_TAC[VECTOR_ANGLE_LMUL] THEN
    ASM_REWRITE_TAC[NORM_EQ_0; NORM_POS_LE]]);;

let VECTOR_ANGLE_EQ_0_LEFT = prove
 (`!x y z:real^N. vector_angle x y = &0
                  ==> (vector_angle z x = vector_angle z y)`,
  MESON_TAC[VECTOR_ANGLE_EQ_0_RIGHT; VECTOR_ANGLE_SYM]);;

let VECTOR_ANGLE_EQ_PI_RIGHT = prove
 (`!x y z:real^N. vector_angle x y = pi
                  ==> (vector_angle x z = pi - vector_angle y z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--x:real^N`; `y:real^N`; `z:real^N`]
   VECTOR_ANGLE_EQ_0_RIGHT) THEN
  ASM_REWRITE_TAC[VECTOR_ANGLE_LNEG] THEN REAL_ARITH_TAC);;

let VECTOR_ANGLE_EQ_PI_LEFT = prove
 (`!x y z:real^N. vector_angle x y = pi
                  ==> (vector_angle z x = pi - vector_angle z y)`,
  MESON_TAC[VECTOR_ANGLE_EQ_PI_RIGHT; VECTOR_ANGLE_SYM]);;

let COS_VECTOR_ANGLE = prove
 (`!x y:real^N.
        cos(vector_angle x y) = if x = vec 0 \/ y = vec 0 then &0
                                else (x dot y) / (norm x * norm y)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[vector_angle; COS_PI2]; ALL_TAC] THEN
  ASM_CASES_TAC `y:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[vector_angle; COS_PI2]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; REAL_LT_MUL; NORM_POS_LT; VECTOR_ANGLE] THEN
  REAL_ARITH_TAC);;

let SIN_VECTOR_ANGLE = prove
 (`!x y:real^N.
        sin(vector_angle x y) =
            if x = vec 0 \/ y = vec 0 then &1
            else sqrt(&1 - ((x dot y) / (norm x * norm y)) pow 2)`,
  SIMP_TAC[SIN_COS_SQRT; SIN_VECTOR_ANGLE_POS; COS_VECTOR_ANGLE] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[SQRT_1]);;

let SIN_SQUARED_VECTOR_ANGLE = prove
 (`!x y:real^N.
        sin(vector_angle x y) pow 2 =
            if x = vec 0 \/ y = vec 0 then &1
            else &1 - ((x dot y) / (norm x * norm y)) pow 2`,
  REPEAT GEN_TAC THEN REWRITE_TAC
   [REWRITE_RULE [REAL_ARITH `s + c = &1 <=> s = &1 - c`] SIN_CIRCLE] THEN
  REWRITE_TAC[COS_VECTOR_ANGLE] THEN REAL_ARITH_TAC);;

let VECTOR_ANGLE_COMPLEX_LMUL = prove
 (`!a. ~(a = Cx(&0))
       ==> vector_angle (a * x) (a * y) = vector_angle x y`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `x = Cx(&0)` THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; vector_angle; COMPLEX_VEC_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `y = Cx(&0)` THENL
   [ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; vector_angle; COMPLEX_VEC_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`a * x:complex`; `a * y:complex`; `x:complex`; `y:complex`]
        VECTOR_ANGLE_EQ) THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC(REAL_RING
   `a pow 2 * xy:real = d ==> xy * (a * x) * (a * y) = d * x * y`) THEN
  REWRITE_TAC[NORM_POW_2] THEN
  REWRITE_TAC[DOT_2; complex_mul; GSYM RE_DEF; GSYM IM_DEF; RE; IM] THEN
  REAL_ARITH_TAC);;

let VECTOR_ANGLE_1 = prove
 (`!x. vector_angle x (Cx(&1)) = acs(Re x / norm x)`,
  GEN_TAC THEN
  SIMP_TAC[vector_angle; COMPLEX_VEC_0; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  COND_CASES_TAC THENL
   [ASM_REWRITE_TAC[real_div; RE_CX; ACS_0; REAL_MUL_LZERO]; ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_MUL_RID] THEN
  REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF; RE_CX; IM_CX] THEN
  AP_TERM_TAC THEN REAL_ARITH_TAC);;

let ARG_EQ_VECTOR_ANGLE_1 = prove
 (`!z. ~(z = Cx(&0)) /\ &0 <= Im z ==> Arg z = vector_angle z (Cx(&1))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_ANGLE_1] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV) [ARG] THEN
  REWRITE_TAC[RE_MUL_CX; RE_CEXP; RE_II; IM_MUL_II; IM_CX; RE_CX] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_EXP_0; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[COMPLEX_NORM_ZERO; REAL_FIELD
   `~(z = &0) ==> (z * x) / z = x`] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ACS_COS THEN
  ASM_REWRITE_TAC[ARG; ARG_LE_PI]);;

let VECTOR_ANGLE_ARG = prove
 (`!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> vector_angle w z = if &0 <= Im(z / w) then Arg(z / w)
                                else &2 * pi - Arg(z / w)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `z = w * (z / w) /\ w = w * Cx(&1)` MP_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD; ALL_TAC];
    SUBGOAL_THEN `w = z * (w / z) /\ z = z * Cx(&1)` MP_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD; ALL_TAC]] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
  ASM_SIMP_TAC[VECTOR_ANGLE_COMPLEX_LMUL] THENL
   [ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC ARG_EQ_VECTOR_ANGLE_1 THEN ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD;
    MP_TAC(ISPEC `z / w:complex` ARG_INV) THEN ANTS_TAC THENL
     [ASM_MESON_TAC[real; REAL_LE_REFL]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    REWRITE_TAC[COMPLEX_INV_DIV] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC ARG_EQ_VECTOR_ANGLE_1 THEN CONJ_TAC THENL
     [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD;
      ONCE_REWRITE_TAC[GSYM COMPLEX_INV_DIV] THEN
      REWRITE_TAC[IM_COMPLEX_INV_GE_0] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Traditional geometric notion of angle (always 0 <= theta <= pi).          *)
(* ------------------------------------------------------------------------- *)

let angle = new_definition
 `angle(a,b,c) = vector_angle (a - b) (c - b)`;;

let ANGLE_LINEAR_IMAGE_EQ = prove
 (`!f a b c.
        linear f /\ (!x. norm(f x) = norm x)
        ==> angle(f a,f b,f c) = angle(a,b,c)`,
  SIMP_TAC[angle; GSYM LINEAR_SUB; VECTOR_ANGLE_LINEAR_IMAGE_EQ]);;

add_linear_invariants [ANGLE_LINEAR_IMAGE_EQ];;

let ANGLE_TRANSLATION_EQ = prove
 (`!a b c d. angle(a + b,a + c,a + d) = angle(b,c,d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[angle] THEN
  BINOP_TAC THEN VECTOR_ARITH_TAC);;

add_translation_invariants [ANGLE_TRANSLATION_EQ];;

let VECTOR_ANGLE_ANGLE = prove
 (`vector_angle x y = angle(x,vec 0,y)`,
  REWRITE_TAC[angle; VECTOR_SUB_RZERO]);;

let ANGLE_EQ_PI_DIST = prove
 (`!A B C:real^N.
        angle(A,B,C) = pi <=>
        ~(A = B) /\ ~(C = B) /\ dist(A,C) = dist(A,B) + dist(B,C)`,
  REWRITE_TAC[angle; VECTOR_ANGLE_EQ_PI_DIST] THEN NORM_ARITH_TAC);;

let SIN_ANGLE_POS = prove
 (`!A B C. &0 <= sin(angle(A,B,C))`,
  REWRITE_TAC[angle; SIN_VECTOR_ANGLE_POS]);;

let ANGLE = prove
 (`!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`,
  REWRITE_TAC[angle; dist; GSYM VECTOR_ANGLE]);;

let ANGLE_REFL = prove
 (`!A B. angle(A,A,B) = pi / &2 /\ angle(B,A,A) = pi / &2`,
  REWRITE_TAC[angle; vector_angle; VECTOR_SUB_REFL]);;

let ANGLE_REFL_MID = prove
 (`!A B. ~(A = B) ==> angle(A,B,A) = &0`,
  SIMP_TAC[angle; vector_angle; VECTOR_SUB_EQ; GSYM NORM_POW_2; ARITH;
    GSYM REAL_POW_2; REAL_DIV_REFL; ACS_1; REAL_POW_EQ_0; NORM_EQ_0]);;

let ANGLE_SYM = prove
 (`!A B C. angle(A,B,C) = angle(C,B,A)`,
  REWRITE_TAC[angle; vector_angle; VECTOR_SUB_EQ; DISJ_SYM;
              REAL_MUL_SYM; DOT_SYM]);;

let ANGLE_RANGE = prove
 (`!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`,
  REWRITE_TAC[angle; VECTOR_ANGLE_RANGE]);;

let COS_ANGLE_EQ = prove
 (`!a b c a' b' c'.
        cos(angle(a,b,c)) = cos(angle(a',b',c')) <=>
        angle(a,b,c) = angle(a',b',c')`,
  REWRITE_TAC[angle; COS_VECTOR_ANGLE_EQ]);;

let ANGLE_EQ = prove
 (`!a b c a' b' c'.
        ~(a = b) /\ ~(c = b) /\ ~(a' = b') /\ ~(c' = b')
        ==> (angle(a,b,c) = angle(a',b',c') <=>
                ((a' - b') dot (c' - b')) * norm (a - b) * norm (c - b) =
                ((a - b) dot (c - b)) * norm (a' - b') * norm (c' - b'))`,
  SIMP_TAC[angle; VECTOR_ANGLE_EQ; VECTOR_SUB_EQ]);;

let SIN_ANGLE_EQ_0 = prove
 (`!A B C. sin(angle(A,B,C)) = &0 <=> angle(A,B,C) = &0 \/ angle(A,B,C) = pi`,
  REWRITE_TAC[angle; SIN_VECTOR_ANGLE_EQ_0]);;

let SIN_ANGLE_EQ = prove
 (`!A B C A' B' C'. sin(angle(A,B,C)) = sin(angle(A',B',C')) <=>
                        angle(A,B,C) = angle(A',B',C') \/
                        angle(A,B,C) = pi - angle(A',B',C')`,
  REWRITE_TAC[angle; SIN_VECTOR_ANGLE_EQ]);;

let COLLINEAR_ANGLE = prove
 (`!A B C. ~(A = B) /\ ~(B = C)
           ==> (collinear {A,B,C} <=> angle(A,B,C) = &0 \/ angle(A,B,C) = pi)`,
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  SIMP_TAC[COLLINEAR_VECTOR_ANGLE; VECTOR_SUB_EQ; angle]);;

let COLLINEAR_SIN_ANGLE = prove
 (`!A B C. ~(A = B) /\ ~(B = C)
           ==> (collinear {A,B,C} <=> sin(angle(A,B,C)) = &0)`,
  REWRITE_TAC[SIN_ANGLE_EQ_0; COLLINEAR_ANGLE]);;

let COLLINEAR_SIN_ANGLE_IMP = prove
 (`!A B C. sin(angle(A,B,C)) = &0
           ==> ~(A = B) /\ ~(B = C) /\ collinear {A,B,C}`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN REWRITE_TAC[angle] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COLLINEAR_SIN_VECTOR_ANGLE_IMP) THEN
  SIMP_TAC[VECTOR_SUB_EQ]);;

let ANGLE_EQ_0_RIGHT = prove
 (`!A B C. angle(A,B,C) = &0 ==> angle(A,B,D) = angle(C,B,D)`,
  REWRITE_TAC[VECTOR_ANGLE_EQ_0_RIGHT; angle]);;

let ANGLE_EQ_0_LEFT = prove
 (`!A B C. angle(A,B,C) = &0 ==> angle(D,B,A) = angle(D,B,C)`,
  MESON_TAC[ANGLE_EQ_0_RIGHT; ANGLE_SYM]);;

let ANGLE_EQ_PI_RIGHT = prove
 (`!A B C. angle(A,B,C) = pi ==> angle(A,B,D) = pi - angle(C,B,D)`,
  REWRITE_TAC[VECTOR_ANGLE_EQ_PI_RIGHT; angle]);;

let ANGLE_EQ_PI_LEFT = prove
 (`!A B C. angle(A,B,C) = pi ==> angle(A,B,D) = pi - angle(C,B,D)`,
  MESON_TAC[ANGLE_EQ_PI_RIGHT; ANGLE_SYM]);;

let COS_ANGLE = prove
 (`!a b c. cos(angle(a,b,c)) = if a = b \/ c = b then &0
                               else ((a - b) dot (c - b)) /
                                    (norm(a - b) * norm(c - b))`,
  REWRITE_TAC[angle; COS_VECTOR_ANGLE; VECTOR_SUB_EQ]);;

let SIN_ANGLE = prove
 (`!a b c. sin(angle(a,b,c)) =
             if a = b \/ c = b then &1
             else sqrt(&1 - (((a - b) dot (c - b)) /
                             (norm(a - b) * norm(c - b))) pow 2)`,
  REWRITE_TAC[angle; SIN_VECTOR_ANGLE; VECTOR_SUB_EQ]);;

let SIN_SQUARED_ANGLE = prove
 (`!a b c. sin(angle(a,b,c)) pow 2 =
             if a = b \/ c = b then &1
             else &1 - (((a - b) dot (c - b)) /
                        (norm(a - b) * norm(c - b))) pow 2`,
  REWRITE_TAC[angle; SIN_SQUARED_VECTOR_ANGLE; VECTOR_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* The basic right angle triangles of elementary trigonometry.               *)
(* ------------------------------------------------------------------------- *)

let COS_ADJACENT_HYPOTENUSE = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> dist(A,C) * cos(angle(B,A,C)) = dist(A,B)`,
  GEOM_ORIGIN_TAC `A:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[DIST_0; angle; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[ORTHOGONAL_LNEG; VECTOR_SUB_LZERO] THEN DISCH_TAC THEN
  ASM_CASES_TAC `B:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[vector_angle; COS_PI2; NORM_0; REAL_MUL_RZERO];
    MATCH_MP_TAC(REAL_RING `~(b = &0) /\ b * x = b pow 2 ==> x = b`) THEN
    ASM_REWRITE_TAC[NORM_EQ_0; GSYM VECTOR_ANGLE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [orthogonal]) THEN
    REWRITE_TAC[DOT_RSUB; NORM_POW_2] THEN REAL_ARITH_TAC]);;

let COS_ADJACENT_OVER_HYPOTENUSE = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> cos(angle(B,A,C)) = dist(A,B) / dist(A,C)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^N = C` THENL
   [ASM_REWRITE_TAC[DIST_REFL; real_div; REAL_INV_0; angle; VECTOR_SUB_REFL;
                    vector_angle] THEN
    REWRITE_TAC[GSYM real_div; COS_PI2; REAL_MUL_RZERO];
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; DIST_POS_LT] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[COS_ADJACENT_HYPOTENUSE]]);;

let SIN_OPPOSITE_HYPOTENUSE = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> dist(A,C) * sin(angle(B,A,C)) = dist(C,B)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^N = C` THEN
  ASM_SIMP_TAC[ORTHOGONAL_REFL; VECTOR_SUB_EQ; DIST_REFL; REAL_MUL_LZERO] THEN
  DISCH_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[dist; NORM_EQ_SQUARE] THEN
  SIMP_TAC[REAL_LE_MUL; SIN_ANGLE_POS; NORM_POS_LE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COS_ADJACENT_HYPOTENUSE) THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_RING
   `x:real = y ==> x pow 2 = y pow 2`)) THEN
  REWRITE_TAC[REAL_POW_MUL; GSYM NORM_POW_2; GSYM dist] THEN
  MATCH_MP_TAC(REAL_RING
   `d + e = h /\ s + c = &1 /\ ~(h = &0) ==> h * c = d ==> e = h * s`) THEN
  ASM_REWRITE_TAC[SIN_CIRCLE; REAL_POW_EQ_0; DIST_EQ_0] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PYTHAGORAS) THEN
  REWRITE_TAC[GSYM dist; DIST_SYM] THEN REAL_ARITH_TAC);;

let SIN_OPPOSITE_OVER_HYPOTENUSE = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B) /\ ~(A = C)
        ==> sin(angle(B,A,C)) = dist(C,B) / dist(A,C)`,
  SIMP_TAC[REAL_EQ_RDIV_EQ; DIST_POS_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  SIMP_TAC[SIN_OPPOSITE_HYPOTENUSE]);;

let TAN_OPPOSITE_ADJACENT = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B) /\ ~(A = B)
        ==> dist(A,B) * tan(angle(B,A,C)) = dist(C,B)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[tan] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP COS_ADJACENT_HYPOTENUSE) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIN_OPPOSITE_HYPOTENUSE) THEN
  ASM_CASES_TAC `cos (angle (B:real^N,A,C)) = &0` THENL
   [ALL_TAC; POP_ASSUM MP_TAC THEN CONV_TAC REAL_FIELD] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; real_div; REAL_MUL_RZERO; REAL_INV_0] THEN
  ASM_MESON_TAC[DIST_EQ_0]);;

let TAN_OPPOSITE_OVER_ADJACENT = prove
 (`!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> tan(angle(B,A,C)) = dist(C,B) / dist(A,B)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `A:real^N = B` THENL
   [ASM_REWRITE_TAC[angle; VECTOR_SUB_REFL; vector_angle] THEN
    REWRITE_TAC[tan; COS_PI2; DIST_REFL; real_div; REAL_INV_0; REAL_MUL_RZERO];
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; DIST_POS_LT] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[TAN_OPPOSITE_ADJACENT]]);;

(* ------------------------------------------------------------------------- *)
(* The law of cosines.                                                       *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_COSINES = prove
 (`!A B C:real^N.
        dist(B,C) pow 2 = (dist(A,B) pow 2 + dist(A,C) pow 2) -
                          &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[angle; ONCE_REWRITE_RULE[NORM_SUB] dist; GSYM VECTOR_ANGLE;
              NORM_POW_2] THEN
  VECTOR_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The law of sines.                                                         *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_SINES = prove
 (`!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  SIMP_TAC[SIN_ANGLE_POS; DIST_POS_LE; REAL_LE_MUL; ARITH] THEN
  REWRITE_TAC[REAL_POW_MUL; MATCH_MP
   (REAL_ARITH `x + y = &1 ==> x = &1 - y`) (SPEC_ALL SIN_CIRCLE)] THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[ANGLE_REFL; COS_PI2] THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[GSYM VECTOR_SUB_EQ]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM NORM_EQ_0]) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_RING
   `~(a = &0) ==> a pow 2 * x = a pow 2 * y ==> x = y`)) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM dist] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN
  REWRITE_TAC[REAL_RING
   `a * (&1 - x) * b = c * (&1 - y) * d <=>
    a * b - a * b * x = c * d - c * d * y`] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; GSYM ANGLE] THEN
  REWRITE_TAC[REAL_POW_MUL; dist; NORM_POW_2] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* The sum of the angles of a triangle.                                      *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_ANGLE_SUM_LEMMA = prove
 (`!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`C:real^N`; `B:real^N`; `A:real^N`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `A:real^N`] LAW_OF_SINES) THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; dist; NORM_SUB] THEN
  MAP_EVERY (fun t -> MP_TAC(SPEC t SIN_CIRCLE))
   [`angle(B:real^N,A,C)`; `angle(A:real^N,B,C)`; `angle(B:real^N,C,A)`] THEN
  REWRITE_TAC[COS_ADD; SIN_ADD; ANGLE_SYM] THEN CONV_TAC REAL_RING);;

let COS_MINUS1_LEMMA = prove
 (`!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. integer n /\ x = n * pi`
   (X_CHOOSE_THEN `nn:real` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[GSYM SIN_EQ_0] THENL
   [MP_TAC(SPEC `x:real` SIN_CIRCLE) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. nn = &n` (X_CHOOSE_THEN `n:num` SUBST_ALL_TAC) THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_MUL_POS_LE]) THEN
    SIMP_TAC[PI_POS; REAL_ARITH `&0 < p ==> ~(p < &0) /\ ~(p = &0)`] THEN
    ASM_MESON_TAC[INTEGER_POS; REAL_LT_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_RING `n = &1 ==> n * p = p`) THEN
  REWRITE_TAC[REAL_OF_NUM_EQ] THEN
  MATCH_MP_TAC(ARITH_RULE `n < 3 /\ ~(n = 0) /\ ~(n = 2) ==> n = 1`) THEN
  RULE_ASSUM_TAC(SIMP_RULE[REAL_LT_RMUL_EQ; PI_POS; REAL_OF_NUM_LT]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN SIMP_TAC[COS_0; REAL_MUL_LZERO; COS_NPI] THEN
  REAL_ARITH_TAC);;

let TRIANGLE_ANGLE_SUM = prove
 (`!A B C:real^N. ~(A = B /\ B = C /\ A = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`A:real^N = B`; `B:real^N = C`; `A:real^N = C`] THEN
  ASM_SIMP_TAC[ANGLE_REFL_MID; ANGLE_REFL; REAL_HALF; REAL_ADD_RID] THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[REAL_ADD_LID; REAL_HALF] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_MINUS1_LEMMA THEN
  ASM_SIMP_TAC[TRIANGLE_ANGLE_SUM_LEMMA; REAL_LE_ADD; ANGLE_RANGE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x <= p /\ &0 <= y /\ y <= p /\ &0 <= z /\ z <= p /\
    ~(x = p /\ y = p /\ z = p)
    ==> x + y + z < &3 * p`) THEN
  ASM_SIMP_TAC[ANGLE_RANGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ANGLE_EQ_PI_DIST])) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [GSYM VECTOR_SUB_EQ])) THEN
  REWRITE_TAC[GSYM NORM_EQ_0; dist; NORM_SUB] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A few more lemmas about angles.                                           *)
(* ------------------------------------------------------------------------- *)

let ANGLE_EQ_PI_OTHERS = prove
 (`!A B C:real^N.
        angle(A,B,C) = pi
        ==> angle(B,C,A) = &0 /\ angle(A,C,B) = &0 /\
            angle(B,A,C) = &0 /\ angle(C,A,B) = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [ANGLE_EQ_PI_DIST]) THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] TRIANGLE_ANGLE_SUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `x + p + y = p ==> &0 <= x /\ &0 <= y ==> x = &0 /\ y = &0`)) THEN
  SIMP_TAC[ANGLE_RANGE; ANGLE_SYM]);;

let ANGLE_EQ_0_DIST = prove
 (`!A B C:real^N. angle(A,B,C) = &0 <=>
                  ~(A = B) /\ ~(C = B) /\
                  (dist(A,B) = dist(A,C) + dist(C,B) \/
                   dist(B,C) = dist(A,C) + dist(A,B))`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `A:real^N = B` THENL
   [ASM_REWRITE_TAC[angle; VECTOR_ANGLE_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `B:real^N = C` THENL
   [ASM_REWRITE_TAC[angle; VECTOR_ANGLE_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ASM_CASES_TAC `A:real^N = C` THENL
   [ASM_SIMP_TAC[ANGLE_REFL_MID; DIST_REFL; REAL_ADD_LID]; ALL_TAC] THEN
  EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THENL
     [MP_TAC(ISPECL[`A:real^N`; `C:real^N`; `B:real^N`] ANGLE_EQ_PI_DIST);
      MP_TAC(ISPECL[`B:real^N`; `A:real^N`; `C:real^N`] ANGLE_EQ_PI_DIST)] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[DIST_SYM; REAL_ADD_AC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ANGLE_EQ_PI_OTHERS) THEN SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[angle; VECTOR_ANGLE_EQ_0; VECTOR_SUB_EQ] THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
    (ISPECL [`norm(A - B:real^N)`; `norm(C - B:real^N)`]
                REAL_LT_TOTAL)
  THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; NORM_EQ_0; VECTOR_SUB_EQ;
                    VECTOR_ARITH `c - b:real^N = a - b <=> a = c`];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `norm(A - B) % (C - B) = norm(C - B) % (A - B) <=>
      (norm(C - B) - norm(A - B)) % (A - B) = norm(A - B) % (C - A)`];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `norm(A - B) % (C - B) = norm(C - B) % (A - B) <=>
      (norm(A - B) - norm(C - B)) % (C - B) = norm(C - B) % (A - C)`]] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] NORM_CROSS_MULTIPLY)) THEN
  ASM_SIMP_TAC[REAL_SUB_LT; NORM_POS_LT; VECTOR_SUB_EQ] THEN
  SIMP_TAC[GSYM DIST_TRIANGLE_EQ] THEN SIMP_TAC[DIST_SYM]);;

let ANGLE_EQ_0_DIST_ABS = prove
 (`!A B C:real^N. angle(A,B,C) = &0 <=>
                  ~(A = B) /\ ~(C = B) /\
                   dist(A,C) = abs(dist(A,B) - dist(C,B))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ANGLE_EQ_0_DIST] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`A:real^N`; `C:real^N`] DIST_POS_LE) THEN
  REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some rules for congruent triangles (not necessarily in the same real^N).  *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_TRIANGLES_SSS = prove
 (`!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        dist(B,C) = dist(B',C') /\
        dist(C,A) = dist(C',A')
        ==> angle(A,B,C) = angle(A',B',C')`,
  REPEAT GEN_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`dist(A':real^N,B') = &0`; `dist(B':real^N,C') = &0`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DIST_EQ_0]) THEN
  ASM_SIMP_TAC[ANGLE_REFL_MID; ANGLE_REFL] THEN
  ONCE_REWRITE_TAC[GSYM COS_ANGLE_EQ] THEN
  MP_TAC(ISPECL [`B:real^M`; `A:real^M`; `C:real^M`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`B':real^N`; `A':real^N`; `C':real^N`] LAW_OF_COSINES) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[GSYM DIST_EQ_0; DIST_SYM] THEN
  CONV_TAC REAL_FIELD);;

let CONGRUENT_TRIANGLES_SAS = prove
 (`!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        angle(A,B,C) = angle(A',B',C') /\
        dist(B,C) = dist(B',C')
        ==> dist(A,C) = dist(A',C')`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIST_EQ] THEN
  MP_TAC(ISPECL [`B:real^M`; `A:real^M`; `C:real^M`] LAW_OF_COSINES) THEN
  MP_TAC(ISPECL [`B':real^N`; `A':real^N`; `C':real^N`] LAW_OF_COSINES) THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REPEAT BINOP_TAC THEN ASM_MESON_TAC[DIST_SYM]);;

let CONGRUENT_TRIANGLES_AAS = prove
 (`!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        angle(B,C,A) = angle(B',C',A') /\
        dist(A,B) = dist(A',B') /\
        ~(collinear {A,B,C})
        ==> dist(A,C) = dist(A',C') /\ dist(B,C) = dist(B',C')`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^M = B` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `~(A':real^N = B')` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN `angle(C:real^M,A,B) = angle(C':real^N,A',B')` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A:real^M`; `B:real^M`; `C:real^M`] TRIANGLE_ANGLE_SUM) THEN
    MP_TAC(ISPECL [`A':real^N`; `B':real^N`; `C':real^N`]
      TRIANGLE_ANGLE_SUM) THEN ASM_REWRITE_TAC[IMP_IMP] THEN
    REWRITE_TAC[ANGLE_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`C:real^M`; `B:real^M`; `A:real^M`] LAW_OF_SINES) THEN
    MP_TAC(ISPECL [`C':real^N`; `B':real^N`; `A':real^N`] LAW_OF_SINES) THEN
    SUBGOAL_THEN `~(sin(angle(B':real^N,C',A')) = &0)` MP_TAC THENL
     [ASM_MESON_TAC[COLLINEAR_SIN_ANGLE_IMP; INSERT_AC];
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ANGLE_SYM; DIST_SYM] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[ANGLE_SYM; DIST_SYM] THEN
      CONV_TAC REAL_FIELD];
    ASM_MESON_TAC[CONGRUENT_TRIANGLES_SAS; DIST_SYM; ANGLE_SYM]]);;

let CONGRUENT_TRIANGLES_ASA = prove
 (`!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        dist(A,B) = dist(A',B') /\
        angle(B,A,C) = angle(B',A',C') /\
        ~(collinear {A,B,C})
        ==> dist(A,C) = dist(A',C')`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^M = B` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `~(A':real^N = B')` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`A:real^M`; `B:real^M`; `C:real^M`] TRIANGLE_ANGLE_SUM) THEN
  MP_TAC(ISPECL [`A':real^N`; `B':real^N`; `C':real^N`]
    TRIANGLE_ANGLE_SUM) THEN
  ASM_REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
    `a + b + x = pi /\ a + b + y = pi ==> x = y`)) THEN
  ASM_MESON_TAC[CONGRUENT_TRIANGLES_AAS; DIST_SYM; ANGLE_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Full versions where we deduce everything from the conditions.             *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_TRIANGLES_SSS_FULL = prove
 (`!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        dist(B,C) = dist(B',C') /\
        dist(C,A) = dist(C',A')
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`,
  MESON_TAC[CONGRUENT_TRIANGLES_SSS; DIST_SYM; ANGLE_SYM]);;

let CONGRUENT_TRIANGLES_SAS_FULL = prove
 (`!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        angle(A,B,C) = angle(A',B',C') /\
        dist(B,C) = dist(B',C')
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`,
  MESON_TAC[CONGRUENT_TRIANGLES_SSS; DIST_SYM; ANGLE_SYM;
            CONGRUENT_TRIANGLES_SAS]);;

let CONGRUENT_TRIANGLES_AAS_FULL = prove
 (`!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        angle(B,C,A) = angle(B',C',A') /\
        dist(A,B) = dist(A',B') /\
        ~(collinear {A,B,C})
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`,
  MESON_TAC[CONGRUENT_TRIANGLES_SSS; DIST_SYM; ANGLE_SYM;
            CONGRUENT_TRIANGLES_AAS]);;

let CONGRUENT_TRIANGLES_ASA_FULL = prove
 (`!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        dist(A,B) = dist(A',B') /\
        angle(B,A,C) = angle(B',A',C') /\
        ~(collinear {A,B,C})
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`,
  MESON_TAC[CONGRUENT_TRIANGLES_ASA; CONGRUENT_TRIANGLES_SAS_FULL;
            DIST_SYM; ANGLE_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Between-ness.                                                             *)
(* ------------------------------------------------------------------------- *)

let ANGLE_BETWEEN = prove
 (`!a b x. angle(a,x,b) = pi <=> ~(x = a) /\ ~(x = b) /\ between x (a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[between; ANGLE_EQ_PI_DIST] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let BETWEEN_ANGLE = prove
 (`!a b x. between x (a,b) <=> x = a \/ x = b \/ angle(a,x,b) = pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ANGLE_BETWEEN] THEN
  MESON_TAC[BETWEEN_REFL]);;

let ANGLES_ALONG_LINE = prove
 (`!A B C D:real^N.
      ~(C = A) /\ ~(C = B) /\ between C (A,B)
      ==> angle(A,C,D) + angle(B,C,D) = pi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM ANGLE_BETWEEN] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP ANGLE_EQ_PI_LEFT) THEN REAL_ARITH_TAC);;

let ANGLES_ADD_BETWEEN = prove
 (`!A B C D:real^N.
        between C (A,B) /\ ~(D = A) /\ ~(D = B)
        ==> angle(A,D,C) + angle(C,D,B) = angle(A,D,B)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^N = B` THENL
   [ASM_SIMP_TAC[BETWEEN_REFL_EQ] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ADD_LID];
    ALL_TAC] THEN
  ASM_CASES_TAC `C:real^N = A` THEN
  ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ADD_LID] THEN
  ASM_CASES_TAC `C:real^N = B` THEN
  ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ADD_RID] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`; `D:real^N`]
        ANGLES_ALONG_LINE) THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  MP_TAC(ISPECL [`A:real^N`; `C:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `angle(C:real^N,A,D) = angle(B,A,D) /\
                angle(A,B,D) = angle(C,B,D)`
   (CONJUNCTS_THEN SUBST1_TAC)
  THENL [ALL_TAC; REWRITE_TAC[ANGLE_SYM] THEN REAL_ARITH_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC ANGLE_EQ_0_RIGHT THEN
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE]);;

(* ------------------------------------------------------------------------- *)
(* Distance from a point to a line expressed with angles.                    *)
(* ------------------------------------------------------------------------- *)

let SETDIST_POINT_LINE = prove
 (`!x y z:real^N.
        setdist({x},affine hull {y,z}) = dist(x,y) * sin(angle(x,y,z))`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `y:real^N` THEN
  REPEAT GEN_TAC THEN
  SIMP_TAC[SETDIST_CLOSEST_POINT; CLOSED_AFFINE_HULL;
           AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  ABBREV_TAC `y = closest_point (affine hull {vec 0, z}) (x:real^N)` THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `y:real^N`; `x:real^N`]
        SIN_OPPOSITE_HYPOTENUSE) THEN
  MP_TAC(ISPECL [`affine hull {vec 0:real^N, z}`; `x:real^N`; `vec 0:real^N`]
        CLOSEST_POINT_AFFINE_ORTHOGONAL) THEN
  ASM_SIMP_TAC[HULL_INC; IN_INSERT; AFFINE_AFFINE_HULL;
               AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  DISCH_THEN(K ALL_TAC) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[DIST_SYM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ANGLE_SYM] THEN
  MP_TAC(ISPECL [`affine hull {vec 0:real^N, z}`; `x:real^N`]
        CLOSEST_POINT_IN_SET) THEN
  ASM_SIMP_TAC[CLOSED_AFFINE_HULL; AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  SIMP_TAC[AFFINE_HULL_2; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `a:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`affine hull {vec 0:real^N, z}`; `x:real^N`; `z:real^N`]
        CLOSEST_POINT_AFFINE_ORTHOGONAL) THEN
  ASM_SIMP_TAC[HULL_INC; IN_INSERT; AFFINE_AFFINE_HULL;
               AFFINE_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
  REWRITE_TAC[angle; VECTOR_SUB_RZERO; SIN_VECTOR_ANGLE_LMUL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  SIMP_TAC[ORTHOGONAL_VECTOR_ANGLE; SIN_PI2]);;

(* ------------------------------------------------------------------------- *)
(* A standard formula for the area of a triangle.                            *)
(* ------------------------------------------------------------------------- *)

let AREA_TRIANGLE_SIN = prove
 (`!a b c:real^2.
     measure(convex hull {a,b,c}) =
     (dist(a,b) * dist(a,c) * sin(angle(b,a,c))) / &2`,
  GEOM_ORIGIN_TAC `a:real^2` THEN
  REWRITE_TAC[MEASURE_TRIANGLE; angle] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; VEC_COMPONENT; REAL_SUB_RZERO; DIST_0] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `&0 <= y /\ abs x = abs y ==> abs x / &2 = y / &2`) THEN
  SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; SIN_VECTOR_ANGLE_POS] THEN
  REWRITE_TAC[REAL_EQ_SQUARE_ABS] THEN
  ASM_CASES_TAC `b:real^2 = vec 0` THENL
   [ASM_REWRITE_TAC[VEC_COMPONENT; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `c:real^2 = vec 0` THENL
   [ASM_REWRITE_TAC[VEC_COMPONENT; NORM_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_MUL; SIN_SQUARED_VECTOR_ANGLE] THEN
  ASM_SIMP_TAC[NORM_EQ_0; REAL_FIELD
   `~(b = &0) /\ ~(c = &0)
    ==> b pow 2 * c pow 2 * (&1 - (d / (b * c)) pow 2) =
        b pow 2 * c pow 2 - d pow 2`] THEN
  REWRITE_TAC[NORM_POW_2; DOT_2] THEN CONV_TAC REAL_RING);;
