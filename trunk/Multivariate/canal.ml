(* ========================================================================= *)
(* Complex analysis.                                                         *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* (c) Copyright, Marco Maggesi, Graziano Gentili and Gianni Ciolli, 2008.   *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

needs "Library/floor.ml";;
needs "Library/iter.ml";;
needs "Multivariate/complexes.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* Some toplogical facts formulated for the complex numbers.                 *)
(* ------------------------------------------------------------------------- *)

let CLOSED_HALFSPACE_RE_GE = prove
 (`!b. closed {z | Re(z) >= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `b:real`] CLOSED_HALFSPACE_GE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[RE_CX; IM_CX; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CLOSED_HALFSPACE_RE_LE = prove
 (`!b. closed {z | Re(z) <= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `b:real`] CLOSED_HALFSPACE_LE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[RE_CX; IM_CX; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CLOSED_HALFSPACE_RE_EQ = prove
 (`!b. closed {z | Re(z) = b}`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x = y <=> x >= y /\ x <= y`] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[CLOSED_INTER; CLOSED_HALFSPACE_RE_GE; CLOSED_HALFSPACE_RE_LE]);;

let OPEN_HALFSPACE_RE_GT = prove
 (`!b. open {z | Re(z) > b}`,
  REWRITE_TAC[OPEN_CLOSED; CLOSED_HALFSPACE_RE_LE;
              REAL_ARITH `x > y <=> ~(x <= y)`;
              SET_RULE `UNIV DIFF {x | ~p x} = {x | p x}`]);;

let OPEN_HALFSPACE_RE_LT = prove
 (`!b. open {z | Re(z) < b}`,
  REWRITE_TAC[OPEN_CLOSED; CLOSED_HALFSPACE_RE_GE;
              REAL_ARITH `x < y <=> ~(x >= y)`;
              SET_RULE `UNIV DIFF {x | ~p x} = {x | p x}`]);;

let CLOSED_HALFSPACE_IM_GE = prove
 (`!b. closed {z | Im(z) >= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`ii`; `b:real`] CLOSED_HALFSPACE_GE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CLOSED_HALFSPACE_IM_LE = prove
 (`!b. closed {z | Im(z) <= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`ii`; `b:real`] CLOSED_HALFSPACE_LE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CLOSED_HALFSPACE_IM_EQ = prove
 (`!b. closed {z | Im(z) = b}`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x = y <=> x >= y /\ x <= y`] THEN
  REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
  SIMP_TAC[CLOSED_INTER; CLOSED_HALFSPACE_IM_GE; CLOSED_HALFSPACE_IM_LE]);;

let OPEN_HALFSPACE_IM_GT = prove
 (`!b. open {z | Im(z) > b}`,
  REWRITE_TAC[OPEN_CLOSED; CLOSED_HALFSPACE_IM_LE;
              REAL_ARITH `x > y <=> ~(x <= y)`;
              SET_RULE `UNIV DIFF {x | ~p x} = {x | p x}`]);;

let OPEN_HALFSPACE_IM_LT = prove
 (`!b. open {z | Im(z) < b}`,
  REWRITE_TAC[OPEN_CLOSED; CLOSED_HALFSPACE_IM_GE;
              REAL_ARITH `x < y <=> ~(x >= y)`;
              SET_RULE `UNIV DIFF {x | ~p x} = {x | p x}`]);;

let CONVEX_HALFSPACE_RE_GE = prove
 (`!b. convex {z | Re(z) >= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `b:real`] CONVEX_HALFSPACE_GE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_RE_GT = prove
 (`!b. convex {z | Re(z) > b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `b:real`] CONVEX_HALFSPACE_GT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_RE_LE = prove
 (`!b. convex {z | Re(z) <= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `b:real`] CONVEX_HALFSPACE_LE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_RE_LT = prove
 (`!b. convex {z | Re(z) < b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`Cx(&1)`; `b:real`] CONVEX_HALFSPACE_LT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_IM_GE = prove
 (`!b. convex {z | Im(z) >= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`ii`; `b:real`] CONVEX_HALFSPACE_GE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_IM_GT = prove
 (`!b. convex {z | Im(z) > b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`ii`; `b:real`] CONVEX_HALFSPACE_GT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_IM_LE = prove
 (`!b. convex {z | Im(z) <= b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`ii`; `b:real`] CONVEX_HALFSPACE_LE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_IM_LT = prove
 (`!b. convex {z | Im(z) < b}`,
  GEN_TAC THEN MP_TAC(ISPECL [`ii`; `b:real`] CONVEX_HALFSPACE_LT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; dot; SUM_2; DIMINDEX_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[ii; RE_CX; IM_CX; RE; IM; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let CONVEX_HALFSPACE_RE_SGN = prove
 (`!b. convex {z | real_sgn(Re z) = b}`,
  REWRITE_TAC[RE_DEF; CONVEX_HALFSPACE_COMPONENT_SGN]);;

let CONVEX_HALFSPACE_IM_SGN = prove
 (`!b. convex {z | real_sgn(Im z) = b}`,
  REWRITE_TAC[IM_DEF; CONVEX_HALFSPACE_COMPONENT_SGN]);;

let COMPLEX_IN_BALL_0 = prove
 (`!v r. v IN ball(Cx(&0),r) <=> norm v < r`,
  REWRITE_TAC [GSYM COMPLEX_VEC_0; IN_BALL_0]);;

let COMPLEX_IN_CBALL_0 = prove
 (`!v r. v IN cball(Cx(&0),r) <=> norm v <= r`,
  REWRITE_TAC [GSYM COMPLEX_VEC_0; IN_CBALL_0]);;

let COMPLEX_IN_SPHERE_0 = prove
 (`!v r. v IN sphere(Cx(&0),r) <=> norm v = r`,
  REWRITE_TAC [GSYM COMPLEX_VEC_0; IN_SPHERE_0]);;

let IN_BALL_RE = prove
 (`!x z e. x IN ball(z,e) ==> abs(Re(x) - Re(z)) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN
  MP_TAC(SPEC `z - x:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN REAL_ARITH_TAC);;

let IN_BALL_IM = prove
 (`!x z e. x IN ball(z,e) ==> abs(Im(x) - Im(z)) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BALL; dist] THEN
  MP_TAC(SPEC `z - x:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[IM_SUB] THEN REAL_ARITH_TAC);;

let IN_CBALL_RE = prove
 (`!x z e. x IN cball(z,e) ==> abs(Re(x) - Re(z)) <= e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
  MP_TAC(SPEC `z - x:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[RE_SUB] THEN REAL_ARITH_TAC);;

let IN_CBALL_IM = prove
 (`!x z e. x IN cball(z,e) ==> abs(Im(x) - Im(z)) <= e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_CBALL; dist] THEN
  MP_TAC(SPEC `z - x:complex` COMPLEX_NORM_GE_RE_IM) THEN
  REWRITE_TAC[IM_SUB] THEN REAL_ARITH_TAC);;

let CLOSED_REAL_SET = prove
 (`closed {z | real z}`,
  REWRITE_TAC[CLOSED_HALFSPACE_IM_EQ; real]);;

let CLOSED_REAL = prove
 (`closed real`,
  GEN_REWRITE_TAC RAND_CONV [SET_RULE `s = {x | s x}`] THEN
  REWRITE_TAC[CLOSED_REAL_SET]);;

let UNBOUNDED_REAL = prove
 (`~(bounded real)`,
  REWRITE_TAC[bounded; IN; REAL_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  MESON_TAC[COMPLEX_NORM_CX; REAL_ARITH `~(abs(abs B + &1) <= B)`]);;

let CONNECTED_REAL = prove
 (`connected real`,
  SIMP_TAC[CONVEX_REAL; CONVEX_CONNECTED]);;

let PATH_CONNECTED_REAL = prove
 (`path_connected real`,
  SIMP_TAC[CONVEX_REAL; CONVEX_IMP_PATH_CONNECTED]);;

let TRIVIAL_LIMIT_WITHIN_REAL = prove
 (`!z. trivial_limit (at z within real) <=> ~(real z)`,
  GEN_TAC THEN REWRITE_TAC[TRIVIAL_LIMIT_WITHIN] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM IN] THEN
  MATCH_MP_TAC CONNECTED_IMP_PERFECT_CLOSED THEN
  REWRITE_TAC[CONNECTED_REAL; CLOSED_REAL] THEN
  MESON_TAC[UNBOUNDED_REAL; BOUNDED_SING]);;

(* ------------------------------------------------------------------------- *)
(* Complex-specific uniform limit composition theorems.                      *)
(* ------------------------------------------------------------------------- *)

let UNIFORM_LIM_COMPLEX_MUL = prove
 (`!net:(A)net P f g l m b1 b2.
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        eventually (\x. !n. P n ==> norm(m n) <= b2) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(f n x * g n x - l n * m n) < e)
                     net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o CONJ BILINEAR_COMPLEX_MUL) THEN
  REWRITE_TAC[UNIFORM_LIM_BILINEAR]);;

let UNIFORM_LIM_COMPLEX_INV = prove
 (`!net:(A)net P f l b.
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        &0 < b /\ eventually (\x. !n. P n ==> b <= norm(l n)) net
        ==> !e. &0 < e
                ==> eventually
                    (\x. !n. P n ==> norm(inv(f n x) - inv(l n)) < e) net`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EVENTUALLY_MONO THEN
  EXISTS_TAC
   `\x. !n. P n ==> b <= norm(l n) /\
                    b / &2 <= norm((f:B->A->complex) n x) /\
                    norm(f n x - l n) < e * b pow 2 / &2` THEN
  REWRITE_TAC[TAUT `(p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:A` THEN STRIP_TAC THEN X_GEN_TAC `n:B` THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:B`) THEN ASM_REWRITE_TAC[]) THEN
    REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `~((f:B->A->complex) n x = Cx(&0)) /\ ~(l n = Cx(&0))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_NORM_CX]) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(x = Cx(&0)) /\ ~(y = Cx(&0))
      ==> inv x - inv y = (y - x) / (x * y)`] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_DIV; REAL_LT_LDIV_EQ; COMPLEX_NORM_NZ;
                 COMPLEX_ENTIRE] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        REAL_LTE_TRANS)) THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH `b pow 2 / &2 = b / &2 * b`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[EVENTUALLY_AND] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `b / &2`) THEN
      ASM_REWRITE_TAC[REAL_HALF] THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN REWRITE_TAC[IMP_IMP] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM EVENTUALLY_AND]) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
      REWRITE_TAC[] THEN
      ASM_MESON_TAC[NORM_ARITH
       `b <= norm l /\ norm(f - l) < b / &2 ==> b / &2 <= norm f`];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_HALF; REAL_POW_LT; REAL_LT_MUL]]]);;

let UNIFORM_LIM_COMPLEX_DIV = prove
 (`!net:(A)net P f g l m b1 b2.
        eventually (\x. !n. P n ==> norm(l n) <= b1) net /\
        &0 < b2 /\ eventually (\x. !n. P n ==> b2 <= norm(m n)) net /\
        (!e. &0 < e
             ==> eventually (\x. !n:B. P n ==> norm(f n x - l n) < e) net) /\
        (!e. &0 < e
             ==> eventually (\x. !n. P n ==> norm(g n x - m n) < e) net)
        ==> !e. &0 < e
                ==> eventually
                     (\x. !n. P n
                              ==> norm(f n x / g n x - l n / m n) < e)
                     net`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[complex_div] THEN MATCH_MP_TAC UNIFORM_LIM_COMPLEX_MUL THEN
  MAP_EVERY EXISTS_TAC [`b1:real`; `inv(b2):real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o CONJUNCT1) o CONJUNCT2) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    GEN_TAC THEN REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC UNIFORM_LIM_COMPLEX_INV THEN
    EXISTS_TAC `b2:real` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The usual non-uniform versions.                                           *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPLEX_MUL = prove
 (`!net:(A)net f g l m.
         (f --> l) net /\ (g --> m) net ==> ((\x. f x * g x) --> l * m) net`,
  SIMP_TAC[LIM_BILINEAR; BILINEAR_COMPLEX_MUL]);;

let LIM_COMPLEX_INV = prove
 (`!net:(A)net f g l m.
         (f --> l) net /\ ~(l = Cx(&0)) ==> ((\x. inv(f x)) --> inv(l)) net`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`net:(A)net`; `\x:one. T`;
    `\n:one. (f:A->complex)`;
    `\n:one. (l:complex)`;
    `norm(l:complex)`] UNIFORM_LIM_COMPLEX_INV) THEN
  ASM_REWRITE_TAC[REAL_LE_REFL; EVENTUALLY_TRUE] THEN
  ASM_REWRITE_TAC[GSYM dist; GSYM tendsto; COMPLEX_NORM_NZ]);;

let LIM_COMPLEX_DIV = prove
 (`!net:(A)net f g l m.
         (f --> l) net /\ (g --> m) net /\ ~(m = Cx(&0))
         ==> ((\x. f x / g x) --> l / m) net`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_div] THEN
  MATCH_MP_TAC LIM_COMPLEX_MUL THEN ASM_SIMP_TAC[LIM_COMPLEX_INV]);;

let LIM_COMPLEX_POW = prove
 (`!net:(A)net f l n.
         (f --> l) net ==> ((\x. f(x) pow n) --> l pow n) net`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[LIM_COMPLEX_MUL; complex_pow; LIM_CONST]);;

let LIM_COMPLEX_LMUL = prove
 (`!f l c. (f --> l) net ==> ((\x. c * f x) --> c * l) net`,
  SIMP_TAC[LIM_COMPLEX_MUL; LIM_CONST]);;

let LIM_COMPLEX_RMUL = prove
 (`!f l c. (f --> l) net ==> ((\x. f x * c) --> l * c) net`,
  SIMP_TAC[LIM_COMPLEX_MUL; LIM_CONST]);;

(* ------------------------------------------------------------------------- *)
(* Mapping real limits between C and R^1.                                    *)
(* ------------------------------------------------------------------------- *)

let LIM_CX_LIFT = prove
 (`!net f l.
     ((\x. Cx(f x)) --> Cx l) net <=> ((\x. lift(f x)) --> lift l) net`,
  REWRITE_TAC[LIM; DIST_LIFT; DIST_CX]);;

let SERIES_CX_LIFT = prove
 (`!f s x.
     ((\x. Cx(f x)) sums (Cx x)) s <=> ((\x. lift(f x)) sums (lift x)) s`,
  SIMP_TAC[sums; LIM_CX_LIFT; VSUM_CX; FINITE_INTER; FINITE_NUMSEG] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] (GSYM LIFT_SUM)]);;

let LIM_INFINITY_POSINFINITY_CX = prove
 (`!f l:real^N. (f --> l) at_infinity ==> ((f o Cx) --> l) at_posinfinity`,
  REWRITE_TAC[LIM_AT_INFINITY; LIM_AT_POSINFINITY; o_THM] THEN
  MESON_TAC[COMPLEX_NORM_CX; REAL_ARITH `x >= b ==> abs(x) >= b`]);;

(* ------------------------------------------------------------------------- *)
(* Special cases of null limits.                                             *)
(* ------------------------------------------------------------------------- *)

let LIM_NULL_COMPLEX = prove
 (`!net f. (f --> l) net <=> ((\x. f x - l) --> Cx(&0)) net`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM LIM_NULL]);;

let LIM_NULL_COMPLEX_NORM = prove
 (`!net f. (f --> Cx(&0)) net <=> ((\x. Cx(norm(f x))) --> Cx(&0)) net`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NORM]);;

let LIM_NULL_COMPLEX_NEG = prove
 (`!net f. (f --> Cx(&0)) net ==> ((\x. --(f x)) --> Cx(&0)) net`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_NEG) THEN
  REWRITE_TAC[COMPLEX_NEG_0]);;

let LIM_NULL_COMPLEX_ADD = prove
 (`!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x + g x) --> Cx(&0)) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_ADD) THEN
  REWRITE_TAC[COMPLEX_ADD_LID]);;

let LIM_NULL_COMPLEX_SUB = prove
 (`!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x - g x) --> Cx(&0)) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
  REWRITE_TAC[COMPLEX_SUB_REFL]);;

let LIM_NULL_COMPLEX_MUL = prove
 (`!net f g. (f --> Cx(&0)) net /\ (g --> Cx(&0)) net
             ==> ((\x. f x * g x) --> Cx(&0)) net`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LIM_COMPLEX_MUL) THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO]);;

let LIM_NULL_COMPLEX_LMUL = prove
 (`!net f c. (f --> Cx(&0)) net ==> ((\x. c * f x) --> Cx(&0)) net`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(COMPLEX_RING `Cx(&0) = c * Cx(&0)`) THEN
  ASM_SIMP_TAC[LIM_COMPLEX_LMUL]);;

let LIM_NULL_COMPLEX_RMUL = prove
 (`!net f c. (f --> Cx(&0)) net ==> ((\x. f x * c) --> Cx(&0)) net`,
  REPEAT STRIP_TAC THEN SUBST1_TAC(COMPLEX_RING `Cx(&0) = Cx(&0) * c`) THEN
  ASM_SIMP_TAC[LIM_COMPLEX_RMUL]);;

let LIM_NULL_COMPLEX_POW = prove
 (`!net f n. (f --> Cx(&0)) net /\ ~(n = 0)
             ==> ((\x. (f x) pow n) --> Cx(&0)) net`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP LIM_COMPLEX_POW) THEN
  ASM_REWRITE_TAC[COMPLEX_POW_ZERO]);;

let LIM_NULL_COMPLEX_BOUND = prove
 (`!f g. eventually (\n. norm (f n) <= norm (g n)) net /\ (g --> Cx(&0)) net
         ==> (f --> Cx(&0)) net`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0; LIM_TRANSFORM_BOUND]);;

let SUMS_COMPLEX_0 = prove
 (`!f s. (!n. n IN s ==> f n = Cx(&0)) ==> (f sums Cx(&0)) s`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0; SUMS_0]);;

let LIM_NULL_COMPLEX_RMUL_BOUNDED = prove
 (`!net f g B.
        (f --> Cx(&0)) net /\
        eventually (\a. f a = Cx(&0) \/ norm(g a) <= B) net
        ==> ((\z. f(z) * g(z)) --> Cx(&0)) net`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
  REWRITE_TAC[LIFT_CMUL; COMPLEX_NORM_MUL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LIM_NULL_VMUL_BOUNDED THEN
  EXISTS_TAC `B:real` THEN
  ASM_REWRITE_TAC[o_DEF; NORM_LIFT; REAL_ABS_NORM; NORM_EQ_0]);;

let LIM_NULL_COMPLEX_LMUL_BOUNDED = prove
 (`!net f g B.
        eventually (\a. norm(f a) <= B \/ g a = Cx(&0)) net /\
        (g --> Cx(&0)) net
        ==> ((\z. f(z) * g(z)) --> Cx(&0)) net`,
  ONCE_REWRITE_TAC[DISJ_SYM; COMPLEX_MUL_SYM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_NULL_COMPLEX_RMUL_BOUNDED THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Bound results for real and imaginary components of limits.                *)
(* ------------------------------------------------------------------------- *)

let LIM_RE_UBOUND = prove
 (`!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. Re(f x) <= b) net
        ==> Re(l) <= b`,
  REWRITE_TAC[RE_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `f:A->complex`; `l:complex`; `b:real`; `1`]
                LIM_COMPONENT_UBOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

let LIM_RE_LBOUND = prove
 (`!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= Re(f x)) net
        ==> b <= Re(l)`,
  REWRITE_TAC[RE_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `f:A->complex`; `l:complex`; `b:real`; `1`]
                LIM_COMPONENT_LBOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

let LIM_IM_UBOUND = prove
 (`!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. Im(f x) <= b) net
        ==> Im(l) <= b`,
  REWRITE_TAC[IM_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `f:A->complex`; `l:complex`; `b:real`; `2`]
                LIM_COMPONENT_UBOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

let LIM_IM_LBOUND = prove
 (`!net:(A)net f l b.
        ~(trivial_limit net) /\ (f --> l) net /\
        eventually (\x. b <= Im(f x)) net
        ==> b <= Im(l)`,
  REWRITE_TAC[IM_DEF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`net:(A)net`; `f:A->complex`; `l:complex`; `b:real`; `2`]
                LIM_COMPONENT_LBOUND) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Case analysis for limit of reciprocal of a function. This can be true     *)
(* degenerately, and it's a bit tiresome to show otherwise that it means     *)
(* what you expect.                                                          *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPLEX_INV_NONDEGENERATE = prove
 (`!f:real^N->complex s a l.
        2 <= dimindex(:N) /\
        a IN s /\ open s /\
        f continuous_on (s DELETE a) /\
        ((inv o f) --> l) (at a)
        ==> ?t. open t /\ t SUBSET s /\
                ((!x. x IN t DELETE a ==> f x = Cx(&0)) /\ l = Cx(&0) \/
                 (!x. x IN t DELETE a ==> ~(f x = Cx(&0))))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `!e. &0 < e ==> ?z:real^N. norm(z - a) < e /\ ~(z = a) /\ f(z) = Cx(&0)`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; NOT_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    EXISTS_TAC `s INTER ball(a:real^N,e)` THEN
    ASM_SIMP_TAC[INTER_SUBSET; OPEN_INTER; OPEN_BALL] THEN DISJ2_TAC THEN
    REWRITE_TAC[IN_DELETE; IN_INTER; IN_BALL; dist] THEN
    ASM_MESON_TAC[NORM_SUB]] THEN
  SUBGOAL_THEN `l = Cx(&0)` SUBST_ALL_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_AT]) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `norm(l:complex)`) THEN
    ASM_SIMP_TAC[COMPLEX_NORM_NZ; dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[NORM_POS_LT; o_THM; VECTOR_SUB_EQ; COMPLEX_INV_0] THEN
    REWRITE_TAC[COMPLEX_SUB_LZERO; NORM_NEG; REAL_LT_REFL];
    REWRITE_TAC[]] THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !z:real^N. norm(z - a) < e /\ ~(z = a)
                   ==> z IN s /\ (f z = Cx(&0) \/ norm(f z) >= &1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_AT]) THEN
    DISCH_THEN(MP_TAC o SPEC `&1`) THEN REWRITE_TAC[REAL_LT_01] THEN
    REWRITE_TAC[o_THM; VECTOR_SUB_EQ; dist; COMPLEX_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d e:real` THEN ASM_SIMP_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[TAUT `p \/ q <=> ~p ==> q`] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`)) THEN
    ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN REPEAT DISCH_TAC THEN
    SUBST1_TAC(REAL_ARITH `&1 = inv(&1)`) THEN REWRITE_TAC[real_ge] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_SIMP_TAC[GSYM COMPLEX_NORM_INV; REAL_LT_IMP_LE] THEN
    ASM_REWRITE_TAC[NORM_POS_LT; COMPLEX_INV_EQ_0; COMPLEX_VEC_0];
    ALL_TAC] THEN
  EXISTS_TAC `ball(a:real^N,e)` THEN
  ASM_REWRITE_TAC[OPEN_BALL; SUBSET; IN_DELETE; IN_BALL; dist] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[NORM_SUB]; DISJ1_TAC] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  ASM_CASES_TAC `f(z:real^N) = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `connected (IMAGE (lift o norm o (f:real^N->complex)) (ball(a,e) DELETE a))`
  MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_PUNCTURED_BALL; o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_BALL; dist] THEN
    ASM_MESON_TAC[NORM_SUB];
    REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1]] THEN
  REWRITE_TAC[IS_INTERVAL_1; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_DELETE; IN_BALL; dist] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[NORM_SUB]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
  ASM_REWRITE_TAC[o_THM; LIFT_DROP; COMPLEX_NORM_0] THEN
  DISCH_THEN(MP_TAC o SPEC `lift(&1 / &2)`) THEN
  ASM_REWRITE_TAC[LIFT_DROP; NOT_IMP] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x >= &1 ==> &1 / &2 <= x`) THEN
    ASM_MESON_TAC[NORM_SUB];
    REWRITE_TAC[IN_IMAGE; o_THM; LIFT_EQ; IN_BALL; IN_DELETE; dist] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o CONJUNCT2) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_NORM_0]) THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Left and right multiplication of series.                                  *)
(* ------------------------------------------------------------------------- *)

let SERIES_COMPLEX_LMUL = prove
 (`!f l c s. (f sums l) s ==> ((\x. c * f x) sums c * l) s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_LINEAR THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[LINEAR_COMPLEX_MUL]);;

let SERIES_COMPLEX_RMUL = prove
 (`!f l c s. (f sums l) s ==> ((\x. f x * c) sums l * c) s`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN REWRITE_TAC[SERIES_COMPLEX_LMUL]);;

let SERIES_COMPLEX_DIV = prove
 (`!f l c s. (f sums l) s ==> ((\x. f x / c) sums (l / c)) s`,
  REWRITE_TAC[complex_div; SERIES_COMPLEX_RMUL]);;

let SUMMABLE_COMPLEX_LMUL = prove
 (`!f c s. summable s f ==> summable s (\x. c * f x)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_COMPLEX_LMUL]);;

let SUMMABLE_COMPLEX_RMUL = prove
 (`!f c s. summable s f ==> summable s (\x. f x * c)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_COMPLEX_RMUL]);;

let SUMMABLE_COMPLEX_DIV = prove
 (`!f c s. summable s f ==> summable s (\x. f x / c)`,
  REWRITE_TAC[summable] THEN MESON_TAC[SERIES_COMPLEX_DIV]);;

(* ------------------------------------------------------------------------- *)
(* Complex-specific continuity closures.                                     *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_COMPLEX_MUL = prove
 (`!net f g.
    f continuous net /\ g continuous net ==> (\x. f(x) * g(x)) continuous net`,
  SIMP_TAC[continuous; LIM_COMPLEX_MUL]);;

let CONTINUOUS_COMPLEX_LMUL = prove
 (`!c f net. f continuous net ==> (\x. c * f x) continuous net`,
  SIMP_TAC[CONTINUOUS_COMPLEX_MUL; CONTINUOUS_CONST]);;

let CONTINUOUS_COMPLEX_RMUL = prove
 (`!c f net. f continuous net ==> (\x. f x * c) continuous net`,
  SIMP_TAC[CONTINUOUS_COMPLEX_MUL; CONTINUOUS_CONST]);;

let CONTINUOUS_COMPLEX_INV = prove
 (`!net f.
    f continuous net /\ ~(f(netlimit net) = Cx(&0))
    ==> (\x. inv(f x)) continuous net`,
  SIMP_TAC[continuous; LIM_COMPLEX_INV]);;

let CONTINUOUS_COMPLEX_DIV = prove
 (`!net f g.
    f continuous net /\ g continuous net /\ ~(g(netlimit net) = Cx(&0))
    ==> (\x. f(x) / g(x)) continuous net`,
  SIMP_TAC[continuous; LIM_COMPLEX_DIV]);;

let CONTINUOUS_COMPLEX_POW = prove
 (`!net f n. f continuous net ==> (\x. f(x) pow n) continuous net`,
  SIMP_TAC[continuous; LIM_COMPLEX_POW]);;

(* ------------------------------------------------------------------------- *)
(* Write away the netlimit, which is otherwise a bit tedious.                *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_COMPLEX_INV_WITHIN = prove
 (`!f s a.
    f continuous (at a within s) /\ ~(f a = Cx(&0))
    ==> (\x. inv(f x)) continuous (at a within s)`,
  MESON_TAC[CONTINUOUS_COMPLEX_INV; CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHIN]);;

let CONTINUOUS_COMPLEX_INV_AT = prove
 (`!f a.
    f continuous (at a) /\ ~(f a = Cx(&0))
    ==> (\x. inv(f x)) continuous (at a)`,
  SIMP_TAC[CONTINUOUS_COMPLEX_INV; NETLIMIT_AT]);;

let CONTINUOUS_COMPLEX_DIV_WITHIN = prove
 (`!f g s a.
    f continuous (at a within s) /\ g continuous (at a within s) /\
    ~(g a = Cx(&0))
    ==> (\x. f x / g x) continuous (at a within s)`,
  MESON_TAC[CONTINUOUS_COMPLEX_DIV; CONTINUOUS_TRIVIAL_LIMIT;
            NETLIMIT_WITHIN]);;

let CONTINUOUS_COMPLEX_DIV_AT = prove
 (`!f g a.
    f continuous at a /\ g continuous at a /\ ~(g a = Cx(&0))
    ==> (\x. f x / g x) continuous at a`,
  SIMP_TAC[CONTINUOUS_COMPLEX_DIV; NETLIMIT_AT]);;

(* ------------------------------------------------------------------------- *)
(* Also prove "on" variants as needed.                                       *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_ON_COMPLEX_MUL = prove
 (`!f g s. f continuous_on s /\ g continuous_on s
           ==> (\x. f(x) * g(x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[CONTINUOUS_COMPLEX_MUL]);;

let CONTINUOUS_ON_COMPLEX_LMUL = prove
 (`!f:real^N->complex s. f continuous_on s ==> (\x. c * f(x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON] THEN SIMP_TAC[LIM_COMPLEX_MUL; LIM_CONST]);;

let CONTINUOUS_ON_COMPLEX_RMUL = prove
 (`!f:real^N->complex s. f continuous_on s ==> (\x. f(x) * c) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON] THEN SIMP_TAC[LIM_COMPLEX_MUL; LIM_CONST]);;

let CONTINUOUS_ON_COMPLEX_INV = prove
 (`!f:real^N->complex.
        f continuous_on s /\
        (!x. x IN s ==> ~(f x = Cx(&0)))
        ==> (\x. inv(f x)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN;
           CONTINUOUS_COMPLEX_INV_WITHIN]);;

let CONTINUOUS_ON_COMPLEX_DIV = prove
 (`!f g s. f continuous_on s /\ g continuous_on s /\
           (!x. x IN s ==> ~(g x = Cx(&0)))
           ==> (\x. f(x) / g(x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  SIMP_TAC[CONTINUOUS_COMPLEX_DIV_WITHIN]);;

let CONTINUOUS_ON_COMPLEX_POW = prove
 (`!f n s. f continuous_on s ==> (\x. f(x) pow n) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_COMPLEX_POW]);;

(* ------------------------------------------------------------------------- *)
(* And also uniform versions.                                                *)
(* ------------------------------------------------------------------------- *)

let UNIFORMLY_CONTINUOUS_ON_COMPLEX_MUL = prove
 (`!f g s:real^N->bool.
        f uniformly_continuous_on s /\ g uniformly_continuous_on s /\
        bounded(IMAGE f s) /\ bounded(IMAGE g s)
        ==> (\x. f(x) * g(x)) uniformly_continuous_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`f:real^N->complex`; `g:real^N->complex`;
    `( * ):complex->complex->complex`; `s:real^N->bool`]
    BILINEAR_UNIFORMLY_CONTINUOUS_ON_COMPOSE) THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL]);;

let UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL = prove
 (`!f c s:real^N->bool.
      f uniformly_continuous_on s ==> (\x. c * f x) uniformly_continuous_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o ISPEC `\x:complex. c * x` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] UNIFORMLY_CONTINUOUS_ON_COMPOSE)) THEN
  ASM_SIMP_TAC[o_DEF; LINEAR_COMPLEX_MUL; LINEAR_UNIFORMLY_CONTINUOUS_ON]);;

let UNIFORMLY_CONTINUOUS_ON_COMPLEX_RMUL = prove
 (`!f c s:real^N->bool.
      f uniformly_continuous_on s ==> (\x. f x * c) uniformly_continuous_on s`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[UNIFORMLY_CONTINUOUS_ON_COMPLEX_LMUL]);;

(* ------------------------------------------------------------------------- *)
(* Continuity prover (not just for complex numbers but with more for them).  *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_TAC =
  let ETA_THM = prove
   (`f continuous net <=> (\x. f x) continuous net`,
    REWRITE_TAC[ETA_AX]) in
  let ETA_TWEAK =
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] o SPEC_ALL in
  let tac_base =
    MATCH_ACCEPT_TAC CONTINUOUS_CONST ORELSE
    MATCH_ACCEPT_TAC CONTINUOUS_AT_ID ORELSE
    MATCH_ACCEPT_TAC CONTINUOUS_WITHIN_ID
  and tac_1 =
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_CMUL) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_NEG) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_COMPLEX_POW)
  and tac_2 =
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_ADD) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_SUB) ORELSE
    MATCH_MP_TAC(ETA_TWEAK CONTINUOUS_COMPLEX_MUL)
  and tac_1' = MATCH_MP_TAC (ETA_TWEAK CONTINUOUS_COMPLEX_INV)
  and tac_2' = MATCH_MP_TAC (ETA_TWEAK CONTINUOUS_COMPLEX_DIV) in
  let rec CONTINUOUS_TAC gl =
   (tac_base ORELSE
    (tac_1 THEN CONTINUOUS_TAC) ORELSE
    (tac_2 THEN CONJ_TAC THEN CONTINUOUS_TAC) ORELSE
    (tac_1' THEN CONJ_TAC THENL
     [CONTINUOUS_TAC; REWRITE_TAC[NETLIMIT_AT; NETLIMIT_WITHIN]]) ORELSE
    (tac_2' THEN REPEAT CONJ_TAC THENL
     [CONTINUOUS_TAC; CONTINUOUS_TAC;
      REWRITE_TAC[NETLIMIT_AT; NETLIMIT_WITHIN]]) ORELSE
    ALL_TAC) gl in
  CONTINUOUS_TAC;;

(* ------------------------------------------------------------------------- *)
(* Hence a limit calculator                                                  *)
(* ------------------------------------------------------------------------- *)

let LIM_TAC =
  MATCH_MP_TAC LIM_CONTINUOUS THEN CONJ_TAC THENL
   [CONTINUOUS_TAC; REWRITE_TAC[NETLIMIT_AT; NETLIMIT_WITHIN]];;

(* ------------------------------------------------------------------------- *)
(* Continuity of the norm.                                                   *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_AT_CX_NORM = prove
 (`!z:real^N. (\z. Cx(norm z)) continuous at z`,
  REWRITE_TAC[continuous_at; dist; GSYM CX_SUB; COMPLEX_NORM_CX] THEN
  MESON_TAC[NORM_ARITH `norm(a - b:real^N) < d ==> abs(norm a - norm b) < d`]);;

let CONTINUOUS_WITHIN_CX_NORM = prove
 (`!z:real^N s. (\z. Cx(norm z)) continuous (at z within s)`,
  SIMP_TAC[CONTINUOUS_AT_CX_NORM; CONTINUOUS_AT_WITHIN]);;

let CONTINUOUS_ON_CX_NORM = prove
 (`!s. (\z. Cx(norm z)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_WITHIN_CX_NORM]);;

let CONTINUOUS_AT_CX_DOT = prove
 (`!c z:real^N. (\z. Cx(c dot z)) continuous at z`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear; DOT_RADD; DOT_RMUL; CX_ADD; COMPLEX_CMUL; CX_MUL]);;

let CONTINUOUS_WITHIN_CX_DOT = prove
 (`!c z:real^N s. (\z. Cx(c dot z)) continuous (at z within s)`,
  SIMP_TAC[CONTINUOUS_AT_CX_DOT; CONTINUOUS_AT_WITHIN]);;

let CONTINUOUS_ON_CX_DOT = prove
 (`!s c:real^N. (\z. Cx(c dot z)) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_WITHIN_CX_DOT]);;

(* ------------------------------------------------------------------------- *)
(* Continuity switching range between complex and real^1                     *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_CX_DROP = prove
 (`!net f. f continuous net ==> (\x. Cx(drop(f x))) continuous net`,
  REWRITE_TAC[continuous; tendsto] THEN
  REWRITE_TAC[dist; GSYM CX_SUB; COMPLEX_NORM_CX; GSYM DROP_SUB] THEN
  REWRITE_TAC[GSYM ABS_DROP]);;

let CONTINUOUS_ON_CX_DROP = prove
 (`!f s. f continuous_on s ==> (\x. Cx(drop(f x))) continuous_on s`,
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CX_DROP]);;

let CONTINUOUS_CX_LIFT = prove
 (`!f. (\x. Cx(f x)) continuous net <=> (\x. lift(f x)) continuous net`,
  REWRITE_TAC[continuous; LIM; dist; GSYM CX_SUB; GSYM LIFT_SUB] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; NORM_LIFT]);;

let CONTINUOUS_ON_CX_LIFT = prove
 (`!f s. (\x. Cx(f x)) continuous_on s <=> (\x. lift(f x)) continuous_on s`,
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN; CONTINUOUS_CX_LIFT]);;

(* ------------------------------------------------------------------------- *)
(* Linearity and continuity of the components.                               *)
(* ------------------------------------------------------------------------- *)

let LINEAR_CX_RE = prove
 (`linear(Cx o Re)`,
  SIMP_TAC[linear; o_THM; COMPLEX_CMUL; RE_ADD; RE_MUL_CX; CX_MUL; CX_ADD]);;

let CONTINUOUS_AT_CX_RE = prove
 (`!z. (Cx o Re) continuous at z`,
  SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_CX_RE]);;

let CONTINUOUS_ON_CX_RE = prove
 (`!s. (Cx o Re) continuous_on s`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CX_RE]);;

let LINEAR_CX_IM = prove
 (`linear(Cx o Im)`,
  SIMP_TAC[linear; o_THM; COMPLEX_CMUL; IM_ADD; IM_MUL_CX; CX_MUL; CX_ADD]);;

let CONTINUOUS_AT_CX_IM = prove
 (`!z. (Cx o Im) continuous at z`,
  SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_CX_IM]);;

let CONTINUOUS_ON_CX_IM = prove
 (`!s. (Cx o Im) continuous_on s`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CX_IM]);;

(* ------------------------------------------------------------------------- *)
(* Complex differentiability.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_complex_derivative",(12,"right"));;
parse_as_infix ("complex_differentiable",(12,"right"));;
parse_as_infix ("holomorphic_on",(12,"right"));;

let has_complex_derivative = new_definition
 `(f has_complex_derivative f') net <=> (f has_derivative (\x. f' * x)) net`;;

let complex_differentiable = new_definition
 `f complex_differentiable net <=> ?f'. (f has_complex_derivative f') net`;;

let complex_derivative = new_definition
 `complex_derivative f x = @f'. (f has_complex_derivative f') (at x)`;;

let higher_complex_derivative = define
 `higher_complex_derivative 0 f = f /\
  (!n. higher_complex_derivative (SUC n) f =
                complex_derivative (higher_complex_derivative n f))`;;

let holomorphic_on = new_definition
 `f holomorphic_on s <=>
     !x. x IN s ==> ?f'. (f has_complex_derivative f') (at x within s)`;;

let HOLOMORPHIC_ON_EMPTY = prove
 (`!f. f holomorphic_on {}`,
  REWRITE_TAC[holomorphic_on; NOT_IN_EMPTY]);;

let HOLOMORPHIC_ON_DIFFERENTIABLE = prove
 (`!f s. f holomorphic_on s <=>
         !x. x IN s ==> f complex_differentiable (at x within s)`,
  REWRITE_TAC[holomorphic_on; complex_differentiable]);;

let HOLOMORPHIC_ON_OPEN = prove
 (`!f s. open s
         ==> (f holomorphic_on s <=>
              !x. x IN s ==> ?f'. (f has_complex_derivative f') (at x))`,
  REWRITE_TAC[holomorphic_on; has_complex_derivative] THEN
  REWRITE_TAC[has_derivative_at; has_derivative_within] THEN
  SIMP_TAC[LIM_WITHIN_OPEN]);;

let HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_WITHIN = prove
 (`!f s x. f holomorphic_on s /\ x IN s
           ==> f complex_differentiable (at x within s)`,
  MESON_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE]);;

let HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT = prove
 (`!f s x. f holomorphic_on s /\ open s /\ x IN s
           ==> f complex_differentiable (at x)`,
  MESON_TAC[HOLOMORPHIC_ON_OPEN; complex_differentiable]);;

let HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT = prove
 (`!f f' x. (f has_complex_derivative f') (at x) ==> f continuous at x`,
  REWRITE_TAC[has_complex_derivative] THEN
  MESON_TAC[differentiable; DIFFERENTIABLE_IMP_CONTINUOUS_AT]);;

let HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_WITHIN = prove
 (`!f f' x s. (f has_complex_derivative f') (at x within s)
              ==> f continuous (at x within s)`,
  REWRITE_TAC[has_complex_derivative] THEN
  MESON_TAC[differentiable; DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE = prove
 (`!net f. f complex_differentiable net ==> f differentiable net`,
  SIMP_TAC[complex_differentiable; differentiable; has_complex_derivative] THEN
  MESON_TAC[]);;

let COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_AT = prove
 (`!f x. f complex_differentiable at x ==> f continuous at x`,
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_IMP_CONTINUOUS_AT; complex_differentiable]);;

let COMPLEX_DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN = prove
 (`!f x s. f complex_differentiable (at x within s)
           ==> f continuous (at x within s)`,
  MESON_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE;
            DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN]);;

let HOLOMORPHIC_ON_IMP_CONTINUOUS_ON = prove
 (`!f s. f holomorphic_on s ==> f continuous_on s`,
  REWRITE_TAC[holomorphic_on; CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  REWRITE_TAC[has_complex_derivative] THEN
  MESON_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_WITHIN; differentiable]);;

let HOLOMORPHIC_ON_SUBSET = prove
 (`!f s t. f holomorphic_on s /\ t SUBSET s ==> f holomorphic_on t`,
  REWRITE_TAC[holomorphic_on; has_complex_derivative] THEN
  MESON_TAC[SUBSET; HAS_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET = prove
 (`!f s t x. (f has_complex_derivative f') (at x within s) /\ t SUBSET s
             ==> (f has_complex_derivative f') (at x within t)`,
  REWRITE_TAC[has_complex_derivative; HAS_DERIVATIVE_WITHIN_SUBSET]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_SUBSET = prove
 (`!f s t. f complex_differentiable (at x within s) /\ t SUBSET s
           ==> f complex_differentiable (at x within t)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_COMPLEX_DERIVATIVE_AT_WITHIN = prove
 (`!f f' x s. (f has_complex_derivative f') (at x)
              ==> (f has_complex_derivative f') (at x within s)`,
  REWRITE_TAC[has_complex_derivative; HAS_DERIVATIVE_AT_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN = prove
 (`!f f' a s.
         a IN s /\ open s
         ==> ((f has_complex_derivative f') (at a within s) <=>
              (f has_complex_derivative f') (at a))`,
  REWRITE_TAC[has_complex_derivative; HAS_DERIVATIVE_WITHIN_OPEN]);;

let COMPLEX_DIFFERENTIABLE_AT_WITHIN = prove
 (`!f s z. f complex_differentiable (at z)
           ==> f complex_differentiable (at z within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN = prove
 (`!f f' g x s d.
       &0 < d /\ x IN s /\
       (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
       (f has_complex_derivative f') (at x within s)
       ==> (g has_complex_derivative f') (at x within s)`,
  REWRITE_TAC[has_complex_derivative] THEN
  MESON_TAC[HAS_DERIVATIVE_TRANSFORM_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = prove
  (`!f g f' s z. open s /\ z IN s /\ (!w. w IN s ==> f w = g w) /\
                 (f has_complex_derivative f') (at z)
                 ==> (g has_complex_derivative f') (at z)`,
   REWRITE_TAC [has_complex_derivative] THEN
   ASM_MESON_TAC [HAS_DERIVATIVE_TRANSFORM_WITHIN_OPEN]);;

let HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT = prove
 (`!f f' g x d.
       &0 < d /\ (!x'. dist (x',x) < d ==> f x' = g x') /\
       (f has_complex_derivative f') (at x)
       ==> (g has_complex_derivative f') (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN; IN_UNIV]);;

let HAS_COMPLEX_DERIVATIVE_ZERO_CONSTANT = prove
 (`!f s.
        convex s /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x within s))
        ==> ?c. !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[has_complex_derivative; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_DERIVATIVE_ZERO_CONSTANT]);;

let HAS_COMPLEX_DERIVATIVE_ZERO_UNIQUE = prove
 (`!f s c a.
        convex s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x within s))
        ==> !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[has_complex_derivative; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_DERIVATIVE_ZERO_UNIQUE]);;

let HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_CONSTANT = prove
 (`!f s.
        open s /\ connected s /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x))
        ==> ?c. !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[has_complex_derivative; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_DERIVATIVE_ZERO_CONNECTED_CONSTANT]);;

let HAS_COMPLEX_DERIVATIVE_ZERO_CONNECTED_UNIQUE = prove
 (`!f s c a.
        open s /\ connected s /\ a IN s /\ f a = c /\
        (!x. x IN s ==> (f has_complex_derivative Cx(&0)) (at x))
        ==> !x. x IN s ==> f(x) = c`,
  REWRITE_TAC[has_complex_derivative; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_DERIVATIVE_ZERO_CONNECTED_UNIQUE]);;

let COMPLEX_DIFF_CHAIN_WITHIN = prove
 (`!f g f' g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at (f x) within (IMAGE f s))
        ==> ((g o f) has_complex_derivative (g' * f'))(at x within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_complex_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC[o_DEF; COMPLEX_MUL_ASSOC]);;

let COMPLEX_DIFF_CHAIN_AT = prove
 (`!f g f' g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at (f x))
        ==> ((g o f) has_complex_derivative (g' * f')) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  ASM_MESON_TAC[COMPLEX_DIFF_CHAIN_WITHIN; SUBSET_UNIV;
                HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET]);;

let HAS_COMPLEX_DERIVATIVE_CHAIN = prove
 (`!P f g.
        (!x. P x ==> (g has_complex_derivative g'(x)) (at x))
        ==> (!x s. (f has_complex_derivative f') (at x within s) /\ P(f x)
                   ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                       (at x within s)) /\
            (!x. (f has_complex_derivative f') (at x) /\ P(f x)
                 ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                     (at x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM o_DEF] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  ASM_MESON_TAC[COMPLEX_DIFF_CHAIN_WITHIN; COMPLEX_DIFF_CHAIN_AT;
                HAS_COMPLEX_DERIVATIVE_AT_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV = prove
 (`!f g. (!x. (g has_complex_derivative g'(x)) (at x))
         ==> (!x s. (f has_complex_derivative f') (at x within s)
                    ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                        (at x within s)) /\
             (!x. (f has_complex_derivative f') (at x)
                  ==> ((\x. g(f x)) has_complex_derivative f' * g'(f x))
                      (at x))`,
  MP_TAC(SPEC `\x:complex. T` HAS_COMPLEX_DERIVATIVE_CHAIN) THEN SIMP_TAC[]);;

let COMPLEX_DERIVATIVE_UNIQUE_AT = prove
 (`!f z f' f''.
        (f has_complex_derivative f') (at z) /\
        (f has_complex_derivative f'') (at z)
        ==> f' = f''`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_complex_derivative] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  DISCH_THEN(MP_TAC o C AP_THM `Cx(&1)`) THEN
  REWRITE_TAC[COMPLEX_MUL_RID]);;

let HIGHER_COMPLEX_DERIVATIVE_1 = prove
 (`!f z. higher_complex_derivative 1 f z = complex_derivative f z`,
  REWRITE_TAC[num_CONV `1`; higher_complex_derivative]);;

(* ------------------------------------------------------------------------- *)
(* A more direct characterization.                                           *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_WITHIN = prove
 (`!f s a. (f has_complex_derivative f') (at a within s) <=>
           ((\x. (f(x) - f(a)) / (x - a)) --> f') (at a within s)`,
  REWRITE_TAC[has_complex_derivative; has_derivative_within] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
  GEN_REWRITE_TAC RAND_CONV [LIM_NULL] THEN
  REWRITE_TAC[LIM_WITHIN; dist; VECTOR_SUB_RZERO; NORM_MUL] THEN
  REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN SIMP_TAC[COMPLEX_FIELD
  `~(x:complex = a) ==> y / (x - a) - z = inv(x - a) * (y - z * (x - a))`] THEN
  REWRITE_TAC[REAL_ABS_INV; COMPLEX_NORM_MUL; REAL_ABS_NORM;
         COMPLEX_NORM_INV; VECTOR_ARITH `a:complex - (b + c) = a - b - c`]);;

let HAS_COMPLEX_DERIVATIVE_AT = prove
 (`!f a. (f has_complex_derivative f') (at a) <=>
         ((\x. (f(x) - f(a)) / (x - a)) --> f') (at a)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetical combining theorems.                                          *)
(* ------------------------------------------------------------------------- *)

let HAS_DERIVATIVE_COMPLEX_CMUL = prove
 (`!net c. ((\x. c * x) has_derivative (\x. c * x)) net`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[LINEAR_COMPLEX_MUL]);;

let HAS_COMPLEX_DERIVATIVE_LINEAR = prove
 (`!net c. ((\x. c * x) has_complex_derivative c) net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_complex_derivative] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING);;

let HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN = prove
 (`!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. c * f(x)) has_complex_derivative (c * f')) (at x within s)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`at ((f:complex->complex) x) within (IMAGE f s)`; `c:complex`]
    HAS_COMPLEX_DERIVATIVE_LINEAR) THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP COMPLEX_DIFF_CHAIN_WITHIN) THEN
  REWRITE_TAC[o_DEF]);;

let HAS_COMPLEX_DERIVATIVE_LMUL_AT = prove
 (`!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. c * f(x)) has_complex_derivative (c * f')) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN = prove
 (`!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. f(x) * c) has_complex_derivative (f' * c)) (at x within s)`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_RMUL_AT = prove
 (`!f f' c x.
        (f has_complex_derivative f') (at x)
        ==> ((\x. f(x) * c) has_complex_derivative (f' * c)) (at x)`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_LMUL_AT]);;

let HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN = prove
 (`!f f' c x s.
        (f has_complex_derivative f') (at x within s)
        ==> ((\x. f(x) / c) has_complex_derivative (f' / c)) (at x within s)`,
  SIMP_TAC[complex_div; HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_CDIV_AT = prove
 (`!f f' c x s.
        (f has_complex_derivative f') (at x)
        ==> ((\x. f(x) / c) has_complex_derivative (f' / c)) (at x)`,
  SIMP_TAC[complex_div; HAS_COMPLEX_DERIVATIVE_RMUL_AT]);;

let HAS_COMPLEX_DERIVATIVE_ID = prove
 (`!net. ((\x. x) has_complex_derivative Cx(&1)) net`,
  REWRITE_TAC[has_complex_derivative; HAS_DERIVATIVE_ID; COMPLEX_MUL_LID]);;

let HAS_COMPLEX_DERIVATIVE_CONST = prove
 (`!c net. ((\x. c) has_complex_derivative Cx(&0)) net`,
  REWRITE_TAC[has_complex_derivative; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_DERIVATIVE_CONST]);;

let HAS_COMPLEX_DERIVATIVE_NEG = prove
 (`!f f' net. (f has_complex_derivative f') net
            ==> ((\x. --(f(x))) has_complex_derivative (--f')) net`,
  SIMP_TAC[has_complex_derivative; COMPLEX_MUL_LNEG; HAS_DERIVATIVE_NEG]);;

let HAS_COMPLEX_DERIVATIVE_ADD = prove
 (`!f f' g g' net.
        (f has_complex_derivative f') net /\ (g has_complex_derivative g') net
        ==> ((\x. f(x) + g(x)) has_complex_derivative (f' + g')) net`,
  SIMP_TAC[has_complex_derivative; COMPLEX_ADD_RDISTRIB; HAS_DERIVATIVE_ADD]);;

let HAS_COMPLEX_DERIVATIVE_SUB = prove
 (`!f f' g g' net.
        (f has_complex_derivative f') net /\ (g has_complex_derivative g') net
        ==> ((\x. f(x) - g(x)) has_complex_derivative (f' - g')) net`,
  SIMP_TAC[has_complex_derivative; COMPLEX_SUB_RDISTRIB; HAS_DERIVATIVE_SUB]);;

let HAS_COMPLEX_DERIVATIVE_MUL_WITHIN = prove
 (`!f f' g g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at x within s)
        ==> ((\x. f(x) * g(x)) has_complex_derivative
             (f(x) * g' + f' * g(x))) (at x within s)`,
  REPEAT GEN_TAC THEN SIMP_TAC[has_complex_derivative] THEN
  DISCH_THEN(MP_TAC o C CONJ BILINEAR_COMPLEX_MUL) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_BILINEAR_WITHIN) THEN
  MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  CONV_TAC COMPLEX_RING);;

let HAS_COMPLEX_DERIVATIVE_MUL_AT = prove
 (`!f f' g g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at x)
        ==> ((\x. f(x) * g(x)) has_complex_derivative
             (f(x) * g' + f' * g(x))) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_MUL_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_POW_WITHIN = prove
 (`!f f' x s n. (f has_complex_derivative f') (at x within s)
                ==> ((\x. f(x) pow n) has_complex_derivative
                     (Cx(&n) * f(x) pow (n - 1) * f')) (at x within s)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[complex_pow] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_CONST; COMPLEX_MUL_LZERO] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_WITHIN) THEN
  REWRITE_TAC[SUC_SUB1] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
  BINOP_TAC THEN REWRITE_TAC[COMPLEX_MUL_AC; GSYM REAL_OF_NUM_SUC] THEN
  SPEC_TAC(`n:num`,`n:num`) THEN REWRITE_TAC[CX_ADD] THEN INDUCT_TAC THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[SUC_SUB1; complex_pow] THEN
  CONV_TAC COMPLEX_FIELD);;

let HAS_COMPLEX_DERIVATIVE_POW_AT = prove
 (`!f f' x n. (f has_complex_derivative f') (at x)
              ==> ((\x. f(x) pow n) has_complex_derivative
                   (Cx(&n) * f(x) pow (n - 1) * f')) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_POW_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_INV_BASIC = prove
 (`!x. ~(x = Cx(&0))
         ==> ((inv) has_complex_derivative (--inv(x pow 2))) (at x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[has_complex_derivative; has_derivative_at] THEN
  REWRITE_TAC[LINEAR_COMPLEX_MUL; COMPLEX_VEC_0] THEN
  MATCH_MP_TAC LIM_TRANSFORM_AWAY_AT THEN
  MAP_EVERY EXISTS_TAC
   [`\y. inv(norm(y - x)) % inv(x pow 2 * y) * (y - x) pow 2`; `Cx(&0)`] THEN
  ASM_REWRITE_TAC[COMPLEX_CMUL] THEN CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  SUBGOAL_THEN `((\y. inv(x pow 2 * y) * (y - x)) --> Cx(&0)) (at x)`
  MP_TAC THENL
   [LIM_TAC THEN POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN REWRITE_TAC[LIM_AT] THEN
  REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_INV; COMPLEX_NORM_POW] THEN
  REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_INV; REAL_ABS_NORM] THEN
  REPLICATE_TAC 2 (AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC) THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MATCH_MP_TAC(MESON[]
   `(p ==> x = y) ==> ((p ==> x < e) <=> (p ==> y < e))`) THEN
  MAP_EVERY ABBREV_TAC
   [`n = norm(x' - x:complex)`;
    `m = inv (norm(x:complex) pow 2 * norm(x':complex))`] THEN
  CONV_TAC REAL_FIELD);;

let HAS_COMPLEX_DERIVATIVE_INV_WITHIN = prove
 (`!f f' x s. (f has_complex_derivative f') (at x within s) /\
              ~(f x = Cx(&0))
              ==> ((\x. inv(f(x))) has_complex_derivative (--f' / f(x) pow 2))
                  (at x within s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(g = Cx(&0)) ==> --f / g pow 2 = --inv(g pow 2) * f`] THEN
  MATCH_MP_TAC COMPLEX_DIFF_CHAIN_WITHIN THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_AT_WITHIN THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_INV_BASIC]);;

let HAS_COMPLEX_DERIVATIVE_INV_AT = prove
 (`!f f' x. (f has_complex_derivative f') (at x) /\
            ~(f x = Cx(&0))
            ==> ((\x. inv(f(x))) has_complex_derivative (--f' / f(x) pow 2))
                (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_INV_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_DIV_WITHIN = prove
 (`!f f' g g' x s.
        (f has_complex_derivative f') (at x within s) /\
        (g has_complex_derivative g') (at x within s) /\
        ~(g(x) = Cx(&0))
        ==> ((\x. f(x) / g(x)) has_complex_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (at x within s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN MP_TAC th) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_INV_WITHIN) THEN
  UNDISCH_TAC `(f has_complex_derivative f') (at x within s)` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_WITHIN) THEN
  REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_FIELD);;

let HAS_COMPLEX_DERIVATIVE_DIV_AT = prove
 (`!f f' g g' x.
        (f has_complex_derivative f') (at x) /\
        (g has_complex_derivative g') (at x) /\
        ~(g(x) = Cx(&0))
        ==> ((\x. f(x) / g(x)) has_complex_derivative
             (f' * g(x) - f(x) * g') / g(x) pow 2) (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIV_WITHIN]);;

let HAS_COMPLEX_DERIVATIVE_VSUM = prove
 (`!f net s.
         FINITE s /\ (!a. a IN s ==> (f a has_complex_derivative f' a) net)
         ==> ((\x. vsum s (\a. f a x)) has_complex_derivative (vsum s f'))
             net`,
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; has_complex_derivative] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP HAS_DERIVATIVE_VSUM) THEN
  REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Same thing just for complex differentiability.                            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIFFERENTIABLE_LINEAR = prove
 (`(\z. c * z) complex_differentiable p`,
  REWRITE_TAC [complex_differentiable] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_LINEAR]);;

let COMPLEX_DIFFERENTIABLE_CONST = prove
 (`!c net. (\z. c) complex_differentiable net`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_CONST]);;

let COMPLEX_DIFFERENTIABLE_ID = prove
 (`!net. (\z. z) complex_differentiable net`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_ID]);;

let COMPLEX_DIFFERENTIABLE_NEG = prove
 (`!f net.
        f complex_differentiable net
        ==> (\z. --(f z)) complex_differentiable net`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_NEG]);;

let COMPLEX_DIFFERENTIABLE_ADD = prove
 (`!f g net.
        f complex_differentiable net /\
        g complex_differentiable net
        ==> (\z. f z + g z) complex_differentiable net`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_ADD]);;

let COMPLEX_DIFFERENTIABLE_SUB = prove
 (`!f g net.
        f complex_differentiable net /\
        g complex_differentiable net
        ==> (\z. f z - g z) complex_differentiable net`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_SUB]);;

let COMPLEX_DIFFERENTIABLE_INV_WITHIN = prove
 (`!f z s.
        f complex_differentiable (at z within s) /\ ~(f z = Cx(&0))
        ==> (\z. inv(f z)) complex_differentiable (at z within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_INV_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_MUL_WITHIN = prove
 (`!f g z s.
        f complex_differentiable (at z within s) /\
        g complex_differentiable (at z within s)
        ==> (\z. f z * g z) complex_differentiable (at z within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_MUL_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_DIV_WITHIN = prove
 (`!f g z s.
        f complex_differentiable (at z within s) /\
        g complex_differentiable (at z within s) /\
        ~(g z = Cx(&0))
        ==> (\z. f z / g z) complex_differentiable (at z within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_DIV_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_POW_WITHIN = prove
 (`!f n z s.
        f complex_differentiable (at z within s)
        ==> (\z. f z pow n) complex_differentiable (at z within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_POW_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN = prove
 (`!f k:A->bool z s.
        FINITE k /\
        (!i. i IN k ==> f i complex_differentiable (at z within s))
        ==> (\z. cproduct k (\i. f i z)) complex_differentiable
            (at z within s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_DIFFERENTIABLE_CONST; FORALL_IN_INSERT;
           ETA_AX; COMPLEX_DIFFERENTIABLE_MUL_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN = prove
 (`!f g x s d.
        &0 < d /\
        x IN s /\
        (!x'. x' IN s /\ dist (x',x) < d ==> f x' = g x') /\
        f complex_differentiable (at x within s)
        ==> g complex_differentiable (at x within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN]);;

let HOLOMORPHIC_TRANSFORM = prove
 (`!f g s. (!x. x IN s ==> f x = g x) /\ f holomorphic_on s
           ==> g holomorphic_on s`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[holomorphic_on; GSYM complex_differentiable] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_WITHIN THEN
  MAP_EVERY EXISTS_TAC [`f:complex->complex`; `&1`] THEN
  ASM_SIMP_TAC[REAL_LT_01]);;

let HOLOMORPHIC_EQ = prove
 (`!f g s. (!x. x IN s ==> f x = g x)
           ==> (f holomorphic_on s <=> g holomorphic_on s)`,
  MESON_TAC[HOLOMORPHIC_TRANSFORM]);;

let COMPLEX_DIFFERENTIABLE_INV_AT = prove
 (`!f z.
        f complex_differentiable at z /\ ~(f z = Cx(&0))
        ==> (\z. inv(f z)) complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_INV_AT]);;

let COMPLEX_DIFFERENTIABLE_MUL_AT = prove
 (`!f g z.
        f complex_differentiable at z /\
        g complex_differentiable at z
        ==> (\z. f z * g z) complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_MUL_AT]);;

let COMPLEX_DIFFERENTIABLE_DIV_AT = prove
 (`!f g z.
        f complex_differentiable at z /\
        g complex_differentiable at z /\
        ~(g z = Cx(&0))
        ==> (\z. f z / g z) complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_DIV_AT]);;

let COMPLEX_DIFFERENTIABLE_POW_AT = prove
 (`!f n z.
        f complex_differentiable at z
        ==> (\z. f z pow n) complex_differentiable at z`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_POW_AT]);;

let COMPLEX_DIFFERENTIABLE_CPRODUCT_AT = prove
 (`!f k:A->bool z.
        FINITE k /\
        (!i. i IN k ==> f i complex_differentiable (at z))
        ==> (\z. cproduct k (\i. f i z)) complex_differentiable (at z)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_DIFFERENTIABLE_CONST; FORALL_IN_INSERT;
           ETA_AX; COMPLEX_DIFFERENTIABLE_MUL_AT]);;

let COMPLEX_DIFFERENTIABLE_TRANSFORM_AT = prove
 (`!f g x d.
        &0 < d /\
        (!x'. dist (x',x) < d ==> f x' = g x') /\
        f complex_differentiable at x
        ==> g complex_differentiable at x`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_TRANSFORM_AT]);;

let COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN = prove
 (`!f g x s.
         f complex_differentiable (at x within s) /\
         g complex_differentiable (at (f x) within IMAGE f s)
         ==> (g o f) complex_differentiable (at x within s)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[COMPLEX_DIFF_CHAIN_WITHIN]);;

let COMPLEX_DIFFERENTIABLE_COMPOSE_AT = prove
 (`!f g x s.
         f complex_differentiable (at x) /\
         g complex_differentiable (at (f x))
         ==> (g o f) complex_differentiable (at x)`,
  REWRITE_TAC[complex_differentiable] THEN
  MESON_TAC[COMPLEX_DIFF_CHAIN_AT]);;

let COMPLEX_DIFFERENTIABLE_WITHIN_OPEN = prove
 (`!f a s.
        a IN s /\ open s
        ==> (f complex_differentiable at a within s <=>
             f complex_differentiable at a)`,
  SIMP_TAC[complex_differentiable; HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN]);;

(* ------------------------------------------------------------------------- *)
(* Same again for being holomorphic on a set.                                *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_LINEAR = prove
 (`!s c. (\w. c * w) holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_LINEAR]);;

let HOLOMORPHIC_ON_CONST = prove
 (`!c s. (\z. c) holomorphic_on s`,
  REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_CONST]);;

let HOLOMORPHIC_ON_ID = prove
 (`!s. (\z. z) holomorphic_on s`,
  REWRITE_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_ID]);;

let HOLOMORPHIC_ON_COMPOSE = prove
 (`!f g s. f holomorphic_on s /\ g holomorphic_on (IMAGE f s)
           ==> (g o f) holomorphic_on s`,
  SIMP_TAC[holomorphic_on; GSYM complex_differentiable; FORALL_IN_IMAGE] THEN
  MESON_TAC[COMPLEX_DIFFERENTIABLE_COMPOSE_WITHIN]);;

let HOLOMORPHIC_ON_NEG = prove
 (`!f s. f holomorphic_on s ==> (\z. --(f z)) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_NEG]);;

let HOLOMORPHIC_ON_ADD = prove
 (`!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z + g z) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_ADD]);;

let HOLOMORPHIC_ON_SUB = prove
 (`!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z - g z) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_SUB]);;

let HOLOMORPHIC_ON_MUL = prove
 (`!f g s.
        f holomorphic_on s /\ g holomorphic_on s
        ==> (\z. f z * g z) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_MUL_WITHIN]);;

let HOLOMORPHIC_ON_LMUL = prove
 (`!f c s. f holomorphic_on s ==> (\x. c * f x) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST]);;

let HOLOMORPHIC_ON_RMUL = prove
 (`!f c s. f holomorphic_on s ==> (\x. f x * c) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST]);;

let HOLOMORPHIC_ON_INV = prove
 (`!f s. f holomorphic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
         ==> (\z. inv(f z)) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_INV_WITHIN]);;

let HOLOMORPHIC_ON_DIV = prove
 (`!f g s.
        f holomorphic_on s /\ g holomorphic_on s /\
        (!z. z IN s ==> ~(g z = Cx(&0)))
        ==> (\z. f z / g z) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_DIV_WITHIN]);;

let HOLOMORPHIC_ON_POW = prove
 (`!f s n. f holomorphic_on s ==> (\z. (f z) pow n) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE; COMPLEX_DIFFERENTIABLE_POW_WITHIN]);;

let HOLOMORPHIC_ON_VSUM = prove
 (`!f s k. FINITE k /\ (!a. a IN k ==> (f a) holomorphic_on s)
           ==> (\x. vsum k (\a. f a x)) holomorphic_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[VSUM_CLAUSES] THEN
  SIMP_TAC[HOLOMORPHIC_ON_CONST; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
  ASM_SIMP_TAC[ETA_AX]);;

let HOLOMORPHIC_ON_CPRODUCT = prove
 (`!f k:A->bool s.
        FINITE k /\
        (!i. i IN k ==> f i holomorphic_on s)
        ==> (\z. cproduct k (\i. f i z)) holomorphic_on s`,
  SIMP_TAC[HOLOMORPHIC_ON_DIFFERENTIABLE;
           COMPLEX_DIFFERENTIABLE_CPRODUCT_WITHIN]);;

let HOLOMORPHIC_ON_COMPOSE_GEN = prove
 (`!f g s t. f holomorphic_on s /\ g holomorphic_on t /\
             (!z. z IN s ==> f z IN t)
             ==>  g o f holomorphic_on s`,
  REWRITE_TAC [holomorphic_on] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:complex->complex) s SUBSET t` MP_TAC THENL
   [ASM SET_TAC []; ASM_MESON_TAC [HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET;
                                   COMPLEX_DIFF_CHAIN_WITHIN]]);;

(* ------------------------------------------------------------------------- *)
(* Same again for the actual derivative function.                            *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_DERIVATIVE = prove
 (`!f f' x. (f has_complex_derivative f') (at x)
                ==> complex_derivative f x = f'`,
  REWRITE_TAC[complex_derivative] THEN
  MESON_TAC[COMPLEX_DERIVATIVE_UNIQUE_AT]);;

let HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE = prove
 (`!f x. (f has_complex_derivative (complex_derivative f x)) (at x) <=>
         f complex_differentiable at x`,
  REWRITE_TAC[complex_differentiable; complex_derivative] THEN MESON_TAC[]);;

let COMPLEX_DIFFERENTIABLE_COMPOSE = prove
 (`!f g z. f complex_differentiable at z /\ g complex_differentiable at (f z)
          ==> (g o f) complex_differentiable at z`,
  REWRITE_TAC [complex_differentiable] THEN
  MESON_TAC [COMPLEX_DIFF_CHAIN_AT]);;

let COMPLEX_DERIVATIVE_CHAIN = prove
 (`!f g z. f complex_differentiable at z /\ g complex_differentiable at (f z)
           ==> complex_derivative (g o f) z =
               complex_derivative g (f z) * complex_derivative f z`,
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_DERIVATIVE; COMPLEX_DIFF_CHAIN_AT;
             HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_LINEAR = prove
 (`!c. complex_derivative (\w. c * w) = \z. c`,
  REWRITE_TAC [FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC [HAS_COMPLEX_DERIVATIVE_LINEAR]);;

let COMPLEX_DERIVATIVE_ID = prove
 (`complex_derivative (\w.w) = \z. Cx(&1)`,
  REWRITE_TAC [FUN_EQ_THM] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_DERIVATIVE; HAS_COMPLEX_DERIVATIVE_ID]);;

let COMPLEX_DERIVATIVE_CONST = prove
 (`!c. complex_derivative (\w.c) = \z. Cx(&0)`,
  REWRITE_TAC [FUN_EQ_THM] THEN
  MESON_TAC [HAS_COMPLEX_DERIVATIVE_DERIVATIVE;
             HAS_COMPLEX_DERIVATIVE_CONST]);;

let COMPLEX_DERIVATIVE_ADD = prove
 (`!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w + g w) z =
               complex_derivative f z + complex_derivative g z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_ADD;
                HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_SUB = prove
 (`!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w - g w) z =
               complex_derivative f z - complex_derivative g z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_SUB;
                HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_MUL = prove
 (`!f g z. f complex_differentiable at z /\ g complex_differentiable at z
           ==> complex_derivative (\w. f w * g w) z =
               f z * complex_derivative g z + complex_derivative f z * g z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_MUL_AT;
                HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_LMUL = prove
 (`!f c z. f complex_differentiable at z
             ==> complex_derivative (\w. c * f w) z =
                 c * complex_derivative f z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_LMUL_AT;
                HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_RMUL = prove
 (`!f c z. f complex_differentiable at z
           ==> complex_derivative (\w. f w * c) z =
               complex_derivative f z * c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  ASM_SIMP_TAC [HAS_COMPLEX_DERIVATIVE_RMUL_AT;
                HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN = prove
 (`!f g s z. open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s /\
             (!w. w IN s ==> f w = g w)
             ==> complex_derivative f z = complex_derivative g z`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
  ASM_MESON_TAC[HAS_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN;
                HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT;
                HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE]);;

let COMPLEX_DERIVATIVE_COMPOSE_LINEAR = prove
 (`!f c z. f complex_differentiable at (c * z)
           ==> complex_derivative (\w. f (c * w)) z =
               c * complex_derivative f (c * z)`,
  SIMP_TAC
    [COMPLEX_MUL_SYM; REWRITE_RULE [o_DEF; COMPLEX_DIFFERENTIABLE_ID;
                   COMPLEX_DIFFERENTIABLE_LINEAR;
                   COMPLEX_DERIVATIVE_LINEAR]
     (SPECL [`\w:complex. c * w`] COMPLEX_DERIVATIVE_CHAIN)]);;

(* ------------------------------------------------------------------------- *)
(* Caratheodory characterization.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT = prove
 (`!f f' z.
        (f has_complex_derivative f') (at z) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g continuous at z /\ g(z) = f'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_RING `w' - z':complex = a <=> w' = z' + a`] THEN
  SIMP_TAC[GSYM FUN_EQ_THM; HAS_COMPLEX_DERIVATIVE_AT; CONTINUOUS_AT] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\w. if w = z then f':complex else (f(w) - f(z)) / (w - z)` THEN
    ASM_SIMP_TAC[FUN_EQ_THM; COND_RAND; COND_RATOR; COMPLEX_SUB_REFL] THEN
    CONV_TAC COMPLEX_FIELD;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_SIMP_TAC[COMPLEX_RING `(z + a) - (z + b * (w - w)):complex = a`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      LIM_TRANSFORM)) THEN
    SIMP_TAC[LIM_CONST; COMPLEX_VEC_0; COMPLEX_FIELD
     `~(w = z) ==> x - (x * (w - z)) / (w - z) = Cx(&0)`]]);;

let HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN = prove
 (`!f f' z s.
        (f has_complex_derivative f') (at z within s) <=>
        ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\
            g continuous (at z within s) /\ g(z) = f'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COMPLEX_RING `w' - z':complex = a <=> w' = z' + a`] THEN
  SIMP_TAC[GSYM FUN_EQ_THM; HAS_COMPLEX_DERIVATIVE_WITHIN;
           CONTINUOUS_WITHIN] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `\w. if w = z then f':complex else (f(w) - f(z)) / (w - z)` THEN
    ASM_SIMP_TAC[FUN_EQ_THM; COND_RAND; COND_RATOR; COMPLEX_SUB_REFL] THEN
    CONV_TAC COMPLEX_FIELD;
    FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_SIMP_TAC[COMPLEX_RING `(z + a) - (z + b * (w - w)):complex = a`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      LIM_TRANSFORM)) THEN
    SIMP_TAC[LIM_CONST; COMPLEX_VEC_0; COMPLEX_FIELD
     `~(w = z) ==> x - (x * (w - z)) / (w - z) = Cx(&0)`]]);;

let COMPLEX_DIFFERENTIABLE_CARATHEODORY_AT = prove
 (`!f z. f complex_differentiable at z <=>
         ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g continuous at z`,
  SIMP_TAC[complex_differentiable; HAS_COMPLEX_DERIVATIVE_CARATHEODORY_AT] THEN
  MESON_TAC[]);;

let COMPLEX_DIFFERENTIABLE_CARATHEODORY_WITHIN = prove
 (`!f z s.
      f complex_differentiable (at z within s) <=>
      ?g. (!w. f(w) - f(z) = g(w) * (w - z)) /\ g continuous (at z within s)`,
  SIMP_TAC[complex_differentiable;
           HAS_COMPLEX_DERIVATIVE_CARATHEODORY_WITHIN] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A slightly stronger, more traditional notion of analyticity on a set.     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("analytic_on",(12,"right"));;

let analytic_on = new_definition
 `f analytic_on s <=>
      !x. x IN s ==> ?e. &0 < e /\ f holomorphic_on ball(x,e)`;;

let ANALYTIC_IMP_HOLOMORPHIC = prove
 (`!f s. f analytic_on s ==> f holomorphic_on s`,
  REWRITE_TAC[analytic_on; holomorphic_on] THEN
  SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL] THEN
  MESON_TAC[HAS_COMPLEX_DERIVATIVE_AT_WITHIN; CENTRE_IN_BALL]);;

let ANALYTIC_ON_OPEN = prove
 (`!f s. open s ==> (f analytic_on s <=> f holomorphic_on s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[ANALYTIC_IMP_HOLOMORPHIC] THEN
  REWRITE_TAC[analytic_on; holomorphic_on] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_WITHIN_OPEN; OPEN_BALL] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  REWRITE_TAC[SUBSET] THEN MESON_TAC[CENTRE_IN_BALL]);;

let ANALYTIC_ON_IMP_DIFFERENTIABLE_AT = prove
 (`!f s x. f analytic_on s /\ x IN s ==> f complex_differentiable (at x)`,
  SIMP_TAC[analytic_on; HOLOMORPHIC_ON_OPEN; OPEN_BALL;
           complex_differentiable] THEN
  MESON_TAC[CENTRE_IN_BALL]);;

let ANALYTIC_ON_SUBSET = prove
 (`!f s t. f analytic_on s /\ t SUBSET s ==> f analytic_on t`,
  REWRITE_TAC[analytic_on; SUBSET] THEN MESON_TAC[]);;

let ANALYTIC_ON_UNION = prove
 (`!f s t. f analytic_on (s UNION t) <=> f analytic_on s /\ f analytic_on t`,
  REWRITE_TAC [analytic_on; IN_UNION] THEN MESON_TAC[]);;

let ANALYTIC_ON_UNIONS = prove
 (`!f s. f analytic_on (UNIONS s) <=> (!t. t IN s ==> f analytic_on t)`,
  REWRITE_TAC [analytic_on; IN_UNIONS] THEN MESON_TAC[]);;

let ANALYTIC_ON_HOLOMORPHIC = prove
 (`!f s. f analytic_on s <=> ?t. open t /\ s SUBSET t /\ f holomorphic_on t`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `?t. open t /\ s SUBSET t /\ f analytic_on t` THEN CONJ_TAC THENL
   [EQ_TAC THENL
    [DISCH_TAC THEN EXISTS_TAC `UNIONS {u | open u /\ f analytic_on u}` THEN
     SIMP_TAC [IN_ELIM_THM; OPEN_UNIONS; ANALYTIC_ON_UNIONS] THEN
     REWRITE_TAC [SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
     ASM_MESON_TAC [analytic_on; ANALYTIC_ON_OPEN; OPEN_BALL; CENTRE_IN_BALL];
     MESON_TAC [ANALYTIC_ON_SUBSET]];
    MESON_TAC [ANALYTIC_ON_OPEN]]);;

let ANALYTIC_ON_LINEAR = prove
 (`!s c. (\w. c * w) analytic_on s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ANALYTIC_ON_HOLOMORPHIC; HOLOMORPHIC_ON_LINEAR] THEN
  EXISTS_TAC `(:complex)` THEN REWRITE_TAC [OPEN_UNIV; SUBSET_UNIV]);;

let ANALYTIC_ON_CONST = prove
 (`!c s. (\z. c) analytic_on s`,
  REWRITE_TAC[analytic_on; HOLOMORPHIC_ON_CONST] THEN MESON_TAC[REAL_LT_01]);;

let ANALYTIC_ON_ID = prove
 (`!s. (\z. z) analytic_on s`,
  REWRITE_TAC[analytic_on; HOLOMORPHIC_ON_ID] THEN MESON_TAC[REAL_LT_01]);;

let ANALYTIC_ON_COMPOSE = prove
 (`!f g s. f analytic_on s /\ g analytic_on (IMAGE f s)
           ==> (g o f) analytic_on s`,
  REWRITE_TAC[analytic_on; FORALL_IN_IMAGE] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "f") (LABEL_TAC "g")) THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  REMOVE_THEN "f" (MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOLOMORPHIC_ON_IMP_CONTINUOUS_ON) THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL; CONTINUOUS_AT_BALL] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min (d:real) k` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
  CONJ_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THENL
   [EXISTS_TAC `ball(z:complex,d)`;
    EXISTS_TAC `ball((f:complex->complex) z,e)`] THEN
  ASM_REWRITE_TAC[BALL_MIN_INTER; INTER_SUBSET] THEN ASM SET_TAC[]);;

let ANALYTIC_ON_COMPOSE_GEN = prove
 (`!f g s t. f analytic_on s /\ g analytic_on t /\ (!z. z IN s ==> f z IN t)
             ==> g o f analytic_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANALYTIC_ON_COMPOSE THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC ANALYTIC_ON_SUBSET THEN ASM SET_TAC[]);;

let ANALYTIC_ON_NEG = prove
 (`!f s. f analytic_on s ==> (\z. --(f z)) analytic_on s`,
  SIMP_TAC[analytic_on] THEN MESON_TAC[HOLOMORPHIC_ON_NEG]);;

let ANALYTIC_ON_ADD = prove
 (`!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z + g z) analytic_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[analytic_on] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d:real`) (X_CHOOSE_TAC `e:real`)) THEN
  EXISTS_TAC `min (d:real) e` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; BALL_MIN_INTER; IN_INTER] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; INTER_SUBSET]);;

let ANALYTIC_ON_SUB = prove
 (`!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z - g z) analytic_on s`,
  SIMP_TAC[complex_sub; ANALYTIC_ON_ADD; ANALYTIC_ON_NEG]);;

let ANALYTIC_ON_MUL = prove
 (`!f g s.
        f analytic_on s /\ g analytic_on s ==> (\z. f z * g z) analytic_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[analytic_on] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  GEN_TAC THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d:real`) (X_CHOOSE_TAC `e:real`)) THEN
  EXISTS_TAC `min (d:real) e` THEN
  ASM_REWRITE_TAC[REAL_LT_MIN; BALL_MIN_INTER; IN_INTER] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; INTER_SUBSET]);;

let ANALYTIC_ON_INV = prove
 (`!f s. f analytic_on s /\ (!z. z IN s ==> ~(f z = Cx(&0)))
         ==> (\z. inv(f z)) analytic_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[analytic_on] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [analytic_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e. &0 < e /\ !y:complex. dist(z,y) < e ==> ~(f y = Cx(&0))`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_OPEN_AVOID THEN
    EXISTS_TAC `ball(z:complex,d)` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON; CENTRE_IN_BALL; OPEN_BALL];
    REWRITE_TAC[GSYM IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min (d:real) e` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN
    ASM_SIMP_TAC[BALL_MIN_INTER; IN_INTER] THEN
    ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; INTER_SUBSET]]);;

let ANALYTIC_ON_DIV = prove
 (`!f g s.
        f analytic_on s /\ g analytic_on s /\
        (!z. z IN s ==> ~(g z = Cx(&0)))
        ==> (\z. f z / g z) analytic_on s`,
  SIMP_TAC[complex_div; ANALYTIC_ON_MUL; ANALYTIC_ON_INV]);;

let ANALYTIC_ON_POW = prove
 (`!f s n. f analytic_on s ==> (\z. (f z) pow n) analytic_on s`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[complex_pow] THEN
  ASM_SIMP_TAC[ANALYTIC_ON_CONST; ANALYTIC_ON_MUL]);;

let ANALYTIC_ON_VSUM = prove
 (`!f s k. FINITE k /\ (!a. a IN k ==> (f a) analytic_on s)
           ==> (\x. vsum k (\a. f a x)) analytic_on s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN SIMP_TAC[VSUM_CLAUSES] THEN
  SIMP_TAC[ANALYTIC_ON_CONST; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ANALYTIC_ON_ADD THEN
  ASM_SIMP_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* The case of analyticity at a point.                                       *)
(* ------------------------------------------------------------------------- *)

let ANALYTIC_AT_BALL = prove
 (`!f z. f analytic_on {z} <=> ?e. &0<e /\ f holomorphic_on ball (z,e)`,
  REWRITE_TAC [analytic_on; IN_SING] THEN MESON_TAC []);;

let ANALYTIC_AT = prove
 (`!f z. f analytic_on {z} <=> ?s. open s /\ z IN s /\ f holomorphic_on s`,
  REWRITE_TAC [ANALYTIC_ON_HOLOMORPHIC; SING_SUBSET]);;

let ANALYTIC_ON_ANALYTIC_AT = prove
 (`!f s. f analytic_on s <=> !z. z IN s ==> f analytic_on {z}`,
  REWRITE_TAC [ANALYTIC_AT_BALL; analytic_on]);;

let ANALYTIC_AT_TWO = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z} <=>
    ?s. open s /\ z IN s /\ f holomorphic_on s /\ g holomorphic_on s`,
  REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HOLOMORPHIC_ON_SUBSET; OPEN_INTER; INTER_SUBSET; IN_INTER]);;

let ANALYTIC_AT_ADD = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> (\w. f w + g w) analytic_on {z}`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HOLOMORPHIC_ON_ADD]);;

let ANALYTIC_AT_SUB = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> (\w. f w - g w) analytic_on {z}`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HOLOMORPHIC_ON_SUB]);;

let ANALYTIC_AT_MUL = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z}

     ==> (\w. f w * g w) analytic_on {z}`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HOLOMORPHIC_ON_MUL]);;

let ANALYTIC_AT_POW = prove
 (`!f n z. f analytic_on {z}
     ==> (\w. f w pow n) analytic_on {z}`,
  REWRITE_TAC [ANALYTIC_AT] THEN MESON_TAC [HOLOMORPHIC_ON_POW]);;

(* ------------------------------------------------------------------------- *)
(* Combining theorems for derivative with analytic_at {z} hypotheses.        *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DERIVATIVE_ADD_AT = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w + g w) z =
           complex_derivative f z + complex_derivative g z`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_ADD THEN
  ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]);;

let COMPLEX_DERIVATIVE_SUB_AT = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w - g w) z =
           complex_derivative f z - complex_derivative g z`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_SUB THEN
  ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]);;

let COMPLEX_DERIVATIVE_MUL_AT = prove
 (`!f g z. f analytic_on {z} /\ g analytic_on {z}
     ==> complex_derivative (\w. f w * g w) z =
           f z * complex_derivative g z + complex_derivative f z * g z`,
  REWRITE_TAC [ANALYTIC_AT_TWO] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_MUL THEN
  ASM_MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT]);;

let COMPLEX_DERIVATIVE_LMUL_AT = prove
 (`!f c z. f analytic_on {z}
    ==> complex_derivative (\w. c * f w) z = c * complex_derivative f z`,
  REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT; COMPLEX_DERIVATIVE_LMUL]);;

let COMPLEX_DERIVATIVE_RMUL_AT = prove
 (`!f c z. f analytic_on {z}
    ==> complex_derivative (\w. f w * c) z = complex_derivative f z * c`,
  REWRITE_TAC [ANALYTIC_AT] THEN
  MESON_TAC [HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT; COMPLEX_DERIVATIVE_RMUL]);;

(* ------------------------------------------------------------------------- *)
(* A composition lemma for functions of mixed type.                          *)
(* ------------------------------------------------------------------------- *)

let HAS_VECTOR_DERIVATIVE_REAL_COMPLEX = prove
 (`(f has_complex_derivative f') (at(Cx(drop a)))
   ==> ((\x. f(Cx(drop x))) has_vector_derivative f') (at a)`,
  REWRITE_TAC[has_complex_derivative; has_vector_derivative] THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN MP_TAC(ISPECL
   [`\x. Cx(drop x)`; `f:complex->complex`;
    `\x. Cx(drop x)`; `\x:complex. f' * x`; `a:real^1`] DIFF_CHAIN_AT) THEN
  REWRITE_TAC[o_DEF; COMPLEX_MUL_SYM; IMP_CONJ] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
  REWRITE_TAC[linear; DROP_ADD; DROP_CMUL; CX_ADD; CX_MUL; COMPLEX_CMUL]);;

let DIFFERENTIABLE_REAL_COMPLEX = prove
 (`!f a. f complex_differentiable at (Cx(drop a))
         ==> (\x. f(Cx(drop x))) differentiable at a`,
  REWRITE_TAC[complex_differentiable; VECTOR_DERIVATIVE_WORKS] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[vector_derivative] THEN
  ASM_MESON_TAC[HAS_VECTOR_DERIVATIVE_REAL_COMPLEX]);;

(* ------------------------------------------------------------------------- *)
(* Complex differentiation of sequences and series.                          *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_SEQUENCE = prove
 (`!s f f' g'.
         convex s /\
         (!n x. x IN s
                ==> (f n has_complex_derivative f' n x) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s ==> norm (f' n x - g' x) <= e) /\
         (?x l. x IN s /\ ((\n. f n x) --> l) sequentially)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) --> g x) sequentially /\
                         (g has_complex_derivative g' x) (at x within s)`,
  REWRITE_TAC[has_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SEQUENCE THEN
  EXISTS_TAC `\n x h:complex. (f':num->complex->complex) n x * h` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; COMPLEX_NORM_MUL] THEN
  ASM_MESON_TAC[REAL_LE_RMUL; NORM_POS_LE]);;

let HAS_COMPLEX_DERIVATIVE_SERIES = prove
 (`!s f f' g' k.
         convex s /\
         (!n x. x IN s
                ==> (f n has_complex_derivative f' n x) (at x within s)) /\
         (!e. &0 < e
              ==> ?N. !n x. n >= N /\ x IN s
                            ==> norm(vsum (k INTER (0..n)) (\i. f' i x) - g' x)
                                    <= e) /\
         (?x l. x IN s /\ ((\n. f n x) sums l) k)
         ==> ?g. !x. x IN s
                     ==> ((\n. f n x) sums g x) k /\
                         (g has_complex_derivative g' x) (at x within s)`,
  REWRITE_TAC[has_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_SERIES THEN
  EXISTS_TAC `\n x h:complex. (f':num->complex->complex) n x * h` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  SIMP_TAC[GSYM COMPLEX_SUB_RDISTRIB; VSUM_COMPLEX_RMUL; FINITE_NUMSEG;
           FINITE_INTER; COMPLEX_NORM_MUL] THEN
  ASM_MESON_TAC[REAL_LE_RMUL; NORM_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Bound theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_DIFFERENTIABLE_BOUND = prove
 (`!f f' s B.
        convex s /\
        (!x. x IN s ==> (f has_complex_derivative f'(x)) (at x within s) /\
                        norm(f' x) <= B)
        ==> !x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_complex_derivative] THEN
  STRIP_TAC THEN MATCH_MP_TAC DIFFERENTIABLE_BOUND THEN
  EXISTS_TAC `\x:complex h. f' x * h` THEN ASM_SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\h. (f':complex->complex) x * h` ONORM) THEN
  REWRITE_TAC[LINEAR_COMPLEX_MUL] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  GEN_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  ASM_MESON_TAC[REAL_LE_RMUL; NORM_POS_LE]);;

(* ------------------------------------------------------------------------- *)
(* Inverse function theorem for complex derivatives.                         *)
(* ------------------------------------------------------------------------- *)

let HAS_COMPLEX_DERIVATIVE_INVERSE_BASIC = prove
 (`!f g f' t y.
        (f has_complex_derivative f') (at (g y)) /\
        ~(f' = Cx(&0)) /\
        g continuous at y /\
        open t /\
        y IN t /\
        (!z. z IN t ==> f (g z) = z)
        ==> (g has_complex_derivative inv(f')) (at y)`,
  REWRITE_TAC[has_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_BASIC THEN
  MAP_EVERY EXISTS_TAC
   [`f:complex->complex`; `\x:complex. f' * x`; `t:complex->bool`] THEN
  ASM_REWRITE_TAC[LINEAR_COMPLEX_MUL; FUN_EQ_THM; o_THM; I_THM] THEN
  UNDISCH_TAC `~(f' = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG = prove
 (`!f g f' s x.
         open s /\
         x IN s /\
         f continuous_on s /\
         (!x. x IN s ==> g (f x) = x) /\
         (f has_complex_derivative f') (at x) /\
         ~(f' = Cx(&0))
         ==> (g has_complex_derivative inv(f')) (at (f x))`,
  REWRITE_TAC[has_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG THEN
  MAP_EVERY EXISTS_TAC [`\x:complex. f' * x`; `s:complex->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  UNDISCH_TAC `~(f' = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

let HAS_COMPLEX_DERIVATIVE_INVERSE_STRONG_X = prove
 (`!f g f' s y.
        open s /\ (g y) IN s /\ f continuous_on s /\
        (!x. x IN s ==> (g(f(x)) = x)) /\
        (f has_complex_derivative f') (at (g y)) /\ ~(f' = Cx(&0)) /\
        f(g y) = y
        ==> (g has_complex_derivative inv(f')) (at y)`,
  REWRITE_TAC[has_complex_derivative] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_DERIVATIVE_INVERSE_STRONG_X THEN MAP_EVERY EXISTS_TAC
   [`f:complex->complex`; `\x:complex. f' * x`; `s:complex->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  UNDISCH_TAC `~(f' = Cx(&0))` THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-Riemann condition and relation to conformal.                       *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_BASIS = prove
 (`basis 1 = Cx(&1) /\ basis 2 = ii`,
  SIMP_TAC[CART_EQ; FORALL_2; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; RE_CX; IM_CX] THEN
  REWRITE_TAC[ii] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let CAUCHY_RIEMANN = prove
 (`!f z. f complex_differentiable at z <=>
         f differentiable at z  /\
         (jacobian f (at z))$1$1 = (jacobian f (at z))$2$2 /\
         (jacobian f (at z))$1$2 = --((jacobian f (at z))$2$1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_differentiable] THEN EQ_TAC THENL
   [REWRITE_TAC[has_complex_derivative] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':complex` ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[differentiable]; ALL_TAC] THEN
    REWRITE_TAC[jacobian] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
    SIMP_TAC[matrix; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
    REWRITE_TAC[COMPLEX_BASIS; GSYM RE_DEF; GSYM IM_DEF; ii] THEN
    SIMPLE_COMPLEX_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC
     `complex(jacobian (f:complex->complex) (at z)$1$1,
              jacobian f (at z)$2$1)` THEN
    REWRITE_TAC[has_complex_derivative] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [JACOBIAN_WORKS]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; DIMINDEX_2; SUM_2; ARITH;
                 FORALL_2; FUN_EQ_THM; LAMBDA_BETA] THEN
    REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; IM; RE; complex_mul] THEN
    REAL_ARITH_TAC]);;

let COMPLEX_DERIVATIVE_JACOBIAN = prove
 (`!f z.
        f complex_differentiable (at z)
        ==> complex_derivative f z =
            complex(jacobian f (at z)$1$1,jacobian f (at z)$2$1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`f:complex->complex`; `z:complex`] THEN
  ASM_REWRITE_TAC[HAS_COMPLEX_DERIVATIVE_DIFFERENTIABLE] THEN
  REWRITE_TAC[has_complex_derivative] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [CAUCHY_RIEMANN]) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [JACOBIAN_WORKS]) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; DIMINDEX_2; SUM_2; ARITH;
               FORALL_2; FUN_EQ_THM; LAMBDA_BETA] THEN
  REWRITE_TAC[GSYM RE_DEF; GSYM IM_DEF; IM; RE; complex_mul] THEN
  REAL_ARITH_TAC);;

let COMPLEX_DIFFERENTIABLE_EQ_CONFORMAL = prove
 (`!f z.
      f complex_differentiable at z /\ ~(complex_derivative f z = Cx(&0)) <=>
      f differentiable at z  /\
      ?a. ~(a = &0) /\ rotation_matrix (a %% jacobian f (at z))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[COMPLEX_DIFFERENTIABLE_IMP_DIFFERENTIABLE;
                 COMPLEX_DERIVATIVE_JACOBIAN] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM DOT_EQ_0] THEN
    REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF; RE; IM; GSYM REAL_POW_2] THEN
    REWRITE_TAC[RE_DEF; IM_DEF; ROTATION_MATRIX_2] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CAUCHY_RIEMANN]) THEN
    ASM_REWRITE_TAC[MATRIX_CMUL_COMPONENT] THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_MUL_RNEG; GSYM REAL_ADD_LDISTRIB;
                REAL_ARITH `(a * x:real) pow 2 = a pow 2 * x pow 2`] THEN
    EXISTS_TAC
     `inv(sqrt(jacobian (f:complex->complex) (at z)$2$2 pow 2 +
               jacobian f (at z)$2$1 pow 2))` THEN
    MATCH_MP_TAC(REAL_FIELD
     `x pow 2 = y /\ ~(y = &0)
      ==> ~(inv x = &0) /\ inv(x) pow 2 * y = &1`) THEN
    ASM_SIMP_TAC[SQRT_POW_2; REAL_LE_ADD; REAL_LE_POW_2];
    REWRITE_TAC[ROTATION_MATRIX_2; MATRIX_CMUL_COMPONENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_RNEG; REAL_EQ_MUL_LCANCEL] THEN
    STRIP_TAC THEN MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[CAUCHY_RIEMANN]; DISCH_TAC] THEN
    ASM_SIMP_TAC[COMPLEX_DERIVATIVE_JACOBIAN] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM DOT_EQ_0] THEN
    REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF; RE; IM; GSYM REAL_POW_2] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP
     (REAL_RING `(a * x) pow 2 + (a * y) pow 2 = &1
                 ==> ~(x pow 2 + y pow 2 = &0)`)) THEN
    ASM_REWRITE_TAC[RE_DEF; IM_DEF]]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let complex_differentiation_theorems = ref [];;

let add_complex_differentiation_theorems =
  let ETA_THM = prove
   (`(f has_complex_derivative f') net <=>
     ((\x. f x) has_complex_derivative f') net`,
    REWRITE_TAC[ETA_AX]) in
  let ETA_TWEAK =
    PURE_REWRITE_RULE [IMP_CONJ] o
    GEN_REWRITE_RULE (LAND_CONV o ONCE_DEPTH_CONV) [ETA_THM] o
    SPEC_ALL in
  fun l -> complex_differentiation_theorems :=
              !complex_differentiation_theorems @ map ETA_TWEAK l;;

add_complex_differentiation_theorems
 [HAS_COMPLEX_DERIVATIVE_LMUL_WITHIN; HAS_COMPLEX_DERIVATIVE_LMUL_AT;
  HAS_COMPLEX_DERIVATIVE_RMUL_WITHIN; HAS_COMPLEX_DERIVATIVE_RMUL_AT;
  HAS_COMPLEX_DERIVATIVE_CDIV_WITHIN; HAS_COMPLEX_DERIVATIVE_CDIV_AT;
  HAS_COMPLEX_DERIVATIVE_ID;
  HAS_COMPLEX_DERIVATIVE_CONST;
  HAS_COMPLEX_DERIVATIVE_NEG;
  HAS_COMPLEX_DERIVATIVE_ADD;
  HAS_COMPLEX_DERIVATIVE_SUB;
  HAS_COMPLEX_DERIVATIVE_MUL_WITHIN; HAS_COMPLEX_DERIVATIVE_MUL_AT;
  HAS_COMPLEX_DERIVATIVE_DIV_WITHIN; HAS_COMPLEX_DERIVATIVE_DIV_AT;
  HAS_COMPLEX_DERIVATIVE_POW_WITHIN; HAS_COMPLEX_DERIVATIVE_POW_AT;
  HAS_COMPLEX_DERIVATIVE_INV_WITHIN; HAS_COMPLEX_DERIVATIVE_INV_AT];;

let GEN_COMPLEX_DIFF_CONV ths =
  let partfn tm = let l,r = dest_comb tm in mk_pair(lhand l,r)
  and is_deriv = can (term_match [] `(f has_complex_derivative f') net`)
  and ths' =
   unions(mapfilter (CONJUNCTS o REWRITE_RULE[FORALL_AND_THM] o
                     MATCH_MP HAS_COMPLEX_DERIVATIVE_CHAIN_UNIV) ths) in
  let rec COMPLEX_DIFF_CONV tm =
    try tryfind (fun th -> PART_MATCH partfn th (partfn tm))
                (!complex_differentiation_theorems @ ths')
    with Failure _ ->
        let ith = tryfind (fun th ->
         PART_MATCH (partfn o repeat (snd o dest_imp)) th (partfn tm))
                    (!complex_differentiation_theorems @ ths') in
        COMPLEX_DIFF_ELIM ith
  and COMPLEX_DIFF_ELIM th =
    let tm = concl th in
    if not(is_imp tm) then th else
    let t = lhand tm in
    if not(is_deriv t) then UNDISCH th
    else COMPLEX_DIFF_ELIM (MATCH_MP th (COMPLEX_DIFF_CONV t)) in
  COMPLEX_DIFF_CONV;;

let COMPLEX_DIFF_CONV = GEN_COMPLEX_DIFF_CONV [];;

(* ------------------------------------------------------------------------- *)
(* Hence a tactic.                                                           *)
(* ------------------------------------------------------------------------- *)

let GEN_COMPLEX_DIFF_TAC ths =
  let pth = MESON[]
   `(f has_complex_derivative f') net
    ==> f' = g'
        ==> (f has_complex_derivative g') net` in
  W(fun (asl,w) -> let th = MATCH_MP pth (GEN_COMPLEX_DIFF_CONV ths w) in
       MATCH_MP_TAC(repeat (GEN_REWRITE_RULE I [IMP_IMP]) (DISCH_ALL th)));;

let COMPLEX_DIFF_TAC = GEN_COMPLEX_DIFF_TAC [];;

let COMPLEX_DIFFERENTIABLE_TAC =
  let DISCH_FIRST th = DISCH (hd(hyp th)) th in
  GEN_REWRITE_TAC I [complex_differentiable] THEN
  W(fun (asl,w) ->
        let th = COMPLEX_DIFF_CONV(snd(dest_exists w)) in
        let f' = rand(rator(concl th)) in
        EXISTS_TAC f' THEN
        (if hyp th = [] then MATCH_ACCEPT_TAC th else
         let th' = repeat (GEN_REWRITE_RULE I [IMP_IMP] o DISCH_FIRST)
                          (DISCH_FIRST th) in
         MATCH_MP_TAC th'));;

(* ------------------------------------------------------------------------- *)
(* A kind of complex Taylor theorem.                                         *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_TAYLOR = prove
 (`!f n s B.
    convex s /\
    (!i x. x IN s /\ i <= n
           ==> ((f i) has_complex_derivative f (i + 1) x) (at x within s)) /\
    (!x. x IN s ==> norm(f (n + 1) x) <= B)
    ==> !w z. w IN s /\ z IN s
              ==> norm(f 0 z -
                       vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))
                  <= B * norm(z - w) pow (n + 1) / &(FACT n)`,
  let lemma = prove
   (`!f:num->real^N.
          vsum (0..n) f = f 0 - f (n + 1) + vsum (0..n) (\i. f (i + 1))`,
    REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF] `(f:num->real^N) o (\i. i + 1)`)] THEN
    ASM_SIMP_TAC[GSYM VSUM_IMAGE; EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM NUMSEG_OFFSET_IMAGE] THEN
    SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM ADD1] THEN
    REWRITE_TAC[ARITH; ARITH_RULE `1 <= SUC n`] THEN VECTOR_ARITH_TAC) in
  REPEAT STRIP_TAC THEN MP_TAC(SPECL
   [`(\w. vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))`;
    `\w. (f:num->complex->complex) (n + 1) w *
         (z - w) pow n / Cx(&(FACT n))`; `segment[w:complex,z]`;
    `B * norm(z - w:complex) pow n / &(FACT n)`]
   COMPLEX_DIFFERENTIABLE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_SEGMENT] THEN X_GEN_TAC `u:complex` THEN
    DISCH_TAC THEN SUBGOAL_THEN `(u:complex) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT; SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
                  COMPLEX_NORM_POW; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_POS; REAL_POW_LE] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_MESON_TAC[SEGMENT_BOUND; NORM_SUB]] THEN
    MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_WITHIN_SUBSET THEN
    EXISTS_TAC `s:complex->bool` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]] THEN
    SUBGOAL_THEN
     `((\u. vsum (0..n) (\i. f i u * (z - u) pow i / Cx (&(FACT i))))
       has_complex_derivative
       vsum (0..n) (\i. f i u * (-- Cx(&i) * (z - u) pow (i - 1)) /
                                Cx(&(FACT i)) +
                        f (i + 1) u * (z - u) pow i / Cx (&(FACT i))))
      (at u within s)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_WITHIN THEN
      ASM_SIMP_TAC[ETA_AX] THEN W(MP_TAC o COMPLEX_DIFF_CONV o snd) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[VSUM_ADD_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lemma] THEN
    REWRITE_TAC[GSYM VSUM_ADD_NUMSEG; GSYM COMPLEX_ADD_ASSOC] THEN
    REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[GSYM ADD1; FACT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[COMPLEX_RING
      `--a * b * inv a * c:complex = --(a * inv a) * b * c`] THEN
    SIMP_TAC[COMPLEX_MUL_RINV; CX_INJ; REAL_ARITH `~(&n + &1 = &0)`] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_ADD_LINV; GSYM COMPLEX_VEC_0; VSUM_0] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ADD_RID] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_NEG_0] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`z:complex`; `w:complex`]) THEN ANTS_TAC THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN MATCH_MP_TAC EQ_IMP THEN
  BINOP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_POW_ADD; real_div; REAL_POW_1] THEN REAL_ARITH_TAC] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; complex_pow; FACT; COMPLEX_DIV_1] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH `x * Cx(&1) + y = x <=> y = Cx(&0)`] THEN
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC[complex_pow; complex_div; COMPLEX_MUL_LZERO;
                  COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL; COMPLEX_VEC_0] THEN
  REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The simplest special case.                                                *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_MVT = prove
 (`!f f' s B.
        convex s /\
        (!z. z IN s ==> (f has_complex_derivative f' z) (at z within s)) /\
        (!z. z IN s ==> norm (f' z) <= B)
        ==> !w z. w IN s /\ z IN s ==> norm (f z - f w) <= B * norm (z - w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`(\n. if n = 0 then f else f'):num->complex->complex`;
                `0`; `s:complex->bool`; `B:real`] COMPLEX_TAYLOR) THEN
  SIMP_TAC[NUMSEG_SING; VSUM_SING; LE; ARITH] THEN
  REWRITE_TAC[complex_pow; REAL_POW_1; FACT; REAL_DIV_1] THEN
  ASM_SIMP_TAC[COMPLEX_DIV_1; COMPLEX_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Something more like the traditional MVT for real components.              *)
(* Could, perhaps should, sharpen this to derivatives inside the segment.    *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_MVT_LINE = prove
 (`!f f' w z.
        (!u. u IN segment[w,z]
             ==> (f has_complex_derivative f'(u)) (at u))
        ==> ?u. u IN segment[w,z] /\ Re(f z) - Re(f w) = Re(f'(u) * (z - w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(lift o Re) o (f:complex->complex) o
     (\t. (&1 - drop t) % w + drop t % z)`;
    `\u. (lift o Re) o
         (\h. (f':complex->complex)((&1 - drop u) % w + drop u % z) * h) o
         (\t. drop t % (z - w))`;
    `vec 0:real^1`; `vec 1:real^1`]
        MVT_VERY_SIMPLE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DROP_VEC; REAL_POS] THEN
    X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; LIFT_ADD; RE_ADD; LIFT_CMUL; RE_CMUL; o_DEF]] THEN
    MATCH_MP_TAC DIFF_CHAIN_AT THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `(&1 - t) % w + t % z = w + t % (z - w)`] THEN
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o ABS_CONV)
        [GSYM VECTOR_ADD_LID] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN
      REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
      CONJ_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM has_complex_derivative] THEN
    FIRST_X_ASSUM MATCH_MP_TAC;
    REWRITE_TAC[o_THM; GSYM LIFT_SUB; LIFT_EQ; DROP_VEC; VECTOR_SUB_RZERO] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(&1 - drop t) % w + drop t % z:complex`] THEN
  ASM_REWRITE_TAC[segment; IN_ELIM_THM] THEN
  EXISTS_TAC `drop t` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
  REWRITE_TAC[DROP_VEC]);;

let COMPLEX_TAYLOR_MVT = prove
 (`!f w z n.
    (!i x. x IN segment[w,z] /\ i <= n
           ==> ((f i) has_complex_derivative f (i + 1) x) (at x))
    ==> ?u. u IN segment[w,z] /\
            Re(f 0 z) =
            Re(vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))) +
               (f (n + 1) u * (z - u) pow n / Cx (&(FACT n))) * (z - w))`,
  let lemma = prove
   (`!f:num->real^N.
          vsum (0..n) f = f 0 - f (n + 1) + vsum (0..n) (\i. f (i + 1))`,
    REWRITE_TAC[GSYM(REWRITE_CONV[o_DEF] `(f:num->real^N) o (\i. i + 1)`)] THEN
    ASM_SIMP_TAC[GSYM VSUM_IMAGE; EQ_ADD_RCANCEL; FINITE_NUMSEG] THEN
    REWRITE_TAC[GSYM NUMSEG_OFFSET_IMAGE] THEN
    SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0] THEN
    REWRITE_TAC[VSUM_CLAUSES_NUMSEG; GSYM ADD1] THEN
    REWRITE_TAC[ARITH; ARITH_RULE `1 <= SUC n`] THEN VECTOR_ARITH_TAC) in
  REPEAT STRIP_TAC THEN MP_TAC(SPECL
   [`(\w. vsum (0..n) (\i. f i w * (z - w) pow i / Cx(&(FACT i))))`;
    `\w. (f:num->complex->complex) (n + 1) w *
         (z - w) pow n / Cx(&(FACT n))`;
    `w:complex`; `z:complex`]
    COMPLEX_MVT_LINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_SEGMENT] THEN X_GEN_TAC `u:complex` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `((\u. vsum (0..n) (\i. f i u * (z - u) pow i / Cx (&(FACT i))))
       has_complex_derivative
       vsum (0..n) (\i. f i u * (-- Cx(&i) * (z - u) pow (i - 1)) /
                                Cx(&(FACT i)) +
                        f (i + 1) u * (z - u) pow i / Cx (&(FACT i))))
      (at u)`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_VSUM THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_MUL_AT THEN
      ASM_SIMP_TAC[ETA_AX] THEN W(MP_TAC o COMPLEX_DIFF_CONV o snd) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    AP_TERM_TAC THEN REWRITE_TAC[VSUM_ADD_NUMSEG] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [lemma] THEN
    REWRITE_TAC[GSYM VSUM_ADD_NUMSEG; GSYM COMPLEX_ADD_ASSOC] THEN
    REWRITE_TAC[ADD_SUB] THEN REWRITE_TAC[GSYM ADD1; FACT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC; GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
    REWRITE_TAC[complex_div; COMPLEX_INV_MUL; GSYM COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[COMPLEX_RING
      `--a * b * inv a * c:complex = --(a * inv a) * b * c`] THEN
    SIMP_TAC[COMPLEX_MUL_RINV; CX_INJ; REAL_ARITH `~(&n + &1 = &0)`] THEN
    REWRITE_TAC[COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_MUL_LID] THEN
    REWRITE_TAC[COMPLEX_ADD_LINV; GSYM COMPLEX_VEC_0; VSUM_0] THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ADD_RID] THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_NEG_0] THEN
    CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:complex` THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[RE_ADD] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[REAL_ADD_SYM] REAL_EQ_SUB_RADD] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  SIMP_TAC[VSUM_CLAUSES_LEFT; LE_0; complex_pow; FACT; COMPLEX_DIV_1] THEN
  REWRITE_TAC[COMPLEX_MUL_RID; RE_ADD] THEN
  MATCH_MP_TAC(REAL_ARITH `Re x = &0 ==> y = y + Re x`) THEN
  SIMP_TAC[RE_VSUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC SUM_EQ_0_NUMSEG THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[COMPLEX_SUB_REFL; complex_pow; complex_div] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; RE_CX]);;

(* ------------------------------------------------------------------------- *)
(* Further useful properties of complex conjugation.                         *)
(* ------------------------------------------------------------------------- *)

let LIM_CNJ = prove
 (`!net f l. ((\x. cnj(f x)) --> cnj l) net <=> (f --> l) net`,
  REWRITE_TAC[LIM; dist; GSYM CNJ_SUB; COMPLEX_NORM_CNJ]);;

let SUMS_CNJ = prove
 (`!net f l. ((\x. cnj(f x)) sums cnj l) net <=> (f sums l) net`,
  SIMP_TAC[sums; LIM_CNJ; GSYM CNJ_VSUM; FINITE_INTER_NUMSEG]);;

let CONTINUOUS_WITHIN_CNJ = prove
 (`!s z. cnj continuous (at z within s)`,
  SIMP_TAC[LINEAR_CONTINUOUS_WITHIN; LINEAR_CNJ]);;

let CONTINUOUS_AT_CNJ = prove
 (`!z. cnj continuous (at z)`,
  SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_CNJ]);;

let CONTINUOUS_ON_CNJ = prove
 (`!s. cnj continuous_on s`,
  SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_CNJ]);;

(* ------------------------------------------------------------------------- *)
(* Some limit theorems about real part of real series etc.                   *)
(* ------------------------------------------------------------------------- *)

let REAL_LIM = prove
 (`!net:(A)net f l.
        (f --> l) net /\ ~(trivial_limit net) /\
        (?b. (?a. netord net a b) /\ !a. netord net a b ==> real(f a))
        ==> real l`,
  REWRITE_TAC[IM_DEF; real] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LIM_COMPONENT_EQ THEN
  REWRITE_TAC[eventually; DIMINDEX_2; ARITH] THEN ASM_MESON_TAC[]);;

let REAL_LIM_SEQUENTIALLY = prove
 (`!f l. (f --> l) sequentially /\ (?N. !n. n >= N ==> real(f n))
         ==> real l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ISPEC `sequentially` REAL_LIM) THEN
  REWRITE_TAC[SEQUENTIALLY; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  ASM_MESON_TAC[GE_REFL]);;

let REAL_SERIES = prove
 (`!f l s. (f sums l) s /\ (!n. real(f n)) ==> real l`,
  REWRITE_TAC[sums] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LIM_SEQUENTIALLY THEN
  EXISTS_TAC `\n. vsum(s INTER (0..n)) f :complex` THEN
  ASM_SIMP_TAC[REAL_VSUM; FINITE_INTER; FINITE_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Often convenient to use comparison with real limit of complex type.       *)
(* ------------------------------------------------------------------------- *)

let LIM_NULL_COMPARISON_COMPLEX = prove
 (`!net:(A)net f g.
        eventually (\x. norm(f x) <= norm(g x)) net /\
        (g --> Cx(&0)) net
        ==> (f --> Cx(&0)) net`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:(A)net` LIM_NULL_COMPARISON) THEN
  EXISTS_TAC `norm o (g:A->complex)` THEN
  ASM_REWRITE_TAC[o_THM; GSYM LIM_NULL_NORM]);;

let LIM_NULL_COMPARISON_COMPLEX_RE = prove
 (`!net:(A)net f g.
        eventually (\x. norm(f x) <= Re(g x)) net /\
        (g --> Cx(&0)) net
        ==> (f --> Cx(&0)) net`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `net:(A)net` LIM_NULL_COMPARISON_COMPLEX) THEN
  EXISTS_TAC `g:A->complex` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] EVENTUALLY_MONO)) THEN
  REWRITE_TAC[] THEN
  MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_ABS_LE; REAL_LE_TRANS]);;

let SERIES_COMPARISON_COMPLEX = prove
 (`!f:num->real^N g s.
        summable s g /\
        (!n. n IN s ==> real(g n) /\ &0 <= Re(g n)) /\
        (?N. !n. n >= N /\ n IN s ==> norm(f n) <= norm(g n))
        ==> summable s f`,
  REPEAT GEN_TAC THEN REWRITE_TAC[summable] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC SERIES_COMPARISON THEN
  EXISTS_TAC `\n. norm((g:num->complex) n)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lift(Re l)` THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\i:num. lift(Re(g i))` THEN
  ASM_SIMP_TAC[REAL_NORM_POS; o_DEF] THEN
  REWRITE_TAC[RE_DEF] THEN MATCH_MP_TAC SERIES_COMPONENT THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

let SERIES_COMPARISON_UNIFORM_COMPLEX = prove
 (`!f:A->num->real^N g P s.
        summable s g /\
        (!n. n IN s ==> real(g n) /\ &0 <= Re(g n)) /\
        (?N. !n x. N <= n /\ n IN s /\ P x ==> norm(f x n) <= norm(g n))
        ==> ?l. !e. &0 < e
                    ==> ?N. !n x. N <= n /\ P x
                                  ==> dist(vsum(s INTER (0..n)) (f x),l x) <
                                       e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[summable] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MATCH_MP_TAC SERIES_COMPARISON_UNIFORM THEN
  EXISTS_TAC `\n. norm((g:num->complex) n)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `l:complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lift(Re l)` THEN MATCH_MP_TAC SUMS_EQ THEN
  EXISTS_TAC `\i:num. lift(Re(g i))` THEN
  ASM_SIMP_TAC[REAL_NORM_POS; o_DEF] THEN
  REWRITE_TAC[RE_DEF] THEN MATCH_MP_TAC SERIES_COMPONENT THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH]);;

let SUMMABLE_SUBSET_COMPLEX = prove
 (`!x s t. (!n. n IN s ==> real(x n) /\ &0 <= Re(x n)) /\
           summable s x /\ t SUBSET s
           ==> summable t x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_SUBSET THEN
  EXISTS_TAC `s:num->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `x:num->complex` THEN ASM_REWRITE_TAC[] THEN
  MESON_TAC[REAL_LE_REFL; NORM_0; NORM_POS_LE]);;

let SERIES_ABSCONV_IMP_CONV = prove
 (`!x:num->real^N k. summable k (\n. Cx(norm(x n))) ==> summable k x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n:num. Cx(norm(x n:real^N))` THEN
  ASM_REWRITE_TAC[REAL_CX; RE_CX; NORM_POS_LE; COMPLEX_NORM_CX] THEN
  REWRITE_TAC[REAL_ABS_NORM; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Complex-valued geometric series.                                          *)
(* ------------------------------------------------------------------------- *)

let SUMS_GP = prove
 (`!n z. norm(z) < &1
         ==> ((\k. z pow k) sums (z pow n / (Cx(&1) - z))) (from n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SERIES_FROM; VSUM_GP] THEN
  ASM_CASES_TAC `z = Cx(&1)` THENL
   [ASM_MESON_TAC[COMPLEX_NORM_NUM; REAL_LT_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THEN
  EXISTS_TAC `\m. (z pow n - z pow SUC m) / (Cx (&1) - z)` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `n:num` THEN SIMP_TAC[GSYM NOT_LE];
    MATCH_MP_TAC LIM_COMPLEX_DIV THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_0; LIM_CONST] THEN
    GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM COMPLEX_SUB_RZERO] THEN
    MATCH_MP_TAC LIM_SUB THEN REWRITE_TAC[LIM_CONST] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; GSYM COMPLEX_VEC_0] THEN
    REWRITE_TAC[NORM_ARITH `dist(x,vec 0) = norm x`] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`norm(z:complex)`; `e:real`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y <= x ==> y < e`)) THEN
    REWRITE_TAC[COMPLEX_NORM_POW] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE] THEN
    UNDISCH_TAC `n:num <= m` THEN ARITH_TAC]);;

let SUMMABLE_GP = prove
 (`!z k. norm(z) < &1 ==> summable k (\n. z pow n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMMABLE_RATIO THEN
  MAP_EVERY EXISTS_TAC [`norm(z:complex)`; `0`] THEN
  ASM_REWRITE_TAC[complex_pow; COMPLEX_NORM_MUL; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Complex version (the usual one) of Dirichlet convergence test.            *)
(* ------------------------------------------------------------------------- *)

let SERIES_DIRICHLET_COMPLEX_GEN = prove
 (`!f g N k m p l.
        bounded {vsum (m..n) f | n IN (:num)} /\
        summable (from p) (\n. Cx(norm(g(n + 1) - g(n)))) /\
        ((\n. vsum(1..n) f * g(n + 1)) --> l) sequentially
        ==> summable (from k) (\n. f(n) * g(n))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  MATCH_MP_TAC SERIES_DIRICHLET_BILINEAR THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `p:num`; `l:complex`] THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [summable]) THEN
  REWRITE_TAC[summable; SERIES_CAUCHY] THEN
  SIMP_TAC[GSYM(REWRITE_RULE[o_DEF] LIFT_SUM); FINITE_NUMSEG; FINITE_INTER;
           VSUM_CX; NORM_LIFT; COMPLEX_NORM_CX]);;

let SERIES_DIRICHLET_COMPLEX = prove
 (`!f g N k m.
        bounded {vsum (m..n) f | n IN (:num)} /\
        (!n. real(g n)) /\
        (!n. N <= n ==> Re(g(n + 1)) <= Re(g n)) /\
        (g --> Cx(&0)) sequentially
        ==> summable (from k) (\n. f(n) * g(n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:num->complex`; `\n:num. Re(g n)`; `N:num`; `k:num`;
                 `m:num`] SERIES_DIRICHLET) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY]) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; o_THM; dist; VECTOR_SUB_RZERO] THEN
    REWRITE_TAC[COMPLEX_SUB_RZERO; NORM_LIFT] THEN
    MESON_TAC[COMPLEX_NORM_GE_RE_IM; REAL_LET_TRANS];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[COMPLEX_CMUL; FUN_EQ_THM] THEN
    ASM_MESON_TAC[REAL; COMPLEX_MUL_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Versions with explicit bounds are sometimes useful.                       *)
(* ------------------------------------------------------------------------- *)

let SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT = prove
 (`!f g B p.
        &0 < B /\ 1 <= p /\
        (!m n. p <= m ==> norm(vsum(m..n) f) <= B) /\
        (!n. p <= n ==> real(g n) /\ &0 <= Re(g n)) /\
        (!n. p <= n ==> Re(g(n + 1)) <= Re(g n))
        ==> !m n. p <= m
                  ==> norm(vsum(m..n) (\k. f k * g k)) <= &2 * B * norm(g m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(vsum(m..n) (\k. (vsum(p..k) f - vsum(p..(k-1)) f) * g k))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SUBGOAL_THEN `p:num <= k`
     (fun th -> SIMP_TAC[GSYM(MATCH_MP NUMSEG_RREC th)])
    THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_NUMSEG; IN_NUMSEG] THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[MATCH_MP BILINEAR_VSUM_PARTIAL_PRE BILINEAR_COMPLEX_MUL] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[NORM_0; REAL_LE_MUL; REAL_POS; REAL_LT_IMP_LE; NORM_POS_LE] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(c) <= e - norm(a) - norm(b) ==> norm(a - b - c) <= e`) THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (m..n) (\k. norm(g(k + 1) - g(k)) * B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LE_REFL; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(m..n) (\k. Re(g(k)) - Re(g(k + 1))) * B` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[SUM_RMUL; REAL_LE_RMUL_EQ] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `p <= i /\ p <= i + 1` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_NORM; REAL_SUB; RE_SUB] THEN
    ASM_SIMP_TAC[REAL_ARITH `abs(x - y) = y - x <=> x <= y`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SUM_DIFFS; COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC(REAL_ARITH
   `w * n1 <= w * B /\ z * n2 <= z * B /\ &0 <= B * (&2 * y - (x + w + z))
    ==> x * B <= &2 * B * y - w * n1 - z * n2`) THEN
  REPEAT(CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; LE_REFL]; ALL_TAC]) THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN
   `p <= m /\ p <= m + 1 /\ p <= n /\ p <= n + 1`
  STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_NORM; real_abs] THEN REAL_ARITH_TAC);;

let SERIES_DIRICHLET_COMPLEX_EXPLICIT = prove
 (`!f g p q.
           1 <= p /\
           bounded {vsum (q..n) f | n IN (:num)} /\
           (!n. p <= n ==> real(g n) /\ &0 <= Re(g n)) /\
           (!n. p <= n ==> Re(g(n + 1)) <= Re(g n))
           ==> ?B. &0 < B /\
                   !m n. p <= m
                         ==> norm(vsum(m..n) (\k. f k * g k))
                                 <= B * norm(g m)`,
  REWRITE_TAC[FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_PARTIAL_SUMS) THEN
  SIMP_TAC[BOUNDED_POS; IN_ELIM_THM; IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MESON[] `(!x a b. x = f a b ==> p a b) <=> (!a b. p a b)`] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN EXISTS_TAC `&2 * B` THEN
  ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC SERIES_DIRICHLET_COMPLEX_VERY_EXPLICIT THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Integrals and complex multiplication.                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_INTEGRAL_COMPLEX_LMUL = prove
 (`!f y i c. (f has_integral y) i ==> ((\x. c * f(x)) has_integral (c * y)) i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[o_DEF] HAS_INTEGRAL_LINEAR) THEN
  ASM_REWRITE_TAC[linear; COMPLEX_CMUL] THEN CONV_TAC COMPLEX_RING);;

let HAS_INTEGRAL_COMPLEX_RMUL = prove
 (`!f y i c. (f has_integral y) i ==> ((\x. f(x) * c) has_integral (y * c)) i`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[HAS_INTEGRAL_COMPLEX_LMUL]);;

let HAS_INTEGRAL_COMPLEX_0 = prove
 (`!s. ((\x. Cx(&0)) has_integral Cx(&0)) s`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0; HAS_INTEGRAL_0]);;

let INTEGRABLE_COMPLEX_LMUL = prove
 (`!f:real^N->complex s c.
        f integrable_on s ==> (\x. c * f x) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_COMPLEX_LMUL]);;

let INTEGRABLE_COMPLEX_RMUL = prove
 (`!f:real^N->complex s c.
        f integrable_on s ==> (\x. f x * c) integrable_on s`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[INTEGRABLE_COMPLEX_LMUL]);;

let INTEGRABLE_COMPLEX_0 = prove
 (`!s. (\x. Cx(&0)) integrable_on s`,
  REWRITE_TAC[integrable_on] THEN MESON_TAC[HAS_INTEGRAL_COMPLEX_0]);;

let INTEGRABLE_COMPLEX_LMUL_EQ = prove
 (`!f:real^N->complex s c.
        (\x. c * f x) integrable_on s <=> c = Cx(&0) \/ f integrable_on s`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THEN
  ASM_SIMP_TAC[INTEGRABLE_COMPLEX_LMUL; COMPLEX_MUL_LZERO] THEN
  REWRITE_TAC[INTEGRABLE_COMPLEX_0] THEN
  ASM_CASES_TAC `c = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `inv c:complex` o
    MATCH_MP INTEGRABLE_COMPLEX_LMUL) THEN
  ASM_SIMP_TAC[COMPLEX_MUL_ASSOC; COMPLEX_MUL_LID; COMPLEX_MUL_LINV; ETA_AX]);;

let INTEGRABLE_COMPLEX_RMUL_EQ = prove
 (`!f:real^N->complex s c.
        (\x. f x * c) integrable_on s <=> c = Cx(&0) \/ f integrable_on s`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[INTEGRABLE_COMPLEX_LMUL_EQ]);;

let INTEGRAL_COMPLEX_LMUL = prove
 (`!f:real^N->complex s c.
        f integrable_on s ==> integral s (\x. c * f x) = c * integral s f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMPLEX_LMUL THEN
  ASM_SIMP_TAC[INTEGRABLE_INTEGRAL]);;

let INTEGRAL_COMPLEX_RMUL = prove
 (`!f:real^N->complex s c.
        f integrable_on s ==> integral s (\x. f x * c) = integral s f * c`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[INTEGRAL_COMPLEX_LMUL]);;

let REAL_COMPLEX_INTEGRAL = prove
 (`!f:real^N->complex s.
     f integrable_on s /\ (!x. x IN s ==> real(f x)) ==> real(integral s f)`,
  REWRITE_TAC[real; IM_DEF] THEN SIMP_TAC[INTEGRAL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP; LIFT_NUM] THEN
  MATCH_MP_TAC INTEGRAL_EQ_0 THEN
  ASM_REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ]);;

let INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL = prove
 (`!f g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. g x * f x) integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_BOUNDED_VARIATION_BILINEAR_LMUL THEN
  ASM_REWRITE_TAC[BILINEAR_COMPLEX_MUL]);;

let INTEGRABLE_BOUNDED_VARIATION_COMPLEX_RMUL = prove
 (`!f g a b.
        f integrable_on interval[a,b] /\
        g has_bounded_variation_on interval[a,b]
        ==> (\x. f x * g x) integrable_on interval[a,b]`,
  ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
  REWRITE_TAC[INTEGRABLE_BOUNDED_VARIATION_COMPLEX_LMUL]);;

let HAS_BOUNDED_VARIATION_ON_COMPLEX_MUL = prove
 (`!f g:real^1->complex s.
        f has_bounded_variation_on s /\
        g has_bounded_variation_on s /\
        is_interval s
        ==> (\x. f x * g x) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
  REWRITE_TAC[complex_mul; DIMINDEX_2; FORALL_2; GSYM IM_DEF; GSYM RE_DEF] THEN
  SIMP_TAC[RE; IM; LIFT_ADD; LIFT_SUB; LIFT_CMUL] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB;
    MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_ADD] THEN
  CONJ_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV)
   [GSYM LIFT_DROP] THEN
  MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_MUL THEN ASM_REWRITE_TAC[]);;

let HAS_BOUNDED_VARIATION_ON_COMPLEX_INV = prove
 (`!f s e. f has_bounded_variation_on s /\
             &0 < e /\ (!x. x IN s ==> e <= norm(f x))
           ==> (\x. inv(f x)) has_bounded_variation_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[has_bounded_variation_on; HAS_BOUNDED_SETVARIATION_ON] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(B / e pow 2):real` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^1->bool)->bool`; `t:real^1->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
   [`d:(real^1->bool)->bool`; `t:real^1->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
   REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY] THEN
  MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f(a:real^1) = Cx(&0)) /\ ~(f(b:real^1) = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[division_of; GSYM REAL_NOT_LT]) THEN
    ASM_MESON_TAC[SUBSET; COMPLEX_NORM_0; ENDS_IN_INTERVAL];
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(w = Cx(&0)) /\ ~(z = Cx(&0))
      ==> inv w - inv z = --(w - z) / (z * w)`]] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; COMPLEX_NORM_DIV] THEN
  REWRITE_TAC[NORM_NEG; real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  ASM_SIMP_TAC[COMPLEX_NORM_MUL; REAL_POW_2; REAL_LT_MUL] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[division_of; GSYM REAL_NOT_LT]) THEN
  ASM_MESON_TAC[SUBSET; COMPLEX_NORM_0; ENDS_IN_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Relations among convergence and absolute convergence for power series.    *)
(* ------------------------------------------------------------------------- *)

let ABEL_LEMMA = prove
 (`!a M r r0.
        &0 <= r /\ r < r0 /\
        (!n. n IN k ==> norm(a n) * r0 pow n <= M)
        ==> summable k (\n. Cx(norm(a(n)) * r pow n))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r0` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k:num->bool = {}` THEN ASM_REWRITE_TAC[SUMMABLE_TRIVIAL] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `i:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x <= y ==> &0 <= y`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(M * (r / r0) pow n)` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CX_MUL; CX_POW] THEN MATCH_MP_TAC SUMMABLE_COMPLEX_LMUL THEN
    MATCH_MP_TAC SUMMABLE_GP THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[REAL_ABS_DIV; real_abs; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID];
    REWRITE_TAC[REAL_CX; RE_CX] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE];
    EXISTS_TAC `0` THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NORM; REAL_ABS_DIV] THEN
    ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_POW_DIV] THEN
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
    ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ; REAL_POW_LT] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
    ASM_SIMP_TAC[REAL_LE_RMUL; REAL_POW_LE; REAL_LT_IMP_LE]]);;

let POWER_SERIES_CONV_IMP_ABSCONV = prove
 (`!a k w z.
        summable k (\n. a(n) * z pow n) /\ norm(w) < norm(z)
        ==> summable k (\n. Cx(norm(a(n) * w pow n)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  MATCH_MP_TAC ABEL_LEMMA THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SUMMABLE_IMP_BOUNDED) THEN
  REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  EXISTS_TAC `norm(z:complex)` THEN REWRITE_TAC[NORM_POS_LE] THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_NORM_POW; GSYM COMPLEX_NORM_MUL]);;

let POWER_SERIES_CONV_IMP_ABSCONV_WEAK = prove
 (`!a k w z.
        summable k (\n. a(n) * z pow n) /\ norm(w) < norm(z)
        ==> summable k (\n. Cx(norm(a(n))) * w pow n)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SERIES_COMPARISON_COMPLEX THEN
  EXISTS_TAC `\n. Cx(norm(a(n) * w pow n))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
    EXISTS_TAC `z:complex` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_CX; RE_CX; NORM_POS_LE] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NORM;
              REAL_ABS_MUL; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Comparing sums and "integrals" via complex antiderivatives.               *)
(* ------------------------------------------------------------------------- *)

let SUM_INTEGRAL_UBOUND_INCREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> Re(f(Cx x)) <= Re(f(Cx y)))
      ==> sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n + &1)) - g(Cx(&m)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `--sum(m..n) (\k. Re(g(Cx(&k))) - Re(g(Cx(&(k + 1)))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[SUM_DIFFS; RE_SUB; REAL_NEG_SUB; REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[REAL_LE_REFL]] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:complex->complex`; `f:complex->complex`;
                 `Cx(&r)`; `Cx(&r + &1)`] COMPLEX_MVT_LINE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `u IN segment[Cx(&r),Cx(&r + &1)]` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SPEC_TAC(`u:complex`,`u:complex`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; GSYM SEGMENT_CONVEX_HULL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT_CX] THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN
    ASM_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN(X_CHOOSE_THEN `u:complex`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[CX_ADD; COMPLEX_RING `y * ((x + Cx(&1)) - x) = y`] THEN
    SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
    REPEAT(FIRST_X_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
    REAL_ARITH_TAC]);;

let SUM_INTEGRAL_UBOUND_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n)) - g(Cx(&m - &1)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `--sum(m..n) (\k. Re(g(Cx(&(k) - &1))) - Re(g(Cx(&(k+1) - &1))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[SUM_DIFFS; REAL_NEG_SUB] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_SUB] THEN
    REWRITE_TAC[RE_SUB; REAL_ARITH `(x + &1) - &1 = x`; REAL_LE_REFL]] THEN
  REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
  REWRITE_TAC[REAL_NEG_SUB] THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_ADD; REAL_ARITH `(x + &1) - &1 = x`] THEN
  MP_TAC(ISPECL [`g:complex->complex`; `f:complex->complex`;
                 `Cx(&r - &1)`; `Cx(&r)`] COMPLEX_MVT_LINE) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `u:complex` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `u IN segment[Cx(&r - &1),Cx(&r)]` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SPEC_TAC(`u:complex`,`u:complex`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; GSYM SEGMENT_CONVEX_HULL] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[IN_SEGMENT_CX] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN DISCH_THEN(X_CHOOSE_THEN `u:complex`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[CX_SUB; COMPLEX_RING `y * (x - (x - Cx(&1))) = y`] THEN
    SUBGOAL_THEN `?y. u = Cx y` (CHOOSE_THEN SUBST_ALL_TAC) THENL
     [ASM_MESON_TAC[REAL_SEGMENT; REAL_CX; REAL]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_SEGMENT_CX]) THEN
    REPEAT(FIRST_X_ASSUM
     (MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE])) THEN
    REAL_ARITH_TAC]);;

let SUM_INTEGRAL_LBOUND_INCREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n ==> Re(f(Cx x)) <= Re(f(Cx y)))
      ==> Re(g(Cx(&n)) - g(Cx(&m - &1))) <= sum(m..n) (\k. Re(f(Cx(&k))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. --((f:complex->complex) z)`;
                 `\z. --((g:complex->complex) z)`;
                 `m:num`; `n:num`] SUM_INTEGRAL_UBOUND_DECREASING) THEN
  REWRITE_TAC[RE_NEG; RE_SUB; SUM_NEG; REAL_LE_NEG2;
              REAL_ARITH `--x - --y:real = --(x - y)`] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_NEG]);;

let SUM_INTEGRAL_LBOUND_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m <= x /\ x <= y /\ y <= &n + &1 ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> Re(g(Cx(&n + &1)) - g(Cx(&m))) <= sum(m..n) (\k. Re(f(Cx(&k))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z. --((f:complex->complex) z)`;
                 `\z. --((g:complex->complex) z)`;
                 `m:num`; `n:num`] SUM_INTEGRAL_UBOUND_INCREASING) THEN
  REWRITE_TAC[RE_NEG; RE_SUB; SUM_NEG; REAL_LE_NEG2;
              REAL_ARITH `--x - --y:real = --(x - y)`] THEN
  ASM_SIMP_TAC[HAS_COMPLEX_DERIVATIVE_NEG]);;

let SUM_INTEGRAL_BOUNDS_INCREASING = prove
 (`!f g m n.
         m <= n /\
         (!x. x IN segment[Cx(&m - &1),Cx (&n + &1)]
              ==> (g has_complex_derivative f x) (at x)) /\
         (!x y.
              &m - &1 <= x /\ x <= y /\ y <= &n + &1
              ==> Re(f(Cx x)) <= Re(f(Cx y)))
         ==> Re(g(Cx(&n)) - g(Cx(&m - &1))) <= sum(m..n) (\k. Re(f(Cx(&k)))) /\
             sum (m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n + &1)) - g(Cx(&m)))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUM_INTEGRAL_LBOUND_INCREASING;
    MATCH_MP_TAC SUM_INTEGRAL_UBOUND_INCREASING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_SEGMENT_CX_GEN; GSYM REAL_OF_NUM_LE]) THEN
  REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN ASM_REAL_ARITH_TAC);;

let SUM_INTEGRAL_BOUNDS_DECREASING = prove
 (`!f g m n.
      m <= n /\
      (!x. x IN segment[Cx(&m - &1),Cx(&n + &1)]
           ==> (g has_complex_derivative f(x)) (at x)) /\
      (!x y. &m - &1 <= x /\ x <= y /\ y <= &n + &1
             ==> Re(f(Cx y)) <= Re(f(Cx x)))
      ==> Re(g(Cx(&n + &1)) - g(Cx(&m))) <= sum(m..n) (\k. Re(f(Cx(&k)))) /\
          sum(m..n) (\k. Re(f(Cx(&k)))) <= Re(g(Cx(&n)) - g(Cx(&m - &1)))`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SUM_INTEGRAL_LBOUND_DECREASING;
    MATCH_MP_TAC SUM_INTEGRAL_UBOUND_DECREASING] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_SEGMENT_CX_GEN; GSYM REAL_OF_NUM_LE]) THEN
  REWRITE_TAC[IN_SEGMENT_CX_GEN] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Relating different kinds of complex limits.                               *)
(* ------------------------------------------------------------------------- *)

let LIM_INFINITY_SEQUENTIALLY_COMPLEX = prove
 (`!f l. (f --> l) at_infinity ==> ((\n. f(Cx(&n))) --> l) sequentially`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_AT_INFINITY; LIM_SEQUENTIALLY] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
  MP_TAC(ISPEC `B:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_CX] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let LIM_AT_INFINITY_COMPLEX_0 = prove
 (`!f l:real^N.
        (f --> l) at_infinity <=> ((f o inv) --> l) (at(Cx(&0)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIM_AT_LE; LIM_AT_INFINITY_POS; o_DEF] THEN
  REWRITE_TAC[GSYM DIST_NZ; real_ge] THEN
  REWRITE_TAC[dist; COMPLEX_SUB_RZERO] THEN EQ_TAC THEN DISCH_TAC THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[real_ge] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `inv(b:real)` THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
  X_GEN_TAC `z:complex` THEN STRIP_TAC THENL
   [ALL_TAC; SUBST1_TAC(SYM(SPEC `z:complex` COMPLEX_INV_INV))] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_INV_INV] THEN
    REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
    ASM_REWRITE_TAC[COMPLEX_INV_EQ_0] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_NORM_NZ] THEN
      TRANS_TAC REAL_LTE_TRANS `inv(b:real)` THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
      REWRITE_TAC[COMPLEX_NORM_INV] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ]]]);;

let LIM_ZERO_INFINITY_COMPLEX = prove
 (`!f l:real^N.
     ((\x. f(Cx(&1) / x)) --> l) (at (Cx(&0))) ==> (f --> l) at_infinity`,
  REWRITE_TAC[LIM_AT_INFINITY_COMPLEX_0; o_DEF; complex_div] THEN
  REWRITE_TAC[COMPLEX_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Transforming complex limits to real ones.                                 *)
(* ------------------------------------------------------------------------- *)

let LIM_COMPLEX_REAL = prove
 (`!f g l m.
         eventually (\n. Re(g n) = f n) sequentially /\
         Re m = l /\
         (g --> m) sequentially
         ==> !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n - l) < e`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; LIM_SEQUENTIALLY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `N1:num`)
   (CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC)) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[dist] THEN
  DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN EXISTS_TAC `N0 + N1:num` THEN
  X_GEN_TAC `n:num` THEN DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP (ARITH_RULE
   `N0 + N1:num <= n ==> N0 <= n /\ N1 <= n`)) THEN
  UNDISCH_THEN `!n. N0 <= n ==> norm ((g:num->complex) n - m) < e`
   (MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM RE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x < e`) THEN
  REWRITE_TAC[COMPLEX_NORM_GE_RE_IM]);;

let LIM_COMPLEX_REAL_0 = prove
 (`!f g. eventually (\n. Re(g n) = f n) sequentially /\
         (g --> Cx(&0)) sequentially
         ==> !e. &0 < e ==> ?N. !n. N <= n ==> abs(f n) < e`,
  MP_TAC LIM_COMPLEX_REAL THEN
  REPLICATE_TAC 2 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(MP_TAC o SPECL [`&0`; `Cx(&0)`]) THEN
  REWRITE_TAC[RE_CX; REAL_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Uniform convergence of power series in a "Stolz angle".                   *)
(* ------------------------------------------------------------------------- *)

let POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1 = prove
 (`!M a s e.
        summable s a /\ &0 < M /\ &0 < e
        ==> eventually
             (\n. !z. norm(Cx(&1) - z) <= M * (&1 - norm z)
                      ==> norm(vsum (s INTER (0..n)) (\i. a i * z pow i) -
                               infsum s (\i. a i * z pow i)) < e)
             sequentially`,
  let lemma = prove
   (`!M w z. &0 < M /\ norm(w - z) <= M * (norm w - norm z) /\ ~(z = w)
             ==> norm(z) < norm(w)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LE_MUL_EQ; REAL_SUB_LE; NORM_POS_LE; REAL_LE_TRANS];
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[REAL_SUB_REFL; REAL_MUL_RZERO;NORM_LE_0; VECTOR_SUB_EQ]])
  and lemma1 = prove
   (`!m n. m < n
           ==> vsum (m..n) (\i. a i * z pow i) =
               (Cx(&1) - z) * vsum(m..n-1) (\i. vsum (m..i) a * z pow i) +
               vsum(m..n) a * z pow n`,
    GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; SUC_SUB1] THEN
    SIMP_TAC[VSUM_CLAUSES_NUMSEG; LT; LT_IMP_LE] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow] THEN CONV_TAC COMPLEX_RING;
      ASM_SIMP_TAC[] THEN UNDISCH_TAC `m:num < n` THEN
      POP_ASSUM(K ALL_TAC)] THEN
    SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[CONJUNCT1 LT] THEN POP_ASSUM(K ALL_TAC) THEN
    SIMP_TAC[SUC_SUB1; VSUM_CLAUSES_NUMSEG; LT_IMP_LE] THEN
    ASM_REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow] THEN
    CONV_TAC COMPLEX_RING) in
  SUBGOAL_THEN
   `!M a e.
        summable (:num) a /\ &0 < M /\ &0 < e
        ==> eventually
             (\n. !z. norm(Cx(&1) - z) <= M * (&1 - norm z)
                      ==> norm(vsum (0..n) (\i. a i * z pow i) -
                               infsum (:num) (\i. a i * z pow i)) < e)
             sequentially`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o ISPECL
     [`M:real`; `\i:num. if i IN s then a i else Cx(&0)`; `e:real`]) THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_MUL_LZERO] THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM VSUM_RESTRICT_SET;
                    INFSUM_RESTRICT; SUMMABLE_RESTRICT] THEN
    REWRITE_TAC[SET_RULE `{i | i IN t /\ i IN s} = s INTER t`]] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!z. P z) <=> P (Cx(&1)) /\ (!z. ~(z = Cx(&1)) ==> P z)`] THEN
  REWRITE_TAC[EVENTUALLY_AND] THEN CONJ_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; COMPLEX_SUB_REFL;
                REAL_SUB_REFL; REAL_MUL_RZERO; REAL_LE_REFL] THEN
    UNDISCH_TAC `&0 < e` THEN SPEC_TAC(`e:real`,`e:real`) THEN
    REWRITE_TAC[GSYM tendsto; COMPLEX_POW_ONE; COMPLEX_MUL_RID; GSYM dist;
                ETA_AX] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM SUMS_INFSUM]) THEN
    REWRITE_TAC[sums; INTER_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; EVENTUALLY_SEQUENTIALLY] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM dist] THEN
  UNDISCH_TAC `&0 < e` THEN SPEC_TAC(`e:real`,`e:real`) THEN
  MATCH_MP_TAC UNIFORMLY_CAUCHY_IMP_UNIFORMLY_CONVERGENT THEN
  REWRITE_TAC[GSYM LIM_SEQUENTIALLY] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REWRITE_TAC[MESON[] `(!m n z. P m /\ P n /\ Q z ==> R m n z) <=>
                         (!z. Q z ==> !m n. P m /\ P n ==> R m n z)`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM SUMS_INFSUM]) THEN
    REWRITE_TAC[sums] THEN
    DISCH_THEN(MP_TAC o MATCH_MP CONVERGENT_IMP_CAUCHY) THEN
    REWRITE_TAC[cauchy; GSYM dist] THEN
    DISCH_THEN(MP_TAC o SPEC `min (e / &2) (e / &2 / M)`) THEN
    ASM_SIMP_TAC[REAL_LT_MIN; REAL_LT_DIV; REAL_HALF; GE; INTER_UNIV] THEN
    REWRITE_TAC[GSYM REAL_LT_MIN] THEN
    ONCE_REWRITE_TAC[SEQUENCE_CAUCHY_WLOG] THEN
    SUBGOAL_THEN
     `!f:num->complex m n. m <= n
              ==> dist(vsum (0..m) f,vsum (0..n) f) = norm(vsum (m+1..n) f)`
     (fun th -> SIMP_TAC[th])
    THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(NORM_ARITH `a + c = b ==> dist(a,b) = norm c`) THEN
      MATCH_MP_TAC VSUM_COMBINE_R THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN STRIP_TAC THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
    SUBGOAL_THEN `norm(z:complex) < &1` ASSUME_TAC THENL
     [UNDISCH_TAC `~(z = Cx(&1))` THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
      REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `norm(a - b) <= M ==> &0 <= --M ==> b = a`)) THEN
      REWRITE_TAC[GSYM REAL_MUL_RNEG; REAL_NEG_SUB] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `m + 1 < n` THENL
     [ASM_SIMP_TAC[lemma1] THEN
      MATCH_MP_TAC(NORM_ARITH
       `norm(a) < e / &2 /\ norm(b) < e / &2 ==> norm(a + b) < e`) THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `(M * (&1 - norm(z:complex))) *
                    sum (m+1..n-1) (\i. e / &2 / M * norm(z) pow i)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
          MATCH_MP_TAC VSUM_NORM_LE THEN
          REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
          X_GEN_TAC `p:num` THEN STRIP_TAC THEN
          ASM_SIMP_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
          MATCH_MP_TAC REAL_LE_RMUL THEN
          SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
          MATCH_MP_TAC(REAL_ARITH
            `x < e / &2 /\ x < e / &2 / M ==> x <= e / &2 / M`) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
          REWRITE_TAC[SUM_LMUL] THEN
          REWRITE_TAC[REAL_ARITH
           `(M * z1) * e / &2 / M * s < e / &2 <=>
            e * (M / M) * s * z1 < e * &1`] THEN
          ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
          ASM_SIMP_TAC[REAL_DIV_REFL; REAL_LT_IMP_NZ; REAL_MUL_LID] THEN
          ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_SUB_LT] THEN
          REWRITE_TAC[SUM_GP] THEN
          COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          COND_CASES_TAC THENL
           [UNDISCH_TAC `norm(Cx(&1) - z) <= M * (&1 - norm z)` THEN
            ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO] THEN
            ASM_REWRITE_TAC[NORM_ARITH `norm(x - y:complex) <= &0 <=> x = y`];
            ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_LT_DIV2_EQ; REAL_SUB_LT] THEN
          MATCH_MP_TAC(REAL_ARITH
           `&0 <= y /\ x < &1 ==> x - y < &1`) THEN
          ASM_SIMP_TAC[REAL_POW_LE; NORM_POS_LE] THEN
          MATCH_MP_TAC REAL_POW_1_LT THEN
          ASM_REWRITE_TAC[NORM_POS_LE] THEN ARITH_TAC];
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
        MATCH_MP_TAC REAL_LT_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_POW_LE] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC(REAL_ARITH
            `x < e / &2 /\ x < e / &2 / M ==> x < e / &2`) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
          MATCH_MP_TAC REAL_POW_1_LT THEN
          ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_ARITH_TAC]];
      ASM_CASES_TAC `(m+1)..n = {}` THENL
       [ASM_REWRITE_TAC[VSUM_CLAUSES; NORM_0]; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[NUMSEG_EMPTY]) THEN
      SUBGOAL_THEN `m + 1 = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VSUM_SING_NUMSEG] THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LT_MUL2 THEN SIMP_TAC[NORM_POS_LE; REAL_POW_LE] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
        SUBGOAL_THEN `m + 1 = n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[VSUM_SING_NUMSEG]] THEN
        ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_1_LT THEN
        ASM_REWRITE_TAC[NORM_POS_LE] THEN ASM_ARITH_TAC]];
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[dist] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`M:real`; `Cx(&1)`; `z:complex`] lemma) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `summable (:num) (\i. a i * z pow i)` MP_TAC THENL
     [MATCH_MP_TAC SERIES_ABSCONV_IMP_CONV THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
      EXISTS_TAC `Cx(&1)` THEN
      REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_NORM_CX] THEN
      ASM_REWRITE_TAC[REAL_ABS_NUM; COMPLEX_MUL_RID; ETA_AX];
      REWRITE_TAC[GSYM SUMS_INFSUM] THEN
      REWRITE_TAC[sums; INTER_UNIV]]]);;

let POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ = prove
 (`!M a w s e.
        summable s (\i. a i * w pow i) /\ &0 < M /\ &0 < e
        ==> eventually
             (\n. !z. norm(w - z) <= M * (norm w - norm z)
                      ==> norm(vsum (s INTER (0..n)) (\i. a i * z pow i) -
                               infsum s (\i. a i * z pow i)) < e)
             sequentially`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN ASM_CASES_TAC `w = Cx(&0)` THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_LZERO; REAL_SUB_LZERO; COMPLEX_NORM_0] THEN
    REWRITE_TAC[NORM_NEG; REAL_ARITH
      `n <= M * --n <=> &0 <= --n * (&1 + M)`] THEN
    ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_ARITH `&0 < M ==> &0 < &1 + M`] THEN
    REWRITE_TAC[NORM_ARITH `&0 <= --norm z <=> z = vec 0`] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; FORALL_UNWIND_THM2] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_POW_ZERO] THEN
    REWRITE_TAC[COND_RATOR; COND_RAND; COMPLEX_MUL_RZERO; COMPLEX_MUL_RID] THEN
    MATCH_MP_TAC(NORM_ARITH `x = y /\ &0 < e ==> norm(y - x) < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INFSUM_UNIQUE THEN
    REWRITE_TAC[sums] THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    SIMP_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA] THEN
    REWRITE_TAC[IN_INTER; LE_0; IN_NUMSEG];
    FIRST_ASSUM(MP_TAC o MATCH_MP POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO) THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN DISCH_TAC THEN
    X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z / w:complex`) THEN
    ASM_SIMP_TAC[GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_MUL] THEN
    ASM_SIMP_TAC[COMPLEX_DIV_LMUL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC REAL_LE_RCANCEL_IMP THEN EXISTS_TAC `norm(w:complex)` THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; GSYM COMPLEX_NORM_MUL] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(w = Cx(&0)) ==> (Cx(&1) - z / w) * w = w - z`] THEN
    REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_SUB_RDISTRIB] THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_MUL; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[COMPLEX_DIV_RMUL]]);;

(* ------------------------------------------------------------------------- *)
(* Hence continuity and the Abel limit theorem.                              *)
(* ------------------------------------------------------------------------- *)

let ABEL_POWER_SERIES_CONTINUOUS = prove
 (`!M s a.
        summable s a /\ &0 < M
        ==> (\z. infsum s (\i. a i * z pow i)) continuous_on
            {z | norm(Cx(&1) - z) <= M * (&1 - norm z)}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
  EXISTS_TAC `\n z. vsum (s INTER (0..n)) (\i. a i * z pow i)` THEN
  ASM_SIMP_TAC[POWER_SERIES_UNIFORM_CONVERGENCE_STOLZ_1; IN_ELIM_THM;
               TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
  SIMP_TAC[CONTINUOUS_ON_COMPLEX_MUL; CONTINUOUS_ON_COMPLEX_POW;
           CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST; FINITE_INTER;
           FINITE_NUMSEG]);;

let ABEL_LIMIT_THEOREM = prove
 (`!M s a.
        summable s a /\ &0 < M
        ==> (!z. norm(z) < &1 ==> summable s (\i. a i * z pow i)) /\
            ((\z. infsum s (\i. a i * z pow i)) --> infsum s a)
            (at (Cx(&1)) within {z | norm(Cx(&1) - z) <= M * (&1 - norm z)})`,
  GEN_TAC THEN ASM_CASES_TAC `&0 < M` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a. summable (:num) a
        ==> (!z. norm(z) < &1 ==> summable (:num) (\i. a i * z pow i)) /\
            ((\z. infsum (:num) (\i. a i * z pow i))
              --> infsum (:num) a)
            (at (Cx(&1)) within {z | norm(Cx(&1) - z) <= M * (&1 - norm z)})`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `(\n. if n IN s then a n else vec 0):num->complex`) THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; COMPLEX_VEC_0; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    ASM_REWRITE_TAC[SUMMABLE_RESTRICT; INFSUM_RESTRICT]] THEN
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC SERIES_ABSCONV_IMP_CONV THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
    EXISTS_TAC `Cx(&1)` THEN REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_NORM_CX] THEN
    ASM_REWRITE_TAC[REAL_ABS_NUM; COMPLEX_MUL_RID; ETA_AX];
    MP_TAC(ISPECL [`M:real`; `(:num)`; `a:num->complex`]
       ABEL_POWER_SERIES_CONTINUOUS) THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    DISCH_THEN(MP_TAC o SPEC `Cx(&1)`) THEN
    REWRITE_TAC[IN_ELIM_THM; CONTINUOUS_WITHIN] THEN
    REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_CX; COMPLEX_POW_ONE;
                COMPLEX_MUL_RID; ETA_AX; REAL_ABS_NUM; REAL_SUB_REFL;
                REAL_LE_REFL; REAL_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* Continuity and uniqueness of power series. These would drop easily out    *)
(* of later developments, but it seems nice to prove them without all the    *)
(* machinery of Cauchy's theorem etc.                                        *)
(* ------------------------------------------------------------------------- *)

let POWER_SERIES_CONTINUOUS = prove
 (`!a k f z r.
        (!w. w IN ball(z,r) ==> ((\n. a n * (w - z) pow n) sums f w) k)
        ==> f continuous_on ball(z,r)`,
  REWRITE_TAC[IN_BALL] THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_BALL] THEN
  X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
  ABBREV_TAC `R = (r + dist(z,w:complex)) / &2` THEN
  MATCH_MP_TAC CONTINUOUS_ON_INTERIOR THEN
  EXISTS_TAC `cball(z:complex,R)` THEN
  REWRITE_TAC[INTERIOR_CBALL; IN_BALL] THEN CONJ_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "R" THEN UNDISCH_TAC `dist(z:complex,w) < r` THEN
    CONV_TAC NORM_ARITH] THEN
  MATCH_MP_TAC(ISPEC `sequentially` CONTINUOUS_UNIFORM_LIMIT) THEN
  EXISTS_TAC
   `\n w. vsum(k INTER (0..n)) (\i. (a:num->complex) i * (w - z) pow i)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_VSUM THEN
    SIMP_TAC[FINITE_INTER; FINITE_NUMSEG; IN_INTER; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_LMUL THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPLEX_POW THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\w n. (a:num->complex) n * (w - z) pow n`;
    `\n. Cx (norm (a n * Cx R pow n))`;
    `\x:complex. x IN cball(z,R)`;
    `k:num->bool`] SERIES_COMPARISON_UNIFORM_COMPLEX) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; dist] THEN ANTS_TAC THENL
   [REWRITE_TAC[RE_CX; NORM_POS_LE; REAL_CX] THEN CONJ_TAC THENL
     [MATCH_MP_TAC POWER_SERIES_CONV_IMP_ABSCONV THEN
      EXISTS_TAC `Cx((r + R) / &2)` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `z + Cx((r + R) / &2)`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[NORM_ARITH `dist(z,z + r) = norm r`];
          REWRITE_TAC[summable; COMPLEX_RING `(z + r) - z:complex = r`] THEN
          MESON_TAC[]];
        ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_NORM_CX] THEN
      EXPAND_TAC "R" THEN UNDISCH_TAC `dist(z:complex,w) < r` THEN
      CONV_TAC NORM_ARITH;
      EXISTS_TAC `1` THEN REWRITE_TAC[IN_CBALL; dist] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
      REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_MUL; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
      REWRITE_TAC[COMPLEX_NORM_POW] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
      REWRITE_TAC[NORM_POS_LE; COMPLEX_NORM_CX] THEN
      UNDISCH_TAC `norm(z - x:complex) <= R` THEN CONV_TAC NORM_ARITH];
    DISCH_THEN(X_CHOOSE_TAC `g:complex->complex`) THEN
    SUBGOAL_THEN `!x. x IN cball(z,R) ==> (f:complex->complex) x = g x`
    MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    X_GEN_TAC `y:complex` THEN REWRITE_TAC[IN_CBALL] THEN DISCH_TAC THEN
    MATCH_MP_TAC SERIES_UNIQUE THEN
    EXISTS_TAC `\n. (a:num->complex) n * (y - z) pow n` THEN
    EXISTS_TAC `k:num->bool` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(K ALL_TAC o SPEC `&0`) THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC NORM_ARITH;
      REWRITE_TAC[sums; LIM_SEQUENTIALLY; dist] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_CBALL]) THEN ASM_MESON_TAC[]]]);;

let POWER_SERIES_LIMIT_POINT_OF_ZEROS = prove
 (`!f k r s.
        &0 < r /\
        (!w. dist(w,z) < r ==> ((\i. c i * (w - z) pow i) sums f(w)) k) /\
        (!w. w IN s ==> f(w) = Cx(&0)) /\ z limit_point_of s
        ==> !i. i IN k ==> c(i) = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[MESON[] `(!x. P x ==> Q x) <=> ~(?x. P x /\ ~Q x)`] THEN
  GEN_REWRITE_TAC RAND_CONV [num_WOP] THEN
  REWRITE_TAC[TAUT `(p ==> ~(q /\ ~r)) <=> q /\ p ==> r`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!w. w IN ball(z,r) /\ ~(w = z)
        ==> ((\i. c(m + i) * (w - z) pow i) sums f(w) / (w - z) pow m)
            {i | m + i IN k}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUMS_EQ THEN
    EXISTS_TAC `\i. (c(m + i) * (w - z) pow (m + i)) / (w - z) pow m` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
      AP_TERM_TAC THEN REWRITE_TAC[GSYM complex_div] THEN
      ASM_SIMP_TAC[COMPLEX_DIV_POW2; COMPLEX_SUB_0; LE_ADD] THEN
      AP_TERM_TAC THEN ARITH_TAC;
      REWRITE_TAC[complex_div] THEN
      MATCH_MP_TAC SERIES_COMPLEX_RMUL THEN
      MP_TAC(ISPECL [`m:num`; `\i. (c:num->complex) i * (w - z) pow i`;
                     `(f:complex->complex) w`; `{i:num | m + i IN k}`]
        (ONCE_REWRITE_RULE[ADD_SYM] SUMS_REINDEX_GEN)) THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[IMAGE; IN_ELIM_THM] THEN
      SUBGOAL_THEN `((\i. c i * (w - z) pow i) sums (f:complex->complex) w) k`
      MP_TAC THENL [ASM_MESON_TAC[IN_BALL; DIST_SYM]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM SERIES_RESTRICT] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUMS_EQ) THEN
      X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
      REWRITE_TAC[GSYM LE_EXISTS; MESON[]
        `(?x. f x IN k /\ y = f x) <=> y IN k /\ (?x. y = f x)`] THEN
      ASM_CASES_TAC `(i:num) IN k` THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_ENTIRE] THEN
      ASM_MESON_TAC[NOT_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\i. c(m + i) * (z - z) pow i) sums
     vsum {0} (\i. c(m + i) * (z - z) pow i))
    {i | m + i IN k}`
  MP_TAC THENL
   [MATCH_MP_TAC SERIES_VSUM THEN EXISTS_TAC `{0}` THEN
    REWRITE_TAC[FINITE_SING; SING_SUBSET; IN_ELIM_THM; IN_SING] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; COMPLEX_VEC_0; COMPLEX_ENTIRE] THEN
    SIMP_TAC[COMPLEX_SUB_REFL; COMPLEX_POW_EQ_0];
    REWRITE_TAC[VSUM_SING; complex_pow; ADD_CLAUSES; COMPLEX_MUL_RID] THEN
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN ball(z,r)
        ==> summable {i | m + i IN k} (\i. c(m + i) * (w - z) pow i)`
  MP_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN REWRITE_TAC[summable] THEN
    ASM_CASES_TAC `w:complex = z` THEN ASM_MESON_TAC[];
    REWRITE_TAC[summable; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `g:complex->complex`)] THEN
  SUBGOAL_THEN `(g:complex->complex) continuous_on ball(z,r)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POWER_SERIES_CONTINUOUS THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN closure((s INTER cball(z,r / &2)) DELETE z)
        ==> (g:complex->complex) x IN {Cx(&0)}`
  MP_TAC THENL
   [MATCH_MP_TAC FORALL_IN_CLOSURE THEN REWRITE_TAC[CLOSED_SING; IN_SING] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        CONTINUOUS_ON_SUBSET)) THEN
      TRANS_TAC SUBSET_TRANS `closure(cball(z:complex,r / &2))` THEN
      SIMP_TAC[SUBSET_CLOSURE; INTER_SUBSET;
               SET_RULE `s SUBSET t ==> (s DELETE z) SUBSET t`] THEN
      SIMP_TAC[CLOSURE_CLOSED; CLOSED_CBALL; SUBSET_BALLS; DIST_REFL] THEN
      ASM_REAL_ARITH_TAC;
      X_GEN_TAC `w:complex` THEN REWRITE_TAC[IN_INTER; IN_DELETE] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(g:complex->complex) w = f w / (w - z) pow m`
       (fun th -> ASM_SIMP_TAC[COMPLEX_DIV_EQ_0; th]) THEN
      MATCH_MP_TAC SERIES_UNIQUE THEN
      EXISTS_TAC `\i. (c:num->complex) (m + i) * (w - z) pow i` THEN
      EXISTS_TAC `{i:num | m + i IN k}` THEN
      REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `w IN cball(z:complex,r / &2)` THEN
      REWRITE_TAC[IN_CBALL; IN_BALL] THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
    REWRITE_TAC[IN_CLOSURE_DELETE; NOT_IMP; IN_SING] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:complex) limit_point_of s` THEN
      REWRITE_TAC[LIMPT_INFINITE_CBALL; INTER_ASSOC] THEN
      REWRITE_TAC[GSYM CBALL_MIN_INTER] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `e:real` THEN
        MP_TAC(SPEC `min (r / &2) e` th)) THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN];
      SUBGOAL_THEN `(g:complex->complex) z = c(m:num)`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC SERIES_UNIQUE THEN
      EXISTS_TAC `\i. (c:num->complex) (m + i) * (z - z) pow i` THEN
      EXISTS_TAC `{i:num | m + i IN k}` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL]]]);;
