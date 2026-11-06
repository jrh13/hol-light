(* ========================================================================= *)
(* A truncated Perron formula and the contour shift for psi_1(x,c).          *)
(*                                                                           *)
(* Kernel K(s) = y^s / (s (s + 1)), y^s = cexp(s log y), on the segment      *)
(* [c - iT, c + iT] with c > 0 and T >= 2 (c + 1):                           *)
(*   PERRON_KERNEL  |int K - 2 pi i (1 - 1/y) [y >= 1]| <= 32 y^c / T.       *)
(* No residue theorem is used.  For y >= 1 the segment and the two other     *)
(* sides of the triangle with third vertex c - T form a closed path with     *)
(* winding number 1 around 0 and -1 (TRIANGLE_WINDING_LEFT), and the Cauchy  *)
(* integral formula CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE for y^s / s and    *)
(* y^s / (s + 1) gives 2 pi i (1 - 1/y) for it; for y < 1 Cauchy's theorem   *)
(* (CAUCHY_THEOREM_CONVEX_SIMPLE) on the triangle with third vertex c + T    *)
(* gives 0.  On the other sides |K| <= 8 y^c / T^2 (KERNEL_SIDE_BOUND).      *)
(* PERRON_SERIES: termwise integration (PATH_INTEGRAL_UNIFORM_LIMIT) of a    *)
(* Dirichlet series with |a(n)| <= B (1 + log n)^k, for c > 1:               *)
(*   |int dseries a s x^s / (s (s + 1)) - 2 pi i sum_{n<=x} a(n) (1 - n/x)|  *)
(*     <= 32 x^c S / T,   S >= sum_{n<=N} |a(n)| n^-c for all N.             *)
(* RECTANGLE_SHIFT: Cauchy's theorem on a convex set replaces the segment by *)
(* the other three sides of the rectangle [s1,c] x [-T,T]; RECT_HORIZ_BOUND  *)
(* and RECT_VERT_BOUND bound them.  PSI1_ESTIMATE: for c nonprincipal,       *)
(* x >= e, 1/2 <= s1 < 1, T >= 6, and L(s,c) <> 0, |L'/L(s,c)| <= M on       *)
(* s1 <= Re s <= 2, |Im s| <= T,                                             *)
(*   |psi_1(x,c)| <= 500 x log^2 x / T + M x / T + T M x^s1,                 *)
(* where psi_1(x,c) = sum_{n<=x} Lambda(n) c(n) (1 - n/x); the right-hand    *)
(* side of the rectangle is Re s = 1 + 1/log x.                              *)
(* ========================================================================= *)

needs "Sieve/lfun.ml";;

prioritize_num(); prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* The kernel y^s / (s (s + 1)) on the sides of a triangle.                  *)
(* ------------------------------------------------------------------------- *)

let KERNEL_DENOM_LOWER = prove
 (`!u c Th. &0 < c /\ &2 * (c + &1) <= Th /\
           (Th - c) pow 2 <= &2 * norm(u) pow 2 /\
           (Th - c - &1) pow 2 <= &2 * norm(u + Cx(&1)) pow 2
           ==> Th pow 2 / &8 <= norm(u * (u + Cx(&1)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `(Th:real) / &2 <= Th - c /\ Th / &2 <= Th - c - &1`
  STRIP_ASSUME_TAC
  THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((Th:real) / &2) pow 2 <= &2 * norm(u:complex) pow 2 /\
                (Th / &2) pow 2 <= &2 * norm(u + Cx(&1)) pow 2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(Th - c:real) pow 2`;
      EXISTS_TAC `(Th - c - &1:real) pow 2`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
  SIMP_TAC[ARITH; REAL_LE_MUL; NORM_POS_LE] THEN
  REWRITE_TAC[REAL_POW_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `((Th / &2) pow 2 / &2) * ((Th / &2) pow 2 / &2):real` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_MUL2 THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
  SIMP_TAC[REAL_LE_POW_2; REAL_LE_DIV; REAL_POS] THEN ASM_REAL_ARITH_TAC);;

let KERNEL_SIDE_BOUND = prove
 (`!y c Th p q i.
     &0 < y /\ &0 < c /\ &2 * (c + &1) <= Th /\
     (!u. u IN segment[p,q]
          ==> (Th - c) pow 2 <= &2 * norm(u) pow 2 /\
              (Th - c - &1) pow 2 <= &2 * norm(u + Cx(&1)) pow 2 /\
              Re u * log y <= c * log y) /\
     ((\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))) has_path_integral i)
     (linepath(p,q))
     ==> norm i <= (&8 * exp(c * log y) / Th pow 2) * norm(q - p)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_BOUND_LINEPATH THEN
  EXISTS_TAC `\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2]];
    ALL_TAC] THEN
  X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:complex`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`u:complex`; `c:real`; `Th:real`] KERNEL_DENOM_LOWER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < Th pow 2 / &8` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_DIV; NORM_CEXP; RE_MUL_CX] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(c * log y) / (Th pow 2 / &8)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV_BOTH THEN ASM_REWRITE_TAC[REAL_EXP_MONO_LE] THEN
    REWRITE_TAC[REAL_EXP_POS_LE];
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    SUBGOAL_THEN `&0 < Th pow 2` MP_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC;
      CONV_TAC REAL_FIELD]]);;

let SEGMENT_GEOM_LEFT = prove
 (`!c Th u. &0 < c /\ &0 < Th /\
            (u IN segment[Cx c + ii * Cx Th,Cx(c - Th)] \/
             u IN segment[Cx(c - Th),Cx c - ii * Cx Th])
            ==> (Th - c) pow 2 <= &2 * norm u pow 2 /\
                (Th - c - &1) pow 2 <= &2 * norm(u + Cx(&1)) pow 2 /\
                Re u <= c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; RE_SUB; IM_SUB; RE_CMUL;
                  IM_CMUL; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II;
                  REAL_NEG_0] THEN
  REWRITE_TAC[REAL_POW_2] THENL
   [MP_TAC(SPEC `&2 * u' * Th - (c + Th)` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `&2 * u' * Th - (c + &1 + Th)` REAL_LE_SQUARE) THEN
    MP_TAC(SPECL [`u':real`; `Th:real`] REAL_LE_MUL);
    MP_TAC(SPEC `&2 * (&1 - u') * Th - (c + Th)` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `&2 * (&1 - u') * Th - (c + &1 + Th)` REAL_LE_SQUARE) THEN
    MP_TAC(SPECL [`&1 - u'`; `Th:real`] REAL_LE_MUL)] THEN
  ASM_REAL_ARITH_TAC);;

let SEGMENT_GEOM_RIGHT = prove
 (`!c Th u. &0 < c /\ &0 < Th /\
            (u IN segment[Cx c + ii * Cx Th,Cx(c + Th)] \/
             u IN segment[Cx(c + Th),Cx c - ii * Cx Th])
            ==> (Th - c) pow 2 <= &2 * norm u pow 2 /\
                (Th - c - &1) pow 2 <= &2 * norm(u + Cx(&1)) pow 2 /\
                c <= Re u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; RE_SUB; IM_SUB; RE_CMUL;
                  IM_CMUL; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II;
                  REAL_NEG_0] THEN
  REWRITE_TAC[REAL_POW_2] THENL
   [MP_TAC(SPEC `&2 * u' * Th + c - Th` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `&2 * u' * Th + c + &1 - Th` REAL_LE_SQUARE) THEN
    MP_TAC(SPECL [`u':real`; `Th:real`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`c:real`; `Th:real`] REAL_LE_MUL);
    MP_TAC(SPEC `&2 * (&1 - u') * Th + c - Th` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `&2 * (&1 - u') * Th + c + &1 - Th` REAL_LE_SQUARE) THEN
    MP_TAC(SPECL [`&1 - u'`; `Th:real`] REAL_LE_MUL) THEN
    MP_TAC(SPECL [`c:real`; `Th:real`] REAL_LE_MUL)] THEN
  ASM_REAL_ARITH_TAC);;

let TRIANGLE_WINDING_LEFT = prove
 (`!c Th z. &0 < Th /\ c - Th < z /\ z < c
            ==> winding_number(linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th) ++
                               linepath(Cx c + ii * Cx Th,Cx(c - Th)) ++
                               linepath(Cx(c - Th),Cx c - ii * Cx Th),Cx z) =
                Cx(&1)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) WINDING_NUMBER_TRIANGLE o
    lhand o snd) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `~collinear{Cx c - ii * Cx Th,Cx c + ii * Cx Th,Cx(c - Th)}`
    ASSUME_TAC THENL
     [REWRITE_TAC[COLLINEAR_3_2D; GSYM RE_DEF; GSYM IM_DEF] THEN
      REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX;
                  RE_MUL_II; IM_MUL_II; REAL_NEG_0] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `Th * Th = &0` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTERIOR_CONVEX_HULL_3_MINIMAL; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC
     [`(&1 - (c - z) / Th) / &2:real`; `(&1 - (c - z) / Th) / &2:real`;
      `(c - z) / Th:real`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ;
                 REAL_ARITH `&0 < x / &2 <=> &0 < x`; REAL_MUL_LID] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[COMPLEX_EQ; RE_ADD; IM_ADD; RE_CMUL; IM_CMUL; RE_SUB; IM_SUB;
                RE_CX; IM_CX; RE_MUL_II; IM_MUL_II; REAL_NEG_0] THEN
    UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[COMPLEX_MUL_RNEG; complex_mul; IM; RE; CNJ_SUB; RE_SUB; IM_SUB;
              RE_CNJ; IM_CNJ; RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II;
              IM_MUL_II; REAL_NEG_0] THEN
  MP_TAC(SPECL [`Th:real`; `c - z:real`] REAL_LT_MUL) THEN
  ASM_REAL_ARITH_TAC);;

let KERNEL_HOLOMORPHIC = prove
 (`!y S. (!s. s IN S ==> ~(s = Cx(&0)) /\ ~(s = --Cx(&1)))
         ==> (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))) holomorphic_on S`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
             HOLOMORPHIC_ON_CEXP];
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
             HOLOMORPHIC_ON_ADD];
    X_GEN_TAC `s:complex` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:complex`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_ENTIRE] THEN CONV_TAC COMPLEX_RING]);;

let KERNEL_PATH_INTEGRAL = prove
 (`!y p q. ~(Cx(&0) IN segment[p,q]) /\ ~(--Cx(&1) IN segment[p,q])
           ==> ((\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1))))
             has_path_integral
                path_integral (linepath(p,q))
                  (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))))
               (linepath(p,q))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
  MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
  MATCH_MP_TAC KERNEL_HOLOMORPHIC THEN ASM_MESON_TAC[]);;

let SEGMENT_VERTICAL_LINE = prove
 (`!c Th u. u IN segment[Cx c - ii * Cx Th,Cx c + ii * Cx Th] ==> Re u = c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[RE_ADD; RE_SUB; RE_CMUL; RE_CX; RE_MUL_II; IM_CX] THEN
  REAL_ARITH_TAC);;

let KERNEL_SIDES_AVOID = prove
 (`!c Th. &0 < c /\ &2 * (c + &1) <= Th
          ==> ~(Cx(&0) IN segment[Cx c - ii * Cx Th,Cx c + ii * Cx Th]) /\
              ~(--Cx(&1) IN segment[Cx c - ii * Cx Th,Cx c + ii * Cx Th]) /\
              (!u. (u IN segment[Cx c + ii * Cx Th,Cx(c - Th)] \/
                    u IN segment[Cx(c - Th),Cx c - ii * Cx Th] \/
                    u IN segment[Cx c + ii * Cx Th,Cx(c + Th)] \/
                    u IN segment[Cx(c + Th),Cx c - ii * Cx Th])
                   ==> ~(u = Cx(&0)) /\ ~(u = --Cx(&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP SEGMENT_VERTICAL_LINE) THEN
    REWRITE_TAC[RE_CX] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP SEGMENT_VERTICAL_LINE) THEN
    REWRITE_TAC[RE_NEG; RE_CX] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Th - c) pow 2 <= &2 * norm(u:complex) pow 2 /\
                (Th - c - &1) pow 2 <= &2 * norm(u + Cx(&1)) pow 2`
  MP_TAC THENL
   [MP_TAC(SPECL [`c:real`; `Th:real`; `u:complex`] SEGMENT_GEOM_LEFT) THEN
    MP_TAC(SPECL [`c:real`; `Th:real`; `u:complex`] SEGMENT_GEOM_RIGHT) THEN
    SUBGOAL_THEN `&0 < Th` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_disj o concl)) THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
   [UNDISCH_TAC `(Th - c) pow 2 <= &2 * norm(Cx(&0)) pow 2`;
    UNDISCH_TAC `(Th - c - &1) pow 2 <= &2 * norm(--Cx(&1) + Cx(&1)) pow 2`]
  THEN REWRITE_TAC[COMPLEX_NORM_0; COMPLEX_ADD_LINV] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x <= &2 * (&0:real) pow 2)`) THEN
  MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC);;

let NORM_LE_RE_IM_BOUND = prove
 (`!z a. abs(Re z) <= a /\ abs(Im z) <= a ==> norm z <= &2 * a`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `z:complex` COMPLEX_NORM_LE_RE_IM) THEN
  ASM_REAL_ARITH_TAC);;

let KERNEL_SIDE_LENGTH = prove
 (`!c Th. &0 <= Th
          ==> norm(Cx(c - Th) - (Cx c + ii * Cx Th)) <= &2 * Th /\
              norm((Cx c - ii * Cx Th) - Cx(c - Th)) <= &2 * Th /\
              norm(Cx(c + Th) - (Cx c + ii * Cx Th)) <= &2 * Th /\
              norm((Cx c - ii * Cx Th) - Cx(c + Th)) <= &2 * Th`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_RE_IM_BOUND THEN
  REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX; RE_MUL_II;
              IM_MUL_II; REAL_NEG_0] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The truncated Perron integral of the kernel.                              *)
(* ------------------------------------------------------------------------- *)

let PERRON_KERNEL_GE1 = prove
 (`!y c Th. &1 <= y /\ &0 < c /\ &2 * (c + &1) <= Th
     ==> norm(path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))) -
              Cx(&2) * Cx pi * ii * Cx(&1 - inv y))
         <= &32 * exp(c * log y) / Th`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `Th:real`] KERNEL_SIDES_AVOID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `a = Cx c - ii * Cx Th` THEN
  ABBREV_TAC `b = Cx c + ii * Cx Th` THEN
  ABBREV_TAC `v = Cx(c - Th)` THEN
  ABBREV_TAC `kf = \s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))` THEN
  SUBGOAL_THEN
   `(kf has_path_integral path_integral(linepath(a,b)) kf) (linepath(a,b)) /\
    (kf has_path_integral path_integral(linepath(b,v)) kf) (linepath(b,v)) /\
    (kf has_path_integral path_integral(linepath(v,a)) kf) (linepath(v,a))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kf" THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC KERNEL_PATH_INTEGRAL THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `gl = linepath(a:complex,b) ++ linepath(b,v) ++ linepath(v,a)`
    THEN
  SUBGOAL_THEN `valid_path gl /\ pathfinish gl = pathstart gl /\
                path_image gl = segment[a,b] UNION segment[b,v] UNION
                                segment[v,a]` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gl" THEN
    SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH; PATHSTART_JOIN;
             PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
             PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kf has_path_integral
                 path_integral(linepath(a,b)) kf +
                 path_integral(linepath(b,v)) kf +
                 path_integral(linepath(v,a)) kf) gl`
  ASSUME_TAC THENL
   [EXPAND_TAC "gl" THEN
    REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
           ASM_SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH;
                        PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                        PATHSTART_JOIN]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(kf has_path_integral (Cx(&2) * Cx pi * ii * Cx(&1 - inv y))) gl`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!z. (z = Cx(&0) \/ z = --Cx(&1))
          ==> ((\w. cexp(w * Cx(log y)) / (w - z)) has_path_integral
               (Cx(&2) * Cx pi * ii * cexp(z * Cx(log y)))) gl`
    ASSUME_TAC THENL
     [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\u. cexp(u * Cx(log y))`; `(:complex)`;
       `gl:real^1->complex`;
                     `z:complex`] CAUCHY_INTEGRAL_FORMULA_CONVEX_SIMPLE) THEN
      ASM_REWRITE_TAC[CONVEX_UNIV; INTERIOR_UNIV; IN_UNIV] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
          MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
          SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID;
                   HOLOMORPHIC_ON_CONST; HOLOMORPHIC_ON_CEXP];
          REWRITE_TAC[SUBSET; IN_DELETE; IN_UNIV; IN_UNION] THEN
          X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
          FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o
            check (is_disj o concl)) THEN
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `winding_number(gl,z) = Cx(&1)`
        (fun th -> SIMP_TAC[th; COMPLEX_MUL_LID]) THEN
      EXPAND_TAC "gl" THEN MAP_EVERY EXPAND_TAC ["a"; "b"; "v"] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      REWRITE_TAC[GSYM CX_NEG] THEN MATCH_MP_TAC TRIANGLE_WINDING_LEFT THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\w. cexp(w * Cx(log y)) / (w - Cx(&0))`;
      `Cx(&2) * Cx pi * ii * cexp(Cx(&0) * Cx(log y))`;
      `\w. cexp(w * Cx(log y)) / (w - --Cx(&1))`;
      `Cx(&2) * Cx pi * ii * cexp(--Cx(&1) * Cx(log y))`;
      `gl:real^1->complex`] HAS_PATH_INTEGRAL_SUB) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN `Cx(&2) * Cx pi * ii * cexp(Cx(&0) * Cx(log y)) -
                  Cx(&2) * Cx pi * ii * cexp(--Cx(&1) * Cx(log y)) =
                  Cx(&2) * Cx pi * ii * Cx(&1 - inv y)`
    SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_MUL_LZERO; CEXP_0; COMPLEX_MUL_LNEG;
                  COMPLEX_MUL_LID; CEXP_NEG; GSYM CX_EXP] THEN
      ASM_SIMP_TAC[EXP_LOG; REAL_ARITH `&1 <= y ==> &0 < y`] THEN
      REWRITE_TAC[CX_SUB; CX_INV] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_EQ) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
    EXPAND_TAC "kf" THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(w = Cx(&0)) /\ ~(w = --Cx(&1))` MP_TAC THENL
     [ASM_MESON_TAC[]; CONV_TAC COMPLEX_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kf:complex->complex`;
                 `path_integral(linepath(a,b)) kf +
                  path_integral(linepath(b,v)) kf +
                  path_integral(linepath(v,a)) kf`;
                 `Cx(&2) * Cx pi * ii * Cx(&1 - inv y)`;
                 `gl:real^1->complex`] HAS_PATH_INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[COMPLEX_RING `a - (a + b + c):complex = --(b + c)`;
   NORM_NEG] THEN
  SUBGOAL_THEN `!p q. (p = b /\ q = v \/ p = v /\ q = a)
                      ==> norm(path_integral(linepath(p,q)) kf)
                          <= &16 * exp(c * log y) / Th`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y:real`; `c:real`; `Th:real`; `p:complex`; `q:complex`;
                   `path_integral(linepath(p,q)) kf`] KERNEL_SIDE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
       [X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
        MP_TAC(SPECL [`c:real`; `Th:real`; `u:complex`] SEGMENT_GEOM_LEFT) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
            check (is_disj o concl)) THEN
          UNDISCH_TAC `u IN segment[p:complex,q]` THEN ASM_REWRITE_TAC[] THEN
          SIMP_TAC[];
          ALL_TAC] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        ASM_SIMP_TAC[LOG_POS];
        FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
    MP_TAC(SPECL [`c:real`; `Th:real`] KERNEL_SIDE_LENGTH) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `norm(q - p:complex) <= &2 * Th` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
        check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&8 * exp(c * log y) / Th pow 2) * (&2 * Th)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_DIV THEN
      SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `&0 < Th` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&32 * x / t = &2 * (&16 * x / t):real`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y:complex e. norm x <= e /\ norm y <= e ==> norm(x + y) <= &2 * e`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]);;

let PERRON_KERNEL_LT1 = prove
 (`!y c Th. &0 < y /\ y < &1 /\ &0 < c /\ &2 * (c + &1) <= Th
     ==> norm(path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))))
         <= &32 * exp(c * log y) / Th`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `Th:real`] KERNEL_SIDES_AVOID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `log y < &0` ASSUME_TAC THENL
   [MP_TAC(SPECL [`y:real`; `&1`] LOG_MONO_LT_IMP) THEN
    ASM_REWRITE_TAC[LOG_1];
    ALL_TAC] THEN
  ABBREV_TAC `a = Cx c - ii * Cx Th` THEN
  ABBREV_TAC `b = Cx c + ii * Cx Th` THEN
  ABBREV_TAC `w = Cx(c + Th)` THEN
  ABBREV_TAC `kf = \s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))` THEN
  SUBGOAL_THEN
   `(kf has_path_integral path_integral(linepath(a,b)) kf) (linepath(a,b)) /\
    (kf has_path_integral path_integral(linepath(b,w)) kf) (linepath(b,w)) /\
    (kf has_path_integral path_integral(linepath(w,a)) kf) (linepath(w,a))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kf" THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC KERNEL_PATH_INTEGRAL THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `gr = linepath(a:complex,b) ++ linepath(b,w) ++ linepath(w,a)`
    THEN
  SUBGOAL_THEN `valid_path gr /\ pathfinish gr = pathstart gr /\
                path_image gr = segment[a,b] UNION segment[b,w] UNION
                                segment[w,a]` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "gr" THEN
    SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH; PATHSTART_JOIN;
             PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
             PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kf has_path_integral
                 path_integral(linepath(a,b)) kf +
                 path_integral(linepath(b,w)) kf +
                 path_integral(linepath(w,a)) kf) gr`
  ASSUME_TAC THENL
   [EXPAND_TAC "gr" THEN
    REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
           ASM_SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH;
                        PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                        PATHSTART_JOIN]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(kf has_path_integral Cx(&0)) gr` ASSUME_TAC THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_CONVEX_SIMPLE THEN
    EXISTS_TAC `{z | Re z > &0}` THEN
    ASM_REWRITE_TAC[CONVEX_HALFSPACE_RE_GT] THEN CONJ_TAC THENL
     [EXPAND_TAC "kf" THEN MATCH_MP_TAC KERNEL_HOLOMORPHIC THEN
      REWRITE_TAC[IN_ELIM_THM; real_gt] THEN X_GEN_TAC `s:complex` THEN
      DISCH_TAC THEN CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[RE_CX; RE_NEG] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; real_gt] THEN
    X_GEN_TAC `u:complex` THEN STRIP_TAC THENL
     [MP_TAC(SPECL [`c:real`; `Th:real`;
      `u:complex`] SEGMENT_VERTICAL_LINE) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC];
      ALL_TAC; ALL_TAC] THEN
    (MP_TAC(SPECL [`c:real`; `Th:real`; `u:complex`] SEGMENT_GEOM_RIGHT) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
     ASM_REAL_ARITH_TAC);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kf:complex->complex`;
                 `path_integral(linepath(a,b)) kf +
                  path_integral(linepath(b,w)) kf +
                  path_integral(linepath(w,a)) kf`;
                 `Cx(&0)`; `gr:real^1->complex`] HAS_PATH_INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[COMPLEX_RING `a + b + c = Cx(&0) <=> a = --(b + c)`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NORM_NEG] THEN
  SUBGOAL_THEN `!p q. (p = b /\ q = w \/ p = w /\ q = a)
                      ==> norm(path_integral(linepath(p,q)) kf)
                          <= &16 * exp(c * log y) / Th`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`y:real`; `c:real`; `Th:real`; `p:complex`; `q:complex`;
                   `path_integral(linepath(p,q)) kf`] KERNEL_SIDE_BOUND) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
     [X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`c:real`; `Th:real`; `u:complex`] SEGMENT_GEOM_RIGHT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
          check (is_disj o concl)) THEN
        UNDISCH_TAC `u IN segment[p:complex,q]` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= (r - c) * --l ==> r * l <= c * l:real`)
      THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x <= y ==> x <= z:real`) THEN
    MP_TAC(SPECL [`c:real`; `Th:real`] KERNEL_SIDE_LENGTH) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
    SUBGOAL_THEN `norm(q - p:complex) <= &2 * Th` ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o
        check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&8 * exp(c * log y) / Th pow 2) * (&2 * Th)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]
      THEN MATCH_MP_TAC REAL_LE_DIV THEN
      SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_POW_2];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      SUBGOAL_THEN `&0 < Th` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `&32 * x / t = &2 * (&16 * x / t):real`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `!x y:complex e. norm x <= e /\ norm y <= e ==> norm(x + y) <= &2 * e`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[]);;

let PERRON_KERNEL = prove
 (`!y c Th. &0 < y /\ &0 < c /\ &2 * (c + &1) <= Th
     ==> norm(path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1)))) -
              (if &1 <= y then Cx(&2) * Cx pi * ii * Cx(&1 - inv y)
               else Cx(&0)))
         <= &32 * exp(c * log y) / Th`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MATCH_MP_TAC PERRON_KERNEL_GE1 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[COMPLEX_SUB_RZERO] THEN MATCH_MP_TAC PERRON_KERNEL_LT1 THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Termwise integration of a Dirichlet series.                               *)
(* ------------------------------------------------------------------------- *)

let CPOW_NUM_CEXP = prove
 (`!n s. 1 <= n ==> Cx(&n) cpow s = cexp(s * Cx(log(&n)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[cpow] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ; CX_LOG]);;

let PERRON_TERM_EQ = prove
 (`!a n s x. 1 <= n /\ &0 < x
             ==> a / Cx(&n) cpow s * cexp(s * Cx(log x)) =
                 a * cexp(s * Cx(log(x / &n)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CPOW_NUM_CEXP; LOG_DIV; CX_SUB; COMPLEX_SUB_LDISTRIB;
               CEXP_SUB] THEN
  MP_TAC(SPEC `s * Cx(log(&n))` CEXP_NZ) THEN CONV_TAC COMPLEX_FIELD);;

let DSERIES_UNIFORM_TAIL = prove
 (`!a B k t s N.
     (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
     &1 < t /\ t <= Re s /\ 1 <= N
     ==> norm(dseries a s - vsum(1..N) (\n. a n / Cx(&n) cpow s)) <=
         (B * (&k / ((t - &1) / &2)) pow k * exp((t - &1) / &2)) *
         &N rpow (--((t - &1) / &2)) / ((t - &1) / &2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:num->complex`; `B:real`; `k:num`; `s:complex`]
    DSERIES_SUMS_ABS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[sums; FROM_INTER_NUMSEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC `\M. vsum(1..M) (\n. a n / Cx(&n) cpow s) -
                  vsum(1..N) (\n. a n / Cx(&n) cpow s)` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
  X_GEN_TAC `M:num` THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `p:num` SUBST1_TAC o
    GEN_REWRITE_RULE I [LE_EXISTS]) THEN
  SIMP_TAC[VSUM_ADD_SPLIT; ARITH_RULE `1 <= N + 1`] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + y) - x:real^N = y`] THEN
  ABBREV_TAC `e = (t - &1) / &2` THEN
  SUBGOAL_THEN `&0 < e /\ (t + &1) / &2 = e + &1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(N+1..N+p) (\n. (B * (&k / e) pow k * exp e) *
                                 &n rpow (--(e + &1)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:num->complex`; `B:real`; `k:num`; `s:complex`;
                   `t:real`; `n:num`] DSERIES_DOMINATION) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[RPOW_NEG; REAL_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `1` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `B:real`)) (concl th))) THEN
      REWRITE_TAC[LE_REFL; LOG_1; REAL_ADD_RID; REAL_POW_ONE;
       REAL_MUL_RID] THEN
      MP_TAC(ISPEC `(a:num->complex) 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_RPOW_TAIL THEN ASM_REWRITE_TAC[]);;

let PERRON_KERNEL_INTEGRABLE = prove
 (`!y c Th. &0 < c /\ &2 * (c + &1) <= Th
            ==> (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1))))
                path_integrable_on
                linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `Th:real`] KERNEL_SIDES_AVOID) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN REWRITE_TAC[path_integrable_on] THEN
  EXISTS_TAC `path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                (\s. cexp(s * Cx(log y)) / (s * (s + Cx(&1))))` THEN
  MATCH_MP_TAC KERNEL_PATH_INTEGRAL THEN ASM_REWRITE_TAC[]);;

let PERRON_FINITE_SUM = prove
 (`!a x c Th N.
     &0 < x /\ &0 < c /\ &2 * (c + &1) <= Th
     ==> path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
           (\s. vsum(1..N) (\n. a n / Cx(&n) cpow s) * cexp(s * Cx(log x)) /
                (s * (s + Cx(&1)))) =
         vsum(1..N) (\n. a n *
           path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
             (\s. cexp(s * Cx(log(x / &n))) / (s * (s + Cx(&1)))))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                (\s. vsum(1..N) (\n. a n * cexp(s * Cx(log(x / &n))) /
                                     (s * (s + Cx(&1)))))` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:complex` THEN
    REWRITE_TAC[complex_div] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(a:num->complex) n`; `n:num`; `s:complex`; `x:real`]
      PERRON_TERM_EQ) THEN
    ASM_REWRITE_TAC[complex_div] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) PATH_INTEGRAL_VSUM o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
    MATCH_MP_TAC PATH_INTEGRABLE_COMPLEX_LMUL THEN
    REWRITE_TAC[GSYM complex_div] THEN
    MATCH_MP_TAC PERRON_KERNEL_INTEGRABLE THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
  MATCH_MP_TAC PATH_INTEGRAL_COMPLEX_LMUL THEN
  REWRITE_TAC[GSYM complex_div] THEN
  MATCH_MP_TAC PERRON_KERNEL_INTEGRABLE THEN ASM_REWRITE_TAC[]);;

let PERRON_FINITE_BOUND = prove
 (`!a x c Th N.
     &0 < x /\ &0 < c /\ &2 * (c + &1) <= Th /\ x <= &N
     ==> norm(vsum(1..N) (\n. a n *
                path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                  (\s. cexp(s * Cx(log(x / &n))) / (s * (s + Cx(&1))))) -
              Cx(&2) * Cx pi * ii *
              vsum {n | 1 <= n /\ &n <= x} (\n. a n * Cx(&1 - &n / x)))
         <= &32 * exp(c * log x) / Th *
            sum(1..N) (\n. norm(a n) * &n rpow (--c))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `Cx(&2) * Cx pi * ii *
    vsum {n | 1 <= n /\ &n <= x} (\n. a n * Cx(&1 - &n / x)) =
    vsum(1..N) (\n. a n * (if &1 <= x / &n
                           then Cx(&2) * Cx pi * ii * Cx(&1 - inv(x / &n))
                           else Cx(&0)))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `{n | 1 <= n /\ &n <= x} = {n | n IN 1..N /\ &n <= x}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
      X_GEN_TAC `n:num` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    SIMP_TAC[VSUM_RESTRICT_SET; FINITE_NUMSEG] THEN
    REWRITE_TAC[COMPLEX_VEC_0] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_MUL_LID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_INV_DIV] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG; GSYM COMPLEX_SUB_LDISTRIB] THEN
  REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC VSUM_NORM_LE THEN
  REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN X_GEN_TAC `n:num` THEN
  STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x / &n`; `c:real`; `Th:real`] PERRON_KERNEL) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm((a:num->complex) n) * &32 * exp(c * log(x / &n)) / Th` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_EQ_IMP_LE THEN
  ASM_SIMP_TAC[LOG_DIV; rpow; REAL_SUB_LDISTRIB; REAL_EXP_SUB] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_EXP_NEG] THEN
  SUBGOAL_THEN `&0 < exp(c * log(&n)) /\ &0 < Th` MP_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT] THEN ASM_REAL_ARITH_TAC;
    CONV_TAC REAL_FIELD]);;

let PERRON_SERIES = prove
 (`!a B k x c Th S.
     (!n. 1 <= n ==> norm(a n) <= B * (&1 + log(&n)) pow k) /\
     &0 < x /\ &1 < c /\ &2 * (c + &1) <= Th /\
     (!N. sum(1..N) (\n. norm(a n) * &n rpow (--c)) <= S)
     ==> norm(path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
                (\s. dseries a s * cexp(s * Cx(log x)) / (s * (s + Cx(&1)))) -
              Cx(&2) * Cx pi * ii *
              vsum {n | 1 <= n /\ &n <= x} (\n. a n * Cx(&1 - &n / x)))
         <= &32 * exp(c * log x) / Th * S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `Th:real`] KERNEL_SIDES_AVOID) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`sequentially`;
    `\N s. vsum(1..N) (\n. (a:num->complex) n / Cx(&n) cpow s) *
           cexp(s * Cx(log x)) / (s * (s + Cx(&1)))`;
    `norm((Cx c + ii * Cx Th) - (Cx c - ii * Cx Th))`;
    `linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th)`;
    `\s. dseries a s * cexp(s * Cx(log x)) / (s * (s + Cx(&1)))`]
    PATH_INTEGRAL_UNIFORM_LIMIT) THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; VALID_PATH_LINEPATH;
              VECTOR_DERIVATIVE_LINEPATH_AT; REAL_LE_REFL;
              PATH_IMAGE_LINEPATH] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ALWAYS_EVENTUALLY THEN X_GEN_TAC `N:num` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_IMP_CONTINUOUS_ON THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
      REWRITE_TAC[HOLOMORPHIC_DSERIES_PARTIAL] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN REPEAT CONJ_TAC THENL
       [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
        SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
                 HOLOMORPHIC_ON_CEXP];
        SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
                 HOLOMORPHIC_ON_ADD];
        X_GEN_TAC `s:complex` THEN DISCH_TAC THEN
        REWRITE_TAC[COMPLEX_ENTIRE] THEN
        REWRITE_TAC[COMPLEX_RING `s + Cx(&1) = Cx(&0) <=> s = --Cx(&1)`] THEN
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC `ee = (c - &1) / &2` THEN
    SUBGOAL_THEN `&0 < ee` ASSUME_TAC THENL
     [EXPAND_TAC "ee" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `1` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `B:real`)) (concl th))) THEN
      REWRITE_TAC[LE_REFL; LOG_1; REAL_ADD_RID; REAL_POW_ONE;
       REAL_MUL_RID] THEN
      MP_TAC(ISPEC `(a:num->complex) 1` NORM_POS_LE) THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `C0 = (B * (&k / ee) pow k * exp ee) / ee *
                     exp(c * log x) / (c * c) + &1` THEN
    SUBGOAL_THEN `&0 < C0` ASSUME_TAC THENL
     [EXPAND_TAC "C0" THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 < x + &1:real`) THEN
      REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_DIV) THEN
             CONJ_TAC) THEN
      ASM_SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_SQUARE; REAL_POS] THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN
      TRY(MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`ee:real`; `e / C0:real`] RPOW_NEG_EVENTUALLY_LT) THEN
    ASM_SIMP_TAC[REAL_LT_DIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `N0:num` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N0:num` THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `s:complex` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Re s = c` ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENT_VERTICAL_LINE]; ALL_TAC] THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_SUB_RDISTRIB] THEN
    REWRITE_TAC[GSYM complex_div; GSYM COMPLEX_MUL_ASSOC] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; NORM_CEXP; RE_MUL_CX] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    MP_TAC(ISPECL [`a:num->complex`; `B:real`; `k:num`; `c:real`;
                   `s:complex`; `N:num`] DSERIES_UNIFORM_TAIL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LE_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `c * c <= norm(s:complex) * norm(s + Cx(&1))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN
      MP_TAC(SPEC `s:complex` COMPLEX_NORM_GE_RE_IM) THEN
      MP_TAC(SPEC `s + Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
      ASM_REWRITE_TAC[RE_ADD; RE_CX] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < c * c` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `K1 = B * (&k / ee) pow k * exp ee` THEN
    ABBREV_TAC `E1 = exp(c * log x)` THEN
    SUBGOAL_THEN `&0 <= K1 /\ &0 < E1` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["K1"; "E1"] THEN REWRITE_TAC[REAL_EXP_POS_LT] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
      MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `(K1 * &N rpow (--ee) / ee) * E1 / (c * c)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE; REAL_LE_MUL];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV_BOTH THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `C0 * &N rpow (--ee)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(C0 - &1) * &N rpow (--ee)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_EQ_IMP_LE THEN EXPAND_TAC "C0" THEN
        REWRITE_TAC[REAL_ARITH `(x + &1) - &1 = x`] THEN
        UNDISCH_TAC `&0 < ee` THEN UNDISCH_TAC `&0 < c * c` THEN
        CONV_TAC REAL_FIELD;
        MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[REAL_ARITH `c - &1 <= c`] THEN
        MATCH_MP_TAC RPOW_POS_LE THEN REAL_ARITH_TAC];
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[PERRON_FINITE_SUM] THEN DISCH_TAC THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_NORM_UBOUND) THEN
  EXISTS_TAC
   `\N. vsum(1..N) (\n. a n *
          path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th))
            (\s. cexp(s * Cx(log(x / &n))) / (s * (s + Cx(&1))))) -
        Cx(&2) * Cx pi * ii *
        vsum {n | 1 <= n /\ &n <= x} (\n. a n * Cx(&1 - &n / x))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_SUB THEN ASM_REWRITE_TAC[LIM_CONST]; ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  MP_TAC(SPEC `x:real` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN EXISTS_TAC `N1:num` THEN
  X_GEN_TAC `N:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `&32 * exp(c * log x) / Th *
              sum(1..N) (\n. norm((a:num->complex) n) * &n rpow (--c))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PERRON_FINITE_BOUND THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N1` THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    REWRITE_TAC[REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_EXP_POS_LE] THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Moving the contour to a rectangle.                                        *)
(* ------------------------------------------------------------------------- *)

let RECTANGLE_SHIFT = prove
 (`!f U c s1 Th.
     convex U /\ f holomorphic_on U /\
     segment[Cx c - ii * Cx Th,Cx c + ii * Cx Th] SUBSET U /\
     segment[Cx c + ii * Cx Th,Cx s1 + ii * Cx Th] SUBSET U /\
     segment[Cx s1 + ii * Cx Th,Cx s1 - ii * Cx Th] SUBSET U /\
     segment[Cx s1 - ii * Cx Th,Cx c - ii * Cx Th] SUBSET U
     ==> path_integral (linepath(Cx c - ii * Cx Th,Cx c + ii * Cx Th)) f =
         path_integral (linepath(Cx c - ii * Cx Th,Cx s1 - ii * Cx Th)) f +
         path_integral (linepath(Cx s1 - ii * Cx Th,Cx s1 + ii * Cx Th)) f +
         path_integral (linepath(Cx s1 + ii * Cx Th,Cx c + ii * Cx Th)) f`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `p1 = Cx c - ii * Cx Th` THEN
  ABBREV_TAC `p2 = Cx c + ii * Cx Th` THEN
  ABBREV_TAC `p3 = Cx s1 + ii * Cx Th` THEN
  ABBREV_TAC `p4 = Cx s1 - ii * Cx Th` THEN
  SUBGOAL_THEN
   `!p q. segment[p,q] SUBSET U
          ==> (f has_path_integral path_integral(linepath(p,q)) f)
              (linepath(p,q))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_PATH_INTEGRAL_INTEGRAL THEN
    MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  ABBREV_TAC `g = linepath(p1:complex,p2) ++ linepath(p2,p3) ++
                  linepath(p3,p4) ++ linepath(p4,p1)` THEN
  SUBGOAL_THEN `(f has_path_integral
                 path_integral(linepath(p1,p2)) f +
                 path_integral(linepath(p2,p3)) f +
                 path_integral(linepath(p3,p4)) f +
                 path_integral(linepath(p4,p1)) f) g`
  ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    REPEAT(MATCH_MP_TAC HAS_PATH_INTEGRAL_JOIN THEN
           ASM_SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH;
                        PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                        PATHSTART_JOIN]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(f has_path_integral Cx(&0)) g` ASSUME_TAC THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_CONVEX_SIMPLE THEN
    EXISTS_TAC `U:complex->bool` THEN EXPAND_TAC "g" THEN
    ASM_SIMP_TAC[VALID_PATH_JOIN; VALID_PATH_LINEPATH; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; PATHSTART_JOIN; PATHFINISH_JOIN;
                 PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; UNION_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:complex->complex`;
                 `path_integral(linepath(p1,p2)) f +
                  path_integral(linepath(p2,p3)) f +
                  path_integral(linepath(p3,p4)) f +
                  path_integral(linepath(p4,p1)) f`;
                 `Cx(&0)`; `g:real^1->complex`] HAS_PATH_INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `path_integral(linepath(p2,p3)) f = --path_integral(linepath(p3,p2)) f /\
    path_integral(linepath(p3,p4)) f = --path_integral(linepath(p4,p3)) f /\
    path_integral(linepath(p4,p1)) f = --path_integral(linepath(p1,p4)) f`
  (REPEAT_TCL CONJUNCTS_THEN SUBST1_TAC) THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC PATH_INTEGRAL_REVERSE_LINEPATH THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U:complex->bool` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    CONV_TAC COMPLEX_RING]);;

let RECT_CONVEX = prove
 (`!s1 cc Th. convex {s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th} =
                {s | Re s >= s1} INTER {s | Re s <= cc} INTER
                {s | Im s <= Th} INTER {s | Im s >= --Th}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REPEAT(MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HALFSPACE_RE_GE; CONVEX_HALFSPACE_RE_LE;
                CONVEX_HALFSPACE_IM_GE; CONVEX_HALFSPACE_IM_LE]]);;

let LOG_DERIV_KERNEL_HOLOMORPHIC = prove
 (`!d c x U. dirichlet_character d c /\ ~(c = chi_0 d) /\
             U SUBSET {s | Re s > &0} /\
             (!s. s IN U ==> ~(dseries c s = Cx(&0)))
             ==> (\s. --(complex_derivative (dseries c) s) / dseries c s *
                      cexp(s * Cx(log x)) / (s * (s + Cx(&1))))
                 holomorphic_on U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(dseries c) holomorphic_on U /\
                (complex_derivative (dseries c)) holomorphic_on U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `{s | Re s > &0}` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[HOLOMORPHIC_LFUN];
      MATCH_MP_TAC HOLOMORPHIC_COMPLEX_DERIVATIVE THEN
      REWRITE_TAC[OPEN_HALFSPACE_RE_GT] THEN ASM_MESON_TAC[HOLOMORPHIC_LFUN]];
    ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_NEG THEN ASM_REWRITE_TAC[ETA_AX];
    ALL_TAC] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_COMPOSE THEN
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
             HOLOMORPHIC_ON_CEXP];
    SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST;
             HOLOMORPHIC_ON_ADD];
    X_GEN_TAC `s:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < Re s` MP_TAC THENL
     [UNDISCH_TAC `U SUBSET {s | Re s > &0}` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_ENTIRE; DE_MORGAN_THM] THEN DISCH_TAC THEN
    CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
    REWRITE_TAC[RE_ADD; RE_CX] THEN ASM_REAL_ARITH_TAC]);;

let SEGMENT_COMPONENTS = prove
 (`!p q u. u IN segment[p,q]
           ==> (Re p <= Re u /\ Re u <= Re q \/ Re q <= Re u /\ Re u <= Re p)
             /\
               (Im p <= Im u /\ Im u <= Im q \/ Im q <= Im u /\ Im u <= Im p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`p:complex`; `q:complex`; `u:complex`; `1`]
      IN_SEGMENT_COMPONENT);
    MP_TAC(ISPECL [`p:complex`; `q:complex`; `u:complex`; `2`]
      IN_SEGMENT_COMPONENT)] THEN
  ASM_REWRITE_TAC[DIMINDEX_2; ARITH; GSYM RE_DEF; GSYM IM_DEF] THEN
  REAL_ARITH_TAC);;

let SIDE_INTEGRAL_BOUND = prove
 (`!g p q B E. g path_integrable_on linepath(p,q) /\ &0 <= B /\
               (!u. u IN segment[p,q] ==> norm(g u) <= B) /\
               B * norm(q - p) <= E
               ==> norm(path_integral (linepath(p,q)) g) <= E`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * norm(q - p:complex)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PATH_INTEGRAL_BOUND_LINEPATH THEN ASM_REWRITE_TAC[]);;

let RECT_HORIZ_BOUND = prove
 (`!g s1 cc Th M x t.
     &1 / &2 <= s1 /\ s1 < cc /\ cc <= &2 /\ &1 <= Th /\ &0 <= M /\
     &1 <= x /\ abs t = Th /\
     (g:complex->complex) continuous_on
       {s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th} /\
     (!s. s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th
          ==> norm(g s) <= M * exp(Re s * log x) / norm(s * (s + Cx(&1))))
     ==> norm(path_integral (linepath(Cx cc + ii * Cx t,Cx s1 + ii * Cx t)) g)
         <= &2 * M * exp(cc * log x) / Th pow 2 /\
         norm(path_integral (linepath(Cx s1 + ii * Cx t,Cx cc + ii * Cx t)) g)
         <= &2 * M * exp(cc * log x) / Th pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= log x /\ &0 < Th pow 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_LT THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u. u IN segment[Cx cc + ii * Cx t,Cx s1 + ii * Cx t] \/
        u IN segment[Cx s1 + ii * Cx t,Cx cc + ii * Cx t]
        ==> s1 <= Re u /\ Re u <= cc /\ abs(Im u) <= Th /\
            norm((g:complex->complex) u) <= M * exp(cc * log x) / Th pow 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s1 <= Re u /\ Re u <= cc /\ Im u = t` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN (MP_TAC o MATCH_MP SEGMENT_COMPONENTS))
       THEN
      REWRITE_TAC[RE_ADD; IM_ADD; RE_CX; IM_CX; RE_MUL_II; IM_MUL_II;
                  REAL_NEG_0; REAL_ADD_LID; REAL_ADD_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * exp(Re u * log x) / norm(u * (u + Cx(&1)))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_MONO_LE; REAL_LE_INV_EQ;
                NORM_POS_LE] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    MP_TAC(SPEC `u:complex` COMPLEX_NORM_GE_RE_IM) THEN
    MP_TAC(SPEC `u + Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
    ASM_REWRITE_TAC[IM_ADD; IM_CX; REAL_ADD_RID] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SIDE_INTEGRAL_BOUND THEN
  EXISTS_TAC `M * exp(cc * log x) / Th pow 2` THEN
  (REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
     MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
     EXISTS_TAC `{s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th}` THEN
     ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
     MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_DIV THEN
     ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE];
     ASM_MESON_TAC[];
     REWRITE_TAC[COMPLEX_RING `(a + b) - (c + b):complex = a - c`] THEN
     REWRITE_TAC[GSYM CX_SUB; COMPLEX_NORM_CX] THEN
     REWRITE_TAC[REAL_ARITH `&2 * m * e / t = (m * e / t) * &2:real`] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC REAL_LE_DIV THEN
       ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_EXP_POS_LE];
       ASM_REAL_ARITH_TAC]]));;

let RECT_VERT_BOUND = prove
 (`!g s1 cc Th M x.
     &1 / &2 <= s1 /\ s1 < cc /\ &1 <= Th /\ &0 <= M /\ &1 <= x /\
     (g:complex->complex) continuous_on
       {s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th} /\
     (!s. s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th
          ==> norm(g s) <= M * exp(Re s * log x) / norm(s * (s + Cx(&1))))
     ==> norm(path_integral
                (linepath(Cx s1 - ii * Cx Th,Cx s1 + ii * Cx Th)) g)
         <= &4 * Th * M * exp(s1 * log x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u. u IN segment[Cx s1 - ii * Cx Th,Cx s1 + ii * Cx Th]
        ==> s1 <= Re u /\ Re u <= cc /\ abs(Im u) <= Th /\
            norm((g:complex->complex) u) <= &2 * M * exp(s1 * log x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `Re u = s1 /\ abs(Im u) <= Th` STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP SEGMENT_COMPONENTS) THEN
      REWRITE_TAC[RE_ADD; IM_ADD; RE_SUB; IM_SUB; RE_CX; IM_CX; RE_MUL_II;
                  IM_MUL_II; REAL_NEG_0; REAL_SUB_RZERO; REAL_ADD_RID;
                  REAL_SUB_LZERO; REAL_ADD_LID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `M * exp(Re u * log x) / norm(u * (u + Cx(&1)))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1 / &2 <= norm(u * (u + Cx(&1)))` ASSUME_TAC THENL
     [REWRITE_TAC[COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &2) * &1` THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      MP_TAC(SPEC `u:complex` COMPLEX_NORM_GE_RE_IM) THEN
      MP_TAC(SPEC `u + Cx(&1)` COMPLEX_NORM_GE_RE_IM) THEN
      ASM_REWRITE_TAC[RE_ADD; RE_CX] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= M * exp(s1 * log x)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(M * exp(s1 * log x)) * inv(norm(u * (u + Cx(&1))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[real_div; REAL_MUL_ASSOC; REAL_LE_REFL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `&2 * M * e = (M * e) * &2:real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_INV] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SIDE_INTEGRAL_BOUND THEN
  EXISTS_TAC `&2 * M * exp(s1 * log x)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRABLE_CONTINUOUS_LINEPATH THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `{s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ASM_MESON_TAC[];
    REWRITE_TAC[COMPLEX_RING `(a + b) - (a - b):complex = Cx(&2) * b`] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN UNDISCH_TAC `&1 <= Th` THEN
    REWRITE_TAC[REAL_ABS_NUM] THEN
    SIMP_TAC[REAL_ARITH `&1 <= t ==> abs t = t`] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The estimate for psi_1(x,c).                                              *)
(* ------------------------------------------------------------------------- *)

let PSI1_ESTIMATE = prove
 (`!d c x s1 Th M.
     dirichlet_character d c /\ ~(c = chi_0 d) /\ exp(&1) <= x /\
     &1 / &2 <= s1 /\ s1 < &1 /\ &6 <= Th /\ &0 <= M /\
     (!s. s1 <= Re s /\ Re s <= &2 /\ abs(Im s) <= Th
          ==> ~(dseries c s = Cx(&0)) /\
              norm(complex_derivative (dseries c) s / dseries c s) <= M)
     ==> norm(vsum {n | 1 <= n /\ &n <= x}
                   (\n. Cx(mangoldt n) * c n * Cx(&1 - &n / x)))
         <= &500 * x * log x pow 2 / Th + M * x / Th +
            Th * M * exp(s1 * log x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP DIRICHLET_CHARACTER_DSERIES_HYPS)
    THEN
  SUBGOAL_THEN `&0 < x /\ &1 <= log x` STRIP_ASSUME_TAC THENL
   [MP_TAC REAL_EXP_POS_LT THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `cc = &1 + inv(log x)` THEN
  SUBGOAL_THEN `&1 < cc /\ cc <= &2 /\ s1 < cc /\
                exp(cc * log x) = exp(&1) * x`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN
    SUBGOAL_THEN `&0 < inv(log x) /\ inv(log x) <= &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; REAL_MUL_LID; REAL_EXP_ADD] THEN
    ASM_SIMP_TAC[EXP_LOG; REAL_MUL_LINV; REAL_ARITH `&1 <= l ==> ~(l = &0)`]
    THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\n. Cx(mangoldt n) * (c:num->complex) n`; `&1`; `1`;
                 `x:real`; `cc:real`; `Th:real`;
                 `&2 / (cc - &1) * exp((cc - &1) / &2) *
                  (&1 + &2 / (cc - &1))`]
    PERRON_SERIES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_1; REAL_MUL_LID] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE;
       REAL_ABS_POS] THEN
      MP_TAC(SPEC `n:num` MANGOLDT_POS_LE) THEN
      MP_TAC(SPEC `n:num` MANGOLDT_LE_LOG) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC];
      ASM_REAL_ARITH_TAC;
      GEN_TAC THEN MATCH_MP_TAC LAMBDA_SERIES_BOUND THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  ABBREV_TAC `S0 = &2 / (cc - &1) * exp((cc - &1) / &2) *
                   (&1 + &2 / (cc - &1))` THEN
  ABBREV_TAC `R0 = {s | s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th}` THEN
  ABBREV_TAC `G = \s. --(complex_derivative (dseries c) s) / dseries c s *
                      cexp(s * Cx(log x)) / (s * (s + Cx(&1)))` THEN
  SUBGOAL_THEN `R0 SUBSET {s | Re s > &0} /\
                (!s. s IN R0 ==> ~(dseries c s = Cx(&0)))`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R0" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; real_gt] THEN
    CONJ_TAC THEN X_GEN_TAC `s:complex` THEN STRIP_TAC THENL
     [ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:complex` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `complex_derivative`))
                             (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `G holomorphic_on R0` ASSUME_TAC THENL
   [EXPAND_TAC "G" THEN MATCH_MP_TAC LOG_DERIV_KERNEL_HOLOMORPHIC THEN
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_integral (linepath(Cx cc - ii * Cx Th,Cx cc + ii * Cx Th))
      (\s. dseries (\n. Cx(mangoldt n) * c n) s * cexp(s * Cx(log x)) /
           (s * (s + Cx(&1)))) =
    path_integral (linepath(Cx cc - ii * Cx Th,Cx cc + ii * Cx Th)) G`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PATH_INTEGRAL_EQ THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    X_GEN_TAC `s:complex` THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP SEGMENT_VERTICAL_LINE) THEN
    EXPAND_TAC "G" THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:num->complex`; `s:complex`] DSERIES_NEG_LOG_DERIV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. (!u. u IN segment[p,q] ==> s1 <= Re u /\ Re u <= cc /\
                                     abs(Im u) <= Th)
          ==> segment[p,q] SUBSET R0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "R0" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`G:complex->complex`; `R0:complex->bool`; `cc:real`;
                 `s1:real`; `Th:real`] RECTANGLE_SHIFT) THEN
  ANTS_TAC THENL
   [EXPAND_TAC "R0" THEN REWRITE_TAC[RECT_CONVEX] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `u:complex` THEN
    DISCH_THEN(MP_TAC o MATCH_MP SEGMENT_COMPONENTS) THEN
    REWRITE_TAC[RE_ADD; RE_SUB; IM_ADD; IM_SUB; RE_CX; IM_CX; RE_MUL_II;
                IM_MUL_II; REAL_NEG_0; REAL_SUB_RZERO; REAL_ADD_RID;
                REAL_SUB_LZERO; REAL_ADD_LID] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `(G:complex->complex) continuous_on R0 /\
    (!s. s1 <= Re s /\ Re s <= cc /\ abs(Im s) <= Th
         ==> norm(G s) <= M * exp(Re s * log x) / norm(s * (s + Cx(&1))))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
    X_GEN_TAC `s:complex` THEN STRIP_TAC THEN EXPAND_TAC "G" THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; NORM_NEG; NORM_CEXP;
                RE_MUL_CX] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:complex` o
        check (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `complex_derivative`))
                             (concl th))) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[COMPLEX_NORM_DIV];
      MATCH_MP_TAC REAL_LE_DIV THEN
      SIMP_TAC[REAL_EXP_POS_LE; REAL_LE_MUL; NORM_POS_LE]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`G:complex->complex`; `s1:real`; `cc:real`; `Th:real`;
                `M:real`; `x:real`; `--Th:real`] RECT_HORIZ_BOUND) THEN
  MP_TAC(SPECL [`G:complex->complex`; `s1:real`; `cc:real`; `Th:real`;
                `M:real`; `x:real`; `Th:real`] RECT_HORIZ_BOUND) THEN
  MP_TAC(SPECL [`G:complex->complex`; `s1:real`; `cc:real`; `Th:real`;
                `M:real`; `x:real`] RECT_VERT_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
  SUBGOAL_THEN `&1 <= Th /\ abs Th = Th /\ &1 <= x` STRIP_ASSUME_TAC THENL
   [MP_TAC REAL_EXP_POS_LT THEN DISCH_THEN(MP_TAC o SPEC `&1`) THEN
    MP_TAC(SPEC `&1` REAL_EXP_LE_X) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_RNEG; GSYM complex_sub] THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `I1 = path_integral
                    (linepath (Cx cc - ii * Cx Th,Cx s1 - ii * Cx Th)) G` THEN
  ABBREV_TAC `I2 = path_integral
                    (linepath (Cx s1 - ii * Cx Th,Cx s1 + ii * Cx Th)) G` THEN
  ABBREV_TAC `I3 = path_integral
                    (linepath (Cx s1 + ii * Cx Th,Cx cc + ii * Cx Th)) G` THEN
  ABBREV_TAC `Ps = vsum {n | 1 <= n /\ &n <= x}
                     (\n. (Cx(mangoldt n) * c n) * Cx(&1 - &n / x))` THEN
  SUBGOAL_THEN `vsum {n | 1 <= n /\ &n <= x}
                  (\n. Cx(mangoldt n) * c n * Cx(&1 - &n / x)) = Ps`
  SUBST1_TAC THENL [EXPAND_TAC "Ps" THEN REWRITE_TAC[COMPLEX_MUL_ASSOC];
                    ALL_TAC] THEN
  SUBGOAL_THEN `S0 <= &12 * log x pow 2` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN EXPAND_TAC "cc" THEN
    REWRITE_TAC[REAL_ADD_SUB] THEN
    ASM_SIMP_TAC[REAL_INV_DIV; REAL_ARITH `&1 <= l ==> ~(l = &0)`;
                 real_div; REAL_INV_INV] THEN
    SUBGOAL_THEN `exp(inv(log x) * inv(&2)) <= &2` ASSUME_TAC THENL
     [MP_TAC(SPEC `inv(log x) * inv(&2)` REAL_EXP_BOUND_LEMMA) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `inv(log x) <= &1` MP_TAC THENL
       [MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * log x) * &2 * (&3 * log x)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 <= &2 * pi` ASSUME_TAC THENL
   [MP_TAC PI_APPROX_32 THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `norm(Cx(&2) * Cx pi * ii * Ps) = &2 * pi * norm(Ps:complex)`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II] THEN
    MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `X1 = exp(s1 * log x)` THEN
  SUBGOAL_THEN `&0 <= X1 /\ exp(&1) <= &4 /\ &0 <= log x pow 2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X1" THEN REWRITE_TAC[REAL_EXP_POS_LE; REAL_EXP_1_LE_4;
                                     REAL_LE_POW_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * pi * norm(Ps:complex) <=
                &32 * (exp(&1) * x) / Th * S0 +
                &2 * (&2 * M * (exp(&1) * x) / Th pow 2) + &4 * Th * M * X1`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> can (find_term ((=) `pi`)) (concl th) &&
                       is_eq(concl th))) THEN
    MATCH_MP_TAC(NORM_ARITH
     `!p i1 i2 i3:complex a b c.
        norm((i1 + i2 + i3) - p) <= a /\ norm i1 <= b /\ norm i2 <= c /\
        norm i3 <= b
        ==> norm p <= a + &2 * b + c`) THEN
    MAP_EVERY EXISTS_TAC [`I1:complex`; `I2:complex`; `I3:complex`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Th /\ &0 <= x / Th /\ &0 <= S0` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "S0" THEN
      REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      REWRITE_TAC[REAL_EXP_POS_LE] THEN
      TRY(MATCH_MP_TAC(REAL_ARITH `&0 <= y ==> &0 <= &1 + y:real`)) THEN
      MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&32 * (exp(&1) * x) / Th * S0 <=
                &1536 * log x pow 2 * (x / Th)` ASSUME_TAC THENL
   [SUBGOAL_THEN `&32 * (exp(&1) * x) / Th * S0 =
                  (&32 * exp(&1) * S0) * (x / Th)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
    REWRITE_TAC[REAL_ARITH `&1536 * l = &32 * (&4 * (&12 * l)):real`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_EXP_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &2 * M * (exp(&1) * x) / Th pow 2 <= &6 * (M * x / Th)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `&2 * &2 * M * (exp(&1) * x) / Th pow 2 =
                  ((&4 * exp(&1)) / Th) * (M * x / Th)` SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[GSYM real_div]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= Th * M * X1 /\ &0 <= M * x / Th /\
                &0 <= log x pow 2 * (x / Th)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    ASM_REWRITE_TAC[] THEN TRY(ASM_REAL_ARITH_TAC) THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[GSYM real_div];
    ALL_TAC] THEN
  SUBGOAL_THEN `&6 * norm(Ps:complex) <= &2 * pi * norm Ps` MP_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_REWRITE_TAC[NORM_POS_LE]; ALL_TAC] THEN
  SUBGOAL_THEN `&500 * x * log x pow 2 / Th = &500 * (log x pow 2 * (x / Th))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < Th` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;
