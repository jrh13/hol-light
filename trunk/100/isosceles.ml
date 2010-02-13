(* ========================================================================= *)
(* Isosceles triangle theorem.                                               *)
(* ========================================================================= *)

needs "Multivariate/geom.ml";;

(* ------------------------------------------------------------------------- *)
(* The theorem, according to Wikipedia.                                      *)
(* ------------------------------------------------------------------------- *)

let ISOSCELES_TRIANGLE_THEOREM = prove
 (`!A B C:real^N. dist(A,C) = dist(B,C) ==> angle(C,A,B) = angle(A,B,C)`,
  MP_TAC(INST_TYPE [`:N`,`:M`] CONGRUENT_TRIANGLES_SSS) THEN
  MESON_TAC[DIST_SYM; ANGLE_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The obvious converse.                                                     *)
(* ------------------------------------------------------------------------- *)

let ISOSCELES_TRIANGLE_CONVERSE = prove
 (`!A B C:real^N. angle(C,A,B) = angle(A,B,C) /\ ~(collinear {A,B,C})
                  ==> dist(A,C) = dist(B,C)`,
  MP_TAC(INST_TYPE [`:N`,`:M`] CONGRUENT_TRIANGLES_ASA_FULL) THEN
  MESON_TAC[DIST_SYM; ANGLE_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Some other equivalents sometimes called the ITT (see the Web page         *)
(* http://www.sonoma.edu/users/w/wilsonst/Courses/Math_150/Theorems/itt.html *)
(* ------------------------------------------------------------------------- *)

let lemma = prove
 (`!A B C D:real^N.
        between D (A,B)
        ==> (orthogonal (A - B) (C - D) <=>
                angle(A,D,C) = pi / &2 /\ angle(B,D,C) = pi / &2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `D:real^N = A` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[ANGLE_REFL] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ORTHOGONAL_LNEG] THEN
    REWRITE_TAC[VECTOR_NEG_SUB; ORTHOGONAL_VECTOR_ANGLE; angle];
    ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N = B` THENL
   [DISCH_TAC THEN ASM_SIMP_TAC[ANGLE_REFL] THEN
    REWRITE_TAC[ORTHOGONAL_VECTOR_ANGLE; angle];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `D:real^N`; `C:real^N`]
      ANGLES_ALONG_LINE) THEN
  ASM_REWRITE_TAC[ORTHOGONAL_VECTOR_ANGLE] THEN
  MATCH_MP_TAC(REAL_ARITH
   `x = z ==> x + y = p ==> (z = p / &2 <=> x = p / &2 /\ y = p / &2)`) THEN
  REWRITE_TAC[angle] THEN MATCH_MP_TAC VECTOR_ANGLE_EQ_0_RIGHT THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_ANGLE_NEG2] THEN
  REWRITE_TAC[VECTOR_NEG_SUB; GSYM angle] THEN
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE]);;

let ISOSCELES_TRIANGLE_1 = prove
 (`!A B C D:real^N.
        dist(A,C) = dist(B,C) /\ D = midpoint(A,B)
        ==> angle(A,C,D) = angle(B,C,D)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`A:real^N`; `D:real^N`; `C:real^N`;
                 `B:real^N`; `D:real^N`; `C:real^N`]
        CONGRUENT_TRIANGLES_SSS_FULL) THEN
  ASM_REWRITE_TAC[DIST_MIDPOINT] THEN ASM_MESON_TAC[DIST_SYM; ANGLE_SYM]);;

let ISOSCELES_TRIANGLE_2 = prove
 (`!A B C D:real^N.
        between D (A,B) /\
        dist(A,C) = dist(B,C) /\ angle(A,C,D) = angle(B,C,D)
        ==> orthogonal (A - B) (C - D)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ISOSCELES_TRIANGLE_THEOREM) THEN
  MP_TAC(ISPECL [`D:real^N`; `C:real^N`; `A:real^N`;
                 `D:real^N`; `C:real^N`; `B:real^N`]
        CONGRUENT_TRIANGLES_SAS_FULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM; ANGLE_SYM]; ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N = B` THEN
  ASM_SIMP_TAC[DIST_EQ_0; DIST_REFL; VECTOR_SUB_REFL; ORTHOGONAL_0] THEN
  ASM_CASES_TAC `D:real^N = A` THENL [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[lemma] THEN
  MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `D:real^N`; `C:real^N`]
      ANGLES_ALONG_LINE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let ISOSCELES_TRIANGLE_3 = prove
 (`!A B C D:real^N.
        between D (A,B) /\
        dist(A,C) = dist(B,C) /\ orthogonal (A - B) (C - D)
        ==> D = midpoint(A,B)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `A:real^N = B` THEN
  ASM_SIMP_TAC[BETWEEN_REFL_EQ; MIDPOINT_REFL] THEN
  ASM_CASES_TAC `D:real^N = A` THENL
   [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`B:real^N`; `A:real^N`; `C:real^N`] PYTHAGORAS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_LNEG; VECTOR_NEG_SUB]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist] THEN
    ASM_REWRITE_TAC[REAL_RING `a = x pow 2 + a <=> x = &0`; DIST_EQ_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `D:real^N = B` THENL
   [ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`] PYTHAGORAS) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_LNEG; VECTOR_NEG_SUB]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist] THEN
    ASM_REWRITE_TAC[REAL_RING `a = x pow 2 + a <=> x = &0`; DIST_EQ_0];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[lemma; MIDPOINT_COLLINEAR; BETWEEN_IMP_COLLINEAR] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ISOSCELES_TRIANGLE_THEOREM) THEN
  MP_TAC(ISPECL
   [`A:real^N`; `C:real^N`; `D:real^N`;
    `B:real^N`; `C:real^N`; `D:real^N`]
        CONGRUENT_TRIANGLES_SAS) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^N`; `C:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `D:real^N`] TRIANGLE_ANGLE_SUM) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_EQ_0]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a:real = a' /\ b = b'
    ==> a + x + b = p ==> a' + x' + b' = p ==> x' = x`) THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[ANGLE_SYM]] THEN
  CONV_TAC SYM_CONV THEN
  UNDISCH_TAC `angle(C:real^N,A,B) = angle (A,B,C)` THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [MATCH_MP_TAC ANGLE_EQ_0_LEFT;
    GEN_REWRITE_TAC RAND_CONV [ANGLE_SYM] THEN
    MATCH_MP_TAC ANGLE_EQ_0_RIGHT] THEN
  ASM_MESON_TAC[ANGLE_EQ_PI_OTHERS; BETWEEN_ANGLE]);;

(* ------------------------------------------------------------------------- *)
(* Now the converses to those as well.                                       *)
(* ------------------------------------------------------------------------- *)

let ISOSCELES_TRIANGLE_4 = prove
 (`!A B C D:real^N.
        D = midpoint(A,B) /\ orthogonal (A - B) (C - D)
        ==> dist(A,C) = dist(B,C)`,
  REPEAT GEN_TAC THEN ASM_SIMP_TAC[IMP_CONJ; BETWEEN_MIDPOINT; lemma] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC CONGRUENT_TRIANGLES_SAS THEN
  MAP_EVERY EXISTS_TAC [`D:real^N`; `D:real^N`] THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "D" THEN REWRITE_TAC[DIST_MIDPOINT]);;

let ISOSCELES_TRIANGLE_5 = prove
 (`!A B C D:real^N.
        ~collinear{D,C,A} /\ between D (A,B) /\
        angle(A,C,D) = angle(B,C,D) /\ orthogonal (A - B) (C - D)
        ==> dist(A,C) = dist(B,C)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `C:real^N = D` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  UNDISCH_TAC `~(C:real^N = D)` THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT; GSYM CONJ_ASSOC] THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `C:real^N = A` THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[ANGLE_REFL] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BETWEEN_ANGLE]) THEN
    ASM_CASES_TAC `D:real^N = A` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `D:real^N = B` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ARITH `x / &2 = &0 <=> x = &0`;
                 PI_NZ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ANGLE_EQ_PI_OTHERS) THEN
    MP_TAC PI_NZ THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `C:real^N = B` THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[ANGLE_REFL] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BETWEEN_ANGLE]) THEN
    ASM_CASES_TAC `D:real^N = B` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `D:real^N = A` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[ANGLE_REFL_MID; REAL_ARITH `&0 = x / &2 <=> x = &0`;
                 PI_NZ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ANGLE_EQ_PI_OTHERS) THEN
    MP_TAC PI_NZ THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[IMP_CONJ; lemma] THEN
  REPEAT DISCH_TAC THEN MP_TAC(
    ISPECL [`D:real^N`; `C:real^N`; `A:real^N`;
            `D:real^N`; `C:real^N`; `B:real^N`]
     CONGRUENT_TRIANGLES_ASA_FULL) THEN
  ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
  ONCE_REWRITE_TAC[ANGLE_SYM] THEN ASM_REWRITE_TAC[]);;

let ISOSCELES_TRIANGLE_6 = prove
 (`!A B C D:real^N.
        ~collinear{D,C,A} /\ D = midpoint(A,B) /\ angle(A,C,D) = angle(B,C,D)
        ==> dist(A,C) = dist(B,C)`,
  REPEAT GEN_TAC THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_CASES_TAC `A:real^N = B` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^N`; `C:real^N`; `D:real^N`] LAW_OF_SINES) THEN
  MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `D:real^N`] LAW_OF_SINES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXPAND_TAC "D" THEN REWRITE_TAC[DIST_MIDPOINT] THEN
  ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ; REAL_HALF; DIST_POS_LT;
               SIN_ANGLE_EQ] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`D:real^N`; `C:real^N`; `A:real^N`;
                   `D:real^N`; `C:real^N`; `B:real^N`]
       CONGRUENT_TRIANGLES_AAS) THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[DIST_SYM]] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ANGLE_SYM] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`A:real^N`; `B:real^N`; `C:real^N`]
                TRIANGLE_ANGLE_SUM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `angle(A:real^N,B,C) = angle(C,B,D) /\
                  angle(B,A,C) = angle(C,A,D)`
     (CONJUNCTS_THEN SUBST1_TAC)
    THENL
     [CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [ANGLE_SYM] THEN
      MATCH_MP_TAC ANGLE_EQ_0_LEFT THEN
      MP_TAC(ISPECL [`A:real^N`; `B:real^N`] BETWEEN_MIDPOINT) THEN
      ASM_REWRITE_TAC[BETWEEN_ANGLE] THEN EXPAND_TAC "D" THEN
      REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[ANGLE_EQ_PI_OTHERS];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_ARITH `a + pi - a + x = pi <=> x = &0`] THEN
    MAP_EVERY ASM_CASES_TAC
     [`B:real^N = C`; `A:real^N = C`] THEN
    ASM_REWRITE_TAC[ANGLE_REFL; REAL_ARITH `p / &2 = &0 <=> p = &0`] THEN
    ASM_REWRITE_TAC[PI_NZ] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`B:real^N`; `C:real^N`; `A:real^N`] COLLINEAR_ANGLE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~collinear{D:real^N,C,A}` THEN
    MATCH_MP_TAC(TAUT `(q ==> p) ==> ~p ==> q ==> r`) THEN
    ONCE_REWRITE_TAC[SET_RULE `{bd,c,a} = {c,a,bd}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN
    REWRITE_TAC[COLLINEAR_LEMMA] THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    EXPAND_TAC "D" THEN REWRITE_TAC[midpoint] THEN
    REWRITE_TAC[VECTOR_ARITH `inv(&2) % (A + B) - A = inv(&2) % (B - A)`] THEN
    MESON_TAC[VECTOR_MUL_ASSOC]]);;
