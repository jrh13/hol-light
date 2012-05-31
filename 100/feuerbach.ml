(* ========================================================================= *)
(* Feuerbach's theorem.                                                      *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Algebraic condition for two circles to be tangent to each other.          *)
(* ------------------------------------------------------------------------- *)

let CIRCLES_TANGENT = prove
 (`!r1 r2 c1 c2.
        &0 <= r1 /\ &0 <= r2 /\
        (dist(c1,c2) = r1 + r2 \/ dist(c1,c2) = abs(r1 - r2))
        ==> c1 = c2 /\ r1 = r2 \/
            ?!x:real^2. dist(c1,x) = r1 /\ dist(c2,x) = r2`,
  MATCH_MP_TAC REAL_WLOG_LE THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC(MESON[]
     `(!x y. P x y <=> Q y x) ==> ((!x y. P x y) <=> (!x y. Q x y))`) THEN
    MESON_TAC[DIST_SYM; REAL_ADD_SYM; REAL_ABS_SUB]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `r1 = &0` THENL
   [ASM_REWRITE_TAC[DIST_EQ_0; MESON[] `(?!x. a = x /\ P x) <=> P a`] THEN
    REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `r2 = &0` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_ARITH `r1 <= r2 ==> abs(r1 - r2) = r2 - r1`] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN STRIP_TAC THENL
   [DISJ2_TAC THEN REWRITE_TAC[EXISTS_UNIQUE] THEN
    EXISTS_TAC `c1 + r1 / (r1 + r2) % (c2 - c1):real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[dist;
       VECTOR_ARITH `c1 - (c1 + a % (x - y)):real^2 = a % (y - x)`;
        VECTOR_ARITH `z - (x + a % (z - x)):real^N = (a - &1) % (x - z)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; GSYM dist] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG;
                   REAL_FIELD `&0 < r1 /\ &0 < r2
                       ==> r1 / (r1 + r2) - &1 = --r2 / (r1 + r2)`] THEN
      ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_LT_ADD] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN segment[c1,c2]` MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
        ASM_MESON_TAC[DIST_SYM];
        REWRITE_TAC[IN_SEGMENT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(c1:real^2,(&1 - u) % c1 + u % c2) = r1` THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % c1 + u % c2:real^N = c1 + u % (c2 - c1)`] THEN
      REWRITE_TAC[NORM_ARITH `dist(x:real^2,x + y) = norm y`] THEN
      ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
      REWRITE_TAC[VECTOR_ARITH `--(a % (x - y)):real^N = a % (y - x)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; GSYM dist; real_abs] THEN
      DISCH_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD];
    ASM_CASES_TAC `r1:real = r2` THENL
     [ASM_MESON_TAC[REAL_SUB_REFL; DIST_EQ_0]; DISJ2_TAC] THEN
    SUBGOAL_THEN `r1 < r2` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE] THEN
    EXISTS_TAC `c2 + r2 / (r2 - r1) % (c1 - c2):real^2` THEN CONJ_TAC THENL
     [REWRITE_TAC[dist;
       VECTOR_ARITH `c1 - (c1 + a % (x - y)):real^2 = --(a % (x - y)) /\
             c1 - (c2 + a % (c1 - c2)):real^2 = (&1 - a) % (c1 - c2)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; NORM_NEG; GSYM dist] THEN
      ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NEG;
        REAL_FIELD `r1 < r2 ==> &1 - r2 / (r2 - r1) = --(r1 / (r2 - r1))`] THEN
      ASM_SIMP_TAC[real_abs; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
      X_GEN_TAC `y:real^2` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(c1:real^2) IN segment[c2,y]` MP_TAC THENL
       [ASM_REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[IN_SEGMENT]] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_CASES_TAC `u = &0` THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_SUB_RZERO] THEN
        REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_MESON_TAC[DIST_EQ_0; REAL_SUB_0];
        ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist((&1 - u) % c2 + u % y:real^2,c2) = r2 - r1` THEN
      REWRITE_TAC[VECTOR_ARITH
       `(&1 - u) % c1 + u % c2:real^N = c1 + u % (c2 - c1)`] THEN
      REWRITE_TAC[NORM_ARITH `dist(x + y:real^2,x) = norm y`] THEN
      ONCE_REWRITE_TAC[GSYM NORM_NEG] THEN
      REWRITE_TAC[VECTOR_ARITH `--(a % (x - y)):real^N = a % (y - x)`] THEN
      ASM_REWRITE_TAC[NORM_MUL; GSYM dist; real_abs] THEN
      REWRITE_TAC[VECTOR_ARITH
       `c + v % ((c + u % (y - c)) - c):real^2 = c + v % u % (y - c)`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_ARITH
       `y:real^2 = c + u % v % (y - c) <=>
        (&1 - u * v) % (y - c) = vec 0`] THEN
      DISJ1_TAC THEN
      REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]]);;

(* ------------------------------------------------------------------------- *)
(*                       Feuerbach's theorem                                 *)
(*                                                                           *)
(* Given a non-degenerate triangle abc, let the circle passing through       *)
(* the midpoints of its sides (the "9 point circle") have center "ncenter"   *)
(* and radius "nradius". Now suppose the circle with center "icenter" and    *)
(* radius "iradius" is tangent to three sides (either internally or          *)
(* externally to one side and two produced sides), meaning that it's either  *)
(* the inscribed circle or one of the three escribed circles. Then the two   *)
(* circles are tangent to each other, i.e. either they are identical or they *)
(* touch at exactly one point.                                               *)
(* ------------------------------------------------------------------------- *)

let FEUERBACH = prove
 (`!a b c mbc mac mab pbc pac pab ncenter icenter nradius iradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      dist(icenter,pbc) = iradius /\
      dist(icenter,pac) = iradius /\
      dist(icenter,pab) = iradius /\
      collinear {a,b,pab} /\ orthogonal (a - b) (icenter - pab) /\
      collinear {b,c,pbc} /\ orthogonal (b - c) (icenter - pbc) /\
      collinear {a,c,pac} /\ orthogonal (a - c) (icenter - pac)
      ==> ncenter = icenter /\ nradius = iradius \/
          ?!x:real^2. dist(ncenter,x) = nradius /\ dist(icenter,x) = iradius`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC CIRCLES_TANGENT THEN
  POP_ASSUM MP_TAC THEN MAP_EVERY (fun t ->
   ASM_CASES_TAC t THENL [ALL_TAC; ASM_MESON_TAC[DIST_POS_LE]])
   [`&0 <= nradius`; `&0 <= iradius`] THEN
  ASM_REWRITE_TAC[dist; NORM_EQ_SQUARE] THEN
  ASM_SIMP_TAC[REAL_LE_ADD; REAL_ABS_POS; GSYM NORM_POW_2; GSYM dist] THEN
  REWRITE_TAC[REAL_POW2_ABS] THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e <=> b /\ c /\ d /\ a /\ e`] THEN
  GEOM_ORIGIN_TAC `a:real^2` THEN
  GEOM_NORMALIZE_TAC `b:real^2` THEN CONJ_TAC THENL
   [REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `b:real^2` THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; real_abs] THEN
  GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[REAL_MUL_RID] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_MUL_LID] THEN
  REPEAT GEN_TAC THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)) THEN
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  REWRITE_TAC[orthogonal; dist; NORM_POW_2] THEN
  ASM_REWRITE_TAC[midpoint] THEN
  REWRITE_TAC[DOT_2; DOT_LSUB; DOT_RSUB] THEN
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VEC_COMPONENT;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* As a little bonus, verify that the circle passing through the             *)
(* midpoints of the sides is indeed a 9-point circle, i.e. it passes         *)
(* through the feet of the altitudes and the midpoints of the lines joining  *)
(* the vertices to the orthocenter (where the alititudes intersect).         *)
(* ------------------------------------------------------------------------- *)

let NINE_POINT_CIRCLE_1 = prove
 (`!a b c:real^2 mbc mac mab fbc fac fab ncenter nradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      collinear {a,b,fab} /\ orthogonal (a - b) (c - fab) /\
      collinear {b,c,fbc} /\ orthogonal (b - c) (a - fbc) /\
      collinear {c,a,fac} /\ orthogonal (c - a) (b - fac)
      ==> dist(ncenter,fab) = nradius /\
          dist(ncenter,fbc) = nradius /\
          dist(ncenter,fac) = nradius`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e <=> b /\ c /\ d /\ a /\ e`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)) THEN
  ASM_REWRITE_TAC[dist; NORM_EQ_SQUARE; REAL_POS] THEN
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  REWRITE_TAC[orthogonal; dist; NORM_POW_2] THEN
  ASM_REWRITE_TAC[midpoint] THEN
  REWRITE_TAC[DOT_2; DOT_LSUB; DOT_RSUB] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[] THEN CONV_TAC REAL_RING);;

let NINE_POINT_CIRCLE_2 = prove
 (`!a b c:real^2 mbc mac mab fbc fac fab ncenter nradius.
      ~(collinear {a,b,c}) /\
      midpoint(a,b) = mab /\
      midpoint(b,c) = mbc /\
      midpoint(c,a) = mac /\
      dist(ncenter,mbc) = nradius /\
      dist(ncenter,mac) = nradius /\
      dist(ncenter,mab) = nradius /\
      collinear {a,b,fab} /\ orthogonal (a - b) (c - fab) /\
      collinear {b,c,fbc} /\ orthogonal (b - c) (a - fbc) /\
      collinear {c,a,fac} /\ orthogonal (c - a) (b - fac) /\
      collinear {oc,a,fbc} /\ collinear {oc,b,fac} /\ collinear{oc,c,fab}
      ==> dist(ncenter,midpoint(oc,a)) = nradius /\
          dist(ncenter,midpoint(oc,b)) = nradius /\
          dist(ncenter,midpoint(oc,c)) = nradius`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e <=> b /\ c /\ d /\ a /\ e`] THEN
  REPLICATE_TAC 3 (DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC)) THEN
  ASM_REWRITE_TAC[dist; NORM_EQ_SQUARE; REAL_POS] THEN
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  REWRITE_TAC[orthogonal; dist; NORM_POW_2] THEN
  ASM_REWRITE_TAC[midpoint] THEN
  REWRITE_TAC[DOT_2; DOT_LSUB; DOT_RSUB] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[] THEN CONV_TAC REAL_RING);;
