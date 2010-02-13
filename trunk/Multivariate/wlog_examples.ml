(* ========================================================================= *)
(* Examples of using the "without loss of generality" tactics.               *)
(* ========================================================================= *)

needs "Multivariate/wlog.ml";;

(* ------------------------------------------------------------------------- *)
(* Example 1.                                                                *)
(* ------------------------------------------------------------------------- *)

let lemma = prove
 (`(?y. y pow 2 = a) <=> &0 <= a`,
  MESON_TAC[SQRT_POW_2; REAL_LE_SQUARE; REAL_POW_2]);;

let TRUONG_1 = prove
 (`!u1:real^3 u2 p a b.
     ~(u1 = u2) /\
     plane p /\
     {u1,u2} SUBSET p /\
     dist(u1,u2) <= a + b /\
     abs(a - b) < dist(u1,u2) /\
     &0 <= a /\
     &0 <= b
     ==> (?d1 d2.
              {d1, d2} SUBSET p /\
              &1 / &2 % (d1 + d2) IN affine hull {u1, u2} /\
              dist(d1,u1) = a /\
              dist(d1,u2) = b /\
              dist(d2,u1) = a /\
              dist(d2,u2) = b)`,
  (*** First, rotate the plane p to the special case z$3 = &0 ***)

  GEOM_HORIZONTAL_PLANE_TAC `p:real^3->bool` THEN

  (*** Now reshuffle the goal to have explicit restricted quantifiers ***)

  ONCE_REWRITE_TAC[TAUT
   `a /\ b /\ c /\ d ==> e <=> c /\ a /\ b /\ d ==> e`] THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN

  (*** Now replace quantifiers over real^3 with those over real^2 ***)

  PAD2D3D_TAC THEN

  (*** Tidy the goal a little ***)

  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN

  (*** Choose u1 as the origin ***)

  GEOM_ORIGIN_TAC `u1:real^2` THEN

  (*** Rotate the point u2 onto the x-axis ***)

  GEOM_HORIZONTAL_LINE_TAC `u2:real^2` THEN

  (*** Only now introduce coordinates ***)

  X_GEN_TAC `u2:real^2` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
  REWRITE_TAC[dist; VECTOR_SUB_RZERO; VECTOR_SUB_LZERO; NORM_NEG] THEN
  SIMP_TAC[GSYM real_gt; NORM_GT_SQUARE; NORM_EQ_SQUARE; NORM_LE_SQUARE] THEN
  REWRITE_TAC[real_gt; REAL_ARITH `~(abs x < &0)`] THEN
  ASM_SIMP_TAC[DOT_2; REAL_MUL_RZERO; REAL_ADD_RID; CART_EQ; DIMINDEX_2;
               FORALL_2; AFFINE_HULL_2; CART_EQ; VECTOR_MUL_COMPONENT;
               VECTOR_SUB_COMPONENT; VEC_COMPONENT; ARITH; IN_ELIM_THM;
               VECTOR_ADD_COMPONENT; REAL_SUB_RZERO; REAL_ADD_LID;
               REAL_POW2_ABS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o GSYM) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[EXISTS_VECTOR_2] THEN
  MATCH_MP_TAC(MESON[]
   `(?x y:real. P x y x (--y)) ==> (?x y x' y'. P x y x' y')`) THEN
  SIMP_TAC[AFFINE_HULL_2; IN_ELIM_THM; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
        VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; ARITH] THEN
  ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID; REAL_ADD_RINV] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `~(a = &0)
    ==> (u + v = &1 /\ b = v * a <=> u = &1 - b / a /\ v = b / a)`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  ABBREV_TAC `u = (u2:real^2)$1` THEN
  REWRITE_TAC[REAL_ARITH `x + --y * --y:real = x + y * y`] THEN
  REWRITE_TAC[TAUT `a /\ b /\ a /\ b <=> a /\ b`] THEN

  (*** Now finally dive in and solve the algebraic problem ***)

  ASM_SIMP_TAC[REAL_FIELD
   `~(u = &0)
    ==> (x * x + y * y = a pow 2 /\ (x - u) * (x - u) + y * y = b pow 2 <=>
         x = (u pow 2 + a pow 2 - b pow 2) / (&2 * u) /\
         y pow 2 = b pow 2 - (x - u) pow 2)`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; lemma] THEN
  ASM_SIMP_TAC[REAL_SUB_LE; REAL_FIELD
   `(u pow 2 + a - b) / (&2 * u) - u = (a - b - u pow 2) / (&2 * u)`] THEN
  REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN
  ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ;
               REAL_ARITH `~(u = &0) ==> &0 < abs(&2 * u)`] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_LE_SQUARE_ABS] THEN

  (*** Can just use SOS: this proof was found by SOS_RULE ***)

  MAP_EVERY UNDISCH_TAC
   [`u * u <= (a + b) pow 2`; `(a - b) pow 2 < u * u`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_IMP_LE) THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
  REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LE_MUL) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definition of "opposite" for example 2, and its invariance theorems.      *)
(* ------------------------------------------------------------------------- *)

let opposite = new_definition
  `opposite a b p <=>
        (&1 / &2 % (a + b)) IN p /\
        (!x y:real^N. {x,y} SUBSET p ==> (x - y) dot (a - b) = &0)`;;

let OPPOSITE_TRANSLATION_EQ = prove
 (`!c a b p. opposite (c + a) (c + b) (IMAGE (\x. c + x) p) <=>
             opposite a b p`,
  REWRITE_TAC[opposite] THEN GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [OPPOSITE_TRANSLATION_EQ];;

let OPPOSITE_LINEAR_IMAGE_EQ = prove
 (`!f a b p. linear f /\ (!x. norm(f x) = norm x)
             ==> (opposite (f a) (f b) (IMAGE f p) <=> opposite a b p)`,
  SIMP_TAC[opposite; INSERT_SUBSET; EMPTY_SUBSET; GSYM orthogonal] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  SIMP_TAC[GSYM LINEAR_ADD; GSYM LINEAR_SUB; ORTHOGONAL_LINEAR_IMAGE_EQ] THEN
  SIMP_TAC[GSYM LINEAR_CMUL; IN_IMAGE] THEN
  MESON_TAC[PRESERVES_NORM_INJECTIVE]);;

add_linear_invariants [OPPOSITE_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Example 2.                                                                *)
(* ------------------------------------------------------------------------- *)

let AFFINE_PLANE = prove
 (`!p. plane p ==> affine p`,
  SIMP_TAC[plane; LEFT_IMP_EXISTS_THM; AFFINE_AFFINE_HULL]);;

let lemma = prove
 (`!a b:real^2.
        a$2 <= &0 /\ &0 <= b$2 ==> ?x. x IN convex hull {a,b} /\ x$2 = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `a <= &0 /\ &0 <= b ==> a = &0 /\ b = &0 \/ &0 < b - a`))
  THENL
   [EXISTS_TAC `a:real^2` THEN ASM_SIMP_TAC[HULL_INC; IN_INSERT];
    REWRITE_TAC[CONVEX_HULL_2_ALT; EXISTS_IN_GSPEC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT;
             DIMINDEX_2; ARITH] THEN
    EXISTS_TAC `--(a$2) / ((b:real^2)$2 - (a:real^2)$2)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_DIV_RMUL;
                 REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
    ASM_REAL_ARITH_TAC]);;

let TRUONG_OPPOSITE_LEMMA = prove
 (`!p a b bb m x y:real^3.
     plane p /\
     {a, b, bb, m, x, y} SUBSET p /\
     ~(x = y) /\ m IN affine hull {x,y} /\ midpoint(b,bb) = m
     ==> ~(convex hull {a, b} INTER affine hull {x, y} = {}) \/
         ~(convex hull {a, bb} INTER affine hull {x, y} = {})`,

  (*** Make the plane p the xy-plane ***)

  GEOM_HORIZONTAL_PLANE_TAC `p:real^3->bool` THEN

  (*** Rewrite with explicit restricted quantifiers ***)

  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(K ALL_TAC) THEN

  (*** Now replace quantifiers over real^3 with those over real^2 ***)

  PAD2D3D_TAC THEN

  (*** Let x be the origin, and y on the x-axis ***)

  GEOM_ORIGIN_TAC `x:real^2` THEN
  GEOM_HORIZONTAL_LINE_TAC `y:real^2` THEN

  (*** Make a few simplifications ***)

  GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
  DISCH_THEN(ASSUME_TAC o GSYM) THEN
  SIMP_TAC[midpoint; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           DIMINDEX_2; ARITH] THEN

  (*** Show aff{x,y} is now exactly the x-axis ***)

  SUBGOAL_THEN `affine hull {vec 0,y} = {u:real^2 | u$2 = &0}` SUBST1_TAC THENL
   [MATCH_MP_TAC HULL_UNIQUE THEN
    REWRITE_TAC[affine; INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[VEC_COMPONENT; DIMINDEX_2; ARITH; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    X_GEN_TAC `s:real^2->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `u:real^2` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `u = (&1 - u$1 / (y:real^2)$1) % vec 0 +
                  (u$1 / (y:real^2)$1) % y`
    SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
      ASM_SIMP_TAC[CART_EQ; VECTOR_MUL_COMPONENT; DIMINDEX_2; ARITH;
                   FORALL_2; REAL_MUL_RZERO; REAL_DIV_RMUL];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN

  (*** Simplify a bit more ***)

  SIMP_TAC[IN_ELIM_THM; REAL_ARITH `inv(&2) * (x + y) = &0 <=> y = --x`] THEN
  REPEAT STRIP_TAC THEN

  (*** Finally, make a 4-way case split then apply the lemma to each ***)

  REWRITE_TAC[SET_RULE `~(s INTER t = {}) <=> ?x. x IN s /\ x IN t`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_ASSUM(MP_TAC o SPEC `(a:real^2)$2` o MATCH_MP (REAL_ARITH
   `b' = --b ==> !a. a <= &0 /\ &0 <= b \/ a <= &0 /\ &0 <= b' \/
                     b <= &0 /\ &0 <= a \/ b' <= &0 /\ &0 <= a`)) THEN
  MESON_TAC[lemma; SET_RULE `{a,b} = {b,a}`]);;

let TRUONG_OPPOSITE_THM = prove
 (`!a b bb x y:real^3 p.
     ~(x = y) /\
     plane p /\
     {a, b, x, y} SUBSET p /\
     opposite b bb (affine hull {x, y})
     ==> ~(convex hull {a, b} INTER affine hull {x, y} = {}) \/
         ~(convex hull {a, bb} INTER affine hull {x, y} = {})`,
  REWRITE_TAC[opposite; INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC TRUONG_OPPOSITE_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`p:real^3->bool`; `&1 / &2 % (b + bb):real^3`] THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; midpoint] THEN
  CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC]  THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFFINE_PLANE) THEN
  MATCH_MP_TAC(TAUT `b /\ (b ==> a) ==> a /\ b`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!t. x IN t /\ t SUBSET s ==> x IN s`) THEN
    EXISTS_TAC `affine hull {x:real^3,y}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    DISCH_TAC THEN SUBST1_TAC(VECTOR_ARITH
      `bb:real^3 = -- &1 % b + &2 % &1 / &2 % (b + bb)`) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[affine]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Affsign variants for example 3, and invariance theorems.                  *)
(* ------------------------------------------------------------------------- *)

let lin_combo = new_definition
  `lin_combo V f = vsum V (\v. f v % (v:real^N))`;;

let affsign = new_definition
  `affsign sgn s t (v:real^A) <=>
     (?f. (v = lin_combo (s UNION t) f) /\
          (!w. t w ==> sgn (f w)) /\
          (sum (s UNION t) f = &1))`;;

let sgn_gt = new_definition `sgn_gt = (\t. (&0 < t))`;;
let sgn_ge = new_definition `sgn_ge = (\t. (&0 <= t))`;;
let sgn_lt = new_definition `sgn_lt = (\t. (t < &0))`;;
let sgn_le = new_definition `sgn_le = (\t. (t <= &0))`;;

let aff_gt_def = new_definition `aff_gt = affsign sgn_gt`;;
let aff_ge_def = new_definition `aff_ge = affsign sgn_ge`;;
let aff_lt_def = new_definition `aff_lt = affsign sgn_lt`;;
let aff_le_def = new_definition `aff_le = affsign sgn_le`;;

let AFFSIGN = prove
 (`affsign sgn s t =
        {y | ?f. y = vsum (s UNION t) (\v. f v % v) /\
                (!w. w IN t ==> sgn(f w)) /\
                sum (s UNION t) f = &1}`,
  REWRITE_TAC[FUN_EQ_THM; affsign; lin_combo; IN_ELIM_THM] THEN
  REWRITE_TAC[IN]);;

let AFFSIGN_ALT = prove
 (`affsign sgn s t =
        {y | ?f. (!w. w IN (s UNION t) ==> w IN t ==> sgn(f w)) /\
                 sum (s UNION t) f = &1 /\
                 vsum (s UNION t) (\v. f v % v) = y}`,
  REWRITE_TAC[SET_RULE `(w IN (s UNION t) ==> w IN t ==> P w) <=>
                        (w IN t ==> P w)`] THEN
  REWRITE_TAC[AFFSIGN; EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

let IN_AFFSIGN = prove
 (`y IN affsign sgn s t <=>
        ?u. (!x. x IN t ==> sgn(u x)) /\
            sum (s UNION t) u = &1 /\
            vsum (s UNION t) (\x. u(x) % x) = y`,
  REWRITE_TAC[AFFSIGN; IN_ELIM_THM] THEN SET_TAC[]);;

let AFFSIGN_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N sgn s t v.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (affsign sgn (IMAGE f s) (IMAGE f t) =
             IMAGE f (affsign sgn s t))`,
  let lemma0 = prove
   (`vsum s (\x. u x % x) = vsum {x | x IN s /\ ~(u x = &0)} (\x. u x % x)`,
    MATCH_MP_TAC VSUM_SUPERSET THEN SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[TAUT `p /\ ~(p /\ ~q) <=> p /\ q`] THEN
    SIMP_TAC[o_THM; VECTOR_MUL_LZERO]) in
  let lemma1 = prove
   (`!f:real^M->real^N s.
           linear f /\ (!x y. f x = f y ==> x = y)
           ==> (sum(IMAGE f s) u = &1 /\ vsum(IMAGE f s) (\x. u x % x) = y <=>
                sum s (u o f) = &1 /\ f(vsum s (\x. (u o f) x % x)) = y)`,
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o funpow 3 lhand o snd) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MATCH_MP_TAC(MESON[] `(p ==> z = x) ==> (p /\ x = y <=> p /\ z = y)`) THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[lemma0] THEN
    SUBGOAL_THEN
     `{y | y IN IMAGE (f:real^M->real^N) s /\ ~(u y = &0)} =
      IMAGE f {x | x IN s /\ ~(u(f x) = &0)}`
    SUBST1_TAC THENL [ASM SET_TAC[]; CONV_TAC SYM_CONV] THEN
    SUBGOAL_THEN `FINITE {x | x IN s /\ ~(u((f:real^M->real^N) x) = &0)}`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
       (LAND_CONV o RATOR_CONV o RATOR_CONV) [sum]) THEN
      ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
      REWRITE_TAC[GSYM sum; support; NEUTRAL_REAL_ADD; o_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ];
      W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o lhand o snd) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
      ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; GSYM LINEAR_CMUL]]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[EXTENSION; IN_AFFSIGN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE; IN_AFFSIGN] THEN
  REWRITE_TAC[GSYM IMAGE_UNION] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP lemma1 th]) THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `vsum (s UNION t) (\x. (u o (f:real^M->real^N)) x % x)` THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `(u:real^N->real) o (f:real^M->real^N)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[o_THM];
    MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
    ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M`
     (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(u:real^M->real) o (g:real^N->real^M)` THEN
    ASM_REWRITE_TAC[o_DEF; ETA_AX]]);;

let AFF_GE_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_ge (IMAGE f s) (IMAGE f t) = IMAGE f (aff_ge s t)`,
  REWRITE_TAC[aff_ge_def; AFFSIGN_INJECTIVE_LINEAR_IMAGE]);;

let AFF_GT_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_gt (IMAGE f s) (IMAGE f t) = IMAGE f (aff_gt s t)`,
  REWRITE_TAC[aff_gt_def; AFFSIGN_INJECTIVE_LINEAR_IMAGE]);;

let AFF_LE_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_le (IMAGE f s) (IMAGE f t) = IMAGE f (aff_le s t)`,
  REWRITE_TAC[aff_le_def; AFFSIGN_INJECTIVE_LINEAR_IMAGE]);;

let AFF_LT_INJECTIVE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> aff_lt (IMAGE f s) (IMAGE f t) = IMAGE f (aff_lt s t)`,
  REWRITE_TAC[aff_lt_def; AFFSIGN_INJECTIVE_LINEAR_IMAGE]);;

add_linear_invariants
  [AFFSIGN_INJECTIVE_LINEAR_IMAGE;
   AFF_GE_INJECTIVE_LINEAR_IMAGE;
   AFF_GT_INJECTIVE_LINEAR_IMAGE;
   AFF_LE_INJECTIVE_LINEAR_IMAGE;
   AFF_LT_INJECTIVE_LINEAR_IMAGE];;

let IN_AFFSIGN_TRANSLATION = prove
 (`!sgn s t a v:real^N.
        affsign sgn s t v
        ==> affsign sgn (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) (a + v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affsign; lin_combo] THEN
  ONCE_REWRITE_TAC[SET_RULE `(!x. s x ==> p x) <=> (!x. x IN s ==> p x)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x. (f:real^N->real)(x - a)` THEN
  ASM_REWRITE_TAC[GSYM IMAGE_UNION] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC;
    ASM_REWRITE_TAC[FORALL_IN_IMAGE; ETA_AX;
                    VECTOR_ARITH `(a + x) - a:real^N = x`];
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE o lhs o snd) THEN
    SIMP_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
    ASM_REWRITE_TAC[o_DEF; VECTOR_ADD_SUB; ETA_AX]] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `a + vsum {x | x IN s UNION t /\ ~(f x = &0)} (\v:real^N. f v % v)` THEN
  CONJ_TAC THENL
   [AP_TERM_TAC THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[VECTOR_MUL_EQ_0; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `vsum (IMAGE (\x:real^N. a + x)
                          {x | x IN s UNION t /\ ~(f x = &0)})
                   (\v. f(v - a) % v)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC[VECTOR_ADD_SUB] THEN SET_TAC[]] THEN
  SUBGOAL_THEN `FINITE {x:real^N | x IN s UNION t /\ ~(f x = &0)}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
     (LAND_CONV o RATOR_CONV o RATOR_CONV) [sum]) THEN
    ONCE_REWRITE_TAC[ITERATE_EXPAND_CASES] THEN
    REWRITE_TAC[GSYM sum; support; NEUTRAL_REAL_ADD] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE o rhs o snd) THEN
  ASM_SIMP_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[o_DEF; VECTOR_ADD_SUB] THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VSUM_ADD] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[VSUM_RMUL] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_MUL_LID] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC SUM_SUPERSET THEN SET_TAC[]);;

let AFFSIGN_TRANSLATION = prove
 (`!a:real^N sgn s t.
        affsign sgn (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
        IMAGE (\x. a + x) (affsign sgn s t)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN] THEN GEN_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `--a:real^N` o
      MATCH_MP IN_AFFSIGN_TRANSLATION) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + x:real^N = x`;
                IMAGE_ID] THEN
    DISCH_TAC THEN REWRITE_TAC[IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `--a + x:real^N` THEN ASM_REWRITE_TAC[IN] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN GEN_TAC THEN REWRITE_TAC[IN] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N` o MATCH_MP IN_AFFSIGN_TRANSLATION) THEN
    REWRITE_TAC[]]);;

let AFF_GE_TRANSLATION = prove
 (`!a:real^N s t.
        aff_ge (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
        IMAGE (\x. a + x) (aff_ge s t)`,
  REWRITE_TAC[aff_ge_def; AFFSIGN_TRANSLATION]);;

let AFF_GT_TRANSLATION = prove
 (`!a:real^N s t.
        aff_gt (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
        IMAGE (\x. a + x) (aff_gt s t)`,
  REWRITE_TAC[aff_gt_def; AFFSIGN_TRANSLATION]);;

let AFF_LE_TRANSLATION = prove
 (`!a:real^N s t.
        aff_le (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
        IMAGE (\x. a + x) (aff_le s t)`,
  REWRITE_TAC[aff_le_def; AFFSIGN_TRANSLATION]);;

let AFF_LT_TRANSLATION = prove
 (`!a:real^N s t.
        aff_lt (IMAGE (\x. a + x) s) (IMAGE (\x. a + x) t) =
        IMAGE (\x. a + x) (aff_lt s t)`,
  REWRITE_TAC[aff_lt_def; AFFSIGN_TRANSLATION]);;

add_translation_invariants
  [AFFSIGN_TRANSLATION;
   AFF_GE_TRANSLATION;
   AFF_GT_TRANSLATION;
   AFF_LE_TRANSLATION;
   AFF_LT_TRANSLATION];;

(* ------------------------------------------------------------------------- *)
(* Example 3.                                                                *)
(* ------------------------------------------------------------------------- *)

let NOT_COPLANAR_NOT_COLLINEAR = prove
 (`!v1 v2 v3 w:real^N. ~coplanar {v1, v2, v3, w} ==> ~collinear {v1, v2, v3}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COLLINEAR_AFFINE_HULL; coplanar; CONTRAPOS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN STRIP_TAC THEN
  EXISTS_TAC `w:real^N` THEN ASM_SIMP_TAC[HULL_INC; IN_INSERT] THEN
  REPEAT CONJ_TAC THEN
  MATCH_MP_TAC(SET_RULE `!t. t SUBSET s /\ x IN t ==> x IN s`) THEN
  EXISTS_TAC `affine hull {x:real^N,y}` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

let AFFINE_DEPENDENT_IMP_COLLINEAR_3 = prove
 (`!a b c:real^N. affine_dependent {a,b,c} ==> collinear{a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affine_dependent] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2; COLLINEAR_AFFINE_HULL] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:real^N`; `c:real^N`];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `c:real^N`];
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`]] THEN
  SIMP_TAC[INSERT_SUBSET; EMPTY_SUBSET; HULL_INC; IN_INSERT] THEN
  POP_ASSUM MP_TAC THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> a IN s ==> a IN t`) THEN
  MATCH_MP_TAC HULL_MONO THEN SET_TAC[]);;

let AFFSIGN = prove
 (`affsign sgn s t =
        {y | ?f. y = vsum (s UNION t) (\v. f v % v) /\
                (!w. w IN t ==> sgn(f w)) /\
                sum (s UNION t) f = &1}`,
  REWRITE_TAC[FUN_EQ_THM; affsign; lin_combo; IN_ELIM_THM] THEN
  REWRITE_TAC[IN]);;

let IN_AFFSIGN = prove
 (`y IN affsign sgn s t <=>
        ?u. (!x. x IN (s UNION t) ==> x IN t ==> sgn(u x)) /\
            sum (s UNION t) u = &1 /\
            vsum (s UNION t) (\x. u(x) % x) = y`,
  REWRITE_TAC[AFFSIGN; IN_ELIM_THM] THEN SET_TAC[]);;

let LEMMA = prove
 (`!v1 v2 v3 w:real^3 p.
     plane p /\ {v1, v2, v3} SUBSET p /\
     ~coplanar {v1, v2, v3, w}
     ==> (?n n'. norm(n - n') = &1 /\
                (!x. x IN aff_ge {v1, v2, v3} {w} <=>
                     (?xx h.
                          xx IN affine hull {v1, v2, v3} /\
                          &0 <= h /\
                          x - xx = h % (n - n'))) /\
                (!x y.
                     {x, y} SUBSET affine hull {v1, v2, v3}
                     ==> (n - n') dot (x - y) = &0))`,
  GEOM_HORIZONTAL_PLANE_TAC `p:real^3->bool` THEN
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
  MAP_EVERY (fun t ->
   ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[INSERT_AC; COPLANAR_3]; ALL_TAC])
   [`v1:real^3 = v2`; `v1:real^3 = v3`; `v2:real^3 = v3`;
    `v1:real^3 = w`; `v2:real^3 = w`; `v3:real^3 = w`] THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `vec 0:real^3` THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  SUBGOAL_THEN `~((w:real^3)$3 = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~coplanar{v1:real^3,v2,v3,w}` THEN
    REWRITE_TAC[coplanar] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [plane]) THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN affine hull {v1,v2,v3}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{v1:real^3,v2,v3}` DEPENDENT_BIGGERSET_GENERAL) THEN
    ANTS_TAC THENL
     [DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[GT] THEN
      MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `dim {z:real^3 | z$3 = &0}` THEN
      CONJ_TAC THENL [MATCH_MP_TAC DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[DIM_SPECIAL_HYPERPLANE; DIMINDEX_3; ARITH] THEN
      REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP NOT_COPLANAR_NOT_COLLINEAR) THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC COLLINEAR_SMALL THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_RULES];
      ALL_TAC] THEN
    REWRITE_TAC[DEPENDENT_AFFINE_DEPENDENT_CASES] THEN
    ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3;
                  NOT_COPLANAR_NOT_COLLINEAR];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull {v1,v2,v3} = {z:real^3 | z$3 = &0}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN] THEN
    MATCH_MP_TAC(SET_RULE
     `!s. t SUBSET u /\ s SUBSET t /\ u SUBSET s ==> t = u`) THEN
    EXISTS_TAC `span {x - v1:real^3 | x IN {v2,v3}}` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN MATCH_MP_TAC SPAN_INDUCT THEN
      REWRITE_TAC[SET_RULE `(\x. x IN s) = s`] THEN
      SIMP_TAC[SUBSPACE_SPECIAL_HYPERPLANE; DIMINDEX_3; ARITH] THEN
      ASM_SIMP_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
      MATCH_MP_TAC SPAN_MONO THEN
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      MESON_TAC[SPAN_SUB; SPAN_INC; IN_INSERT; SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM;
                  FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH; REAL_SUB_REFL];
      REWRITE_TAC[independent] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        DEPENDENT_IMP_AFFINE_DEPENDENT)) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3;
                    NOT_COPLANAR_NOT_COLLINEAR];
      SIMP_TAC[DIM_SPECIAL_HYPERPLANE; DIMINDEX_3; ARITH] THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      SIMP_TAC[CARD_IMAGE_INJ; FINITE_INSERT; FINITE_RULES;
               VECTOR_ARITH `x - a:real^N = y - a <=> x = y`] THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_RULES;
                   IN_INSERT; NOT_IN_EMPTY; ARITH]];
    ALL_TAC] THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `~(x = &0) ==> &0 < x \/ &0 < --x`))
  THENL
   [EXISTS_TAC `basis 3:real^3`; EXISTS_TAC `--(basis 3):real^3`] THEN
  ASM_SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; IN_ELIM_THM; DOT_BASIS;
               NORM_NEG; DOT_LNEG; DIMINDEX_3; ARITH; VECTOR_SUB_COMPONENT;
               REAL_SUB_REFL; REAL_NEG_0] THEN
  X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[aff_ge_def; IN_AFFSIGN; sgn_ge] THEN
  REWRITE_TAC[SET_RULE `{a,b,c} UNION {d} = {a,b,c,d}`] THEN
  REWRITE_TAC[SET_RULE `x IN {a} <=> a = x`] THEN
  SIMP_TAC[AFFINE_HULL_FINITE_STEP_GEN; REAL_LE_ADD; FINITE_INSERT;
           CONJUNCT1 FINITE_RULES; REAL_ARITH `&0 <= x / &2 <=> &0 <= x`;
           RIGHT_EXISTS_AND_THM] THEN
  ASM_REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[REAL_ARITH `x - y:real = z <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ARITH `x - y:real^3 = z <=> x = y + z`] THEN
  REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `&1 = x + y <=> x + y = &1`] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`; `h:real`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `a % v1 + b % v2 + c % v3 +
                h % ((w:real^3)$1 % basis 1 + w$2 % basis 2):real^3` THEN
    EXISTS_TAC `h * (w:real^3)$3` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB;
                GSYM VECTOR_ADD_ASSOC] THEN
    REPLICATE_TAC 4 AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; CONJUNCT1 FINITE_RULES] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; VECTOR_ADD_RID];

    MAP_EVERY X_GEN_TAC [`y:real^3`; `h:real`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(vec 0:real^3) IN affine hull {v1,v2,v3}` THEN
    SUBGOAL_THEN `(y - h / (w:real^3)$3 % (w$1 % basis 1 + w$2 % basis 2))
                  IN affine hull {v1:real^3,v2,v3}` MP_TAC THENL
     [ASM_SIMP_TAC[IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
            VECTOR_SUB_COMPONENT; BASIS_COMPONENT; ARITH; DIMINDEX_3] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; CONJUNCT1 FINITE_RULES;
             AFFINE_HULL_FINITE_STEP; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = z <=> x = y + z`] THEN
    REWRITE_TAC[VECTOR_ARITH `x - y:real^3 = z <=> x = y + z`] THEN
    REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[REAL_ARITH `&1 = x + y <=> x + y = &1`] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`; `c':real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC
     [`a + (&1 - (a + b + c + h / (w:real^3)$3)) * a'`;
      `b + (&1 - (a + b + c + h / (w:real^3)$3)) * b'`;
      `c + (&1 - (a + b + c + h / (w:real^3)$3)) * c'`; `h / (w:real^3)$3`] THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `(a + x * a') + (b + x * b') + (c + x * c') + h:real =
      (a + b + c + h) + x * (a' + b' + c')`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + x * a') % v1 + (b + x * b') % v2 + (c + x * c') % v3 + h:real^N =
      (a % v1 + b % v2 + c % v3) + x % (a' % v1 + b' % v2 + c' % v3) + h`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(x + a) + y:real^3 = a + z <=> x + y = z`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; CONJUNCT1 FINITE_RULES] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; VECTOR_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; GSYM VECTOR_ADD_ASSOC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_RMUL; REAL_LT_IMP_NZ];

    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`; `h:real`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `a % v1 + b % v2 + c % v3 +
                h % ((w:real^3)$1 % basis 1 + w$2 % basis 2):real^3` THEN
    EXISTS_TAC `h * --((w:real^3)$3)` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[VECTOR_ARITH `(x * --y) % --z:real^N = (x * y) % z`] THEN
    ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
                 DIMINDEX_3; ARITH; REAL_MUL_RZERO; REAL_ADD_RID] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB;
                GSYM VECTOR_ADD_ASSOC] THEN
    REPLICATE_TAC 4 AP_TERM_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM BASIS_EXPANSION] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; CONJUNCT1 FINITE_RULES] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; VECTOR_ADD_RID];

    MAP_EVERY X_GEN_TAC [`y:real^3`; `h:real`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(vec 0:real^3) IN affine hull {v1,v2,v3}` THEN
    SUBGOAL_THEN `(y - h / --((w:real^3)$3) % (w$1 % basis 1 + w$2 % basis 2))
                  IN affine hull {v1:real^3,v2,v3}` MP_TAC THENL
     [ASM_SIMP_TAC[IN_ELIM_THM; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
            VECTOR_SUB_COMPONENT; BASIS_COMPONENT; ARITH; DIMINDEX_3] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[AFFINE_HULL_FINITE; FINITE_INSERT; CONJUNCT1 FINITE_RULES;
             AFFINE_HULL_FINITE_STEP; IN_ELIM_THM] THEN
    REWRITE_TAC[REAL_ARITH `x - y:real = z <=> x = y + z`] THEN
    REWRITE_TAC[VECTOR_ARITH `x - y:real^3 = z <=> x = y + z`] THEN
    REWRITE_TAC[VECTOR_ADD_RID; REAL_ADD_RID; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[REAL_ARITH `&1 = x + y <=> x + y = &1`] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`] THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`a':real`; `b':real`; `c':real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
    MAP_EVERY EXISTS_TAC
     [`a + (&1 - (a + b + c + h / --((w:real^3)$3))) * a'`;
      `b + (&1 - (a + b + c + h / --((w:real^3)$3))) * b'`;
      `c + (&1 - (a + b + c + h / --((w:real^3)$3))) * c'`;
      `h / --((w:real^3)$3)`] THEN
    ASM_REWRITE_TAC[REAL_ARITH
     `(a + x * a') + (b + x * b') + (c + x * c') + h:real =
      (a + b + c + h) + x * (a' + b' + c')`] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `(a + x * a') % v1 + (b + x * b') % v2 + (c + x * c') % v3 + h:real^N =
      (a % v1 + b % v2 + c % v3) + x % (a' % v1 + b' % v2 + c' % v3) + h`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(x + a) + y:real^3 = a + z <=> x + y = z`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    REWRITE_TAC[DIMINDEX_3] THEN CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_INSERT; CONJUNCT1 FINITE_RULES] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ; VECTOR_ADD_RID] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; GSYM VECTOR_ADD_ASSOC] THEN
    REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG] THEN
    REWRITE_TAC[VECTOR_MUL_RNEG; VECTOR_MUL_LNEG; GSYM real_div] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

let THEOREM = prove
 (`!v1 v2 v3 w:real^3.
     ~coplanar {v1, v2, v3, w}
     ==> (?nor. norm nor = &1 /\
                (!x. x IN aff_ge {v1, v2, v3} {w} <=>
                     (?xx h.
                          xx IN affine hull {v1, v2, v3} /\
                          &0 <= h /\
                          x = xx + h % nor)) /\
                (!x y.
                     {x, y} SUBSET affine hull {v1, v2, v3}
                     ==> nor dot (x - y) = &0))`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^3 = y + h % z <=> x - y = h % z`] THEN
  MATCH_MP_TAC(MESON[] `(?a b. P(a - b)) ==> ?a:real^3. P a`) THEN
  MATCH_MP_TAC LEMMA THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `affine hull {v1:real^3,v2,v3}` THEN
  REWRITE_TAC[HULL_SUBSET; plane] THEN
  ASM_MESON_TAC[NOT_COPLANAR_NOT_COLLINEAR]);;
