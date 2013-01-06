(* ========================================================================= *)
(* Proof that Tarski's axioms for geometry hold in Euclidean space.          *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Axiom 1 (reflexivity for equidistance).                                   *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_1_EUCLIDEAN = prove
 (`!a b:real^2. dist(a,b) = dist(b,a)`,
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Axiom 2 (transitivity for equidistance).                                  *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_2_EUCLIDEAN = prove
 (`!a b p q r s.
        dist(a,b) = dist(p,q) /\ dist(a,b) = dist(r,s)
        ==> dist(p,q) = dist(r,s)`,
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Axiom 3 (identity for equidistance).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_3_EUCLIDEAN = prove
 (`!a b c. dist(a,b) = dist(c,c) ==> a = b`,
  NORM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Axiom 4 (segment construction).                                           *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_4_EUCLIDEAN = prove
 (`!a q b c:real^2. ?x:real^2. between a (q,x) /\ dist(a,x) = dist(b,c)`,
  GEOM_ORIGIN_TAC `a:real^2` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[DIST_0] THEN ASM_CASES_TAC `q:real^2 = vec 0` THENL
   [ASM_SIMP_TAC[BETWEEN_REFL; VECTOR_CHOOSE_SIZE; DIST_POS_LE];
    EXISTS_TAC `--(dist(b:real^2,c) / norm(q) % q):real^2` THEN
    REWRITE_TAC[between; DIST_0] THEN
    REWRITE_TAC[dist; NORM_MUL; NORM_NEG; REAL_ABS_DIV; REAL_ABS_NORM;
                VECTOR_ARITH `q - --(a % q) = (&1 + a) % q`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_RING `a = &1 + b ==> a * q = q + b * q`) THEN
      SIMP_TAC[REAL_ABS_REFL; REAL_POS; REAL_LE_ADD; REAL_LE_DIV; NORM_POS_LE];
      ASM_SIMP_TAC[REAL_DIV_RMUL; NORM_EQ_0]]]);;

(* ------------------------------------------------------------------------- *)
(* Axiom 5 (five-segments axiom).                                            *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_5_EUCLIDEAN = prove
 (`!a b c x:real^2 a' b' c' x':real^2.
        ~(a = b) /\
        dist(a,b) = dist(a',b') /\
        dist(a,c) = dist(a',c') /\
        dist(b,c) = dist(b',c') /\
        between b (a,x) /\ between b' (a',x') /\ dist(b,x) = dist(b',x')
        ==> dist(c,x) = dist(c',x')`,
  let lemma = prove
   (`!a b x y:real^N.
      ~(b = a) /\ between b (a,x) /\ between b (a,y) /\ dist(b,x) = dist(b,y)
      ==> x = y`,
    REPEAT STRIP_TAC THEN REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE
     [IMP_CONJ] BETWEEN_EXISTS_EXTENSION))) THEN ASM_SIMP_TAC[] THEN
    REPEAT STRIP_TAC THEN UNDISCH_TAC `dist(b:real^N,x) = dist(b,y)` THEN
    ASM_REWRITE_TAC[NORM_ARITH `dist(b:real^N,b + x) = norm x`; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; NORM_EQ_0; real_abs; VECTOR_SUB_EQ]) in
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`a:real^2`; `b:real^2`; `c:real^2`; `a':real^2`; `b':real^2`; `c':real^2`]
   RIGID_TRANSFORMATION_BETWEEN_3) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_EQ_0; DIST_SYM]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2`
   (X_CHOOSE_THEN `f:real^2->real^2` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  SUBGOAL_THEN `x' = k + (f:real^2->real^2) x` SUBST1_TAC THENL
   [MATCH_MP_TAC lemma THEN MAP_EVERY EXISTS_TAC
      [`k + (f:real^2->real^2) a`; `k + (f:real^2->real^2) b`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a + y) = dist(x,y)`;
    BETWEEN_TRANSLATION; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
  ASM_MESON_TAC[BETWEEN_TRANSLATION; orthogonal_transformation;
                NORM_ARITH `dist(a + x:real^N,a + y) = dist(x,y)`;
                ORTHOGONAL_TRANSFORMATION_ISOMETRY; BETWEEN_LINEAR_IMAGE_EQ;
                DIST_EQ_0; ORTHOGONAL_TRANSFORMATION_INJECTIVE]);;

(* ------------------------------------------------------------------------- *)
(* Axiom 6 (identity for between-ness).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_6_EUCLIDEAN = prove
 (`!a b. between b (a,a) ==> a = b`,
  SIMP_TAC[BETWEEN_REFL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Axiom 7 (Pasch's axiom).                                                  *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_7_EUCLIDEAN = prove
 (`!a b c p q:real^2.
        between p (a,c) /\ between q (b,c)
        ==> ?x. between x (p,b) /\ between x (q,a)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `q:real^2 = c` THENL
   [ASM_MESON_TAC[BETWEEN_REFL; BETWEEN_SYM]; POP_ASSUM MP_TAC] THEN
  ASM_CASES_TAC `p:real^2 = a /\ b:real^2 = q` THENL
   [ASM_MESON_TAC[BETWEEN_REFL; BETWEEN_SYM]; POP_ASSUM MP_TAC] THEN
  GEOM_ORIGIN_TAC `a:real^2` THEN GEOM_NORMALIZE_TAC `q:real^2` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[BETWEEN_REFL_EQ] THEN
    REWRITE_TAC[UNWIND_THM2; between; DIST_0] THEN NORM_ARITH_TAC;
    ALL_TAC] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `q:real^2` THEN SIMP_TAC
   [NORM_MUL; NORM_BASIS; real_abs; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
  GEN_TAC THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN SIMP_TAC[VECTOR_MUL_LID] THEN
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[BETWEEN_SYM] THEN DISCH_TAC THEN
  DISCH_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC o
     REWRITE_RULE[BETWEEN_IN_SEGMENT; IN_SEGMENT])
   (MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] BETWEEN_EXISTS_EXTENSION))) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  SUBGOAL_THEN `&0 < &1 - d + e` ASSUME_TAC THENL
   [ASM_CASES_TAC `d = &1 /\ e = &0` THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_eq o concl))) THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_MUL_RZERO] THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; IMP_IMP];
    EXISTS_TAC `(&1 - d + e - d * e) / (&1 - d + e) % basis 1:real^2` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `e / (&1 - d + e)` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
      REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
      SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; BASIS_COMPONENT; VEC_COMPONENT;
       ARITH; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
       VECTOR_SUB_COMPONENT] THEN
      UNDISCH_TAC `&0 < &1 - d + e` THEN CONV_TAC REAL_FIELD;
      EXISTS_TAC `(&1 - d + e - d * e) / (&1 - d + e)` THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ] THEN
      SUBGOAL_THEN `&0 <= (&1 - d) * (&1 + e) /\ &0 <= d * e` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Axiom 8 (lower 2-dimensional axiom).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_8_EUCLIDEAN = prove
 (`?a b c:real^2. ~between b (a,c) /\ ~between c (b,a) /\ ~between a (c,b)`,
  REWRITE_TAC[GSYM DE_MORGAN_THM] THEN ONCE_REWRITE_TAC[BETWEEN_SYM] THEN
  REWRITE_TAC[GSYM COLLINEAR_BETWEEN_CASES; COLLINEAR_3_2D] THEN
  MAP_EVERY EXISTS_TAC
   [`vec 0:real^2`; `basis 1:real^2`; `basis 2:real^2`] THEN
  SIMP_TAC[BASIS_COMPONENT; VEC_COMPONENT; DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Axiom 9 (upper 2-dimensional axiom).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_9_EUCLIDEAN = prove
 (`!p q a b c:real^2.
        ~(p = q) /\
        dist(a,p) = dist(a,q) /\ dist(b,p) = dist(b,q) /\ dist(c,p) = dist(c,q)
        ==> between b (a,c) \/ between c (b,a) \/ between a (c,b)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[BETWEEN_SYM] THEN
  REWRITE_TAC[GSYM COLLINEAR_BETWEEN_CASES] THEN
  REWRITE_TAC[dist; NORM_EQ; NORM_ARITH
    `~(p = q) <=> ~(norm(p - q) = &0)`] THEN
  ONCE_REWRITE_TAC[REAL_RING `~(x = &0) <=> ~(x pow 2 = &0)`] THEN
  REWRITE_TAC[NORM_POW_2; COLLINEAR_3_2D] THEN
  REWRITE_TAC[DOT_2; VECTOR_SUB_COMPONENT] THEN
  CONV_TAC REAL_FIELD);;

(* ------------------------------------------------------------------------- *)
(* Axiom 10 (Euclidean axiom).                                               *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_10_EUCLIDEAN = prove
 (`!a b c d t:real^N.
        between d (a,t) /\ between d (b,c) /\ ~(a = d)
        ==> ?x y. between b (a,x) /\ between c (a,y) /\ between t (x,y)`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `d:real^N`; `t:real^N`]
        BETWEEN_EXISTS_EXTENSION) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; VECTOR_ARITH
   `d + u % (d - vec 0):real^N = (&1 + u) % d`] THEN
  X_GEN_TAC `u:real` THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(&1 + u) % b:real^N`; `(&1 + u) % c:real^N`] THEN
  ASM_REWRITE_TAC[between; dist; GSYM VECTOR_SUB_LDISTRIB] THEN
  ASM_REWRITE_TAC[VECTOR_SUB_LZERO; NORM_NEG;
                  VECTOR_ARITH `b - (&1 + u) % b:real^N = --(u % b)`] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_LE_ADD; REAL_POS; real_abs] THEN
  REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; REAL_EQ_MUL_LCANCEL] THEN
  ASM_REWRITE_TAC[GSYM dist; GSYM between] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Axiom 11 (Continuity).                                                    *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_11_EUCLIDEAN = prove
 (`!X Y:real^2->bool.
        (?a. !x y. x IN X /\ y IN Y ==> between x (a,y))
        ==> (?b. !x y. x IN X /\ y IN Y ==> between b (x,y))`,
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN GEOM_ORIGIN_TAC `a:real^2` THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `!x:real^2. x IN X ==> x = vec 0` THENL
   [ASM_MESON_TAC[BETWEEN_REFL]; POP_ASSUM MP_TAC] THEN
  ASM_CASES_TAC `Y:real^2->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `?c:real^2. c IN Y` (CHOOSE_THEN MP_TAC) THENL
   [ASM SET_TAC[]; REPEAT(POP_ASSUM MP_TAC)] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `c:real^2` THEN
  X_GEN_TAC `c:real` THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(LABEL_TAC "*") THEN
  SUBGOAL_THEN `X SUBSET IMAGE (\c. c % basis 1:real^2) {c | &0 <= c} /\
                Y SUBSET IMAGE (\c. c % basis 1:real^2) {c | &0 <= c}`
  MP_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
       [`x:real^2`; `c % basis 1:real^2`]) THEN
      ASM_REWRITE_TAC[BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; IN_ELIM_THM] THEN
      ASM_MESON_TAC[VECTOR_MUL_ASSOC; REAL_LE_MUL];
      DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `~(z:real^2 = vec 0)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
      STRIP_TAC THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPECL [`z:real^2`; `y:real^2`]) THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      REWRITE_TAC[BETWEEN_IN_SEGMENT; IN_SEGMENT] THEN
      REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
      ASM_CASES_TAC `u = &0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0] THEN
      STRIP_TAC THEN EXISTS_TAC `inv(u) * d:real` THEN
      ASM_REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; VECTOR_MUL_LID]];
    REWRITE_TAC[SUBSET_IMAGE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s:real->bool` STRIP_ASSUME_TAC)
     (X_CHOOSE_THEN `t:real->bool` STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "*" MP_TAC THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    DISCH_THEN(fun th ->
      EXISTS_TAC `sup s % basis 1 :real^2` THEN MP_TAC th) THEN
    REWRITE_TAC[between; dist; NORM_ARITH `norm(vec 0 - x) = norm x`] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_RDISTRIB; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_GE_1; LE_REFL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `&0 <= x /\ &0 <= y ==> (abs y = abs x + abs(x - y) <=> x <= y)`] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real` THEN DISCH_TAC THEN
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `x <= s /\ s <= y ==> abs(x - y) = abs(x - s) + abs(s - y)`) THEN
    MP_TAC(SPEC `s:real->bool` SUP) THEN
    ASM_MESON_TAC[IMAGE_EQ_EMPTY; MEMBER_NOT_EMPTY]]);;
