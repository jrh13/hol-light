(* ========================================================================= *)
(* Results intended for Flyspeck.                                            *)
(* ========================================================================= *)

needs "Multivariate/polytope.ml";;
needs "Multivariate/realanalysis.ml";;
needs "Multivariate/geom.ml";;
needs "Multivariate/cross.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* Not really Flyspeck-specific but needs both angles and cross products.    *)
(* ------------------------------------------------------------------------- *)

let NORM_CROSS = prove
 (`!x y. norm(x cross y) = norm(x) * norm(y) * sin(vector_angle x y)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC REAL_POW_EQ THEN EXISTS_TAC `2` THEN
  SIMP_TAC[NORM_POS_LE; SIN_VECTOR_ANGLE_POS; REAL_LE_MUL; ARITH_EQ] THEN
  MP_TAC(SPECL [`x:real^3`; `y:real^3`] NORM_CROSS_DOT) THEN
  REWRITE_TAC[VECTOR_ANGLE] THEN
  MP_TAC(SPEC `vector_angle (x:real^3) y` SIN_CIRCLE) THEN
  CONV_TAC REAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Other miscelleneous lemmas.                                               *)
(* ------------------------------------------------------------------------- *)

let COPLANAR_INSERT_0_NEG = prove
 (`coplanar(vec 0 INSERT --x INSERT s) <=> coplanar(vec 0 INSERT x INSERT s)`,
  REWRITE_TAC[coplanar; INSERT_SUBSET] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a ==> ~(b /\ c))`] THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; SPAN_NEG_EQ]);;

let COPLANAR_IMP_NEGLIGIBLE = prove
 (`!s:real^3->bool. coplanar s ==> negligible s`,
  REWRITE_TAC[coplanar] THEN
  MESON_TAC[NEGLIGIBLE_AFFINE_HULL_3; NEGLIGIBLE_SUBSET]);;

let NOT_COPLANAR_0_4_IMP_INDEPENDENT = prove
 (`!v1 v2 v3:real^N. ~coplanar {vec 0,v1,v2,v3} ==> independent {v1,v2,v3}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[independent; CONTRAPOS_THM] THEN
  REWRITE_TAC[dependent] THEN
  SUBGOAL_THEN
   `!v1 v2 v3:real^N. v1 IN span {v2,v3} ==> coplanar{vec 0,v1,v2,v3}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[coplanar] THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `v2:real^N`; `v3:real^N`] THEN
    SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    ASM_SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN
    POP_ASSUM MP_TAC THEN SPEC_TAC(`v1:real^N`,`v1:real^N`) THEN
    REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SPAN_MONO THEN SET_TAC[];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`v2:real^N`; `v3:real^N`; `v1:real^N`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`v3:real^N`; `v1:real^N`; `v2:real^N`])]
    THEN REWRITE_TAC[INSERT_AC] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `a IN s ==> s SUBSET t ==> a IN t`)) THEN
    MATCH_MP_TAC SPAN_MONO THEN SET_TAC[]]);;

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

(* ------------------------------------------------------------------------- *)
(* Some special scaling theorems.                                            *)
(* ------------------------------------------------------------------------- *)

let SUBSET_AFFINE_HULL_SPECIAL_SCALE = prove
 (`!a x s t.
        ~(a = &0)
        ==> (vec 0 INSERT (a % x) INSERT s SUBSET affine hull t <=>
             vec 0 INSERT x INSERT s SUBSET affine hull t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INSERT_SUBSET] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; SPAN_MUL_EQ]);;

let COLLINEAR_SPECIAL_SCALE = prove
 (`!a x y. ~(a = &0) ==> (collinear {vec 0,a % x,y} <=> collinear{vec 0,x,y})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL] THEN
  ASM_SIMP_TAC[SUBSET_AFFINE_HULL_SPECIAL_SCALE]);;

let COLLINEAR_SCALE_ALL = prove
 (`!a b v w. ~(a = &0) /\ ~(b = &0)
             ==> (collinear {vec 0,a % v,b % w} <=> collinear {vec 0,v,w})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {a,c,b}`] THEN
  ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE]);;

let COPLANAR_SPECIAL_SCALE = prove
 (`!a x y z.
    ~(a = &0) ==> (coplanar {vec 0,a % x,y,z} <=> coplanar {vec 0,x,y,z})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[coplanar] THEN
  ASM_SIMP_TAC[SUBSET_AFFINE_HULL_SPECIAL_SCALE]);;

let COPLANAR_SCALE_ALL = prove
 (`!a b c x y z.
        ~(a = &0) /\ ~(b = &0) /\ ~(c = &0)
        ==> (coplanar {vec 0,a % x,b % y,c % z} <=> coplanar {vec 0,x,y,z})`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COPLANAR_SPECIAL_SCALE] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = {a,c,d,b}`] THEN
  ASM_SIMP_TAC[COPLANAR_SPECIAL_SCALE] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = {a,c,d,b}`] THEN
  ASM_SIMP_TAC[COPLANAR_SPECIAL_SCALE]);;

(* ------------------------------------------------------------------------- *)
(* Specialized lemmas about "dropout".                                       *)
(* ------------------------------------------------------------------------- *)

let DROPOUT_BASIS_3 = prove
 (`(dropout 3:real^3->real^2) (basis 1) = basis 1 /\
   (dropout 3:real^3->real^2) (basis 2) = basis 2 /\
   (dropout 3:real^3->real^2) (basis 3) = vec 0`,
  SIMP_TAC[LAMBDA_BETA; dropout; basis; CART_EQ; DIMINDEX_2; DIMINDEX_3; ARITH;
           VEC_COMPONENT; LT_IMP_LE; ARITH_RULE `i <= 2 ==> i + 1 <= 3`;
           ARITH_RULE `1 <= i + 1`] THEN
  ARITH_TAC);;

let COLLINEAR_BASIS_3 = prove
 (`collinear {vec 0,basis 3,x} <=> (dropout 3:real^3->real^2) x = vec 0`,
  SIMP_TAC[CART_EQ; FORALL_2; FORALL_3; DIMINDEX_2; DIMINDEX_3;
           dropout; LAMBDA_BETA; BASIS_COMPONENT; ARITH; REAL_MUL_RID;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RZERO; UNWIND_THM1;
           COLLINEAR_LEMMA] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM EXISTS_REFL] THEN REAL_ARITH_TAC);;

let OPEN_DROPOUT_3 = prove
 (`!P. open {x | P x} ==> open {x | P((dropout 3:real^3->real^2) x)}`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPECL
   [`dropout 3:real^3->real^2`; `{x:real^2 | P x}`]
   CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  SIMP_TAC[LINEAR_DROPOUT; DIMINDEX_2; DIMINDEX_3; ARITH]);;

let SLICE_DROPOUT_3 = prove
 (`!P t. slice 3 t {x | P((dropout 3:real^3->real^2) x)} = {x | P x}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[slice] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN
  X_GEN_TAC `y:real^2` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `(pushin 3 t:real^2->real^3) y` THEN
  ASM_SIMP_TAC[DIMINDEX_2; DIMINDEX_3; DROPOUT_PUSHIN; ARITH] THEN
  SIMP_TAC[pushin; LAMBDA_BETA; LT_REFL; DIMINDEX_3; ARITH]);;

let NOT_COPLANAR_IMP_NOT_COLLINEAR_DROPOUT_3 = prove
 (`!x y:real^3.
        ~coplanar {vec 0,basis 3, x, y}
        ==> ~collinear {vec 0,dropout 3 x:real^2,dropout 3 y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_AFFINE_HULL; coplanar] THEN
  REWRITE_TAC[CONTRAPOS_THM; INSERT_SUBSET; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN
  REWRITE_TAC[EMPTY_SUBSET] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [AFFINE_HULL_2]) THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real`;`b:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?r s. a * r + b * s = -- &1` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `a = &0` THENL
     [UNDISCH_TAC `a + b = &1` THEN
      ASM_SIMP_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_MUL_LID; EXISTS_REFL];
      ASM_SIMP_TAC[REAL_FIELD
       `~(a = &0) ==> (a * r + x = y <=> r = (y - x) / a)`] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `vector[(u:real^2)$1; u$2; r]:real^3` THEN
  EXISTS_TAC `vector[(v:real^2)$1; v$2; s]:real^3` THEN
  EXISTS_TAC `basis 3:real^3` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[AFFINE_HULL_3; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY EXISTS_TAC [`a / &2`;`b / &2`; `&1 / &2`] THEN
    ASM_REWRITE_TAC[REAL_ARITH
      `a / &2 + b / &2 + &1 / &2 = &1 <=> a + b = &1`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CART_EQ]) THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3;
             VEC_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             VECTOR_3; BASIS_COMPONENT; ARITH] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SYM)) THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN] THEN DISCH_TAC THEN
  SIMP_TAC[SPAN_SUPERSET; IN_INSERT] THEN
  SUBGOAL_THEN
    `!x. (dropout 3:real^3->real^2) x IN span {u,v}
         ==> x IN span {vector [u$1; u$2; r], vector [v$1; v$2; s], basis 3}`
    (fun th -> ASM_MESON_TAC[th]) THEN
  GEN_TAC THEN REWRITE_TAC[SPAN_2; SPAN_3] THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; CART_EQ; DIMINDEX_2; DIMINDEX_3;
           FORALL_2; FORALL_3; dropout; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
           VECTOR_MUL_COMPONENT; VECTOR_3; BASIS_COMPONENT; ARITH] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `x = a + b + c * &1 <=> c = x - a - b`] THEN
  REWRITE_TAC[EXISTS_REFL]);;

let SLICE_312 = prove
 (`!s:real^3->bool. slice 1 t s = {y:real^2 | vector[t;y$1;y$2] IN s}`,
  SIMP_TAC[EXTENSION; IN_SLICE; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; pushin; LAMBDA_BETA; FORALL_3; DIMINDEX_3; ARITH;
           VECTOR_3]);;

let SLICE_123 = prove
 (`!s:real^3->bool. slice 3 t s = {y:real^2 | vector[y$1;y$2;t] IN s}`,
  SIMP_TAC[EXTENSION; IN_SLICE; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SIMP_TAC[CART_EQ; pushin; LAMBDA_BETA; FORALL_3; DIMINDEX_3; ARITH;
           VECTOR_3]);;

(* ------------------------------------------------------------------------- *)
(* "Padding" injection from real^2 -> real^3 with zero last coordinate.      *)
(* ------------------------------------------------------------------------- *)

let pad2d3d = new_definition
 `(pad2d3d:real^2->real^3) x = lambda i. if i < 3 then x$i else &0`;;

let FORALL_PAD2D3D_THM = prove
 (`!P. (!y:real^3. y$3 = &0 ==> P y) <=> (!x. P(pad2d3d x))`,
  GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[pad2d3d] THEN
    SIMP_TAC[LAMBDA_BETA; DIMINDEX_3; ARITH; LT_REFL];
    FIRST_X_ASSUM(MP_TAC o SPEC `(lambda i. (y:real^3)$i):real^2`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; pad2d3d; DIMINDEX_3; ARITH; LAMBDA_BETA; DIMINDEX_2;
             ARITH_RULE `i < 3 <=> i <= 2`] THEN
    REWRITE_TAC[ARITH_RULE `i <= 3 <=> i <= 2 \/ i = 3`] THEN
    ASM_MESON_TAC[]]);;

let QUANTIFY_PAD2D3D_THM = prove
 (`(!P. (!y:real^3. y$3 = &0 ==> P y) <=> (!x. P(pad2d3d x))) /\
   (!P. (?y:real^3. y$3 = &0 /\ P y) <=> (?x. P(pad2d3d x)))`,
  REWRITE_TAC[MESON[] `(?y. P y) <=> ~(!x. ~P x)`] THEN
  REWRITE_TAC[GSYM FORALL_PAD2D3D_THM] THEN MESON_TAC[]);;

let LINEAR_PAD2D3D = prove
 (`linear pad2d3d`,
  REWRITE_TAC[linear; pad2d3d] THEN
  SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
           LAMBDA_BETA; DIMINDEX_2; DIMINDEX_3; ARITH;
           ARITH_RULE `i < 3 ==> i <= 2`] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REAL_ARITH_TAC);;

let INJECTIVE_PAD2D3D = prove
 (`!x y. pad2d3d x = pad2d3d y ==> x = y`,
  SIMP_TAC[CART_EQ; pad2d3d; LAMBDA_BETA; DIMINDEX_3; DIMINDEX_2] THEN
  REWRITE_TAC[ARITH_RULE `i < 3 <=> i <= 2`] THEN
  MESON_TAC[ARITH_RULE `i <= 2 ==> i <= 3`]);;

let NORM_PAD2D3D = prove
 (`!x. norm(pad2d3d x) = norm x`,
  SIMP_TAC[NORM_EQ; DOT_2; DOT_3; pad2d3d; LAMBDA_BETA;
           DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Apply 3D->2D conversion to a goal. Take care to preserve variable names.  *)
(* ------------------------------------------------------------------------- *)

let PAD2D3D_QUANTIFY_CONV =
  let gv = genvar `:real^2` in
  let pth = CONV_RULE (BINOP_CONV(BINDER_CONV(RAND_CONV(GEN_ALPHA_CONV gv))))
                      QUANTIFY_PAD2D3D_THM in
  let conv1 = GEN_REWRITE_CONV I [pth]
  and dest_quant tm = try dest_forall tm with Failure _ -> dest_exists tm in
  fun tm ->
    let th = conv1 tm in
    let name = fst(dest_var(fst(dest_quant tm))) in
    let ty = snd(dest_var(fst(dest_quant(rand(concl th))))) in
    CONV_RULE(RAND_CONV(GEN_ALPHA_CONV(mk_var(name,ty)))) th;;

let PAD2D3D_TAC =
  let pad2d3d_tm = `pad2d3d`
  and pths = [LINEAR_PAD2D3D; INJECTIVE_PAD2D3D; NORM_PAD2D3D]
  and cth = prove
   (`{} = IMAGE pad2d3d {} /\
     vec 0 = pad2d3d(vec 0)`,
    REWRITE_TAC[IMAGE_CLAUSES] THEN MESON_TAC[LINEAR_PAD2D3D; LINEAR_0]) in
  let lasttac =
    GEN_REWRITE_TAC REDEPTH_CONV [LINEAR_INVARIANTS pad2d3d_tm pths] in
  fun gl -> (GEN_REWRITE_TAC ONCE_DEPTH_CONV [cth] THEN
             CONV_TAC(DEPTH_CONV PAD2D3D_QUANTIFY_CONV) THEN
             lasttac) gl;;

(* ------------------------------------------------------------------------- *)
(* The notion of a plane, and using it to characterize coplanarity.          *)
(* ------------------------------------------------------------------------- *)

let plane = new_definition
  `plane x = (?u v w. ~(collinear {u,v,w}) /\ x = affine hull {u,v,w})`;;

let PLANE_TRANSLATION_EQ = prove
 (`!a:real^N s. plane(IMAGE (\x. a + x) s) <=> plane s`,
  REWRITE_TAC[plane] THEN GEOM_TRANSLATE_TAC[]);;

let PLANE_TRANSLATION = prove
 (`!a:real^N s. plane s ==> plane(IMAGE (\x. a + x) s)`,
  REWRITE_TAC[PLANE_TRANSLATION_EQ]);;

add_translation_invariants [PLANE_TRANSLATION_EQ];;

let PLANE_LINEAR_IMAGE_EQ = prove
 (`!f:real^M->real^N p.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (plane(IMAGE f p) <=> plane p)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[plane] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
   `?u. u IN IMAGE f (:real^M) /\
        ?v. v IN IMAGE f (:real^M) /\
            ?w. w IN IMAGE (f:real^M->real^N) (:real^M) /\
                ~collinear {u, v, w} /\ IMAGE f p = affine hull {u, v, w}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[RIGHT_AND_EXISTS_THM; IN_IMAGE; IN_UNIV] THEN
    REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
    EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{u,v,w} SUBSET IMAGE (f:real^M->real^N) p` MP_TAC THENL
     [ASM_REWRITE_TAC[HULL_SUBSET]; SET_TAC[]];
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV] THEN
    REWRITE_TAC[SET_RULE `{f a,f b,f c} = IMAGE f {a,b,c}`] THEN
    ASM_SIMP_TAC[AFFINE_HULL_LINEAR_IMAGE] THEN
    REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN BINOP_TAC THENL
     [ASM_MESON_TAC[COLLINEAR_LINEAR_IMAGE_EQ]; ASM SET_TAC[]]]);;

let PLANE_LINEAR_IMAGE = prove
 (`!f:real^M->real^N p.
        linear f /\ plane p /\ (!x y. f x = f y ==> x = y)
        ==> plane(IMAGE f p)`,
  MESON_TAC[PLANE_LINEAR_IMAGE_EQ]);;

add_linear_invariants [PLANE_LINEAR_IMAGE_EQ];;

let AFFINE_PLANE = prove
 (`!p. plane p ==> affine p`,
  SIMP_TAC[plane; LEFT_IMP_EXISTS_THM; AFFINE_AFFINE_HULL]);;

let ROTATION_PLANE_HORIZONTAL = prove
 (`!s. plane s
       ==>  ?a f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                  IMAGE f (IMAGE (\x. a + x) s) = {z:real^3 | z$3 = &0}`,
  let lemma = prove
   (`span {z:real^3 | z$3 = &0} = {z:real^3 | z$3 = &0}`,
    REWRITE_TAC[SPAN_EQ_SELF; subspace; IN_ELIM_THM] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [plane]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`; `c:real^3`] THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC];
                           ALL_TAC])
   [`a:real^3 = b`; `a:real^3 = c`; `b:real^3 = c`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
  ASM_SIMP_TAC[AFFINE_HULL_INSERT_SPAN; IN_INSERT; NOT_IN_EMPTY] THEN
  EXISTS_TAC `--a:real^3` THEN
  REWRITE_TAC[SET_RULE `IMAGE (\x:real^3. --a + x) {a + x | x | x IN s} =
                        IMAGE (\x. --a + a + x) s`] THEN
  REWRITE_TAC[VECTOR_ARITH `--a + a + x:real^3 = x`; IMAGE_ID] THEN
  REWRITE_TAC[SET_RULE `{x - a:real^x | x = b \/ x = c} = {b - a,c - a}`] THEN
  MP_TAC(ISPEC `span{b - a:real^3,c - a}`
    ROTATION_LOWDIM_HORIZONTAL) THEN
  REWRITE_TAC[DIMINDEX_3] THEN ANTS_TAC THENL
   [MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `CARD{b - a:real^3,c - a}` THEN
    SIMP_TAC[DIM_SPAN; DIM_LE_CARD; FINITE_RULES] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:real^3->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  ASM_SIMP_TAC[GSYM SPAN_LINEAR_IMAGE] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM lemma] THEN
  MATCH_MP_TAC DIM_EQ_SPAN THEN CONJ_TAC THENL
   [ASM_MESON_TAC[IMAGE_SUBSET; SPAN_INC; SUBSET_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`{z:real^3 | z$3 = &0}`; `(:real^3)`] DIM_EQ_SPAN) THEN
    REWRITE_TAC[SUBSET_UNIV; DIM_UNIV; DIMINDEX_3; lemma] THEN
    MATCH_MP_TAC(TAUT `~r /\ (~p ==> q) ==> (q ==> r) ==> p`) THEN
    REWRITE_TAC[ARITH_RULE `~(x <= 2) <=> 3 <= x`] THEN
    REWRITE_TAC[EXTENSION; SPAN_UNIV; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `vector[&0;&0;&1]:real^3`) THEN
    REWRITE_TAC[IN_UNIV; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `dim {b - a:real^3,c - a}` THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[LE_REFL; DIM_INJECTIVE_LINEAR_IMAGE;
             ORTHOGONAL_TRANSFORMATION_INJECTIVE]] THEN
  MP_TAC(ISPEC `{b - a:real^3,c - a}` INDEPENDENT_BOUND_GENERAL) THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_RULES; IN_SING; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `b - a:real^3 = c - a <=> b = c`; ARITH] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (RAND_CONV o RAND_CONV)
    [SET_RULE `{a,b,c} = {b,a,c}`]) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[independent; CONTRAPOS_THM; dependent] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; RIGHT_OR_DISTRIB] THEN
  REWRITE_TAC[EXISTS_OR_THM; UNWIND_THM2] THEN
  ASM_SIMP_TAC[SET_RULE `~(a = b) ==> {a,b} DELETE b = {a}`;
               SET_RULE `~(a = b) ==> {a,b} DELETE a = {b}`;
               VECTOR_ARITH `b - a:real^3 = c - a <=> b = c`] THEN
  REWRITE_TAC[SPAN_BREAKDOWN_EQ; SPAN_EMPTY; IN_SING] THEN
  ONCE_REWRITE_TAC[VECTOR_SUB_EQ] THEN MESON_TAC[COLLINEAR_LEMMA; INSERT_AC]);;

let ROTATION_HORIZONTAL_PLANE = prove
 (`!p. plane p
       ==>  ?a f. orthogonal_transformation f /\ det(matrix f) = &1 /\
                  IMAGE (\x. a + x) (IMAGE f {z:real^3 | z$3 = &0}) = p`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP ROTATION_PLANE_HORIZONTAL) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3`
   (X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC o MATCH_MP
    ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  MAP_EVERY EXISTS_TAC [`--a:real^3`; `g:real^3->real^3`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
                  VECTOR_ARITH `--a + a + x:real^3 = x`] THEN
  MATCH_MP_TAC(REAL_RING `!f. f * g = &1 /\ f = &1 ==> g = &1`) THEN
  EXISTS_TAC `det(matrix(f:real^3->real^3))` THEN
  REWRITE_TAC[GSYM DET_MUL] THEN
  ASM_SIMP_TAC[GSYM MATRIX_COMPOSE; ORTHOGONAL_TRANSFORMATION_LINEAR] THEN
  ASM_REWRITE_TAC[o_DEF; MATRIX_ID; DET_I]);;

let COPLANAR = prove
 (`2 <= dimindex(:N)
   ==> !s:real^N->bool. coplanar s <=> ?x. plane x /\ s SUBSET x`,
  DISCH_TAC THEN GEN_TAC THEN REWRITE_TAC[coplanar; plane] THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?x u v w. p x u v w) <=> (?u v w x. p x u v w)`] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  EQ_TAC THENL [MESON_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`; `w:real^N`] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `s SUBSET {u + x:real^N | x | x IN span {y - u | y IN {v,w}}}`
  MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    REWRITE_TAC[AFFINE_HULL_INSERT_SUBSET_SPAN];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  DISCH_THEN(MP_TAC o ISPEC `\x:real^N. x - u` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ADD_SUB; IMAGE_ID; SIMPLE_IMAGE] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  MP_TAC(ISPECL [`{v - u:real^N,w - u}`; `2`] LOWDIM_EXPAND_BASIS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD{v - u:real^N,w - u}` THEN
    SIMP_TAC[DIM_LE_CARD; FINITE_INSERT; FINITE_RULES] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
   (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
  UNDISCH_TAC `span {v - u, w - u} SUBSET span {a:real^N, b}` THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP SUBSET_TRANS) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `u + a:real^N`; `u + b:real^N`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[COLLINEAR_3; COLLINEAR_LEMMA;
                VECTOR_ARITH `--x = vec 0 <=> x = vec 0`;
                VECTOR_ARITH `u - (u + a):real^N = --a`;
                VECTOR_ARITH `(u + b) - (u + a):real^N = b - a`] THEN
    REWRITE_TAC[DE_MORGAN_THM; VECTOR_SUB_EQ;
      VECTOR_ARITH `b - a = c % -- a <=> (c - &1) % a + &1 % b = vec 0`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT; INDEPENDENT_NONZERO]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `u:real`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
    REWRITE_TAC[DEPENDENT_EXPLICIT] THEN
    MAP_EVERY EXISTS_TAC [`{a:real^N,b}`;
                          `\x:real^N. if x = a then u - &1 else &1`] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES; SUBSET_REFL] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `b:real^N` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[VSUM_CLAUSES; FINITE_RULES] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; VECTOR_ADD_RID];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFFINE_HULL_INSERT_SPAN o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_ARITH `u = u + a <=> a = vec 0`] THEN
    ASM_MESON_TAC[INDEPENDENT_NONZERO; IN_INSERT];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `\x:real^N. u + x` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID;
              ONCE_REWRITE_RULE[VECTOR_ADD_SYM] VECTOR_SUB_ADD] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; VECTOR_ADD_SUB] THEN
  SET_TAC[]);;

let COPLANAR_DET_EQ_0 = prove
 (`!v0 v1 (v2: real^3) v3.
        coplanar {v0,v1,v2,v3} <=>
        det(vector[v1 - v0; v2 - v0; v3 - v0]) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DET_EQ_0_RANK; RANK_ROW] THEN
  REWRITE_TAC[rows; row; LAMBDA_ETA] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  REWRITE_TAC[GSYM numseg; DIMINDEX_3] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUMSEG_CONV) THEN
  SIMP_TAC[IMAGE_CLAUSES; coplanar; VECTOR_3] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`; `c:real^3`] THEN
    W(MP_TAC o PART_MATCH lhand AFFINE_HULL_INSERT_SUBSET_SPAN o
        rand o lhand o snd) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP SUBSET_TRANS) THEN
    DISCH_THEN(MP_TAC o ISPEC `\x:real^3. x - a` o MATCH_MP IMAGE_SUBSET) THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF; VECTOR_ADD_SUB; IMAGE_ID;
                SIMPLE_IMAGE] THEN
    REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM DIM_SPAN] THEN MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `CARD {b - a:real^3,c - a}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SPAN_CARD_GE_DIM;
      SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN ARITH_TAC] THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_RULES] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM SPAN_SPAN] THEN
    MATCH_MP_TAC SPAN_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    MP_TAC(VECTOR_ARITH `!x y:real^3. x - y = (x - a) - (y - a)`) THEN
    DISCH_THEN(fun th -> REPEAT CONJ_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [th]) THEN
    MATCH_MP_TAC SPAN_SUB THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`{v1 - v0,v2 - v0,v3 - v0}:real^3->bool`; `2`]
                  LOWDIM_EXPAND_BASIS) THEN
    ASM_REWRITE_TAC[ARITH_RULE `n <= 2 <=> n < 3`; DIMINDEX_3; ARITH] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool`
     (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC) THEN
    SIMP_TAC[COPLANAR; DIMINDEX_3; ARITH; plane] THEN
    MAP_EVERY EXISTS_TAC [`v0:real^3`; `v0 + a:real^3`; `v0 + b:real^3`] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFFINE_HULL_INSERT_SPAN o
      rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[VECTOR_ARITH `u = u + a <=> a = vec 0`] THEN
      ASM_MESON_TAC[INDEPENDENT_NONZERO; IN_INSERT];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; IMAGE_ID; VECTOR_ADD_SUB] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC
     `IMAGE (\v:real^3. v0 + v) (span{v1 - v0, v2 - v0, v3 - v0})` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `vec 0:real^3` THEN REWRITE_TAC[SPAN_0] THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH `v1:real^N = v0 + x <=> x = v1 - v0`] THEN
      REWRITE_TAC[UNWIND_THM2] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_INSERT]]]);;

let COPLANAR_CROSS_DOT = prove
 (`!v w x y. coplanar {v,w,x,y} <=> ((w - v) cross (x - v)) dot (y - v) = &0`,
  REWRITE_TAC[COPLANAR_DET_EQ_0; GSYM DOT_CROSS_DET] THEN
  MESON_TAC[CROSS_TRIPLE; DOT_SYM]);;

let PLANE_AFFINE_HULL_3 = prove
 (`!a b c:real^N. plane(affine hull {a,b,c}) <=> ~collinear{a,b,c}`,
  REWRITE_TAC[plane] THEN MESON_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR]);;

let AFFINE_HULL_3_GENERATED = prove
 (`!s u v w:real^N.
        s SUBSET affine hull {u,v,w} /\ ~collinear s
        ==> affine hull {u,v,w} = affine hull s`,
  REWRITE_TAC[COLLINEAR_AFF_DIM; INT_NOT_LE] THEN REPEAT STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM HULL_HULL] THEN
  MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&2:int` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_INT_ARITH_TAC] THEN
  REWRITE_TAC[AFF_DIM_AFFINE_HULL] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) AFF_DIM_LE_CARD o lhand o snd) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] INT_LE_TRANS) THEN
  REWRITE_TAC[INT_LE_SUB_RADD; INT_OF_NUM_ADD; INT_OF_NUM_LE] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Additional WLOG tactic to rotate any plane p to {z | z$3 = &0}.           *)
(* ------------------------------------------------------------------------- *)

let GEOM_HORIZONTAL_PLANE_RULE =
  let ifn = MATCH_MP
   (TAUT `(p ==> (x <=> x')) /\ (~p ==> (x <=> T)) ==> (x' ==> x)`)
  and pth = prove
   (`!a f. orthogonal_transformation (f:real^N->real^N)
           ==> ((!P. (!x. P x) <=> (!x. P (a + f x))) /\
                (!P. (?x. P x) <=> (?x. P (a + f x))) /\
                (!Q. (!s. Q s) <=> (!s. Q (IMAGE (\x. a + x) (IMAGE f s)))) /\
                (!Q. (?s. Q s) <=> (?s. Q (IMAGE (\x. a + x) (IMAGE f s))))) /\
               (!P. {x | P x} =
                    IMAGE (\x. a + x) (IMAGE f {x | P(a + f x)}))`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPEC `(\x. a + x) o (f:real^N->real^N)`
      QUANTIFY_SURJECTION_THM) THEN REWRITE_TAC[o_THM; IMAGE_o] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE;
                  VECTOR_ARITH `a + (x - a:real^N) = x`])
  and cth = prove
   (`!a f. {} = IMAGE (\x:real^3. a + x) (IMAGE f {})`,
    REWRITE_TAC[IMAGE_CLAUSES])
  and oth = prove
   (`!f:real^3->real^3.
        orthogonal_transformation f /\ det(matrix f) = &1
        ==> linear f /\
            (!x y. f x = f y ==> x = y) /\
            (!y. ?x. f x = y) /\
            (!x. norm(f x) = norm x) /\
            (2 <= dimindex(:3) ==> det(matrix f) = &1)`,
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]])
  and fth = MESON[]
   `(!a f. q a f ==> (p <=> p' a f))
    ==> ((?a f. q a f) ==> (p <=> !a f. q a f ==> p' a f))` in
  fun tm ->
    let x,bod = dest_forall tm in
    let th1 = EXISTS_GENVAR_RULE
      (UNDISCH(ISPEC x ROTATION_HORIZONTAL_PLANE)) in
    let [a;f],tm1 = strip_exists(concl th1) in
    let [th_orth;th_det;th_im] = CONJUNCTS(ASSUME tm1) in
    let th2 = PROVE_HYP th_orth (UNDISCH(ISPECL [a;f] pth)) in
    let th3 = (EXPAND_QUANTS_CONV(ASSUME(concl th2)) THENC
               SUBS_CONV[GSYM th_im; ISPECL [a;f] cth]) bod in
    let th4 = PROVE_HYP th2 th3 in
    let th5 = TRANSLATION_INVARIANTS a in
    let th6 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV)
                [ASSUME(concl th5)] th4 in
    let th7 = PROVE_HYP th5 th6 in
    let th8s = CONJUNCTS(MATCH_MP oth (CONJ th_orth th_det)) in
    let th9 = LINEAR_INVARIANTS f th8s in
    let th10 = GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [th9] th7 in
    let th11 = if intersect (frees(concl th10)) [a;f] = []
               then PROVE_HYP th1 (itlist SIMPLE_CHOOSE [a;f] th10)
               else MP (MATCH_MP fth (GENL [a;f] (DISCH_ALL th10))) th1 in
    let th12 = REWRITE_CONV[ASSUME(mk_neg(hd(hyp th11)))] bod in
    let th13 = ifn(CONJ (DISCH_ALL th11) (DISCH_ALL th12)) in
    let th14 = MATCH_MP MONO_FORALL (GEN x th13) in
    GEN_REWRITE_RULE (TRY_CONV o LAND_CONV) [FORALL_SIMP] th14;;

let GEOM_HORIZONTAL_PLANE_TAC p =
  W(fun (asl,w) ->
        let avs,bod = strip_forall w
        and avs' = subtract (frees w) (freesl(map (concl o snd) asl)) in
        let avs,bod = strip_forall w in
        MAP_EVERY X_GEN_TAC avs THEN
        MAP_EVERY (fun t -> SPEC_TAC(t,t)) (rev(subtract (avs@avs') [p])) THEN
        SPEC_TAC(p,p) THEN
        W(MATCH_MP_TAC o GEOM_HORIZONTAL_PLANE_RULE o snd));;

(* ------------------------------------------------------------------------- *)
(* Affsign and its special cases, with invariance theorems.                  *)
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

let AFFSIGN_DISJOINT_DIFF = prove
 (`!s t. affsign sgn s t = affsign sgn (s DIFF t) t`,
  REWRITE_TAC[AFFSIGN; SET_RULE `(s DIFF t) UNION t = s UNION t`]);;

let AFF_GE_DISJOINT_DIFF = prove
 (`!s t. aff_ge s t = aff_ge (s DIFF t) t`,
  REWRITE_TAC[aff_ge_def] THEN MATCH_ACCEPT_TAC AFFSIGN_DISJOINT_DIFF);;

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
(* Automate special cases of affsign.                                        *)
(* ------------------------------------------------------------------------- *)

let AFF_TAC =
  REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[aff_ge_def; aff_gt_def; aff_le_def; aff_lt_def;
              sgn_ge; sgn_gt; sgn_le; sgn_lt; AFFSIGN_ALT] THEN
  REWRITE_TAC[SET_RULE `(x INSERT s) UNION t = x INSERT (s UNION t)`] THEN
  REWRITE_TAC[UNION_EMPTY] THEN
  SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
           FINITE_EMPTY; RIGHT_EXISTS_AND_THM; REAL_LT_ADD;
           REAL_LE_ADD; REAL_ARITH `&0 <= a / &2 <=> &0 <= a`;
           REAL_ARITH `&0 < a / &2 <=> &0 < a`;
           REAL_ARITH `a / &2 <= &0 <=> a <= &0`;
           REAL_ARITH `a / &2 < &0 <=> a < &0`;
           REAL_ARITH `a < &0 /\ b < &0 ==> a + b < &0`;
           REAL_ARITH `a < &0 /\ b <= &0 ==> a + b <= &0`] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; real_ge] THEN
  REWRITE_TAC[REAL_ARITH `x - y:real = z <=> x = y + z`;
              VECTOR_ARITH `x - y:real^N = z <=> x = y + z`] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; REAL_ADD_RID; VECTOR_ADD_RID] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `&1 = x <=> x = &1`] THEN
  REWRITE_TAC[] THEN SET_TAC[];;

let AFF_GE_1_1 = prove
 (`!x v w.
        DISJOINT {x} {v}
        ==> aff_ge {x} {v} =
             {y | ?t1 t2.
                     &0 <= t2 /\
                     t1 + t2 = &1 /\
                     y = t1 % x + t2 % v }`,
  AFF_TAC);;

let AFF_GE_1_2 = prove
 (`!x v w.
        DISJOINT {x} {v,w}
        ==> aff_ge {x} {v,w} =
             {y | ?t1 t2 t3.

                     &0 <= t2 /\ &0 <= t3 /\

                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;

let AFF_GE_2_1 = prove
 (`!x v w.
        DISJOINT {x,v} {w}
        ==> aff_ge {x,v} {w} =
             {y | ?t1 t2 t3.
                     &0 <= t3 /\
                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;

let AFF_GT_1_1 = prove
 (`!x v w.
        DISJOINT {x} {v}
        ==> aff_gt {x} {v} =
             {y | ?t1 t2.
                     &0 < t2 /\
                     t1 + t2 = &1 /\
                     y = t1 % x + t2 % v}`,
  AFF_TAC);;

let AFF_GT_1_2 = prove
 (`!x v w.
        DISJOINT {x} {v,w}
        ==> aff_gt {x} {v,w} =
             {y | ?t1 t2 t3.
                     &0 < t2 /\ &0 < t3 /\
                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;

let AFF_GT_2_1 = prove
 (`!x v w.
        DISJOINT {x,v} {w}
        ==> aff_gt {x,v} {w} =
             {y | ?t1 t2 t3.
                     &0 < t3 /\
                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;

let AFF_GT_3_1 = prove
 (`!v w x y.
        DISJOINT {v,w,x} {y}
        ==> aff_gt {v,w,x} {y} =
             {z | ?t1 t2 t3 t4.
                     &0 < t4 /\
                     t1 + t2 + t3 + t4 = &1 /\
                     z = t1 % v + t2 % w + t3 % x + t4 % y}`,
  AFF_TAC);;

let AFF_LT_1_1 = prove
 (`!x v.
        DISJOINT {x} {v}
        ==> aff_lt {x} {v} =
             {y | ?t1 t2.
                     t2 < &0 /\
                     t1 + t2 = &1 /\
                     y = t1 % x + t2 % v}`,
  AFF_TAC);;

let AFF_LT_2_1 = prove
 (`!x v w.
        DISJOINT {x,v} {w}
        ==> aff_lt {x,v} {w} =
             {y | ?t1 t2 t3.
                     t3 < &0 /\
                     t1 + t2 + t3 = &1 /\
                     y = t1 % x + t2 % v + t3 % w}`,
  AFF_TAC);;

let AFF_GE_1_2_0 = prove
 (`!v w.
        ~(v = vec 0) /\ ~(w = vec 0)
        ==> aff_ge {vec 0} {v,w} = {a % v + b % w | &0 <= a /\ &0 <= b}`,
  SIMP_TAC[AFF_GE_1_2;
           SET_RULE `DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)`] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?a b c. P b c /\ Q b c /\ R a b c /\ S b c) <=>
    (?b c. P b c /\ Q b c /\ S b c /\ ?a. R a b c)`] THEN
  REWRITE_TAC[REAL_ARITH `t + s:real = &1 <=> t = &1 - s`; EXISTS_REFL] THEN
  SET_TAC[]);;

let AFF_GE_1_1_0 = prove
 (`!v. ~(v = vec 0) ==> aff_ge {vec 0} {v} = {a % v | &0 <= a}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SET_RULE `{a} = {a,a}`] THEN
  ASM_SIMP_TAC[AFF_GE_1_2_0; GSYM VECTOR_ADD_RDISTRIB] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[REAL_LE_ADD; REAL_ARITH
   `&0 <= a ==> &0 <= a / &2 /\ a / &2 + a / &2 = a`]);;

let AFF_GE_2_1_0 = prove
 (`!v w. DISJOINT {vec 0, v} {w}
         ==> aff_ge {vec 0, v} {w} = {s % v + t % w |s,t| &0 <= t}`,
  SIMP_TAC[AFF_GE_2_1; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
  ONCE_REWRITE_TAC[MESON[] `(?a b c. P a b c) <=> (?c b a. P a b c)`] THEN
  REWRITE_TAC[REAL_ARITH `t + u = &1 <=> t = &1 - u`; UNWIND_THM2] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Properties of affsign variants.                                           *)
(* ------------------------------------------------------------------------- *)

let CONVEX_AFFSIGN = prove
 (`!sgn. (!x y u. sgn(x) /\ sgn(y) /\ &0 <= u /\ u <= &1
                  ==> sgn((&1 - u) * x + u * y))
         ==> !s t:real^N->bool. convex(affsign sgn s t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFSIGN; CONVEX_ALT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`] THEN
  REWRITE_TAC[IN_ELIM_THM; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  X_GEN_TAC `f:real^N->real` THEN STRIP_TAC THEN
  X_GEN_TAC `g:real^N->real` THEN STRIP_TAC THEN
  EXISTS_TAC `\x:real^N. (&1 - u) * f x + u * g x` THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RDISTRIB] THEN REPEAT CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    W(MP_TAC o PART_MATCH (lhs o rand) VSUM_ADD_GEN o lhand o snd) THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
    DISCH_THEN MATCH_MP_TAC;
    ASM_MESON_TAC[];
    W(MP_TAC o PART_MATCH (lhs o rand) SUM_ADD_GEN o lhand o snd) THEN
    ASM_REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; SUM_LMUL] THEN
    REWRITE_TAC[REAL_MUL_RID; REAL_SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC] THEN
  (CONJ_TAC THENL
    [MP_TAC(ASSUME `sum (s UNION t:real^N->bool) f = &1`);
     MP_TAC(ASSUME `sum (s UNION t:real^N->bool) g = &1`)]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [sum] THEN
  ONCE_REWRITE_TAC[iterate] THEN
  REWRITE_TAC[support; NEUTRAL_REAL_ADD] THEN
  COND_CASES_TAC THEN REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_THEN(K ALL_TAC) THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; REAL_MUL_RZERO]);;

let CONVEX_AFF_GE = prove
 (`!s t. convex(aff_ge s t)`,
  REWRITE_TAC[aff_ge_def; sgn_ge] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD; REAL_SUB_LE]);;

let CONVEX_AFF_LE = prove
 (`!s t. convex(aff_le s t)`,
  REWRITE_TAC[aff_le_def; sgn_le] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
  REWRITE_TAC[REAL_ARITH `x <= &0 <=> &0 <= --x`; REAL_NEG_ADD; GSYM
    REAL_MUL_RNEG] THEN
  SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD; REAL_SUB_LE]);;

let CONVEX_AFF_GT = prove
 (`!s t. convex(aff_gt s t)`,
  REWRITE_TAC[aff_gt_def; sgn_gt] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`;
              REAL_ARITH `x <= &1 <=> x = &1 \/ x < &1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_LT_ADD; REAL_LT_MUL; REAL_SUB_LT]);;

let CONVEX_AFF_LT = prove
 (`!s t. convex(aff_lt s t)`,
  REWRITE_TAC[aff_lt_def; sgn_lt] THEN MATCH_MP_TAC CONVEX_AFFSIGN THEN
  REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`; REAL_NEG_ADD; GSYM
    REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`;
              REAL_ARITH `x <= &1 <=> x = &1 \/ x < &1`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_LID] THEN
  ASM_SIMP_TAC[REAL_LT_ADD; REAL_LT_MUL; REAL_SUB_LT]);;

let AFFSIGN_SUBSET_AFFINE_HULL = prove
 (`!sgn s t. (affsign sgn s t) SUBSET (affine hull (s UNION t))`,
  REWRITE_TAC[AFFINE_HULL_FINITE; AFFSIGN] THEN SET_TAC[]);;

let AFF_GE_SUBSET_AFFINE_HULL = prove
 (`!s t. (aff_ge s t) SUBSET (affine hull (s UNION t))`,
  REWRITE_TAC[aff_ge_def; AFFSIGN_SUBSET_AFFINE_HULL]);;

let AFF_LE_SUBSET_AFFINE_HULL = prove
 (`!s t. (aff_le s t) SUBSET (affine hull (s UNION t))`,
  REWRITE_TAC[aff_le_def; AFFSIGN_SUBSET_AFFINE_HULL]);;

let AFF_GT_SUBSET_AFFINE_HULL = prove
 (`!s t. (aff_gt s t) SUBSET (affine hull (s UNION t))`,
  REWRITE_TAC[aff_gt_def; AFFSIGN_SUBSET_AFFINE_HULL]);;

let AFF_LT_SUBSET_AFFINE_HULL = prove
 (`!s t. (aff_lt s t) SUBSET (affine hull (s UNION t))`,
  REWRITE_TAC[aff_lt_def; AFFSIGN_SUBSET_AFFINE_HULL]);;

let AFFSIGN_EQ_AFFINE_HULL = prove
 (`!sgn s t. affsign sgn s {} = affine hull s`,
  REWRITE_TAC[AFFSIGN; AFFINE_HULL_FINITE] THEN
  REWRITE_TAC[UNION_EMPTY; NOT_IN_EMPTY] THEN SET_TAC[]);;

let AFF_GE_EQ_AFFINE_HULL = prove
 (`!s t. aff_ge s {} = affine hull s`,
  REWRITE_TAC[aff_ge_def; AFFSIGN_EQ_AFFINE_HULL]);;

let AFF_LE_EQ_AFFINE_HULL = prove
 (`!s t. aff_le s {} = affine hull s`,
  REWRITE_TAC[aff_le_def; AFFSIGN_EQ_AFFINE_HULL]);;

let AFF_GT_EQ_AFFINE_HULL = prove
 (`!s t. aff_gt s {} = affine hull s`,
  REWRITE_TAC[aff_gt_def; AFFSIGN_EQ_AFFINE_HULL]);;

let AFF_LT_EQ_AFFINE_HULL = prove
 (`!s t. aff_lt s {} = affine hull s`,
  REWRITE_TAC[aff_lt_def; AFFSIGN_EQ_AFFINE_HULL]);;

let AFFSIGN_SUBSET_AFFSIGN = prove
 (`!sgn1 sgn2 s t.
        (!x. sgn1 x ==> sgn2 x) ==> affsign sgn1 s t SUBSET affsign sgn2 s t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFSIGN; SUBSET; IN_ELIM_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN ASM_MESON_TAC[]);;

let AFF_GT_SUBSET_AFF_GE = prove
 (`!s t. aff_gt s t SUBSET aff_ge s t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[aff_gt_def; aff_ge_def] THEN
  MATCH_MP_TAC AFFSIGN_SUBSET_AFFSIGN THEN
  SIMP_TAC[sgn_gt; sgn_ge; REAL_LT_IMP_LE]);;

let AFFSIGN_MONO_LEFT = prove
 (`!sgn s s' t:real^N->bool.
        s SUBSET s' ==> affsign sgn s t SUBSET affsign sgn s' t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[AFFSIGN; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. if x IN s UNION t then u x else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SET_RULE
   `s SUBSET s' ==> {x | x IN s' UNION t /\ x IN s UNION t} = s UNION t`] THEN
  ASM SET_TAC[]);;

let AFFSIGN_MONO_SHUFFLE = prove
 (`!sgn s t s' t'.
        s' UNION t' = s UNION t /\ t' SUBSET t
        ==> affsign sgn s t SUBSET affsign sgn s' t'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFSIGN; SUBSET; IN_ELIM_THM] THEN
  GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let AFF_GT_MONO_LEFT = prove
 (`!s s' t. s SUBSET s' ==> aff_gt s t SUBSET aff_gt s' t`,
  REWRITE_TAC[aff_gt_def; AFFSIGN_MONO_LEFT]);;

let AFF_GE_MONO_LEFT = prove
 (`!s s' t. s SUBSET s' ==> aff_ge s t SUBSET aff_ge s' t`,
  REWRITE_TAC[aff_ge_def; AFFSIGN_MONO_LEFT]);;

let AFF_LT_MONO_LEFT = prove
 (`!s s' t. s SUBSET s' ==> aff_lt s t SUBSET aff_lt s' t`,
  REWRITE_TAC[aff_lt_def; AFFSIGN_MONO_LEFT]);;

let AFF_LE_MONO_LEFT = prove
 (`!s s' t. s SUBSET s' ==> aff_le s t SUBSET aff_le s' t`,
  REWRITE_TAC[aff_le_def; AFFSIGN_MONO_LEFT]);;

let AFFSIGN_MONO_RIGHT = prove
 (`!sgn s t t':real^N->bool.
        sgn(&0) /\ t SUBSET t' /\ DISJOINT s t'
        ==> affsign sgn s t SUBSET affsign sgn s t'`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[AFFSIGN; SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. if x IN s UNION t then u x else &0` THEN
  REWRITE_TAC[COND_RAND; COND_RATOR; VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[GSYM SUM_RESTRICT_SET; GSYM VSUM_RESTRICT_SET] THEN
  ASM_SIMP_TAC[SET_RULE
   `t SUBSET t' ==> {x | x IN s UNION t' /\ x IN s UNION t} = s UNION t`] THEN
  ASM SET_TAC[]);;

let AFF_GE_MONO_RIGHT = prove
 (`!s t t'. t SUBSET t' /\ DISJOINT s t' ==> aff_ge s t SUBSET aff_ge s t'`,
  SIMP_TAC[aff_ge_def; AFFSIGN_MONO_RIGHT; sgn_ge; REAL_POS]);;

let AFF_LE_MONO_RIGHT = prove
 (`!s t t'. t SUBSET t' /\ DISJOINT s t' ==> aff_le s t SUBSET aff_le s t'`,
  SIMP_TAC[aff_le_def; AFFSIGN_MONO_RIGHT; sgn_le; REAL_LE_REFL]);;

let AFFINE_HULL_SUBSET_AFFSIGN = prove
 (`!sgn s t:real^N->bool.
        sgn(&0) /\ DISJOINT s t
        ==> affine hull s SUBSET affsign sgn s t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `affsign sgn (s:real^N->bool) {}` THEN CONJ_TAC THENL
   [REWRITE_TAC[AFFSIGN_EQ_AFFINE_HULL; SUBSET_REFL];
    MATCH_MP_TAC AFFSIGN_MONO_RIGHT THEN ASM SET_TAC[]]);;

let AFFINE_HULL_SUBSET_AFF_GE = prove
 (`!s t. DISJOINT s t ==> affine hull s SUBSET aff_ge s t`,
  SIMP_TAC[aff_ge_def; sgn_ge; REAL_LE_REFL; AFFINE_HULL_SUBSET_AFFSIGN]);;

let AFF_GE_AFF_GT_DECOMP = prove
 (`!s:real^N->bool.
        FINITE s /\ FINITE t /\ DISJOINT s t
        ==> aff_ge s t = aff_gt s t UNION
                         UNIONS {aff_ge s (t DELETE a) | a | a IN t}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `t' SUBSET t /\ (!a. a IN s ==> f(a) SUBSET t) /\
    (!y. y IN t ==> y IN t' \/ ?a. a IN s /\ y IN f(a))
    ==> t = t' UNION UNIONS {f a | a IN s}`) THEN
  REWRITE_TAC[AFF_GT_SUBSET_AFF_GE] THEN
  ASM_SIMP_TAC[DELETE_SUBSET; AFF_GE_MONO_RIGHT] THEN
  REWRITE_TAC[aff_ge_def; aff_gt_def; AFFSIGN; sgn_ge; sgn_gt] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `!x:real^N. x IN t ==> &0 < u x` THENL
   [DISJ1_TAC THEN EXISTS_TAC `u:real^N->real` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> (&0 < x <=> ~(x = &0))`] THEN
    REWRITE_TAC[NOT_IMP] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `u:real^N->real` THEN
    ASM_SIMP_TAC[SET_RULE
     `a IN t /\ DISJOINT s t
      ==> s UNION (t DELETE a) = (s UNION t) DELETE a`] THEN
    ASM_SIMP_TAC[IN_DELETE; SUM_DELETE; VSUM_DELETE; REAL_SUB_RZERO;
                 FINITE_UNION; IN_UNION] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]]);;

let AFFSIGN_SPECIAL_SCALE = prove
 (`!sgn s t a v.
        FINITE s /\ FINITE t /\
        ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
        (!x. sgn x ==> sgn(x / &2)) /\
        (!x y. sgn x /\ sgn y ==> sgn(x + y)) /\
        &0 < a
        ==> affsign sgn (vec 0 INSERT (a % v) INSERT s) t =
            affsign sgn (vec 0 INSERT v INSERT s) t`,
  REWRITE_TAC[EXTENSION] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[AFFSIGN_ALT; IN_ELIM_THM; INSERT_UNION_EQ] THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
               RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  GEN_REWRITE_TAC BINOP_CONV [SWAP_EXISTS_THM] THEN
  GEN_REWRITE_TAC (BINOP_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[REAL_ARITH `x = &1 - v - v' <=> v = &1 - (x + v')`] THEN
  REWRITE_TAC[EXISTS_REFL] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(MESON[REAL_LT_IMP_NZ; REAL_DIV_LMUL]
   `!a. &0 < a ==> (!y. ?x. a * x = y)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
  DISCH_THEN(CONV_TAC o RAND_CONV o EXPAND_QUANTS_CONV) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_SYM]);;

let AFF_GE_SPECIAL_SCALE = prove
 (`!s t a v.
        FINITE s /\ FINITE t /\
        ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
        &0 < a
        ==> aff_ge (vec 0 INSERT (a % v) INSERT s) t =
            aff_ge (vec 0 INSERT v INSERT s) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aff_ge_def] THEN
  MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
  ASM_REWRITE_TAC[sgn_ge] THEN REAL_ARITH_TAC);;

let AFF_LE_SPECIAL_SCALE = prove
 (`!s t a v.
        FINITE s /\ FINITE t /\
        ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
        &0 < a
        ==> aff_le (vec 0 INSERT (a % v) INSERT s) t =
            aff_le (vec 0 INSERT v INSERT s) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aff_le_def] THEN
  MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
  ASM_REWRITE_TAC[sgn_le] THEN REAL_ARITH_TAC);;

let AFF_GT_SPECIAL_SCALE = prove
 (`!s t a v.
        FINITE s /\ FINITE t /\
        ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
        &0 < a
        ==> aff_gt (vec 0 INSERT (a % v) INSERT s) t =
            aff_gt (vec 0 INSERT v INSERT s) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aff_gt_def] THEN
  MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
  ASM_REWRITE_TAC[sgn_gt] THEN REAL_ARITH_TAC);;

let AFF_LT_SPECIAL_SCALE = prove
 (`!s t a v.
        FINITE s /\ FINITE t /\
        ~(vec 0 IN t) /\ ~(v IN t) /\ ~((a % v) IN t) /\
        &0 < a
        ==> aff_lt (vec 0 INSERT (a % v) INSERT s) t =
            aff_lt (vec 0 INSERT v INSERT s) t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aff_lt_def] THEN
  MATCH_MP_TAC AFFSIGN_SPECIAL_SCALE THEN
  ASM_REWRITE_TAC[sgn_lt] THEN REAL_ARITH_TAC);;

let AFF_GE_SCALE_LEMMA = prove
 (`!a u v:real^N.
        &0 < a /\ ~(v = vec 0)
        ==> aff_ge {vec 0} {a % u,v} = aff_ge {vec 0} {u,v}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u:real^N = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  ASM_SIMP_TAC[AFF_GE_1_2_0; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ;
   SET_RULE `DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)`] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; FORALL_IN_GSPEC] THEN
  CONJ_TAC THEN MAP_EVERY X_GEN_TAC [`b:real`; `c:real`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THENL
   [EXISTS_TAC `a * b:real`; EXISTS_TAC `b / a:real`] THEN
  EXISTS_TAC `c:real` THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_MUL; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  REPLICATE_TAC 2 (AP_THM_TAC THEN AP_TERM_TAC) THEN
  UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD);;

let AFFSIGN_0 = prove
 (`!sgn s t.
        FINITE s /\ FINITE t /\ (vec 0) IN (s DIFF t)
        ==> affsign sgn s t =
             { vsum (s UNION t) (\v. f v % v) |f|
               !x:real^N. x IN t ==> sgn(f x)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[AFFSIGN] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `x IN s DIFF t ==> s UNION t = x INSERT ((s UNION t) DELETE x)`)) THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_UNION; FINITE_DELETE] THEN
  REWRITE_TAC[IN_DELETE; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[FORALL_IN_GSPEC; SUBSET; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`y:real^N`; `f:real^N->real`] THEN
    STRIP_TAC THEN EXISTS_TAC `f:real^N->real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `f:real^N->real` THEN DISCH_TAC THEN
    EXISTS_TAC
     `\x:real^N. if x = vec 0
                 then &1 - sum ((s UNION t) DELETE vec 0) (\x. f x)
                 else f x` THEN
    MP_TAC(SET_RULE
     `!x:real^N. x IN (s UNION t) DELETE vec 0 ==> ~(x = vec 0)`) THEN
    SIMP_TAC[ETA_AX; REAL_SUB_ADD] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM SET_TAC[]]);;

let AFF_GE_0_AFFINE_MULTIPLE_CONVEX = prove
 (`!s t:real^N->bool.
        FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t) /\ ~(t = {})
        ==> aff_ge s t =
               {x + c % y | x IN affine hull (s DIFF t) /\
                            y IN convex hull t /\ &0 <= c}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[aff_ge_def; AFFSIGN_0; sgn_ge] THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = (s DIFF t) UNION t`] THEN
  ASM_SIMP_TAC[VSUM_UNION; FINITE_DIFF;
               SET_RULE `DISJOINT (s DIFF t) t`] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
  ASM_SIMP_TAC[SPAN_FINITE; FINITE_DIFF; CONVEX_HULL_FINITE] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `f:real^N->real` THEN DISCH_TAC THEN
    EXISTS_TAC `vsum (s DIFF t) (\x:real^N. f x % x)` THEN
    ASM_CASES_TAC `sum t (f:real^N->real) = &0` THENL
     [MP_TAC(ISPECL [`f:real^N->real`; `t:real^N->bool`] SUM_POS_EQ_0) THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO; REAL_MUL_LZERO; VSUM_0] THEN
      DISCH_TAC THEN EXISTS_TAC `&0` THEN
      REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_REFL] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
       [EXISTS_TAC `f:real^N->real` THEN REWRITE_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; GSYM EXISTS_REFL] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
      EXISTS_TAC `\x:real^N. if x = a then &1 else &0` THEN
      ASM_REWRITE_TAC[SUM_DELTA] THEN MESON_TAC[REAL_POS];
      EXISTS_TAC `sum t (f:real^N->real)` THEN
      EXISTS_TAC `inv(sum t (f:real^N->real)) % vsum t (\v. f v % v)` THEN
      REPEAT CONJ_TAC THENL
       [EXISTS_TAC `f:real^N->real` THEN REWRITE_TAC[];
        EXISTS_TAC `\x:real^N. f x / sum t (f:real^N->real)` THEN
        ASM_SIMP_TAC[REAL_LE_DIV; SUM_POS_LE] THEN
        ONCE_REWRITE_TAC[REAL_ARITH `x / y:real = inv y * x`] THEN
        ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; SUM_LMUL; VSUM_LMUL] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV];
        ASM_SIMP_TAC[SUM_POS_LE];
        AP_TERM_TAC THEN ASM_CASES_TAC `sum t (f:real^N->real) = &0` THEN
        ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID]]];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `c:real`; `y:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `u:real^N->real` (SUBST1_TAC o SYM)) MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `v:real^N->real`MP_TAC) ASSUME_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    EXISTS_TAC `(\x. if x IN t then c * v x else u x):real^N->real` THEN
    ASM_SIMP_TAC[REAL_LE_MUL; VSUM_LMUL; GSYM VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
    SIMP_TAC[IN_DIFF]]);;

let AFF_GE_0_MULTIPLE_AFFINE_CONVEX = prove
 (`!s t:real^N->bool.
        FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t) /\ ~(t = {})
        ==> aff_ge s t =
               affine hull (s DIFF t) UNION
               {c % (x + y) | x IN affine hull (s DIFF t) /\
                              y IN convex hull t /\ &0 <= c}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[AFF_GE_0_AFFINE_MULTIPLE_CONVEX;
                 AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `c:real`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN ASM_CASES_TAC `c = &0` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      DISJ2_TAC THEN MAP_EVERY EXISTS_TAC
       [`c:real`; `inv(c) % x:real^N`; `y:real^N`] THEN
      ASM_SIMP_TAC[SPAN_MUL; VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
                   REAL_MUL_RINV; VECTOR_MUL_LID]];
    REWRITE_TAC[aff_ge_def] THEN ONCE_REWRITE_TAC[AFFSIGN_DISJOINT_DIFF] THEN
    REWRITE_TAC[GSYM aff_ge_def] THEN
    MATCH_MP_TAC AFFINE_HULL_SUBSET_AFF_GE THEN SET_TAC[];
    ASM_SIMP_TAC[AFF_GE_0_AFFINE_MULTIPLE_CONVEX;
                 AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC
     [`c % x:real^N`; `c:real`; `y:real^N`] THEN
    ASM_SIMP_TAC[SPAN_MUL; VECTOR_ADD_LDISTRIB]]);;

let AFF_GE_0_AFFINE_CONVEX_CONE = prove
 (`!s t:real^N->bool.
        FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t)
        ==> aff_ge s t =
               {x + y | x IN affine hull (s DIFF t) /\
                        y IN convex_cone hull t}`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_GE_EQ_AFFINE_HULL; CONVEX_CONE_HULL_EMPTY] THEN
    REWRITE_TAC[IN_SING; DIFF_EMPTY] THEN
    REWRITE_TAC[SET_RULE `{x + y:real^N | P x /\ y = a} = {x + a | P x}`] THEN
    REWRITE_TAC[VECTOR_ADD_RID] THEN SET_TAC[];
    ASM_SIMP_TAC[CONVEX_CONE_HULL_CONVEX_HULL_NONEMPTY;
                  AFF_GE_0_AFFINE_MULTIPLE_CONVEX] THEN
   SET_TAC[]]);;

let AFF_GE_0_N = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(vec 0 IN s)
        ==> aff_ge {vec 0} s =
                {y | ?u. (!x. x IN s ==> &0 <= u x) /\
                         y = vsum s (\x. u x % x)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aff_ge_def] THEN
  ASM_SIMP_TAC[AFFSIGN_0; IN_DIFF; IN_INSERT; NOT_IN_EMPTY;
               FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_SIMP_TAC[EXTENSION; sgn_ge; IN_ELIM_THM; INSERT_UNION; UNION_EMPTY] THEN
  ASM_SIMP_TAC[VSUM_CLAUSES; VECTOR_MUL_RZERO; VECTOR_ADD_LID]);;

let AFF_GE_0_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(s = {}) /\ ~(vec 0 IN s)
        ==> aff_ge {vec 0} s = {t % y | &0 <= t /\ y IN convex hull s}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[AFF_GE_0_AFFINE_MULTIPLE_CONVEX; IN_DIFF;
               FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
  ASM_SIMP_TAC[SET_RULE `~(a IN s) ==> {a} DIFF s = {a}`] THEN
  REWRITE_TAC[AFFINE_HULL_SING; IN_SING] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_LID]);;

let AFF_GE_0_CONVEX_HULL_ALT = prove
 (`!s:real^N->bool.
        FINITE s /\ ~(vec 0 IN s)
        ==> aff_ge {vec 0} s =
            vec 0 INSERT {t % y | &0 < t /\ y IN convex hull s}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_GE_EQ_AFFINE_HULL; CONVEX_HULL_EMPTY] THEN
    REWRITE_TAC[AFFINE_HULL_SING; NOT_IN_EMPTY] THEN SET_TAC[];
    ASM_SIMP_TAC[AFF_GE_0_CONVEX_HULL; EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    X_GEN_TAC `y:real^N` THEN ASM_CASES_TAC `y:real^N = vec 0` THEN
    ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_POS; VECTOR_MUL_LZERO] THEN
      ASM_REWRITE_TAC[MEMBER_NOT_EMPTY; CONVEX_HULL_EQ_EMPTY];
      AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      ASM_CASES_TAC `t = &0` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LT_REFL] THEN
      ASM_REWRITE_TAC[REAL_LT_LE]]]);;

let AFF_GE_0_CONVEX_CONE_NEGATIONS = prove
 (`!s t:real^N->bool.
        FINITE s /\ FINITE t /\ vec 0 IN (s DIFF t)
        ==> aff_ge s t =
            convex_cone hull (s UNION t UNION IMAGE (--) (s DIFF t))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AFF_GE_0_AFFINE_CONVEX_CONE] THEN
  ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC] THEN
  REWRITE_TAC[SPAN_CONVEX_CONE_ALLSIGNS; GSYM CONVEX_CONE_HULL_UNION] THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let CONVEX_HULL_AFF_GE = prove
 (`!s. convex hull s = aff_ge {} s`,
  SIMP_TAC[aff_ge_def; AFFSIGN; CONVEX_HULL_FINITE; sgn_ge; UNION_EMPTY] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[]);;

let POLYHEDRON_AFF_GE = prove
 (`!s t:real^N->bool. FINITE s /\ FINITE t ==> polyhedron(aff_ge s t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[aff_ge_def] THEN
  ONCE_REWRITE_TAC[AFFSIGN_DISJOINT_DIFF] THEN
  REWRITE_TAC[GSYM aff_ge_def] THEN
  SUBGOAL_THEN `FINITE(s DIFF t) /\ FINITE(t:real^N->bool) /\
                DISJOINT (s DIFF t) t`
  MP_TAC THENL [ASM_SIMP_TAC[FINITE_DIFF] THEN ASM SET_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`s DIFF t:real^N->bool`,`s:real^N->bool`) THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CONVEX_HULL_AFF_GE] THEN
    MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN REWRITE_TAC[polytope] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `s:real^N->bool`] THEN
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN ((vec 0 INSERT s) DIFF t)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_GE_0_CONVEX_CONE_NEGATIONS; FINITE_INSERT] THEN
  MATCH_MP_TAC POLYHEDRON_CONVEX_CONE_HULL THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; FINITE_DIFF; FINITE_IMAGE]);;

let CLOSED_AFF_GE = prove
 (`!s t:real^N->bool. FINITE s /\ FINITE t ==> closed(aff_ge s t)`,
  SIMP_TAC[POLYHEDRON_AFF_GE; POLYHEDRON_IMP_CLOSED]);;

let CONIC_AFF_GE_0 = prove
 (`!s:real^N->bool. FINITE s /\ ~(vec 0 IN s) ==> conic(aff_ge {vec 0} s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[AFF_GE_0_N; conic] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN X_GEN_TAC `c:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\v. c * (u:real^N->real) v` THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
  ASM_MESON_TAC[REAL_LE_MUL]);;

let ANGLES_ADD_AFF_GE = prove
 (`!u v w x:real^N.
        ~(v = u) /\ ~(w = u) /\ ~(x = u) /\ x IN aff_ge {u} {v,w}
        ==> angle(v,u,x) + angle(x,u,w) = angle(v,u,w)`,
  GEOM_ORIGIN_TAC `u:real^N` THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[AFF_GE_1_2_0] THEN
  REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `a = &0 /\ b = &0 \/ &0 < a + b` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  DISCH_TAC THEN MP_TAC(ISPECL
   [`v:real^N`; `w:real^N`; `inv(a + b) % x:real^N`; `vec 0:real^N`]
   ANGLES_ADD_BETWEEN) THEN
  ASM_REWRITE_TAC[angle; VECTOR_SUB_RZERO] THEN
  ASM_SIMP_TAC[VECTOR_ANGLE_RMUL; VECTOR_ANGLE_LMUL;
    REAL_INV_EQ_0; REAL_LE_INV_EQ; REAL_LT_IMP_NZ; REAL_LT_IMP_LE] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[BETWEEN_IN_SEGMENT; CONVEX_HULL_2; SEGMENT_CONVEX_HULL] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`a / (a + b):real`; `b / (a + b):real`] THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; VECTOR_ADD_LDISTRIB] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; real_div; REAL_MUL_AC] THEN
  UNDISCH_TAC `&0 < a + b` THEN CONV_TAC REAL_FIELD);;

let AFF_GE_2_1_0_DROPOUT_3 = prove
 (`!w z:real^3.
        ~collinear{vec 0,basis 3,z}
        ==> (w IN aff_ge {vec 0,basis 3} {z} <=>
             (dropout 3 w) IN aff_ge {vec 0:real^2} {dropout 3 z})`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `z:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
  ASM_CASES_TAC `z:real^3 = basis 3` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
  REWRITE_TAC[COLLINEAR_BASIS_3] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[AFF_GE_2_1_0; SET_RULE `DISJOINT s {a} <=> ~(a IN s)`;
               IN_INSERT; NOT_IN_EMPTY; AFF_GE_1_1_0] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(MESON[]
   `(!t. ((?s. P s t) <=> Q t)) ==> ((?s t. P s t) <=> (?t. Q t))`) THEN
  X_GEN_TAC `t:real` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC[DROPOUT_ADD; DROPOUT_MUL; DROPOUT_BASIS_3] THEN
    VECTOR_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(w:real^3)$3 - t * (z:real^3)$3` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CART_EQ]) THEN
    ASM_REWRITE_TAC[CART_EQ; FORALL_2; FORALL_3; DIMINDEX_2; DIMINDEX_3] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[dropout; LAMBDA_BETA; DIMINDEX_2; ARITH; BASIS_COMPONENT;
             DIMINDEX_3] THEN
    CONV_TAC REAL_RING]);;

let AFF_GE_2_1_0_SEMIALGEBRAIC = prove
 (`!x y z:real^3.
        ~collinear {vec 0,x,y} /\ ~collinear {vec 0,x,z}
        ==> (z IN aff_ge {vec 0,x} {y} <=>
             (x cross y) cross x cross z = vec 0 /\
             &0 <= (x cross z) dot (x cross y))`,
  let lemma0 = prove
   (`~(y = vec 0) ==> ((?s. x = s % y) <=> y cross x = vec 0)`,
    REWRITE_TAC[CROSS_EQ_0] THEN SIMP_TAC[COLLINEAR_LEMMA_ALT])
  and lemma1 = prove
   (`!x y:real^N.
          ~(y = vec 0)
          ==> ((?t. &0 <= t /\ x = t % y) <=>
               (?t. x = t % y) /\ &0 <= x dot y)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `t:real` THEN
    ASM_CASES_TAC `x:real^N = t % y` THEN
    ASM_SIMP_TAC[DOT_LMUL; REAL_LE_MUL_EQ; DOT_POS_LT]) in
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC])
   [`x:real^3 = vec 0`; `y:real^3 = vec 0`; `y:real^3 = x`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[AFF_GE_2_1_0; IN_ELIM_THM; SET_RULE
    `DISJOINT {a,b} {c} <=> ~(a = c) /\ ~(b = c)`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; VECTOR_ARITH
    `a:real^N = b + c <=> a - c = b`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CROSS_EQ_0]) THEN
  ASM_SIMP_TAC[lemma0; lemma1; CROSS_RMUL; CROSS_RSUB; VECTOR_SUB_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Special case of aff_ge {x} {y}, i.e. rays or half-lines.                  *)
(* ------------------------------------------------------------------------- *)

let HALFLINE_REFL = prove
 (`!x. aff_ge {x} {x} = {x}`,
  ONCE_REWRITE_TAC[AFF_GE_DISJOINT_DIFF] THEN
  ASM_REWRITE_TAC[DIFF_EQ_EMPTY; GSYM CONVEX_HULL_AFF_GE; CONVEX_HULL_SING]);;

let HALFLINE_EXPLICIT = prove
 (`!x y:real^N.
        aff_ge {x} {y} =
          {z | ?t1 t2. &0 <= t2 /\ t1 + t2 = &1 /\ z = t1 % x + t2 % y}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:real^N = y` THENL
   [ASM_REWRITE_TAC[HALFLINE_REFL]; AFF_TAC] THEN
  REWRITE_TAC[REAL_ARITH `x + y = &1 <=> x = &1 - y`] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - x) % v + x % v:real^N = v`;
    MESON[] `(?x y. P y /\ x = f y /\ Q x y) <=> (?y. P y /\ Q (f y) y)`] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING; EXTENSION] THEN MESON_TAC[REAL_POS]);;

let HALFLINE = prove
 (`!x y:real^N.
        aff_ge {x} {y} =
          {z | ?t. &0 <= t /\ z = (&1 - t) % x + t % y}`,
  REWRITE_TAC[HALFLINE_EXPLICIT;  REAL_ARITH `x + y = &1 <=> x = &1 - y`] THEN
  SET_TAC[]);;

let CLOSED_HALFLINE = prove
 (`!x y. closed(aff_ge {x} {y})`,
  SIMP_TAC[CLOSED_AFF_GE; FINITE_SING]);;

let SEGMENT_SUBSET_HALFLINE = prove
 (`!x y. segment[x,y] SUBSET aff_ge {x} {y}`,
  REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_2; HALFLINE_EXPLICIT] THEN
  SET_TAC[]);;

let ENDS_IN_HALFLINE = prove
 (`(!x y. x IN aff_ge {x} {y}) /\ (!x y. y IN aff_ge {x} {y})`,
  MESON_TAC[SEGMENT_SUBSET_HALFLINE; SUBSET; ENDS_IN_SEGMENT]);;

let HALFLINE_SUBSET_AFFINE_HULL = prove
 (`!x y. aff_ge {x} {y} SUBSET affine hull {x,y}`,
  REWRITE_TAC[AFF_GE_SUBSET_AFFINE_HULL; SET_RULE `{x,y} = {x} UNION {y}`]);;

let HALFLINE_INTER_COMPACT_SEGMENT = prove
 (`!s a b:real^N.
        compact s /\ convex s /\ a IN s
        ==> ?c. aff_ge {a} {b} INTER s = segment[a,c]`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `b:real^N = a` THENL
   [EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[SEGMENT_REFL; HALFLINE_REFL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u v:real^N. aff_ge {a} {b} INTER s = segment[u,v]`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONVEX_COLLINEAR_SEGMENT THEN
    ASM_SIMP_TAC[CLOSED_INTER_COMPACT; CLOSED_AFF_GE; FINITE_SING] THEN
    ASM_SIMP_TAC[CONVEX_INTER; CONVEX_AFF_GE] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      ASM_MESON_TAC[ENDS_IN_HALFLINE];
      MATCH_MP_TAC COLLINEAR_SUBSET THEN
      EXISTS_TAC `affine hull {a:real^N,b}` THEN
      REWRITE_TAC[COLLINEAR_AFFINE_HULL_COLLINEAR; COLLINEAR_2] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET u ==> (s INTER t) SUBSET u`) THEN
      REWRITE_TAC[HALFLINE_SUBSET_AFFINE_HULL]];
    ASM_CASES_TAC `u:real^N = a` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `v:real^N = a` THENL
     [ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `u IN aff_ge {a:real^N} {b} /\ v IN aff_ge {a} {b}`
    MP_TAC THENL [ASM_MESON_TAC[IN_INTER; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [HALFLINE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `s:real` MP_TAC) (X_CHOOSE_THEN `t:real` MP_TAC)) THEN
    MAP_EVERY ASM_CASES_TAC [`s = &0`; `t = &0`] THEN
    ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                    VECTOR_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^N) IN segment[u,v]` MP_TAC THENL
     [ASM_MESON_TAC[IN_INTER; ENDS_IN_HALFLINE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SEGMENT; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:real` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[VECTOR_ARITH
     `a = (&1 - u) % ((&1 - s) % a + s % b) + u % ((&1 - t) % a + t % b) <=>
      ((&1 - u) * s + u * t) % (b - a):real^N = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE; REAL_ARITH
     `&0 <= x /\ &0 <= y ==> (x + y = &0 <=> x = &0 /\ y = &0)`] THEN
    ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Definition and properties of conv0.                                       *)
(* ------------------------------------------------------------------------- *)

let conv0 = new_definition `conv0 S:real^A->bool = affsign sgn_gt {} S`;;

let CONV0_INJECTIVE_LINEAR_IMAGE = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> conv0(IMAGE f s) = IMAGE f (conv0 s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o GSYM o MATCH_MP AFFSIGN_INJECTIVE_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[conv0; IMAGE_CLAUSES]);;

add_linear_invariants [CONV0_INJECTIVE_LINEAR_IMAGE];;

let CONV0_TRANSLATION = prove
 (`!a s. conv0(IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (conv0 s)`,
  REWRITE_TAC[conv0; GSYM AFFSIGN_TRANSLATION; IMAGE_CLAUSES]);;

add_translation_invariants [CONV0_TRANSLATION];;

let CONV0_SUBSET_CONVEX_HULL = prove
 (`!s. conv0 s SUBSET convex hull s`,
  REWRITE_TAC[conv0; AFFSIGN; sgn_gt; CONVEX_HULL_FINITE; UNION_EMPTY] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN
  MESON_TAC[REAL_LT_IMP_LE]);;

let CONV0_AFF_GT = prove
 (`!s. conv0 s = aff_gt {} s`,
  REWRITE_TAC[conv0; aff_gt_def]);;

let CONVEX_HULL_CONV0_DECOMP = prove
 (`!s:real^N->bool.
        FINITE s
        ==> convex hull s = conv0 s UNION
                            UNIONS {convex hull (s DELETE a) | a | a IN s}`,
  REWRITE_TAC[CONV0_AFF_GT; CONVEX_HULL_AFF_GE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFF_GE_AFF_GT_DECOMP THEN
  ASM_REWRITE_TAC[FINITE_EMPTY] THEN SET_TAC[]);;

let CONVEX_CONV0 = prove
 (`!s. convex(conv0 s)`,
  REWRITE_TAC[CONV0_AFF_GT; CONVEX_AFF_GT]);;

let BOUNDED_CONV0 = prove
 (`!s:real^N->bool. bounded s ==> bounded(conv0 s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `convex hull s:real^N->bool` THEN
  ASM_SIMP_TAC[BOUNDED_CONVEX_HULL; CONV0_SUBSET_CONVEX_HULL]);;

let MEASURABLE_CONV0 = prove
 (`!s. bounded s ==> measurable(conv0 s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN
  ASM_SIMP_TAC[CONVEX_CONV0; BOUNDED_CONV0]);;

let NEGLIGIBLE_CONVEX_HULL_DIFF_CONV0 = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD s <= dimindex(:N) + 1
        ==> negligible(convex hull s DIFF conv0 s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONVEX_HULL_CONV0_DECOMP] THEN
  REWRITE_TAC[SET_RULE `(s UNION t) DIFF s = t DIFF s`] THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFF THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE] THEN ASM_ARITH_TAC);;

let MEASURE_CONV0_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD s <= dimindex(:N) + 1
        ==> measure(conv0 s) = measure(convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  ASM_SIMP_TAC[MEASURABLE_CONVEX_HULL; FINITE_IMP_BOUNDED] THEN
  MATCH_MP_TAC NEGLIGIBLE_UNION THEN
  ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_HULL_DIFF_CONV0] THEN
  ASM_SIMP_TAC[CONV0_SUBSET_CONVEX_HULL; NEGLIGIBLE_EMPTY;
               SET_RULE `s SUBSET t ==> s DIFF t = {}`]);;

(* ------------------------------------------------------------------------- *)
(* Orthonormal triples of vectors in 3D.                                     *)
(* ------------------------------------------------------------------------- *)

let orthonormal = new_definition
  `orthonormal e1 e2 e3 <=>
     e1 dot e1 = &1 /\ e2 dot e2 = &1 /\ e3 dot e3 = &1 /\
     e1 dot e2 = &0 /\ e1 dot e3 = &0 /\ e2 dot e3 = &0 /\
     &0 < (e1 cross e2) dot e3`;;

let ORTHONORMAL_LINEAR_IMAGE = prove
 (`!f. linear(f) /\ (!x. norm(f x) = norm x) /\
       (2 <= dimindex(:3) ==> det(matrix f) = &1)
       ==> !e1 e2 e3. orthonormal (f e1) (f e2) (f e3) <=>
                      orthonormal e1 e2 e3`,
  SIMP_TAC[DIMINDEX_3; ARITH; CONJ_ASSOC; GSYM ORTHOGONAL_TRANSFORMATION] THEN
  SIMP_TAC[orthonormal; CROSS_ORTHOGONAL_TRANSFORMATION] THEN
  SIMP_TAC[orthogonal_transformation; VECTOR_MUL_LID]);;

add_linear_invariants [ORTHONORMAL_LINEAR_IMAGE];;

let ORTHONORMAL_PERMUTE = prove
 (`!e1 e2 e3. orthonormal e1 e2 e3 ==> orthonormal e2 e3 e1`,
  REWRITE_TAC[orthonormal] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM CROSS_TRIPLE] THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[]);;

let ORTHONORMAL_CROSS = prove
 (`!e1 e2 e3.
        orthonormal e1 e2 e3
        ==> e2 cross e3 = e1 /\ e3 cross e1 = e2 /\ e1 cross e2 = e3`,
  SUBGOAL_THEN
   `!e1 e2 e3. orthonormal e1 e2 e3 ==> e3 cross e1 = e2`
   (fun th -> MESON_TAC[th; ORTHONORMAL_PERMUTE]) THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `e1:real^3` THEN X_GEN_TAC `k:real` THEN
  REWRITE_TAC[orthonormal; DOT_LMUL; DOT_RMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_RING `k * k = &1 <=> k = &1 \/ k = -- &1`] THEN
  ASM_CASES_TAC `k = -- &1` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `k = &1` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID; REAL_MUL_LID; REAL_MUL_RID] THEN
  SIMP_TAC[cross; DOT_3; VECTOR_3; CART_EQ; FORALL_3; DIMINDEX_3;
           BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_POS] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_ADD_RID;
              REAL_MUL_LID] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(e2:real^3)$1 = &0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(e3:real^3)$1 = &0` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; REAL_ADD_LID] THEN
  REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(u = &1 /\ v = &1 /\ w = &0 ==> a = b /\ --c = d \/ a = --b /\ c = d) /\
    (a = --b /\ c = d ==> x <= &0)
    ==> (u = &1 /\ v = &1 /\ w = &0 /\ &0 < x
         ==> a:real = b /\ --c:real = d)`) THEN
  CONJ_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x * x /\ &0 <= y * y ==> --x * x + y * -- y <= &0`) THEN
  REWRITE_TAC[REAL_LE_SQUARE]);;

let ORTHONORMAL_IMP_NONZERO = prove
 (`!e1 e2 e3. orthonormal e1 e2 e3
              ==> ~(e1 = vec 0) /\ ~(e2 = vec 0) /\ ~(e3 = vec 0)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[orthonormal; DOT_LZERO] THEN REAL_ARITH_TAC);;

let ORTHONORMAL_IMP_DISTINCT = prove
 (`!e1 e2 e3. orthonormal e1 e2 e3 ==> ~(e1 = e2) /\ ~(e1 = e3) /\ ~(e2 = e3)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[orthonormal; DOT_LZERO] THEN REAL_ARITH_TAC);;

let ORTHONORMAL_IMP_INDEPENDENT = prove
 (`!e1 e2 e3. orthonormal e1 e2 e3 ==> independent {e1,e2,e3}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIRWISE_ORTHOGONAL_INDEPENDENT THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[ORTHONORMAL_IMP_NONZERO]] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal]) THEN
  REWRITE_TAC[pairwise; IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[orthogonal] THEN
  ASM_MESON_TAC[DOT_SYM]);;

let ORTHONORMAL_IMP_SPANNING = prove
 (`!e1 e2 e3. orthonormal e1 e2 e3 ==> span {e1,e2,e3} = (:real^3)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(:real^3)`; `{e1:real^3,e2,e3}`] CARD_EQ_DIM) THEN
  ASM_SIMP_TAC[ORTHONORMAL_IMP_INDEPENDENT; SUBSET_UNIV] THEN
  REWRITE_TAC[DIM_UNIV; DIMINDEX_3; HAS_SIZE; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ORTHONORMAL_IMP_DISTINCT) THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; ARITH] THEN SET_TAC[]);;

let ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0 = prove
 (`!e1 e2 e3 t1 t2 t3.
        orthonormal e1 e2 e3
        ==> (t1 % e1 + t2 % e2 + t3 % e3 = vec 0 <=>
             t1 = &0 /\ t2 = &0 /\ t3 = &0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INDEPENDENT_3 THEN
  ASM_MESON_TAC[ORTHONORMAL_IMP_INDEPENDENT; ORTHONORMAL_IMP_DISTINCT]);;

let ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT = prove
 (`!e1 e2 e3 s1 s2 s3 t1 t2 t3.
        orthonormal e1 e2 e3
        ==> (s1 % e1 + s2 % e2 + s3 % e3 = t1 % e1 + t2 % e2 + t3 % e3 <=>
             s1 = t1 /\ s2 = t2 /\ s3 = t3)`,
  SIMP_TAC[ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0; REAL_SUB_0; VECTOR_ARITH
   `a % x + b % y + c % z:real^3 = a' % x + b' % y + c' % z <=>
    (a - a') % x + (b - b') % y + (c - c') % z = vec 0`]);;

(* ------------------------------------------------------------------------- *)
(* Flyspeck arcV is the same as angle even in degenerate cases.              *)
(* ------------------------------------------------------------------------- *)

let arcV = new_definition
  `arcV u v w = acs (( (v - u) dot (w - u))/((norm (v-u)) * (norm (w-u))))`;;

let ARCV_ANGLE = prove
 (`!u v w:real^N. arcV u v w = angle(v,u,w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[arcV; angle; vector_angle] THEN
  REWRITE_TAC[VECTOR_SUB_EQ] THEN
  ASM_CASES_TAC `v:real^N = u` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; DOT_LZERO] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; ACS_0] THEN
  ASM_CASES_TAC `w:real^N = u` THEN
  ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; DOT_RZERO] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; ACS_0]);;

let ARCV_LINEAR_IMAGE_EQ = prove
 (`!f a b c.
        linear f /\ (!x. norm(f x) = norm x)
        ==> arcV (f a) (f b) (f c) = arcV a b c`,
  REWRITE_TAC[ARCV_ANGLE; ANGLE_LINEAR_IMAGE_EQ]);;

add_linear_invariants [ARCV_LINEAR_IMAGE_EQ];;

let ARCV_TRANSLATION_EQ = prove
 (`!a b c d. arcV (a + b) (a + c) (a + d) = arcV b c d`,
  REWRITE_TAC[ARCV_ANGLE; ANGLE_TRANSLATION_EQ]);;

add_translation_invariants [ARCV_TRANSLATION_EQ];;

(* ------------------------------------------------------------------------- *)
(* Azimuth angle.                                                            *)
(* ------------------------------------------------------------------------- *)

let AZIM_EXISTS = prove
 (`!v w w1 w2.
          ?theta. &0 <= theta /\ theta < &2 * pi /\
                  ?h1 h2.
                     !e1 e2 e3.
                        orthonormal e1 e2 e3 /\
                        dist(w,v) % e3 = w - v /\
                        ~(w = v)
                        ==> ?psi r1 r2.
                                w1 - v = (r1 * cos psi) % e1 +
                                         (r1 * sin psi) % e2 +
                                         h1 % (w - v) /\
                                w2 - v = (r2 * cos (psi + theta)) % e1 +
                                         (r2 * sin (psi + theta)) % e2 +
                                         h2 % (w - v) /\
                                (~collinear {v, w, w1} ==> &0 < r1) /\
                                (~collinear {v, w, w2} ==> &0 < r2)`,
  let lemma = prove
   (`cos(p) % e + sin(p) % rotate2d (pi / &2) e = rotate2d p e`,
    SIMP_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
      FORALL_2; rotate2d; LAMBDA_BETA; DIMINDEX_2; ARITH; VECTOR_2] THEN
    REWRITE_TAC[SIN_PI2; COS_PI2] THEN REAL_ARITH_TAC) in
  GEN_GEOM_ORIGIN_TAC `v:real^3` ["e1"; "e2"; "e3"] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  EXISTS_TAC `(w dot (w1:real^3)) / (w dot w)` THEN
  GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
  EXISTS_TAC `(w dot (w2:real^3)) / (w dot w)` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV
   [REAL_ARITH `&0 <= w <=> w = &0 \/ &0 < w`] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_RZERO; NORM_0] THEN
    EXISTS_TAC `&0` THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[DOT_LMUL; NORM_MUL; DIMINDEX_3; ARITH; DOT_RMUL; DOT_BASIS;
           VECTOR_MUL_COMPONENT; NORM_BASIS; BASIS_COMPONENT] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < w ==> (w * x) / (w * w) * w = x`;
               REAL_ARITH `&0 < w ==> abs w = w`] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH
    `a % x:real^3 = a % y <=> a % (x - y) = vec 0`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; BASIS_NONZERO;
               DIMINDEX_3; ARITH; VECTOR_SUB_EQ] THEN
  REWRITE_TAC[MESON[] `(!e3. p e3 /\ e3 = a ==> q e3) <=> p a ==> q a`] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^3 = a + b + c <=> x - c = a + b`] THEN
  REPEAT GEN_TAC THEN
  ABBREV_TAC `v1:real^3 = w1 - (w1$3) % basis 3` THEN
  ABBREV_TAC `v2:real^3 = w2 - (w2$3) % basis 3` THEN
  SUBGOAL_THEN
   `(collinear{vec 0, w % basis 3, w1} <=>
     w1 - w1$3 % basis 3:real^3 = vec 0) /\
    (collinear{vec 0, w % basis 3, w2} <=>
     w2 - w2$3 % basis 3:real^3 = vec 0)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [ASM_SIMP_TAC[COLLINEAR_LEMMA; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ;
                 BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    MAP_EVERY EXPAND_TAC ["v1"; "v2"] THEN
    SIMP_TAC[CART_EQ; VEC_COMPONENT; VECTOR_ADD_COMPONENT; FORALL_3;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             VECTOR_SUB_COMPONENT; REAL_MUL_RZERO; REAL_MUL_RID;
             REAL_SUB_RZERO] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    CONV_TAC(BINOP_CONV(BINOP_CONV(ONCE_DEPTH_CONV SYM_CONV))) THEN
    ASM_SIMP_TAC[GSYM REAL_EQ_RDIV_EQ; EXISTS_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(v1:real^3)$3 = &0 /\ (v2:real^3)$3 = &0` MP_TAC THENL
   [MAP_EVERY EXPAND_TAC ["v1"; "v2"] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_SUB_EQ] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`v2:real^3`; `v1:real^3`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[orthonormal] THEN
  SIMP_TAC[DOT_BASIS; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d /\ e /\ f <=>
                         d /\ e /\ a /\ b /\ c /\ f`] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  PAD2D3D_TAC THEN REPEAT STRIP_TAC THEN
  SIMP_TAC[cross; VECTOR_3; pad2d3d; LAMBDA_BETA; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  ASM_CASES_TAC `v1:real^2 = vec 0` THEN ASM_REWRITE_TAC[NORM_POS_LT] THENL
   [MP_TAC(ISPECL [`basis 1:real^2`; `v2:real^2`]
      ROTATION_ROTATE2D_EXISTS_GEN) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`e1:real^2`; `basis 1:real^2`]
      ROTATION_ROTATE2D_EXISTS_GEN) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `norm(v2:real^2)`] THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    SUBGOAL_THEN `norm(e1:real^2) = &1 /\ norm(e2:real^2) = &1`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_1]; ALL_TAC] THEN
    SUBGOAL_THEN `e2 = rotate2d (pi / &2) e1` SUBST1_TAC THENL
     [MATCH_MP_TAC ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED THEN
      ASM_REWRITE_TAC[NORM_EQ_1; orthogonal];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB] THEN
    REWRITE_TAC[lemma] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[ROTATE2D_ADD] THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
    EXISTS_TAC `norm(basis 1:real^2)` THEN
    ASM_SIMP_TAC[NORM_EQ_0; BASIS_NONZERO; DIMINDEX_2; ARITH] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `a % b % x:real^2 = b % a % x`] THEN
    AP_TERM_TAC THEN
    SIMP_TAC[GSYM(MATCH_MP LINEAR_CMUL (SPEC_ALL LINEAR_ROTATE2D))] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_ROTATE2D; VECTOR_MUL_LID];
    MP_TAC(ISPECL [`v1:real^2`; `v2:real^2`] ROTATION_ROTATE2D_EXISTS_GEN) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`e1:real^2`; `v1:real^2`] ROTATION_ROTATE2D_EXISTS_GEN) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:real` THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`norm(v1:real^2)`; `norm(v2:real^2)`] THEN
    ASM_REWRITE_TAC[NORM_POS_LT] THEN
    SUBGOAL_THEN `norm(e1:real^2) = &1 /\ norm(e2:real^2) = &1`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[NORM_EQ_1]; ALL_TAC] THEN
    SUBGOAL_THEN `e2 = rotate2d (pi / &2) e1` SUBST1_TAC THENL
     [MATCH_MP_TAC ROTATION_ROTATE2D_EXISTS_ORTHOGONAL_ORIENTED THEN
      ASM_REWRITE_TAC[NORM_EQ_1; orthogonal];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB] THEN
    REWRITE_TAC[lemma] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    REWRITE_TAC[ROTATE2D_ADD] THEN ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `norm(v1:real^2)` THEN
    ASM_REWRITE_TAC[NORM_EQ_0] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `a % b % x:real^2 = b % a % x`] THEN
    AP_TERM_TAC THEN
    SIMP_TAC[GSYM(MATCH_MP LINEAR_CMUL (SPEC_ALL LINEAR_ROTATE2D))] THEN
    AP_TERM_TAC THEN
    ASM_SIMP_TAC[LINEAR_CMUL; LINEAR_ROTATE2D; VECTOR_MUL_LID]]);;

let azim_spec =
   (REWRITE_RULE[SKOLEM_THM]
    (REWRITE_RULE[RIGHT_EXISTS_IMP_THM] AZIM_EXISTS));;

let azim_def = new_definition
  `azim v w w1 w2 =
        if collinear {v,w,w1} \/ collinear {v,w,w2} then &0
        else @theta. &0 <= theta /\ theta < &2 * pi /\
                     ?h1 h2.
                         !e1 e2 e3.
                            orthonormal e1 e2 e3 /\
                            dist(w,v) % e3 = w - v /\
                            ~(w = v)
                            ==> ?psi r1 r2.
                                    w1 - v = (r1 * cos psi) % e1 +
                                             (r1 * sin psi) % e2 +
                                             h1 % (w - v) /\
                                    w2 - v = (r2 * cos (psi + theta)) % e1 +
                                             (r2 * sin (psi + theta)) % e2 +
                                             h2 % (w - v) /\
                                    &0 < r1 /\ &0 < r2`;;

let azim = prove
 (`!v w w1 w2:real^3.
        &0 <= azim v w w1 w2 /\ azim v w w1 w2 < &2 * pi /\
        ?h1 h2.
           !e1 e2 e3.
              orthonormal e1 e2 e3 /\
              dist(w,v) % e3 = w - v /\
              ~(w = v)
              ==> ?psi r1 r2.
                      w1 - v = (r1 * cos psi) % e1 +
                               (r1 * sin psi) % e2 +
                               h1 % (w - v) /\
                      w2 - v = (r2 * cos (psi + azim v w w1 w2)) % e1 +
                               (r2 * sin (psi + azim v w w1 w2)) % e2 +
                               h2 % (w - v) /\
                      (~collinear {v, w, w1} ==> &0 < r1) /\
                      (~collinear {v, w, w2} ==> &0 < r2)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[azim_def] THEN
  COND_CASES_TAC THENL
   [ALL_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SELECT_CONV THEN
    MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `w1:real^3`; `w2:real^3`]
        AZIM_EXISTS) THEN
    ASM_REWRITE_TAC[]] THEN
  SIMP_TAC[PI_POS; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH; REAL_LE_REFL] THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THENL
   [MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `w2:real^3`; `w1:real^3`]
     AZIM_EXISTS) THEN
    DISCH_THEN(CHOOSE_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h2:real`; `h1:real`] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`h1:real`; `h2:real`] THEN
    MAP_EVERY X_GEN_TAC [`e1:real^3`; `e2:real^3`; `e3:real^3`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^3`; `e2:real^3`; `e3:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `psi:real` THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_ADD_RID] THEN
    MAP_EVERY X_GEN_TAC [`r2:real`; `r1:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`&0`; `r2:real`];
    MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `w1:real^3`; `w2:real^3`]
       AZIM_EXISTS) THEN
    DISCH_THEN(CHOOSE_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2)) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h1:real`; `h2:real`] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`h1:real`; `h2:real`] THEN
    MAP_EVERY X_GEN_TAC [`e1:real^3`; `e2:real^3`; `e3:real^3`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^3`; `e2:real^3`; `e3:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `psi:real` THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_ADD_RID] THEN
    MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`r1:real`; `&0`]] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
   [SET_RULE `{v,w,x} = {w,v,x}`]) THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_THEN `dist(w:real^3,v) % e3 = w - v` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthonormal]) THEN
  ASM_REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; REAL_MUL_RZERO] THEN
  ONCE_REWRITE_TAC[DOT_SYM] THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `(r * c) * (r * c):real = r pow 2 * c pow 2`] THEN
  REWRITE_TAC[REAL_ARITH `r * c + r * s + f:real = r * (s + c) + f`] THEN
  REWRITE_TAC[SIN_CIRCLE] THEN REWRITE_TAC[REAL_RING
   `(d * h * d) pow 2 = (d * d) * (r * &1 + h * d * h * d) <=>
    d = &0 \/ r = &0`] THEN
  ASM_REWRITE_TAC[DIST_EQ_0; REAL_POW_EQ_0; ARITH] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_MUL_LZERO; DOT_LZERO]);;

let AZIM_UNIQUE = prove
 (`!v w w1 w2 h1 h2 r1 r2 e1 e2 e3 psi theta.
        &0 <= theta /\
        theta < &2 * pi /\
        orthonormal e1 e2 e3 /\
        dist(w,v) % e3 = w - v /\
        ~(w = v) /\
        &0 < r1 /\ &0 < r2 /\
        w1 - v = (r1 * cos psi) % e1 +
                 (r1 * sin psi) % e2 +
                 h1 % (w - v) /\
        w2 - v = (r2 * cos (psi + theta)) % e1 +
                 (r2 * sin (psi + theta)) % e2 +
                 h2 % (w - v)
        ==> azim v w w1 w2 = theta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~collinear{v:real^3,w,w2} /\ ~collinear {v,w,w1}`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `{a,b,c} = {b,a,c}`] THEN
    ONCE_REWRITE_TAC[COLLINEAR_3] THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
    ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[VECTOR_SUB_EQ] THEN
    UNDISCH_THEN `dist(w:real^3,v) % e3 = w - v` (SUBST1_TAC o SYM) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC; VECTOR_ARITH
     `a + b + c % x:real^N = d % x <=> a + b + (c - d) % x = vec 0`] THEN
    ASM_SIMP_TAC[ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT_0] THEN
    ASM_SIMP_TAC[CONJ_ASSOC; REAL_LT_IMP_NZ; SIN_CIRCLE; REAL_RING
     `s pow 2 + c pow 2 = &1 ==> (r * c = &0 /\ r * s = &0 <=> r = &0)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(azim v w w1 w2 - theta) / (&2 * pi) = &0` MP_TAC THENL
   [ALL_TAC; MP_TAC PI_POS THEN CONV_TAC REAL_FIELD] THEN
  MATCH_MP_TAC REAL_EQ_INTEGERS_IMP THEN
  ASM_SIMP_TAC[REAL_SUB_RZERO; REAL_ABS_DIV; REAL_ABS_MUL; REAL_ABS_NUM;
       REAL_ABS_PI; REAL_LT_LDIV_EQ; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH;
       PI_POS; INTEGER_CLOSED; REAL_MUL_LID] THEN
  MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `w1:real^3`; `w2:real^3`] azim) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 <= x /\ x < k /\ &0 <= y /\ y < k ==> abs(x - y) < k`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k1:real`; `k2:real`] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^3`; `e2:real^3`; `e3:real^3`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`phi:real`; `s1:real`; `s2:real`] THEN
  UNDISCH_THEN `dist(w:real^3,v) % e3 = w - v` (SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[ORTHONORMAL_IMP_INDEPENDENT_EXPLICIT] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> (c /\ d) /\ a /\ b`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (MP_TAC o MATCH_MP (REAL_FIELD
   `r * c = r' * c' /\ r * s = r' * s' /\ u:real = v
    ==> s pow 2 + c pow 2 = &1 /\ s' pow 2 + c' pow 2 = &1 /\
        &0 < r /\ (r pow 2 = r' pow 2 ==> r = r')
        ==> s = s' /\ c = c'`))) THEN
  ASM_REWRITE_TAC[SIN_CIRCLE; GSYM REAL_EQ_SQUARE_ABS] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < x /\ &0 < y ==> (abs x = abs y <=> x = y)`] THEN
  REWRITE_TAC[SIN_COS_EQ] THEN
  REWRITE_TAC[REAL_ARITH
   `psi + theta = (phi + az) + x:real <=> psi = phi + x + (az - theta)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[REAL_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[REAL_ARITH
   `&2 * m * pi + x = &2 * n * pi <=> x = (n - m) * &2 * pi`] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[PI_POS; REAL_FIELD `&0 < pi ==> (x * &2 * pi) / (&2 * pi) = x`;
               INTEGER_CLOSED]);;

let AZIM_TRANSLATION = prove
 (`!a v w w1 w2. azim (a + v) (a + w) (a + w1) (a + w2) = azim v w w1 w2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[azim_def] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + w) - (a + v):real^3 = w - v`;
              VECTOR_ARITH `a + w:real^3 = a + v <=> w = v`;
              NORM_ARITH `dist(a + v,a + w) = dist(v,w)`] THEN
  REWRITE_TAC[SET_RULE
   `{a + x,a + y,a + z} = IMAGE (\x:real^3. a + x) {x,y,z}`] THEN
  REWRITE_TAC[COLLINEAR_TRANSLATION_EQ]);;

add_translation_invariants [AZIM_TRANSLATION];;

let AZIM_LINEAR_IMAGE = prove
 (`!f. linear f /\ (!x. norm(f x) = norm x) /\
       (2 <= dimindex(:3) ==> det(matrix f) = &1)
       ==> !v w w1 w2. azim (f v) (f w) (f w1) (f w2) = azim v w w1 w2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[azim_def] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB; dist] THEN
  MP_TAC(ISPEC `f:real^3->real^3` QUANTIFY_SURJECTION_THM) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION;
                  ORTHOGONAL_TRANSFORMATION_SURJECTIVE];
    ALL_TAC] THEN
  DISCH_THEN(CONV_TAC o LAND_CONV o EXPAND_QUANTS_CONV) THEN
  ASM_SIMP_TAC[ORTHONORMAL_LINEAR_IMAGE] THEN
  ASM_SIMP_TAC[GSYM LINEAR_CMUL; GSYM LINEAR_ADD] THEN
  SUBGOAL_THEN `!x y. (f:real^3->real^3) x = f y <=> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRESERVES_NORM_INJECTIVE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `{f x,f y,f z} = IMAGE f {x,y,z}`] THEN
  ASM_SIMP_TAC[COLLINEAR_LINEAR_IMAGE_EQ]);;

add_linear_invariants [AZIM_LINEAR_IMAGE];;

let AZIM_DEGENERATE = prove
 (`(!v w w1 w2. v = w ==> azim v w w1 w2 = &0) /\
   (!v w w1 w2. collinear{v,w,w1} ==> azim v w w1 w2 = &0) /\
   (!v w w1 w2. collinear{v,w,w2} ==> azim v w w1 w2 = &0)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[azim_def] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_AC; COLLINEAR_2]);;

let AZIM_REFL_ALT = prove
 (`!v x y. azim v v x y = &0`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC(last(CONJUNCTS AZIM_DEGENERATE)) THEN
  REWRITE_TAC[COLLINEAR_2; INSERT_AC]);;

let AZIM_SPECIAL_SCALE = prove
 (`!a v w1 w2.
        &0 < a
        ==> azim (vec 0) (a % v) w1 w2 = azim (vec 0) v w1 w2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[azim_def] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(MESON[REAL_LT_IMP_NZ; REAL_DIV_LMUL]
   `!a. &0 < a ==> (!y. ?x. a * x = y)`)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
  DISCH_THEN(CONV_TAC o RAND_CONV o
    PARTIAL_EXPAND_QUANTS_CONV ["psi"; "r1"; "r2"]) THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 < a ==> abs a = a`] THEN
  REWRITE_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[VECTOR_ARITH `a % x:real^3 = a % y <=> a % (x - y) = vec 0`] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; VECTOR_MUL_EQ_0] THEN
  REWRITE_TAC[VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE; REAL_LT_IMP_NZ]);;

let AZIM_SCALE_ALL = prove
 (`!a v w1 w2.
        &0 < a /\ &0 < b /\ &0 < c
        ==> azim (vec 0) (a % v) (b % w1) (c % w2) = azim (vec 0) v w1 w2`,
  let lemma = MESON[REAL_LT_IMP_NZ; REAL_DIV_LMUL]
   `!a. &0 < a ==> (!y. ?x. a * x = y)` in
  let SCALE_QUANT_TAC side asm avoid =
    MP_TAC(MATCH_MP lemma (ASSUME asm)) THEN
    DISCH_THEN(MP_TAC o MATCH_MP QUANTIFY_SURJECTION_THM) THEN
    DISCH_THEN(CONV_TAC o side o PARTIAL_EXPAND_QUANTS_CONV avoid) in
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[azim_def; COLLINEAR_SCALE_ALL; REAL_LT_IMP_NZ] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  ASM_SIMP_TAC[DIST_0; NORM_MUL; GSYM VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`; VECTOR_MUL_LCANCEL] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN
  SCALE_QUANT_TAC RAND_CONV `&0 < a`  ["psi"; "r1"; "r2"] THEN
  SCALE_QUANT_TAC LAND_CONV `&0 < b`  ["psi"; "h2"; "r2"] THEN
  SCALE_QUANT_TAC LAND_CONV `&0 < c`  ["psi"; "h1"; "r1"] THEN
  ASM_SIMP_TAC[GSYM VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_LDISTRIB;
               VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ; REAL_LT_MUL_EQ] THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC; REAL_MUL_AC]);;

let AZIM_ARG = prove
 (`!x y:real^3. azim (vec 0) (basis 3) x y = Arg(dropout 3 y / dropout 3 x)`,
  let lemma = prove
   (`(r * cos t) % basis 1 + (r * sin t) % basis 2 = Cx r * cexp(ii * Cx t)`,
    REWRITE_TAC[CEXP_EULER; COMPLEX_BASIS; GSYM CX_SIN; GSYM CX_COS;
                COMPLEX_CMUL; CX_MUL] THEN
    CONV_TAC COMPLEX_RING) in
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `collinear {vec 0:real^3,basis 3,x}` THENL
   [ASM_SIMP_TAC[AZIM_DEGENERATE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
    ASM_REWRITE_TAC[COMPLEX_VEC_0; complex_div; COMPLEX_INV_0;
                    COMPLEX_MUL_RZERO; ARG_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `collinear {vec 0:real^3,basis 3,y}` THENL
   [ASM_SIMP_TAC[AZIM_DEGENERATE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
    ASM_REWRITE_TAC[COMPLEX_VEC_0; complex_div; COMPLEX_MUL_LZERO; ARG_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `basis 3:real^3`; `x:real^3`; `y:real^3`]
        azim) THEN
  ABBREV_TAC `a = azim (vec 0) (basis 3) x (y:real^3)` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; VECTOR_SUB_RZERO; DIST_0] THEN
  MAP_EVERY X_GEN_TAC [`h1:real`; `h2:real`] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`basis 1:real^3`; `basis 2:real^3`; `basis 3:real^3`]) THEN
  SIMP_TAC[orthonormal; DOT_BASIS_BASIS; CROSS_BASIS; DIMINDEX_3; NORM_BASIS;
    ARITH; VECTOR_MUL_LID; BASIS_NONZERO; REAL_LT_01; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`psi:real`; `r1:real`; `r2:real`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  REWRITE_TAC[DROPOUT_ADD; DROPOUT_MUL; DROPOUT_BASIS_3] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_RID; lemma] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_MUL] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING
   `(a * b) * (c * d):complex = (a * c) * b * d`] THEN
  REWRITE_TAC[GSYM complex_div; GSYM CX_DIV; GSYM CEXP_SUB] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC ARG_UNIQUE THEN
  EXISTS_TAC `r2 / r1:real` THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CX_ADD] THEN
  CONV_TAC COMPLEX_RING);;

let REAL_CONTINUOUS_AT_AZIM_SHARP = prove
 (`!v w w1 w2.
        ~collinear{v,w,w1} /\ ~(w2 IN aff_ge {v,w} {w1})
        ==> (azim v w w1) real_continuous at w2`,
  GEOM_ORIGIN_TAC `v:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN ASM_CASES_TAC `w = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LT; COLLINEAR_SPECIAL_SCALE] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GE_SPECIAL_SCALE o
    rand o rand o lhand o snd) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_SING] THEN ANTS_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[DE_MORGAN_THM] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THENL
     [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC];
      ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC];
      ASM_SIMP_TAC[COLLINEAR_LEMMA_ALT; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
      MESON_TAC[]];
    DISCH_THEN SUBST1_TAC THEN DISCH_TAC] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; AZIM_ARG] THEN
  MATCH_MP_TAC(REWRITE_RULE[o_DEF]
    REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[complex_div] THEN MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
    REWRITE_TAC[CONTINUOUS_CONST; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_AT; LINEAR_DROPOUT; DIMINDEX_3; DIMINDEX_2;
             ARITH];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_AT_WITHIN THEN
  MATCH_MP_TAC REAL_CONTINUOUS_AT_ARG THEN
  MP_TAC(ISPECL [`w2:real^3`; `w1:real^3`] AFF_GE_2_1_0_DROPOUT_3) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [COLLINEAR_BASIS_3])) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w2`,`v2:real^2`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w1`,`v1:real^2`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `v1:complex` THEN
  X_GEN_TAC `w:real` THEN ASM_CASES_TAC `w = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN X_GEN_TAC `z:complex` THEN
  DISCH_THEN(K ALL_TAC) THEN
  REWRITE_TAC[CONTRAPOS_THM; COMPLEX_BASIS; COMPLEX_CMUL] THEN
  REWRITE_TAC[COMPLEX_MUL_RID; RE_DIV_CX; IM_DIV_CX; real] THEN
  ASM_SIMP_TAC[REAL_DIV_EQ_0; REAL_LE_RDIV_EQ; REAL_MUL_LZERO] THEN
  STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GE_1_1_0 o rand o snd) THEN
  ASM_REWRITE_TAC[COMPLEX_VEC_0; CX_INJ] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `Re z / w` THEN
  ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; COMPLEX_EQ] THEN
  ASM_SIMP_TAC[COMPLEX_CMUL; CX_DIV; COMPLEX_DIV_RMUL; CX_INJ] THEN
  REWRITE_TAC[RE_CX; IM_CX]);;

let REAL_CONTINUOUS_AT_AZIM = prove
 (`!v w w1 w2. ~coplanar{v,w,w1,w2} ==> (azim v w w1) real_continuous at w2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_CONTINUOUS_AT_AZIM_SHARP THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[NOT_COPLANAR_NOT_COLLINEAR; INSERT_AC];
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET]
       AFF_GE_SUBSET_AFFINE_HULL)) THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[coplanar; CONTRAPOS_THM] THEN
    REWRITE_TAC[SET_RULE `{a,b} UNION {c} = {a,b,c}`] THEN
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC
     [`v:real^3`; `w:real^3`; `w1:real^3`] THEN
    SIMP_TAC[SET_RULE `{a,b,c,d} SUBSET s <=> {a,b,c} SUBSET s /\ d IN s`] THEN
    ASM_REWRITE_TAC[HULL_SUBSET]]);;

let AZIM_REFL = prove
 (`!v0 v1 w. azim v0 v1 w w = &0`,
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[VECTOR_MUL_LZERO; AZIM_DEGENERATE] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; AZIM_ARG; ARG_EQ_0] THEN
  X_GEN_TAC `w:real^3` THEN
  ASM_CASES_TAC `(dropout 3 :real^3->real^2) w = Cx(&0)` THEN
  ASM_SIMP_TAC[COMPLEX_DIV_REFL; REAL_CX; RE_CX; REAL_POS] THEN
  ASM_SIMP_TAC[complex_div; COMPLEX_MUL_LZERO; REAL_CX; RE_CX; REAL_POS]);;

let AZIM_EQ = prove
 (`!v0 v1 w x y.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x} /\ ~collinear{v0,v1,y}
        ==> (azim v0 v1 w x = azim v0 v1 w y <=> y IN aff_gt {v0,v1} {x})`,
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; REAL_LT_IMP_NZ; COLLINEAR_SPECIAL_SCALE] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SPECIAL_SCALE o
    rand o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT; FINITE_INSERT; FINITE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    TRY(RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC; COLLINEAR_2]) THEN
        FIRST_X_ASSUM CONTR_TAC) THEN
    UNDISCH_TAC `~collinear {vec 0:real^3, basis 3, v1 % basis 3}` THEN
    REWRITE_TAC[COLLINEAR_LEMMA] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[AZIM_ARG] THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
  W(MP_TAC o PART_MATCH (lhs o rand) ARG_EQ o lhand o snd) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
  ASM_REWRITE_TAC[complex_div; COMPLEX_ENTIRE; COMPLEX_INV_EQ_0] THEN
  ASM_REWRITE_TAC[GSYM complex_div; GSYM COMPLEX_VEC_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[GSYM COMPLEX_VEC_0; COMPLEX_FIELD
    `~(w = Cx(&0)) ==> (y / w = x * u / w <=> y = x * u)`] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_2_1 o rand o rand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SET_RULE `DISJOINT {a,b} {x} <=> ~(x = a) /\ ~(x = b)`] THEN
    ASM_MESON_TAC[DROPOUT_BASIS_3; DROPOUT_0];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(?a b c. p c /\ q a b c /\ r b c) <=>
    (?c. p c /\ ?b. r b c /\ ?a. q a b c)`] THEN
  SIMP_TAC[REAL_ARITH `a + b + c = &1 <=> a = &1 - b - c`; EXISTS_REFL] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `t:real` THEN REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  SIMP_TAC[CART_EQ; FORALL_2; FORALL_3; DIMINDEX_2; DIMINDEX_3;
           dropout; LAMBDA_BETA; BASIS_COMPONENT; ARITH; REAL_MUL_RID;
           VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RZERO; UNWIND_THM1;
           VECTOR_ADD_COMPONENT; REAL_ADD_LID; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[REAL_ARITH `y:real = t + z <=> t = y - z`; EXISTS_REFL]);;

let AZIM_EQ_ALT = prove
 (`!v0 v1 w x y.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x} /\ ~collinear{v0,v1,y}
        ==> (azim v0 v1 w x = azim v0 v1 w y <=> x IN aff_gt {v0,v1} {y})`,
  ASM_SIMP_TAC[GSYM AZIM_EQ] THEN MESON_TAC[]);;

let AZIM_EQ_0 = prove
 (`!v0 v1 w x.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
        ==> (azim v0 v1 w x = &0 <=> w IN aff_gt {v0,v1} {x})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `azim v0 v1 w x = azim v0 v1 w w` THEN CONJ_TAC THENL
   [REWRITE_TAC[AZIM_REFL];
    ASM_SIMP_TAC[AZIM_EQ]]);;

let AZIM_EQ_0_ALT = prove
 (`!v0 v1 w x.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
        ==> (azim v0 v1 w x = &0 <=> x IN aff_gt {v0,v1} {w})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `azim v0 v1 w x = azim v0 v1 w w` THEN CONJ_TAC THENL
   [REWRITE_TAC[AZIM_REFL];
    ASM_SIMP_TAC[AZIM_EQ_ALT]]);;

let AZIM_EQ_0_GE = prove
 (`!v0 v1 w x.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
        ==> (azim v0 v1 w x = &0 <=> w IN aff_ge {v0,v1} {x})`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `v1:real^3 = v0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; STRIP_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o
      rand o rand o snd) THEN
  ANTS_TAC THENL
   [SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; DISJOINT_INSERT; DISJOINT_EMPTY] THEN
    REWRITE_TAC[IN_SING] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_2; INSERT_AC]) THEN
    FIRST_ASSUM CONTR_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[AZIM_EQ_0] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_1] THEN
  REWRITE_TAC[SET_RULE `{x} DELETE x = {}`] THEN
  REWRITE_TAC[AFF_GE_EQ_AFFINE_HULL; IN_UNION] THEN
  ASM_SIMP_TAC[GSYM COLLINEAR_3_AFFINE_HULL]);;

let AZIM_COMPL_EQ_0 = prove
 (`!z w w1 w2.
        ~collinear {z,w,w1} /\ ~collinear {z,w,w2} /\ azim z w w1 w2 = &0
        ==> azim z w w2 w1 = &0`,
  REWRITE_TAC[IMP_CONJ] THEN
  GEOM_ORIGIN_TAC `z:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE; AZIM_ARG] THEN
  REWRITE_TAC[ARG_EQ_0; real; IM_COMPLEX_DIV_EQ_0; RE_COMPLEX_DIV_GE_0] THEN
  REWRITE_TAC[complex_mul; RE; IM; cnj] THEN REAL_ARITH_TAC);;

let AZIM_COMPL = prove
 (`!z w w1 w2.
        ~collinear {z,w,w1} /\ ~collinear {z,w,w2}
        ==> azim z w w2 w1 = if azim z w w1 w2 = &0 then &0
                             else &2 * pi - azim z w w1 w2`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [ASM_MESON_TAC[AZIM_COMPL_EQ_0]; ALL_TAC] THEN
  DISCH_THEN(fun th -> POP_ASSUM MP_TAC THEN MP_TAC th) THEN
  GEOM_ORIGIN_TAC `z:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE; AZIM_ARG] THEN
  REWRITE_TAC[COLLINEAR_BASIS_3] THEN REWRITE_TAC[ARG_EQ_0] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(dropout 3:real^3->real^2) w2 /
                (dropout 3:real^3->real^2) w1` ARG_INV) THEN
  ASM_REWRITE_TAC[COMPLEX_INV_DIV]);;

let AZIM_EQ_PI_SYM = prove
 (`!z w w1 w2.
        ~collinear {z, w, w1} /\ ~collinear {z, w, w2}
        ==> (azim z w w1 w2 = pi <=> azim z w w2 w1 = pi)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o lhand o rand o snd) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let AZIM_EQ_0_SYM = prove
 (`!z w w1 w2.
        ~collinear {z, w, w1} /\ ~collinear {z, w, w2}
        ==> (azim z w w1 w2 = &0 <=> azim z w w2 w1 = &0)`,
  MESON_TAC[AZIM_COMPL_EQ_0]);;

let AZIM_EQ_0_GE_ALT = prove
 (`!v0 v1 w x.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
        ==> (azim v0 v1 w x = &0 <=> x IN aff_ge {v0,v1} {w})`,
  ASM_MESON_TAC[AZIM_EQ_0_SYM; AZIM_EQ_0_GE]);;

let AZIM_EQ_PI = prove
 (`!v0 v1 w x.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
        ==> (azim v0 v1 w x = pi <=> w IN aff_lt {v0,v1} {x})`,
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  STRIP_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; REAL_LT_IMP_NZ;
               COLLINEAR_SPECIAL_SCALE] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_LT_SPECIAL_SCALE o
    rand o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT; FINITE_INSERT; FINITE_EMPTY; NOT_IN_EMPTY] THEN
    REPEAT CONJ_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    TRY(RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC; COLLINEAR_2]) THEN
        FIRST_X_ASSUM CONTR_TAC) THEN
    UNDISCH_TAC `~collinear {vec 0:real^3, basis 3, v1 % basis 3}` THEN
    REWRITE_TAC[COLLINEAR_LEMMA] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[AZIM_ARG] THEN CONV_TAC(LAND_CONV SYM_CONV) THEN
  CONV_TAC(LAND_CONV SYM_CONV) THEN REWRITE_TAC[ARG_EQ_PI] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
  `(dropout 3 (w:real^3)) IN aff_lt {vec 0:real^2} {dropout 3 (x:real^3)}` THEN
  CONJ_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[COLLINEAR_BASIS_3] THEN
    SPEC_TAC(`(dropout 3:real^3->real^2) x`,`y:complex`) THEN
    SPEC_TAC(`(dropout 3:real^3->real^2) w`,`v:complex`) THEN
    GEOM_BASIS_MULTIPLE_TAC 1 `v:complex` THEN
    X_GEN_TAC `v:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC `v = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
    SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID] THEN
    REWRITE_TAC[real; RE_DIV_CX; IM_DIV_CX; CX_INJ] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_MUL_LZERO] THEN
    REPEAT STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_LT_1_1 o rand o rand o snd) THEN
    ASM_REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY; IN_SING] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[COMPLEX_CMUL; IN_ELIM_THM; COMPLEX_MUL_RZERO] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[REAL_ARITH `t1 + t2 = &1 <=> t1 = &1 - t2`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; COMPLEX_ADD_LID] THEN
    EQ_TAC THENL
     [REWRITE_TAC[GSYM real; REAL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) ASSUME_TAC) THEN
      EXISTS_TAC `v / Re y` THEN REWRITE_TAC[GSYM CX_MUL; CX_INJ] THEN
      CONJ_TAC THENL
       [ALL_TAC; REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD];
      DISCH_THEN(X_CHOOSE_THEN `t:real`
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_SIMP_TAC[CX_INJ; REAL_ARITH `x < &0 ==> ~(x = &0)`; COMPLEX_FIELD
        `~(t = Cx(&0)) ==> (v = t * y <=> y = v / t)`] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM CX_DIV] THEN
      REWRITE_TAC[RE_CX; IM_CX]] THEN
    REWRITE_TAC[REAL_ARITH `x < &0 <=> &0 < --x`] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_RNEG; GSYM REAL_INV_NEG] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_LT_2_1 o rand o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE `DISJOINT {a,b} {x} <=> ~(x = a) /\ ~(x = b)`] THEN
      CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_2; INSERT_AC]) THEN
      FIRST_ASSUM CONTR_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_LT_1_1 o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE `DISJOINT {a} {x} <=> ~(x = a)`] THEN
      ASM_MESON_TAC[COLLINEAR_BASIS_3];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; IN_ELIM_THM] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `s + t = &1 <=> s = &1- t`] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
    GEN_REWRITE_TAC (RAND_CONV o BINDER_CONV) [SWAP_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; RIGHT_EXISTS_AND_THM] THEN X_GEN_TAC `t:real` THEN
    AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; FORALL_2; FORALL_3; DIMINDEX_2; DIMINDEX_3;
             dropout; LAMBDA_BETA; BASIS_COMPONENT; ARITH; REAL_MUL_RID;
             VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RZERO; UNWIND_THM1;
             VECTOR_ADD_COMPONENT; REAL_ADD_LID; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[REAL_ARITH `x:real = t + y <=> t = x - y`] THEN
    REWRITE_TAC[EXISTS_REFL]]);;

let AZIM_EQ_PI_ALT = prove
 (`!v0 v1 w x.
        ~collinear{v0,v1,w} /\ ~collinear{v0,v1,x}
        ==> (azim v0 v1 w x = pi <=> x IN aff_lt {v0,v1} {w})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AZIM_EQ_PI_SYM) THEN
  ASM_SIMP_TAC[AZIM_EQ_PI]);;

let AZIM_EQ_0_PI_IMP_COPLANAR = prove
 (`!v0 v1 w1 w2.
        azim v0 v1 w1 w2 = &0 \/ azim v0 v1 w1 w2 = pi
        ==> coplanar {v0,v1,w1,w2}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `collinear {v0:real^3,v1,w1}` THENL
   [MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w1:real^3`; `w2:real^3`]
                NOT_COPLANAR_NOT_COLLINEAR) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    POP_ASSUM MP_TAC] THEN
  ASM_CASES_TAC `collinear {v0:real^3,v1,w2}` THENL
   [MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w2:real^3`; `w1:real^3`]
                NOT_COPLANAR_NOT_COLLINEAR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_AC] THEN CONV_TAC TAUT;
    POP_ASSUM MP_TAC] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t))
   [`w2:real^3`; `w1:real^3`; `v1:real^3`; `v0:real^3`] THEN
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  SIMP_TAC[AZIM_SPECIAL_SCALE] THEN
  ASM_SIMP_TAC[AZIM_ARG; COLLINEAR_SPECIAL_SCALE] THEN
  REWRITE_TAC[COLLINEAR_BASIS_3; ARG_EQ_0_PI] THEN
  REWRITE_TAC[real; IM_COMPLEX_DIV_EQ_0] THEN
  REWRITE_TAC[complex_mul; cnj; IM; RE] THEN
  REWRITE_TAC[REAL_ARITH `x * --y + a * b = &0 <=> x * y = a * b`] THEN
  REWRITE_TAC[RE_DEF; IM_DEF] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_TAC THEN DISCH_TAC THEN
  SIMP_TAC[dropout; LAMBDA_BETA; DIMINDEX_3; ARITH; DIMINDEX_2] THEN
  DISCH_TAC THEN REWRITE_TAC[coplanar] THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^3`; `w % basis 3:real^3`; `w1:real^3`] THEN
  ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = d INSERT {a,b,c}`] THEN
  ONCE_REWRITE_TAC[INSERT_SUBSET] THEN REWRITE_TAC[HULL_SUBSET] THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; HULL_INC] THEN
  REWRITE_TAC[SPAN_BREAKDOWN_EQ; SPAN_EMPTY; IN_SING] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; FORALL_3; dropout; LAMBDA_BETA;
           DIMINDEX_2; DIMINDEX_3; ARITH; VEC_COMPONENT; ARITH;
           VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  ASM_SIMP_TAC[EXISTS_REFL; REAL_FIELD
   `&0 < w ==> (x - k * w * &1 - y = &0 <=> k = (x - y) / w)`] THEN
  SUBGOAL_THEN `~((w1:real^3)$2 = &0) \/ ~((w2:real^3)$1 = &0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING;
    EXISTS_TAC `(w2:real^3)$2 / (w1:real^3)$2` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    EXISTS_TAC `(w2:real^3)$1 / (w1:real^3)$1` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD]);;

let AZIM_SAME_WITHIN_AFF_GE = prove
 (`!a u v w z.
        v IN aff_ge {a} {u,w} /\ ~collinear{a,u,v} /\ ~collinear{a,u,w}
        ==> azim a u v z = azim a u w z`,
  GEOM_ORIGIN_TAC `a:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `u:real^3` THEN
  X_GEN_TAC `u:real` THEN ASM_CASES_TAC `u = &0` THEN
  ASM_SIMP_TAC[AZIM_DEGENERATE; VECTOR_MUL_LZERO; REAL_LE_LT] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `w:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFF_GE_SCALE_LEMMA] THEN
  REWRITE_TAC[COLLINEAR_BASIS_3; AZIM_ARG] THEN
  ASM_SIMP_TAC[AFF_GE_1_2_0; BASIS_NONZERO; ARITH; DIMINDEX_3;
   SET_RULE `DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)`] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o AP_TERM `dropout 3:real^3->real^2`) THEN
  REWRITE_TAC[DROPOUT_ADD; DROPOUT_MUL; DROPOUT_BASIS_3] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  DISCH_THEN SUBST1_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_CMUL] THEN
  REWRITE_TAC[complex_div; COMPLEX_INV_MUL; GSYM CX_INV] THEN
  ONCE_REWRITE_TAC[COMPLEX_RING `a * b * c:complex = b * a * c`] THEN
  MATCH_MP_TAC ARG_MUL_CX THEN REWRITE_TAC[REAL_LT_INV_EQ] THEN
  ASM_REWRITE_TAC[REAL_LT_LE] THEN ASM_MESON_TAC[VECTOR_MUL_LZERO]);;

let AZIM_SAME_WITHIN_AFF_GE_ALT = prove
 (`!a u v w z.
        v IN aff_ge {a} {u,w} /\ ~collinear{a,u,v} /\ ~collinear{a,u,w}
        ==> azim a u z v = azim a u z w`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AZIM_SAME_WITHIN_AFF_GE) THEN
  ASM_CASES_TAC `collinear {a:real^3,u,z}` THEN
  ASM_SIMP_TAC[AZIM_DEGENERATE] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o rand o snd) THEN
  ASM_SIMP_TAC[]);;

let COLLINEAR_WITHIN_AFF_GE_COLLINEAR = prove
 (`!a u v w:real^N.
        v IN aff_ge {a} {u,w} /\ collinear{a,u,w} ==> collinear{a,v,w}`,
  GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `w:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = vec 0` THENL
   [ONCE_REWRITE_TAC[AFF_GE_DISJOINT_DIFF] THEN
    ASM_REWRITE_TAC[SET_RULE `{a} DIFF {a,b} = {}`] THEN
    REWRITE_TAC[GSYM CONVEX_HULL_AFF_GE] THEN
    ONCE_REWRITE_TAC[SET_RULE `{z,v,w} = {z,w,v}`] THEN
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
    MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
    ONCE_REWRITE_TAC[SET_RULE `{z,v,w} = {z,w,v}`] THEN
    ASM_REWRITE_TAC[COLLINEAR_LEMMA_ALT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_TAC `a:real`)) THEN
    ASM_SIMP_TAC[AFF_GE_1_2_0; SET_RULE
     `DISJOINT {a} {b,c} <=> ~(b = a) /\ ~(c = a)`] THEN
    REWRITE_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`b:real`; `c:real`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB; VECTOR_MUL_ASSOC] THEN
    MESON_TAC[]]);;

let AZIM_EQ_IMP = prove
 (`!v0 v1 w x y.
     ~collinear {v0, v1, w} /\
     ~collinear {v0, v1, y} /\
     x IN aff_gt {v0, v1} {y}
     ==> azim v0 v1 w x = azim v0 v1 w y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `v1:real^3 = v0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `collinear {v0:real^3,v1,x}` THENL
   [ALL_TAC; ASM_SIMP_TAC[AZIM_EQ_ALT]] THEN
  UNDISCH_TAC `collinear {v0:real^3,v1,x}` THEN
  MATCH_MP_TAC(TAUT
   `(s /\ p ==> r) ==> p ==> ~q /\ ~r /\ s ==> t`) THEN
  ASM_SIMP_TAC[COLLINEAR_3_IN_AFFINE_HULL] THEN
  ASM_CASES_TAC `y:real^3 = v0` THEN
  ASM_SIMP_TAC[HULL_INC; IN_INSERT] THEN
  ASM_CASES_TAC `y:real^3 = v1` THEN
  ASM_SIMP_TAC[HULL_INC; IN_INSERT] THEN
  ASM_SIMP_TAC[AFF_GT_2_1; SET_RULE
   `DISJOINT {a,b} {c} <=> ~(c = a) /\ ~(c = b)`] THEN
  REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t1:real`; `t2:real`; `t3:real`; `s1:real`; `s2:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (inv t3) :real^3->real^3`) THEN
  ASM_SIMP_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
               REAL_LT_IMP_NZ; VECTOR_ARITH
                `x:real^N = y + z + &1 % w <=> w = x - (y + z)`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `inv t3 * s1 - inv t3 * t1:real` THEN
  EXISTS_TAC `inv t3 * s2 - inv t3 * t2:real` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_FIELD
     `&0 < t ==> (inv t * a - inv t * b + inv t * c - inv t * d = &1 <=>
                  (a + c) - (b + d) = t)`] THEN
    ASM_REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

let AZIM_EQ_0_GE_IMP = prove
 (`!v0 v1 w x. x IN aff_ge {v0, v1} {w} ==> azim v0 v1 w x = &0`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `collinear {v0:real^3,v1,w}` THEN
  ASM_SIMP_TAC[AZIM_DEGENERATE] THEN
  ASM_CASES_TAC `collinear {v0:real^3,v1,x}` THEN
  ASM_SIMP_TAC[AZIM_DEGENERATE] THEN ASM_MESON_TAC[AZIM_EQ_0_GE_ALT]);;

let REAL_SGN_SIN_AZIM = prove
 (`!v w x y. real_sgn(sin(azim v w x y)) =
             real_sgn(((w - v) cross (x - v)) dot (y - v))`,
  GEOM_ORIGIN_TAC `v:real^3` THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN ASM_CASES_TAC `w = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; CROSS_LZERO; DOT_LZERO; REAL_SGN_0;
                  AZIM_REFL_ALT; SIN_0] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; CROSS_LMUL; DOT_LMUL] THEN
  REWRITE_TAC[REAL_SGN_MUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [real_sgn] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID; AZIM_ARG] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `real_sgn(Im(dropout 3 (y:real^3) / dropout 3 (x:real^3)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[REAL_SGN_IM_COMPLEX_DIV] THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; cross; VECTOR_3; DOT_3; dropout;
             LAMBDA_BETA; ARITH; cnj; complex_mul; RE_DEF; IM_DEF; DIMINDEX_2;
             complex; VECTOR_2; BASIS_COMPONENT] THEN REAL_ARITH_TAC] THEN

  SPEC_TAC(`(dropout 3:real^3->real^2) x`,`z:complex`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) y`,`w:complex`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 `z:complex` THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_MUL_RID] THEN
  X_GEN_TAC `x:real` THEN DISCH_TAC THEN X_GEN_TAC `z:complex` THEN
  ASM_CASES_TAC `x = &0` THENL
   [ASM_REWRITE_TAC[complex_div; COMPLEX_INV_0; COMPLEX_MUL_RZERO] THEN
    REWRITE_TAC[ARG_0; SIN_0; IM_CX; REAL_SGN_0];
    SUBGOAL_THEN `&0 < x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  ASM_SIMP_TAC[ARG_DIV_CX; IM_DIV_CX; REAL_SGN_DIV] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [real_sgn] THEN
  ASM_REWRITE_TAC[REAL_DIV_1] THEN ASM_CASES_TAC `z = Cx(&0)` THEN
  ASM_REWRITE_TAC[IM_CX; ARG_0; SIN_0] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [ARG] THEN
  REWRITE_TAC[IM_MUL_CX; REAL_SGN_MUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [real_sgn] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_NZ; REAL_MUL_LID] THEN
  REWRITE_TAC[IM_CEXP; RE_MUL_II; IM_MUL_II; RE_CX; REAL_SGN_MUL] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [real_sgn] THEN
  REWRITE_TAC[REAL_EXP_POS_LT; REAL_MUL_LID]);;

let AZIM_IN_UPPER_HALFSPACE = prove
 (`!v w x y. azim v w x y <= pi <=>
             &0 <= ((w - v) cross (x - v)) dot (y - v)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `&0 <= sin(azim v w x y)` THEN CONJ_TAC THENL
   [EQ_TAC THEN SIMP_TAC[SIN_POS_PI_LE; azim] THEN
    MP_TAC(ISPEC `azim v w x y - pi` SIN_POS_PI) THEN
    REWRITE_TAC[SIN_SUB; SIN_PI; COS_PI; azim;
                REAL_ARITH `x - pi < pi <=> x < &2 * pi`] THEN
    REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM REAL_SGN_INEQS] THEN
    REWRITE_TAC[REAL_SGN_SIN_AZIM]]);;

(* ------------------------------------------------------------------------- *)
(* Dihedral angle and relation to azimuth angle.                             *)
(* ------------------------------------------------------------------------- *)

let dihV = new_definition
  `dihV w0 w1 w2 w3 =
     let va = w2 - w0 in
     let vb = w3 - w0 in
     let vc = w1 - w0 in
     let vap = ( vc dot vc) % va - ( va dot vc) % vc in
     let vbp = ( vc dot vc) % vb - ( vb dot vc) % vc in
     arcV (vec 0) vap vbp`;;

let DIHV = prove
 (`dihV (w0:real^N) w1 w2 w3 =
     let va = w2 - w0 in
     let vb = w3 - w0 in
     let vc = w1 - w0 in
     let vap = (vc dot vc) % va - (va dot vc) % vc in
     let vbp = (vc dot vc) % vb - (vb dot vc) % vc in
     angle(vap,vec 0,vbp)`,
  REWRITE_TAC[dihV; ARCV_ANGLE]);;

let DIHV_TRANSLATION_EQ = prove
 (`!a w0 w1 w2 w3:real^N.
        dihV (a + w0) (a + w1) (a + w2) (a + w3) = dihV w0 w1 w2 w3`,
  REWRITE_TAC[DIHV; VECTOR_ARITH `(a + x) - (a + y):real^N = x - y`]);;

add_translation_invariants [DIHV_TRANSLATION_EQ];;

let DIHV_LINEAR_IMAGE = prove
 (`!f:real^M->real^N w0 w1 w2 w3.
        linear f /\ (!x. norm(f x) = norm x)
        ==> dihV (f w0) (f w1) (f w2) (f w3) = dihV w0 w1 w2 w3`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIHV] THEN
  ASM_SIMP_TAC[GSYM LINEAR_SUB] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[PRESERVES_NORM_PRESERVES_DOT] THEN
  ASM_SIMP_TAC[GSYM LINEAR_CMUL; GSYM LINEAR_SUB] THEN
  REWRITE_TAC[angle; VECTOR_SUB_RZERO] THEN
  ASM_SIMP_TAC[VECTOR_ANGLE_LINEAR_IMAGE_EQ]);;

add_linear_invariants [DIHV_LINEAR_IMAGE];;

let DIHV_SPECIAL_SCALE = prove
 (`!a v w1 w2:real^N.
        ~(a = &0)
        ==> dihV (vec 0) (a % v) w1 w2 = dihV (vec 0) v w1 w2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIHV; VECTOR_SUB_RZERO] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[DOT_LMUL; DOT_RMUL; GSYM VECTOR_MUL_ASSOC] THEN
  REWRITE_TAC[VECTOR_ARITH `a % a % x - a % b % a % y:real^N =
                            (a * a) % (x - b % y)`] THEN
  REWRITE_TAC[angle; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ANGLE_LMUL; VECTOR_ANGLE_RMUL] THEN
  ASM_REWRITE_TAC[REAL_LE_SQUARE; REAL_ENTIRE]);;

let DIHV_RANGE = prove
 (`!w0 w1 w2 w3. &0 <= dihV w0 w1 w2 w3 /\ dihV w0 w1 w2 w3 <= pi`,
  REWRITE_TAC[DIHV] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ANGLE_RANGE]);;

let COS_AZIM_DIHV = prove
 (`!v w v1 v2:real^3.
        ~collinear {v,w,v1} /\ ~collinear {v,w,v2}
        ==> cos(azim v w v1 v2) = cos(dihV v w v1 v2)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `w:real^3 = v` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; POP_ASSUM MP_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  GEOM_ORIGIN_TAC `v:real^3` THEN GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; DIHV_SPECIAL_SCALE; REAL_LT_IMP_NZ;
               COLLINEAR_SPECIAL_SCALE; COLLINEAR_BASIS_3] THEN
  DISCH_TAC THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  MAP_EVERY X_GEN_TAC [`w1:real^3`; `w2:real^3`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
  REWRITE_TAC[DIHV; VECTOR_SUB_RZERO] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
  SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; VECTOR_MUL_LID] THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `basis 3:real^3`; `w1:real^3`; `w2:real^3`]
        azim) THEN
  ABBREV_TAC `a = azim (vec 0) (basis 3) w1 (w2:real^3)` THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; VECTOR_SUB_RZERO; DIST_0] THEN
  MAP_EVERY X_GEN_TAC [`h1:real`; `h2:real`] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`basis 1:real^3`; `basis 2:real^3`; `basis 3:real^3`]) THEN
  SIMP_TAC[orthonormal; DOT_BASIS_BASIS; CROSS_BASIS; DIMINDEX_3; NORM_BASIS;
    ARITH; VECTOR_MUL_LID; BASIS_NONZERO; REAL_LT_01; LEFT_IMP_EXISTS_THM] THEN
  ASM_REWRITE_TAC[COLLINEAR_BASIS_3] THEN
  MAP_EVERY X_GEN_TAC [`psi:real`; `r1:real`; `r2:real`] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ADD_LID] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + b + c) - c:real^N = a + b`] THEN
  REWRITE_TAC[COS_ANGLE; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[vector_norm; GSYM DOT_EQ_0; DIMINDEX_3; FORALL_3; DOT_3] THEN
  REWRITE_TAC[VEC_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_ADD_LID; REAL_ADD_RID; REAL_MUL_RZERO] THEN
  REWRITE_TAC[REAL_ARITH `(r * c) * (r * c) + (r * s) * (r * s):real =
                          r pow 2 * (s pow 2 + c pow 2)`] THEN
  ASM_SIMP_TAC[SIN_CIRCLE; REAL_MUL_RID; REAL_POW_EQ_0; REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[POW_2_SQRT; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_ARITH `(r1 * c1) * (r2 * c2) + (r1 * s1) * (r2 * s2):real =
                          (r1 * r2) * (c1 * c2 + s1 * s2)`] THEN
  ASM_SIMP_TAC[REAL_FIELD
   `&0 < r1 /\ &0 < r2 ==> ((r1 * r2) * x) / (r1 * r2) = x`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real = b + c * d <=> b - --c * d = a`] THEN
  GEN_REWRITE_TAC (funpow 3 LAND_CONV) [GSYM COS_NEG] THEN
  REWRITE_TAC[GSYM SIN_NEG; GSYM COS_ADD] THEN AP_TERM_TAC THEN
  REAL_ARITH_TAC);;

let AZIM_DIHV_SAME = prove
 (`!v w v1 v2:real^3.
        ~collinear {v,w,v1} /\ ~collinear {v,w,v2} /\
        azim v w v1 v2 < pi
        ==> azim v w v1 v2 = dihV v w v1 v2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COS_INJ_PI THEN
  ASM_SIMP_TAC[COS_AZIM_DIHV; azim; REAL_LT_IMP_LE; DIHV_RANGE]);;

let AZIM_DIHV_COMPL = prove
 (`!v w v1 v2:real^3.
        ~collinear {v,w,v1} /\ ~collinear {v,w,v2} /\
        pi <= azim v w v1 v2
        ==> azim v w v1 v2 = &2 * pi - dihV v w v1 v2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[REAL_ARITH `x = &2 * pi - y <=> y = &2 * pi - x`] THEN
  MATCH_MP_TAC COS_INJ_PI THEN
  REWRITE_TAC[COS_SUB; SIN_NPI; COS_NPI; REAL_MUL_LZERO] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[COS_AZIM_DIHV; REAL_ADD_RID; REAL_MUL_LID] THEN
  ASM_REWRITE_TAC[DIHV_RANGE] THEN MATCH_MP_TAC(REAL_ARITH
   `p <= x /\ x < &2 * p ==> &0 <= &2 * p - x /\ &2 * p - x <= p`) THEN
  ASM_SIMP_TAC[azim]);;

let AZIM_DIVH = prove
 (`!v w v1 v2:real^3.
        ~collinear {v,w,v1} /\ ~collinear {v,w,v2}
        ==> azim v w v1 v2 = if azim v w v1 v2 < pi then dihV v w v1 v2
                             else &2 * pi - dihV v w v1 v2`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN
  ASM_SIMP_TAC[AZIM_DIHV_SAME; AZIM_DIHV_COMPL]);;

let AZIM_DIHV_EQ_0 = prove
 (`!v0 v1 w1 w2.
        ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
        ==> (azim v0 v1 w1 w2 = &0 <=> dihV v0 v1 w1 w2 = &0)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AZIM_DIVH o lhs o lhs o snd) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a:real = p - b <=> b = p - a`] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[REAL_ARITH `&2 * p - (&2 * p - a) = &0 <=> a = &0`] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a < &2 * pi /\ ~(a < pi) ==> (a = &0 <=> &2 * pi - a = &0)`) THEN
  ASM_REWRITE_TAC[azim]);;

let AZIM_DIHV_EQ_PI = prove
 (`!v0 v1 w1 w2.
        ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
        ==> (azim v0 v1 w1 w2 = pi <=> dihV v0 v1 w1 w2 = pi)`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AZIM_DIVH o lhs o lhs o snd) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let AZIM_EQ_0_PI_EQ_COPLANAR = prove
 (`!v0 v1 w1 w2.
        ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
        ==> (azim v0 v1 w1 w2 = &0 \/ azim v0 v1 w1 w2 = pi <=>
             coplanar {v0,v1,w1,w2})`,
  REWRITE_TAC[TAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  REWRITE_TAC[AZIM_EQ_0_PI_IMP_COPLANAR] THEN
  SIMP_TAC[GSYM IMP_CONJ_ALT; COPLANAR; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`v0:real^3`; `v1:real^3`; `v2:real^3`; `v3:real^3`; `p:real^3->bool`] THEN
  GEOM_HORIZONTAL_PLANE_TAC `p:real^3->bool` THEN
  REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              EMPTY_SUBSET] THEN
  SIMP_TAC[AZIM_DIHV_EQ_0; AZIM_DIHV_EQ_PI] THEN
  REWRITE_TAC[DIHV] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  DISCH_THEN(K ALL_TAC) THEN PAD2D3D_TAC THEN
  REWRITE_TAC[angle; VECTOR_SUB_RZERO] THEN
  GEOM_ORIGIN_TAC `v0:real^2` THEN REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (rand o rand) COLLINEAR_VECTOR_ANGLE o snd) THEN
  ANTS_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC); DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
  REWRITE_TAC[DOT_2; CART_EQ; FORALL_2; DIMINDEX_2; VEC_COMPONENT;
              VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let DIHV_EQ_0_PI_EQ_COPLANAR = prove
 (`!v0 v1 w1 w2:real^3.
        ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
        ==> (dihV v0 v1 w1 w2 = &0 \/ dihV v0 v1 w1 w2 = pi <=>
             coplanar {v0,v1,w1,w2})`,
  SIMP_TAC[GSYM AZIM_DIHV_EQ_0; GSYM AZIM_DIHV_EQ_PI;
           AZIM_EQ_0_PI_EQ_COPLANAR]);;

let DIHV_SYM = prove
 (`!v0 v1 v2 v3:real^N.
        dihV v0 v1 v3 v2 = dihV v0 v1 v2 v3`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DIHV] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[DOT_SYM; ANGLE_SYM]);;

let DIHV_NEG = prove
 (`!v0 v1 v2 v3. dihV (--v0) (--v1) (--v2) (--v3) = dihV v0 v1 v2 v3`,
  REWRITE_TAC[DIHV; VECTOR_ARITH `--a - --b:real^N = --(a - b)`] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[DOT_RNEG; DOT_LNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[VECTOR_MUL_RNEG] THEN
  REWRITE_TAC[angle; VECTOR_ARITH `--a - --b:real^N = --(a - b)`] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ANGLE_NEG2]);;

let DIHV_NEG_0 = prove
 (`!v1 v2 v3. dihV (vec 0) (--v1) (--v2) (--v3) = dihV (vec 0) v1 v2 v3`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM DIHV_NEG] THEN
  REWRITE_TAC[VECTOR_NEG_0]);;

let DIHV_ARCV = prove
 (`!e u v w:real^N.
      orthogonal (e - u) (v - u) /\ orthogonal (e - u) (w - u) /\ ~(e = u)
      ==> dihV u e v w = arcV u v w`,
  GEOM_ORIGIN_TAC `u:real^N` THEN
  REWRITE_TAC[dihV; orthogonal; VECTOR_SUB_RZERO] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  SIMP_TAC[DOT_SYM; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[ARCV_ANGLE; angle; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ANGLE_LMUL; VECTOR_ANGLE_RMUL] THEN
  SIMP_TAC[DOT_POS_LE; DOT_EQ_0]);;

let AZIM_DIHV_SAME_STRONG = prove
 (`!v w v1 v2:real^3.
        ~collinear {v,w,v1} /\ ~collinear {v,w,v2} /\
        azim v w v1 v2 <= pi
        ==> azim v w v1 v2 = dihV v w v1 v2`,
  REWRITE_TAC[REAL_LE_LT] THEN
  MESON_TAC[AZIM_DIHV_SAME; AZIM_DIHV_EQ_PI]);;

let AZIM_ARCV = prove
 (`!e u v w:real^3.
        orthogonal (e - u) (v - u) /\ orthogonal (e - u) (w - u) /\
        ~collinear{u,e,v} /\ ~collinear{u,e,w} /\
        azim u e v w <= pi
        ==> azim u e v w = arcV u v w`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `u:real^3 = e` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[GSYM DIHV_ARCV] THEN
  MATCH_MP_TAC AZIM_DIHV_SAME_STRONG THEN ASM_REWRITE_TAC[]);;

let COLLINEAR_AZIM_0_OR_PI = prove
 (`!u e v w. collinear {u,v,w} ==> azim u e v w = &0 \/ azim u e v w = pi`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `collinear{u:real^3,e,v}` THEN
  ASM_SIMP_TAC[AZIM_DEGENERATE] THEN
  ASM_CASES_TAC `collinear{u:real^3,e,w}` THEN
  ASM_SIMP_TAC[AZIM_DEGENERATE] THEN
  ASM_SIMP_TAC[AZIM_EQ_0_PI_EQ_COPLANAR] THEN
  ONCE_REWRITE_TAC[SET_RULE `{u,e,v,w} = {u,v,w,e}`] THEN
  ASM_MESON_TAC[NOT_COPLANAR_NOT_COLLINEAR]);;

let REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE = prove
 (`!f:real^M->real^N g h k x s.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      f continuous (at x within s) /\ g continuous (at x within s) /\
      h continuous (at x within s) /\ k continuous (at x within s)
      ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous (at x within s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dihV] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[ARCV_ANGLE; angle; REAL_CONTINUOUS_CONTINUOUS; o_DEF] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE THEN
  ASM_REWRITE_TAC[VECTOR_SUB_EQ; GSYM COLLINEAR_3_DOT_MULTIPLES] THEN
  CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC CONTINUOUS_MUL THEN REWRITE_TAC[o_DEF] THEN
  ASM_SIMP_TAC[CONTINUOUS_LIFT_DOT2; o_DEF; CONTINUOUS_SUB]);;

let REAL_CONTINUOUS_AT_DIHV_COMPOSE = prove
 (`!f:real^M->real^N g h k x.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      f continuous (at x) /\ g continuous (at x) /\
      h continuous (at x) /\ k continuous (at x)
      ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE]);;

let REAL_CONTINUOUS_WITHINREAL_DIHV_COMPOSE = prove
 (`!f:real->real^N g h k x s.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      f continuous (atreal x within s) /\ g continuous (atreal x within s) /\
      h continuous (atreal x within s) /\ k continuous (atreal x within s)
      ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous
          (atreal x within s)`,
  REWRITE_TAC[CONTINUOUS_CONTINUOUS_WITHINREAL;
              REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL] THEN
  SIMP_TAC[o_DEF; REAL_CONTINUOUS_WITHIN_DIHV_COMPOSE; LIFT_DROP]);;

let REAL_CONTINUOUS_ATREAL_DIHV_COMPOSE = prove
 (`!f:real->real^N g h k x.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      f continuous (atreal x) /\ g continuous (atreal x) /\
      h continuous (atreal x) /\ k continuous (atreal x)
      ==> (\x. dihV (f x) (g x) (h x) (k x)) real_continuous (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL_DIHV_COMPOSE]);;

let REAL_CONTINUOUS_AT_DIHV = prove
 (`!v w w1 w2:real^N.
        ~collinear {v, w, w2} ==> dihV v w w1 real_continuous at w2`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  REWRITE_TAC[dihV] THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC REAL_CONTINUOUS_CONTINUOUS_AT_COMPOSE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN
    SIMP_TAC[CONTINUOUS_CONST; o_DEF; CONTINUOUS_SUB; CONTINUOUS_AT_ID;
             CONTINUOUS_LIFT_DOT2];
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    REWRITE_TAC[ARCV_ANGLE; angle] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; ETA_AX] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE THEN
    POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `v:real^N` THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; CONTRAPOS_THM; VECTOR_SUB_EQ] THEN
    MAP_EVERY X_GEN_TAC [`z:real^N`; `w:real^N`] THEN
    ASM_CASES_TAC `w:real^N = vec 0` THEN
    ASM_REWRITE_TAC[COLLINEAR_LEMMA_ALT] THEN DISCH_THEN(MP_TAC o AP_TERM
     `(%) (inv((w:real^N) dot w)):real^N->real^N`) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; DOT_EQ_0] THEN
    MESON_TAC[VECTOR_MUL_LID]]);;

let REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE = prove
 (`!f:real^M->real^3 g h k x s.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      ~(k x IN aff_ge {f x,g x} {h x}) /\
      f continuous (at x within s) /\ g continuous (at x within s) /\
      h continuous (at x within s) /\ k continuous (at x within s)
      ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous (at x within s)`,
  let lemma = prove
   (`!s t u f:real^M->real^N g h.
          (closed s /\ closed t) /\ s UNION t = UNIV /\
          (g continuous_on (u INTER s) /\ h continuous_on (u INTER t)) /\
          (!x. x IN u INTER s ==> g x = f x) /\
          (!x. x IN u INTER t ==> h x = f x)
          ==> f continuous_on u`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `u:real^M->bool = (u INTER s) UNION (u INTER t)`
    SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_UNION_LOCAL THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `s:real^M->bool` THEN ASM SET_TAC[];
      EXISTS_TAC `t:real^M->bool` THEN ASM SET_TAC[];
      ASM_MESON_TAC[CONTINUOUS_ON_EQ];
      ASM_MESON_TAC[CONTINUOUS_ON_EQ]]) in
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS; o_DEF] THEN
  SUBGOAL_THEN
   `(\x:real^M. Cx(azim (f x) (g x) (h x) (k x))) =
    (\z. Cx(azim (vec 0) (fstcart z)
                 (fstcart(sndcart z)) (sndcart(sndcart z)))) o
    (\x. pastecart (g x - f x) (pastecart (h x - f x) (k x - f x)))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    X_GEN_TAC `y:real^M` THEN
    SUBST1_TAC(VECTOR_ARITH `vec 0 = (f:real^M->real^3) y - f y`) THEN
    SIMP_TAC[ONCE_REWRITE_RULE[VECTOR_ADD_SYM] AZIM_TRANSLATION; VECTOR_SUB];
    MATCH_MP_TAC CONTINUOUS_WITHIN_COMPOSE THEN
    ASM_SIMP_TAC[CONTINUOUS_PASTECART; CONTINUOUS_SUB]] THEN
  MATCH_MP_TAC CONTINUOUS_AT_WITHIN THEN
  SUBGOAL_THEN
   `!z. ~collinear {vec 0,fstcart z,fstcart(sndcart z)} /\
        ~collinear {vec 0,fstcart z,sndcart(sndcart z)} /\
        ~(sndcart(sndcart z) IN aff_ge {vec 0,fstcart z} {fstcart(sndcart z)})
        ==> (\z. Cx(azim (vec 0) (fstcart z) (fstcart(sndcart z))
                                             (sndcart(sndcart z))))
            continuous (at z)`
  MATCH_MP_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[FSTCART_PASTECART; SNDCART_PASTECART; GSYM COLLINEAR_3] THEN
    REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[INSERT_AC]; ALL_TAC]) THEN
    SUBST1_TAC(VECTOR_ARITH `vec 0 = (f:real^M->real^3) x - f x`) THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b} = {a} UNION {b}`] THEN
    REWRITE_TAC[GSYM IMAGE_UNION; SET_RULE
     `{a - b:real^3} = IMAGE (\x. x - b) {a}`] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[VECTOR_ADD_SYM] AFF_GE_TRANSLATION;
                VECTOR_SUB] THEN
    ASM_REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `a + x:real^3 = b + x <=> a = b`;
                    UNWIND_THM1; SET_RULE `{a} UNION {b} = {a,b}`]] THEN
  ONCE_REWRITE_TAC[SET_RULE
   `(!x. ~P x /\ ~Q x /\ ~R x ==> J x) <=>
    (!x. x IN UNIV DIFF (({x | P x} UNION {x | Q x}) UNION {x | R x})
         ==> J x)`] THEN
  MATCH_MP_TAC(MESON[CONTINUOUS_ON_EQ_CONTINUOUS_AT]
   `open s /\ f continuous_on s ==> !z. z IN s ==> f continuous at z`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN
    MATCH_MP_TAC(MESON[]
     `!t'. s UNION t = s UNION t' /\ closed(s UNION t')
           ==> closed(s UNION t)`) THEN
    EXISTS_TAC
      `{z | (fstcart z cross fstcart(sndcart z)) cross
             fstcart z cross sndcart(sndcart z) = vec 0 /\
            &0 <= (fstcart z cross sndcart(sndcart z)) dot
                  (fstcart z cross fstcart(sndcart z))}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. ~(x IN s) ==> (x IN t <=> x IN t'))
        ==> s UNION t = s UNION t'`) THEN
      REWRITE_TAC[AFF_GE_2_1_0_SEMIALGEBRAIC; IN_UNION; IN_ELIM_THM;
                  DE_MORGAN_THM];
      ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THEN
      REWRITE_TAC[GSYM DOT_CAUCHY_SCHWARZ_EQUAL] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
      REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN
      SIMP_TAC[SET_RULE `{x | f x = a} = {x | x IN UNIV /\ f x IN {a}}`] THEN
      MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      SIMP_TAC[CLOSED_UNIV; CLOSED_SING; LIFT_SUB; REAL_POW_2; LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF] THEN REPEAT CONJ_TAC THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN CONJ_TAC;
      ONCE_REWRITE_TAC[MESON[LIFT_DROP; real_ge]
       `&0 <= x <=> drop(lift x) >= &0`] THEN
      REWRITE_TAC[SET_RULE
       `{z | f z = vec 0 /\ drop(g z) >= &0} =
        {z | z IN UNIV /\ f z IN {vec 0}} INTER
        {z | z IN UNIV /\ g z IN {k | drop(k) >= &0}}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      REWRITE_TAC[CLOSED_SING; drop; CLOSED_UNIV;
                  CLOSED_HALFSPACE_COMPONENT_GE] THEN
      REPEAT((MATCH_MP_TAC CONTINUOUS_ON_CROSS ORELSE
              MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2) THEN CONJ_TAC)] THEN
    TRY(GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF]) THEN
    SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_CONTINUOUS_ON;
             LINEAR_FSTCART; LINEAR_SNDCART];
    MATCH_MP_TAC lemma THEN
    MAP_EVERY EXISTS_TAC
     [`{z | z IN UNIV /\ lift((fstcart z cross (fstcart(sndcart z))) dot
                              (sndcart(sndcart z))) IN {x | x$1 >= &0}}`;
      `{z | z IN UNIV /\ lift((fstcart z cross (fstcart(sndcart z))) dot
                              (sndcart(sndcart z))) IN {x | x$1 <= &0}}`;
      `\z. Cx(dihV (vec 0:real^3) (fstcart z)
                   (fstcart(sndcart z)) (sndcart(sndcart z)))`;
      `\z. Cx(&2 * pi - dihV (vec 0:real^3) (fstcart z)
                             (fstcart(sndcart z)) (sndcart(sndcart z)))`] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE THEN
      REWRITE_TAC[CLOSED_UNIV; CLOSED_HALFSPACE_COMPONENT_GE;
                  CLOSED_HALFSPACE_COMPONENT_LE] THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_DOT2 THEN
      (CONJ_TAC THENL [MATCH_MP_TAC CONTINUOUS_ON_CROSS; ALL_TAC]) THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      SIMP_TAC[CONTINUOUS_ON_COMPOSE; LINEAR_CONTINUOUS_ON;
               LINEAR_FSTCART; LINEAR_SNDCART];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIV; IN_ELIM_THM] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[FORALL_PASTECART; IN_DIFF; IN_UNIV; IN_UNION; IN_INTER;
        FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM; DE_MORGAN_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[CX_SUB] THEN
      TRY(MATCH_MP_TAC CONTINUOUS_SUB THEN REWRITE_TAC[CONTINUOUS_CONST]) THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS] THEN
      MATCH_MP_TAC REAL_CONTINUOUS_AT_DIHV_COMPOSE THEN
      ASM_REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART;
                      CONTINUOUS_CONST] THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      SIMP_TAC[CONTINUOUS_AT_COMPOSE; LINEAR_CONTINUOUS_AT;
               LINEAR_FSTCART; LINEAR_SNDCART];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PASTECART; IN_DIFF; IN_UNIV; IN_UNION; IN_INTER; CX_INJ;
        FSTCART_PASTECART; SNDCART_PASTECART; IN_ELIM_THM; DE_MORGAN_THM] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM drop; LIFT_DROP; real_ge] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM AZIM_DIHV_SAME_STRONG) THEN
      ASM_REWRITE_TAC[AZIM_IN_UPPER_HALFSPACE; VECTOR_SUB_RZERO];
      REWRITE_TAC[GSYM drop; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(GSYM AZIM_DIHV_COMPL) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `(x <= pi ==> x = pi) ==> pi <= x`) THEN
      ASM_REWRITE_TAC[AZIM_IN_UPPER_HALFSPACE; VECTOR_SUB_RZERO] THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= &0 ==> (&0 <= x <=> x = &0)`] THEN
      REWRITE_TAC[REWRITE_RULE[VECTOR_SUB_RZERO]
         (SPEC `vec 0:real^3` (GSYM COPLANAR_CROSS_DOT))] THEN
      ASM_SIMP_TAC[GSYM AZIM_EQ_0_PI_EQ_COPLANAR; AZIM_EQ_0_GE_ALT]]]);;

let REAL_CONTINUOUS_AT_AZIM_COMPOSE = prove
 (`!f:real^M->real^3 g h k x.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      ~(k x IN aff_ge {f x,g x} {h x}) /\
      f continuous (at x) /\ g continuous (at x) /\
      h continuous (at x) /\ k continuous (at x)
      ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous (at x)`,
  ONCE_REWRITE_TAC[GSYM WITHIN_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE]);;

let REAL_CONTINUOUS_WITHINREAL_AZIM_COMPOSE = prove
 (`!f:real->real^3 g h k x s.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      ~(k x IN aff_ge {f x,g x} {h x}) /\
      f continuous (atreal x within s) /\ g continuous (atreal x within s) /\
      h continuous (atreal x within s) /\ k continuous (atreal x within s)
      ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous
          (atreal x within s)`,
  REWRITE_TAC[CONTINUOUS_CONTINUOUS_WITHINREAL;
              REAL_CONTINUOUS_REAL_CONTINUOUS_WITHINREAL] THEN
  SIMP_TAC[o_DEF; REAL_CONTINUOUS_WITHIN_AZIM_COMPOSE; LIFT_DROP]);;

let REAL_CONTINUOUS_ATREAL_AZIM_COMPOSE = prove
 (`!f:real->real^3 g h k x.
      ~collinear {f x,g x,h x} /\ ~collinear {f x,g x,k x} /\
      ~(k x IN aff_ge {f x,g x} {h x}) /\
      f continuous (atreal x) /\ g continuous (atreal x) /\
      h continuous (atreal x) /\ k continuous (atreal x)
      ==> (\x. azim (f x) (g x) (h x) (k x)) real_continuous (atreal x)`,
  ONCE_REWRITE_TAC[GSYM WITHINREAL_UNIV] THEN
  REWRITE_TAC[REAL_CONTINUOUS_WITHINREAL_AZIM_COMPOSE]);;

(* ------------------------------------------------------------------------- *)
(* Can consider angle as defined by arcV a zenith angle.                     *)
(* ------------------------------------------------------------------------- *)

let ZENITH_EXISTS = prove
 (`!u v w:real^3.
       ~(u = v) /\ ~(w = v)
       ==> (?u' r phi e3.
                phi = arcV v u w /\
                r = dist(u,v) /\
                dist(w,v) % e3 = w - v /\
                u' dot e3 = &0 /\
                u = v + u' + (r * cos phi) % e3)`,
  ONCE_REWRITE_TAC[VECTOR_ARITH
   `u:real^3 = v + u' + x <=> u - v = u' + x`] THEN
  GEN_GEOM_ORIGIN_TAC `v:real^3` ["u'"; "e3"] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
  ONCE_REWRITE_TAC[VECTOR_ARITH
   `u:real^3 = u' + x <=> u - u' = x`] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN ASM_CASES_TAC `w = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_LT] THEN DISCH_TAC THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < w ==> abs w * &1 = w`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  REWRITE_TAC[ARCV_ANGLE; angle; VECTOR_SUB_RZERO] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^3`; `w % basis 3:real^3`] VECTOR_ANGLE) THEN
  REWRITE_TAC[DOT_RMUL; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < w ==> n * ((abs w) * x) * y = w * n * x * y`] THEN
  ASM_REWRITE_TAC[REAL_EQ_MUL_LCANCEL] THEN
  SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_LID] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[VECTOR_ARITH `u - u':real^3 = x <=> u' = u - x`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RMUL; DOT_LMUL] THEN
  SIMP_TAC[DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Spherical coordinates.                                                    *)
(* ------------------------------------------------------------------------- *)

let SPHERICAL_COORDINATES = prove
 (`!u v w u' e1 e2 e3 r phi theta.
       ~collinear {v, w, u} /\
       ~collinear {v, w, u'} /\
       orthonormal e1 e2 e3 /\
       dist(w,v) % e3 = w - v /\
       (v + e1) IN aff_gt {v, w} {u} /\
       r = dist(v,u') /\
       phi = arcV v u' w /\
       theta = azim v w u u'
       ==> u' = v + (r * cos theta * sin phi) % e1 +
                    (r * sin theta * sin phi) % e2 +
                    (r * cos phi) % e3`,
  ONCE_REWRITE_TAC[VECTOR_ARITH
   `u':real^3 = u + v + w <=> u' - u = v + w`] THEN
  GEN_GEOM_ORIGIN_TAC `v:real^3` ["e1"; "e2"; "e3"] THEN
  REWRITE_TAC[VECTOR_ADD_RID; VECTOR_ADD_LID] THEN
  REWRITE_TAC[TRANSLATION_INVARIANTS `v:real^3`] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
  X_GEN_TAC `w:real` THEN ASM_CASES_TAC `w = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_LE_LT] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC
   [`u:real^3`; `v:real^3`; `e1:real^3`; `e2:real^3`; `e3:real^3`;
    `r:real`; `phi:real`; `theta:real`] THEN
  ASM_CASES_TAC `u:real^3 = w % basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = w % basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o GSYM) THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < w ==> abs w * &1 = w`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
  ASM_CASES_TAC `e3:real^3 = basis 3` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARCV_ANGLE; angle; VECTOR_SUB_RZERO] THEN
  ASM_SIMP_TAC[VECTOR_ANGLE_RMUL; REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `u:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `u:real^3 = basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v:real^3`; `basis 3:real^3`] VECTOR_ANGLE) THEN
  ASM_SIMP_TAC[DOT_BASIS; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_LID] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL
   [`vec 0:real^3`; `w % basis 3:real^3`; `u:real^3`; `e1:real^3`]
        AZIM_EQ_0_ALT) THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  ANTS_TAC THENL
   [SIMP_TAC[COLLINEAR_LEMMA; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    STRIP_TAC THEN UNDISCH_TAC `orthonormal e1 e2 (basis 3)` THEN
    ASM_REWRITE_TAC[orthonormal; DOT_LZERO; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    ASM_CASES_TAC `c = &0` THEN
    ASM_SIMP_TAC[VECTOR_MUL_LZERO; CROSS_LZERO; DOT_LZERO; REAL_LT_REFL;
                 DOT_LMUL; DOT_BASIS_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `dropout 3 (v:real^3):real^2 =
    norm(dropout 3 (v:real^3):real^2) %
    (cos theta % (dropout 3 (e1:real^3)) +
     sin theta % (dropout 3 (e2:real^3)))`
  MP_TAC THENL
   [ALL_TAC;
    SUBGOAL_THEN `norm((dropout 3:real^3->real^2) v) = r * sin phi`
    SUBST1_TAC THENL
     [REWRITE_TAC[NORM_EQ_SQUARE] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[REAL_LE_MUL; NORM_POS_LE; SIN_VECTOR_ANGLE_POS];
        ALL_TAC] THEN
      UNDISCH_TAC `(v:real^3)$3 = r * cos phi` THEN
      MATCH_MP_TAC(REAL_RING
       `x + a pow 2 = y + b pow 2 ==> a:real = b ==> x = y`) THEN
      REWRITE_TAC[REAL_POW_MUL; GSYM REAL_ADD_LDISTRIB] THEN
      REWRITE_TAC[SIN_CIRCLE; REAL_MUL_RID] THEN
      UNDISCH_THEN `norm(v:real^3) = r` (SUBST1_TAC o SYM) THEN
      REWRITE_TAC[NORM_POW_2; DOT_2; DOT_3] THEN
      SIMP_TAC[dropout; LAMBDA_BETA; DIMINDEX_2; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; DIMINDEX_2; FORALL_3; FORALL_2] THEN
    SIMP_TAC[dropout; LAMBDA_BETA; DIMINDEX_2; ARITH; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3] THEN
    REPEAT STRIP_TAC THEN TRY REAL_ARITH_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [orthonormal]) THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH] THEN CONV_TAC REAL_RING] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE LAND_CONV [AZIM_ARG])) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE RAND_CONV [COLLINEAR_BASIS_3])) THEN
  SUBGOAL_THEN `norm((dropout 3:real^3->real^2) e1) = &1 /\
                norm((dropout 3:real^3->real^2) e2) = &1 /\
                dropout 3 (e2:real^3) / dropout 3 (e1:real^3) = ii`
  MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(a /\ b) /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_EQ_1] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [orthonormal]) THEN
      SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH; dropout; LAMBDA_BETA;
               DOT_2; DIMINDEX_2; DOT_3] THEN
      CONV_TAC REAL_RING;
      ALL_TAC] THEN
    ASM_CASES_TAC `dropout 3 (e1:real^3) = Cx(&0)` THEN
    ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_OF_NUM_EQ; ARITH_EQ; REAL_ABS_NUM] THEN
    ASM_SIMP_TAC[COMPLEX_FIELD
     `~(x = Cx(&0)) ==> (y / x = ii <=> y = ii * x)`] THEN
    DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP ORTHONORMAL_CROSS) THEN
    SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3;
             cross; VECTOR_3; BASIS_COMPONENT; ARITH; dropout; LAMBDA_BETA;
             complex_mul; ii; complex; RE_DEF; IM_DEF; VECTOR_2] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) e2`,`d2:real^2`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) e1`,`d1:real^2`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) v`,`z:real^2`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) u`,`w:real^2`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `w:real^2` THEN
  X_GEN_TAC `k:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `k = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
  SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID] THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `d1 = Cx(&1)` THENL
   [ASM_SIMP_TAC[COMPLEX_DIV_1; COMPLEX_MUL_LID] THEN
    REPEAT STRIP_TAC THEN MP_TAC(SPEC `z:complex` ARG) THEN
    ASM_REWRITE_TAC[CEXP_EULER; CX_SIN; CX_COS; COMPLEX_MUL_RID] THEN
    CONV_TAC COMPLEX_RING;
    ASM_REWRITE_TAC[ARG_EQ_0] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [COMPLEX_EQ]) THEN
    REWRITE_TAC[RE_CX; IM_CX;real] THEN
    ASM_CASES_TAC `Im d1 = &0` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_NORM; real] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Definition of a wedge and invariance theorems.                            *)
(* ------------------------------------------------------------------------- *)

let wedge = new_definition
 `wedge v0 v1 w1 w2 = {y | ~collinear {v0,v1,y} /\
                         &0 < azim v0 v1 w1 y /\
                         azim v0 v1 w1 y < azim v0 v1 w1 w2}`;;

let WEDGE_ALT = prove
 (`!v0 v1 w1 w2.
        ~(v0 = v1)
        ==> wedge v0 v1 w1 w2 = {y | ~(y IN affine hull {v0,v1}) /\
                                     &0 < azim v0 v1 w1 y /\
                                     azim v0 v1 w1 y < azim v0 v1 w1 w2}`,
  SIMP_TAC[wedge; COLLINEAR_3_AFFINE_HULL]);;

let WEDGE_TRANSLATION = prove
 (`!a v w w1 w2. wedge (a + v) (a + w) (a + w1) (a + w2) =
                 IMAGE (\x. a + x) (wedge v w w1 w2)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
   [MESON_TAC[VECTOR_ARITH `a + (x - a):real^3 = x`]; ALL_TAC] THEN
  REWRITE_TAC[wedge; IN_ELIM_THM; AZIM_TRANSLATION] THEN
  REWRITE_TAC[SET_RULE
   `{a + x,a + y,a + z} = IMAGE (\x:real^N. a + x) {x,y,z}`] THEN
  REWRITE_TAC[COLLINEAR_TRANSLATION_EQ]);;

add_translation_invariants [WEDGE_TRANSLATION];;

let WEDGE_LINEAR_IMAGE = prove
 (`!f. linear f /\ (!x. norm(f x) = norm x) /\
       (2 <= dimindex(:3) ==> det(matrix f) = &1)
       ==> !v w w1 w2. wedge (f v) (f w) (f w1) (f w2) =
                       IMAGE f (wedge v w w1 w2)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE;
                  ORTHOGONAL_TRANSFORMATION];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[wedge; IN_ELIM_THM] THEN
  BINOP_TAC THEN ASM_SIMP_TAC[AZIM_LINEAR_IMAGE] THEN
  SUBST1_TAC(SET_RULE `{f v,f w,f y} = IMAGE (f:real^3->real^3) {v,w,y}`) THEN
  ASM_MESON_TAC[COLLINEAR_LINEAR_IMAGE_EQ; PRESERVES_NORM_INJECTIVE]);;

add_linear_invariants [WEDGE_LINEAR_IMAGE];;

let WEDGE_SPECIAL_SCALE = prove
 (`!a v w1 w2.
        &0 < a /\
        ~collinear{vec 0,a % v,w1} /\
        ~collinear{vec 0,a % v,w2}
        ==> wedge (vec 0) (a % v) w1 w2 = wedge (vec 0) v w1 w2`,
  SIMP_TAC[wedge; AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE;
           REAL_LT_IMP_NZ]);;

let WEDGE_DEGENERATE = prove
 (`(!z w w1 w2. z = w ==> wedge z w w1 w2 = {}) /\
   (!z w w1 w2. collinear{z,w,w1} ==> wedge z w w1 w2 = {}) /\
   (!z w w1 w2. collinear{z,w,w2} ==> wedge z w w1 w2 = {})`,
  REWRITE_TAC[wedge] THEN SIMP_TAC[AZIM_DEGENERATE] THEN
  REWRITE_TAC[REAL_LT_REFL; REAL_LT_ANTISYM; EMPTY_GSPEC]);;

(* ------------------------------------------------------------------------- *)
(* Basic relation between wedge and aff, so Tarski-type characterization.    *)
(* ------------------------------------------------------------------------- *)

let AFF_GT_LEMMA = prove
 (`!v1 v2:real^N.
        &0 < t1 /\ ~(v2 = vec 0)
        ==> aff_gt {vec 0} {t1 % basis 1, v2} =
                {a % basis 1 + b % v2 | &0 < a /\ &0 < b}`,
  REWRITE_TAC[AFFSIGN_ALT; aff_gt_def; sgn_gt; IN_ELIM_THM] THEN
  REWRITE_TAC[SET_RULE `{a} UNION {b,c} = {a,b,c}`] THEN
  REWRITE_TAC[SET_RULE `x IN {a} <=> a = x`] THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
               RIGHT_EXISTS_AND_THM; REAL_LT_ADD; REAL_HALF; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[IN_INSERT; VECTOR_ARITH `vec 0 = a % x <=> a % x = vec 0`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; BASIS_NONZERO;
               DIMINDEX_GE_1; LE_REFL] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[REAL_ARITH `&1 - v - v' - v'' = &0 <=> v = &1 - v' - v''`] THEN
  ONCE_REWRITE_TAC[MESON[] `(?a b c. P a b c) <=> (?b c a. P a b c)`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `b:real` THEN
  REWRITE_TAC[VECTOR_ARITH `y - a - b:real^N = vec 0 <=> y = a + b`] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `a * t1:real`; EXISTS_TAC `a / t1:real`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]);;

let WEDGE_LUNE_GT = prove
 (`!v0 v1 w1 w2.
        ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2} /\
        &0 < azim v0 v1 w1 w2 /\ azim v0 v1 w1 w2 < pi
        ==> wedge v0 v1 w1 w2 = aff_gt {v0,v1} {w1,w2}`,
  let lemma = prove
   (`!a x:real^3. (?a. x = a % basis 3) <=> dropout 3 x:real^2 = vec 0`,
    SIMP_TAC[CART_EQ; FORALL_2; FORALL_3; DIMINDEX_2; DIMINDEX_3;
        dropout; LAMBDA_BETA; BASIS_COMPONENT; ARITH; REAL_MUL_RID;
        VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RZERO; UNWIND_THM1] THEN
    MESON_TAC[]) in
  REWRITE_TAC[wedge] THEN GEOM_ORIGIN_TAC `v0:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`w1:real^3`; `w2:real^3`] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  ONCE_REWRITE_TAC[TAUT `~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))`] THEN
  ASM_SIMP_TAC[AZIM_ARG] THEN REWRITE_TAC[COLLINEAR_BASIS_3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SPECIAL_SCALE o rand o snd) THEN
  SUBGOAL_THEN
   `~(w1:real^3 = vec 0) /\ ~(w2:real^3 = vec 0) /\
    ~(w1 = basis 3) /\ ~(w2 = basis 3)`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
    ASM_REWRITE_TAC[DROPOUT_BASIS_3; DROPOUT_0; DROPOUT_MUL; VECTOR_MUL_RZERO];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(DISJ_CASES_THEN (SUBST_ALL_TAC o SYM)) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
    ASM_REWRITE_TAC[DROPOUT_BASIS_3; DROPOUT_0; DROPOUT_MUL; VECTOR_MUL_RZERO];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[AFFSIGN_ALT; aff_gt_def; sgn_gt; IN_ELIM_THM] THEN
  REWRITE_TAC[SET_RULE `{a,b} UNION {c,d} = {a,b,d,c}`] THEN
  REWRITE_TAC[SET_RULE `x IN {a} <=> a = x`] THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
               RIGHT_EXISTS_AND_THM; REAL_LT_ADD; REAL_HALF; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `{y | (dropout 3:real^3->real^2) y IN
                   aff_gt {vec 0}
                   {dropout 3 (w1:real^3),dropout 3 (w2:real^3)}}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[AFFSIGN_ALT; aff_gt_def; sgn_gt; IN_ELIM_THM] THEN
    REWRITE_TAC[SET_RULE `{a} UNION {b,c} = {a,b,c}`] THEN
    REWRITE_TAC[SET_RULE `x IN {a} <=> a = x`] THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
               RIGHT_EXISTS_AND_THM; REAL_LT_ADD; REAL_HALF; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
    REWRITE_TAC[REAL_EQ_SUB_RADD; RIGHT_AND_EXISTS_THM] THEN
    REWRITE_TAC[REAL_ARITH `&1 = x + v <=> v = &1 - x`] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
    ONCE_REWRITE_TAC[MESON[]
      `(?a b c d. P a b c d) <=> (?b c d a. P a b c d)`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    ONCE_REWRITE_TAC[MESON[]
      `(?a b c. P a b c) <=> (?c b a. P a b c)`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[VECTOR_ARITH
     `y - a - b - c:real^N = vec 0 <=> y - b - c = a`] THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; lemma] THEN
    REWRITE_TAC[DROPOUT_SUB; DROPOUT_MUL] THEN
    REWRITE_TAC[VECTOR_ARITH `y - a - b:real^2 = vec 0 <=> y = a + b`] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[VECTOR_ADD_SYM]] THEN
  MATCH_MP_TAC(SET_RULE
   `{x | P x} = s ==> {y | P(dropout 3 y)} = {y | dropout 3 y IN s}`) THEN
  MP_TAC(CONJ (ASSUME `~((dropout 3:real^3->real^2) w1 = vec 0)`)
              (ASSUME `~((dropout 3:real^3->real^2) w2 = vec 0)`)) THEN
  UNDISCH_TAC `Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3)) < pi` THEN
  UNDISCH_TAC `&0 < Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))` THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w2`,`v2:complex`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w1`,`v1:complex`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 `v1:complex` THEN
  X_GEN_TAC `v1:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `v1 = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  SIMP_TAC[AFF_GT_LEMMA] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
  ASM_SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID; CX_INJ] THEN DISCH_TAC THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN X_GEN_TAC `z:complex` THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:complex` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`\t. Arg(Cx t + Cx(&1 - t) * z)`;
                  `&0`; `&1`; `Arg w`] REAL_IVT_DECREASING) THEN
    REWRITE_TAC[REAL_POS; REAL_SUB_REFL; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[REAL_SUB_RZERO; COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
    ASM_SIMP_TAC[COMPLEX_ADD_RID; ARG_NUM; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [REWRITE_TAC[REAL_CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      REWRITE_TAC[REAL_CONTINUOUS_CONTINUOUS; IN_REAL_INTERVAL] THEN
      X_GEN_TAC `t:real` THEN STRIP_TAC THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN REWRITE_TAC[o_ASSOC] THEN
      MATCH_MP_TAC CONTINUOUS_WITHINREAL_COMPOSE THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ADD THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC LAND_CONV [SYM(CONJUNCT2(SPEC_ALL I_O_ID))] THEN
          REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS] THEN
          REWRITE_TAC[I_DEF; REAL_CONTINUOUS_WITHIN_ID];
          MATCH_MP_TAC CONTINUOUS_COMPLEX_MUL THEN
          REWRITE_TAC[CONTINUOUS_CONST] THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
          REWRITE_TAC[GSYM REAL_CONTINUOUS_CONTINUOUS] THEN
          SIMP_TAC[REAL_CONTINUOUS_SUB; REAL_CONTINUOUS_CONST;
                   REAL_CONTINUOUS_WITHIN_ID]];
        MATCH_MP_TAC CONTINUOUS_WITHIN_SUBSET THEN
        EXISTS_TAC `{z | &0 <= Im z}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_WITHIN_UPPERHALF_ARG THEN
          ASM_CASES_TAC `t = &1` THENL
           [ASM_REWRITE_TAC[REAL_SUB_REFL] THEN CONV_TAC COMPLEX_RING;
            ALL_TAC] THEN
          DISCH_THEN(MP_TAC o AP_TERM `Im`) THEN
          REWRITE_TAC[IM_ADD; IM_CX; IM_MUL_CX; REAL_ADD_LID; REAL_ENTIRE] THEN
          ASM_REWRITE_TAC[REAL_SUB_0] THEN
          ASM_MESON_TAC[ARG_LT_PI; REAL_LT_IMP_NZ; REAL_LT_TRANS];
          REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_REAL_INTERVAL] THEN
          REWRITE_TAC[IN_ELIM_THM; IM_ADD; IM_CX; IM_MUL_CX] THEN
          REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ADD_LID] THEN
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[GSYM ARG_LE_PI] THEN
          ASM_REAL_ARITH_TAC]];
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real` MP_TAC) THEN
      ASM_CASES_TAC `t = &0` THENL
       [ASM_REWRITE_TAC[REAL_SUB_RZERO; COMPLEX_ADD_LID; COMPLEX_MUL_LID] THEN
        ASM_MESON_TAC[REAL_LT_REFL];
        ALL_TAC] THEN
      ASM_CASES_TAC `t = &1` THENL
       [ASM_REWRITE_TAC[REAL_SUB_REFL; COMPLEX_MUL_LZERO] THEN
        REWRITE_TAC[COMPLEX_ADD_RID; ARG_NUM] THEN ASM_MESON_TAC[REAL_LT_REFL];
        ALL_TAC] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_LE_LT] THEN
      ASM_REWRITE_TAC[] THEN ABBREV_TAC `u = Cx t + Cx(&1 - t) * z` THEN
      ASM_CASES_TAC `u = Cx(&0)` THENL
       [ASM_MESON_TAC[ARG_0; REAL_LT_REFL]; ALL_TAC] THEN
      STRIP_TAC THEN
      EXISTS_TAC `norm(w:complex) / norm(u:complex) * t` THEN
      EXISTS_TAC `norm(w:complex) / norm(u:complex) * (&1 - t)` THEN
      ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV; COMPLEX_NORM_NZ; REAL_SUB_LT] THEN
      SIMP_TAC[CX_MUL; GSYM COMPLEX_MUL_ASSOC; GSYM COMPLEX_ADD_LDISTRIB] THEN
      ASM_REWRITE_TAC[CX_DIV] THEN
      ASM_SIMP_TAC[CX_INJ; COMPLEX_NORM_ZERO; COMPLEX_FIELD
        `~(nu = Cx(&0)) ==> (w = nw / nu * u <=> nu * w = nw * u)`] THEN
      GEN_REWRITE_TAC (BINOP_CONV o RAND_CONV) [ARG] THEN
      ASM_REWRITE_TAC[COMPLEX_MUL_AC]];
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `Cx a + Cx b * z = complex(a + b * Re z,b * Im z)`
    SUBST1_TAC THENL
     [REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_ADD; IM_ADD; RE_CX; IM_CX;
                  RE_MUL_CX; IM_MUL_CX] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_EQ; IM; IM_CX] THEN
    SUBGOAL_THEN `&0 < Im z` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM ARG_LT_PI]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARG_ATAN_UPPERHALF; REAL_LT_MUL; REAL_LT_IMP_NZ; IM] THEN
    REWRITE_TAC[RE; REAL_SUB_LT; ATN_BOUNDS] THEN
    REWRITE_TAC[REAL_ARITH `pi / &2 - x < pi / &2 - y <=> y < x`] THEN
    REWRITE_TAC[ATN_MONO_LT_EQ] THEN
    ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_MUL] THEN
    ASM_SIMP_TAC[REAL_FIELD `&0 < z ==> w / z * b * z = b * w`] THEN
    ASM_REAL_ARITH_TAC]);;

let WEDGE_LUNE_GE = prove
 (`!v0 v1 w1 w2.
        ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2} /\
        &0 < azim v0 v1 w1 w2 /\ azim v0 v1 w1 w2 < pi
        ==> {x | &0 <= azim v0 v1 w1 x /\
                 azim v0 v1 w1 x <= azim v0 v1 w1 w2} =
            aff_ge {v0,v1} {w1,w2}`,
  REPEAT GEN_TAC THEN
  MAP_EVERY (fun t -> ASM_CASES_TAC t THENL
       [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC] THEN NO_TAC; ALL_TAC])
   [`v1:real^3 = v0`; `w1:real^3 = v0`; `w2:real^3 = v0`;
    `w1:real^3 = v1`; `w2:real^3 = v1`] THEN
  ASM_CASES_TAC `w1:real^3 = w2` THEN
  ASM_REWRITE_TAC[AZIM_REFL; REAL_LT_REFL] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[REAL_ARITH
   `&0 < a
    ==> (&0 <= x /\ x <= a <=> x = &0 \/ x = a \/ &0 < x /\ x < a)`] THEN
  MATCH_MP_TAC(SET_RULE
   `!c. c SUBSET {x | p x} /\ c SUBSET s /\
        ({x | ~(~c x ==> ~p x)} UNION {x | ~(~c x ==> ~q x)} UNION
         ({x | ~c x /\ r x} DIFF c) = s DIFF c)
        ==> {x | p x \/ q x \/ r x} = s`) THEN
  EXISTS_TAC `{x:real^3 | collinear {v0,v1,x}}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; AZIM_EQ_ALT; AZIM_EQ_0_ALT;
               GSYM wedge; WEDGE_LUNE_GT] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; AZIM_DEGENERATE];
    ASM_SIMP_TAC[COLLINEAR_3_AFFINE_HULL] THEN
    REWRITE_TAC[SET_RULE `{x | x IN s} = s`] THEN
    MATCH_MP_TAC AFFINE_HULL_SUBSET_AFF_GE THEN
    ASM_REWRITE_TAC[DISJOINT_INSERT; IN_INSERT; NOT_IN_EMPTY; DISJOINT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_IMP] THEN MATCH_MP_TAC(SET_RULE
   `(!x. ~c x ==> (p x \/ q x \/ x IN t <=> x IN e))
    ==> {x | ~c x /\ p x} UNION {x | ~c x /\ q x} UNION (t DIFF {x | c x}) =
        e DIFF {x | c x}`) THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o rand o
    rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[DISJOINT_INSERT; IN_INSERT; NOT_IN_EMPTY; DISJOINT_EMPTY];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
  ASM_SIMP_TAC[SET_RULE `~(w1 = w2) ==> {w1,w2} DELETE w1 = {w2}`;
               SET_RULE `~(w1 = w2) ==> {w1,w2} DELETE w2 = {w1}`] THEN
  REWRITE_TAC[IN_UNION; DISJ_ACI] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o rand o lhand o
    rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[DISJOINT_INSERT; IN_INSERT; NOT_IN_EMPTY; DISJOINT_EMPTY];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GE_AFF_GT_DECOMP o rand o lhand o
    rand o rand o snd) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[DISJOINT_INSERT; IN_INSERT; NOT_IN_EMPTY; DISJOINT_EMPTY];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[IN_UNION] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_1] THEN
  REWRITE_TAC[SET_RULE `{a} DELETE a = {}`; AFF_GE_EQ_AFFINE_HULL] THEN
  ASM_MESON_TAC[COLLINEAR_3_AFFINE_HULL]);;

let WEDGE_LUNE = prove
 (`!v0 v1 w1 w2.
        ~coplanar{v0,v1,w1,w2} /\ azim v0 v1 w1 w2 < pi
        ==> wedge v0 v1 w1 w2 = aff_gt {v0,v1} {w1,w2}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WEDGE_LUNE_GT THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w1:real^3`; `w2:real^3`]
                NOT_COPLANAR_NOT_COLLINEAR) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w2:real^3`; `w1:real^3`]
                NOT_COPLANAR_NOT_COLLINEAR) THEN
    ONCE_REWRITE_TAC[SET_RULE `{a,b,c,d} = {a,b,d,c}`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[azim; REAL_LT_LE] THEN
    ASM_MESON_TAC[AZIM_EQ_0_PI_IMP_COPLANAR]]);;

let WEDGE = prove
 (`wedge v1 v2 w1 w2 =
        if collinear{v1,v2,w1} \/ collinear{v1,v2,w2} then {}
        else
          let z = v2 - v1 in
          let u1 = w1 - v1 in
          let u2 = w2 - v1 in
          let n = z cross u1 in
          let d =  n dot u2 in
          if w2 IN (aff_ge {v1,v2} {w1}) then {}
          else if w2 IN (aff_lt {v1,v2} {w1}) then aff_gt {v1,v2,w1} {v1 + n}
          else if d > &0 then aff_gt {v1,v2} {w1,w2}
          else (:real^3) DIFF aff_ge {v1,v2} {w1,w2}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN
    ASM_SIMP_TAC[WEDGE_DEGENERATE];
    POP_ASSUM MP_TAC THEN REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC] THEN
  ASM_SIMP_TAC[GSYM AZIM_EQ_0_GE_ALT] THEN
  ASM_CASES_TAC `azim v1 v2 w1 w2 = &0` THENL
   [ASM_REWRITE_TAC[wedge] THEN
    ASM_REWRITE_TAC[REAL_LT_ANTISYM; LET_DEF; LET_END_DEF; EMPTY_GSPEC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM AZIM_EQ_PI_ALT] THEN
  ASM_CASES_TAC `azim v1 v2 w1 w2 = pi` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEOM_ORIGIN_TAC `v1:real^3` THEN
  REWRITE_TAC[VECTOR_ADD_RID; TRANSLATION_INVARIANTS `v1:real^3`] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; VECTOR_ADD_LID] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v2:real^3` THEN
  X_GEN_TAC `v2:real` THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  (STRIP_TAC THENL
    [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC]) THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE; REAL_LT_IMP_NZ;
               WEDGE_SPECIAL_SCALE] THEN
  (REPEAT GEN_TAC THEN
   MAP_EVERY (fun t -> ASM_CASES_TAC t THENL
        [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC] THEN NO_TAC; ALL_TAC])
    [`w1:real^3 = vec 0`; `w2:real^3 = vec 0`; `w1:real^3 = basis 3`;
     `w2:real^3 = basis 3`] THEN
   ASM_CASES_TAC `w1:real^3 = v2 % basis 3` THENL
    [ASM_REWRITE_TAC[COLLINEAR_LEMMA] THEN MESON_TAC[]; ALL_TAC] THEN
   ASM_CASES_TAC `w2:real^3 = v2 % basis 3` THENL
    [ASM_REWRITE_TAC[COLLINEAR_LEMMA] THEN MESON_TAC[]; ALL_TAC])
  THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `y:real^3` THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `(dropout 3 (y:real^3)) IN
      aff_gt {vec 0:real^2,dropout 3 (w1:real^3)}
              {rotate2d (pi / &2) (dropout 3 (w1:real^3))}` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE LAND_CONV [AZIM_ARG]) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE (RAND_CONV o LAND_CONV)
       [AZIM_ARG]) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV
        [COLLINEAR_BASIS_3])) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[wedge; IN_ELIM_THM; AZIM_ARG; COLLINEAR_BASIS_3] THEN
      SPEC_TAC(`(dropout 3:real^3->real^2) y`,`x:real^2`) THEN
      SPEC_TAC(`(dropout 3:real^3->real^2) w2`,`v2:real^2`) THEN
      SPEC_TAC(`(dropout 3:real^3->real^2) w1`,`v1:real^2`) THEN
      GEOM_BASIS_MULTIPLE_TAC 1 `v1:complex` THEN
      X_GEN_TAC `v:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
      ASM_CASES_TAC `v = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
      REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
      SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID] THEN
      REWRITE_TAC[real; RE_DIV_CX; IM_DIV_CX; CX_INJ] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_EQ_LDIV_EQ; REAL_MUL_LZERO] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[ARG_LT_PI; ROTATE2D_PI2] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_2_1 o rand o rand o snd) THEN
      ASM_REWRITE_TAC[DISJOINT_INSERT; DISJOINT_EMPTY; IN_SING] THEN
      ANTS_TAC THENL
       [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
        ASM_REWRITE_TAC[COMPLEX_ENTIRE; II_NZ; CX_INJ] THEN
        DISCH_THEN(MP_TAC o AP_TERM `Re`) THEN
        REWRITE_TAC[RE_MUL_II; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[COMPLEX_CMUL; IN_ELIM_THM; COMPLEX_MUL_RZERO] THEN
      ONCE_REWRITE_TAC[MESON[] `(?a b c. P a b c) <=> (?b c a. P a b c)`] THEN
      REWRITE_TAC[REAL_ARITH `t1 + t2 = &1 <=> t1 = &1 - t2`] THEN
      REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM2; COMPLEX_ADD_LID] THEN
      EQ_TAC THENL
       [DISCH_TAC THEN
        MAP_EVERY EXISTS_TAC [`Re x / v`; `Im x / v`] THEN
        ASM_SIMP_TAC[REAL_LT_DIV; COMPLEX_EQ; IM_ADD; RE_ADD] THEN
        REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_CX; IM_CX; RE_II; IM_II] THEN
        UNDISCH_TAC `~(v = &0)` THEN CONV_TAC REAL_FIELD;
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`s:real`; `t:real`] THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_EQ; IM_ADD; RE_ADD] THEN
        REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; RE_CX; IM_CX; RE_II; IM_II] THEN
        ASM_SIMP_TAC[REAL_MUL_RZERO; REAL_MUL_LID; REAL_LT_MUL; REAL_ADD_LID;
                     REAL_MUL_LZERO] THEN
        MAP_EVERY UNDISCH_TAC [`&0 < v`; `&0 < t`] THEN
        CONV_TAC REAL_FIELD];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_3_1 o rand o rand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE
       `DISJOINT {a,b,c} {x} <=> ~(x = a) /\ ~(x = b) /\ ~(x = c)`] THEN
      ASM_SIMP_TAC[CROSS_EQ_0; CROSS_EQ_SELF; VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ;
                   REAL_LT_IMP_NZ; BASIS_NONZERO; DIMINDEX_3;
                   ARITH; COLLINEAR_SPECIAL_SCALE];
      DISCH_THEN SUBST1_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_2_1 o rand o lhand o snd) THEN
    REWRITE_TAC[ROTATE2D_PI2] THEN ANTS_TAC THENL
     [REWRITE_TAC[SET_RULE `DISJOINT {a,b} {x} <=> ~(x = a) /\ ~(x = b)`] THEN
      REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_RING `ii * x = x <=> x = Cx(&0)`;
                  COMPLEX_VEC_0; II_NZ] THEN
      ASM_REWRITE_TAC[GSYM COMPLEX_VEC_0; GSYM COLLINEAR_BASIS_3];
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(?a b c d. P a b c d) <=> (?d c b a. P a b c d)`] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `s + t = &1 <=> s = &1 - t`] THEN
    REWRITE_TAC[UNWIND_THM2; RIGHT_EXISTS_AND_THM] THEN
    ONCE_REWRITE_TAC[MESON[] `(?a b c. P a b c) <=> (?c b a. P a b c)`] THEN
    REWRITE_TAC[UNWIND_THM2; RIGHT_EXISTS_AND_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    SIMP_TAC[CART_EQ; FORALL_2; FORALL_3; DIMINDEX_2; DIMINDEX_3;
      dropout; LAMBDA_BETA; BASIS_COMPONENT; ARITH; REAL_MUL_RID;
      VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RZERO; UNWIND_THM1;
      VECTOR_ADD_COMPONENT; cross; VECTOR_3;
      REWRITE_RULE[RE_DEF; IM_DEF] RE_MUL_II;
      REWRITE_RULE[RE_DEF; IM_DEF] IM_MUL_II;
      REAL_ADD_LID; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_ADD_RID;
      REAL_SUB_LZERO; REAL_SUB_RZERO] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `s:real` THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    ASM_SIMP_TAC[EXISTS_REFL; REAL_FIELD
     `&0 < v ==> (x = a * v + b <=> a = (x - b) / v)`] THEN
    REWRITE_TAC[REAL_MUL_RNEG; REAL_MUL_ASSOC] THEN EQ_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `t / v2:real`; EXISTS_TAC `t * v2:real`] THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_DIV; REAL_LT_IMP_NZ; REAL_LT_MUL];
    ALL_TAC] THEN
  REWRITE_TAC[CROSS_LMUL] THEN
  SIMP_TAC[cross; BASIS_COMPONENT; DIMINDEX_3; ARITH; DOT_3; VECTOR_3;
      VECTOR_MUL_COMPONENT; REAL_MUL_LZERO; REAL_SUB_RZERO; REAL_NEG_0;
           REAL_MUL_RZERO; REAL_SUB_LZERO; REAL_MUL_LID; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH
  `(v * --x2) * y1 + (v * x1) * y2 > &0 <=> &0 < v * (x1 * y2 - x2 * y1)`] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ; REAL_SUB_LT] THEN
  REWRITE_TAC[AZIM_ARG; COLLINEAR_BASIS_3] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `w1$2 * w2$1 < w1$1 * w2$2 <=>
    Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3)) < pi`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `&0 < Im(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IM_COMPLEX_DIV_GT_0] THEN
      REWRITE_TAC[complex_mul; cnj; RE_DEF; IM_DEF; complex] THEN
      SIMP_TAC[dropout; VECTOR_2; LAMBDA_BETA; DIMINDEX_3; ARITH;
               DIMINDEX_2] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[GSYM ARG_LT_PI] THEN ASM_MESON_TAC[ARG_LT_NZ]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SPECIAL_SCALE o rand o snd) THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC WEDGE_LUNE THEN
    ASM_SIMP_TAC[GSYM AZIM_EQ_0_PI_EQ_COPLANAR; COLLINEAR_BASIS_3] THEN
    ASM_REWRITE_TAC[AZIM_ARG];
    ALL_TAC] THEN
  REWRITE_TAC[wedge] THEN
  GEN_REWRITE_TAC (funpow 3 RAND_CONV) [SET_RULE `{a,b} = {b,a}`] THEN
  W(MP_TAC o PART_MATCH (rand o rand) WEDGE_LUNE_GE o rand o rand o snd) THEN
  ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE; REAL_LT_IMP_NZ; AZIM_SPECIAL_SCALE] THEN
  ASM_REWRITE_TAC[AZIM_ARG; COLLINEAR_BASIS_3] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARG_LT_NZ] THEN
    ONCE_REWRITE_TAC[GSYM ARG_INV_EQ_0] THEN
    ASM_REWRITE_TAC[COMPLEX_INV_DIV] THEN
    ONCE_REWRITE_TAC[GSYM COMPLEX_INV_DIV] THEN
    ASM_SIMP_TAC[ARG_INV; GSYM ARG_EQ_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIV; IN_ELIM_THM; ARG] THEN
  REWRITE_TAC[REAL_NOT_LE] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w1`,`w:complex`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w2`,`z:complex`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x3:real^3` THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) x3`,`x:complex`) THEN
  GEN_TAC THEN REWRITE_TAC[COMPLEX_VEC_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_VEC_0]) THEN
  ASM_CASES_TAC `x = Cx(&0)` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LZERO; REAL_NOT_LT; ARG; ARG_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ARG_LT_NZ] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(Arg (z / w) < pi)`;
    `~(Arg (z / w) = pi)`;
    `~(Arg (z / w) = &0)`;
    `~(x = Cx (&0))`;
    `~(w = Cx (&0))`;
    `~(z = Cx (&0))`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `w:complex` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
  SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID] THEN
  REWRITE_TAC[real; RE_DIV_CX; IM_DIV_CX; CX_INJ] THEN
  SIMP_TAC[complex_div; ARG_MUL_CX] THEN
  SIMP_TAC[ARG_INV; GSYM ARG_EQ_0; ARG_INV_EQ_0] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[GSYM complex_div] THEN
  ASM_CASES_TAC `Arg x = &0` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ARG_EQ_0]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[REAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[complex_div; CX_INJ] THEN
    ASM_SIMP_TAC[ARG_MUL_CX; REAL_LT_LE] THEN
    ASM_SIMP_TAC[ARG_INV; GSYM ARG_EQ_0];
    ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  SIMP_TAC[PI_POS; REAL_ARITH
   `&0 < pi ==> (~(z = &0) /\ ~(z = pi) /\ ~(z < pi) <=> pi < z)`] THEN
  STRIP_TAC THEN REWRITE_TAC[REAL_LT_SUB_RADD] THEN
  DISJ_CASES_TAC(REAL_ARITH `Arg z <= Arg x \/ Arg x < Arg z`) THENL
   [ASM_REWRITE_TAC[GSYM REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    ASM_SIMP_TAC[GSYM ARG_LE_DIV_SUM] THEN
    SIMP_TAC[ARG; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:complex`; `z:complex`] ARG_LE_DIV_SUM) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ ~(x = &0) /\ y = k - z ==> k < y + x + z`) THEN
  ASM_REWRITE_TAC[ARG] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM COMPLEX_INV_DIV] THEN
  MATCH_MP_TAC ARG_INV THEN REWRITE_TAC[REAL] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ABBREV_TAC `t = Re(z / x)` THEN UNDISCH_TAC `Arg x < Arg z` THEN
  UNDISCH_TAC `z / x = Cx t` THEN
  ASM_SIMP_TAC[COMPLEX_FIELD
   `~(x = Cx(&0)) ==> (z / x = t <=> z = t * x)`] THEN
  ASM_CASES_TAC `t = &0` THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
  ASM_SIMP_TAC[ARG_MUL_CX; REAL_LT_LE]);;

let OPEN_WEDGE = prove
 (`!z:real^3 w w1 w2. open(wedge z w w1 w2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `z:real^3 = w \/  collinear{z,w,w1} \/ collinear{z,w,w2}` THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    ASM_SIMP_TAC[WEDGE_DEGENERATE; OPEN_EMPTY];
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[DE_MORGAN_THM]] THEN
  REWRITE_TAC[wedge] THEN GEOM_ORIGIN_TAC `z:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))`] THEN
  ASM_SIMP_TAC[AZIM_ARG] THEN REWRITE_TAC[COLLINEAR_BASIS_3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; DROPOUT_0] THEN
  MATCH_MP_TAC OPEN_DROPOUT_3 THEN
  UNDISCH_TAC `~((dropout 3:real^3->real^2) w1 = vec 0)` THEN
  UNDISCH_TAC `~((dropout 3:real^3->real^2) w2 = vec 0)` THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w2`,`v2:complex`) THEN
  SPEC_TAC(`(dropout 3:real^3->real^2) w1`,`v1:complex`) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 `v1:complex` THEN
  X_GEN_TAC `v1:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `v1 = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
  SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `{x | ~(x = a) /\ P x} = {x | P x} DIFF {a}`] THEN
  MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[CLOSED_SING] THEN
  MATCH_MP_TAC OPEN_ARG_LTT THEN
  SIMP_TAC[REAL_LT_IMP_LE; REAL_LE_REFL; ARG]);;

let ARG_EQ_SUBSET_HALFLINE = prove
 (`!a. ?b. ~(b = vec 0) /\ {z | Arg z = a} SUBSET aff_ge {vec 0} {b}`,
  GEN_TAC THEN ASM_CASES_TAC `{z | Arg z = a} SUBSET {vec 0}` THENL
   [EXISTS_TAC `basis 1:real^2` THEN
    SIMP_TAC[BASIS_NONZERO; DIMINDEX_2; ARITH] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       SUBSET_TRANS)) THEN SIMP_TAC[SUBSET; IN_SING; ENDS_IN_HALFLINE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP (SET_RULE
   `~(s SUBSET {a}) ==> ?z. ~(a = z) /\ z IN s`)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:complex` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `x:complex` THEN
  ASM_CASES_TAC `x:complex = vec 0` THEN ASM_REWRITE_TAC[ENDS_IN_HALFLINE] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COMPLEX_VEC_0]) THEN ASM_SIMP_TAC[ARG_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM COMPLEX_CMUL] THEN
  REWRITE_TAC[HALFLINE_EXPLICIT; IN_ELIM_THM; VECTOR_MUL_RZERO] THEN
  MAP_EVERY EXISTS_TAC [`&1 - u`; `u:real`] THEN
  ASM_SIMP_TAC[VECTOR_ADD_LID; REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

let ARG_DIV_EQ_SUBSET_HALFLINE = prove
 (`!w a. ~(w = vec 0)
         ==> ?b. ~(b = vec 0) /\
                 {z | Arg(z / w) = a} SUBSET aff_ge {vec 0} {b}`,
  REPEAT GEN_TAC THEN GEOM_BASIS_MULTIPLE_TAC 1 `w:complex` THEN
  X_GEN_TAC `w:real` THEN ASM_CASES_TAC `w = &0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; REAL_LE_LT] THEN DISCH_TAC THEN
  X_GEN_TAC `a:real` THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[ARG_DIV_CX; COMPLEX_CMUL; COMPLEX_BASIS; GSYM CX_MUL;
               REAL_MUL_RID; ARG_EQ_SUBSET_HALFLINE]);;

let COPLANAR_AZIM_EQ = prove
 (`!v0 v1 w1 a.
     (collinear{v0,v1,w1} ==> ~(a = &0))
     ==> coplanar {z | azim v0 v1 w1 z = a}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `collinear{v0:real^3,v1,w1}` THENL
   [ASM_SIMP_TAC[azim_def; EMPTY_GSPEC; COPLANAR_EMPTY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  X_GEN_TAC `v1:real` THEN ASM_CASES_TAC `v1 = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LT; COLLINEAR_SPECIAL_SCALE] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; AZIM_ARG] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [COLLINEAR_BASIS_3]) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_THEN(X_CHOOSE_THEN `b:real^2`
   STRIP_ASSUME_TAC o SPEC `a:real` o MATCH_MP ARG_DIV_EQ_SUBSET_HALFLINE) THEN
  REWRITE_TAC[coplanar] THEN MAP_EVERY EXISTS_TAC
   [`vec 0:real^3`; `pushin 3 (&0) (b:real^2):real^3`; `basis 3:real^3`] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
  REWRITE_TAC[AFFINE_HULL_3; HALFLINE; SUBSET; IN_ELIM_THM] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
   MP_TAC(SPEC `(dropout 3:real^3->real^2) x` th)) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`&1 - v - (x:real^3)$3`; `v:real`; `(x:real^3)$3`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CART_EQ]) THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; DIMINDEX_3; FORALL_2; FORALL_3; LAMBDA_BETA;
           dropout; pushin; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; ARITH;
           BASIS_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Volume of a tetrahedron defined by conv0.                                 *)
(* ------------------------------------------------------------------------- *)

let delta_x = new_definition
 `delta_x x1 x2 x3 x4 x5 x6 =
        x1*x4*(--x1 + x2 + x3 -x4 + x5 + x6) +
        x2*x5*(x1 - x2 + x3 + x4 -x5 + x6) +
        x3*x6*(x1 + x2 - x3 + x4 + x5 - x6)
        -x2*x3*x4 - x1*x3*x5 - x1*x2*x6 -x4*x5*x6:real`;;

let VOLUME_OF_CLOSED_TETRAHEDRON = prove
 (`!x1 x2 x3 x4:real^3.
     measure(convex hull {x1,x2,x3,x4}) =
     sqrt(delta_x (dist(x1,x2) pow 2) (dist(x1,x3) pow 2) (dist(x1,x4) pow 2)
                  (dist(x3,x4) pow 2) (dist(x2,x4) pow 2) (dist(x2,x3) pow 2))
      / &12`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[MEASURE_TETRAHEDRON] THEN
  REWRITE_TAC[REAL_ARITH `x / &6 = y / &12 <=> y = &2 * x`] THEN
  MATCH_MP_TAC SQRT_UNIQUE THEN
  SIMP_TAC[REAL_LE_MUL; REAL_ABS_POS; REAL_POS] THEN
  REWRITE_TAC[REAL_POW_MUL; REAL_POW2_ABS; delta_x] THEN
  REWRITE_TAC[dist; NORM_POW_2] THEN
  SIMP_TAC[DOT_3; VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH] THEN
  CONV_TAC REAL_RING);;

let VOLUME_OF_TETRAHEDRON = prove
 (`!v1 v2 v3 v4:real^3.
        measure(conv0 {v1,v2,v3,v4}) =
            let x12 = dist(v1,v2) pow 2 in
            let x13 = dist(v1,v3) pow 2 in
            let x14 = dist(v1,v4) pow 2 in
            let x23 = dist(v2,v3) pow 2 in
            let x24 = dist(v2,v4) pow 2 in
            let x34 = dist(v3,v4) pow 2 in
            sqrt(delta_x x12 x13 x14 x34 x24 x23)/(&12)`,
  REPEAT GEN_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  ASM_SIMP_TAC[GSYM VOLUME_OF_CLOSED_TETRAHEDRON] THEN
  MATCH_MP_TAC MEASURE_CONV0_CONVEX_HULL THEN
  SIMP_TAC[DIMINDEX_3; FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Circle area. Should maybe extend WLOG tactics for such scaling.           *)
(* ------------------------------------------------------------------------- *)

let AREA_UNIT_CBALL = prove
 (`measure(cball(vec 0:real^2,&1)) = pi`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:1`,`:M`; `:2`,`:N`] FUBINI_SIMPLE_COMPACT) THEN
  EXISTS_TAC `1` THEN
  SIMP_TAC[DIMINDEX_1; DIMINDEX_2; ARITH; COMPACT_CBALL; SLICE_CBALL] THEN
  REWRITE_TAC[VEC_COMPONENT; DROPOUT_0; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MEASURE_EMPTY] THEN
  SUBGOAL_THEN `!t. abs(t) <= &1 <=> t IN real_interval[-- &1,&1]`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV; BALL_1] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. &2 * sqrt(&1 - t pow 2)` THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN SIMP_TAC[IN_REAL_INTERVAL; MEASURE_INTERVAL] THEN
    REWRITE_TAC[REAL_BOUNDS_LE; VECTOR_ADD_LID; VECTOR_SUB_LZERO] THEN
    DISCH_TAC THEN
    W(MP_TAC o PART_MATCH (lhs o rand) CONTENT_1 o rand o snd) THEN
    REWRITE_TAC[LIFT_DROP; DROP_NEG] THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[REAL_POW_ONE] THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> --x <= x`) THEN
    ASM_SIMP_TAC[SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
                 REAL_ABS_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x.  asn(x) + x * sqrt(&1 - x pow 2)`;
    `\x. &2 * sqrt(&1 - x pow 2)`;
    `-- &1`; `&1`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS_INTERIOR) THEN
  REWRITE_TAC[ASN_1; ASN_NEG_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[SQRT_0; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  REWRITE_TAC[REAL_ARITH `x / &2 - --(x / &2) = x`] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_CONTINUOUS_ON_ADD THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_ASN; IN_REAL_INTERVAL; REAL_BOUNDS_LE] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_MUL THEN
    REWRITE_TAC[REAL_CONTINUOUS_ON_ID] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[REAL_CONTINUOUS_ON_SUB; REAL_CONTINUOUS_ON_POW;
             REAL_CONTINUOUS_ON_ID; REAL_CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC REAL_CONTINUOUS_ON_SQRT THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_REAL_INTERVAL] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= &1 - x <=> x <= &1 pow 2`] THEN
    REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_ABS_NUM] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[IN_REAL_INTERVAL; REAL_BOUNDS_LT] THEN REPEAT STRIP_TAC THEN
    REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[REAL_MUL_LID; REAL_POW_1; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_RNEG; REAL_INV_MUL] THEN
    ASM_REWRITE_TAC[REAL_SUB_LT; ABS_SQUARE_LT_1] THEN
    MATCH_MP_TAC(REAL_FIELD
     `s pow 2 = &1 - x pow 2 /\ x pow 2 < &1
      ==> (inv s + x * --(&2 * x) * inv (&2) * inv s + s) = &2 * s`) THEN
    ASM_SIMP_TAC[ABS_SQUARE_LT_1; SQRT_POW_2; REAL_SUB_LE; REAL_LT_IMP_LE]]);;

let AREA_CBALL = prove
 (`!z:real^2 r. &0 <= r ==> measure(cball(z,r)) = pi * r pow 2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `r = &0` THENL
   [ASM_SIMP_TAC[CBALL_SING; REAL_POW_2; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC MEASURE_UNIQUE THEN
    REWRITE_TAC[HAS_MEASURE_0; NEGLIGIBLE_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `r:real`; `z:real^2`; `pi`]
        HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_CBALL;
              AREA_UNIT_CBALL] THEN
  ASM_REWRITE_TAC[real_abs; DIMINDEX_2] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [REAL_MUL_SYM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_CBALL_0; IN_IMAGE] THEN REWRITE_TAC[IN_CBALL] THEN
  REWRITE_TAC[NORM_ARITH `dist(z,a + z) = norm a`; NORM_MUL] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `abs r * x <= r <=> abs r * x <= r * &1`] THEN
  ASM_SIMP_TAC[real_abs; REAL_LE_LMUL; dist] THEN X_GEN_TAC `w:real^2` THEN
  DISCH_TAC THEN EXISTS_TAC `inv(r) % (w - z):real^2` THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV] THEN
  CONJ_TAC THENL [NORM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN ASM_REWRITE_TAC[real_abs] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
  ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]);;

let AREA_BALL = prove
 (`!z:real^2 r. &0 <= r ==> measure(ball(z,r)) = pi * r pow 2`,
  SIMP_TAC[GSYM INTERIOR_CBALL; GSYM AREA_CBALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
  SIMP_TAC[BOUNDED_CBALL; NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);;

(* ------------------------------------------------------------------------- *)
(* Volume of a ball.                                                         *)
(* ------------------------------------------------------------------------- *)

let VOLUME_CBALL = prove
 (`!z:real^3 r. &0 <= r ==> measure(cball(z,r)) = &4 / &3 * pi * r pow 3`,
  GEOM_ORIGIN_TAC `z:real^3` THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:2`,`:M`; `:3`,`:N`] FUBINI_SIMPLE_COMPACT) THEN
  EXISTS_TAC `1` THEN
  SIMP_TAC[DIMINDEX_2; DIMINDEX_3; ARITH; COMPACT_CBALL; SLICE_CBALL] THEN
  REWRITE_TAC[VEC_COMPONENT; DROPOUT_0; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MEASURE_EMPTY] THEN
  SUBGOAL_THEN `!t. abs(t) <= r <=> t IN real_interval[--r,r]`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. pi * (r pow 2 - t pow 2)` THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_BOUNDS_LE] THEN
    SIMP_TAC[AREA_CBALL; SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
             SQRT_POW_2; REAL_ARITH `abs x <= r ==> abs x <= abs r`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. pi * (r pow 2 * t - &1 / &3 * t pow 3)`;
    `\t. pi * (r pow 2 - t pow 2)`;
    `--r:real`; `r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RING]);;

let VOLUME_BALL = prove
 (`!z:real^3 r. &0 <= r ==> measure(ball(z,r)) =  &4 / &3 * pi * r pow 3`,
  SIMP_TAC[GSYM INTERIOR_CBALL; GSYM VOLUME_CBALL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_INTERIOR THEN
  SIMP_TAC[BOUNDED_CBALL; NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);;

(* ------------------------------------------------------------------------- *)
(* Frustum.                                                                  *)
(* ------------------------------------------------------------------------- *)

let rconesgn = new_definition
  `rconesgn sgn v w h =
       {x:real^A | sgn ((x-v) dot (w-v)) (dist(x,v)*dist(w,v)*h)}`;;

let rcone_gt = new_definition `rcone_gt = rconesgn ( > )`;;

let rcone_ge = new_definition `rcone_ge = rconesgn ( >= )`;;

let rcone_eq = new_definition `rcone_eq = rconesgn ( = )`;;

let frustum = new_definition
  `frustum v0 v1 h1 h2 a =
     { y:real^N | rcone_gt v0 v1 a y /\
                  let d = (y - v0) dot (v1 - v0) in
                  let n = norm(v1 - v0) in
                  (h1*n < d /\ d < h2*n)}`;;

let frustt = new_definition `frustt v0 v1 h a = frustum v0 v1 (&0) h a`;;

let FRUSTUM_DEGENERATE = prove
 (`!v0 h1 h2 a. frustum v0 v0 h1 h2 a = {}`,
  REWRITE_TAC[frustum; VECTOR_SUB_REFL; NORM_0; DOT_RZERO] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL] THEN SET_TAC[]);;

let CONVEX_RCONE_GT = prove
 (`!v0 v1:real^N a. &0 <= a ==> convex(rcone_gt v0 v1 a)`,
  REWRITE_TAC[rcone_gt; rconesgn] THEN
  GEOM_ORIGIN_TAC `v0:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
  REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM; real_gt; DOT_LADD; DOT_LMUL] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `t:real`] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&1 - t) * norm(x:real^N) * norm v1 * a +
              t * norm(y:real^N) * norm(v1:real^N) * a` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^N) = a /\ norm(y) = b ==> norm(x + y) <= a + b`) THEN
    REWRITE_TAC[NORM_MUL] THEN CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_CONVEX_BOUND2_LT THEN ASM_REAL_ARITH_TAC]);;

let OPEN_RCONE_GT = prove
 (`!v0 v1:real^N a. open(rcone_gt v0 v1 a)`,
  REWRITE_TAC[rcone_gt; rconesgn] THEN
  GEOM_ORIGIN_TAC `v0:real^N` THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
  MP_TAC(ISPECL [`\x:real^N. lift(x dot v1 - norm x * norm v1 * a)`;
                 `{x:real^1 | x$1 > &0}`]
        CONTINUOUS_OPEN_PREIMAGE_UNIV) THEN
  REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN REWRITE_TAC[GSYM drop] THEN
  REWRITE_TAC[IN_ELIM_THM; real_gt; REAL_SUB_LT; LIFT_DROP] THEN
  DISCH_THEN MATCH_MP_TAC THEN GEN_TAC THEN REWRITE_TAC[LIFT_SUB] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  MATCH_MP_TAC CONTINUOUS_SUB THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_DOT] THEN
  MATCH_MP_TAC CONTINUOUS_CMUL THEN
  REWRITE_TAC[REWRITE_RULE[o_DEF] CONTINUOUS_AT_LIFT_NORM]);;

let RCONE_GT_NEG = prove
 (`!v0 v1:real^N a.
        rcone_gt v0 v1 (--a) =
         IMAGE (\x. &2 % v0 - x) ((:real^N) DIFF rcone_ge v0 v1 a)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MESON_TAC[VECTOR_ARITH `a - (a - b):real^N = b`];
    REWRITE_TAC[rcone_gt; rconesgn; rcone_ge;
                IN_ELIM_THM; IN_DIFF; IN_UNIV] THEN
    REWRITE_TAC[NORM_ARITH `dist(&2 % x - y,x) = dist(y,x)`] THEN
    REWRITE_TAC[VECTOR_ARITH `&2 % v - x - v:real^N = --(x - v)`] THEN
    REWRITE_TAC[DOT_LNEG] THEN REAL_ARITH_TAC]);;

let VOLUME_FRUSTT_STRONG = prove
 (`!v0 v1:real^3 h a.
       &0 < a
       ==> bounded(frustt v0 v1 h a) /\
           convex(frustt v0 v1 h a) /\
           measurable(frustt v0 v1 h a) /\
           measure(frustt v0 v1 h a) =
           if v1 = v0 \/ &1 <= a \/ h < &0 then &0
           else pi * ((h / a) pow 2 - h pow 2) * h / &3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[frustt; frustum; rcone_gt; rconesgn; IN_ELIM_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN GEOM_ORIGIN_TAC `v0:real^3` THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; REAL_MUL_LZERO; DIST_0; real_gt] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `v1:real^3` THEN
  X_GEN_TAC `b:real` THEN REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `&0 <= x ==> x = &0 \/ &0 < x`)) THEN
  ASM_REWRITE_TAC[DOT_RZERO; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_LT_REFL;
    MEASURABLE_EMPTY; MEASURE_EMPTY; EMPTY_GSPEC; VECTOR_MUL_LZERO;
    BOUNDED_EMPTY; CONVEX_EMPTY] THEN
  ASM_CASES_TAC `&1 <= a` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `!y:real^3. ~(norm(y) * norm(b % basis 1:real^3) * a
                   < y dot (b % basis 1))`
     (fun th -> REWRITE_TAC[th; EMPTY_GSPEC; MEASURABLE_EMPTY;
       BOUNDED_EMPTY; CONVEX_EMPTY; MEASURE_EMPTY]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN X_GEN_TAC `y:real^3` THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    SIMP_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_MUL; DOT_BASIS; NORM_BASIS;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_ARITH
     `b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_ABS_POS; COMPONENT_LE_NORM; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DOT_BASIS; DOT_RMUL; DIMINDEX_3; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `n * x * a:real = x * n * a`] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_MUL_RID; REAL_LT_LMUL_EQ; REAL_LT_MUL_EQ; NORM_POS_LT] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH;
               REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_LT_SQUARE] THEN
  ASM_SIMP_TAC[REAL_POW_DIV; REAL_POW_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(&0 * x < y /\ u < v) /\ &0 < y /\ y < h <=>
                          &0 < y /\ y < h /\ u < v`] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^3,h / a)` THEN
    REWRITE_TAC[BOUNDED_BALL; IN_BALL_0; SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REWRITE_RULE[IMP_CONJ] REAL_LTE_TRANS)) THEN
    MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x /\ R x} =
                          {x | Q x} INTER {x | P x /\ R x}`] THEN
    REWRITE_TAC[REAL_ARITH `&0 < y <=> y > &0`] THEN
    MATCH_MP_TAC CONVEX_INTER THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_LT] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `basis 1:real^3`; `a:real`]
        CONVEX_RCONE_GT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; rcone_gt; rconesgn] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
    SIMP_TAC[DOT_BASIS; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[real_gt; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC[NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] FUBINI_SIMPLE_CONVEX_STRONG) THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[SLICE_312; DIMINDEX_2; DIMINDEX_3; ARITH; IN_ELIM_THM;
           VECTOR_3; DOT_3; GSYM DOT_2] THEN
  SUBGOAL_THEN `&0 < inv(a pow 2) - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
    ASM_SIMP_TAC[REAL_POW_1_LT; REAL_LT_IMP_LE; ARITH; REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. if &0 < t /\ t < h then pi * (inv(a pow 2) - &1) * t pow 2
                  else &0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; CONJ_ASSOC;
                    MEASURE_EMPTY; MEASURABLE_EMPTY] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `measure(ball(vec 0:real^2,sqrt(inv(a pow 2) - &1) * t))` THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (lhs o rand) AREA_BALL o rand o snd) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; SQRT_POS_LT; REAL_LT_MUL] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_MUL];
      AP_TERM_TAC THEN REWRITE_TAC[IN_BALL_0; EXTENSION; IN_ELIM_THM] THEN
      REWRITE_TAC[NORM_LT_SQUARE] THEN
      ASM_SIMP_TAC[SQRT_POS_LT; SQRT_POW_2; REAL_LT_IMP_LE; REAL_LT_MUL;
                   REAL_POW_MUL; GSYM REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[REAL_INTERVAL_EQ_EMPTY; HAS_REAL_INTEGRAL_EMPTY];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT])] THEN
  MP_TAC(ISPECL
   [`\t. pi / &3 * (inv (a pow 2) - &1) * t pow 3`;
    `\t. pi * (inv (a pow 2) - &1) * t pow 2`;
    `&0`; `h:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD]);;

let VOLUME_FRUSTT = prove
 (`!v0 v1:real^3 h a.
       &0 < a
       ==> measurable(frustt v0 v1 h a) /\
           measure(frustt v0 v1 h a) =
           if v1 = v0 \/ &1 <= a \/ h < &0 then &0
           else pi * ((h / a) pow 2 - h pow 2) * h / &3`,
  SIMP_TAC[VOLUME_FRUSTT_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Ellipsoid.                                                                *)
(* ------------------------------------------------------------------------- *)

let scale = new_definition
  `scale (t:real^3) (u:real^3):real^3 =
       vector[t$1 * u$1; t$2 * u$2; t$3 * u$3]`;;

let normball = new_definition `normball x r = { y:real^A | dist(y,x) < r}`;;

let ellipsoid = new_definition
  `ellipsoid t r = IMAGE (scale t) (normball(vec 0) r)`;;

let NORMBALL_BALL = prove
 (`!z r. normball z r = ball(z,r)`,
  REWRITE_TAC[normball; ball; DIST_SYM]);;

let MEASURE_SCALE = prove
 (`!s. measurable s
       ==> measurable(IMAGE (scale t) s) /\
           measure(IMAGE (scale t) s) = abs(t$1 * t$2 * t$3) * measure s`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURE] THEN
  DISCH_THEN(MP_TAC o SPEC `\i. (t:real^3)$i` o
    MATCH_MP HAS_MEASURE_STRETCH) THEN
  REWRITE_TAC[DIMINDEX_3; PRODUCT_3] THEN
  SUBGOAL_THEN `(\x:real^3. (lambda k. t$k * x$k):real^3) = scale t`
  SUBST1_TAC THENL
   [SIMP_TAC[CART_EQ; FUN_EQ_THM; scale; LAMBDA_BETA; DIMINDEX_3;
             VECTOR_3; ARITH; FORALL_3];
    MESON_TAC[measurable; MEASURE_UNIQUE]]);;

let MEASURE_ELLIPSOID = prove
 (`!t r. &0 <= r
         ==> measurable(ellipsoid t r) /\
             measure(ellipsoid t r) =
                abs(t$1 * t$2 * t$3) * &4 / &3 * pi * r pow 3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    SPEC `vec 0:real^3` o MATCH_MP VOLUME_BALL) THEN
  REWRITE_TAC[normball; ellipsoid] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
  REWRITE_TAC[GSYM ball] THEN MATCH_MP_TAC MEASURE_SCALE THEN
  REWRITE_TAC[MEASURABLE_BALL]);;

let MEASURABLE_ELLIPSOID = prove
 (`!t r. measurable(ellipsoid t r)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 <= r` THEN ASM_SIMP_TAC[MEASURE_ELLIPSOID] THEN
  REWRITE_TAC[ellipsoid; NORMBALL_BALL; IMAGE; IN_BALL_0] THEN
  ASM_SIMP_TAC[NORM_ARITH `~(&0 <= r) ==> ~(norm(x:real^3) < r)`] THEN
  REWRITE_TAC[EMPTY_GSPEC; MEASURABLE_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Conic cap.                                                                *)
(* ------------------------------------------------------------------------- *)

let conic_cap = new_definition
  `conic_cap v0 v1 r a = normball v0 r INTER rcone_gt v0 v1 a`;;

let CONIC_CAP_DEGENERATE = prove
 (`!v0 r a. conic_cap v0 v0 r a = {}`,
  REWRITE_TAC[conic_cap; rcone_gt; rconesgn; VECTOR_SUB_REFL] THEN
  REWRITE_TAC[DIST_REFL; DOT_RZERO; REAL_MUL_RZERO; REAL_MUL_LZERO] THEN
  REWRITE_TAC[real_gt; REAL_LT_REFL] THEN SET_TAC[]);;

let BOUNDED_CONIC_CAP = prove
 (`!v0 v1:real^3 r a. bounded(conic_cap v0 v1 r a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[conic_cap; NORMBALL_BALL] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(v0:real^3,r)` THEN
  REWRITE_TAC[BOUNDED_BALL] THEN SET_TAC[]);;

let MEASURABLE_CONIC_CAP = prove
 (`!v0 v1:real^3 r a. measurable(conic_cap v0 v1 r a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[conic_cap; NORMBALL_BALL] THEN
  MATCH_MP_TAC MEASURABLE_OPEN THEN
  SIMP_TAC[OPEN_INTER; OPEN_RCONE_GT; OPEN_BALL] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `ball(v0:real^3,r)` THEN
  REWRITE_TAC[BOUNDED_BALL] THEN SET_TAC[]);;

let VOLUME_CONIC_CAP_STRONG = prove
 (`!v0 v1:real^3 r a.
       &0 < a
       ==> bounded(conic_cap v0 v1 r a) /\
           convex(conic_cap v0 v1 r a) /\
           measurable(conic_cap v0 v1 r a) /\
           measure(conic_cap v0 v1 r a) =
             if v1 = v0 \/ &1 <= a \/ r < &0 then &0
             else &2 / &3 * pi * (&1 - a) * r pow 3`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[conic_cap; rcone_gt; rconesgn; IN_ELIM_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] normball; GSYM ball] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN GEOM_ORIGIN_TAC `v0:real^3` THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; REAL_MUL_LZERO; DIST_0; real_gt] THEN
  GEOM_BASIS_MULTIPLE_TAC 1 `v1:real^3` THEN
  X_GEN_TAC `b:real` THEN REPEAT(GEN_TAC ORELSE DISCH_TAC) THEN
  FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `&0 <= x ==> x = &0 \/ &0 < x`))
  THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; GSYM REAL_NOT_LE; DOT_RZERO] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; NORM_POS_LE] THEN
    REWRITE_TAC[EMPTY_GSPEC; INTER_EMPTY; MEASURE_EMPTY; MEASURABLE_EMPTY;
                CONVEX_EMPTY; BOUNDED_EMPTY];
    ALL_TAC] THEN
  ASM_CASES_TAC `&1 <= a` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `!y:real^3. ~(norm(y) * norm(b % basis 1:real^3) * a
                   < y dot (b % basis 1))`
     (fun th -> REWRITE_TAC[th; EMPTY_GSPEC; INTER_EMPTY; MEASURE_EMPTY;
                         MEASURABLE_EMPTY; BOUNDED_EMPTY; CONVEX_EMPTY]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN X_GEN_TAC `y:real^3` THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    SIMP_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_MUL; DOT_BASIS; NORM_BASIS;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_ARITH
     `b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_ABS_POS; COMPONENT_LE_NORM; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  SIMP_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_NORM; DOT_BASIS;
           DIMINDEX_3; ARITH; NORM_BASIS] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `n * x * a:real = x * n * a`] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_MUL_RID; REAL_LT_LMUL_EQ; REAL_LT_MUL_EQ; NORM_POS_LT] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_LT_SQUARE] THEN
  ASM_SIMP_TAC[REAL_POW_DIV; REAL_POW_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[INTER; REAL_MUL_LZERO; IN_BALL_0; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH;
               REAL_LT_IMP_NZ] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm x < r)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; MEASURE_EMPTY; MEASURABLE_EMPTY;
                BOUNDED_EMPTY; CONVEX_EMPTY];
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[REAL_NOT_LT])] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c /\ d) ==> a /\ b /\ c /\ d`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `ball(vec 0:real^3,r)` THEN
    SIMP_TAC[BOUNDED_BALL; IN_BALL_0; SUBSET; IN_ELIM_THM];
    ONCE_REWRITE_TAC[SET_RULE
      `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    MATCH_MP_TAC CONVEX_INTER THEN
    REWRITE_TAC[GSYM IN_BALL_0; CONVEX_BALL; SIMPLE_IMAGE; IMAGE_ID] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `basis 1:real^3`; `a:real`]
        CONVEX_RCONE_GT) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; rcone_gt; rconesgn] THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0] THEN
    SIMP_TAC[DOT_BASIS; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[real_gt; REAL_MUL_LID] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC[NORM_LT_SQUARE] THEN
    ASM_SIMP_TAC[REAL_POW_DIV; REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
    REWRITE_TAC[REAL_MUL_LZERO];
    STRIP_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] FUBINI_SIMPLE_CONVEX_STRONG) THEN
  EXISTS_TAC `1` THEN ASM_REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  SIMP_TAC[SLICE_312; DIMINDEX_2; DIMINDEX_3; ARITH; IN_ELIM_THM;
           VECTOR_3; DOT_3; GSYM DOT_2] THEN
  SUBGOAL_THEN `&0 < inv(a pow 2) - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
    ASM_SIMP_TAC[REAL_POW_1_LT; REAL_LT_IMP_LE; ARITH; REAL_POW_LT];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. if &0 < t /\ t < r
                  then measure
                    {y:real^2 | norm(vector[t; y$1; y$2]:real^3) pow 2
                                 < r pow 2 /\
                                (t * t + y dot y) * a pow 2 < t pow 2}
                  else &0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `&0 < t` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; MEASURE_EMPTY; MEASURABLE_EMPTY] THEN
    ASM_CASES_TAC `t:real < r` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[NORM_LT_SQUARE] THEN
      SUBGOAL_THEN `&0 < r` (fun th -> REWRITE_TAC[th; NORM_POW_2]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `!y. ~(norm(vector[t; (y:real^2)$1; y$2]:real^3) < r)`
     (fun th -> REWRITE_TAC[th; EMPTY_GSPEC; MEASURE_EMPTY;
                            MEASURABLE_EMPTY]) THEN
    ASM_REWRITE_TAC[NORM_LT_SQUARE; DOT_3; VECTOR_3] THEN
    GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= a /\ &0 <= b /\ c <= d
                             ==> ~(&0 < r /\ d + a + b < c)`) THEN
    REWRITE_TAC[REAL_LE_SQUARE] THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3; VECTOR_3; DOT_2] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `pi * &2 / &3 * (&1 - a) * r pow 3 =
    pi / &3 * (inv (a pow 2) - &1) * (a * r) pow 3 +
    (pi * &2 / &3 * (&1 - a) * r pow 3 -
     pi / &3 * (inv (a pow 2) - &1) * (a * r) pow 3)`] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN
  EXISTS_TAC `a * r:real` THEN
  REWRITE_TAC[REAL_ARITH `a * r <= r <=> &0 <= r * (&1 - a)`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
     `\t. measure(ball(vec 0:real^2,sqrt(inv(a pow 2) - &1) * t))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_BALL_0; NORM_LT_SQUARE_ALT] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; REAL_LE_MUL; SQRT_POW_2; REAL_LT_IMP_LE;
                   REAL_POW_MUL] THEN
      REWRITE_TAC[REAL_ARITH `x < (a - &1) * t <=> t + x < t * a`] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[DOT_2] THEN
      ASM_SIMP_TAC[GSYM REAL_POW_2; GSYM REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
      MATCH_MP_TAC(REAL_ARITH `b <= a ==> (x < b <=> x < a /\ x < b)`) THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; GSYM REAL_POW_MUL] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\t. pi * (inv(a pow 2) - &1) * t pow 2` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN
      W(MP_TAC o PART_MATCH (lhs o rand) AREA_BALL o rand o snd) THEN
      ASM_SIMP_TAC[REAL_POW_MUL; REAL_LT_IMP_LE; SQRT_POS_LT; REAL_LE_MUL;
                   SQRT_POW_2];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\t. pi / &3 * (inv (a pow 2) - &1) * t pow 3`;
      `\t. pi * (inv (a pow 2) - &1) * t pow 2`;
      `&0`; `a * r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
     `\t. measure(ball(vec 0:real^2,sqrt(r pow 2 - t pow 2)))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
      REWRITE_TAC[IN_BALL_0; NORM_LT_SQUARE_ALT] THEN
      SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * r:real` THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_SUB_LE; REAL_POW_LE2] THEN
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[DOT_2] THEN
      REWRITE_TAC[REAL_ARITH `x < r - t <=> t + x < r`] THEN
      ASM_SIMP_TAC[GSYM REAL_POW_2; GSYM REAL_LT_RDIV_EQ; REAL_POW_LT] THEN
      MATCH_MP_TAC(REAL_ARITH `a <= b ==> (x < a <=> x < a /\ x < b)`) THEN
      ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_POW_LT; GSYM REAL_POW_MUL] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[REAL_POW_LE2; REAL_LE_MUL; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
    EXISTS_TAC `\t. pi * (r pow 2 - t pow 2)` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN
      W(MP_TAC o PART_MATCH (lhs o rand) AREA_BALL o rand o snd) THEN
      SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * r:real` THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POS_LE; SQRT_POW_2; REAL_SUB_LE; REAL_POW_LE2];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\t. pi * (r pow 2 * t - t pow 3 / &3)`;
      `\t. pi * (r pow 2 - t pow 2)`;
      `a * r:real`; `r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_ARITH `a * r <= r <=> &0 <= r * (&1 - a)`] THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
      REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
      CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD]]);;

let VOLUME_CONIC_CAP = prove
 (`!v0 v1:real^3 r a.
       &0 < a
       ==> measurable(conic_cap v0 v1 r a) /\ measure(conic_cap v0 v1 r a) =
           if v1 = v0 \/ &1 <= a \/ r < &0 then &0
           else &2 / &3 * pi * (&1 - a) * r pow 3`,
  SIMP_TAC[VOLUME_CONIC_CAP_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Negligibility of a circular cone.                                         *)
(* This isn't exactly using the Flyspeck definition of "cone" but we use it  *)
(* to get that later on. Could now simplify this using WLOG tactics.         *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL = prove
 (`!c:real^N k. ~(c = vec 0) /\ ~(k = &0) /\ ~(k = pi)
                ==> negligible {x | vector_angle c x = k}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `(vec 0:real^N) INSERT
              UNIONS { {x | x IN ((:real^N) DIFF ball(vec 0,inv(&n + &1))) /\
                            Cx(vector_angle c x) = Cx k} |
                       n IN (:num)  }` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_INSERT; IN_UNIONS; IN_ELIM_THM; CX_INJ] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[IN_UNIV] THEN
    ASM_CASES_TAC `x:real^N = vec 0` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; IN_DIFF; IN_UNIV] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(SPEC `norm(x:real^N)` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[NORM_POS_LT; IN_BALL_0; REAL_NOT_LT; REAL_LT_INV_EQ] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&n)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[NEGLIGIBLE_INSERT] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_STRONG THEN EXISTS_TAC `c:real^N` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_CONSTANT THEN
    SIMP_TAC[CLOSED_DIFF; CLOSED_UNIV; OPEN_BALL] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_CX_VECTOR_ANGLE) THEN
    REWRITE_TAC[IN_DIFF; IN_BALL_0; NORM_0; IN_UNIV] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `x:real^N`] THEN
  SIMP_TAC[IN_ELIM_THM; IN_UNIV; IN_DIFF; IN_BALL_0; REAL_NOT_LT; CX_INJ] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN ASM_CASES_TAC `(c + x:real^N) = vec 0` THENL
   [ASM_REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_INV_EQ; NORM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `c + a % x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[GSYM REAL_NOT_LT; REAL_LT_INV_EQ; NORM_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `x:real^N = vec 0` THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_RID; VECTOR_ANGLE_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `a = &0` THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_ANGLE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[TAUT `~a \/ ~b <=> a ==> ~b`] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `c:real^N`; `c + a % x:real^N`;
                 `vec 0:real^N`; `c:real^N`; `c + x:real^N`]
                CONGRUENT_TRIANGLES_ASA_FULL) THEN
  REWRITE_TAC[angle; VECTOR_ADD_SUB] THEN ASM_SIMP_TAC[VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[NORM_ARITH `dist(x,x + a) = norm(a)`; NORM_MUL] THEN
  REWRITE_TAC[REAL_FIELD `a * x = x <=> a = &1 \/ x = &0`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= a /\ a < &1 ==> ~(abs a = &1)`] THEN
  ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_ANGLE_RMUL; COLLINEAR_LEMMA] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` MP_TAC) THEN
  DISCH_THEN(MP_TAC o AP_TERM `\x:real^N. inv(a) % x`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; VECTOR_ADD_LDISTRIB;
               VECTOR_MUL_LID; REAL_MUL_LINV] THEN
  REWRITE_TAC[VECTOR_ARITH `a % c + x = b % c <=> x = (b - a) % c`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[VECTOR_ARITH `c + a % c = (a + &1) % c`]) THEN
  UNDISCH_TAC `vector_angle c ((inv a * u - inv a + &1) % c:real^N) = k` THEN
  RULE_ASSUM_TAC(REWRITE_RULE
   [VECTOR_ANGLE_RMUL; VECTOR_MUL_EQ_0; DE_MORGAN_THM]) THEN
  ASM_REWRITE_TAC[VECTOR_ANGLE_RMUL; VECTOR_ANGLE_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let NEGLIGIBLE_CIRCULAR_CONE_0 = prove
 (`!c:real^N k. 2 <= dimindex(:N) /\ ~(c = vec 0)
                ==> negligible {x | vector_angle c x = k}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `orthogonal (basis 1:real^N) (basis 2)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[ORTHOGONAL_BASIS_BASIS; ARITH;
                 ARITH_RULE `2 <= d ==> 1 <= d`];
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &0 \/ k = pi` THENL
   [ALL_TAC; ASM_MESON_TAC[NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL]] THEN
  SUBGOAL_THEN
   `?b:real^N. ~(b = vec 0) /\
               ~(vector_angle c b = &0) /\
               ~(vector_angle c b = pi)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(MESON[] `!a b. P a \/ P b ==> ?x. P x`) THEN
    MAP_EVERY EXISTS_TAC [`basis 1:real^N`; `basis 2:real^N`] THEN
    REWRITE_TAC[BASIS_EQ_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= d ==> 1 <= d`; IN_NUMSEG; ARITH] THEN
    REWRITE_TAC[GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^N` o
      MATCH_MP VECTOR_ANGLE_EQ_0_LEFT)) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `basis 1:real^N` o
      MATCH_MP VECTOR_ANGLE_EQ_PI_LEFT)) THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[VECTOR_ANGLE_REFL; BASIS_EQ_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= d ==> 1 <= d`; IN_NUMSEG; ARITH] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [ORTHOGONAL_VECTOR_ANGLE]) THEN
    REWRITE_TAC[VECTOR_ANGLE_SYM] THEN MP_TAC PI_POS THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `k = &0 \/ k = pi` THENL
   [ALL_TAC; ASM_MESON_TAC[NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL]] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `{x:real^N | vector_angle b x = vector_angle c b}` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[VECTOR_ANGLE_EQ_0_RIGHT; VECTOR_ANGLE_SYM];
    EXISTS_TAC `{x:real^N | vector_angle b x = pi - vector_angle c b}` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_CIRCULAR_CONE_0_NONPARALLEL;
                 REAL_SUB_0; REAL_ARITH `p - x = p <=> x = &0`] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[VECTOR_ANGLE_EQ_PI_RIGHT; VECTOR_ANGLE_SYM]]);;

let NEGLIGIBLE_CIRCULAR_CONE = prove
 (`!a:real^N c k.
      2 <= dimindex(:N) /\ ~(c = vec 0)
      ==> negligible(a INSERT {x | vector_angle c (x - a) = k})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[NEGLIGIBLE_INSERT] THEN
  MATCH_MP_TAC NEGLIGIBLE_TRANSLATION_REV THEN EXISTS_TAC `--a:real^N` THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | vector_angle c x = k}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_CIRCULAR_CONE_0] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
  REWRITE_TAC[VECTOR_ARITH `--a + x:real^N = x - a`]);;

let NEGLIGIBLE_RCONE_EQ = prove
 (`!w z:real^3 h. ~(w = z) ==> negligible(rcone_eq z w h)`,
  REWRITE_TAC[rcone_eq; rconesgn] THEN GEOM_ORIGIN_TAC `z:real^3` THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIST_0; VECTOR_SUB_RZERO] THEN
  ASM_CASES_TAC `abs(h) <= &1` THENL
   [MP_TAC(ISPECL [`w:real^3`; `acs h`] NEGLIGIBLE_CIRCULAR_CONE_0) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
      HAS_MEASURE_NEGLIGIBLE_SYMDIFF) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{vec 0:real^3}` THEN
    REWRITE_TAC[NEGLIGIBLE_SING] THEN MATCH_MP_TAC(SET_RULE
     `(!x. ~(x = a) ==> (x IN s <=> x IN t))
      ==> (s DIFF t) UNION (t DIFF s) SUBSET {a}`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[vector_angle] THEN ASM_SIMP_TAC[NORM_EQ_0; REAL_FIELD
     `~(x = &0) /\ ~(w = &0) ==> (a = x * w * b <=> a / (w * x) = b)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [DOT_SYM] THEN
    MATCH_MP_TAC ACS_INJ THEN ASM_REWRITE_TAC[NORM_CAUCHY_SCHWARZ_DIV];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{vec 0}:real^3->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_SING] THEN
    REWRITE_TAC[SET_RULE `{x | P x} SUBSET {a} <=> !x. ~(x = a) ==> ~P x`] THEN
    X_GEN_TAC `x:real^3` THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^3`; `w:real^3`] NORM_CAUCHY_SCHWARZ_ABS) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM; REAL_ARITH
     `~(x * w * h <= x * w) <=> &0 < x * w * (h - &1)`] THEN
    REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[NORM_POS_LT]) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Area of sector of a circle delimited by Arg values.                       *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_ARG_EQ = prove
 (`!t. negligible {z | Arg z = t}`,
  GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{z | cexp(ii * Cx(pi / &2 + t)) dot z = &0}` THEN
  SIMP_TAC[NEGLIGIBLE_HYPERPLANE; COMPLEX_VEC_0; CEXP_NZ] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:complex` THEN
  DISCH_TAC THEN MP_TAC(SPEC `z:complex` ARG) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_CMUL; DOT_RMUL; REAL_ENTIRE] THEN
  DISJ2_TAC THEN REWRITE_TAC[CEXP_EULER] THEN
  REWRITE_TAC[DOT_2; GSYM RE_DEF; GSYM IM_DEF] THEN
  REWRITE_TAC[GSYM CX_SIN; GSYM CX_COS; RE_ADD; IM_ADD;
              RE_MUL_II; IM_MUL_II; RE_CX; IM_CX] THEN
  REWRITE_TAC[SIN_ADD; COS_ADD; SIN_PI2; COS_PI2] THEN
  REAL_ARITH_TAC);;

let MEASURABLE_CLOSED_SECTOR_LE = prove
 (`!r t. measurable {z | norm(z) <= r /\ Arg z <= t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
  REWRITE_TAC[SET_RULE `{z | P z /\ Q z} = {z | P z} INTER {z | Q z}`] THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED THEN REWRITE_TAC[CLOSED_ARG_LE] THEN
  REWRITE_TAC[NORM_ARITH `norm z = dist(vec 0,z)`; GSYM cball] THEN
  REWRITE_TAC[COMPACT_CBALL]);;

let MEASURABLE_CLOSED_SECTOR_LT = prove
 (`!r t. measurable {z | norm(z) <= r /\ Arg z < t}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_NEGLIGIBLE_SYMDIFF THEN
  EXISTS_TAC `{z | norm(z) <= r /\ Arg z <= t}` THEN
  REWRITE_TAC[MEASURABLE_CLOSED_SECTOR_LE] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{z | Arg z = t}` THEN
  REWRITE_TAC[NEGLIGIBLE_ARG_EQ; NEGLIGIBLE_UNION_EQ] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC);;

let MEASURABLE_CLOSED_SECTOR_LTE = prove
 (`!r s t. measurable {z | norm(z) <= r /\ s < Arg z /\ Arg z <= t}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
   `{z | P z /\ Q z /\ R z} = {z | P z /\ R z} DIFF {z | P z /\ ~Q z}`] THEN
  SIMP_TAC[MEASURABLE_DIFF; REAL_NOT_LT; MEASURABLE_CLOSED_SECTOR_LE]);;

let MEASURE_CLOSED_SECTOR_LE = prove
 (`!t r. &0 <= r /\ &0 <= t /\ t <= &2 * pi
         ==> measure {x:real^2 | norm(x) <= r /\ Arg(x) <= t} =
             t * r pow 2 / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\t. measure {z:real^2 | norm(z) <= r /\ Arg(z) <= t}`;
    `&2 * pi`] REAL_CONTINUOUS_ADDITIVE_IMP_LINEAR_INTERVAL) THEN
  ANTS_TAC THENL
   [ALL_TAC;
    DISCH_THEN(MP_TAC o SPECL [`t / (&2 * pi)`; `&2 * pi`]) THEN
    MP_TAC(SPECL [`vec 0:real^2`; `r:real`] AREA_CBALL) THEN
    ASM_REWRITE_TAC[cball; NORM_ARITH `dist(vec 0,z) = norm z`] THEN
    SIMP_TAC[ARG; REAL_LT_IMP_LE] THEN DISCH_THEN(K ALL_TAC) THEN
    SIMP_TAC[PI_POS; REAL_FIELD `&0 < p ==> t / (&2 * p) * p * r = t * r / &2`;
             REAL_FIELD `&0 < p ==> t / (&2 * p) * &2 * p = t`] THEN
    DISCH_THEN MATCH_MP_TAC THEN MP_TAC PI_POS THEN ASM_REAL_ARITH_TAC] THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC REALLIM_TRANSFORM_BOUND THEN
    EXISTS_TAC `\t. r pow 2 * sin(t)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[EVENTUALLY_WITHINREAL] THEN EXISTS_TAC `pi / &2` THEN
      SIMP_TAC[PI_POS; REAL_LT_DIV; IN_ELIM_THM; REAL_OF_NUM_LT; ARITH] THEN
      X_GEN_TAC `x:real` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      ASM_SIMP_TAC[real_abs; MEASURE_POS_LE; MEASURABLE_CLOSED_SECTOR_LE] THEN
      STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(interval[vec 0,complex(r,r * sin x)])` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_SUBSET THEN
        REWRITE_TAC[MEASURABLE_CLOSED_SECTOR_LE; MEASURABLE_INTERVAL] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL] THEN
        X_GEN_TAC `z:complex` THEN STRIP_TAC THEN
        REWRITE_TAC[DIMINDEX_2; FORALL_2; VEC_COMPONENT] THEN
        REWRITE_TAC[GSYM IM_DEF; GSYM RE_DEF; IM; RE] THEN
        SUBST1_TAC(last(CONJUNCTS(SPEC `z:complex` ARG))) THEN
        REWRITE_TAC[RE_MUL_CX; IM_MUL_CX; CEXP_EULER] THEN
        REWRITE_TAC[RE_ADD; GSYM CX_COS; GSYM CX_SIN; RE_CX; IM_CX;
                    RE_MUL_II; IM_MUL_II; IM_ADD] THEN
        REWRITE_TAC[REAL_NEG_0; REAL_ADD_LID; REAL_ADD_RID] THEN
        SUBGOAL_THEN `&0 <= Arg z /\ Arg z < pi / &2 /\ Arg z <= pi / &2`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[ARG] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
          MATCH_MP_TAC COS_POS_PI_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC(REAL_ARITH `abs(a * b) <= c * &1 ==> a * b <= c`) THEN
          REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NORM] THEN
          MATCH_MP_TAC REAL_LE_MUL2 THEN
          ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS; COS_BOUND];
          MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[NORM_POS_LE] THEN
          MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC;
            MATCH_MP_TAC SIN_MONO_LE THEN ASM_REAL_ARITH_TAC]];
        REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
        REWRITE_TAC[FORALL_2; PRODUCT_2; DIMINDEX_2; VEC_COMPONENT] THEN
        REWRITE_TAC[GSYM IM_DEF; GSYM RE_DEF; IM; RE] THEN
        REWRITE_TAC[REAL_SUB_RZERO; REAL_POW_2; REAL_MUL_ASSOC] THEN
        SUBGOAL_THEN `&0 <= sin x` (fun th ->
          ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_REFL; REAL_LE_MUL; th]) THEN
        MATCH_MP_TAC SIN_POS_PI_LE THEN ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC REALLIM_ATREAL_WITHINREAL THEN
      SUBGOAL_THEN `(\t. r pow 2 * sin t) real_continuous atreal (&0)`
      MP_TAC THENL
       [MATCH_MP_TAC REAL_CONTINUOUS_LMUL THEN
        REWRITE_TAC[ETA_AX; REAL_CONTINUOUS_AT_SIN];
        REWRITE_TAC[REAL_CONTINUOUS_ATREAL; SIN_0; REAL_MUL_RZERO]]];
    ASM_SIMP_TAC[REAL_ARITH
      `&0 <= x /\ &0 <= y
       ==> (norm z <= r /\ Arg z <= x + y <=>
            norm z <= r /\ Arg z <= x \/
            norm z <= r /\ x < Arg z /\ Arg z <= x + y)`] THEN
    REWRITE_TAC[SET_RULE `{z | Q z \/ R z} = {z | Q z} UNION {z | R z}`] THEN
    SIMP_TAC[MEASURE_UNION; MEASURABLE_CLOSED_SECTOR_LE;
             MEASURABLE_CLOSED_SECTOR_LTE] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE; SET_RULE
     `{z | P z /\ Q z} INTER {z | P z /\ ~Q z /\ R z} = {}`] THEN
    REWRITE_TAC[MEASURE_EMPTY; REAL_SUB_RZERO; REAL_EQ_ADD_LCANCEL] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `measure {z | norm z <= r /\ x < Arg z /\ Arg z < x + y}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
      REWRITE_TAC[MEASURABLE_CLOSED_SECTOR_LTE] THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{z | Arg z = x + y}` THEN
      REWRITE_TAC[NEGLIGIBLE_ARG_EQ; NEGLIGIBLE_UNION_EQ] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `measure {z | norm z <= r /\ &0 < Arg z /\ Arg z < y}` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
      REWRITE_TAC[MEASURABLE_CLOSED_SECTOR_LE] THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{z | Arg z = &0} UNION {z | Arg z = y}` THEN
      REWRITE_TAC[NEGLIGIBLE_ARG_EQ; NEGLIGIBLE_UNION_EQ] THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
      MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `measure (IMAGE (rotate2d x)
              {z | norm z <= r /\ &0 < Arg z /\ Arg z < y})` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[MEASURE_ORTHOGONAL_IMAGE_EQ;
                   ORTHOGONAL_TRANSFORMATION_ROTATE2D]] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
     [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE;
                    ORTHOGONAL_TRANSFORMATION_ROTATE2D]; ALL_TAC] THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `z = Cx(&0)` THENL
     [ASM_REWRITE_TAC[Arg_DEF; ROTATE2D_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[NORM_ROTATE2D] THEN AP_TERM_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `z = rotate2d (--x) (rotate2d x z)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM ROTATE2D_ADD; REAL_ADD_LINV; ROTATE2D_ZERO];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`--x:real`; `rotate2d x z`] ARG_ROTATE2D) THEN
      ASM_REWRITE_TAC[ROTATE2D_EQ_0] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC;
      STRIP_TAC THEN
      MP_TAC(ISPECL [`x:real`; `z:complex`] ARG_ROTATE2D) THEN
      ASM_REWRITE_TAC[ROTATE2D_EQ_0] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
      ASM_REAL_ARITH_TAC]]);;

let HAS_MEASURE_OPEN_SECTOR_LT = prove
 (`!t r. &0 <= t /\ t <= &2 * pi
         ==> {x:real^2 | norm(x) < r /\ &0 < Arg x /\ Arg x < t}
             has_measure (if &0 <= r then t * r pow 2 / &2 else &0)`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_SIMP_TAC[NORM_ARITH `~(&0 <= r) ==> ~(norm x < r)`;
               EMPTY_GSPEC; HAS_MEASURE_EMPTY] THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_SYMDIFF THEN
  EXISTS_TAC `{x | norm x <= r /\ Arg x <= t}` THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
  ASM_SIMP_TAC[MEASURE_CLOSED_SECTOR_LE; MEASURABLE_CLOSED_SECTOR_LE] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x | dist(vec 0,x) = r} UNION
              {z | Arg z = &0} UNION {z | Arg z = t}` THEN
  REWRITE_TAC[NEGLIGIBLE_ARG_EQ; REWRITE_RULE[sphere] NEGLIGIBLE_SPHERE;
              NEGLIGIBLE_UNION_EQ] THEN
  REWRITE_TAC[DIST_0; SUBSET; IN_DIFF; IN_UNION; IN_ELIM_THM] THEN
      MP_TAC ARG THEN MATCH_MP_TAC MONO_FORALL THEN REAL_ARITH_TAC);;

let MEASURE_OPEN_SECTOR_LT = prove
 (`!t r. &0 <= t /\ t <= &2 * pi
         ==> measure {x:real^2 | norm(x) < r /\ &0 < Arg x /\ Arg x < t} =
             if &0 <= r then t * r pow 2 / &2 else &0`,
  SIMP_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
           HAS_MEASURE_OPEN_SECTOR_LT]);;

let HAS_MEASURE_OPEN_SECTOR_LT_GEN = prove
 (`!w z.
        ~(w = vec 0)
        ==> {x | norm(x) < r /\ &0 < Arg(x / w) /\ Arg(x / w) < Arg(z / w)}
            has_measure (if &0 <= r then Arg(z / w) * r pow 2 / &2 else &0)`,
  GEOM_BASIS_MULTIPLE_TAC 1 `w:complex` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
  SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID] THEN ASM_REWRITE_TAC[CX_INJ] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_OPEN_SECTOR_LT THEN
  SIMP_TAC[ARG; REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Hence volume of a wedge of a ball.                                        *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_BALL_WEDGE = prove
 (`!z:real^3 w w1 w2. measurable(ball(z,r) INTER wedge z w w1 w2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_OPEN THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_INTER THEN REWRITE_TAC[BOUNDED_BALL];
    MATCH_MP_TAC OPEN_INTER THEN REWRITE_TAC[OPEN_BALL] THEN
    ASM_SIMP_TAC[OPEN_WEDGE]]);;

let VOLUME_BALL_WEDGE = prove
 (`!z:real^3 w r w1 w2.
        &0 <= r ==> measure(ball(z,r) INTER wedge z w w1 w2) =
                       azim z w w1 w2 * &2 * r pow 3 / &3`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `z:real^3 = w \/  collinear{z,w,w1} \/ collinear{z,w,w2}` THENL
   [FIRST_X_ASSUM STRIP_ASSUME_TAC THEN
    ASM_SIMP_TAC[WEDGE_DEGENERATE; AZIM_DEGENERATE; INTER_EMPTY; REAL_MUL_LZERO;
                 MEASURE_EMPTY];
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP; DE_MORGAN_THM]] THEN
  REWRITE_TAC[wedge] THEN GEOM_ORIGIN_TAC `z:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; COLLINEAR_SPECIAL_SCALE] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE[`:2`,`:M`; `:3`,`:N`] FUBINI_SIMPLE_OPEN) THEN
  EXISTS_TAC `3` THEN REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  REPEAT CONJ_TAC THENL
   [MESON_TAC[BOUNDED_SUBSET; INTER_SUBSET; BOUNDED_BALL];
    REWRITE_TAC[GSYM wedge] THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_REWRITE_TAC[OPEN_BALL; OPEN_WEDGE];
    SIMP_TAC[SLICE_INTER; DIMINDEX_2; DIMINDEX_3; ARITH; SLICE_BALL]] THEN
  ONCE_REWRITE_TAC[TAUT `~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))`] THEN
  ASM_SIMP_TAC[AZIM_ARG] THEN REWRITE_TAC[COLLINEAR_BASIS_3] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; DROPOUT_0] THEN
  MAP_EVERY ABBREV_TAC
   [`v1:real^2 = dropout 3 (w1:real^3)`;
    `v2:real^2 = dropout 3 (w2:real^3)`] THEN
  REWRITE_TAC[SLICE_DROPOUT_3; VEC_COMPONENT; REAL_SUB_RZERO] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[INTER_EMPTY] THEN REWRITE_TAC[INTER; IN_BALL_0; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[MEASURE_EMPTY] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(v1:complex = vec 0)`; `~(v2:complex = vec 0)`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`v2:complex`; `v1:complex`] THEN
  UNDISCH_TAC `&0 <= r` THEN SPEC_TAC(`r:real`,`r:real`) THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN GEOM_BASIS_MULTIPLE_TAC 1 `v1:complex` THEN
  X_GEN_TAC `v1:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `v1 = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  REWRITE_TAC[COMPLEX_CMUL; COMPLEX_BASIS; COMPLEX_VEC_0] THEN
  SIMP_TAC[ARG_DIV_CX; COMPLEX_MUL_RID; CX_INJ] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!t z. ~(z = Cx(&0)) /\ &0 < Arg z /\ Arg z < t <=>
          &0 < Arg z /\ Arg z < t`
   (fun th -> REWRITE_TAC[th])
  THENL [MESON_TAC[ARG_0; REAL_LT_REFL]; ALL_TAC] THEN
  ASM_SIMP_TAC[MEASURE_OPEN_SECTOR_LT; REAL_LE_REFL; ARG; REAL_LT_IMP_LE] THEN
  SUBGOAL_THEN `!t. abs(t) < r <=> t IN real_interval(--r,r)`
   (fun th -> REWRITE_TAC[th])
  THENL [REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC `\t. Arg v2 * (r pow 2 - t pow 2) / &2` THEN CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL; REAL_BOUNDS_LE] THEN
    SIMP_TAC[AREA_CBALL; SQRT_POS_LE; REAL_SUB_LE; GSYM REAL_LE_SQUARE_ABS;
             SQRT_POW_2; REAL_ARITH `abs x <= r ==> abs x <= abs r`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t. Arg v2 * (r pow 2 * t - &1 / &3 * t pow 3) / &2`;
    `\t. Arg v2 * (r pow 2 - t pow 2) / &2`;
    `--r:real`; `r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    CONV_TAC REAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Hence volume of lune.                                                     *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_LUNE = prove
 (`!z:real^3 w r w1 w2.
        &0 <= r /\ ~(w = z) /\
        ~collinear {z,w,w1} /\ ~collinear {z,w,w2} /\ ~(dihV z w w1 w2 = pi)
        ==> (ball(z,r) INTER aff_gt {z,w} {w1,w2})
            has_measure (dihV z w w1 w2 * &2 * r pow 3 / &3)`,
  GEOM_ORIGIN_TAC `z:real^3` THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `w:real^3` THEN
  X_GEN_TAC `w:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `w = &0` THEN ASM_REWRITE_TAC[] THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_LZERO; INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[DIHV_SPECIAL_SCALE] THEN
  MP_TAC(ISPECL [`{}:real^3->bool`; `{w1:real^3,w2:real^3}`;
                 `w:real`; `basis 3:real^3`] AFF_GT_SPECIAL_SCALE) THEN
  ASM_CASES_TAC `w1:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `w2:real^3 = vec 0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_CASES_TAC `w1:real^3 = w % basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `w2:real^3 = w % basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE] THEN
  ASM_CASES_TAC `w1:real^3 = basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_CASES_TAC `w2:real^3 = basis 3` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
  ASM_CASES_TAC `azim (vec 0) (basis 3) w1 w2 = &0` THENL
   [MP_TAC(ASSUME `azim (vec 0) (basis 3) w1 w2 = &0`) THEN
    W(MP_TAC o PART_MATCH (lhs o rand) AZIM_DIVH o lhs o lhand o snd) THEN
    ASM_REWRITE_TAC[PI_POS] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[REAL_MUL_LZERO; HAS_MEASURE_0] THEN
    MATCH_MP_TAC COPLANAR_IMP_NEGLIGIBLE THEN
    MATCH_MP_TAC COPLANAR_SUBSET THEN
    EXISTS_TAC `affine hull {vec 0:real^3,basis 3,w1,w2}` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[COPLANAR_AFFINE_HULL_COPLANAR; AZIM_EQ_0_PI_IMP_COPLANAR];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `t SUBSET u ==> (s INTER t) SUBSET u`) THEN
    SIMP_TAC[aff_gt_def; AFFSIGN; sgn_gt; AFFINE_HULL_FINITE;
             FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[SET_RULE `{a,b} UNION {c,d} = {a,b,c,d}`] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < azim (vec 0) (basis 3) w1 w2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_LE; azim]; ALL_TAC] THEN
  ASM_CASES_TAC `azim (vec 0) (basis 3) w1 w2 < pi` THENL
   [ASM_SIMP_TAC[GSYM AZIM_DIHV_SAME; GSYM WEDGE_LUNE_GT] THEN
    ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL_WEDGE;
                 VOLUME_BALL_WEDGE];
    ALL_TAC] THEN
  ASM_CASES_TAC `azim (vec 0) (basis 3) w1 w2 = pi` THENL
   [MP_TAC(ISPECL [`vec 0:real^3`; `basis 3:real^3`; `w1:real^3`; `w2:real^3`]
           AZIM_DIVH) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dihV (vec 0) (basis 3) w1 w2 = azim (vec 0) (basis 3) w2 w1`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC[REAL_ARITH `x:real = y - z <=> z = y - x`] THEN
    MATCH_MP_TAC AZIM_DIHV_COMPL THEN
    ASM_REWRITE_TAC[GSYM REAL_NOT_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < azim (vec 0) (basis 3) w2 w1 /\
                azim (vec 0) (basis 3) w2 w1 < pi`
  ASSUME_TAC THENL
   [W(MP_TAC o PART_MATCH (lhs o rand) AZIM_COMPL o lhand o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `basis 3:real^3`; `w1:real^3`; `w2:real^3`]
        azim) THEN
    REWRITE_TAC[CONJ_ASSOC] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBST1_TAC(SET_RULE `{w1:real^3,w2} = {w2,w1}`) THEN
  ASM_SIMP_TAC[GSYM AZIM_DIHV_SAME; GSYM WEDGE_LUNE_GT] THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_BALL_WEDGE;
               VOLUME_BALL_WEDGE]);;

let HAS_MEASURE_LUNE_SIMPLE = prove
 (`!z:real^3 w r w1 w2.
        &0 <= r /\ ~coplanar{z,w,w1,w2}
        ==> (ball(z,r) INTER aff_gt {z,w} {w1,w2})
            has_measure (dihV z w w1 w2 * &2 * r pow 3 / &3)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `w:real^3 = z` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COPLANAR_3]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_LUNE THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT(CONJ_TAC THENL
   [ASM_MESON_TAC[NOT_COPLANAR_NOT_COLLINEAR; INSERT_AC]; ALL_TAC]) THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`z:real^3`; `w:real^3`; `w1:real^3`; `w2:real^3`]
        AZIM_DIVH) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&2 * pi - pi = pi`; COND_ID] THEN
  ASM_MESON_TAC[AZIM_EQ_0_PI_IMP_COPLANAR]);;

(* ------------------------------------------------------------------------- *)
(* Now the volume of a solid triangle.                                       *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_BALL_AFF_GT = prove
 (`!z r s t. measurable(ball(z,r) INTER aff_gt s t)`,
  MESON_TAC[MEASURABLE_CONVEX; CONVEX_INTER; CONVEX_AFF_GT; CONVEX_BALL;
            BOUNDED_INTER; BOUNDED_BALL]);;

let AFF_GT_SHUFFLE = prove
 (`!s t v:real^N.
        FINITE s /\ FINITE t /\
        vec 0 IN s /\ ~(vec 0 IN t) /\
        ~(v IN s) /\ ~(--v IN s) /\ ~(v IN t)
        ==> aff_gt (v INSERT s) t =
            aff_gt s (v INSERT t) UNION
            aff_gt s (--v INSERT t) UNION
            aff_gt s t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[aff_gt_def; AFFSIGN_ALT; sgn_gt] THEN
  REWRITE_TAC[SET_RULE `(v INSERT s) UNION t = v INSERT (s UNION t)`;
              SET_RULE `s UNION (v INSERT t) = v INSERT (s UNION t)`] THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
               RIGHT_EXISTS_AND_THM; REAL_LT_ADD; REAL_HALF; FINITE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN
  ASM_SIMP_TAC[SET_RULE
   `~(a IN s)
    ==> ((w IN s UNION t ==> w = a \/ w IN t ==> P w) <=>
         (w IN t ==> P w))`] THEN
  REWRITE_TAC[SET_RULE `x IN (s UNION t)
                        ==> x IN t ==> P x <=> x IN t ==> P  x`] THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `v:real` ASSUME_TAC) THEN
    ASM_CASES_TAC `&0 < v` THENL
     [DISJ1_TAC THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC] THEN
    ASM_CASES_TAC `v = &0` THENL
     [DISJ2_TAC THEN
      FIRST_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO; VECTOR_MUL_LZERO; VECTOR_SUB_RZERO];
      DISJ1_TAC] THEN
    EXISTS_TAC `--v:real` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `\x:real^N. if x = vec 0 then f(x) + &2 * v else f(x)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_SIMP_TAC[SUM_CASES_1; FINITE_UNION; IN_UNION] THEN REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH `--a % --x:real^N = a % x`] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
      MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[VECTOR_MUL_RZERO]];
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL
     [DISCH_THEN(X_CHOOSE_THEN `a:real`
       (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `--a:real` THEN
      EXISTS_TAC `\x:real^N. if x = vec 0 then &2 * a + f(vec 0) else f x` THEN
      ASM_SIMP_TAC[SUM_CASES_1; FINITE_UNION; IN_UNION] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `y - --a % v:real^N = y - a % --v`] THEN
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC VSUM_EQ THEN REPEAT GEN_TAC THEN REWRITE_TAC[] THEN
      DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_RZERO];
      GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN
      EXISTS_TAC `&0` THEN ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN
      VECTOR_ARITH_TAC]]);;

let MEASURE_BALL_AFF_GT_SHUFFLE_LEMMA = prove
 (`!r s t v:real^N.
        &0 <= r /\
        independent(v INSERT((s DELETE vec 0) UNION t)) /\
        FINITE s /\ FINITE t /\ CARD(s UNION t) <= dimindex(:N) /\
        vec 0 IN s /\ ~(vec 0 IN t) /\
        ~(v IN s) /\ ~(--v IN s) /\ ~(v IN t)
        ==> measure(ball(vec 0,r) INTER aff_gt (v INSERT s) t) =
            measure(ball(vec 0,r) INTER aff_gt s (v INSERT t)) +
            measure(ball(vec 0,r) INTER aff_gt s (--v INSERT t))`,
  let lemma = prove
   (`!s t u:real^N->bool.
          measurable s /\ measurable t /\ s INTER t = {} /\ negligible u
          ==> measure(s UNION t UNION u) = measure s + measure t`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[UNION_ASSOC] THEN
    ASM_SIMP_TAC[GSYM MEASURE_DISJOINT_UNION; DISJOINT] THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    ASM_SIMP_TAC[MEASURABLE_UNION] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] NEGLIGIBLE_SUBSET)) THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhs o rand) AFF_GT_SHUFFLE o
    rand o rand o lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[UNION_OVER_INTER] THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[MEASURABLE_BALL_AFF_GT] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `t INTER u = {} ==> (s INTER t) INTER (s INTER u) = {}`) THEN
    REWRITE_TAC[aff_gt_def; AFFSIGN_ALT; sgn_gt] THEN
    REWRITE_TAC[SET_RULE `(v INSERT s) UNION t = v INSERT (s UNION t)`;
                SET_RULE `s UNION (v INSERT t) = v INSERT (s UNION t)`] THEN
    ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
                 RIGHT_EXISTS_AND_THM; REAL_LT_ADD;
                 REAL_HALF; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_INSERT] THEN
    ASM_SIMP_TAC[SET_RULE
     `~(a IN s) ==> ((w IN s UNION t ==> w = a \/ w IN t ==> P w) <=>
                     (w IN t ==> P w))`] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTER; NOT_IN_EMPTY; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `a:real`
       (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `f:real^N->real` STRIP_ASSUME_TAC)))
     (X_CHOOSE_THEN `b:real`
       (CONJUNCTS_THEN2 ASSUME_TAC
         (X_CHOOSE_THEN `g:real^N->real` STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INDEPENDENT_EXPLICIT]) THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_DELETE; FINITE_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC
     `\x. if x = v then a + b else (f:real^N->real) x - g x`) THEN
    ASM_SIMP_TAC[VSUM_CLAUSES; FINITE_DELETE; FINITE_UNION] THEN
    ASM_REWRITE_TAC[IN_DELETE; IN_UNION] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
      REWRITE_TAC[IN_INSERT] THEN ASM_REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[SET_RULE
      `~(a IN t) ==> (s DELETE a) UNION t = (s UNION t) DELETE a`] THEN
    ASM_SIMP_TAC[VSUM_DELETE_CASES; FINITE_UNION; IN_UNION] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
    SUBGOAL_THEN
     `!x:real^N. (if x = v then a + b else f x - g x) % x =
                 (if x = v then a else f x) % x -
                 (if x = v then --b else g x) % x`
     (fun th -> REWRITE_TAC[th])
    THENL
     [GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ASM_SIMP_TAC[VSUM_SUB; FINITE_UNION]] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(a + b) % v + (y - a % v) - (y - b % --v):real^N` THEN
    CONJ_TAC THENL [ALL_TAC; VECTOR_ARITH_TAC] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_UNION];
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `aff_gt s t :real^N->bool` THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `affine hull (s UNION t:real^N->bool)` THEN
    REWRITE_TAC[AFF_GT_SUBSET_AFFINE_HULL] THEN
    ASM_SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_UNION; HULL_INC] THEN
    ONCE_REWRITE_TAC[GSYM SPAN_DELETE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `CARD((s UNION t) DELETE (vec 0:real^N))` THEN
    ASM_SIMP_TAC[DIM_LE_CARD; FINITE_DELETE; FINITE_UNION; DIM_SPAN] THEN
    ASM_SIMP_TAC[CARD_DELETE; IN_UNION; FINITE_UNION] THEN
    MATCH_MP_TAC(ARITH_RULE `1 <= n /\ x <= n ==> x - 1 < n`) THEN
    ASM_REWRITE_TAC[DIMINDEX_GE_1]]);;

let MEASURE_BALL_AFF_GT_SHUFFLE = prove
 (`!r s t v:real^N.
        &0 <= r /\ ~(v IN (s UNION t)) /\
        independent(v INSERT (s UNION t))
        ==> measure(ball(vec 0,r) INTER aff_gt (vec 0 INSERT v INSERT s) t) =
            measure(ball(vec 0,r) INTER aff_gt (vec 0 INSERT s) (v INSERT t)) +
            measure(ball(vec 0,r) INTER
                    aff_gt (vec 0 INSERT s) (--v INSERT t))`,
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real`; `(vec 0:real^N) INSERT s`;
                 `t:real^N->bool`; `v:real^N`]
        MEASURE_BALL_AFF_GT_SHUFFLE_LEMMA) THEN
  ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[INSERT_AC]] THEN
  ASM_REWRITE_TAC[IN_INSERT; FINITE_INSERT] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INDEPENDENT_NONZERO) THEN
  REWRITE_TAC[IN_INSERT; IN_UNION; DE_MORGAN_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP INDEPENDENT_BOUND) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_UNION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[SET_RULE `(a INSERT s) UNION t = a INSERT (s UNION t)`] THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_UNION; IN_UNION; FINITE_INSERT] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[VECTOR_NEG_EQ_0] THEN CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] INDEPENDENT_MONO)) THEN
    SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [independent]) THEN
    REWRITE_TAC[dependent; CONTRAPOS_THM] THEN DISCH_TAC THEN
    EXISTS_TAC `v:real^N` THEN REWRITE_TAC[IN_INSERT] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_NEG_NEG] THEN
    MATCH_MP_TAC SPAN_NEG THEN MATCH_MP_TAC SPAN_SUPERSET THEN
    ASM_REWRITE_TAC[IN_DELETE; VECTOR_ARITH `--v:real^N = v <=> v = vec 0`;
                    IN_INSERT; IN_UNION]]);;

let MEASURE_LUNE_DECOMPOSITION = prove
 (`!v1 v2 v3:real^3.
         &0 <= r /\ ~coplanar {vec 0, v1, v2, v3}
         ==> measure(ball(vec 0,r) INTER aff_gt {vec 0} {v1,v2,v3}) +
             measure(ball(vec 0,r) INTER aff_gt {vec 0} {--v1,v2,v3}) =
             dihV (vec 0) v1 v2 v3 * &2 * r pow 3 / &3`,
  let rec distinctpairs l =
    match l with
     x::t -> itlist (fun y a -> (x,y) :: a) t (distinctpairs t)
    | [] -> [] in
  REPEAT GEN_TAC THEN MAP_EVERY
   (fun t -> ASM_CASES_TAC t THENL
    [ASM_REWRITE_TAC[INSERT_AC; COPLANAR_3]; ALL_TAC])
   (map mk_eq (distinctpairs
    [`v3:real^3`; `v2:real^3`; `v1:real^3`; `vec 0:real^3`])) THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM(REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
    HAS_MEASURE_LUNE_SIMPLE)] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_BALL_AFF_GT_SHUFFLE THEN
  ASM_REWRITE_TAC[UNION_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_SIMP_TAC[NOT_COPLANAR_0_4_IMP_INDEPENDENT]);;

let SOLID_TRIANGLE_CONGRUENT_NEG = prove
 (`!r v1 v2 v3:real^N.
        measure(ball(vec 0,r) INTER aff_gt {vec 0} {--v1, --v2, --v3}) =
        measure(ball(vec 0,r) INTER aff_gt {vec 0} {v1, v2, v3})`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `ball(vec 0:real^N,r) INTER aff_gt {vec 0} {--v1, --v2, --v3} =
    IMAGE (--)
          (ball(vec 0,r) INTER aff_gt {vec 0} {v1, v2, v3})`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MEASURE_ORTHOGONAL_IMAGE_EQ THEN
    REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; linear; NORM_NEG] THEN
    CONJ_TAC THEN VECTOR_ARITH_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  CONJ_TAC THENL [MESON_TAC[VECTOR_NEG_NEG]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; IN_BALL_0; NORM_NEG] THEN
  REWRITE_TAC[AFFSIGN_ALT; aff_gt_def; sgn_gt; IN_ELIM_THM] THEN
  REWRITE_TAC[SET_RULE `{a} UNION {b,c,d} = {a,b,d,c}`] THEN
  REWRITE_TAC[SET_RULE `x IN {a} <=> a = x`] THEN
  ASM_SIMP_TAC[FINITE_INSERT; FINITE_UNION; AFFINE_HULL_FINITE_STEP_GEN;
               RIGHT_EXISTS_AND_THM; REAL_LT_ADD; REAL_HALF; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_SUB_RZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `vec 0:real^N = --x <=> vec 0 = x`] THEN
  REWRITE_TAC[VECTOR_ARITH `--x - a % --w:real^N = --(x - a % w)`] THEN
  REWRITE_TAC[VECTOR_NEG_EQ_0]);;

let VOLUME_SOLID_TRIANGLE = prove
 (`!r v0 v1 v2 v3:real^3.
       &0 < r /\ ~coplanar{v0, v1, v2, v3}
       ==> measure(ball(v0,r) INTER aff_gt {v0} {v1,v2,v3}) =
                let a123 = dihV v0 v1 v2 v3 in
                let a231 = dihV v0 v2 v3 v1 in
                let a312 = dihV v0 v3 v1 v2 in
                  (a123 + a231 + a312 - pi) * r pow 3 / &3`,
  let tac convl =
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURE_BALL_AFF_GT_SHUFFLE o
      convl o lhand o lhand o snd) THEN
    ASM_REWRITE_TAC[UNION_EMPTY; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    REWRITE_TAC[SET_RULE `(a INSERT s) UNION t = a INSERT (s UNION t)`] THEN
    ASM_SIMP_TAC[UNION_EMPTY; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [DISCH_THEN(STRIP_THM_THEN SUBST_ALL_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[COPLANAR_3]) THEN
        FIRST_ASSUM CONTR_TAC;
        MATCH_MP_TAC NOT_COPLANAR_0_4_IMP_INDEPENDENT THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN
        ASM_REWRITE_TAC[INSERT_AC]];
      DISCH_THEN SUBST1_TAC] in
  GEN_TAC THEN GEOM_ORIGIN_TAC `v0:real^3` THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
    `measure(ball(vec 0:real^3,r) INTER aff_gt {vec 0,v1,v2,v3} {}) =
     &4 / &3 * pi * r pow 3`
  MP_TAC THENL
   [MP_TAC(SPECL [`vec 0:real^3`; `r:real`] VOLUME_BALL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE `t = UNIV ==> s INTER t = s`) THEN
    REWRITE_TAC[AFF_GT_EQ_AFFINE_HULL] THEN
    SIMP_TAC[AFFINE_HULL_EQ_SPAN; HULL_INC; IN_INSERT; SPAN_INSERT_0] THEN
    REWRITE_TAC[SET_RULE `s = UNIV <=> UNIV SUBSET s`] THEN
    MATCH_MP_TAC CARD_GE_DIM_INDEPENDENT THEN
    ASM_SIMP_TAC[DIM_UNIV; DIMINDEX_3; SUBSET_UNIV] THEN
    ASM_SIMP_TAC[NOT_COPLANAR_0_4_IMP_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    MAP_EVERY (fun t ->
      ASM_CASES_TAC t THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC; COPLANAR_3]) THEN
        ASM_MESON_TAC[];
        ASM_REWRITE_TAC[]])
     [`v3:real^3 = v2`; `v3:real^3 = v1`; `v2:real^3 = v1`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(coplanar {vec 0:real^3,v1,v2,v3}) /\
    ~(coplanar {vec 0,--v1,v2,v3}) /\
    ~(coplanar {vec 0,v1,--v2,v3}) /\
    ~(coplanar {vec 0,--v1,--v2,v3}) /\
    ~(coplanar {vec 0,--v1,--v2,v3}) /\
    ~(coplanar {vec 0,--v1,v2,--v3}) /\
    ~(coplanar {vec 0,v1,--v2,--v3}) /\
    ~(coplanar {vec 0,--v1,--v2,--v3}) /\
    ~(coplanar {vec 0,--v1,--v2,--v3})`
  STRIP_ASSUME_TAC THENL
   [REPLICATE_TAC 3
     (REWRITE_TAC[COPLANAR_INSERT_0_NEG] THEN
      ONCE_REWRITE_TAC[SET_RULE `{vec 0,a,b,c} = {vec 0,b,c,a}`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY tac
   [I; lhand; rand;
    lhand o lhand; rand o lhand; lhand o rand; rand o rand] THEN
  MP_TAC(ISPECL [`v1:real^3`; `v2:real^3`; `v3:real^3`]
    MEASURE_LUNE_DECOMPOSITION) THEN
  MP_TAC(ISPECL [`v2:real^3`; `v3:real^3`; `v1:real^3`]
    MEASURE_LUNE_DECOMPOSITION) THEN
  MP_TAC(ISPECL [`v3:real^3`; `v1:real^3`; `v2:real^3`]
    MEASURE_LUNE_DECOMPOSITION) THEN
  MP_TAC(ISPECL [`--v1:real^3`; `--v2:real^3`; `--v3:real^3`]
    MEASURE_LUNE_DECOMPOSITION) THEN
  MP_TAC(ISPECL [`--v2:real^3`; `--v3:real^3`; `--v1:real^3`]
    MEASURE_LUNE_DECOMPOSITION) THEN
  MP_TAC(ISPECL [`--v3:real^3`; `--v1:real^3`; `--v2:real^3`]
    MEASURE_LUNE_DECOMPOSITION) THEN
  ASM_REWRITE_TAC[VECTOR_NEG_NEG] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE; INSERT_AC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INSERT_AC]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DIHV_NEG_0] THEN
  REWRITE_TAC[SOLID_TRIANGLE_CONGRUENT_NEG] THEN
  REWRITE_TAC[INSERT_AC] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Volume of wedge of a frustum.                                             *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_BOUNDED_INTER_OPEN = prove
 (`!s t:real^N->bool.
       measurable s /\ bounded s /\ open t ==> measurable(s INTER t)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP (SET_RULE
   `s SUBSET i ==> s INTER t = s INTER (t INTER i)`)) THEN
  MATCH_MP_TAC MEASURABLE_INTER THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_OPEN THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL; BOUNDED_INTER; BOUNDED_INTERVAL]);;

let SLICE_SPECIAL_WEDGE = prove
 (`!w1 w2.
        ~collinear {vec 0, basis 3, w1} /\ ~collinear {vec 0, basis 3, w2}
        ==> slice 3 t (wedge (vec 0) (basis 3) w1 w2) =
            {z | &0 < Arg(z / dropout 3 w1) /\
                 Arg(z / dropout 3 w1) < Arg(dropout 3 w2 / dropout 3 w1)}`,
  REWRITE_TAC[wedge] THEN
  ONCE_REWRITE_TAC[TAUT `~a /\ b /\ c <=> ~(~a ==> ~(b /\ c))`] THEN
  ASM_SIMP_TAC[AZIM_ARG] THEN REWRITE_TAC[COLLINEAR_BASIS_3] THEN
  REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; DROPOUT_0] THEN
  MAP_EVERY ABBREV_TAC
   [`v1:real^2 = dropout 3 (w1:real^3)`;
    `v2:real^2 = dropout 3 (w2:real^3)`] THEN
  REWRITE_TAC[SLICE_DROPOUT_3; VEC_COMPONENT; REAL_SUB_RZERO] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; COMPLEX_VEC_0] THEN
  X_GEN_TAC `w:complex` THEN
  ASM_CASES_TAC `w = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[complex_div; COMPLEX_MUL_LZERO; ARG_0; REAL_LT_REFL]);;

let VOLUME_FRUSTT_WEDGE = prove
 (`!v0 v1:real^3 w1 w2 h a.
       &0 < a /\ ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
       ==> bounded(frustt v0 v1 h a INTER wedge v0 v1 w1 w2) /\
           measurable(frustt v0 v1 h a INTER wedge v0 v1 w1 w2) /\
           measure(frustt v0 v1 h a INTER wedge v0 v1 w1 w2) =
           if &1 <= a \/ h < &0 then &0
           else azim v0 v1 w1 w2 * ((h / a) pow 2 - h pow 2) * h / &6`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `v1:real^3 = v0` THENL
   [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]; STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_INTER THEN ASM_SIMP_TAC[VOLUME_FRUSTT_STRONG];
    MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
    ASM_SIMP_TAC[VOLUME_FRUSTT_STRONG; OPEN_WEDGE];
    ALL_TAC] THEN
  REWRITE_TAC[frustt; frustum; rcone_gt; rconesgn; IN_ELIM_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; REAL_MUL_LZERO; DIST_0; real_gt] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  X_GEN_TAC `b:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
  ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE; WEDGE_SPECIAL_SCALE] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 <= a` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `!y:real^3. ~(norm(y) * norm(b % basis 3:real^3) * a
                   < y dot (b % basis 3))`
     (fun th -> REWRITE_TAC[th; EMPTY_GSPEC; MEASURABLE_EMPTY;
                    INTER_EMPTY; MEASURE_EMPTY]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN X_GEN_TAC `y:real^3` THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    SIMP_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_MUL; DOT_BASIS; NORM_BASIS;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_ARITH
     `b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_ABS_POS; COMPONENT_LE_NORM; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  SIMP_TAC[NORM_MUL; NORM_BASIS; DOT_BASIS; DOT_RMUL; DIMINDEX_3; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `n * x * a:real = x * n * a`] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_MUL_RID; REAL_LT_LMUL_EQ; REAL_LT_MUL_EQ; NORM_POS_LT] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH;
               REAL_LT_IMP_NZ] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_LT_SQUARE] THEN
  ASM_SIMP_TAC[REAL_POW_DIV; REAL_POW_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `(&0 * x < y /\ u < v) /\ &0 < y /\ y < h <=>
                          &0 < y /\ y < h /\ u < v`] THEN
  DISCH_TAC THEN MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] FUBINI_SIMPLE_ALT) THEN
  EXISTS_TAC `3` THEN ASM_REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  ASM_SIMP_TAC[WEDGE_SPECIAL_SCALE; REAL_LT_IMP_LE] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; SLICE_INTER; DIMINDEX_2;
               DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN
   `!t. slice 3 t {y:real^3 | norm y * a < y$3 /\ &0 < y$3 /\ y$3 < h} =
        if t < h
        then ball(vec 0:real^2,sqrt(inv(a pow 2) - &1) * t)
        else {}`
   (fun th -> ASM_SIMP_TAC[th; SLICE_SPECIAL_WEDGE])
  THENL
   [REWRITE_TAC[EXTENSION] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^2`] THEN
    SIMP_TAC[SLICE_123; DIMINDEX_2; DIMINDEX_3; ARITH; IN_ELIM_THM;
             VECTOR_3; DOT_3; GSYM DOT_2] THEN
    ASM_CASES_TAC `t < h` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
    REWRITE_TAC[IN_BALL_0; IN_DELETE] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= a /\ (a < t <=> u < v) ==> (a < t /\ &0 < t <=> u < v)`) THEN
    ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LT_IMP_LE] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_LT_SQUARE] THEN
    SUBGOAL_THEN `&0 < inv(a pow 2) - &1` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
      ASM_SIMP_TAC[REAL_POW_1_LT; REAL_LT_IMP_LE; ARITH; REAL_POW_LT];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; SQRT_POS_LT; REAL_POW_MUL; SQRT_POW_2;
                 REAL_LT_IMP_LE; REAL_LT_MUL_EQ] THEN
    ASM_SIMP_TAC[real_div; REAL_LT_MUL_EQ; REAL_LT_INV_EQ] THEN
    ASM_CASES_TAC `&0 < t` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DOT_3; DOT_2; VECTOR_3; REAL_INV_POW] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [COND_RATOR; COND_RAND] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [COND_RATOR; COND_RAND] THEN
  REWRITE_TAC[INTER_EMPTY; MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  REWRITE_TAC[INTER; IN_BALL_0; IN_ELIM_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                 HAS_MEASURE_OPEN_SECTOR_LT_GEN] THEN
  REWRITE_TAC[COND_ID] THEN
  SUBGOAL_THEN `&0 < inv(a pow 2) - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
    ASM_SIMP_TAC[REAL_POW_1_LT; REAL_LT_IMP_LE; ARITH; REAL_POW_LT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_MUL_EQ; SQRT_POS_LT] THEN
  ASM_SIMP_TAC[AZIM_SPECIAL_SCALE; AZIM_ARG; COLLINEAR_BASIS_3] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\t. if &0 < t /\ t < h
        then Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3)) / &2 *
             (inv(a pow 2) - &1) * t pow 2
        else &0` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_CASES_TAC `t < h` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= t <=> t = &0 \/ &0 < t`] THEN
    ASM_CASES_TAC `t = &0` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_RZERO; SQRT_0] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
    ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; REAL_LT_IMP_LE] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
  COND_CASES_TAC THENL
   [ASM_MESON_TAC[REAL_INTERVAL_EQ_EMPTY; HAS_REAL_INTEGRAL_EMPTY];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT])] THEN
  ABBREV_TAC `g = Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))` THEN
  MP_TAC(ISPECL
   [`\t. g / &6 * (inv (a pow 2) - &1) * t pow 3`;
    `\t. g / &2 * (inv (a pow 2) - &1) * t pow 2`;
    `&0`; `h:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD]);;

(* ------------------------------------------------------------------------- *)
(* Wedge of a conic cap.                                                     *)
(* ------------------------------------------------------------------------- *)

let VOLUME_CONIC_CAP_WEDGE_WEAK = prove
 (`!v0 v1:real^3 w1 w2 r a.
       &0 < a /\ ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
       ==> bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
           measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
           measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =
           if &1 <= a \/ r < &0 then &0
           else azim v0 v1 w1 w2 / &3 * (&1 - a) * r pow 3`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `v1:real^3 = v0` THENL
   [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (a /\ b ==> c) ==> a /\ b /\ c`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_INTER THEN ASM_SIMP_TAC[VOLUME_CONIC_CAP_STRONG];
    MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
    ASM_SIMP_TAC[VOLUME_CONIC_CAP_STRONG; OPEN_WEDGE];
    ALL_TAC] THEN
  REWRITE_TAC[conic_cap; rcone_gt; rconesgn; IN_ELIM_THM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] normball; GSYM ball] THEN
  CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; REAL_MUL_LZERO; DIST_0; real_gt] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  X_GEN_TAC `b:real` THEN
  ASM_CASES_TAC `b = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
  SIMP_TAC[COLLINEAR_SPECIAL_SCALE; WEDGE_SPECIAL_SCALE] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&1 <= a` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN
     `!y:real^3. ~(norm(y) * norm(b % basis 3:real^3) * a
                   < y dot (b % basis 3))`
     (fun th -> REWRITE_TAC[th; EMPTY_GSPEC; INTER_EMPTY; MEASURE_EMPTY;
                         MEASURABLE_EMPTY; BOUNDED_EMPTY; CONVEX_EMPTY]) THEN
    REWRITE_TAC[REAL_NOT_LT] THEN X_GEN_TAC `y:real^3` THEN
    MATCH_MP_TAC(REAL_ARITH `abs(x) <= a ==> x <= a`) THEN
    SIMP_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_MUL; DOT_BASIS; NORM_BASIS;
             DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[REAL_ARITH
     `b * y <= n * (b * &1) * a <=> b * &1 * y <= b * a * n`] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_POS; REAL_ABS_POS; COMPONENT_LE_NORM; DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  SIMP_TAC[DOT_RMUL; NORM_MUL; REAL_ABS_NORM; DOT_BASIS;
           DIMINDEX_3; ARITH; NORM_BASIS] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `n * x * a:real = x * n * a`] THEN
  ASM_REWRITE_TAC[real_abs; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_MUL_RID; REAL_LT_LMUL_EQ; REAL_LT_MUL_EQ; NORM_POS_LT] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; NORM_LT_SQUARE] THEN
  ASM_SIMP_TAC[REAL_POW_DIV; REAL_POW_LT; REAL_LT_RDIV_EQ] THEN
  REWRITE_TAC[INTER; REAL_MUL_LZERO; IN_BALL_0; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_3; ARITH;
               REAL_LT_IMP_NZ] THEN
  COND_CASES_TAC THENL
   [ASM_SIMP_TAC[NORM_ARITH `r < &0 ==> ~(norm x < r)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; MEASURE_EMPTY; MEASURABLE_EMPTY;
                BOUNDED_EMPTY; CONVEX_EMPTY];
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[REAL_NOT_LT])] THEN
  STRIP_TAC THEN MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] FUBINI_SIMPLE_ALT) THEN
  EXISTS_TAC `3` THEN ASM_REWRITE_TAC[DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[WEDGE_SPECIAL_SCALE; AZIM_SPECIAL_SCALE] THEN
  ONCE_REWRITE_TAC[SET_RULE `{x | P x /\ x IN s} = {x | P x} INTER s`] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; SLICE_INTER; DIMINDEX_2;
               DIMINDEX_3; ARITH] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[MATCH_MP COLLINEAR_SPECIAL_SCALE (ASSUME `~(b = &0)`)]) THEN
  SUBGOAL_THEN `&0 < inv(a pow 2) - &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
    ASM_SIMP_TAC[REAL_POW_1_LT; REAL_LT_IMP_LE; ARITH; REAL_POW_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t. slice 3 t {y:real^3 | norm y < r /\ norm y * a < y$3} =
        if &0 < t /\ t < r
        then ball(vec 0:real^2,min (sqrt(r pow 2 - t pow 2))
                                   (t * sqrt(inv(a pow 2) - &1)))
        else {}`
   (fun th -> ASM_SIMP_TAC[th; SLICE_SPECIAL_WEDGE])
  THENL
   [REWRITE_TAC[EXTENSION] THEN
    MAP_EVERY X_GEN_TAC [`t:real`; `z:real^2`] THEN
    SIMP_TAC[SLICE_123; DIMINDEX_2; DIMINDEX_3; ARITH; IN_ELIM_THM;
             VECTOR_3; DOT_3; GSYM DOT_2] THEN
    ASM_CASES_TAC `&0 < t` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      REWRITE_TAC[NOT_IN_EMPTY; DE_MORGAN_THM] THEN DISJ2_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `~(&0 < t) ==> &0 <= a ==> ~(a < t)`)) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; NORM_POS_LE; REAL_LT_IMP_LE]] THEN
    ASM_CASES_TAC `t < r` THEN ASM_REWRITE_TAC[] THENL
     [ALL_TAC;
      REWRITE_TAC[NOT_IN_EMPTY; DE_MORGAN_THM] THEN DISJ1_TAC THEN
      REWRITE_TAC[NORM_LT_SQUARE; DE_MORGAN_THM] THEN DISJ2_TAC THEN
      REWRITE_TAC[DOT_3; VECTOR_3] THEN
      MATCH_MP_TAC(REAL_ARITH
       `r <= t /\ &0 <= a /\ &0 <= b ==> ~(a + b + t < r)`) THEN
      REWRITE_TAC[REAL_LE_SQUARE; REAL_POW_2] THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[IN_BALL_0; REAL_LT_MIN] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN REWRITE_TAC[NORM_LT_SQUARE] THEN
    SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t pow 2 < r pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_POW_LT2 THEN REWRITE_TAC[ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; SQRT_POS_LT; REAL_LT_MUL; REAL_SUB_LT;
                 SQRT_POW_2; REAL_LT_IMP_LE; REAL_POW_MUL] THEN
    REWRITE_TAC[DOT_2; DOT_3; VECTOR_3] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a + b + c < d <=> a + b < d - c`] THEN
    BINOP_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [COND_RATOR; COND_RAND] THEN
  GEN_REWRITE_TAC (RAND_CONV o RATOR_CONV o LAND_CONV o TOP_DEPTH_CONV)
   [COND_RATOR; COND_RAND] THEN
  REWRITE_TAC[INTER_EMPTY; MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  REWRITE_TAC[INTER; IN_BALL_0; IN_ELIM_THM] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[COLLINEAR_BASIS_3]) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                 HAS_MEASURE_OPEN_SECTOR_LT_GEN] THEN
  REWRITE_TAC[COND_ID] THEN
  ASM_SIMP_TAC[REAL_LE_MIN; SQRT_POS_LE; REAL_LT_IMP_LE; REAL_LE_MUL;
               REAL_POW_LE2; ARITH; REAL_SUB_LE; REAL_LT_MUL; SQRT_POS_LT] THEN
  REWRITE_TAC[GSYM IN_REAL_INTERVAL; HAS_REAL_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[HAS_REAL_INTEGRAL_OPEN_INTERVAL] THEN
  REWRITE_TAC[NORM_POW_2; DOT_3; VECTOR_3; DOT_2] THEN
  ASM_SIMP_TAC[AZIM_ARG; COLLINEAR_BASIS_3] THEN
  ONCE_REWRITE_TAC[REAL_ARITH
   `(&1 - a) * az / &3 * r pow 3 =
    az / &6 * (inv (a pow 2) - &1) * (a * r) pow 3 +
    (az * &1 / &3 * (&1 - a) * r pow 3 -
     az / &6 * (inv (a pow 2) - &1) * (a * r) pow 3)`] THEN
  MATCH_MP_TAC HAS_REAL_INTEGRAL_COMBINE THEN
  EXISTS_TAC `a * r:real` THEN
  REWRITE_TAC[REAL_ARITH `a * r <= r <=> &0 <= r * (&1 - a)`] THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
  ABBREV_TAC `k = Arg(dropout 3 (w2:real^3) / dropout 3 (w1:real^3))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
     `\t. k * t pow 2 * (inv(a pow 2) - &1) / &2` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `t pow 2 * (inv(a pow 2) - &1) <= r pow 2 - t pow 2`
      ASSUME_TAC THENL
       [REWRITE_TAC[REAL_ARITH `t * (a - &1) <= r - t <=> t * a <= r`] THEN
        ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_POW_LT] THEN
        REWRITE_TAC[GSYM REAL_POW_MUL] THEN MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `t * sqrt(inv(a pow 2) - &1) <= sqrt(r pow 2 - t pow 2)`
        (fun th -> SIMP_TAC[th; REAL_ARITH `a <= b ==> min b a = a`])
      THENL
       [MATCH_MP_TAC REAL_POW_LE2_REV THEN EXISTS_TAC `2` THEN
        REWRITE_TAC[ARITH] THEN
        SUBGOAL_THEN `&0 <= r pow 2 - t pow 2` ASSUME_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `a <= x ==> &0 <= a ==> &0 <= x`)) THEN
          ASM_SIMP_TAC[REAL_POW_2; REAL_LE_MUL; REAL_LE_SQUARE; REAL_LT_IMP_LE];
          ASM_SIMP_TAC[SQRT_POS_LE; REAL_POW_MUL; SQRT_POW_2;
                       REAL_LT_IMP_LE]];
        ASM_SIMP_TAC[REAL_POW_MUL; SQRT_POW_2; SQRT_POW_2; REAL_LT_IMP_LE] THEN
        REAL_ARITH_TAC];
      MP_TAC(ISPECL
       [`\t. k / &6 * (inv (a pow 2) - &1) * t pow 3`;
        `\t. k * t pow 2 * (inv (a pow 2) - &1) / &2`;
        `&0`; `a * r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD]];
    MATCH_MP_TAC HAS_REAL_INTEGRAL_EQ THEN EXISTS_TAC
     `\t:real. k * (r pow 2 - t pow 2) / &2` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `t:real` THEN REWRITE_TAC[IN_REAL_INTERVAL] THEN
      STRIP_TAC THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `&0 <= t` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `a * r:real` THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `a <= b /\ a pow 2 = x ==> x / &2 = (min a b pow 2) / &2`) THEN
      SUBGOAL_THEN `&0 <= r pow 2 - t pow 2` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_LE_SQUARE_ABS; REAL_SUB_LE] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_SIMP_TAC[SQRT_POW_2] THEN MATCH_MP_TAC REAL_POW_LE2_REV THEN
      EXISTS_TAC `2` THEN REWRITE_TAC[ARITH] THEN
      ASM_SIMP_TAC[SQRT_POW_2; REAL_POW_MUL; REAL_LE_MUL; SQRT_POS_LT;
                   REAL_LT_MUL; REAL_LT_IMP_LE; SQRT_POS_LE] THEN
      REWRITE_TAC[REAL_ARITH `r - t <= t * (a - &1) <=> r <= t * a`] THEN
      REWRITE_TAC[REAL_INV_POW; GSYM REAL_POW_MUL] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      MP_TAC(ISPECL
       [`\t. k / &2 * (r pow 2 * t - t pow 3 / &3)`;
        `\t. k * (r pow 2 - t pow 2) / &2`;
        `a * r:real`; `r:real`] REAL_FUNDAMENTAL_THEOREM_OF_CALCULUS) THEN
      ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[REAL_ARITH `a * r <= r <=> &0 <= r * (&1 - a)`] THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; REAL_SUB_LE] THEN
        REPEAT STRIP_TAC THEN REAL_DIFF_TAC THEN
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RING;
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < a` THEN CONV_TAC REAL_FIELD]]]);;

let BOUNDED_CONIC_CAP_WEDGE = prove
 (`!v0 v1:real^3 w1 w2 r a.
        bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `conic_cap (v0:real^3) v1 r a` THEN
  REWRITE_TAC[BOUNDED_CONIC_CAP] THEN SET_TAC[]);;

let MEASURABLE_CONIC_CAP_WEDGE = prove
 (`!v0 v1:real^3 w1 w2 r a.
        measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2)`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
  REWRITE_TAC[BOUNDED_CONIC_CAP; MEASURABLE_CONIC_CAP; OPEN_WEDGE]);;

let VOLUME_CONIC_CAP_COMPL = prove
 (`!v0 v1:real^3 w1 w2 r a.
        &0 <= r
        ==> measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) +
            measure(conic_cap v0 v1 r (--a) INTER wedge v0 v1 w1 w2) =
            azim v0 v1 w1 w2 * &2 * r pow 3 / &3`,
  let lemma = prove
   (`!f:real^N->real^N s t t' u.
          measurable(s) /\ measurable(t) /\ measurable(u) /\
          orthogonal_transformation f /\
          s SUBSET u /\ t' SUBSET u /\ s INTER t' = {} /\
          negligible(u DIFF (s UNION t')) /\
          ((!y. ?x. f x = y) ==> IMAGE f t = t')
          ==> measure s + measure t = measure u`,
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC `orthogonal_transformation(f:real^N->real^N)` THEN
    ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `measure(s:real^N->bool) + measure(t':real^N->bool)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MEASURE_ORTHOGONAL_IMAGE_EQ]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (rhs o rand) MEASURE_DISJOINT_UNION o
      lhand o snd) THEN
    ASM_REWRITE_TAC[DISJOINT] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_LINEAR_IMAGE; ORTHOGONAL_TRANSFORMATION_LINEAR];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]) in
  REWRITE_TAC[conic_cap; rcone_gt; NORMBALL_BALL; rconesgn] THEN
  GEOM_ORIGIN_TAC `v0:real^3` THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0; real_gt] THEN
  GEOM_BASIS_MULTIPLE_TAC 3 `v1:real^3` THEN
  X_GEN_TAC `v1:real` THEN
  GEN_REWRITE_TAC LAND_CONV [REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
  STRIP_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_LZERO; WEDGE_DEGENERATE; AZIM_DEGENERATE] THEN
    REWRITE_TAC[INTER_EMPTY; MEASURE_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VOLUME_BALL_WEDGE] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `collinear {vec 0:real^3,v1 % basis 3,w1}` THENL
   [ASM_SIMP_TAC[WEDGE_DEGENERATE; AZIM_DEGENERATE] THEN
    REWRITE_TAC[INTER_EMPTY; MEASURE_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM VOLUME_BALL_WEDGE] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `collinear {vec 0:real^3,v1 % basis 3,w2}` THENL
   [ASM_SIMP_TAC[WEDGE_DEGENERATE; AZIM_DEGENERATE] THEN
    REWRITE_TAC[INTER_EMPTY; MEASURE_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[WEDGE_SPECIAL_SCALE] THEN
  MAP_EVERY UNDISCH_TAC
   [`~collinear{vec 0:real^3,v1 % basis 3,w1}`;
    `~collinear{vec 0:real^3,v1 % basis 3,w2}`] THEN
  ASM_SIMP_TAC[COLLINEAR_SPECIAL_SCALE] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[NORM_MUL; DOT_RMUL] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH
    `&0 < v1 ==> n * (abs v1 * y) * a = v1 * n * y * a`] THEN
  MATCH_MP_TAC lemma THEN
  MP_TAC(ISPECL
   [`vec 0:real^3`; `basis 3:real^3`; `w1:real^3`; `w2:real^3`;
    `r:real`; `a:real`] MEASURABLE_CONIC_CAP_WEDGE) THEN
  MP_TAC(ISPECL
   [`vec 0:real^3`; `basis 3:real^3`; `w1:real^3`; `w2:real^3`;
    `r:real`; `--a:real`] MEASURABLE_CONIC_CAP_WEDGE) THEN
  REWRITE_TAC[conic_cap; rcone_gt; NORMBALL_BALL; rconesgn] THEN
  REWRITE_TAC[VECTOR_SUB_RZERO; DIST_0; real_gt] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[MEASURABLE_BALL_WEDGE] THEN
  SIMP_TAC[NORM_BASIS; DOT_BASIS; DIMINDEX_3; ARITH; REAL_MUL_LID] THEN
  EXISTS_TAC `(\x. vector[x$1; x$2; --(x$3)]):real^3->real^3` THEN
  EXISTS_TAC `(ball(vec 0,r) INTER {x | norm x * a > x$3}) INTER
              wedge (vec 0:real^3) (basis 3) w1 w2` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; linear] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; vector_norm; DOT_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE AP_TERM_TAC) THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_ELIM_THM; real_gt] THEN
    MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `rcone_eq (vec 0:real^3) (basis 3) a` THEN
    SIMP_TAC[NEGLIGIBLE_RCONE_EQ; BASIS_NONZERO; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[SUBSET; rcone_eq; rconesgn; VECTOR_SUB_RZERO; DIST_0] THEN
    SIMP_TAC[DOT_BASIS; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    REWRITE_TAC[IN_DIFF; IN_ELIM_THM; IN_INTER; IN_UNION] THEN
    GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTER; IN_BALL_0; IN_ELIM_THM; VECTOR_3] THEN
  X_GEN_TAC `x:real^3` THEN
  SUBGOAL_THEN `norm(vector [x$1; x$2; --(x$3)]:real^3) = norm(x:real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[NORM_EQ; DOT_3; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[REAL_ARITH `n * a > --x <=> n * --a < x`] THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> b')) ==> (a /\ b <=> a /\ b')`) THEN
  STRIP_TAC THEN
  REWRITE_TAC[COLLINEAR_BASIS_3; wedge; AZIM_ARG] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(dropout 3 :real^3->real^2) (vector [x$1; x$2; --(x$3)]) =
                (dropout 3 :real^3->real^2) x`
   (fun th -> REWRITE_TAC[th]) THEN
  SIMP_TAC[CART_EQ; DIMINDEX_2; FORALL_2; dropout; LAMBDA_BETA; ARITH;
           VECTOR_3]);;

let VOLUME_CONIC_CAP_WEDGE_MEDIUM = prove
 (`!v0 v1:real^3 w1 w2 r a.
       &0 <= a /\ ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
       ==> bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
           measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
           measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =
           if &1 < abs a \/ r < &0 then &0
           else azim v0 v1 w1 w2 / &3 * (&1 - a) * r pow 3`,
  REWRITE_TAC[BOUNDED_CONIC_CAP_WEDGE; MEASURABLE_CONIC_CAP_WEDGE] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (REAL_ARITH
   `&0 <= a ==> &0 < a \/ a = &0`))
  THENL
   [ASM_SIMP_TAC[VOLUME_CONIC_CAP_WEDGE_WEAK] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    ASM_CASES_TAC `a = &1` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  COND_CASES_TAC THENL
   [REWRITE_TAC[conic_cap; NORMBALL_BALL] THEN
    SUBGOAL_THEN `ball(v0:real^3,r) = {}`
     (fun th -> SIMP_TAC[th; INTER_EMPTY; MEASURE_EMPTY]) THEN
    REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w1:real^3`; `w2:real^3`;
                   `r:real`; `&0`] VOLUME_CONIC_CAP_COMPL) THEN
    REWRITE_TAC[REAL_NEG_0] THEN ASM_REAL_ARITH_TAC]);;

let VOLUME_CONIC_CAP_WEDGE = prove
 (`!v0 v1:real^3 w1 w2 r a.
       ~collinear {v0,v1,w1} /\ ~collinear {v0,v1,w2}
       ==> bounded(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
           measurable(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) /\
           measure(conic_cap v0 v1 r a INTER wedge v0 v1 w1 w2) =
                if &1 < a \/ r < &0 then &0
                else azim v0 v1 w1 w2 / &3 * (&1 - max a (-- &1)) * r pow 3`,
  REWRITE_TAC[BOUNDED_CONIC_CAP_WEDGE; MEASURABLE_CONIC_CAP_WEDGE] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `&0 <= a` THEN
  ASM_SIMP_TAC[VOLUME_CONIC_CAP_WEDGE_MEDIUM;
               REAL_ARITH `&0 <= a ==> abs a = a /\ max a (-- &1) = a`] THEN
  MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w1:real^3`; `w2:real^3`;
                   `r:real`; `--a:real`] VOLUME_CONIC_CAP_WEDGE_MEDIUM) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`v0:real^3`; `v1:real^3`; `w1:real^3`; `w2:real^3`;
                 `r:real`; `a:real`] VOLUME_CONIC_CAP_COMPL) THEN
  ASM_CASES_TAC `r < &0` THENL
   [REWRITE_TAC[conic_cap; NORMBALL_BALL] THEN
    SUBGOAL_THEN `ball(v0:real^3,r) = {}`
     (fun th -> SIMP_TAC[th; INTER_EMPTY; MEASURE_EMPTY]) THEN
    REWRITE_TAC[BALL_EQ_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `~(&0 <= a) ==> ~(&1 < a) /\ abs a = --a`] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[REAL_ARITH `&1 < --a ==> max a (-- &1) = -- &1`] THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_ARITH `~(&1 < --a) ==> max a (-- &1) = a`] THEN
    REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Precise formulation of Flyspeck volume properties.                        *)
(* ------------------------------------------------------------------------- *)

(*** Might be preferable to switch
 ***
 *** normball z r -> ball(z,r)
 *** rect a b -> interval(a,b)
 ***
 *** to fit existing libraries. But I left this alone for now,
 *** to be absolutely sure I didn't introduce new errors.
 *** I also maintain
 ***
 *** NULLSET -> negligible
 *** vol -> measure
 ***
 *** as interface maps for the real^3 case.
 ***)

let cone = new_definition `cone v S:real^A->bool = affsign sgn_ge {v} S`;;

(*** JRH: should we exclude v for S = {}? Make it always open ***)

let cone0 = new_definition `cone0 v S:real^A->bool = affsign sgn_gt {v} S`;;

(*** JRH changed from cone to cone0 ***)

let solid_triangle = new_definition
  `solid_triangle v0 S r = normball v0 r INTER cone0 v0 S`;;

let rect = new_definition
  `rect (a:real^3) (b:real^3) =
        {(v:real^3) | !i. (a$i < v$i /\ v$i < b$i )}`;;

let RECT_INTERVAL = prove
 (`!a b. rect a b = interval(a,b)`,
  REWRITE_TAC[rect; EXTENSION; IN_INTERVAL; IN_ELIM_THM] THEN
  MESON_TAC[FINITE_INDEX_INRANGE]);;

let RCONE_GE_GT = prove
 (`rcone_ge z w h =
        rcone_gt z w h UNION
        { x | (x - z) dot (w - z) = norm(x - z) * norm(w - z) * h}`,
  REWRITE_TAC[rcone_ge; rcone_gt; rconesgn] THEN
  REWRITE_TAC[dist; EXTENSION; IN_UNION; NORM_SUB; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let RCONE_GT_GE = prove
 (`rcone_gt z w h =
        rcone_ge z w h DIFF
        { x | (x - z) dot (w - z) = norm(x - z) * norm(w - z) * h}`,
  REWRITE_TAC[rcone_ge; rcone_gt; rconesgn] THEN
  REWRITE_TAC[dist; EXTENSION; IN_DIFF; NORM_SUB; IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

override_interface("NULLSET",`negligible:(real^3->bool)->bool`);;
override_interface("vol",`measure:(real^3->bool)->real`);;

let is_sphere= new_definition
  `is_sphere x=(?(v:real^3)(r:real). (r> &0)/\ (x={w:real^3 | norm (w-v)= r}))`;;

let c_cone = new_definition
  `c_cone (v,w:real^3, r:real)=
       {x:real^3 | ((x-v) dot w = norm (x-v)* norm w* r)}`;;

(*** JRH added the condition ~(w = 0), or the cone is all of space ***)

let circular_cone =new_definition
  `circular_cone (V:real^3-> bool)=
   (? (v,w:real^3)(r:real). ~(w = vec 0) /\ V = c_cone (v,w,r))`;;

let NULLSET_RULES = prove
 (`(!P. ((plane P)\/ (is_sphere P) \/ (circular_cone P)) ==> NULLSET P) /\
   (!(s:real^3->bool) t. (NULLSET s /\ NULLSET t) ==> NULLSET (s UNION t))`,
  SIMP_TAC[NEGLIGIBLE_UNION] THEN
  X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THENL
   [MATCH_MP_TAC COPLANAR_IMP_NEGLIGIBLE THEN
    SIMP_TAC[COPLANAR; DIMINDEX_3; ARITH] THEN ASM_MESON_TAC[SUBSET_REFL];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [is_sphere]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[GSYM dist] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    REWRITE_TAC[REWRITE_RULE[sphere] NEGLIGIBLE_SPHERE];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [circular_cone]) THEN
    REWRITE_TAC[EXISTS_PAIRED_THM; c_cone] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`w + v:real^3`; `v:real^3`; `r:real`]
     NEGLIGIBLE_RCONE_EQ) THEN
    ASM_REWRITE_TAC[rcone_eq; rconesgn] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `(w + v) - v:real^N = w`] THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `w + v:real^N = v <=> w = vec 0`]]);;

(*** JRH added &0 < a for frustum; otherwise it's in general unbounded ***)

let primitive = new_definition `primitive (C:real^3->bool) =
  ((?v0 v1 v2 v3 r.  (C = solid_triangle v0 {v1,v2,v3} r)) \/
  (?v0 v1 v2 v3. (C = conv0 {v0,v1,v2,v3})) \/
  (?v0 v1 v2 v3 h a. &0 < a /\
                     (C = frustt v0 v1 h a INTER wedge v0 v1 v2 v3)) \/
  (?v0 v1 v2 v3 r c. (C = conic_cap v0 v1 r c INTER wedge v0 v1 v2 v3)) \/
  (?a b.  (C = rect a b)) \/
  (?t r. (C = ellipsoid t r)) \/
  (?v0 v1 v2 v3 r. (C = normball v0 r INTER wedge v0 v1 v2 v3)))`;;

let MEASURABLE_RULES = prove
 (`(!C. primitive C ==> measurable C) /\
   (!Z. NULLSET Z ==> measurable Z) /\
   (!X t. measurable X ==> (measurable (IMAGE (scale t) X))) /\
   (!X v. measurable X ==> (measurable (IMAGE ((+) v) X))) /\
   (!(s:real^3->bool) t. (measurable s /\ measurable t)
                         ==> measurable (s UNION t)) /\
   (!(s:real^3->bool) t. (measurable s /\ measurable t)
                         ==> measurable (s INTER t)) /\
   (!(s:real^3->bool) t. (measurable s /\ measurable t)
                         ==> measurable (s DIFF t))`,
  SIMP_TAC[MEASURABLE_UNION; MEASURABLE_INTER; MEASURABLE_DIFF] THEN
  REWRITE_TAC[REWRITE_RULE[ETA_AX] MEASURABLE_TRANSLATION] THEN
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_MEASURABLE_MEASURE] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`X:real^3->bool`; `t:real^3`] THEN
    REWRITE_TAC[HAS_MEASURE_MEASURE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_STRETCH) THEN
    DISCH_THEN(MP_TAC o SPEC `\i. (t:real^3)$i`) THEN
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[FUN_EQ_THM; scale; CART_EQ; LAMBDA_BETA;
             DIMINDEX_3; VECTOR_3; FORALL_3]] THEN
  X_GEN_TAC `C:real^3->bool` THEN REWRITE_TAC[primitive] THEN
  REWRITE_TAC[NORMBALL_BALL; RECT_INTERVAL] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN MP_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[solid_triangle; NORMBALL_BALL; cone0; GSYM aff_gt_def] THEN
    REWRITE_TAC[MEASURABLE_BALL_AFF_GT];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_CONV0 THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    MAP_EVERY X_GEN_TAC
     [`v0:real^3`; `v1:real^3`; `v2:real^3`; `v3:real^3`;
      `h:real`; `a:real`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_CASES_TAC `collinear {v0:real^3, v1, v2}` THENL
     [ASM_SIMP_TAC[WEDGE_DEGENERATE; INTER_EMPTY; MEASURABLE_EMPTY];
      ALL_TAC] THEN
    ASM_CASES_TAC `collinear {v0:real^3, v1, v3}` THENL
     [ASM_SIMP_TAC[WEDGE_DEGENERATE; INTER_EMPTY; MEASURABLE_EMPTY];
      ALL_TAC] THEN
    ASM_SIMP_TAC[VOLUME_FRUSTT_WEDGE];
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_INTER_OPEN THEN
    REWRITE_TAC[MEASURABLE_CONIC_CAP; BOUNDED_CONIC_CAP; OPEN_WEDGE];
    SIMP_TAC[MEASURABLE_INTERVAL];
    SIMP_TAC[MEASURABLE_ELLIPSOID];
    SIMP_TAC[MEASURABLE_BALL_WEDGE]]);;

let vol_solid_triangle = new_definition `vol_solid_triangle v0 v1 v2 v3 r =
   let a123 = dihV v0 v1 v2 v3 in
   let a231 = dihV v0 v2 v3 v1 in
   let a312 = dihV v0 v3 v1 v2 in
     (a123 + a231 + a312 - pi)*(r pow 3)/(&3)`;;

let vol_frustt_wedge = new_definition `vol_frustt_wedge v0 v1 v2 v3 h a =
       (azim v0 v1 v2 v3)*(h pow 3)*(&1/(a*a) - &1)/(&6)`;;

let vol_conic_cap_wedge = new_definition `vol_conic_cap_wedge v0 v1 v2 v3 r c =
       (azim v0 v1 v2 v3)*(&1 - c)*(r pow 3)/(&3)`;;

(*** JRH corrected delta_x x12 x13 x14 x34 x24 x34 ***)
(*** to delta_x x12 x13 x14 x34 x24 x23            ***)

let vol_conv = new_definition `vol_conv v1 v2 v3 v4 =
   let x12 = dist(v1,v2) pow 2 in
   let x13 = dist(v1,v3) pow 2 in
   let x14 = dist(v1,v4) pow 2 in
   let x23 = dist(v2,v3) pow 2 in
   let x24 = dist(v2,v4) pow 2 in
   let x34 = dist(v3,v4) pow 2 in
   sqrt(delta_x x12 x13 x14 x34 x24 x23)/(&12)`;;

let vol_rect = new_definition `vol_rect a b =
   if (a$1 < b$1) /\ (a$2 < b$2) /\ (a$3 < b$3) then
   (b$3-a$3)*(b$2-a$2)*(b$1-a$1) else &0`;;

let vol_ball_wedge = new_definition `vol_ball_wedge v0 v1 v2 v3 r =
   (azim v0 v1 v2 v3)*(&2)*(r pow 3)/(&3)`;;

let SDIFF = new_definition `SDIFF X Y = (X DIFF Y) UNION (Y DIFF X)`;;

(*** JRH added the hypothesis "measurable" to the first one ***)
(*** Could change the definition to make this hold anyway   ***)

(*** JRH changed solid triangle hypothesis to ~coplanar{...} ***)
(*** since the current condition is not enough in general    ***)

let volume_props = prove
 (`(!C. measurable C ==> vol C >= &0) /\
   (!Z. NULLSET Z ==> (vol Z = &0)) /\
   (!X Y. measurable X /\ measurable Y /\ NULLSET (SDIFF X Y)
          ==> (vol X = vol Y)) /\
   (!X t. (measurable X) /\ (measurable (IMAGE (scale t) X))
          ==> (vol (IMAGE (scale t) X) = abs(t$1 * t$2 * t$3)*vol(X))) /\
   (!X v. measurable X ==> (vol (IMAGE ((+) v) X) = vol X)) /\
   (!v0 v1 v2 v3 r. (r > &0) /\ ~coplanar{v0,v1,v2,v3}
                    ==> vol (solid_triangle v0 {v1,v2,v3} r) =
                        vol_solid_triangle v0 v1 v2 v3 r) /\
   (!v0 v1 v2 v3. vol(conv0 {v0,v1,v2,v3}) = vol_conv v0 v1 v2 v3) /\
   (!v0 v1 v2 v3 h a. ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\
                      (h >= &0) /\ (a > &0) /\ (a <= &1)
                      ==> vol(frustt v0 v1 h a INTER wedge v0 v1 v2 v3) =
                          vol_frustt_wedge v0 v1 v2 v3 h a) /\
   (!v0 v1 v2 v3 r c.  ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\
                       (r >= &0) /\ (c >= -- (&1)) /\ (c <= &1)
                       ==> (vol(conic_cap v0 v1 r c INTER wedge v0 v1 v2 v3) =
                           vol_conic_cap_wedge v0 v1 v2 v3 r c)) /\
   (!(a:real^3) (b:real^3). vol(rect a b) = vol_rect a b) /\
   (!v0 v1 v2 v3 r. ~(collinear {v0,v1,v2}) /\ ~(collinear {v0,v1,v3}) /\
                    (r >= &0)
                    ==> (vol(normball v0 r INTER wedge v0 v1 v2 v3) =
                         vol_ball_wedge v0 v1 v2 v3 r))`,
  SIMP_TAC[MEASURE_POS_LE; real_ge; real_gt] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_MEASURABLE_MEASURE];
    MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `t:real^3->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
    REWRITE_TAC[SDIFF] THEN SET_TAC[];
    MAP_EVERY X_GEN_TAC [`X:real^3->bool`; `t:real^3`] THEN
    REWRITE_TAC[HAS_MEASURE_MEASURE] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_STRETCH o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPEC `\i. (t:real^3)$i`) THEN
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[DIMINDEX_3; PRODUCT_3] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[FUN_EQ_THM; scale; CART_EQ; LAMBDA_BETA;
             DIMINDEX_3; VECTOR_3; FORALL_3];
    REWRITE_TAC[REWRITE_RULE[ETA_AX] MEASURE_TRANSLATION];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[solid_triangle; vol_solid_triangle; NORMBALL_BALL] THEN
    REWRITE_TAC[cone0; GSYM aff_gt_def] THEN
    MATCH_MP_TAC VOLUME_SOLID_TRIANGLE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[vol_conv; VOLUME_OF_TETRAHEDRON];
    SIMP_TAC[VOLUME_FRUSTT_WEDGE; vol_frustt_wedge] THEN
    SIMP_TAC[REAL_ARITH `&0 <= h ==> ~(h < &0)`] THEN
    SIMP_TAC[REAL_ARITH `a <= &1 ==> (&1 <= a <=> a = &1)`] THEN
    REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;
    SIMP_TAC[VOLUME_CONIC_CAP_WEDGE; vol_conic_cap_wedge] THEN
    SIMP_TAC[REAL_ARITH `&0 <= r ==> ~(r < &0)`] THEN
    SIMP_TAC[REAL_ARITH `c <= &1 ==> ~(&1 < c)`] THEN
    ASM_SIMP_TAC[REAL_ARITH `-- &1 <= c ==> max c (-- &1) = c`] THEN
    REPEAT STRIP_TAC THEN REAL_ARITH_TAC;
    REWRITE_TAC[vol_rect; RECT_INTERVAL; MEASURE_INTERVAL] THEN
    REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[DIMINDEX_3; FORALL_3; PRODUCT_3] THEN
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN
    REWRITE_TAC[REAL_LE_LT] THEN
    ASM_CASES_TAC `(a:real^3)$1 = (b:real^3)$1` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                    REAL_SUB_REFL; COND_ID] THEN
    ASM_CASES_TAC `(a:real^3)$2 = (b:real^3)$2` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                    REAL_SUB_REFL; COND_ID] THEN
    ASM_CASES_TAC `(a:real^3)$3 = (b:real^3)$3` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                    REAL_SUB_REFL; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_AC];
    SIMP_TAC[VOLUME_BALL_WEDGE; NORMBALL_BALL; vol_ball_wedge]]);;

(* ------------------------------------------------------------------------- *)
(* Additional results on polyhedra and relation to fans.                     *)
(* ------------------------------------------------------------------------- *)

let POLYHEDRON_COLLINEAR_FACES_STRONG = prove
 (`!P:real^N->bool f f' p q s t.
        polyhedron P /\ vec 0 IN relative_interior P /\
        f face_of P /\ ~(f = P) /\ f' face_of P /\ ~(f' = P) /\
        p IN f /\ q IN f' /\ s > &0 /\ t > &0 /\ s % p = t % q
        ==> s = t`,
  ONCE_REWRITE_TAC[MESON[]
   `(!P f f' p q s t. Q P f f' p q s t) <=>
    (!s t P f f' p q. Q P f f' p q s t)`] THEN
  MATCH_MP_TAC REAL_WLOG_LT THEN
  REWRITE_TAC[real_gt] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `(%) (inv s):real^N->real^N`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[VECTOR_MUL_LID; GSYM real_div] THEN
  ABBREV_TAC `u:real = t / s` THEN
  SUBGOAL_THEN `&0 < u /\ &1 < u` MP_TAC THENL
   [EXPAND_TAC "u" THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID];
    ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`s < t`; `&0 < s`; `&0 < t`; `t:real / s = u`] THEN
  SPEC_TAC(`u:real`,`t:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `?g:real^N->bool. g facet_of P /\ f' SUBSET g`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_POLYHEDRON_SUBSET_FACET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((vec 0:real^N) IN g)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`P:real^N->bool`; `g:real^N->bool`; `P:real^N->bool`]
                   SUBSET_OF_FACE_OF) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; NOT_IMP] THEN CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[facet_of]; ASM SET_TAC[]];
      ASM_MESON_TAC[facet_of; FACET_OF_REFL;
                    SUBSET_ANTISYM; FACE_OF_IMP_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) face_of P` MP_TAC THENL
   [ASM_MESON_TAC[facet_of]; ALL_TAC] THEN
  REWRITE_TAC[face_of] THEN DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
  DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `t % q:real^N`; `q:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    ALL_TAC] THEN
  EXPAND_TAC "p" THEN REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [CONV_TAC(RAND_CONV SYM_CONV) THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ] THEN ASM SET_TAC[];
    EXISTS_TAC `inv t:real` THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_INV_LT_1] THEN
    EXPAND_TAC "p" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC]);;

let POLYHEDRON_COLLINEAR_FACES = prove
 (`!P:real^N->bool f f' p q s t.
        polyhedron P /\ vec 0 IN interior P /\
        f face_of P /\ ~(f = P) /\ f' face_of P /\ ~(f' = P) /\
        p IN f /\ q IN f' /\ s > &0 /\ t > &0 /\ s % p = t % q
        ==> s = t`,
  MESON_TAC[POLYHEDRON_COLLINEAR_FACES_STRONG;
            INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET]);;

let vertices = new_definition
 `vertices s = {x:real^N | x extreme_point_of s}`;;

let edges = new_definition
 `edges s = {{v,w} | segment[v,w] edge_of s}`;;

let VERTICES_TRANSLATION = prove
 (`!a s. vertices (IMAGE (\x. a + x) s) = IMAGE (\x. a + x) (vertices s)`,
  REWRITE_TAC[vertices] THEN GEOM_TRANSLATE_TAC[]);;

let VERTICES_LINEAR_IMAGE = prove
 (`!f s. linear f /\ (!x y. f x = f y ==> x = y)
         ==> vertices(IMAGE f s) = IMAGE f (vertices s)`,
  REWRITE_TAC[vertices; EXTREME_POINTS_OF_LINEAR_IMAGE]);;

let EDGES_TRANSLATION = prove
 (`!a s. edges (IMAGE (\x. a + x) s) = IMAGE (IMAGE (\x. a + x)) (edges s)`,
  REWRITE_TAC[edges] THEN GEOM_TRANSLATE_TAC[] THEN SET_TAC[]);;

let EDGES_LINEAR_IMAGE = prove
 (`!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> edges(IMAGE f s) = IMAGE (IMAGE f) (edges s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[edges] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN
    SUBGOAL_THEN `?v w. x = (f:real^M->real^N) v /\ y = f w` MP_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; EDGE_OF_IMP_SUBSET; SUBSET; IN_IMAGE];
      REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC)];
    MAP_EVERY X_GEN_TAC [`v:real^M`; `w:real^M`] THEN DISCH_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(f:real^M->real^N) v`; `(f:real^M->real^N) w`]] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  ASM_MESON_TAC[EDGE_OF_LINEAR_IMAGE; CLOSED_SEGMENT_LINEAR_IMAGE]);;

add_translation_invariants [VERTICES_TRANSLATION; EDGES_TRANSLATION];;
add_linear_invariants [VERTICES_LINEAR_IMAGE; EDGES_LINEAR_IMAGE];;

(*** Correspondence with Flypaper:

Definition 4.5:   IS_AFFINE_HULL
                  affine / hull
                  aff_dim
                  AFF_DIM_EMPTY

Definition 4.6 :  IN_INTERIOR
                  IN_RELATIVE_INTERIOR
                  CLOSURE_APPROACHABLE
                  (Don't have definition of relative boundary, but several
                   theorems use closure s DIFF relative_interior s.)

Definition 4.7:   face_of
                  extreme_point_of (presumably it's meant to be the point not
                  the singleton set, which the definition literally gives)
                  facet_of
                  edge_of
                  (Don't have a definition of "proper"; I just use
                   ~(f = {}) and/or ~(f = P) as needed.)

Lemma 4.18:       KREIN_MILMAN_MINKOWSKI

Definition 4.8:   polyhedron
                  vertices

Lemma 4.19:       AFFINE_IMP_POLYHEDRON

Lemma 4.20 (i):   FACET_OF_POLYHEDRON_EXPLICIT

Lemma 4.20 (ii):  Direct consequence of RELATIVE_INTERIOR_POLYHEDRON

Lemma 4.20 (iii): FACE_OF_POLYHEDRON_EXPLICIT / FACE_OF_POLYHEDRON

Lemma 4.20 (iv):  FACE_OF_TRANS

Lemma 4.20 (v):   EXTREME_POINT_OF_FACE

Lemma 4.20 (vi):  FACE_OF_EQ

Corr. 4.7:        FACE_OF_POLYHEDRON_POLYHEDRON

Lemma 4.21:       POLYHEDRON_COLLINEAR_FACES

Def 4.9:          vertices
                  edges

****)

(* ------------------------------------------------------------------------- *)
(* Temporary backwards-compatible fix for introduction of "sphere" and       *)
(* "relative_frontier".                                                      *)
(* ------------------------------------------------------------------------- *)

let COMPACT_SPHERE =
  REWRITE_RULE[sphere; NORM_ARITH `dist(a:real^N,b) = norm(b - a)`]
  COMPACT_SPHERE;;

let FRONTIER_CBALL = REWRITE_RULE[sphere] FRONTIER_CBALL;;

let NEGLIGIBLE_SPHERE = REWRITE_RULE[sphere] NEGLIGIBLE_SPHERE;;

let RELATIVE_FRONTIER_OF_POLYHEDRON = RELATIVE_BOUNDARY_OF_POLYHEDRON;;

(* ------------------------------------------------------------------------- *)
(* Also, the finiteness hypothesis was removed from this theorem.            *)
(* Put back the old version since that might break some proofs.              *)
(* ------------------------------------------------------------------------- *)

let SUM_POS_LE = prove
 (`!f s. FINITE s /\ (!x. x IN s ==> &0 <= f(x)) ==> &0 <= sum s f`,
  REWRITE_TAC[REWRITE_RULE[SUM_0] (ISPEC `\x. &0` SUM_LE)]);;

(* ------------------------------------------------------------------------- *)
(* Also, the definition of sqrt was totalized, so keep old theorems          *)
(* that have more hypotheses than the current ones.                          *)
(* ------------------------------------------------------------------------- *)

let SQRT_MUL = prove
 (`!x y. &0 <= x /\ &0 <= y ==> sqrt(x * y) = sqrt x * sqrt y`,
  MESON_TAC[SQRT_MUL]);;

let SQRT_INV = prove
 (`!x. &0 <= x ==> (sqrt (inv x) = inv(sqrt x))`,
  MESON_TAC[SQRT_INV]);;

let SQRT_DIV = prove
 (`!x y. &0 <= x /\ &0 <= y ==> sqrt(x / y) = sqrt x / sqrt y`,
  MESON_TAC[SQRT_DIV]);;

let SQRT_LT_0 = prove
 (`!x. &0 <= x ==> (&0 < sqrt x <=> &0 < x)`,
  MESON_TAC[SQRT_LT_0]);;

let SQRT_EQ_0 = prove
 (`!x. &0 <= x ==> ((sqrt x = &0) <=> (x = &0))`,
  MESON_TAC[SQRT_EQ_0]);;

let SQRT_MONO_LT = prove
 (`!x y. &0 <= x /\ x < y ==> sqrt(x) < sqrt(y)`,
  MESON_TAC[SQRT_MONO_LT]);;

let SQRT_MONO_LE = prove
 (`!x y. &0 <= x /\ x <= y ==> sqrt(x) <= sqrt(y)`,
  MESON_TAC[SQRT_MONO_LE]);;

let SQRT_MONO_LT_EQ = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (sqrt(x) < sqrt(y) <=> x < y)`,
  MESON_TAC[SQRT_MONO_LT_EQ]);;

let SQRT_MONO_LE_EQ = prove
 (`!x y. &0 <= x /\ &0 <= y ==> (sqrt(x) <= sqrt(y) <=> x <= y)`,
  MESON_TAC[SQRT_MONO_LE_EQ]);;

let SQRT_INJ = prove
 (`!x y. &0 <= x /\ &0 <= y ==> ((sqrt(x) = sqrt(y)) <=> (x = y))`,
  MESON_TAC[SQRT_INJ]);;

let REAL_LE_LSQRT = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x <= y pow 2 ==> sqrt(x) <= y`,
  MESON_TAC[REAL_LE_LSQRT]);;

let REAL_LT_LSQRT = prove
 (`!x y. &0 <= x /\ &0 <= y /\ x < y pow 2 ==> sqrt x < y`,
  MESON_TAC[REAL_LT_LSQRT]);;

(* ------------------------------------------------------------------------- *)
(* Fix the congruence rules as expected in Flyspeck.                         *)
(* Should exclude 6 recent mixed real/vector limit results.                  *)
(* ------------------------------------------------------------------------- *)

let bcs =
  [`(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')`;
   `(g <=> g')
    ==> (g' ==> t = t')
    ==> (~g' ==> e = e')
    ==> (if g then t else e) = (if g' then t' else e')`;
   `(!x. p x ==> f x = g x) ==> nsum {y | p y} (\i. f i) = nsum {y | p y} g`;
   `(!i. a <= i /\ i <= b ==> f i = g i)
    ==> nsum (a..b) (\i. f i) = nsum (a..b) g`;
   `(!x. x IN s ==> f x = g x) ==> nsum s (\i. f i) = nsum s g`;
   `(!x. p x ==> f x = g x) ==> sum {y | p y} (\i. f i) = sum {y | p y} g`;
   `(!i. a <= i /\ i <= b ==> f i = g i)
    ==> sum (a..b) (\i. f i) = sum (a..b) g`;
   `(!x. x IN s ==> f x = g x) ==> sum s (\i. f i) = sum s g`;
   `(!x. p x ==> f x = g x) ==> vsum {y | p y} (\i. f i) = vsum {y | p y} g`;
   `(!i. a <= i /\ i <= b ==> f i = g i)
    ==> vsum (a..b) (\i. f i) = vsum (a..b) g`;
   `(!x. x IN s ==> f x = g x) ==> vsum s (\i. f i) = vsum s g`;
   `(!x. p x ==> f x = g x)
    ==> product {y | p y} (\i. f i) = product {y | p y} g`;
   `(!i. a <= i /\ i <= b ==> f i = g i)
    ==> product (a..b) (\i. f i) = product (a..b) g`;
   `(!x. x IN s ==> f x = g x) ==> product s (\i. f i) = product s g`;
   `(!x. ~(x = a) ==> f x = g x)
    ==> (((\x. f x) --> l) (at a) <=> (g --> l) (at a))`;
   `(!x. ~(x = a) ==> f x = g x)
    ==> (((\x. f x) --> l) (at a within s) <=> (g --> l) (at a within s))`]
and equiv t1 t2 = can (term_match [] t1) t2 & can (term_match [] t2) t1 in
let congs' =
  filter (fun th -> exists (equiv (concl th)) bcs) (basic_congs()) in
set_basic_congs congs';;
