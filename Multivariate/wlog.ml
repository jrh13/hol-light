(* ========================================================================= *)
(* Geometric "without loss of generality" tactics to pick convenient coords. *)
(* ========================================================================= *)

needs "Multivariate/determinants.ml";;
needs "Multivariate/convex.ml";;

(* ------------------------------------------------------------------------- *)
(* Flyspeck definition of plane, and its invariance theorems.                *)
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

(* ------------------------------------------------------------------------- *)
(* Rotating and translating so a given plane in R^3 becomes {x | x$3 = &0}.  *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Apply plane rotation to a goal.                                           *)
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
(* Injection from real^2 -> real^3 plane with zero last coordinate.          *)
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
(* Rotating so a given line from the origin becomes the x-axis.              *)
(* ------------------------------------------------------------------------- *)

let ROTATION_HORIZONTAL_LINE = prove
 (`!a:real^N.
        ?b f. orthogonal_transformation f /\ det(matrix f) = &1 /\ f b = a /\
              (!k. 1 < k /\ k <= dimindex(:N) ==> b$k = &0)`,
  GEN_TAC THEN ASM_CASES_TAC `dimindex(:N) = 1` THENL
   [MAP_EVERY EXISTS_TAC [`a:real^N`; `\x:real^N. x`] THEN
    ASM_SIMP_TAC[DET_I; MATRIX_ID; ORTHOGONAL_TRANSFORMATION_ID; LTE_ANTISYM];
    EXISTS_TAC `norm(a:real^N) % (basis 1):real^N` THEN
    SIMP_TAC[VECTOR_MUL_COMPONENT; LT_IMP_LE; BASIS_COMPONENT] THEN
    SIMP_TAC[ARITH_RULE `1 < k ==> ~(k = 1)`; REAL_MUL_RZERO] THEN
    MATCH_MP_TAC ROTATION_EXISTS THEN
    SIMP_TAC[NORM_MUL; NORM_BASIS; LE_REFL; DIMINDEX_GE_1] THEN
    REWRITE_TAC[REAL_ABS_NORM; REAL_MUL_RID] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 1) /\ 1 <= n ==> 2 <= n`) THEN
    ASM_REWRITE_TAC[DIMINDEX_GE_1]]);;

let GEOM_HORIZONTAL_LINE_RULE =
  let pth = prove
   (`!f. orthogonal_transformation (f:real^N->real^N)
         ==> (vec 0 = f(vec 0) /\ {} = IMAGE f {}) /\
             ((!P. (!x. P x) <=> (!x. P (f x))) /\
              (!P. (?x. P x) <=> (?x. P (f x))) /\
              (!Q. (!s. Q s) <=> (!s. Q (IMAGE f s))) /\
              (!Q. (?s. Q s) <=> (?s. Q (IMAGE f s)))) /\
             (!P. {x | P x} = IMAGE f {x | P(f x)})`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
      MESON_TAC[LINEAR_0];
      MATCH_MP_TAC QUANTIFY_SURJECTION_THM THEN
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE]])
  and oth = prove
   (`!f:real^N->real^N.
        orthogonal_transformation f /\ det(matrix f) = &1
        ==> linear f /\
            (!x y. f x = f y ==> x = y) /\
            (!y. ?x. f x = y) /\
            (!x. norm(f x) = norm x) /\
            (2 <= dimindex(:N) ==> det(matrix f) = &1)`,
    GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[ORTHOGONAL_TRANSFORMATION_LINEAR];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_INJECTIVE];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_SURJECTIVE];
      ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]])
    and sth = prove
   (`((!k. 1 < k /\ k <= dimindex(:2) ==> b$k = &0) <=> b$2 = &0) /\
     ((!k. 1 < k /\ k <= dimindex(:3) ==> b$k = &0) <=> b$2 = &0 /\ b$3 = &0)`,
    REWRITE_TAC[DIMINDEX_2; DIMINDEX_3;
                ARITH_RULE `k <= 3 <=> k = 3 \/ k <= 2`;
                ARITH_RULE `k <= 2 <=> k = 2 \/ ~(1 < k)`] THEN
    MESON_TAC[ARITH_RULE `1 < 2 /\ 1 < 3`]) in
  let sfn = GEN_REWRITE_RULE ONCE_DEPTH_CONV [sth] in
  fun tm ->
    let x,bod = dest_forall tm in
    let th1 = EXISTS_GENVAR_RULE
     (sfn(ISPEC x ROTATION_HORIZONTAL_LINE)) in
    let [a;f],tm1 = strip_exists(concl th1) in
    let th_orth,th2 = CONJ_PAIR(ASSUME tm1) in
    let th_det,th2a = CONJ_PAIR th2 in
    let th_works,th_zero = CONJ_PAIR th2a in
    let thc,thq = CONJ_PAIR(PROVE_HYP th2 (UNDISCH(ISPEC f pth))) in
    let th3 = CONV_RULE(RAND_CONV(SUBS_CONV(GSYM th_works::CONJUNCTS thc)))
               (EXPAND_QUANTS_CONV(ASSUME(concl thq)) bod) in
    let th4 = PROVE_HYP thq th3 in
    let thps = CONJUNCTS(MATCH_MP oth (CONJ th_orth th_det)) in
    let th5 = LINEAR_INVARIANTS f thps in
    let th6 = PROVE_HYP th_orth
     (GEN_REWRITE_RULE (RAND_CONV o REDEPTH_CONV) [th5] th4) in
    let ntm = mk_forall(a,mk_imp(concl th_zero,rand(concl th6))) in
    let th7 = MP(SPEC a (ASSUME ntm)) th_zero in
    let th8 = DISCH ntm (EQ_MP (SYM th6) th7) in
    if intersect (frees(concl th8)) [a;f] = [] then
      let th9 = PROVE_HYP th1 (itlist SIMPLE_CHOOSE [a;f] th8) in
      let th10 = DISCH ntm (GEN x (UNDISCH th9)) in
      CONV_RULE(LAND_CONV (GEN_ALPHA_CONV x)) th10
    else
      let mtm = list_mk_forall([a;f],mk_imp(hd(hyp th8),rand(concl th6))) in
      let th9 = EQ_MP (SYM th6) (UNDISCH(SPECL [a;f] (ASSUME mtm))) in
      let th10 = itlist SIMPLE_CHOOSE [a;f] (DISCH mtm th9) in
      let th11 = GEN x (PROVE_HYP th1 th10) in
      MATCH_MP MONO_FORALL th11;;

let GEOM_HORIZONTAL_LINE_TAC l (asl,w as gl) =
  let avs,bod = strip_forall w
  and avs' = subtract (frees w) (freesl(map (concl o snd) asl)) in
  (MAP_EVERY X_GEN_TAC avs THEN
   MAP_EVERY (fun t -> SPEC_TAC(t,t)) (rev(subtract (avs@avs') [l])) THEN
   SPEC_TAC(l,l) THEN
   W(MATCH_MP_TAC o GEOM_HORIZONTAL_LINE_RULE o snd)) gl;;

(* ------------------------------------------------------------------------- *)
(* Drop the dimension of an (outer) universally quantified theorem.          *)
(* ------------------------------------------------------------------------- *)

let GEOM_DROP_DIMENSION_RULE =
  let oth = prove
   (`!f:real^M->real^N.
          linear f /\ (!x. norm(f x) = norm x)
          ==> linear f /\
              (!x y. f x = f y ==> x = y) /\
              (!x. norm(f x) = norm x)`,
    MESON_TAC[PRESERVES_NORM_INJECTIVE])
  and real_ty = `:real` in
  fun dth th ->
    let ath = GEN_ALL th
    and eth = MATCH_MP ISOMETRY_UNIV_UNIV dth
    and avoid = variables(concl th) in
    let f,bod = dest_exists(concl eth) in
    let lin,iso = CONJ_PAIR(ASSUME bod) in
    let newty = mk_type
     ("cart",[real_ty; fst(dest_fun_ty(type_of(rand(lhand(concl dth)))))]) in
    let modvar v = variant avoid (mk_var(fst(dest_var v),newty)) in
    let specrule th =
      let v = fst(dest_forall(concl th)) in
      try SPEC (mk_comb(f,modvar v)) th with Failure _ -> SPEC v th in
    let fth = SUBS[SYM(MATCH_MP LINEAR_0 lin)] (repeat specrule ath) in
    let thps = CONJUNCTS(MATCH_MP oth (ASSUME bod)) in
    let th5 = LINEAR_INVARIANTS f thps in
    let th6 = GEN_REWRITE_RULE REDEPTH_CONV [th5] fth in
    let th7 = PROVE_HYP eth (SIMPLE_CHOOSE f th6) in
    GENL (map modvar (fst(strip_forall(concl th)))) th7;;
