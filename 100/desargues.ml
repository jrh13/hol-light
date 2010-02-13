(* ========================================================================= *)
(* #87: Desargues's theorem.                                                 *)
(* ========================================================================= *)

needs "Multivariate/cross.ml";;

(* ------------------------------------------------------------------------- *)
(* A lemma we want to justify some of the axioms.                            *)
(* ------------------------------------------------------------------------- *)

let NORMAL_EXISTS = prove
 (`!u v:real^3. ?w. ~(w = vec 0) /\ orthogonal u w /\ orthogonal v w`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ORTHOGONAL_SYM] THEN
  MP_TAC(ISPEC `{u:real^3,v}` ORTHOGONAL_TO_SUBSPACE_EXISTS) THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; DIMINDEX_3] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `CARD {u:real^3,v}` THEN CONJ_TAC THEN
  SIMP_TAC[DIM_LE_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type of directions.                                                       *)
(* ------------------------------------------------------------------------- *)

let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir")
 (MESON[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] `?x:real^3. ~(x = vec 0)`);;

parse_as_infix("||",(11,"right"));;
parse_as_infix("_|_",(11,"right"));;

let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;

let pardir = new_definition
 `x || y <=> (dest_dir x) cross (dest_dir y) = vec 0`;;

let DIRECTION_CLAUSES = prove
 (`((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`,
  MESON_TAC[direction_tybij]);;

let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let PARDIR_EQUIV = prove
 (`!x y. ((||) x = (||) y) <=> x || y`,
  REWRITE_TAC[FUN_EQ_THM] THEN
  MESON_TAC[PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS]);;

let DIRECTION_AXIOM_1 = prove
 (`!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p:real^3`; `p':real^3`] NORMAL_EXISTS) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;

let DIRECTION_AXIOM_2 = prove
 (`!l l'. ?p. p _|_ l /\ p _|_ l'`,
  REWRITE_TAC[perpdir; DIRECTION_CLAUSES] THEN
  MESON_TAC[NORMAL_EXISTS; ORTHOGONAL_SYM]);;

let DIRECTION_AXIOM_3 = prove
 (`?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN MAP_EVERY
   (fun t -> EXISTS_TAC t THEN SIMP_TAC[BASIS_NONZERO; DIMINDEX_3; ARITH])
   [`basis 1 :real^3`; `basis 2 : real^3`; `basis 3 :real^3`] THEN
  VEC3_TAC);;

let DIRECTION_AXIOM_4_WEAK = prove
 (`!l. ?p p'. ~(p || p') /\ p _|_ l /\ p' _|_ l`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 2) l /\
    ~((l cross basis 1) cross (l cross basis 2) = vec 0) \/
    orthogonal (l cross basis 1) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 1) cross (l cross basis 3) = vec 0) \/
    orthogonal (l cross basis 2) l /\ orthogonal (l cross basis 3) l /\
    ~((l cross basis 2) cross (l cross basis 3) = vec 0)`
  MP_TAC THENL [POP_ASSUM MP_TAC THEN VEC3_TAC; MESON_TAC[CROSS_0]]);;

let ORTHOGONAL_COMBINE = prove
 (`!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)`,
  REWRITE_TAC[DIRECTION_CLAUSES; pardir; perpdir] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `a + b:real^3` THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN VEC3_TAC);;

let DIRECTION_AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l`,
  MESON_TAC[DIRECTION_AXIOM_4_WEAK; ORTHOGONAL_COMBINE]);;

let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;

let PERPDIR_WELLDEF = prove
 (`!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`,
  REWRITE_TAC[perpdir; pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;

let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;

let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;

let point_tybij = new_type_definition "point" ("mk_point","dest_point")
 (prove(`?x:line. T`,REWRITE_TAC[]));;

parse_as_infix("on",(11,"right"));;

let on = new_definition `p on l <=> perpl (dest_point p) l`;;

let POINT_CLAUSES = prove
 (`((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))`,
  MESON_TAC[point_tybij]);;

let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;

let AXIOM_1 = prove
 (`!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)`,
  POINT_TAC LINE_AXIOM_1);;

let AXIOM_2 = prove
 (`!l l'. ?p. p on l /\ p on l'`,
  POINT_TAC LINE_AXIOM_2);;

let AXIOM_3 = prove
 (`?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)`,
  POINT_TAC LINE_AXIOM_3);;

let AXIOM_4 = prove
 (`!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`,
  POINT_TAC LINE_AXIOM_4);;

(* ------------------------------------------------------------------------- *)
(* Mappings from vectors in R^3 to projective lines and points.              *)
(* ------------------------------------------------------------------------- *)

let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`;;

let projp = new_definition
 `projp x = mk_point(projl x)`;;

(* ------------------------------------------------------------------------- *)
(* Mappings in the other direction, to (some) homogeneous coordinates.       *)
(* ------------------------------------------------------------------------- *)

let PROJL_TOTAL = prove
 (`!l. ?x. ~(x = vec 0) /\ l = projl x`,
  GEN_TAC THEN
  SUBGOAL_THEN `?d. l = mk_line((||) d)` (CHOOSE_THEN SUBST1_TAC) THENL
   [MESON_TAC[fst line_tybij; snd line_tybij];
    REWRITE_TAC[projl] THEN EXISTS_TAC `dest_dir d` THEN
    MESON_TAC[direction_tybij]]);;

let homol = new_specification ["homol"]
  (REWRITE_RULE[SKOLEM_THM] PROJL_TOTAL);;

let PROJP_TOTAL = prove
 (`!p. ?x. ~(x = vec 0) /\ p = projp x`,
  REWRITE_TAC[projp] THEN MESON_TAC[PROJL_TOTAL; point_tybij]);;

let homop_def = new_definition
 `homop p = homol(dest_point p)`;;

let homop = prove
 (`!p. ~(homop p = vec 0) /\ p = projp(homop p)`,
  GEN_TAC THEN REWRITE_TAC[homop_def; projp; MESON[point_tybij]
   `p = mk_point l <=> dest_point p = l`] THEN
  MATCH_ACCEPT_TAC homol);;

(* ------------------------------------------------------------------------- *)
(* Key equivalences of concepts in projective space and homogeneous coords.  *)
(* ------------------------------------------------------------------------- *)

let parallel = new_definition
 `parallel x y <=> x cross y = vec 0`;;

let ON_HOMOL = prove
 (`!p l. p on l <=> orthogonal (homop p) (homol l)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [homop; homol] THEN
  REWRITE_TAC[on; projp; projl; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[GSYM perpl_th; perpdir] THEN BINOP_TAC THEN
  MESON_TAC[homol; homop; direction_tybij]);;

let EQ_HOMOL = prove
 (`!l l'. l = l' <=> parallel (homol l) (homol l')`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINOP_CONV) [homol] THEN
  REWRITE_TAC[projl; MESON[fst line_tybij; snd line_tybij]
   `mk_line((||) l) = mk_line((||) l') <=> (||) l = (||) l'`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir; parallel] THEN
  MESON_TAC[homol; direction_tybij]);;

let EQ_HOMOP = prove
 (`!p p'. p = p' <=> parallel (homop p) (homop p')`,
  REWRITE_TAC[homop_def; GSYM EQ_HOMOL] THEN
  MESON_TAC[point_tybij]);;

(* ------------------------------------------------------------------------- *)
(* A "welldefinedness" result for homogeneous coordinate map.                *)
(* ------------------------------------------------------------------------- *)

let PARALLEL_PROJL_HOMOL = prove
 (`!x. parallel x (homol(projl x))`,
  GEN_TAC THEN REWRITE_TAC[parallel] THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[CROSS_0] THEN MP_TAC(ISPEC `projl x` homol) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [projl] THEN
  DISCH_THEN(MP_TAC o AP_TERM `dest_line`) THEN
  REWRITE_TAC[MESON[fst line_tybij; snd line_tybij]
   `dest_line(mk_line((||) l)) = (||) l`] THEN
  REWRITE_TAC[PARDIR_EQUIV] THEN REWRITE_TAC[pardir] THEN
  ASM_MESON_TAC[direction_tybij]);;

let PARALLEL_PROJP_HOMOP = prove
 (`!x. parallel x (homop(projp x))`,
  REWRITE_TAC[homop_def; projp; REWRITE_RULE[] point_tybij] THEN
  REWRITE_TAC[PARALLEL_PROJL_HOMOL]);;

let PARALLEL_PROJP_HOMOP_EXPLICIT = prove
 (`!x. ~(x = vec 0) ==> ?a. ~(a = &0) /\ homop(projp x) = a % x`,
  MP_TAC PARALLEL_PROJP_HOMOP THEN MATCH_MP_TAC MONO_FORALL THEN
  REWRITE_TAC[parallel; CROSS_EQ_0; COLLINEAR_LEMMA] THEN
  GEN_TAC THEN ASM_CASES_TAC `x:real^3 = vec 0` THEN
  ASM_REWRITE_TAC[homop] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `c:real` THEN ASM_CASES_TAC `c = &0` THEN
  ASM_REWRITE_TAC[homop; VECTOR_MUL_LZERO]);;

(* ------------------------------------------------------------------------- *)
(* Brackets, collinearity and their connection.                              *)
(* ------------------------------------------------------------------------- *)

let bracket = define
 `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`;;

let COLLINEAR = new_definition
 `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`;;

let COLLINEAR_SINGLETON = prove
 (`!a. COLLINEAR {a}`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[AXIOM_1; AXIOM_3]);;

let COLLINEAR_PAIR = prove
 (`!a b. COLLINEAR{a,b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:point = b` THEN
  ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_SINGLETON] THEN
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[AXIOM_1]);;

let COLLINEAR_TRIPLE = prove
 (`!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`,
  REWRITE_TAC[COLLINEAR; FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let COLLINEAR_BRACKET = prove
 (`!p1 p2 p3. COLLINEAR {p1,p2,p3} <=> bracket[p1;p2;p3] = &0`,
  let lemma = prove
   (`!a b c x y.
          x cross y = vec 0 /\ ~(x = vec 0) /\
          orthogonal a x /\ orthogonal b x /\ orthogonal c x
          ==> orthogonal a y /\ orthogonal b y /\ orthogonal c y`,
    REWRITE_TAC[orthogonal] THEN VEC3_TAC) in
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[COLLINEAR_TRIPLE; bracket; ON_HOMOL; LEFT_IMP_EXISTS_THM] THEN
    MP_TAC homol THEN MATCH_MP_TAC MONO_FORALL THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    REWRITE_TAC[DET_3; orthogonal; DOT_3; VECTOR_3; CART_EQ;
              DIMINDEX_3; FORALL_3; VEC_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ASM_CASES_TAC `p1:point = p2` THENL
     [ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_PAIR]; ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC[parallel; COLLINEAR_TRIPLE; bracket; EQ_HOMOP; ON_HOMOL] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `mk_line((||) (mk_dir(homop p1 cross homop p2)))` THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `homop p1 cross homop p2` THEN
    ASM_REWRITE_TAC[ORTHOGONAL_CROSS] THEN
    REWRITE_TAC[orthogonal] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ONCE_REWRITE_TAC[CROSS_TRIPLE] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
    ASM_REWRITE_TAC[DOT_CROSS_DET] THEN
    REWRITE_TAC[GSYM projl; GSYM parallel; PARALLEL_PROJL_HOMOL]]);;

(* ------------------------------------------------------------------------- *)
(* Rather crude shuffling of bracket triple into canonical order.            *)
(* ------------------------------------------------------------------------- *)

let BRACKET_SWAP,BRACKET_SHUFFLE = (CONJ_PAIR o prove)
 (`bracket[x;y;z] = --bracket[x;z;y] /\
   bracket[x;y;z] = bracket[y;z;x] /\
   bracket[x;y;z] = bracket[z;x;y]`,
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;

let BRACKET_SWAP_CONV =
  let conv = GEN_REWRITE_CONV I [BRACKET_SWAP] in
  fun tm -> let th = conv tm in
            let tm' = rand(rand(concl th)) in
            if term_order tm tm' then th else failwith "BRACKET_SWAP_CONV";;

(* ------------------------------------------------------------------------- *)
(* Direct proof following Richter-Gebert's "Meditations on Ceva's Theorem",  *)
(* except for a change of variable names. The degenerate conditions here are *)
(* just those that naturally get used in the proof.                          *)
(* ------------------------------------------------------------------------- *)

let DESARGUES_DIRECT = prove
 (`~COLLINEAR {A',B,S} /\
   ~COLLINEAR {A,P,C} /\
   ~COLLINEAR {A,P,R} /\
   ~COLLINEAR {A,C,B} /\
   ~COLLINEAR {A,B,R} /\
   ~COLLINEAR {C',P,A'} /\
   ~COLLINEAR {C',P,B} /\
   ~COLLINEAR {C',P,B'} /\
   ~COLLINEAR {C',A',S} /\
   ~COLLINEAR {C',A',B'} /\
   ~COLLINEAR {P,C,A'} /\
   ~COLLINEAR {P,C,B} /\
   ~COLLINEAR {P,A',R} /\
   ~COLLINEAR {P,B,Q} /\
   ~COLLINEAR {P,Q,B'} /\
   ~COLLINEAR {C,B,S} /\
   ~COLLINEAR {A',Q,B'}
   ==> COLLINEAR {P,A',A} /\
       COLLINEAR {P,B,B'} /\
       COLLINEAR {P,C',C} /\
       COLLINEAR {B,C,Q} /\
       COLLINEAR {B',C',Q} /\
       COLLINEAR {A,R,C} /\
       COLLINEAR {A',C',R} /\
       COLLINEAR {B,S,A} /\
       COLLINEAR {A',S,B'}
       ==> COLLINEAR {Q,S,R}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COLLINEAR_BRACKET] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(bracket[P;A';A] = &0
     ==> bracket[P;A';R] * bracket[P;A;C] =
         bracket[P;A';C] * bracket[P;A;R]) /\
    (bracket[P;B;B'] = &0
     ==> bracket[P;B;Q] * bracket[P;B';C'] =
         bracket[P;B;C'] * bracket[P;B';Q]) /\
    (bracket[P;C';C] = &0
     ==> bracket[P;C';B] * bracket[P;C;A'] =
         bracket[P;C';A'] * bracket[P;C;B]) /\
    (bracket[B;C;Q] = &0
     ==> bracket[B;C;P] * bracket[B;Q;S] =
         bracket[B;C;S] * bracket[B;Q;P]) /\
    (bracket[B';C';Q] = &0
     ==> bracket[B';C';A'] * bracket[B';Q;P] =
         bracket[B';C';P] * bracket[B';Q;A']) /\
    (bracket[A;R;C] = &0
     ==> bracket[A;R;P] * bracket[A;C;B] =
         bracket[A;R;B] * bracket[A;C;P]) /\
    (bracket[A';C';R] = &0
     ==> bracket[A';C';P] * bracket[A';R;S] =
         bracket[A';C';S] * bracket[A';R;P]) /\
    (bracket[B;S;A] = &0
     ==> bracket[B;S;C] * bracket[B;A;R] =
         bracket[B;S;R] * bracket[B;A;C]) /\
    (bracket[A';S;B'] = &0
     ==> bracket[A';S;C'] * bracket[A';B';Q] =
         bracket[A';S;Q] * bracket[A';B';C'])`
  MP_TAC THENL
   [REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC(TAUT
   `(c ==> d ==> b ==> e) ==> ((a ==> b) /\ c ==> a /\ d ==> e)`)) THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  REPEAT(ONCE_REWRITE_TAC[IMP_IMP] THEN
         DISCH_THEN(MP_TAC o MATCH_MP (REAL_RING
          `a = b /\ x:real = y ==> a * x = b * y`))) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[BRACKET_SHUFFLE] THEN
  CONV_TAC(ONCE_DEPTH_CONV BRACKET_SWAP_CONV) THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LNEG; REAL_MUL_RNEG] THEN
  REWRITE_TAC[REAL_NEG_NEG; REAL_NEG_EQ_0] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `!b. (a ==> b) /\ (b ==> c) ==> a ==> c`) THEN
  EXISTS_TAC `bracket[B;Q;S] * bracket[A';R;S] =
              bracket[B;R;S] * bracket[A';Q;S]` THEN
  CONJ_TAC THENL [POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;
