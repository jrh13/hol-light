(* ========================================================================= *)
(* Formalization of Alain Connes's paper "A new proof of Morley's theorem".  *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Multivariate/geom.ml";;

(* ------------------------------------------------------------------------- *)
(* Reflection about the line[0,e^{i t}]                                      *)
(* ------------------------------------------------------------------------- *)

let reflect2d = new_definition
 `reflect2d t = rotate2d t o cnj o rotate2d(--t)`;;

let REFLECT2D_COMPOSE = prove
 (`!s t. reflect2d s o reflect2d t = rotate2d (&2 * (s - t))`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; reflect2d] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CNJ] THEN
  REWRITE_TAC[CNJ_II; CNJ_CX; CNJ_NEG; COMPLEX_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[GSYM CEXP_ADD] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; CX_MUL] THEN
  AP_TERM_TAC THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Rotation about point "a" by angle "t".                                    *)
(* ------------------------------------------------------------------------- *)

let rotate_about = new_definition
 `rotate_about a t x = a + rotate2d t (x - a)`;;

(* ------------------------------------------------------------------------- *)
(* Reflection across line (a,b).                                             *)
(* ------------------------------------------------------------------------- *)

let reflect_across = new_definition
 `reflect_across (a,b) x = a + reflect2d (Arg(b - a)) (x - a)`;;

let REFLECT_ACROSS_COMPOSE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a)
        ==> reflect_across(a,b) o reflect_across(a,c) =
            rotate_about a (&2 * Arg((b - a) / (c - a)))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[reflect_across; FUN_EQ_THM; o_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `(a + x) - a:real^N = x`] THEN
  REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM] REFLECT2D_COMPOSE] THEN
  X_GEN_TAC `x:complex` THEN AP_TERM_TAC THEN
  REWRITE_TAC[REAL_MUL_2; ROTATE2D_ADD] THEN
  ASM_SIMP_TAC[ROTATE2D_SUB_ARG; COMPLEX_SUB_0]);;

let REFLECT_ACROSS_COMPOSE_ANGLE = prove
 (`!a b c.
        ~(b = a) /\ ~(c = a) /\ &0 <= Im((c - a) / (b - a))
        ==> reflect_across(a,c) o reflect_across(a,b) =
            rotate_about a (&2 * angle(c,a,b))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[ANGLE_SYM] THEN
  ASM_SIMP_TAC[REFLECT_ACROSS_COMPOSE] THEN
  ASM_SIMP_TAC[angle; VECTOR_ANGLE_ARG; COMPLEX_SUB_0;
               REAL_SUB_ARG; ARG_LE_PI]);;

let REFLECT_ACROSS_COMPOSE_INVOLUTION = prove
 (`!a b. ~(a = b) ==> reflect_across(a,b) o reflect_across(a,b) = I`,
  SIMP_TAC[REFLECT_ACROSS_COMPOSE; COMPLEX_DIV_REFL; COMPLEX_SUB_0] THEN
  REWRITE_TAC[ARG_NUM; REAL_MUL_RZERO; rotate_about; FUN_EQ_THM] THEN
  REWRITE_TAC[ROTATE2D_ZERO; I_THM] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let REFLECT_ACROSS_SYM = prove
 (`!a b. reflect_across(a,b) = reflect_across(b,a)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a:complex = b` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FUN_EQ_THM; reflect_across; reflect2d; o_THM] THEN
  REWRITE_TAC[ROTATE2D_COMPLEX; CNJ_CEXP; CNJ_MUL; CNJ_CX; CNJ_II] THEN
  REWRITE_TAC[CX_NEG; COMPLEX_RING `--ii * --z = ii * z`] THEN
  SUBGOAL_THEN `cexp(ii * Cx(Arg(b - a))) = (b - a) / Cx(norm(b - a)) /\
                cexp(ii * Cx(Arg(a - b))) = (a - b) / Cx(norm(a - b))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(COMPLEX_FIELD
     `~(a = Cx(&0)) /\ a * b = c ==> b = c / a`) THEN
    ASM_REWRITE_TAC[GSYM ARG; CX_INJ; NORM_EQ_0; VECTOR_SUB_EQ];
    REWRITE_TAC[COMPLEX_RING `a * a * cnj b = a pow 2 * cnj b`] THEN
    SUBST1_TAC(ISPECL [`a:complex`; `b:complex`] NORM_SUB) THEN
    X_GEN_TAC `z:complex` THEN REWRITE_TAC[complex_div] THEN
    MATCH_MP_TAC(COMPLEX_RING
     `b - a = ((b - a) * n) pow 2 * (cnj za - cnj zb)
      ==> a + ((b - a) * n) pow 2 * cnj za =
          b + ((a - b) * n) pow 2 * cnj zb`) THEN
    REWRITE_TAC[CNJ_SUB; COMPLEX_RING `(z - a) - (z - b):complex = b - a`] THEN
    MATCH_MP_TAC(COMPLEX_FIELD
     `(b' - a') * (b - a) = n pow 2 /\ ~(n = Cx(&0))
      ==> b - a = ((b - a) * inv n) pow 2 * (b' - a')`) THEN
    REWRITE_TAC[GSYM CNJ_SUB; COMPLEX_MUL_CNJ; CX_INJ] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_ZERO; COMPLEX_SUB_0]]);;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

let ITER_ROTATE_ABOUT = prove
 (`!n a t. ITER n (rotate_about a t) = rotate_about a (&n * t)`,
  REWRITE_TAC[FUN_EQ_THM; rotate_about] THEN
  REWRITE_TAC[VECTOR_ARITH `a + b:real^N = a + c <=> b = c`] THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER_ALT; REAL_MUL_LZERO; ROTATE2D_ZERO] THEN
  REWRITE_TAC[VECTOR_ARITH `a + x - a:real^N = x`; GSYM REAL_OF_NUM_SUC] THEN
  ASM_REWRITE_TAC[REAL_ADD_RDISTRIB; ROTATE2D_ADD] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[rotate_about; REAL_MUL_LID] THEN VECTOR_ARITH_TAC);;

let REAL_LE_IM_DIV_CYCLIC = prove
 (`!a b c. &0 <= Im ((c - a) / (b - a)) <=> &0 <= Im((a - b) / (c - b))`,
  REWRITE_TAC[IM_COMPLEX_DIV_GE_0] THEN
  REWRITE_TAC[complex_mul; IM; IM_SUB; RE_SUB; IM_CNJ; CNJ_SUB; RE_CNJ] THEN
  REAL_ARITH_TAC);;

let ROTATE_ABOUT_INVERT = prove
 (`rotate_about a t w = z <=> w = rotate_about a (--t) z`,
  MATCH_MP_TAC(MESON[]
   `(!x. f(g x) = x) /\ (!y. g(f y) = y)
    ==> (f x = y <=> x = g y)`) THEN
  REWRITE_TAC[rotate_about; VECTOR_ADD_SUB; GSYM ROTATE2D_ADD] THEN
  REWRITE_TAC[REAL_ADD_LINV; REAL_ADD_RINV] THEN
  REWRITE_TAC[ROTATE2D_ZERO] THEN VECTOR_ARITH_TAC);;

let ROTATE_EQ_REFLECT_LEMMA = prove
 (`!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = t
        ==> rotate_about a t z = reflect_across (a,b) z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rotate_about; reflect_across] THEN
  AP_TERM_TAC THEN REWRITE_TAC[ROTATE2D_COMPLEX; reflect2d; o_THM] THEN
  REWRITE_TAC[CNJ_MUL; COMPLEX_MUL_ASSOC; CNJ_CEXP; CNJ_II] THEN
  REWRITE_TAC[CNJ_CX; COMPLEX_MUL_LNEG; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG;
              GSYM CEXP_ADD; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_RING `ii * a + ii * a = ii * Cx(&2) * a`] THEN
  ASM_CASES_TAC `z:complex = a` THEN
  ASM_REWRITE_TAC[CNJ_CX; COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
   `~(z = a)
    ==> c * (z - a) pow 2 = b * cnj (z - a) * (z - a)
        ==> c * (z - a) = b * cnj(z - a)`)) THEN
  REWRITE_TAC[COMPLEX_MUL_CNJ] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [ARG] THEN
  MATCH_MP_TAC(COMPLEX_RING
   `(e1:complex) * e2 pow 2 = e3 ==> e1 * (n * e2) pow 2 = e3 * n pow 2`) THEN
  REWRITE_TAC[GSYM CEXP_ADD; GSYM CEXP_N; CEXP_EQ] THEN
  REWRITE_TAC[COMPLEX_RING
   `ii * t + Cx(&2) * ii * z = ii * u + v * ii <=>
    t + Cx(&2) * z - u = v`] THEN
  REWRITE_TAC[GSYM CX_MUL; GSYM CX_SUB; GSYM CX_ADD; CX_INJ] THEN
  EXPAND_TAC "t" THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; GSYM REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `&2 * a = &2 * b <=> a = b`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + (b - c):real = a - (c - b)`] THEN
  ASM_SIMP_TAC[REAL_SUB_ARG; COMPLEX_SUB_0] THEN COND_CASES_TAC THENL
   [EXISTS_TAC `&0`; EXISTS_TAC `&2`] THEN
  SIMP_TAC[INTEGER_CLOSED] THEN REAL_ARITH_TAC);;

let ROTATE_EQ_REFLECT_PI_LEMMA = prove
 (`!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = &4 * pi + t
        ==> rotate_about a t z = reflect_across (a,b) z`,
  REWRITE_TAC[REAL_ARITH `a = &4 * pi + t <=> t = a + --(&4 * pi)`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `rotate_about a (&2 * Arg((b - a) / (z - a))) z` THEN
  CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA THEN ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[rotate_about; ROTATE2D_ADD] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[ROTATE2D_COMPLEX] THEN
  REWRITE_TAC[EULER; RE_MUL_II; IM_MUL_II; RE_CX; IM_CX; COS_NEG; SIN_NEG] THEN
  REWRITE_TAC[SIN_NPI; COS_NPI; REAL_EXP_NEG; REAL_EXP_0; CX_NEG] THEN
  REWRITE_TAC[COMPLEX_NEG_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[COMPLEX_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Algebraic characterization of equilateral triangle.                       *)
(* ------------------------------------------------------------------------- *)

let EQUILATERAL_TRIANGLE_ALGEBRAIC = prove
 (`!A B C j.
        j pow 3 = Cx(&1) /\ ~(j = Cx(&1)) /\
        A + j * B + j pow 2 * C = Cx(&0)
        ==> dist(A,B) = dist(B,C) /\ dist(C,A) = dist(B,C)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[dist] THEN
  SUBGOAL_THEN `C - A:complex = j * (B - C) /\ A - B = j pow 2 * (B - C)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(j pow 3) = &1` MP_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM];
    REWRITE_TAC[COMPLEX_NORM_POW; REAL_POW_EQ_1; ARITH; REAL_ABS_NORM] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The main algebraic lemma.                                                 *)
(* ------------------------------------------------------------------------- *)

let AFFINE_GROUP_ITER_3 = prove
 (`ITER 3 (\z. a * z + b) = (\z. a pow 3 * z + b * (Cx(&1) + a + a pow 2))`,
  REWRITE_TAC[TOP_DEPTH_CONV num_CONV `3`] THEN
  REWRITE_TAC[ITER; FUN_EQ_THM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC COMPLEX_RING);;

let AFFINE_GROUP_COMPOSE = prove
 (`(\z. a1 * z + b1) o (\z. a2 * z + b2) =
   (\z. (a1 * a2) * z + (b1 + a1 * b2))`,
  REWRITE_TAC[o_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;

let AFFINE_GROUP_I = prove
 (`I = (\z. Cx(&1) * z + Cx(&0))`,
  REWRITE_TAC[I_THM; FUN_EQ_THM] THEN CONV_TAC COMPLEX_RING);;

let AFFINE_GROUP_EQ = prove
 (`!a b a' b. (\z. a * z + b) = (\z. a' * z + b') <=> a = a' /\ b = b'`,
  REPEAT GEN_TAC THEN EQ_TAC THEN SIMP_TAC[FUN_EQ_THM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&1)`) THEN
  CONV_TAC COMPLEX_RING);;

let AFFINE_GROUP_ROTATE_ABOUT = prove
 (`!a t. rotate_about a t =
         (\z. cexp(ii * Cx(t)) * z + (Cx(&1) - cexp(ii * Cx(t))) * a)`,
  REWRITE_TAC[rotate_about; FUN_EQ_THM; ROTATE2D_COMPLEX] THEN
  CONV_TAC COMPLEX_RING);;

let ALGEBRAIC_LEMMA = prove
 (`!a1 a2 a3 b1 b2 b3 A B C.
        (\z. a3 * z + b3) ((\z. a1 * z + b1) B) = B /\
        (\z. a1 * z + b1) ((\z. a2 * z + b2) C) = C /\
        (\z. a2 * z + b2) ((\z. a3 * z + b3) A) = A /\
        ITER 3 (\z. a1 * z + b1) o ITER 3 (\z. a2 * z + b2) o
        ITER 3 (\z. a3 * z + b3) = I /\
        ~(a1 * a2 * a3 = Cx(&1)) /\
        ~(a1 * a2 = Cx(&1)) /\
        ~(a2 * a3 = Cx(&1)) /\
        ~(a3 * a1 = Cx(&1))
        ==> (a1 * a2 * a3) pow 3 = Cx (&1) /\
            ~(a1 * a2 * a3 = Cx (&1)) /\
            C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B = Cx(&0)`,
  REWRITE_TAC[AFFINE_GROUP_ITER_3; AFFINE_GROUP_COMPOSE; AFFINE_GROUP_I;
              AFFINE_GROUP_EQ] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(a1 * a2 * a3) * a1 pow 2 * a2 *
    (a1 - a1 * a2 * a3) * (a2 - a1 * a2 * a3) * (a3 - a1 * a2 * a3) *
    (C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B) = Cx(&0)`
  MP_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP (COMPLEX_FIELD
     `a3 * (a1 * B + b1) + b3 = B
      ==> ~(a1 * a3 = Cx(&1))
          ==> B = (a3 * b1 + b3) / (Cx(&1) - a1 * a3)`))) THEN
    REPEAT(ANTS_TAC THENL
     [ASM_MESON_TAC[COMPLEX_MUL_SYM]; DISCH_THEN SUBST1_TAC]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (COMPLEX_RING
     `s = Cx(&0) ==> s + t = Cx(&0) ==> t = Cx(&0)`));
    REWRITE_TAC[COMPLEX_ENTIRE]] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC COMPLEX_FIELD);;

(* ------------------------------------------------------------------------- *)
(* A tactic to avoid some duplication over cyclic permutations.              *)
(* ------------------------------------------------------------------------- *)

let CYCLIC_PERM_SUBGOAL_THEN =
  let lemma = MESON[]
   `(!A B C P Q R a b c g1 g2 g3.
       Ant A B C P Q R a b c g1 g2 g3 ==> Cns A B C P Q R a b c g1 g2 g3)
    ==> (!A B C P Q R a b c g1 g2 g3.
           Ant A B C P Q R a b c g1 g2 g3
           ==> Ant B C A Q R P b c a g2 g3 g1)
        ==> (!A B C P Q R a b c g1 g2 g3.
                   Ant A B C P Q R a b c g1 g2 g3
                   ==> Cns A B C P Q R a b c g1 g2 g3 /\
                       Cns B C A Q R P b c a g2 g3 g1 /\
                       Cns C A B R P Q c a b g3 g1 g2)`
  and vars =
   [`A:complex`; `B:complex`; `C:complex`;
    `P:complex`; `Q:complex`; `R:complex`;
    `a:real`; `b:real`; `c:real`;
    `g1:complex->complex`; `g2:complex->complex`; `g3:complex->complex`] in
  fun t ttac (asl,w) ->
      let asm = list_mk_conj (map (concl o snd) (rev asl)) in
      let gnw = list_mk_forall(vars,mk_imp(asm,t)) in
      let th1 = MATCH_MP lemma (ASSUME gnw) in
      let tm1 = fst(dest_imp(concl th1)) in
      let th2 = REWRITE_CONV[INSERT_AC; CONJ_ACI; ANGLE_SYM; EQ_SYM_EQ] tm1 in
      let th3 = DISCH_ALL(MP th1 (EQT_ELIM th2)) in
      (MP_TAC th3 THEN ANTS_TAC THENL
        [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC;
         DISCH_THEN(MP_TAC o SPEC_ALL) THEN ANTS_TAC THENL
          [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
           DISCH_THEN(CONJUNCTS_THEN2 ttac MP_TAC) THEN
           DISCH_THEN(CONJUNCTS_THEN ttac)]]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Morley's theorem a la Connes.                                             *)
(* ------------------------------------------------------------------------- *)

let MORLEY = prove
 (`!A B C:real^2 P Q R.
     ~collinear{A,B,C} /\ {P,Q,R} SUBSET convex hull {A,B,C} /\
     angle(A,B,R) = angle(A,B,C) / &3 /\
     angle(B,A,R) = angle(B,A,C) / &3 /\
     angle(B,C,P) = angle(B,C,A) / &3 /\
     angle(C,B,P) = angle(C,B,A) / &3 /\
     angle(C,A,Q) = angle(C,A,B) / &3 /\
     angle(A,C,Q) = angle(A,C,B) / &3
     ==> dist(R,P) = dist(P,Q) /\ dist(Q,R) = dist(P,Q)`,
  MATCH_MP_TAC(MESON[]
    `(!A B C. &0 <= Im((C - A) / (B - A)) \/
              &0 <= Im((B - A) / (C - A))) /\
     (!A B C. Property A B C ==> Property A C B) /\
     (!A B C. &0 <= Im((C - A) / (B - A)) ==> Property A B C)
     ==> !A B C. Property A B C`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM IM_COMPLEX_INV_LE_0] THEN
    REWRITE_TAC[COMPLEX_INV_DIV] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`P:real^2`; `Q:real^2`; `R:real^2`] THEN
    REWRITE_TAC[ANGLE_SYM; DIST_SYM; INSERT_AC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`P:real^2`; `R:real^2`; `Q:real^2`]) THEN
    REWRITE_TAC[ANGLE_SYM; DIST_SYM; INSERT_AC] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  MAP_EVERY (fun t ->
    ASM_CASES_TAC t THENL [ASM_REWRITE_TAC[COLLINEAR_2; INSERT_AC]; ALL_TAC])
   [`A:real^2 = B`; `A:real^2 = C`; `B:real^2 = C`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
       let th' = GEN_REWRITE_RULE I [REAL_LE_IM_DIV_CYCLIC] th in
       let th'' = GEN_REWRITE_RULE I [REAL_LE_IM_DIV_CYCLIC] th' in
       ASSUME_TAC th' THEN ASSUME_TAC th'') THEN
  ABBREV_TAC `a = angle(C:real^2,A,B) / &3` THEN
  ABBREV_TAC `b = angle(A:real^2,B,C) / &3` THEN
  ABBREV_TAC `c = angle(B:real^2,C,A) / &3` THEN
  ABBREV_TAC `g1 = rotate_about A (&2 * a)` THEN
  ABBREV_TAC `g2 = rotate_about B (&2 * b)` THEN
  ABBREV_TAC `g3 = rotate_about C (&2 * c)` THEN
  CYCLIC_PERM_SUBGOAL_THEN
    `ITER 3 g1 o ITER 3 g2 o ITER 3 g3 = (I:real^2->real^2)`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g1"; "g2"; "g3"] THEN
    REWRITE_TAC[ITER_ROTATE_ABOUT] THEN
    MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN
    REWRITE_TAC[REAL_ARITH `&3 * &2 * a / &3 = &2 * a`] THEN
    ASM_SIMP_TAC[GSYM REFLECT_ACROSS_COMPOSE_ANGLE] THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM; REFLECT_ACROSS_SYM] THEN
    ASM_SIMP_TAC[REWRITE_RULE[FUN_EQ_THM; I_THM; o_THM]
                 REFLECT_ACROSS_COMPOSE_INVOLUTION];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN `&0 <= Im((P - B) / (C - B))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ARITH `(u % A + v % B + w % C) - B:real^N =
                 u % (A - B) + w % (C - B) + ((u + v + w) - &1) % B`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; IM_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[IM_MUL_CX; COMPLEX_DIV_REFL; COMPLEX_SUB_0; IM_CX] THEN
    SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN `&0 <= Im((B - C) / (P - C))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IM_COMPLEX_INV_LE_0; COMPLEX_INV_DIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INSERT_SUBSET]) THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
    REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ARITH `(u % A + v % B + w % C) - C:real^N =
                   v % (B - C) + u % (A - C) + ((u + v + w) - &1) % C`] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    REWRITE_TAC[complex_div; COMPLEX_ADD_RDISTRIB; IM_ADD; COMPLEX_CMUL] THEN
    REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM complex_div] THEN
    ASM_SIMP_TAC[IM_MUL_CX; COMPLEX_DIV_REFL; COMPLEX_SUB_0; IM_CX] THEN
    SIMP_TAC[REAL_MUL_RZERO; REAL_ADD_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= u * --a ==> u * a <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `&0 <= --x <=> x <= &0`] THEN
    ASM_REWRITE_TAC[GSYM IM_COMPLEX_INV_GE_0; COMPLEX_INV_DIV];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `~(P:real^2 = B) /\ ~(P = C)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!x y z. ~(angle(x:real^2,y,z) / &3 = pi / &2)`
     (fun th -> ASM_MESON_TAC[th; ANGLE_REFL]) THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `a <= pi /\ &0 < pi ==> ~(a / &3 = pi / &2)`) THEN
    REWRITE_TAC[ANGLE_RANGE; PI_POS];
    ALL_TAC] THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `(g3:complex->complex)(g1(Q)) = Q`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["g1"; "g3"] THEN
    ONCE_REWRITE_TAC[ROTATE_ABOUT_INVERT] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `reflect_across(A,C) Q` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ROTATE_EQ_REFLECT_LEMMA THEN
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `angle(C:real^2,A,Q) = a`)] THEN
      REWRITE_TAC[angle] THEN ONCE_REWRITE_TAC[VECTOR_ANGLE_SYM] THEN
      ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[REFLECT_ACROSS_SYM] THEN
    MATCH_MP_TAC ROTATE_EQ_REFLECT_PI_LEMMA THEN
    ASM_REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
    REWRITE_TAC[REAL_ARITH `&2 * a = &4 * pi + &2 * --c <=>
                            a = &2 * pi - c`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
     [SYM(ASSUME `angle(B:real^2,C,A) / &3 = c`)] THEN
    ONCE_REWRITE_TAC[ANGLE_SYM] THEN FIRST_ASSUM(fun th ->
     GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [SYM th]) THEN
    REWRITE_TAC[angle] THEN
    ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM COMPLEX_INV_DIV] THEN
    MATCH_MP_TAC ARG_INV THEN REWRITE_TAC[GSYM ARG_EQ_0] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `angle(A:real^2,C,Q) = &0` MP_TAC THENL
     [REWRITE_TAC[angle] THEN ASM_SIMP_TAC[VECTOR_ANGLE_ARG; COMPLEX_SUB_0];
      ASM_REWRITE_TAC[REAL_ARITH `a / &3 = &0 <=> a = &0`]] THEN
    ASM_MESON_TAC[COLLINEAR_ANGLE; ANGLE_SYM; INSERT_AC];
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o
    GEN_REWRITE_RULE LAND_CONV [AFFINE_GROUP_ROTATE_ABOUT])) THEN
  CYCLIC_PERM_SUBGOAL_THEN
   `~(cexp(ii * Cx(&2 * a)) * cexp(ii * Cx(&2 * b)) = Cx(&1)) /\
    ~(cexp(ii * Cx(&2 * a)) * cexp(ii * Cx(&2 * b)) *
      cexp(ii * Cx(&2 * c)) = Cx(&1))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CEXP_ADD; GSYM COMPLEX_ADD_LDISTRIB; GSYM CX_ADD] THEN
    MP_TAC(REAL_ARITH
     `&0 <= a /\ &0 <= b /\ &0 <= c /\ &0 < pi /\
      &3 * a + &3 * b + &3 * c = pi /\ ~(&3 * c = pi)
      ==> (&0 < &2 * a + &2 * b /\ &2 * a + &2 * b < &2 * pi) /\
          (&0 < &2 * a + &2 * b + &2 * c /\
           &2 * a + &2 * b + &2 * c < &2 * pi)`) THEN
    ANTS_TAC THENL
     [MAP_EVERY EXPAND_TAC ["a"; "b"; "c"] THEN
      REWRITE_TAC[REAL_ARITH `&3 * x / &3 = x`; PI_POS] THEN
      SIMP_TAC[ANGLE_RANGE; REAL_LE_DIV; REAL_POS] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[TRIANGLE_ANGLE_SUM; ADD_AC; ANGLE_SYM];
        ASM_MESON_TAC[COLLINEAR_ANGLE; ANGLE_SYM; INSERT_AC]];
      MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
      REWRITE_TAC[CEXP_II_NE_1; GSYM CX_ADD]];
    ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
   [`a1 = cexp(ii * Cx(&2 * a))`;
    `a2 = cexp(ii * Cx(&2 * b))`;
    `a3 = cexp(ii * Cx(&2 * c))`;
    `b1 = (Cx (&1) - a1) * A`;
    `b2 = (Cx (&1) - a2) * B`;
    `b3 = (Cx (&1) - a3) * C`] THEN
  REPEAT DISCH_TAC THEN MATCH_MP_TAC EQUILATERAL_TRIANGLE_ALGEBRAIC THEN
  EXISTS_TAC `a1 * a2 * a3:complex` THEN
  MATCH_MP_TAC ALGEBRAIC_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`b1:complex`; `b2:complex`; `b3:complex`] THEN
  PURE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[]);;
