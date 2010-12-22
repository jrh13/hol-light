(* ========================================================================= *)
(* Moebius functions and the classification of the biholomorphisms of the    *)
(* unit disc.                                                                *)
(*                                                                           *)
(* (c) Copyright, Gianni Ciolli, Graziano Gentili, Marco Maggesi 2009.       *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;

let moebius_function = new_definition
  `!t w z. moebius_function t w z =
           cexp (ii * Cx t) * (z - w) / (Cx(&1) - cnj w * z)`;;

let MOEBIUS_FUNCTION_EQ_ZERO = prove
  (`!t w. moebius_function t w w = Cx(&0)`,
   REWRITE_TAC [moebius_function] THEN CONV_TAC COMPLEX_FIELD);;

let MOEBIUS_FUNCTION_OF_ZERO = prove
  (`!t w. moebius_function t w (Cx(&0)) = -- cexp (ii * Cx t) * w`,
   REWRITE_TAC [moebius_function] THEN CONV_TAC COMPLEX_FIELD);;

let MOEBIUS_FUNCTION_NORM_LT_1 = prove
  (`!t w z. norm w < &1 /\ norm z < &1
            ==> norm (moebius_function t w z) < &1`,
   REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `!a. &0 <= a /\ &0 < &1 - a pow 2 ==> a < &1` MATCH_MP_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `&0 <= a` THEN
    ASM_REWRITE_TAC [REAL_FIELD `&1 - a pow 2 = (&1 - a) * (&1 + a)`;
                     REAL_MUL_POS_LT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [NORM_POS_LE] THEN
   SUBGOAL_THEN `~(Cx (&1) - cnj w * z = Cx (&0))` ASSUME_TAC THENL
   [REWRITE_TAC [COMPLEX_SUB_0] THEN
    SUBGOAL_THEN `~(norm (Cx(&1)) = norm (cnj w * z))`
     (fun th -> MESON_TAC [th]) THEN
    REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ] THEN
    MATCH_MP_TAC (REAL_ARITH `a * b < &1  ==> ~(&1 = a * b)`) THEN
    STRIP_ASSUME_TAC (NORM_ARITH `norm (z:complex) = &0 \/ &0 < norm z`) THENL
    [ASM_REWRITE_TAC [REAL_MUL_RZERO; REAL_LT_01];
     MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (z:complex)` THEN
     ASM_SIMP_TAC[REAL_LT_RMUL; REAL_MUL_LID]];
   ALL_TAC] THEN
   SUBGOAL_THEN
    `&1 - norm (moebius_function t w z) pow 2 =
     ((&1 - norm w pow 2) / (norm (Cx(&1) - cnj w * z) pow 2)) *
     (&1 - norm z pow 2)`
   SUBST1_TAC THENL
   [REWRITE_TAC [moebius_function;
                 GSYM CX_INJ; CX_SUB; CX_MUL; CX_DIV; CX_POW; CNJ_SUB; CNJ_CX;
                 CNJ_MUL; CNJ_DIV; CNJ_CNJ; COMPLEX_NORM_POW_2] THEN
    SUBGOAL_THEN
      `cnj (cexp (ii * Cx t)) * (cexp (ii * Cx t)) = Cx(&1) /\
       ~(Cx(&1) - cnj w * z = Cx(&0)) /\ ~(Cx(&1) - w * cnj z = Cx(&0))`
     MP_TAC THENL [ALL_TAC; CONV_TAC COMPLEX_FIELD] THEN
    REWRITE_TAC [CNJ_CEXP; CNJ_MUL; CNJ_II; CNJ_CX;
                  COMPLEX_MUL_LNEG; CEXP_NEG_LMUL] THEN ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `~(cnj (Cx (&1) - cnj w * z) = Cx (&0))` MP_TAC THENL
    [ASM_REWRITE_TAC [CNJ_EQ_0];
     REWRITE_TAC [CNJ_SUB; CNJ_CX; CNJ_MUL; CNJ_CNJ]];
    SUBGOAL_THEN `!u:complex. norm u < &1 ==> &0 < &1 - norm u pow 2`
      ASSUME_TAC THENL
    [REWRITE_TAC [REAL_FIELD `!a. &1 - a pow 2 = (&1 - a) * (&1 + a)`] THEN
     ASM_SIMP_TAC [REAL_LT_MUL; REAL_SUB_LT; REAL_LTE_ADD; REAL_LT_01;
                   NORM_POS_LE];
     SUBGOAL_THEN `&0 < norm (Cx (&1) - cnj w * z) pow 2`
      (fun th -> ASM_MESON_TAC [th; REAL_LT_MUL; REAL_LT_DIV]) THEN
     ASM_REWRITE_TAC [REAL_RING `!a:real. a pow 2 =  a * a`;
                      REAL_LT_SQUARE; COMPLEX_NORM_ZERO]]]);;

let MOEBIUS_FUNCTION_HOLOMORPHIC = prove
  (`!t w. norm w < &1 ==> moebius_function t w holomorphic_on ball(Cx(&0),&1)`,
   let LEMMA_1 = prove
    (`!a b:complex. norm a < &1 /\ norm b < &1 ==> ~(Cx(&1) - a * b = Cx(&0))`,
     GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_SUB_0] THEN
     SUBGOAL_THEN `~(norm (Cx(&1)) = norm (a * b))`
       (fun th -> MESON_TAC[th]) THEN
     REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL] THEN
     MATCH_MP_TAC (REAL_ARITH `!x y. y < x ==> ~(x = y)`) THEN
     ASM_CASES_TAC `b = Cx(&0)` THEN
     ASM_REWRITE_TAC [COMPLEX_NORM_NUM; REAL_MUL_RZERO; REAL_LT_01] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (b:complex)` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC [COMPLEX_NORM_NZ];
      ASM_REWRITE_TAC [REAL_MUL_LID]]) in
   REPEAT STRIP_TAC THEN
   SUBST1_TAC (GSYM (ISPEC `moebius_function t w` ETA_AX)) THEN
   REWRITE_TAC [moebius_function] THEN
   MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN  CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [o_DEF] HOLOMORPHIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `(:complex)` THEN REWRITE_TAC [HOLOMORPHIC_ON_CEXP; IN_UNIV] THEN
    SIMP_TAC [HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_CONST];
    MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
    SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_CONST;
             HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_MUL] THEN
    ASM_SIMP_TAC[COMPLEX_IN_BALL_0; LEMMA_1; COMPLEX_NORM_CNJ]]);;

(* ------------------------------------------------------------------------- *)
(* Classification of the biholomorphisms of the unit disk.                   *)
(* ------------------------------------------------------------------------- *)

let BALL_BIHOLOMORPHISM_MOEBIUS_FUNCTION = prove
  (`!f g.
      f holomorphic_on ball (Cx(&0),&1) /\
      (!z. z IN ball (Cx(&0),&1) ==> f z IN ball (Cx(&0),&1)) /\
      g holomorphic_on ball (Cx(&0),&1) /\
      (!z. z IN ball (Cx(&0),&1) ==> g z IN ball (Cx(&0),&1)) /\
      (!z. z IN ball (Cx(&0),&1) ==> f (g z) = z) /\
      (!z. z IN ball (Cx(&0),&1) ==> g (f z) = z)
      ==> ?t w. w IN ball (Cx(&0),&1) /\
                (!z. z IN ball (Cx(&0),&1) ==> f z = moebius_function t w z)`,
   let LEMMA_1 = prove
     (`!a b:complex. norm a < &1 /\ norm b < &1
                     ==> ~(Cx(&1) - a * b = Cx(&0))`,
      GEN_TAC THEN GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC [COMPLEX_SUB_0] THEN
      SUBGOAL_THEN `~(norm (Cx(&1)) = norm (a * b))`
        (fun th -> MESON_TAC[th]) THEN
      REWRITE_TAC [COMPLEX_NORM_NUM; COMPLEX_NORM_MUL] THEN
      MATCH_MP_TAC (REAL_ARITH `!x y. y < x ==> ~(x = y)`) THEN
      ASM_CASES_TAC `b = Cx(&0)` THEN
      ASM_REWRITE_TAC [COMPLEX_NORM_NUM; REAL_MUL_RZERO; REAL_LT_01] THEN
      MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `&1 * norm (b:complex)` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC [COMPLEX_NORM_NZ];
       ASM_REWRITE_TAC [REAL_MUL_LID]]) in
   let LEMMA_1_ALT = prove
     (`!a b:complex. norm a < &1 /\ norm b < &1
                     ==> ~(Cx(&1) + a * b = Cx(&0))`,
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      SUBST1_TAC (COMPLEX_RING `a : complex = -- (-- a)`) THEN
      ABBREV_TAC `u : complex= -- a` THEN
      REWRITE_TAC [COMPLEX_MUL_LNEG; GSYM complex_sub] THEN
      MATCH_MP_TAC LEMMA_1 THEN EXPAND_TAC "u" THEN
      ASM_REWRITE_TAC[NORM_NEG]) in
   let LEMMA_2 = prove
     (`!w1 w2 z.
        -- w1 = w2  /\ norm w1 < &1 /\ norm z < &1
        ==> moebius_function (&0) w1 (moebius_function (&0) w2 z) = z`,
      REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `norm (w2:complex) < &1` ASSUME_TAC THENL
      [EXPAND_TAC "w2" THEN ASM_REWRITE_TAC [NORM_NEG]; ALL_TAC] THEN
      REWRITE_TAC [moebius_function; COMPLEX_MUL_RZERO;
                   CEXP_0; COMPLEX_MUL_LID] THEN
      MATCH_MP_TAC (COMPLEX_FIELD
        `!a b c. ~(b = Cx(&0)) /\ a = b * c ==> a / b = c`) THEN
      CONJ_TAC THENL
      [ALL_TAC; MP_TAC (SPECL [`cnj w2`;`z:complex`] LEMMA_1) THEN
       ASM_REWRITE_TAC [COMPLEX_NORM_CNJ] THEN EXPAND_TAC "w2" THEN
       REWRITE_TAC [CNJ_NEG] THEN CONV_TAC COMPLEX_FIELD] THEN
      MATCH_MP_TAC (COMPLEX_FIELD
         `!a b c d. ~(d = Cx(&0)) /\ ~(d * a - b * c  = Cx(&0))
                    ==> ~(a - b * c / d  = Cx(&0))`) THEN
      ASM_SIMP_TAC [LEMMA_1; COMPLEX_NORM_CNJ] THEN
      ASM_REWRITE_TAC [COMPLEX_MUL_RID] THEN
      SUBGOAL_THEN
         `Cx(&1) - cnj w2 * z - cnj w1 * (z - w2) =
          Cx(&1) + cnj w1 * w2` SUBST1_TAC THENL
      [EXPAND_TAC "w2" THEN REWRITE_TAC [CNJ_NEG] THEN CONV_TAC COMPLEX_RING;
       ASM_SIMP_TAC [LEMMA_1_ALT; COMPLEX_NORM_CNJ]]) in
   let LEMMA_3 = prove
     (`!t w s z. norm w < &1 /\ norm z < &1
                 ==> moebius_function t w (cexp (ii * Cx s) * z) =
                     moebius_function (t + s) (cexp (-- (ii * Cx s)) * w) z`,
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[moebius_function; CX_ADD; COMPLEX_ADD_LDISTRIB; CEXP_ADD;
                  GSYM COMPLEX_MUL_ASSOC; COMPLEX_EQ_MUL_LCANCEL; CEXP_NZ;
               CNJ_MUL] THEN
      MATCH_MP_TAC (COMPLEX_FIELD
        `!a b c d e. ~(b = Cx(&0)) /\ ~(e = Cx(&0)) /\ e * a = b * c * d
                     ==> a / b = c * d / e`) THEN CONJ_TAC THENL
      [MATCH_MP_TAC LEMMA_1 THEN
       ASM_REWRITE_TAC [COMPLEX_NORM_CNJ; COMPLEX_NORM_MUL; NORM_CEXP_II;
                        REAL_MUL_LID];
       ALL_TAC] THEN
      CONJ_TAC THENL
      [REWRITE_TAC [COMPLEX_MUL_ASSOC] THEN MATCH_MP_TAC LEMMA_1 THEN
       ASM_REWRITE_TAC [COMPLEX_NORM_MUL; COMPLEX_NORM_CNJ; COMPLEX_NEG_RMUL;
                        GSYM CX_NEG; NORM_CEXP_II; REAL_MUL_LID];
       REWRITE_TAC [CNJ_CEXP; CNJ_NEG; CNJ_MUL; CNJ_II; CNJ_CX;
                    COMPLEX_MUL_LNEG; COMPLEX_NEG_NEG; CEXP_NEG] THEN
       ABBREV_TAC `a = cexp (ii * Cx s)` THEN
       SUBGOAL_THEN `inv a * a = Cx(&1)` MP_TAC THENL
       [ALL_TAC; CONV_TAC COMPLEX_RING] THEN
       MATCH_MP_TAC COMPLEX_MUL_LINV THEN EXPAND_TAC "a" THEN
       REWRITE_TAC [CEXP_NZ]]) in
   REWRITE_TAC [COMPLEX_IN_BALL_0] THEN REPEAT STRIP_TAC THEN
   ABBREV_TAC `w:complex = f (Cx(&0))` THEN
   SUBGOAL_THEN `norm(w:complex) < &1` ASSUME_TAC THENL
   [ASM_MESON_TAC [COMPLEX_NORM_NUM; REAL_LT_01]; ALL_TAC] THEN
   SUBGOAL_THEN
    `?t. !z. z IN ball (Cx(&0),&1)
             ==> moebius_function (&0) w (f z) = cexp (ii * Cx t) * z`
    STRIP_ASSUME_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `t:real` THEN EXISTS_TAC `-- (cexp(-- (ii * Cx t)) * w)` THEN
    ASM_REWRITE_TAC [NORM_NEG; COMPLEX_NORM_MUL; COMPLEX_NEG_RMUL;
                     GSYM CX_NEG; NORM_CEXP_II; REAL_MUL_LID] THEN
    GEN_TAC THEN DISCH_TAC THEN EQ_TRANS_TAC
      `moebius_function (&0) (--w)
         (moebius_function (&0) w (f (z:complex)))` THENL
    [MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC LEMMA_2 THEN
     ASM_SIMP_TAC [COMPLEX_NEG_NEG; NORM_NEG];
     ASM_SIMP_TAC[COMPLEX_IN_BALL_0] THEN ASM_SIMP_TAC[LEMMA_3; NORM_NEG] THEN
     REWRITE_TAC [REAL_ADD_LID; CX_NEG; COMPLEX_MUL_RNEG]]] THEN
   MATCH_MP_TAC SECOND_CARTAN_THM_DIM_1 THEN EXISTS_TAC
     `\z. g (moebius_function (&0) (--w) z) : complex` THEN
   REWRITE_TAC [COMPLEX_IN_BALL_0] THEN REWRITE_TAC [REAL_LT_01] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [o_DEF] HOLOMORPHIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN
    ASM_SIMP_TAC [ETA_AX; MOEBIUS_FUNCTION_HOLOMORPHIC; COMPLEX_IN_BALL_0];
    ALL_TAC] THEN CONJ_TAC THENL [ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1];
    ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REWRITE_TAC [MOEBIUS_FUNCTION_EQ_ZERO]; ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC (REWRITE_RULE [o_DEF] HOLOMORPHIC_ON_COMPOSE_GEN) THEN
    EXISTS_TAC `ball(Cx(&0),&1)` THEN
    ASM_SIMP_TAC [COMPLEX_IN_BALL_0; MOEBIUS_FUNCTION_NORM_LT_1;
                  NORM_NEG] THEN
    ASM_SIMP_TAC [ETA_AX; MOEBIUS_FUNCTION_HOLOMORPHIC; NORM_NEG];
    ALL_TAC] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1; NORM_NEG]; ALL_TAC] THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC [MOEBIUS_FUNCTION_OF_ZERO; COMPLEX_MUL_RZERO; CEXP_0;
                     GSYM COMPLEX_NEG_LMUL; COMPLEX_MUL_LID;
                      COMPLEX_NEG_NEG] THEN
    ASM_MESON_TAC [COMPLEX_NORM_0; REAL_LT_01];
    ALL_TAC] THEN CONJ_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC [REWRITE_RULE [COMPLEX_NEG_NEG; NORM_NEG]
                  (SPECL [`--w:complex`;`w:complex`] LEMMA_2)]] THEN
    REPEAT STRIP_TAC THEN SUBGOAL_THEN
     `f (g (moebius_function (&0) (--w) z) : complex) =
      (moebius_function (&0) (--w) z)`
     SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_SIMP_TAC [MOEBIUS_FUNCTION_NORM_LT_1; NORM_NEG];
    MATCH_MP_TAC LEMMA_2 THEN ASM_REWRITE_TAC []]);;
