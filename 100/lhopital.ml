(* ========================================================================= *)
(* #64: L'Hopital's rule.                                                    *)
(* ========================================================================= *)

needs "Library/analysis.ml";;

override_interface ("-->",`(tends_real_real)`);;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Cauchy mean value theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let MVT2 = prove
 (`!f g a b.
        a < b /\
        (!x. a <= x /\ x <= b ==> f contl x /\ g contl x) /\
        (!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x)
        ==> ?z f' g'. a < z /\ z < b /\ (f diffl f') z /\ (g diffl g') z /\
                      (f b - f a) * g' = (g b - g a) * f'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`\x:real. f(x) * (g(b) - g(a)) - g(x) * (f(b) - f(a))`;
                `a:real`; `b:real`] MVT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONT_SUB; CONT_MUL; CONT_CONST] THEN
    X_GEN_TAC `x:real` THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    REWRITE_TAC[differentiable] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `f':real`) (X_CHOOSE_TAC `g':real`)) THEN
    EXISTS_TAC `f' * (g(b:real) - g a) - g' * (f b - f a)` THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] DIFF_CMUL; DIFF_SUB];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:real` THEN
  REWRITE_TAC[REAL_ARITH
   `(fb * (gb - ga) - gb * (fb - fa)) -
    (fa * (gb - ga) - ga * (fb - fa)) = y <=> y = &0`] THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_SUB_0; REAL_LT_IMP_NE] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `l = &0` SUBST_ALL_TAC THEN
  UNDISCH_TAC
   `!x. a < x /\ x < b ==> f differentiable x /\ g differentiable x` THEN
  DISCH_THEN(MP_TAC o SPEC `z:real`) THEN ASM_REWRITE_TAC[differentiable] THEN
  DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_TAC `f':real`) (X_CHOOSE_TAC `g':real`)) THEN
  MAP_EVERY EXISTS_TAC [`f':real`; `g':real`] THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_0] THEN
  MATCH_MP_TAC DIFF_UNIQ THEN
  EXISTS_TAC `\x:real. f(x) * (g(b) - g(a)) - g(x) * (f(b) - f(a))` THEN
  EXISTS_TAC `z:real` THEN
  ASM_SIMP_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] DIFF_CMUL; DIFF_SUB]);;

(* ------------------------------------------------------------------------- *)
(* First, assume f and g actually take value zero at c.                      *)
(* ------------------------------------------------------------------------- *)

let LHOPITAL_WEAK = prove
 (`!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        f(c) = &0 /\ g(c) = &0 /\ (f --> &0) c /\ (g --> &0) c /\
        ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `!x. &0 < abs(x - c) /\ abs(x - c) < d
        ==> ?z. &0 < abs(z - c) /\ abs(z - c) < abs(x - c) /\
                f(x) * g'(z) = f'(z) * g(x)`
  (LABEL_TAC "*") THENL
   [X_GEN_TAC `x:real` THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `&0 < abs(x - c) /\ abs(x - c) < d
      ==> c < x /\ x < c + d \/ c - d < x /\ x < c`)) THEN
    STRIP_TAC THENL
     [MP_TAC(SPECL
       [`f:real->real`; `g:real->real`; `c:real`; `x:real`] MVT2) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o funpow 2 LAND_CONV)
          [REAL_LE_LT] THEN
        ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_IMP_LE; differentiable;
          REAL_ARITH
          `c < z /\ z <= x /\ x < c + d ==> &0 < abs(z - c) /\ abs(z - c) < d`];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_RZERO] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN GEN_REWRITE_TAC (funpow 4 RAND_CONV) [REAL_MUL_SYM] THEN
      REPEAT STRIP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN
          MATCH_MP_TAC EQ_IMP THEN BINOP_TAC) THEN
        ASM_MESON_TAC[DIFF_UNIQ; REAL_ARITH
         `c < z /\ z < x /\ x < c + d ==> &0 < abs(z - c) /\ abs(z - c) < d`]];
      MP_TAC(SPECL
       [`f:real->real`; `g:real->real`; `x:real`; `c:real`] MVT2) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV o LAND_CONV o RAND_CONV)
          [REAL_LE_LT] THEN
        ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_IMP_LE; differentiable;
          REAL_ARITH
          `c - d < x /\ x <= z /\ z < c ==> &0 < abs(z - c) /\ abs(z - c) < d`];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_SUB_LZERO; REAL_MUL_LNEG; REAL_EQ_NEG2] THEN
      MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
      GEN_REWRITE_TAC (funpow 4 RAND_CONV) [REAL_MUL_SYM] THEN
      REPEAT STRIP_TAC THENL
       [ASM_REAL_ARITH_TAC;
        ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM(fun th -> MP_TAC th THEN
         MATCH_MP_TAC EQ_IMP THEN BINOP_TAC) THEN
        ASM_MESON_TAC[DIFF_UNIQ; REAL_ARITH
         `c - d < x /\ x < z /\ z < c
          ==> &0 < abs(z - c) /\ abs(z - c) < d`]]];
    ALL_TAC] THEN
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC `((\x. f' x / g' x) --> L) c` THEN REWRITE_TAC[LIM] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`d:real`; `r:real`] REAL_DOWN2) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
  UNDISCH_TAC
   `!x. &0 < abs(x - c) /\ abs(x - c) < r ==> abs(f' x / g' x - L) < e` THEN
  REMOVE_THEN "*" (MP_TAC o SPEC `x:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `z:real`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> abs(x - l) < e ==> abs(y - l) < e`) THEN
  MATCH_MP_TAC(REAL_FIELD
   `~(gz = &0) /\ ~(gx = &0) /\ fx * gz = fz * gx ==> fz / gz = fx / gx`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_TRANS]; ALL_TAC] THEN
  MP_TAC(ASSUME `&0 < abs(x - c)`) THEN DISCH_THEN(MP_TAC o MATCH_MP
   (REAL_ARITH `&0 < abs(x - c) ==> c < x \/ x < c`)) THEN
  REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`g:real->real`; `c:real`; `x:real`] ROLLE) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC (funpow 2 LAND_CONV) [REAL_LE_LT] THEN
      ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_TRANS; REAL_ARITH
       `c < z /\ z <= x /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[differentiable; REAL_LT_TRANS; REAL_ARITH
       `c < z /\ z < x /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[DIFF_UNIQ];
    MP_TAC(SPECL [`g:real->real`; `x:real`; `c:real`] ROLLE) THEN
    ASM_REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
     [GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_LE_LT] THEN
      ASM_MESON_TAC[CONTL_LIM; DIFF_CONT; REAL_LT_TRANS; REAL_ARITH
       `x <= z /\ z < c /\ z < c /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[differentiable; REAL_LT_TRANS; REAL_ARITH
       `x < z /\ z < c /\ abs(x - c) < d
        ==> &0 < abs(z - c) /\ abs(z - c) < d`];
      ALL_TAC] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[DIFF_UNIQ]]);;

(* ------------------------------------------------------------------------- *)
(* Now generalize by continuity extension.                                   *)
(* ------------------------------------------------------------------------- *)

let LHOPITAL = prove
 (`!f g f' g' c L d.
        &0 < d /\
        (!x. &0 < abs(x - c) /\ abs(x - c) < d
             ==> (f diffl f'(x)) x /\ (g diffl g'(x)) x /\ ~(g'(x) = &0)) /\
        (f --> &0) c /\ (g --> &0) c /\ ((\x. f'(x) / g'(x)) --> L) c
        ==> ((\x. f(x) / g(x)) --> L) c`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`\x:real. if x = c then &0 else f(x)`;
                `\x:real. if x = c then &0 else g(x)`;
                `f':real->real`; `g':real->real`;
                `c:real`; `L:real`; `d:real`] LHOPITAL_WEAK) THEN
  SIMP_TAC[LIM; REAL_ARITH `&0 < abs(x - c) ==> ~(x = c)`] THEN
  REWRITE_TAC[diffl] THEN STRIP_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[diffl] THENL
   [MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC `\h. (f(x + h) - f x) / h`;
    MATCH_MP_TAC LIM_TRANSFORM THEN EXISTS_TAC `\h. (g(x + h) - g x) / h`;
    ASM_MESON_TAC[]] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < abs(x - c) ==> ~(x = c)`] THEN
  REWRITE_TAC[LIM] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `abs(x - c)` THEN REWRITE_TAC[REAL_SUB_RZERO] THEN
  ASM_SIMP_TAC[REAL_ARITH
   `&0 < abs(x - c) /\ &0 < abs z /\ abs z < abs(x - c) ==> ~(x + z = c)`] THEN
  ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_NUM]);;
