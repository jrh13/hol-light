(* ========================================================================= *)
(* Taylor expansion, residues on circles and the interpolation bound.        *)
(*                                                                           *)
(* Purpose: complex analysis for the Baker method: Taylor expansion of a     *)
(* holomorphic function with holomorphic remainder; a residue theorem on a   *)
(* circle for f / prod_a (z - a)^(m a) via principal parts; the              *)
(* interpolation identity of Baker (Transcendental Number Theory, Ch. 3,     *)
(* eq. (8)) for nodes of multiplicity t + 1 and an extra simple node w; and  *)
(* the resulting upper bound for norm(f w): length bound on the big circle,  *)
(* Cauchy inequalities on small circles around the nodes.                    *)
(*                                                                           *)
(* Main results: INTERPOLATION_RESIDUE_BOUND (the bound for norm(f w)),      *)
(*   INTERPOLATION_RESIDUE_CIRCLEPATH (the identity),                        *)
(*   RESIDUE_CPRODUCT_CIRCLEPATH, RESIDUE_PRINCIPAL_PARTS_CIRCLEPATH,        *)
(*   HOLOMORPHIC_TAYLOR_EXPANSION, HIGHER_COMPLEX_DERIVATIVE_MUL_DIV_FACT    *)
(*   (Leibniz rule).                                                         *)
(*                                                                           *)
(* Uses: Baker/algebraic.ml (CPRODUCT_DELETE), Baker/delta.ml                *)
(*   (HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR).                             *)
(* ========================================================================= *)

needs "Baker/delta.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Taylor expansion of a holomorphic function with holomorphic remainder.    *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_DIVIDED_DIFFERENCE = prove
 (`!f s a. open s /\ f holomorphic_on s
           ==> ?g. g holomorphic_on s /\
                   !z. z IN s ==> f z = f a + (z - a) * g z`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\z. if z = a then complex_derivative f a
                  else (f z - f a) / (z - a)` THEN
  ASM_SIMP_TAC[POLE_LEMMA_OPEN] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
  UNDISCH_TAC `~(z:complex = a)` THEN CONV_TAC COMPLEX_FIELD);;

let HIGHER_COMPLEX_DERIVATIVE_DIVIDED_DIFFERENCE = prove
 (`!g s c a n.
        open s /\ g holomorphic_on s /\ a IN s
        ==> higher_complex_derivative (SUC n) (\z. c + (z - a) * g z) a =
            Cx(&(SUC n)) * higher_complex_derivative n g a`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\z:complex. c:complex`;
                 `\z. (z - a) * (g:complex->complex) z`; `s:complex->bool`;
                 `SUC n`; `a:complex`] HIGHER_COMPLEX_DERIVATIVE_ADD) THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_MUL; HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID;
               HOLOMORPHIC_ON_CONST] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`g:complex->complex`; `s:complex->bool`; `a:complex`;
                 `n:num`; `a:complex`]
         HIGHER_COMPLEX_DERIVATIVE_MUL_SUB_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[HIGHER_COMPLEX_DERIVATIVE_CONST; NOT_SUC] THEN
  CONV_TAC COMPLEX_RING);;

let HOLOMORPHIC_TAYLOR_EXPANSION = prove
 (`!f s a n.
        open s /\ f holomorphic_on s /\ a IN s
        ==> ?g. g holomorphic_on s /\
                !z. z IN s
                    ==> f z = vsum(0..n) (\j. higher_complex_derivative j f a /
                                              Cx(&(FACT j)) * (z - a) pow j) +
                              (z - a) pow (n + 1) * g z`,
  REPEAT GEN_TAC THEN
  SPEC_TAC(`f:complex->complex`,`f:complex->complex`) THEN
  SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN X_GEN_TAC `f:complex->complex` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`; `a:complex`]
         HOLOMORPHIC_DIVIDED_DIFFERENCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:complex->complex` STRIP_ASSUME_TAC) THENL
   [EXISTS_TAC `h:complex->complex` THEN
    ASM_REWRITE_TAC[VSUM_SING_NUMSEG; higher_complex_derivative; FACT;
                    complex_pow; COMPLEX_DIV_1; COMPLEX_MUL_RID; ADD_CLAUSES;
                    COMPLEX_POW_1];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:complex->complex`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:complex->complex` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!j. higher_complex_derivative (SUC j) f a =
        Cx(&(SUC j)) * higher_complex_derivative j h a`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    TRANS_TAC EQ_TRANS
     `higher_complex_derivative (SUC j) (\z. f a + (z - a) * h z) a` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_ADD THEN
      REWRITE_TAC[HOLOMORPHIC_ON_CONST] THEN
      MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST];
      MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_DIVIDED_DIFFERENCE THEN
      EXISTS_TAC `s:complex->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `f z = f a + (z - a) * h z /\
    h z = vsum(0..n) (\j. higher_complex_derivative j h a /
                          Cx(&(FACT j)) * (z - a) pow j) +
          (z - a) pow (n + 1) * g z`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum(0..SUC n) (\j. higher_complex_derivative j f a / Cx(&(FACT j)) *
                        (z - a) pow j) =
    f a + (z - a) * vsum(0..n) (\j. higher_complex_derivative j h a /
                                    Cx(&(FACT j)) * (z - a) pow j)`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATCH_MP VSUM_CLAUSES_LEFT (SPEC `SUC n` LE_0)] THEN
    REWRITE_TAC[ADD1; VSUM_OFFSET] THEN
    REWRITE_TAC[higher_complex_derivative; FACT; complex_pow; COMPLEX_DIV_1;
                COMPLEX_MUL_RID] THEN
    AP_TERM_TAC THEN SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[GSYM ADD1; FACT; complex_pow; GSYM REAL_OF_NUM_MUL;
                    CX_MUL] THEN
    MP_TAC(SPEC `j:num` FACT_NZ) THEN
    MP_TAC(SPEC `j:num` NOT_SUC) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN CONV_TAC COMPLEX_FIELD;
    REWRITE_TAC[ADD_CLAUSES; complex_pow] THEN CONV_TAC COMPLEX_RING]);;

(* ------------------------------------------------------------------------- *)
(* Dividing a polynomial in w of degree < n by w^n.                          *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POW_DIV_POW_INV = prove
 (`!w j n. ~(w = Cx(&0)) /\ j <= n ==> w pow j / w pow n = inv(w) pow (n - j)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[COMPLEX_DIV_POW2; COMPLEX_POW_INV] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `j - n = 0 /\ n - j = 0`
   (fun th -> REWRITE_TAC[th; complex_pow; COMPLEX_INV_1]) THEN
  ASM_ARITH_TAC);;

let VSUM_POW_DIV_POW = prove
 (`!c w n. ~(w = Cx(&0))
           ==> vsum(0..n-1) (\j. c j * w pow j) / w pow n =
               vsum(0..n-1) (\j. c j * inv(w) pow (n - j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_div] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM complex_div] THEN MATCH_MP_TAC COMPLEX_POW_DIV_POW_INV THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local holomorphy, points inside a circle, and the integral of a           *)
(* principal part sum_j q(j) / (z - a)^(n - j) over a circle around a.       *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_LOCALLY_EQ = prove
 (`!f s. open s /\
         (!z. z IN s ==> ?t g. open t /\ z IN t /\ g holomorphic_on t /\
                               !w. w IN t ==> g w = f w)
         ==> f holomorphic_on s`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_OPEN; GSYM complex_differentiable] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:complex->bool`
   (X_CHOOSE_THEN `g:complex->complex` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `t:complex->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[SUBSET; IN_BALL] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`g:complex->complex`; `e:real`] THEN
  ASM_MESON_TAC[HOLOMORPHIC_ON_IMP_DIFFERENTIABLE_AT; DIST_SYM]);;

let NOT_IN_PATH_IMAGE_CIRCLEPATH = prove
 (`!a c r. norm(a - c) < r ==> ~(a IN path_image(circlepath(c,r)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (r:real)` (fun th -> SIMP_TAC[th; PATH_IMAGE_CIRCLEPATH])
  THENL
   [MP_TAC(ISPEC `a - c:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_SPHERE; dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_REAL_ARITH_TAC]);;

let HOLOMORPHIC_ON_PRINCIPAL_PART = prove
 (`!q a n k t.
        ~(a IN t)
        ==> (\z. vsum(0..n) (\j. q j * inv(z - a) pow k j)) holomorphic_on t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_LMUL THEN MATCH_MP_TAC HOLOMORPHIC_ON_POW THEN
  MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN
  SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
  REWRITE_TAC[COMPLEX_SUB_0] THEN ASM_MESON_TAC[]);;

let HAS_PATH_INTEGRAL_PRINCIPAL_PART_CIRCLEPATH = prove
 (`!q a n c r.
        norm(a - c) < r /\ 1 <= n
        ==> ((\z. vsum(0..n-1) (\j. q j * inv(z - a) pow (n - j)))
             has_path_integral (Cx(&2) * Cx pi * ii * q(n - 1)))
            (circlepath(c,r))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `Cx(&2) * Cx pi * ii * q(n - 1) =
    vsum(0..n-1) (\j. q j * (if n - j = 1
                             then Cx(&2) * Cx pi * ii *
                                  winding_number(circlepath(c,r),a)
                             else Cx(&0)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[WINDING_NUMBER_CIRCLEPATH; COMPLEX_MUL_RID] THEN
    TRANS_TAC EQ_TRANS
     `vsum(0..n-1) (\j. if j = n - 1 then Cx(&2) * Cx pi * ii * q(n - 1)
                        else vec 0)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VSUM_DELTA; IN_NUMSEG; LE_0; LE_REFL];
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[ARITH_RULE
       `1 <= n /\ j <= n - 1 ==> (n - j = 1 <=> j = n - 1)`] THEN
      COND_CASES_TAC THEN
      ASM_REWRITE_TAC[COMPLEX_VEC_0; COMPLEX_MUL_RZERO] THEN
      REWRITE_TAC[COMPLEX_MUL_AC]];
    MATCH_MP_TAC HAS_PATH_INTEGRAL_VSUM THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_PATH_INTEGRAL_COMPLEX_LMUL THEN
    MATCH_MP_TAC HAS_RESIDUE_INTEGRAL THEN
    ASM_SIMP_TAC[VALID_PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH;
                 PATHFINISH_CIRCLEPATH; NOT_IN_PATH_IMAGE_CIRCLEPATH]]);;

(* ------------------------------------------------------------------------- *)
(* Residue theorem on a circle: if h is holomorphic off the finite set s     *)
(* inside the circle and h - R(a) extends holomorphically near each a in s,  *)
(* then the integral of h is the sum of the integrals of the R(a).           *)
(* ------------------------------------------------------------------------- *)

let RESIDUE_SINGULAR_PARTS_CIRCLEPATH = prove
 (`!h R i s c r.
        FINITE s /\ (!a. a IN s ==> norm(a - c) < r) /\
        h holomorphic_on ((:complex) DIFF s) /\
        (!a. a IN s
             ==> R a holomorphic_on ((:complex) DELETE a) /\
                 (R a has_path_integral i a) (circlepath(c,r))) /\
        (!a. a IN s
             ==> ?g. g holomorphic_on ((:complex) DIFF (s DELETE a)) /\
                     !z. ~(z IN s) ==> h z = R a z + g z)
        ==> (h has_path_integral vsum s i) (circlepath(c,r))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `g:complex->complex->complex`))))) THEN
  SUBGOAL_THEN
   `!b u. b IN s /\ ~(b IN u)
          ==> (R:complex->complex->complex) b holomorphic_on u`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `(:complex) DELETE b` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. if z IN s
         then (g:complex->complex->complex) z z -
              vsum (s DELETE z) (\b. (R:complex->complex->complex) b z)
         else (h:complex->complex) z - vsum s (\b. R b z))
    holomorphic_on (:complex)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_LOCALLY_EQ THEN
    REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    X_GEN_TAC `a:complex` THEN ASM_CASES_TAC `(a:complex) IN s` THENL
     [MAP_EVERY EXISTS_TAC
       [`(:complex) DIFF (s DELETE a)`;
        `\z. (g:complex->complex->complex) a z -
             vsum (s DELETE a) (\b. (R:complex->complex->complex) b z)`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN
        ASM_SIMP_TAC[OPEN_UNIV; FINITE_IMP_CLOSED; FINITE_DELETE];
        REWRITE_TAC[IN_DIFF; IN_UNIV; IN_DELETE];
        MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN CONJ_TAC THENL
         [REWRITE_TAC[ETA_AX] THEN ASM_SIMP_TAC[];
          MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN ASM_SIMP_TAC[FINITE_DELETE] THEN
          X_GEN_TAC `b:complex` THEN DISCH_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
        X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_DIFF; IN_UNIV; IN_DELETE] THEN
        DISCH_TAC THEN ASM_CASES_TAC `z:complex = a` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~((z:complex) IN s)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`\b. (R:complex->complex->complex) b z`;
                       `s:complex->bool`; `a:complex`] VSUM_DELETE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `(h:complex->complex) z = R (a:complex) z + g a z`
        SUBST1_TAC THENL [ASM_MESON_TAC[]; CONV_TAC COMPLEX_RING]];
      MAP_EVERY EXISTS_TAC
       [`(:complex) DIFF s`;
        `\z. (h:complex->complex) z -
             vsum s (\b. (R:complex->complex->complex) b z)`] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_UNIV; FINITE_IMP_CLOSED];
        ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
        MATCH_MP_TAC HOLOMORPHIC_ON_SUB THEN ASM_REWRITE_TAC[ETA_AX] THEN
        MATCH_MP_TAC HOLOMORPHIC_ON_VSUM THEN ASM_REWRITE_TAC[] THEN
        X_GEN_TAC `b:complex` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        X_GEN_TAC `z:complex` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
        DISCH_TAC THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_EQ THEN
  EXISTS_TAC
   `\z. (if z IN s
          then (g:complex->complex->complex) z z -
               vsum (s DELETE z) (\b. (R:complex->complex->complex) b z)
          else (h:complex->complex) z - vsum s (\b. R b z)) +
        vsum s (\b. R b z)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((z:complex) IN s)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[NOT_IN_PATH_IMAGE_CIRCLEPATH]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_SUB_ADD];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [GSYM COMPLEX_ADD_LID] THEN
  MATCH_MP_TAC HAS_PATH_INTEGRAL_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC CAUCHY_THEOREM_GLOBAL THEN EXISTS_TAC `(:complex)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; VALID_PATH_CIRCLEPATH; PATHSTART_CIRCLEPATH;
                    PATHFINISH_CIRCLEPATH; SUBSET_UNIV; IN_UNIV];
    MATCH_MP_TAC HAS_PATH_INTEGRAL_VSUM THEN ASM_SIMP_TAC[]]);;

let RESIDUE_PRINCIPAL_PARTS_CIRCLEPATH = prove
 (`!h s m q c r.
        FINITE s /\ (!a. a IN s ==> norm(a - c) < r /\ 1 <= m a) /\
        h holomorphic_on ((:complex) DIFF s) /\
        (!a. a IN s
             ==> ?g. g holomorphic_on ((:complex) DIFF (s DELETE a)) /\
                     !z. ~(z IN s)
                         ==> h z = vsum(0..m a - 1)
                                    (\j. q a j * inv(z - a) pow (m a - j)) +
                                   g z)
        ==> (h has_path_integral
             (Cx(&2) * Cx pi * ii * vsum s (\a. q a (m a - 1))))
            (circlepath(c,r))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL] THEN
  MATCH_MP_TAC RESIDUE_SINGULAR_PARTS_CIRCLEPATH THEN
  EXISTS_TAC `\a z. vsum(0..m a - 1) (\j. (q:complex->num->complex) a j *
                                          inv(z - a) pow (m a - j))` THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_PRINCIPAL_PART THEN SET_TAC[];
    MATCH_MP_TAC HAS_PATH_INTEGRAL_PRINCIPAL_PART_CIRCLEPATH THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The residue theorem for an entire function divided by a product of        *)
(* powers of linear factors with all roots inside the circle.                *)
(* ------------------------------------------------------------------------- *)

let HOLOMORPHIC_ON_DIV_CPRODUCT_POW = prove
 (`!f t m. f holomorphic_on (:complex) /\ FINITE t
           ==> (\z. f z / cproduct t (\b. (z - b) pow m b))
               holomorphic_on ((:complex) DIFF t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_DIV THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV];
    MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID;
             HOLOMORPHIC_ON_CONST];
    ASM_SIMP_TAC[CPRODUCT_EQ_0; COMPLEX_POW_EQ_0; COMPLEX_SUB_0; IN_DIFF;
                 IN_UNIV] THEN
    MESON_TAC[]]);;

let RESIDUE_CPRODUCT_LOCAL = prove
 (`!f s m a.
     f holomorphic_on (:complex) /\ FINITE s /\ a IN s /\ 1 <= m a
     ==> ?g. g holomorphic_on ((:complex) DIFF (s DELETE a)) /\
             !z. ~(z IN s)
                 ==> f z / cproduct s (\b. (z - b) pow m b) =
                     vsum(0..m a - 1)
                      (\j. higher_complex_derivative j
                             (\z. f z / cproduct (s DELETE a)
                                         (\b. (z - b) pow m b)) a /
                           Cx(&(FACT j)) * inv(z - a) pow (m a - j)) +
                     g z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z. (f:complex->complex) z /
         cproduct (s DELETE a) (\b. (z - b) pow m b)`;
    `(:complex) DIFF (s DELETE a)`; `a:complex`; `(m:complex->num) a - 1`]
   HOLOMORPHIC_TAYLOR_EXPANSION) THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_DIV_CPRODUCT_POW; FINITE_DELETE; OPEN_DIFF;
               OPEN_UNIV; FINITE_IMP_CLOSED; IN_DIFF; IN_UNIV; IN_DELETE;
               ARITH_RULE `1 <= n ==> n - 1 + 1 = n`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:complex->complex` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:complex` THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `z:complex`) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`\b. (z - b) pow (m:complex->num) b`; `s:complex->bool`;
                 `a:complex`] CPRODUCT_DELETE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL
   [`\j. higher_complex_derivative j
          (\z. (f:complex->complex) z /
               cproduct (s DELETE a) (\b. (z - b) pow m b)) a /
         Cx(&(FACT j))`;
    `z - a:complex`; `(m:complex->num) a`] VSUM_POW_DIV_POW) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[COMPLEX_SUB_0]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN
   `~((z - a) pow (m:complex->num) a = Cx(&0)) /\
    ~(cproduct (s DELETE a) (\b. (z - b) pow m b) = Cx(&0))`
  MP_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_POW_EQ_0; COMPLEX_SUB_0; CPRODUCT_EQ_0; FINITE_DELETE;
                 IN_DELETE] THEN
    ASM_MESON_TAC[];
    CONV_TAC COMPLEX_FIELD]);;

let RESIDUE_CPRODUCT_CIRCLEPATH = prove
 (`!f s m c r.
     f holomorphic_on (:complex) /\ FINITE s /\
     (!a. a IN s ==> norm(a - c) < r /\ 1 <= m a)
     ==> ((\z. f z / cproduct s (\a. (z - a) pow m a)) has_path_integral
          Cx(&2) * Cx pi * ii *
          vsum s (\a. higher_complex_derivative (m a - 1)
                        (\z. f z / cproduct (s DELETE a)
                                    (\b. (z - b) pow m b)) a /
                      Cx(&(FACT(m a - 1)))))
         (circlepath(c,r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\z. (f:complex->complex) z / cproduct s (\b. (z - b) pow m b)`;
    `s:complex->bool`; `m:complex->num`;
    `\a j. higher_complex_derivative j
             (\z. (f:complex->complex) z /
                  cproduct (s DELETE a) (\b. (z - b) pow m b)) a /
           Cx(&(FACT j))`;
    `c:complex`; `r:real`] RESIDUE_PRINCIPAL_PARTS_CIRCLEPATH) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_DIV_CPRODUCT_POW] THEN
  X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
  MATCH_MP_TAC RESIDUE_CPRODUCT_LOCAL THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The interpolation identity: nodes s of multiplicity t + 1 and an extra    *)
(* simple node w (Baker, Transcendental Number Theory, Ch. 3, eq. (8)).      *)
(* ------------------------------------------------------------------------- *)

let HIGHER_COMPLEX_DERIVATIVE_MUL_DIV_FACT = prove
 (`!f g s n z.
        open s /\ f holomorphic_on s /\ g holomorphic_on s /\ z IN s
        ==> higher_complex_derivative n (\x. f x * g x) z / Cx(&(FACT n)) =
            vsum(0..n) (\j. higher_complex_derivative j f z / Cx(&(FACT j)) *
                            higher_complex_derivative (n - j) g z /
                            Cx(&(FACT(n - j))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `g:complex->complex`;
                 `s:complex->bool`; `n:num`; `z:complex`]
         HIGHER_COMPLEX_DERIVATIVE_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[complex_div] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `j:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n - j:num`; `j:num`] BINOM_FACT) THEN
  ASM_SIMP_TAC[SUB_ADD] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `~(binom(n,j) = 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[BINOM_EQ_0; NOT_LT]; ALL_TAC] THEN
  MP_TAC(SPEC `j:num` FACT_NZ) THEN MP_TAC(SPEC `n - j:num` FACT_NZ) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
  CONV_TAC COMPLEX_FIELD);;

let HOLOMORPHIC_ON_INV_LINEAR_CPRODUCT = prove
 (`!w u k. FINITE u
           ==> (\z. inv((z - w) * cproduct u (\b. (z - b) pow k)))
               holomorphic_on ((:complex) DIFF (w INSERT u))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOLOMORPHIC_ON_INV THEN CONJ_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_MUL THEN
    SIMP_TAC[HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID; HOLOMORPHIC_ON_CONST] THEN
    MATCH_MP_TAC HOLOMORPHIC_ON_CPRODUCT THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[HOLOMORPHIC_ON_POW; HOLOMORPHIC_ON_SUB; HOLOMORPHIC_ON_ID;
             HOLOMORPHIC_ON_CONST];
    ASM_SIMP_TAC[COMPLEX_ENTIRE; CPRODUCT_EQ_0; COMPLEX_POW_EQ_0;
                 COMPLEX_SUB_0; IN_DIFF; IN_UNIV; IN_INSERT] THEN
    MESON_TAC[]]);;

let INTERPOLATION_RESIDUE_CIRCLEPATH = prove
 (`!f s t w c r.
     f holomorphic_on (:complex) /\ FINITE s /\ ~(w IN s) /\
     norm(w - c) < r /\ (!a. a IN s ==> norm(a - c) < r)
     ==> ((\z. f z / ((z - w) * cproduct s (\a. (z - a) pow (t + 1))))
          has_path_integral
          Cx(&2) * Cx pi * ii *
          (f w / cproduct s (\a. (w - a) pow (t + 1)) +
           vsum s (\a. vsum(0..t) (\j.
              higher_complex_derivative j f a / Cx(&(FACT j)) *
              higher_complex_derivative (t - j)
                (\z. inv((z - w) *
                         cproduct (s DELETE a) (\b. (z - b) pow (t + 1)))) a /
              Cx(&(FACT(t - j)))))))
         (circlepath(c,r))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:complex->complex`; `(w:complex) INSERT s`;
                 `\a:complex. if a = w then 1 else t + 1`;
                 `c:complex`; `r:real`] RESIDUE_CPRODUCT_CIRCLEPATH) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT] THEN ANTS_TAC THENL
   [REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:complex` THEN
    AP_TERM_TAC THEN ASM_SIMP_TAC[CPRODUCT_CLAUSES; COMPLEX_POW_1] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
    X_GEN_TAC `b:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(b:complex = w)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[VSUM_CLAUSES] THEN BINOP_TAC THENL
   [REWRITE_TAC[SUB_REFL; higher_complex_derivative; FACT; COMPLEX_DIV_1] THEN
    REWRITE_TAC[DELETE_INSERT] THEN
    SUBGOAL_THEN `s DELETE (w:complex) = s` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
    X_GEN_TAC `b:complex` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(b:complex = w)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `a:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(a:complex = w)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[ADD_SUB]] THEN
  SUBGOAL_THEN
   `(\z. f z / cproduct ((w INSERT s) DELETE a)
                (\b. (z - b) pow (if b = w then 1 else t + 1))) =
    (\z. f z * inv((z - w) *
                   cproduct (s DELETE a) (\b. (z - b) pow (t + 1))))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; complex_div] THEN X_GEN_TAC `z:complex` THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[DELETE_INSERT; CPRODUCT_CLAUSES; FINITE_DELETE; IN_DELETE;
                 COMPLEX_POW_1] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC CPRODUCT_EQ THEN
    X_GEN_TAC `b:complex` THEN REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(b:complex = w)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HIGHER_COMPLEX_DERIVATIVE_MUL_DIV_FACT THEN
  EXISTS_TAC `(:complex) DIFF (w INSERT (s DELETE a))` THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_INV_LINEAR_CPRODUCT; FINITE_DELETE] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN
    ASM_SIMP_TAC[OPEN_UNIV; FINITE_IMP_CLOSED; FINITE_DELETE; FINITE_INSERT];
    ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; SUBSET_UNIV];
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_INSERT; IN_DELETE]]);;

(* ------------------------------------------------------------------------- *)
(* The resulting bound for |f(w)|: the big circle is estimated by the        *)
(* length bound, the residues at the nodes by Cauchy inequalities on         *)
(* small circles of radius d around the nodes.                               *)
(* ------------------------------------------------------------------------- *)

let INTERPOLATION_RESIDUE_SUM_BOUND = prove
 (`!f s t w d U.
     FINITE s /\ ~(w IN s) /\ &0 < d /\
     (!a. a IN s
          ==> d < norm(w - a) /\
              (!b. b IN s /\ ~(b = a) ==> d < norm(b - a))) /\
     (!a z. a IN s /\ norm(z - a) = d
            ==> norm(inv((z - w) *
                         cproduct (s DELETE a) (\b. (z - b) pow (t + 1))))
                <= U a)
     ==> norm(vsum s (\a. vsum(0..t) (\j.
              higher_complex_derivative j f a / Cx(&(FACT j)) *
              higher_complex_derivative (t - j)
                (\z. inv((z - w) *
                         cproduct (s DELETE a) (\b. (z - b) pow (t + 1)))) a /
              Cx(&(FACT(t - j))))))
         <= sum s (\a. sum(0..t) (\j. norm(higher_complex_derivative j f a) /
                                      &(FACT j) * U a / d pow (t - j)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC VSUM_NORM_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `d < norm(w - a:complex) /\
    (!b. b IN s /\ ~(b = a) ==> d < norm(b - a:complex))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(\z. inv((z - w) * cproduct (s DELETE a) (\b. (z - b) pow (t + 1))))
    holomorphic_on cball(a:complex,d)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOLOMORPHIC_ON_SUBSET THEN
    EXISTS_TAC `(:complex) DIFF (w INSERT (s DELETE a))` THEN
    ASM_SIMP_TAC[HOLOMORPHIC_ON_INV_LINEAR_CPRODUCT; FINITE_DELETE] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_DIFF; IN_UNIV; IN_INSERT; IN_DELETE] THEN
    X_GEN_TAC `x:complex` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(d < norm(x - a:complex))` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_DIV; COMPLEX_NORM_CX;
              REAL_ABS_NUM] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  SIMP_TAC[REAL_LE_DIV; NORM_POS_LE; REAL_POS] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_LT; FACT_LT] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  MATCH_MP_TAC CAUCHY_INEQUALITY THEN
  ASM_SIMP_TAC[HOLOMORPHIC_ON_IMP_CONTINUOUS_ON] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HOLOMORPHIC_ON_SUBSET; BALL_SUBSET_CBALL];
    X_GEN_TAC `x:complex` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[]]);;

let COMPLEX_NORM_BOUND_DIV_ADD = prove
 (`!x p y a b.
        ~(p = Cx(&0)) /\ norm(x / p + y) <= a /\ norm(y) <= b
        ==> norm(x) <= norm(p) * (a + b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(p:complex)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; COMPLEX_VEC_0]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_DIV] THEN
  ASM_MESON_TAC[NORM_ARITH
   `norm(x + y:complex) <= a /\ norm(y) <= b ==> norm(x) <= a + b`]);;

let REAL_LE_TWO_PI_MUL_CANCEL = prove
 (`!n a r. &2 * pi * n <= a * &2 * pi * r ==> n <= r * a`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:real`; `r * a:real`; `&2 * pi`] REAL_LE_LMUL_EQ) THEN
  ANTS_TAC THENL [MP_TAC PI_POS THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_MUL_AC]);;

let INTERPOLATION_RESIDUE_BOUND = prove
 (`!f s t w c r d M mu U.
     f holomorphic_on (:complex) /\ FINITE s /\ ~(w IN s) /\
     norm(w - c) < r /\ (!a. a IN s ==> norm(a - c) < r) /\ &0 < d /\
     (!a. a IN s
          ==> d < norm(w - a) /\
              (!b. b IN s /\ ~(b = a) ==> d < norm(b - a))) /\
     &0 < mu /\
     (!z. norm(z - c) = r
          ==> norm(f z) <= M /\
              mu <= norm((z - w) * cproduct s (\a. (z - a) pow (t + 1)))) /\
     (!a z. a IN s /\ norm(z - a) = d
            ==> norm(inv((z - w) *
                         cproduct (s DELETE a) (\b. (z - b) pow (t + 1))))
                <= U a)
     ==> norm(f w) <=
         norm(cproduct s (\a. (w - a) pow (t + 1))) *
         (r * M / mu +
          sum s (\a. sum(0..t) (\j. norm(higher_complex_derivative j f a) /
                                    &(FACT j) * U a / d pow (t - j))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [MP_TAC(ISPEC `w - c:complex` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= M` ASSUME_TAC THENL
   [SUBGOAL_THEN `norm((c + Cx r) - c) = r` ASSUME_TAC THENL
     [REWRITE_TAC[COMPLEX_ADD_SUB; COMPLEX_NORM_CX] THEN ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[NORM_POS_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_NORM_BOUND_DIV_ADD THEN
  EXISTS_TAC
   `vsum s (\a. vsum(0..t) (\j.
              higher_complex_derivative j f a / Cx(&(FACT j)) *
              higher_complex_derivative (t - j)
                (\z. inv((z - w) *
                         cproduct (s DELETE a) (\b. (z - b) pow (t + 1)))) a /
              Cx(&(FACT(t - j)))))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[CPRODUCT_EQ_0; COMPLEX_POW_EQ_0; COMPLEX_SUB_0] THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`f:complex->complex`; `s:complex->bool`; `t:num`;
                   `w:complex`; `c:complex`; `r:real`]
           INTERPOLATION_RESIDUE_CIRCLEPATH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] HAS_PATH_INTEGRAL_BOUND_CIRCLEPATH)) THEN
    DISCH_THEN(MP_TAC o SPEC `M / mu`) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:complex` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP
       (ASSUME `norm(x - c:complex) = r`)) THEN
      REWRITE_TAC[COMPLEX_NORM_DIV] THEN
      TRANS_TAC REAL_LE_TRANS `norm((f:complex->complex) x) / mu` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[real_div] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        REWRITE_TAC[NORM_POS_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LE_DIV2_EQ]];
      REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II;
                  REAL_ABS_PI; REAL_ABS_NUM; REAL_MUL_LID] THEN
      MATCH_ACCEPT_TAC REAL_LE_TWO_PI_MUL_CANCEL];
    MATCH_MP_TAC INTERPOLATION_RESIDUE_SUM_BOUND THEN ASM_REWRITE_TAC[]]);;
