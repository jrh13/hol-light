(* ========================================================================= *)
(* Uniqueness of exponential polynomials; polynomials of distinct degrees.   *)
(*                                                                           *)
(* Purpose: replaces the determinant Lemma 3 of Baker (Transcendental Number *)
(* Theory, Ch. 3): if sum_i P_i(l) w_i^l = 0 for all l < sum_i (deg P_i +    *)
(* 1), with pairwise distinct nonzero nodes w_i, then all P_i are zero       *)
(* (induction on the number of coefficients, applying the difference         *)
(* operator u(l) |-> u(l + 1) - w(a) u(l)). Also the shift x |-> x + 1 of    *)
(* polynomials (by the binomial theorem) and the linear independence of      *)
(* polynomials of pairwise distinct exact degrees (which replaces Baker      *)
(* Lemma 2).                                                                 *)
(*                                                                           *)
(* Main results: EXPOLY_UNIQUENESS, EXPOLY_UNIQUENESS_POLYFUN (parts given   *)
(*   as polynomial functions), EXPOLY_UNIQUENESS_UNIFORM,                    *)
(*   EXPOLY_UNIQUENESS_NODES (a nonzero coefficient forces two equal nodes), *)
(*   COMPLEX_POLYFUN_DISTINCT_DEGREES, COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN; *)
(*   COMPLEX_POLYFUN_SHIFT1.                                                 *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (COMPLEX_BINOMIAL_THEOREM, COMPLEX_POLYFUN_SHIFT,   *)
(*   COMPLEX_POLYFUN_AT_0, COMPLEX_POLYFUN_TRUNCATE).                        *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* The shift x |-> x + 1 of polynomials (COMPLEX_BINOMIAL_THEOREM and the    *)
(* general shift COMPLEX_POLYFUN_SHIFT of Baker/lemmas.ml).                  *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_SHIFT1 = prove
 (`!M (c:num->complex) x.
     vsum(0..M) (\t. c t * (x + Cx(&1)) pow t) =
     vsum(0..M) (\t. vsum(0..M) (\k. Cx(&(binom(k,t))) * c k) * x pow t)`,
  REWRITE_TAC[COMPLEX_POLYFUN_SHIFT; COMPLEX_POW_ONE; COMPLEX_MUL_LID]);;

let COMPLEX_POLYFUN_LINEAR_COMB = prove
 (`!n u v (a:num->complex) b x.
     vsum(0..n) (\t. (u * a t - v * b t) * x pow t) =
     u * vsum(0..n) (\t. a t * x pow t) - v * vsum(0..n) (\t. b t * x pow t)`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_SUB; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  CONV_TAC COMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Triangularity of the shift on coefficients, and the two consequences used *)
(* in the induction (downward induction on the coefficient index).           *)
(* ------------------------------------------------------------------------- *)

let VSUM_BINOM_TRIANGULAR = prove
 (`!M t (c:num->complex).
     (!k. t < k /\ k <= M ==> c k = Cx(&0))
     ==> vsum(0..M) (\k. Cx(&(binom(k,t))) * c k) =
         if t <= M then c t else Cx(&0)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `vsum(0..M) (\k. if k = t then c t else Cx(&0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `k:num = t` THEN
    ASM_REWRITE_TAC[BINOM_REFL; COMPLEX_MUL_LID] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP
     (ARITH_RULE `~(k:num = t) ==> k < t \/ t < k`)) THEN
    ASM_SIMP_TAC[BINOM_LT; COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO];
    REWRITE_TAC[GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG; LE_0]]);;

let VSUM_BINOM_PENULT = prove
 (`!M r (c:num->complex).
     SUC r <= M /\ (!k. SUC r < k /\ k <= M ==> c k = Cx(&0))
     ==> vsum(0..M) (\k. Cx(&(binom(k,r))) * c k) =
         c r + Cx(&(SUC r)) * c(SUC r)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `vsum(0..M) (\k. (if k = r then c r else Cx(&0)) +
                    (if k = SUC r then Cx(&(SUC r)) * c(SUC r)
                     else Cx(&0)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (ARITH_RULE `k < r \/ k = r \/ k = SUC r \/ SUC r < k`) THEN
    ASM_SIMP_TAC[BINOM_LT; BINOM_REFL; BINOM_PENULT; COMPLEX_MUL_LZERO;
      COMPLEX_MUL_LID; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID; COMPLEX_ADD_RID;
      ARITH_RULE `~(r = SUC r) /\ ~(SUC r = r)`;
      ARITH_RULE `k < r ==> ~(k = r) /\ ~(k = SUC r)`;
      ARITH_RULE `SUC r < k ==> ~(k = r) /\ ~(k = SUC r)`];
    SIMP_TAC[VSUM_ADD_NUMSEG; GSYM COMPLEX_VEC_0; VSUM_DELTA; IN_NUMSEG;
             LE_0] THEN
    ASM_SIMP_TAC[ARITH_RULE `SUC r <= M ==> r <= M`]]);;

let VSUM_BINOM_SHIFT_NE_ZERO = prove
 (`!M (c:num->complex) u v.
     ~(u = v) /\ (!t. M < t ==> c t = Cx(&0)) /\
     (!t. u * vsum(0..M) (\k. Cx(&(binom(k,t))) * c k) = v * c t)
     ==> !t. c t = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF_DOWN THEN
  EXISTS_TAC `M + 1` THEN ASM_SIMP_TAC[ARITH_RULE `M + 1 <= n <=> M < n`] THEN
  X_GEN_TAC `t:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`M:num`; `t:num`; `c:num->complex`] VSUM_BINOM_TRIANGULAR) THEN
  ASM_SIMP_TAC[ARITH_RULE `t < M + 1 ==> t <= M`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `u * (c:num->complex) t = v * c t` MP_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[COMPLEX_EQ_MUL_RCANCEL]]);;

let VSUM_BINOM_SHIFT_EQ_CONST = prove
 (`!M (c:num->complex).
     (!t. M < t ==> c t = Cx(&0)) /\
     (!t. vsum(0..M) (\k. Cx(&(binom(k,t))) * c k) = c t)
     ==> !t. 1 <= t ==> c t = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC num_WF_DOWN THEN
  EXISTS_TAC `M + 1` THEN ASM_SIMP_TAC[ARITH_RULE `M + 1 <= n <=> M < n`] THEN
  X_GEN_TAC `t:num` THEN STRUCT_CASES_TAC(SPEC `t:num` num_CASES) THEN
  REWRITE_TAC[ARITH_RULE `~(1 <= 0)`; ARITH_RULE `1 <= SUC n`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`M:num`; `n:num`; `c:num->complex`] VSUM_BINOM_PENULT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[COMPLEX_RING `a = a + b <=> b = Cx(&0)`; COMPLEX_ENTIRE] THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; NOT_SUC]]);;

(* ------------------------------------------------------------------------- *)
(* The core statement: common bound M for the coefficient index, e i is the  *)
(* number of (possibly) nonzero coefficients of the i-th polynomial part.    *)
(* Induction on the total number N of coefficients via the difference        *)
(* operator u(l) |-> u(l + 1) - w(a) u(l).                                   *)
(* ------------------------------------------------------------------------- *)

let EXPOLY_UNIQUENESS_COMMON_BOUND = prove
 (`!N M s (w:A->complex) e c.
     FINITE s /\ nsum s e = N /\
     (!i. i IN s ==> ~(w i = Cx(&0))) /\
     (!i j. i IN s /\ j IN s /\ w i = w j ==> i = j) /\
     (!i t. i IN s /\ (e i <= t \/ M < t) ==> c i t = Cx(&0)) /\
     (!l. l < N
          ==> vsum s (\i. vsum(0..M) (\t. c i t * Cx(&l) pow t) *
                          w i pow l) = Cx(&0))
     ==> !i t. i IN s ==> c i t = Cx(&0)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC `nsum s (e:A->num) = 0` THEN
    ASM_SIMP_TAC[NSUM_EQ_0_IFF] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`i:A`; `t:num`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[LE_0];
    ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?a:A. a IN s /\ ~(e a = 0)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:A->num`; `s:A->bool`] NSUM_EQ_0) THEN
    ASM_REWRITE_TAC[NOT_SUC] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`M:num`; `s:A->bool`; `w:A->complex`;
    `\i. if i = a then (e:A->num) i - 1 else e i`;
    `\i t. (w:A->complex) i * vsum(0..M) (\k. Cx(&(binom(k,t))) * c i k) -
           w a * (c:A->num->complex) i t`]) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `nsum s (e:A->num) =
        nsum s (\i. (if i = a then e i - 1 else e i) +
                    (if i = a then 1 else 0))`
      MP_TAC THENL
       [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
        ASM_ARITH_TAC;
        SIMP_TAC[NSUM_ADD; NSUM_DELTA; ASSUME `FINITE(s:A->bool)`;
                 ASSUME `(a:A) IN s`; ASSUME `nsum s (e:A->num) = SUC N`] THEN
        ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`i:A`; `t:num`] THEN
      ASM_CASES_TAC `i:A = a` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        MP_TAC(ISPECL [`M:num`; `t:num`; `(c:A->num->complex) a`]
          VSUM_BINOM_TRIANGULAR) THEN
        ANTS_TAC THENL
         [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        COND_CASES_TAC THEN REWRITE_TAC[COMPLEX_SUB_REFL] THEN
        SUBGOAL_THEN `(c:A->num->complex) a t = Cx(&0)` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL]];
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
        MP_TAC(ISPECL [`M:num`; `t:num`; `(c:A->num->complex) i`]
          VSUM_BINOM_TRIANGULAR) THEN
        ANTS_TAC THENL
         [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          ASM_ARITH_TAC;
          DISCH_THEN SUBST1_TAC] THEN
        SUBGOAL_THEN `(c:A->num->complex) i t = Cx(&0)` SUBST1_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[COND_ID; COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL]];
      X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `!i. vsum(0..M) (\t. ((w:A->complex) i *
                             vsum(0..M) (\k. Cx(&(binom(k,t))) * c i k) -
                             w a * c i t) * Cx(&l) pow t) * w i pow l =
            vsum(0..M) (\t. c i t * Cx(&(l + 1)) pow t) * w i pow (l + 1) -
            w a * (vsum(0..M) (\t. (c:A->num->complex) i t * Cx(&l) pow t) *
                   w i pow l)`
       (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD; COMPLEX_POLYFUN_SHIFT1;
                    COMPLEX_POLYFUN_LINEAR_COMB] THEN
        REWRITE_TAC[COMPLEX_POW_ADD; COMPLEX_POW_1] THEN
        CONV_TAC COMPLEX_RING;
        ASM_SIMP_TAC[VSUM_SUB; VSUM_COMPLEX_LMUL;
                     ARITH_RULE `l < N ==> l < SUC N /\ l + 1 < SUC N`] THEN
        REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_SUB_REFL]]];
    DISCH_TAC] THEN
  SUBGOAL_THEN `!i. i IN s /\ ~(i = a) ==> !t. (c:A->num->complex) i t = Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC VSUM_BINOM_SHIFT_NE_ZERO THEN
    MAP_EVERY EXISTS_TAC [`M:num`; `(w:A->complex) i`; `(w:A->complex) a`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_SIMP_TAC[];
      X_GEN_TAC `t:num` THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:A->num->complex) a 0 = Cx(&0)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `0 < SUC N`)) THEN
    REWRITE_TAC[COMPLEX_POLYFUN_AT_0; complex_pow; COMPLEX_MUL_RID] THEN
    SUBGOAL_THEN
     `vsum s (\i. (c:A->num->complex) i 0) =
      vsum s (\i. if i = a then c a 0 else vec 0)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[COMPLEX_VEC_0];
      ASM_REWRITE_TAC[VSUM_DELTA]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. 1 <= t ==> (c:A->num->complex) a t = Cx(&0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC VSUM_BINOM_SHIFT_EQ_CONST THEN EXISTS_TAC `M:num` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      X_GEN_TAC `t:num` THEN
      SUBGOAL_THEN `~((w:A->complex) a = Cx(&0))` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `t:num`]) THEN
      ASM_REWRITE_TAC[COMPLEX_SUB_0; COMPLEX_EQ_MUL_LCANCEL] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `t:num`] THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:A = a` THEN ASM_SIMP_TAC[] THEN
  ASM_CASES_TAC `t = 0` THEN ASM_SIMP_TAC[ARITH_RULE `~(t = 0) ==> 1 <= t`]);;

(* ------------------------------------------------------------------------- *)
(* The main statement: polynomial parts of degree <= e i, vanishing at the   *)
(* first sum_i (e i + 1) natural numbers.                                    *)
(* ------------------------------------------------------------------------- *)

let EXPOLY_UNIQUENESS = prove
 (`!s (w:A->complex) e c.
     FINITE s /\
     (!i. i IN s ==> ~(w i = Cx(&0))) /\
     (!i j. i IN s /\ j IN s /\ w i = w j ==> i = j) /\
     (!l. l < nsum s (\i. e i + 1)
          ==> vsum s (\i. vsum(0..e i) (\t. c i t * Cx(&l) pow t) *
                          w i pow l) = Cx(&0))
     ==> !i t. i IN s /\ t <= e i ==> c i t = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> (e:A->num) i <= nsum s e` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`e:A->num`; `nsum s (e:A->num)`; `s:A->bool`]
      NSUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`nsum s (\i. (e:A->num) i + 1)`; `nsum s (e:A->num)`; `s:A->bool`;
    `w:A->complex`; `\i. (e:A->num) i + 1`;
    `\i t. if t <= (e:A->num) i then (c:A->num->complex) i t
           else Cx(&0)`]
   EXPOLY_UNIQUENESS_COMMON_BOUND) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:A`; `t:num`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(t <= (e:A->num) i)` (fun th -> REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      X_GEN_TAC `l:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(MESON[] `(b:complex) = a ==> a = z ==> b = z`) THEN
      MATCH_MP_TAC VSUM_EQ THEN
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[COMPLEX_POLYFUN_TRUNCATE]];
    DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`i:A`; `t:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`i:A`; `t:num`]) THEN
    ASM_REWRITE_TAC[]]);;

let EXPOLY_UNIQUENESS_UNIFORM = prove
 (`!s (w:A->complex) d c.
     FINITE s /\
     (!i. i IN s ==> ~(w i = Cx(&0))) /\
     (!i j. i IN s /\ j IN s /\ w i = w j ==> i = j) /\
     (!l. l < CARD s * (d + 1)
          ==> vsum s (\i. vsum(0..d) (\t. c i t * Cx(&l) pow t) *
                          w i pow l) = Cx(&0))
     ==> !i t. i IN s /\ t <= d ==> c i t = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `w:A->complex`; `\i:A. (d:num)`;
                 `c:A->num->complex`] EXPOLY_UNIQUENESS) THEN
  ASM_SIMP_TAC[NSUM_CONST] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_MESON_TAC[]);;

let EXPOLY_UNIQUENESS_POLYFUN = prove
 (`!s (w:A->complex) e (P:A->complex->complex).
     FINITE s /\
     (!i. i IN s ==> ~(w i = Cx(&0))) /\
     (!i j. i IN s /\ j IN s /\ w i = w j ==> i = j) /\
     (!i. i IN s ==> ?c. !x. P i x = vsum(0..e i) (\t. c t * x pow t)) /\
     (!l. l < nsum s (\i. e i + 1)
          ==> vsum s (\i. P i (Cx(&l)) * w i pow l) = Cx(&0))
     ==> !i x. i IN s ==> P i x = Cx(&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `w:A->complex`; `e:A->num`;
                 `c:A->num->complex`] EXPOLY_UNIQUENESS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `(b:complex) = a ==> a = z ==> b = z`) THEN
    MATCH_MP_TAC VSUM_EQ THEN
    SIMP_TAC[ASSUME `!i. i IN s
                         ==> !x. (P:A->complex->complex) i x =
                                 vsum(0..e i) (\t. c i t * x pow t)`];
    DISCH_TAC THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN MATCH_MP_TAC VSUM_EQ_0 THEN
    ASM_SIMP_TAC[IN_NUMSEG; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]]);;

let EXPOLY_UNIQUENESS_NODES = prove
 (`!s (w:A->complex) e c.
     FINITE s /\
     (!i. i IN s ==> ~(w i = Cx(&0))) /\
     (!l. l < nsum s (\i. e i + 1)
          ==> vsum s (\i. vsum(0..e i) (\t. c i t * Cx(&l) pow t) *
                          w i pow l) = Cx(&0)) /\
     (?i t. i IN s /\ t <= e i /\ ~(c i t = Cx(&0)))
     ==> ?i j. i IN s /\ j IN s /\ ~(i = j) /\ w i = w j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `w:A->complex`; `e:A->num`;
                 `c:A->num->complex`] EXPOLY_UNIQUENESS) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Polynomials with pairwise distinct exact degrees are linearly             *)
(* independent.                                                              *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_DISTINCT_DEGREES = prove
 (`!s (p:A->num->complex) (deg:A->num) N a.
     FINITE s /\
     (!i. i IN s
          ==> deg i <= N /\ ~(p i (deg i) = Cx(&0)) /\
              !k. deg i < k ==> p i k = Cx(&0)) /\
     (!i j. i IN s /\ j IN s /\ deg i = deg j ==> i = j) /\
     (!x. vsum s (\i. a i * vsum(0..N) (\k. p i k * x pow k)) = Cx(&0))
     ==> !i. i IN s ==> a i = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!k. k <= N
        ==> vsum s (\i. (a:A->complex) i * (p:A->num->complex) i k) =
            Cx(&0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`N:num`; `\k. vsum s (\i. (a:A->complex) i * (p:A->num->complex) i k)`]
      COMPLEX_POLYFUN_EQ_0) THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    X_GEN_TAC `x:complex` THEN
    FIRST_X_ASSUM(fun th ->
      GEN_REWRITE_TAC RAND_CONV [GSYM(SPEC `x:complex` th)]) THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL;
             FINITE_NUMSEG; ASSUME `FINITE(s:A->bool)`] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `~(?i:A. i IN s /\ ~(a i = Cx(&0))) ==> !i. i IN s ==> a i = Cx(&0)`) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `?m. (?i:A. i IN s /\ ~(a i = Cx(&0)) /\ deg i = m) /\
        !d. (?i:A. i IN s /\ ~(a i = Cx(&0)) /\ deg i = d) ==> d <= m`
  MP_TAC THENL
   [REWRITE_TAC[GSYM num_MAX] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `m:num` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) ASSUME_TAC))] THEN
  SUBGOAL_THEN
   `vsum s (\i. (a:A->complex) i * (p:A->num->complex) i m) = Cx(&0)`
  MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vsum s (\i. (a:A->complex) i * (p:A->num->complex) i m) =
    vsum s (\i. if i = j then a j * p j m else vec 0)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[COMPLEX_VEC_0] THEN
    ASM_CASES_TAC `(a:A->complex) i = Cx(&0)` THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_LZERO] THEN
    SUBGOAL_THEN `(deg:A->num) i < m` ASSUME_TAC THENL
     [REWRITE_TAC[LT_LE] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `i:A` THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[]];
      ASM_SIMP_TAC[COMPLEX_MUL_RZERO]];
    ASM_REWRITE_TAC[VSUM_DELTA; COMPLEX_ENTIRE] THEN ASM_MESON_TAC[]]);;

let COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN = prove
 (`!s (P:A->complex->complex) (deg:A->num) a.
     FINITE s /\
     (!i. i IN s
          ==> ?c. ~(c(deg i) = Cx(&0)) /\
                  !x. P i x = vsum(0..deg i) (\k. c k * x pow k)) /\
     (!i j. i IN s /\ j IN s /\ deg i = deg j ==> i = j) /\
     (!x. vsum s (\i. a i * P i x) = Cx(&0))
     ==> !i. i IN s ==> a i = Cx(&0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!i. i IN s ==> (deg:A->num) i <= nsum s deg` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`deg:A->num`; `nsum s (deg:A->num)`; `s:A->bool`]
      NSUM_POS_BOUND) THEN
    ASM_REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  MATCH_MP_TAC COMPLEX_POLYFUN_DISTINCT_DEGREES THEN
  MAP_EVERY EXISTS_TAC
   [`\i k. if k <= (deg:A->num) i then (c:A->num->complex) i k
           else Cx(&0)`;
    `deg:A->num`; `nsum s (deg:A->num)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[LE_REFL; GSYM NOT_LE];
    X_GEN_TAC `x:complex` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:complex`) THEN
    MATCH_MP_TAC(MESON[] `(b:complex) = a ==> a = z ==> b = z`) THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[COMPLEX_POLYFUN_TRUNCATE]]);;
