(* ========================================================================= *)
(* Two logarithms: the zero lemma for C x C-star and the                     *)
(* maximal rank of the interpolation matrix.                                 *)
(*                                                                           *)
(* Purpose: Lemmas E.1 and E.2 of Y. Bugeaud, Linear Forms in Logarithms and *)
(* Applications (EMS 2018), Appendix E, and the rank statement at the        *)
(* beginning of section 11.3 there: some K L x K L minor of the matrix       *)
(* (b2 r + b1 s)^k (a1^r a2^s)^l is non-zero.                                *)
(*                                                                           *)
(* Main results: TL_ZERO_VANDERMONDE (Lemma E.2, generalized Vandermonde     *)
(* determinant), TL_ZERO_LEMMA (Lemma E.1), TL_ZERO_RANK, TL_ZERO_RANK_MINOR *)
(* and TWOLOG_ZERO_MINOR (the real rational form used in Baker/twolog.ml).   *)
(*                                                                           *)
(* Uses: Baker/twolog_det.ml (COMPLEX_RING_DET, CDET_CX, CDET_ROWS_CMUL,     *)
(* CDET_DEPENDENT_ROWS, CDET_MINOR_SELECTION), Library/ring_det.ml           *)
(* (RING_DET_EQ, RING_DET_EMPTY, COEFF_POLY_MUL_LE), Baker/lemmas.ml         *)
(* (VSUM_DELTA_FUN, COMPLEX_POLYFUN_POLY, COMPLEX_POLYFUN_SHIFT),            *)
(* poly_eval_vsum of 100/transcendence.ml.                                   *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;
needs "Baker/twolog_det.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Polynomial forms vsum(0..N) (\t. w t * x pow t), keeping track of the     *)
(* coefficient at the top index N.                                           *)
(* ------------------------------------------------------------------------- *)

let TL_ZERO_POLY_MUL = prove
 (`!a b (u:num->complex) (v:num->complex).
        ?w. w(a + b) = u a * v b /\
            !x. vsum(0..a) (\s. u s * x pow s) *
                vsum(0..b) (\t. v t * x pow t) =
                vsum(0..a + b) (\k. w k * x pow k)`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`b:num`; `v:num->complex`] COMPLEX_POLYFUN_POLY) THEN
  MP_TAC(SPECL [`a:num`; `u:num->complex`] COMPLEX_POLYFUN_POLY) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_POLY_RING_CARRIER; SUBSET_UNIV] THEN
  X_GEN_TAC `p:(1->num)->complex` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)))) THEN
  X_GEN_TAC `q:(1->num)->complex` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)))) THEN
  EXISTS_TAC `\k. coeff k (poly_mul complex_ring p q)` THEN
  ASM_SIMP_TAC[COEFF_POLY_MUL_LE; COMPLEX_RING_CLAUSES; LE_REFL] THEN
  X_GEN_TAC `x:complex` THEN
  MP_TAC(ISPECL [`complex_ring`; `p:(1->num)->complex`;
                 `q:(1->num)->complex`; `x:complex`] POLY_EVAL_MUL) THEN
  ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES; IN_UNIV] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] poly_eval_vsum) THEN
  ASM_SIMP_TAC[RING_POLYNOMIAL_MUL] THEN
  ASM_MESON_TAC[POLY_DEG_MUL_LE; LE_ADD2; LE_TRANS]);;

let TL_ZERO_POLY_CPRODUCT = prove
 (`!n (m:num->num) (u:num->num->complex).
        ?w. w(nsum(1..n) m) = cproduct(1..n) (\i. u i (m i)) /\
            !x. cproduct(1..n) (\i. vsum(0..m i) (\t. u i t * x pow t)) =
                vsum(0..nsum(1..n) m) (\k. w k * x pow k)`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[CPRODUCT_CLAUSES_NUMSEG; NSUM_CLAUSES_NUMSEG; ARITH_EQ] THEN
    EXISTS_TAC `\k:num. Cx(&1)` THEN
    REWRITE_TAC[VSUM_SING_NUMSEG; complex_pow; COMPLEX_MUL_LID];
    REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `w0:num->complex` STRIP_ASSUME_TAC o
      SPECL [`m:num->num`; `u:num->num->complex`]) THEN
    MP_TAC(ISPECL [`nsum(1..n) m`; `(m:num->num)(SUC n)`;
                   `w0:num->complex`; `(u:num->num->complex)(SUC n)`]
      TL_ZERO_POLY_MUL) THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `w:num->complex` THEN
    ASM_REWRITE_TAC[CPRODUCT_CLAUSES_NUMSEG; NSUM_CLAUSES_NUMSEG;
                    ARITH_RULE `1 <= SUC n`]]);;

let TL_ZERO_POLY_VSUM = prove
 (`!s N (w:A->num->complex) x.
        FINITE s
        ==> vsum s (\p. vsum(0..N) (\k. w p k * x pow k)) =
            vsum(0..N) (\k. vsum s (\p. w p k) * x pow k)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL] THEN
  MP_TAC(ISPECL [`\p k. (w:A->num->complex) p k * x pow k`; `s:A->bool`;
                 `0..N`] VSUM_SWAP) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG]);;

let TL_ZERO_POLY_SHIFT = prove
 (`!m (c:num->complex) beta.
        ?g. g m = c m /\
            !x. vsum(0..m) (\k. c k * (x + beta) pow k) =
                vsum(0..m) (\t. g t * x pow t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[COMPLEX_POLYFUN_SHIFT] THEN
  EXISTS_TAC `\t. vsum(0..m) (\k. Cx(&(binom(k,t))) * beta pow (k - t) *
                                  (c:num->complex) k)` THEN
  REWRITE_TAC[] THEN
  TRANS_TAC EQ_TRANS `vsum(0..m) (\k. if k = m then (c:num->complex) k
                                      else Cx(&0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    BETA_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[BINOM_REFL; SUB_REFL; complex_pow] THEN
    ASM_SIMP_TAC[BINOM_LT; LT_LE; COMPLEX_MUL_LZERO] THEN
    CONV_TAC COMPLEX_RING;
    REWRITE_TAC[VSUM_DELTA_FUN; IN_NUMSEG; LE_0; LE_REFL]]);;

let TL_ZERO_POLY_SHIFT_TRUNC = prove
 (`!K d (c:num->complex) beta (z:complex).
        d < K /\ (!k. d < k /\ k < K ==> c k = Cx(&0))
        ==> ?g. g d = c d * z /\
                !x. vsum(0..K-1) (\k. c k * (x + beta) pow k) * z =
                    vsum(0..d) (\t. g t * x pow t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:num`; `c:num->complex`; `beta:complex`]
    TL_ZERO_POLY_SHIFT) THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\t. (g0:num->complex) t * z` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN
  SUBGOAL_THEN
   `vsum(0..K-1) (\k. (c:num->complex) k * (x + beta) pow k) =
    vsum(0..d) (\k. c k * (x + beta) pow k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_SUPERSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:num->complex) k = Cx(&0)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0]];
    ASM_REWRITE_TAC[] THEN SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    REWRITE_TAC[COMPLEX_MUL_AC]]);;

let TL_ZERO_CDET_POLY = prove
 (`!n (m:num->num) (u:num->num->num->complex) (M:num->num->complex->complex).
        (!i j x. i IN 1..n /\ j IN 1..n
                 ==> M i j x = vsum(0..m i) (\t. u i j t * x pow t))
        ==> ?w. w(nsum(1..n) m) =
                ring_det complex_ring (1..n) (\i j. u i j (m i)) /\
                !x. ring_det complex_ring (1..n) (\i j. M i j x) =
                    vsum(0..nsum(1..n) m) (\k. w k * x pow k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. ring_det complex_ring (1..n)
          (\i j. (M:num->num->complex->complex) i j x) =
        ring_det complex_ring (1..n)
          (\i j. vsum(0..m i) (\t. (u:num->num->num->complex) i j t * x pow t))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[COMPLEX_RING_DET; FINITE_NUMSEG] THEN
  MP_TAC(GEN `p:num->num` (ISPECL
    [`n:num`; `m:num->num`;
     `\i t. (u:num->num->num->complex) i ((p:num->num) i) t`]
    TL_ZERO_POLY_CPRODUCT)) THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:(num->num)->num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\k. vsum {p | p permutes 1..n}
                    (\p. Cx(sign p) * (W:(num->num)->num->complex) p k)` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:complex` THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MP_TAC(ISPECL [`{p | p permutes 1..n}`; `nsum(1..n) m`;
                 `\p k. Cx(sign(p:num->num)) *
                        (W:(num->num)->num->complex) p k`;
                 `x:complex`] TL_ZERO_POLY_VSUM) THEN
  SIMP_TAC[FINITE_PERMUTATIONS; FINITE_NUMSEG; COMPLEX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Lemma E.2 (generalized Vandermonde determinant).                          *)
(* ------------------------------------------------------------------------- *)

let TL_ZERO_MONOMIALS_INDEPENDENT = prove
 (`!n (kk:num->num) L (e:complex->bool) (c:num->complex).
        (!i. i IN 1..n ==> kk i < L) /\
        (!i i'. i IN 1..n /\ i' IN 1..n /\ kk i = kk i' ==> i = i') /\
        FINITE e /\ L <= CARD e /\
        (!z. z IN e ==> vsum(1..n) (\i. c i * z pow (kk i)) = Cx(&0))
        ==> !i. i IN 1..n ==> c i = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `i0:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(kk:num->num) i0 < L` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `d = \t. vsum(1..n) (\i. if (kk:num->num) i = t
                                      then (c:num->complex) i
                                      else Cx(&0))` THEN
  SUBGOAL_THEN
   `!z. vsum(1..n) (\i. (c:num->complex) i * z pow (kk i)) =
        vsum(0..L-1) (\t. (d:num->complex) t * z pow t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:complex` THEN EXPAND_TAC "d" THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    GEN_REWRITE_TAC RAND_CONV [VSUM_SWAP_NUMSEG] THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS
     `vsum(0..L-1) (\t. if t = (kk:num->num) i
                        then (c:num->complex) i * z pow t else Cx(&0))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VSUM_DELTA_FUN; IN_NUMSEG; LE_0] THEN
      SUBGOAL_THEN `(kk:num->num) i <= L - 1` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(ARITH_RULE `k < L ==> k <= L - 1`) THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_CASES_TAC `t = (kk:num->num) i` THENL
       [ASM_REWRITE_TAC[];
        SUBGOAL_THEN `~((kk:num->num) i = t)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_MESON_TAC[]; REWRITE_TAC[COMPLEX_MUL_LZERO]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN 0..L-1 ==> (d:num->complex) t = Cx(&0)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP COMPLEX_POLYFUN_ROOTBOUND) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(ARITH_RULE
     `!L a b. L <= a /\ 1 <= L /\ a <= b ==> b <= L - 1 ==> F`) THEN
    EXISTS_TAC `CARD(e:complex->bool)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:num->complex)(kk(i0:num)) = c i0` MP_TAC THENL
   [EXPAND_TAC "d" THEN
    TRANS_TAC EQ_TRANS
     `vsum(1..n) (\i. if i = i0 then (c:num->complex) i else Cx(&0))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN ASM_CASES_TAC `i:num = i0` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((kk:num->num) i = kk i0)`
       (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[VSUM_DELTA_FUN]];
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG; LE_0] THEN ASM_ARITH_TAC]);;

let TL_ZERO_VANDERMONDE = prove
 (`!n (kk:num->num) L (e:complex->bool).
        (!i. i IN 1..n ==> kk i < L) /\
        (!i i'. i IN 1..n /\ i' IN 1..n /\ kk i = kk i' ==> i = i') /\
        FINITE e /\ L <= CARD e
        ==> ?a. (!j. j IN 1..n ==> a j IN e) /\
                (!j j'. j IN 1..n /\ j' IN 1..n /\ a j = a j' ==> j = j') /\
                ~(ring_det complex_ring (1..n) (\i j. a j pow (kk i)) =
                  Cx(&0))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `e:complex->bool`;
                 `\i (z:complex). z pow ((kk:num->num) i)`]
    CDET_MINOR_SELECTION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
    MATCH_MP_TAC TL_ZERO_MONOMIALS_INDEPENDENT THEN
    MAP_EVERY EXISTS_TAC [`kk:num->num`; `L:num`; `e:complex->bool`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma E.1 (zero lemma for C x C-star), pointwise version of the proof:    *)
(* instead of Cramer rule: for each point of the second set, the matrix of   *)
(* the rows Q_i (shifted, times powers of the chosen columns)                *)
(* has a non-zero left null vector, so its determinant (a polynomial in x    *)
(* with known top coefficient) has too many zeros.                           *)
(* ------------------------------------------------------------------------- *)

let TL_ZERO_ROWDATA = prove
 (`!K L (p:num->num->complex).
        (?k l. k < K /\ l < L /\ ~(p k l = Cx(&0)))
        ==> ?n kk m.
              1 <= n /\ n <= L /\
              (!i. i IN 1..n ==> kk i < L) /\
              (!i i'. i IN 1..n /\ i' IN 1..n /\ kk i = kk i' ==> i = i') /\
              (!l. l < L /\ (!i. i IN 1..n ==> ~(kk i = l))
                   ==> !k. k < K ==> p k l = Cx(&0)) /\
              (!i. i IN 1..n
                   ==> m i < K /\ ~(p (m i) (kk i) = Cx(&0)) /\
                       (!k. m i < k /\ k < K ==> p k (kk i) = Cx(&0)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:num` (X_CHOOSE_THEN `l0:num`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC
   `S = {l | l < L /\ ?k. k < K /\ ~((p:num->num->complex) k l = Cx(&0))}` THEN
  SUBGOAL_THEN `S SUBSET {l:num | l < L}` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(S:num->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; FINITE_NUMSEG_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(S:num->bool) <= L` ASSUME_TAC THENL
   [GEN_REWRITE_TAC RAND_CONV [GSYM CARD_NUMSEG_LT] THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_NUMSEG_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l0:num) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `S:num->bool` FINITE_INDEX_NUMSEG) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num->num` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `n = CARD(S:num->bool)` THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL
   [UNDISCH_TAC `(l0:num) IN S` THEN ASM_REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN
    STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i IN 1..n ==> (kk:num->num) i < L /\
                      ?k. k < K /\ ~((p:num->num->complex) k (kk i) = Cx(&0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(kk:num->num) i IN S` MP_TAC THENL
     [ASM_MESON_TAC[FUN_IN_IMAGE];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l < L /\ (!i. i IN 1..n ==> ~((kk:num->num) i = l))
        ==> !k. k < K ==> (p:num->num->complex) k l = Cx(&0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:num` THEN STRIP_TAC THEN X_GEN_TAC `k:num` THEN
    DISCH_TAC THEN SUBGOAL_THEN `~((l:num) IN S)` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. ?d. i IN 1..n
            ==> d < K /\
                ~((p:num->num->complex) d ((kk:num->num) i) = Cx(&0)) /\
                (!k. d < k /\ k < K ==> p k (kk i) = Cx(&0))`
  MP_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `\k. k < K /\
                      ~((p:num->num->complex) k ((kk:num->num) i) = Cx(&0))`
      num_MAX) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; EXISTS_TAC `K:num`] THEN
      MESON_TAC[LT_IMP_LE];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(p:num->num->complex) k ((kk:num->num) i) = Cx(&0)` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `m:num->num`)] THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `kk:num->num`; `m:num->num`] THEN
  ASM_MESON_TAC[]);;

let TL_ZERO_DEPENDENT = prove
 (`!n K L (p:num->num->complex) (kk:num->num) (alpha:num->complex)
    (beta:num->complex) x y.
        1 <= n /\ 1 <= K /\ ~(y = Cx(&0)) /\
        (!i. i IN 1..n ==> kk i < L) /\
        (!i i'. i IN 1..n /\ i' IN 1..n /\ kk i = kk i' ==> i = i') /\
        (!l. l < L /\ (!i. i IN 1..n ==> ~(kk i = l))
             ==> !k. k < K ==> p k l = Cx(&0)) /\
        (!j. j IN 1..n
             ==> vsum(0..K-1) (\k. vsum(0..L-1) (\l.
                   p k l * (x + beta j) pow k * (alpha j * y) pow l)) =
                 Cx(&0))
        ==> ring_det complex_ring (1..n)
              (\i j. vsum(0..K-1) (\k. p k (kk i) * (x + beta j) pow k) *
                     alpha j pow (kk i)) = Cx(&0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= L` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `!k. k < L ==> 1 <= L`) THEN
    EXISTS_TAC `(kk:num->num) 1` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC CDET_DEPENDENT_ROWS THEN
  EXISTS_TAC `\i. (y:complex) pow ((kk:num->num) i)` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXISTS_TAC `1` THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL; COMPLEX_POW_EQ_0];
    ALL_TAC] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC RAND_CONV [VSUM_SWAP_NUMSEG] THEN REWRITE_TAC[] THEN
  MP_TAC(ISPECL
   [`\l. vsum(0..K-1) (\k. (p:num->num->complex) k l *
           (x + (beta:num->complex) j) pow k *
           ((alpha:num->complex) j * y) pow l)`;
    `IMAGE (kk:num->num) (1..n)`; `0..L-1`] VSUM_SUPERSET) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `k < L ==> k <= L - 1`) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG];
      ALL_TAC] THEN
    X_GEN_TAC `l:num` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM COMPLEX_VEC_0] THEN
    MATCH_MP_TAC VSUM_EQ_0 THEN X_GEN_TAC `k:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:num->num->complex) k l = Cx(&0)`
     (fun th -> REWRITE_TAC[th; COMPLEX_MUL_LZERO; COMPLEX_VEC_0]) THEN
    UNDISCH_TAC
     `!l. l < L /\ (!i. i IN 1..n ==> ~((kk:num->num) i = l))
          ==> !k. k < K ==> (p:num->num->complex) k l = Cx(&0)` THEN
    DISCH_THEN(MP_TAC o SPEC `l:num`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[IN_NUMSEG; ARITH_RULE
      `1 <= L /\ l <= L - 1 ==> l < L`]; ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
    DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL
   [`kk:num->num`;
    `\l. vsum(0..K-1) (\k. (p:num->num->complex) k l *
           (x + (beta:num->complex) j) pow k *
           ((alpha:num->complex) j * y) pow l)`;
    `1..n`] VSUM_IMAGE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[o_THM] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  REWRITE_TAC[COMPLEX_POW_MUL; COMPLEX_MUL_AC]);;

let TL_ZERO_DET_ROOTS = prove
 (`!n K (p:num->num->complex) (kk:num->num) (m:num->num)
    (alpha:num->complex) (beta:num->complex).
        (!i. i IN 1..n
             ==> m i < K /\ ~(p (m i) (kk i) = Cx(&0)) /\
                 (!k. m i < k /\ k < K ==> p k (kk i) = Cx(&0))) /\
        ~(ring_det complex_ring (1..n) (\i j. alpha j pow (kk i)) = Cx(&0))
        ==> FINITE {x | ring_det complex_ring (1..n)
                          (\i j. vsum(0..K-1) (\k. p k (kk i) *
                                                   (x + beta j) pow k) *
                                 alpha j pow (kk i)) = Cx(&0)} /\
            CARD {x | ring_det complex_ring (1..n)
                        (\i j. vsum(0..K-1) (\k. p k (kk i) *
                                                 (x + beta j) pow k) *
                               alpha j pow (kk i)) = Cx(&0)}
            <= nsum(1..n) m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!i j. ?g. i IN 1..n
              ==> g (m i) = (p:num->num->complex) (m i) (kk i) *
                            (alpha:num->complex) j pow (kk i) /\
                  !x. vsum(0..K-1) (\k. p k (kk i) *
                                        (x + (beta:num->complex) j) pow k) *
                      alpha j pow (kk i) =
                      vsum(0..m i) (\t. g t * x pow t)`
  MP_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:num`; `(m:num->num) i`;
                   `\k. (p:num->num->complex) k ((kk:num->num) i)`;
                   `(beta:num->complex) j`;
                   `(alpha:num->complex) j pow ((kk:num->num) i)`]
      TL_ZERO_POLY_SHIFT_TRUNC) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `G:num->num->num->complex`)] THEN
  MP_TAC(ISPECL
   [`n:num`; `m:num->num`; `G:num->num->num->complex`;
    `\i j x. vsum(0..K-1) (\k. (p:num->num->complex) k ((kk:num->num) i) *
                               (x + (beta:num->complex) j) pow k) *
             (alpha:num->complex) j pow (kk i)`]
    TL_ZERO_CDET_POLY) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->complex` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPLEX_POLYFUN_ROOTBOUND THEN
  DISCH_THEN(MP_TAC o SPEC `nsum(1..n) m`) THEN
  REWRITE_TAC[IN_NUMSEG; LE_0; LE_REFL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `ring_det complex_ring (1..n)
      (\i j. (G:num->num->num->complex) i j ((m:num->num) i)) =
    ring_det complex_ring (1..n)
      (\i j. (p:num->num->complex) (m i) ((kk:num->num) i) *
             (alpha:num->complex) j pow (kk i))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC RING_DET_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CDET_ROWS_CMUL; COMPLEX_ENTIRE; DE_MORGAN_THM] THEN
  ASM_SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN ASM_MESON_TAC[]);;

let TL_ZERO_GSPEC_PAIR = prove
 (`!(f:num->num->A) E.
        {f r s | r,s | (r,s) IN E} = IMAGE (\z. f (FST z) (SND z)) E`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; FST; SND] THEN
  MESON_TAC[]);;

let TL_ZERO_LEMMA = prove
 (`!a1 a2 b1 b2 K L (p:num->num->complex) E E'.
     ~(a1 = Cx(&0)) /\ ~(a2 = Cx(&0)) /\ FINITE E /\
     L <= CARD {a1 pow r * a2 pow s | r,s | (r,s) IN E} /\
     (K - 1) * L < CARD {b2 * Cx(&r) + b1 * Cx(&s) | r,s | (r,s) IN E'} /\
     (?k l. k < K /\ l < L /\ ~(p k l = Cx(&0)))
     ==> ?r s r' s'.
           (r,s) IN E /\ (r',s') IN E' /\
           ~(vsum(0..K-1) (\k. vsum(0..L-1) (\l.
               p k l * (b2 * Cx(&(r + r')) + b1 * Cx(&(s + s'))) pow k *
               (a1 pow (r + r') * a2 pow (s + s')) pow l)) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = {(a1:complex) pow r * (a2:complex) pow s |
                   r,s | (r,s) IN (E:num#num->bool)}` THEN
  ABBREV_TAC `X' = {(b2:complex) * Cx(&r) + (b1:complex) * Cx(&s) |
                    r,s | (r,s) IN (E':num#num->bool)}` THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE
   [NOT_EXISTS_THM; TAUT `~(a /\ b /\ ~c) <=> a /\ b ==> c`]) THEN
  SUBGOAL_THEN `1 <= K` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARITH_RULE `k < K ==> 1 <= K`]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:num`; `L:num`; `p:num->num->complex`] TL_ZERO_ROWDATA) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `kk:num->num`
    (X_CHOOSE_THEN `m:num->num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`n:num`; `kk:num->num`; `L:num`; `e:complex->bool`]
    TL_ZERO_VANDERMONDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[TL_ZERO_GSPEC_PAIR] THEN ASM_SIMP_TAC[FINITE_IMAGE];
    DISCH_THEN(X_CHOOSE_THEN `alpha:num->complex` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `!j. ?r s. j IN 1..n
              ==> (r,s) IN E /\
                  (alpha:num->complex) j =
                  (a1:complex) pow r * (a2:complex) pow s`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[GSYM RIGHT_IMP_EXISTS_THM] THEN
    DISCH_TAC THEN SUBGOAL_THEN `(alpha:num->complex) j IN e` MP_TAC THENL
     [ASM_SIMP_TAC[]; EXPAND_TAC "e" THEN REWRITE_TAC[IN_ELIM_THM]];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `rr:num->num` (X_CHOOSE_TAC `ss:num->num`))] THEN
  ABBREV_TAC `beta = \j. (b2:complex) * Cx(&((rr:num->num) j)) +
                         (b1:complex) * Cx(&((ss:num->num) j))` THEN
  MP_TAC(ISPECL [`n:num`; `K:num`; `p:num->num->complex`; `kk:num->num`;
                 `m:num->num`; `alpha:num->complex`; `beta:num->complex`]
    TL_ZERO_DET_ROOTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MATCH_MP_TAC(ARITH_RULE
   `!x r N. x <= r /\ N <= (K - 1) * L /\ (K - 1) * L < x
            ==> r <= N ==> F`) THEN
  EXISTS_TAC `CARD(X':complex->bool)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "X'" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `z:complex` THEN
    DISCH_THEN(X_CHOOSE_THEN `r':num` (X_CHOOSE_THEN `s':num`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    MP_TAC(ISPECL [`n:num`; `K:num`; `L:num`; `p:num->num->complex`;
                   `kk:num->num`; `alpha:num->complex`; `beta:num->complex`;
                   `(b2:complex) * Cx(&r') + (b1:complex) * Cx(&s')`;
                   `(a1:complex) pow r' * (a2:complex) pow s'`]
      TL_ZERO_DEPENDENT) THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; DE_MORGAN_THM] THEN
    X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `((rr:num->num) j,(ss:num->num) j) IN E /\
      (alpha:num->complex) j = (a1:complex) pow rr j * (a2:complex) pow ss j`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(j:num) IN 1..n` THEN SPEC_TAC(`j:num`,`j:num`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((b2:complex) * Cx(&r') + (b1:complex) * Cx(&s')) +
      (beta:num->complex) j =
      b2 * Cx(&((rr:num->num) j + r')) + b1 * Cx(&((ss:num->num) j + s'))`
    SUBST1_TAC THENL
     [EXPAND_TAC "beta" THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD; CX_ADD] THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(alpha:num->complex) j * (a1:complex) pow r' * (a2:complex) pow s' =
      a1 pow ((rr:num->num) j + r') * a2 pow ((ss:num->num) j + s')`
    SUBST1_TAC THENL
     [SUBGOAL_THEN
       `(alpha:num->complex) j =
        (a1:complex) pow ((rr:num->num) j) *
        (a2:complex) pow ((ss:num->num) j)`
      SUBST1_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[COMPLEX_POW_ADD] THEN CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`(rr:num->num) j`; `(ss:num->num) j`; `r':num`; `s':num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]];
    TRANS_TAC LE_TRANS `CARD(1..n) * (K - 1)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ARITH_RULE `m < K ==> m <= K - 1`) THEN ASM_SIMP_TAC[];
      REWRITE_TAC[CARD_NUMSEG_1] THEN GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL]]]);;

(* ------------------------------------------------------------------------- *)
(* Maximal rank of the interpolation matrix (start of Bugeaud, section 11.3) *)
(* ------------------------------------------------------------------------- *)

let TL_ZERO_VSUM_DIVMOD = prove
 (`!K L (g:num->complex).
        1 <= K /\ 1 <= L
        ==> vsum(0..K-1) (\k. vsum(0..L-1) (\l. g (k + K * l + 1))) =
            vsum(1..K * L) g`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[VSUM_VSUM_PRODUCT; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC
   [`\z:num#num. FST z + K * SND z + 1`;
    `\i:num. ((i - 1) MOD K, (i - 1) DIV K)`] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG; FST; SND;
              PAIR_EQ] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `y:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`y - 1`; `K:num`] DIVISION) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(y - 1) DIV K < L` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 <= K ==> ~(K = 0)`] THEN
      ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `K * b <= K * (L - 1) /\ K * (L - 1) + K = K * L`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
      REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
      MATCH_MP_TAC SUB_ADD THEN
      MATCH_MP_TAC(ARITH_RULE `1 * K <= L * K ==> K <= K * L`) THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a + K * b + 1) - 1 = a + K * b` SUBST1_TAC THENL
     [ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`a + K * b`; `K:num`; `b:num`; `a:num`] DIVMOD_UNIQ) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN ASM_ARITH_TAC]);;

let TL_ZERO_FINITE_RECT = prove
 (`!(f:num->num->A) R S. FINITE {f r s | r,s | r < R /\ s < S}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\z. (f:num->num->A) (FST z) (SND z))
                    ({r:num | r < R} CROSS {s:num | s < S})` THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_CROSS; FINITE_NUMSEG_LT] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS;
              FST; SND] THEN
  MESON_TAC[]);;

let TL_ZERO_CARD_CX_RECT = prove
 (`!(f:num->num->real) R S.
        CARD {Cx(f r s) | r,s | r < R /\ s < S} =
        CARD {f r s | r,s | r < R /\ s < S}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{Cx((f:num->num->real) r s) | r,s | r < R /\ s < S} =
    IMAGE Cx {f r s | r,s | r < R /\ s < S}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    SIMP_TAC[TL_ZERO_FINITE_RECT; CX_INJ]]);;

let TL_ZERO_RANK = prove
 (`!a1 a2 b1 b2 K L R1 S1 R2 S2 (c:num->num->complex).
     ~(a1 = Cx(&0)) /\ ~(a2 = Cx(&0)) /\
     L <= CARD {a1 pow r * a2 pow s | r,s | r < R1 /\ s < S1} /\
     (K - 1) * L < CARD {b2 * &r + b1 * &s | r,s | r < R2 /\ s < S2} /\
     (!r s. r < R1 + R2 - 1 /\ s < S1 + S2 - 1
            ==> vsum(0..K-1) (\k. vsum(0..L-1) (\l.
                  c k l * Cx(b2 * &r + b1 * &s) pow k *
                  (a1 pow r * a2 pow s) pow l)) = Cx(&0))
     ==> !k l. k < K /\ l < L ==> c k l = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  MP_TAC(ISPECL [`a1:complex`; `a2:complex`; `Cx b1`; `Cx b2`;
                 `K:num`; `L:num`; `c:num->num->complex`;
                 `{r:num | r < R1} CROSS {s:num | s < S1}`;
                 `{r:num | r < R2} CROSS {s:num | s < S2}`] TL_ZERO_LEMMA) THEN
  ANTS_TAC THENL
   [SIMP_TAC[IN_CROSS; IN_ELIM_THM; FINITE_CROSS; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[GSYM CX_MUL; GSYM CX_ADD; TL_ZERO_CARD_CX_RECT] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` (X_CHOOSE_THEN `s:num`
    (X_CHOOSE_THEN `r':num` (X_CHOOSE_THEN `s':num` MP_TAC)))) THEN
  REWRITE_TAC[IN_CROSS; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r + r':num`; `s + s':num`]) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`r < R1`; `s < S1`; `r' < R2`; `s' < S2`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CX_ADD; CX_MUL] THEN ASM_REWRITE_TAC[]);;

let TL_ZERO_RANK_MINOR = prove
 (`!a1 a2 b1 b2 K L R1 S1 R2 S2.
     ~(a1 = Cx(&0)) /\ ~(a2 = Cx(&0)) /\
     L <= CARD {a1 pow r * a2 pow s | r,s | r < R1 /\ s < S1} /\
     (K - 1) * L < CARD {b2 * &r + b1 * &s | r,s | r < R2 /\ s < S2}
     ==> ?rr ss.
           (!j. j IN 1..K * L
                ==> rr j < R1 + R2 - 1 /\ ss j < S1 + S2 - 1) /\
           (!j j'. j IN 1..K * L /\ j' IN 1..K * L /\
                   rr j = rr j' /\ ss j = ss j' ==> j = j') /\
           ~(ring_det complex_ring (1..K * L)
               (\i j. Cx(b2 * &(rr j) + b1 * &(ss j)) pow ((i - 1) MOD K) *
                      (a1 pow (rr j) * a2 pow (ss j)) pow ((i - 1) DIV K)) =
             Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `K * L = 0` THENL
   [ASM_REWRITE_TAC[NUMSEG_CLAUSES; RING_DET_EMPTY; COMPLEX_RING_CLAUSES;
                    IN_NUMSEG; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ] THEN
    MAP_EVERY EXISTS_TAC [`\j:num. 0`; `\j:num. 0`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= K /\ 1 <= L` STRIP_ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[MULT_EQ_0] THEN ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`K * L`; `{z:num#num | FST z < R1 + R2 - 1 /\ SND z < S1 + S2 - 1}`;
    `\i (z:num#num). Cx(b2 * &(FST z) + b1 * &(SND z)) pow ((i - 1) MOD K) *
                     ((a1:complex) pow (FST z) * (a2:complex) pow (SND z)) pow
                     ((i - 1) DIV K)`]
    CDET_MINOR_SELECTION) THEN
  REWRITE_TAC[IN_ELIM_THM; FORALL_PAIR_THM; FST; SND] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `{r:num | r < R1 + R2 - 1} CROSS {s:num | s < S1 + S2 - 1}` THEN
      SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG_LT] THEN
      REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM; FST; SND];
      ALL_TAC] THEN
    X_GEN_TAC `c:num->complex` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a1:complex`; `a2:complex`; `b1:real`; `b2:real`;
                   `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`;
                   `\k l. (c:num->complex) (k + K * l + 1)`] TL_ZERO_RANK) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [MAP_EVERY X_GEN_TAC [`r:num`; `s:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r:num`; `s:num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`K:num`; `L:num`;
        `\i. (c:num->complex) i * Cx(b2 * &r + b1 * &s) pow ((i - 1) MOD K) *
             ((a1:complex) pow r * (a2:complex) pow s) pow ((i - 1) DIV K)`]
        TL_ZERO_VSUM_DIVMOD) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `k:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `l:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(k + K * l + 1) - 1 = l * K + k` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`l * K + k`; `K:num`; `l:num`; `k:num`] DIVMOD_UNIQ) THEN
      ANTS_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`k <= K - 1`; `1 <= K`] THEN ARITH_TAC;
        SIMP_TAC[]];
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`i - 1`; `K:num`] DIVISION) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
      SUBGOAL_THEN `(i - 1) DIV K < L` ASSUME_TAC THENL
       [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 <= K ==> ~(K = 0)`] THEN
        ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `i = (i - 1) MOD K + K * (i - 1) DIV K + 1`
      SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`i - 1 = (i - 1) DIV K * K + (i - 1) MOD K`; `1 <= i`] THEN
        ARITH_TAC;
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->num#num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`\j. FST((g:num->num#num) j)`; `\j. SND((g:num->num#num) j)`] THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[PAIR]);;

(* ------------------------------------------------------------------------- *)
(* The rational real form used in the final assembly (Baker/twolog.ml).      *)
(* ------------------------------------------------------------------------- *)

let TL_ZERO_CARD_REAL_RECT = prove
 (`!(f:num->num->num) R S.
        CARD {real_of_num(f r s) | r,s | r < R /\ s < S} =
        CARD {f r s | r,s | r < R /\ s < S}`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `{real_of_num((f:num->num->num) r s) | r,s | r < R /\ s < S} =
    IMAGE real_of_num {f r s | r,s | r < R /\ s < S}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    SIMP_TAC[TL_ZERO_FINITE_RECT; REAL_OF_NUM_EQ]]);;

let TWOLOG_ZERO_MINOR = prove
 (`!p1 q1 p2 q2 b1 b2 K L R1 S1 R2 S2.
     1 <= p1 /\ 1 <= q1 /\ 1 <= p2 /\ 1 <= q2 /\ 1 <= b1 /\ 1 <= b2 /\
     1 <= K /\ 1 <= L /\
     L <= CARD {(&p1 / &q1) pow r * (&p2 / &q2) pow s | r,s |
                r < R1 /\ s < S1} /\
     (K - 1) * L < CARD {r * b2 + s * b1 | r,s | r < R2 /\ s < S2}
     ==> ?rr ss. (!j. j IN 1..K * L
                      ==> rr j < R1 + R2 - 1 /\ ss j < S1 + S2 - 1) /\
                 ~(ring_det real_ring (1..K * L)
                     (\i j. &(rr j * b2 + ss j * b1) pow ((i - 1) MOD K) *
                            (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
                            (&p2 / &q2) pow (((i - 1) DIV K) * ss j)) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(Cx(&p1 / &q1) = Cx(&0)) /\ ~(Cx(&p2 / &q2) = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_DIV_EQ_0; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `L <= CARD {Cx(&p1 / &q1) pow r * Cx(&p2 / &q2) pow s | r,s |
               r < R1 /\ s < S1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[GSYM CX_POW; GSYM CX_MUL; TL_ZERO_CARD_CX_RECT] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(K - 1) * L < CARD {(&b2:real) * &r + &b1 * &s | r,s | r < R2 /\ s < S2}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `!r s. (&b2:real) * &r + &b1 * &s = &(r * b2 + s * b1)`
     (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[TL_ZERO_CARD_REAL_RECT] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Cx(&p1 / &q1)`; `Cx(&p2 / &q2)`; `&b1:real`; `&b2:real`;
                 `K:num`; `L:num`; `R1:num`; `S1:num`; `R2:num`; `S2:num`]
    TL_ZERO_RANK_MINOR) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `rr:num->num` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `ss:num->num` THEN
  MATCH_MP_TAC(TAUT `(c ==> c') ==> a /\ b /\ c ==> a /\ c'`) THEN
  SUBGOAL_THEN
   `!i j. Cx(&b2 * &((rr:num->num) j) + &b1 * &((ss:num->num) j)) pow
          ((i - 1) MOD K) *
          (Cx(&p1 / &q1) pow rr j * Cx(&p2 / &q2) pow ss j) pow
          ((i - 1) DIV K) =
          Cx(&(rr j * b2 + ss j * b1) pow ((i - 1) MOD K) *
             (&p1 / &q1) pow (((i - 1) DIV K) * rr j) *
             (&p2 / &q2) pow (((i - 1) DIV K) * ss j))`
   (fun th -> REWRITE_TAC[th; CDET_CX; CX_INJ]) THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(&b2:real) * &((rr:num->num) j) + &b1 * &((ss:num->num) j) =
    &(rr j * b2 + ss j * b1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM REAL_OF_NUM_ADD; GSYM REAL_OF_NUM_MUL] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[CX_MUL; CX_POW; COMPLEX_POW_MUL; COMPLEX_POW_POW] THEN
    REWRITE_TAC[MULT_SYM]]);;
