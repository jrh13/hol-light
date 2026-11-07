(* ========================================================================= *)
(* The final step of Baker, Ch. 3, sec. 4: an integer relation.              *)
(*                                                                           *)
(* Purpose: if the auxiliary exponential polynomial                          *)
(*   sum_(a,b,mu) p(a,b,mu) B_{a,b}(l/k) cexp(l (sum_r mu_r lg_r) / k)       *)
(* (B_{a,b} = feldman_basis h a b, a < h, b <= L, 0 <= mu_r <= L) vanishes   *)
(* at l = 0, ..., h(L+2)(L+1)^n - 1 and p is not identically zero, then two  *)
(* distinct nodes cexp((sum_r mu_r lg_r) / k) coincide, and if moreover      *)
(* L (|lg_1| + ... + |lg_n|) < 2 pi k there are integers b_r, |b_r| <= L,    *)
(* not all zero, with b_1 lg_1 + ... + b_n lg_n = 0 (Baker, Transcendental   *)
(* Number Theory, Ch. 3, sec. 4). Baker Lemma 2 is replaced by the pairwise  *)
(* distinct degrees a + h(b+1) of the B_{a,b}, Baker Lemma 3 by              *)
(* EXPOLY_UNIQUENESS_POLYFUN.                                                *)
(*                                                                           *)
(* Main results: BAKER_INTEGER_RELATION, BAKER_NODES_COINCIDE;               *)
(*   COMPLEX_POLYFUN_VSUM, COMPLEX_POLYFUN_SCALE_ARG,                        *)
(*   FELDMAN_BASIS_DEGREE_INJ, FELDMAN_BASIS_DEGREE_BOUND.                   *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (COMPLEX_POLYFUN_TRUNCATE), Baker/intpoly.ml        *)
(*   (cartesian products), Baker/delta.ml (FELDMAN_BASIS_POLYFUN),           *)
(*   Baker/expoly.ml (EXPOLY_UNIQUENESS_POLYFUN,                             *)
(*   COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN), Baker/auxiliary.ml               *)
(*   (baker_index).                                                          *)
(* ========================================================================= *)

needs "Baker/expoly.ml";;
needs "Baker/auxiliary.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Polynomial helpers: finite sums of polynomials of degree <= d, scaling of *)
(* the argument, and the degrees a + h(b+1) of the Feldman basis.            *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_POLYFUN_VSUM = prove
 (`!s (f:A->complex->complex) d.
        FINITE s /\
        (!i. i IN s ==> ?c. !z. f i z = vsum(0..d) (\t. c t * z pow t))
        ==> ?c. !z. vsum s (\i. f i z) = vsum(0..d) (\t. c t * z pow t)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_TAC `c:A->num->complex`) THEN
  EXISTS_TAC `\t. vsum s (\i. (c:A->num->complex) i t)` THEN
  X_GEN_TAC `z:complex` THEN
  TRANS_TAC EQ_TRANS
   `vsum s (\i. vsum(0..d) (\t. (c:A->num->complex) i t * z pow t))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_NUMSEG] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) VSUM_SWAP o lhand o snd) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG]]);;

let COMPLEX_POLYFUN_SCALE_ARG = prove
 (`!f (e:num->complex) d D u w.
        d <= D /\ (!z. f z = vsum(0..d) (\i. e i * z pow i))
        ==> ?c. !x. u * f(x / w) = vsum(0..D) (\t. c t * x pow t)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `\t. if t <= d then u * (e:num->complex) t / w pow t else Cx(&0)` THEN
  X_GEN_TAC `x:complex` THEN ASM_SIMP_TAC[COMPLEX_POLYFUN_TRUNCATE] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[COMPLEX_POW_DIV; complex_div] THEN CONV_TAC COMPLEX_RING);;

let FELDMAN_BASIS_DEGREE_INJ = prove
 (`!h a b a' b'.
        a < h /\ a' < h /\ a + h * (b + 1) = a' + h * (b' + 1)
        ==> a = a' /\ b = b'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`a + h * (b + 1)`; `h:num`; `b + 1`; `a:num`] DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`a' + h * (b' + 1)`; `h:num`; `b' + 1`; `a':num`]
         DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_eq o concl)) THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let FELDMAN_BASIS_DEGREE_BOUND = prove
 (`!h L a b. a < h /\ b <= L ==> a + h * (b + 1) <= h * (L + 2) - 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `h * (b + 1) <= h * (L + 1)` MP_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Two distinct nodes coincide. Grouping the sum by mu gives an exponential  *)
(* polynomial sum_mu P_mu(l) w_mu^l with P_mu of degree <= h(L+2) - 1 and    *)
(* (L+1)^n nodes w_mu; if the nodes were distinct, all P_mu would vanish     *)
(* identically, and by the distinct degrees so would p.                      *)
(* ------------------------------------------------------------------------- *)

let BAKER_NODES_COINCIDE = prove
 (`!n h L k (p:num#num#(num->num)->real) (lg:num->complex).
     1 <= n /\ 1 <= h /\ 1 <= k /\
     ~(!x. x IN baker_index h L n ==> p x = &0) /\
     (!l. l < h * (L + 2) * (L + 1) EXP n
          ==> vsum (baker_index h L n)
               (\(a,b,mu). Cx(p(a,b,mu)) *
                           feldman_basis h a b (Cx(&l) / Cx(&k)) *
                           cexp(Cx(&l) * vsum(1..n) (\r. Cx(&(mu r)) * lg r) /
                                Cx(&k))) = Cx(&0))
     ==> ?mu mu'. mu IN cartesian_product (1..n) (\r. 0..L) /\
                  mu' IN cartesian_product (1..n) (\r. 0..L) /\
                  ~(mu = mu') /\
                  cexp(vsum(1..n) (\r. Cx(&(mu r)) * lg r) / Cx(&k)) =
                  cexp(vsum(1..n) (\r. Cx(&(mu' r)) * lg r) / Cx(&k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  MATCH_MP_TAC(TAUT `(~c ==> a) ==> ~a ==> c`) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!mu x. mu IN cartesian_product (1..n) (\r:num. 0..L)
           ==> vsum {y | y IN baker_index h L n /\ SND(SND y) = mu}
                    (\y. Cx(p y) * feldman_basis h (FST y) (FST(SND y))
                                     (x / Cx(&k))) = Cx(&0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL
     [`cartesian_product (1..n) (\r:num. 0..L)`;
      `\mu:num->num. cexp(vsum(1..n) (\r. Cx(&(mu r)) * lg r) / Cx(&k))`;
      `\mu:num->num. h * (L + 2) - 1`;
      `\(mu:num->num) (x:complex).
         vsum {y | y IN baker_index h L n /\ SND(SND y) = mu}
              (\y. Cx(p y) * feldman_basis h (FST y) (FST(SND y))
                               (x / Cx(&k)))`]
     EXPOLY_UNIQUENESS_POLYFUN) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_CARTESIAN_PRODUCT_FINITE THEN
      REWRITE_TAC[FINITE_NUMSEG];
      REWRITE_TAC[CEXP_NZ];
      ASM_MESON_TAC[];
      X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPLEX_POLYFUN_VSUM THEN
      SIMP_TAC[FINITE_RESTRICT; FINITE_BAKER_INDEX] THEN
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; FST; SND] THEN
      MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `nu:num->num`] THEN
      REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG] THEN
      STRIP_TAC THEN
      MP_TAC(SPECL [`h:num`; `a:num`; `b:num`] FELDMAN_BASIS_POLYFUN) THEN
      DISCH_THEN(X_CHOOSE_THEN `e:num->complex` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC COMPLEX_POLYFUN_SCALE_ARG THEN
      MAP_EVERY EXISTS_TAC [`e:num->complex`; `a + h * (b + 1)`] THEN
      ASM_SIMP_TAC[FELDMAN_BASIS_DEGREE_BOUND];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `nsum (cartesian_product (1..n) (\r:num. 0..L))
           (\mu. h * (L + 2) - 1 + 1) =
      h * (L + 2) * (L + 1) EXP n`
    SUBST1_TAC THENL
     [SIMP_TAC[NSUM_CONST; FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG] THEN
      SIMP_TAC[CARD_CARTESIAN_PRODUCT; FINITE_NUMSEG; CARD_NUMSEG; SUB_0;
               NPRODUCT_CONST_NUMSEG_1] THEN
      SUBGOAL_THEN `h * (L + 2) - 1 + 1 = h * (L + 2)` SUBST1_TAC THENL
       [MATCH_MP_TAC SUB_ADD THEN
        REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; MULT_EQ_0] THEN
        ASM_ARITH_TAC;
        REWRITE_TAC[MULT_AC]];
      ALL_TAC] THEN
    X_GEN_TAC `l:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `l:num`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[] `(b:complex) = a ==> a = z ==> b = z`) THEN
    W(fun (_,w) -> MP_TAC(ISPECL
     [`\y:num#num#(num->num). SND(SND y)`; rand(rand w);
      `baker_index h L n`; `cartesian_product (1..n) (\r:num. 0..L)`]
     VSUM_GROUP)) THEN
    REWRITE_TAC[FINITE_BAKER_INDEX] THEN ANTS_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_PAIR_THM; baker_index;
                  IN_CROSS] THEN SIMP_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `mu:num->num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_RMUL; FINITE_RESTRICT; FINITE_BAKER_INDEX] THEN
    MATCH_MP_TAC VSUM_EQ THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `nu:num->num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    REWRITE_TAC[CEXP_N; COMPLEX_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `mu IN cartesian_product (1..n) (\r:num. 0..L)` ASSUME_TAC THENL
   [UNDISCH_TAC `(a,b,mu) IN baker_index h L n` THEN
    SIMP_TAC[baker_index; IN_CROSS];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{y | y IN baker_index h L n /\ SND(SND y) = (mu:num->num)}`;
    `\(y:num#num#(num->num)) (z:complex).
       feldman_basis h (FST y) (FST(SND y)) z`;
    `\y:num#num#(num->num). FST y + h * (FST(SND y) + 1)`;
    `\y:num#num#(num->num). Cx(p y)`]
   COMPLEX_POLYFUN_DISTINCT_DEGREES_FUN) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SIMP_TAC[FINITE_RESTRICT; FINITE_BAKER_INDEX];
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; FST; SND] THEN
      REWRITE_TAC[FELDMAN_BASIS_POLYFUN];
      REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; FST; SND; PAIR_EQ] THEN
      REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM] THEN
      MESON_TAC[FELDMAN_BASIS_DEGREE_INJ];
      X_GEN_TAC `z:complex` THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`mu:num->num`; `Cx(&k) * z`]) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(Cx(&k) * z) / Cx(&k) = z` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC(COMPLEX_FIELD `~(u = Cx(&0)) ==> (u * v) / u = v`) THEN
      REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC];
    DISCH_THEN(MP_TAC o SPEC `(a,b,mu):num#num#(num->num)`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; FST; SND; CX_INJ]]);;

(* ------------------------------------------------------------------------- *)
(* The integer relation: equal nodes give (X - Y) / k = 2 pi i j with an     *)
(* integer j, and |X - Y| <= L sum_r |lg r| < 2 pi k forces j = 0.           *)
(* ------------------------------------------------------------------------- *)

let VSUM_NUM_COMB_SUB_NORM_LE = prove
 (`!n L (mu:num->num) mu' (lg:num->complex).
        (!r. r IN 1..n ==> mu r <= L /\ mu' r <= L)
        ==> norm(vsum(1..n) (\r. Cx(&(mu r)) * lg r) -
                 vsum(1..n) (\r. Cx(&(mu' r)) * lg r))
            <= &L * sum(1..n) (\r. norm(lg r))`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM VSUM_SUB; FINITE_NUMSEG; GSYM SUM_LMUL] THEN
  MATCH_MP_TAC VSUM_NORM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
  X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM COMPLEX_SUB_RDISTRIB; GSYM CX_SUB; COMPLEX_NORM_MUL;
              COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let BAKER_INTEGER_RELATION = prove
 (`!n h L k (p:num#num#(num->num)->real) (lg:num->complex).
     1 <= n /\ 1 <= h /\ 1 <= k /\
     ~(!x. x IN baker_index h L n ==> p x = &0) /\
     (!l. l < h * (L + 2) * (L + 1) EXP n
          ==> vsum (baker_index h L n)
               (\(a,b,mu). Cx(p(a,b,mu)) *
                           feldman_basis h a b (Cx(&l) / Cx(&k)) *
                           cexp(Cx(&l) * vsum(1..n) (\r. Cx(&(mu r)) * lg r) /
                                Cx(&k))) = Cx(&0)) /\
     &L * sum(1..n) (\r. norm(lg r)) < &2 * pi * &k
     ==> ?b:num->real.
           (!r. r IN 1..n ==> integer(b r) /\ abs(b r) <= &L) /\
           ~(!r. r IN 1..n ==> b r = &0) /\
           vsum(1..n) (\r. Cx(b r) * lg r) = Cx(&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `h:num`; `L:num`; `k:num`;
                `p:num#num#(num->num)->real`; `lg:num->complex`]
         BAKER_NODES_COINCIDE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:num->num` (X_CHOOSE_THEN `mu':num->num`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!r. r IN 1..n ==> (mu:num->num) r <= L /\ (mu':num->num) r <= L`
  ASSUME_TAC THENL
   [UNDISCH_TAC `mu IN cartesian_product (1..n) (\r:num. 0..L)` THEN
    UNDISCH_TAC `mu' IN cartesian_product (1..n) (\r:num. 0..L)` THEN
    REWRITE_TAC[IN_CARTESIAN_PRODUCT; IN_NUMSEG] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `cexp(vsum(1..n) (\r. Cx(&(mu r)) * lg r) / Cx(&k)) =
    cexp(vsum(1..n) (\r. Cx(&(mu' r)) * lg r) / Cx(&k))` THEN
  REWRITE_TAC[CEXP_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `vsum(1..n) (\r. Cx(&(mu r)) * lg r) -
    vsum(1..n) (\r. Cx(&(mu' r)) * lg r) =
    Cx(&k) * Cx(&2 * j * pi) * ii`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(Cx(&k) = Cx(&0))` MP_TAC THENL
     [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC
     `vsum(1..n) (\r. Cx(&(mu r)) * lg r) / Cx(&k) =
      vsum(1..n) (\r. Cx(&(mu' r)) * lg r) / Cx(&k) +
      Cx(&2 * j * pi) * ii` THEN
    SPEC_TAC(`vsum(1..n) (\r. Cx(&(mu r)) * lg r)`,`u:complex`) THEN
    SPEC_TAC(`vsum(1..n) (\r. Cx(&(mu' r)) * lg r)`,`v:complex`) THEN
    SPEC_TAC(`Cx(&2 * j * pi)`,`c:complex`) THEN
    SPEC_TAC(`Cx(&k)`,`w:complex`) THEN
    CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(j:real) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `&2 * pi * &k` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN REWRITE_TAC[PI_POS; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`n:num`; `L:num`; `mu:num->num`; `mu':num->num`;
                  `lg:num->complex`] VSUM_NUM_COMB_SUB_NORM_LE) THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_II;
                    REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_PI] THEN
    UNDISCH_TAC `&L * sum(1..n) (\r. norm(lg r:complex)) < &2 * pi * &k` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `j = &0` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_INTEGER_LEMMA; REAL_NOT_LE]; ALL_TAC] THEN
  EXISTS_TAC `\r. &((mu:num->num) r) - &((mu':num->num) r):real` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN SIMP_TAC[INTEGER_CLOSED] THEN
    UNDISCH_TAC
     `!r. r IN 1..n ==> (mu:num->num) r <= L /\ (mu':num->num) r <= L` THEN
    DISCH_THEN(MP_TAC o SPEC `r:num`) THEN
    ASM_REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    DISCH_TAC THEN UNDISCH_TAC `~(mu:num->num = mu')` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC CARTESIAN_PRODUCT_EQ_MEMBERS THEN
    MAP_EVERY EXISTS_TAC [`1..n`; `\r:num. 0..L`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!r. r IN 1..n ==> &((mu:num->num) r) - &((mu':num->num) r) = &0` THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[REAL_SUB_0; REAL_OF_NUM_EQ];
    REWRITE_TAC[CX_SUB; COMPLEX_SUB_RDISTRIB] THEN
    SIMP_TAC[VSUM_SUB; FINITE_NUMSEG] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_RZERO; COMPLEX_MUL_LZERO;
                COMPLEX_MUL_RZERO]]);;
