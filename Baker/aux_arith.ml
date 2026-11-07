(* ========================================================================= *)
(* Arithmetic of the auxiliary function: Baker Lemmas 4, 5 and 7.            *)
(*                                                                           *)
(* Purpose: the algebraic counterpart of the auxiliary function at an        *)
(* integer point l, multiplied by the denominators N^(m 0) g_n^|m|, is an    *)
(* integer polynomial expression (intpoly) in the algebraic numbers          *)
(* involved, with explicit bounds (Baker, Transcendental Number Theory,      *)
(* Ch. 3). The Siegel lemma then gives Lemma 4 (integers p, not all 0, of    *)
(* controlled size, such that the counterpart vanishes at l = 1..h for       *)
(* |m| <= k), and the Liouville inequality gives the second parts of Lemma 5 *)
(* (a nonzero value at an integer is not too small) and of Lemma 7 (the same *)
(* at a rational point l/k with m = 0, the numbers cexp(lg_r / k) being      *)
(* roots of a_r(x^k)).                                                       *)
(*                                                                           *)
(* Main results: BAKER_LEMMA4_ARITH, BAKER_LEMMA5_ARITH, BAKER_LEMMA7_ARITH, *)
(*   BAKER_ALG_ZERO (the counterpart for m = 0), CARD_BAKER_INDEX,           *)
(*   CEXP_LINEAR_COMBINATION_NUM, CEXP_LINEAR_COMBINATION_RATIONAL,          *)
(*   CEXP_DIV_POW, NSUM_RESTRICTION.                                         *)
(*                                                                           *)
(* Uses: Baker/lemmas.ml (CPRODUCT_POW_NSUM), Library/products.ml            *)
(*   (REAL_POW_NSUM), Baker/intpoly.ml (intpoly),                            *)
(*   Baker/liouville_inequality.ml (INTPOLY_LIOUVILLE), Baker/siegel.ml      *)
(*   (ALGEBRAIC_SIEGEL), Baker/delta.ml (feldman_basis), Baker/auxiliary.ml  *)
(*   (baker_index, baker_alg).                                               *)
(* ========================================================================= *)

needs "Baker/liouville_inequality.ml";;
needs "Baker/siegel.ml";;
needs "Baker/auxiliary.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Rearranging the algebraic term.                                           *)
(* ------------------------------------------------------------------------- *)

let CEXP_LINEAR_COMBINATION_NUM = prove
 (`!s (lg:num->complex) mu l.
        FINITE s
        ==> cexp(Cx(&l) * vsum s (\r. Cx(&(mu r)) * lg r)) =
            cproduct s (\r. cexp(lg r) pow (mu r * l))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; CEXP_VSUM] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM CEXP_N; COMPLEX_MUL_ASSOC; GSYM CX_MUL; REAL_OF_NUM_MUL] THEN
  REWRITE_TAC[MULT_SYM]);;

let BAKER_ALGTERM_REARRANGE = prove
 (`!n h beta lg theta (gg:num->complex) N l m a b mu.
        1 <= n /\
        (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
        (!j. j < n ==> beta j * gg n = --(gg j))
        ==> Cx(&N) pow (m 0) * gg n pow (nsum(0..n-1) m) *
            baker_algterm n h (\x. &1) beta lg m (a,b,mu) (Cx(&l)) =
            vsum(0..m 0)
             (\j. Cx(&(binom(m 0,j))) * Cx(&N) pow (m 0 - j) *
                  Cx(&(FACT j)) *
                  (Cx(&N) pow j *
                   higher_complex_derivative j (feldman_basis h a b) (Cx(&l)) /
                   Cx(&(FACT j))) *
                  gg n pow j * (--(Cx(&(mu n)) * gg 0)) pow (m 0 - j)) *
            cproduct(1..n-1)
             (\r. (Cx(&(mu r)) * gg n - Cx(&(mu n)) * gg r) pow (m r)) *
            cproduct(1..n) (\r. theta r pow (mu r * l))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[baker_algterm; COMPLEX_MUL_LID] THEN
  SIMP_TAC[CEXP_LINEAR_COMBINATION_NUM; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `cproduct(1..n) (\r. cexp(lg r) pow (mu r * l)) =
    cproduct(1..n) (\r. (theta:num->complex) r pow (mu r * l))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `0 <= n - 1` (fun th ->
    REWRITE_TAC[MATCH_MP NSUM_CLAUSES_LEFT th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD_CLAUSES; COMPLEX_POW_ADD] THEN
  SIMP_TAC[GSYM CPRODUCT_POW_NSUM; FINITE_NUMSEG] THEN
  SUBGOAL_THEN
   `cproduct(1..n-1) (\r. (gg:num->complex) n pow (m r)) *
    cproduct(1..n-1) (\r. baker_gamma n beta mu r pow (m r)) =
    cproduct(1..n-1)
     (\r. (Cx(&(mu r)) * gg n - Cx(&(mu n)) * gg r) pow (m r))`
  MP_TAC THENL
   [SIMP_TAC[GSYM CPRODUCT_MUL; FINITE_NUMSEG; GSYM COMPLEX_POW_MUL] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `r:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[baker_gamma] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `Cx(&N) pow (m 0) * gg n pow (m 0) *
    vsum(0..m 0) (\j. Cx(&(binom(m 0,j))) *
                      higher_complex_derivative j (feldman_basis h a b)
                        (Cx(&l)) *
                      (Cx(&(mu n)) * beta 0) pow (m 0 - j)) =
    vsum(0..m 0)
     (\j. Cx(&(binom(m 0,j))) * Cx(&N) pow (m 0 - j) *
          Cx(&(FACT j)) *
          (Cx(&N) pow j *
           higher_complex_derivative j (feldman_basis h a b) (Cx(&l)) /
           Cx(&(FACT j))) *
          (gg:num->complex) n pow j * (--(Cx(&(mu n)) * gg 0)) pow (m 0 - j))`
  MP_TAC THENL
   [SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_NUMSEG] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `Cx(&N) pow (m 0) = Cx(&N) pow (m 0 - j) * Cx(&N) pow j /\
      (gg:num->complex) n pow (m 0) = gg n pow j * gg n pow (m 0 - j)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN ANTS_TAC THENL
     [ASM_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(--(Cx(&((mu:num->num) n)) * gg 0)) pow (m 0 - j) =
      (Cx(&(mu n)) * beta 0) pow (m 0 - j) * (gg:num->complex) n pow (m 0 - j)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM COMPLEX_POW_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      UNDISCH_TAC `beta 0 * (gg:num->complex) n = --(gg 0)` THEN
      CONV_TAC COMPLEX_RING;
      ALL_TAC] THEN
    MP_TAC(SPEC `j:num` FACT_NZ) THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_EQ; GSYM CX_INJ] THEN
    SPEC_TAC(`higher_complex_derivative j (feldman_basis h a b) (Cx(&l))`,
             `dd:complex`) THEN
    GEN_TAC THEN CONV_TAC COMPLEX_FIELD;
    ALL_TAC] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* The factors as integer polynomial expressions.                            *)
(* ------------------------------------------------------------------------- *)

let BAKER_DSUM_INTPOLY = prove
 (`!h L (g:num->(num->complex)->complex) V e G N l m0 a b nn mun.
        1 <= L /\ &1 <= G /\ FINITE V /\
        intpoly V e G (g nn) /\ intpoly V e G (g 0) /\
        a < h /\ b <= L /\ mun <= L /\
        (!i. 1 <= i /\ i <= h ==> (l + i) divides N)
        ==> intpoly V (\r. m0 * e r)
             (&N pow m0 * &2 pow ((L + 2) * ((l + 1) + h)) *
              (&m0 + &1) pow m0 * (&2 * &L * G) pow m0)
             (\x. vsum(0..m0)
                   (\j. Cx(&(binom(m0,j))) * Cx(&N) pow (m0 - j) *
                        Cx(&(FACT j)) *
                        (Cx(&N) pow j *
                         higher_complex_derivative j (feldman_basis h a b)
                           (Cx(&l)) /
                         Cx(&(FACT j))) *
                        g nn x pow j * (--(Cx(&mun) * g 0 x)) pow (m0 - j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= G` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &2 * &L * G` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[REAL_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?kappa. !j. integer(kappa j) /\
                Cx(kappa j) =
                Cx(&N) pow j *
                higher_complex_derivative j (feldman_basis h a b) (Cx(&l)) /
                Cx(&(FACT j))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`h:num`; `a:num`; `b:num`; `l:num`; `N:num`]
           FELDMAN_BASIS_DERIV_INTEGER) THEN
    ASM_SIMP_TAC[LT_IMP_LE] THEN DISCH_THEN(MP_TAC o SPEC `j:num`) THEN
    REWRITE_TAC[COMPLEX_INTEGER; complex_div; COMPLEX_MUL_ASSOC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. abs(kappa j) <= &N pow j * &2 pow ((L + 2) * ((l + 1) + h))`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o SPEC `j:num`) THEN
    DISCH_THEN(MP_TAC o AP_TERM `norm:complex->real`) THEN
    REWRITE_TAC[COMPLEX_NORM_CX] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[complex_div; GSYM COMPLEX_MUL_ASSOC; COMPLEX_NORM_MUL;
                COMPLEX_NORM_POW; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    REWRITE_TAC[GSYM COMPLEX_NORM_MUL; GSYM complex_div] THEN
    MATCH_MP_TAC FELDMAN_BASIS_DERIV_BOUND_UNIFORM THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_ABS_NUM; GSYM REAL_OF_NUM_ADD] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTPOLY_EQ THEN
  EXISTS_TAC
   `\x. vsum(0..m0)
         (\j. Cx(&(binom(m0,j)) * &N pow (m0 - j) * &(FACT j) * kappa j) *
              ((g:num->(num->complex)->complex) nn x pow j *
               (--(Cx(&mun) * g 0 x)) pow (m0 - j)))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:num->complex` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC VSUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CX_MUL; CX_POW; GSYM COMPLEX_MUL_ASSOC]] THEN
  MATCH_MP_TAC INTPOLY_MONO THEN
  EXISTS_TAC `\r:num. m0 * e r` THEN
  EXISTS_TAC
   `sum(0..m0) (\j. abs(&(binom(m0,j)) * &N pow (m0 - j) * &(FACT j) *
                         kappa j) *
                    (G pow j * (&mun * G) pow (m0 - j)))` THEN
  REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_VSUM THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC INTPOLY_CMUL THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[INTEGER_MUL; INTEGER_CLOSED]; ALL_TAC] THEN
    MATCH_MP_TAC INTPOLY_MONO THEN
    EXISTS_TAC `\r:num. j * e r + (m0 - j) * e r` THEN
    EXISTS_TAC `G pow j * (&mun * G) pow (m0 - j)` THEN
    REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTPOLY_MUL THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC INTPOLY_POW THEN ASM_SIMP_TAC[ETA_AX] THEN
      MATCH_MP_TAC INTPOLY_NEG THEN
      MP_TAC(ISPECL [`V:num->bool`; `e:num->num`; `G:real`;
                     `(g:num->(num->complex)->complex) 0`; `&mun`]
             INTPOLY_CMUL) THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM];
      REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
      ASM_SIMP_TAC[ARITH_RULE `j <= m0 ==> j + m0 - j = m0`; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `G <= &2 * &L * G /\ &mun * G <= &2 * &L * G`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MUL_ASSOC] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_RMUL;
      MATCH_MP_TAC REAL_LE_RMUL] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `1 <= L` THEN UNDISCH_TAC `mun <= L` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum(0..m0) (\j. &(binom(m0,j)) * &(FACT j)) *
    (&N pow m0 * &2 pow ((L + 2) * ((l + 1) + h)) * (&2 * &L * G) pow m0)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_NUM; REAL_ABS_POW] THEN
    SUBGOAL_THEN `&N pow m0 = &N pow (m0 - j) * &N pow j /\
                  (&2 * &L * G) pow m0 =
                  (&2 * &L * G) pow j * (&2 * &L * G) pow (m0 - j)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [REWRITE_TAC[GSYM REAL_POW_ADD] THEN CONJ_TAC THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!x y bf n1 k g kb hh:real.
        x = (bf * n1) * (k * g) /\ y = (bf * n1) * (kb * hh) /\
        (bf * n1) * (k * g) <= (bf * n1) * (kb * hh) ==> x <= y`) THEN
    EXISTS_TAC `&(binom(m0,j)) * &(FACT j)` THEN
    EXISTS_TAC `&N pow (m0 - j)` THEN EXISTS_TAC `abs((kappa:num->real) j)` THEN
    EXISTS_TAC `G pow j * (&mun * G) pow (m0 - j)` THEN
    EXISTS_TAC `&N pow j * &2 pow ((L + 2) * ((l + 1) + h))` THEN
    EXISTS_TAC `(&2 * &L * G) pow j * (&2 * &L * G) pow (m0 - j)` THEN
    REPEAT CONJ_TAC THENL [REAL_ARITH_TAC; REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_LE_MUL; REAL_POS;
                                            REAL_POW_LE] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS];
    ALL_TAC] THEN
  MP_TAC(SPECL [`m0:num`; `&1`] SUM_BINOM_FACT_POW_LE) THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_MUL_RID; REAL_POS] THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `!s c t y:real. s * c <= t * c /\ t * c = y ==> s * c <= y`) THEN
  EXISTS_TAC `(&m0 + &1) pow m0` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS];
    REWRITE_TAC[REAL_MUL_AC]]);;

let BAKER_GAMMAPROD_INTPOLY = prove
 (`!L (g:num->(num->complex)->complex) V e G n m mu.
        1 <= n /\ 1 <= L /\ &1 <= G /\ FINITE V /\
        (!j. j <= n ==> intpoly V e G (g j)) /\
        (!r. r IN 1..n ==> mu r <= L)
        ==> intpoly V (\r. nsum(1..n-1) m * e r)
             ((&2 * &L * G) pow (nsum(1..n-1) m))
             (\x. cproduct(1..n-1)
                   (\r. (Cx(&(mu r)) * g n x - Cx(&(mu n)) * g r x)
                        pow (m r)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= G` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(mu:num->num) n <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTPOLY_MONO THEN
  EXISTS_TAC `\i:num. nsum(1..n-1) (\r. m r * e i)` THEN
  EXISTS_TAC
   `product(1..n-1) (\r. (&((mu:num->num) r) * G + &(mu n) * G) pow (m r))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_CPRODUCT THEN ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `r:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC INTPOLY_POW THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTPOLY_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC INTPOLY_NUM_MUL THEN
    REWRITE_TAC[ETA_AX] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
    SIMP_TAC[NSUM_RMUL; FINITE_NUMSEG; LE_REFL];
    ALL_TAC] THEN
  SIMP_TAC[REAL_POW_NSUM; FINITE_NUMSEG] THEN
  MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_ADD; REAL_POS] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_ADD; REAL_POS] THEN
  REWRITE_TAC[GSYM REAL_ADD_RDISTRIB; REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(mu:num->num) r <= L` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    UNDISCH_TAC `(mu:num->num) n <= L` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* N^(m 0) g_n^|m| times the algebraic term is an intpoly in theta.          *)
(* ------------------------------------------------------------------------- *)

let BAKER_ALGTERM_INTPOLY = prove
 (`!n h L beta lg theta V (g:num->(num->complex)->complex) e G N l m a b mu.
        1 <= n /\ 1 <= L /\ &1 <= G /\ FINITE V /\ (1..n) SUBSET V /\
        (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
        (!j. j <= n ==> intpoly V e G (g j)) /\
        (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
        (!i. 1 <= i /\ i <= h ==> (l + i) divides N) /\
        (a,b,mu) IN baker_index h L n
        ==> ?psi. intpoly V (\r. (if r IN 1..n then L * l else 0) +
                                 nsum(0..n-1) m * e r)
                    (&N pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
                     (&(m 0) + &1) pow (m 0) *
                     (&2 * &L * G) pow (nsum(0..n-1) m))
                    psi /\
                  psi theta =
                  Cx(&N) pow (m 0) * g n theta pow (nsum(0..n-1) m) *
                  baker_algterm n h (\x. &1) beta lg m (a,b,mu) (Cx(&l))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `a < h /\ b <= L /\ (!r. r IN 1..n ==> (mu:num->num) r <= L)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a,b,mu) IN baker_index h L n` THEN
    REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
                cartesian_product; EXTENSIONAL] THEN
    SIMP_TAC[IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(mu:num->num) n <= L` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `\x. vsum(0..m 0)
         (\j. Cx(&(binom(m 0,j))) * Cx(&N) pow (m 0 - j) *
              Cx(&(FACT j)) *
              (Cx(&N) pow j *
               higher_complex_derivative j (feldman_basis h a b)
                 (Cx(&l)) /
               Cx(&(FACT j))) *
              (g:num->(num->complex)->complex) n x pow j *
              (--(Cx(&((mu:num->num) n)) * g 0 x)) pow (m 0 - j)) *
        cproduct(1..n-1)
         (\r. (Cx(&(mu r)) * g n x - Cx(&(mu n)) * g r x) pow (m r)) *
        cproduct(1..n) (\r. x r pow (mu r * l))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`n:num`; `h:num`; `beta:num->complex`; `lg:num->complex`;
                   `theta:num->complex`;
                   `\j. (g:num->(num->complex)->complex) j theta`;
                   `N:num`; `l:num`; `m:num->num`; `a:num`; `b:num`;
                   `mu:num->num`] BAKER_ALGTERM_REARRANGE) THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC INTPOLY_MONO THEN
  EXISTS_TAC
   `\r. m 0 * e r +
        (nsum(1..n-1) m * e r +
         (if r IN 1..n then (mu:num->num) r * l else 0))` THEN
  EXISTS_TAC
   `(&N pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
     (&(m 0) + &1) pow (m 0) * (&2 * &L * G) pow (m 0)) *
    ((&2 * &L * G) pow (nsum(1..n-1) m) * &1)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BAKER_DSUM_INTPOLY THEN ASM_SIMP_TAC[LE_REFL] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      MATCH_MP_TAC INTPOLY_MUL THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC BAKER_GAMMAPROD_INTPOLY THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INTPOLY_MONOMIAL THEN ASM_REWRITE_TAC[]]];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `0 <= n - 1` (fun th ->
      REWRITE_TAC[MATCH_MP NSUM_CLAUSES_LEFT th]) THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; RIGHT_ADD_DISTRIB] THEN
    COND_CASES_TAC THEN REWRITE_TAC[ADD_CLAUSES] THENL
     [SUBGOAL_THEN `(mu:num->num) r * l <= L * l` MP_TAC THENL
       [REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_SIMP_TAC[]; ARITH_TAC];
      ARITH_TAC];
    SUBGOAL_THEN `0 <= n - 1` (fun th ->
      REWRITE_TAC[MATCH_MP NSUM_CLAUSES_LEFT th]) THENL
     [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES; REAL_POW_ADD; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_MUL_AC; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Baker Lemma 4, arithmetic part: Siegel lemma gives integers p, not all 0, *)
(* of controlled size, such that the algebraic counterpart of F_m vanishes   *)
(* at l = 1..h for |m| <= k.                                                 *)
(* ------------------------------------------------------------------------- *)

let BAKER_ALGTERM_LINEAR = prove
 (`!n h p beta lg m a b mu z.
        baker_algterm n h p beta lg m (a,b,mu) z =
        Cx(p(a,b,mu)) * baker_algterm n h (\x. &1) beta lg m (a,b,mu) z`,
  REWRITE_TAC[baker_algterm; COMPLEX_MUL_LID]);;

let BAKER_ALGTERM_RESTRICT = prove
 (`!n h p beta lg m x z.
        1 <= n
        ==> baker_algterm n h p beta lg (RESTRICTION (0..n-1) m) x z =
            baker_algterm n h p beta lg m x z`,
  REPEAT STRIP_TAC THEN
  SUBST1_TAC(SYM(ISPEC `x:num#num#(num->num)` PAIR)) THEN
  SUBST1_TAC(SYM(ISPEC `SND(x:num#num#(num->num))` PAIR)) THEN
  REWRITE_TAC[baker_algterm; RESTRICTION; IN_NUMSEG; LE_0] THEN
  ASM_SIMP_TAC[ARITH_RULE `1 <= n ==> 0 <= n - 1`] THEN
  AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN SIMP_TAC[IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let BAKER_ALG_RESTRICT = prove
 (`!n h L p beta lg m z.
        1 <= n
        ==> baker_alg n h L p beta lg (RESTRICTION (0..n-1) m) z =
            baker_alg n h L p beta lg m z`,
  SIMP_TAC[baker_alg; BAKER_ALGTERM_RESTRICT]);;

let NSUM_RESTRICTION = prove
 (`!s (m:num->num). nsum s (RESTRICTION s m) = nsum s m`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN SIMP_TAC[RESTRICTION]);;

let CARD_BAKER_INDEX = prove
 (`!h L n. CARD(baker_index h L n) = h * (L + 1) * (L + 1) EXP n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[baker_index] THEN
  SIMP_TAC[CARD_CROSS; FINITE_CROSS; FINITE_NUMSEG; FINITE_NUMSEG_LT;
           FINITE_CARTESIAN_PRODUCT_FINITE; CARD_NUMSEG_LT; CARD_NUMSEG] THEN
  SIMP_TAC[CARD_CARTESIAN_PRODUCT; FINITE_NUMSEG; CARD_NUMSEG] THEN
  REWRITE_TAC[NPRODUCT_CONST_NUMSEG; SUB_0] THEN
  REWRITE_TAC[ARITH_RULE `(n + 1) - 1 = n`; ARITH_RULE `(L + 1) - 0 = L + 1`]);;

let BAKER_LEMMA4_ARITH = prove
 (`!n h L k beta lg theta V (g:num->(num->complex)->complex) e G N a d H.
        1 <= n /\ 1 <= L /\ 1 <= h /\ &1 <= G /\ FINITE V /\
        (1..n) SUBSET V /\ (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
        (!j. j <= n ==> intpoly V e G (g j)) /\
        ~(g n theta = Cx(&0)) /\
        (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
        (!r. r IN V
             ==> 1 <= d r /\ (!j. integer(a r j) /\ abs(a r j) <= H r) /\
                 ~(a r (d r) = &0) /\
                 vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
        ~(N = 0) /\ (!i. 1 <= i /\ i <= 2 * h ==> i divides N) /\
        2 * nproduct V d * (k + 1) EXP n <= (L + 1) * (L + 1) EXP n
        ==> ?p. (!x. x IN baker_index h L n
                     ==> integer(p x) /\
                         abs(p x) <=
                         &(CARD(baker_index h L n)) *
                         max (&1)
                          ((&N pow k * &2 pow ((L + 2) * ((h + 1) + h)) *
                            (&k + &1) pow k * (&2 * &L * G) pow k) *
                           product V (\r. (&2 * H r) pow
                                          ((if r IN 1..n then L * h else 0) +
                                           k * e r)))) /\
                ~(!x. x IN baker_index h L n ==> p x = &0) /\
                (!l m. 1 <= l /\ l <= h /\ nsum(0..n-1) m <= k
                       ==> baker_alg n h L p beta lg m (Cx(&l)) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `Mset = {m:num->num | m IN cartesian_product (0..n-1) (\i:num. 0..k) /\
                         nsum(0..n-1) m <= k}` THEN
  ABBREV_TAC `eqs = (1..h) CROSS (Mset:(num->num)->bool)` THEN
  SUBGOAL_THEN `FINITE(Mset:(num->num)->bool) /\ CARD Mset <= (k + 1) EXP n`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `FINITE(cartesian_product (0..n-1) (\i:num. 0..k)) /\
      CARD(cartesian_product (0..n-1) (\i:num. 0..k)) = (k + 1) EXP n`
    STRIP_ASSUME_TAC THENL
     [SIMP_TAC[FINITE_CARTESIAN_PRODUCT_FINITE; FINITE_NUMSEG;
               CARD_CARTESIAN_PRODUCT; CARD_NUMSEG; NPRODUCT_CONST_NUMSEG] THEN
      ASM_SIMP_TAC[SUB_0; ARITH_RULE `1 <= n ==> n - 1 + 1 = n`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(Mset:(num->num)->bool) SUBSET cartesian_product (0..n-1) (\i:num. 0..k)`
    ASSUME_TAC THENL [EXPAND_TAC "Mset" THEN SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[FINITE_SUBSET; CARD_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE(eqs:num#(num->num)->bool) /\ CARD eqs <= h * (k + 1) EXP n`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eqs" THEN ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; CARD_CROSS;
                                       CARD_NUMSEG_1; LE_MULT_LCANCEL];
    ALL_TAC] THEN
  ABBREV_TAC `nexp = \r. (if r IN 1..n then L * h else 0) + k * e r` THEN
  ABBREV_TAC
   `B = &N pow k * &2 pow ((L + 2) * ((h + 1) + h)) * (&k + &1) pow k *
        (&2 * &L * G) pow k` THEN
  SUBGOAL_THEN
   `?psi. !i x. i IN eqs /\ x IN baker_index h L n
                ==> intpoly V nexp B (psi i x) /\
                    psi i x theta =
                    Cx(&N) pow (SND i 0) *
                    (g:num->(num->complex)->complex) n theta pow
                      (nsum(0..n-1) (SND i)) *
                    baker_algterm n h (\x. &1) beta lg (SND i) x
                      (Cx(&(FST i)))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`l:num`; `m:num->num`; `a':num`; `b':num`; `mu:num->num`] THEN
    EXPAND_TAC "eqs" THEN EXPAND_TAC "Mset" THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM; IN_NUMSEG] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`n:num`; `h:num`; `L:num`; `beta:num->complex`;
                   `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
                   `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
                   `N:num`; `l:num`; `m:num->num`; `a':num`; `b':num`;
                   `mu:num->num`] BAKER_ALGTERM_INTPOLY) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `i:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `psi:(num->complex)->complex` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\r. (if r IN 1..n then L * l else 0) + nsum(0..n-1) m * e r`;
      `&N pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
       (&(m 0) + &1) pow (m 0) * (&2 * &L * G) pow (nsum(0..n-1) m)`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN DISCH_TAC THEN EXPAND_TAC "nexp" THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC LE_ADD2 THEN CONJ_TAC THENL
       [COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_REFL; LE_MULT_LCANCEL];
        ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m:num->num) 0 <= k` ASSUME_TAC THENL
     [TRANS_TAC LE_TRANS `nsum(0..n-1) m` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:num->num`; `0..n-1`; `0`] NSUM_DELETE) THEN
      REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG; LE_0] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "B" THEN
    SUBGOAL_THEN `&1 <= &2 * &L * G` ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 * &1 <= y ==> &1 <= &2 * y`) THEN
      MATCH_MP_TAC REAL_LE_MUL2 THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_POS; ARITH];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
      TRY(MATCH_MP_TAC REAL_POW_LE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
      MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [TRANS_TAC REAL_LE_TRANS `(&(m 0) + &1) pow k` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_POW_LE2 THEN
        ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_LE_RADD] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`V:num->bool`; `nexp:num->num`; `B:real`;
    `psi:num#(num->num)->num#num#(num->num)->(num->complex)->complex`;
    `eqs:num#(num->num)->bool`; `baker_index h L n`; `theta:num->complex`;
    `a:num->num->real`; `d:num->num`; `H:num->real`] ALGEBRAIC_SIEGEL) THEN
  ASM_SIMP_TAC[FINITE_BAKER_INDEX] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(0,0,RESTRICTION (1..n) (\r:num. 0))` THEN
      REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
                  RESTRICTION_IN_CARTESIAN_PRODUCT; LE_0] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CARD_BAKER_INDEX] THEN
    TRANS_TAC LE_TRANS
     `2 * nproduct (V:num->bool) (d:num->num) * h * (k + 1) EXP n` THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `2 * a * h * b = h * (2 * a * b)`] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL; GSYM MULT_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `p:num#num#(num->num)->real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:num#num#(num->num)` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:num#num#(num->num)`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "B" THEN EXPAND_TAC "nexp" THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`l:num`; `m:num->num`] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM(MATCH_MP BAKER_ALG_RESTRICT (ASSUME `1 <= n`))] THEN
  ABBREV_TAC `m' = RESTRICTION (0..n-1) (m:num->num)` THEN
  SUBGOAL_THEN `(l,m') IN (eqs:num#(num->num)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "eqs" THEN EXPAND_TAC "Mset" THEN EXPAND_TAC "m'" THEN
    REWRITE_TAC[IN_CROSS; IN_ELIM_THM; IN_NUMSEG; NSUM_RESTRICTION] THEN
    ASM_REWRITE_TAC[RESTRICTION_IN_CARTESIAN_PRODUCT; IN_NUMSEG; LE_0] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    TRANS_TAC LE_TRANS `nsum(0..n-1) m` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:num->num`; `0..n-1`; `i:num`] NSUM_DELETE) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(l,m'):num#(num->num)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `vsum (baker_index h L n)
     (\x. Cx(p x) * psi (l,m') x (theta:num->complex)) =
    (Cx(&N) pow (m' 0) *
     (g:num->(num->complex)->complex) n theta pow (nsum(0..n-1) m')) *
    baker_alg n h L p beta lg m' (Cx(&l))`
  SUBST1_TAC THENL
   [REWRITE_TAC[baker_alg] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_BAKER_INDEX] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':num`; `b':num`; `mu:num->num`] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(l,m'):num#(num->num)`;
                                  `(a',b',mu):num#num#(num->num)`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [BAKER_ALGTERM_LINEAR] THEN
    REWRITE_TAC[COMPLEX_MUL_AC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Baker Lemma 5, arithmetic part: a nonzero value of the algebraic          *)
(* counterpart at an integer point is bounded below (Liouville).             *)
(* ------------------------------------------------------------------------- *)

let BAKER_ALG_INTPOLY = prove
 (`!n h L beta lg theta V (g:num->(num->complex)->complex) e G N l m p P.
        1 <= n /\ 1 <= L /\ &1 <= G /\ FINITE V /\ (1..n) SUBSET V /\
        (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
        (!j. j <= n ==> intpoly V e G (g j)) /\
        (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
        (!i. 1 <= i /\ i <= h ==> (l + i) divides N) /\
        (!x. x IN baker_index h L n ==> integer(p x) /\ abs(p x) <= P)
        ==> ?psi. intpoly V (\r. (if r IN 1..n then L * l else 0) +
                                 nsum(0..n-1) m * e r)
                    (&(CARD(baker_index h L n)) * P *
                     (&N pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
                      (&(m 0) + &1) pow (m 0) *
                      (&2 * &L * G) pow (nsum(0..n-1) m)))
                    psi /\
                  psi theta =
                  Cx(&N) pow (m 0) * g n theta pow (nsum(0..n-1) m) *
                  baker_alg n h L p beta lg m (Cx(&l))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `B = &N pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
        (&(m 0) + &1) pow (m 0) * (&2 * &L * G) pow (nsum(0..n-1) m)` THEN
  SUBGOAL_THEN
   `?psi. !x. x IN baker_index h L n
              ==> intpoly V (\r. (if r IN 1..n then L * l else 0) +
                                 nsum(0..n-1) m * e r) B (psi x) /\
                  psi x theta =
                  Cx(&N) pow (m 0) *
                  (g:num->(num->complex)->complex) n theta pow
                    (nsum(0..n-1) m) *
                  baker_algterm n h (\x. &1) beta lg m x (Cx(&l))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
    EXPAND_TAC "B" THEN MATCH_MP_TAC BAKER_ALGTERM_INTPOLY THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `\x:num->complex.
      vsum (baker_index h L n)
       (\y. Cx((p:num#num#(num->num)->real) y) *
            (psi:num#num#(num->num)->(num->complex)->complex) y x)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\r. (if r IN 1..n then L * l else 0) + nsum(0..n-1) m * e r`;
      `sum (baker_index h L n) (\y. abs((p:num#num#(num->num)->real) y) * B)`]
    THEN REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC INTPOLY_VSUM THEN REWRITE_TAC[FINITE_BAKER_INDEX] THEN
      X_GEN_TAC `y:num#num#(num->num)` THEN DISCH_TAC THEN
      MATCH_MP_TAC INTPOLY_CMUL THEN ASM_SIMP_TAC[ETA_AX];
      ALL_TAC] THEN
    MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_BAKER_INDEX] THEN
    X_GEN_TAC `y:num#num#(num->num)` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[] THEN
    EXPAND_TAC "B" THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LE) THEN
    REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN
    REWRITE_TAC[REAL_POS] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[baker_alg] THEN
  SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_BAKER_INDEX] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `b:num`; `mu:num->num`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
   [BAKER_ALGTERM_LINEAR] THEN
  REWRITE_TAC[COMPLEX_MUL_AC]);;

let BAKER_LEMMA5_ARITH = prove
 (`!n h L beta lg theta V (g:num->(num->complex)->complex) e G N l m p P a d H.
        1 <= n /\ 1 <= L /\ &1 <= G /\ FINITE V /\ (1..n) SUBSET V /\
        (!r. r IN 1..n ==> theta r = cexp(lg r)) /\
        (!j. j <= n ==> intpoly V e G (g j)) /\
        (!j. j < n ==> beta j * g n theta = --(g j theta)) /\
        (!i. 1 <= i /\ i <= h ==> (l + i) divides N) /\
        (!x. x IN baker_index h L n ==> integer(p x) /\ abs(p x) <= P) /\
        (!r. r IN V
             ==> (!j. integer(a r j) /\ abs(a r j) <= H r) /\
                 ~(a r (d r) = &0) /\
                 vsum(0..d r) (\j. Cx(a r j) * theta r pow j) = Cx(&0)) /\
        ~(N = 0) /\ ~(g n theta = Cx(&0)) /\
        ~(baker_alg n h L p beta lg m (Cx(&l)) = Cx(&0))
        ==> inv(&(FACT(nproduct V d)) *
                (max (&1)
                 ((&(CARD(baker_index h L n)) * P *
                   (&N pow (m 0) * &2 pow ((L + 2) * ((l + 1) + h)) *
                    (&(m 0) + &1) pow (m 0) *
                    (&2 * &L * G) pow (nsum(0..n-1) m))) *
                  product V (\r. H r pow
                     ((if r IN 1..n then L * l else 0) +
                      nsum(0..n-1) m * e r)) *
                  product V (\r. (H r * (&1 + &(d r) * H r)) pow
                     ((if r IN 1..n then L * l else 0) +
                      nsum(0..n-1) m * e r))))
                pow (nproduct V d - 1) *
                product V (\r. H r pow
                     ((if r IN 1..n then L * l else 0) +
                      nsum(0..n-1) m * e r)))
            <= norm(Cx(&N) pow (m 0) * g n theta pow (nsum(0..n-1) m) *
                    baker_alg n h L p beta lg m (Cx(&l)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `h:num`; `L:num`; `beta:num->complex`;
                 `lg:num->complex`; `theta:num->complex`; `V:num->bool`;
                 `g:num->(num->complex)->complex`; `e:num->num`; `G:real`;
                 `N:num`; `l:num`; `m:num->num`;
                 `p:num#num#(num->num)->real`; `P:real`]
         BAKER_ALG_INTPOLY) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:(num->complex)->complex`
    STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
  MATCH_MP_TAC INTPOLY_LIOUVILLE THEN
  EXISTS_TAC `a:num->num->real` THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Baker Lemma 7, arithmetic part: at a rational point l/k the counterpart   *)
(* with m = 0 lies in Q(alpha_1^(1/k),...,alpha_n^(1/k)), each a root of     *)
(* a_r(x^k); if nonzero it is bounded below (Liouville).                     *)
(* ------------------------------------------------------------------------- *)

let VSUM_POLY_POW_SUBST = prove
 (`!(a:num->real) d k w.
        1 <= k
        ==> vsum(0..k * d)
              (\j. Cx(if k divides j then a(j DIV k) else &0) * w pow j) =
            vsum(0..d) (\i. Cx(a i) * (w pow k) pow i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\j. Cx(if k divides j then (a:num->real)(j DIV k) else &0) *
         (w:complex) pow j`;
    `IMAGE (\i. k * i) (0..d)`; `0..k * d`] VSUM_SUPERSET) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_VEC_0] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `i:num` SUBST_ALL_TAC o
      REWRITE_RULE[divides]) THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC `k * i <= k * d` THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN
    MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) VSUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG; EQ_MULT_LCANCEL] THEN ASM_MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[o_DEF; DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT;
               COMPLEX_POW_POW]);;

let BAKER_ALG_ZERO = prove
 (`!n h L p beta lg z.
        baker_alg n h L p beta lg (\r. 0) z =
        vsum (baker_index h L n)
         (\(a,b,mu). Cx(p(a,b,mu)) * feldman_basis h a b z *
                     cexp(z * vsum(1..n) (\r. Cx(&(mu r)) * lg r)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[baker_alg] THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[baker_algterm; VSUM_SING_NUMSEG; binom; SUB_0; complex_pow;
              higher_complex_derivative; COMPLEX_MUL_LID; COMPLEX_MUL_RID;
              CPRODUCT_1]);;

let CEXP_LINEAR_COMBINATION_RATIONAL = prove
 (`!s (lg:num->complex) mu l k.
        FINITE s /\ 1 <= k
        ==> cexp(Cx(&l) / Cx(&k) * vsum s (\r. Cx(&(mu r)) * lg r)) =
            cproduct s (\r. cexp(lg r / Cx(&k)) pow (mu r * l))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; CEXP_VSUM] THEN
  MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `r:num` THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM CEXP_N] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL; CX_MUL] THEN
  SUBGOAL_THEN `~(Cx(&k) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    CONV_TAC COMPLEX_FIELD]);;

let CEXP_DIV_POW = prove
 (`!z k. 1 <= k ==> cexp(z / Cx(&k)) pow k = cexp z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM CEXP_N] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `~(Cx(&k) = Cx(&0))` MP_TAC THENL
   [REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    CONV_TAC COMPLEX_FIELD]);;

let BAKER_LEMMA7_ARITH = prove
 (`!n h L beta lg p P k l X a d H.
        1 <= n /\ 1 <= h /\ 1 <= k /\ l <= k * X /\
        (!x. x IN baker_index h L n ==> integer(p x) /\ abs(p x) <= P) /\
        (!r. r IN 1..n
             ==> 1 <= d r /\ (!j. integer(a r j) /\ abs(a r j) <= H r) /\
                 ~(a r (d r) = &0) /\
                 vsum(0..d r) (\j. Cx(a r j) * cexp(lg r) pow j) = Cx(&0)) /\
        ~(baker_alg n h L p beta lg (\r. 0) (Cx(&l) / Cx(&k)) = Cx(&0))
        ==> inv(&(FACT(nproduct(1..n) (\r. k * d r))) *
                (max (&1)
                  ((&(CARD(baker_index h L n)) *
                    (P * &k pow (2 * h * (L + 2)) *
                     &2 pow ((L + 2) * (X + h)))) *
                   product(1..n) (\r. H r pow (L * l)) *
                   product(1..n) (\r. (H r * (&1 + &(k * d r) * H r))
                                      pow (L * l))))
                pow (nproduct(1..n) (\r. k * d r) - 1) *
                product(1..n) (\r. H r pow (L * l)))
            <= norm(Cx(&k) pow (2 * h * (L + 2)) *
                    baker_alg n h L p beta lg (\r. 0) (Cx(&l) / Cx(&k)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `E = 2 * h * (L + 2)` THEN
  SUBGOAL_THEN
   `?c. !x. x IN baker_index h L n
            ==> integer(c x) /\
                abs(c x) <= &k pow E * &2 pow ((L + 2) * (X + h)) /\
                Cx(c x) =
                Cx(&k) pow E *
                feldman_basis h (FST x) (FST(SND x)) (Cx(&l) / Cx(&k))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RIGHT_EXISTS_IMP_THM; GSYM SKOLEM_THM] THEN
    REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':num`; `b':num`; `mu:num->num`] THEN
    REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `2 * a' + 2 * h * (b' + 1) <= E` ASSUME_TAC THENL
     [EXPAND_TAC "E" THEN
      MATCH_MP_TAC(ARITH_RULE
       `a < h /\ h * (b + 1) <= h * (L + 1)
        ==> 2 * a + 2 * h * (b + 1) <= 2 * h * (L + 2)`) THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:num`; `a':num`; `b':num`; `k:num`; `l:num`]
           FELDMAN_BASIS_RATIONAL) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_INTEGER] THEN
    DISCH_THEN(X_CHOOSE_THEN `c0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `&k pow (E - (2 * a' + 2 * h * (b' + 1))) * c0` THEN
    SUBGOAL_THEN
     `Cx(&k pow (E - (2 * a' + 2 * h * (b' + 1))) * c0) =
      Cx(&k) pow E * feldman_basis h a' b' (Cx(&l) / Cx(&k))`
    ASSUME_TAC THENL
     [REWRITE_TAC[CX_MUL; CX_POW] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
      REWRITE_TAC[COMPLEX_MUL_ASSOC; GSYM COMPLEX_POW_ADD] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[INTEGER_MUL; INTEGER_POW; INTEGER_CLOSED] THEN
    ONCE_REWRITE_TAC[GSYM COMPLEX_NORM_CX] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_POW; COMPLEX_NORM_CX;
                REAL_ABS_NUM] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
    TRANS_TAC REAL_LE_TRANS `&2 pow ((X + a') + (b' + 1) * (X + h))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FELDMAN_BASIS_BOUND THEN
      REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
      SUBGOAL_THEN `&0 < &k` ASSUME_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[REAL_OF_NUM_LE] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC(ARITH_RULE
       `a < h /\ (b + 1) * (X + h) <= (L + 1) * (X + h)
        ==> (X + a) + (b + 1) * (X + h) <= (L + 2) * (X + h)`) THEN
      ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `theta' = \r. cexp((lg:num->complex) r / Cx(&k))` THEN
  ABBREV_TAC
   `psi = \x:num->complex.
      vsum (baker_index h L n)
       (\(a,b,mu). Cx((p:num#num#(num->num)->real)(a,b,mu) * c(a,b,mu)) *
                   cproduct(1..n) (\r. x r pow (mu r * l)))` THEN
  SUBGOAL_THEN
   `(psi:(num->complex)->complex) theta' =
    Cx(&k) pow E * baker_alg n h L p beta lg (\r. 0) (Cx(&l) / Cx(&k))`
  ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN EXPAND_TAC "theta'" THEN
    REWRITE_TAC[BAKER_ALG_ZERO] THEN
    SIMP_TAC[GSYM VSUM_COMPLEX_LMUL; FINITE_BAKER_INDEX] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a':num`; `b':num`; `mu:num->num`] THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[CEXP_LINEAR_COMBINATION_RATIONAL; FINITE_NUMSEG] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(a',b',mu):num#num#(num->num)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[CX_MUL] THEN REWRITE_TAC[COMPLEX_MUL_AC];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INTPOLY_LIOUVILLE THEN
  EXISTS_TAC `\r j. if k divides j then (a:num->num->real) r (j DIV k)
                    else &0` THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC INTPOLY_MONO THEN
    MAP_EVERY EXISTS_TAC
     [`\r:num. L * l`;
      `sum (baker_index h L n)
        (\x. abs((p:num#num#(num->num)->real) x * c x) * &1)`] THEN
    REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [EXPAND_TAC "psi" THEN
      SUBGOAL_THEN
       `!x:num->complex.
          vsum (baker_index h L n)
           (\(a,b,mu). Cx((p:num#num#(num->num)->real)(a,b,mu) *
                          c(a,b,mu)) *
                       cproduct(1..n) (\r. x r pow (mu r * l))) =
          vsum (baker_index h L n)
           (\y. Cx(p y * c y) *
                cproduct(1..n) (\r. x r pow (SND(SND y) r * l)))`
      (fun th -> REWRITE_TAC[th]) THENL
       [GEN_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
        REWRITE_TAC[FORALL_PAIR_THM];
        ALL_TAC] THEN
      MATCH_MP_TAC INTPOLY_VSUM THEN REWRITE_TAC[FINITE_BAKER_INDEX] THEN
      REWRITE_TAC[FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`a':num`; `b':num`; `mu:num->num`] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `!r. r IN 1..n ==> (mu:num->num) r <= L` ASSUME_TAC THENL
       [UNDISCH_TAC `(a',b',mu) IN baker_index h L n` THEN
        REWRITE_TAC[baker_index; IN_CROSS; IN_ELIM_THM; IN_NUMSEG;
                    cartesian_product; EXTENSIONAL] THEN
        SIMP_TAC[IN_ELIM_THM; IN_NUMSEG] THEN MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC INTPOLY_CMUL THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[INTEGER_MUL]; ALL_TAC] THEN
      MATCH_MP_TAC INTPOLY_MONO THEN
      MAP_EVERY EXISTS_TAC
       [`\r. if r IN 1..n then (mu:num->num) r * l else 0`; `&1`] THEN
      REWRITE_TAC[REAL_LE_REFL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC INTPOLY_MONOMIAL THEN
        REWRITE_TAC[FINITE_NUMSEG; SUBSET_REFL];
        X_GEN_TAC `r:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[LE_MULT_RCANCEL]];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MUL_RID] THEN
    MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_BAKER_INDEX] THEN
    X_GEN_TAC `y:num#num#(num->num)` THEN DISCH_TAC THEN
    REWRITE_TAC[REAL_ABS_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[INTEGER_CLOSED; REAL_ABS_NUM] THEN
      TRANS_TAC REAL_LE_TRANS `abs((a:num->num->real) r 0)` THEN
      ASM_REWRITE_TAC[REAL_ABS_POS];
      ASM_SIMP_TAC[DIVIDES_RMUL; DIVIDES_REFL; DIV_MULT;
                   ARITH_RULE `1 <= k ==> ~(k = 0)`];
      EXPAND_TAC "theta'" THEN REWRITE_TAC[] THEN
      ASM_SIMP_TAC[VSUM_POLY_POW_SUBST; CEXP_DIV_POW]];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_EQ_0; CX_INJ; REAL_OF_NUM_EQ]
    THEN ASM_ARITH_TAC]);;
