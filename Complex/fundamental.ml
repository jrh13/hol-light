(* ========================================================================= *)
(* Fundamental theorem of algebra.                                           *)
(* ========================================================================= *)

needs "Complex/complex_transc.ml";;
needs "Complex/cpoly.ml";;

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A cute trick to reduce magnitude of unimodular number.                    *)
(* ------------------------------------------------------------------------- *)

let SQRT_SOS_LT_1 = prove
 (`!x y. sqrt(x pow 2 + y pow 2) < &1 <=> x pow 2 + y pow 2 < &1`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM SQRT_1] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SIMP_TAC[SQRT_MONO_LT_EQ; REAL_POS; REAL_LE_ADD; REAL_LE_SQUARE]);;

let SQRT_SOS_EQ_1 = prove
 (`!x y. (sqrt(x pow 2 + y pow 2) = &1) <=> (x pow 2 + y pow 2 = &1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM SQRT_1] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  SIMP_TAC[SQRT_INJ; REAL_POS; REAL_LE_ADD; REAL_LE_SQUARE]);;

let UNIMODULAR_REDUCE_NORM = prove
 (`!z. (norm(z) = &1)
       ==> norm(z + Cx(&1)) < &1 \/
           norm(z - Cx(&1)) < &1 \/
           norm(z + ii) < &1 \/
           norm(z - ii) < &1`,
  GEN_TAC THEN
  REWRITE_TAC[ii; CX_DEF; complex_add; complex_sub; complex_neg; complex_norm;
        RE; IM; REAL_ADD_RID; REAL_NEG_0; SQRT_SOS_LT_1; SQRT_SOS_EQ_1] THEN
  SIMP_TAC[REAL_POW_2;
           REAL_ARITH `a * a + (b + c) * (b + c) =
                       (a * a + b * b) + (&2 * b * c + c * c)`;
           REAL_ARITH `(b + c) * (b + c) + a * a =
                       (b * b + a * a) + (&2 * b * c + c * c)`] THEN
  DISCH_TAC THEN REWRITE_TAC[REAL_ARITH `&1 + x < &1 <=> &0 < --x`] THEN
  REWRITE_TAC[REAL_NEG_ADD; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  REWRITE_TAC[REAL_MUL_RID] THEN
  MATCH_MP_TAC(REAL_ARITH
    `~(abs(a) <= &1 /\ abs(b) <= &1)
     ==> &0 < --a + --(&1) \/ &0 < a + --(&1) \/
         &0 < --b + --(&1) \/ &0 < b + --(&1)`) THEN
  STRIP_TAC THEN UNDISCH_TAC `Re z * Re z + Im z * Im z = &1` THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH
   `(&2 * r) * (&2 * r) <= &1 /\ (&2 * i) * (&2 * i) <= &1
    ==> ~(r * r + i * i = &1)`) THEN
  REWRITE_TAC[GSYM REAL_POW_2] THEN ONCE_REWRITE_TAC[GSYM REAL_POW2_ABS] THEN
  ASM_SIMP_TAC[REAL_POW_1_LE; REAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can always reduce modulus of 1 + b z^n if nonzero                *)
(* ------------------------------------------------------------------------- *)

let REDUCE_POLY_SIMPLE = prove
 (`!b n. ~(b = Cx(&0)) /\ ~(n = 0)
         ==> ?z. norm(Cx(&1) + b * z pow n) < &1`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `EVEN(n)` THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_SIMP_TAC[ARITH_RULE `~(2 * m = 0) ==> m < 2 * m /\ ~(m = 0)`] THEN
    DISCH_THEN(X_CHOOSE_TAC `w:complex`) THEN EXISTS_TAC `csqrt w` THEN
    ASM_REWRITE_TAC[GSYM COMPLEX_POW_POW; CSQRT]; ALL_TAC] THEN
  MP_TAC(SPEC `Cx(norm b) / b` UNIMODULAR_REDUCE_NORM) THEN ANTS_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX] THEN
    ASM_SIMP_TAC[COMPLEX_ABS_NORM; REAL_DIV_REFL; COMPLEX_NORM_ZERO];
    ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?v. norm(Cx(norm b) / b + v pow n) < &1` MP_TAC THENL
   [SUBGOAL_THEN `(Cx(&1) pow n = Cx(&1)) /\
                  (--Cx(&1) pow n = --Cx(&1)) /\
                  (((ii pow n = ii) /\ (--ii pow n = --ii)) \/
                   ((ii pow n = --ii) /\ (--ii pow n = ii)))`
    MP_TAC THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[complex_sub]) THEN ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EVEN]) THEN
    SIMP_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[complex_pow; COMPLEX_POW_NEG; EVEN; EVEN_MULT; ARITH_EVEN] THEN
    REWRITE_TAC[GSYM COMPLEX_POW_POW] THEN
    REWRITE_TAC[COMPLEX_POW_ONE; COMPLEX_POW_II_2; COMPLEX_MUL_LID;
                COMPLEX_POW_NEG] THEN
    COND_CASES_TAC THEN
    REWRITE_TAC[COMPLEX_MUL_RID; COMPLEX_MUL_RNEG; COMPLEX_NEG_NEG];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:complex` ASSUME_TAC) THEN
  EXISTS_TAC `v / Cx(root(n) (norm b))` THEN
  REWRITE_TAC[COMPLEX_POW_DIV; GSYM CX_POW] THEN
  SUBGOAL_THEN `root n (norm b) pow n = norm b` SUBST1_TAC THENL
   [UNDISCH_TAC `~(EVEN n)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
    INDUCT_TAC THEN SIMP_TAC[EVEN; ROOT_POW_POS; COMPLEX_NORM_POS];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `norm(Cx(norm b) / b)` THEN
  REWRITE_TAC[GSYM COMPLEX_NORM_MUL; COMPLEX_ADD_LDISTRIB] THEN
  REWRITE_TAC[COMPLEX_MUL_RID; REAL_MUL_RID] THEN
  SUBGOAL_THEN `norm(Cx(norm b) / b) = &1` SUBST1_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_DIV; COMPLEX_NORM_CX; COMPLEX_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_DIV_REFL; COMPLEX_NORM_ZERO]; ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_01; complex_div] THEN
  ONCE_REWRITE_TAC[AC COMPLEX_MUL_AC
   `(m * b') * b * p * m' = (m * m') * (b * b') * p`] THEN
  ASM_SIMP_TAC[COMPLEX_MUL_RINV; COMPLEX_MUL_LID;
               CX_INJ; COMPLEX_NORM_ZERO] THEN
  ASM_REWRITE_TAC[GSYM complex_div]);;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about polynomials.                                           *)
(* ------------------------------------------------------------------------- *)

let POLY_CMUL_MAP = prove
 (`!p c x. poly (MAP (( * ) c) p) x = c * poly p x`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; poly; COMPLEX_MUL_RZERO] THEN
  ASM_REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

let POLY_0 = prove
 (`!p x. ALL (\b. b = Cx(&0)) p ==> (poly p x = Cx(&0))`,
  LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[ALL; poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID]);;

let POLY_BOUND_EXISTS = prove
 (`!p r. ?m. &0 < m /\ !z. norm(z) <= r ==> norm(poly p z) <= m`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  LIST_INDUCT_TAC THENL
   [EXISTS_TAC `&1` THEN REWRITE_TAC[poly; COMPLEX_NORM_CX] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_LT_01; REAL_POS]; ALL_TAC] THEN
  POP_ASSUM(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&1 + norm(h) + abs(r * m)` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x /\ &0 <= y ==> &0 < &1 + x + y`;
               REAL_ABS_POS; COMPLEX_NORM_POS] THEN
  X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
  REWRITE_TAC[poly] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(h) + norm(z * poly t z)` THEN
  REWRITE_TAC[COMPLEX_NORM_TRIANGLE] THEN
  MATCH_MP_TAC(REAL_ARITH `y <= z ==> x + y <= &1 + x + abs(z)`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_SIMP_TAC[COMPLEX_NORM_POS]);;

(* ------------------------------------------------------------------------- *)
(* Offsetting the variable in a polynomial gives another of same degree.     *)
(* ------------------------------------------------------------------------- *)

let POLY_OFFSET_LEMMA = prove
 (`!a p. ?b q. (LENGTH q = LENGTH p) /\
               !x. poly (CONS b q) x = (a + x) * poly p x`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [EXISTS_TAC `Cx(&0)` THEN EXISTS_TAC `[]:complex list` THEN
    REWRITE_TAC[poly; LENGTH; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID];
    ALL_TAC] THEN
  POP_ASSUM STRIP_ASSUME_TAC THEN
  EXISTS_TAC `a * h` THEN EXISTS_TAC `CONS (b + h) q` THEN
  ASM_REWRITE_TAC[LENGTH; poly] THEN X_GEN_TAC `x:complex ` THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:complex`) THEN
  REWRITE_TAC[poly] THEN DISCH_THEN(MP_TAC o AP_TERM `( * ) x`) THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let POLY_OFFSET = prove
 (`!a p. ?q. (LENGTH q = LENGTH p) /\ !x. poly q x = poly p (a + x)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; poly] THENL
   [EXISTS_TAC `[]:complex list` THEN REWRITE_TAC[poly; LENGTH]; ALL_TAC] THEN
  POP_ASSUM(X_CHOOSE_THEN `p:complex list` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`a:complex`; `p:complex list`] POLY_OFFSET_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:complex` (X_CHOOSE_THEN `r: complex list`
        (STRIP_ASSUME_TAC o GSYM))) THEN
  EXISTS_TAC `CONS (h + b) r` THEN ASM_REWRITE_TAC[LENGTH] THEN
  REWRITE_TAC[poly] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bolzano-Weierstrass type property for closed disc in complex plane.       *)
(* ------------------------------------------------------------------------- *)

let METRIC_BOUND_LEMMA = prove
 (`!x y. norm(x - y) <= abs(Re(x) - Re(y)) + abs(Im(x) - Im(y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[complex_norm] THEN
  MATCH_MP_TAC(REAL_ARITH
   `a <= abs(abs x + abs y) ==> a <= abs x + abs y`) THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM POW_2_SQRT_ABS] THEN
  MATCH_MP_TAC SQRT_MONO_LE THEN
  SIMP_TAC[REAL_POW_2; REAL_LE_ADD; REAL_LE_SQUARE] THEN
  REWRITE_TAC[complex_add; complex_sub; complex_neg; RE; IM] THEN
  REWRITE_TAC[GSYM real_sub] THEN
  REWRITE_TAC[REAL_ARITH `(a + b) * (a + b) = a * a + b * b + &2 * a * b`] THEN
  REWRITE_TAC[GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[REAL_ARITH `a + b <= abs a + abs b + &2 * abs c`]);;

let BOLZANO_WEIERSTRASS_COMPLEX_DISC = prove
 (`!s r. (!n. norm(s n) <= r)
         ==> ?f z. subseq f /\
                   !e. &0 < e ==> ?N. !n. n >= N ==> norm(s(f n) - z) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `Re o (s:num->complex)` SEQ_MONOSUB) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` MP_TAC) THEN
  REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  MP_TAC(SPEC `Im o (s:num->complex) o (f:num->num)` SEQ_MONOSUB) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->num` MP_TAC) THEN
  REWRITE_TAC[o_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `(f:num->num) o (g:num->num)` THEN
  SUBGOAL_THEN `convergent (\n. Re(s(f n :num))) /\
                convergent (\n. Im(s((f:num->num)(g n))))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SEQ_BCONV THEN ASM_REWRITE_TAC[bounded] THEN
    MAP_EVERY EXISTS_TAC [`r + &1`; `&0`; `0`] THEN
    REWRITE_TAC[GE; LE_0; MR1_DEF; REAL_SUB_LZERO; REAL_ABS_NEG] THEN
    X_GEN_TAC `n:num` THEN
    W(fun (_,w) -> FIRST_ASSUM(MP_TAC o SPEC (funpow 3 rand (lhand w)))) THEN
    REWRITE_TAC[complex_norm] THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> b <= r ==> a < r + &1`) THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM POW_2_SQRT_ABS] THEN
    MATCH_MP_TAC SQRT_MONO_LE THEN
    REWRITE_TAC[REAL_POW_2; REAL_LE_SQUARE; REAL_LE_ADDR; REAL_LE_ADDL];
    ALL_TAC] THEN
  REWRITE_TAC[convergent; SEQ; GE] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `x:real`) (X_CHOOSE_TAC `y:real`)) THEN
  EXISTS_TAC `complex(x,y)` THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`subseq f`; `subseq g`] THEN
    REWRITE_TAC[subseq; o_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!e. &0 < e
        ==> (?N. !n. N <= n ==> abs(Re(s ((f:num->num) n)) - x) < e)` THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e / &2`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_TAC `N2:num`) THEN DISCH_THEN(X_CHOOSE_TAC `N1:num`) THEN
  EXISTS_TAC `N1 + N2:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&2 * e / &2` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH; REAL_LE_REFL]] THEN
  W(MP_TAC o PART_MATCH lhand METRIC_BOUND_LEMMA o lhand o snd) THEN
  MATCH_MP_TAC(REAL_ARITH
    `a < c /\ b < c ==> x <= a + b ==> x < &2 * c`) THEN
  REWRITE_TAC[o_THM; RE; IM] THEN CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_MESON_TAC[LE_ADD; SEQ_SUBLE; LE_TRANS; ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial is continuous.                                                 *)
(* ------------------------------------------------------------------------- *)

let POLY_CONT = prove
 (`!p z e. &0 < e
           ==> ?d. &0 < d /\ !w. &0 < norm(w - z) /\ norm(w - z) < d
                   ==> norm(poly p w - poly p z) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`z:complex`; `p:complex list`] POLY_OFFSET) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:complex list` (MP_TAC o CONJUNCT2)) THEN
  DISCH_THEN(MP_TAC o GEN `w:complex` o SYM o SPEC `w - z`) THEN
  REWRITE_TAC[COMPLEX_SUB_ADD2] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  REWRITE_TAC[COMPLEX_SUB_REFL] THEN
  SPEC_TAC(`q:complex list`,`p:complex list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[poly] THENL
   [EXISTS_TAC `e:real` THEN
    ASM_REWRITE_TAC[COMPLEX_SUB_REFL; COMPLEX_NORM_CX; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; COMPLEX_ADD_SUB] THEN
  MP_TAC(SPECL [`t:complex list`; `&1`] POLY_BOUND_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`&1`; `e / m:real`] REAL_DOWN2) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_01] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:complex` THEN
  STRIP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `d * m:real` THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN MATCH_MP_TAC REAL_LE_MUL2 THEN
  ASM_MESON_TAC[REAL_LT_TRANS; REAL_LT_IMP_LE; COMPLEX_NORM_POS]);;

(* ------------------------------------------------------------------------- *)
(* Hence a polynomial attains minimum on a closed disc in the complex plane. *)
(* ------------------------------------------------------------------------- *)

let POLY_MINIMUM_MODULUS_DISC = prove
 (`!p r. ?z. !w. norm(w) <= r ==> norm(poly p z) <= norm(poly p w)`,
  let lemma = prove
   (`P /\ (m = --x) /\ --x < y <=> (--x = m) /\ P /\ m < y`,
    MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `&0 <= r` THENL
   [ALL_TAC; ASM_MESON_TAC[COMPLEX_NORM_POS; REAL_LE_TRANS]] THEN
  MP_TAC(SPEC `\x. ?z. norm(z) <= r /\ (norm(poly p z) = --x)`
    REAL_SUP_EXISTS) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`--norm(poly p (Cx(&0)))`; `Cx(&0)`] THEN
      ASM_REWRITE_TAC[REAL_NEG_NEG; COMPLEX_NORM_CX; REAL_ABS_NUM];
      EXISTS_TAC `&1` THEN
      REWRITE_TAC[REAL_ARITH `(a = --b) <=> (--b = a:real)`] THEN
      REWRITE_TAC[REAL_ARITH `x < &1 <=>  --(&1) < --x`] THEN
      SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
      SIMP_TAC[REAL_ARITH `&0 <= x ==> --(&1) < x`; COMPLEX_NORM_POS]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` MP_TAC) THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a < b <=> --b < --a:real`] THEN
  ABBREV_TAC `m = --s:real` THEN
  DISCH_THEN(MP_TAC o GEN `y:real` o SPEC `--y:real`) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; GSYM CONJ_ASSOC; lemma] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(--a = b) <=> (a = --b:real)`] THEN
  REWRITE_TAC[LEFT_EXISTS_AND_THM; EXISTS_REFL] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `m:real` th)) THEN
  REWRITE_TAC[REAL_LT_REFL; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
  REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `m + inv(&(SUC n))`) THEN
  REWRITE_TAC[REAL_LT_ADDR; REAL_LT_INV_EQ; REAL_OF_NUM_LT; LT_0] THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`s:num->complex`; `r:real`]
    BOLZANO_WEIERSTRASS_COMPLEX_DISC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` (X_CHOOSE_THEN `z:complex`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `z:complex` THEN X_GEN_TAC `w:complex` THEN DISCH_TAC THEN
  SUBGOAL_THEN `norm(poly p z) = m` (fun th -> ASM_SIMP_TAC[th]) THEN
  MATCH_MP_TAC(REAL_ARITH `~(&0 < abs(a - b)) ==> (a = b)`) THEN DISCH_TAC THEN
  ABBREV_TAC `e = abs(norm(poly p z) - m)` THEN
  MP_TAC(SPECL [`p:complex list`; `z:complex`; `e / &2`] POLY_CONT) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!w. norm(w - z) < d ==> norm(poly p w - poly p z) < e / &2`
  MP_TAC THENL
   [X_GEN_TAC `u:complex` THEN
    ASM_CASES_TAC `u = z:complex` THEN
    ASM_SIMP_TAC[COMPLEX_SUB_REFL; REAL_LT_DIV; REAL_OF_NUM_LT; ARITH;
                 COMPLEX_NORM_CX; REAL_ABS_NUM] THEN
    DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ; COMPLEX_SUB_0]; ALL_TAC] THEN
  FIRST_ASSUM(K ALL_TAC o check (is_conj o lhand o
    snd o dest_forall o concl)) THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[GE] THEN
  DISCH_THEN(X_CHOOSE_THEN `N1:num` ASSUME_TAC) THEN
  MP_TAC(SPEC `&2 / e` REAL_ARCH_SIMPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `N2:num` ASSUME_TAC) THEN
  SUBGOAL_THEN `norm(poly p (s((f:num->num) (N1 + N2))) - poly p z) < e / &2`
  MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[LE_ADD]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH
   `!m. abs(norm(psfn) - m) < e2 /\
        &2 * e2 <= abs(norm(psfn) - m) + norm(psfn - pz)
        ==> norm(psfn - pz) < e2 ==> F`) THEN
  EXISTS_TAC `m:real` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&(SUC(N1 + N2)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `m <= x /\ x < m + e ==> abs(x - m:real) < e`) THEN
      ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LTE_TRANS THEN
      EXISTS_TAC `m + inv(&(SUC(f(N1 + N2:num))))` THEN
      ASM_REWRITE_TAC[REAL_LE_LADD] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; LT_0; LE_SUC; SEQ_SUBLE];
      GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_DIV] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&N2` THEN
      ASM_REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC]; ALL_TAC] THEN
  SIMP_TAC[REAL_DIV_LMUL; REAL_OF_NUM_EQ; ARITH] THEN
  EXPAND_TAC "e" THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(norm(psfn) - norm(pz)) <= norm(psfn - pz)
    ==> abs(norm(pz) - m) <= abs(norm(psfn) - m) + norm(psfn - pz)`) THEN
  REWRITE_TAC[COMPLEX_NORM_ABS_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Nonzero polynomial in z goes to infinity as z does.                       *)
(* ------------------------------------------------------------------------- *)

let POLY_INFINITY = prove
 (`!p a. EX (\b. ~(b = Cx(&0))) p
         ==> !d. ?r. !z. r <= norm(z) ==> d <= norm(poly (CONS a p) z)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[EX] THEN X_GEN_TAC `a:complex` THEN
  ASM_CASES_TAC `EX (\b. ~(b = Cx(&0))) t` THEN ASM_REWRITE_TAC[] THENL
   [X_GEN_TAC `d:real` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:complex`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `r:real` o SPEC `d + norm(a)`) THEN
    EXISTS_TAC `&1 + abs(r)` THEN X_GEN_TAC `z:complex` THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[poly] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm(z * poly (CONS h t) z) - norm(a)` THEN CONJ_TAC THENL
     [ALL_TAC;
      ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
      REWRITE_TAC[REAL_LE_SUB_RADD; COMPLEX_NORM_TRIANGLE_SUB]] THEN
    REWRITE_TAC[REAL_LE_SUB_LADD] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `&1 * norm(poly (CONS h t) z)` THEN CONJ_TAC THENL
     [REWRITE_TAC[REAL_MUL_LID] THEN FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `&1 + abs(r) <= x ==> r <= x`];
      REWRITE_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[COMPLEX_NORM_POS] THEN
      ASM_MESON_TAC[REAL_ARITH `&1 + abs(r) <= x ==> &1 <= x`]];
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_EX]) THEN
    ASM_SIMP_TAC[poly; POLY_0; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    DISCH_TAC THEN X_GEN_TAC `d:real` THEN
    EXISTS_TAC `(abs(d) + norm(a)) / norm(h)` THEN X_GEN_TAC `z:complex` THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; COMPLEX_NORM_NZ; GSYM COMPLEX_NORM_MUL] THEN
    MATCH_MP_TAC(REAL_ARITH
     `mzh <= mazh + ma ==> abs(d) + ma <= mzh ==> d <= mazh`) THEN
    ONCE_REWRITE_TAC[COMPLEX_ADD_SYM] THEN
    REWRITE_TAC[COMPLEX_NORM_TRIANGLE_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Hence polynomial's modulus attains its minimum somewhere.                 *)
(* ------------------------------------------------------------------------- *)

let POLY_MINIMUM_MODULUS = prove
 (`!p. ?z. !w. norm(poly p z) <= norm(poly p w)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly; REAL_LE_REFL] THEN
  ASM_CASES_TAC `EX (\b. ~(b = Cx(&0))) t` THENL
   [FIRST_ASSUM(MP_TAC o SPEC `h:complex` o MATCH_MP POLY_INFINITY) THEN
    DISCH_THEN(MP_TAC o SPEC `norm(poly (CONS h t) (Cx(&0)))`) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` ASSUME_TAC) THEN
    MP_TAC(SPECL [`CONS (h:complex) t`; `abs(r)`]
       POLY_MINIMUM_MODULUS_DISC) THEN
    REWRITE_TAC[GSYM(CONJUNCT2 poly)] THEN
    ASM_MESON_TAC[REAL_ARITH `r <= z \/ z <= abs(r)`; REAL_LE_TRANS;
                  COMPLEX_NORM_CX; REAL_ABS_NUM; REAL_ABS_POS];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_EX]) THEN
    REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o MATCH_MP POLY_0) THEN
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO; REAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Constant function (non-syntactic characterization).                       *)
(* ------------------------------------------------------------------------- *)

let constant = new_definition
  `constant f = !w z. f(w) = f(z)`;;

let NONCONSTANT_LENGTH = prove
 (`!p. ~constant(poly p) ==> 2 <= LENGTH p`,
  REWRITE_TAC[constant] THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly] THEN
  REWRITE_TAC[LENGTH; ARITH_RULE `2 <= SUC n <=> ~(n = 0)`] THEN
  SIMP_TAC[TAUT `~a ==> ~b <=> b ==> a`; LENGTH_EQ_NIL; poly] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Decomposition of polynomial, skipping zero coefficients after the first.  *)
(* ------------------------------------------------------------------------- *)

let POLY_DECOMPOSE_LEMMA = prove
 (`!p. ~(!z. ~(z = Cx(&0)) ==> (poly p z = Cx(&0)))
       ==> ?k a q. ~(a = Cx(&0)) /\
                   (SUC(LENGTH q + k) = LENGTH p) /\
                   !z. poly p z = z pow k * poly (CONS a q) z`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[poly]; ALL_TAC] THEN
  ASM_CASES_TAC `h = Cx(&0)` THENL
   [GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [poly] THEN
    ASM_SIMP_TAC[COMPLEX_ADD_LID; COMPLEX_ENTIRE] THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `a:complex`
     (X_CHOOSE_THEN `q:complex list` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k + 1`; `a:complex`; `q:complex list`] THEN
    ASM_REWRITE_TAC[poly; LENGTH; GSYM ADD1; ADD_CLAUSES] THEN
    REWRITE_TAC[COMPLEX_ADD_LID; complex_pow; GSYM COMPLEX_MUL_ASSOC];
    DISCH_THEN(K ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`0`; `h:complex`; `t:complex list`] THEN
    ASM_REWRITE_TAC[complex_pow; COMPLEX_MUL_LID; ADD_CLAUSES; LENGTH]]);;

let POLY_DECOMPOSE = prove
 (`!p. ~constant(poly p)
       ==> ?k a q. ~(a = Cx(&0)) /\ ~(k = 0) /\
                   (LENGTH q + k + 1 = LENGTH p) /\
                   !z. poly p z = poly p (Cx(&0)) +
                                  z pow k * poly (CONS a q) z`,
  LIST_INDUCT_TAC THENL [REWRITE_TAC[constant; poly]; ALL_TAC] THEN
  POP_ASSUM(K ALL_TAC) THEN DISCH_TAC THEN
  MP_TAC(SPEC `t:complex list` POLY_DECOMPOSE_LEMMA) THEN ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[constant; poly] THEN
    REWRITE_TAC[TAUT `~b ==> ~a <=> a ==> b`; COMPLEX_EQ_ADD_LCANCEL] THEN
    SIMP_TAC[TAUT `~a ==> b <=> a \/ b`; GSYM COMPLEX_ENTIRE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `a:complex`
     (X_CHOOSE_THEN `q:complex list` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`SUC k`; `a:complex`; `q:complex list`] THEN
  ASM_REWRITE_TAC[ADD_CLAUSES; GSYM ADD1; LENGTH; NOT_SUC] THEN
  ASM_REWRITE_TAC[poly; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID; complex_pow] THEN
  REWRITE_TAC[GSYM COMPLEX_MUL_ASSOC]);;

let POLY_REPLICATE_APPEND = prove
 (`!n p x. poly (APPEND (REPLICATE n (Cx(&0))) p) x = x pow n * poly p x`,
  INDUCT_TAC THEN
  REWRITE_TAC[REPLICATE; APPEND; complex_pow; COMPLEX_MUL_LID] THEN
  ASM_REWRITE_TAC[poly; COMPLEX_ADD_LID] THEN REWRITE_TAC[COMPLEX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Fundamental theorem.                                                      *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_ALGEBRA = prove
 (`!p. ~constant(poly p) ==> ?z. poly p z = Cx(&0)`,
  SUBGOAL_THEN
   `!n p. (LENGTH p = n) /\ ~constant(poly p) ==> ?z. poly p z = Cx(&0)`
   (fun th -> MESON_TAC[th]) THEN
  MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  X_GEN_TAC `p:complex list` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NONCONSTANT_LENGTH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  X_CHOOSE_TAC `c:complex` (SPEC `p:complex list` POLY_MINIMUM_MODULUS) THEN
  ASM_CASES_TAC `poly p c = Cx(&0)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:complex`; `p:complex list`] POLY_OFFSET) THEN
  DISCH_THEN(X_CHOOSE_THEN `q:complex list` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  SUBGOAL_THEN `~constant(poly q)` ASSUME_TAC THENL
   [UNDISCH_TAC `~(constant(poly p))` THEN
    SUBGOAL_THEN `!z. poly q (z - c) = poly p z`
      (fun th -> MESON_TAC[th; constant]) THEN
    ASM_MESON_TAC[SIMPLE_COMPLEX_ARITH `a + (x - a) = x`]; ALL_TAC] THEN
  SUBGOAL_THEN `poly p c = poly q (Cx(&0))` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[COMPLEX_ADD_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `!w. norm(poly q (Cx(&0))) <= norm(poly q w)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th ->
    if free_in `p:complex list` (concl th)
    then ALL_TAC else ASSUME_TAC th)) THEN
  MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
  REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
  ABBREV_TAC `a0 = poly q (Cx(&0))` THEN
  SUBGOAL_THEN
   `!z. poly q z = poly (MAP (( * ) (inv(a0))) q) z * a0`
  ASSUME_TAC THENL
   [REWRITE_TAC[POLY_CMUL_MAP] THEN
    ONCE_REWRITE_TAC[AC COMPLEX_MUL_AC `(a * b) * c = b * c * a`] THEN
    ASM_SIMP_TAC[COMPLEX_MUL_RINV; COMPLEX_MUL_RID];
    ALL_TAC] THEN
  ABBREV_TAC `r = MAP (( * ) (inv(a0))) q` THEN
  SUBGOAL_THEN `LENGTH(q:complex list) = LENGTH(r:complex list)`
  SUBST_ALL_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[LENGTH_MAP]; ALL_TAC] THEN
  SUBGOAL_THEN `~(constant(poly r))` ASSUME_TAC THENL
   [UNDISCH_TAC `~constant(poly q)` THEN
    ASM_REWRITE_TAC[constant; COMPLEX_EQ_MUL_RCANCEL] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `poly r (Cx(&0)) = Cx(&1)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `Cx(&0)`) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM COMPLEX_MUL_LID] THEN
    ASM_SIMP_TAC[COMPLEX_EQ_MUL_RCANCEL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MAP_EVERY (fun th ->
    if free_in `q:complex list` (concl th)
    then ALL_TAC else ASSUME_TAC th)) THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; COMPLEX_NORM_NZ; COMPLEX_NORM_MUL;
               REAL_DIV_REFL; COMPLEX_NORM_ZERO] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP POLY_DECOMPOSE) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `a:complex`
        (X_CHOOSE_THEN `s:complex list` MP_TAC))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) MP_TAC) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k + 1 = n` THENL
   [UNDISCH_TAC `LENGTH(s:complex list) + k + 1 = n` THEN
    ASM_REWRITE_TAC[ARITH_RULE `(s + m = m) <=> (s = 0)`; LENGTH_EQ_NIL] THEN
    REWRITE_TAC[LENGTH_EQ_NIL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[poly; COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    ONCE_REWRITE_TAC[COMPLEX_MUL_SYM] THEN
    MATCH_MP_TAC REDUCE_POLY_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`k + 1 = n`; `2 <= n`] THEN ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k + 1`) THEN ANTS_TAC THENL
   [UNDISCH_TAC `~(k + 1 = n)` THEN
    UNDISCH_TAC `LENGTH(s:complex list) + k + 1 = n` THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC
   `CONS (Cx(&1)) (APPEND (REPLICATE (k - 1) (Cx(&0))) [a])`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[LENGTH; LENGTH_APPEND; LENGTH_REPLICATE] THEN
      UNDISCH_TAC `~(k = 0)` THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[constant; POLY_REPLICATE_APPEND; poly] THEN
    REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
    DISCH_THEN(MP_TAC o SPECL [`Cx(&0)`; `Cx(&1)`]) THEN
    REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_LZERO; COMPLEX_ADD_RID] THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE; COMPLEX_POW_ONE; SIMPLE_COMPLEX_ARITH
                  `(a = a + b) <=> (b = Cx(&0))`] THEN
    REWRITE_TAC[CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ]; ALL_TAC] THEN
  REWRITE_TAC[constant; POLY_REPLICATE_APPEND; poly] THEN
  REWRITE_TAC[COMPLEX_MUL_RZERO; COMPLEX_ADD_RID] THEN
  ONCE_REWRITE_TAC[AC COMPLEX_MUL_AC `a * b * c = (a * b) * c`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 complex_pow)] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(k = 0) ==> (SUC(k - 1) = k)`] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:complex`) THEN
  MP_TAC(SPECL [`s:complex list`; `norm(w)`] POLY_BOUND_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(w = Cx(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `Cx(&1) + w pow k * a = Cx(&0)` THEN
    ONCE_REWRITE_TAC[TAUT `a ==> ~b <=> b ==> ~a`] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `~(k = 0)` THEN SPEC_TAC(`k:num`,`k:num`) THEN
    INDUCT_TAC THEN REWRITE_TAC[complex_pow; COMPLEX_MUL_LZERO] THEN
    REWRITE_TAC[COMPLEX_ADD_RID; CX_INJ; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  MP_TAC(SPECL [`&1`; `inv(norm(w) pow (k + 1) * m)`] REAL_DOWN2) THEN
  ASM_SIMP_TAC[REAL_LT_01; REAL_LT_INV_EQ; REAL_LT_MUL; REAL_POW_LT;
               COMPLEX_NORM_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Cx(t) * w` THEN REWRITE_TAC[COMPLEX_POW_MUL] THEN
  REWRITE_TAC[COMPLEX_ADD_LDISTRIB; GSYM COMPLEX_MUL_ASSOC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SIMPLE_COMPLEX_ARITH
   `(a + w = Cx(&0)) ==> (w = --a)`)) THEN
  REWRITE_TAC[GSYM CX_NEG; GSYM CX_POW; GSYM CX_MUL] THEN
  REWRITE_TAC[COMPLEX_ADD_ASSOC; GSYM CX_ADD] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm(Cx(&1 + t pow k * -- &1)) +
              norm(Cx(t pow k) * w pow k * Cx t * w * poly s (Cx t * w))` THEN
  REWRITE_TAC[COMPLEX_NORM_TRIANGLE] THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC(REAL_ARITH
   `&0 <= x /\ x < t /\ t <= &1 ==> abs(&1 + t * --(&1)) + x < &1`) THEN
  REWRITE_TAC[COMPLEX_NORM_POS] THEN
  ASM_SIMP_TAC[REAL_POW_1_LE; REAL_LT_IMP_LE] THEN
  ONCE_REWRITE_TAC[COMPLEX_NORM_MUL] THEN REWRITE_TAC[COMPLEX_NORM_CX] THEN
  ASM_SIMP_TAC[real_abs; REAL_LT_IMP_LE; REAL_POW_LE] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
  MATCH_MP_TAC REAL_LT_LMUL THEN ASM_SIMP_TAC[REAL_POW_LT] THEN
  ONCE_REWRITE_TAC[AC COMPLEX_MUL_AC `a * b * c * d = b * (c * a) * d`] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 complex_pow)] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; ADD1; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `abs t * norm(w pow (k + 1)) * m` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[COMPLEX_NORM_POS] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[COMPLEX_NORM_MUL] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[COMPLEX_NORM_POS] THEN
    ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH
      `&0 < t /\ t < &1 ==> abs(t) <= &1`]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_MUL; COMPLEX_NORM_POW;
               REAL_POW_LT; COMPLEX_NORM_NZ] THEN
  ASM_SIMP_TAC[real_div; REAL_MUL_LID;
               REAL_ARITH `&0 < t /\ t < x ==> abs(t) < x`]);;

(* ------------------------------------------------------------------------- *)
(* Alternative version with a syntactic notion of constant polynomial.       *)
(* ------------------------------------------------------------------------- *)

let FUNDAMENTAL_THEOREM_OF_ALGEBRA_ALT = prove
 (`!p. ~(?a l. ~(a = Cx(&0)) /\ ALL (\b. b = Cx(&0)) l /\ (p = CONS a l))
       ==> ?z. poly p z = Cx(&0)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[poly; CONS_11] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  ONCE_REWRITE_TAC[AC CONJ_ACI `a /\ b /\ c /\ d <=> c /\ d /\ a /\ b`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
  ASM_CASES_TAC `h = Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_ADD_LID] THENL
   [EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[COMPLEX_MUL_LZERO]; ALL_TAC] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 poly)] THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_ALGEBRA THEN
  UNDISCH_TAC `~ALL (\b. b = Cx (&0)) t` THEN
  REWRITE_TAC[TAUT `~b ==> ~a <=> a ==> b`] THEN POP_ASSUM(K ALL_TAC) THEN
  REWRITE_TAC[constant; poly; REAL_EQ_LADD] THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(&0)` o ONCE_REWRITE_RULE[SWAP_FORALL_THM]) THEN
  REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[COMPLEX_ENTIRE; TAUT `a \/ b <=> ~a ==> b`] THEN
  SPEC_TAC(`t:complex list`,`p:complex list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL] THEN
  ASM_CASES_TAC `h = Cx(&0)` THEN
  ASM_SIMP_TAC[poly; COMPLEX_ADD_LID; COMPLEX_ENTIRE] THEN
  MP_TAC(SPECL [`t:complex list`; `&1`] POLY_BOUND_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`norm(h) / m`; `&1`] REAL_DOWN2) THEN
  ASM_SIMP_TAC[REAL_LT_01; REAL_LT_DIV; COMPLEX_NORM_NZ] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `Cx(x)`) THEN
  ASM_SIMP_TAC[CX_INJ; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[SIMPLE_COMPLEX_ARITH `(x + y = Cx(&0)) <=> (y = --x)`] THEN
  DISCH_THEN(MP_TAC o AP_TERM `norm`) THEN REWRITE_TAC[COMPLEX_NORM_NEG] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(a) < abs(b) ==> ~(a = b)`) THEN
  REWRITE_TAC[real_abs; COMPLEX_NORM_POS] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `norm(h) / m * m` THEN
  CONJ_TAC THENL
   [ALL_TAC; ASM_SIMP_TAC[REAL_LE_REFL; REAL_DIV_RMUL; REAL_LT_IMP_NZ]] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs(x) * m` THEN
  ASM_SIMP_TAC[REAL_LT_RMUL; REAL_ARITH `&0 < x /\ x < a ==> abs(x) < a`] THEN
  ASM_MESON_TAC[REAL_LE_LMUL; REAL_ABS_POS; COMPLEX_NORM_CX;
                REAL_ARITH `&0 < x /\ x < &1 ==> abs(x) <= &1`]);;
