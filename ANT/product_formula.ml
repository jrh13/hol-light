(* ========================================================================= *)
(* The product formula for number fields. For nonzero x in a number field k, *)
(* with O = ring_of_integers k:                                              *)
(*                                                                           *)
(*   product {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\ ~(v_P(x) = &0)}    *)
(*           (\P. &(ideal_norm O P) zpow --v_P(x)) *                         *)
(*   product (complex_embeddings k) (\g. norm(g x)) = &1                     *)
(*                                                                           *)
(* (NUMBER_FIELD_PRODUCT_FORMULA, with v_P = dedekind_valuation (O,k) I P    *)
(* and the support finite): the normalized P-adic absolute values of         *)
(* ANT/dedekind_absolute.ml times the archimedean ones, each complex place   *)
(* counted through its two conjugate embeddings. Equivalently the product of *)
(* the |x|_P is 1 / |N_{k/Q}(x)|, the norm read in C through any embedding g *)
(* (NUMBER_FIELD_PRODUCT_FORMULA_NORM, with algebra_norm). In terms of the   *)
(* predicates of ANT/dedekind_absolute.ml, each |g(.)| is an absolute_value  *)
(* (COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE), each normalized |.|_P is a           *)
(* nonarchimedean_absolute_value, and the product of the |x|_P over the      *)
(* finitely many P with |x|_P <> 1, times the archimedean product, is 1      *)
(* (NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES).                           *)
(*                                                                           *)
(* Route: x = a / b with a, b nonzero in O                                   *)
(* (RING_OF_INTEGERS_FRACTION_FIELD); for a in O the product of N(P) zpow    *)
(* v_P(a) is N((a)) (DEDEKIND_VALUATION_IDEAL_NORM,                          *)
(* RING_OF_INTEGERS_FINITE_QUOTIENT), which is the product of the |g a|      *)
(* (NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS of ANT/infinite_places.ml,  *)
(* through algebra_norm); v_P(x) = v_P(a) - v_P(b), and the products over    *)
(* the union of the supports (PRODUCT_SUPERSET, PRODUCT_DIV).                *)
(*                                                                           *)
(* Uses: Library/products.ml, ANT/numfield.ml, ANT/ring_of_integers.ml,      *)
(* ANT/nf_valuation.ml, ANT/dedekind_absolute.ml, ANT/complex_embeddings.ml  *)
(* and ANT/infinite_places.ml (and with them Multivariate/cauchy.ml). Also   *)
(* Multivariate/complex_ring.ml (COMPLEX_RING_CLAUSES).                      *)
(* ========================================================================= *)

needs "Library/products.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/nf_valuation.ml";;
needs "ANT/dedekind_absolute.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "Multivariate/complex_ring.ml";;

(* ------------------------------------------------------------------------- *)
(* The product formula.                                                      *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_PRODUCT_FORMULA = prove
 (`!(k:A ring) x.
        number_field k /\ x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                        ~(P = {ring_0 k}) /\
                        ~(dedekind_valuation (ring_of_integers k,k) I P x =
                          &0)} /\
            product {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         ~(dedekind_valuation (ring_of_integers k,k) I P x =
                           &0)}
                    (\P. &(ideal_norm (ring_of_integers k) P) zpow
                         --(dedekind_valuation (ring_of_integers k,k) I P x)) *
            product (complex_embeddings k) (\g. norm(g x)) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[field_of_fractions; RING_OF_INTEGERS; I_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  ABBREV_TAC `O = ring_of_integers(k:A ring)` THEN
  SUBGOAL_THEN
   `ring_carrier(O:A ring) SUBSET ring_carrier k /\ ring_0 O = ring_0 k`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[RING_OF_INTEGERS_SUBSET; RING_OF_INTEGERS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a:A = ring_0 k)` ASSUME_TAC THENL
   [UNDISCH_TAC `ring_mul k b x = (a:A)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[INTEGRAL_DOMAIN_MUL_EQ_0; FIELD_IMP_INTEGRAL_DOMAIN];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:A. y IN ring_carrier O /\ ~(y = ring_0 k)
          ==> FINITE {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                          ~(dedekind_valuation (O,k) I P y = &0)} /\
              product {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                           ~(dedekind_valuation (O,k) I P y = &0)}
                (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P y) =
              product (complex_embeddings k) (\g. norm(g y))`
  (LABEL_TAC "int") THENL
   [X_GEN_TAC `y:A` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `y:A`]
      NUMBER_FIELD_IDEAL_NORM_PRINCIPAL_EMBEDDINGS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `y:A`]
      DEDEKIND_VALUATION_IDEAL_NORM) THEN
    ASM_REWRITE_TAC[I_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `ideal_generated O {y:A}`]
      RING_OF_INTEGERS_FINITE_QUOTIENT) THEN
    ASM_REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `ring_0 O = ring_0 (k:A ring)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IDEAL_GENERATED_EQ_0] THEN
    EXPAND_TAC "O" THEN ASM_REWRITE_TAC[RING_OF_INTEGERS];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P. prime_ideal O P /\ ~(P = {ring_0 k})
        ==> dedekind_valuation (O,k) I P x =
            dedekind_valuation (O,k) I P a -
            dedekind_valuation (O,k) I P (b:A)`
  (LABEL_TAC "sub") THENL
   [X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`O:A ring`; `k:A ring`; `I:A->A`; `P:A->bool`;
                   `b:A`; `x:A`] DEDEKIND_VALUATION_MUL) THEN
    ASM_REWRITE_TAC[I_THM] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "int" (MP_TAC o SPEC `a:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "int" (MP_TAC o SPEC `b:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!P. prime_ideal O P /\ ~(P = {ring_0 k})
        ==> &0 < (&(ideal_norm O (P:A->bool)):real)`
  (LABEL_TAC "npos") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC(ARITH_RULE `1 < n ==> 0 < n`) THEN
    MATCH_MP_TAC IDEAL_NORM_GT_1 THEN ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_IMP_PROPER_IDEAL) THEN
      SIMP_TAC[PROPER_IDEAL_ALT];
      ALL_TAC] THEN
    UNDISCH_TAC `ring_of_integers k = (O:A ring)` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
    ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
    ALL_TAC] THEN
  ABBREV_TAC
   `Sa = {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
              ~(dedekind_valuation (O,k) I P (a:A) = &0)}` THEN
  ABBREV_TAC
   `Sb = {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
              ~(dedekind_valuation (O,k) I P (b:A) = &0)}` THEN
  ABBREV_TAC
   `Sx = {P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
              ~(dedekind_valuation (O,k) I P (x:A) = &0)}` THEN
  SUBGOAL_THEN `(Sx:(A->bool)->bool) SUBSET Sa UNION Sb` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Sx"; "Sa"; "Sb"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(dedekind_valuation (O,k) I P (x:A) = &0)` THEN
    USE_THEN "sub" (fun th -> ASM_SIMP_TAC[th]) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(Sa:(A->bool)->bool) /\ FINITE(Sb:(A->bool)->bool)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. P IN Sa UNION Sb
        ==> prime_ideal O P /\ ~(P = {ring_0 k:A})`
  (LABEL_TAC "inS") THENL
   [MAP_EVERY EXPAND_TAC ["Sa"; "Sb"] THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product Sx (\P. &(ideal_norm O P) zpow --dedekind_valuation (O,k) I P x) =
    product (Sa UNION Sb)
     (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P b) /
    product (Sa UNION Sb)
     (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P (a:A))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_DIV; FINITE_UNION] THEN
    CONV_TAC SYM_CONV THEN
    TRANS_TAC EQ_TRANS
     `product (Sa UNION Sb)
        (\P. &(ideal_norm O P) zpow --dedekind_valuation (O,k) I P (x:A))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `P:A->bool` THEN DISCH_TAC THEN
      USE_THEN "inS" (MP_TAC o SPEC `P:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      USE_THEN "sub" (MP_TAC o SPEC `P:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      USE_THEN "npos" (MP_TAC o SPEC `P:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      ASM_SIMP_TAC[GSYM REAL_ZPOW_SUB; REAL_LT_IMP_NZ] THEN
      AP_TERM_TAC THEN INT_ARITH_TAC;
      MATCH_MP_TAC PRODUCT_SUPERSET THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
      USE_THEN "inS" (MP_TAC o SPEC `P:A->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `~((P:A->bool) IN Sx)` THEN EXPAND_TAC "Sx" THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      SIMP_TAC[INT_NEG_0; REAL_ZPOW_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product (Sa UNION Sb)
     (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P b) =
    product Sb
     (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P (b:A)) /\
    product (Sa UNION Sb)
     (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P a) =
    product Sa
     (\P. &(ideal_norm O P) zpow dedekind_valuation (O,k) I P (a:A))`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN MATCH_MP_TAC PRODUCT_SUPERSET THEN
    REWRITE_TAC[SUBSET_UNION] THEN
    X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    USE_THEN "inS" (MP_TAC o SPEC `P:A->bool`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MAP_EVERY EXPAND_TAC ["Sa"; "Sb"] THEN
    RULE_ASSUM_TAC(REWRITE_RULE
     [SYM(ASSUME `{P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                      ~(dedekind_valuation (O,k) I P (a:A) = &0)} = Sa`);
      SYM(ASSUME `{P | prime_ideal O P /\ ~(P = {ring_0 k}) /\
                      ~(dedekind_valuation (O,k) I P (b:A) = &0)} = Sb`)]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM;
      TAUT `~(p /\ q /\ ~r) <=> p ==> q ==> r`]) THEN
    ASM_SIMP_TAC[REAL_ZPOW_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `product (complex_embeddings k) (\g. norm((g:A->complex) a)) =
    product (complex_embeddings k) (\g. norm(g b)) *
    product (complex_embeddings k) (\g. norm(g x))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM PRODUCT_MUL; FINITE_COMPLEX_EMBEDDINGS] THEN
    MATCH_MP_TAC PRODUCT_EQ THEN X_GEN_TAC `g:A->complex` THEN DISCH_TAC THEN
    UNDISCH_TAC `ring_mul k b x = (a:A)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPLEX_EMBEDDINGS_NORM_MUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_FIELD
   `!B X:real. &0 < B /\ &0 < X ==> B / (B * X) * X = &1`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_POS_LT THEN
  ASM_SIMP_TAC[FINITE_COMPLEX_EMBEDDINGS; COMPLEX_EMBEDDINGS_NORM_POS]);;

let NUMBER_FIELD_PRODUCT_FORMULA_NORM = prove
 (`!(k:A ring) (g:A->complex) x.
        number_field k /\ g IN complex_embeddings k /\
        x IN ring_carrier k /\ ~(x = ring_0 k)
        ==> product {P | prime_ideal (ring_of_integers k) P /\
                         ~(P = {ring_0 k}) /\
                         ~(dedekind_valuation (ring_of_integers k,k) I P x =
                           &0)}
                    (\P. &(ideal_norm (ring_of_integers k) P) zpow
                         --(dedekind_valuation (ring_of_integers k,k) I P x)) *
            norm(g(algebra_norm (subfield_generated k {ring_0 k},k) I x)) =
            &1`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[NUMBER_FIELD_NORM_COMPLEX_EMBEDDINGS; NORM_CPRODUCT;
               FINITE_COMPLEX_EMBEDDINGS] THEN
  ASM_SIMP_TAC[NUMBER_FIELD_PRODUCT_FORMULA]);;

(* ------------------------------------------------------------------------- *)
(* The same in terms of absolute values: the normalized |.|_P are            *)
(* nonarchimedean absolute values, the |g(.)| absolute values, and the       *)
(* product over the finitely many P with |x|_P <> 1 times the archimedean    *)
(* product is 1.                                                             *)
(* ------------------------------------------------------------------------- *)

let COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE = prove
 (`!k (g:A->complex).
        field k /\ g IN complex_embeddings k
        ==> absolute_value k (\x. norm(g x))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    COMPLEX_EMBEDDINGS_MONOMORPHISM) THEN
  ASM_REWRITE_TAC[RING_MONOMORPHISM_ALT_EQ; ring_homomorphism;
                  COMPLEX_RING_CLAUSES] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[absolute_value; NORM_POS_LE; COMPLEX_NORM_ZERO;
               COMPLEX_NORM_MUL; NORM_TRIANGLE]);;

let NUMBER_FIELD_PRODUCT_FORMULA_ABSOLUTE_VALUES = prove
 (`!(k:A ring) f.
        number_field k /\
        (!P x. f P x =
               if x = ring_0 k then &0
               else &(ideal_norm (ring_of_integers k) P) zpow
                    --(dedekind_valuation (ring_of_integers k,k) I P x))
        ==> (!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
                 ==> nonarchimedean_absolute_value k (f P)) /\
            (!g. g IN complex_embeddings k
                 ==> absolute_value k (\x. norm(g x))) /\
            (!x. x IN ring_carrier k /\ ~(x = ring_0 k)
                 ==> FINITE {P | prime_ideal (ring_of_integers k) P /\
                                 ~(P = {ring_0 k}) /\ ~(f P x = &1)} /\
                     product {P | prime_ideal (ring_of_integers k) P /\
                                  ~(P = {ring_0 k}) /\ ~(f P x = &1)}
                             (\P. f P x) *
                     product (complex_embeddings k) (\g. norm(g x)) = &1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPEC `k:A ring` RING_OF_INTEGERS_FRACTION_FIELD) THEN
  ASM_REWRITE_TAC[field_of_fractions; RING_OF_INTEGERS; I_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!P. prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k})
        ==> 1 < ideal_norm (ring_of_integers k) P /\
            nonarchimedean_absolute_value k ((f:(A->bool)->A->real) P)`
  (LABEL_TAC "nP") THENL
   [X_GEN_TAC `P:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `k:A ring`; `I:A->A`;
                   `P:A->bool`; `(f:(A->bool)->A->real) P`]
      DEDEKIND_VALUATION_NORMALIZED_ABSOLUTE_VALUE) THEN
    ASM_REWRITE_TAC[field_of_fractions; RING_OF_INTEGERS; I_THM] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
      ASM_SIMP_TAC[PRIME_IMP_RING_IDEAL];
      SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_ABSOLUTE_VALUE];
    ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
         ~((f:(A->bool)->A->real) P x = &1)} =
    {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
         ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `P:A->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT
     `(a /\ b ==> (c <=> d)) ==> (a /\ b /\ c <=> a /\ b /\ d)`) THEN
    STRIP_TAC THEN USE_THEN "nP" (MP_TAC o SPEC `P:A->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`dedekind_valuation (ring_of_integers k,k) I (P:A->bool) x`,
             `v:int`) THEN
    UNDISCH_TAC `1 < ideal_norm (ring_of_integers k) (P:A->bool)` THEN
    SPEC_TAC(`ideal_norm (ring_of_integers k) (P:A->bool)`,`N:num`) THEN
    REPEAT STRIP_TAC THEN AP_TERM_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `&1 < (&N:real)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_OF_NUM_LT]; ALL_TAC] THEN
      DISJ_CASES_TAC(INT_ARITH `&0 < --v:int \/ --v < &0:int \/ v = &0`) THENL
       [MP_TAC(ISPECL [`&N:real`; `&0:int`; `--v:int`] REAL_ZPOW_MONO_LT) THEN
        ASM_REWRITE_TAC[REAL_ZPOW_0] THEN ASM_REAL_ARITH_TAC;
        FIRST_X_ASSUM DISJ_CASES_TAC THENL
         [MP_TAC(ISPECL [`&N:real`; `--v:int`; `&0:int`] REAL_ZPOW_MONO_LT) THEN
          ASM_REWRITE_TAC[REAL_ZPOW_0] THEN ASM_REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]]];
      SIMP_TAC[INT_NEG_0; REAL_ZPOW_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `product {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}
            (\P. (f:(A->bool)->A->real) P x) =
    product {P | prime_ideal (ring_of_integers k) P /\ ~(P = {ring_0 k}) /\
                 ~(dedekind_valuation (ring_of_integers k,k) I P x = &0)}
            (\P. &(ideal_norm (ring_of_integers k) P) zpow
                  --(dedekind_valuation (ring_of_integers k,k) I P x))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC PRODUCT_EQ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`] NUMBER_FIELD_PRODUCT_FORMULA) THEN
  ASM_REWRITE_TAC[]);;
