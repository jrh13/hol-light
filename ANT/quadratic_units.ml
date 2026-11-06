(* ========================================================================= *)
(* Units of quadratic fields and the Pell equation, with the general facts   *)
(* on unit rank one. A number field k with two infinite places and a real    *)
(* embedding g (the real quadratic fields, the cubic fields with one real    *)
(* place) has a fundamental unit: a unit e with g(e) > 1 such that the units *)
(* are exactly the e^n and -e^n, n an integer, e has infinite order, and     *)
(* g(e) is the least value > 1 of g on the units                             *)
(* (NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL); the regulator is log g(e)           *)
(* (NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL).                           *)
(*                                                                           *)
(* For a quadratic field k (ANT/quadratic.ml) with x^2 = d, x not in Q: k    *)
(* has two infinite places, both real, if d > 0 and one if d < 0             *)
(* (QUADRATIC_FIELD_REAL_EMBEDDINGS, QUADRATIC_FIELD_INFINITE_PLACES), and   *)
(* the embedding other than g maps x to -g(x)                                *)
(* (QUADRATIC_FIELD_CONJUGATE_EMBEDDING). Imaginary quadratic fields: the    *)
(* units are the roots of unity                                              *)
(* (QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY); for d squarefree they   *)
(* are the (A + B x) / 2 with A^2 - d B^2 = 4                                *)
(* (QUADRATIC_FIELD_UNIT_IMAGINARY, QUADRATIC_FIELD_UNITS_IMAGINARY), so     *)
(* there are 4 of them if d = -1, 6 if d = -3 and 2 otherwise                *)
(* (QUADRATIC_FIELD_UNITS_IMAGINARY_CARD), namely 1 and -1                   *)
(* (QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC). Real quadratic fields: the     *)
(* fundamental unit and the regulator (QUADRATIC_FIELD_FUNDAMENTAL_UNIT).    *)
(*                                                                           *)
(* The Pell equation: for every nonsquare integer d > 0, x^2 - d y^2 = 1 has *)
(* infinitely many solutions in positive integers (PELL_EQUATION_INFINITE,   *)
(* and PELL_EQUATION_INFINITE_NUM for x^2 = d y^2 + 1 in natural numbers).   *)
(* The solutions come from the unit group: if y^2 = D in a field then a + b  *)
(* y is a unit of the ring of integers for every solution (a,b) of a^2 - D   *)
(* b^2 = 1 (QUADRATIC_FIELD_PELL_UNIT); conversely, writing d = c^2 d0 with  *)
(* d0 squarefree, a power of the fundamental unit of the field with x^2 = d0 *)
(* lies in Z[c x] (QUADRATIC_FIELD_UNIT_POW_IN_ORDER, by the pigeonhole      *)
(* principle in the finite ring O / 2 c O), and its square gives a solution  *)
(* with y <> 0 (QUADRATIC_FIELD_PELL_SOLUTION); the powers of one such       *)
(* solution are infinitely many (PELL_SOLUTION_IMP_INFINITE).                *)
(*                                                                           *)
(* Routes. Unit rank one: by NUMBER_FIELD_FUNDAMENTAL_UNITS the units are z  *)
(* e0^n with one unit e0 of infinite order and z a root of unity, here z = 1 *)
(* or -1 (NUMBER_FIELD_REAL_ROOTS_OF_UNITY); |g(e0)| <> 1, and e is one of   *)
(* e0, -e0, 1/e0, -1/e0 (UNIT_GROUP_ZPOW_RING_NEG of Library/ring_groups.ml: *)
(* (-x)^n = +-x^n). The imaginary units: the norm                            *)
(* |g(u)|^2 = (A^2 - d B^2) / 4 of 2 u = A + B x                             *)
(* is 1, and conversely such u are integral of norm 1. The norms in the real *)
(* case are g(u) h(u) for the two embeddings g and h, computed through the   *)
(* real monomorphisms (REAL_EMBEDDINGS_MONOMORPHISM of                       *)
(* ANT/infinite_places.ml); the product of their absolute values is 1 for    *)
(* units (RING_OF_INTEGERS_UNIT_NORM_PRODUCT).                               *)
(*                                                                           *)
(* Uses: Library/ringtheory.ml, Library/grouptheory.ml,                      *)
(* Library/fieldtheory.ml, Library/products.ml, Library/pocklington.ml       *)
(* (INT_SQUAREFREE_DECOMPOSITION), ANT/integral.ml, ANT/numfield.ml,         *)
(* ANT/ring_of_integers.ml (RING_OF_INTEGERS_FINITE_QUOTIENT),               *)
(* Library/ring_groups.ml (unit_group, GROUP_REAL_MULTIPLICATIVE_ZPOW,       *)
(* UNIT_GROUP_ZPOW_RING_NEG), ANT/quadratic.ml                               *)
(* (QUADRATIC_FIELD_EXISTS, QUADRATIC_FIELD_COORDINATES,                     *)
(* QUADRATIC_FIELD_INTEGRAL_COORDINATES, QUADRATIC_FIELD_INT_COORDINATES_EQ, *)
(* INT_NORM_FORM_4_IMAGINARY, SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD),        *)
(* ANT/complex_embeddings.ml, ANT/infinite_places.ml                         *)
(* (REAL_EMBEDDINGS_MONOMORPHISM, COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL),   *)
(* ANT/unit_theorem.ml, ANT/regulator.ml and ANT/roots_of_unity.ml. Also     *)
(* Multivariate/complex_ring.ml (complex_ring) and                           *)
(* Multivariate/transcendentals.ml (log).                                    *)
(* ========================================================================= *)

needs "Library/ringtheory.ml";;
needs "Library/grouptheory.ml";;
needs "Library/fieldtheory.ml";;
needs "Library/products.ml";;
needs "ANT/algmisc.ml";;
needs "ANT/integral.ml";;
needs "ANT/numfield.ml";;
needs "ANT/ring_of_integers.ml";;
needs "ANT/fingen_group.ml";;
needs "Library/ring_groups.ml";;
needs "ANT/quadratic.ml";;
needs "ANT/complex_embeddings.ml";;
needs "ANT/infinite_places.ml";;
needs "ANT/unit_theorem.ml";;
needs "ANT/regulator.ml";;
needs "ANT/roots_of_unity.ml";;
needs "Multivariate/complex_ring.ml";;
needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* Real embeddings; number fields of unit rank one with a real place.        *)
(* ------------------------------------------------------------------------- *)

let NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL = prove
 (`!k (g:A->complex).
        number_field k /\ CARD(infinite_places k) = 2 /\
        g IN real_embeddings k
        ==> ?e. ring_unit (ring_of_integers k) e /\ &1 < Re(g e) /\
                (!u. ring_unit (ring_of_integers k) u <=>
                     ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                         u = ring_neg k
                              (group_zpow (unit_group(ring_of_integers k))
                                          e n)) /\
                (!n. group_zpow (unit_group(ring_of_integers k)) e n =
                     ring_1 k ==> n = &0) /\
                (!u. ring_unit (ring_of_integers k) u /\ &1 < Re(g u)
                     ==> Re(g e) <= Re(g u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_monomorphism(k,real_ring) (\x. Re((g:A->complex) x))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EMBEDDINGS_MONOMORPHISM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [ring_monomorphism]) THEN
  REWRITE_TAC[ring_homomorphism; REAL_RING_CLAUSES] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!y. ring_unit (ring_of_integers k) y ==> (y:A) IN ring_carrier k) /\
    (!y n. ring_unit (ring_of_integers k) y
           ==> ring_unit (ring_of_integers k)
                 (group_zpow (unit_group(ring_of_integers k)) (y:A) n)) /\
    (!y. ring_unit (ring_of_integers k) y
         ==> ring_unit (ring_of_integers k) (ring_neg k y)) /\
    (!y. ring_unit (ring_of_integers k) y
         ==> ring_unit (ring_of_integers k)
               (ring_inv (ring_of_integers k) y) /\
             ring_mul k y (ring_inv (ring_of_integers k) y) = ring_1 k)`
  (CONJUNCTS_THEN2 (LABEL_TAC "car") (CONJUNCTS_THEN2 (LABEL_TAC "zpow")
    (CONJUNCTS_THEN2 (LABEL_TAC "neg") (LABEL_TAC "inv")))) THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO];
      MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`; `y:A`;
                     `n:int`] GROUP_ZPOW) THEN
      ASM_REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM];
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `y:A`] RING_UNIT_NEG) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS];
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `y:A`] RING_MUL_RINV) THEN
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `y:A`] RING_UNIT_INV) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. ring_unit (ring_of_integers k) y ==> ~(Re((g:A->complex) y) = &0)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "inv" (MP_TAC o SPEC `y:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. Re((g:A->complex) x)`) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y n. ring_unit (ring_of_integers k) y
          ==> abs(Re((g:A->complex)
                    (group_zpow (unit_group(ring_of_integers k)) y n))) =
              abs(Re(g y)) zpow n`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`;
                   `\x. abs(Re((g:A->complex) x))`; `y:A`; `n:int`]
      GROUP_REAL_MULTIPLICATIVE_ZPOW) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM; RING_OF_INTEGERS] THEN
    ASM_SIMP_TAC[GSYM REAL_ABS_NZ; REAL_ABS_MUL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NUMBER_FIELD_FUNDAMENTAL_UNITS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `e0:A`) MP_TAC) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2; GROUP_SUM_SING] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[GROUP_ZPOW; UNIT_GROUP; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ind0") (LABEL_TAC "gen0")) THEN
  REMOVE_THEN "ind0" (MP_TAC o GEN `m:int` o SPEC `\x:A. (m:int)`) THEN
  REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ind0") THEN
  SUBGOAL_THEN
   `!u. ring_unit (ring_of_integers k) u
        ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e0 n \/
                u = ring_neg k
                     (group_zpow (unit_group(ring_of_integers k)) (e0:A) n)`
  (LABEL_TAC "gen1") THENL
   [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    REMOVE_THEN "gen0" (MP_TAC o SPEC `u:A`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`z:A`; `n:A->int`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) SUBST1_TAC)) THEN
    EXISTS_TAC `(n:A->int) e0` THEN
    MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_REAL_ROOTS_OF_UNITY) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE o SPEC `z:A`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `group_zpow (unit_group(ring_of_integers k)) e0 ((n:A->int) e0) IN
      ring_carrier k`
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    ASM_SIMP_TAC[RING_MUL_LID; RING_MUL_LNEG; RING_1];
    ALL_TAC] THEN
  REMOVE_THEN "gen0" (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!e. ring_unit (ring_of_integers k) e /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                     u = ring_neg k
                          (group_zpow (unit_group(ring_of_integers k)) e n))
        ==> (!u. ring_unit (ring_of_integers k) u
                 ==> ?n. u = group_zpow (unit_group(ring_of_integers k))
                                        (ring_neg k e) n \/
                         u = ring_neg k
                              (group_zpow (unit_group(ring_of_integers k))
                                          (ring_neg k e) n)) /\
            (!u. ring_unit (ring_of_integers k) u
                 ==> ?n. u = group_zpow (unit_group(ring_of_integers k))
                                        (ring_inv (ring_of_integers k) e) n \/
                         u = ring_neg k
                              (group_zpow (unit_group(ring_of_integers k))
                                (ring_inv (ring_of_integers k) (e:A)) n))`
  (LABEL_TAC "transport") THENL
   [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "g")) THEN
    CONJ_TAC THEN X_GEN_TAC `u:A` THEN DISCH_TAC THEN
    REMOVE_THEN "g" (MP_TAC o SPEC `u:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:int` (LABEL_TAC "u")) THENL
     [MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_neg k e:A`; `n:int`]
        UNIT_GROUP_ZPOW_RING_NEG) THEN
      REWRITE_TAC[RING_OF_INTEGERS] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `ring_neg k (ring_neg k e) = (e:A)` SUBST1_TAC THENL
       [ASM_MESON_TAC[RING_NEG_NEG]; ALL_TAC] THEN
      SUBGOAL_THEN
       `group_zpow (unit_group(ring_of_integers k)) (ring_neg k e) n IN
        ring_carrier (k:A ring)`
      ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
      EXISTS_TAC `n:int` THEN
      REMOVE_THEN "u" MP_TAC THEN ASM_SIMP_TAC[RING_NEG_NEG] THEN
      MESON_TAC[];
      EXISTS_TAC `--n:int` THEN
      MP_TAC(ISPECL [`unit_group(ring_of_integers k):A group`; `e:A`;
                     `--n:int`] GROUP_ZPOW_INV) THEN
      ASM_REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM; INT_NEG_NEG] THEN
      DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "ind0" (MP_TAC o GEN `m:int` o
    ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM] o SPEC `m:int`) THEN
  DISCH_THEN(LABEL_TAC "ind0") THEN
  SUBGOAL_THEN `(e0:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `Re((g:A->complex)(ring_inv (ring_of_integers k) e0)) = inv(Re(g e0))`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN
    USE_THEN "inv" (MP_TAC o SPEC `e0:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. Re((g:A->complex) x)`) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Re((g:A->complex) e0) = &1) /\ ~(Re(g e0) = -- &1)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(CONJUNCT2(GEN_REWRITE_RULE I [ring_monomorphism]
      (ASSUME `ring_monomorphism(k,real_ring) (\x. Re((g:A->complex) x))`)))
    THEN REWRITE_TAC[] THEN DISCH_THEN(fun th ->
      MP_TAC(SPECL [`e0:A`; `ring_neg k (ring_1 k):A`] th) THEN
      MP_TAC(SPECL [`e0:A`; `ring_1 k:A`] th)) THEN
    ASM_SIMP_TAC[RING_1; RING_NEG] THEN
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> (a ==> p) ==> (b ==> q) ==> ~a /\ ~b`) THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [REMOVE_THEN "ind0" (MP_TAC o SPEC `&1:int`);
      REMOVE_THEN "ind0" (MP_TAC o SPEC `&2:int`)] THEN
    ASM_SIMP_TAC[GROUP_ZPOW_1; GROUP_ZPOW_2; UNIT_GROUP; IN_ELIM_THM;
                 RING_OF_INTEGERS; INT_OF_NUM_EQ; ARITH_EQ] THEN
    SIMP_TAC[RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG; RING_MUL_LID;
             RING_1; RING_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e. ring_unit (ring_of_integers k) e /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                     u = ring_neg k
                          (group_zpow (unit_group(ring_of_integers k)) e n)) /\
        &1 < Re((g:A->complex) e)`
  MP_TAC THENL
   [SUBGOAL_THEN
     `ring_unit (ring_of_integers k) (ring_inv (ring_of_integers k) e0) /\
      ring_inv (ring_of_integers k) e0 IN ring_carrier (k:A ring)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "transport" (MP_TAC o SPEC `e0:A`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gneg") (LABEL_TAC "ginv")) THEN
    USE_THEN "transport"
      (MP_TAC o SPEC `ring_inv (ring_of_integers k) e0:A`) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gneginv") (K ALL_TAC)) THEN
    MP_TAC(ISPEC `Re((g:A->complex) e0)` (REAL_ARITH
     `!(a:real). ~(a = &0) /\ ~(a = &1) /\ ~(a = -- &1)
          ==> &1 < a \/ a < -- &1 \/ (&0 < a /\ a < &1) \/
              (-- &1 < a /\ a < &0)`)) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `e0:A` THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `ring_neg k e0:A` THEN REPEAT CONJ_TAC THENL
       [USE_THEN "neg" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "gneg" ACCEPT_TAC;
        ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
      EXISTS_TAC `ring_inv (ring_of_integers k) e0:A` THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "ginv" ACCEPT_TAC;
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_INV_1_LT THEN
        ASM_REWRITE_TAC[]];
      EXISTS_TAC `ring_neg k (ring_inv (ring_of_integers k) e0):A` THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "neg" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "gneginv" ACCEPT_TAC;
        ASM_SIMP_TAC[] THEN REWRITE_TAC[GSYM REAL_INV_NEG] THEN
        MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "gen") ASSUME_TAC))) THEN
  EXISTS_TAC `e:A` THEN
  SUBGOAL_THEN
   `!n. Re((g:A->complex)(group_zpow (unit_group(ring_of_integers k)) e n)) =
        Re(g e) zpow n \/
        Re(g(group_zpow (unit_group(ring_of_integers k)) e n)) =
        --(Re(g e) zpow n)`
  (LABEL_TAC "val") THENL
   [GEN_TAC THEN
    FIRST_ASSUM(MP_TAC o SPECL [`e:A`; `n:int`] o check (is_eq o snd o
      dest_imp o snd o strip_forall o concl)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `abs(Re((g:A->complex) e)) = Re(g e)` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `u:A` THEN EQ_TAC THENL
     [USE_THEN "gen" (ACCEPT_TAC o SPEC `u:A`);
      DISCH_THEN(X_CHOOSE_THEN `n:int` (DISJ_CASES_THEN SUBST1_TAC)) THEN
      ASM_MESON_TAC[]];
    X_GEN_TAC `n:int` THEN DISCH_TAC THEN
    REMOVE_THEN "val" (MP_TAC o SPEC `n:int`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `Re((g:A->complex) e) zpow n = &1` MP_TAC THENL
     [MP_TAC(ISPECL [`Re((g:A->complex) e)`; `n:int`] REAL_ZPOW_LT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`Re((g:A->complex) e)`; `n:int`; `&0:int`]
      REAL_ZPOW_MONO_LT) THEN
    MP_TAC(ISPECL [`Re((g:A->complex) e)`; `&0:int`; `n:int`]
      REAL_ZPOW_MONO_LT) THEN
    ASM_REWRITE_TAC[REAL_ZPOW_0] THEN INT_ARITH_TAC;
    X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    USE_THEN "gen" (MP_TAC o SPEC `u:A`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:int` (LABEL_TAC "un")) THEN
    SUBGOAL_THEN `Re((g:A->complex) u) = Re(g e) zpow n` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`Re((g:A->complex) e)`; `n:int`] REAL_ZPOW_LT) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
      REMOVE_THEN "val" (MP_TAC o SPEC `n:int`) THEN
      UNDISCH_TAC `&1 < Re((g:A->complex) u)` THEN
      REMOVE_THEN "un" (DISJ_CASES_THEN SUBST1_TAC) THEN
      ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`Re((g:A->complex) e)`; `n:int`; `&0:int`]
      REAL_ZPOW_MONO) THEN
    MP_TAC(ISPECL [`Re((g:A->complex) e)`; `&1:int`; `n:int`]
      REAL_ZPOW_MONO) THEN
    ASM_REWRITE_TAC[REAL_ZPOW_0; REAL_ZPOW_1] THEN
    UNDISCH_TAC `&1 < Re((g:A->complex) u)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `&1:int <= n` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; INT_ARITH `~(&1:int <= n) ==> n <= &0`] THEN
    REAL_ARITH_TAC]);;

let NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL = prove
 (`!k (g:A->complex) e.
        number_field k /\ CARD(infinite_places k) = 2 /\
        g IN real_embeddings k /\
        ring_unit (ring_of_integers k) e /\ &1 < Re(g e) /\
        (!u. ring_unit (ring_of_integers k) u
             ==> ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                     u = ring_neg k
                          (group_zpow (unit_group(ring_of_integers k)) e n))
        ==> number_field_regulator k = log(Re(g e))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen")))))) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `(g:A->complex) IN complex_embeddings k /\
                !x. x IN ring_carrier k ==> real(g x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:A->complex) IN real_embeddings k` THEN
    REWRITE_TAC[real_embeddings; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:A) IN ring_carrier k` ASSUME_TAC THENL
   [ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `{e:A}`; `\x:A. x`;
                 `\u:A. \x:A. norm((g:A->complex) x)`]
    NUMBER_FIELD_REGULATOR) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING; IN_SING;
              FORALL_UNWIND_THM2] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GROUP_SUM_SING] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:A` THEN DISCH_TAC THEN
      USE_THEN "gen" (MP_TAC o SPEC `u:A`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:int` MP_TAC) THEN
      SUBGOAL_THEN
       `group_zpow (unit_group(ring_of_integers k)) (e:A) n IN
        group_carrier(unit_group(ring_of_integers k))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC GROUP_ZPOW THEN
        ASM_REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `group_zpow (unit_group(ring_of_integers k)) (e:A) n IN
        ring_carrier k`
      ASSUME_TAC THENL
       [UNDISCH_TAC
         `group_zpow (unit_group(ring_of_integers k)) (e:A) n IN
          group_carrier(unit_group(ring_of_integers k))` THEN
        REWRITE_TAC[UNIT_GROUP; IN_ELIM_THM] THEN
        ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [EXISTS_TAC `ring_1 k:A`; EXISTS_TAC `ring_neg k (ring_1 k):A`] THEN
      EXISTS_TAC `\x:A. (n:int)` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[RING_1; RING_NEG; RING_MUL_LID; RING_MUL_LNEG] THENL
       [EXISTS_TAC `1` THEN SIMP_TAC[RING_POW_1; LE_REFL; RING_1];
        EXISTS_TAC `2` THEN
        SIMP_TAC[RING_POW_2; RING_MUL_LNEG; RING_MUL_RNEG; RING_NEG_NEG;
                 RING_MUL_LID; RING_1; RING_NEG] THEN
        ARITH_TAC];
      CONJ_TAC THENL
       [REWRITE_TAC[infinite_places; IN_IMAGE] THEN
        EXISTS_TAC `g:A->complex` THEN ASM_REWRITE_TAC[];
        MESON_TAC[]]];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) RING_DET_SING o rand o lhand o snd) THEN
  REWRITE_TAC[REAL_RING_CLAUSES; IN_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  ASM_SIMP_TAC[CARD_INFINITE_PLACE_EMBEDDINGS; REAL_MUL_LID; REAL_NORM] THEN
  SUBGOAL_THEN `abs(Re((g:A->complex) e)) = Re(g e)` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_ABS_REFL] THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
  MATCH_MP_TAC LOG_POS_LT THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* The embeddings and the infinite places of a quadratic field.              *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_REAL_EMBEDDINGS =
  let lemma1 = prove
   (`!w r. w pow 2 = Cx r /\ &0 < r ==> real w`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[COMPLEX_EQ; COMPLEX_POW_2; complex_mul; RE; IM; RE_CX; IM_CX;
                real] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `Re w * Im w = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE]] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Re w * Re w - Im w * Im w = r` THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    MP_TAC(SPEC `Im w` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC)
  and lemma2 = prove
   (`!w r. w pow 2 = Cx r /\ real w ==> &0 <= r`,
    REWRITE_TAC[REAL_EXISTS] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM CX_POW; CX_INJ]) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[REAL_LE_POW_2]) in
  prove
   (`!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> (real_embeddings k = complex_embeddings k <=> &0 < d) /\
            (real_embeddings k = {} <=> d < &0)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    SUBGOAL_THEN
     `!g:A->complex. g IN complex_embeddings k
                     ==> (g x) pow 2 = Cx(real_of_int d)`
    ASSUME_TAC THENL
     [REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
        RING_HOMOMORPHISM_POW) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`x:A`; `2`]) THEN
      ASM_REWRITE_TAC[COMPLEX_RING_POW] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
        RING_HOMOMORPHISM_RING_OF_INT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[th; COMPLEX_RING_OF_INT]);
      ALL_TAC] THEN
    SUBGOAL_THEN `~(d:int = &0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `ring_pow k (x:A) 2 = ring_of_int k (&0)` THEN
      ASM_SIMP_TAC[RING_OF_INT_0; FIELD_POW_EQ_0; ARITH_EQ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `~(ring_0 k IN
          ring_carrier(subfield_generated k {ring_0 (k:A ring)}))` THEN
      REWRITE_TAC[] THEN
      MESON_TAC[SUBFIELD_GENERATED; RING_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(complex_embeddings(k:A ring) = {})` ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPLEX_EMBEDDINGS_NONEMPTY]; ALL_TAC] THEN
ASM_CASES_TAC `&0 < (d:int)` THENL
     [SUBGOAL_THEN `real_embeddings k = complex_embeddings(k:A ring)`
      ASSUME_TAC THENL
       [REWRITE_TAC[real_embeddings; EXTENSION; IN_ELIM_THM] THEN
        X_GEN_TAC `g:A->complex` THEN
        ASM_CASES_TAC `(g:A->complex) IN complex_embeddings k` THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `real((g:A->complex) x)` ASSUME_TAC THENL
         [MATCH_MP_TAC lemma1 THEN EXISTS_TAC `real_of_int d` THEN
          ASM_SIMP_TAC[REAL_OF_INT_CLAUSES];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`k:A ring`; `x:A`; `z:A`]
          QUADRATIC_FIELD_COORDINATES) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A`
          STRIP_ASSUME_TAC)) THEN
        SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
          ALL_TAC] THEN
        SUBGOAL_THEN `real((g:A->complex) a) /\ real(g b)` STRIP_ASSUME_TAC
        THENL
         [CONJ_TAC THEN MATCH_MP_TAC COMPLEX_EMBEDDINGS_PRIME_SUBFIELD_REAL THEN
          EXISTS_TAC `k:A ring` THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(g:A->complex) IN complex_embeddings k` THEN
        REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_ADD) THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_MUL) THEN
        ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
        ASM_SIMP_TAC[RING_MUL; COMPLEX_RING_CLAUSES] THEN
        MATCH_MP_TAC REAL_ADD THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_MUL THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC];
      SUBGOAL_THEN `real_embeddings k = {}:(A->complex)->bool` ASSUME_TAC THENL
       [REWRITE_TAC[real_embeddings; EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
        X_GEN_TAC `g:A->complex` THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`(g:A->complex) x`; `real_of_int d`] lemma2) THEN
        ASM_SIMP_TAC[REAL_OF_INT_CLAUSES] THEN ASM_INT_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC]]);;

let QUADRATIC_FIELD_CONJUGATE_EMBEDDING = prove
 (`!k x (g:A->complex).
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 IN ring_carrier(subfield_generated k {ring_0 k}) /\
        g IN complex_embeddings k
        ==> ?h. h IN complex_embeddings k /\ ~(h = g) /\
                complex_embeddings k = {g,h} /\ h x = --(g x) /\
                !a. a IN ring_carrier(subfield_generated k {ring_0 k})
                    ==> h a = g a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  MP_TAC(ISPEC `k:A ring` COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g1:A->complex`; `g2:A->complex`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?h:A->complex. h IN complex_embeddings k /\ ~(h = g) /\
                   complex_embeddings k = {g,h}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:A->complex) IN complex_embeddings k` THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
     [EXISTS_TAC `g2:A->complex`; EXISTS_TAC `g1:A->complex`] THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN `complex_embeddings k = {g1:A->complex, g2}` (K ALL_TAC) THEN
  EXISTS_TAC `h:A->complex` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!a. a IN ring_carrier(subfield_generated k {ring_0 k})
        ==> (h:A->complex) a = g a`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RING_HOMOMORPHISMS_EQ_FROM_SUBFIELD_GENERATED THEN
    EXISTS_TAC `complex_ring` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[IN_SING] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `h:A->complex`]
      RING_HOMOMORPHISM_0) THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
      RING_HOMOMORPHISM_0) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `(h:A->complex) x pow 2 = g x pow 2` MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `ring_pow k (x:A) 2`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `h:A->complex`]
      RING_HOMOMORPHISM_POW) THEN
    MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
      RING_HOMOMORPHISM_POW) THEN
    ASM_REWRITE_TAC[COMPLEX_RING_POW] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `2`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`x:A`; `2`]) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_TAC o GEN_REWRITE_RULE I
   [COMPLEX_RING `a pow 2 = b pow 2 <=> a = b \/ a = --b:complex`]) THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((h:A->complex) = g)` THEN
    MATCH_MP_TAC(TAUT `q ==> ~q ==> p`) THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `z:A` THEN
    ASM_CASES_TAC `(z:A) IN ring_carrier k` THENL
     [ALL_TAC;
      RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM;
                                  EXTENSIONAL]) THEN
      ASM_SIMP_TAC[]] THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `z:A`] QUADRATIC_FIELD_COORDINATES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:A` (X_CHOOSE_THEN `b:A`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:A) IN ring_carrier k /\ (b:A) IN ring_carrier k`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[RING_CARRIER_SUBFIELD_GENERATED_SUBSET; SUBSET];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[complex_embeddings; IN_ELIM_THM]) THEN
    MAP_EVERY (fun f ->
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; f] RING_HOMOMORPHISM_ADD) THEN
      MP_TAC(ISPECL [`k:A ring`; `complex_ring`; f] RING_HOMOMORPHISM_MUL))
     [`g:A->complex`; `h:A->complex`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    ASM_SIMP_TAC[RING_MUL];
    ASM_REWRITE_TAC[]]);;

let QUADRATIC_FIELD_INFINITE_PLACES = prove
 (`!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d
        ==> (&0 < d ==> CARD(infinite_places k) = 2) /\
            (d < &0 ==> CARD(infinite_places k) = 1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP QUADRATIC_FIELD_REAL_EMBEDDINGS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN (fun th -> REWRITE_TAC[GSYM th])) THEN
  MP_TAC(ISPEC `k:A ring` CARD_INFINITE_PLACES) THEN
  MP_TAC(ISPEC `k:A ring` COMPLEX_EMBEDDINGS_HAS_SIZE) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN DISCH_TAC THEN
  CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CARD_CLAUSES]) THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Imaginary quadratic fields: the units are the roots of unity.             *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_UNITS_IMAGINARY_ROOTS_OF_UNITY = prove
 (`!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\ d < &0
        ==> {u | ring_unit (ring_of_integers k) u} =
            {z | z IN ring_carrier k /\
                 ?n. 1 <= n /\ ring_pow k z n = ring_1 k}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th ->
    REWRITE_TAC[MATCH_MP NUMBER_FIELD_UNITS_EQ_ROOTS_OF_UNITY th]) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    QUADRATIC_FIELD_INFINITE_PLACES) THEN
  ASM_SIMP_TAC[]);;

let QUADRATIC_FIELD_UNIT_IMAGINARY =
  let normlemma = prove
 (`!w d A B. w pow 2 = Cx d /\ d < &0
               ==> norm(Cx A + Cx B * w) pow 2 = A pow 2 - d * B pow 2`,
    REPEAT GEN_TAC THEN
    REWRITE_TAC[COMPLEX_EQ; COMPLEX_POW_2; complex_mul; RE; IM; RE_CX;
                IM_CX] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `Re w = &0` ASSUME_TAC THENL
     [SUBGOAL_THEN `Re w * Im w = &0` MP_TAC THENL
       [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE]] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Re w * Re w - Im w * Im w = d` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_SUB_RZERO] THEN
      MP_TAC(SPEC `Re w` REAL_LE_SQUARE) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_SQNORM; RE_ADD; IM_ADD; RE_CX; IM_CX; RE; IM] THEN
    UNDISCH_TAC `Re w * Re w - Im w * Im w = d` THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING)
  and ringlemma = RING_RULE
     `!k:A ring z x a b dd.
       ring_mul k (ring_of_num k 2) z = ring_add k a (ring_mul k b x) /\
       ring_pow k x 2 = dd /\
       ring_sub k (ring_pow k a 2) (ring_mul k dd (ring_pow k b 2)) =
       ring_of_num k 4
       ==> ring_mul k (ring_of_num k 4)
             (ring_add k (ring_pow k z 2)
                (ring_add k (ring_mul k (ring_neg k a) z) (ring_1 k))) =
           ring_0 k` in
  prove
   (`!k (x:A) d z.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ d < &0
        ==> (ring_unit (ring_of_integers k) z <=>
             z IN ring_carrier k /\
             ?A B. ring_mul k (ring_of_num k 2) z =
                   ring_add k (ring_of_int k A)
                              (ring_mul k (ring_of_int k B) x) /\
                   A pow 2 - d * B pow 2 = &4)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
    SUBGOAL_THEN `~(d:int = &1)` ASSUME_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `~((x:A) IN ring_carrier(subfield_generated k {ring_0 k}))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN
      EXISTS_TAC `d:int` THEN ASM_MESON_TAC[number_field];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(ring_of_num k 2 = ring_0 (k:A ring)) /\
                  ~(ring_of_num k 4 = ring_0 (k:A ring))`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[NUMBER_FIELD_RING_OF_NUM_EQ_0] THEN CONV_TAC NUM_REDUCE_CONV;
      ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `z:A`] RING_OF_INTEGERS_UNIT_NONZERO) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `z:A`]
        QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN
      ASM_SIMP_TAC[RING_UNIT_IN_CARRIER] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`A:int`; `B:int`; `N:int`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`A:int`; `B:int`] THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?m. 1 <= m /\ ring_pow k (z:A) m = ring_1 k`
        STRIP_ASSUME_TAC THENL
         [MP_TAC(ISPEC `k:A ring` NUMBER_FIELD_UNITS_ROOTS_OF_UNITY) THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `CARD(infinite_places(k:A ring)) = 1`
          (fun th -> REWRITE_TAC[th]) THENL
           [ASM_SIMP_TAC[CARD_INFINITE_PLACES_EQ_1] THEN
            MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
              QUADRATIC_FIELD_REAL_EMBEDDINGS) THEN
            ASM_REWRITE_TAC[] THEN SIMP_TAC[];
            DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC] THEN
        FIRST_ASSUM(MP_TAC o MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `g:A->complex`) THEN
        MP_TAC(ISPECL [`k:A ring`; `g:A->complex`; `z:A`; `m:num`]
          COMPLEX_EMBEDDINGS_ROOT_OF_UNITY) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
        UNDISCH_TAC `(g:A->complex) IN complex_embeddings k` THEN
        REWRITE_TAC[complex_embeddings; IN_ELIM_THM] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_ADD) THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_MUL) THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_POW) THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_RING_OF_INT) THEN
        MP_TAC(ISPECL [`k:A ring`; `complex_ring`; `g:A->complex`]
          RING_HOMOMORPHISM_RING_OF_NUM) THEN
        ASM_REWRITE_TAC[COMPLEX_RING_CLAUSES; COMPLEX_RING_POW;
                        COMPLEX_RING_OF_INT; COMPLEX_RING_OF_NUM] THEN
        REPEAT DISCH_TAC THEN
        SUBGOAL_THEN
         `(g:A->complex)(ring_mul k (ring_of_num k 2) z) =
          Cx(real_of_int A) + Cx(real_of_int B) * g x`
        MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[RING_OF_INT; RING_MUL];
          ALL_TAC] THEN
        ASM_SIMP_TAC[RING_OF_NUM] THEN
        DISCH_THEN(MP_TAC o AP_TERM `\w:complex. norm w pow 2`) THEN
        REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`(g:A->complex) x`; `real_of_int d`; `real_of_int A`;
                       `real_of_int B`] normlemma) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL
           [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `2`] o check
              (fun th -> is_forall(concl th) &&
                         can (find_term ((=) `(pow):complex->num->complex`))
                             (concl th))) THEN
            ASM_REWRITE_TAC[] THEN MESON_TAC[];
            ASM_REWRITE_TAC[REAL_OF_INT_CLAUSES]];
          DISCH_THEN SUBST1_TAC] THEN
        ASM_REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV THEN
        REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
        UNDISCH_TAC `(A:int) pow 2 - d * B pow 2 = &4 * N` THEN INT_ARITH_TAC;
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN DISCH_TAC THEN
        MAP_EVERY X_GEN_TAC [`A:int`; `B:int`] THEN REPEAT DISCH_TAC THEN
        SUBGOAL_THEN
         `ring_add k (ring_pow k z 2)
            (ring_add k (ring_mul k (ring_neg k (ring_of_int k A)) z)
                        (ring_1 k)) = ring_0 (k:A ring)`
        ASSUME_TAC THENL
         [MP_TAC(ISPECL [`k:A ring`; `z:A`; `x:A`; `ring_of_int k A:A`;
                         `ring_of_int k B:A`; `ring_of_int k d:A`]
            ringlemma) THEN
          ASM_SIMP_TAC[RING_OF_INT] THEN ANTS_TAC THENL
           [REWRITE_TAC[GSYM RING_OF_INT_POW; GSYM RING_OF_INT_MUL;
                        GSYM RING_OF_INT_SUB] THEN
            ASM_REWRITE_TAC[RING_OF_INT_OF_NUM];
            ALL_TAC] THEN
          MP_TAC(ISPECL [`k:A ring`; `ring_of_num k 4:A`;
            `ring_add k (ring_pow k z 2)
               (ring_add k (ring_mul k (ring_neg k (ring_of_int k A)) z)
                           (ring_1 k)):A`] INTEGRAL_DOMAIN_MUL_EQ_0) THEN
          ANTS_TAC THENL
           [ASM_SIMP_TAC[FIELD_IMP_INTEGRAL_DOMAIN] THEN CONJ_TAC THEN
            RING_CARRIER_TAC THEN ASM_REWRITE_TAC[];
            DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN
         `!y:A. y IN ring_carrier k /\
                ring_add k (ring_pow k y 2)
                 (ring_add k (ring_mul k (ring_neg k (ring_of_int k A)) y)
                             (ring_1 k)) = ring_0 k
                ==> y IN ring_carrier(ring_of_integers k)`
        ASSUME_TAC THENL
         [REPEAT STRIP_TAC THEN
          REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
          MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
          MAP_EVERY EXISTS_TAC [`--A:int`; `&1:int`] THEN
          ASM_REWRITE_TAC[RING_OF_INT_NEG; RING_OF_INT_1];
          ALL_TAC] THEN
        REWRITE_TAC[ring_unit] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `ring_sub k (ring_of_int k A) (z:A)` THEN
        REWRITE_TAC[RING_OF_INTEGERS] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_SIMP_TAC[RING_SUB; RING_OF_INT] THEN
          MP_TAC(ISPECL [`k:A ring`; `z:A`; `ring_of_int k A:A`]
           (RING_RULE
             `!k:A ring z a.
                ring_add k (ring_pow k z 2)
                  (ring_add k (ring_mul k (ring_neg k a) z) (ring_1 k)) =
                ring_0 k
                ==> ring_add k (ring_pow k (ring_sub k a z) 2)
                     (ring_add k (ring_mul k (ring_neg k a) (ring_sub k a z))
                                 (ring_1 k)) = ring_0 k`)) THEN
          ASM_REWRITE_TAC[RING_OF_INT];
          MP_TAC(ISPECL [`k:A ring`; `z:A`; `ring_of_int k A:A`]
           (RING_RULE
             `!k:A ring z a.
                ring_add k (ring_pow k z 2)
                  (ring_add k (ring_mul k (ring_neg k a) z) (ring_1 k)) =
                ring_0 k
                ==> ring_mul k z (ring_sub k a z) = ring_1 k`)) THEN
          ASM_REWRITE_TAC[RING_OF_INT]]]);;

let QUADRATIC_FIELD_UNITS_IMAGINARY = prove
 (`!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ d < &0
        ==> {u | ring_unit (ring_of_integers k) u} =
            IMAGE (\(a,b). ring_mul k (ring_inv k (ring_of_num k 2))
                             (ring_add k (ring_of_int k a)
                                         (ring_mul k (ring_of_int k b) x)))
                  {(a,b) | a pow 2 - d * b pow 2 = &4} /\
            (!a b a' b'.
                a pow 2 - d * b pow 2 = &4 /\
                a' pow 2 - d * b' pow 2 = &4 /\
                ring_mul k (ring_inv k (ring_of_num k 2))
                  (ring_add k (ring_of_int k a)
                              (ring_mul k (ring_of_int k b) x)) =
                ring_mul k (ring_inv k (ring_of_num k 2))
                  (ring_add k (ring_of_int k a')
                              (ring_mul k (ring_of_int k b') x))
                ==> a = a' /\ b = b')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `~((x:A) IN ring_carrier(subfield_generated k {ring_0 k}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN
    EXISTS_TAC `d:int` THEN ASM_MESON_TAC[number_field; INT_ARITH
     `d:int < &0 ==> ~(d = &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_inv k (ring_of_num k 2) IN ring_carrier k /\
    ring_mul k (ring_of_num k 2) (ring_inv k (ring_of_num k 2)) =
    ring_1 (k:A ring)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_INV; FIELD_MUL_RINV; RING_OF_NUM;
                 NUMBER_FIELD_RING_OF_NUM_EQ_0; ARITH_EQ];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; EXISTS_PAIR_THM] THEN
    X_GEN_TAC `z:A` THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `z:A`]
      QUADRATIC_FIELD_UNIT_IMAGINARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:int`
        (X_CHOOSE_THEN `b:int` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`a:int`; `b:int`] THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MAP_EVERY EXISTS_TAC [`a:int`; `b:int`] THEN ASM_REWRITE_TAC[]] THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:A ring`; `z:A`;
        `ring_inv k (ring_of_num k 2):A`;
        `ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) x):A`;
        `ring_of_num k 2:A`]
       (RING_RULE
         `!k:A ring z t y c.
            ring_mul k c t = ring_1 k /\ ring_mul k c z = y
            ==> z = ring_mul k t y`)) THEN
      ASM_SIMP_TAC[RING_ADD; RING_MUL; RING_OF_INT; RING_OF_NUM];
      DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int`
        (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC))) THEN
      DISCH_THEN(X_CHOOSE_THEN `a':int` (X_CHOOSE_THEN `b':int`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST_ALL_TAC)))) THEN
      ASM_SIMP_TAC[RING_MUL; RING_ADD; RING_OF_INT; RING_OF_NUM] THEN
      MAP_EVERY EXISTS_TAC [`a':int`; `b':int`] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`k:A ring`;
        `ring_inv k (ring_of_num k 2):A`;
        `ring_add k (ring_of_int k a') (ring_mul k (ring_of_int k b') x):A`;
        `ring_of_num k 2:A`]
       (RING_RULE
         `!k:A ring t y c.
            ring_mul k c t = ring_1 k
            ==> ring_mul k c (ring_mul k t y) = y`)) THEN
      ASM_SIMP_TAC[RING_ADD; RING_MUL; RING_OF_INT; RING_OF_NUM]];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:A ring`; `x:A`; `a:int`; `b:int`; `a':int`; `b':int`]
      QUADRATIC_FIELD_INT_COORDINATES_EQ) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[number_field]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    FIRST_X_ASSUM(MP_TAC o AP_TERM `ring_mul k (ring_of_num k 2):A->A`) THEN
    MP_TAC(ISPECL [`k:A ring`;
        `ring_inv k (ring_of_num k 2):A`]
       (RING_RULE
         `!k:A ring t c y.
            ring_mul k c t = ring_1 k
            ==> ring_mul k c (ring_mul k t y) = y`)) THEN
    DISCH_THEN(MP_TAC o SPEC `ring_of_num k 2:A`) THEN
    ASM_SIMP_TAC[RING_ADD; RING_MUL; RING_OF_INT; RING_OF_NUM]]);;

let QUADRATIC_FIELD_UNITS_IMAGINARY_CARD = prove
 (`!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ d < &0
        ==> {u | ring_unit (ring_of_integers k) u} HAS_SIZE
            (if d = -- &1 then 4 else if d = -- &3 then 6 else 2)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP QUADRATIC_FIELD_UNITS_IMAGINARY th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC (LABEL_TAC "inj")) THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; PAIR_EQ] THEN
    CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT GEN_TAC THEN
    STRIP_TAC THEN USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d = -- &4:int)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `squarefree(num_of_int(abs(-- &4:int)))` THEN
    CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM; squarefree; NOT_FORALL_THM; NOT_IMP] THEN
    EXISTS_TAC `2` THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIVIDES_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{(a,b) | a pow 2 - d * b pow 2 = &4:int} =
    if d = -- &1 then {(&2,&0),(-- &2,&0),(&0,&2),(&0,-- &2)}
    else if d = -- &3
    then {(&2,&0),(-- &2,&0),(&1,&1),(&1,-- &1),(-- &1,&1),(-- &1,-- &1)}
    else {(&2,&0),(-- &2,&0)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:int`; `b:int`] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPECL [`a:int`; `b:int`; `d:int`] INT_NORM_FORM_4_IMAGINARY) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[] THEN
      REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
      CONV_TAC INT_REDUCE_CONV;
      REPEAT COND_CASES_TAC THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) THEN
      CONV_TAC INT_REDUCE_CONV THEN INT_ARITH_TAC];
    ASM_CASES_TAC `d = -- &1:int` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `d = -- &3:int` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[HAS_SIZE; FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; PAIR_EQ] THEN
    CONV_TAC INT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

let QUADRATIC_FIELD_UNITS_IMAGINARY_GENERIC = prove
 (`!k (x:A) d.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ d < &0 /\
        ~(d = -- &1) /\ ~(d = -- &3)
        ==> {u | ring_unit (ring_of_integers k) u} =
            {ring_1 k, ring_neg k (ring_1 k)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    QUADRATIC_FIELD_UNITS_IMAGINARY_CARD) THEN
  ASM_REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `ring_unit (ring_of_integers k) (ring_1 k) /\
      ring_unit (ring_of_integers k) (ring_neg k (ring_1 (k:A ring)))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_UNIT_1) THEN
      DISCH_THEN(fun th -> REWRITE_TAC[REWRITE_RULE[RING_OF_INTEGERS] th] THEN
        MP_TAC(MATCH_MP RING_UNIT_NEG th)) THEN
      REWRITE_TAC[RING_OF_INTEGERS];
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `~(ring_1 k = ring_neg k (ring_1 (k:A ring)))`
    ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`k:A ring`; `2`] NUMBER_FIELD_RING_OF_NUM_EQ_0) THEN
      ASM_REWRITE_TAC[ARITH_EQ] THEN
      REWRITE_TAC[ARITH_RULE `2 = 1 + 1`; RING_OF_NUM_ADD; RING_OF_NUM_1] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
      SIMP_TAC[RING_ADD_RNEG; RING_1];
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                   NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV]]);;

(* ------------------------------------------------------------------------- *)
(* Real quadratic fields: the fundamental unit and the regulator.            *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_FUNDAMENTAL_UNIT = prove
 (`!k (x:A) d (g:A->complex).
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\
        ~(x IN ring_carrier(subfield_generated k {ring_0 k})) /\
        ring_pow k x 2 = ring_of_int k d /\ &0 < d /\
        g IN complex_embeddings k
        ==> ?e. ring_unit (ring_of_integers k) e /\ &1 < Re(g e) /\
                (!u. ring_unit (ring_of_integers k) u <=>
                     ?n. u = group_zpow (unit_group(ring_of_integers k)) e n \/
                         u = ring_neg k
                              (group_zpow (unit_group(ring_of_integers k))
                                          e n)) /\
                (!n. group_zpow (unit_group(ring_of_integers k)) e n =
                     ring_1 k ==> n = &0) /\
                (!u. ring_unit (ring_of_integers k) u /\ &1 < Re(g u)
                     ==> Re(g e) <= Re(g u)) /\
                number_field_regulator k = log(Re(g e))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    QUADRATIC_FIELD_INFINITE_PLACES) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    QUADRATIC_FIELD_REAL_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:A->complex) IN real_embeddings k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `g:A->complex`]
    NUMBER_FIELD_FUNDAMENTAL_UNIT_REAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:A` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NUMBER_FIELD_REGULATOR_FUNDAMENTAL_UNIT_REAL THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The Pell equation.                                                        *)
(* ------------------------------------------------------------------------- *)

let QUADRATIC_FIELD_PELL_UNIT = prove
 (`!k (y:A) D a b.
        field k /\ y IN ring_carrier k /\ ring_pow k y 2 = ring_of_int k D /\
        a pow 2 - D * b pow 2 = &1
        ==> ring_unit (ring_of_integers k)
              (ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k b) y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:A) IN ring_carrier(ring_of_integers k)` ASSUME_TAC THENL
   [REWRITE_TAC[RING_OF_INTEGERS_CARRIER; IN_ELIM_THM] THEN
    MATCH_MP_TAC INTEGRAL_ELEMENT_QUADRATIC THEN
    MAP_EVERY EXISTS_TAC [`&0:int`; `--D:int`] THEN
    ASM_REWRITE_TAC[RING_OF_INT_0; RING_OF_INT_NEG] THEN
    ASM_SIMP_TAC[RING_MUL_LZERO; RING_ADD_LZERO; RING_OF_INT; RING_ADD_RNEG;
                 RING_NEG];
    ALL_TAC] THEN
  REWRITE_TAC[ring_unit] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_ADD) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC
   `ring_add k (ring_of_int k a) (ring_mul k (ring_of_int k (--b)) y):A` THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `ring_of_integers k:A ring` RING_ADD) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_MUL) THEN
    MP_TAC(ISPEC `ring_of_integers k:A ring` RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RING_OF_INTEGERS] THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `ring_of_int (k:A ring)`) THEN
  ASM_REWRITE_TAC[RING_OF_INT_SUB; RING_OF_INT_MUL; RING_OF_INT_POW;
                  RING_OF_INT_NEG; RING_OF_INT_1] THEN
  UNDISCH_TAC `ring_pow k y 2 = ring_of_int k D:A` THEN
  MP_TAC(ISPECL [`k:A ring`; `a:int`] RING_OF_INT) THEN
  MP_TAC(ISPECL [`k:A ring`; `b:int`] RING_OF_INT) THEN
  MP_TAC(ISPECL [`k:A ring`; `D:int`] RING_OF_INT) THEN
  UNDISCH_TAC `(y:A) IN ring_carrier k` THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t)))
   [`ring_of_int k a:A`; `ring_of_int k b:A`; `ring_of_int k D:A`; `y:A`] THEN
  RING_TAC);;

let QUADRATIC_FIELD_UNIT_POW_IN_ORDER = prove
 (`!k (x:A) d c e.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ ~(d = &1) /\ ~(c = &0) /\
        ring_unit (ring_of_integers k) e
        ==> ?m a b. 1 <= m /\
                    ring_pow k e m =
                    ring_add k (ring_of_int k a)
                      (ring_mul k (ring_of_int k b)
                         (ring_mul k (ring_of_int k c) x))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `ring_char(k:A ring) = 0` ASSUME_TAC THENL
   [ASM_MESON_TAC[number_field]; ALL_TAC] THEN
  SUBGOAL_THEN
   `ring_of_int k (&2 * c) IN ring_carrier(ring_of_integers k) /\
    ~(ring_of_int k (&2 * c) = ring_0 (k:A ring))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RING_OF_INT_EQ_0_CHAR_0] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `&2 * c:int`] RING_OF_INT) THEN
    REWRITE_TAC[RING_OF_INTEGERS] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `j = ideal_generated (ring_of_integers k)
                    {ring_of_int k (&2 * c):A}` THEN
  SUBGOAL_THEN
   `ring_ideal (ring_of_integers k) (j:A->bool) /\
    FINITE(ring_carrier(quotient_ring (ring_of_integers k) j))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [EXPAND_TAC "j" THEN REWRITE_TAC[RING_IDEAL_IDEAL_GENERATED];
      DISCH_TAC THEN MATCH_MP_TAC RING_OF_INTEGERS_FINITE_QUOTIENT THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `ring_of_int k (&2 * c) IN (j:A->bool)` MP_TAC THENL
       [EXPAND_TAC "j" THEN MATCH_MP_TAC IDEAL_GENERATED_INC THEN
        ASM_REWRITE_TAC[SING_SUBSET; IN_SING];
        ASM_REWRITE_TAC[IN_SING]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. ring_pow k e n IN ring_carrier(ring_of_integers k) /\
        ring_unit (ring_of_integers k) (ring_pow k (e:A) n)`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `e:A`; `n:num`]
      RING_UNIT_POW) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN MESON_TAC[RING_UNIT_IN_CARRIER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?p q. p < q /\
          ring_coset (ring_of_integers k) j (ring_pow k e q) =
          ring_coset (ring_of_integers k) j (ring_pow k (e:A) p)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MP_TAC(ISPECL
     [`\n. ring_coset (ring_of_integers k) j (ring_pow k (e:A) n)`;
      `(:num)`] INFINITE_IMAGE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
      MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
      CONJ_TAC THENL [MESON_TAC[]; ASM_MESON_TAC[]];
      REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC
       `ring_carrier(quotient_ring (ring_of_integers k) (j:A->bool))` THEN
      ASM_SIMP_TAC[QUOTIENT_RING_CARRIER; SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ring_of_integers k:A ring`; `j:A->bool`;
                 `ring_pow k e q:A`; `ring_pow k e p:A`] RING_COSET_EQ) THEN
  ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (fun th -> rand(concl th) = `j:A->bool`)) THEN
  ASM_SIMP_TAC[IDEAL_GENERATED_SING_ALT; IN_ELIM_THM; RING_OF_INTEGERS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `v = ring_inv (ring_of_integers k) (ring_pow k e p):A` THEN
  SUBGOAL_THEN
   `v IN ring_carrier(ring_of_integers k) /\
    ring_mul k (ring_pow k e p) v = ring_1 (k:A ring)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_pow k e p:A`]
      RING_MUL_RINV) THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `ring_pow k e p:A`]
      RING_INV) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ring_carrier(ring_of_integers k) SUBSET ring_carrier(k:A ring)`
  ASSUME_TAC THENL [REWRITE_TAC[RING_OF_INTEGERS_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `ring_mul k v t:A`]
    QUADRATIC_FIELD_INTEGRAL_COORDINATES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`ring_of_integers k:A ring`; `v:A`; `t:A`] RING_MUL) THEN
    ASM_REWRITE_TAC[RING_OF_INTEGERS];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`A:int`; `B:int`; `N:int`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`q - p:num`; `&1 + c * A:int`; `B:int`] THEN
  CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(e:A) IN ring_carrier k /\ (v:A) IN ring_carrier k /\
                (t:A) IN ring_carrier k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RING_UNIT_IN_CARRIER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:A ring`; `e:A`; `p:num`; `q - p:num`] RING_POW_ADD) THEN
  ASM_SIMP_TAC[ARITH_RULE `p < q ==> p + (q - p) = q:num`] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `ring_sub k (ring_pow k e q) (ring_pow k e p) =
    ring_mul k (ring_of_int k (&2 * c)) (t:A)` THEN
  ASM_REWRITE_TAC[RING_OF_INT_MUL; RING_OF_INT_OF_NUM] THEN DISCH_TAC THEN
  REWRITE_TAC[RING_OF_INT_ADD; RING_OF_INT_MUL; RING_OF_INT_1] THEN
  MP_TAC(ISPECL [`k:A ring`; `ring_pow k e p:A`; `ring_pow k e (q - p):A`;
                 `v:A`; `t:A`; `ring_of_num k 2:A`; `ring_of_int k c:A`;
                 `ring_of_int k A:A`; `ring_of_int k B:A`; `x:A`]
   (RING_RULE
     `!k:A ring P W v t T C a b x.
        ring_sub k (ring_mul k P W) P = ring_mul k (ring_mul k T C) t /\
        ring_mul k P v = ring_1 k /\
        ring_mul k T (ring_mul k v t) = ring_add k a (ring_mul k b x)
        ==> W = ring_add k (ring_add k (ring_1 k) (ring_mul k C a))
                           (ring_mul k b (ring_mul k C x))`)) THEN
  ASM_SIMP_TAC[RING_POW; RING_OF_NUM; RING_OF_INT]);;

let QUADRATIC_FIELD_PELL_SOLUTION = prove
 (`!k (x:A) d c.
        number_field k /\
        extension_degree (subfield_generated k {ring_0 k},k) I = 2 /\
        x IN ring_carrier k /\ ring_pow k x 2 = ring_of_int k d /\
        squarefree(num_of_int(abs d)) /\ &0 < d /\ ~(d = &1) /\ ~(c = &0)
        ==> ?a b. a pow 2 - (d * c pow 2) * b pow 2 = &1 /\ ~(b = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NUMBER_FIELD_IMP_FIELD) THEN
  SUBGOAL_THEN `~((x:A) IN ring_carrier(subfield_generated k {ring_0 k}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SQRT_SQUAREFREE_NOT_IN_PRIME_SUBFIELD THEN
    EXISTS_TAC `d:int` THEN ASM_MESON_TAC[number_field];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `g:A->complex` o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    MATCH_MP COMPLEX_EMBEDDINGS_NONEMPTY) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `g:A->complex`]
    QUADRATIC_FIELD_FUNDAMENTAL_UNIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:A` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`; `c:int`; `e:A`]
    QUADRATIC_FIELD_UNIT_POW_IN_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `a:int`; `b:int`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `g:A->complex`]
    QUADRATIC_FIELD_CONJUGATE_EMBEDDING) THEN
  ASM_SIMP_TAC[RING_OF_INT_IN_SUBFIELD_GENERATED] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:A->complex` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:A ring`; `x:A`; `d:int`]
    QUADRATIC_FIELD_REAL_EMBEDDINGS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN
   `ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x)) /\
    ring_homomorphism(k,real_ring) (\x. Re((h:A->complex) x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC RING_MONOMORPHISM_IMP_HOMOMORPHISM THEN
    MATCH_MP_TAC REAL_EMBEDDINGS_MONOMORPHISM THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:A) IN ring_carrier k /\
                ring_unit (ring_of_integers k) (ring_pow k e m)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[RING_OF_INTEGERS_UNIT_NONZERO];
      MP_TAC(ISPECL [`ring_of_integers k:A ring`; `e:A`; `m:num`]
        RING_UNIT_POW) THEN
      ASM_REWRITE_TAC[RING_OF_INTEGERS]];
    ALL_TAC] THEN
  MAP_EVERY (fun th ->
    ASSUME_TAC(REWRITE_RULE[REAL_FIELD_CLAUSES; REAL_RING_OF_INT] th))
   [MATCH_MP RING_HOMOMORPHISM_POW (ASSUME
     `ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x))`);
    MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (ASSUME
     `ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x))`);
    MATCH_MP RING_HOMOMORPHISM_RING_OF_INT (ASSUME
     `ring_homomorphism(k,real_ring) (\x. Re((h:A->complex) x))`)] THEN
  SUBGOAL_THEN `&1 < Re((g:A->complex)(ring_pow k e m))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_POW_LT_1 THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(Re((g:A->complex)(ring_pow k e m))) *
    abs(Re((h:A->complex)(ring_pow k e m))) = &1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~((g:A->complex) = h)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:A ring`; `ring_pow k e m:A`]
      RING_OF_INTEGERS_UNIT_NORM_PRODUCT) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PRODUCT_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY; REAL_MUL_RID] THEN
    SUBGOAL_THEN `real((g:A->complex)(ring_pow k e m)) /\
                  real((h:A->complex)(ring_pow k e m))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `real_embeddings k = {g:A->complex, h}` THEN
      REWRITE_TAC[EXTENSION; real_embeddings; IN_ELIM_THM; IN_INSERT;
                  NOT_IN_EMPTY] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `g:A->complex` th) THEN
                           MP_TAC(SPEC `h:A->complex` th)) THEN
      REWRITE_TAC[] THEN ASM_SIMP_TAC[RING_POW];
      ASM_SIMP_TAC[REAL_NORM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `Re((g:A->complex)
      (ring_add k (ring_of_int k a)
        (ring_mul k (ring_of_int k b) (ring_mul k (ring_of_int k c) x)))) =
    real_of_int a + real_of_int b * (real_of_int c * Re(g x)) /\
    Re((h:A->complex)
      (ring_add k (ring_of_int k a)
        (ring_mul k (ring_of_int k b) (ring_mul k (ring_of_int k c) x)))) =
    real_of_int a + real_of_int b * (real_of_int c * --Re(g x))`
  (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `ring_homomorphism(k,real_ring) (\x. Re((g:A->complex) x))` THEN
    UNDISCH_TAC `ring_homomorphism(k,real_ring) (\x. Re((h:A->complex) x))` THEN
    REWRITE_TAC[ring_homomorphism; REAL_RING_CLAUSES] THEN
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[RING_OF_INT; RING_MUL; RE_NEG];
    ALL_TAC] THEN
  SUBGOAL_THEN `Re((g:A->complex) x) pow 2 = real_of_int d` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `2`] o check (is_forall o concl) o
      check (fun th -> can (find_term ((=) `ring_pow:A ring->A->num->A`))
                           (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(real_of_int a + real_of_int b * real_of_int c * Re((g:A->complex) x)) *
    (real_of_int a + real_of_int b * real_of_int c * --Re(g x)) =
    real_of_int(a pow 2 - (d * c pow 2) * b pow 2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[int_sub_th; int_mul_th; int_pow_th] THEN
    UNDISCH_TAC `Re((g:A->complex) x) pow 2 = real_of_int d` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((a:int) pow 2 - (d * c pow 2) * b pow 2) = &1`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM(CONJUNCT1 REAL_OF_INT_CLAUSES)] THEN
    REWRITE_TAC[int_abs_th; int_of_num_th] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[REAL_ABS_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b:int = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `&1 < real_of_int a + real_of_int(&0) * real_of_int c *
                           Re((g:A->complex) x)` THEN
    UNDISCH_TAC `abs((a:int) pow 2 - (d * c pow 2) * &0 pow 2) = &1` THEN
    REWRITE_TAC[int_of_num_th; REAL_MUL_LZERO; REAL_ADD_RID] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    REWRITE_TAC[INT_MUL_RZERO; INT_SUB_RZERO] THEN
    ONCE_REWRITE_TAC[GSYM INT_POW2_ABS] THEN
    REWRITE_TAC[GSYM REAL_OF_INT_CLAUSES] THEN
    DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&2:int`; `a:int`] INT_LE_SQUARE_ABS) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= (d:int) /\ &1 <= (c:int) pow 2 /\ &1 <= (b:int) pow 2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_INT_ARITH_TAC;
      MP_TAC(SPECL [`&1:int`; `c:int`] INT_LE_SQUARE_ABS);
      MP_TAC(SPECL [`&1:int`; `b:int`] INT_LE_SQUARE_ABS)] THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= (d * c pow 2) * (b:int) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&2:int`; `d:int`; `&1:int`; `(c:int) pow 2`]
      INT_LE_MUL2) THEN
    MP_TAC(SPECL [`&2:int`; `d * (c:int) pow 2`; `&1:int`; `(b:int) pow 2`]
      INT_LE_MUL2) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:int = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `abs((&0:int) pow 2 - (d * c pow 2) * b pow 2) = &1` THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(a:int) pow 2 + (d * c pow 2) * b pow 2`; `&2 * (a:int) * b`] THEN
  ASM_REWRITE_TAC[INT_ENTIRE; INT_OF_NUM_EQ; ARITH_EQ] THEN
  SUBGOAL_THEN
   `((a:int) pow 2 + (d * c pow 2) * b pow 2) pow 2 -
    (d * c pow 2) * (&2 * a * b) pow 2 =
    (abs(a pow 2 - (d * c pow 2) * b pow 2)) pow 2`
  SUBST1_TAC THENL
   [REWRITE_TAC[INT_POW2_ABS] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV]);;

let PELL_SOLUTION_IMP_INFINITE = prove
 (`!d a b:int.
        &0 < d /\ a pow 2 - d * b pow 2 = &1 /\ ~(b = &0)
        ==> INFINITE {(x,y) | &0 < x /\ &0 < y /\ x pow 2 - d * y pow 2 = &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= (b:int) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1:int`; `b:int`] INT_LE_SQUARE_ABS) THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= d * (b:int) pow 2` ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1:int`; `d:int`; `&1:int`; `(b:int) pow 2`]
      INT_LE_MUL2) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= abs(a:int)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`a:int`; `&1:int`] INT_LE_SQUARE_ABS) THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p q:int. p pow 2 - d * q pow 2 = &1 /\ &2 <= p /\ &1 <= q`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXISTS_TAC [`abs(a:int)`; `abs(b:int)`] THEN
    ASM_REWRITE_TAC[INT_POW2_ABS] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(p,q):int#int`;
                 `\(z:int#int) (n:num).
                    (FST z * p + d * SND z * q, FST z * q + SND z * p)`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->int#int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!n. FST(f n) pow 2 - d * SND(f n) pow 2 = &1 /\
        &2 <= FST((f:num->int#int) n) /\ &1 <= SND(f n)`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `FST((f:num->int#int) n) pow 2 - d * SND(f n) pow 2 = &1 /\
                 &2 <= FST(f n) /\ &1 <= SND(f n)` THEN
    SPEC_TAC(`SND((f:num->int#int) n)`,`v:int`) THEN
    SPEC_TAC(`FST((f:num->int#int) n)`,`u:int`) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `&4 <= u * p /\ &0 <= d * v * q /\ &0 <= u * q /\
                  &2 <= v * (p:int)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MP_TAC(SPECL [`&2:int`; `u:int`; `&2:int`; `p:int`] INT_LE_MUL2);
        MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
         [ALL_TAC; MATCH_MP_TAC INT_LE_MUL];
        MATCH_MP_TAC INT_LE_MUL;
        MP_TAC(SPECL [`&1:int`; `v:int`; `&2:int`; `p:int`] INT_LE_MUL2)] THEN
      ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN
       `(u * p + d * v * q) pow 2 - d * (u * q + v * p) pow 2 =
        (u pow 2 - d * v pow 2) * ((p:int) pow 2 - d * q pow 2)`
      SUBST1_TAC THENL [INT_ARITH_TAC; ASM_REWRITE_TAC[INT_MUL_LID]];
      ASM_INT_ARITH_TAC;
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!m n. m < n ==> FST((f:num->int#int) m) < FST(f n)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `\m n. FST((f:num->int#int) m) < FST(f n)`
      TRANSITIVE_STEPWISE_LT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_conj o snd o
      dest_forall o concl)) THEN
    SPEC_TAC(`SND((f:num->int#int) n)`,`v:int`) THEN
    SPEC_TAC(`FST((f:num->int#int) n)`,`u:int`) THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `u * &2 <= u * (p:int) /\ &0 <= d * v * (q:int)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC;
        MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
         [ALL_TAC; MATCH_MP_TAC INT_LE_MUL] THEN ASM_INT_ARITH_TAC];
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC INFINITE_SUPERSET THEN
  EXISTS_TAC `IMAGE (f:num->int#int) (:num)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INFINITE_IMAGE THEN REWRITE_TAC[num_INFINITE; IN_UNIV] THEN
    MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[INT_LT_REFL];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `n:num` THEN
    MAP_EVERY EXISTS_TAC
     [`FST((f:num->int#int) n)`; `SND((f:num->int#int) n)`] THEN
    REWRITE_TAC[PAIR] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o check (is_conj o snd o
      dest_forall o concl)) THEN
    INT_ARITH_TAC]);;

let PELL_EQUATION_INFINITE = prove
 (`!d:int.
        &0 < d /\ ~(?m. d = m pow 2)
        ==> INFINITE {(x,y) | &0 < x /\ &0 < y /\
                              x pow 2 - d * y pow 2 = &1}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `d:int` INT_SQUAREFREE_DECOMPOSITION) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d0:int`; `c:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&c:int) pow 2` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LT THEN ASM_SIMP_TAC[INT_OF_NUM_LT; LE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < d0 /\ ~(d0:int = &1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`&0:int`; `d0:int`; `(&c:int) pow 2`]
        INT_LT_RMUL_EQ) THEN
      ASM_REWRITE_TAC[INT_MUL_LZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
        check (fun th -> lhs(concl th) = `d:int`)) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(?m:int. d = m pow 2)` THEN
      REWRITE_TAC[] THEN EXISTS_TAC `&c:int` THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPEC `d0:int` QUADRATIC_FIELD_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(((1->num)->real)->bool) ring`
   (X_CHOOSE_THEN `w:((1->num)->real)->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`k:(((1->num)->real)->bool) ring`;
                 `w:((1->num)->real)->bool`; `d0:int`; `&c:int`]
    QUADRATIC_FIELD_PELL_SOLUTION) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:int` (X_CHOOSE_THEN `b:int`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC PELL_SOLUTION_IMP_INFINITE THEN
  MAP_EVERY EXISTS_TAC [`a:int`; `b:int`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC INT_LT_MUL THEN ASM_REWRITE_TAC[]);;

let PELL_EQUATION_INFINITE_NUM = prove
 (`!d. ~(?m. d = m EXP 2) ==> INFINITE {(x,y) | x EXP 2 = d * y EXP 2 + 1}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `&d:int` PELL_EQUATION_INFINITE) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LT; ARITH_RULE `0 < d <=> ~(d = 0)`] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(?m. 0 = m EXP 2)` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `0` THEN ARITH_TAC;
      DISCH_THEN(X_CHOOSE_TAC `m:int`) THEN
      UNDISCH_TAC `~(?m. d = m EXP 2)` THEN REWRITE_TAC[] THEN
      EXISTS_TAC `num_of_int(abs m)` THEN
      REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_POW] THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ABS_POS; INT_POW2_ABS]];
    ALL_TAC] THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\z:num#num. (&(FST z):int,&(SND z):int))
                    {(x,y) | x EXP 2 = d * y EXP 2 + 1}` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_IMAGE;
              EXISTS_PAIR_THM; PAIR_EQ; FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`x:int`; `y:int`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`num_of_int x`; `num_of_int y`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LT_IMP_LE] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_ADD;
              GSYM INT_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_LT_IMP_LE] THEN ASM_INT_ARITH_TAC);;
