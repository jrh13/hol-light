(* ========================================================================= *)
(* Units of the order Z[theta].                                              *)
(*                                                                           *)
(* Purpose: cocompactness of the logarithmic embedding of the units in the   *)
(* trace-zero, conjugation-symmetric hyperplane, bounded generation of the   *)
(* units by a finite set, and the decomposition of the elements of a fixed   *)
(* norm. No Dirichlet unit theorem: cocompactness comes from the box         *)
(* principle and the finiteness of elements of bounded norm up to units,     *)
(* bounded generation from a chain argument along the segment from 0 to      *)
(* the logarithmic vector of a unit, with steps in a finite set              *)
(* (Northcott).                                                              *)
(*                                                                           *)
(* Main results: NF_UNITS_COCOMPACT, NF_UNITS_BOUNDED_GENERATION,            *)
(* NF_NORM_EQ_DECOMPOSITION (an element of norm m is b times a power         *)
(* product of a finite set of units, b in a finite set, with exponent sum    *)
(* linear in the logarithmic size), NF_UNIT_NONZERO.                         *)
(*                                                                           *)
(* Uses: Baker/nf_defs.ml (nf_data, nf_unit), Baker/nf_order.ml              *)
(* (NF_UNIT_NORM, NF_NORM_INTEGER, NF_ORDER_CNJ), Baker/nf_box.ml            *)
(* (NF_BOX_PRINCIPLE, NF_BOUNDED_NORM_FINITE), Baker/ant_bridge_nf.ml        *)
(* (NF_ORDER_NORTHCOTT).                                                     *)
(* ========================================================================= *)

needs "Baker/nf_box.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Elementary facts about units.                                             *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_NONZERO = prove
 (`!n r u k. nf_unit n r u /\ k IN 1..n ==> ~(u k = Cx(&0))`,
  REWRITE_TAC[nf_unit] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; CX_INJ] THEN REAL_ARITH_TAC);;

let NF_UNIT_NORM_NONZERO = prove
 (`!n a k. ~(cproduct(1..n) a = Cx(&0)) /\ k IN 1..n ==> ~(a k = Cx(&0))`,
  SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
  MESON_TAC[]);;

let NF_UNIT_ONE = prove
 (`!n r. nf_unit n r (\k. Cx(&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_unit] THEN
  SIMP_TAC[NF_ORDER_CX; INTEGER_CLOSED] THEN
  EXISTS_TAC `\k:num. Cx(&1)` THEN
  SIMP_TAC[NF_ORDER_CX; INTEGER_CLOSED; COMPLEX_MUL_LID]);;

let NF_UNIT_EQ = prove
 (`!n r a b. nf_unit n r a /\ (!k. k IN 1..n ==> b k = a k)
             ==> nf_unit n r b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_unit] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `w:num->complex`))
   ASSUME_TAC) THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[NF_ORDER_EQ];
    EXISTS_TAC `w:num->complex` THEN ASM_SIMP_TAC[]]);;

let NF_UNIT_MUL = prove
 (`!n r a b. nf_unit n r a /\ nf_unit n r b
             ==> nf_unit n r (\k. a k * b k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[nf_unit] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `a':num->complex`))
   (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `b':num->complex`))) THEN
  ASM_SIMP_TAC[NF_ORDER_MUL] THEN
  EXISTS_TAC `\k. (a':num->complex) k * b' k` THEN
  ASM_SIMP_TAC[NF_ORDER_MUL] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:num->complex) k * a' k = Cx(&1) /\
                (b:num->complex) k * b' k = Cx(&1)`
  MP_TAC THENL [ASM_MESON_TAC[]; CONV_TAC COMPLEX_RING]);;

let NF_UNIT_INV = prove
 (`!n r a. nf_unit n r a ==> nf_unit n r (\k. inv(a k))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[nf_unit]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC NF_UNIT_EQ THEN EXISTS_TAC `b:num->complex` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[nf_unit] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a:num->complex` THEN ASM_SIMP_TAC[COMPLEX_MUL_SYM];
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPLEX_MUL_RINV_UNIQ THEN ASM_SIMP_TAC[]]);;

let NF_UNIT_DIV = prove
 (`!n r a b. nf_unit n r a /\ nf_unit n r b
             ==> nf_unit n r (\k. a k / b k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_div] THEN
  MP_TAC(ISPECL [`n:num`; `r:num->complex`; `a:num->complex`;
                 `\k. inv((b:num->complex) k)`] NF_UNIT_MUL) THEN
  ASM_SIMP_TAC[NF_UNIT_INV]);;

let NF_UNIT_NORM_CNJ = prove
 (`!n r a cj k.
        nf_order n r a /\
        (!k. k IN 1..n ==> cj k IN 1..n /\ r(cj k) = cnj(r k)) /\
        k IN 1..n
        ==> norm(a(cj k)) = norm(a k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `r:num->complex`; `a:num->complex`; `cj:num->num`;
                `k:num`] NF_ORDER_CNJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[COMPLEX_NORM_CNJ]);;

let NF_UNIT_PRODUCT_NORM = prove
 (`!n c r u. nf_data n c r /\ nf_unit n r u
             ==> product(1..n) (\k. norm(u k)) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `u:num->complex`]
         NF_UNIT_NORM) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[GSYM NORM_CPRODUCT; FINITE_NUMSEG] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[COMPLEX_NORM_CX; NORM_NEG] THEN
  REAL_ARITH_TAC);;

let NF_UNIT_LOG_SUM = prove
 (`!n c r u. nf_data n c r /\ nf_unit n r u
             ==> sum(1..n) (\k. log(norm(u k))) = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `u:num->complex`]
         NF_UNIT_PRODUCT_NORM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\k. norm((u:num->complex) k)`; `1..n`] LOG_PRODUCT) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG; LOG_1] THEN ANTS_TAC THENL
   [REWRITE_TAC[COMPLEX_NORM_NZ] THEN ASM_MESON_TAC[NF_UNIT_NONZERO];
    DISCH_THEN(ACCEPT_TAC o SYM)]);;

let NF_UNIT_LOG_BOUND_FINITE = prove
 (`!n (A:(num->complex)->bool).
        FINITE A
        ==> ?L. &0 <= L /\
                !b k. b IN A /\ k IN 1..n ==> abs(log(norm(b k))) <= L`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\p:(num->complex)#num. abs(log(norm(FST p (SND p))))`;
                 `(A:(num->complex)->bool) CROSS (1..n)`]
         UPPER_BOUND_FINITE_SET_REAL) THEN
  ASM_SIMP_TAC[FINITE_CROSS; FINITE_NUMSEG; FORALL_PAIR_THM; IN_CROSS] THEN
  DISCH_THEN(X_CHOOSE_TAC `L:real`) THEN EXISTS_TAC `abs L` THEN
  REWRITE_TAC[REAL_ABS_POS] THEN
  ASM_MESON_TAC[REAL_ARITH `(x:real) <= L ==> x <= abs L`]);;

(* ------------------------------------------------------------------------- *)
(* Cocompactness of the logarithmic embedding of the units.                  *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_EXP_PRODUCT = prove
 (`!n CK v. 1 <= n /\ &0 < CK /\ sum(1..n) v = &0
            ==> product(1..n) (\k. exp(log CK / &n + v k)) = CK`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[GSYM REAL_EXP_SUM; FINITE_NUMSEG] THEN
  REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB; ETA_AX] THEN
  ASM_REWRITE_TAC[REAL_ADD_RID] THEN
  SUBGOAL_THEN `&n * log CK / &n = log CK` SUBST1_TAC THENL
   [MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[EXP_LOG]]);;

let NF_UNIT_LOG_BOX = prove
 (`!n CK v x.
        1 <= n /\ &1 <= CK /\ sum(1..n) v = &0 /\
        (!k. k IN 1..n ==> &0 < x k /\ x k <= exp(log CK / &n + v k)) /\
        &1 <= product(1..n) x
        ==> !k. k IN 1..n ==> abs(log(x k) - v k) <= log CK`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. k IN 1..n ==> log(x k) <= log CK / &n + v k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM LOG_EXP] THEN
    MATCH_MP_TAC LOG_MONO_LE_IMP THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= sum(1..n) (\k. log(x k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:num->real`; `1..n`] LOG_PRODUCT) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..n) (\k. log CK / &n + v k) = log CK` ASSUME_TAC THENL
   [REWRITE_TAC[SUM_ADD_NUMSEG; SUM_CONST_NUMSEG; ADD_SUB; ETA_AX] THEN
    ASM_REWRITE_TAC[REAL_ADD_RID] THEN
    MATCH_MP_TAC REAL_DIV_LMUL THEN REWRITE_TAC[REAL_OF_NUM_EQ] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log CK` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= log CK / &n /\ log CK / &n <= log CK`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < &n` ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_OF_NUM_LE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\k. (log CK / &n + (v:num->real) k) - log((x:num->real) k)`;
                 `log CK`; `1..n`]
         SUM_POS_BOUND) THEN
  REWRITE_TAC[FINITE_NUMSEG; SUM_SUB_NUMSEG] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_SUB_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let NF_UNITS_COCOMPACT = prove
 (`!n c r. nf_data n c r
           ==> ?C0. &0 <= C0 /\
                    !cj v. (!k. k IN 1..n
                                 ==> cj k IN 1..n /\ r(cj k) = cnj(r k) /\
                                     v(cj k) = v k) /\
                            sum(1..n) v = &0
                            ==> ?u. nf_unit n r u /\
                                    !k. k IN 1..n
                                        ==> abs(log(norm(u k)) - v k) <= C0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_MESON_TAC[nf_data]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NF_BOX_PRINCIPLE) THEN
  DISCH_THEN(X_CHOOSE_THEN `CK:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "box"))) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `CK:real`]
         NF_BOUNDED_NORM_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(num->complex)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fin")))) THEN
  MP_TAC(SPECL [`n:num`; `A:(num->complex)->bool`]
         NF_UNIT_LOG_BOUND_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `LA:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LA"))) THEN
  SUBGOAL_THEN `&0 <= log CK` ASSUME_TAC THENL
   [MATCH_MP_TAC LOG_POS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `log CK + LA` THEN CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`cj:num->num`; `v:num->real`] THEN STRIP_TAC THEN
  USE_THEN "box" (MP_TAC o SPECL
   [`cj:num->num`; `\k. exp(log CK / &n + (v:num->real) k)`]) THEN
  REWRITE_TAC[REAL_EXP_POS_LT] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_SIMP_TAC[];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC NF_UNIT_EXP_PRODUCT THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `a:num->complex` STRIP_ASSUME_TAC)] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `a:num->complex`]
         NF_NORM_INTEGER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `cproduct(1..n) (a:num->complex) = Cx(&0)` THEN
    SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `product(1..n) (\k. norm((a:num->complex) k)) = abs m`
  ASSUME_TAC THENL
   [SIMP_TAC[GSYM NORM_CPRODUCT; FINITE_NUMSEG] THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_CX];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= abs m` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_ABS_INTEGER_LEMMA THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `product(1..n) (\k. norm((a:num->complex) k)) <= CK`
  ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `product(1..n) (\k. exp(log CK / &n + (v:num->real) k))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PRODUCT_LE_NUMSEG THEN REWRITE_TAC[NORM_POS_LE] THEN
      ASM_MESON_TAC[IN_NUMSEG];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC NF_UNIT_EXP_PRODUCT THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`; `CK:real`; `v:num->real`;
                `\k. norm((a:num->complex) k)`] NF_UNIT_LOG_BOX) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_NZ]; DISCH_THEN(LABEL_TAC "lb")] THEN
  USE_THEN "fin" (MP_TAC o SPEC `a:num->complex`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_NORM_CX; CX_INJ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->complex`
   (X_CHOOSE_THEN `u:num->complex` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u:num->complex` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((b:num->complex) k = Cx(&0)) /\
                ~((u:num->complex) k = Cx(&0))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM COMPLEX_ENTIRE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `log(norm((a:num->complex) k)) =
                log(norm((b:num->complex) k)) + log(norm((u:num->complex) k))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC LOG_MUL THEN
    ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(log(norm((b:num->complex) k))) <= LA /\
                abs(log(norm((a:num->complex) k)) - v k) <= log CK`
  MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `log(norm((a:num->complex) k)) =
               log(norm((b:num->complex) k)) +
               log(norm((u:num->complex) k))` THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Regrouping a product according to the values of an index map.             *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_CPRODUCT_GROUP = prove
 (`!(f:A->B) (g:B->complex) s t.
        FINITE s /\ IMAGE f s SUBSET t
        ==> cproduct s (\x. g(f x)) =
            cproduct t (\y. g y pow CARD {x | x IN s /\ f x = y})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `\x:A. (g:B->complex)(f x)`; `s:A->bool`]
    (MATCH_MP ITERATE_IMAGE_GEN MONOIDAL_COMPLEX_MUL)) THEN
  ASM_REWRITE_TAC[GSYM cproduct] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `cproduct (IMAGE (f:A->B) s)
                (\y. (g:B->complex) y pow CARD {x | x IN s /\ f x = y})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CPRODUCT_EQ THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    ASM_SIMP_TAC[GSYM CPRODUCT_CONST; FINITE_RESTRICT] THEN
    MATCH_MP_TAC CPRODUCT_EQ THEN SIMP_TAC[IN_ELIM_THM];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CPRODUCT_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:B` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{x | x IN s /\ (f:A->B) x = y} = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES; complex_pow]]]);;

(* ------------------------------------------------------------------------- *)
(* The chain argument: a unit u with all abs(log(norm(u k))) <= X is a       *)
(* product of at most 1 + X units with all conjugates of norm at most        *)
(* exp(2 C0 + 1), C0 the cocompactness constant (for a fixed cj).            *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_CHAIN = prove
 (`!n c r cj C0.
        nf_data n c r /\
        (!k. k IN 1..n ==> cj k IN 1..n /\ r(cj k) = cnj(r k)) /\
        &0 <= C0 /\
        (!v. (!k. k IN 1..n ==> v(cj k) = v k) /\ sum(1..n) v = &0
             ==> ?u. nf_unit n r u /\
                     !k. k IN 1..n ==> abs(log(norm(u k)) - v k) <= C0)
        ==> !u X. nf_unit n r u /\
                  (!k. k IN 1..n ==> abs(log(norm(u k))) <= X)
                  ==> ?N q. &N <= &1 + X /\
                            (!j. j IN 1..N
                                 ==> nf_unit n r (q j) /\
                                     !k. k IN 1..n
                                         ==> norm(q j k) <=
                                             exp(&2 * C0 + &1)) /\
                            (!k. k IN 1..n
                                 ==> u k = cproduct(1..N) (\j. q j k))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cc")))) THEN
  MAP_EVERY X_GEN_TAC [`u:num->complex`; `X:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ub")) THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_MESON_TAC[nf_data]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(log(norm((u:num->complex) 1))) <= X` MP_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?N. 1 <= N /\ X < &N /\ &N <= &1 + X` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `X:real` FLOOR_POS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `N0:num`) THEN
    MP_TAC(SPEC `X:real` FLOOR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `N0 + 1` THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    CONJ_TAC THENL [ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(N = 0) /\ &0 < &N` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nf_order n r (u:num->complex)` ASSUME_TAC THENL
   [ASM_MESON_TAC[nf_unit]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN 1..n
                    ==> log(norm((u:num->complex)(cj k))) = log(norm(u k))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[NF_UNIT_NORM_CNJ];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum(1..n) (\k. log(norm((u:num->complex) k))) = &0`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[NF_UNIT_LOG_SUM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. ?w. nf_unit n r w /\
            !k. k IN 1..n
                ==> abs(log(norm(w k)) -
                        &j / &N * log(norm((u:num->complex) k))) <= C0`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    USE_THEN "cc" (MP_TAC o SPEC
     `\k. &j / &N * log(norm((u:num->complex) k))`) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[SUM_LMUL; REAL_MUL_RZERO];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `w0:num->num->complex`)] THEN
  SUBGOAL_THEN
   `?w:num->num->complex.
        (!j. nf_unit n r (w j) /\
             !k. k IN 1..n
                 ==> abs(log(norm(w j k)) -
                         &j / &N * log(norm((u:num->complex) k))) <= C0) /\
        (!k. w 0 k = Cx(&1)) /\ (!k. w N k = u k)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\j:num. if j = 0 then (\k:num. Cx(&1))
                        else if j = N then (u:num->complex) else w0 j` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `j:num` THEN
    ASM_CASES_TAC `j = 0` THEN ASM_REWRITE_TAC[] THENL
     [REWRITE_TAC[NF_UNIT_ONE; COMPLEX_NORM_CX; REAL_ABS_NUM; LOG_1] THEN
      ASM_REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_SUB_REFL; REAL_ABS_0];
      ASM_CASES_TAC `(j:num) = N` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; REAL_OF_NUM_EQ; REAL_MUL_LID;
                   REAL_SUB_REFL; REAL_ABS_0]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j k. k IN 1..n ==> ~((w:num->num->complex) j k = Cx(&0))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL [`n:num`; `r:num->complex`; `(w:num->num->complex) j`;
                  `k:num`] NF_UNIT_NONZERO) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `N:num` THEN
  EXISTS_TAC `\j k. (w:num->num->complex) j k / w (j - 1) k` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[IN_NUMSEG]) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NF_UNIT_DIV THEN ASM_REWRITE_TAC[ETA_AX]; ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs(log(norm((u:num->complex) k))) <= X` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(log(norm((w:num->num->complex) j k)) -
          &j / &N * log(norm((u:num->complex) k))) <= C0 /\
      abs(log(norm(w (j - 1) k)) - &(j - 1) / &N * log(norm(u k))) <= C0`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&(j - 1) = &j - &1` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC REAL_OF_NUM_SUB THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(log(norm((u:num->complex) k)) / &N) <= &1`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_ABS_DIV; REAL_ABS_NUM; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `&j / &N * log(norm((u:num->complex) k)) -
      (&j - &1) / &N * log(norm(u k)) = log(norm(u k)) / &N`
    ASSUME_TAC THENL [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm((w:num->num->complex) j k) /\
                  &0 < norm((w:num->num->complex) (j - 1) k)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPLEX_NORM_NZ]; ALL_TAC] THEN
    REWRITE_TAC[COMPLEX_NORM_DIV] THEN
    SUBGOAL_THEN
     `norm((w:num->num->complex) j k) / norm(w (j - 1) k) =
      exp(log(norm(w j k)) - log(norm(w (j - 1) k)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[GSYM LOG_DIV; REAL_LT_DIV; EXP_LOG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_EXP_MONO_LE] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN `!m k. m <= N /\ k IN 1..n
                        ==> (w:num->num->complex) m k =
                            cproduct(1..m) (\j. w j k / w (j - 1) k)`
    ASSUME_TAC THENL
     [INDUCT_TAC THENL
       [ASM_REWRITE_TAC[CPRODUCT_CLAUSES_NUMSEG; ARITH_EQ];
        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        REWRITE_TAC[CPRODUCT_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC m`;
                    SUC_SUB1] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC COMPLEX_DIV_LMUL THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`N:num`; `k:num`]) THEN
    ASM_REWRITE_TAC[LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Bounded generation of the units.                                          *)
(* ------------------------------------------------------------------------- *)

let NF_UNIT_BOUNDED_GENERATION_1 = prove
 (`!n c r. nf_data n c r
           ==> ?S. FINITE S /\ (!s. s IN S ==> nf_unit n r s) /\
                   !u X. nf_unit n r u /\
                         (!k. k IN 1..n ==> abs(log(norm(u k))) <= X)
                         ==> ?mm. (!k. k IN 1..n
                                       ==> u k = cproduct S
                                                 (\s. s k pow mm s)) /\
                                  &(nsum S mm) <= &1 + X`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NF_CONJ_INVOLUTION) THEN
  DISCH_THEN(X_CHOOSE_THEN `cj:num->num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!k. k IN 1..n ==> cj k IN 1..n /\ r(cj k) = cnj(r k)`
  ASSUME_TAC THENL [ASM_MESON_TAC[PERMUTES_IN_IMAGE]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NF_UNITS_COCOMPACT) THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `cj:num->num`))) THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `cj:num->num`;
                `C0:real`] NF_UNIT_CHAIN) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_THEN(LABEL_TAC "chain")] THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`;
                `exp(&2 * C0 + &1)`] NF_ORDER_NORTHCOTT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(num->complex)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "north")))) THEN
  EXISTS_TAC `{s | s IN A /\ nf_unit n r s}` THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:num->complex`; `X:real`] THEN STRIP_TAC THEN
  USE_THEN "chain" (MP_TAC o SPECL [`u:num->complex`; `X:real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:num` (X_CHOOSE_THEN `q:num->num->complex`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "qj") (LABEL_TAC "prod"))))) THEN
  SUBGOAL_THEN
   `!j. ?s. j IN 1..N
            ==> (s IN A /\ nf_unit n r s) /\
                !k. k IN 1..n ==> (q:num->num->complex) j k = s k`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
    DISCH_TAC THEN
    USE_THEN "north" (MP_TAC o SPEC `(q:num->num->complex) j`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[nf_unit]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:num->complex` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `b:num->complex` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NF_UNIT_EQ THEN
    EXISTS_TAC `(q:num->num->complex) j` THEN ASM_MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `sel:num->num->complex` (LABEL_TAC "sel"))] THEN
  SUBGOAL_THEN
   `IMAGE (sel:num->num->complex) (1..N) SUBSET {s | s IN A /\ nf_unit n r s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\s:num->complex. CARD {j | j IN 1..N /\
                                          (sel:num->num->complex) j = s}` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `cproduct(1..N) (\j. (sel:num->num->complex) j k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `cproduct(1..N) (\j. (q:num->num->complex) j k)` THEN
      CONJ_TAC THENL
       [USE_THEN "prod" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CPRODUCT_EQ THEN ASM_MESON_TAC[]];
      MP_TAC(ISPECL [`sel:num->num->complex`; `\s:num->complex. s k`;
                     `1..N`; `{s | s IN A /\ nf_unit n r s}`]
             NF_UNIT_CPRODUCT_GROUP) THEN
      ASM_REWRITE_TAC[FINITE_NUMSEG]];
    MP_TAC(ISPECL [`sel:num->num->complex`; `\j:num. 1`; `1..N`;
                   `{s | s IN A /\ nf_unit n r s}`] NSUM_GROUP) THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
    SIMP_TAC[GSYM CARD_EQ_NSUM; FINITE_RESTRICT; FINITE_NUMSEG;
             CARD_NUMSEG_1] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

let NF_UNITS_BOUNDED_GENERATION = prove
 (`!n c r. nf_data n c r
           ==> ?S C1. FINITE S /\ (!s. s IN S ==> nf_unit n r s) /\
                      !u X. nf_unit n r u /\
                            (!k. k IN 1..n ==> abs(log(norm(u k))) <= X)
                            ==> ?mm. (!k. k IN 1..n
                                          ==> u k = cproduct S
                                                    (\s. s k pow mm s)) /\
                                     &(nsum S mm) <= C1 * (&1 + X)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NF_UNIT_BOUNDED_GENERATION_1) THEN
  DISCH_THEN(X_CHOOSE_TAC `S:(num->complex)->bool`) THEN
  MAP_EVERY EXISTS_TAC [`S:(num->complex)->bool`; `&1`] THEN
  ASM_REWRITE_TAC[REAL_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Elements of a fixed norm.                                                 *)
(* ------------------------------------------------------------------------- *)

let NF_NORM_EQ_DECOMPOSITION = prove
 (`!n c r m. nf_data n c r /\ ~(m = &0)
             ==> ?M S C2. FINITE M /\ FINITE S /\
                          (!b. b IN M ==> nf_order n r b) /\
                          (!s. s IN S ==> nf_unit n r s) /\
                          !a X. nf_order n r a /\ cproduct(1..n) a = Cx m /\
                                (!k. k IN 1..n ==> abs(log(norm(a k))) <= X)
                                ==> ?b mm. b IN M /\
                                           (!k. k IN 1..n
                                                ==> a k = b k * cproduct S
                                                          (\s. s k pow mm s)) /\
                                           &(nsum S mm) <= C2 * (&1 + X)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 <= n` ASSUME_TAC THENL [ASM_MESON_TAC[nf_data]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NF_UNIT_BOUNDED_GENERATION_1) THEN
  DISCH_THEN(X_CHOOSE_THEN `S:(num->complex)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "gen")))) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `abs(m:real)`]
         NF_BOUNDED_NORM_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:(num->complex)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "dec")))) THEN
  MP_TAC(SPECL [`n:num`; `M:(num->complex)->bool`]
         NF_UNIT_LOG_BOUND_FINITE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `LA:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "LA"))) THEN
  MAP_EVERY EXISTS_TAC
   [`M:(num->complex)->bool`; `S:(num->complex)->bool`; `&1 + (LA:real)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; ASM_MESON_TAC[];
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:num->complex`; `X:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ub"))) THEN
  SUBGOAL_THEN `&0 <= X` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs(log(norm((a:num->complex) 1))) <= X` MP_TAC THENL
     [USE_THEN "ub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG; LE_REFL];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cproduct(1..n) (a:num->complex) = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CX_INJ]; ALL_TAC] THEN
  USE_THEN "dec" (MP_TAC o SPEC `a:num->complex`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPLEX_NORM_CX; REAL_LE_REFL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->complex`
   (X_CHOOSE_THEN `u:num->complex` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!k. k IN 1..n ==> abs(log(norm((u:num->complex) k))) <= X + LA`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((b:num->complex) k = Cx(&0)) /\
                  ~((u:num->complex) k = Cx(&0))`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM DE_MORGAN_THM; GSYM COMPLEX_ENTIRE] THEN
      ASM_MESON_TAC[NF_UNIT_NORM_NONZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `log(norm((a:num->complex) k)) =
      log(norm((b:num->complex) k)) + log(norm((u:num->complex) k))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[COMPLEX_NORM_MUL] THEN MATCH_MP_TAC LOG_MUL THEN
      ASM_REWRITE_TAC[COMPLEX_NORM_NZ];
      ALL_TAC] THEN
    SUBGOAL_THEN `abs(log(norm((b:num->complex) k))) <= LA /\
                  abs(log(norm((a:num->complex) k))) <= X`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC
     `log(norm((a:num->complex) k)) =
      log(norm((b:num->complex) k)) + log(norm((u:num->complex) k))` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "gen" (MP_TAC o SPECL [`u:num->complex`; `(X:real) + LA`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:(num->complex)->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`b:num->complex`; `mm:(num->complex)->num`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 + (X:real) + LA` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`LA:real`; `X:real`] REAL_LE_MUL) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;
