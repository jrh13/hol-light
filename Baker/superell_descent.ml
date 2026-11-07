(* ========================================================================= *)
(* The superelliptic descent at one simple root.                             *)
(*                                                                           *)
(* Purpose: for a simple root z of a monic integer polynomial f and          *)
(* integer solutions of y^m = c0 f(x) with Cx x <> z, the number d (x - z)   *)
(* is an m-th power of an integer polynomial in z of degree < n for some d   *)
(* in a finite set DD of non-zero algebraic integers (independent of x,      *)
(* y). Route: z is an algebraic integer; NF_DATA_EXISTS gives nf_data n c r  *)
(* with r 1 = z (g = minimal polynomial); NF_DATA_POLY_DIVIDES gives the     *)
(* cofactor h, f = g h; h(z) <> 0 since z is a simple root of f (product     *)
(* rule for the derivative); g(x) <> 0 for integers x with Cx x <> z         *)
(* (NF_ORDER_ZERO for x - theta); NF_POWER_DESCENT_FACTOR; read off at the   *)
(* conjugate 1, reduce xi to degree < n (NF_ORDER_REDUCE), DD = values of    *)
(* the descent set at index 1 (NF_ORDER_ALGEBRAIC_INTEGER).                  *)
(*                                                                           *)
(* Main results: SUPERELL_ROOT_DESCENT.                                      *)
(*                                                                           *)
(* Uses: Baker/nf_fields.ml (NF_DATA_EXISTS), Baker/descent.ml               *)
(* (NF_POWER_DESCENT_FACTOR, NF_DATA_POLY_DIVIDES), Baker/schinzel_sunit.ml  *)
(* (NF_DESCENT_VSUM_CX, SUPERELL_DERIV_SHIFT), Baker/nf_order.ml             *)
(* (NF_ORDER_REDUCE, NF_ORDER_ZERO, NF_ORDER_ALGEBRAIC_INTEGER),             *)
(* Baker/algint.ml (ALGEBRAIC_INTEGER_EXPLICIT), Baker/nf_defs.ml            *)
(* (NF_DATA_1_IN).                                                           *)
(* ========================================================================= *)

needs "Baker/descent.ml";;
needs "Baker/nf_fields.ml";;

prioritize_real();;
prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* At a simple root z of f = g h with g(z) = 0 the cofactor h is non-zero.   *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_SIMPLE_ROOT_COFACTOR = prove
 (`!N (a:num->real) n (c:num->real) (h:num->real) (z:complex).
        (!w. vsum(0..N) (\i. Cx(a i) * w pow i) =
             vsum(0..n) (\i. Cx(c i) * w pow i) *
             vsum(0..N) (\i. Cx(h i) * w pow i)) /\
        vsum(0..n) (\i. Cx(c i) * z pow i) = Cx(&0) /\
        ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))
        ==> ~(vsum(0..N) (\i. Cx(h i) * z pow i) = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC
   `~(vsum(1..N) (\i. Cx(&i * (a:num->real) i) * z pow (i - 1)) = Cx(&0))` THEN
  REWRITE_TAC[GSYM SUPERELL_DERIV_SHIFT] THEN
  MATCH_MP_TAC COMPLEX_DERIVATIVE_UNIQUE_AT THEN
  EXISTS_TAC `\w. vsum(0..N) (\i. Cx((a:num->real) i) * w pow i)` THEN
  EXISTS_TAC `z:complex` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`N:num`; `\i. Cx((a:num->real) i)`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\w. vsum(0..N) (\i. Cx((a:num->real) i) * w pow i)) =
    (\w. vsum(0..n) (\i. Cx((c:num->real) i) * w pow i) *
         vsum(0..N) (\i. Cx((h:num->real) i) * w pow i))`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MP_TAC(CONJ
   (BETA_RULE(ISPECL [`n:num`; `\i. Cx((c:num->real) i)`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN))
   (BETA_RULE(ISPECL [`N:num`; `\i. Cx((h:num->real) i)`; `z:complex`]
      HAS_COMPLEX_DERIVATIVE_POLYFUN))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_COMPLEX_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO; COMPLEX_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* An integer different from theta = r 1 is not a root of the field poly.    *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_NF_NONROOT = prove
 (`!n c r (x:real).
        nf_data n c r /\ integer x /\ ~(Cx x = r 1)
        ==> ~(sum(0..n) (\i. c i * x pow i) = &0)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  SUBGOAL_THEN `nf_order n r (\k. Cx x - (r:num->complex) k)` ASSUME_TAC
  THENL
   [MP_TAC(ISPECL [`n:num`; `r:num->complex`; `\k:num. Cx x`;
                   `r:num->complex`] NF_ORDER_SUB) THEN
    ASM_SIMP_TAC[NF_ORDER_CX; NF_ORDER_ROOT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Cx x - (r:num->complex) 1 = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COMPLEX_SUB_0]; ALL_TAC] THEN
  SUBGOAL_THEN `!k. k IN 1..n ==> ~(Cx x - (r:num->complex) k = Cx(&0))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN REPEAT STRIP_TAC THEN
    MP_TAC(BETA_RULE(ISPECL [`n:num`; `c:num->real`; `r:num->complex`;
                             `\k. Cx x - (r:num->complex) k`; `k:num`; `1`]
      NF_ORDER_ZERO)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(cproduct(1..n) (\k. Cx x - (r:num->complex) k) = Cx(&0))`
  MP_TAC THENL
   [SIMP_TAC[CPRODUCT_EQ_0; FINITE_NUMSEG] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP NF_DATA_FACTOR th)]) THEN
  ASM_REWRITE_TAC[NF_DESCENT_VSUM_CX; CX_INJ]);;

(* ------------------------------------------------------------------------- *)
(* The export.                                                               *)
(* ------------------------------------------------------------------------- *)

let SUPERELL_ROOT_DESCENT = prove
 (`!N (a:num->real) m c0 z.
   1 <= m /\ (!i. integer(a i)) /\ a N = &1 /\ integer c0 /\
   ~(c0 = &0) /\
   vsum(0..N) (\i. Cx(a i) * z pow i) = Cx(&0) /\
   ~(vsum(1..N) (\i. Cx(&i * a i) * z pow (i - 1)) = Cx(&0))
   ==> ?n DD. 1 <= n /\ FINITE DD /\
              (!d. d IN DD ==> algebraic_integer d /\ ~(d = Cx(&0))) /\
              !x y. integer x /\ integer y /\ ~(Cx x = z) /\
                    y pow m = c0 * sum(0..N) (\i. a i * x pow i)
                    ==> ?d q. d IN DD /\ (!i. integer(q i)) /\
                              d * (Cx x - z) =
                              vsum(0..n-1) (\i. Cx(q i) * z pow i) pow m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `algebraic_integer z` MP_TAC THENL
   [REWRITE_TAC[ALGEBRAIC_INTEGER_EXPLICIT] THEN
    MAP_EVERY EXISTS_TAC [`N:num`; `a:num->real`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `c:num->real`
    (X_CHOOSE_THEN `r:num->complex` STRIP_ASSUME_TAC)) o
    MATCH_MP NF_DATA_EXISTS) THEN
  UNDISCH_THEN `(r:num->complex) 1 = z` (SUBST_ALL_TAC o SYM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP NF_DATA) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP NF_DATA_1_IN) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `N:num`;
                `a:num->real`] NF_DATA_POLY_DIVIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `m:num`; `N:num`;
                `h:num->real`; `c0:real`] NF_POWER_DESCENT_FACTOR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [MATCH_MP_TAC SUPERELL_SIMPLE_ROOT_COFACTOR THEN
    MAP_EVERY EXISTS_TAC [`a:num->real`; `n:num`; `c:num->real`] THEN
    ASM_SIMP_TAC[NF_DATA_ROOT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(num->complex)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `IMAGE (\d:num->complex. d 1) D`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [X_GEN_TAC `d:num->complex` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC NF_ORDER_ALGEBRAIC_INTEGER THEN
    MAP_EVERY EXISTS_TAC [`n:num`; `c:num->real`; `r:num->complex`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `sum(0..N) (\i. (a:num->real) i * x pow i) =
    sum(0..n) (\i. (c:num->real) i * x pow i) *
    sum(0..N) (\i. (h:num->real) i * x pow i)`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CX_INJ] THEN
    REWRITE_TAC[CX_MUL; GSYM NF_DESCENT_VSUM_CX] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(sum(0..n) (\i. (c:num->real) i * x pow i) = &0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUPERELL_NF_NONROOT THEN EXISTS_TAC `r:num->complex` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num->complex` (X_CHOOSE_THEN `xi:num->complex`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(SPECL [`n:num`; `c:num->real`; `r:num->complex`; `xi:num->complex`]
    NF_ORDER_REDUCE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`(d:num->complex) 1`; `p:num->real`] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `d:num->complex` THEN
  ASM_REWRITE_TAC[]);;
